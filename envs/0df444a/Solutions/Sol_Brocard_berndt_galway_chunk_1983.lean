-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1983
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:12.690508+00:00
-- url     : https://prove2.me/submissions/3d37ef54-4636-4b6c-ab99-26eadad6ea28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 356474820 ≤ n < 356654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 356476070 1250 356474820 356474857
    0x610060c0602092815050d050603150a0c0e0f0d140c060a05040306050105010915111023060109080d080604060905070207210b06210105100e0f0c07020112060b 70
    0x1a203040205a040c5c0c400b4120300900c8201211445d840011140e82a0380454085042d0725030f04086885c0031821014002c2c40307041042482594038441d0041c2c50951442e554103a20032440034104044000f504180710ba200c82c2180c00307000041c10344071300b00c0040c1d5621001e0300d50488180d40801c0455202000b1340c03001420024061080080920625014041c28604a83ca080c01c20408010118220004109010541002ca8560001008211251070b1041800d00100f01c9012074031a8a024032201040d15441000004925501c921000b60840c0c89910080040c104841d1040e588070300003920240c0c1145c0c80b444049500003072801058016000c0354028500ea03845c2820710006100b05820a940b800c40c84541c2d0f40200307035aa400340350070550460b964200402c644c01604048400342c0c3e182100d035401d180070030011907002e0281c18110343e900b0662800558801c2c21000c5d49500480d040094000141314010240d48200c2045408102258000400c50b494005240c1d01c0c3d040302c460a00440c8252 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 356477320 1250 356476070 356476129
    0xa1205090a02151c06030507061d04110c010b010305191a12060f1e010317071505061002010e0d0f020321060f0906101d1513080610060c060209 63
    0x107400d1400d10b44d4100e0000c02070a07003545d490381d4880c4010303c2203108202c070290300d040044140c0d5644040250005008010142e28054001e21a03081802c085c9115483c180310004694064010340344500f421b0076101d0b00310360481c61500c00134807254402c1b09004180c24200d04e030b140c070f41080e484102d14110300103103d207181049100180144c010300704041c060442085000c110786c1059103d056a9000080f500d030302c02030b8a14840980a42d08000e04030180e02a07604c80d40b20386a1303111901920065400714049841e0640c16801c0e40c0c1e5076030000c01154001a1502d08039032241c0040a0914007600c16689410490704007040d0000c0510544074408103120103000080c82c2040c4004d071102c0042d104ca0000d80790240c009000e490134102c024007880400c0000c3c500080c0a400700700303440d61004108411030000c6541128468002400803020712090480108005100040c03540c441e01200000f010868240101103c0c80f0500d030350201d403c80c0e001e214081a980e0742c81c1d03d030115070f2130004000388581c125 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 356478570 1250 356477320 356477347
    0x60c150405071e030b01060518040c030c09050411030604050a0e0307060e16060e040c0504090c02030301170c030a0f052a090c0a021e030d060b03040501050901020a1205090a0215 78
    0x41071140c40f0070340c280e42010000200c400040a044820a0801e55213800e004500b84004612815003194468030380302440d114503030594010029541d40d9600c4040d00c41e1a0000e020480e15a00e40140240b075060000490a14140d00507580c8201c0e00000811400b5203401c0c03662954021080441c0c0c030a03111082c80c201c034402084102100000001d0421000b4682140a4200d01401852a000700e84511340300703194a0103a0b0407078004140000c81007200c9100b5000094403900280100f840d09503c60703e104842c1d42000a91901101c40140a44200c0f2219a12080400102e0004072114051100d200104142c080a100d94803595260350247c43d240c0001001074034180188042a040c2c014052044075903800210a10820000e00d14920b56200d10300c0c120703145004106003000030074103128001c607050000c14040d600441c400c200074807442c0c489242d0a03091b03001e0741c400b080000d901030040d05050702c09501302c541c018550b107095502603042900403680210f190949040c1141000810704440b800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 356479820 1250 356478570 356478599
    0x91b061b150a0525090513020405010e1206130309030c090b040509010912050904060b04090c02160b1812100b0a0905011401050f040902030405010b090a0515060c15040507 75
    0x184680412551602039292403d200c100c40d16441c0c98018100040c860364002e40140000d04401410f1000c1c4007028221f810181d072140c0507460000344060043c04903418410f02d42134064022130080c1c0031740d603542501c40c606c1c0c009480040d8200401d0000c00004140415000303005000030b58030214548400c03078240070a48170007a001c0001d50385402d4054000c580241c03075021403c61b03140f0780340c0d581d40615800503000d0030341500001c601d8400018005010307001c95012003080c0b191502030300c4445140c5200c40941000d1b1744260700560724200a4440680412214000348032001410003840094003038003181b4102c1c03a07250340a1107a5a450a00c1d145140140e0030f40018013504805020944c141089404440d0300c4484041c113014000c500300248100d04003d580160540d400b0440d00c03881c181c2406c502900000c020799000f040321401051010805e8022907100b5030008801c4801c50700c0700001e20495904c420303003002c014020009848000b0b8044c0e99014010742c040d00043c0442402e101c04134027802d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 356481070 1250 356479820 356479831
    0x412030801060c0f032006090705090906010e01090207020d062c03040b1801030603140c1503070c120912140609062403120a030207060605010503091b061b15 69
    0x4108a40d10009090080c2003980d084d894070700b2803044811b410007118a03402583d1040281d029800801a50000c0099054101c8100302c0d00c816280d250220790300d48800003802015041c400313030401485001c165800914a0600c05412400f200d112600e44a0880d00386080c41d2406281030807014910f501d045001811000e50000518582854008038049912400c048a08440c0c4000d0780720460740e002e648200c00841e08403468014050510413002e484554100c0a0340c411001d8a10044a120040c5d0541e03101d9202500c481c03030f07030307980c00c1e15400d8590350303c03139400307002c120400320080350400440040980c050711802200d00c0c01c0449642c4503007840700c01840020190701c000d0410030344844410241520040101d14840448019000320b0b00780318880b0908080c501e000201c1c00040360341070f070003010294004d0350204000758440300110345612041e540c0282a070b0064072010342881300100f0004038604014442480c0402030040516000e42481d84207441d500104101c0c00d111884425030755000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 356482320 1250 356481070 356481077
    0x50712030815011107180902150a020d0f0e012d050a020c030a05031c020f0a0f120501030312020d0b0913030f050a080414030d050405010209010e0306010b0316021002041203080106 79
    0xc040b84856960f02d17002485004e40f20b039005554107114a005501100701d00c4d80107009012850300001021265078810808500103100b007603215415070f84a1405800e41107119940d41c40d101c607240c00111000407003081d450650010112019003440d03810b0030001801c45594440030344403038950300040c0c01e103420f0202450098114410701c0c4000f03413001c41180c0c40301c0c46e0407041003400e103650003c80d0001e0140c02e40003038003840d0000c0c006020035000198020314001c641d5840c601c9081c0001c80b20701340d4a0038070000340030512650104400446640240c204000b804800150540c00407000400d01c540a0303c10003461001034910b4424582d00060055080030350741002490000007080085c40003500500140110055034176070541c240f014400c5828404404005010604040c20118000e41c0001099404500c69400c2c6c481507007404a02d81d4100d400c80c059450450791020715188980252100403001c40c0124030804510044900c098409052412030300640400c59241c0a04034501c1131300540280f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 356483570 1250 356482320 356482337
    0xc1006080d0203211b0d020d0e0109170309280b01060f02030414060903060403080105040b01030c050714070308030a050108010c030204140f4b01051605071203081501 73
    0x414084c5040c500c40710301d0120a40c440d540c4040c03038900c40020862260900f031500241000c0c00410030380107000c1090700c0680400c04140c607140d4003400c076108200c00419214405500404d410400009154483c1c042c9003070700e00e442c190303400d00d003114201d003008401110a68076030001801031481d00c0380e000d8031490a0188800002d514003942d240258420948070b40c00c805070140722520f59006440d290607001d0100c59141c206440c0140001c2003d000d01d40c0120b10305128207035590b1103809508548202c640b21145052001c1c1c07036200c44903c0000c8409403511542c40c00200060410008500c940440f035000116541410061825242600307882c6007018011f1109002d1004940010141d21001b00d50400c0300d54a8400441c003070440310a02805040d00b4941460988502e00340040054421411018100030046440c0e00040c110015410b0009a082c1322192034414802d00301c0c8100390064040310702c001d41e9002c00030910030149000320001814034040c850103500b01c1c4403501c1c00da542420310100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 356484820 1250 356483570 356483587
    0x150a06030f0f0501090804090515010203090604060c050325030e1909050910180c0503070608011a0909041a09121e0d02120609010b03040507030b09030c1006080d0203 73
    0x60314080340c07025081078100b60b4400b080000960003c582164043d050f5611585e9610355a0000d1404460010300840310300d641c40e0440d0301c080210307803210030300800780c81c00e0906004040303d401e5590391080fa4148002c000000b50b4040c0c955441d55544000a803441c1c40c8030f42450000e00f510100d24101e4050340c1d042100b18200098420f80c182510480c0310001007580d0b910b0f102c527140c402e0300e05214204900d440a00d84480d00c0251811080130f02030750700034802c607a4482c185130382d44450b803080b13100103210403005000444640341400b104520307a45881d4280385078040019404002070304d085400480e00c01c94010031a1805403901da004e9a2480a421006201c0d0a1a07040c1c1c0300f5520310740c8084d004600c0d26403d45080303c054400201c20500b04544541c055608074040d0700701034495500c070301a2000001500341800302100d02c6a40c3c0100a0a56240b40da03951001503207000d401c6103054001480788405245e010040c2410840042d00c3c040b0b0304510340741c802c5042c113810b07480740300454004000004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 356486070 1250 356484820 356484833
    0x90b0a090c0519020730020d02030319090e0f070206160c0c1d060303070c0e07050d0e0601050a0503030703020303130311160f0506091309020103020d020c150a0603 72
    0x4541905401248280c10400708694a20640064510300002054070010482d400121881520a11841c01c4071000320b29103109640c811041045001d030b41981c80f206c0050130504400c483c0244060100c81c10104a0110f014501c0711035801c410001c3c52103031080140000c0144815041803140447c6041c5040c40d4000a4880000818a1000080c1c01c1c1c4404d030110700c07070161001c1c1c40c0d41050303904041d981c4420000c0001c40417940d049130721a0001e0003081180c540407044408444d4020002c54100780b400014007910400140005c00784401401aa01207803100e010b21000c09030b100c80500955810301c010040540302c40d81116001e50700600a0340002074001003102e4102d00079124003404052140f034202d441405051034a8014060412030026001c01d509051058410f0035108951194441c0c0a120f080d005803181d040d80030400c2040c3d91082e9440d54000031040c1c1c018540549890205c0f40c83e001603a10250000c1c01d191321440204000780703001c4901c41e802c000c01000500c4018034507140d20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 356487320 1250 356486070 356486089
    0x5070905070512101a03040b010602071d04031202041205011b170c0405060a110105070c12111e0d1d030307021309020d0b01031b08101d0609030310090b 67
    0x81c48034a20003107420f600e80954a04020086005c007281d81a03840000080c2540040d1411141100c2e10000482c40500200740c54050300c1c000c00d0b44800f94002c8548003c50007102070416824060714070450041400240002c00c043c0003540c0b400446052076160a608548184d02c02c0c3d81c000640c086403900c0b96511203942000d03d0b000700d800b1f00725915079001d11f4030284200d9002d02e03400800060200c0140c1d80045d07044000d0880540200100d40c4d9201c1c0a85080c59640c4d40285685800c8100340c00440c0907082c8401802d1140c02148d000b000940600030303059000c440d8803155540f0168100c0d81c1c0381d50100c0c021183d58000808084102801e5000c00c0c0c0d2400b46d41c030020701c9605585038141000d21541c2c070028000d80c00908580300d5041604290a41c0340003800113a038034454030340000030301103800c402c40e00488030322100900549001445e00001450040404171440d00081082115500c04010241c0510a10320180d6501e003403060780711921413141e611031540d80d41441c00800d110740c2e922844 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 356488570 1250 356487320 356487337
    0x120e0c0409050708012c03030f24150c0d110c04050622020a031820030a06050c3a09060b0d030e03010b03010e07170a0519050709050705 60
    0x440d809000d0302c0c0150030301581d0313040140c4640ca481254003079464156114021154900b840c40005c58882c0b10950b02ca12044444241915a020100b0b04401d000322500140c2042c0d0107400c0e02034120385d00080c002c40d440164142d07100c1804181160420428002d00072030220303d041003841424008a0b042d140c0c504104018800d9580380f001907015180c0f00783c120007440d01103aa004180054020402c0250800200c80340080d140c603a4404121140d01000034003076800540e5901480403003c1c5100401c001c03400c5268050250b0000103001a0460107133600a080c04103510b500d4141c03c490402d41110540c10b004842c01203a400c41d01c8200f41410364680c0001c80040100d440203603410031001038140f124000c0d0f0002042c244070700505500c400d649a4000c001c900a10500c0d000d00e00b01800d0313805260303180100740c0001000f001482c5018000103045034a04040d10003480145d1101404c003a04a00450003036950030a000d801c04c00c003403003084017428000030f080115041052006091b4000da451 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 356489820 1250 356488570 356488579
    0xc030a15020c0f0d02071508011805040c0503030d05011d060105071e120e091005301c080603060c040509130803131a0408030c03040f02150901120e0c 66
    0x4102d100e015092101c1d200c030b200300350101c9005444000b4001c1d56a0303c1880744c520340c42c1580c415034030101d00c909940ca04075801002d11889001c900c0381141c0007800d01800c11608446081c10000fa551001e20117048071403646000043c0079854083e07a9491030740601001e0001c080000f00308040d9a070050191030301030b03030049048962800005e004010300585500c0150131081018414000d00350311010040d008038003944c10031510303240c104e100c0408562500900b980481c450740d00c0e076a003501448082d000400500b001c0140301d41b0040d5103500b070080440030300d00350404150100d105603410030030280d0048000e50041283d490440d100d86090300482c0a2688a51760042c04150000c4c0c4c101e51410000c0e4004a1190340c0741032a602906032556335100417181c1e0070702100c0c90702c00c0c0351100d580244241e03001850070340303140e80b01030888020b9400104100c82400320f000c0d07031401507154140e25a10f60801102c00e240c3c2c1e9040c47c00090f1580d1103182080340c400d8104190580c0fa01408141d9034450b190680e07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 356491070 1250 356489820 356489827
    0x304080f030901140a060305010c0c080910120f05010608070206060a05010804050a0c1806050f10050702060408010c030f1b090302060309150c0301050f1503070507080d1404050c030a1502 82
    0xc070140134210038404090080351000500c9503800142d807011086130b106070004c1141c050401c3c0c3c240c0d840500c0160141003800d041c003040d4000c0c1001e03010040300b820719243c41d840c2080d0b002d00c80c000320b41100784142041680c07080103100c019007006415400c001903000600c0e29140c45030025100680e64020a81001200c00104082050402c003801c40660b020989080c065201c0603030241d42400c0201c511800c505094000880e42070404490403030850240c181703906520304003402d4400d0f902001e0101e0b00304104020001d0f0b0b886080c1b00c0c003120801c0303540d0041241d001c00900303074083c1d4030f81c0c01c1d0704038540c003240400c29865a0408504400c6950580d1101c0c0c40c0d6462151090a100e6007281c00f02001404200b04403107000c203000114140c40e070440710b44141c104070f08144101700c0e04001841342c5103001040031912403400740001d060f10300d1003400064604128500054195141c00c0f07a039008000b034a000380170820405001943c42e250b4254000c4c030105940780c480b56a01d0b810b00801c240780b1603001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 356492320 1250 356491070 356491081
    0x40e01050d0c03050f0d14040503120f0c0f1633120f1d07030519060b0d0f03111c080a0b030607180f0b030403030b03010b091f08030304080f03 63
    0x202c4a1000940d0003e06903403624810290f00c64480d505c0800c00e07000546260a0b56941070300c1c0c0c0050f03030301791400a8000d040c01d4904a8003000c844d40260f01c6481d00c040309100c10403001000f080700045108105015121040440e0003075031641080d03410809195500c2d28a14482d07500300603038504078402d101ca101500c0030201100f40e0303c1100c0c8a446c150300501300b9107044800c00e05604115052203142c3d424048034001c1c0403440c0c2d01c07070b603c80c04020b115400210100940e22001d10050003c42d0003140005284120305000866000c00d88408840d10b80d40d400c7c002061581002c0050314001100340600084c0d0080304501d10308003450300019080c803d50310b0200380005842d500c490600c2e2405030485440d41044240604070a000504035500d181c5500fa0201d00d91032841d075040c04950010b00260b0840d1034aa500780c000d000f625029a0701503581c0c0b45180c0803652401089030198000d000402d01180d01c40020300494291034000740781d01c1d4000c10920000451080854a4055000d900503440b900d49 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 356493570 1250 356492320 356492333
    0x703020d0605040c031b0302090c0f0a21050a05190b030c0d14031612051603050901050c12031e01030f0b0618040b07031b02100f0f0e0f010b0303040e01050d 69
    0x1d03805c0038220041101011a40f545030561020682e0f008641c800b00d641d9034103214205510401c0c03050000c40406010110310305004500d80e0036035148808551038510300e50b0340c1400848808480b40c0540c1612101806000d100c0c00390020045c45098100340700b03540c000c40100c0d681c3c00b04000041c0c00348080701c14503401d0104095a542400d4040c0c000c0e030366120741040d240c00e400124800e0946582182c2614955158003403c101e07144814424001d1842c0085600d05071410740000f00700c3c9061040c20000c004029406208001094151404140d140d040444c010910404180c1421040306110001407010540803000c44800e0382d032014601e08140e2791b10001c9185141c054a006030000750007402c2c0020004401d00d500d10900ca2a60100306020b00095480202d58418082d000540c1021640d207107103e807503800041e0820b8410030041084211010340384226201c0c000000c1580d0000d030502290300400f0b0140c5290301000301c2c002c0d4106801d000848060740c0040c0f0589219483c0306210004110b407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 356494820 1250 356493570 356493593
    0x91506040e0304080c010e0d0b010306020f0903060f01080d0c0c0b090406080f030301091505090403030f180510051f14131404050d020d0c020d050a0c0305030d0e0703020d060504 78
    0x340403041d41d40f40c41c0d075203400302d0f6589407800284d800b003540445c10304551b080c0801c03101d01080d0040d48985e00d507440c3d038032014000e40c407400451444010401085001d038a00700030b2240030b80101e5070120f0349980360100d41410003c030f40d44a4000c01c1451207060740850200310f17001c82510f1074030000a40c0c0d6050400024010f0540d54885142409035540b145108440400514100e402d003130303c288842c4080c624031848a400c940601d5038020921400b10340400c0c401e50117040500144000000c058240c041c8101440184801c22034090b031150000e540040070341e01880e5008005420016243c04c02200500d04c0c2c0c0505c0d00a9020f450705ca103032000d2484da680300b02440d0705000514104402503400d10105000c5804444c180e440e84144050450020310000f800108001e0a540e80d940c1c000c42e80d401c0140ad00100032068529104100b84000130802d020702402c000c44c4102c00540d6903c10103052003054894050460010340c01500c7c00300050703260746c0d001001596120500240640d11841c0184001d41d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 356496070 1250 356494820 356494841
    0x30b0d0b06060d050c04170304050112050a150b1e250303150902070212120409020d060f1203080f090604030f1704050c010e090112081e0a02010204030b01060809150604 74
    0x9007440e05004174007000074018016210745c10119201120740c043c41755500d2080d03100710390015040e20040d0325403a2031a48056085440b4080200306044842d90018403a50184c0243c460900c00040d0580003e01c6034003040000304500401c58103003850280705a88042c1d601c0034450060a85ca4403490400d0320a512030301d82c03004205880b21a183e15001000002d420038001240107120214100a0340c041c0001c03442110b944a0300040d00c0c2505089244010350814000030380304640303800c0003007154034003144640068112800030b1140c09456060042059202802c00c04102c0b40482c18411049004138407a540280c260500d00303a03402c1c0110b4111081031881c506602c2198201c0180800c011010400007143c0400340c3c0d4400541c1400002c00500320404c1c80345900b804072450000300059107900192a00f041c184401030b800c64514518484279500420920b80180d500050500c2042104d491940c007403c141d1601108910b02031940c10396031040c000c0f04030341403101100052407941d00ca030411821032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 356497320 1250 356496070 356496097
    0x8030402030a05192f0f060405120a020a050d030503010506340b0117030304021522030204060b0703050a08060307050a030b10090209011d0102070b1204030e01030b0d0b0606 76
    0x11001c0b50602c14030b01101500031030300c1200f01041c0c0c0c00c9605d81c110285100c1c40d01401950b110f0304949081001c2080c001e0030302c6402420034000013842d60350310f040388147c000079980030782000e40b03251041054a074219045517104a00b038a101c4c07004a07034458141c9066440c02c4d04d41c280d46501c0d206040300c041002002546051805c4070360a05101c0c4010800707090300e4450802800d25036280d42000c910748010081743caa85600620009000d4540001481b2072103038501040d510b00415410103889080e580b0321092a180c803501e40c03c04c00c40c24540304040003001000c001604048155a00800601c5118040804c21424002090441d501802454010304000b0842078000d41d491402180d1450211082d02001201e00e100083e00c1045008407240114140d54141d00480c19000d03106d10104050082030440c8203807000412401c016900402c800c07501846143c4240c44c041c90f0003070004242d402218109030a2002e01e60709038503401c0071030711001c0c0c0c450000c1c1040c0d40e800022500030f02a040c44503440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 356498570 1250 356497320 356497333
    0x4060e240c06090d0f12060305060907030309151d0f100f020105011203020a030c0602041a07050f1506100e10030606080c03070906080711010c050a020c0a03050a08030402030a05 78
    0x91080c1680100384141e41c190a9030110b64074611400d4841c00c0000e05080030688161600c00700c54814190310400f424941000100c8648130749449280c0102100c9003002988081c5052080c980c0105d80c0c00e0081a002e0f2306004040700c0700100804c420b01031840d240f1000450034905c0d13600e98501e4851160300c80040c0482d80c078020140d40080003c071003940d04074050b501e45800424100c901881c0d00600c2e80c0c05400500c076800003a038044074101c0c0d601a095401c1c80c0c2c24800031801400f00d540d940c0324007500074065501c0361400c0c100743d800d15441200c83c0c456941b0094017100b100744000e20342c0360b0120044994205000000710709a55032038450324002da10030502c000e0f050580ba01a801074007a514107680350005556007000b9a81c1034071040d1003034004254400f0301001a9480780005a42c06081d51030408445940c00f503040d401e490080001c180800c0003c00e5003464207504100c076a00010080f100e01c140c1c01d146844454641a807500080e00c0c02400200040a40d2000c000c0103040e558060101c036076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 356499820 1250 356498570 356498629
    0xf0e01020d060f0506161a010605131d010510021002033105061f0b0d06060e04020412020d03050f0d050108010b09040206181f08160507050304060e 65
    0x3940300501c48500c580c0361020100345000501e202d04180c61010704024500714107011820881c6005e0744d011030707400d00044600d4480d90300e4140403500074000c41d21843e0711001c0e1540000105281508403490001081ea40c1152076040c001c0c113541105d200352114458020035100483c00c04003020f00404001d80000180003000e0f00050180d041d1118041103a080d074505138059540e0400e40100c05000c9034031150106049102d448100c04828402540fa0715100340e070780b001410300b900118810202c1d20b59629003041200d030451001800c0c800211807c618140c00c20b000d0380c210201f0020301a00400c0c980c42c8031000c243c01102161071260f00146840d0301d510701e01c0c48030b07c064a07090107200215400d1210082c85820f0150303003140039a600030101410a00b060110400341c240b01d80665502412446c46c807a1201a059142d00e6400c03220755842040c2c1c80e114080c0000c03051000c1c8540308105040200e0804201e001c0107640644000389045141500b0000018000c81040e20180c0c8019a50111400c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 356501070 1250 356499820 356499823
    0xb150303130515070f1b09020c0303250207061b02040c02011b14070f0602041a0a12091518061a0f0f0a0b1c020a0507050d090b0322051b090c0406051902010f0e 70
    0x188103540c641e1800d01002c5002d0203933600000302c0d034040c0001d81e200795024459640100c5100080394440607240e002d3712142d40025054411a44881016075582d0525090040403101e40f0700d500348003424004002940902c91f150603125052000d00f0520b01220540c080180c1c54045900074480110440e201544210780501d181e8080c00300400405e840c011041140603090080c1c2c1109600262000111501c1040030801351009000b1400d061100302503c00c00580f461141c110001003180d10564881c0701e040c1400800c147c3d8980c2c0504c912860040505203644d04200c0a09072141700021503120800035503410301518803190500d04050000c15881d0015500c94003030141f150280c800c8800d2245892402d480c84440c5004201d1b408100700001025494840c440607402a020149502ca41640d520b4180c04d100041e4a8440da111301e1280c0141c480c0341140ca0760b50005100c5007075525146c540000a421403091b402d6401c0c3c440d40b14040055628001c1d07001d204800c80d00b00c0f0a10400c0454034086 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 356502320 1250 356501070 356501077
    0x3010e1605030f0105010803032404050c04090609050903031f0f1508070e0307090510091505040c0203180f0f0603040c08071e030b150303130515070f1b09020c03 71
    0x154028800e03243c0e10b41e4581e40c140207607412590444050351451b12407513202586e003030250f140e80c1e400141030905d1a00503202c511526128041e1601c1c11078480b424901c0c80301c1590784030781c00a00300c02d0501c02408108400441240c3e00411031000c2c100340f65107070009848103ca00350b80507034452a0210400100c03581c04289541005101e90707070381d80d1980d0b0786a50580350714000f1208160941c2c00860b05021000c407a0f880795400205c40150340e81d21300e0b0b442622030b0a440c805104030480404024080060b07040602a100480841d030000e5820b008443e03071214110980e03400c0703c907c01c82c0d0119600703110f5217502520038031002028019950300d142500740748007885d0703091041031060b10541c4400030341d60005055540243c4460705400040a146032508000c5141c05021080607400b0107204030f03810381e010001880340c40704c241840084e903031030f10301008454003440114010344030742000740d02c00081001e10b2004241d03500030392908801c2c940d40040d04803100c40b608031550580c400a00d0071482840013024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 356503570 1250 356502320 356502329
    0x90712030f031d1510170a020f030c130203040804031e03170c0f0d02090415091401030f060203070e040203090a020f0a150c0f080313061508190203010e16 68
    0x9010340c1ca1000c0e03150380c3c05190840300e0002900100d04200704000b0100240d600003940c640145107064944452101c0b02c28040d204400c44d0703000c800b514086080409090704c08010480c013400b1030400b1903010840b903420300020003400340e500200041c20006080c0c00e407405580c00c1704112003d040d0300d40900e41300d10174909054000c11603c490040100000f0032882c0d1052100004250411002400440c2c0b0f9801c2940744402071502805080b0241c0c6580c481c1c4d5000401800e5690402d41c540492041140e1303e440b0100381503a0050b0041c0b0101e0b580001d0309001c4ea5100301c1c01680c079622001c086643d540f0f003519855000780004203004241100213640d00401303008803295115841510200554503030300703124140c20640d0850b0404444c82c001c1c0f0b000704030680100751980402c1c610381d884030030304da108607102d00c01601d04210701020311000f48036072501d0324210742022003240d052400495803030005c8002c2c2c2c800a0360401c2e800e011500c003904040014040e078001c030b402500682c80d00700e403901c1e0107005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 356504820 1250 356503570 356503577
    0x15021303050f0a0312020d0b130219020d0e0114070b0115020f0102091c0203100203040305040f0504090b0f0a0e01090606061b0f030f1719230c03090712030f 69
    0x4000b8440c0c03000c24000b070701d2503154070b804000300c0c09401020013940100c0c1048541070394a912000540c1c84001000e01e000e501c000005a541e4540b4164100240380f03249240119408135002e102039503007100400ec0c01d05002d081140140b4209036000700b80c2e228140004000352880000090b031b24400324404e0202000b5502510b115050540c1524200c3c001c00c1d6141e64021050205c81d40c500301140a040c480314005000d0b01c00e1701807000c0d00c040581e03109407011000100c00140c1040740c00e2012148030060181101c0c18096098940c85032104400301901c03090070300701540e0200d8640400d41d80042020b058201c0240204078840c2030508c01022070f8414031010400811815006c20711030816800d10035403025005900c100300e0b0714100c64100141480c070f0144003600950310704010140341c03d184620030000d030101c44084007060b80000e81c1c20411180811042010b82d2030869a1000c00156100703000340d17400c0d0344036980d0420380345c58600a58070600d521000e198205050660100c01c040f1140700c00e45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 356506070 1250 356504820 356504833
    0xa030606030b06160210050f0714060114030a0605060f370f06052212020307061e0c020a09060b07060b09040f120207051f02070b03060a121502130305 66
    0xd0600103a0b120b41c4c400440c468241c1038150300145001d000e01d1801c103c6900d802803c00c42e024088a0f8a40c2c4581c0080c2e80d401000c0320782049441041101d00c1c0544103142c04070404601840210b46d80329145000100b0407520b420014181e91200c00310607540349001080950044d1001d000811400c41c8107540c0c1c4d8586540c0e82400307500303820340780c0c03c2021103101700d80541a42d850408100e9180d049900f9031810165800c0c181d4620001903101000640741012458800400078410075242c0075813a0b00c030006020310019080c7c0288514081458055110b0030582d0300d0040c1c2e4800142e50301c0058009031600d62604101046500121001d044043d120b500c007004450028030400c0250031048900070485400421711000152440002640b216090300440d1f0300a42c441000800c002500c112840a40301e40700d1a0564035a41048150700400c040c0c24000d2540c00c00d0b41c085425404075001e040c015860380340d92881007114204900740e50b030312481011502d036441640c840101c10031701d00c416113451055a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 356507320 1250 356506070 356506091
    0x904082d0421030c0803090111040b040503060f04051b011106040305120a02130306020d020d0501170c09100614070506070f030c0518011b05010e1006060906050f0d0b060a03060603 79
    0x220750011100e50541c0b42c9080224040c0e0307a030003591b030004001c9400c0355200c5c0050100c1451803800350028045408841e6190781c02c0c078050501c2c2000003459220080034880a200c00b040011a6031081c124001c0400c80e50000702d107006035a0701d440b050500c0414464a0100010701d40d0050140c19500e81d09000040b86440d80200c00c400d078083c4000440301d821425208000003515603000b03000d1550000009400c0c0042c02038064100d803004da00c034a0015522803d8030100407020b00000ca051901103882001500b0502c41146440c0c42a0168005115001449080e4038501c00242da0165a200003100c01030700d00028000c18582c5184c1c21000401e04144000f03c04c18091010344d44010030080c130394504180124011540c210340c440c20005000f00700424100400c0d42805210080c0392804010110200300500e07000440d00707287e01180410140031414040a41e1010442e540311070003503052912101c0205290000b0182c2c0b07c40e0031f600101c0060010042074050704240201e0309691003c000340b0029 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 356508570 1250 356507320 356507369
    0xc030c061012030f0806040b10110606150301231f09152316060b0906041b0c0614011202040c0212041814010609080d0309020904082d04 60
    0xb0004000c000c0784190b445904894401e0840c59800309005002040c81c22180e408181d480701880d004200040c010449852440c0c010031007150000800d544440c0100310052802c90700d40010700a409114840d41008502c028035541840240140100348440025500b001d01788112140c5c0c542902040b04110000b554030070000503043e10b400b031a1501c240101c403022240603900b81c00d05212070004801d001c0d0a5034a07440441043d0080c1c403581d07000450101d0f000400150302e1005010314401d5090440380c1071140000d4411b13501d41c000c541003000d4508030500d0100050309004c0911000003034007500024548042000100009000b43c804000c5d040400c04200c0c4c444207010465080c0c18002c1108000010100c0480884490400310001c1c03100c0c4661412104d0700001ea1110340021a0741c1002e1102100501248100400a0030100059207607580814807880f8001d02c0a0034407480880e1071400c100f061081100075002481001c501a0907070070074110030b50402d020b166080141c0c01c0320080c3c900038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 356509820 1250 356508570 356508599
    0x2120a061a18030f010c03020a0201060503010204240e03030304031e0801030209070f020307060501080115080c030d0c0206090d0b0a0b121207080c010609020712050901120c050c030c0610 82
    0x400380d210616010301c80c640c990464000040b010b405105128180040c00340038442c0006032085942c015030381c0c02c0700841c0242510040d8018511030303441000100700c0600c1c03401201d114a0355a60007001d00800e00c20066030000358203070240d034142c0400420801095404085401c01c01c40f484900c010b500202c407400c031211803090000030741010150003c240e800f070040301428a10011031048078075201d616652402914030a07400198280c1d100c0c403003880d10058030b60103031018000220081110400d0240001d94a040c0301100c0300034844c00701603940964590401b1500c0c198005485940703c60403a1408a2540c081102c02e80e03130180c50300f001d5001a1920382143e0704055403c400130449803000180609040d0b00081081300c3c85201080040c0f5041401c1c041c8800800d082403005031120058200720b500c0403280c00790076082100401c09074a0507a00311158600720b82c058180003e680701a803106454900c078000b0b06281038800810102c60581000400c03910800309003e00590f00380e9543d0544030410b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 356511070 1250 356509820 356509859
    0x311010f03092d0206041e06051c02030c071a06040e0708060c16021c1709220e01060902070c06020304050303033108030f0114030d030203040204060902120a06 70
    0x10030308544007024503d10b481c254842e240810343d5806049650000f07036564856800740e000200760095944400c801c10124100401c041e04082c0e2600a01c0d0420030145440c244003084880ea010000c24018030510007590304150380030582218102242c20104081c80c0e048555620a60501071506180c8001003403c408031a0810000e1040b44c070742100c41807240d0452480c046c7da074002c200c080c81c003581c3c400c0d0b14040010b000011800ca10525802c4c40410111458201c645610b41008000d0580d11401c1941c0b022402045245402200408155000e401e044500c0740042d8200003001c548902d00358010320340244500c3c1d14020780350340c403a170985e00c038021841129810f4006100041d00f184200741c0c0361404030101e40c0c00c1103c50050009103000841080c50035070b102c031004410403040540307000d4524050301200034800032445911001070307a103201e5000c200c0200354000c00440e04549843e00120040d0494010554070b40d52000803c0384009422a500b020044c06c014000a90188180c40d44078810f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 356512320 1250 356511070 356511083
    0x50106090b070213021e03070807050a0e0904050f01020d0b0a090501050105070b04080d020d1a041a01031a090103080c1009020f06030c3105030f0a06150b040311010f0309 75
    0x200311038007040f0391319100350b12400c9a9030702001007078400c064210101491450b407080140d100d04001c0c0005000250091400d410f0007401c20413080e0b032a400181500e001d60041301e84043c5540e0f1071516505000c01d90301481e48940c00403a144411400c1b5400454004109544450085607516400d45c00d0342c6080c85450701081c5c08000200c00314013940e402c913a025004d195002e01d01803e980c0e0b181d0499000d8042206a81e070b43d890800a00f00c07000c1d111001c1504200c074107118440780610528040c5001c48000f40c141035440c100d00140102c1c0780c1c210482018000d010108543c0c0d20f00780003d0652024941890f9406070750100d0450040c14425841c541350041c0400c28044d03500c5040c0039050344084c22503681e0071414811401400e012034214986140350303c00b038000c00500c24001c012036014a80000780f181c0c0090190003c3c1d0440051242c5459030080d13030114804014030b6080020361029005028502d80019010050102554070540103806c20b0781c0b03003110030b0031460044044461800c0002d181b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 356513570 1250 356512320 356512327
    0x70e07020a02030d4a0a03080403080703080108060f0106180801050f01080609060f0a091a0709090608191b0302030607050a09060f2c06071406070509060d150306090602030901050106090b 82
    0x10f03104040002109000941b483c812151280c90313924081c1c10031f500442e6000d500041c42010035600201281c01810910014420ba0401254605540c0c1050080700c04000200c1d140785407160014000310700510050b4000c01c8103003407140c1d02c416a00c109004501092042d10080b0384902c44c0007840318841c0348081c1c04000701c0c0d120081c01c10058900c141c0c06480200081240007841001122101c1c041c0c0d080b41c5511000078030304030880c41a21015480f100c2150411281038a03100091082c0e400055400b44581e41c075440e0041c03003c0594030990704041d40600c5950100076019401400034481e0840b584c603003680c42680c5041c01c81d1800d205040b040c0020f000e1741a2860b000c0200d9034510020b603540840c00b8400322111001c2402034122007015219400080404806983c1c2803002a40140840c60b00c280740c0440c00010803014480d641c0c6922146545400d680f1000c8400094400559445581803001c003106080c09800780d0029507820089501c4c002c0000ac0c120b000c6d035046011103816003001801e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 356514820 1250 356513570 356513687
    0xc020909030901021f1e09051b0f0409020315090a0b1b09060a020c03120a110607080f04170a030b010f08012321031911070e07020a02030d 61
    0xb41251500c808205e651a00c032108032100040b0080d10b03003891200c0d00052140fa440c10150b10f0520b40228141004041d600d0400c07880d200c082c2c0c02901218250b4020950180a1000c40e150118400980a05403807941c18415001d1000c220b40400500906c03c00c1c05985400c50401c2c4130701ca2450b88029010300c10070016110b400e256000e8000041c01d40180e41c1c011100300e0200303092500c5009c5150184000044c094030894109d81e0801003c0304003001080c03545443c1d50080d00040001c3e100c12a81d5002200040402040f813004803483c03898212032940310104010044c010340172140c20b0301e020540030782a40c80100d2203040020304a480f900c441e40d2000c580c02007a4440d0521001000d5006065144c6042c400303080b0340010510f40c40300400a640d075052102e03454000000f10003005042080c503208265490100194150543c4ca60601031452038459050580c07802a1040000750540501012200ba03a030704100e00c01442d0107000c48a0800c0703c405c684040c91069402c07116111000c04460040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 356516070 1250 356514820 356514853
    0xa0209010f03110904090339060902120114010e160f05161703010f08060103120f0309061e060504110315010e0a0b03011e081908040f03030c02090903090102 69
    0x283c42501030428074241c181004181a6500c038081034004c181c04401c100d01c1016102c1141e80c600fa03070566030313400c40006460142000d030894074000e0309480c0c83c0e010031001e540d0341084004050026100801c411180f050080058a10034031480041d40060000030700b06405081c1c0c1018050016603951004135440b582c16501070700500c6403062800b201c01a64070000311440f010180f02180c42c82c01544a6240013080c0b95007403902d800c0007a16402c684010800141700030032401c140c40c110b003001040c168052a0407002011303c070070043c02070350502c040c0c8000000921850810010081400c0c801103807504180030a444045080c0c1465540810024103990828031035141c0d80d0405152100c69242101c0005417414060b400c40941c166001004018180003000e1029002d5000c03e403000d542440c09200680795a03080d8103094180c44586038000403c40640c046901a0409041604e0700542b07a040080140b00f285004a025424140c04030f2802d280000554200703203c164000d014401c480342c00f10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 356517320 1250 356516070 356516081
    0x501030201020c2b082502030708120d09110a03061b05090609060913020310092304030813200301060902072103090204180201180b04150203040512150a0209010f03 72
    0x40d504201c040c010014004010400c1681071560041800c0341001b1a004150900160354000c4c4860b5010340c001c0c0c00240b03881e0054444216000710009518042420200c3d44070000640280c2d010003286004420880d00b540003001c0d00c03446030b01c1a580011050403e6943d407045e00039144c0e02005c10301c21200716150240040400b09000b800012a091000744144141d802c00d90340c0e15580d500166082c84022082d00c50048820108203616494664100801704032140140003c2e0400038440c00090109804102c5079040690001b40100000007034002c88041c16501804280320794204000050450054000da654060f001408001d40e080c0d08184001e803c06000c1005083c5901c840080d8050ba4407442103005414021064034103600c20303031000419007484802e001c0702403481075105000240e0040c0c1604d0030748644424242d6600c4021200b03030b00d0350040c0d41c009503110071044d034013040100c0081680f15001d4065a0034101503101c6421075000e9001e40c02c15240010100000f0692144c070a4105 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 356518570 1250 356517320 356517323
    0xb060d0b1801171c0c060209031627060503030a05070203070314010203011d0403020c090c0412050d0807051213030e13050708091603170f0301090501030201020c2b 72
    0x49180c240400400a201c400d0036485009500c0260030211036002c0180210440030303e1500c86411080804c060250640310030160290400398046000c28103030300c0c100701c4120000004030001290035500c0c504401401003d00c00d409000820601344003034103060303010b24425121300401460401c408aa01102e40d42c111300401c0e40e251003881000804036013407840c2d005980c0b030001e0002da41e941c10401c0040c500f219040c03e8a01b0403254030108070110b54049690601c582c0c0c2201e90303a841d40c5030345401804031701031a0000084811002d206c08200400081c54182d0001d032600e4190660307030303100400d840c0360260310a0ba031800401000000e040e005101141c0391218032a0030030f80484a20703000850010b000c40e809000b1215901d009000000360894001c0c1d9100302210010260248243d1301390794100300342e100c010403140812103c08161501e41064403e00c80b010001503440c0d60f510940d10016000030702c030903400b60140fa001460b6a0038890307804a10f01b030707070315880e0003017000302080001c08205904030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 356519820 1250 356518570 356518579
    0x60711040f180b1f080c0f090421090515120705090303040303081f060305040302060f060f0105090301091406070e0402180f12030409020702041103090a020603180a0b07080a0b060d0b 80
    0x800c04c4c1c16484040592028000c840c00401c0401d2820013440004034810616900c5020302d882003000190400200000c000891004171030383c4140c1400c1a12009203a41020b5805a100440744030080d0302c3e54043c05444e15880544086a1103068041e43d40e489403c1031030341c041d00200700c1400800d008054103500020703000304103079244070160800052440da40c1c04c1075000940b250248814580c1c1004401d411060400c42000c0b103042240014601000452480c1d060240104a129180d5401c2d07104120710760300101420001040d0344101616500b04480410208484200000b980c3c1480e109903114040049054040c0d801407a0411541c20141e80c0c04507440711061801c1c155208060014200900e04c102025850b031200d403040105841c5400d0000c0006a41071041041840000918480d01c0e60180c900359965214049070808400300c4042940c06440b40c0e00307010301040745901c00d05124410b1a900d2a0081d00e4241503d0141d0707a10702406a8000c1c800e00c844014003109074800e01c80d8443c01030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 356521070 1250 356519820 356519851
    0x40f0c0b030f01171b040c0e0402070b1605070b04060e03070c080c13090803060d21080a110a080411010309050f010e0c0909060103030c0f02060711040f180b 69
    0xa40c40345003035100322a541480b08286004002054603c60395200c03540f0048068041660010713800b800b11001203010341d00c126102d04020110324012892849007a0300540159500c80282c10312240446013546c03509200424100700226203031051042e00c1e81981c0c8003040c018203803501d4031000c2c0500218011003d80b400100f114100061940740400010000300300030300280d0301e41034200301081402104c1318001c1400c01d689403001413281c404507644450700301c85c10411590a801c01c00d108401088140c2520720030f0700c0301e0203201c0313410079405031040c01c01381800c0c032028070354030040003142c01180403610102d0a50008180018a01220f104a01006140004181441e6100e03e480c01c54510f0300b12a040e5550b0844480051091201e812000030035a4018107a04080281e1342e6141e00500c000360400400c0f00d482001c102c561100c000d030f0740d500106010384884250400d075481550115070300f407080e40340411305010b280c1c250080310b100c5422904880e038136070000c1c0c4600b100200c0040c80c0580d00501c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 356522320 1250 356521070 356521079
    0x2010e04090309090c0f021203130f050703020406050a080615030f0a030801080706170f04080702130f14010501020703030305040206070c1d070e06030106050702030703080409020d050c030c03040f0c 87
    0x103105100645001c0e507540380340301d4130b028800740c221420142e00c0c0d0204510008203145a50300000c0000c144405030401d55038a5540000a1900194140b4000c0034440980030507000c3c041c0000d1410160383c022a03040042580d101c040145c1003c151242c41c1554000c9000180359444c034030440c905502004e000d4520410015040b42d084c4242c009080b07000c0384424006002581d4200281c0020b845a8101140700c82003008094201000080191000c813200e10300140410240e802943e40043e0b029241c54080040340346460060609118261a410301c0c08003491400c484480d030131812528180c002c0c021450642e1000c901404000b002660006401c00c540310005140000c100300410008907015003803680900c035410052800fa00600c1008001c5182145075603816007124110b48084c142542d80da040751000c44d003072806541c00540701d241d0101d0300150525030f94000f0110400c10310300c1004660343c1c101341c2c82c0103408245e0f00088540e4090000400144007496010125401401c0d0181003a41d503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 356523570 1250 356522320 356522329
    0x3060e0108030d0e03032505040308190806031506010e01090f03060615080702070b09011701060206150306040c05040e0f010519050a0513030f050919031202060c070602030402010e 79
    0x20780c062541e90780300040903520f00000744030781c03c104900840507520307600305210065075403049151388070800d20300d684440200600030700480d03005540c00004207841e200c8140030500d00c40c0117282d440002c10900382c00207005141c040b0751540008880f42170384249407914001110b446a240d490b00e4140001c80f680410000040740216000f18442d10011556604040d11800c2c029031542c4191f05100c0c513202400380341600440c2c800151003550308400d03111842c51004982881180c40c0000d841c0f40110000324100307501141551041c1511203800c04000420414940d550208980143c181250b6007000d1001e45001c2e08500c00c00c00b5004101c0d0b014501c82c07200282158015524000b0960b005e280d406014036407806090341c007032140706040000d4039000726000ea000003950381c000c041000b10061190454028010f503240484040c156401c0300b5881800300058a0280c0801d9810501d541428105948000b800c644110018940e403420506a581c03580040d42005e4000c80c1400442080310074141c94 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 356524820 1250 356523570 356523599
    0x9130f080a1404080f190f060504060b0d06150602030403050303011a121e01050402070321020c0f0303011a2a12160b010803181c170a1419030c0306 65
    0x119131001d008490800300d051454025404c00342801c0d00380398034000f07001c583d041800400403a0004400324140d942e920f841001003141c882140d500850103082ea01c1400119804000740141004035002d000b5100e8005a03541d0140d40b00041c610713070003040144800b12420120008080c04410010300705040e44002000c400000c651a017901c007510180c941d02e540700604440d0040c20182c60461800303609481c0184031081c022241d0240a0355054408101d90459045494110205041d0f40c0744550b10582583c03070f030780207106181e90310100122204a144940c2d084075659010010700c0d84031032260844101c00350811030502009406003070030b881c01e1802044010301a0b50100d41000501950a14042d201e404042e004030800d50300500c40034032805e00591510a002d20704a03100882000103c600a0324640300e0407000300000c1c0b801145419181003600a4090115540c84032180c00802000a0900303010310b0b540c441c1c01000004103000214000d60007580c4100c11483c0203d0004d4480702d0f80c924015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 356526070 1250 356524820 356524829
    0x11b020d260f07020f0a080618010b03161a0f0409051f050108010918120503070f020604050304091a04050106051c090c030204020f190e09130f080a1404 67
    0x3440c50940055124900300800c1c045000c090401c0c10041074141014a83c015268000d02508000480480313a80e9003044100050001030100c1d0f0131450b1100c64644040c01001d0210940c1d820050804160b160209a00307034040e234030040240d5094035104041040d015800c41e800d501d81d40401c9130220445c01c8400400c0a0503c2c3d07000451642808961450040e40329a0300c042421800c1a052080341c2e84a0651411601080c00100e040d0013001703103200b26900c0b00301000702a2683c00d100807408680040255100368001e442e0750003c400c1000c010ba840d807408540060081d0810081400030703d5699100300468480010b104d9100740c000c0000c901200d4083c1c0010000c9a00802c1a0070341c0c06c550320b800400c10107103c8041c440000c496498000552860100900c66500411925543c0d03030031034190b400c441001d003c109001d910510b400342c400d02c0c0015640340982942d100180b034107542956000b404641c041c209200a0420740c44003140d0307401c6400303084c082103102c5034200665410400600080c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 356527320 1250 356526070 356526083
    0x2030f0402010e0d050d03020c010605130b150a05070f06020702101709010b0a1a07020306100503100207020105090d1b09050f010f05030a0605040302010f020f0306030f011a011b020d 80
    0x103041034000940f614514042c224850000c0c454a82e0018402003400e9049a486e414050303101c144000c0264003418039508820b401082c100d4041c054010940c10841030b820055411413841200443d10107004d1064030042c2000c03403030402000b4002100006c0c1031900307d0240c1001400d2410350350000d40a52060040d210000d41c421410842ea403c204081a4200340440001c10070000c000012900f625114805c0d0882e140c01041204110414482101c4500754000c0c183c070146c0c0382039a0391000d0396030940551800f80c81188078040c2044803510843d03c000da0140c449605150f1030307070b082141801203481c2c12141030600c5088150101c02400ba041d0141c8000381c4c01107041d01d0151100300494005a0041e02c1800304800c0030001074070003140c54125a5080500414265620b0030143d0142c003582060750f0080d440040c41c0003004851501440c00b0305020ad00381c03041d4030b04030f05c8104d0a941c5216504840200e02ca040510290300494071801d0752101d00840a86e11840340e0001004004901001d5461 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 356528570 1250 356527320 356527351
    0xc0215030a14090d0f02010e0c0108040c0f08061e0114130603150b0f0301060e010b07080906130501020d0201050106050319090b0c0a0906140304031b051f060e01030b040201210203 79
    0xc0e0000408160b1720081d05c000c100c51041d00401c0b030780c0d03904a5548a41070281c40070105060145141d800000340c400015078160303075a500c10340d1903a40d000031a0f1070540e8182e5038140e04030a450415015040700c8111000500d03401c482020001002e000545c0040070540c1c8050000002c0c21001c0c003035088140d41240010440c0004e820301881406489582d4030a034900740302403190a90360341c502030664003c0007030301c2c0d02c911035490115124402c5401c00ca6100c0004a4403410000741c00806005a070000e070300362800d0400c001d006a007a150f0038000c3c03c012400500000b08152220304940d115020401c50200c0e0081d81e07902e0fa040070600036100e00c80110300000e05400da00d07070000c2c12000101020329020b41c0d1800c0303400b0718140301c0c000980010f003009882d0241d644c0c4081d2180440c410f241d04407055031106040040281c0c40e0002c3e41840400a500304440003032011261143c9a048039001081c0448070741d960341c01101c0d5440c4036040441c801085045018880c0128400f8500c196248200d2420 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 356529820 1250 356528570 356528593
    0xf06010216030b0604110403080316021e06010510170103142406030c0a0303050f21070903030315030c0317040e0a060e061f0804021314060405070c0215030a1409 71
    0x7503400c07090100381c02c1c1d1007c00003080010562021a544501c80381d2a202c180c10401c41d0803402c0004000224902c060340c80c1c9100061000070a9842c12181d003255141540410313610243c801e240000280c60683c3c254400400200341414045190f505445040d2040c50b803840c01040340c1086540d2520303884c4400a01001958141040050b0840300200d8501c1c8680d450b582c1c008000b441001d000b690f0b85000410031903014040748602d102820402d98a42c40d251074068001810704440d03110a0340001c3c181448052030100c820000b4041c0c9400003041c0103514116120383c101080c0e54845810015001c020004000503000409030150341101d0011810340d1501e4400da19000c1c01030304881c81580c160208800c100000e4003828015400e0f0b00348103003d6502c60001504500c5001480300440c2d0600c070159280c002c001c15001d100f92402c440400c019110501c007207881c00e521100c001e420070704d2129058078040c6c0e0b0320050340e80070043c9030011400f4080140018107a407016034901d1819441040a103d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 356531070 1250 356529820 356529829
    0x2120a0210060b16140106170a0507061404170c120d030e07050d0605062e020625050d15030c0303030f1515021002120106260f06010216030b06 63
    0x2c01003d00c4010a8181020300c80c00746800c41220100500f200c5106034160925036003074020400030107180c82900810416851055107401960808131100e006000c004981e00707000d81c040341c0c8600e601d0072859050506200078031052100400100e001403203200c064550503070710280502e036002c43e4403002c4c05000c080040003030309031601e60b55201c1c09600155414851501c131608424800b03034000101145949031100828401c48114454104512040042c41c411250340c0b003407103800d031000d542112041d41d50160940310302c1d41d84490344414690350319001c00e18103200360050414200d04040004070104141d03642e02c1070340031550049070502d81c2810100107241d010300c00c0c9141000f01c1d500900400c4110071262110340402e00961540c00c0b1417902c40c034041403082150f0080c10400c0c0703a04554500c1d80203025050417009106000008890388000344034850707a1000c41c0a600d52907071000d0000e4613140d008144542c801044a411072241c0009075401d41040e049036070083d80a5507070301006090034420b21 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 356532320 1250 356531070 356531081
    0x1050403050910090b070314070203010c080615030610080907081f0501090504050a02332a03040603091e1a0a0618050709080304140906010c050c010f02120a0210 71
    0x107201301114200410301072141118101c40c0e1614104000400c4121001518012004041d41540c689101c241c420354002000368010300003203406404440c007040240344140310842e8120f4000541c279a00010450007003100303035000068841500c10070381e210103800b03241c820004042c00d2280e5060000c008540814465a8050614543d040c000da18147d120103584403400c88000b4010916041c56551101c2106880c088841100024290251980c5440300d0f8507000840001020050122007482d4001d544600d81c0c00a80e4450141d4106890284240d00078800c840080d558002c0ca41202c0c140c825080c10201500d92240012209811448583d007102c0d090040031906450310b08141804010303c0582d80c2007250130818030108156442071070840741440503621026881c0300103c5d0108860701d200f031021224030030580310880e180d5075080045414032241000600281c204800681c078075441034200c00041c503064011280c4050801040c0c2c070b242c1d031000d205080140c0011440c0c1a00d003106d4000c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 356533570 1250 356532320 356532349
    0xc0f0901081c0e060403030c0c0806040f060c200f1c141305040603140d0302070803060d0228080f010c05042702160311070303021902060408010504030509 68
    0x46290306144205940c0d1800e66805204a29520b1000300c035039100d0780c14904000000781c2030544850743d1349005030610f6400c504c01c03180c1c002d1550000c6141080061114070458000340a9401c5410a842d20402060602a02d00c100407082d0800c60f10380c1054400031050240c41c87c010131410001f5034006060140e00701c00d00f540941d40d55001c1398465400f07540181d100f06404003256561001c0307150315200a402d43e101ea0742141c1802070000a0094101c001010101d84006980303c5800d0300300101c1c224400d0480051825805001140786800c00702c003001c0e003d0384040d0042003101e0707101440107890002d00d582000784040d4050300744000e080074000a84005d45600080c420107198484c007601074002c3d8040d91110a943c00c1c004000b40c1140d025080300a280308404541c0c9103005080c01528110504041c0c0210340100008000e1402c0051078038116600b50740504908144844241000f2081050a9910010901010031030321030a00c525400b40d0702c40d455044e5101148400d011041000015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 356534820 1250 356533570 356533579
    0x2030901050703050d23090708100e0a0203100e12030c07031b021315140a0302040b1801231014130305030d0e06060607030c080304060212070905010e030d020c0603060f060c0c0f 78
    0x2020460900d001400400f0714107c0b05c1d01041700300e68815039070b19050000300701941c5440fd100340e0000e40c0613994010070321040b40c8800d90385060345580040d00c2c0c074407098664101a103020040180802e02c204071803803201c4402c100e015090201c0e40c00241c8244d0b0b034001005807850740d4540c03032011100783d084d0f80c2c8000c1107c500c280502007540000100d50400c40c1c40f000c2d00071600c587c8480559510306c031642803403103415040c102075540c41d1800c8101884078034081d0140b0030101e9404441626050303010617082d81c0681c4d01c0046411202e102070440341c0160203d41441038203e9070110020741d050000d40b0090345001c2d40091200000180103180c184050900340c003900c020402c0201003580320410640326034012002c59941d0f10b0b2860442c0c001d10034418081c128400c50001d00c20350640c130100c072004469090761120160b120302000c0607290b0180382c0504000d6031021000c2d40c243d00f89880615400500101107084420041c00403440c640d11404801d0525005891400700500e8035811440c105201a0f5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 356536070 1250 356534820 356534833
    0x306060e0a03020a05091003151b080c3a0209040c0309080703050703021e0c010210020310090504020a0e09100e0c0907030e071e05150a02030901050703050d2309 71
    0x1c0116004e10510b01495000d000041e0000329041e00c404640e038011a484840c82c40507960000c50403006100c01072503069040c40e002c4200d1103007840b03100c40e01d01a0010300d035814500000c0381c600760301811a02d48041c8145504031100700a8110540c0080b54005982c900035a460b40a03c0070041111003144050084c0b62405d1904004207149000b030300c070140c1c0c4c035080140d501c412904060380b5101c0309030070405d0710000070b245410b10a640800c2d40000c1e40c400382c0803075010100f1108000142e000031902606040340d0002c0800c0344030402d40080b90041c2c0050080c600154032100006010501259514860703440504072a0000c08a03216226503543c80b80040e1030090360320000140e080c8030107003180041540f0344445002904050040100601c00c007149c030382180e00070f41060480c803400c0c0e12034640702c1c440119a120b1500c4d42d4104541c1444c200d54091440d2140610041d00e09400c0070a041c2c00b008000d02c2214040100b601c1a0b00011608040060200c910840c502451007002050810240c020701e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 356537320 1250 356536070 356536073
    0x509100308070c0b04141e030c0409080c01020c210f040b0d1e050108010c03150501050c03070506090109060c05120c03060301181202060916051912030306060e0a03 72
    0x212018050301d601c00265075441d0000c0c14410b80c681600d0300f001e484240000340001d21382e0a01d01e10540402000e07500c94800040c0940d180780381540741c00c08907030141c01205101c44685001d510030000c807031240d42d01604018001c200c203422a0000604000c2c82e41c4121162100014540c07201c0c644241c0c50000545041508ac925107058092441004021903021800503045080c40e00450250700c98640442c001024000c240d1000d40350a10881c091940b0703209803560a01c2c428000d039942c0868030f042001c485441c0030300441750b0303074095076801100380010f0103100002001845450700400c0c9010000c02c0d24000c82c14550100d0700000c02c148140301e0108560540583c06001040c0c0c0001d0000c81e80b6100d81d03e0402180c050217203150030160340003100e5150300400000c0d6410310a81406903080303488035a074410070303580d0f900304440d0005450028507404000c10301e44402c02d021000091900103130070b41c0d43e43d101e01000030100b0404a0210341c0b2081d05008243e8006d10410120b28219404101503156 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 356538570 1250 356537320 356537341
    0x4020a0905070c051c1403130809040603060e01060306110c0703020f0d12030c12020c1e01110703030f06140603040609053c01150b0c07050316080601060503071b0309030203030417070509 82
    0x4948c80140f0091000c03800c1400da6503583e010100554220b0000e02000155400540c000c10ba1070104a544c54541b05100c4c004200c20400d83e40d561000c0401050124195020040121403a400203a84015001a280b0006513101a0702c0070122064502003418156880f019000c03007600884035400e03610500105100703d60000c2c0c0c405c50041103294200c8030701c1c0c3e20510300d8050455070034001ca0b94400001d1030310030142c1c1580710305d440c3c0003080c00030480603031100c4104040c00c0e60010340d035038844414404200441c20503070003012407911550490394206032752810385070400c03600340300e01d042d003091581c016450f910317032804424035605010300820404c4500c0491500000d910f0151410303900000c24607400c62203040010a020b0b04000313040300c031440d5582c86a002c00145a005600283c02060000280140580d040d03a0150f11507480d2203481c10030307004002c8240c041600b41942003000300c0340c001000d6281800140040d110085156103000c0c2074440741890700001c0c1e4002c9010704120001c02042580 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 356539820 1250 356538570 356538601
    0x207020105030f2715090109030207031b03020a0b0d0b010c0c0b0a050d060806060a08010905031c0f05040311160b0304171308010209150304020a0905070c051c1403 72
    0x8003100034007019284c1c11460030404d00c650008049800407200e02000c40c0c080050f1005045481c5104222182d8034681030a00741c688800004002da0b1002e4014000200060400c03c03074a4031b80380c45031049a940b0340000e084510240d0005140d000001140ea105900324056014084401e09101000c100c6a0341d540404180a109075113030044003050000c0748030f203c2c100300c1e14072102c0d8180911a094070b405185858540a9985a20884060900194011042c0074501100c0d03040809541407194414118484094180789010055a0380350b015102c000c06e48207035802540659548180c07454048c400919111010015904007a1465010019020300c5e008803a8883d5004d04030559900360168085c1060007078119101c4111224400031881484c150301a140e0700034102c4011400b030041017020746182c0f00540b40690007101076001071007800b0841d000036400016502d0090011512034454034101620401c3ca00c1d4480b001c448089215680f010715005803031480480d0070302d90f0900c1c81801d4448031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 356541070 1250 356539820 356539831
    0x50a1e03080a140301140906150906030a0f0c020c1512180a211d060a0e19120501050108071d040f020a03080307080c040f030803270d020f01020702010503 68
    0x80001941c40400e889560700d8122414100242a1139503101c07440701d1800e080464006008030341400000b00c3e60b00d07040d803c40e5011610100c6051802a00303009208090340024240f20345c03691540350303002d20360055100f1000d81d1080f0740c2c05001c495040d0303002c0007018035848030300d2954144184841c084c20030844860a070021100141c415151a441701c505043c000c0c1041c000c0d150803280100c00406d800003441010511a16595180c5124003d9030b2000692041e403040b940c10131401e00c81c04003c5401807082d50314849001303001500e84000c41041a9541d0f40b160025140d00307414083d9502080000d0151601520b9494090401079080c40c11507600d06504070603c4a00c0040540400e050207510720640c1362039030300504003d50841d1a0b0504518640c01640d80400084c104000511481c829000b03840c00d035050a00003120080c6151200e801c6500068100318440c88104000140291064580c4911f0100c683c007404880b51002000f0781405118540c9240b80e0b40100480d00042c1e901204030b81e80103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 356542320 1250 356541070 356541083
    0x12032004050103050a1401081b040c140c0708060924060607032303180f0c01051608270a0602070513020d090203010c1e02150c0c030f070c050a1e03 65
    0x20b60320044070602411b004650780746410440400800d40e03020100c3e03503403661514810987c002c8484d00e4188000c5802040c810300000e0b51007408810406820360041500c6c40c414800c8860854865038440d007400c109542c0d40425911843c44003244401407440c8100300d515911000110385404004902a44108074000b02007210440503101e581403820500c2540d140c41810b4244c0720b261500030180800c5c0c0d004007614030340c4594107140701d04220002e0b074468220b0041c1e40b6582842880c100c070f0480b000c090502124200d105002099842000c1491807001c03e401e6090519a400011b06102d0600c1c050b80200007150441c10301400700d40c60301801c100305501c50000060380c5070040403d0300d00401050000039410350812071144207460307001d0b0080d0a010141e1100d4140886440e130f0681c1e034ac002604130803908013114400200800468400b8100780010001035925004101e20800300b41c2c1c1c03002d401210711400382c25050166040c041d8903240034105c551120711100120341c2182803200000e10008184 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 356543570 1250 356542320 356542331
    0x510021b04020c15010906170307020307060516050f0633010e04060306020328090b0402060c0109050703210503130b060a0504060305010b18040b2a0712032004050103 73
    0x10070100f00306003883e113008030003074011a5031980f0780d002c05459240b084804460002503040d400e59400f00031900340d154001c005010300c2d0714090702030b80c3c160010a10307a034050020101c0718002c10740070301281aa00c2200301c040c051034604005034148030500c4ca6400c036520141c0e924840280c0400340a000f024000c242405888a21082c0000f230240105800041c105070000c401c0c03024166040c0b60f403e000402141c0e0b1200070349100c60001c0f01711105240b02034507200540002c1000341c246a001400000200e4001150206042c0c407440e107801c916900882d26800401c004038030001d509c100020b04411186080d500d90705050564100701c0d00450806480000c000340414102d0b80c403107055000510015100744800c2d950307070505a00900306c2c41e0545004035001c0c011749503840035030b6001603c690391080c8110311544031882c80454481e252884041d051040c01144803541c881c44014040523441000d5500c4070407501a001010b441502c540740c4041c540309078201d0101250301054030199142841c1c000380d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 356544820 1250 356543570 356543587
    0xd14072a0c06030507030e1204030204020310030506190c0f0e130605033004050d080f0f0f091e0901090f020412050d080c070c141f090510021b0402 65
    0xd510340c41820080041080c003600090040d00f54000501c10552520200000004500050740340e0b0390f5150406102d0740c00b000140010302d040d9000c3d541114a07107050310525500d90f595545812003d5a00e01c2d14110501101c1d1102c1400d07001741c2120000a243c2499131501508028000c02481c0241a04c20038100300f42007a90b075210340c440001020001d048400c951000c45800350500c14401242d81c00c10b1801c0d507036002c20800c3c88125011a100a46041c141180c140c131003a9140e004150710850240f002c003c80c1041d541000c02800d010650a04503a5890040e8010400608000d02d00e90040c0740782d8240100403980e1b980c1c407080c1102c8000f14045505800c4810340c3d0000d201d180c000e0b4400ca401d400c0700d0710a00400103001080202d450b141c454060f100d42c0210700f845d010ba40401004000110401e11070040c3c0c1c42c1441c8541c0174090300c04500c00b03503030304d4a0120050220040000046030000100018640300003200641c503a0f60021b010301603199440014510164150309000c1e5400094190 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 356546070 1250 356544820 356544887
    0x1e0d08130f05150108010c170c0c070e044e0c140601090e0601080a020d080d02030f070305060402090a150c0f030e0109050f032d0a06020d1407 63
    0x8031002d91101c180e079001e080040112030540828011546258601105850402e010300d10a401740888002d0840d8941e1711048170070910351260041d12014010a800040c050084020b0035000d98410801c1c0b44c0c050208803a941802c1f088120f203600902a201d0005c40c0d03070007000840c6002202d980c10301c80b151060202003501c807261030090060814200c50f5a00c100442e010840d18162005088240b1100c00681d0205942c0c03e028020b81c41c03190801c0c0c1c03a5030014604694500c01641c0705100060408450003a80003c903001120407008500c0c0c41d070200080241d242c03240a5000c242281c00f103003040d5000b800306458036454080c070300d1078111002041c5007860084841c120031590000b14802480c1291030024501c0780c0c00f104a901140c607824021610f888c105901501400000d002040302c00f10b90966100f50740c00d020b800c2c01131501c41101d0911000c90901c05004818001c5802580c0c44840c50204022940190440c500503540e83c004e0010b41a48220510341c07103002141c40c004102180107406 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 356547320 1250 356546070 356546093
    0x3220c1703070506070804031b11040c0210050c2106060c03031e060102210d0f0c09032d120e0405010306050108160807150207030803091e0d0813 64
    0x850105002440344000e0110000c010003400c1d124009480e115241d60209035102c2c00191001004108070b40120100030b5090310081f00e0081c020b20302c0f8956089481c1c08502111107002c130300c4005802950402c81f070f18a00c0d0081075045071440312158500710781031955100040d6043c064140c00c08114010401950ba20000c0e920113881981c207a85c0d4a040014108201072080300c042000040c40c0400512103600104e10002510201891401c24410081d00101d6950040030400070311551280d9511440c42d041c1b1580c001040ca544036220890f0560038000c4401608041044040d0422060040703d51291200310030241e5111810801802d081101910101000508a0b41081c5410000010301404d07800c034034101d42441003503c07408d2608054a044105882c05400300c5540443c1e0708102080c403500c0c494045500500c192000c46480f513556514947c8140c8840c8000d90000c007000b40c5c25984e0260f41c07a105404c1c80000e100189510b0005410700c540184001d580141c80300c1e600c82404001c000070b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 356548570 1250 356547320 356547329
    0x509070809030307120b03070b0702090a0b0105030a050414070e07110c0604030f0302120d091502072006090301090c0501030b0102150a0f0f02070c06180f1203020703120302030105030d0503220c 85
    0x41c0d9000d191128110100341e0048ac00680c81222824003084070300c0d201c0d00c00d08440d241c040e5501c80c91071351804203034009040c2c00380080b5a050754031422040000814403545002c1c194245074400c050519400040c10403d0032202c00e0b0303481d080040800e235580d4402044a0460303034400400c840d03104d0a801d05a0034403407075860104c02d400001600350f2010707808e9804004000e1143c40c0364144008003c101e401240500c00009106051810000c580450040c6940003c184001e00b0a868890070b840444d0940e03c405804544100c1490b009020035130b01401425094030707082c80107110034114014040404200030b000d85000729074030001d2198404940d00503090080c02075800b95612491850440100e003a540b00d807400040071000b2210700f80b407807100e4010442d6018100e1020003414160300c044101d9180408a065109403000000044d003441d01c20040c01d01d07552801a141d40c500005e0508103c10101d808040040402c2040000004514000070f04000c20350321003494802407500c014051201e400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 356549820 1250 356548570 356548573
    0x30c3216020310020301180906020409020a03021801020a050d030e0304030f0305220503120c10061512060f151403090307031106090c091510090509070809030307120b03 74
    0x11615100e003168000304988500c2a000c8411105100c9001001ca001c280140c0c0d00c504c0f83c0c0f00a000d003180300e07600300b82075050042a0052401d075072246080200ea00c1030322980d002c290049408004295400d0407020001c10a0028059008043d1703211610351804c94900c1d424160b42d0380072481840020020380c5c010b16402084190314241c9410058066082501040c9040210040d4501c000b82c001107480d003103c1c0007400034080b42181c5c811018103034100c414450301a10844070020508016070150200401160700750b510340344030030100240035200c07001403003005509080b41080340003154022007080310104038141024602210b4119250708c00700b080c02020305804070034040741c01c4010008108403442911200740c1202c1801025403151000c079841c3d50325810a065101180c01c100b601240d0101c4500c4d00d03401c12441040c00100b1503844102d0007000101a0501400309061180c4415000342c42410084e0b070b5450220041c50340ca100c0140104104a10410401c6400c15950454030b2101c40040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 356551070 1250 356549820 356549827
    0x6060a02011509050901050601020f0705011b0c0f05030f01090335010608091b0303090103021e04030c151107140607050f0a02030c0a060903110f030f0d0906030c32 72
    0x103c00c240900320903202d0003107075403138040410229800000d400c40c1840d4000c0103080850b1902c4015191242100b0241100e41440168a400501805807074005000c541d04450324060030035051502d041c0c0c8103020b100d801c0e0b25021500f808207410444251506000701c10140c680030941c803803d0000800f000420301c04100d40740c004924036070000041489464850f0031614084d03412030038064407a8801001503003580003080300c02e0b41c0d5403090b0010b00d42040003041d41c0c03417911100c416101503a80a64800d545058040005200d000320b000b01900740b0b034801c0d1424007151461060140c5d1540f180f4811001a40541d000c540003644419040d10b0565401c181601c07800c2412112140e156103080504a00c00d000b0780408990304d15081d804d040564085550760380119042d556045802031031103900c40e610200c002d20443c1103503000c02c041510203600401810301406070b08400b81401c402c0d5003100040c1810000e0380365605901541c815012000045031102d070100000561802c00d004410014800d003000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 356552320 1250 356551070 356551079
    0x41401050403021b01090f030b060a05030d050403020f040e0d03090203010e0a0f0b0c030709061202190c030e030111122d01030507080714040e0c041e06150806060a020115 75
    0x401d04c0341e621443c5030214000d030f4650000459002c4800d01882071007141c1c15030207102043c440102160f0012020307000c42101c50300c40e0300117882c00307020b50766100000d000090207108600b4540500c1402c02003d441c1031202e41c03120300c00c00340c682d01e400e40318404140d511a484400d555003504842408140402a40d403000d0b0507060040940b00c1030f0909880300c410310008650105811011684210000d40e80c0f4000c03103042110494840c5140c1d52010f50f040c0d020700c000380d83c1c040041130a42c1c0a00c01d40d1a00401c1804500d07014080307440308241a44a40d1400050090b500c1162084072210b1131102401e04669580340d514000c260640c4403842d41981841c0c0c0660441e0180c040414140c17401035003100c4841d59140c02203541e4240e90301890ba0000691015031f0400c1c00c181d000f501081032a5400c3c0d40d00c12091501080488440107080402803500c0d0001032600078652013540041e20814010080c4141070003c081e18080c0043c0c41180603d90000785602028800e40c00110b000c1c004c4040ca00303260341c1d034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 356553570 1250 356552320 356552323
    0xb070507050415030f03120f0e06090604020f09040512030a021909030507090216080f0a1701080d050a02030d051906080307050d0c0804170307021c030816051b010c0801080a1a04140105040302 84
    0x501303440704058800c180212f140501c00040c1c892240354001d152050071b80301d28081c848180350103401242c0d103201e041c00d641c50b0f189404001d1480380d00103100043c0c03548410210b00c0300141103e1000c00c14000c2c0c0001c01d00114001143c030034103030340b4a107001590b50325544180c18840c6112031b10151841d0340200710845030040300e80c0102a18025640d841e2440c01003110b10440c443d6082c882c260b50ba40c81690301640641c020000741c4940c030814015641085d04c003201210030f07940201c1d90a9040303c03a4903d18020300e103031481400080d04801c00210304041895440b60307500c1c490403a04405004403640503000b007212210803240074003007000000e00d0612404036801e680e6000382030100d1246400c100c5091138050303038413070554500b601655a0365460f2941c00d218083c05280381e22603001c22604001040000310800c1309100c0811500c0e00001d00c0a40d914402001c0c004107801c9012140c001c40540004648408400c1e623004c00f03850002c540c1a1100d03d000309d5413001c00c40d0414055400d000410041c541c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 356554820 1250 356553570 356553581
    0xe0a09020d051b070605070c06020c0c1f080a0b120a03020d2a030e040f110301090e03090904060e01060e13120819020717040b070507050415030f03120f 67
    0x52201d820300258881184840d0314601c0003400d0b602e104000d200300342c0440c4c03d98102c1d5400400505000031120551340706c65090764000c81207003006511506000d816030802c000c21341c0d60203000176210440ea02e500702c0028140d020240100c103402d41c5421125034076a680041424030041c60380101c400c000c0c0340f45806501c2c2c0d00d018000c000400c00580d08031a5040c40440c000c14800c4500481241c022041d039000d40d51041180445a049a91a012042d22501038070942c1000c2a0381d0442c3d584035071500c50034005a13408040c440761740d41c205100012168171481c41890300654460f1011910400c003444141c010940c55000301c041c4201003060044c41007200e5000301a80d401640c401ca8107a80691054407051805d9074044500152200c032001051515805080700d54031600b0030386644079051020401940090300030543d880000036021081040804c403100007404280e409103d0402c92140302404c2440b20f105c094a10002e1045e501e042520078944140e40b48400441045902c620003180c400811 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 356556070 1250 356554820 356554837
    0x110c070806013303050a0e060a020705060903091c030507050d0f110c0102030318010e030a0807090e090604030c0503090307060f1206050d1101051e0d140f01150e0a0902 74
    0x143c3c242c0079080303000c0d0038901d0341c4014058188880b02c020002411002008018039013408a991000051000383e0280509801810f440e0005600c0d01200d0500d142410009021107640e6481000064400c0d12000312134101d5138a01407280d503891b01142000ea42c01d00c2460801400d500400e10755450003500900c031411100c08558444000003000c9107002e589045408009000da402400060720101c0d40030794000e03255200c500082680c16984026502e1500004803c0010034008810050740685c040381402c01820a44a01d455908280ea4441e88488001c2e01c003400300311448100301c1c1407100c100201d03210300314050100c41245503a400020164064000c4102c0020a941c11003038072a601806800c0070f07145c00403d039072243c29441d40c41001c04007034548450b0621000b4045480c111101561242c40c0640b2410155a200000d4402504a4010302c802036201c41868003484420704104070b82c54103481004c2e000a003d200803540685c0d00402540c40d5540c0103661950100d50100706401820400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 356557320 1250 356556070 356556089
    0xc080720010c051c050702060d05180d0f0c290603010c050c1b04060e01030b0a06060302030108061306061e0e1008100f06050409060b0901080c01090603110c07080601 73
    0x3500e00045510141401001e442640210742c030390220706001051440c0c0c0c1015007080b5152a410384d0118025401c900480c2076400e90314030421030321048440c026601a031521020f441e030810224405803c01c11540680400c01c40d03058420410070949052480e401258103401c40e00314881c528210f0120b420844086000c0c0d424483d440004501800580d40d110420341c0203400f20008540d01c418085d085280300c240d200c1d8850a002506a2104104902850082070a80420720301800d1510a0b280c1d154001340030144108010040c240c40800c80c2e64026880002d030390100d002505010000d400583c101d408159039001c180ea0884680840310340c121071850036202c03156510301c40c00e40b41c0000306120b42c071155080701c440300c4000e107080e40c024803488881c1c441c001001e036200c80100703040341c18400741210300c260354001000711131801d0306500b401014a00d0081104252040000f05401c00c903214840a250701c82180e200066801419582c181d0b16030700841c2c0a0f0356948596980e150360a03c10300020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 356558570 1250 356557320 356557373
    0x6050402030f18072702070b09160f05010c06020d0b120307140105071e0908100605180403140c0106030803090c0109140307031202010e0a0308060307060806031c0c0807 74
    0x3070300042160130171581000800010820709071503854000540318944003805508010310000581d90582440c0582d125000800c00a44108941101d070760068221010360320701440b04100d035a07400707050003d5490748100050b07191030010220002400040301d419610030800070743c48680760000809490f809002c2c044c0010582c401c10022801ca6105460740c00024207400c00180442d18500800c09100015144ca18030340b66451107a9410110310007007900b81140c50f14800c00c2140350030301c0c0fa0248040301001a94142c1016034014100d5411070383d4901d04001c0210303803030742603100030751140000f5500100c0240d0b803850b0000005417540ba00e804000d001c21414107011441700340c0040100700071030014000300006801c68846105002c06000c031481150348407465155203520601144088900c03a444280300c0381840000c15003040c440790000b00400503410100080741c1d40001d01c40203000055100059940308841d812540c511100b107002d4040750b000108c003410028521070044c02c0340c030340341c00c0c40a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 356559820 1250 356558570 356558611
    0xf0609120f0904091203060e011520190c0b0c0604030f09120c0302030d140702010e0f03031303120f02100e010209120c0103060905151203040f0e010f08030403080a1206050402030f 79
    0x1100c1800c0c0200c407940010254030840d854002c0c01d070b0b03c40307100524405144406103101080d1902034003e03c80e03001c2000000646040101c58a64200a07001143b0441c0c2032442c541280b41c2d075160010406400c100225600e85212801480b094020702611400c0d03014140c02c6007012801c521042c030049000b44a0b01d40442d582e1032140080510003000b01240078070f040c1c0ba5400448025041d000c85940c09240d456483d02c580e50200000d0001c48443c02524405924504100b110841c40d1107504062020340805143e807a03502103040041103e4412000450400c40f6184500900500750151f0700301d4100700c0000180e10b000540e511010b00c003640d051000076116800741c01500e40035103802c10364401544250740c480c600f03a0100001d80d80084100e80c00c00d80c2e540c0b00d048508410780e001084d01c020810060103120b20302c0280e2000b404c40c0d44000d5260600d59902c901c980c0c821410f05204215030740c2c198400907011600508001e01c0024000e54403801c0c098110b4100040544040c460306020102041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 356561070 1250 356559820 356559839
    0xa05070e0601050d0b06040b03131101030e0d05180a0b04080f0a030e09040201020a021e460503011a01030f110f0715021204050f0609120f090409120306 67
    0xe104401c107942c3c0d0b50800d0302c9001440080d0200800299102c1018440403914100440243d440342c59600d6285c1e054520b603080810101c00209202ca04040c2881c0302e120411500080c060b2102d2210320f4400c1e070b20100c0180c1e225020040a680650100600307500240310302403240600241d60301e410550340c2c891842e4500c90b0351041c01500060201c0d0844c015010b80e803904d95000c6031b2050040c010f603803115019030300150890b000003160414005140714241428113100b00c041c035054036990040b0356800440742d06100c100407940c0308210460b101d407a2000500c02880161030003004040d00074032283d4036110540c1c1351801e11807004c50019103030400c600b45002890280e111550080704849140256806038289541d01994054800100c51501c80a20403607600c000c1038050686440070703c2c1030500f850118103014044010516580c04241440076440000c00e4180c25040c150784a903a455a00030b60801460148e0085580d1003450700000030184002c01d0700402c00120b282c1c0d01000650380b02c40381103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 356562320 1250 356561070 356561099
    0x607063210150e03030c0706080117030c120705190f2f0405070306031e0201030c0215150111010c08070e06180402030408040509070e0108060418171b0a0507 69
    0x50b500e801524216030509016050007a20818050142c070316103411001c0e89450041c140c0d000c1000180c41900400401c5402c00000e40103001c004061032070615000002030740c441500421a01014001500303804100b01088039056a10726003004580310102d5013044400400c0308074090b102d84510340361008109400c21070509a10341d88000c5400070208000911004140c0241550306060340c50034040041003110280114440700e91140c0c14100c41244001415500c0410111040d544400700360545036010035101a401f418000003489000008401250700c0843c0e0002c01446520300300310b041406510819052040d80d44d62100d00c01c51000c0418480c0c03603c25940c10040000280200280d2843d107074009541082c014500c03581000c1e19080002c4038130170309440c84030218190004018203540c00901c05c660140003280e04200103180590104000c24144074001d001f401000c85441c0036103011000c0d5001101610005015200c0b4180365540c0da043c80038054440d8403595200160320202c0a114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 356563570 1250 356562320 356562329
    0x60f031e031808100605030102091507111003050a062c060f0612040b0a1406060702030109060e1b061e1e0a0804140c030304050607063210 61
    0x4101000c06000c40c900c14444840032020460449642078040c442c590991000c0c0900d00058484000c4504844040312880c2e8007180c026401070280b429169a0940f1001c4140b10000001d035455003240380011000601c80d41c020351000c180008018103a615501842c403801c1c44010400000c1c3d1900e811140000491140c0e01e0491082500790001d035500203003880c0c00510241a00c100030f548a8001a9a60070504490300061800401c000600504100d20f60304180803000c2003046194510007900d645200a10301800365000041c3c034030454909501124485d5040003003001102d0b03c56003c691201c0342c4800f2500f000000c10702004991800404940c2410744004001e2061402c414000040350001521854400314001c0010404010030b4010300d0001c5256444024074581807400f200d603010500c0d0a904141e2040c8212405600c1c00002c4406070b0394102ca4090700d0305150300c1c0c03180240c20307078004108261800840180c0080c44400303013000301a0303884296031101e60394104d1001c2c802405118 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 356564820 1250 356563570 356563583
    0x6031c0302090409080304030302071e0203070b0901200606150f0301120807060c030f0c0216030b10090e0a2d0230070303030c0311030613021308060a060f03 69
    0x6015001406940141141200540041103988007a192030105030412503082e80072a0f00040d40c14100400c2c4000301070030000541c03801c0e4240d210380e0082550340500d801a0a5600380006a80c031044c4c0c0039a0b0800c19031201c0b01c045100d0450100e1560b5141e80c016103e9074000c003980c4182040054003d03040c2c1d0181021209000c2c08d40c0e00c0c0c0744240c5080011071005540d40242003182c040030403924000c50583e038078940c501194204100e118030003100e080c0c50056045400c26240300c002c040d5403206003812a07402900300007040e01ca00d43d070b00d10451510707484507220324904881d00c02d9203180424010302440c001ea801c1e4034100c2c4a4075040542c005400c2100440c00c01c5407007400c0040c40c11380c101107040000401d440105400d4403150182c0d05c40303107600080241e440f000e8200704055150046150704001c0740341c140701450891a5052003404083c00d403601c00c5851603c330805501403603050314100005415186001552071305065213402050740c3c200704042c10514041411044001c405007126800030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 356566070 1250 356564820 356564863
    0xe0d0509092202100504050306060a1d1803160614101503110c010e0c10090603050901090501020a1205010506211302120d26011208090a060905090603 66
    0x100c034044410b42604502c101030746000500310151316051640540d0300711355102c0e195903606010030140352000003841c1c14031802040606200c44050010303070164000300d0801d210318989030400400304001002004039039a00c0003141a42c8448160710f100c0d00a60700400d0204541d041d1162420301c1d0110495900800d203a620104028100505d03800901010076841e0001d10408000a2001203602070f82c44200c086c3e450744288403c2040a01c8014500722080b1014101300760003000180500c5d00c2c0e807068400707140c2c0d102c3c0040c0700d40b04290000c0d500254001d0007190342d50490200544036540000c01c800c40c80385482e0000c1001d0400f0001c60b29018254070742e410f904400082c0b9064202802060b0226445405840300010384076186456a40741000700030308040151420001d200424107909800104c0d401c260410061021800032415100c46401c40588890305081c4103070503100d1014902c2c1c22800c541c034000b0700c45511681090543c2c904807600b07000350b10b4134070402d0703617801011500c480a0103900703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 356567320 1250 356566070 356566081
    0x5090c040b070512031806060301090b0a0e030403020d0b0712090809210f010614030a0f1b15020a11010503040c0b0903011e0f0c090e0a020304060b0d0302010e0d050909 74
    0x70014018151241e4116140d4101d003000203446074009840e0780d6a007403510071500b040010248030071031348120264006c114000050b203c05022020141004404c99514402078904000500407a40515000380c42703240c19140c20321f13110740c01d464121020340000303420300400d601c884214044c0000036600109450f00346060102005010113507112003100c40c0702000e80c448045001440301038030680c0108000202c082c580403111080e469040c0d141c0707100b900411492400100f00100c2e0810701a000524915009201001c1020310281600304484421000505025196000404030003051240100c0002d6030309540054900d404259402000c200700b080c002c0c400020110043c2c82c044c90020b00224120742d58070821034040035144210003030542c0324441803180b2101800358503104141450a2038001e890000c841003040d00207402079203902e400101290902c0100e822405000e00010722517a011001413802900a0413925203a01d0140181440c003820726026106030b492051001e010300703016546c2c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 356568570 1250 356567320 356567339
    0xa03020d08060d0f060e0d0c0203060f070521041b0303120504060b060c06060f060a090603020c0c120d0f033c020406080415050411100e030f0d0905090c04 68
    0x105034a812080f001d0000c0046181d6102210102d4094200014541e000c0e10b445820a19510010424407884071100401a00c2c00101240d000700000e40f298a1074550081c201c40030b11421004050a074141100d0100202c020054503020f188110090001c00c20000900d0144004501c0060082001400584510f4419412895100344540000650618004005040d0b034101c2003a28501c0e43c00720f0300700081400c090708101d00b0324074200d441ca03003080c001c4140102140701c640240002c045c0c0112740c540400d0801c200c490000040100342030f0480400c0c42c00c1c00c0ea40c40c9800d11010005d50b44007440c0e040c0500901c242c1c000160400c4003401601d100280300000d00301181d14104d14010b00c02c514090000d0a803015001402c415980c01d101806c0504101c134032000d81c056141c40c11413070034091000052038030748415081c140a540741c02d80c007402c1c0b400640342d4484144070550180200a94010055804641152682070b141c50300100181c0710001e0154a8004a51a42c5078810400c0b090205080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 356569820 1250 356568570 356568587
    0xf0f04050703120e130e06060d031e05090118030c060e010210060b27010801140f0307031217040803010b0708040b0a0302070b010503031201030b071b0819020a03020d 73
    0x148200c8420641d26a1806040c103c900c0b0060001640c5465000051600000da0103020803440018815141241c100b00d80b12074018007007501c241400d0540c40c04050007000010f01c901e0066920502c3c0c03903155030000d8540d40c04840c0507030014081003003105100650701c1c039690a60390032a60625a150030264107480181c2c0421140703040d032040d42c070503681c01c520a0195001410200311581d448401101800035082d440e0300c000044401c100e544a40d4076644207540c0740c11640d0400c209940c070209000800c5644140e2402d8540601800d8800300c18001a09070301390307025a0a41c4d8168000082500c2151030020959000380034000410040243702c80d410041c00b400741c0209641441c00e030741c2d6210300d41564041261800401d401140320400c1c0800540500e0060400750091031a049418582c05401801400020b1501c0c40d601d0214122030f00c03600ea107040d85215030310845080d03400b07400e04e02110f800280100300c0352080003022900140c40031030030004140c1d05070002e00d20100601c00540302c141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 356571070 1250 356569820 356569823
    0x303050f1b090f0a0305010c090f060e090403090302091005091008120d06050a080c040c0e030c01120605030d0c11030a03020d0804020f0d03030e010e0c030a260f0c060a050f0f04 78
    0x244580100f003d44d2082461401103108000000b0358101180014202c050f60360b209070150980741c402001400c0c0c0101c20743da80b000c0d08031040074980e540c5281c16203070540c50340c0010b90010b60f00ea00708844c080c007842ca401e007520021640d41c011a40d4800102d0a01c280500961b4116007050743d010080e09031090150180d04010240400ca158680d000702d08450810b90181241d580444480301050819103d4240c82920038a804011180740202181d0b41d003200100c9141084103003540a0019403e40c0e04c410041d14009054400c550305c2c529009040c0810140d047d9194803807019040d0340c614001900c4224250706801034151403041803000c0c0e680c0c0e0303401401aa007103140d4403502c0005507129042080424481d8500003941c14004001a08485c144007480c103540c1d00c035a1240400c4d503030000d4204070f4640c0c00911542c18030150710301c0000c1180180383d040201d420115000c100070102802030300e443d00707040f02112001c0e41da0540a000b6160103440100d140b145000200300c122604050066205 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 356572320 1250 356571070 356571079
    0x11b170606091f030507050a0903020f0312041e05040606090632070b150109090c110102030c070b07050313020d06091406010510110318010c1403070303050f1b09 71
    0x4006001040c0306607501400d0009941000e07100f81e1241da05440340f160440c1c5d00e454000d04021490314050001c100c0781c00046e00c00d09071141032031042c0c0e80800c0040442c0c0b44080608c0c0e101d690f103503400890340c2c4c80e41180c1c2d04844008180401c580c00d0512070f4204131280d654900b0400c84c80d040d230954501c0b12009100540c1001d03801424174401845404240e9100d0040009030303a4800307801c0900c04090041c010003140b00d195019080c160303038001800019902002d50018000c004040c041d00c0d13090b45040e003262554008002c101040840101400e00749004907070711501a5210ba00480c1c2c288011113591022050b200c03c0c24015050441041e0780151040c50300069070b000d141c50f603c03003201c1246840f2500e13610000040c0806d00f00907088103402c0407181088000015600415600c0e0f0050b0007448000001c4080e801c071103a8400c0344612019034000b80d00d00c02d80d403000c0c00143c0e02c0b50320aa2003038010a080102003406c05071180c500c0d61155040740c00451201c1d414001d8110150f110902881c0d22 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 356573570 1250 356572320 356572327
    0x10020705120c0712110f040203070903081b060f0405060106050c0303070f0905030102071506050303040605071b0b0a020604060b0603040f0204110f040b130b0a200712080c011b170606 80
    0x1007400c8516130700341050143c403061000414800c10480d00c03c10341102e20780500d00500074044413a400c540c0c5038050729440340c90700e61100c0d444d982c025003031a2200442c1c00c2921910040c4030581d42d4003003281e4001c0d1b0040c0c0030341c1e11aa890f0103090f00d85100e1460031000b1030f80b0400015042a101d002084041e03030300d40c9010035110b9510070000703007a41c0014070143c89044e420310080c10849050311039040180802e80140d03060a20f0300b8400741280c0903c140c080d15205d0b0150040142c0340304a050003024150841e61140c481c500100001c0d07880f84d04a6040b50050701d4003001c2255803500c0c206880c85680d0000691400b442c040c2d0900010b0319852500e450044400c4c8115031600310340c0400707400500942c2d0344680d20345c900000038046003883c40d0700070102c181c403c01070040780c160b10243c210400070f030080d110941030610100d40303841d10038507a02901204064610078020004408010a01d007000c0100038480000e00c1e204ca211000c1d081e02010780440d00421261050080a84034140e200324010001c0b0308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 356574820 1250 356573570 356573579
    0x9010e07120213020309030903010b0a0807090b0a080304121203110d020a2003130f0b070f05070b0304200916030f0f020c010606080f0f01090908280210020705120c07 73
    0x80e80c00984180c06c86401c003080003403d1f070800340714003407440c0f0f001c880504045185c03801d541d03201c04107030140c104160340f0307001241c0e45c545404076044002c1c510345040b01c9c0d4030303076480306401940241d2030f03000c9603030204950071425254402c2c003d0f084410034009105190040d51140e440080d884908841c040c04000019803810003d0f6910003c410b0455001070359540c007090a0303688440d142d9070004000e41107800014030404003810182d070301203540403624150340c00b0075060462410a145c0d00070484070400104000410840c47d403104900c00d481c003074034040d0300d9118080241c0a40d0440c0c2200840403105203180d0981d02c650000c50142c1200c840c0040c60341c8906015006a07445404103030760740e07034484204104032544042095401541c10210040506050784a04001041841a064025241e6035484203200c016000c984e01f1782d0b0a5480f0310b0120b078010f1881c1c072089004a06413000b40c05a03018000c0300c2601c900031146681e80c002c0282001c904102040038913500804401503039031054800115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 356576070 1250 356574820 356574859
    0xb06090603010b0a0e0712110a031104030b040602120a0236060d14070908070315060b1809010602150402041119110106060c03020c09281409010e071202 67
    0x1c068009007460001c10b06e802d80d0080d040c0c0712030b400160006444d20600c2c2103030040c9401500c580071100e180c08102e00c43d000d130305180c01d40141d42000d0305046c440c074140010041940c0c000c15082a24101c1e07140990745914000040b805101e0b041d10145038008940c02841303402c00c042d908045182440c88900c00c9005022031041d40040244008841c0d6508094002003045640603500c80390790311b442100a17042100d40e40d141c1c042c5100007829590964001403554070300b034200c10003034201c0c000402d4641400c0350510254218140000e401783d00603100203d4803910105603081a50300780085650603403119803d003c020000c0840d2805444011b0040c8000300d81101003c03600e01d2030759950f503911141d040c0b114a02311401039221000b4006e9440060f400290080760100014000325440d88580c5c0d00c800040d150420030321000c6400201001c2c4040039050a43e0103a081000b01100c00c031500d644078040c40d400c803400c2d4048240c10ba484000c3c20440407584d01c0da04503d241c40030384482125a041e44040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 356577320 1250 356576070 356576089
    0xf040e031e07060513020604060c08120a09030e0f0a031b17070303020105130b040b0a060306060b04180204050a0506030406140420010c150b01050909070e1201090b06090603010b 78
    0x400085800242c280e003800080c0c007802d50000220000d20b29190416400190070344aa44141010300035030800c0381080c040380500383ea200c1c1c00500c985030164500342d0309020051204901c2100409c201403100380c0c6504018990081022024004400f002d045448818100f1203440070398401c42c20001d40459841c07080d00140c0b42c0d41864100600b0505c3c1103150103800c0d40d00041456030310b4510f409080011844032061150065005001e542080d200c00c0200b40207480190030160180b82411780000c0c003004003c0050040702d400c41d000b00c1080080025441c2070b8491849540d44c4081c0001041c805860803400a540241c800c1400180317003030380c036042c2c03284030343e0100c9040e2104103520078110b000c006c00610080008009107008070759070b1256510f21284035000c5840b03d0f4642d035550400d0320307a64066170072140440802016100145802d04000701a1560074014a0080580c0b100440c0001e20501481d03400075402214800c10b41da80070240540301000510560b0303d9902e54244d00341907118404113 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 356578570 1250 356577320 356577367
    0xe130f0b1309030e0105030a200c07050303030402031b060d090503070309080619050702101a040b12030913020d0509060a0b0d03020606120106031a071b020f040e03 72
    0x10612504000401c41011040d010600c09039052098000c0080d03070008400c030404d8001d08043d0703103c3e00e600d41c50b903005106194000f0078031000c0600b1428a005550042c0448041c3e14080390300d1036899000380b540b03e020a58000350158044220640740f444a2041a10fa4200250100307040502c42030030036082d11144e980030f40b00c0c2d400000d00c400c1810b030301110000190621400504d02410042c24002c032004001c411441c556940d81e012414840c401e011504c41c29042c0030080c4440d11034121042e030015092444103110b42c0c40c1880884c3c040c2465100b0030b00d000c00c10809142003203050805e006800d00d016141d4251950f00704082128841c06116503070007200300750010400c902d022034000d0121070490420511440101c1c1d1910700103540041e403154082c03c1a11701c0a0361081140985014101e2600018040a003c0505104403802c020400d84a00040d603203447d07035000c0c1440c45a0080c849070030040d4000c4e003851070010a505182d0091404d1b5034031613044a181002e001d03038013070000c6c888180 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 356579820 1250 356578570 356578601
    0x19062f09010201060905010e04060e01020d090506060907090b0403030f020c0a0303050304050d14090f04020712080f060103060b09010e010c080a0207030311061e040c0305011a100305060f010e13 85
    0x14401010750342440b8580152490500c10032083d414194502c89041d00201f0040440c0e407125807401119000390141e4600e1102e010052281407030702d14203d501c580c0111176a500036018100010030080c4610032410485070340ca2842841d25040d80c80440b0034400e0400d40e20103601c0748107034516007515003801420040d400381c1c6c1c0c0c854032030816141c1a07040058401101341040310208030b440c1a02d00400442d00303505800c8440540b21540c2c01c011034068015000007900e00c1415103880c4c51181d801c1440c0382d1040b4207a00e00b4585070341c0c680c001541120701c94020101c1c290b809003d000d00d207501841800e5061003050400084000c01642d0706c034540d502c40d114000058008010820806030011003155400b5804005400740307203003040064540781c00315070001c2840d41c0041c0c041001d024080b80c0d07031409907030410000e0101d4a03d130386180f00562041106140110103d00c41c0700320f014446d1103a42d00950000b802e4442868600c03004440403101002d056500c030060240100108515100c1c52520000c4041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 356581070 1250 356579820 356579827
    0x10603020408010b0a181e09053702150c0a030504060216051311040b0706050f070f02060c13090615180f05190509091c0219062f 57
    0xa0b5803070a4903138038074285000e01240c0006201403881d03c182107980c44611a00000d161510b5410484580c2401d100c4d1899035203480c2c14207041c4180030620440d050885005401200075070001255181200301c1c0b80225591071030748a10062408861680d020340c0c0140e25030703052030380003e035003030900c550340314200c003c51000070301004060740500480034181c08070494408000d00d40300100e0300400380c0700003001180d0765032441c80500c049620180d41c090070102c4200c603100c07151860200024030060300c48044280c44a800909010320812001c21069156070140440c0d8480110b42002c81e00001141110510a810045a100da06100d6480207100000302445071035040c6401801c8400d000d24201c044124002003403041c0c550012410040303880940c2c441262100b00400e200b5801c01ca0703001203500c592210140082d02100059070540e51040c00e90800580c2d02ca410181e036940c004800ea1800e4600c0d07a1040c901140301c2c0d51220903078515006180b8550246080300709007103520420f042c0480358021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 356582320 1250 356581070 356581079
    0x9030f060a20040b0c010216030210060938030a03081006050a090e060a0e0108160b04051302031317030901050702010212060d02010c1e02090f06090c07030c0b0106030204 75
    0x2d008035012522149010541d6111454003040c0a2040e802442407902e03001400511100d800d604403050003200003100f4112100501d80251150105c0c401c5100c0b0034184100815160580d20038010f44006805072040004880c1840d060007070844040108641190f40c00040182c90034442080158844d640c0d05615142900c003030000d20007241c20083c100034062207100e814a40007448181941d001003175410440e07550704009202c0151a402020200071a000001010140096085650928080004d4035181c841510b540340340140d214541e405549240b807016103448690086401900d2415003089040440d2540c5052145881052314004000010004c001000703105080d0851440c0c40207616254600b42c3c007920001016020911611055281c0011a80640001100e99500241c1c4408190088007802604001000141d028803e9400080c000010700d0b020740e44549002814458151105500403602d07800045c811020310054030080c00204241c41d0740d6900a225070b507400742e562420b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 356583570 1250 356582320 356582341
    0x30305092a010912020d031b0c0b04171203010b090103150b0c16080a08210c03190e070618032a09090c031407090216051c12020f09030f06 61
    0x1e84e400207080c812090f400e2001030b0340e16030342e03008159090318050f160400d42220040c0e00406500c030040600d0541400003407041c5400700940210398003082c0080d070307801c4d04020281e16010b0303144030703920720b0001040148000e00d565006000c100c10b06140009210300683c0080c40440350a41250b4645903010805c0703180c050040007054589034811000d080510b00d07021009075200da104500416045012a42e040651a0032031460300745e0b900040032203007908104c40c00c1c049991040e201c0c50055540c003089041e0b4003509000303021032200e0b20350061582c2031800c0c81c00c03101b01c02e0080d0031207804500410000003044000c5107010011001c070b401800c1d941da000015180c0600f45902140d03903e8100500d500204c7d214105600c00c0b00d800810000011840b101e0355030a040150304031f2030400d031011645002003c0340390352120645202e00200d03240e80b090b103500036584168030f0140c0c0c0c0001d48800e44c496500741250300640380c0a0000110242003090420029080035012421200f4640c8054100642c5000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 356584820 1250 356583570 356583587
    0x2040b0d051b070b01050105070201142107020111030604230a0c08010504060b18130c020c0301050705040b04180902090f04050714031e160617060a0f03030305092a01 73
    0x42480924a00b0f40250348601c0f00000500c125410700501003502e4040d039001f52143c92103901c0e01d082c03056560180801512841d1150001408209522000a042e40307005204005140c03c0d04000e42e403d654071001004080c04021540d900502c000d08007400c40046040c0000b4010011400c012807104d8036003000801c140c40507480188a6818064100031400b201c40c119100246034001c460341d0030138008045041c00000742401040103281100e51441d032540881c03500f00d1104114020700c03158541110480c0c007401140a483c480302020401000500000c1c0e580394801e1351820408035001c2c000c1d800151506400701c8032280403c002c001000100042800700310068000c100e01c0c0d80b85100340201007551007030200380445141d80820300e12540c0b18020808851140084042c0070708441d1100d60040c15044403804002c0c408000d20049a82d500e00025041d055540c0d030042040000e03c1c61710110050000541481164050013201c103505041810390078813030711421400d00300d80c0106038000411244 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 356586070 1250 356584820 356584861
    0x40902030a0b151b100507081914060105090117130b0a020c060f090106080106060504051c0503041214032b0c08241f0207080303190207050304150207050109050906091902040b0d05 79
    0x32b00d401008040340100480c1d25400c103100b843c20544500221006844192580402254111810302085180d034030b182c40c020750207485282c0010741034446d81d02d00300a034090010951095040400000e8404514116095025400f00c0001c40c2855840108900b140c00070b8119030300049000030240124103240301e40b00500b01e0300071a40501c0001c07d80303030350391280100c1c058020a10f244441140a210000024850b19241103040c0da544140180034240030281803000c05480380d20341410040700341002d2040c0d0403695143d07214a0b81c83d958103c040071561098104401504903a5401d021060316000c0040c801154689000c1c0c1ea502c9078410080c1c90010154444021f0350300800400030942d030f5000410031000c08010b005a03c41d19a450710303a003140034507000740c030301082d03440c620710300186c0d000400c1c2c01202e0b000e895824146890300c081c050b89980071500306400c003202c4400319a4504200c03403d16007880c084100182802c0e100e580b9408035510803203c0b5000ca036100c2e001d00c6025880c07125101d0b01c0381c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 356587320 1250 356586070 356586121
    0xa1e030507080711101d01050a0204030233030601050706050403090816271806060302040609060803071419061406030604051e0c06040902030a0b151b10050708 70
    0x2900c00c200100c1c3c2c0c0b01210410306440980f1b65442000c05004603855402240848000b072005141110b0301d14000d4000344000d034400c10101500d4542c0004842118031801c08480414000680700c1031031912691000d8051810488104400800304400c1e21600b401184281e5900d00410703d03007102c0f1898200d00381403903000003800380320411589940d09540c4100d18101c0e101d40e0305803103d42500700000d290f2000000d07240b01400300c0480803c51954401c80c140e078401c036800c01c00e040e02c90f02c0200c211445401001855402004614007261040c6140441500341100b1192400290145800442c0001000312002ca495040c110381c87d00c030b40c064846d40400240e004140360702c1c0c40e88a01381d8491580b1440c0740c010004441d080440881401010500080034250300d94442d583e0100030000c1d030003107511050480c41c1020489461806026400d5040d6003000d20505181c15040740030540c029000c1414054801c090400405c18514000c071485a6410744988800d482c0040c2c6400a0b8a40320f4020b5205 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 356588570 1250 356587320 356587337
    0xa03020115050d0f05070806010e04120e060901210e0114150d03110304080105070f020c04051b1602100e150a0c110d1a01060905010311040b0a1e0305070807 69
    0x640d100c03001020145500820a08032421403405d03d03a0038620580c02680d21805044000b02c0d180b165510004d0296100d0107124003040e90480b4222407003161405456801801000141d51a41c0318180400d60701e00f84540003a0440081100d040454007651606c1146035100c00500300b4030403651540036844904295141980c1c9a44000100800014400101403000c0c032050b4041104080003924041c200b100c00030012800c05400c0948034607000c5250000510841e20712110034201805198000c0c000740290301c211503a03c00b0008030a80042042603540c0c045540701c14056540c4502c44100500251294240c581c03109041c01403400c590300c41d04641d81e030100325003400658080781d11000340360801c06c0001c00540017400a10151040c1202501e0105100018002841c00c001d80d141201ca0300d80b5034000440d40c2c0c8005605036900c0c6244505070320014001000003040314402403803424103d00c0c100c0300320300e0f070003150100d5030403800304090000c0c2e44c400811440541100b441a000045804c20111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 356589820 1250 356588570 356588579
    0x5011e0b0406030203090f0d09170114010b180a0b180603040f020405220b090d030b011d010c0c0806040203010b12030313030e04060311040f0903080106031a0d03020a03020115 77
    0x200d48a01e22442c82016800000990201c0050000742180d48800d810344a4040c0c1030f00004101904030700821910018440131455144014814004003408200291110f603207059481e40054110132800e428441010748000c0c041e940301e59668002d8980500c075941c072513070300340020146210003500d0a405002d0030000d120202d102e0071001401c03160304440210b40b0b580d404801d0001c9810722055000082201041030341048642c0310441d04c50b8420404031060283c507510110165020035151602080c0c51107018030308c1c0403500300c0c0b28a010340e040c11300039015003161b50352a0f00e2611541c49810940c1140090100718a420b004203032042c8000c40795911308e10159000c054507440054011180814140b80c14000c00d0b004240800c05280000c0007004210b03560b040001070314035145440e5105174501050711040304060b100d20190a80c25035100c981c56805c2c05002e600800b11760440884a00c21940941001c0d5241c10445003921300c81d5005c4d15400103540b8000c0c0c29104c007100304a2011720300d03110602 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 356591070 1250 356589820 356589839
    0x90302030d09020d02060d020a0f08070e0111030c060103080c060115090b0306041b020a060e030717030c0409090c09140c0a0c022b12020601060503241305011e 70
    0x200305500c0c1c50301c0028507190314800510302a20741403009402c0000440c40c560f0940c002c2d8040c0251070b030140c07030b10014101540d00455103088102e6452012443c0540940c1c003552280c100c0c40b1900d800882103a11f4909105181d9150040980c0300701c944043c00650081003030000d0200500420b003410a101d640c210a1a01030030304017060041c0c200c500c6011000801564135a0003c40d600044100454400c03100c2520003500d03000841411b4510a00340018008003d030000121030318036810652415026054a40d503071020703400a0300002c1106000c2c8408501c0c04998801c0c0d0005078030a03854200b40a00c0c04a00b0015200c02203140c200c43d031411400c1104407100c40c411143d50341240d203080d042402d0203100040f0302c0c0048490300c07044140b2400d502c440e00c842c3d101d841800075004401c1c4d14588507091308201d9071a182400782d0300000b5824000b0800080c03401c2c10380e81d044220305a1010900300300f4004610118444000c442d9556180c0d001000300e0303d0322105d040281c0a1629102c20740030308144450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 356592320 1250 356591070 356591077
    0x1809070503162714010303050c010c140a1b050f0303010e06063a2f07050c010806120d08070807030e0c1c050f03070b0a021204320a05010e0109030203 66
    0x240600f1030203840b001491840380c0e0010075003080c16280c848495840c0d003001005608504005441503103045804840c107070140b00f00a1031584511040352130711180c01022140c1c2074000e605004040c555080034030002c0c1d030074042c521403002c0750713401581c996142010b0501c1c00e03e0060903c601451041086100f1040010401400e0005d03a14101100501c0b56103658104007100141c100224600300c0d01419007051340c1001c0056078039454420f04c1d1282d40c60040001485903100043c019441030030b960361103502a2600c540d000c04000c02c1101c80d4800308103524144220140c40d00300284260040105081d00940f43c95006100792504000020907541c5d01c0340e82e880440d80441c4901d20014500c1c000301d0150341103081c41580072050390402e400300c82000784e580e0024402143c0c022100360020302038801a02c20744021600312601c411003901c698a41c80c044030f560001800030040c840000d160520050303400b601110b4220401800e00301101d040960848518050000e84ca034100b11803403010075400001e8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 356593570 1250 356592320 356592359
    0x108070804060504080d090804090c0201060f0e0901060b03041a0907050d030318020a030b0405120f0406030b0f090907080609060c0301150c050d200d02031602180907050316 76
    0x406803124180f10001b8000e08003880720f49401c14002c24204640310000e031003100e07801c2d08140301c0b0007100351050342643c0d080e026500c5034501031301040150b000d100c0102c80e04a28180b000045a944850010401e40e00407242507801403140ba620102d003405562100794010002c00c00b4042d00c2d400c0000003002d41c44034207005810180c0340da206500d00c03d64000e84103000382d8020021a0714a50760b15107080300c03003021a0705494502540c48180c000081d04411103203180a030310002860181031140030383c002d2003040d10b81500024065680c24207600c0d2501c0041c0244110710081400900d40b1100500e05200101000f009070805020f000344203202c2001d590640340744200d079420310030402c0301c100e803014101203024040c2d1044443c1300e181c41d0341101c0c0399550710300d03100083d2911511071244a41d840d500c0c0d081c01c0006a00412203a038012500d640d210031520320042146881d5590110440300100c4207440014154101d00805c2246107400c111200125500c02c008d0380c02d00345850040720f80c1e900716014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 356594820 1250 356593570 356593583
    0x70c031413080616140d271518060c03021611040e0f031e0d0f020d06120209070f11070803180a1203080403090b0a11070609030b06041d07030b04020f0108070804 71
    0x40c480c10703c1b20140c01c088100215400c0a10030754860f0401851100300144050706d800c58080d5400c0b9100c0d01d04e0283e6107202000c06003003c00580303566100c0c00107000118480c42099400d0046c019414601901988200e00072414a51942c1c406020002110100782417118164030400d41d0300001e80000c010783c0c0c1030040c5032407244030902a850030a00765110302140f03282001e20b00203a8100319041580609815041c0c0b100c2008015140c1000ea8001d18030180043e40c0494001c00050800344926440d859a08052815102c6103000300002884c00c00140c01805180c0c0000ca00c00702600710150003101004c03021100b43ca0114a4980f110550005000c0c020301000b0b030301e00c0000e0602d402091902d005243c089291543d0b000c00c500300600c581202110f02605001c3c501001803031070b02c0340b10000d00341e90700702401c01c02c140c0b07c05040100800b0641010007080044181002c20b911091290000450145072041c24902e001d204128102e1034100b01c1c113040c0440c940c02d00035030342d600201040c1d00c203600c02d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 356596070 1250 356594820 356594827
    0x402070c18020414060f1b0309150702031b0d060c051303060903230409020c070806010b03010905091501060e040e010510090f050906070c03141308061614 68
    0x18404684000307500301c140c07400034441208551a070203a0050089660444000c80d0814007401002502d104800d1680c05552003808540e078501d43d104d507403d001c21080c0048030320704000f440100b0211000000c1006003014045800020742c141402b9040c0c0300002c410b00c8500c00d54240300000c1c0405540c0300045d0040740e5034820a802d10740180c0c21180b800740c1101d045864250351b481c1c2840509442c103c01c034001842500709100920384082c40b1034840c006080f0440c00c203030501d035503c00250011300c3e1821741c0340b01e80880040c5180c010710815010b404070351151a5250305200a5a041d100c0c0500b510706e640d48100b440c045040e4000607800d0558007586440c03000d108540e400275000d400808401540c139441c0c9014007081140700780c1c0c560100c8910303220901403244210f111904135802264031003440c1d0032540020f05940d1261400090051090408a00400718034116550700c0d0402d107490001c00740c1503081800030340000c01007203500000300241c02440076001d210040480325005481d049061010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 356597320 1250 356596070 356596073
    0x70c0b0415050c0711030a05030301090b0a0509010305010501170a080f090111070f061d03060601141c06030606090c020a0303020309030d021c0c0f020304060f0314070e0306011202010e040207 84
    0x34141c0741001200000c05028500b008080c1e515203510103403003150800d03c98250422603050116010103980d8009000d5815030386000b01113806007441600059003d80710b9074011400c0da0b81d04190502a500440c00000c0b198100120301700c0f9910903684aa209502542e0128001224a01214086440040001e4942140c40b005032554240c44556078158020111302045507012a0f01c600110382041c0d6031045004071400c4002c00005030a0f0200381c0607000b200003d0025400303070000c010a60121384103e4980180070302d40f0040144503131600025203444200070418441640640790140c5068202040100c889030b5010b903807411000f40080505030080f0004170703040380c18002d480f14012025415907540c42180c5030300720740c441d040d400b8040b1146003401c80c0a05a10560b19007241c06250b030011441c003402c0175815a101c041910662007059126491038845100201040340900d5868642d40300070b40710882010300f8500140c00c00141c070b9540d458481c015030391050764484448804d8400603541c0031075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 356598570 1250 356597320 356597333
    0xf06011107061206180f110906030a0b120f01090b16020c040c05040825080c01202404060606050306030a02060d0222031106030105061206010903120f02060609070c0b04 74
    0x9602c180c5c034481600100b2440b00900f6044a1460f00c3c6030201000f440c07820340400c040038062042e070a034000505100103000e04c801a401010070403002040504680b00030301d41d030fa140c0b11b14001e07641c080341d440350445810059625451600803110a07000d20340060803020082d81d41da88071003414810303612491440640e40c000c07401c95010301301041c10360380940809140704404401d0701c0721280301c070000c01d24002640000881e0120403681e0503500c0e5140084c030b00d1054490880383c14200c1610303020341c540401e03000c200174440580401c0034205400c01481c2c00d050003821907a06512410074441c0c2002008819a0301146001005904440081d20340345050900002400341e06440c401216200c0000007015440044800440b88121a000000c040348414840540800e1040310303007102090009000031a01040b00a074401d90601d005082e450b40c9448412881000501d1100401ca1095002d40c00d0341d41400f0440e4403840580c4e081c1100e06082400802e118500c0801030714541d45400800d082140 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 356599820 1250 356598570 356598581
    0x23030f030f04110301020a0f0905151e0f0a0f0e01020c090c160b1302190506070609020f030625021209012d05041716180e030708030f060111070612 65
    0x140139000315107400d0088005001100c28104081c041951440e00080b546806640d40c004645150091810518405d282e640b0382c8103d00e42c1035130940428000803030903000d40e4016040c01409076507841d82003101000301400039501004090b0464000c80c89018507600c40c4440503401c42d510f03621ba142d03150014500820303500c0c8000c0f0004c04001502e070902c501007544102c1103122174022180d401200d1589038100c200d40c261803183e150008024400030000c200140c0c0301c858040e00140100c4151202900082d091030811208072110414040e28105450700c8050159070140c0580014038511603a40703114201c50041e03e10640c1048407650700300d0896202590902500302e40780d4ac40c2440c0440d00040648141c03c03900440746440250b40e07004403601e90000c0c182c40701908051a40503154104501444030901c545c1142c0c0b0401c2c1c0f100b42446480904000915603d4007a006450322402d000d920f0310075607400980f04604025102821a6840300c01080035070449416080020411381c6001c1860042c0c80b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 356601070 1250 356599820 356599853
    0xb041b05250506060f0a030308010605091219140a02030303040b130b011203020d0e0609010f05040b1b06010602010e0d0f02010627060b0415030e030d020723030f030f04 74
    0x60000010707810060001101c40c0213202c21203d002d1426021028003502d11001c0c0f10280002c0d000000402029000720001e140c00040a03040e10211003224140c1480c1c0402034402c050b06d22035207481c0e4002d026462524480d058070301405041400340e1500025030300e0001510242c15080350101254a20006000964007981e201890810569448480340070403d0380b648190054016140e405941d81e200c0d54a00c501694024401e608000e0310400442c1c03601465908a41881020040800c8002500d00540881b40900d003450010094a0030391904001c0b040c0d102d4001d582c10014810f51150001c82c2496555203e0b203012604d01030012400c0f40501038940c01800c13807101001c00707542114643c500e00c000c00c0390b54500500040740d0b1242484921301c198402c0038800522800d0b9258014401c0d00040c5c445005031040b07c2c1040d1181e00d02500701d0384814000c0302e03040040101540100c014049100109800f0006103040c070003404030b00500c6200061075280e0400d5480c00044c01c00c4a144490440320 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 356602320 1250 356601070 356601127
    0x10207261603050c01020a020d03050d1e0f06050312120406060302090f0420060f0706020c0102031303080a0b0d0b040311100b0406050604240c20040b041b05 69
    0xc1e209120688514140c007003a10301380111001000903500000380580f042e80d0183c424140c2d014641c404032a103402c00c80c2c00a000940b512a07000030708801340740020a00c41150f000107820340304202c0c5041256074585c070180c040d400c0b900e13200803000f0828099540b40c0342c1c082d14034140e65a031407410b1401045142c000950011201050209012151394202c0c0b003148102c6848201400e07c0200500842c0c0801045a1000c0304000080e44004035101500e00244031b583d015091800e00c00585003660070450310381a21990356030380c00052542c00000303a60484044841080b1100c01980400c1400c00414400703003c3c03288160100e010140721300700c1d2050784a000380c292501034401c00d443d00c2c00340008000e460b10890a102d0041400c0c600841100c045440c0390072400388050750031002925504016a0480500209400040100d03142e03200a448020312100c0807404c0c0c549540400048480f0b0348200d0340a286480001e078010361074454006100459130801503140d1201c01880860300c05001c2101600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 356603570 1250 356602320 356602333
    0x2c0c2701030309050a0b120402060a0306050913020a27090305040b0d05060a050a0b1b0c15120c1603110c06040801020315040c0c031116080d0e0402040501020726 71
    0x500d50300c5407101c03041ea6000c0f25002e441a81d1011b04002e14000c0303000101030f45000201240c010715010004101110082c00d0101d0065620800a1002036040b1480391a400c80720300c094086150003e0324202600d552031a240e01e1407401c4100a104041e94104006000d60390150201030501500644006024103012987d039402900da1003400b030002992014052200301101103840c5c608160301c00e0903120710807006030a2001c0404a806821790505070700289016503c42d848560703c070200c041c1015803030613003425512025540c030410b8446004240c582c031030405116002c408001070102c0c2c4081d0381c040c0b40c0008401c840f4101d0500304100da1100303507449103001500003194581900a03520030907461f801205151f548200b4081602e4400c0300030800034100706100380000340a09560400003d00e58200c0c0c880d40d1586100100c22010703500003804984c080c44a0124882d4004210382d4400f40a4809504251402c00041d54907550342c0182c04c003da100540c05120f00e0300c40712100c0080c10590048402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 356604820 1250 356603570 356603573
    0xa020102070201120c0c0201080606090402040e090f070303050a0c14010614030118080f070804051c022707030b04111602010f0305010f05061803010504062c0c270103 73
    0x70351020000b01c1c0800c009404c1102440341602c035805110b40640c44104c40e840304d50380110340c01140100306a500c07000521801d602910341d440900046e0801012851440c146154858501542c80810703140d503500022081c400a54040f080c0c1d5000d56180c140f4403030090051408130039030030405c0c440200c03030f610b231100002d540d034070400481d070f441e460a60082258084028214001d5001640058001c44040008101132000b5100a040c07150042c0c903130505140d00c4d000007880143d01404040d6460001001502c10351402540e140080010010341c06020050308c000d2144003d001401c60085c160744640304a5592070f280c000249140055015942e10560b2800101d0341c0020120141d002500094160301703442e001c0d105642c1070301c07042e480443c0514070340402c10100340c2c05104000c078411704514080d031454809001e258021845404041110540d021174031400744500110203809803005241000b1010700410500301c04031060b50061656030305240768480411182069005407941c1400010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 356606070 1250 356604820 356604823
    0x31902030a110309030c0d050a0503030c03150d110f0109080613030201060503030f0706020a050f070c1403011a0d050c1f030f0204050163060207030807080f0a02 71
    0xc010140303a1101c2d801c45040020700760740c038081c8a8509030903901c104402a0280340664902c00994451070444001c1d0640b6a0740d1811074105441d5044812000f00c14070141d21401003000c91600800e54000b054001c513500c9d000d0303441e565403c0310350003541c102428800c1644140503101c0640040421650a418000c189021600300c2070010b07001540b0300030b008680ea0ad008012907040003141d800142c14000d540d1a84c400942c8590554800c1c040100030300741100c3c240401500031a801024001a51031a20761016482c03040e40c0d600c7c034401e0345845010004a6060088840c0f607500964503012151024904180b425969144040d4440b44a0510740842c03150b8589410f0407011594042c0410781c2c18201140c2a401103008107400316000b6040c1610032a00182985150b01c900c05c940b941148016148040030080c0907503503100008604e03c01c184a6010004182e4141d034a610090049490120000c0d00c50f070312800000e0889000140c0c040c144031005050f250700442144156503034010304040a0f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 356607320 1250 356606070 356606077
    0x150904050a021e0702042316021c020d17011a07020a0302040203040f3806040b103b060c15070f020d0809060613060b031e180d0c020303190203 63
    0x8901c92800c0010010903e002c048603040c01422260947c0c2203500c6050a640d1072801c0407510710114858850601000195101c0b80644000350380c018003400c41d14249c00a281058001300840c10503c030f14010024881c04c500c020b070850540350780490f03c0e08041c1c03002134901c1030356901c040d51050012003800103000c0c0900054040300d00c114101400424410281090700c1404d00c0c094640503170700360040c222115518285540310305c0003000014015012400643d402d000701c5540400a01105041c44546003815070710b11200301940e0262806050031013000b0f003c038000000c1c09011b040301265904400004005182d4030119101032102d803454402d030000e1042c50071909030b6005105800c2c92565680c09880b80130b0044d503251004e400181c0d145400e114005001c0881445882d50702e0a0018842155078007550141a0800e041400000441d1032aa42c609000d02440c0711410780903822403c0c540300051400c5288282d00b48020703854860f00000e030942c0100406011201542411a007110340d011004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 356608570 1250 356607320 356607323
    0x90b06030601060c03020d030903020c0a03050607030b030a02060901030c020709110d0c031b0e0303040f090b030c06160f21031d070302011706030a1a15150904050a021e07 75
    0x48076010b0381c1c0c80d8000c13268442294009005a0003400e10f0008061203900000344e40c0340030380115210403200c60301044484540d0b606c1607d0a4004d030b800e0003803c0f649401100361030362046004103098046500000e585102d02c4042d50b061665501461001500910016000306040361040007444580030643e0926440a85042d6102b458080c40000d40c074080d20480d00e00c012440d031031a0350000c09010a42d2060040d1103810b50521040c0000604034a40701d20140180c0501c50012490244d01024540b500c0c1c403429110b84982000d21100b04602100010000030a41159400b080c5070002d04100100d0750f08500350103010341102e1450040541c05800c00324000d069036165071407590300301e01110307142c88840c08000d00060240f12644075008010304c02d40e07001040201920b102c1c0f0034030b0341c5492501070240303852070444c0448000c00c00c80d10300340c1c6241039901c041074420005560040030451121303c60401202e1107559907901017140301e4580e5041c2c03044041d90b0758284540f00c0c619501203445400c2100d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 356609820 1250 356608570 356608573
    0xb090c0318061006090f0e16090801231003020d0605100510050c060609060a030b0c1603180503030a080f0414031321030c140120040801050708100b0702040f090b0603 73
    0xd0010b400c01203122808100d4100b03254824043d2100c4003451580c00048d1205e408100c1102ea0105d0011020301c64219404d1203074005083d08150b00601001e1108028200240184210410005602c4c4d144c0d046045952048000619950721a40d403001290340d600701c5e640001819000c440d40c03d07040802413014002600445a1a42c1d40500704460100100e9129030800121141040000d018503801c6410040d001c2015040a0000380c407003507100e00c940403d0b0001801d00d5880c407000c0c01001d01c500b015040584c0036614040141c00040c0400c0e40152a002c03108a82d440007406001c80c2d0b882c526010f54100c0700703a035078507002c09410f05108200d03409408001580d8409040c2849020001e8030682c1ea03168489a0f48103a1980700c10325844007080601070035540743c0b2400c4008011140c5580600c0f042400010f403960b003041f04190031290010300303490510412406001c0e24200b4005540304403110810180c2e034030186440400c002c1c00c041e4806110550915024404100000803058441e603800d40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 356611070 1250 356609820 356609837
    0x3070801081b0609120102040e041b060f0507110612010303120c03090c0e06010c050102031311010f09150c05010e030406020c09041713120f0201020d030b090c0318061006 75
    0x12207145042d000282e0a0358040e208011440403800c081d00400208030b40c03a80010300f001d644030301003d00705c80c080718112201c40000b8032088201003020300d42b501030000b078a01000f0054050348064243c0c842c90070060710083d881c450303025040e5111012104000d0001d86108031550f941e24001c4c2441520f0360f100510b0340e04107240006000c3c82032248041903600052000585440c003611701540410140040d41048054888600403a20900096005d148101000028400c50b41070003041412101403480c10010400142c0d86415800180b01096883c881c000e0401220007403001c2e54100102c0e040100070794207206442945e07440100180c41110b2040e0280c98110540400304505a80c08a50040c052110302c550010700314a81005869075581c505040e040031b0780c8462064600010b202c10807100e40300a010401c0455034180003582100c0ca441c1000d00001c01c60f00001030602c400101b41841ca0400400081c01413980b20803a0140d080d0000b05407281424500040451070182d030050501040314035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 356612320 1250 356611070 356611093
    0xb0d0606081b1f0e030d051201050a24030f1a0f101b020303041206021804050106200a0b0f01030b0c04060c1506030c060507020f041802060a03110307080108 69
    0x800d0b0400701c44004003100b0f0b4440301c2c008540b600441d080402030410068501400440d14200208221840182c844a86a80b011652100941c50580000c0e0294582c1d00081014042d00340d440444003044242e949120f4182c01010bd000340070b101c40d10b061035410440740ca4201d03804c0070000d1a8610040c0c400c02d084002030f00600445000201c10500001d010480c052500c2d241202422100e03440201a01d242c560b50319889100e2b15102e1506481c2c89034002125040016000c40d040b00040c41564140040d615004019003298043c07202800b059107030400c011144d41e0240100d08069510903015a40340c01c00304035001440303209000072502038068101180e05100120f09035012036040b96500c0d81a000160344560b000800c0410207002180c41743d4010000400c0d01607a00041c000036911952210800e0040140d0305909a1140b0b01035480e126400781401521030850341516015500f443c1d0390320703960a08400405203481c0307100c50100080207101d000c540c003003c41d5048a100404407400035006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 356613570 1250 356612320 356612353
    0x250302040b030a08191b060c0e0a080d12020f040b030115020f192603060102010b041a04020912010606030c1709070315060f0306090209070804081c0b0d060608 70
    0x88000d44000014449452007261019446403010b000d49820501d005429548540b00c104400080b201e8070f48900380e10450340d0b8400f07a0003910308011510720180600d007655158550702040cd03e44104402d4003a01c0c58400d100350121082d000590301c08a40d030b140c0d1144408031940003801041c030700c0d015141d908411584001629110910804090a0340e030300c0d580001f4000100c2400c0403540300031401d44100c1e559a183c1c1d1a04044103580e6551940c918040c40020700b12924004414807440ca0001c849140c54292000074051850a0f00c0042e607600c0c283d000030b4402c4840b010307095440d40c244075000c15403582c5508091401c201588441c592014080c0e00800207003c02c50300103420707034052541000469000b4442c3d4441000c4038000091464941c8911000015035810545d4920b840d0910340341103080140d2404c0e40f11080b45800d1941c0d0509540e04001c0e403082008207a41e0483c141541d00900382c45c0d41c800c005c0113500800d90700700c510f40351134060701500862203440c00f03600552802141c0e000c1c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 356614820 1250 356613570 356613583
    0x201080601050f0301050906041b0201090b0112110f040b060301140405060a08190201030b0a031b060207080a0809030c061b011b020a020607060b092505040b1605250302040b03 77
    0x14540f04081c00c503030034070050020040c00101000e40c840d485105d50545a403407130080701828502d550011840a981d41008070b000d4906a02001e65000c4101848c004074007003290700200201c0407139a81009803034400000700608600308541c0e5001c200003000013040342c641703203801d0b52924058605010030360ba030804012401010f031052409541211f00385012014000600d101880d205040004180c4400c6000c0342282e051600111180b4090700342080d440c2082403c00c0c40180f0240c8000c00080d414118541d840d00740790403000b0102c1e01c002c00c6401d103903a400e1142421801012f80842e4840c070205e452000400c4c540d501b100303500d520f0f040c0d503c0445503a10708030301d6404041e82c0007004411910340c03d20109500141060b41e005948500c5080c3d16134624818074040c002e0619011307166150404012111104a2000410702c42c040100300b2004900d00240d4122840264003100045900d0400c4c81c1401c2c91422900d003420303003403c8000f41c94001c8450001c140c900913603081001807500400d150340c501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 356616070 1250 356614820 356614837
    0x105090105030114010c05010c0504060815210f011a3f010902030708150a18022e1d0102150105060a0c0b100303030e210c16030c03020108060105 64
    0x158100014851054481a1407041c1301043c0340c10000b404160325030508641c501114400002c100003010000982e10806045d0410032800c00c051200400c80001611180130911030b40701007480d0098450a5001030100080c00081103000344607c80d4004103505145030380d040414803411141d103411841d0f26418080c00718180c001d440000d072014655400607959500c54240502d60b640350313a8840d00684041c03040c0402805000b00070f01041072495100a1403400c0146010496032a003003070b03910b09600c1543c40105141d016500c00001800900548821411245000040782910960902010b900506031814660184102c080302200c807001240c07a08403c500b804241134482b8014011450460000c1c5611449402d040c0311107280c9a480c0c3c2502e82085500c4904481000c004109164144c050070344016142400b4205503003184d9965031510715040e007916002c05e404650034450100410107002121801c00c50502e407a5031342e01e040c84400c011400b00300d000440b81c2d0007290165004001b90307520316 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 356617320 1250 356616070 356616077
    0x2210f01060510110d080a06030c0b04060e0d0302060a0b0109030b190f060b0d020f130e0a0b040c050a030b0a080f0303010f30020d0b0a02070b090c0117060d020918010b01050901 78
    0x1c175040744c2201d80b03a2028007050542c0d562000008001031011240c00020580c4a1000d5140c80c6000380c041d000da5501c00d190b50165284030009400264041005a4899119500025120302580040b40c82980c2d03900000c28181c500000e03c020b00448812642500180361400d02c240403074200b070841038840c54421102002c1f81030001460350030300f0750054032003101058822405e040b203600d5941d040c41441e41c0504049052207080c02100b01c094000d0b0112404191001c2c059011103000042040c072030340c5050b100701039440301405460f80da118a444020480755044848000e0369001c50343e2258000c0c412040640c110b501c0000301a440d0348a4003a40d12a200d00c0c0749031003920100652061f000f03414040340d0064000c0d00700c00014011040c070600407501c260005032142d100b81340c418412030f000341100f5080e03800150740d204a0381c0d10440500c1c4001b0000c1001d83d440c0c41ea200030444c841e060f000029401005c0c0c40c00c101c10110001008070401e540c60b4000d002c00c2c10420010f540720720541d01d00c41d001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 356618570 1250 356617320 356617333
    0x212090f0a02060f190915090e0403050306030708070b0a09050a03021005030703020d020406030b10030b0604120203150a0c0f1115090a050d0e1008010e0402210f0106051011 76
    0x1502c1d000c0050824113030030b40a0f052030700d0503040d0114806903449a0340004a1500c001c140501240207400054519081c20411112410082a0007113000c0050000b000c00c900000050201d86040c0716101c0241280821114050344804400c180ca0f002110346500094070703200c0010b0f00c0c1c505882054112030f0041c00d40041c4184806080383c40754030050144c41410b030200b081d4500200d02d840200020f1849990000300f8249010410800040446c400420181490000c80c034a503210401c4078216408200c8081e041c1c1c1c0c3da84003080c02d0484a00302055400903c100b0403001c0d0721030b50440b6000001c01e5846040c074244420301510880c011a040d01071540c00ba2020b0840042000780145e0000410310480c0e0000d1201d42d01c0910705001000144c00050860780b0440c287c1c00e014200c0c444002079410501c05640c1001130b502480d0500400203480340c044003070400d081802554071207044000d0042925001f401001001d0b02801851040c6400b40040c0541c02000c20310440c80400106040c0b03015000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 356619820 1250 356618570 356618573
    0x81b0a0f03080903160618060f0f2007140a0e16050d1812031d0a02040b0402120901020a0e0409080306120c060c010e0d050a080106051c0c02010212090f0a 68
    0x39410071211280c0520640425205d00384202ea1050010b04040c1d40d183c0c600c0010b1101000b8106a13a807020044c800822100400d40d50040d030700540ca4141441c00c2820b4044142002201d1800603091481d9401028000300d101c1e1522030b1003000801003a520015070715a01d0042440c20001212006442030401c486884c0300d502c00d1005080003429050040755580506079040c82181e03024908841e85000585149441e079054003c505641e11810091500e0715000c0d2815034683e20080c20080c030541d40c4548480255481c2d0781603078410806014038102d80e00e05410300328000d6020054610118020352003140240ca0a0b0103040e2510790720450207400d6403141c20501900d2401c0703450b00e1419000c2d088100c001c1d0b4580d000540810b400c007400208045c0300c005501410404c280031503500700b102c00c024003a441c0b07800400c114110b40c900c1c90425510000c59a10b4018201c1d41c202d110102e505000c12001080c1e0b054000e40300300c00c0c07400d00307030102512a07291060b40d43e5025007411203030b500300d0740c3c4080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 356621070 1250 356619820 356619833
    0xc06090518100504060608060307050307080d2a1203050108120702040c0c060509030a0908031612050f0d0906150819031e02010905150408030a0e1006081b0a0f03 71
    0x2d800448064481640544030b80001d400c0e01d4242d003040000071010350810115140812009000b00010341c080d1035514108890b19450300c0008554070240128002002c207a6103c080c046580c106841c110083c000e4424607006041814a504c00d00003c5d06080020640703980200f40b141c0c94036410364507149080307243e43c05d00020f0311080004509001c1c3d0010040041841805403520a880b4007002d140d41e945000c4014265029541007810a0f500500801e8050140e500540b0600d40c0c2201c54081549800312084829208000b103508207004003007000c4441d030985810101100744152000d200084401c040300d16407607814800c00b191903020340081d522000962440110641c020b240403240c4088298000d40c100a0074180140103039034404030902800002d22039844904c01c2007001c20b440d07007002e0b19042c2e440d001c0036241c0084546c0c0d8400c1e40d000f080c02045580d640d00900102403041c039588804d5141c5509042420849140d0700d03100505040c070b8080980c406543c1a031002c050f02505517102c54 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 356622320 1250 356621070 356621119
    0x512040e071b02040c05031b0309060402043303030e10020a03110111130602060601110c0f1c030e040f09020307090b0d0f0b061003052203140d05040c060905 69
    0x1200c0c000841058001507100c0e4000e64a10005c240c0342ca0303079241000310799070400d018010329504005400f4004e101c564107000c0b401942058044074081404080892020304000342000300c00c056140d030904201c500c20f040c0054404590107a02c40b07050301d450500034006842860140b0f0401a08400c0765a070009016401d112130002d044000002e403440040f640c2c0c501540501c0c10b51075240d28514041101d244d040100c594420001c2ca010500100d05003001c641c0c49000c20501d034483c1180203c0300031261540184480188600460100321441701d0601030003100242008501642c00c5c540c0100c142070b103501621140541c05002460040d00d4040798070014003001d42910b1f0300c94210018000880c50045680a03502c1c000c14094100e4203001080100c0302c804889800700785030401d0104500d07044074032100d8a4882800359002010b400702c0c6012103c9401c0140182e1840c580840c0f0240a4461980001d21841c4900c01c0c059176940c0300c21040c0c941807040d101e00e60744820000c040380040900d0b03070001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 356623570 1250 356622320 356622347
    0x90a060c050f0d060504050c0405210a08031320100e03030f0406050406091211040b04110d0b01080f151c060903080a1b09210515040512040e07 63
    0x45080a0745100310342025400729080109494a9450034405071501e07201d004d408c074946081c5546130501c0d01c000300c0c0c20140c07414241c290340c440000d080001000c05000702d4030a030b0392041660f81d0b2490b14074650340607180b6601c000c0c0e0384100e040c6d50f807480c00e1311020400041030000a1a07501d69107940002280c2405500300d0080d05400309120260107000c140000d000a407619407180e54946007000b600030083d00041e8055203072698007498034000308407080358440c1400001e035800b01d129000c4102090143c0800c40341540492800248075603980403550044841007000da8031400c680d16040540c03041d882064078940d803010058240013000c1e20f001d40800d100c2d0841c002511046a0f09a114842116101c80c0c050b408038000f40700700441c20001d031040c03103c964901d5007900820740e004032000340000701c58082e20720300303010f41503620702c1c03a240240506091550110840b00441035240030300e10960007e40e070855252040c0104401d06d0340c6100305840a40d4100d40070305d070150b668510110b4400ea0341506 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 356624820 1250 356623570 356623577
    0x1005040302030f1e0313030f030510030b0c090d06020c0f0c060a0c0c0e1905010803210a0209030a060f110a08060607030c061d12070206160819120c08090a060c 70
    0x3407402480c4c1415000d1441440c0c145e03404c401d000790a050140c80034008040360300400d854482000801d00d02d2034040c6040c0c036008005054181e8038104141c049104203104698414041200c3c442000043d400030300030945501e0039503420542410403140d4510b0b1601c80d69500c0a4240846108076114051300c0c072020f40210040c06e00385942e003c01884145040d500d0347c0300d441d05464031510304c41c1c42e40a50b50040c020640110714042c09031140035110040d409045003d1b400e80d5000c02d030f0f1408940c05503076a6800040c16510001d03010710382003004004c4c1859003212603081117400041e064509042d91302c843c50301d4540900c00c6d0344000420000e41d2006204506100b902070008022400501c20581d44980d0348802103941c05003140d07624a4503e40c848a0600f503c020805c40c40183c48880079a50b10f40d4540b048110308590910f084403c070f0041070740e540c1040030000050401303240d01131040494018119401c100329540007104484030b02c2c0c02c80f010344280c0c0c445c00c03404000800d41c0d481003510801174074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 356626070 1250 356624820 356624857
    0x1a07020303070f030509030d1e0806011e0201090b0604090503040e06300609070f14031c051c0b1e0a03021e0307090b030a0f050c030304171005040302030f 68
    0x20340d43c009550444000740e0019601049400241c1020851040b0b903200034207100c3d4500520381103002c400c071000000c8030104004800825490790040a0307200030903140c8103e184402c10300500c000c1c000c1600c0402030b2085006070000c5100d500f07042c40790740840e5410401442c035007820101e0503080e808010304682c0d0002c40e1402c0d40003c5196490b0380c5400310344400c4131105013454803170a80e440d100c00580036001e160440c6030304200e003440e1807560750202c4802400180c115403d520019051000d030a034010350034414583c034010300950003801004070100d1a521411040f2841004500716035031404000c0e008600e40c000f804008640319410340003104004c0881810079100e602041306011601d4900480e00414459a00309181c1071202c00083c02c1154400c01000c203140d000656642c0c490a4041d0040380c0284480c014007505115030b20034060080c0440350f586070780f003240c3c02c0c0101038a485440f41340101c0810308581c1d141c5009042c000c1d50150300031410f0401c54140c05503254808014200d411b6040d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 356627320 1250 356626070 356626073
    0x5010c0b040f0b0a05010303110111041401090906060201151d0f0402060918091207050703080a020703050d0c02100503060114090f030a0f02040e0601060f030515220b0a1a0702030307 80
    0x1003e06031081c4039500020959502d145005480791030920041e61051341402c13601c104042422040d20201c45581d50010340b210410401a2200416904010083c2e41031030740c04a11950150044048001d0712101845034550700c0c2600c00719101420030401c10714a03c080880c444405c03c2011680050000705083c1ca002c24010006440445c90103500f08110503030010090800b80901c59284452103045000d883d00841d45d40c0d0030380f201924000200b40b51404a502c0034902e20820104010310ba21400315110195180c60140040c2c1e0b42041c120310a5800004100d01c1c1449102070b6030044506848607802e8589401c10380c016604805440f0390000082c06d00005507581c2044460f91032070080e40b101020800d00c0c011300041e285524440c50785503000d0070040000aa105140000c08551031030001065112010032501c408800d6684d25401401a0130000881503800c4001e0301e96601e1003010011110320806100815183e48500001940107107842c0302404008401490302520007405e0340d1400c24503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 356628570 1250 356627320 356627333
    0x306020d06081b0310060509060d060902060c060910020c21450907050a120e031c0e12090301090c0b040e070201020301030b040f020409080409090c050a05010c0b040f 73
    0x10602030f01c110a040401c251807604007803203034000781910039000380001410310000c42c0c01c60101821417401404801d00020520013103622102c07640f580100416a12040c0704101c2d40c2ea84415980e001c02400f622900070142506803013280d8103d85001c0251100c81186082080619640820f0b23000f8100108600c0c41c95140e03840756461701031808042041c6a0303072164592004149410100e09089001c2000ca1003140c0ea4500e001d07a01c010285052503545910602c21640340c002e4080034090340c0e0034003103003000b03841c0080041d00c0200c0801c807040d210b990010313030540191a11007110791303d6500b004d41c002940c04451001481e007920080d0000c17a42c2c0e8551740d0703900569803460307000550840001c902030080882d47c102985d040344042c4025401d550640e10355900e104009040282280c40311501d200c11500c8541001d1445074000d4070385601d40d60b84040c86e002900021a044a54123404000800d0900d0b00030100d0f01624010f9403a24903061750355880502d181b202900c00c3c9c550045040300f0300001401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 356629820 1250 356628570 356628583
    0x20325051c020706080610080402241207120501061d0607140309130c09090203041109240a080a170c0f1f0c12020d020f03040b0f1e010306020d0608 65
    0x7296004154403441d14000500390070010b403006104142c55544021000e6021000640140e0111004824900c184000c0d541c20040591224003050000c01d04240b80c480c80d178a45481040705480c0c2036014100d10407100c048035424040d41010800d0a2603040c040f4036404115440071101900355441c02180307444500404401c15801e4881e90700014611115040c43c0300c000410180b02c24003400040d4907440e0244c100789032800345c031065640c0840003d0500c1a40241804000341c003405042060501c1004061003c000c11920003031022031100100c010706040300400c0448146001030420410142c3d2881c0c4441d14807075800c0d486140c14040061001800d025102c0c8420705d080c01801d414812008440d4809100000002020b183c90030b030005141c0c1010f401ca2001e4a4407100690311006048404000e0241d19507040c404071002c810003081010744290180104813154964000340c2c0c800200020240101100224042d9210010800101640c002e008034041a05001c1790468580b85582c0c80c142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 356631070 1250 356629820 356629873
    0xb01150302090627030703080a180905100f17060f0907080f160f080307030e0303040b0703210209030d03200a08070306230909070504020f0309070602032505 69
    0x59060381c48804824070341e0744400304c3c48019009482d10b64955110058107008803209101401098001111100d280300754000140401540800036801c10300c03550310055605025080b0400b1081300081034019910700c111401203091030003000e6541d41c1c1030b0180c0c543d04c4040c1440905104001d030118503808107010460802140030f0003022503070003c90b00400d02d411168040e04084c1e49404050000160200856440f260075042c15840701c44803001092640c07046a2101a611201049100c20507501160000f9130039424610302c0040403e000405040f4030074181c0f440e074560310102848aa0718002c0e00108600d512091078032002c09000701c120140e0340d1103110000001340e026801c0100c01c0c0e82500c1640c010307000f505008841161007211640082340c001e2962071042c80d00c03000045403000d0070480500503000c0903100f5074a5210041001800d9041030b105c50000313008240010800510000c2a6030b0a07602c90801c0308541c407070700c0381824201c00381c050302074400d8001c002810110759050103204183e00f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 356632320 1250 356631070 356631097
    0x218150c010f060e0c03060102100606030e12030c04050d0606050d030804140106051c060209030109050313080d120c0e0301050c04050f03120a030e1f0c030c03090b011503020906 78
    0x34464900d2160859a405100b1000d45103000e01c180815440d2a003200c0d0720000c48101c1c01d55139111100181d2600b0301a18591020ba400c0000c0869042e50540000c554610300408541d40358015035030071005400101e541b040420030502c020851840d04401d1080e07200e02910340020502d84840100d0620503541c003099010668000c1404204030701d01c4000740740701300780d074000300304090a003000110b030207c501c0c0b80000140c0c2c203401030b24103025880e070440f0714480d0010020007410000d85800f40d129005160351410a84134050006495940491150b001e00c071a40e4400141400361b6101100500707011020304200070b28018841d04980342485800e00806141780c0c055112417401042040102d0080485030081e001076429a40300c0d8126402c1d81d021030340908010030114049403415140001804815140d034903415010005068540d12136901200c09650500581071080015416900740c44030041c240c000c8100100034034000d213010490254094600985001ca43d8400141c040c2c11040c050000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 356633570 1250 356632320 356632327
    0x20303061203070c05221a03071512091104020711030c1c0605060d1505010305010b1c03121503080301210b16090902070305091201060b070204021815 66
    0x6854241d001e45400d80e4114000c5191030941e0303807920614040c03441510f0246146c18075401110b42039034201b06412110364002c008407480c800c010f5020100501107280203006800303011500c1c504004d0f0128545c812a16843d00c440800280c0000038052040252601080485c000041ea6503a0006000880c0501c0c05c5503004140d100400d400c0c0b2203440500d901c1400c10a1500c440764101c110352102041d041180003074199580d102190b03107500a00d2005280652018080c1502c460380e51010f03050b039025000070424049404248060b6801801013440509a41c1c525640001e10400610342c18030340720714010a411800e0070185404c0710058000b1038a045000c00180421500d50404814260030a400000c4011b541c2d1150010200054a600c9015006280c0704c03080700d0060004000826900004540d29000d60500030006c2c1c1220380c040d44180c0201c2506050840c050040c50709603120380300f1203450413006908100081d488001e844585900c100503c004a90310460180f00700108a05800c3d03a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 356634820 1250 356633570 356633581
    0x20d05030915010b1c2007050304030b1306060603180210020c060c0d031808090904030c080d0c0e0a08070b09040608033c070b060f030a030e010912080a030903110706020303 76
    0x1088010010320100242c030f04148580d8081c903a2a01180c080c525566259481f50b060510741d0552066400161041d8000003c1c0103d182c494592504603d0007100100710b00ca89030b05049080d0303152845065501c02c50b4070309007005032400e22007007a0182c000d1b0040f144414441d42c003154594024403606819600504c2d005e030f62841c0c050040707000c0d60100d200c030040d805040740e0340c0d800280644545c1c18000e000400000701014000c1049000d19034000440c42d494852584412003c0c0c13511400c00000038100c0698901903040c150200425501c4000107441d006090010051050b002074406aa005403103900015481009100901d0b80d90742944442981c4201031220054038074180084005445407c00442d03e4280c8850039a44000e07405040e400f100e40710714001030303d02c400c1d0b814016403500598640400b091303004000942919000c1c1c960000c0907903208402e19201e484110040c003804030804c60806600d2099205900b254402d04000412030309080e4410b00d000321940044c0f000d40e100105124 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 356636070 1250 356634820 356634847
    0x31e01030803060112050f0109020a12060e0114120a0206130f080f06090d051c0b041e0e0c09010e0c04080a03030f1a2d04020c030304150c020d05030915010b 69
    0x2005d41e4140740d050195003010b0810018047e01442041e80e46640800c260402d14421907019010003500317602401425111b11040503601020302c02c56901c00e046041519060402619501840d81d0f201c02402c2040b45980a0080d96800802c031900245514400407070140c10400d414406041d0b00300081614903c010819407800801405c200703201c1c0c0c400080d580c002a031100c00c40701c00c0125078218400902c58514500d01605c1079404080c0c2c01801c10100c0700c0c07a00d440b80c0c103081115010100038014000c0c00302144e500c400711100342031342103e151801840207000707800400341c000585410721407405640d1304600741885540881140007076102c0d8103151185010f40181e039032118461402801480800c0001000083c3c41c0700b126401040000c0c458940400085401c1c1820901034000d40d650003081c94036a0300c07548220341c21191a00581d1841c030841c2c0240c89140002c40031034000384100e62044400b590203420090010880703108006d400c4250a280c2c001c494000d10800ca1a244c5541030020203e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 356637320 1250 356636070 356636087
    0xf090305090f0f030d0507061104120b010501050406090e0606070605090601030b06150304062004080c0114070c032307030605090d020f0c060c0109021216080c01090b031e010308030601 81
    0xe40c0300384080003d40400340d03000700301800606040d0400540d58116071500e04060300382c0c000b000d00a84004a8000780f042400007408440520490701084aa80c071100103443e00d0041d80a03071000104003220500000f0104881107401c0440148420706140c1c6503540d050a0b603400301c6a08516410040042003089910a001504600c007201c01e640d40c80c0d0880802811800003d002520f0039883d41500780104030300a410505c0003074030340156942c868a48080550f07a526103440c0600149842208041111428044e01d032456800740800c0c01e4a1f00d1078030303060802c411a9064400485070303080d0820390040c00700040c00c000e5124000202c0c00b40361071208a82403610104049041d074001c2c00030451031b0400402c119001040032284280c4840c125100c40e8010003188500a401c21a01c40804080d5000060208256030307410120b560f00030b032154002505d03170800c103100d80c0c041408010300b0b22a0030395900103541d00c89410701e43c00c01314200b00c00e0390006099080c1d01c1500e04040000030b00080c1e5a100d07460 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 356638570 1250 356637320 356637349
    0x1060c0b070309030e04180b0906150a03050a081c1803030b0904030c0201030e0c041d301b060a0f0510080613030306030b0117070509040201080f0a0f09030509 70
    0x402001400b0380b40580700c07000105c0e0481c0300e55a9006600c0c964001c41d0a0024110b41003210504903280c1051b0103030303840c802910308085007911244920341c0d0b80b5041e50480140c81d13020014003803c0d100c1d5a1205115017003200b00900591000e038034221904090700c44c40220542d540c98165035100c007814068103c0c0c61942400f40140f00105c02c1002081d0000c210340c840b02d90a20340094441d4980344898108106001c00d0390b4014202031003550140c46003501c800c410040f16040e1020103010154402034648001d104401062443d0201e06046c2228006045001010881c0b03520107250080c0c1d41b42402000c4401012850352a0202c82d80700c44288039140d40100c40c001e000e1100c03820000d1050307a0741001024805c2c0c0f1166184208c00700b510a400101c01141e00ca40da030700a035616501e03484490032002005030f6141c86002c800194030b1910194641c040e03501030712264100c0d101c030100c0c4d42d04814000d02c3e005c0006d44822001c41c1781d64207841810016406580c502e5201d064031001c000d080105100c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 356639820 1250 356638570 356638577
    0xb010902070812090106090c030e0d021504030806030a080d020d062106020d1b211119020a0213021b0c0312030a060306060303080702160f05010c03030f0501060c0b07 73
    0x612001545040841c2d0740c84034920a03c2c2d0680d07651109960151500345c204404d03090608000004040c1c02d0303001290f9204070344040d2400e40320300d280126900d02004640c10002131541001c6000f19015140342034000c04081c1c01e03100415200e442d0348103aa07204144c2160210b030300080d070400c090154401d9034041c00440c136a140030503400d04280d81e61009800030142400707074000b071940000c5106174419146500c1410035200140318001d03016000e48112246015980819005c54910392524420105c925494a40c090b080602c8240c0300e024010001c0c07050b03004d500c01c0705040000360b43c50a2084000d00162240503a40700c0c80000d00d0a10002d4140c440c0d011940861107404840c0e0b004501c09404000c4480d00b903460340e136911151001b500580c0d001400071460007002106066002c24601e1050110b1703021200b10558221990020b1080c600c03a5102c80c610b8200c00348041e40c420303000c04c0a80e030b000c3d10b00420400691541d1404551013030f070203503001c2604542c5050402c8000150242d0002160a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 356641070 1250 356639820 356639827
    0x80f06030f0d03021c05010906030302060c0901050a111006080303010f1d040b1e0c0703080c09090103120c15020309070b0f0906090604080d0e0436050102040b030709030b010902 78
    0x1403400b55038840c10940c03001419004503241102c03948407000d0700c0c1010050706080c00300c0e50f500d02468004041c2c2d80420f40040c040c0200190000803c282245e00781c0c035040c0e44503072a1401c4184225210315075010b00a075a4002d40d41403024a07860703070103000050041e14018550301c4d450903094a00024581c1c0c09034142a41c03d0a54402c0082c0d00244180d2081d00822a801c1c5669100800c608540345441c038032044078400c206109a800910000d800014807030745880145031245074071101c05004c0d10102e2548040380900502c0040e108030040b190f0310490f4203003038a01200641d102421300c8841040d9114040c0c1c040304022507031800f0815040281315a4118624002c84500341c024540300e0480140e011340c0c0d00090b56041030b280d410445000f40b044a05444580d42d045500600300c0300443d0030f05105908210b2911a403a103544804007111000c0c8229004038403020300d1115a8110104041c1d03544d550074040001d618000200035403040020399961851300e41145400c0c01101c006070400250b691051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 356642320 1250 356641070 356641093
    0x1a0105030109020c070b070c06081e15011b0b0415060605180f12060a050a051005013204030506010819020409060e030a030617061b030411060703080f0603 68
    0x2004590550304500720140e039800d21440314515202455210320440c20780003900c41c040c400d900c100c030400e40d4840e07640e1103540c0d280c51090000f072501d03080420006c00c00c22800318044a01108108403446410305144810204502526031061808002660b908a00030b0402c001c07c1040660250700e110f1500c1c0400955003401d030014898098403c1c481c00d6403041745c06180c00c0e944c0f20400d01e07103001360044c2691a1140038440c0d4544a4006407591800e2505240109039241c01c0743c00740a2040c5d410107400074440f898140119500c1e00310488901d80c558400114078244046c02905050500c40b0041259686280d031500ca480c05105032301c103010580115481b0f80c540710440c0b81d0740c102e00e030b011200400c0401e403e003000c000400303002d10520441c0c800025103000035509a04170100710340310000d2080000110718000390701c940040f100b840940c0403ca020b0140711080102444e00325028081d0560424503050124116130302204094020072016020840c45500e903a000d039070b21440c260058590354500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 356643570 1250 356642320 356642327
    0x9070206070804050a06021c0e010608120d1107050c011b0b04030c031205090f07170a02091e010810061e0b030718031b06021902060d020f03040c05041a01 68
    0x40c1c008802c0080100c00f103414000c00b000382070000c40c0c125604540d940580080f0700905d03542003400d801151704214009042c03800c10f100781c208448100010b40700103e00d506001501d5030041071a5103034595115120400000218040c181951040303000382009482080090112820044401c0000d104d61102e10009002082e00d150002d0381801c080711841341320301d401e0341c00010b0040c8108030503141104109000c1d50004500c002000a0000d65615507101c02c640a03440c15034042c4181294041c034031076001800c02c1e429040d4000a117420302201110103841400701c1040aa10403181a8405950010380a03424840c100080014000424054489144000140d8114480d8020302c080220015010300c1c0101c26003246118144d9501c0f550580300d00e402c6506150050300c15001090158000c1030560002420a40081aa0b92011701390400c1d5401c0252903400801e2050700c3d15028000000401c80740d078080c5d8051445103a0001c6058280300600045600740d130711308400348199964460b06640c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 356644820 1250 356643570 356643583
    0x51903020601050a38160c09150b0d02120109050a060b0a0e010804110d05160b04081e0c0a0303080603010e0309010507020f0a050604060f11030304080a0e0a030b09010c020606090702 80
    0x49441c44809420300c0403074103201c425005c484102000280f0fa45244850002c0c032001502c00c0c51661030315900c0f00c461304200d941a50115900140240062003501d6000005c5c28400c61102e01c050319003901c01e001140da100c000e0384504001074407039090190080700c2c1e0041c603010301002604141408000e0754002e14114031941c0c140d0612603410045000c2c04480070400c100c100000d800c600300c0070384030724019648260000d00820704010407a00031890314180300448040719041001000c0420844559045a88110640342e06034414044a180c0c2c644410b42118010760003900d40722001d143c58014142907a20585211b60550001c0004c940c0d00c0ea0004140d8541c0b82d0191601b6042b144990081881c1c87c00c0390b0003090b80904003050000310765038001060000380c020380d81c460040c5480e0003102c80c0c1d280400c0e85e006203071260030b2120800710ba1180c045904802c1c0c008180c0e2281c142da80c1c850f9046250b0554905400340d46500e58514100e0f010003a042d00300000780c403048610320706920001e48420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 356646070 1250 356644820 356644859
    0xb030309011e0c08030c0d14010e01060f120c050301060e01090302100e0a1205031b0609070306020a02102c0610031202070914060a240318051903020601050a 69
    0xb002e0602606000b403082c49141c414692141c40103642e03041825103554030741c10003c40074010303505100203180810f10100d4450b04035070300c10041e03000590801c802518075070071340e901a00c20400c241c00c5001603800b96004008440c8041e0b00d4503030ba00e504228000341240c504502190500024075002c100603202c011030300da0040120314042000c0040003001503503000183c1c0c481d080c0d8410a07810582401400300040c02c40c43c0300d0f0308035418600001c1c0c41e0217840e8103040b02d405809130000c80d000c02c00b05c5c46d10f4004082c001610310585100000300044803080302d540c40030810f01450b0103661240181d040100790152386070013100a001520b01003410820700081d60000a04074240c41c0b014040c07460080001c0d101504060700f050000c650082c141c2c80c20540704031030f90307846611008400100c058030740880341800c90214140c2010100c5140050f0080c004d1003403a01004e251140c1040082507051040c40c00d59402c109408a441070b035810028944041a0041841850040300c01c0012490341d00d200504030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 356647320 1250 356646070 356646107
    0x906100f082205010f0506030703121b0614070206011406070809010207030f0303090b0109050f0f060f2d01050405030304060f02070e18011b0504060e13021209010b03030901 76
    0x60340c90125039144008100c8140010303900b8007091808000f019000b09255441128040160750f0700c1100f050369581440c80054030301400802d01c01d000c40c2c801c54220a01700042e1000d17101c01a2140c1c0c4070400c0301c8201001910b1a0400000d1105466040c010300740144074a08900001c83e689170002240352080c01c900900c070790000600320071140d009001160003960002c00d643c401d4101e6050107000b80684540896680281100108180c0c1c403030312805001d5000071100e040c03640d40e02d000035103640c3c2000e03144c154021510000c41c81140d80d104a900b10840c5284404a83e45a90300f541c019040e00303c0e0180350522505020034090368a0003c160307811140d0a11300720540070080c4100380d00303000440d0800e00200c1540010040c0c800050030041c810103030500c0007080b039146210b03207002c0e2071408440ea05000490410040288920483c3c0e502884203005000d610313105000b2540400700e0744804800300400030810700300018081c0a10070181ca80c6401e41c080d514002020000030001c400011000d80d45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 356648570 1250 356647320 356647337
    0x50406050601031a012f070303171003030e030c09240301093804060c0f0311090d02030102040b07210806220e073008070f02011116050906100f 63
    0x421b01794146104010408110054825180c592603440354203a00043c0d010448030644801d10007081a8054490b01c800d00015031018210768044411080240d4002d074940b260100c1c80c10303582d131190380d02800340e40c012041004100c890110003540510b60842c04d88282d1400c0001070204140d5500c0103809400d080c0d01c551807039003030004e4034207413130540c043c2c82c043e100d04001300700400000c0d62081c10440283e13140c41d4141120a1030403420360702581d1015446110074445000301e41400d035418001288010300140c10f180d1140c4803c683e030f4111610941d50b503400c0d00c40102d9442504001010b00050b98030b045681e82c41d00001140d00808014000c6a21140560800a00405507402422208401401c2d03c0030306503584010b001136480c0c90b5076180c00246d110866002140070040443d180c547c0408454205203003519517200340074000d81d0980c180f041883d076120f4140703c03d00541000c82441c5881c1e4000c58249800e024010100400940c024480003400c101180d030040082c0c1110025803502c3c2c0e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 356649820 1250 356648570 356648597
    0x2090607060e1614030303270105090606090a0513060b0105040b0f0304170304051207030c080a090807060c210302070218100b03060d2010171308030a0911090703050406050601031a01 80
    0x130141071408e921100d500e030005011255002061060007103170308540d0980691145e81507001100d030152101c03201401418044c2c0b000650980002d84001c805042480c00c05940b605201d0407030b07001c1d17249080914800410002041003080c1121920444010014214a02565140d540e041c1d5401d018160400c08112182018442c2c03030300b04201507000c1241d030b4032168502d001030301665650003950b81038001c0c140080303510761142514030380f0141c10407501040a0342800d0100401030900341c1e80d408043e020068080541c580104031144140c01c1100f21440d885e02c450f280180002e20f410006440d80c0800501625940340030b0300e103200c660401401102d02d504016100e0800c80000c0f1416082a84003c03400304180d044240700148508061200100d507a60900919000070f84510040c01c9400500110311851a182c0c090aa00c0d4410010560328040c02c000082c040d24086682c6c800180e154401c007c108a0381d4014107130090001c1c01c00788030013140d0100710051030f41e2112181e070400141410160 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 356651070 1250 356649820 356649871
    0x80304150b0a0e0a052214070e07121104120206030a06090c030b090603070f170109060921030516030e03070204060905100b0a02060a02090607060e1614030303 70
    0x401070034014100301c00c490b5590384410f402e200440c0c0c14107145181c503002a000d07040302e0310000180c8580e016041c0301c15520ba07803240760342d83c2c90100910135031040c82004121900d1506015020306015120741482c00001d0309241c2c00d4585c001507420340ea00c01440104600000c0f099850b0709607904492107500d1750390346605603005003000d0f801080590f04200c0300445290300759001d16001c03171096840c00403a54440042c10350701e907000d10450303d141d81d540208200301d100002c041040002d0b81800030902d200d1036110074094501c1010291a03032203105040701c1241c1d01002080300c80306107504042c011854280d1610840414501c140390900d520b58009400508003401140c00e003030343c0213208220282c0c0f10954040100406c40d40200c2440301c029011815804103030940c0c1d94800380381d004010607a06d44c100e0401a4100045194005200380500000502a40a070111090201c001032400e441c141140d01c0c1c1c48401a441020031446c6820311a85030f85002c02242d6108035203101c02c005130002c220004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 356652320 1250 356651070 356651081
    0x6120102120f0603120c030d0c1b0305130603290a030b0108010501060801050913021c08031503070b071e020f060d0605100f020613060e0d050c120708030415 69
    0x140c4400d00104102c00d00794280c8455010305001d03030443d018a4220035101606200d00e000c03c48050f441070140031400503040d0454102540c01d07241041d07030105039036418041036a10300c0701117003c240e000c0b6030500c07900340d85003000b4020138542ca410310941400381484499810040c2d01c0c44800400d035081595a500c4031664039000703581c440207446280d80d60301d40a9000306020300501000a45201c000034240c034215030198007400d011266441c03070b070043c1c0d8204105007401754050800e04000c40701c001d0200e400070000d944134100d81b9035060349019420007010700706429a000711520803010300030744000c600c640c0000301144221215001c11031409000142803811160b4000f6407250001420303014001c4190003034070407583d041e60f080b0400000840207a0b01c04880b2030354040141e000100050160a13400c1c0541c0d001070144070000b0f142c0701c1d507040707072030828034080600ca0100354006007410349600208140019442220f41560811300c4030f541c1c4c09a04e100c051702c081e140001400091200d040c407035011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 356653570 1250 356652320 356652337
    0x213e0a03020f0405042619050403020114030a060302040c0f020c0102030c1515041811180a0c1215050307121211010204050a030b0402040b191509031b030b07020705010806120102 78
    0x161046c40030a007210901590003c0038403608000101010303803400d409481a5026294140c49010300c1e0491400c1c94003c0d604010514800380c1d1b120480040562910b2080d04250f010300c2d0748202e145040404082c1c40d042030582160704542c0b00300b2100e441180702040c280b140091500c201580c64581c4506220a154290142940701e45043c0f082c8260401c5810943c500302e00c6408600c1c01864800b08100312040078600c107418034081c040c00a200003100b60b11688015450341000f1501e030740045070180c100c0d10401d03440c10210981c040180f041d840c04001c40d000800d00c566448011002e40c1e55501301850900c0d000a041c011b00c110b074908280c4003901664040d0401900c3c07001025928201860030200a4800b84c2c050762400881d00150304100079407040408503c2c031140c112902d050340e041201d00c1340e003440d002007108a03074000c0005941d8000c4c00b1070742c150541c0d42c0c010290560401954018000e0f008109650000070100660798200b00c04d6940036000b11000310240e44910083e5001e0b03c01d5964 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 356654676 1106 356653570 356653613
    0x90105031306090501150e0c0a2d09060f05070c0324050a05040302010e16050609010507060c08150a213e0a03020f040504 54
    0x3580c001802129824611540351220b03800c03108500411612651540c07914152040802080c90190800e146008030900b402032140002d840f03152810020301100d500e68000030050500c15200c1e416404600e000400b50040c0c0080c4101d800b4001e5401155081a500c1d010510400c19500b1266108020160543c2182c40704000306003030441407406000070030403191101a05000d424059180b881002c920b80c1014940a0700f075524082084c580c6034051744e00174000380001171600085400548510341c3d2084941b0040b0307003e00c030302100501002d0820303540100f0b641e803241c1d03458402c0c103144005004c41c0d20444200680c0c1c81c0144120324000f24543da0130000c4418008081203c2071003110019500070b8118140990220f01d004a002c2c13401031440d2040280c80c1841401c104080116800c021043c116800200b500703450002081c0115941d0000404110342c410a042200c2413400 = true := by decide +kernel

theorem cover : BRFrame.Cov 356474820 356654676 := by
  have h0 := BRFrame.cov_init 356474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 356474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 356474820 ≤ n) (h2 : n < 356654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
