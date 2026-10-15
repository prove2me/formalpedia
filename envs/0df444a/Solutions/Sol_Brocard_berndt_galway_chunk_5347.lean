-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5347
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:34:20.764291+00:00
-- url     : https://prove2.me/submissions/0a1681e7-9df0-47ad-97ab-f3d59f53c1a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 961510791 ≤ n < 961690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 961512041 1250 961510791 961510801
    0x3190216050f19230307050715090603050615071b0807030b0601030203040b010e0c0c0604080306190609150c02122d0307080f07230c010906021005041b081f05 70
    0x2c2080d00404040d01071106240d0800c580300c4e1820741c4a0700b40b00a2061064020014030710401442007850000d4581b07960800b555507800a8050354801c660290740304000000700201c0c2a48000646003040c090001c01181c031030111325071320001012b03400090081e800500c007002006030003421030b58441401c0c44c056065007050741c0d8840c410711060045400d06000680001d940c0303c0710005644900741c1c0b450480d1410704240c00c00d0205a88191004e6015418030720b800c81e8800d50b0803044904498040d0b540313058951504e240ca101100b81c0c5013805080260001080b8050780c0c4140741b882880c043c0c013010303108207403240d101c00b0740d00072907280341d80581c02c001e283d0086002c401205440306c0c03a03041003e0079601c10314280141c40911501800a110784d0800391154820404c4036000314aa524880856601285000c0156010b845038070801005a1100341c00003580b68241d004180c00074414516030032200300e014180b428840d03c0741c02c20714003944048003044154456203174100f0113624090b0100100d043c9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 961513291 1250 961512041 961512053
    0x108010513050a020906060d1112060307030309030b190608010506010315050a0b0c030f030903030702010e121c0b120a0213050403090b0a111f1505010503190216050f19 74
    0x702d000c000e403040280170002466912090700301ca00aa040c0c410070081160201c1c9503043c85d4200303000c13504c0e04480c00b60005426090001e001c03016290981c484019031484d607518600e19031001007507000e48200e81202d10010203043c0c018007010b007810304004079071454544001011203c0302c200001d11030b03000040c00c1003941c8410342e18005030751000702c00710303640c1c20214000d52441c0f05109070141e4503a4004100002c80c14040065070041119030700034070140c445950560745d200405201c03203048007030401284a083c3d40c0110f8140c41c410030b491010a0580300d000001d40b407000f00c8407104450341c000000900462501d420881580e0080b0382007003001d0b042c42c2c0c0f002060385049000f110809400000c0d00381c4141e005110022100c0200b004880704a403460110107130300341c202181d01c403c0318144001211043e9035401650305030340e010b94446041d591307121300324001d900081132400e44182c0c0c200400d00c02d82d400600051001401f440061581aa080742a01d10300018901d90720849100f80306108001270b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 961514541 1250 961513291 961513303
    0xa0b24030a060501090b0405270c030a121202030103050316021207090507090e010b031f21060c020303090a031209021801030209010b03130209180303041b0801060803040e0c13030b010801051305 85
    0x8044001c0f004004900c0805a00c0e180e2b800c14020360502c1451246001c01c071815151180045095032000020060105514241d0100303002c0117210383c0060280750040181c900c0700021150006110642c01c81ca02202d0070709109040c2c005c89034443d160703410030800c45d404c40190300007440c0501d0400c1c625850709004c10240d0201819649103115110480c1030502c55906205002c0c003410407402006140100e550074180041c00d108540da0350424248404641c00803050301e118407050b03000b60518007003941c1e0842e03207843c180f140701c10039543d030b1155040035031906a403a103000440f5102d03007403655055004121080b0cd05074000000c0d503070f0820030400715440d049219100f044d81501c001170149c54868803120701417103110715246544004000c01c0184002d0f42c010b000350190980c0c0380042241c84d00c055509031080d902614030141c0c01000100300c00529410322a45c842a024040c3d400d0003042401c2450f006074a40c81560001d0480b0011310400d6000e210380c9400100110b41680d030041c3c07a030750707107a2103070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 961515791 1250 961514541 961514581
    0xf0b1509031209190f08010b0a060819020c01020406030504150501060507030813020d03020313060305010b0405090910060807150338060c0a03030e0a0b24030a060501090b0405 77
    0x410041003032540f60b00c2c1c01000d0310022031640700880d1019144c43c4580c0c1c8a50782c51080c1c484560801c0217140150401c8060032094644540e104091580c0d2649071640e0801108203021000f5820002d140c030b40f2900788040c02c090040c640d000328582c20142805845004a512a242c04514280c010800b1681260482d800c695050900289950b500300054410722001400130f5005600103054008141d4080020b00c0703114011042c491499885e00012400c070b442c01d015807858400100028060340c035068103000d51001003030003220140320030b403002c02d401c1e01c0656011050b03d51140e9024008042d8440b1886009601031070100800048409a110481110304098191012086048200d610540060702c000c1e08007500d00340c4e568003011281036807802040000c3d40020310f840134061002002040501003140c10102c81030301034a0f40f5869685002c9044902880b04002108004040d202030000a1605018820000e2190314052000c410348981d0152503220300d19100c108100001d13001202c103005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 961517041 1250 961515791 961515823
    0x314011a0a0f110604032a031b08160f260a030b04140c130602210c0f06010b03040b130309090509160909050f0d0f031802040f0b150903 60
    0x200031100296032003003c2000d181030b1030007020304000902d41c005d039030070905030b02404540c040e4603112400302c0080c0120800040000300c0603181c20041c01207080504810034042c041491420040000d0b110110100312400c4506030030030460082403190042c050300e06545040500011070141a000013060f114000d55a81403560703900040c2441c2d1115441415107031151130001c010b60a0075034019400e41c03c50140251149554040410541d2000c18542291414a03180c44508243da59440b141a045403100030103521900450104140040010394000c0c040e203082947d40303040a0800d844035503001480f030740e2080c00b1036000c01c0020b40e0001500e0101e80340010005003e45030f65411504180d00f00554100b40c036000100821404099400403030b030f4900c17a00440e2902c0086684140e114045010700d0008a15820300d4525072038003a8101c0c140b000b142110f050300a10180e0f00290881e20460310380b41006546900b07201b904c1c00d02c3d130341c0342c1d01e0454200051801c020b14840080d68070798940c6405561 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 961518291 1250 961517041 961517057
    0x20060414090408071a090f0f060f15030a120e0418030c051e0106090501211101050403060e150f01081e030d09030807020c0f102007060314011a0a 64
    0x40c0020001130712003140d400a0340c0300c000701d8040e8481107400c800f507660030f100d40608854070206890025108041c40d00c00070240c0308503550103c0380c0345540001400d00c6445441c4d0700c2c03004c01907501440f140540d40c0c841c891450014140200040c21a0040d001c124001c41c541445150b00d4540c481307800300300c1603051914485409881c6411800c00c160390320680d03444403d040303d0003030046041d00510151904440c0400c0b070b130b0780c0c4c1d22842e10880c4807074a9110003005547c8082c10101d9224442e941d42000103042c038a01e05503403a551401201d0010740309001035005034480608591b021410642c00844840d50100c1d15410255815140c100c0c401040030000b00e28110015401414425251203246285040040c00c0c598103000c4d2924004940a5006000700031207048185010680d00c0c10505010700407000407007041105030b074030040d01c0b00c0c980001d0b00c07504648040c900e0100052000b5108540d00072402c04003110109045400c180c01c55010b0741c80b191200303d080c00040d826541c0b10101b5103000d0072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 961519541 1250 961518291 961518293
    0xa0b0d0c02100e0c040e070608010519030206030c070b18100c0216060206160f050d0e0a0b09010e010c0302070515190e010b10110a11041404200604140904 68
    0x80707880840446545200d003807100c40f0400a80210b80b03250f005001340c500340007425051100b651650354074020000415030010041c84142000d4042032441851a850419034503180e800164164100322769251600e2f80000d8000c08102c1da4860b11038000707081182c5040c2c2c088085281e0b5445110302d4821a28441c1e03160302568a16108000f151039048107030360045400303030b11010001c1d1900011181d080f48483c0d80e0355901a014800d48000a00c08219500ca60400c84c9401da0ba00c081e0881441c00041e612a65041c000840c00b01d081244c0518031010000507001e5050f0041825644407081c8001490700c1403040ea00031a40c00b18040040002401c4040c032541d50310311150281d500c000c0c0303c00401516000d50b07150016815804101c1c952000c030381e00c13500208003110072145c0c0e003070a080441d03041e0401c1391340350f001078000c00d0800e00024008101284c1c1c01050f010540c1c1d000c00440d0140c510031160409144140f1400703546404d140410b40e07070280f40034101402e01040c844d0145205006100c8500098 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 961520791 1250 961519541 961519543
    0x41e0f11031203180114070c03050304030e03030d09031b0b040213091506050312190e01021908070204050c093102190e06040617040507030501020f070606050a0b0d0c02 74
    0x41e100070032408015100d04204c0181899240b4080c20440258a00032510000c81e48510005114025644d030398002094a40d5003290b054101400031400d1088005d000c02d40da64060000d40010f0035041d0340080e00005504004081c0d2000b00340c9030301d044425400080c081110b404d11039900940507101c42c0040f0f0395180d10207000b8030505030040d018548003200f40c1c1020041d504048100c41c01113048541040030b2901c9985144a03510b0403450711201d44002b5080c0d14020301050f850001d05005840e072484012480540c0040405401c880e10400000c08200318901032103a40d4000c50801c91090400c0c0e01d400218103100c10081400100c6070007550980041042001c03000b00c007404105065403240541c1c0c1c01034186184030366401c0c022414805121045041203001d44003110700c1940d13070100d00304401f0384102010501510a8480d401100000700106d02c0c00d000414020805403074181da141c8a50604004541c0280c0009202e4100d0320400c02620780820150740c0101429000040c00d280c0c0d0f80005e07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 961522041 1250 961520791 961520803
    0x609060815070905011b0f1212140106050306041a15070c0b03090c010c26032706060409020105160c0f1215021b1006060f020304080d08060607051203041e0f1103 71
    0x400e4100034590041c01c0c01c3d0300a40c148840c9c041c0010070710004ca66442d14000f01d240074014500060802c1c80083c0345d0349020b4200e215510600413440e64030008000110707000306c2c119045c1040d448030000c5c010041280c0607042c10020503081c1240c4c1d0942c1801110591186406050241081038065400f0244031449401c042c032840c0c140a01254514040d003010f45580085070a00412050615046021107054a00c845002c11380000f51207296130740303000c010060040c1c14084e81000418041c0340c0110802c3d2038011480d60240c121360b14580c3c075003858000580030311b4100c0c07800080d40110340800520301c0b0303025403410100060090f03103944000aa28100400c1190380150070b00c101c1c860f046c280c016a50103801074621540c0c60813020000c00400341ea480c410762140e0002540061140b015880c8202d0801d41c010038020110344c0351001c4ca4503610300e0710711980b03040c0e41e5000c03001041c4003c1141100e44110700e244c800441100c540c140f5100d80307009280201e03020700703d00503301c000010780d80c081c00304e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 961523291 1250 961522041 961522043
    0xa0c090b0c0d08010801090b220204050c09121c1202070f030f080105011b0209130f050f061003051b03100608010f0b04020f0712030609060815070905011b0f 69
    0x6464a994650940707541d98440700301610046100d92001240e205018041c900400790032900008880e1580104121a14480888855100c9001f0450401aa0381e4020603000d245000000b41d00c450001c800c10203800d070b0407940008260300c003d00507507412810302000090b118071070804008216504248902904ca41c0d07800078901c0d50303003014a50405401030340d035070f501c3ca420356102c2c1003da88400c0151226035002c150340301c0d0b04a4248420700186442c4040c02d0f0f000840314841031201318a41e440403400b0511700d100320f0b02d540000164001903001000740590101ea607803000800640f43d40c65543c0c0343c01c4450070f80c12850141c0300e4104426102000a80141c4840c580c00b00800780e501c0400718000d01c81c5d21440c110080c10200300030103515050003038030162440c0701242458201c0507500d89058140d241c12076410f144c0c648600149250301d62080600501000000d080c815a4603200c102c07020b070005000d5010b0109922007407020341d902480c02a51980382480c4c6444015150515506044100d94 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 961524541 1250 961523291 961523309
    0x5130f2009070c06050a020c0a0206091804050a050c0f0a09092f0916090b0703170106030504030806040e0712060608160515030f040228031b14090a0c09 67
    0x80c0078502d5880309910003618014070040250b0340380c45c00c0e048280e209040b2941101e0b070200b508140980b908074000c040300c1400800b02c55403525050014001900115010382d43c1d074000416000500000380400c1c4001e0000b00c480d103e05560200010b40c030680c041c010220407950f9400584108840c0c490101c6501011010a08140042c00c0c0c1d10303000908150201360195460f000402c6080c40442d52103000100c0d551607601c0d039107042c0203c802590700030290030340070010424140b042c0c00740d00318a900c2c00380019a902254504e803604028160314009040603010b1450078036003000007440450380d0000e5410316030070301c02020b0311401c24002501658000b0389880c0507242c0036642d00d09400f426981201c10950b88a000c64150110300882404200d81c418024460500050018507200e40c0181c103696000440d12034442e580103003d008004d094008441d040310f0b440e03449003000d240b41c0c2554000d000d0803211044001e20600440d1103510301500c0c1c825640c1c1c2307405108440f580100e005801030700c0044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 961525791 1250 961524541 961524559
    0x311030a06050415060b16080a12020c0312150a21080d0605010e01090e010b070c150801051509011d24030109050a020a0c0f0503220905130f20 63
    0x402c000c003130b000d180988189040d2408034006408070051058032225078041c12034000c2035406d529048080c1c0d000b90b6044042000c28401090b000d1602e102901100c81060010f50311510307135140048040c031010b045000107801c02e000d03842d0f00742d4421581000ba50b030492415040a021f2482d10b10b400d00d07150070700500011000c5444048006641e0140007200c4099803000203c070415401511080e0650140301d04403100213006100d6840300380010b15505201c0c40703030f02c030340d55680b42600c01c0c2c1502d00f004013070009501c9100412491400310390b5030742c07402036101078545004003200c000b070000e198400300c0e20000c240c0b8030100d0f1101d81d1192005a1100896101e034181035070b0388000ca0303481754401d0041454161502000c212608442c2c0b0941c1c0c03103135000d0380329036145035200d4a524082801c0380c0012a0244410010a140b0354810444404150020048082c0729424885078a080c0d0310001c1c400d4851080c45001c0030040703003465510321040c0d0b401096003441320309081514215100c0d5050b0300e9030002c85d14 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 961527041 1250 961525791 961525793
    0xf0204201c050f1905040206040b0a0806090a110403230604052503020a030222060f052407170d02070f1e080415030b030111041503150311030a060504 66
    0x5000085580681e00400c016a91954082245042070300c0070950100084528044c3c16600d610507500240010982800c00b0350b00c0d2420711546c0d006085840015030703060b00380685424016030f0070b500488a034406020149151259206030b00035444040c10000c1c509040307241c201002000081c04141c8070090390b445250500f0800c0c0c3c1c1d221200c105c40341c94138485081f0201081c0c2c584c01c0c0c50a4960003401b8158041c070703613020000c240034124041ea5242d6070406001c1d081040604c1404010107654110622840ca850701704030740000425000080d55040310748210843e401030044620302d50344140c3c1c00340038031140e0a017009140101010f880c0c2c142e00c002002c0060040c1d00c901e02d181c05101e64804c03c2c890346045c1d07032140755408100c0010524041403209001c9000c199850101703415051800180401ba440002030949840e0485000d01c0c034230000307007480740d800b01000c8030900442c14103003449050311000c0a035401c00650310018148000500b0b018659980c288110013105030441018003480c141 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 961528291 1250 961527041 961527067
    0x1e0e06041707060504050603010e07020c0d03020c10230c1002030c040e0604140f09030c0610050a06050a02030412060f0c0e0a05240a090e1801060608040f020420 71
    0x445105600306108030b07640080c11612410031a019904040d02082c1942d10380318035416421405004101036000c0e0242a10260702c03141100940640681d0003030082e6200718090001d400c203001503060412029080070414010b02040c4101100d14070300550765190010f4580504080b201d032204c0c1d504600000a200c1c40304144005003040d60308211910900d84c407840100300c201c038985400060318a41f500d00242e031480c4070800040c0c3c03215141041e00d182948121240b4113010040700c1c61005110a090240040d00b495100f407800f030000750400364540041c4e618080e5407401144610403c4883d801002010403119800072141100341001c00e0100d039490040c00341184000740c2d40305005020680c40020302c1d143c00256580c60318401c5c9001007008000c00b0b101c4c0c4007035003e50140702c2070111b020310010310340080c144400d105544406024050002000d40d481c00d4501c182d01c803508006011040c08040340c0072546006c40e05904a9000510300000740503d846814195401c442c610004126900a145 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 961529541 1250 961528291 961528319
    0x3060f0120031e07033938130302070b04090507020f07050604210c03081b010b0105091201151d0901141f051c021f1e0e0604 55
    0x109a05a100c480e440d01c041c8140c3d50041903400f0700081d021083d00740c60400f802d509880d42c444a17002d010302c2c42000c03050b28003000011100407111364580c2068480c4000459207000ea03100b82e046900e4045460f5801c0b0398040400142c0900d001d030103080d5042003010300030450b0303000030010608125181da035507400c000000e00c02152030704c000d4041c01418164014022810800751000101818281400c0080d00c0104109100070340d4400c0265a440ca0b0104d02a10034034402988541901d60b41c8943e18240e071030b94404501410b007216030400215082036a044010b56001d0602039a04094440d0256502405450803000c1111180c84201c00413403581418142e0210b0f228042c800101c0a0b03e820310703650708844482052540881850020580ca80a0650744850354240d04000c50000d40d115000204694442644001d02c20940a0320400718100402450600300c1c4110001010703110035070b0090886100310070782000200c0d5590808940754081d403803c050302a405854552982d4507030f4100c070007041d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 961530791 1250 961529541 961529557
    0x60e0d210e19060807020a03021903030209060c031b010615031806060e18030309030301090b0a031e0b090c01120b0301090b0a0203010303200a0303152120010503060f012003 76
    0x52003850005c0e9102d030000821320500e50f07056004054000d10303400c80c480034414904044040640030050b000259459201030980305030403001540e5608500c4480700c55407007900c1041422641032540c108250150008000321258107810086002510394024404000111000030001c910300000481c3d0381103c40390491049181900d20b0f02c00070006240e0350b50703d010483c1c000000382e00c1080144200c21007900903c03c01100a03003074540c415207d9803140c520308024401012076030450301840041c4003c0303c451680098409020700174810011000030300382c0c24074100000c29140c4460741c0403043c0e202503008034001c5070000300a001a04024441e40c001e0b42c8207120a400061041d0844201510f407800a0b2a680d00390b00000d00744c1d4003282d0790540c003401d030040045034808a09200010600241145000301d640401c0d06500b2001061a02c4443c4190003070b1240403802034140550050398020084940200080b00c80b141e8034101c0100407141c500f04003007541200718030b0354101704d401e402c00800f0702969 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 961532041 1250 961530791 961530797
    0x1514060d02162d0c0b091915090504090201020a020d110310021c060506120702030d0207080a03050702030313060908040b131d13140a0203070609060e0d210e1906 71
    0x504001c181946280c0c4010058200103a4140170032201060310010284110050f0400c8400080080c0e0001142400d0b4090703913514459910460300503601042c0741c8098001100c04000100c0d194000070742d00e640a840080c0110141e140107410301803c494606502c460007412504590041c144c000c010b500509801c0c959101c0604000c0080c5860380541401d07588054850b0303040014000c0c1209103408058070f29400d60004000e0021140d04500041a059001d004140e030340741040440241140d10041291046420500c1801014201743c0c42102110f500b0200102e1640300038202080c0fa40304552003510300c00c80c0003d802032541e010000355405c450202ca0300c0a89091700103680b145441c01202e03402c10501c81d541c09100000e14842c1c40c01c1c0d0a2249608540080480340d000c2072038101a03070072400c04902d090904012869202040380a12102a02c0c0784000d92015901c07001205a402707a2983c12208240d80720360f407207208240804110100500145902c00c051011071a03080c5c89000c1e071000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 961533291 1250 961532041 961532093
    0x7051c0e010f0e0106170a030806060a0516111311030703020f0c06180f0304150c110d0b090106060507020d08070f0618021302130608090a061505041514060d0216 71
    0x1640c00114040300c1f032039090703100e83c04190b44010410020350b0201e900c4d03106006c0305100300c14a483c02c892404085901c80c0619501e040f602e40204620710100c6244052000d01344021115106090016240c1007810307405c5c0542c0341c04c90f901140216000d1110302042da44144402c1040703e8000c40c4040720207114030b2040c0d07616030130305215041d100d100300e0207080c805520314000c0303485d041d209900c4902080d02031a00c0d600003249440c001240303070b1680503003590384a03183c8040c000d40100a1207400b00402182c00c05514080715540800d0100114010103481c07c2c101162000070300c40d41e07400380700116520a0081021140c02000111942644442a80144004010402d45001602c01c6644510440d5102100c8a180c600220b0718054001c00241c2a400707040c101000203600d60042e04c40760321070100c410400f142054144402c8840c91b00181107402c42c00b4204001802030880355280b150b10a5540c2031b40c0e9164224040d0282c0310b4101d20741381202640301c46030240040f1412030308071811100f0103600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 961534541 1250 961533291 961533329
    0x102121006020304140609060c030d14061c020d050f0d03020403030212030c0715060b070807120906080103030e310b0618040b180405070e07051c0e010f0e0106 70
    0x3c1e03070340a58000c07107184544803804501c003484c02038040c02070340d1401401079180c0424001660300f541c0203600b407100c000c1d40716035104440d5240e507048a40d100d0b02c240c842641c000f5042e03a0801500940b560003070b00402c4500009024000288001c1c4440a4107204a075180d0070f084100800a60143c4402da0060060440c4011036070600000ca81c000e1140191403810b180702d540718002802c0f01646081009951800c001910011000103454020b0048010310746981490a1400442c45107800c3c1008000360302c40309006441e00010b41c01c0c1541d8241c9004a100804031021502030b5084001c9003000211680b03181c1d4505003c00342c10303410800b004001740920010756050011034020860701101c486140c60710041142065031000c00100f400a000c032505040c0c00c40c2c00b0000040a880540382500004e03000d20229110741c0015801c001546407042c44c10800d01a01c015007049400c80e115020740300d0743c550741188400d407c007100c0403a410310204954580400140e00030f00e0144036007004040c3c4041e00301c03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 961535791 1250 961534541 961534543
    0x3180905010b070206091311040f0f15123b0a03050a14040302150306150f0702010f0509151309060b030a32040b13030c0206030603010608010212100602 67
    0xa0704841c41c49a0050800c0003030740c2003103915001241d82e030750092a414041032042649015040e41c040352151041c3da11030a10800b40c02c440d140350445414207002c4101007010341500d0188140d110914034181e554899422211809000c483c0c1202d0003d400c12405850400c1100d84c5200000360000c9115200030a0400d080d61190003030700700035003c200c05011042c02c49001c1c614001d040d100d02000945803e0b126030010760b8540503600007107440c01e800f0003005107030304001580c04442c55014003607908007034030100301290030b218020303000f0704214500d40640c00d81d500400c159405400020400c258500e0b8012440c00290081168190011100c0d007000a83c0d54040c4940c0040d11090780c1110b186503a01c04464024000a8081021101446405403198090f01502c920310082d0000c04a00900780350501c0424070304043c041c0103440d4041255840060382040d030800400340d05480c801d4596a07040d0020303004001590041c05d8550000030342c141015800128284543d40c103015111a194544a0403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 961537041 1250 961535791 961535801
    0x30209040c0f1e05040b0d02070c0812031303030608030a03050a06140303030a0216050a050d090f0503030a0e030127120309050709090f020a0e07030b03061b031909031809 75
    0xb440414104403c200c0d04000d0400c20341e800a90600b0810700d0550303600e02040c0e4070b0384448078003c4071660218035403007040300c0c4141c0b0b0700003094020028a0000540c148248080c071002d420345c0c1302c01c0610050030f01010300a80000e070041c492042600e0710b9400801d07026000e8030048441c00c0c081458079502150b1803582c40041441d100300607009505654a00322a0b400a500c100136400080204100a0000030300030401d01c94243e2141001d80448508603102400c000d071650080f403205908100203100a49001054481140c402c1ca4500e5107181c00c1d1000c28010102d020842012070751316213070303d4103e114040e0441007941c030420324210601000c180440884a800c14010015082400108841ba01e55000085490b02607480e40044903c0d91340000e0855640b54068681c0400d054204611142c241c400e0116030750041c0c0103401c4603e0710310a10803111030f650411200700000030000c1090109045d100c41d95100f402e420030480300d501818094070619101c05100d101d00c0c007000e0085103510180c010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 961538291 1250 961537041 961537067
    0xf0402090f0c2517071a06100e040605040f02090f0303090901170c06030a05061c110105070f0804060c1b0e04141f0e0d021507180e0403030209040c 65
    0x20b6420300342105400a070308018004980401c4a00b401d04a000c01c284459140d00e4218111324aa5a01c0703c3c0c3ca0071021002020790f40d0700742e441e24401001f4480d119440c019420500d43d25200c092642039100040050030141c02054025240c4848000d140e09203500500c103e03e000c80d600350036950302008169880c0b180a181c0c5411200400040103103990203101103010031100001d43e4106080c101c0410050f800c00c031404c200c4550ac0e401401118105204400d503c0d0780380c121403040780c100680b01c0341002c1d2290f499050401100064003000d1088110045844907840420a40d4441e544c0345d00810300b1039454015196038020f0050100d61b1011039214004507601803810000383c2d901c0ba1241c0b0012004a000c1041c0c1d805407090201e1714121000405009020b02c1100280c1d050441040914200a50000300b06652040d08a00030030001d07a0055a8850301500d82524511501030b50071385076540c558002c8070420300308070600082507059005405081800d90b000c004101c5440001c035110071408031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 961539541 1250 961538291 961538311
    0x2210105010b3609180d05070b0105030307020121020405030a06060e1317090103022206020d11030d050901060b0c01020d1422020102011803090e0703020f1902150f0402090f 76
    0xb03e01c102c0e82400d640c0264441c1089000400480c0d426003490f080c441000b0807100024000201042000407502005003d028250021400d01c000780d4000380c090340321425a544034501480c8500129407803070f0100d038050315000c2c0644c1c0a40d02c80345064000750840303000e081f10403100000020421042400581c0c1b076a90070105092100024107200c20056104d464814101a020002000031042c0c040e800074105046004094810b450004000c1c2811350626040702001080342400c5c81c2c2550010513614804507010000134035071a080ea8041c010300480d80808410200400c10300384c183d0065002e0701340708024960502c40d625284204e0f078807040301100c1122a400740d8208220070401010b68166403d071040c0000540c1c0240940a100d03403126102080707000030424041441411070000760079130440301c1414154204140506959201d00411202c40c5005800c490000c011030b05c02c006480c030380394510b010075460341801540a030359040708940580c0500710b01401308000800349000240b1501e1000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 961540791 1250 961539541 961539637
    0x6261005011511072601181e05010b0a170c100e0906060c0f0303070206070c030915031d2b020622380408090d1415090f010603020d02210105010b 64
    0x46041c2808400e4071030240c80b1990b80340be104140c1e840341e40348070003d040b040c2002000d00a40c201c4a900d0002c0f00081d5601625801c061442c060340c011390316444040e01110321110564401000c40c00c00e001d5088180707020b01c05c0030b0303055090b5200400154003400700c80d402c0c1c504698480000b0746a04008040003000510381c130781c081110400e01c02d03225410841a10340418201d100c22407401561024096403111034000f0301c0501ca241c0121004511008080350508080b040500c1010f500c0380c8000f0410150303141004003d54003452103015103c0140d5020b6840e5400c200e003100018580070805111006040000340381e106019511124240316540c40072a0341d107409038010a0054500822608517100896414290320240381407198881240711102011300500e030840c801c5180029a04c44a42c4991408400384056115501e80705004c0760142c0d0107a440c031242c1d03500b050400b0a812004e0155518120010441c1402c6900130300c03183d24841040304500c1c28008100440820000000b500c40c2c5001c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 961542041 1250 961540791 961540823
    0x2072409140706210902030d120b010e030a08161b0e01290d0f06230d0b13030c20011115011205010626100501151107260118 55
    0x5558a62110214140080380c1607550380c6c0464604200070031a40041554015039503081100c52041000d0427100346040d1501b40c11101c04244ca90080000181c80140002214090781c0e5800390051007090f40300c000845461640080e0b0700e1006401c1c059181c0800c0881c0c0005849103450802181c544a50b002d00450001c107070106201c207030310070340214450a495000200001c511031044100500c0ba0130040d00341d44c44030801c840880c0380000c45442c41050241c1590b00420416181c0796440704500d00008442d1640303046c191450702080100501e2101c55100a240d480320b1282003059610702070320782c0c4410310444906540c503034032542009100d00d250340c401040300841c0c9501a000440c01540001035503a20b40c01e0b8001c091080ca15043d03801040c4204913100c03d070302005011145c09452108000c01d504003104205454a200305a2040000450400d204010140030642c000c040002e2050161807090488034550718515400038020f500c2e0821102c1c0b540b805070700034003100381e00201c946991604 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 961543291 1250 961542041 961542077
    0x31005010311030a090311070306050615040b160827090906130f0614010824010608010303180b030106030f05010f05061b01060b031305010506010212040902072409140706 75
    0x9040e4040e1b04104100741011921003050040344044e500480001c1143d1405030b0a0048480500749801d10710b050401c010448503220400382e40001c80c4403072100700c3c010751a00f001030560040143c0841303844e08000101aa40c0c10710040414002000e0303494101315618a001280c46150445036080e0091441c02550000354031b50b0130000105209007400a040081c0180c03290b180c044c01d82114186038062a80d5170481003101c802c0c0b6040e4001c3e00d14003541981405801800d04006200003424040c40c503a40d002c680040f4149000038082d007003d072640f07941c4e640d08014003400050040c0c100c21450200041011a03903044c841301078032805007060785846903400c07401001200f1015a099a13558403d40450148019001940600c0104039440a4910141072107030840d1000f5087d28107560000b080018041c2c101c00564040760030520005880310007600b000c11610107803607040003550140980b48003100e00140d11803541d040c050a0404801d400d0031322170075510b08990092030b02117087c241c041c40f20140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 961544541 1250 961543291 961543301
    0x10608030a120f152c010602151f0504090602070f080319090b060105031e01060206062b020f0303040f030f110d03080f1b070c060f0201020a0912020312030a02031005010311030a 78
    0x2403004500c0b001c5c1050301c210892141c0c82a0400310060b0401952003040b0506e020440350040c080302d5250300700720000030812000012902c0307494061038840c2303020024045560305441c0c2441d004644004034079a140b80c81c20a030742c022642c000205d00505c20030070003410a0712402000340d41c020b012107060f4a40600544150308024800c03c00246c80c480114102046c88540314002c0059400a10f01420600708000e12a42e0340004038400200c4e900519041000244010300c1e51501900c0d040000e20307000010a0031841a03410205000440c0c4070000f003003042801e42d0448c0c690003401c108805071201000c10480007850301001d800034101a01049002d410032040a0b00024046441d140880c11909170805c1c0b50400d940680300880015410001c1c3d0b50807260442e18240d151000718071300203010070081e1191000e401020520320036038441c5070440d1070801031021080b041c0c1400584901d800d0581002035032080b980c0803c0300764900300002ea25402030064103420300220b0080d81c01c0d541e50b1900040240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 961545791 1250 961544541 961544579
    0x90506120a1b0507060f0b010215041b0f090f0b030a08131d0f09010c090306020705190c090c09030b01030f02030c1e01090b0306010c080c010608030a120f15 69
    0x50b5100080342c42d03900300c0308811441140c0368031980d4071005103040c1441100c01058071042d180d802d00610f40000da0740810007101d488007216002443d500d07203040051101d080070b05c5d614148a003024020840142420004049911002092181d01c1c08084070900391814a40b9a07a05a40a40d0004001880d00e001030f100344071058181d0846e450740c510056404c3d181c40c074400349400c00301c4018000010202c2c190150300c02c1c2d100d0004e20001920002c010300c400e007144800780890f039020507840104482404a03a0a100b10602d41300484c1d02d5900301481c007200c5c184102940c1d20310f4001c080d0800b074001d031495022250060000389a41e0718685542e07140314088101280c0c1805509000e4200b90344041c078007110328800d118407000c5861a1000544a03e802d600000c1c42c0d020248100221030381c1c04080c1a1910b07500800d044d40760780d8010402c03405081c2c1908510500e002c0400c0070f5588035488400e6404a0341d10031302c107100c0215400801d90480e00c094a0703080440c440d84906104403103401810070403d0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 961547041 1250 961545791 961545811
    0x801201b030f03220203190201050d060f062c010c060f0c050c0d02030315060901090305060405210a270905090106080c030d0c0f02060f0a0801080d09050612 69
    0x3128000c48040c11507110548a0120072004000c1c840c2c0c1e40c49a1140941d11084e1420083c2e0410442d00065a5002c06542c0c4000c50501c944400003164800c50548400b110100020b0064a84886003280f41c60307080d000c0c0034001495079403031813983c0c9008404586100016484c6e220404044d800444241d83d0a920030f45420340c03210305402d2040312520607075601100b01d80e205a114105101c0301810300d108021007108644c028010300402c04d6884900300a41d160444035280d445034070300f00581c0c03144050382c0090158040e0108000501201003000c045c0044804008468a03840c40610442409010034000010ba0452001c0c0100d0f10740e100b8004100080601d0b0500e816070300d0b105070f41a164100c40318045a510344604020000d010050410280d10171405444c0c5041e91000c02450000d021a0260110103601c00900035912038100f107584400c500920140c0e903003001540602118000e01c00d8440078400d0032aa42c1407544104901030668100034403240c50041e03154034010309504e000e4030308010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 961548291 1250 961547041 961547077
    0xc020114041236030c060f0e040209030f06010b07110d0f140c0616050f01110319060b2205010207060c03030f0b2e14030103120e0a080c0a080120 64
    0x94101121243d400c0d11034040d60000003981189044c00004070164800400c1c00070200c01c1420550b000011841e0040083d03600607120055a00000d240c9001512440d5075401180c001144520b03c2000804031b050050500b4014180d282e418070404c1540c000300a0200800d010001000071414504040e15142c1c1e41e00304c454400714140000c0090b4040030202480702c09040700c400c2084418428801405e504c0c0b2b00801800001c01112150f92000524030700015414002511aa108075408100a82084603403c1d496041c5065036043c0001400d074041d24081c0d04401c006041d40c40013a03032600351910350b0f6a08a190030960303420703000380444004040e5542d454010038000e40c1c40e1a21101051100f010340c58580d017001d052035091007000c1201c01010071980250701c1072948001011241120383c4503481403080b1001c100e00315601000c08200683c0020b6446002880c11000184204a01e00840d41d502c0c40a0340ca255003800c9550440c40f00034200507062208913140840400b4001901040c03d071010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 961549541 1250 961548291 961548347
    0xa1e0504090504061d0d092102100908030f1c0507120e25150c020604060807051612120926160b071d012a050703060c0201140412 57
    0x1110201e011080c000da101c049411076096000c911f001c004c2015080c468607940c03928000b644501e00c0b040c00a402034107821080001181b0906400000f8a0303c0b05c292a101c0c00e070502510364a600c42c204c44020700c680040c6c000da200d2614403509000700c60303030345070003411180c507881c000c02034449138001c1e14842c05840049075075024a0700c0310511115078030b083c2e54113081c2000b001d8210500c0003d0fa100401c40c0c000c0008006854090440e400e0342c43c6400d1040e519550701e88200d40c03c2c4100002d0b0b400101a00c1d84407000c01c010510030302c1c000c1c1500d44039400a83c1c001c4040300300719401120041d165031440888103030361001702c825020178468500b545901d445100c0d05a9108864000c00031554000a1030410545c0c0341d1000c00f507001040340c01d407404088101e4000080046c03030062003080e54903042c25a44d244440c4215a5104ac050303221042c1c1d00300b19034900b01080101a01820b010142d402c00342e000b00c18600025080b0b12079903014994031101441500115030707008229900a00803032410140c14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 961550791 1250 961549541 961549571
    0xb09190e0a14060a051803040302060315061c0c03021305150405030a050f0115080d120209030f15010f0302031009050102070f0b040c0902030c0a032f0a1e050409050406 74
    0xe15541c11903402000f913400c181c0001d4085880050a001000316122168000f24001000f29011a601100e041d5242c2d25030a403035145000902e10340744e07070203c0002001d1442c0340426112126070201200100401c0c03420b0380701601644a4090404140842c2034414480c5185c40301d1140000e400801a003801c090b00c84020a1800c440c0c1401030b60680d120b0000c4800c258824012105105d020000d00d0b492180340110195644802010410902401c0070002c02ca146c0f2942c1903c8103041c00404a44403c0e180c01d0500743c0b92403420200400b055400d0002090016080d166a02142c0c0d0250090032005a019032880c0100201c00b07044800e950208800070110b2608412000c0341030203060300b4030842c2014a000111845240c5c040902140184100308406030242e003540d820743c2d07a6040101e0000d910100300040310350000d04401c0c2076000e44440b05070704030b403020140103130014130348032800038080f81800e0f0562500f844903079000098007044280507003000d94003d50b170840c4c840c0c940810507490040001e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 961552041 1250 961550791 961550813
    0x120e100c0507060e150a0e0c1018090501030305041703280806030109030503061e0901030c1806080a080a110d021b010801240203210a0b09190e0a 64
    0x310000070710114550301807107224843c00401051981c0184014180c650980c14030080c01409542d51607600ca0100600e44000c1c040740700303200c800078050319400d40c0030785000c2c203030f48070802405c5210200c0a5010540d64a944140c038141c030303016107500c0e05040c5010b401c07240c0d00001d56041d541c180002c3c011020480010000c0d40310f40c0d607000c051881070315409507004111001c0240958820785c1007050f4240880c0e080011642c00c40c40a4412040384180802c0c41d08082c5240e00600e40c01815271000002440881c003043c8050703400f00f1031030002d00786c0290848020f4402d240681b0f915604142140400912524020484c051003401d04420000d1090141c070300b4000030741103030000360300300103050003140d0341d03090104921407002d00341041154100015002c014070808182200750f840420500742c060b008000307503100007010301c0035022600200c204010305030794141d81412185041c00340078000d030300d04400f240384503505265aa04c01480211207280207460b400560a4a601a9060200201e102c5002e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 961553291 1250 961552041 961552061
    0xd03050c0d021b030309090406150308130509090f030a0e0a120c0501020c1203030c070201051603020109020a060309052509091121031e040f030506040b0c0a120e10 72
    0x140680342000c0c52407a9541c0b510a803e54802d4008102c4100340c2da07140c03103a40d42c11680000780000c000310201c1103007040f01c0d1030350005400c0c0d00002c180002140d10800c0c0100568000340c0b005403081c1c65003030110f035031082c00c0c503854070541e00140140c2025920a903a2440200c2005000c040260f580e002c0000840022001c00d0f81c00441804d000e021a5030100324031490b0490507255101e100d01d00ca000d06450b03020103440f10b6010b0b0000210081960300c0784042c1c404000c1e561882020800c050302c1c000e0700030701506408a000c4d6004883c001044e90017440f90152003500710000d00800580000082c203540042d411890f01c82c4128080818440114410b145c18107100308070184800410108001150300540b4603160380c811840c10f402e00e2a8004015185020112540c0804610b00480c47c0314080c00303180c03c540289180c1400001c1440360000725a80114001c07140c8009603191030840e60300520a003582c1c078021480c07a585614050710994020208040c5000958481d1240349820314147c17604444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 961554541 1250 961553291 961553293
    0x80301080a0506060f280e012705070e0121020c030a0e10020a0219030f0c060e03010501050306062e020d0f05120c030901020c0727060803090d03050c0d02 68
    0x30071004100003042001d40080045a034100551050f400091140c0010703c40204249180038a280b071144007012080060058007480f6003140da1150b89840da50021031002c4070040304010b403041003840e5280b203502c5c003600a681c1c410300803000890065a508096803402c0d51b4441c0300c1c4003040120030391840900f59103000030700503681d030b07451180008203404e140c40d403003038400c007036086410040c0d03500040c84802642d415078500e00c00e41543c0901c080210704035400940344a03446000c1a0401841084000c00d503009601c480c1c0500d600b0b98281800c0311743c00d0246507015445200031440701e14009241d440300c0305000140a5001c00128045541c18032548108000f41e8008018000c600341c00030700c15030481d07207145031190905e41c03803848690000d60f011f803050400c02800404102c0c6461300b0340483c1d04500340c450844030040c0d540d1170000082006039058580303401824034a000214060f00a080460301c400d001541800c6c080c1c410440c1c00c2c00000d1040313007408030401c0081c0c0039560521070440011600e030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 961555791 1250 961554541 961554553
    0x90c03010504080316020c09180a05070b0703080132030307062a080415090c1d010e060d020d060f1b09090f0c0815060d0218030c0a060815040908030108 67
    0x2c0c6900f101105c03a560250564010a0311417805854a039065a8408100701c4d410745004500b5035054181403034a0b40c0075000f8080c1400c0805c44403800001410900d100e59100741881e82c0e0f903402c030a6600c82c04100610800c0c2d00403427007030282d1060300c00c50000c0380b00202920b29000c2d9554920046480c202030101380d0039015049040714200301d903a0600d8142450030301e46814901696540c145680522500141c03507556100d80e02032045072144203024041560620390030242e80d4030307010302000702441075014010118002030380500b040604aa84980e0152080c0385406166a880b8054901e01111110308c0b6964071407520710003500250b9200300c04140d00e500d4861400c102501003030710316070f001e404025070808842c03600031540550072503413000100341c694030703181d0000c80001e503248111140c5004503400803540c0c890011051140d19a0351100724212000350104a0620007c01542d00c6010301040c1e007100000d0f64401440c941041c00c00c0014030000e0b240140e0f0b80c40c00081d4000b0303000740406038014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 961557041 1250 961555791 961555801
    0x204021c06150804231c030e070b040b1e0d181403090f010c21020f0f0111040e040f080315010e19054f050106090905090c030105040803 60
    0x240100c0c0c200042d0a1400903c00e28140e2200d4000d15541700b402c1c6500f07440500c041c680003205120001075000d01a0b242c0540c2180c040c6d0050140c0030550102401b40290100001c2c2c00d031481c811135080f11410500c00d4200581c02d401c10a084118207020b520051007000040201c2800303200b95100350307201c2c003043c0015048506140301c0719010323800721071140d500c204041407150395002c0d0164080c2009107400d10840c99a880c1c800302c040c140a031a0684e03162a1140c00c0e00340c40c0c010911562400c8418211142c041c02d4242c0d0078280d50000c0b6207034030031000c204000d2001c040090075490384203005241070640040c0707607034862889500444003482c0500ca0060490007e6030b0081440d42202e404403200311440c6010a01013803c200c07070f4411b051003004000d50342d80c4641d0002c2c2244c5818104c1204070074941c050381c01d038900c800480c1302d808244a034410300850040301d41846041c0c103950f031959559000d54249801d41c402083c0240440c0c00d14401c07840121032942d800d000d210f00c0303503218001080d00c074181 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 961558291 1250 961557041 961557059
    0x70602040e040b0a051504020d09060c02210403110405071b060b1503070906080603010e191b0605040b07020105040e040c050f0d17070320030c07060e0f0d0204021c06 73
    0x3c041e0100d00510b04000c10300c4544a1041080c450b0b8039821138005a07a0070044840200802107400c000345070900300804021103c0d00410f8a88442c0010119249007420307110b80b00b90f0034412400001d007400c040c0c804480c07460070130f54000c66000b115420001080d107007030f800500020410140841d41c954640700300c4042400c1c0300030107588016502001c00d066080c410800340000125010f00c10810204000003452035a094002c10700299908050341d440d00401c022800e038185101d01309440c1c200c1111a810b6005461112030400c43e2025a100b0b41424140504a407047d44141e0042e810014180b00104095070101c1109019071701c43c01090a03c0b038038003818403595802d5001c844d8442c0c82e44003a6040840c418844240e14003451a041c0d5a688009140a07580c460f03402c00a8150300300c00701080c0917142400001032580b1500c1000b185da10540e1000201d54050059482d550010706a05582445051a04076250680c1c402000035003480f600e00403070004101001c1400c002103498000400402c46 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 961559541 1250 961558291 961558313
    0x80301090605031e0d0c080f0a080f10050d0b0408070c09050406061e030204020f130b13050a06301a090906070504180912030b0909071503020d02070602040e04 70
    0x1490394400081008210100e034403011100e000100f031241410040040144400072150708d2141a01800d8589502d070000414081045030070100c001c40200129807a0b68200340100c1c1120300062100d000080181d032400f01d0041c0262040f9500c000034440e0f000003e4402c0712450140c4100100062640303080c2c10100301b075440c03560005020064012070606a10401c05a2105694040c0d0b40965500c4107004403a00314468548000303900c04c8408030106a8190305001032440036090f0660012903500c2e1800c00c01a40420320900d00843e54110756508800c2006000a401065100d044007c4080c41c440d2502030318607108105da41054103111003443d0307162002e03039283c01c540345d50b000704140e00c2c001c00d001e481d1380300318001c041c0c0303a00d8024a0748400050540000401d50b41c42415480a005c8110026010f40030144065105554040020b110102d00054140483e40803100d112690440303801d040e4025485090000100c035000c00501002c02d900340020802403c00e0717818202c5a01e098140300729880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 961560791 1250 961559541 961559563
    0x4050304300b040b0a0e030a0c14010e0606180f1512010c05040f060318030e0307210c0b0705060f0901060e160f08010605120a06030b180705010e03061b0708030109060503 75
    0x1a1402e031b5404500e400003c03e5480b80d0b541800d040180e500b040c2001519541c002c50a002d940d8280100c0c01444403011401c14042e00003910121040c154542428410080484103103085e40b443c80002841100300710111400020042c0c05074504a080721485429031705201032950204000160421803a055a44900001c044501c0d00b04082840d007a85102c11204c59100541004500c2c0401c032165031301403024070000c4c00103801c0310110500b040707c20250043c025105680322042c108000607800034a40465000907400800307013080b80d0312260321009007400a0b00d985100d6503950b41c04911031404040d02c50049030071000e6030813141d10415004040e01e54a045080c100119000100102c0c0d0b041026250610041840910b803030342c95070744080041466a10280c00703e10081c041c002a041e0760b003501502e00c3c1c01c032025110640d0b244c1e001503889032150b4015540550042d400a181d0111003810740c006140c000442500c2c004982e181c0030903036002a000303545065030704c06081100b071904012580100c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 961562041 1250 961560791 961560811
    0x2060313021801210f110a180516030c0c02040519020a0305090c0a050307030f06140103080c1218060705100c17010f0501092904060c060b0904050304300b040b 70
    0x71202d6030361615080305100e0300a0007041b094014051558403206c191002d00742e6105040c40c8140302c288610041d01c0d06a82d0301d10041400e01c3c0310300080340f00c2c0c0130729009038009480394515a1003d0307092000800004160381c460340030b00702c400faa0b0324032280001c091140132030390003280c1da091501d2172a0405801708a054418074025070100915140851200304680e00441038002c038840c1c030b081a0b005841020384000710075001800100401481402510f000541c0408031041c1d180d04900d0340c03000744191503041c800c40407601030041c110301d800d40013001c1c5e06100d1419940c48a40c031041507030995034050900804141d030081039400070310076142242d0062210000051100f480c1000107040500b01e40a191101403121b15100403907020b19605d0303040d01c0f1350720070515035503641e907900101038071407e5004032035090910074584c000303242880f00b26000e1038114000d5031509142c21041d048030340c40ea41400c1000623551100c040c40b240200c6c120042180a040540101d01d02881e02400b4a00014005204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 961563291 1250 961562041 961562099
    0x3110703090303080901200304060e06010f050d022b1b140d1b03030305181b100c0609050109060506090709060e221d071202060313021801 61
    0x2080d8400c100c001202e0f01400e20080030780710319041a025014821040c0c03181c0004241aa04c1e440001c4003c1d8411401864108480300d0104952a212030b401c0c03003080d41e12a1240424002c9203420201184e0483c4010704580b41c0d56481c5041c0d424241c6444404103150055051201c1800b41e0058031604881c0781e07a0703502c01ca15003000342c0302c060f4502d0004010f00444180800c9820440341340c07a01c42110703c014220b03546080e500c0c03a00402a140c102d0351501e40e0700030b40040b80e0075500000b403d916002103d20084500f510154144050401c06040171003c1003412005100820080d1103140c2d07081c2d0040002203803299890826030b05031100900705078040c10700541001003103071380134460314141c40c0d40b071414071000a5000000b0f090350740c0f200460143e40351407844403145034429034401d002044c090902c801044107501d08294403400c41e40708803075624902c1c900700c100500d000302c01950f0044041d92040d4039611a0b40101c1e51b100d0b0000c0c0200039041200c0010301914502018200c010701c82d5a10000e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 961564541 1250 961563291 961563293
    0xb0105070510201b010c020a030c02090a061a0a0f0c03080a0b010e030f1501060f050418021b01051b19080a091e1401150e09120d060501031107 63
    0x107641c2020328807090403190f40301d840040e00c00c0325803001e01c5614803200b60241c5510308040c81e0b01c0700600b07490503a411981303800e980041082c000300d2083c01c0b041d010b46906500100e00d03001c1c0301541e5001016074003480d0351402c011503004c070104a20ba00f40c031842104107498200394807010300343c4400c65070002c0500219040c480006a8402c183da5444007414401103001c1c001040180e400420700c0a94541c14012801d03000e4082e14000313030400c22184c507401852010799031494280c40081e03501d0221070025108000a00c1112134a0f081009404154580140f41101402450b0382d0441d004404180790723515075040c00500030240035090704402e80308410b01e1810424000c401301310072a040c5008107114956000495190813039201c1c2c2d85e0160000048140c4094403401107009407401700044620000d003903084140c0403014803035280f01c1032400041131042c1d0b040c907400c040d2100c0018416203103481002c900c40025032240b07000e41201000140e02007030807400c00c000502036031003040e8121a016002d2002d14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 961565791 1250 961564541 961564543
    0x91005190507110d02060f0408090a090c050c01060b0a05030402210601270506060913020409150f0915140319081306020309060f0310030645111201051006030b01050705 74
    0x240c12a2748014000e603a8412640030465001603a4400412140341c45060b65140e03810100414800b00980001c0041c6525003904412500420316100001a801e000082c01810140012342d210800b205000d13501c5203030f682c021840c00000342c210001c0c4000000111100c415000b0041402c41401c44092105161141c0451114047e4411143c81102842100c0002003100c1e8100c0d80070b04403010080c0700010303058941501100c1075105520041e1014880052294a00d02c20080c182903a20003509460380381154240a010400c000e06034140140d88040f043c40400580c0c0340c1400741305110064695408003102451004968450310a540080101101c00d41d40d500445080300140c00480e0b4a030f4886404001032800117400090003140b8040003036850440f40d0384440003040d68280c200101961810800e1640e0010400c0b510000f80d154481400198a240c5003c07500f00e4050400c1009070642190203080d075405981c0909180705401040c000168540038600e012134082c02c1851800c0350301c0c4e41e02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 961567041 1250 961565791 961565821
    0x3020a0e030c101d060d1406220504080d0504030806040b120718021b06011e14011d030714131b08041110170609091005190507110d0206 60
    0x3d1030403c0340e400325841c104d4180c1000324828031009880039445a4286000d4401012107007240c0f0200302d007440024021345031034040c06003d00880090112048101d10002024010103070088428940c09d100d444089032807881890311a5009503144c1c0b40f40d09100c001d1008070b40d601244240260031495000c02d85400000d81c1d0401c03180b80d0144a03040d81e8910048500a000c0c074404540c440041c031507582e001d103800017542c1d4103840b0b14109008001c01480c0d8654140d4980d8441e0f01e1507550318503c844600c1d070259103000760720b0000c29001c41e00c1001d6100083e040c81075a07088070415800a548014540c01e1130b00b00c042d482045480100303c0e40701d0041360600790040c074400c104104030441001404200c0303621040e018004000d417200210310540d980c054104011626a50004c081003000200c19107000040315005681034809020084603035440342002d4200181021001c0e00299461050b035040703889400c1c4030b403040f56541008010780c1089541800b07000e8ac1c10704119880384080c00940f00c004411 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 961568291 1250 961567041 961567069
    0x2a0c0602190f17072a050f01050703020a0b131505070e0907121104181e0b040b030f07030b130201020c01120f111306090e0609090a0b0703020a0e030c 66
    0x5a041c4229180040210f402c0030030a0840602c0811074008100f00035a079100c0300768484180070861580184910140350043c4202c030740c44130040c41031581550080380249034060007441600c140348502e03115018410015990750340540c0140a032041844101003030846500b504c54414001c900b0207040041c0350740c1011580d240314843c81004212a03038000c100308035060025003c01d01c030a0700c24102e500e0340c079006440381c80c103030417120340c680c5410007824424104c0140013030b00ea44120010716004ca070001c24007980116003059850075090425a003c00031105410800340040042d2801c40c640010002c00180c551041020040d0301c0c540140c2c0c01281500c0c2980c400c2c68410210510504414003502503140464981c500e00b002d000000402d10008040301b4031002c01200a95950743d10441e0303001c030b0314840c0e680590a0800410900d141040405810001c0d440440e1500302d9252181189601e00303842c10804a030b4005813142200d0f401001c044c001107411009800329038000804a0449110303584 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 961569541 1250 961568291 961568303
    0x1060b041a03180609150906040203060414031606020301050102010b1206010902030601030f140f100b1602030a020901090504061104050f010c330617030403080a2a0c060219 76
    0x400140e14805039080d40640e1141c83d41280c030030341480c04403139441c0e0380b01c81043c0b00c040b401c00c40003503d20f000004e1034600580e400390003048a40d03625100c041e205854095904090300007080ac0e03201886481440075480c5004601c010380e603500d000d001900319a80015194014810504440d80c0c3d1a408190740d411228501d0026940340c1c2d90300012001000420b4900da1020b00d405911146c651000101c584102d28501da2840b140d100c41c1c1820442c06c06a1080c1e00c020441004004080d0b080d0404483c5058405003c60780c001019a0002d02c00e003100740c0100302901e644404000621410380540f086e100e60680c4201c0c902403c1502081d120306006441d6418054030607150404c005802d007900040d20100b00003007a0b0005a42d406843d6500c110546016540c201000894114103010000399642002001140781c03501d199a40d800d980c00110580d0140400210201107514103080340b0154031100100440000c1464903008900d02c400c0c0e04034804640c001d129203205000c10800384049241c0020f = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 961570791 1250 961569541 961569547
    0x90807080f10090201030f021c0b090c0a1d030d11010b100c0303020a0e031606110102040501200f1006030618050706050711040c0206060328240903020c0301060b041a 73
    0xc00184c000c0c0840e155105c40403423001500000c0300001c100701e001900041042032081c1d40e11041000105481a155000b200360304010303d00140b1b0007070940c040100d489090403441c0111410001c0c1c2440125001c0c00081442c14540c9640340f00288524140c20104540d00080021040c0d40107001c91140030004080c142d000982e0034400c0e01881d02501c2c2c202d03000702195010803a04801c403118840c540700c0c0c2e401191905541d00e240503010b00031345040d9101030f0344400010010b00d6510114580070400c010703079405030044950001c00103100c4584101c88001012038402c1c036600d0003000701d40c082c42c2c0c00340c1147c00c160603200000e0408180982150003a1038040e0b00c4204600b4003000c031049041d1645c0d446845c01f1105580c0c29000b00302c6510130390f803c900b61114400c000030b030700715451007102113481e82422085406000403003050b20784039202d2100c5203860044411032049011100c0c0303d0010703030141c4c0c080b0415400ca0301c0c00340190406001020440ca083c41d1a140980b610280080d102040b001404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 961572041 1250 961570791 961570793
    0x40905010e0a081207112a1e0a061d0919050406050105010f0c260c01052a0a0c031421010e070302040503060109020f09090703050f0a090f020925090807080f1009 71
    0x14145501d4400c00802c840e1000407210048e09525001d1505240610150600040c215004d002209984c002c0300600020480f94403040040c4401d000301096482d964000004441400c1071080520603403141200141a5040ca000036183d018802c0000c0204503404138602d0004044041d450203014903424480d0f41200e085214140034080c0b02c000103499842e00c010041240091050003a810f80c21500900c01c039010064248260310030200c0440204500900d4140060b214456900a40b03c1e00702c002d5080007440305040307440c2c4015400c040c0c0400b41c0c03000144027600310001060340160441c1400c5161919000100b9100c51051244990a40d800b00d40000003c01c0b420480b04000c0000b072105065140a05000e001804159000c1c000c8020700000070b03461203840c0c413031546051b401085084803240240c2c03c1000721800208001c480b00341074500c1903000300358802d40541a0b405074030b90341c00c003a007082000d520b80751b015030080500358001c1c415044400c0d40072a009550191842000c2080507003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961573291 1250 961572041 961572103
    0x507050c0a08040f0f030515040206190503041203050702071217160501060b31090c0302180306040201140d021e25020609040905010e0a08120711 64
    0x1410031080c824001c0295060421810308014410355846161810300551514800f5400078001d0000801d25480303041e000509828801d9003d80c000c0c030040c00146091001d40b4001030034004004c0d20780108801005020800c90301045442540d003007468104040d1602e07100007541c48045200702070320244a002000284090808801c0d503021001d1107440d80d454080341c041d84190704911042e1255441c0490124107440450100d60042c41103d0b51425200c104807240745254030045105407244079060000038416040e07028020804035143c50046e201d00c0c402c2554503110b0030305001c80b8405e13040382c410080140c0e00880c0b0851040f40c2d0307003401034540103c108808001c0c0319240e01c0d0301e025540c281c9075140e4060580300800400c11a5680a400003c000d1031903414840070b244001d41c05502885070b0345690405520007403c0900400c0003280c04c000c50320742181805251003090f105541c2c0055404084078030601529008001380c94032490350000c5182494480100b02002502112000204204005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 961574541 1250 961573291 961573297
    0xc120c0c1701090b15030d0302040b0d0f0b040504260306030a17131e140109050f010201110315030706081509060f1c050606190b07080f031306141504050705 69
    0x36200015910034104071022520041815a041b84244694401540024868001d03202151000c120850400640648800140000d00c0c0011202c550320320380c20a080d0740740e0050f58001c078003038100c000542148004074180200c072046604d040d100c1c10000c4c0038040e100040c204c00215041003030550b030345c085407400003903900c00c80741c2044020b403411030041003515012401145404444c02e801c58116aa041304001c014817560039513000c1100b15038100320a0900b01403107160840148000120b024001204034510307042070f150210b11500301c90b0159014102088100b01418060400840707030701e41b0021030561006400411802117414202161590b01c03100000424103034001d03ca14803040400da003525000e00c00d48420340741481080301140180c105500a05100c8100c83c18141803030381803004240d0594401203044176540c404200c0c0c1c107680607000000c1e6018680c280c0c0c98000010039400d14070140c034029441c5129003004002484186c100d00c0030394580380c500a81d004502c41d0313030703d12040e15140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 961575791 1250 961574541 961574543
    0x4060c1404171903020a0f060f0f1b020c0d0f02040f0504060c320309030408030301080d021203060603182a090114061b0309040c0c120c0c170109 64
    0x100300401d0100d00e4441d00032680080c01c505a00302c810708188a080c00e10014549000907002d03030410340200022555003003c060480d03018100110394008100802c50440d4140300480c42000d58450b103410340f00700d0301c04504000344414802810745404c000300040e000701400f00700425681240c441381c0308549a6402201248050b03050811882c0b800342803010182500d900c0b1800001c1006501440142008103840b01c900406100c405100c0395611041341c0b290300150003108a44010300c0002480501000114003030f100703503c00342150241e0018080e15191143c0c0e161364801000380104070540d00c0321340959501103920301c40c2e070505044080d03503503040001d00c1c2d0107888034501c440116218918a850364400d000c0c0d05807400852a030360f541c9180030344045000d0f4143d200c0c508100203081c0b00010301b8500440c00200041e41e203044075030070000d01107528813800140858190700c2d1603007c0c040c10160030b106094050501c071100503007507640c4840d6002c40c1d01400c4000c1071419101320f00c060096102c804c4507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 961577041 1250 961575791 961575827
    0x50114040303200a0f0b060405100608011e03020d140f060f0a110903101b261e0106030f061502070e0c0f0403050325050303070c1e060f05060a05060304060c 69
    0x8906a4141b099a001c401c803200340c016401c220125400c0e2051352403041c2281c4040e56810f841d0303421320f030b540c1c010080c2c038180c54403a10300c10b60b8011025076229070300e4058491003000300c4011103200c224141e040156150032010380d60401420070811141c51001568081404d190010b49641d61800b03494040c02090034440c1c161081082c2c00302051070640c02074540841110118540d00ea8440048400d800b4942110000101164400a50350320507100250455402a030400100051007441080d86100742d02c81700c0029281d0f0040703070b4501420b1041c82c010f00a14407182c4c908405d900c030301a5903030780305105089075003400c6800101c1010f11a825a4911002a2020755456503039090881e600d070010600d1510b100004062000802c43d504600414154000041c5045d13903034010042d135800b451204241c40e43c622154000c1003030b030030490061900b0ba101e200005143d8413041101411113100500290084001e0300701032000d0340d201d405a84e0302991200b00801c40d045203403401c5441c000504038210407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 961578291 1250 961577041 961577063
    0x302072903070f02010f0b0303040315230a1a09041202071802070c060807080a0507091203170f0c18120106030b090115180b1f09050114040303200a 65
    0x5095404001e03101883d0507a4001c1c40610000e4240008031882c84885d19419801040100002401445d8100e0502007082e00000c0010032070000b405801181030412100005c44410440c0948642c0706800040e0f00c0c941c04a4040b490540200c3c000703030750160000e820070031048510004544200001d2001c0c002690300c0160241e45468543c010707402c41e5008a60241d00d0031004520f5031711411720070b8031501c40740c0d0f40d2400a480e1101003400500f40685802d040207240c010220f0203501c050443c04140c0d1190740d400c1400510128041c00c0407030050800300c5200001010301c20495010f4064a00d11030010040000c2480000c00080203541c4211100c0400d5003441c40000a00040303d143d180714000c49030080c002100105690028032049004400f0210b84c840310f0003404480c0c5074031551000c400501004028079205d0054203e42890010880c0010059a4280011350f030140006242584418043d0304190540d60003900000003000d6180c92150301031400d03a407803241041900c8501f5048481060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 961579541 1250 961578291 961578301
    0x132a09060b040305100c0e13020c150a05070309111219030f02070603090507090b0f040509010b01091205030d0c02072c060d0b060105030604060e0f0618040302072903 73
    0x101c54010344070695540c003030b00074105400f24280c001c03c410190169211500d862001003003018022100600c400701030b50074051098036441c05c0081c0c83d9000010784484520b49400d195000540f60010401001c0500b051001c04c00514100e0842c0c090702021514a80d440c1c4844000301d1138000303140d507a400c0c8855400da0380d206040e0821007c0b03400d8440755099850858880d03800342c0649401e000024000e45c8000ca0070080800326920410351640c0050441e40007001b104001000c4d20750503240c0e141c8a03503603007a115070191f80041030000101250381120099107801d07140d01e522400341d201000c110341d4030b036090419540e20030b00000340603214940440006803544010b120b03103881100130444000000a01013003061400001c880800c1b07a0014000381c1c3c03907582200441e91500060b00250700141c840402003010040b01c1c0245100e02c0e6801030020f003a00e4001c04001441e03500c1401040008485814000400d42c04500c1005039807000403024401c16504045051036942000551035040e00401880 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 961580791 1250 961579541 961579559
    0x21c110903060a05090f0712060c11010207030314160c06090303021905030912190e0f04180b0705090a17190b0403090b0a0e0405060a09020406020a0308132a0906 71
    0x50041100c01c0461b15a076003805030045c2d9509440c00340c5a00b60f8042c0c5c0b0a60009040c58201207003856031458900c41d070400749080682687c00007d02100400c3e1a07948200006080303a0145070b2045400c1604055801e8503d00030f0400f8030440c80180c0740380d460b00d003490189402601110110103140e030090308105660034004003990019540d0b00828040d03041c0b44511420044180da8801e8016045201565502e100c140d84004040100b036810500b81c18120b4103641d15032081401344003080342c0304021620a40707003451705500001d014100f4001c0500040a01e134a038035000c10f064490481c40c01c410040c1e0861000e243c041c00b13440d581441030030100f04904114945d00804d001d2440b03070b111241d41301d0b2220f6603201a8056448004001035582001c10051700d0030307410141d0068000f40684042d6a250032007042a0790240c1c110f01c2c0036034403980c005003c0541c4a01842e42c411918422800284c46030f5442c04480d069414003140f07010fa2035a051030395143c0b442d0300c080040003208020400c070342c0e50f22042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 961582041 1250 961580791 961580801
    0x70f210216150b09010e0613090803010b0d0b04020a0c1e0818040b0904051903140309030c0f01060501170c1b010b040b01021902011b0605010621021c110903060a 71
    0x148400c14200b0f040e401260600780d003424103840c120054511155648030620007c0c2c5001c040101200d0380b41c0d034003080400c284400840c043c081182103030781d84040000c034110544185840003401180304000300f101e1940d1001c105044181c0c0720f100c001d200c0b4100c082825280c81c1303000c0042c02e082c4000501408039004403185a8203103005803418070813040c4901c20403c1b0b18900b2940a401600101e6810031a440b410b15030513099846800c002a0a07000d44039090381d1a0400c0b540180b82d40c0c0006030403100d45404116560341c0c203039080c0003401140d01307040008040a49804203e00c1003460200481c3d0400b5210007600e99450345014032061504129517045c1c041c10102e030b03002d030103903150948a07065944041218070b0401d201c3c0359291b0011b03000358011500d40070f094211b500d02141c0c10504038009552070107080d000b001c440d658841000360243e010500f030040076540b101c816104110700b00d003000803443e016010b40701031a030010303030034013619443d2000f4402e59000907814050703034080204c0c4040350380c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 961583291 1250 961582041 961582073
    0x91905100e1620010e1002090a0e010f06051e0a020106060f2606031c0c05060c04141011190c08070b1e0d05041505070f210216 56
    0x100d00c69a481c0c540a9007080a140b5a0b24000203d503031a850400300c074900c8607100703908894000000d4030f00c49419024242640e500141c0c0c4919000030708404175140a4800501900e41b807210240107524251410502000078421141441804035620240300b584060900c0d44008400780186c2d81e40307440000a000b440b1500a201c0401c2c0d55200c04072082c0d110303d40c0000080e4561314000aa42c0001101e00c40d00b041c000c02c0c90b645481154004080030751040402c10149003107840b0030a001405250007810100014145940590103000c100700d140031041c9a09403982042d940c42e4003080c03040d281211a015030900d08141c42c81001c085d00d0308a040816499201805081035540351a00e443c0c110303031aa0035604c900c003400c01e010320009216034416200b034407561140000603490000d00f40d117071909460003190f041e5840c07200303148068100a0180142d0745d0191f0946026800c01c240d10f540074003190920003c00040c40020404281e000500703904403440103c5440a442a000b40e61510782c404a07003501d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 961584541 1250 961583291 961583309
    0x110a050705012a08270304210c050f030a080415080606092b0c030b090105060301060f060f02071802071e02010f0309021801080309120a020d0209190510 67
    0x51691811108044a084044079003d101a070310241d0700c400ca4200b50041e025401004822650402c4500700035820913994101c500030f1a21280740c0b000d0b10150801184100740c0c0800400c14640020701401d241a0030743d0012280c1c80507402580f00864500410078034000d1041030300140c04209000814003982118240c0c0e44c4025083d40c0b80002e0101c1405170340c1203103401c030f58000680020820700d030003035a071000030a078502509000303952241080301070107500580308c1000034000d01c41269028001c040d40a9401c3d0003e0201e5803074961100c8904002e4400d0700100402c4003000340c2020320a02880c4006d15590311200001c4105031000402903100c40c4040301c90041c2d0301315040c4062031aa1040e03038900d4058507508400b41d0300100c10f9001d802c500c0320490780078049920059498803c1d00359a40038060040041d130301c2e03225640500248000522a0150300e501400080c00103a65613803141c08690340c1600e0174203154803030a0703c545441c41c0e0210100111800c0c502040404403e01044600701e541d018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 961585791 1250 961584541 961584551
    0x812040c080c1507060c271d0f01030602160b10060906090311040504060e0d03380f010507050d050715021204060c050906120f0609071b030201110a05070501 69
    0x24081140c01c3c0014004141551400c0c032124000c1607090740190340189550810b0500308001032a03440a543c603491588604003d4402c05011281505103102041044400c1d00e040c40d00308080c804103034082c140302c010b281c29000190300380202485082104056401022000f06040040000d4140c1c41d55001d840c1c0001e0322941c0000318140300340c1640f8100d030740204c202c0f84d80e560341c003040c4805070000400503504580c65140405181c88200428001d076601a035000490150070064100da5886284103040106034a441002150710089401c03008000304548003080c0740e01440050702c1c0e60044140c054050f0040385225400c0ea90001d00400c070b02031182044144001c1402400000c03805000c00c650a000200303c0001c000400c664000994114103003003036810080700c00000740d010751082420380c000c020f10109228035020031501480d006041200c005842d8584424002d00c80340e001c4c0d100c5e000300c908036135107041494001c2d88002110ba0005801542c0ca2021001c042c1003a40050030490b41e0b58070304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 961587041 1250 961585791 961585813
    0x90a09060302032103011e0e09030c0c031216021504180c0c0b060f0a0b0d02091201051506221511011509020d06182004060504050d0812040c08 63
    0x10000454104c6080014542540d0030b150000c2040741c0c41000c40c5012034050f01010071008056001c480c402c0d00450025503440c402c0340400c506218811085a0203a4041040c0c5825102042d05a03440d601010900700e411505600009442c54041982001800c0c00001c01003110f0070410fa00170755400c0c95800620035401504811101811141e0002d0f2020391b80034046011407502d0755121512050007044000102c2d140c520f8035400741d00468902d054944d001600c0702c3c0c40c1c24403c8031b00404481c81d100800142ca008500a003e0f58a09000709100c5c04002503025048140070301c46403c1903c0000340001d2301505d03140d0340250002420400c0011401090b00007507914414041d6010703003c09420b07841c00f13580c40c182c070308000b075080503c2d010601a295400454000644000c000c04880014400300b4441c2218841c4180741d001d030084404e007440204424001c854200c4204c07000ca60050710480ac10a680381894142405940c6100207002e2030a010321040c84600e24051040c0ca46070b4056410308186 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 961588291 1250 961587041 961587073
    0xa08010e070b030c030406090302033112080d090c23040b06190807051204051522110d02060d0b040c030606020606040c18030b0a1109061c02090a0906030203 69
    0x40f1a0b21050450810000700000c949411223000580710f03004490400d419000c1c08d5101d41001c405860514100b03021425104804110700300c02040084c800b0380100d1041d40f03495942d482001400c568054130b8981d0b400402055009840040500290300440744240803940e40c036111903488903d00c00d6081280a00e07440c41c1410450303604c490b4038401100c2d18540c8600c01c0c1d0b440b48000b00080d0510006100300c4007082c60a0000910641c07042018211002e600d610716809210013821200d4640b6180341c600e0103052951921207407254202804070301d03030142000022041d4101c046e00a40008004c10b20b03404541994020f82c103080801c550602808894a0088044408521171440160700500202d045410070b07500032441c81c3d0843c9019880324503800e846034043d5940d40c2c401c4030046890000c200c014040361040c10b00c8144100c00c01c40c68042d02c0d10014640d4091080005548000d020300700441200540c12030b491800060300c05105980d0342c0300c0c0440149032501c8103030300070301810800500308a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 961589541 1250 961588291 961588297
    0x7020f0a0317271c032003040305060907030201080408090a0f0905150301050601120207020420070501050f13060e0708060709031118010b07330b030f1c030b0a08010e070b 75
    0x18013030010180300c1d20b020301141c0588101d49065003400050b00c50300700b1758401582c8401341078203140003e6940da842d6141c19850107070b0003045c900041d0040c000070700040c1e0b80200c107950056008140d070364030341c0219000948114000d621180843d02e1368140050101e42e190032880c41010b406c0d8040343c49000714070070b05080e10012070b030742d034005007003c0c12a107500340c055030207011800e001920025292680800340c400e10010a07054039000748001c2411410410309015140c0d03c0041690015028100340b44140e4031500c1d45a0020480754440742100c0d10b071f043c2007003c0c0e0010009501120280c0c00c1651b00504480e240f130105030707160720f940130074540c1c41e040400c0d140107012004050042c2036841c05031010495004000200d5400c203443c000c121200f440c1e8540e0200132400071448000c0c00c2448148a4100c4d040d4103512400783d00022a003104492000c03400c01d020410108181e41e4140d8910310403001807880004980c1d0085803241d012a8070081544103601d0040d02c5803c803503480d9180c80d81e80c25240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 961590791 1250 961589541 961589617
    0x106060305012c0a020f1908060a1a041a12180d0201150302041d010c0905040b040c0c080307022506030630110d050607091a07020f0a0317 61
    0xf041c4401190038405150f0003403a0304992403200c1401c000e04425910460f0b00f00e801da00d0000744c201024420a4541201c450009018100c10f141d03000f07604100102544c0141c1c8111414000c0042c20500d0295800003240c5030880b500c11541503502e0322000428180bc0d0701101400188585d10600c0d851500500c174400c0c2e280b42d400e21001c0c44a255508200140120f000807140285200304d000c4c0d071007002400b404000703126540750300d100d0030306010501c41205c024600040c49907040404c071003001d070340081100e0341c0d540d004060203a40360740d0b01600381c0c94542070590106240180100c1c031080040602600d40c15503100740e60502107665110800c141007255070354140d0302c80303090051000e01451107400c54210a40b050300e80749082070f5803400007a000c1030228030507540e94120904000c00d540d030214003400039104040081c1070400d1360700b900c500d8501070303000020b01500b54029243c000d41c0c0c691025170011355100594182040701c43d08030342e81c0350300004a66104048004895191f1a0101310101e07022 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 961592041 1250 961590791 961590869
    0x2090306010b09040e0601080d0f1b03080934050909070b071a070507060608030301140411090d0c14090c19031b0302210f010510050c010606030501 65
    0x41d90030103624500315880350b21400d0344503503180e18040700f01c002400458000d00098002c4c0c460785d004100082d2420480c40082820052a001416454810050301d40c0d00c160300341c9000851a50b0310244546483c030b94078481301c0101d035a407203110584e0040c2602d028401005400c0801119500c40038802500000e840072004e40d0440c00003404407200820161145a000304580c0d1f2820081e2948800c2c0c980c4107580c444000b0b540001c014050004502401c001840100000e44c50f40d80340035021000700e28440346041c4101c6c0c0f110310101480811509a07048000c00400314810900c89150400c01f0459074800e5500e14092201083c5051030400350403031060071089a014604829264141200114609801c1c18599a189400780d1000060500b001145a0f41c600507a11041900186103600d0104803090202211030100404805411072440c1103903403c1e04c0041000800d60b10a0b103540c0500c075032100d004c4d8a09200060b84950641000e8100ca10704000c0c5c2a89002802d54007000c680306c58a40984 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 961593291 1250 961592041 961592053
    0x11e05060405220902040c050d0c2307110316080d03020a050706051e0916080f250b0c0601030314030402030a0b060f0301090602040603060803120103020f0a0b03040501091203020903 80
    0x42540c00140119420064000281300c6100754006021075500601c0040041d1001c142d80791950840d10689200c0c4c0302e00d043c020300c005074625030260070b85401039110404690120380e07001000b030a4141080920801819108410100507045a03503107410b204007003040c070070600c085030031600920844490000f6692403e10341341d219211600948400303444181391901c049200400210488003044c040d21109001d0120440c44c00300b1001c1000584c0c02481c42a0001806050820400244001d001c040a045034a0b401c114880740c10004000b07600155101b600080d945030118000300ea2141a24400d4841c0c01c14000d103121000e07214042210002d40543c00001c01c2d801064510007201d038032001c000d04e20101d80300241d01103801d6850300881240d00c140c01140c1440101d41501418014210301c0d070007941441c9090030100304050041c807020f400746211180700300032a1100542c02010b0b0001c141e8140d40c074106454058000d0035003500540315042892251281c181c0300c1d0080b103500403002001008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 961594541 1250 961593291 961593319
    0x150a0e01060c11040e1c090605090922030207031b03020d50060f070332090c0906030703020616050f061915060c031205011e05060405 59
    0x2104102004282c0b003145000f03061400a941d640100c80d25a8250700246c08030086180c41072414000e0607200b00c05100900c2828031616078003105407144107170304031410003054a48440c5207401c417400c242e080003660b43d54075680013816000a00d802c00c80703101d00f1000c42d002204110b080103451043c000254443c20541000012a100c06060b81d0001c00481007051104180004800316400e0300c0c0341c540031555075040316101408a0301e000740f91580b504000e401245052900154044801006202419034644d40002000d1402c080d140340c20f941d00002d40c1884021b51260650800308642c40c01480c4101141645d0605003030141c00c2c05108060010002581140c3c2000440d8204080c64440c0000c2c0c082c0510205000700b088504412944018005c1814010303104005100301e0700c4c500503080e04001c449503a064400828100f118400d240282d007145d0b85250845203e10701112100c940307400d00c00003080102c04840030701c40e0201c406c0304402c40079540e03205200180c01039100b10b61340100c80a001c5d60b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 961595791 1250 961594541 961594547
    0xa120b1c03050a0833010201060504020301141512070c0501060b0a110105090a21020c04020d1d030304050d202b020a0203070506031308030a02030f0a05150f060706060e150a0e0106 79
    0x81d1703400140004943c5a88620100d404c80e0026449400b0042005030548081d00341030390400800c2002c100250702d1301c014010001c510203801307002403082048400302c20051203820b50184000d01a48107085554018616008048048400199906500c1e0030003141c0308500000e585445903a0054030100b0302810302612109030b01885c12960254051b05610b00a20365035071000b0015151091400100340041c00d50144c092613000e605002c0c40d80c810000d010215000143c036890a50641c5001004013240c0040248541c0600301d26852502c1381201d652160341c0c0110303441c810000c1482c00c088102c285a40c040b0f0343c415020344040d4164200c0300c0d080c001410100000e65004c000c3c042c2c034002d40c40d03d0ba81d441c1211381c021103d56440560120500c80b00781c1441c8422030304603050000030b01c40c40c104850000c9141d01c4c1c000b0030340e1140003405074498031600c645007520150b54001e00100600c580d00d00302d00c850356600701e0f00418013548201c94145185012460302e0140c03100d180b1100102c1e8200042a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 961597041 1250 961595791 961595881
    0x803070f03090507270207060c02070506030f010b0a050f0a0221040302061b030f0c060708010504090b2403010e010b130c0807050a14041211060a120b1c03050a08 71
    0x40000213100030701c03440000810b40018854523101d01000a01a80c17002402401c00c0a01d0b0807040c410071041007444910410107440c1410369254a442a5444250740015201c42c0305100c094417520318086540b400d850f401180c9031705200c0003100111442040002c00466500c503d000083d403143d0248100010b034044d0300c1078072942043d5a001c880c0b0b0a2079a180890306500203241201d81a0305c80d10030810760f160300c0200c940c0101410340301840503140a070340b28020036000926100b11800c801100c5205014003515004401c07801800030446400011315035406070140582040c01111650403c034902005846034030405012591801d8868403078841c121082e03840a542e9500308040120000e200c00d0050000b03000030501c6001038815071791646010440c03205c00c103003050311401003440b680d1241a0010310210f2084c3c01e04600085455070000002d103148085000c1e0f032241901158408101500718009102d02c45450710364901983ea407100040358444241e00d111600081441200c1c9091064010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 961598291 1250 961597041 961597079
    0x3030606220b16060c050a0e010f0c0b18010509061302011b0605150102010b040b010f0f110607080717090705151e030109060b030105060f16050a0803070f03090507 72
    0x180102003a602d415201407074101c24602240d4a40c601d282108201c010302c0342d004100c0e45802c1c41030510903401d8001e09075011008101d4103216125582440403442080c41d03500c0198403c143c0001c6007000009800400035802140d001ca6107030a01203106004002100d40c4030301c202c014042e5080049a0045407000141703100e000b07642140440c1000000c4050081c03d11800c000041d00000031a80070009094411003080a4062840d140c1c4405031a40d01000c80389584482c3d0a080166508a001c1250500c0d00880b90051a00402090003041030b800006940140e07000d03918020005285410001c1d1403209136098181548a0203080005060082c01c0810981c0000c007543e040502e0b0f4012420403060004454818000000040c4640601445507502030160701c0d984a0640d81010301042c100d1040c2c160500b840c1d0303004a856491003603c150744c403000540c08001c0c0e4581413528a0511865007054030000d02103107005a2030180301703220b4413500a00603040b0b0f000b441e0b031500e01241c2c0701403107038074200f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 961599541 1250 961598291 961598347
    0x507180e010e0426221205071415072001050f07203102071106090307050307060309151a1018060e030601060816050c1f020304060b0303030606 63
    0x340e10403503000c00e001400180c1c00c1705020040203114942c0031222591181c000014180311198010081400080d0314020748500c07540c1181c9410725071002800c820140c01104602d07680004428007004000e02041a0000500d44425403028180c0010b440600a10540340c18003e0309100c00d80104031b42c0c00c90340e00700721300034043c00402d501c001011070a640d0550501e003222405d4a003000000c1e001c40c904640303c0d0b440b800d20860034894140d071010041d41501301c145204041c04100d00c0216642802140c0003840d008084401540d91060090044c050f0752000b030f520b41c10b440e2042d45860740c031401480740c0e490016800c10302c415068170800c40790100d2006003c040184020054281c1c10170100d07064003603e8591107007041c3e0900003041501d000701c140c210303400b00b20040003485050098654030154090b00c80c02c040c0d0301e80300304e0b101c06840c2403114280d06c2c244241216181082140780c1d4001d5019a02070002880002c2c03041007415074031302c01910029080001000803d07580301c4c070740c60b808110038010340f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 961600791 1250 961599541 961599593
    0x41a04020a030213050603060f06060412110307170f0c0603041b0510030905010e0c0102071512060e010303110f0303150d060f0209100306060503070f030b040507180e010e04 76
    0xe00030450880140781880c0132165900184881c62508024840c0d0025108035445003505d400360119007280901d02c5461284540d40c000b240c02c01901c0c3d01039001840e40030b8100e499840d9507403121007544190114078081c50007101c64600c03d030203020422200d01d14003e0540740c5542c4440d500d0400510501042100d034031150b8034081001e940d0710f15034069220320b82c1e40104003c5690b00300103013150030007240c2c4101d540c00381c1ca1142e060398003c5404801c460303102140d54102807410a007030b582044480d94100046240ca08041000c10041d412241a030f8040d6441c400c00080310441c13203551703018503558921a42d1080c80040c00245a45500c02160b0b040138191030b0580e08071741e84080949a03550100103180f034001c00c55200a080610380403051040c580b0b4180f141c54945803010708240b2007d0406400c20080300d04508159000742c00620038102c02a000701300c1ca14103448000c21410180c80082c0c03d002c003800c40090280c1400a8407070580d00801044501da40340c9079944005200c0f440c04400c0e40800403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 961602041 1250 961600791 961600793
    0x30a2c0d0e04090215250c060e01050f070b100e090c121504050303040215040b030703050a0207140a0201090f0e06102106050a0518180f0a0303020408070b03041a04020a03 75
    0x51004851600c03145007905d92602001c0b12402e4070700000104842d82c4a00c1c4540d418041400d0403108812283c2608180381c00303004c4400125150320650f41c8107411034400042007020020001a800c0c400c103504e0542c0341c06a511810400384213001554000e91940c40b4842002c02490084901441c059040d001c82c0c0d0350015001c80280c1c04942120103451303a40020007040f0942c2044007102d030302058504038040c130301400e05403140d00500000d400441050390b500b00040420005904489010b038004480040096039540341644e1810945c03000c0703001a04103000006d01d026522860416501e000041100582d2020140490006100340120402c1640c1284d4050018240c0c050f440000d10407e001c50751b40d040c04107001600f0001d43400703180107990300b086109011101058258010041182d50301d004d012092415141280800188040d4040e82020008164042e0f0050040f5240c4000755100d40b5a1401d044010380030031100030348400146c000584007803150520340c07544240f00508440c4a5910303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 961603291 1250 961602041 961602049
    0x1128030908192102030a18020a0303030908400f0612150b0403060b0a0510050d09080301120c090507021c110106091a040c1d03070b030a2c0d0e040902 66
    0x507810f1411000380d002060000391040e81c05003030464125215451484103540c2c0c08550003e0082c400601010759681c817910400000508880c07012080c61000c524403000100748107070f051a0700010050703c40004400d140d000300d419181a0440e912100d04501c000d26081d0242c0d04c4d04103800c050016a42d513054000c90030900540604041c12511108a4941d421460030b202202e4600c0440c5d0b2281c1203600040006680303850b81060411590b1404984510702c45986001405a180000b005000040004141000080d1015403002d00609003071100c15964911001200e0040d80e0b03180058224046070300301203900307818003440002c4501c1e00f240b1819800c9040c0b403c45915401448213103890b184446004070446802e5000101c0896007046116040070015068150303000360700500200741c42c5a80c08a60b418092100204080071913142e03240ba142120070028140315049a190f40e40000300f0080c5545020320031100c540345c0704001c02103134410305401d80d81c140000c0030a662058883d9840380050316 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 961604541 1250 961603291 961603337
    0x60f120d03110d021201030b0a1a1302130b0a03060e060f0f01020a0507080a060c050a090504110705100f0e07030b0604090c0803070309240e060904112803090819 71
    0x17034001c101407100c1d419450000348003440980342d00c940e542046961040641c10820307400803480700300d9080c0c0c40302c44000100340c040e0051580806003000c00c0b0700002071590b0214000c141c05010341e601000100e1702c502c40040841800d695481e000b4a20507078148407420040b03940c171001101401110f00b100e002d40e84d018500080c41c3c21020b204e42004514404200031401800303840c1d59141000303030400012002c000c20720140b82c81014800c50716213210b02810600201200c0c0d031103410005488451250002c0d075005009002c651401703040c0fa01c000c5660140000c01c4c41c40070349034442090816030301c3d4003040002070605407000380c500c0305a0181c000b864900070801040b0740c51003501c919038110301d086801080e201e56901e082c0f4200c8604010184000d0340f00ba100340301c83c40e084840d01c2d2503400003004500205040b07800c2c031040c2c403000100e0f0381041042038000c541c011250604149a80c540ca4002c40c00c1d01c2c7d940c0401413010b08103000520061141d0480301840c2045803404010104011100e00c144079 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 961605791 1250 961604541 961604557
    0x20f030c0406020d050a1706120f1b090705070b3c07020106081015050a06091a0720150f090405010b070203071a0d090803060f120d03110d02 62
    0x242000804002d05a018071802d180340744c0c40d0901c40e0038080484c5000d810034000b2002040041d0320100096456500c1c070f100d60400c0c44160084409500440004540d290701010007a80c021458170369070b01d5140f605a113405d10400141d0b84141c00d1042c0c4e550360b0780ba483c2020f400c981e0510a0500307100101510352001c1d408454500300688207a85032185108070041000c2c02003000c41e4100441481410b500042d0350800c50401d400002c0c105070512900e480380c4034030784c0000c0d43c4602400000540d2561101501c820703568010f100012a800b09003802010307104440c00146940f11402da42c0515402020a01c04284030140020001502c1c85065608a9101d465890030681012490100e14141441068054054503c50624280c025000241d484003030f840380c074484205600240c200b0300c040e00d041d65000701c01040c0501c4030705024a4511855042169410f010b81174903000b42060740391088510740b8903007240d03000d000c0507444400100c0c0030b800600644942e50704200300b0b0b40c0a4141a20042101c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 961607041 1250 961605791 961605811
    0x31b050307050a2003011418010905060108030307090801060e040f031b081c0501030b041118010f180b0a140a0b030f01060206060d050d0e010e090709080105010b0a050d0f020f03 78
    0x4c260300084041242ca0014081d03000781e24005801c41c6500c1e1003003102d50811001d400707514032001c0940c3c0460140549000043c03aa00614000080c6c1c90400005903005811645132340c42c9040c5c607600018201d6080788980d0030002d0301c3c1340c04900030600b094545a4818000d10f041160b00c0c1d1042c10788a02e106010208a1b00f180002904584241c0140402d0b218081940d00520103545941c48030710a03c0300140010780f0030580c00741082103958030030340129020b0000196644082d80d44021100e04549140304407a814402d42181c120070030030350300c9081c0740104020043c00d090303410000721841000c0e41c440c880d90040e1200d40003041000c00000558445c9110312a1500c076981080c40c02818142c0c090003031806000c80d44032100005002042000740f40303099117031400307440c03a0990048918240940c800d80d0812030880c140010340383e0024100703050307481c0c1c540244000d913624801c4445d588a5031140380c0000c0c5051018294094454100c1b08030000a1540581401c40441100720300d40c0c000d443d25084 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 961608291 1250 961607041 961607063
    0xe0303072006271c020315060a120605060907030c0819020c0f1f050705040e090715020a0b0721110c01060f03030f05030606030105041d0105070e09010f03031b050307050a 75
    0x8249407800c41074008804e401c507500310381201540481da613201d0740c2010034042070707038940094145d448400d200350040c1004c0454200000350350412078000e0805076510360140e07503c01c0005811a029019400d440b0744d0325995182c103569412407414140389030702d0301e04032000d80812000a62190030007484081e0201040500103c40310403580200c10080c0d01c4843c1040350510040041c140c0c0c0040a5400b01d95006400750020343d5048005030070900e0396084141c2c04040d0b15140200fa03170f40040c2c1200360030303c64402d03500c403034541c5c00f01070b43c038851052450811444540c05943c8855480d4000e001042295400e41b420f02001c001414203540c1260020101440c4004042052613071144019406890307600b0031516504000c1e0201e0031038401406524019911090807000141c5003410031103420307900400812117411302010044c113080c8200c0085216501240000c0f52140f402610320085a1341178441c549401c4032082211081210003100b81c980380424011000401c02c02d001035400e281c4100d00e6400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 961609541 1250 961608291 961608367
    0x90406150e041d03340b011d06130f110c03030f0c0702150c030904060e0702280f080d0504061e090b0a021c060b03070e0303072006 58
    0x81100c00c40d030402003c01003070341c500034104880803080302c10103e0f1644040e0034103050784900d03014404d0001d0303e000d10403014110410510401e2040c2c9410f8804a6071940c2c82160208401d4250010580c5c44540c0b0907282c0f500040c1d004101e1344004903100d080e600115241c01c8440404009400c505070590098000001308001800007000380b6034440c4056410070306000c0c45401003000914007050303405500000140c80c0000d44420401d44511410040c424842c450b00c500e000e018003101590204d0161042260303401d081884d52964400b080001800b516004105441d0042c05d074582c500151440030007004031401d00181405240d2203180135040c007080142d001d088a040c44a2101203241300b0500c1c14242c0c20000b0740003810244c00490300c01c070158036a0303041045030706121040c809540c1d60310325004001a9900220000e580720f00140e480d0044001d9010b010300d512445040c0c401800b900c400a80300c009414142041c00301124060b04542c201030422006101900ea050886002103c4000e1450 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 961610791 1250 961609541 961609549
    0x20c060f0702070b0d270f140109030806210f032817091e07140121020c0a06051e010503070b0a05070203012a1103090f06090406150e 59
    0x5a008074481c401401c0c00b52808201c007280b802421920184162602c2541c1654440c0b114003890343c80766100c00355a9031240c0d140813403c8003030f400c0e000c5600c0b00c10165000c4290406100d07802003190140c503511400d0740c82c04100701c5426802c0c43c800c8000742d42d02c809561a20f104011341000e20f40114011517072698030840e1450144a07030507a07120040c050591800700c49038022103102030481c00400e5600540c4606600500384030b00b2029004d1210075141341d404000c07000041e800211003c0c0e0140e0321044200c80c00440300d4400390008500ca4568142c9544503940741d0ba801050300000140a45400d900b084d0344800580e9415600815001c4a02e0240d9190071031107211903004243c00c40c01802103e140415201d03240c05000010700c180000440c8280940d1821b4124138100c00840c160642104071201034913607000c0010100100251400080548030074000049602e84880101072101910301c810410280768021407a00da003060b103072400010000302c402c4100030008040c2e11016034140c2c60200780 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 961612041 1250 961610791 961610821
    0x30c040e06060a05120601090312020a030905040b010509010503040f080310051e09150616122007051c121e0c02090402060f1207020607091710150801020c06 69
    0x74910a400401c5200f482c5a0000221442c00e0003800b4014090707910100103a45a5000d507001500e0548402c03410a000c43d800316103008141c0c440d4403150b40b62510748040c0300031915a0f98005d40480c50411101103558010341c080d50f40188250074403174800c0850b69408059802c01e0301c00c03110891950106000754600340c10000c0da0242e102d14a560360004602c0000d60382d980280041c4c1c0304240021607c00540c075420115038102007641c1b041d110712256480d02c1e2642503c005c2071980007034440c1c0c1001c80000740090342c103c5000d180a006000880c1041c04102ba00c401c9003406940d0a05407009140000317294100c02038840c015502c40700b010001e10600000003072558003550080050710500600141e80e4808550b0300b160301a80c140f41c480c00c0206e02c12545100c0c0e414071400c0703a1924010040760982c0003440d10700c5240309075a1019426a82c0c41c1c02443c60780704446141044e08080814100d0105581c80541c80d10102903604d00011380e10b100f41390890b4000b003142c10071034200c00700300071642084540b0313 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 961613291 1250 961612041 961612051
    0xf020303070801090c0203090d0b0117070f06121e05010e10050a0b0307020a020303180a0f2904090c030504060b090c040b0a1205070203280c141002030c040e 69
    0x265146150140c00145400d105002d1048000e550301844400703c1e20800507079203000c40141818a000d8403500b4003413420034003445003890f580c240d0766122062105c00f094034002c585010414186490070440d094030303044450505840304e1555a440024a0800c03030391005203002c000345000441d0f5040410311401007400801562aa40545100704685c0e12103072121303012115841203040d00d80c0c640590482c24680040c038007951510021544076200000c628401c5400c06d42100c0b02c5d501e40b603075291168803c2d46544295424160136054210005503050100264034615182c44d6160540b1140030004450008440e8000a550b450410080101c280300d0540c904d981214402400d00d000200e18109120700c4c0100604080d022503054882d5006040840c685c04c82810244298030380160300a64036040008519000140080400040103503c00342d482040074540c4d800f4001c40080c2c60b030a10380d480311000d03054140b003094007082121500744061409140d680c213900d80c0d04c500d1306030320094940d8003800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 961614541 1250 961613291 961613293
    0x10b07050c09090c120a020604031a01060804031d0a050a0828020a150e040f05040308130c050114220f0905100603050603010e0d120c110a06021b0a0309060f02 70
    0x10611641020004d03020030401390071a085c24102c0b405d084502e0800c80e074844008e402000101d8003204103c6504659000d480c00300b11102c81b0360b81d17180700c126010b11050b10003802103804d0312104050200e12208541c003001001d044103000350354450108150461580c090700c125005000350044059111101100e05e00000052082e000c5c92074001074580744c0c481c480d8101d011807820900690034000c030700c00c3c01c0b03121004108011800d03030038000001030300b0102c804800150f00c1d04000380d100c10585240c110155007081030b00d10018241801075882d240307400c1d980300111209010320203400021011308115440040c0c1102e01543ca082c4c141c10082095411101c0d696040400700b109054a6598460480d0300500d000316a42e100c42011900500300584110384c1030240e101c03240b03680c6810807012120030300c08040c100920403c01c0012510b180480c03403da0b0a0b6086041c00384040b030400e4014101d11000b242001c41084101004180340100c0c51104801040c44008200441a000700d078040c1030b100640 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 961615791 1250 961614541 961614559
    0xe060105060a051303080c0102180409170309100204090902010e0d03081902070203150105190f05060d02161406010f0b03180f10091e03120b0d0b010b07050c 69
    0x100040c8503802500d50b02e41c1041804103e04c02c100781100c80300d200440c0c024807210b58990810714014081d40c88103011810b800f41c5483c0c0c1e0b104904141c440c50b031040b500101d6090040d0001031941e6160f030b00207031603418035128034242000c8510542c8014401085008070008003025103100141081c407104d403c0724440d504a48911000c030340c10105541d40002410f46180c1e18640844140c4001d01641c1400b075003610030400c203a01b4094090803a24166030742181d00314170006070105d0550b043e28441c010202100c941c118100110b05252015101d01441a00003504001444c00b128034040103003002603c018001c2c1180c400c0da50f2080c4641c0f4054a0702d10344810b813607814044c81c0201c070301c005020140030040100214420010500004a102e01c81405840e140d00c0d40368041005001c5d98a0280c5440b0481c400d21401c28241c085450380700350f0b00da2544d500003102c4011503802410404241504102e8038000070000814a80c45203000e07041800d1501d85540b0b86d414030900d84038550145c83d008642d89 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 961617041 1250 961615791 961615799
    0xa06110a03030e032b050109110f1b0105101404270311010213050f0612010308160204060e0f0f010302011e02012a0206070c03050f03150d150e0601 65
    0x104552604a03018240481c1d02c09400f81402d140d8032480c01c40602d11071032080913002d050400c014500098014010030710090b41c9444032241268075811190f014400d00b04042c00c0780158400c09803000e001e030302c01c034036243c000c0e290703c11820740e0011500020715440c00d010601c0100390680b01c0486d4400246c07010082e10040d88480401c1c815501d000d5903807000403c01c1d020425100e980074090074007101000b5074032108110341801807050603000d41446040695a043d8a5007006002e0f01d01004103007801d00d50302c0e441c640750300860f03030b110320403040c000d80d403026240003da22507000b543c00401220141d00941e2030126040c4014480107044401c03120f0202c0c00400150f03038003519150916690011030014941d0880b01a8010440002804501800b591150b21003071142d04d201d221280c210f809880c543c3e07407040b200712840c1c590490010007040051103103a50507030051014650000030b8200b0180aa40c8000c000784004880c042c08640e155001103500109040700d000f03800d00030031440002c1102d035041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 961618291 1250 961617041 961617043
    0x60207062114040c4b0305010c021e070b030709030501141b12191503050601050a0f0e22061815090b04021306121401050f0105031507020c0a090b0a0611 67
    0x2910f000030700110341182e917803050001c40e03110b1110a072804400d8014010f6880c03901d03d021b840152041c40140c003504030504440540c3c10300f80e400790300406000e40b902e603007420350030302250300003030729100400c0264040440020300c01d00c143c50500c001d00c00f108030300e0b15210210040740e00d80120101078415050044481100410f03002c280c0080c102d0001c10070a10146c1e0041d802480182440024000d00903c00024421301180541c140c1e8410754902400c1602d54912800c40c985501c69182500d02002c0006c241001521401017003420420206180c00c40a4480074190707640c80020400500c41b1040d17017810801c20a41410302c01100c4a820300100b1455102c4020340380c402040603000720112044421840f039903074041000b600b48131031807984039001400c0411421040e0151240a5072800f00450b40b05180e88034058100c400040007080c0300b0300f448507610340c0c0704000740803481980328000903400d45540c2c803c44070780501900400051070151030000c2044258492303200d4020303c0710051001c2c01c081d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 961619541 1250 961618291 961618349
    0x60803030402010e1906030902150405030d230301090b0f030d0509190312020d0e1507080c0c040203010b070606050405010e040803040c03121215060207062114040c 72
    0xc0c090801c030b018204e000012692180c4d50b41d0030042607045071100441e01d42d1f059803060030500e0003524004622140c0720340b20002d512943c003456a2582c460001c0780300003449003814028180540703100340c1002c60300741c2c50080940c1083c1c001c00d5000e600c841513200641055a94a9040b020403070003070010700c00c2154003030700c203109001c401d5029242e4900740ca404103902096400041d603204005208007916028000d4a402280d100760700082ca0041c044100c1c0d2404006950624440c403100074600742c000d075542c2a0507400301c15510344500900b601d6103642e95032480514020016520600d030395000d185030182c04c0340c89a81041d84200d143c100103000080c40d0001032507005a1040c1076603502d0715039082480404885510080c9060381d41d80d02d054005030701c101500241c4502000c144414a8004511542c0c00818000c082c010b034414030080220502c901c0041484104868000c050f561030390514800741c0d42080c1c0c45801c4540d068060204009010b009840103001110401400c903c5028106101030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 961620791 1250 961619541 961619543
    0x3060f092b08060405250c0b07030b090108030c100b01020f0601080730060b1828051905060a0807030f0c060914060901050d09061a1921020d081201090608030304 71
    0x7580703186620ba07008050111fa41504401103480500d400c41d4009c005c0e00c02d00c041a80125103c1000056408000083d241030442ca500a800001e0054403013800800c00c0d501d4076411846030642190081e1403c2c4030450181042d14054200c03181081a441c030f501c01c11625405080254424201d00c14103900b0101511070b50000703021034511040000078500c102d151400c0b440c141c45801c248800c08220912002110003a10091aa503564090500040302d40032a441d850072100c854180640f1721135603000c96800140101210946600c580c00545488a0ba8208584580906100c1828030442000d210001c01a078030740750403141c0c14035510501910171900814041c500210384500e4681c083d500303549034000c600104001300d00c0d80341408030151192406003000403002c4940c001031805c00c45060400854090040034038580b502c100502c08c148261208503040000b0071200005030740b50011002c2c054020713200103031102c90140420b9a10742043e07105400e4945450700402c014003003c4240da6000f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 961622041 1250 961620791 961620841
    0xe0a03090b0304050a05030c030a1b02060319110705060612010615030c021504030210060b0922020d09120806010e0d060216050d022a03060f092b08060405 68
    0x94843e4a80365103400342620009100b8013020400c119040c0c800000b60030403c0c119030720b00761200d2200207039071000d526010000c0e400a0003040028203140042106c0314542d0141080010102030304881908660000d15044803c0e07002501445402c0c034040302c0c0b002c102044c05000700036452411400c0410718400700060420b041d02d581003113207100d0003802619a1081c4044200c1f0a03480c03d40340081d00e0f48100e0f460214120306e80310b030105c1c4c1c00901c0001d0744e0302400c007d071034030382c0c8407069000040b00000204000e502c019005c000000d024142c80c012408180c0c825841285401d21110000d01581d50017840341c1d04100500700c18520940c0e410302d02071040742e0080c900594a441c100c29040340c0e5042c900d8043c100e44580584880f02c5940043c0420b0040310000464040d8846420340d0b44c050703101e07034002a41c1a4405c0700414240950280344130f41142d500c100301c03509240070120b4200d0105060a990090041c00001c481d4172640000d00c071540300e40221400c200c0d0346001c0c0d0304a440489030f18010040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 961623291 1250 961622041 961622047
    0x80a0f14090913060e01110325020304090e16030c0329060409051c052a031207020313030803070816231c020405280509132003010e0a03090b 62
    0x6010a5a1181c24091740280c000d0001403080c0940444651040e1150764007100340c8030b142440040d000748400052112135019601d040c3c50b028803a00609108134116420340245040c0440c1c00040404000c0250f204440341c420061a509040c0b00822032032680021030080041d0340441d00302d002074003503800901242cac006001d088a0402c9868018480c1c000030310f2003070354540c080000d0380240207001d034550304101c802a1025198121a48010001000100c9074401c3c0080c0020844039804d49600030b0713039481143c1c1442843c0e912000b03d40100d038410b1f90182c0d000407d001c48a584607089503401400600c0c0c1099105415400800520003401c408080ca0114032203903c503803459070100e40c0752400040341544003440d440c400c44020340c882d03c10039218111000340000c015640050260340c03010307405440c201c031740e180c2024003688a000070172b15000303215541c000000003103882d4144040d0160a019034014400f4460605085900300d4041000c107600015450380001c3d40280440281c4049400f1075407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 961624541 1250 961623291 961623293
    0x170712060e010f1a310213031a01060305060d06270c050a1521180b160e060703121404050607080609040b010608090a080a0f14090913 59
    0x402031050120001c0254200304080910320b845800101d0f003003180340030001c1003408190800c01c0720346442c82c650b448509042c003140c001a644100704841d00380340d03880c050701e4030021200b031007203442d02034004560410744c6021800d0700c0c5034041052400760016040421250810a00141c400d8490b1080107000e641c9507005d1070300c030401c112002e6403c00799075841906000c100e4946103607081c03094064540516000b031000580d80401002c1e00402c03591a4030b565103091035940c810079106244022040c0c4458039204880a44003070142104003040c040c02d180a8603060500380e07100b0940729100c80340300b007000101400702c041d074824040b2030020b5818100b50000c101d0401402d00076080b01e2014010351080c0404000611102088661041c80c85a48a2540d995114200311401c0300944c0e01400303800351003006100c028020001242c01c8a408000c5482426090307850f8000c6a109c18018000100c0c11422904000e4201e0321f0540c603641e01d151114280100b5802092403210020b01007410b0700c260f694994 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 961625791 1250 961624541 961624553
    0x601050f0a181701110f09013903170709050d0213020f04051507051e0f12040503010b240a180902070b070f020d0e030f190507170712 59
    0x1448440210352070540c241c2d070350903c4016060810355008055400d0200080ca0b045002040301c103501038000105050200c4036004548038404503903d032201c03555120210300a01c21000f1244200b10b5502095501c2400314070300205a03200c0985c08401b40c4d061342d0305001a03e60021410800c1e03602c1540c43d20384054040c00003510f0b100c824505405960320008082440507501801441600d005071901c6083c1407180500300c00350310903580d0142140d00400c00c0c0800a403219000003070501060130844080d90442c07050340c0d00740400c0300b0300840e1903240001d007080542820700a6000c2100c04444000240c07800d4090094001e50b00742498507000340004520492074001c0448034002c140c10701158010300d80b280209002540060011f0b0741e6080324100148146100d407a400c001c0c1007181d0b0180102000e1148142c6540b00d840c450386905008040441049400800000c3c00c5194a2100500c510480b41011410302c0030075040201d100140400c0568000790019282c1e04540070f9491b888845c4038242060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 961627041 1250 961625791 961625807
    0xc05101a06070c03032c100504080f0a0302010e07030503030f131a04060f3c02070302060610021c14070803041a0f01051e1c0c08150601050f0a 63
    0x19402070020500500340700c8400480b509881c440c2d224900303071001c0703800088004001131100d400d096007242c540c2042030910040e0603101f4181d5090080c100b50f100c0746040e092500c6a540203103154040000d44081c5682406040c400f800441c01814525085484490b01c03407000500d18101c0001d44008540b2002142c8140ba0103240c000850146d07101e41c10080300300c21141a00c05039001030420300550303082c0c0e840384110070b4843c150018a5402140c1d43c4401c1001c0074030301c49817600c074015400800750842814001050000d100750701618079032812008201200542450920031580000020190718034000c4295626244a040c1402a1808081c09001c2445500c100a091040100a11003003040751210b10b110071402c42410541640d5a039003030f0100203803d100781a0f00061074400b20002d0b0802104640050300d01a00f6280b0361034568a11403217040c1c003d00304031070941109004020f100c0003408500a101c000700041e49450600400081c818011320140b00078014000500c0b014881c002d03980 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 961628291 1250 961627041 961627091
    0x71e020a060507060c03050c040501030b04062115230903040807061d0312040603020904060807080c030f06040203060601050d020c061501020d0503060307030605061809100c0c0510 79
    0x60900c80e41d0719107000034040d421a401c103c55481c01c000e017255882d802801440c0c42400541e112908152500004402408403602069040b90769010007003042c0d0508480c6800d102a454084840c1034510300e00310610b6804540419180c61070540300e8004110b4201c42d0f407001801c6603011240685848002c01d003903215030740c0b02c952984105130340010030035040640d0061384000f980ba00b202c884064002d140d00c0c1c9004202902c000001000b091003814000d6001d00450312021313000094107a10b41004500d0803095400581169000301c000084a140400c65207802ca100320000d80464100366001c69940e5401034032581c1400030200794411302c0c0c091903064620010140c4110f62840c10503411801c14544100c46190050061109102960b8050811a4040e00b0040c008100741403031602c2e100018100544640e03400446400800c88000c0030095080c01039076600d0151040c1130066160754219107031951940305200001d40200301085003c92400d00450841d4804103180b00d0540c0c0e800300c1c880036000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 961629541 1250 961628291 961628299
    0x203091002070f0c14030d0809030c030c031207140708070204090203101a030d02070905040f020603160e270702280203071403100902030c220507050f071e02 69
    0x81c103071043c016040b0103ca5581c1c01081c40a00441e15460800c0300340c1c014058068041c0c0c08441c52005152285680e282c0c401c0070345054a041000401ca0142186d0214010415551012400307806042041002c15040b603c3c60506140c07850b24080c4002050160150160418a021440d03400b5900c0b01e03080038000d59030040503554080e00c85611038001b00300181401d412001130f0040c1c203059003000502d821074440150000d101c0345107811010700c0035042c001d000701c0e079400090172184016240c2601844c0179030354140005540c0009448028401e100d00310000b485841401203107140d402100c10700c1c210604001128807140d907a400420387c0b5140a810030b00d80c400117050700c04034200340c82440c0401414030031415074145030f640f081c1c001d814020f107550a90780364004800c070451103a401d500c540d41451003d400d9528811802d030025001980205070034080320920003602c2c0048440d80b2550b41d0200c2d041c2805400c04a5041700c0c0d45460068141c002d21050303c41002c1500c843c0c00b5403c4040c4594010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 961630791 1250 961629541 961629547
    0x60203040305041d0a0c020d1b0206160302030d0b0307061d0415180b04091703280606030b031621060e0f06010f0509040822141212030105040203091002 67
    0xd0a80c0c44151310443c0c04062180c40c4c154a4014140b021890700356001059035052030800f00b0910b05030840000c18802c0307a01c031808100c02c05a40030000700e003128250081d005151600f6080b0030340c600340c40a0680380362003604844800c1c0501c0340c000044003051216051003022000783c0b0360208008002208821011010130352000072904004625141d100c03030054424005e82c8022002c0c001560032003072008100c4600d80030300b80320b0210303498065a0310445101c003201d6003198809030800684240390380310a07810303100d0800b0b1002503014006c094100754250018442004031950000001e1990700646038107d01c14001000441c2059007220070b815009241044058a8008515a90000513400444501401c400010416010544002145c4018048410546da96503806d04158000b03002d0900000009101c0744002d680321410401030301e00218104940710101c0f042020b051851030006905510030061001f440c5001021780781140d2080d54003503140d80780c0c04035143c10441f42d00d080f00c281e82d1003c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 961632041 1250 961630791 961630829
    0x1142a010519020403020a12051006241e0e030705040203090c09010e040506060f040f0923030c2a100903260702010f180b0c01240306020304030504 65
    0x19405140140e44440c07602030140441c40342d010036405144006544160203090400c00d1090b1211042c400511803400e441c8107043c07003500c1c0b0080321b0781500400c410030f00444040c01d4454140005884030003c900713204e10244605058103514007129078454042141035840d1401c103440421021002d01001031040d0349901e49a03400c241d03034019802050f40f007403100030300001d801c0790306032550350242d0380090260020760b031040b090110010f6540000390300301e6503800140f0383d070040c40d00c951420f01d48154001d0440e554112112414250f6100350f9127142d40080004112a01c0c1c00141440316030b84e280b0264808440100103924804c824208880d00081c0440d01045402d034450254000c1d42c6c030070b08600900644100e409103800c40200e058080704801007110340d01640c010740084a4400151a0400c2450012400a50712003243d900c0b6209640e030200300305480400170b0050403000040420b9441c4503401d140c2401490b0071052201414080d40003020805051241049070042c00400d52518904811 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 961633291 1250 961632041 961632043
    0xc0b06121603081801030c0801090203190e030d0b040218090a0e071e0609060804080304140d02100f0b0a05100504050d08190807050409020d0e011119090501142a 71
    0x8a60013205100c207452258000641c064030400f07510b40803035030300c0c41c0c0640e0910404030001c1d030000e012043c04140214801c10280128040c04000d0540c0401450311660054070ba001591008a0380c244107a005214142c0340500750010313100600012601c401240d02c9455480c401001c041300921841e002e0720700c000c6143e03070b40300d48041d140e440c440da002e22020b80d607814200e90900d40b60207158006840e0303c1c041004501120b0145400c50702401c542150003004034126454410070005000258102c1d181c085403160301c9110701c202c2100c40031024000c04180600088040c1c43e0350045c20b01c02c0d140c3c0004821854480c0f01903030050034019229050600d0319040c00c0143e90005020941605503a140406055121316400f50261516445180c113240c24110000041c0d00141e8084010b9641c800000904c4542402a0a903c1d0000462181d03608448400901008041850380040c80100300003008241d038040040707a030000c1c00d4001591164032900455401a05600c43d800e81070990122400c0c040324 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 961634541 1250 961633291 961633297
    0xc02100917010603050c010c11030610170c0f060a272d090209030a0816060c0203040b09060304020f19080d030c0c14010b0d0c0305010c0c0b0612160308 67
    0x190107518000c1c5000340c0001030342660b95601005203a50000d0340c0c00741055004910018101d8400d1425403401880f4501003490b00388211142c1c1861820000108410101e5884620340060104094158454074101140c405c812000c051801079130001a4616024401c42d0400460303006540004604020328a040401411318003460748480050728109144c205440c41d5580c80d070b20652088252a45403039903400080d00821405034040c0103503127600002030640d10041000298504102030041482d09194081328032040c2c58400355803007000280310050f0304105680c1d01c0c1c0011600d01e540c0355558030100c1d26030a8103580098100e00040e482d0100c903280c1d503003140e00361845078084031a000c940c64030480c00e035201019020040780b042c3c0141c80200399640d80244034200c40e2400840c400d0b1222000c2205881c0b0700700c0c02d4690040780c41d42841008800e0044200c2d04d1000d1a040706900e1281e12011350100020704207034400d61040441042c416818003066045807080401c2140007992800c2c0321100740c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 961635791 1250 961634541 961634549
    0x90105090705192303130b1f080115050307030201050f13210302010e070501050d050c12090715170f070903020310020a0206010b040b0708030901090503040609060206072d0c021009 79
    0x4641281c0a504e51001c0302543e2081001c0c424060385201207485903102480d0151104421000104100139054600d0110400504d201c50000030002c01d54800326112a9071030b0446403194001c64003c00241c0e80c01030644040c025000d240c0360355132041a18500340c1600e580e00640c40b01622400c07680e042c2d5161842c2c1c0070245d000343c00900c042d118400f10180c442815003d11800f1403014080c0068110040d0300c41c96001d1101045a450840310485106105000b01d0311809694012201400781103020034114030b038aa880c2c00c0240040c0540b001001001000a0603400d0000c1c420000900d0580700da8109001140c02400340c82c441c84840810001070f5000c031183d0005445084000140070101070120750413030764800003143c140348080c2d54656041e84040c040b2400e039921000d030384000c2030090000308010a0144c6035100154904407004e0f0070110000e14000601c40c002d0407480d03d101341c52038010100c1240c40b0a000d04480d1000c42595000311461010307401182c1405009102078215030a40196 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 961637041 1250 961635791 961635827
    0xd110a0305060307180b03250501090f05010504030f0f0614090111120423120d060b2823030403090e04051c1101020c0601050f0102030909010509070519 67
    0x240d03210b00900d5600c245501c01c0c940741801000c600840501e15500a00c96158010280c03000c24a00042c8a50148a030f20110300340030305007850030040c5680020b440307401010042c038a04032562400001805d035002e01d00c00a0302030200c803051302d0200940c0d05054060750358071841c200401940140074607003041003111051504d43c80c141d0201076841c12081501c01081100c82503030b40580d6a941c1d8000a036081c0ba120808807910112483c0c1080000d01c0541c603d40780701002161150a200140810780b4a140d1200c1c000c0c40081110010101020b41c008074800c0c00840310700d0290400d0b480031109564090310035040707007212149007208866803d000394000e502036612207401548822190400b03401c16100104640c2c040390032000000040c007004c00d0092101d08016445814070224036007a40d00200726003c89400c08001802545803500850f211401c0a02c001c2d03044c4040a0049441510180500c511170f180b103c0001d00054130841c200d40440c010140c14889400404034050804404900d0b48664 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 961638291 1250 961637041 961637051
    0xf12011a0c071814130b07090602031b12071514060a170a02060c03070507080309100305090a14030c010b0108131112010c0903110301050403051e0d110a03 68
    0x280006030426034403000c007a0805803288074a02410640070b00031000c141a00c19445001d0041c08030044070b4860311401d50702440b0b0031042d540d49060084d02000030282000e00c20031100c103004a40d0700106845170341c060b00f01040705000080e54500c1c0351040e0154114030040d00000d454041003440030414140c0d001c2c44400384444413601d510710701d002d1011036420707402141400d402c000d806400c9820841c401510380135602e03c1181d503000b0a60580c03010070740400c107500016980d401c201c0c0421014009000180c040c3d41401d00071380028080f87c24400d20501050784070390206507080014009039007283c1e4402c4180d80360005900f20705071a5000034010b845035500c0d01d1200030785035019520303451040a00d529a11910311141d62a4958080307940706c0141c010509580c014203620b004d10403640d100800742c0f2030310400e0340385d8682030719003c032070b200301c1c0d4081d074181000d1200187e000020b8031403a001000000041003614801240c05000b600100c0e84c07402c2c1450700c280c20a00c8600001c08010010f03a0301402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 961639541 1250 961638291 961638329
    0x6060d06050a2c0601020c13020706290906010f0c0302010b060c0106061704111203090a0e010f090209030a0605060d06050a0501150c0f02010f1709010b010f020d09030b0601050f1201 80
    0x3c00501c084a107203015801004945040f46011004030018800da21401410048185c54201c110384003620a40c40c0500c0b08081d0780c6111140305944201030350112014001c0e4903100c030000b011030701d0300e1100f131082c0000200080d003014001e400c01c0c03030302410251496031034000c042e8036603018026502c01d0001040c2c15078030902c0a941e900d180305c2c0c23041d5000b0f020306150500000c10310108400c1e4001e10000da000230700101c1e001d82d56074a00700001740041c8011403400d50406410200082150f44082c0b1700314410000550f00352030100340c9031413980e08490002220f54030b040115040143d0301a00500c07a601d001d0070814410b0b160b070f0040d81601d055100700743c8500c19080040e600b408070301e01c018000c070084890140040d84285140c0301031500b24503040c1c2240e80d14081c0301500c603406844281c0182d440e14040c108030350748201e038005410507502c02070042801c52a40903190a03014000642aa0301020001c0d0841c0d0084007210300c01c01020000c02c1e0b031400e00c2409400c03104e2003070041408100013204408 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 961640791 1250 961639541 961639619
    0x1606050a090212060f010b030c090d1208090c0a1503060b1210140d0b0709081203061009030b18150f180106151805030a03080a060503010c0806060d06050a 68
    0x51080e2217906a40406900702a014803181c0c0008040040e102000c12210300140c444004400290b8480c04480c001092100c202600c1e440c1c008080c802c2541c000d081000d011fa4850764030720210b8400807120f45403114072202c11400707840315400440701380341d002032400300d00c0000c00c0743d01e03214101001340c03c0078a49c1c80d00050380010002610099014003008071308000f0a41e5200c0803900140e060078580e2400355920109070030704840c039000c440c51600210801c4090b08002c001c000e6115400d01c3c080e80000e003565698a03a00780054207a001c540909078021000c0c2e5801c002c001481130891031117590a140c40611940710020841e02070700e11031210340c1117424089050041d81c0942d4a01a1805040114154125403035140a1004103000003100e00004840e2001d1001c20203803400307951540d041d880d25410580c00d6518540c07155010740c1c5002c00720303034400d940441e207540c103e0021034aa5560b000d01041d550003908245c0c020a0703000c2c071032120001d80741110301c082030390a0b5011006441700803810980c1c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 961642041 1250 961640791 961640803
    0x40203070c08030a090b18060c0c0d0c110a030602030405011a030c0d0201350c09010c080306040e1c14090901120203030f1c060801021602061606050a090212 69
    0xa404980407114010004035035030081c40e481a200070001403c180e03d40c40d200c0c1d1309002030b988541c071100c591255449624061240c0707076006114403500e502d080718800b00076580e03c0c0441302401c2008054030081c8100030700c2c0300000800041c0201a445442d07200c0c10140003c5d401924211810740c40e041c403c801c2c41820001c84e02c40c1c0c0c82d005004c1d21008c0c0086040c005214011142213040000030010714902e40c141c1905118800e13495040e811024a0040541007103460142101c0d08a08007800a1902a0b07400192080d17255440b0010b142c99848500105001e4a0092042900c50107044421005d01c400003050310b5180e04240e0b9004001a200000e200039846040c1c40c1c0d0360071122800050140104894891880503c0501200d28001d031021a05005400101c00303140f20b06910456203050b021280520005003800a0003145007140321540e00d4540050408024029800800e11081124101e00700c00034084d0050401d120380e00d0102a6a0024018410101d2186004c1001c601080b40300107a1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 961643291 1250 961642041 961642051
    0x3032724090a030c0b070c05030309030702011b0b072a2d02030604080306060c03180a050907121a0a09060e0109020705190609140a0218191109040c1d040203 69
    0x1132a5600e00e2a480b00580c4003002428001405102c0d01d0301000282c041000303500c21003400b000342d902d841303d40c40018000e2240c400480c041102c001414800305029200881c0c03c0b8034142400c480542c1244c080c2c0c00202c00c034001f2a0f602c050f03002c820109005072000c41420304075035002c681c0c0f4030754004e03001409042c01240b00030b0f4166102c4000240040c40003c021340d003140004100310304085600b403c4038555840b103c4107100401b18480a1500c6051954021018000448100b28940b4000310010100082111004100c6032110028464116918003102200d00042c2107400a5500c031040c0c3c0002d0005481502f03c1300302020000550320049109a88110b176004000c0d0441207045000030a100c03070640e0069414903a41e0390001d000880b59809145556404c401030300700841c2da0300401403042100c40f0305081d14110300003000500d403031000540c100c0c1d030041080000d512651000d024042e019000090f07411504d403440c0449c4c25074000c40d00911400680c0104000c0d000002c080c40140c0c007066070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 961644541 1250 961643291 961643297
    0xc0d0807111e1905090108301210050402030a060f09020702030a02150c014107050c070e0906100f0506040603110c0604030818010501030503032724090a03 68
    0x614030f890301908084008035a01e542043e034984407800140d50031400ea12496156000d202c0c80c0050300e0031031585001d07180d42c8066082983d4000c2041c0e078046c0c4101c8801b951440c1d051400180c0300c07210014048040c00000c6c10864680c0340c25400000240307458060140c04131542d1000003003030641030084408180d4003030040c2c580b0028541c24050640350300012800e01c103609100362000c80a0034400c6000c0c0105656140d04200c0b0070742145081e5046000a441c01e58540c1c408917952091f0030340d40150045030078501290342d0f04000f5516410008103400a01c0410412000d100c1054800102e0714041c817555440b4444140e0f490380100ea400205114094110a007440200700701400f903030080c240c4940c0d8000040c507015001c11181e080100442c0d040700842d00c40302c1400312045610814141c03081da020000c001c9541103865069580c0802441d47d2800303405070160400c40c1e0504541c0114102c11001126121515440e0314a2074209441c0e0807082e0f80d607182c0c0010300710a800611001d0b9a07030552 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 961645791 1250 961644541 961644589
    0x405010507230d0b030316061a06092b0209040b010608130b010b0706060e19050a060609140102010e0d023a0c1b09090209090601061209050c0d080711 66
    0x50200e83c0501010f0842a9040c0810b01a011104c00d4140001c0c800c00e02c14100002c2111001c01d0780c140307140d051001c25000ea0014040703442d160311018400c2e00c0d807030494001100c150340c581c020101d11080903880290444d1642c0240706c00c0108607440d640c140d51840d16000d84030340d141000d071104803c0c661005007070801494010018514080010028a8010f14001c01c2064442c3c28155040c3e10640d261580c2412065030798040010070320601d60031030520081404014a0300d2001806090340f402408a00318456401c10040d03070003548049105084c0c681554141c09800c00c0107521440c19442c0010a80100d0901c075000040b24407140d03814860410540921009200049030185540c050071164900e000c01300c00600c0d9412000d02c401000c2c3c40c440420018000d1040c0540350f04058800c01203030f0311070780c018480c498101d00e0365044441084400201040c941c14640d1401c280c00c0a03c41e00304040d520400c043c00f842070010154140a8801c1e810400d0038481481025248c042e04019580420 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 961647041 1250 961645791 961645807
    0x8040e09060c03041220032d070206280504061e140703170c041701180308041b030b270c130e010e0106031202070303050313030302070b040501050723 66
    0x42650700d40c0e45182c030310340701c8502000008980700fa03c1101c0e0b46e050507a0b1010a00310220100c41e0f0a00b14080000b0544240320100c460041009008810000f44a0400403075002221843c05840021942c00802015030705140802c025190303070b110340200d00006105041003c0e0324403424200701025003c03940d907400c5901d4410b40080c05a04034110072820061340c01d00c940c4141d0104105c0178010644820090394540c40e01c2820300407122040c09404141c2d0600340c0c85040692030240c482c021540504001c15141d85600d8905800403400342c0c4040341b00a54117000c030900401101191080c01603141c4100a0700b00364401900301051000b4000301980140c7e03842e180c07800c18000c11140d82c2042c081c08200d4a02c02c6c2001402e45212004000007a9520a02082800f2102246001110103400904441419500c0050841c40006c1600040d03402000425080600c82d60403503410540000c0410181e04040c41c0c0306010f0503060350600001507103c03103001800d50780700c0d411640091038050800e20700385003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 961648291 1250 961647041 961647053
    0x302040207140a05060603190b010501110304120f0201030b03011406011b060e030924091504080105180601062a0c0e1816083708040e09060c0304 64
    0x540c0c01150311084a02d2440b0301c20308100482e114403849030014001d185072203014149424080c0100213403007500350000c000400e00295407607065a00070320f014003441003420f014510754807030780d0303c0b4205007020301036404180715009004240040c401d0740c0900c0941050340803d07003603840c3c201e500d280c40c0c030042d40407551b19800340d1011254800c1c42e4000010204541e114a4100c0d5800300004d0f08940000441c078083c1d1426582d01c441115800f000344400d95840004a02c0324003c030811517010f810f040420b4848031003035006840040055000a000d5407038060514203196030000c400004504c40c030030022524502500c803e01030f0400110b03900c014540c2003490b0400410300c1c2d620681d0b44400001002c01c140c03440d001114450000303e074044017000d408000480c84c00c00c40d0035152840014044050040c0403010510003800070b450b221050110310000b2404071401c20072817a00d10381b50442d0481d00100010100a4002c0310020916111079070348140c4403984440c4215210402494200000307000905 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 961649541 1250 961648291 961648297
    0x209180709060b090910080f0307060f1514040213140f0604060c0b1f171b0d200a12051002130e090309040203040c051905011e110312190203060a03020402 68
    0x18118040e20141f95908400b5040c010521081d41144e000015080244070150040c094400019001041840100704440749000110300614400400510000820341c1e070b81d80540e6821a07a800380d24504039035806a40c1929100980c109006a944a00300c41e1030b45400d13810340e03003152441e8448026000c010f580e14500400d00500c0c05d90303a102e11600e201400340c00e80144c803024100e406940160748800441407442c20001c03500d12400d2500d0301c0626103154039030a204c6204070390300c43d0030408014840e61400c048688a04170389900030360b0450000480700c560a524003007860050303080d510840b1307048072510144d00c03818800c00e1141d209c0c04810401103222a00d0700368403080440640b41410030345000501a0f0b4801d4405451000b80c044040c0194503003d041c5220f03095000da00c03540d100f071034400040d200e50402903100c02c0000f0a041c1c0e82444c01d0140000c00001080390042c2c80d9114501c1440307800d129002c1d510755880d04e84140c002c940c5a00707284204d0380506002420701c6001e620f55800c100182d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 961650791 1250 961649541 961649551
    0x6072d090e01060f11241504050903130b030c04030f1b06030506040c051912150f0905100b1215090a0917090609040902010c0209180709060b0909 64
    0x84240320001d01408a058414082c1c00030360340d40c402a0641340360041140c00000007003806a048003020b81d0001185065032026084a420304049965803100c0c3d801041508000564125080908000e04810040001c140300a41201102920b60329004908180d0004480600d0310190811040c4080341000d205074401520901030011502ca12181c20b41d400c02e203a611080100303032985c00b80720349407601c0d01400400080710301e172a03030401141f0381c6800301440f0200244014403195050003a45502c181c2c00210403101116560340c2c2041e502d84034009981030901c0b510380700300c0c03920707010603103c98400c641c1400700c51400c901582018090001d180411802400300b94090060640d10f0401d500c0340d041f210302c0782c5d011610000307040e819801c06d642c0c081c10701454180d000c1010000c61840e1742c2c600080e0343e00c6400c1581c001403403074400c0c801039940000302100139511140101c1002a03120100d400d10b00e00340c80d000c2c22340d041d056451140c031040d600503004030010a0000c0c0b110190b1070420b100e90507884 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 961652041 1250 961650791 961650797
    0x20301020f040902040f0504142e1d0708070c06022107020d12021e0d060909150e070605030406050910060f050f0d1a0403180e040506072d 61
    0x212000c9101c1c01015405540b121050540100b001c1100341e00c07440940d40245030a44041c012401c42e0312100c402004010f103510a801107103503003840d00d40741c90b840d08188020380740d1080400c0b40e112401c08054000080030100c61001ca1000903003031522440c10103000e4541501d406c10b20307140982e0303500c0103500701c00b001e0102e2030004981c3d00c903000181c4140c18003030f1105402070800c02809040042078104110ba81031a4507004006c41c01d078011520030603a0600169414040e1907001034081003014110b00c0c2c0c0700103440f60520b11280d060201050455400c0707241003408100c00c0030b0994007151100f205201d9440414400d00000380411456084180c0c41100c0380103489400030209820300464080b5001003c0400e0a010184024200b803800200c05000407142070700556502d031f64211400c1021070360035400c50a501c0110f81054011501d03800311340d2002c10440012074a81d02c40d20300d020030850742903859101d250046441e440c0515030b20106c2201c0c205800400030420030780c0712660345c540e204100070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 961653291 1250 961652041 961652047
    0x9011e020a0501060f1e24030f14010509070831050723010201110a050a170a05070e1c030e06090a182004060305100801050403031d0d02150402030102 66
    0x802c00e00c9260301070b24140c2c0c1041c2485041c00c0c074544440c2c1c0c00b9038440b641c12004000500804581c10788400c8011003000e03071050b0507404110304502030450b180c0300f070340716604111011180c07180150713011381070b01c2d815100e40b40b06d41d640d110121500300341039441c100c1c01009001120400e03a0307032030580c0003441c409491580c462041a40d601d840c001c4241c1c4100008200980c1500b024401700d07201407440c400c248024420064000100c01d0396118514200c410700000181e16000140a038030300301e517076001070b19074402c80d440c2140040b40035180845407000010500c064012440c42c3c0032102d140b0011103a03181c00c0030010aa941920599041d50071180e00401c180030100035a40d42410350b00c0500600304c001c4821035164030711070040c0c2d5070382240382085030780fa8038000458a00800640d421206c2c186400308180e19011344604051075141c001035165400c0c41c081100341501a0407002a01c842080a00460454940103079151841e250310800107030810400b80f81c0e55205080b4442c1c10a00041c00145 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 961654541 1250 961653291 961653293
    0x2070b01080309010f082a0403232a090a150603061a032403010b100309061d03030406050c04030c0b07031409100503041103070e04150c0e0103050405070302060c0a110609011e020a 79
    0x70055a1020601e8ac10010600414000001406100c580408d00440c0c0084118018000b0280c0340c880c03401daa000d401180300080351442190400d0001018a0003c5ca1070282c0b140401409040785009a000050b0508607030424401c10030f08030381c4a04a1780e10144400718680c290f4513900441e6060507039146d901c401c410314280e0f07640100c284100845440024000c401391520000355464400b484c2020000e5448001c2011004012280e1040e8490400501035842400070780703a0307000b00d80002c0c00440120002080c2c1410b4030008181d00c40c006c6d140c0481510540000d00d40510400c01c40e01c3e0020f41e0744c1c1b08503a2450043d405141c100c1c0c407808260303482c418400701003860825990700210320300c2c95038410302040c0030b01c50266035508591018240f03c10a1807410280c008154070030b1550400d5039803000102031200c28402c1102842c0d0062940d6a94030040d0074403541e90013012002e9440d038108400701c240c00e1900328200c030714004c01130711041322201e1920a204500c0b91326901c1c6c4019030060b141220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 961655791 1250 961654541 961654553
    0x102070810090c05030a030c02010f170a0603030e090c0a051e13031511160f050d030519090c03060504240c080903070f08030a02070b01080309010f082a0403 69
    0x1681e00306545000150001181011404620184c0c005406500a840c0e0700021981c81040311541c26020300703000242284030340c1e0031034041d211a80340014403603800d4240040f80007650095070072207000b9520b40c0010b0f54a0420003c01080075140c10018400030003140071181c2c043c0010b412652004004400300100b01200107005034440c004c2c3e101902d40141d0140104495540301d46010340c90800c0030001d8180c100300704c1c50548103e1441c00d112500d0b0800820030040116511601c0961010075030320300c0201c1d110007401808003914012100007503103503050802c100d54803403030282c01c0d0880c00c085245440c43e02d800d801020083c005540c0000300b10708101891030b540300c14414104120720009101d140c410700c02000036a0141801000307801c10080e210119011241c01c041007a007002040b95603465640055009209520300200344016280000078401d101001070180c1d24000e880d9103212a07804001125101d8040310450781032615420b440c041012951401da21500c0c0301152103107055240d4480c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 961657041 1250 961655791 961655803
    0x3180405060f1504080f150f10050409060e01020d0504121b0b060f330c0c010e01031b020708061f0627081029271603050108030405010e0d0201020708 66
    0x2c0074850707211800940701100b624215581c0540101440320b512704140c1c661001c400b815110341c611443d120844141400000d50001d105212101e0085589000d40344c0b4a0000e0842101c0c1600d110903500329004200c1d00816002005800c0208a440c042d0090380e41e0444480e0040c04503500056850240f000c0d5450305802840078450b00c000401c0500c88220b1003624103011803080840c083d00903c04201182000101f101c81040d090810814440552004800078131600c00780f80c110038807040304048503a4004c81c200040daa014030a44d1030a0381c1e1030300c90260407c1c9000c0e800c44400c202d07c900b000883e10683d5442081150030030300910040640b0300c00c5401c0c645a4200710b00941011038005c0c0d00482500c01d0b0601a890100c4809206100f41181803840e010990240c2c002d00411000c2440c42428903e561909407402c882d40b040d40c1041030440b035401504107040400301c0c0c644030000c034081e41c002003982d00f2107170143c0d107601402244406004c40c1150348a4202d0561140c04004a40d080c0c0c05e01030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 961658291 1250 961657041 961657063
    0x171305070f0e1501142124100504120c0b21240f0d0605040b1b0c0601120201030e120a030b040504051e1e03180405060f150408 56
    0x40c0d40107003002c001c85400a4040c040c105044540280c06103166080750860381051200d036180341e1030b01c2800c80070700c0c0000800c502070780e82241440f017040307415420181c005504503c2c041d041c002148881e818131a50b40e40c13682c146404580140f00400941e1600c8031040b010701e00c1912582c03900d564400d480b0f2510782003d040320203110b207070101c142d10003614011440d0303020b1040e01c044c000c1390140c4000c5668000340850301c036010300f44236003480c042a210b0824503140310b070b8070040401141c43c0c2410040e030f100c1401c4c0e03912045046460034046410310f0308400c0d181d031601c1080140c403880c0d10340300c800007039151582012814141c5408160300d0016040c44070301250709506102c02da071000300c60001000c80d8400c880c2c25106601c1c10042c400815000101d00f110241c0c1c14803070901072450801507526004150091242542c0c000303000101e41400400900100000c1035014000000e44004100654004a8085030000e0048116045514082c86c40b005420003070a000c0d440c1c0b036101c00d5600c1c04d000d0542c40e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 961659541 1250 961658291 961658309
    0x1090b120402090c16060b120712020f0904050705040902011202071b091103060402030a0e070b0403020405240d14011401080f0c0123040e010617090d17130507 70
    0x108000c00d60500b10310f20740d4400840d155403803030001982401959805100c2d8050080d070f03501c040c100000d1302d0703c034100c40c000c0d03110008440115684180c00540400d0040741280a0707054140071440505001c0031032801568090080c00c60305040034103200041440e01003e80c108052500f00704600e40e1584010024240103850714200003414201c038200c40c521550152802914240e50842c4000408e01a6074000904030303030140c3c2e00c0e180c0c007034040c3c050962400c003420b0324021102c0003e18001c10900401c11a4801d40d001e20196841c1c241348079411a000c056480d245c140030000c541685040d40c01403000c240700303030722200d82c99000000302c0e0308640c40c00c40c565160349002801032004000400020100e20007920041c200c60b80300f40002800640340400036802c4003903400036a04880c04030404e07680a445880c0003a00075694440c2c0007400b8580c1d403e0522141042400410620940880c0032511005540ca807801420702c1c056200143c840300811a8002000000428000510500c406070081801003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 961660791 1250 961659541 961659577
    0x140a17011103040b070927110d050c030a06050607120320130806060f011e1e0c03031404121404080609030a09060207060212030403020319030f0c030b091501090b 71
    0x51805401400603400815148650341f20b05000b05810a0703201c9588600200e02054a01c0b145a100301240600318040091504160400800310288806903104140c1100c09205240e0b4800503c010b034490920040e010078512950b03c020180681c000120344001480d4150074420400c104580c80d4001ca0000c00b40c1d20300c410803c029032001045a0b64000c2c00899614a03145088000038148070b0340c0740c00c41d50342d0b041d0f0a902e01910074010000803084090100c43c034520a0b4545030010411042000210086454a0100c00b0340000c20001c04c1d201d0341c1c0c060807181a13245c100300155010850900c0641401c1070030400881c21100620920b40212501c0c4000e6840d1a8113240c0603180f0500d0ba046030003154005e0000b04803e076030014407030200c281044130340b9949841e0b50400f00e04503c42c1060300c8038101c070032420074091164168070000d060300a6030810014240c40302e00c120709031a82480031940c841d81c00c1003c0341100e0640b1a511200007014180a000343d642d50080c4513080e00800e041c0c441a90040e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 961662041 1250 961660791 961660801
    0x1e030111160b1b0409053411010f060b04051f02060a180209090723012f070b03060a0e04020102150403030b0d08030907140a17011103040b 61
    0xd014905240d5a615240ca050551441d07040090034000540944082c495801148810011461850707501d0040100b4607038840d11628403101030706003030320540804065100f100c1315145900b4040c1c004841c01891b10904002000c204a440c406000844001c6550750500d4808085091042d00b00800076000c1c01c0f91554508030811824224144580c6116994404182c48240c0e0102e0201c0d4010380e401c03c000b8140074000502c0000c0041010001d42009112050140e0040c3c0004c41004030340b86021001104d2141c05000500d48198004c00340c01304032030318011140052040d2440e042c0b108541d1346207031210f4400c40c105180440030751000000003800014000c440c00e1508201d000b4059021500000d03040a60000356600c1c1000d0111041843e4807021074201031198001c8061b051700141009914043c50034900034652040c0c070f80d06042d104001002451004d80e40c00348010040080101c10018902411600301140c002060803155607a00c044101c0c06400c50003640c019405045921514901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 961663291 1250 961662041 961662043
    0xb0c1006050303072d0c031a06040b01021518030f0a1103031006030203041b080102090901120201080f07030b0a09090302210f0903030c01390f1b021e03 67
    0x140e0801e034000d400030032004011604020361526451080300d00c840e607500ca10ba400e60b588103443ea82c0105072046007403002080c0205c0f001100710802958112002540b511010042150356040c90940981c2001d8621503854041000903640540c24031711900080c130340324054509503408030040c4049030602042c8141020703804015142200001c0d030007235185082585c9405104425407190004154000001404000244001d90f083d24041410409509e450f517212174080d4200c0440d940c041c0550200020710241241828665190107848007201c1d5200c02c0a404500d41c40144054145a2038a0380e12401d80c0703810204a00a05503580000f0f1101c0032464002c0c20450000341d0380721516900341c003a0b4540072101c0201e86140300c210188513076a82540f000b0a0650151491400c4217501c0e0080688090405041d1081d403c120360f00e6140c50300c0341000f00017103a103032801c813004001024003414401c880d0044c0e10032401c03071700c0c110658620800c0542c00200c4801c03403041001b407208219080180c540c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 961664541 1250 961663291 961663301
    0xf05030c01060f0f06021906140709092a08041a040803040303060e070e130b0418050c010903030e010c030e030a05100605010c0807060903091206091109070203180a0b0c10 75
    0x2a04013182d1403000c2c078080d80250307034103220780d0032440d5401c450300303c10704014050f40a503100c00f1b014a030105052800b100c000d0003080d000d06c00c0544141c204041c003451b1007a181c0000d41c030001e508094811181c400387c02200d10501c024802c9424518002c1d100401c07146444146100350701c50071101d82c0d28500b0346030007800d94081c0d51052045682d400244032030f041c1c210360384140f000400d403101180981903c6002c8041d01c44401a160080d283c032a10805001200090011b00c9000d003013183c0d02000c00c9401101d01c0c1d011840064009400340081380e640e588111003001da143e000e40b42c150b2584940c080000d080404046044030658400c3c0f05071504d5510318001c04c4000d0400b4241440c400c07400c0e4131030584a11480d10005c06141c1d4450b01c4138105401045100064484101c80c10350083d0f0918001e002094030300340684945500541a336080d150074041c480c41450341d58003842c00c010601d005030410300d00840900d58000381845000c103020341448087c2c02d81c02c000c000180360b404090840c03c42214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 961665791 1250 961664541 961664549
    0x71b0e04080711120c121f0e0106050a080a060e1c0305090c01080709050d05120406120b091b03060f04020d0c080c310803070818040501050a0b070f05030c01060f 71
    0x149139403000f40d80684000c144602c4d8134405846007024180d20032a11401c14800444490958540700382c10390410700950b000c15010030111b4000c1060307546840030021111030303e2041402e03603401703201543c00103042a04106410210030084500c0000c00310005690315540514040000766075904110315103000f003007400900c84080c2003601090418000040031007940d806900d00409181104104125040004a03200890400c1050300d84c1e80354540100308142c071a00501c1e241c1c1c05d10501503410b2030301d1039010b40a80c013100d0481c9055a004c400c80c12003500f0003007400313501800e26800d48031142c030b0314001860403481075400000e120680300c40203042e03068081c0c400c4070703c043c3c188000b0411040c0c200700c6400ba0307168900e2050001440381c07070540128265821100700e50202050400402080c50041c0030003a405812203005581110240012520244074490340208010000c0009000020041031651302070343c81c90002036040e8581b03034a9644586034441582c1c1d91400b041094003000400e940c090 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 961667041 1250 961665791 961665799
    0xd050f06030303130c03051e06070206060d0213330f03110f03120a0c0b090f070509070e1e03010b150441030d0c08071b0e04080711 58
    0x1410301a0100b40c0c0c1c2d000013842401d46081a207960000c1c494641280c000555000c03007260807402030f465191001030810440750840f8810040030607540c90011406501c80d01014050182c4d4426640030040042c8046126000c410b542d50064a00001c0d130404038040c1910005a280010000041c0002003071456880032902004003201171000405004400c03c07005001c4403a40d0b01a0540d80001c3d050075069680b1807154000003440c5030301e80c0e4202c00d411807824020030740203480c1e64803049400c0c3c842c0b0b0000403449142d00284011722441c40d010102907001012031030488c48510684021540400081c00714041e8052205400b03100c0e171800f4003d07110580d1090702c1c1c04c09102241991400f150250740610300b14070985100310005868801c80607406130840c90b007604070005021152445481d0a010b01c107020340901d0300701050340c0f40a282c204080c00d9008207620301d0600c0640302c800d58200d407110540c41d140c06000002440401005210340940c0c0110000740d900c00c43c41c03401d0005004070443d1103004d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 961668291 1250 961667041 961667071
    0xe011e021f0c020a2303070506160f080a20040b09040c090b0d0203151c0b0718031e02061b07050a140904022107080c0301060e1b1207050d05 62
    0x10140c1d000c81d0898070a075001c05e55054051320304412448039444400900e04a100c0030500d1424010300199081c01003442100c0c1801c1c0b9514060304031a1404000c0e603990219601001007684a4056809161458051401d100700c030b43d0b548140c5145a030041c0d0103042c0d54040810142020302e040c0c070450015030240d00b0614241c92034401c111000c1d008010020464681c044001b07035000e0940403002c1c08108000741210024940c4810440c1e01e1030b624002a190010b0500020710403d0040620141092007c0c3c41414450719603510705048111101007401001c0500d81c1c4000140c03034800140401c40704803090a81840d0080c0041441c1400503840070744a1070303503054108140d1225200d80d100a00b819150a40c0941c0d031400400d60ba0b408585000e4040d201410110040c2007010583c107041d10070174000d91369809803010800d0b0036038415005c0d50015188803400300301030b03203410311442084a81c041e030100e007010100006084050000c03103e00000c41c000191030f81c150780c02e610409a00500c400d43c4210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 961669541 1250 961668291 961668311
    0x5071b180609020313140709110301030b1605180d08040e01061805010c020405060d150204150c020916090801050a020409050a090b04030f05040503011a1f0804030e011e021f 76
    0x780310301d0090405000072906e0103101808880600c404406495110b800780100d628040304031f42143d1092005650140350301002c103c840348085011422841c13903940307440c00c242d03818180f02c01c0305001c207482ca41d200054110100024200c407000d840200b56000d000681585400006410500b0110005420075049a0f043c000c0341e030818100c890841d01506d000540e5070329213000c41d14844c10260094a200140d003074a104181c0030390020019690720068207001503030f55010648001c6030b45800254400d0108000902090030410404e1001c0490300d05440c141d55101d041e80e003110307800e6608105880c7c0000d0b091003691014020642c02225040b004c01c1000c0301a22800242d8001500080421031185a440002441002544d0151070010000c118030079101d040c860402c20001007240c0a091881085400f031200403146000e8040603884444440d41c90382c2e42100c02040c251900b605005a907903c1d81304003005071031007a40b400c0b8160000c08001c092041c5480400b0721101c090004182040ba00c45 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 961670791 1250 961669541 961669561
    0xc03040b0f041a1e0a0b0a1505270d03020105090c01050304030f2717010b0105070206070602090102011104080a0515070207050603040206121306061208030705071b1806090203 77
    0x1200422103000e810349900c60703a8205400c1c81013180401008010181400030480d003c0e0b000c41500902100d1a40c45140d80c0c45401c1c0c6078030034604030302d40450024045032000d24100030141c10702a10507600206400180d500280d44001034040c158010f0703549404210001e03008000300380c1a103809003000c2d800c514150b580180300300d036011a114104010303002c95404124502901c101601100131062613055150789071490680000c0702e03c8a61582041ca4103000795000d030084400258014020600c0c040003610b5074000382d03002e8104141159a95080b210b21101c0312400761019291880107000c2e40d41c45c1d07040081c54400d840e051508607545010030b02400c3c41d00090950219241911007588a81d00c80c000121940078060484111800807000c0003000c442d215000c00e0401d100344410040ca549840b102d50140348400c5000300141c2c07040020460150180d00a00a05480341ca900d980b00c100115400905055035480301d4019005068088043c8050740691400342c20b494000314150b04e071103100a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 961672041 1250 961670791 961670813
    0x70b04030507030e030601090212060604080705060a120501030803180d08071b080f030106020607020d050f03130f0507140415031e14100c02030705070302010305100503060c03040b0f04 81
    0x1424440c0001d038501c00c0501035850a42211802810f451b400d41c1d403080000d01035401092003110600400001800501e8090240c8081c1c50512000b0807a0034103040502806610000007001449102c14040c82e0b44490f501503030340038601c00c2d01c166480b81003808250403858120304050825420020402d0300d51980401550392203e41442c207803000c3c0f803144c0404101c54294000c040c5c5802c0000540a9010160704021030484603944d085070390560f01c840c800c80e100c000b001c0c2c2c010001139040005000104018001d0340d00600302c60a40e1107000c0f4181e4580710705c0680c1503002c81c0c4540040c3c130100711000406110b100940300c2aa02440f000f4a4080b07001c2c00c003a118040203003110030070369142c4501071780080141c1002c0e41c170642c2d0608000e21016841d070b44071054034800d036901e410030107950000c074400b10550300c0f503540c00344c002c048142c21940194090400100b11010031020004d0000d001d0303900700f020303901400d9400941aa01e0a00703080804045400902d002400ea9007613040c440003500070422 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 961673291 1250 961672041 961672043
    0xf0d020d23011118060f1207050c010c080f0601050c06010b0c0a021e0a0b04060206161e0e0a050f06030103140c0424170c0d0c030f03081902070b04 65
    0x51a009400e81d5040d0300000c0ca11128081035881d20075242c884418036001001c200d0341e0a244405032600801c1081068440c10f5440030b108101440362100c0f44135541030054200c112030800d136003401b07649000c0a007103816583e880f10001d181e802c14450342102554440e50032203c01c0c42d041d03260010103800555201010711420307281003400107020045e81014401e000400c1c1c1d004040540150314001342140c1c581046144912a403c1860b0020320801d5481c100c40884081360058012542c402440792a03480140c1c04900903c038400301704058800c40010340d20101e1955403581a0404004004d110307008200350041801403030060a00b004540e030b46403c0d01d04503580148015540004800103e040c103805000c0c4942007410712218610b0740400307030010210380c01c44003480d500155890070304904001d42044c111100b6085004000060300700081c1c0b00000c5401502030f20b201550340d0b581d0301d40711601d4040680004032440d05100d1241c4503a00e0444807200404030550502e00c064490320304c90040580 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 961674541 1250 961673291 961673303
    0x406080a0f060605060c060415150e060a030c090608071401091814041109071e0e030106150f021e0706081e04231f1d1b0f0d020d 57
    0x300c92001c02100f6081400500800f900703254481c108144002d40d1240141c0b411100804001c204c942c1c206414480c0b407840e40d13000e80c0c100250718035140041105050181c000c07500103040c0c040c040081850700c4c012400402c2308400002e04140391401882c02c00605800040c4504025200c8641c240e0340f011050f004d560b015400c00c0d440302c4a2041d140020070000f103d28848500c0241000240140c0b4540b0742007202d010b0324901440d80c0c408100b2924669000c0c0c03014205110601000b400c5441f0324052040d155002d800040c0d0303140c981408201c00c2e01c46c9500000044d80710308052120b1a81488040760402c0903282c3c1e03400320540004c80d1921528280695000c000d6030900140303041402034001701900c0141011405035041900308a401c9164649519031100404680048031071070004195500404941044403e440e0302003411000c0d0418829211400030640b40d80c00142c1e0040c040070b46643c1110f441c7c5501c4801075411b1140d501205410281308880c000c2007000543c44074001c41d42c0c0d80358414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 961675791 1250 961674541 961674563
    0x12061f1508090a301b0803071407060902030d0f050d1a10020d030e0d0813080c0706020706080a050601050a030c09080a0b06040509030408030a0e0a0e09011a0406080a 73
    0x2690b05140041080c000f6282000d40b420726121030002480c0104c0d8000e070082c08240d15000140103070303802084ca40c0a2030540035407800c2500032941c1c58024540040107450040180e02c111841c01425820100041d900c041e030740d011040c21850100018007611110342044000040350b650003410a000e10504c10354426200c00c003d200803040c2c0300d4180344001c030080c490010752078541c00003540d4030001d2024001091400070319034103000d4009002e9804808540ea0340300e51b41e480103201c83c500500c4650849400006005110b070001c4248510405003070507500400a2601e40803008240340340140c00c210140b0310344424802030745d07402000c446c040c0d12103080c00f04003495081d102f240c01c281c2c541d00c244424007812041008120035008114026030b8120780030700480d1603011010f40c50740f16a00c298201a0300401c03240d00c080d401051841030005000f0150070949560300411280305d00308580d0452180d41d906800209068843c0ea0201c00030f0013590700708031007410b0198081ea00e070024080604140400c2c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 961677041 1250 961675791 961675801
    0x19180e04030212070b060108090c150904020405030703080d11071a060a0312020309040e032505011b030f1808030106120609110901391112061f1508 65
    0xc103c4189410010007400e9600d440b01e0410345150501a1812030001e14880c012980da000c00080075441c606005002c9400001d13500701c51030559014010840e001074081c8400a1b2540c1e09108210045001c0d1190650304e10748030320704804a8420000d9108245405c2c030003400031800c0e8900f5100e03580c401440d441a203407640782c00035009480607031000f0044030358134580b1001290b010002d45000141a00c00b406108403100c2800d44900903c05402100c0070200554400070080807441c0d0001801103000007041d1120038010410103143d040d00002080d29003403007030501000d41c0b00e0031000b00110700d020a48407586030b840040b9840184107250420000e81c03248101e8051301d81c400340040c0001581008400c1c0e00040e554944d41010243d240030070041c0d0000c020028804520341c0000030030201642c40001041740e00c0382002c1d080d40081e50345046201400e20a40c4030031680e41c030b849600f40e00401c031a140022003190303420742010b040b042c0709641000410501022044400d550b660034100710300c00307a0318 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 961678291 1250 961677041 961677043
    0x12270501090b011e080f100c0c0b040f030e030109170c0106050406030f06060e0c0304030f090305030a0804020f1507060b121606080a0608300f19180e040302 69
    0x4104409041070000c4000061180d04402403400d04108007044c0400715591a080540c40f41c200035220202600100e05440042010703922001c081500340c1002944001c942d290a0011002103c3c100d5140d099100708100b450b40042d00b08404150440c001d000b5841240d4400c00350721a03840041224010108481e11101c9003074001d0310142c40060420001140e4070f0802c0c691055028400b81c91451421001080d00341c07815203000d200d25078071304680d4556140c43c0d03800c035244000c468241040241c007440200006000f0b0000349a24045540c420450b42402e00400040c0519008918487e03098070500c0c81c511819034060701c81260300404000380242110000c1005010340103a0702082d405800d01d80c0040c03c1c8813008540c10303200c040d6518041039540c1e0f6540b0040364081d00860b040d903030040c01d02d110340070001c1100742e070601846800b40717a0710350a014a00009420282c205141d0800208020b490000c400c00c00461030081441c00c5201700703e5428040401c0c0099020300030444403500005018540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 961679541 1250 961678291 961678301
    0x10c030f0e03010e01020715140c0f0423040e0606030a0f1406090607030c020109020a0b49090809060a021c090312080601021b03010b1306050112270501 67
    0x1c001d402441100410001c0d50300030352101904031440320b5072000b4090100311502c1445075000030090b40b0380c84c5842c1e10f010002d19812071401c0c4040c101d41040081981c65104c3c19070742c014030b8071100291014a078801040165441c0039000071480d400101004440d580001c3c5070710616401100908149404d400c01c0421745c01000d071000c0e564807841051009440000031410300ca502075680402100400710812426160321200c06980070300d0060302071000800f402d0041c0003c1d00d4030400525072060881e14040d05c0009958103408808200e880305000034061494070040380404039042125801650750740540380134960f5298000c45001c2200c6003c1e6008110f200d0180b2049080a020300d003001500400b140d056020403500c400001700800351403030154003482d00078407050f005400c40e089410340301c3c04480340451800341d140d03483d80d80010aa0b100c03d40700c0d00b0000c408000100c0c1090410002420503002c0c2807101001a00d0701011020603e00484905511101c0810716200345030642031090140c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 961680791 1250 961679541 961679567
    0x903030c03030f010f0b130902280905011d0603180f0709151706060105030601090e100e090a050d050904090206120402010f1d15130605090a1202010c030f 68
    0x80300c000b0601106501c205203150499061107a002d00c10b13a1101c1d0351001a00a21004426100342d50718240304202e465006040b4100c0b5141d50740901c3d02e08070307042923426288241a4030120344840014040d55a111040b504400250158105000701d0800030440e1884014003402c0754180101c08a00700000c140200c3c542c1c03290180c1114182e5480e60a00401400d0700d8400303042d1210100400103903400300f04142e0085440c0b045c050700361a916000103450f140d0004003c5410000801400710b20086030030f02850103414518a04072025081101e011000035004d84164083c0d4028862000043c00c00100142401b541c0d01d0503a44581e00040810b010b41a04070000754045400b00d20099010103d00416100354000d07a540307000000444c40a0707480c1002c43d00380c1d009404907081004a5410072820000a24520704a450f103066072004200e400034000e90004000a44001041c10451a15034400c01c0900a00c699101e20b044040c1c0c00a07000c040c020200506001c11400c80700142c034011401c6c0e16400c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 961682041 1250 961680791 961680793
    0x3040305031206011b05100b040605030d02030706390905090414210708070f0501111e19033b190b01050603150303280f0905060903030c 60
    0x110400e0030b07029200c0008840181c00100c1d0521041d0803c2410500c0b420026040406045006c03907078441c2d130018040641c021500191039041c0052184c404000c4c14000c584035501564903040309142c44001d81d404c1a8580503400d28a00124154026044004200d03418101d04092030701a031000a99000e80f0726072040d84d12021003403c11081c4200101e4240310702017107900307882050b00b00704003840c0d0f0520120981000d007481401043c00141b4100c0081891900904078401b0f603240c5c55175801d007540d03030f2009010b0b405030b00400c5d0402031281d14400142c0c4034950380185030400c0a2500c03940e003459908082e903420142c0b40c1c145401e90088c0804140c10f052500d28810a110000c0c85e4403088114481110152520541c00ca0f182ca003480c002c45070f48041c0c0e010a03129250303442c007010001c06800c05041501c410b0801340820400c0d5404000030400070201468043c0f0303040005c040320010f02201820b40e010321428032000480d603580300034031509449040318955240e120010102e031540c06a083c8040341 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 961683291 1250 961682041 961682047
    0xa050c0a060515011e0207140d02031915060602032a250f05062b050115030b100e15070204050108030d0b0102030a0207052e090302040c05041a0c0304030503 69
    0x40021000d10303071207081c20281c85003800400180d0402d200b044917601c1810051700211802e01811400482c03071a88560000c0441c2c840d5146900001d08081007018030050500d6010f01c01410441002c0020900c100c042008021103403401d400039460384510340d038801400004400c034004045407207609030700500810b005c44001c0f000704407241030b210500c40e115442aa61031040024600d4000000000345c4102800050030310170007008507520b007005004101c080805400c1c0c80c0610610600c074940c000e007400c0309401c400f0440e0300d8010301190550803150b4018070446424a0203140c000c0c0180042000030365010401060303581405181e8003a00000950090410000083d1900700001502700c800d403038181000b01000c94401642d03240700342e6442c4400758214010801c81ca00e812440e1083d0510f800001d058145420408200c213a80d00c031110b4008204880018801c0d41070134440c40601400a0500b58a014142001501580401265169a40d0000400814514090003a54002e40d403140c12251 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 961684541 1250 961683291 961683301
    0x1103040b0c1303200f0a0b04050d0611030a14010b072432130b0103240e100c0504180b0d020a120506060103020a05030112020409170a1d060a050c0a0605 67
    0x7180320f1100052207651720210a01552814164800880b01a1400d003450301d45480103001520314841d80964003240d494014454184010009502c01c4281c528002088131000c0d80a800e40328040c0c002c04a454010b001d81c80004210030000586180000c0007041d8000300403030514040d00300001d5035032080740700c90441151124040c09440d40b035000b07100d201e01e070707542c80a0021081412607036014005002803801000420481e050344404c2903040944c2000c40030854401d039041d0344080b807040985900070b80034085080c041d4400c07000800c483d490410300d8070703140111300c1da0752840041002e0b03440da6907080002e03200d40d9080a00712005601a1681020a643d0000000c13500820241a46c16014450024081c1c0d80301e40308640510703a4580b6500e06603402c225000700d0841108904036005940c54040c1ca0104500c0100020b03404c10428000d40d0716607038100003d0029100d841c440000d0b17944154025226a608804d80d4403400c2d40b0f00e0074079161781d4610400c524007117100002401079132505007402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 961685791 1250 961684541 961684583
    0x30106230f0d0b060307020a031b0f0b0a0f0b150a0c0b1303080109090816050f0109240204050913030c120e011106060a18151203031103040b0c1303 65
    0x40300c6941028200110140d0f07005102441c4811500c0307500503080f0610790b900080c02a4122840091480365507482c00c0b0f2a5500c1e541100355861042e158401c2140c10080b524940f0700401141e80d400791401d1042c030b0420008500c1407580040070582004d4049240001144202280fa0a00303412540b94146420007411080b12007440c81019000aa8850300125a513000d6008940f10b05030301c940c055190007002c002050011880840031941801040890865403009020340300500b8000c0100c1d032020205280c0310365101e904800000316860041c0000c010325075502940c55480300405516084a03409460100c601d01140a001070288103111480070156034005100038032010282c85140b070b80e405001200d90703190310454841e94044041501800018240700d0300320383c0004544004078900143c1c900c0311100702c00640064650420005404040c980d0502a0303441030550400221700d58100740d1601c0303002100040040010040006045d4249807000a200d00110380041d0010a4000e10b10005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 961687041 1250 961685791 961685797
    0x804050103060605040315050c12090607110a08180a081221010e280204061e2316151d030307050904051305060f041214030106230f 58
    0x200d000a141c2a000701e41039010fa4110b8040d203401c1616895018184150030000d00707802031620000e21010301089024000000c2c0e054058204030016080b1490418401400c0001402c14600f0507400a00d400c0f02043d2414120351084541a2080406207401c0c400701d142d15445e640440d0440c4602e00d40030040c1ca14083c00780c0280c0902c0c09580b8071400030081d01c1c2018200038020640b1307810009020481000c00c60600280c14408241c2c1030328040000080d0b00300305e0304564401400700300c6034590704800c10111140030301c8044550410780070204407007c10300035814050010120502c00095248031104054600d4906a60301c082807001c00b110549000c40600008000e8040c000290504403002c6030001c002da038819203065038ad090070621140100070282001800901c1a449030f040300c240803070414400c20341b00e42450a0680400e042506d4002006081c40d00c00400b040002d400c0760416010031001c5034119562490000350421040b020200c99900440030302101600008070068611404006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 961688291 1250 961687041 961687049
    0xf030d08040c090911010c020406052101110703171911040602010506030d0e13020904060e1e04030e0607030513090506010905040203190e070f1d1509010603050a0212040804 76
    0x407080c0311070f6542000409550781100020b050000c00b0041d4a110351003004020900e0b40010408191150b5480215000d100301e1608540c803140049840110b460782400384110b81d40d038210207030b490700b004c64a0050050380d0703034540d0030110001c00000c120b50301140d0310b5000349100307001030400c1000c003820380d4005564014880d42c409035082200140440c41c010403819100c1141d0785440180020580420000c20507401c1e003414504d41c203001042240e183c0d84640009000800c140017420700344203501030090110304440d105100821010400043c2d13019070401c01d5074400340c80264440900c0d2900351464040e01d003080141190404002484505d69044030b0300a21080e241d005c0880e450f00c0501040e442b04450000030950622924080b049859101000034500030050f070b56040d44071903038501004500c0e40b0007225025400c40d860700230980d18540c44d420050110305020040c0c0b035000451003500b81441800203065035440080c042c0d59858049456002c802602000300e850315140c402001e8002c1d000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 961689541 1250 961688291 961688303
    0xa0b0a080607051b0d09060f1202070f050111213d09090302030426030a02070603060902182e050d05070207180225230c01050d0b0f030d0804 62
    0x9521300d44401e0110740300240100300d941d054001814004141d43c44428039021504010f80317081c4c0c04107400498800b403d942c6116a00003441c0400c9820045c1c20b44640c051503031140107003001140d100b02d07c124094942008200a0400c40d83d0720840440405aa411a03120b041414010303040a004120314551082c20303842c00011003081d440f4024a400c0b106a07203030040240e4402c02040c0881083c1c55450360f084c000300d90000045040c544801811600701415680150348408000e000d0b058150040f400680704010007142010542e0988142440000b41a14010303000385202c0750044202141181110f8082c41d110248240c0d071040c01032a40d881402d079040140d1614000c5844248013040541c1121406080d90f5807200c200880c9000940c4000d820300c0701030038103413801a81d00171300c0700c199804103006505120140c51218030034050000c49140065680e089256040490381c1c1001c1aa0180c0342c00e10380000b543d42c1030402140310f05e00130040c0540e00d445140c0c0545c0c44264404480351080384240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 961690647 1106 961689541 961689577
    0x15150d0507270b010e09040620040f17070f270c030e011b0f1803020a030605061206040206040308030405150406020c01060515030a0b0a08060705 64
    0x2d2685440e030780b6089000036210450721508021180a08040707001880313180018070744c8000144010503040c0d035100e501210303919401e04030500c4400384400c41d550b15110050900c0710441440f44112402c91008901100540840c0c00002c45140c143e0ba400102e040c01d50960032a130000d9840a000480001a20003c08590003890a03242c8640c60005015aa40c81d295080d1035048100b0070f002503903100c0c0000a95488480182181417600c0c0c00346580b85402c0000c0030001c00340e803010b5400030618002209000d1264000350050404545603244419410f59503034070307a082240c0295100009000c100b02142217000150f030702078410400c0d100c564041d09442c0c1c08070002911b00755440e035804156150744420034411031015241c1255070b000c58000249010030b03644030040000c91001e4580d904101e00d80c9a030242140a4800442555a540361400c0c0040c860342040c41c4c001e400c584a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 961510791 961690647 := by
  have h0 := BRFrame.cov_init 961510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 961510791 ≤ n) (h2 : n < 961690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
