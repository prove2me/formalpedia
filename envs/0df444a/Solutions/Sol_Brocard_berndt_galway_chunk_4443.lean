-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4443
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:37:41.491998+00:00
-- url     : https://prove2.me/submissions/f4938aa8-3274-4652-a418-f8c4a19100c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 798920863 ≤ n < 799100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 798922113 1250 798920863 798920879
    0x320d0e10050115080115031a091305010507030e1905150403050c06060a030803060d0602160f020a1502060a0b03011116020f01110316060221090d020109030909022b06 73
    0x43c84030320b0704a00f0070400d1541001c03c1140d42c00750030116102059a1000080e00458400b00640301050024000c00d5160a203d070b40030081100c034400c01c4d5a1f540c03c10000c0342800d8481c1c4141050302c000e00c005410755003803005511000c0302d040b00017a01c0f0361142c07002c08010801c8401c0010700451094850303550b00c2c0100c4003020b08001e40107100c0341c0f003a0390101c0e00f04082130250048039072104003211f0f550505201440d10320700074028681c0700c1d03e28038070040d40139041014840720030310074038000c1303540e10811039440080c01d94400c0c111000c0b0005810690215400030350640220a41280060011034500603c9072407403250741200c0800703013001c80d000c0c107500c00350300707200b402c14045000c00e28144031400640710311140d6a1103a003414050707a030010036400c0203020190b81940c0050902d411440742072014400f42070030719601038800d210740e130240140540030f09005100e44445680d150f00d40c01c00c95850902002c000750407500419196080c1d030f00e0386039140c3d0800e01100d645545880700018003a07042401ca = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 798923363 1250 798922113 798922139
    0x3110409062408010501050702010e031f15050405060d03110a1205220f1203030b09010b0c073201211a03240c0d05010b0703320d0e100501 61
    0x60b140c14004420700600403660300c90b013107070134a60302030034100c40340d142c01d00109140500c0495110201c03004030b9800400701c05076400040c1030010212401c00041d0300d64041100712903040e191207500004944206000034003e010044569a050058a1001800d0f07140c1e00e2181d25a00080800036000080c442c0740c10421042d40d07921880441c0d444c4180c82d003000405803805405008000101c4101d00032082054480e800441d206180606981078559540c029500e11780c00144540d1a680144400400c1c05070ba0130b1031001041c2812106980030101c0210421004242c0380341c0f5504000b00080d01840123618100707040340040762810005640034a10340c5082d0443d046050340342c0320350086804600000b41044d0500c082c1118007414000680b078042104042c2d110b41d241600c401428240002149034a42c00540307071290094482d0050a60003443c5100602007059410004c8540c1c07060541c0340380612005003510040725070700081d04905013601c4600d171800140760103200d262a240140041110301750 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 798924613 1250 798923363 798923429
    0x307050d0513052a0d1a010506070c0312030b0d0f0203010b0303120c03100f080601051c08070f1b030507260706031a0d05160b190311040906 62
    0x103003044442c03602c1e940d2552a041804503006140588441103820980e4a140042c01c8800c010b001900d1a8100e2401c0401d000c14204080b150400120000030a420803008a801042e407013262a4421829a81d03078083c0550142107910405a03500d01c0c402d0f064503209546001c1c0340c0214142800035940e8070415081d6528a607a440c060b070810702c1f000502c0418204900c0d0083c40c04041552a99039902c180040b001040d44091500d542c103400010b03d82e507012502c0b6041e80e60947d4200c00000c004e1402e010b880c019250000e107129010000100032a040c040001e8099106180001e40b100d00b6558601c80301c15582c005a586800690b000c00200500328110015002c0c41c07072258240f1040a10007980360307603142c82400b00f40350b2106500311100c07003000790100006400420003041d00748a41003040c0d07506d03050140c410f00700b00b03112000310799422120241c5070b010410f4030720a040e83d11880401c6000e8250302c0c81c02000010240404502410103024400103815020301400d0180d0400c020740c0c40da289041c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 798925863 1250 798924613 798924631
    0x14040f27060501170615030103080d0e070f03020105130911131e12031101020a050a0807091404180605181204050a0b0a020f2a0324040c0306020307050d05 68
    0x4204221a076000403904804100b5a040f540845d45c1c1e403004034903403a12000c0404000c0e8030000002c0108401c0f00040d16040880d000108690300c01c080d441070356500c0b24000e11050303016002c1e04100540c42040245160020100fa0110155442002c00240e6046103841c0080c03990100c4e45401d182e8907916040001c103034003000441e040c500e10456102280c07084c0603044d240c02c05a00600c0500d8010507141c2d09582002e40210743d1100040da0003865504030880030400120060701041c5061700c500c02c01c1c0c00791105149540017024452040000601644820f602c45260844282c804219240310b054462401000c2c1002e010300014595401c01c030205002c0c80d0b0004050009001907261903100400780c80313071003c10720303560b14a1082c1070b480c084038610342c1400c0e0722500f110100c810b080032036589000388804210380e030891041400c141d16071860101ca0b80c1d03124440d10220011502a40700141c2080c001c0e580c03503240c691a611203070140d91084a401001c10b038009804a03841d50107100f0503034880500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 798927113 1250 798925863 798925871
    0x9110f0402070c170f0d03060f14181b0705030409050f0903030403030f09051006060f0c08090609011e050306180f0f04060b030a050c03070602030c070614040f27 71
    0x95a0350800880f51070040300303102260050000b0850204000b00213103114150210f8020741201c400040190101d8001c0c1818114020030000d040c9240400d07100ba0548010003800420203d16018a00701c4d000904103d612500c16a060072a204400e0003007030710a01482c00b455481c0e007001c8602d42924006461540c500c0c1440d030800c4048800441a240c1181e41842e02088490700c012007000a000c00c01009401401340c82805200404641d200c0c404840064940b02c90a00302c04500355202c8512107000f40500b9820480310360249403503001043d41c408141801d082208030203a041211006107420342c2d01081c40081485403e2030070400e07103000d070000903095402526101c0c038070000205002d001202c1046128003c40c08000c840d400c030803440b85001d070482d080180d450401540c4c4503501001180a400760380c001203202d40c230110456115200074001484542e1815500315040b1a800aa410302954240404105210ba41410900030100442c00e000b4040340c070030f024154034485510101d200c5240c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 798928363 1250 798927113 798927127
    0x6060f05101209150216031409030309010305061302191b0c0e1503010f09020913030f1b1703070e0108190e2103040b0a090305030a020705010f09110f0402 68
    0x4400350b60041c1e150048000700f120b10030b80c90040d01c401d00242046660301d0001c1900c0e61101c49a0802401660182e0740d50154040754102580c1248500d0f41a039815800401c2000300c0d650094220b02e81060014141752560940c600344901260005444c000b40c2c0500304030001665039100d007101c3e6004049500d1b481c1014082e0b41e812059050a04c91240f0100c0c4681c0000c540c1c28140051000d9050040c00a0040d0224100f1150003800c1810040780b2805010001c1668900c450101c0000550703d91517000c19a000140180d4444003501d034854810030151961900041455071b06c0c140c0e44400250300c50312801e10440c080c12404207950424100b00e074000c108075044899035550054540c0229002504400d038032015414407900c9460701b403d11030310406030f00300360345030000440c4514028a000740d007940f11810b5480544002e0007014000820510200740d01ca406903004040c0e461007000001b8688582000c45400c0d5a60745c0025100071681c3d40304004541400d4031401402e1404540441c54122 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 798929613 1250 798928363 798928367
    0x21021614031005090f07152303040305031308120601080112170a090905091506150301030b13051c0305090106230a050d0c030c05040c0507030309030e0d06060f0510 72
    0x10400280e240744036120404141d022405110424030310489905560106c3c2d142d0048000e0001c03580005000035074407100d4154522a940079411b60031043c840040d2030354442d0b48040703c6581010300601a25240b40c01824002143d0f0300013002111070f0708100440b02d00c4d00200240000405078000701700c1c40a1540c070702c0001a01d00c0300e10348510509201c0360781c450241c144204d5059100d0b4104c503051501d4103003441700000f40007482c9038a0740881d1a1001c1d890342c41c1c20500c9000b14080c1191203d4100a20041c0000364801206d06d500c0b402c9642c04203982e117070645070a86410041c1c240840258242c14040c0e031800d0341401030701c0d441030680c0c00a0100c00c0c6404400c00d003805e0341d007024410000030440d960100d40d50390020342c4020440280311041407100c50601454600c0d00340710458a48099038800680e40c1085c0c020000c9046582c0c80d140d08100140d1820b03000780c660464200e040000001c0614540c2d0f0741c3c999000c030044d005000010ba0203043c0000628011159001503205610f131007603056101c0e03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 798930863 1250 798929613 798929623
    0x7030903050a1404170c03060a021e0313080301060528020a0f02030a1a090c010c08030609100b1c0f09021f020c03031818010e132102161403 62
    0x248545441c00120f64031803040712042c0070743d4201c40f685416502000307010305400580712164140480c151030058941e25158003c900c24545514200c001c3e911070403003a0a0035030091035010308021248141c0c1482540d03a0301c0503501c2604200045400403400c01800107814904030240300030720001450171084240b01a5440056038401400c1e51516400340702191406d014842440360b0000b40748002c5400800301c8061540226040001d49c414044440c3c1e6075841894551401a001356100b0701d540c40b05400e102c45040c006000c00802040c4000c00590419204003d040b03500003c01000300c41101c8802d00c100303a0741401306544c00c20b4104032403000941d6600d030001d104003600d6408010100300000041e82032008944d030040d4180400716801d080303210700544d04412480221402e000d945022406400d41c43c500b802402481043c841c005045a00070002092609004858840c100500c1d0315216140d500382046420060f001040c49900f00d03114000c1e494040e242c81161a0f0000500c000429034035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 798932113 1250 798930863 798930877
    0xc100e0318040b06030412020d05180f0d02131e020705030d05070915080a0e150406240902041a040e0f04061e0c020c0d11040c0e0d0c030204050703090305 68
    0x400c6a8100408040e80d0b190f001d0030800034050b0201e900c0e0310306400c01c05030110074410400301501070702e207013501e400d480b5000321803c0c28040da1107208001d41d03040c28050002401113450760405019521900507a8604107494015400d42a006c100c0142000c2e22020310052188214400b60052190030300107074020041c2d60209041001c001101c0d550400c0c1180c031720305141d000d0b100c1c1c1e60701c004501008541c480080b0b84114800d40c8184200c50300d0180f07031079455510402075000d44031001d0100b4001000c035000034040c00c5116411103100321482070004113221050b03025044180d8001420004040c0820561503074100030502942001d00d0310b0071680d4000002000528651110000601044240d0740007820300181140c940c40603446a0623407000400074008100c015108003440c81540b031500300003195905620802903560014a03000344006020011035000c28003c0e9181985c015403a5414544500c0d406009190600703851401400121040030f01120101820200d100020070b400008459003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 798933363 1250 798932113 798932137
    0xa050909040c170714060a0f141e0403060b03030a140705030f0705150a0e100f0b09070c03080a020708030412020f01021306030510032402090a06050c100e03 69
    0x45580c0307600e0220052800741e00005548000079604501084000030b4250540350395280c0342c42644044820484c00f4001c0c0511800011400300300000764a1149040400c2c98901c07162590801c105603558802002012401915088002c2810014400503006e6281e541300300760044c1d40391043d00c03080200000099001d10444010000e80402041000c001300c608100d05c41d0451074481e000707445d0982d1501d070090300640142b9580008100c00c0e0041d4414460050004002080b0f6485141c020001802030711703503404540d0307980e0501845161558007840b44204040d58401917281210b103401b45c541300000e06052043c500c140184400100e8005c103c0c0e8216401800300c48a640b19140c0481c03070700b4074011202d8a554000310303119810b0b030340c0110f050050741c41603102844165a0004190f8114403140f1018042c01b41900035068070706800348065105203104c84016103440070440100d290f9541d03aa00c49800100c0008000325507080c1400414400745100340d0501104a1030622a030f80c80c0a140f0107000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 798934613 1250 798933363 798933379
    0x50a0e0c180a17070e1006050708090a0902090f0301050c031f0306050c030709080715050c031603030203061809030f09180708220f0605090c1323240f0310050a060602030a0509 77
    0x4140400b00301a18bc40300c200808030301d4126203c9000c10043c2d08181c074580c0c000c082e000482e000618040c0a80380c46071403038000440c00c41e0f40398103008109402c01c202c08440080f0220020011400c580180d520924405201c00d40d00c0c01c0226004040c03407581da00c00d003a56000a601807140380e18420012005148c9803801c2078440e2810000d0504511843d8550384803002000c2c41d00d0700701509900a0362040e0320403501030180d40d80341c2c0404110307203104441000b01d9400420500e2505e40c2464090404d50034050010310b08081c0c0c1c000c1c891b502c01801e90b00705e030100d24080c041100301b0507145466106452160010915041d155648511441c0030302c000906280d1a0f40000380505801c00585104080040c00b018a80071001c00708070040007200c6811174000350001503c3d000b512035420071801001110b22a41c490210b16046020807581e00030303641c1d032141c4008003801d40c99404012005155041910000359410920b013903000b1500503078448030554105100d503031841b50f0420280c5410840540c1c04103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 798935863 1250 798934613 798934627
    0x30f15011202150c0115050f0310020721020c090604090b1b0910050711240304150903020318090106020a031101020d020a0203030f01050a0e0c180a17070e100605 71
    0x207204000380f80302ca1001204007290340088110150400940700c0c0303518100070704c0151070307801b0300a60159007000140c0650002400c40c900b0841030b802420002e0040782c2002d01000c0301c4007102c084031411480207006a00215a1b864186410701280d40c015508079010854880581d40e07500141c80d00030643c441040d641490b100441d02180110b410540009210542d060419200070344207802c000015200e41c80d04018145c1c0c00e00303015848105c11317602c600280f0300320f001e04215403031036500080c000ca0382d15503040c81207031061256000703000310288281c01071501c40046222a220804080017080e10600e408001002041c2d00419040041d940605c0c00c101007040f20800a40680f0a204c210081c044c40003582010659000c0043c4d0300034084001d40050a0741c0c0d071002c1204001d1680a0452601100c0001c41c1b5001c0515008011400c000800340c03a1517882d050005100b4551580018a81500d4042d11048400c0030b10038a000b4140c0f03a1400d0b1302600704141d0042d00b40140e030241005000001030300c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 798937113 1250 798935863 798935869
    0xd181508060d050106090e030d0e15010312121a03010b0d0b06010302180603040305040314031c270803102715080105090d0815100f050405090405010b030f15011202 72
    0x170405000702aa0a110f20003c83c0000c3d59071340d0004020029030703481c215600249450201d81d03040c045e4584419a2056400c5440d52112501001061024450424101c10540d0202d014420410028803402c01110440f4802c0c582035522140c8072511552400018500256202142c150000c0080ca1700589505852880a60f6502c07101082e036400784001c0100400c0551050040083c1d0780301d041550103800040d09020781e640500400c0300d0101ba0442199030703048003503074001002a0000710388041020150340c80d89000380b0794400c0582c3e42d9200002001050030048050a0060444850103805055201c0c00c07511403102d00002e1550840d100c0100070180e40a504108010f8030007030000f04241d06001000c290384204098060020484500c0082c1d040e1501444148003c8805841409440300e2094100c80707050b84000ba0f0810701c001804081025110203000074032951003a4000540245d00100301460541200007100d05984032102c6501c0c2e001c00780300202d04469000c4041ca46c406254400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 798938363 1250 798937113 798937121
    0x806120d2a35070605100602061e22230c0a051c081201030203012a0e0103060b0406020f0c090402060a030203090a1406160f0504060804140d181508060d0501 69
    0x10300c2ea41c030000729030901489140c0d0700c02e600640700c0c0c4950511b0990384aa09a0f16180d082340d2010681415240503000c59840820142d0b01405040101506064464040380400c02408040d540da9030401c0c00c902807521118440c0050984a500600001c800c20340010403c3d001401194001c030001040b40d00b0f242c1d4044e92030301000d0381c45001980c40d0328a402001c43c03008401d01c0241c1c465828940f1700d10b007182c07503504803040d240141d4034551540400c0c100280ca9080d1303c0848107040694030300c0006034503a41e11003c1c20162a40b54080c3c0411008000e210b854a1381c14151644078600b40030034000160b9410007113070030f81e00f081c1c140980c03a543c80c611098180140d501c80646044c4400d41e25a02c2c40d0781c04507065108000c1041180306440c1d00742000c8804000c101000004101d041005009040c018000180d10511032010740301001400d03ca40350900803034180080205100c0514040031450128141000c1c1034004c24006000c0020000208040c0010700164011001c00b034100003402000c2d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 798939613 1250 798938363 798938453
    0x240f020f10110415110c0d120302070f0c12050c030303071b1a01152d0c110406030c0e13021032030108010b010203070209070806120d2a 60
    0x241c2c138260101181c101514a460101ca20000b601030152008060302d8103240035540d05801c040e1769580701c2142c04041d0000d40c480003003920390307042d140000000201c44140300700c042d04545030564a08105482c003d4500111420714034420740040c420406440e500c00312002e02c009401c000b04c0880032103800d00000300124840c1d8203c0019030305002052224921500c9442d40d40d0640e642e5a04009242c0707104140c04e0100959402001e4894880404901c03800105030143e0003034000c0c646011410000078119182e651007254044044802046541d1012200507409070304d40709018030300b80e81540014031448a407801e03078040c41b0541c4141400c4a000a00800001104000001505034411248a8290000d100d00c030055801c0c4510952254404400e403602c01d80e0240c4200c2560b124008282c80b1450010161508440b00300c0042c507002604004107100300034140c85515124108442c0c0560000b11604002e01c03e0b0383d0764901e000052017a1002030180140900d00610079007607441c5030118a0301d164 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 798940863 1250 798939613 798939629
    0x409140a030203040f1401200c03030d090c05060f0409022b0b0a050a0f2d0e090c0105190806060c0321100503190606240f020f101104 59
    0x14040e010541c0000080007550062815005c540b992011201c001300940b50110707000444d0742091109011941800380d2a8542c2101078583c0c024460010a10f180c0040080910140d11200f001d028042c0c41880c0001500c0d081e2441441c00c0048a01005680b28500c10468010b600003511900d2001d0001101c0000070240714981d2011071580e0100050131034882c101d407044c2051800000c0d203140000414080360303503030583e4040262800341d06420400c0c080d004450f000d840754440c00c3c200100c4031451006000c0410035809075060580318145400d81c0c80007000d040c070100708214004810b0451110704040041d16140c17403684c0d2410003240d8076018200d00d11b4802d1001117070700c0d003182d41042e00b090f51401c01d911810b80300d070380c1c3c544c1265040c00c181c0c4181034064105a02d094456030324040d9607000305001d48000b141017a52180500100a0300c0307640d00003602440b02141911a50103800b076180070301d070740c030050401d542002c450648071351461646503e05a541c0d0a010340000000b001d460044c1124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 798942113 1250 798940863 798940873
    0x909060f1513050f0c042603071a01081005040b01150e100f1107030b060d060908030a0219091505130312051c0e070e1905090f0c0f0d02040914 63
    0x3059880000e00400d980b00c107003042103d0001039107000c80e9400c4e036080f0340c0c070081d070701c1303004087c03124441d01011101c1c0d0000840d01081120201007104d060842d07d24509800c55542c0540c900400c071410310314a0800c02003580e08000510000c00e12000c803013410b407003000041c08140b484400c1c06651955101500f241c118403a00921841c45070400405032845c4c01c56100e41000c0400e1041442d11542e150000824224114000c2215400d020320301d820424414100041c3e04192612007507000d401c100c8003c029182c000695140012581400d2030700d10303c260400c040740500b002c0c02c4110300c4a03010040c2d0200140414040c02040444185000030340d08440050176411022a0040213948020a00b90510983c0d00b06001c0300c08452251080e05003200010702040740c18400c1c0b001030a18050900c01d40000320300c840d5201d100d00ae21030380d030291002c1401803484841c1304010904002c9a41d805c01c2c410b0300098480001c1b030300c1e90810300c101c283d41201d000508003007500d0a04d0750719400702d100105a20403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 798943363 1250 798942113 798942139
    0x20c0a02040509070f060203040305032236051317071b030209010e0c0307030f14070c0605010515030a0f02040f140415051c02060d0f15050909060f15 66
    0x1c0422444c05841210f4034510f022622900b090380e0320700c0f603844010300c0d6a104000b600034041c2e40507440d140c22813841110031610756441040074000340511401c4150b082c031001401c0b400c1400c1d410304a510703070061b1000b44650724101c1c110300302003490410040d100800d89c442d0000c52198010444245c5035101492902e0740340b60360030008034a0580c0c042207000304211130001c6501c000036060b240c811124071481a10f90f56404030201d001d0300c0095446500c80d03890b08401944810140d105a11030b0a640c1e4840300c000401d030a00405665060740002c0c0110144003003001861880c8040300e0348006200008180d01a03505950340080c4100c2c1d1200b952200e10040110303419030100e10610040340101c0307041c03100701961442009800c140f4852103900c41520068051080e5501060f03901c0306c1c0c0020241da08000030f400b4908165034030f92030007662131942c0700b1114101c0c0410f50402c0d409008242c035104501d140c1300e102c01d9680c50380902001c1c181c04044001900c2c8030055250100d07100f10103000070282c213603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 798944613 1250 798943363 798943381
    0x20d2717070603020304080d11070807030206190209100c14010e0303070f05090a15030609060b0901020f0615011107050a0b1b0a02010f1206230a060c020112020c0a020405 75
    0xc0d100d20390350540c0500c1030300240c01403090007986e00550300403070a2807808840c1c08800c0010103c13200c0c507ca08540610001c404124400c010344081030082e0003070100c6140004403a01c501c01080c405c510f03c03510512000c000e9448034600c0340300d46c0b0000e041204e00d1003031324281294040300c0300c80940c69540c03c1001c9803111910110145010712402d03215100b1090f81e0283c181ca441c080c41504540010101d02e0070000085090038030110a0707018100041c0380340d1107004040c15141c40b030700070b0140c1d0715000607203824a59040110941c80c10800d006000070341803042c0c3d0503124240020b2a68104000c0030040d8844600034804080100340c000c1240207800d65030308041e41300f07030081140200041010b50314100c44100114202032096416918a41d40c3c0d009078900307075076000820580160141d5034003404164440c19214405c50b403c1e130030102500c2c030340328541007240111183d00a4400c00688013032010050f41c001001010349036801b0710142e01c66154031840d41c5004d64056020b5842824001400f807506 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 798945863 1250 798944613 798944639
    0xe07081e030408030a0c02090c0c2a0d20150301120203191514160f1211030109242c040f1203020a12050603070305030f120610020d27 59
    0xb4400d440100560351102a0451140a42040c0d4ad449800407101e801c40c80030300c510181402c2c0c1038800b0811004180c1404191500c0014404461541001c03003440010101e151030300d0f0811004448141c91a1220078040c011b42c0018898207510f03c01d450000e80455800b805030035a080d001e2429410246228203004480180c0600032442e014074041d002c40c5800c3e81d030343c0490720480748030300301c14070828180504880c5010154441c07020801d0002c0400303041225030143d0816040d00c52545a01c80d410810400101c512498203118111400010071f00403043c5500610111200d0000c00445041002c1007250ce00c0b45510342c000900c0c00060070001004031480e115819580103030100da8a41206070410b03800c0380704e9001d6180110380103200e015181d803050b0f00b0040d4000300c00f4081c0c0b481716035691358041c510b802481c206520700c000428588208442080b40e550320181c00ca40d1441e0620881030701944605144041c0170030451090002c0450320702180880344c8a802c4d070b22440411136a606c05460b21a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 798947113 1250 798945863 798945887
    0x230a0c03050106050901050306280e0a05071e141c020c0d0801080c090c120c0a1106060d080309070f0f0603050a111c0609021c0e07081e030408030a 65
    0x31a2405001280461140c03050711100901a104c403451601c8001c104103605601d07208200288101a0706000081e0b2841c22030700007440254107014880c1440070840c4243c0381c00800d804100140404032034030a0101400d09201004035040500c0b50948580c40701c2c0341d920075100d2545400024404030034055400c6d500515032810104140c943d4030b44404021a5a113800388170701c1c40e160f4800035442c0010320740040c52581285034155031078a084240c003403111013000220f400c07401c05a0081800c07803a5540040745101209000ca02400003841e0410002d00509007003200941581000700c000760345007038200046005403402d0744595000c10303a0350040111f9045240208030002e401e00340452808030b6603014000c02120f01c5000281080c4134281a038884d602d0600d0794120094451400041300c60042c0300410441c81c0a4442c424261001020f0100b0355541002c005900da00c504402c11241e400818041020700c800c44015445a42c1d12008515501954010741c00701d010004064002d59080844003801c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 798948363 1250 798947113 798947117
    0x5010b28050d090f1a01061e050408060103062c0a060c11060c0d1a0303040b0c0a0602040e04060b030a0b06100320070c062604030324080606150d230a0c 67
    0x480c02405d001c003070010001c0c0700e000c0110b04049003038010800b420726000b584a03c189003c40c2440c0e900c20030300307107000020303401070300c05030380d9243c1c010700b01c00051004200388016080c1c4083c0340000d0012056545a07585406011a540d035140c2c4403c00c1c0c4039000300c2d002d48036820102d0b90f51341410f0049900c25400003407220b00031898095080015421034480e0541d00c60000d0146090910300903640580fa4000e141e1140c841c080c1002480c0090198409000034040103000704d01a480c0a15003a822242e100480601c40d52142810a001500e210101540305800f031380d50380002054110181c01508a040a1030204007030400c0601c25020aa000303070120900517150b150704070b50396800903112008203003000d19401080000807000b0034480101560458407901d80010b421940c0394443d5504001071001c00b181001d010780801c2581000c0101540140e01154000500090182c65101e81d00c1010040c0701c06d91b44030815850b50340141199001d1401c07003442e0030791451a203000500c009107801955900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 798949613 1250 798948363 798948383
    0x20a030614030a0512030604060b0f0c07140319060b03010f020c06130c06081b042702160f020d1209060f020c0d0803060409060c030f05010b28050d090f 67
    0x50b481c00041001c00d0a802c44003078030b00070407014106840c42d40001c003042e400c00e4544400082d20a0408000e000c20780e407240c3d2540d1030b24001102c0c28100240b0394050000c103502c01606001c41d036004203078004440c9240403075460502240c600b00700942094208030ba419480e1450f618220000364004101081d10130050301c416580b0090001c143c41c000540203004002c1e1900300b03000641c000c0509070307001b6800843d071a0500c0c0c080c0e00004241e42c8180c0000c1100c40b0952400c0070624800900240064500d4101358140000d04003c45411102c50300084d1120302088944025910b031008808902c0b9041804400402031540014020465512640000440e0343d0516203200e4404a9200c031082c00040a405140c1c0e03c6484204681d00007611050780f00b9038451160b40020010f00c520f080026083d117010aa40c42d10301188001c0300c50582c840d0141060810901c882c0040d0400c0c103102400303642d4011f110065103244201d82c2809100c0d1454201481c00000c9411f01154258010865104180e488 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 798950863 1250 798949613 798949649
    0x9271803030b0907050901110102040302031605010809010b130f0e07121a0106050a0806012007140102160b07080f0c010209100302130e062733040b0103090204020a0306 74
    0xf050a07402110308800250f02800300d40000d45c070801050101000c52030015050644940001b030501c61285182c030001212103804005e0b43d60007803041c0e6400780c102070080085c1003200010845c5e450040c0300f40c1f01415a5540d400e03c2d01440e50384504d12841940c003c8a0050f61540488500318815210a4030700701000c14004845c50400308203141600d1856603002d0403c1c0503058161007d900c040c001c1070500404100764604824418684046004008007e10085241c29003000e42006140003003411900641494070a0b085041241d0044a03040480c0d50b46d0f650242c103055189000c2c0c0b0180d03102c006000940020000815000303130406000c100c5600c02c940745541819806c034410700064001c1c5038100d4008200b51841f0301035843d40070f2000380858854030001c84884694100728002400070660b4171007406004011032030504440442201c0c0c40c80800380c0000b0780c00c24a402e50700640d10843c2c4843d0300e41c44a0744660080c01d40716038064029525408030b03141c0a0080c00650181a0011850136140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 798952113 1250 798950863 798950869
    0x16020a12030f030f0e060405062403070515130915091406120717010e0d0e061801030f020403080a0f08100308090f060412050c060a09271803030b 64
    0x226a41611101c1030b80c40b06040c1500605094590140c107107558003007203500004140091440303244114081e120341e140010025440c1001148401c10024110761190543d440001d411010b41d00101d40a181c442d9001405000314814000c4015040301440000139a610b4690003190f40f844240c04401d40c416255144941241c130b11003403195403091464081517482c200700000d90a0400c2200030313580e400747c5500d000300f2116603807103030202d807a13540300a00d2412810900600c1c030119010b14000824001c140d0029810740a10843c82a840d4102e03040c0c40324503030280e8410110802c11000c155151507582c20702c10300c00d4204c02c4990000c40d055402c500100d45c820500244030b202c03c040c0002c0c2c880c0c00c50711444036681124000581008483e08014843e039a0a00504010b00641c2d24580347d28026107850f0382014554006240502c0084c00042002c58000c844030081e100364a0703103443c0306840711205000a40600300c5440089107482100d541c00d011200c211403900d4040e031414000f16200c1428 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 798953363 1250 798952113 798952139
    0x90316140f0118111305070c05070b0a051b01180b070f0e0a0b0c0c210f06151002100603030503011505120a020f1201060503010e06040507020d0e04060b16020a 70
    0x240d0f040d0310360b10911900007482050082c44030b4440900041018124084030702e0859105441c0c0300c003c00c2c0d0820003e020083d0800c050b9001c3e003520403000f403d01c0941000a0041d02841c0742a0702c560b4030390b502d2032002d03450941c4000072040d09503180041c0c0c0482030624107419801501c0c0319001030071b442400c0c405507004d114211240e510244c408002280392402c000603a411994409809001d51081e5540c2039a83c0001e0900b84c1e03103064010f0342e5954030303025124580700240e0064500354018a04000c001e20003170b000800c02580c2a254041030001c0b40c0d10882c1043c00001c04540f5040c5031003001320901d40c3c0306001c0d5041c0c40010200c0b05c481c1d15502c509403501e020b10071031540c07032020b410009000d120403034015100a07400401c910b8203204881130002c0074a002600240300260000c0010001c1c890881d01c3c031750300100259000c00550508c848002e40f601c0300c07080540c049c012424107859042d16564072078401410035809032910307900044150210700380311070000e92080c040450301043c41840c80708 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 798954613 1250 798953363 798953381
    0x9010e030c0f040c17160201060f0b030c13090207060b210a140c100c050c01030501180c020c04020a080103420207080304030201020d11031b03090316140f01 69
    0x401025100b02840411003c0d14401c0d081004110302000e5045100307010100c19402403956040d44140c101c002c0070000d00311a241d51098488100c04030040000380210703012640c01c140821070f241d40e00c10303030000d80000001c401d91054914510000700c40c0d0a1215a50110ba410700d02210f01000070b40b018202142c0980110003480480d804c644401d800180340109502c140ca00a41d045c0d070306641c0da0100103003891214421180104404a0b800340410406001e0000c0c000405d08081003154100401c1e00e42061100103216549603442820b031800500800034100b0f210801071095513180504000140302c0440be1001700e9580b4441d00c01c02c03800340c400400c0b09100e05001e01141421982ca602034400055035804040c13201035003001002c010450040095210b46c1c0680c0000d0b950b020702000c00c2c1d00721401080b01640c40182130091210707c203403102c82e84059880c80d41c1c4554503519000900d60461040f402843c2503003040117109000c00070000160080b005d121000d88440300301c20740c560f900b17070b520b209 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 798955863 1250 798954613 798954619
    0xf21090f03090f010c0501061d010806010510050409020d0603060e030a090509040b0619080321060409200a05030607030b15031509190c030b121605041d0d0509010e030c 74
    0x40d00c007031113075105000c1c0013070341c41c09400041200c1d545d07402d40354015034158001d65100c01580c8018020210100000ba00420040da20301104040d0800010158000c1d030003510807840d00003d64508208107174001d08040c40c1c0060741080051031880c40c00d660b079405141c088020408c0b10100103254504545a070380300b40d410900000440c0c4d500800c1003040103101040c0020752064007800708150500b08050a14507041d54560640e0042c05550a0040500200380522550900101800050880f800c3d2450030458680d40c0c15824034940010b0040d10381500001c0e003509c1080200240c060f0705801102c09001e05070f600e10a03003d00312001031103d100072500b45510354a02444a80d0750f0034841449a84180c200d4003920520040c0c0d0948810b40b801116454006902c51040001c103250410180d010200040000d1210802c900b0000485c42014070400d40308642d03508000c002c005210f01e140b188020b0038800d940c4080d041846c041c1458100802490015540090307030585814006141441001c0007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 798957113 1250 798955863 798955879
    0x12020607150e16210605130b040c030606080c15030901021c020406080709031707020112140105030f03070b13030e0303030f01061b081c020412080c060c0f04030303020f21090f0309 79
    0x25182c8201810000e0042900011000158000700d0b20b123810b00341c090351046244801e001d02e1400d203103041d80c5c1c2d0394010160640000071000443d50710003a900300010000300415880b6959046254024003034030b80c8c50140035114900c0f03000480c00c15402803054170f90903100c0e0704c0c40344c64103d0121a18012030100401401280007241d41507001c400c0907101e00703441490702c81e1310001d01803060410394100203a5050302100000042c07107189400c0c0300d03042000204000540c1054110f841b00101000083c02107241c440000e000d0005044c49098803c0c80030001270101ca99030f0078250380c0c142c2084002d00c1043e0000726101d00d8000300c06110b0794106d100365003004c0d406040403e02241402e10f90031501c40c042405034200000100c540c6000c148260950240c142d040c0c940c07041003045402c080004214814000d001c02883e15210015015107003600d80600d80141c0b24241038003c03441038440c0180061103129660070250704490440d111500c500000d00030780b0081803449100e07039980d01508015030307405801 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 798958363 1250 798957113 798957179
    0x603050a080f07020a0306091401231f0e180106060c02131e0606030509071a0f040902040e01060e030f0613050a1401021b0712020607150e16 62
    0x10781d6016000494030701e41c8082c604209540001d07103000d0076500850b26151950000024008409805200d840036107000f03008480c10a40d9601d20f0014001a20851303040000104035000700301c1c080072110700144c2c500c003501143c5070380e6400c0340f0341d0086031203403e03a01c4021250382080c4010b003d00c404991140e110b607a4107007156801c20411101052200c81c0465480107118502031100b0f043e00608004001300040ba14100f0100406444c4020411401a44038400400c440e0111042d451b005115200388242c0760f400861400c00c0a20030b40e03019607001400420b0100d141180748051504903a10b1ba01c0c0c42c080521244117050301c82d04090501c0215810420000c0c1610384140340f011034070340c8a030068485440e0075940e5018900000741c5880310503907010600301941201c0d5495091021442c1004110091070114580b42c41100e908000b0302418010411408103c0d28507042c03403001003000814080c4202000045a0700e002509808650007908000000e985801c4201d00c1103800306015010b9840320 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 798959613 1250 798958363 798958373
    0xd110418022106180c0d1412030402090103020603090a0c0618061110020c010e0f070512070311010f2604021009060207050d0f080a2f0d0e01020726100603050a 70
    0xd40c5130841c00050103401244141690345c0340140c0d2405209007002100a100803c10a25100f242c2842000c0840200709003c056510340030300d6811280c0c100c90040c1c3c1c0b55070384c11140d170a2210f0400020801c5071805004941d03160030250101c070f851001032501031081d81c1c66000300c80301041d40e80c00f85070580140c0f1407203450700256002814160503600000c9100002003000a141401060749408a03801a500134095031425080d5000c01100480041482a06684580742100240c24081d41403142010042e1001400740483c40c2120500603100100700c082e071308141c0107000c0111001c130700c8bd04201101c4007217140034107400c10554160358002c00e2011b0500c410b000e0100400030f416518203843c0e01003440001c04100090140318030643c0c5190031401c4110588149400203545524800d42e06846040c1540d40000c901542d00c2403031411014080000740142d003040101d0f0031440701085840820014290141038106d440c02d001320880300e001e01b64500800c1143c2c0140401000307600920240e1010913 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 798960863 1250 798959613 798959641
    0x4020d21030c0e18090f1204081006060f0c020a031203050702100c1407050a061b02120306010c030c02040b090c0a021504030804080703030e0a030e09090a0c050d110418022106 77
    0x7105c00c011100d4170091008000d00d08044600c8403140d8000c0081e084c00b441c50240712110340f5070040349051001900b00302c0003402107070f680601d8500b00300406001c601503680b43c0401000854205050501207416290010080c04040700c02601512498103140c42c2c500880c0b24601d8603d040340d0714048a50502504070308540c2c48030005584070300c140260900031410500ca14034411440813104440c03c9000301010b41010602d010040725540148104201640c0040010160b40d0b850301e400842e40e01c2c41d10000b4002c040e0101820b40041c0903204212485040c4401090845003640840d03400f42c40c010700b44009010300300c0d0018001107030b600200f000100d240c0081d0092a20904020509040f119441340c030b080642038054000450762840c00300c52f410200750558002c0040c2d4083c050103001138943c0c1c4078120b06840b0715405411175041c080184040c5e00f50040b42550300500a01200c125601c0121095803405401da1040c8500700c02e56841c580180500410001c4000280507130713941e0901c001c8161 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 798962113 1250 798960863 798960871
    0xa08131106070303330b030702070b1b0d020106050111010203010305030a1b06090b011502061614070501020304201002190f1509060605060a051204020d21030c0e18 72
    0x4540ca50348003084116100d096885c0c0c1101c801e062603030b841044503003000546900d84c411001c0110070018046056800315554007641c0303050f0702e42581d46245000b80f4070151550b20100195001d6400c40703022059044d0400700480c0c200340d13101c2c00004e252000d01c40c00c0348400c1c40000c1072036000b0000c03004020700170080d0804100404030b4000300b041258480d0f0003925144982101e100c2800c80050010010340c41c140700c6200b4052004004528008983e00c4840380c012440500340b109038120340340062194001c032202c0b280d106000750b449051624050350854112403092560030768034410300501d4200341d4005e54141e0702982c020860a244139000c1044921200002d44221858110a034040b4602d81c100408000c0314801c0081c0c1e200090030441e0840e80150053b41c41074004011155a00781e1103410744c2d00e0241c0010403c82161540d1002644071060300720010b04e1018404540702d42d90f508160102503000b12a28280310140c1421011180a03900f2032940b40d003d0300d21070040c80070340400d61400b0b0340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 798963363 1250 798962113 798962117
    0x609010f0c1d1f0e0310060e041b150518040c080103060e011d0312011502120c210c061003020d0f26070c140607080d06050a0b0a081311060703 63
    0x368000d0421103c01d050041258900801c25042032a00c00781001c000e00ca011580e0740c1070410119042020201c402c41002d0700107012510729280f2094003007001c00f1210001c0c412403c0110703689441c403001900b103810255001c51108180940c000246c01e03c6c0c007603020003480c0f80c0c1e1500340983c2507958090040408244d440415035907a09120880308024440c410075000d110001c41c1c6418604880d05220b010503044038446005800f5048099500012046090307440104c0e42504d494060400500c0e000401e08014601e00202034500c504a113440002c0c055000160143c501513600c01e101d904141d1078500c0025008000d21130030a01103007101d50780c502094410325480b103284502003000d14800f800704000c118281d2001940c1e0b407c115810031070100400d89aa8844a105610030001e4034502034503401074507685001811710f06200c02c4c1e03441403003e48001031042e40c50036142d074510810b0341c11030585100400c3c092404a03440203142c0c0c168840d559440b840b048643c1640000b48800c54225601c1101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 798964613 1250 798963363 798963379
    0x11401140c010203040602030a0e0f030f07050a0c14010801140901060e0f0307060e0a080c0d020913080409020307030e0115090c0201180b090717190f020405090609010f0c1d 76
    0x20111028001180546d0140c0c001680740c1c103100750000c088441080c0a41020fa00a0068420450003c0282d4a0785a1001090f13512400c540c207105003054070388513004000c400101000f069140e400704d01c0f800840000c1c0d0b0358800c20f0fa00c80204c41c28120340f03050040e51000041c4010403006110f81d400c20f4510724040c041c0c020102509000c40d10b06249600483c021800d0031706a0455400c0070004400100300c094000c2c903000c00c4110110b00c00c001070401c044d0060144400050301250b0b03240510404a90060101341c2e40c1c1c0e41ca222850094105951900000782000e008880010050240c0c3e2035019008854000341464410500b005000002c070140940d5202d0b82d8840501280c2c20f00c0d60007860061001400601e00020b003903041c052260480349410940754010a08024000b46400c541041c000039100440254204210b40c1180e600000707501c142000c00304648007030041601800b40020900900682060310318060644030b42c0302040d030000d1881240c4d5032145075000383e03440c0200c2c1c01a10180d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 798965863 1250 798964613 798964627
    0x180606190b16080a113007061413031e02061611010f090210020718020322050a11060307051e041a030106090f03110402071407060f02100501140114 65
    0x40c205420908096011032404903010b10305d40e000744050b9018070420380010280c074281004900c0480e0b0348a110340340030031010880000b0494642d01009800068444c0321005160418050b022030810310b600b180080d070100c1c0c0040305003001c44c40d1b5403101d01d181d802510455644041002d214090407940b9401c000d004100c0488110083c0b2424039100d4080704d0120748801c060051040c1105160801021580715800c01c02c03000c5c04051140c42c0c2e041e80d0460240c0e89485180c0144000900507480342806110700d20100e081007000a100c03107025100d90249500145d440081014a0104441d4100468410407c03040303115030406881c0039000c080b004040c14039846101805103840881e4840c00610781c00001400400d800103400c600801c20100540c0a490540d510025041c003941400340c061500400c81c00708016520114400d0051900115044550f680c06c0c01009060701607017280150185110301090f0032950700031141a6044001c1c00b0781c00c84518001154492000140c24400380010302c501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 798967113 1250 798965863 798965873
    0x5190b07111002070302180708060d030e0a0e0105090708010311010c2303040614130603020304020303091f030b1c14030403060e0303060a1203020a080307120203180606190b16 77
    0x4050302080c075402401045e08500c140031440840713650301c6002d20318001c1040100daa1100314103511000503161540446060301c0c0c15503030b07100c114a103590b00c1440b079000032446078620005103040300e404135040440381d100d8500960b84030100f17020141041580100203445035004000314a012071088083c0c81d98141c80d6541000d000d105c0386040d4050b60400a020840d00b0741c840c0010090345040402c01e843c02c09a81105440c1d0700191181205040d0040009001c1d550140300303803010500040d10060b242081500d0388002e56243c0d12014000c40c1c0350420700301d0241001900c030104485065511205120340703890f41000100183c0c2c0541c0c492108100110003c0c01c01e000f5001c011018200039922410710b034040000c04036094014100c628503145144005c40d6000a0040c3c0d150b412848840c3d40351039940d030448401700704a01c08108580004107020205002c0c812504409911a080e0707a1035482d2b140c100121412001e200958014400b9000d12848050900410f8a4104840244c071018655551 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 798968363 1250 798967113 798967129
    0xa09090209030307080f0706050906010f06030906020f0706090203121c110415020106081b130b040605210c060906030711010b091e06102309121605190b0711 69
    0x906c80c0003038808035158007000154091aa004503180025200b0f0350305000f084142003031a032150004064031076444c28223104c91907044910007408500415a01c000a080c800d000e402054000c030f01034401c2624203c00e0801d80d00540d41c0030f25919101000100d80c4541e26800351208400011200a0401000507052601800d405000241e500003042c418608440239041c201c90030510460300827100c021381c40307a940f0303500703c9501e0004002c0300064200e00140071400425a07600600e420880c84940031702185009070625221002d120205d42024001905200090140d403d04030303003102c801d1000c54015806108440040c900d0103000060f021049000205000300c1510400898690b82070100da20301d0002806a51016040e241c50702600345259000b05520b1804243d00c03c01098698840d0741c20021600304c03031030290010301d0103d60701040310f8019210786070081140f50180745403000182504000c140c242078041c00f000010466840d013280d4201c1c943c4078000481d02940520400c406981d0741003c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 798969613 1250 798968363 798968377
    0xc04090204240e060618040903140a0528200a06051602010b0111100c090b030408040501110d140313020d0507090f050603061605070c24050a0909020903030708 70
    0x185002c200c625115400803002005007034503008000420103100d012002c001c2080ca1801e06032400501255076040c1241c0340048400c12074100800080d072219030030b0384803000c0c268250804001400442c1da0484a080d6410b802010f08046040b84c0c03818000d103c41c0ca40108048500c09040e075100c070701103a030b030142121300c100d48190b65441e400d01c204000715030912680c0c40c0e500080c00d1143c9801c060396501a80c805804251801c800e03200c00e40484640e20800c014002412418603844c0c5900b0103203000390440e0440d000d0744c2d000030000c040d007483e013520020303103880f28080d01d032205107448040310521821544001d00c00752400301c0124100c00140ca801c0c41e400800c034021005002190f003407000f40750079100e43d8810b10785138500b04424400c82c3d0360003281c81900b00c0103024040c505030700c08a0003543c07103000d142400381600342d0343c0f0000981200640030600440101d8a0504128032484405440d00d0243c070503400c000035100d42e414044488941c2c028401ca2078010105ca0804401d9542d4100662000c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 798970863 1250 798969613 798969671
    0x81204050d09141f051b060402030c09190209010c05030c01060302031e1b0315070305070f14030f0903040f081506100221070c0e090607020f0c04090204 67
    0x40700020050741c48070070b140250281e4610b5440182603480003544e80480c03a03282c180c2d8403510900800c115030090341103455001080500328211508241d00e40d031180c0d8101d40aa000b401020710041c11403420003c100d104203650395a0100d0004640003d10094001081d03250600650b4400940410001c00c00f80c2119001e4000101d0b146080d0b1040c0b60914112404080c100c2c0c84601828603501d002040b140c04142000100600d06200c1c0400a07240400080060003040f40320018026400c0c3d01d070b00f2042c400c000b980c6809c04028450300044661407034411002528103001c1c40424140a00b24038801c0d0460701c00781c102c900b0705496416241c990301d0554029102c2d603005040c00144c108032054250b40c4207600300c44031000a590000d0181d112410452130004041380c4a00e502c00780031440d816103040d96084012003410303075260200728102d84016a4841c149101d25400500000d100040d02e120060244015101c281454020b2101a001d01182264032076212403008609405d0615145c250300d00b58 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 798972113 1250 798970863 798970873
    0x1a030c07240f060e1005150708040b030901051b072303030c09030111040518040309150309021e0a15021c0207061e0f0e180106051309051302040908120405 68
    0x8441142210111360014400800a80411900d14501c41300c0d00101c0d2804d4604c1c4500044046019a0a03c0f030f482c0d008190800c00710340451025814000340d8850b0b851a00200019100e6070031040f10401c403807161101382e207010071100c4000343c50ac02c05d0015802c0000c0401c1c0300c2c08004ca1255081d80c000700d41c980e10343d0202040f503514a00e405d001e4052500800c2001702e00e010304220100d85040c0d05d07860b2540103401e030031012804252003001a000101509120988601c500740d01c010f011744810041030b0711541c414075594032034080b92800088410360040c101820103240000d81c40712803c680700080e066000301642c0110300e06c4010048d05981d102030340a000554100203001d016540c15101c009101001c1c8440b0403202504202c2801030007106041c001c00550036080003a81103542c1d6507417030f03683e03610b40703000010302c1c541000182074026012004182010340713480c01d803000c0312401c40f0911403940450840354098105a48080042c030b001d40041c0f46000c2c1354401d01c41c143c032804c1d1000c030313039907408 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 798973363 1250 798972113 798972131
    0x5010c180e010e010306020c1002130504050f060d0b090f0105010e070f08041a06041e0b011b02010801030f0219030332030732070c1a030c0724 63
    0x44000c0c5014000d4103101c03a00c15414624848941c82050000610843d800110010704c040c0410400c46c880701405029540c0307031a183c0422402203040d200f602d000701e00b403001140e00100d51040d114072030407014001581aa420782c648074420030000c1d09801042c056400c421103011420f0003200c2c040c0198060120765130034115401070400d440400c1e45410403506405020000d2a0070032100c4003d507460803000030359111702000400401c071107512201e03039901c4a580801c64800d80d0304a6200c01300241c0390440448082202219880c55813030000b400114442c006100242e00c810806240c0c90000d044409010700403c400498910150020b50115118421840c1d13401c0141004d040f2103220b428070420040301c404d00c4903666000103404041400500410001800514841031202c50440e5900b0020b1019443c0d62108a038003200f0180c4090401103008503100c13a010380c68a0034104601501c0346103a5882d40b5502c0c1c1600841400c840c1c2c090890340385200c842443d40e0255451801c041c00040230b400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 798974613 1250 798973363 798973397
    0x604030804140105030c0403030804020a23100207120f1b060c050c041a09071206091a0301060f06051305030703030807020c0d0503030703090c0b0705151b030c0c0a05010c 75
    0x705002c0c40d10304001e0208100300c2000e500b001501c1c2100ea050800805c107031560b2000480c0c0d03120030f40088110800c01c80e86101075800e00c0400c1d0389045030a445070704044001c00320803610340c0c3d0a030085500c1e440c0004ca0040c005002895100311103805066403d04143d68103401400040b03442e801080011035111400c01408028001044c2602045404010074099a080c0141141100210038403c815400000c1d03015401041c84460040000310200001070710b440e088001444140c058001d4080e03546051803203070030148620002d07501c0166845100c60321740708045410b94428403088a602001c1d000004690310108441030245200b5102e210052a12070b20092401400d10f2000c1e20520300c00e524039011074000b1003103135000010f40c81e02040c00c0d80c0c181401c034107202160740208183e010000b14041404008144050041703c00c50180ca500d8866091080c018801c1c000240a00c42c403c0010444100001c4024620381d014801903d0680e40c036a210f582c01c54070768541e80400706460483c4500d0341d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 798975863 1250 798974613 798974639
    0x2210a23070314071511090406030b070e06130506070507031e0317060d02090c04050d0f1b0807060e0d052505030d08220c2c0403020a030f0306050604030804 69
    0x41443c1503402e040c9a51110a044589101c084081d159255408900348040000f21424041d001c0c00c00c0c0040d941e02d1814180c1c0400860340d2400040141e0140b21240c80d002044440d601041000d80d10482d084c00100f203d03a60021008032500d205500f000000118100d442492541c0050078501c8403440608010344165800c0c0a01c10258004108201803070742e5012403084a2074058400304441d03515000002d0761407080c5d8205a511240180d24001080118080011014480c1c1007003190400c81c40c06624400b02c09000c0c000c0c850300004401d00032513102e4560a010103c00405c4c000b903080075074881c01c3c107040c00412000302d01244801e1034a4001207a0034030a0080100f03900230903c50340a0680181034200c0640180c0c94030780030f000e00e41b001c07640012100a806c4d4005c007a2810362542d44480051000302c1d003200c1e0348000003401c4d102c40344100c914042da2103213800d500078007801c2000e0340d8119403041c03045460805155603824049001d8840300007600145201c1d42a10395907501b41455200c00c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 798977113 1250 798975863 798975887
    0x25150305010603051612050604150320010305101a0708121501050c0c0904050106051809011b080c0c1606120b060a140d0b030105070c060c02210a230703 67
    0x282e60317002031010900341d1001312150141c1c114100041c1c0c81e1030b0780c00014007800306403020460801030960040184909900004044108a900e4500e408901401034090313500444140000c5a01c4030b200f00100700c40b001e0400e0001c0b603407a00c0d07286803562940d87c00020760081e603071900030441c410041016605030509400440c05007400e00384d0900c0d8400000035510603404010758000c805c900081420440309411020103898010030040d458180c40d2444802000c00312903140b001d60a000c94032481c5040340803220f032602c00a03566400d0560352400038100d290700898101d101482001e004000315000d041600000c0d103c00d0f502d41303042d641488201000d844800080d648500000c000c11840590000706186e118000c02c03180c1911249070b41145401410081c4640d9015402c00c003c100301e0030750040e0010303101ca110b00c0c0100192510f00c071040f039458080c4d604849016181c805c0c804030900303009014106500407071400003801032400c0f0300703030041100040b024012800f020070080300705500076a5a00070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 798978363 1250 798977113 798977131
    0xa091706040b060607020d061a0a0b0703021b01020c040c02030426210705030a0905120c0f1c02030319091215020f041e05130e2515030501060305 64
    0xc01d040649034606807450141801c0c0c82441c000819108640390345a07048000d0f078104000708502028001030b01880d8144005044c412038114401040e02074103001510120354050340101012600c0400406104041c0b2410034194030485510028681d9a401066440c0801d503000d1a1075516003965103000c003441d021806821540f80c1c00d0701c081030310001011048103104100454074226000500f41080c8600240074140d400005955080340b904038070600c04948007603940180050244c8259600c4001a0072400d41c08820040f10440700d26003c808041c224102200c00c462503003a950000b407a5512000302e00c0300c42402c5070222072410750490710050003051034012a20503c1459230f510284000762582110071280e02080007841d0403041000d0f10040e00e01c22501003414401400580d4000c4214411075200b4144481c00661041e46030180003170444482c8001d200c0341c4100e1032a0421501480046240200c98200015000c1e029000da40c24030081920006a02d5050aa00a080c0c0380002c000c411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 798979613 1250 798978363 798978373
    0x30a0c140307270e0d0507050c06120a050c0c03160b0709030c0621110c01060b13140f04020304031d0612190b0a091a0a1a0d110a0917 59
    0x402d09000840703000a060180400d42c0c1244200d01c1c100007013a07114495401c91158682e052009034114000305607041c06817084a141070056000c110584c4140d4450082440e00c01021032240301c20350300410703003049200c00300354240000441e82d580f464008e140e9003084c1c110040400c5080c4040440c03a250040011315002c64454116141e50043e00c00b948205030030011500c900b6482c0b000015040e094000300714409101800d0540d98080d0550001c0c45c00c940d19501e48a0000748104c40841141c0d5007482c0310700d0746101580f0340300c140301d40d0a00110f02e441c1c00c0f03a5150b042c040e050782c403032005520652083e20348441c00c2b881400002c8620b801d0020341030140c0d1003081038805102043c00c5d00e552110059a482f41c04190b4108450b01400044907450341082c0085400b284266150b00305440d03080d010751144440502903c2080070f010700611038480c407581c07800002c90403c1c0841d00140300700342c04000042211000d08501c015568440c1c0c2080d000101329281c1404080350085c1c992042e030720008002d10b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 798980863 1250 798979613 798979619
    0xc0201020a0b090a0b220f0c150801150306060e040c0212070804081005070527090a02180a150e1908060115030509060f150306150109320f030a0c140307 67
    0x1b9468107201c82019045140300c40750390007088101c1142034081c101d510f10800d00e600d54180003a188030000c0c028400c290304060603145415104e8800ca400310ba240d0364813160700103880ea00303102c002d003a1030003148110b01465100c1d0014100200c010000b451050320a1a40d691405600b41e00300b00c50858260500c0d401d1000344540b90754414251030300c4824034103101c215160320510020701c45108907111a04181100308020a4103042c0c0d0141001c80200341c040020310200e0010444001814000d03c0031015071410039000052080740c64161441000e8076080808100700c1030390f188000eaa40c0300070015444200140103004042e00c5925115001d8103040c00f26081109030941c41d41801419800520124000524a40b08252401040341400f074143d03940b50508508140e034200120b420389000c41d5501034006003031005034a03030400825130109100341070a0f07440c040d0000c4a45400000358404021000740200e60380c280302c02c82d0024480c502041e802894400005100d44810f0102032003908403020070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 798982113 1250 798980863 798980911
    0x71511060118020715050f1f03080c0f0a0c0302030c0d0f1209090c12060605190809100e160f050d23010207050706020c0a0311010c0201020a0b090a0b 66
    0x35041d80d0644800045094110000300000c0c0a8000c0c045c0800084003d4020185075130b030f10440c041c20340ca0071128131a5a42090020f1001001090924a200160000c001044281c0d0180012901041c140c6240e803080d44102d52078034400074070a9a104041950401c1103207410400b40400d50400e50701941303101307003e0300d52100070b21413910041c007509001100300401078450202c3c40c018040c544000c21041c2c5002000502044064028007095494441c0100d080740c0a40141c0395034031124001d50000f04003c0104813554080034155203258410701e400d1003400b40460184448803800c000050000414032284105801ca840d440079840141441c0d0900c40b50301c0d8003034092411078110460700b21155048a41902c6075020803a440b006500c08201c0c0300c20084082111800c440302903007252202c00082c004c01800001511005003550403440b104180d80d4041c03103020316503d00500542d80400d0701e5072a00d0310308440445034100f15401a800309020801f284035002d400108203041718a101c47c8682d03070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 798983363 1250 798982113 798982123
    0x60e0406020714030310180902030303130c270f0605100c03020c0a08030301150503060d1709031c032306040b270f06030a0b0f100f08071511 62
    0x800303040d0a8000039101e0074801500720000000600714201c0369a454a64502d41300d01c40355000358040300f0284810044880440e020701b01b9102d4004003d145991944d50144481d9005143c2c11900c1d8010b0b010300169842118501417181104844900b00c0404281414070444404003000c1c1300d224a03040382402203032255500d000c000400c40c20300b54a40810342c20280d1601e521449690340c0402d0750100401d0400010001e18103c40644110600800f001481601c1c0783c0000c039482034014550000c5640401d1040950a0140c492502101d14002c200c90119041c0031700140c0c1164094001142c40f400700b61b0620070181d541e8101e0442e680784c040119512400304c44081c01c0c0c14412522000790300060f580d03607a20070100c07000c02080c140b42c6103511044003520010450707941e40071511000000700103040c00300d40c21030f94680c8002d002400d544d03034500102400101401c101d00c02000c41c1d1021500c1000702030700c40041c0001400800b03820340350038420002c26054144e1714082000b007a00643c100080018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 798984613 1250 798983363 798983371
    0x1030501080607090509100e0a06090b06030c070f0206120709210503030c0c070b0d060807060c0506040b1518060a0609061409060f040312080a0b030d3c020d03060e 72
    0x4096401e0384a542107c0308040143c0c000c814051409401d100d410021603000d582200c20400042c40002c480d43e003004207900044580103078618080103180c00081442100c405c007079100421483c1401c5402510462480c411a0003402041c0031030014400c040c2e040c01c1307044d4940301d52030040090301229a60107450b0b0001900045a070790f0041020304222500780032035805030019030000d984906001d600100070344110b1141510601690b00f0101d40c851040811104454006c0c0040682d83c0f00d5660321a00c03010000e004422501400174504500c0e6240360310070b583c030b030104420301103035007050010010701188640c00310050100c6204200b02c0d0503042028200b007602550405515203507e00d000c604c1314401c41076000c5110744001400702c10400217900b615008401941d440c907032507a841441104807160608040d5250b84410a02c0103194420a400305c50640301c08516002c1940325122183c1d8482c1040921907021022b00784100c0880c0c0c10040402d04220038503060200d2882c10521030920140a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 798985863 1250 798984613 798984619
    0xa080a030305180f100507080c1605010b09100305011a01090303110309060406050a0e030d12020d391d010c06140f010f0e0402130b0a150806010305010806070905 71
    0x800182c0f04803d100d2000e140f000e58000307a40c451544180c140c1d444000c0030105e42682e07407030580440e007500d108000c114494008040310506d00f0410091016544c407025500310b81d00d40d00e404400d0b00326181d09184a028280100300c0000302c0d401d5203401400d450f002200704044080e42c40c001e4080d40ea1003c9200c0c1101d4050810803100155504500c0c114441c801c01c9a800170310011703000411650203002408080c0e0076a850010388228034003010303160800c1c000c0030000100280070b85034040340030b58000d020f80708005500045148982070035047d810300240a141c3c1000740c0703c08002c2084030b40e044183d00108546418414095040004204034000760791003030412001114a60400036181c0c40101445441c108003c010320303024030310341d0a002c0c0900901c1c10203881c2210028100702e02e100c0b0745004130741c0281b1501c04403500d081070f80004c0040f40500340e800103081c4000154900358000704032503841959600c04a5203041e00024081d2081a0701c51585a03102c6010807442562040c204400e4540032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 798987113 1250 798985863 798985871
    0x20f01053903070f08070f08040b2805101e0905130f121101090b06270108010b090f071d0406090e06181c0e040f020703050304020306060a080a0303 65
    0x104968500c6079a01000000890000010711419030b4108541d916240d403590340d0f8607510751700c3d6502100c074044a410440c1c08109910301140001e1003d04003160710098400c09114104c44803c1d00c1550003850309910848580e0369010701111800350041c0300068107502c602400706264410101c2d014040390701c28070000d19900c1012450000c6800e4440c1c1405402c00c0f954a5521203a040031120142d601c10301c3d001060200c000c16a02d100306000303000f50b003a0080d4020042e0341c2c80c1e405024018003003540340603640d0741100411001100007890300303020303100c228000500d141408062118650000c1c0c1082800701d0150100110282d10880c90910300c3c000c55048030201510f140424050289508180111800d10180c02c000c02c40008101d032081800d040f1182140c64140712154461054130401d03074048141c4044004441d000f0312217003083e5600a00700060002c0d90b140c8403000c030b8112800071000900000300384425842c0402005810800c06c4452904c0036140800d090382e0b0f110b9010b801404e05440d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 798988363 1250 798987113 798987181
    0x607080c070302040f0c12271401050c030a0c0c08090f0a0f09200726040815060112151a070501050a02220b0409020d020c0f03040501020f0105 63
    0x7403190034001c40c0d002c2d00c1030020380d00e444882d00c0035000f40301901d400500801d60b01170344001ca034003540440c40140d05000302d184420740c0710400a034150040646807442018103401001380709102d05403041030b400a0f1180c40c0e0500003e20416542c403a00714208000540c1802d0b004540d10000b111041d0a0840e0219001c00b81030000c6080c8a0361a032085c06000c0c111500000c030b0042030b8000318003042d816040c02c03424000da080481c0d028041c062000c1d0030441c00d55201c00200d4096035022403090403680400e418180d680300002d141c01801c480180150407060705015155030051210b242d01500b01c1c4e801d100108110b00b00c004480304030701c0381c03003101e6080c0075030140c4070303c0c0c41c404649516402c98024030a40ca4408000070180d40190080c01f01080280d02c420f0a002c1c480000106440803030681070321f058035210601c1c001e074000389001032019501f0024021724000030060008050180301c003558440d490800060701b801011340805500c2d90500d020403800380044400103101140030b0b090010302c060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 798989613 1250 798988363 798988387
    0x80d0c020f0d08160318060501060311030c040905040219060f091514030a270201080c0c07060305100e04121101060b040b0f0f041d10031e06110f0304110609060708 72
    0xda8520303043c0c1b50306021060600809070000e44c180d43c0700d40c0307050000541d90030820000380300454134644024002d010510003002507401842d00640001c1c0b03240810781001042000e100c0e80c03640070308080b9846410b910221034118503008001c140500d0351034030a01c80e450004e491198210b200c0302201800000042c3c2c0002e0940c400341646ca40740d640100e0040e040852a042e08448a000368007040c50900054903241e00c0c14200d803825040d02d000b9082151401c2d0f400d40c041c000140424110b510308c0c04011620298450000c0d200d1070040c1030354403142d0801d0074040c094070390302e8410361000d03410a40305104280307808080301d00701c4604000540e030f10f03051170090f241d060040c84002d28905c040000c000502403100242050031288040c17001c0c00d075440e0030168440c028040d103c0109403d5071007154208961700720440404160007090041030035030041043c255103500002c4011501c100c003005000500c8548425041002000d40710030740752000003400107500b4065060001c0c00341400007045506c0305 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 798990863 1250 798989613 798989621
    0x506091f120e0705150703050a0f03060e090c130e07030b040f06050106080a0605041a120703022101060f081903020709020d1e090305090609060403080d0c020f0d081603 74
    0x30115810400d0301c0d5030401960f100c0c0c00c00e105240c0301d00c5505d40b05e1101c1e003a200c001c54000980c982c4410b131408400711002d40b079503102078080f0303024180ea0762800a0302100348141280309025001c00780c0815801c2c2400c00c08484058901200400c0c9000c1d580400d074034000440300103a9400c03484903502555207260084641c00c03c0a070003000303d4100400068819002034406004903c9890180071180c0c54100f400300300ca42c80c091800010020803600050350400d01e0008601c040540c0a0301e504e10f8982c2c02054121380c04211b1020007581290100211060a10500b409007032a58044002c1d90300d01090203650303002c01420300d01e501d013554465004143c000c002d584010310700c05034199118601e5480309401803030004074001e60700e07100c606454004040d52144c0140f140d455101c81d42031004003018404160800341001380c00510800010006c074500d0005401d41c0b1510307000108110940110007418854074441281440e0300107025003541d140c02076005039201c030744080303660450002c05508030090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 798992113 1250 798990863 798990887
    0x7021e03061503012405032407050904021308031c0e101d150f280e1f0b0301060b07030e010e0109121a0105030c0f040b04090b0c0409060506091f 64
    0x482e01070308082417601810312160490300c04800b600c00c800740035030b070042042c1c0c2d40071141c203618891800000c51650044018040c0d4500160005003004c010403205000403401e034104115540c400325031000d0080d444440250a04090001030156542c6071071096500d8404007455200c0540f00c03006004151042501e01075180f2800342140c140380081c43c0600500a001c0c6c070000f003c165240c000600c981c002c0c0305c1c19280484200200303c242da80000f5a0f4009040134804400c0502880824028007403864051072504031081e40005090240c034401c141c01c40c0c0392030340800c005030424403505011030340003520b220b041a00be083c20341200300341400494200403150031001414482c82c0c40141840200c00d080448010400001e8584d84d0300d407070805a0700d43d010f42450307902001c8a61144201d0a141e04003600c110302c0608040703100d80d065504c245004000f22039840c2140c030045400c0042d058a4000c0100400003502d800f85414015000314004614034012405200e0105002c2800c0c98401e44a030044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 798993363 1250 798992113 798992141
    0x3030706020904200403051b0904030c03021024091407081009020c0312060306010f090f020f21010909030905040209121002040504060e010b040e22060207021e0306150301 75
    0x4100d0800d0052204e0740081c001030384d20f481082c00501c2c42d01107801018162039401000c0d107445560300c2c2e400f151a607403400c50480440c0a0078039401e48202890007442c1d1152040070614442c0c0d1070261080c00c1e00c9105a2050203140d08202041d1210088480c415400692500e0880666074810250500034511584044449840011100c417107190120280c0f1003466420750307012460321450101035a03031390203004d60003075844064003c100304d0009a0180c12581c01c02600582400d80795075840c1180c0c0c0200c0c403450036440c003149444459182e11501c217405030040301c0b0b0810140c04251002001c3c518139000742400341da80080c881e4484e980c2d07010031594003400e110455031495411040b180103034110303101d01d501031401c043c0d001c5002649a0804c42c180e07030400c9107060a051408501300e2041c400505200b40b01d0301c10451940010250603540b02c42503000302805a620703403007441880705c603c1c06219280b103144541401120709035808500c05030003100301e5055004068014000034014010201c401c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 798994613 1250 798993363 798993401
    0xc020724170a090c0e22020f060912010c020d230a05071b030305090a050405040b04021c050307050a0c0608040c0605030a060905010e06042306040914061f1403030706020904 76
    0x45103d8040ca100d03216510f2144403405170032002c506540785041b0218000e40c40580b0560f15511408c106002c1d220040d0000c08002c7d001c00c01c10700b111300711150000c0840060300850740903421640c015100303200f1614500401000013012600c80005401482e4071001080760024150051140c0410f21a40400d1b0141e42c0f041040e80d203150280039a840414210302800703c0c03035070000c0e00740341503c650382c85030742c201600c002c060341e85608004120114055040200c5201e0810b0004074000b0006081d03030b18032400052008980b50f041c400b80503583d560040e01044448010400054600205001102c002d41040c03a160f40303031000150f01414240e0800b50480b07103040c000150854420b1040307405a102910104004400c00d148038545414501500345480304110106a03075040c80d07880740030b4060050403810f66518600341030720704040081c0c0318090f040d41c540241110b041c440802200040160200000c2900030400202c2d0b1240030724000070307001302e40c0031500c03250710740b01c603004804610303d4045d0000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 798995863 1250 798994613 798994619
    0x10507030908100b040c020a0201020604080c030c0f0a030201060909030e091503190209010b0406090b0703170702010c111618020708040b0c120403150e100c020724170a090c 76
    0x5002821564040740c0701745c0c10003041702d40d01400400c1100c03010790180d010784640e0360f032602c4c1c001035580b0803034203030071644410400f2a601a01c10f001507000184800701801e004140b030300300282560b00a4000b2201d11f440c244072034001a4000d0520029160305a4084015680e00d2001e00000e003900c607071194150049003643d13001c090800c020104400d200303d5125042c1d0f40c035403011a0041c019405098049000120300380240712810001e045c02c0c0344286070a404841c3d614042515007082500d8601c0542c0d12001107950982e004240c1071510313551540203041c28442c00b544029140010300c03800014005003850000b001649404550304290400c00c119500c55583c0064840760340640301c0d55444d0300841e18000000d200c3d203c2101c003280c7d044a800c03200b000411a8103001041c40e00b16036546445210130305440500c2501030b41c4071100070762b00a0100a45070901a40710040307034007550000e01858035142002103401c405003540c43d00c4040b00300c040e41c0c0e803458030880040541d024050104001a8800 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 798997113 1250 798995863 798995893
    0x306010e0f01230702190b040b0705030c01060617060906010516021216081e0c04020d09022d01050903190c030807120e030114041502121302030609031602010507030908 74
    0x90415510a560090520050710348141b042d118034041c0060b1540c080104000c441d0b460005001e02e03501640070b41e407408008000040c01c40780e00340c0c4450040b03096241100c1901e200c9030354041d40f207481624040c0581c40d05100007440391280594452030000c460b91042c05644030742e103070b41c1c10301c0c01d071790080b2141380e54546000036015019201c0d00c0342c01d209020b640c004645070381e40b0f080841c00d01e071801055801000000c0101940142c81d90005451750703640c201000d81d80301d0710707554074124410141c242c0105042d009810b0502148007494148401004081c0090f1000108102c881e031003180782e298900c1fa82c1ca04410040c449500c050140500171400900780303c40c2120202d400d00c065203e01394072070354a90a141c280e0b0758482611058421440024000c91802034181c0301a0070703516801482c3c00b10340070b5941c4180c4016100c0c8100c020b0030784511001c5007010406280c014201d14004d5042800c03028003200103481084009041140c046520700c10940180030b0700c00034086540544140070700740440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 798998363 1250 798997113 798997117
    0x303111609090507080a0b0c18060d06050a0b0f070b0405210d0c090605071101030605040e06090c060403020d15020706090609030e01050a0e06180d05030a1101020306010e0f0123 78
    0x25151402552800280744d0000640c48510b00d5100c0303c1100d055823036462040d00c9801010000070a80c000782d024142d10342d52400100000890f015000409500b02400d00c0100d00250b003042580301c40c1044001c10422102007a0780040707903c143c404030b4a44c0c03a0300d80182024508000c004400311140035408915420724003500c0e03c1824070004205261000d08c00320b1705035907a80b0480c0041031042240d0004514440080d45515806040c0401e40c4c90b0340c1c0c004a4220b460040c00076800d0303004070302403003904501400800801300c01216414141070641c0c00040e94120054001000803060242c6101c0101c92a0113a686490700004c0c01c1140710110b08005000e07110281046002078202452555198000c03001e0b5161032038540e6640c01d0790b5100c00d060142c01d50107907003407103910208071905d48510364a00020802e010320800155496900c41c0070054401601c015540b29582d0040c0200920791b684440940c8900100f03c4040503001c15032001601e0500038481e00c460718440f45910140c0d84815540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798999613 1250 798998363 798998381
    0xc0b0f071b0612020c01200c010e2107030e06180315071d030c0409080903060a02120f060f090103051f060f0501141b060402040b01020f070303111609 66
    0x14006070400708007041000841924024400454411118104641c00d107601600d4004c1130304000061181c42880e00d941c03820390002034034000070f500094681010400307001c0d868001060740014141544a805403600014801c40030840451012403060140340c0300b60000c540500d40501a5942c480b0081c00c958031a0700b021724a02d001c1c1c4121200c070302c40c0c590011090340c490419551a0894903250242c5004078403200403841e07034188251344030741c0c400d90744a22035550041d104201031640d4400c80000e050500c54000c19141c0041d2044c000603005c02d4251007040e038820b8032107690611310790340e110000300c20700500101c0541054181002004100000400da000700000131440900c20000e40c080324203490071070064441180d011042042954055150300c2c8804812150690410109074100545a20100000d0703916601620910003513060611034400110400c1c03000d88021010307110701655814140c40300400b0031180040d003003880c00f420b0042c1009044512011581c2c19078a01030003001e081034031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799000863 1250 798999613 798999623
    0x20108060904020108160c080c010b010801060504030c0b13150306060201242c09010b0a09141602030d1109040605040209100806042703090b030603190c0b0f07 70
    0x540800c440345060741100740b003107605964520480d95455904581d8030401c03407948080c0701001c0c214000290317910019140034a101d20000500100010006100c0001039001c80c0600c441040141301191750071070035106803207104998668428200050500125603035002001c048030a40c1e0f01e640d03d5905070860405c40390795900a1140180040003000740c50320040260000001c181da0400072070114950322051b00f68100031610f111328045d40e2001802d1000c40321040d07240d41d9412301c40801d24200200b00040c201940c400c0001d008140a46100003030043c3c61418401c0020801c0c19002d44200300b02d6040d20f128140921a404402e60342000340d8000d1340407203204508207000800d40c2e040034401e42e01d80190040600010381c50a1005582a8001514590b00280c130344010801e205142e85201c0749000e0204050b5007081c000f4100100001100c5e08040c0308254104103000c4650fa000034080304c08128800070040300840c619003600368500c15400101041004150181040441d001602c4c2082c02a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 799002113 1250 799000863 799000877
    0x309070801020a0504140d1a0907060c1a10030203010204060234030b040f06020f1210030209010506090a09141b0306030a060f0f0504050f0c0a03020f040c14160201 72
    0x340346503400c0c1d000350300380e4034000b85051004001c0c003210007000f450384610140c039418050100c2e403a40311301c15841520030052120b0080c04d04c00c0c400002c00104000b48103620344081800025902d40c0d841801d1403040070000030800010940000c042801c010045034000c0007195500d9503441e010351100c40031206842c4c6981044000118030014000340044591501d000d00e0b4003e0443c0e5a0a900400c0a0320a94131155007511000c0020b50f10b10080c682e03030b080f05480d251a070320300b4500d0221200e40100001410b01c4640001c0005031128407007103040d20740840c1d9040d1540804004a000c1a60b10740c0242c25142c00c104131002e0701d0801d030311281d0045503401030114112000c0001c882e902c1c4410740d410340d00f5078020110364020070720301d03400340310100e945034404500451007006a60541d84255010b50f115001030040c0e0a20340801c014611540600f980c1400400c0e1030b54001804a10549054500131621403e560b85150700c18010041000c0424100c80c1d01e40c100014022418590740b203089011481c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 799003363 1250 799002113 799002119
    0x20c100221030f2e09060e060402090d06020c160927050c1c06020d0c110a0305120903091c020109090513030c0507051e0f01111e0c0d0305030907 64
    0x29882124890880360820024546904100d80c0d10348000502d4065461207a04c0c2180c138035010981c080004001040c000300300340b03050403c40980f140025054a1045104010303c0020340c441d401c0040d40b848e0040e40c010386588600300e2003030a14500c805001c0f44900030210114a42070340342d00c14200404003018840b80840036148030810144220300241c1390340c0c425481c2081034a0000541c1c00442e00007400c01c0d20310b080e5079840c542640c000d1804204010b40b0307164010222035000c000d40404015050080c071f80106d280d00c0213842445032507440a0246c0400001400c01e04081040b11601d0b0806048001c1120103071500310300c4403a40540490002d6004107000508070214010a40100c0c968880e00358401d00d5070b0b80665074980c84c010200d615000d440d0000845076105552600e03e0710840b00f0105068030107100300410403203440c01050500050005c01c81d807161000071109601300c4201c1140ca6520005070803549031130040c03501280d0110300014074408059005004d1030150320400200ca1502da1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 799004613 1250 799003363 799003423
    0x305160e06031507050f0406050d11040b0a0507170304050d0e0604050906010e0a080102031f05030a051908070506070c0501051302030c01050a120617070911120601020c1002 76
    0x40950720325505501118850400d422400c44542c0c00a4450510500c1d103034107a0039002c400d400070351010000c5900450300e04101c040a01810700c08004206056244ca410f01401081c20f001d11030001f8104100450700504000304070b4001c0101d898058201034491a05192003940c0b91b0803101c1000c00515140c480c2d1020742441810f4806444c0010b04241e8a5581d407001182c1002808509507030012400c0e800003896071b0288010350007070504800c800b00f080750003404c8541c2d20043c0d0f0711482c001e0b40240007000104101085001d0558484c081058040501d4200200a0300034118080c000d4002d0300b052041581c3c002402c02c1e202031050b0028003066032030021211100300c80c03540103900742c0c1021303507001036541c402c400170000e560780c90070084c0106103481c0401040f50450740084050300c501c0151606100c10400c882401020040014000d00e07410600c01e614901403491045440441d042c0401c031168000e010300200a48080d150009a00c1c6010000759a041801e5088064000000030303c2d14241c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 799005863 1250 799004613 799004639
    0xf011401081501080304050427030305090c0102120a080915240d0f030305060a0e090a061401150e04060b0a08241e010201060e0115030c03020924090406030516 70
    0x250f00d80061030600341f510041c0800703007000740340040b0b4030b030035071080c3d01060300030507801b10402d80c006e80d000101842d11000c09460300802504c9181550b200314000311501000c40c044558000c29440d20102e180c80b490300c05844d042c01c0b1318001124004450030081080400038011940012a050b6807400f032080e4004d21980d0134440c000035103105210080c610200340a90016a00a00c01502804400b540c9407005561000140d46004070341d00040c0742c80013130181e6030099411405080d4000e19032940f510313540da01c800c60a81c0000e0140710800301d03a819550741b241e019000134a11154910360b201d17421100205044400c40d501ca18000425501607440c12406204404001000d0100c1d0040c18400306907603002c90b002c02041341150b481c0c1e07001140034511221880c0c020480400c0c4101003925490014096a11054100007054030510012200f559000181e0403165075039070002d401c68158560351403540c4156022690040d0034980c001040080000304041c001815484811415841e502050001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 799007113 1250 799005863 799005869
    0x903160b1e0910120f0c170603031201060c02100f0e042c060a050601021501051e03120a0e0d022404091415240a020f011401081501 58
    0x400051202074000c411014000a24215162005003040c1a01d00020000000011210f0004d543e02c014850840080c0c043c400c000701030b290040c014003039000d1005141d20940e0100c40c850704801d00208960362800e02c21282c0410f5000e012001c1c070341e1100300180c4240d040c0c4800300d010303820704403100f125144039480e00200340c2155035403c4507030380c10b440c200805010095008401c01968a0301000c4203c001d55003410b035505190003400031071030f0401405040340c074003c1200d810b46d0003072160248400361505500c5d05440741102e4500c0180c410750402c1015401c1a80001c1d0540300c1c00c000145400070201c0604003060165450b00400d00d1060b003070048010000d0b00003034010403000000b1003100162034145100f9600a00b4a9003001d030b686052800f56541005100c00e01e003002030601c601400a00280302c0101c3e42a100c0800342541e40c3c1070f611048000518810f00114086620f5030418820300038611071070a0b1000034403041c0e0f0105000e1411880030f01c519002440340c801910640e004402c45030b412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 799008363 1250 799007113 799007129
    0x140304200103090b010909081207021e0114130618211403151c0c030c0e0f060f030a05100203070e0d03020c1306031a0402090106030b0a090b0607020d08090316 70
    0x42c59103080013503805050515001c9998440030b09c66102104000d000b110710844d210b030300030840304100c00d12407a1a81c4840f40c201400e45d0400b4000050040545001a040800700040c60150942d60078108000c24100581c00f400001004100050041e614100030040314945c24600302c00c0031003502960f00407503080040d52000000d000040e0302205c9200e80c1c1865034400340060888040b9084502c50388248600202c8021088441c00d0040c850f4420396080034120a002070382c3c0b0b07410b0550441c10142c10041c882031150483d2001040c45441c28001403003281c0c2d00104032000c4804103008a0040c4d00300b1241c541c000354400c24500d400b880d100914150b02901900030f420440010700a00c227851031444041e00814cd100d0400000007000360886264040c000c00943c84a4140391042107981ca506902000800d42031940c0741301113a07a90585e403411203c901000065100144000c01c0b01c6010b440e40c00f03075000501600800030b0089080c001c100b640c0301101910607804001003100810000da0080700d107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 799009613 1250 799008363 799008383
    0x91203180314030601210e0c181302040213090218041107122f0c09060f04021e0a090f0501080f040b07020f1c02071403061614030420010309 62
    0x1080582800159041030043c54110155504101b51202080101c18400e0345035640c5d40e45140502e500340900030000004881c0303080714048500c030300b960b04500034042000e5100c410031003a085544650494015030840c2c030040c00550350b160081c0000750001030340445840d204c48000f5a007464907104580c4401ca82185880c1440d070642c4440e880b00807070500400c10321240d0482080d003038950f280c01c0c15510545c0f0960039003060010810506003201f02e01c4031800741c11030006000103075490720382c80140c0c403200760360040c3c45280300850b211441004208480402100140c0070048952107201d00f01501d03d904031b104074995491004680084040300e140c211030400002290000309060128bd0300180d00380304641880a20280884c2070088a5241800e0070980000401049130184034520003018480718900c1c40060042c0401d4641000a0000c4c0070851a10b8000000c6401b0300d11906040030044c9501d62030349054600b6100d0042d01c0241c566603d507a02015100542c4a80104c04801e07a0241800c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 799010863 1250 799009613 799009637
    0x60e0a0215190c14120403021e13090602040b070308090601060c051903020a17040602010c0815121005010f030204060e04051b03030705030315040b19060f0509040912031803 76
    0x30790740040e051048901d2107040c4d9490420b0300f8100401208010b002409070756961962040103500010030104040700e89900c41204681e98601a1315003030828440c1c0c010492184500e405c1009200d25007203004c0741200401c849042c1a4002010f500c44c0c0382c00011aa2641d07282e18040c0e0701c660b10340400501540c4170009419070b400c4802d0310031898900ca8011110051407aa5540340c030780c41d44d007400700b8114401140421800e40e0901410f42449554101413503c0c0c00c224a0794944454a140341e1805888007111b00b04241d070040003c8050141c40300d904110300d584038100c01000201c20720046c1c3c404d90528202054556042020364069030b03002e40204200c074022404400031b00c072186050350385400240949001705406100540c800d8940c0001c0c100302c07642400c01c000481d80c0c01c112441c0038107140c040302c40c4461080c10034232043d1011030403c101c020003c56011522880b4048080360403504004101c02080805040c0c0d4581c41380369101030013507e941c207022014603000c52a020740005c0058402c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 799012113 1250 799010863 799010867
    0x50d1109011404030c061d030d08190c0c17090d060204230612070306080f03070210050a0206190b1c02010306090b1333031b0605030106110703060e0a021519 69
    0x100901087c2c42904140980e41400064145180042c440001c103600c03500708042c4813088080b0842c050500300081014500c08640141138612a500003083c0100c26030700d0301c10b10080c8006035840908003d0128000001c24a010406074002e48105c07616a0400720300c42c4030070884030640c401c0310702c0050101030330400040c01c41040752a003d05900d0a242e5510000304100d0400e200c0c092202001500942e0f07140c030180f043c0540403100518036001c0010a02102100c03543c00314000d40c0080488246c5543c465949010a00034846a80029801109664130704d0002160007511034000b4000d072003c014044c1e48005410642d01c0c104c410300e0303010b440b00d0b80b540b005045c0360307100c210084041540c81c005403a40c01a90b620003004160324101412080c0410010401c616115001c503240f0a01003440041c600300c4e014009000601400d001d10100c140109a00c820820002e0f00445e00510309104600c100e10b616034440c0112107040c0c0c00380708286e12000202540d6012030301100c00c1a150700c4400e00b003403441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 799013363 1250 799012113 799012127
    0x50a03090201031104140315090d2604061410050a0501110115030f021c20030a06110316090806010b09120a06050105092a0901050d1109011404030c06 66
    0x100c0c14507584020302200c000c0024045c00142c451900f42406040c000c408043c0341040401d0403800340316840041009007840440c0d202c0c20f403590f40c10042d0b179041d80e04c102041540d91108007a811418440c04100a10585411020b8403010803107070024941c80b046003959440e5510300a150300440d03100070800c115445502c070740c411400080000103ca2503e5080003d2071400382e071060f51000980300541045d858131505d918090341c00c1640c000858070196680c3c01d20311032050ba5040e081d4038800510f04054074240242d9520719445481004038000b910050b00030313500281c43c1c10401300c070310441c0054100c1c09031124130f00740e81c010707c002c20042e881c0c040340c04d606600090745603070080345071203e2008036034081029892040c03041e10046841c3d030400d070a00401c1400200307070846070300784d035506804128080004100c500200c942015a00d219203001658107102c1c0115400c0c90a160280842c00001244094059064244d0b5080b05031602100070450601840c08003a0a01070482c078200725643c0252070f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 799014613 1250 799013363 799013381
    0x10221070e0d0201140f0304081902031201030f03030225050d140d0b060432151914040e040203070e070504091509050403120e031c051e070f0305090d050a03 69
    0x5445460804002c3c07906c0f065800a903801c550310b181c042084100b45420240c45490100e01d440110704100c2c80d0f60000903203000600c0044c0402511410a0080c1803081d011103c4810340b40c559540b02c107203c1c0c0548184001d00d40c10a0320a805500d0326800c5d101d2140307001c1c0c0c040b00500c4550350305150414001c03400805440f04619482001004009864071403d00091644840d110350580b00400c1000b0300c41165020324041449145500031220749003c0e200b0984158503a41c00c000120810f2343e45003580c000d000700d282d440302c0e9803012070001400c1000d42003180c0310302e10a500740c60050350380e110881182c4109980e0300b000b1440c148002d01c001303000b41e0300c1100d1701e41c104040c1c0071406039070710060000c0715010f071801d400007080c1c07251004016950340280c00c82a4a004011494244078410a040c0c03040703540059980982c0341c03408100081e4144039410300e204078406074501981481013029100740e2000b034111010a061070001070003003002081001103030410351076040c40d1041c100812801408155 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 799015863 1250 799014613 799014647
    0x180c0806130f0b030a03020304060201061401090b071b08030a02010f090b062701032a21060213080c030d0207030b0415140c04090e010e0304091d010221070e0d0201 72
    0x44160f15503590400c290a1001c0c000d030041e550b80d50038604028256440c9800c0194004d940a26000090364446290f03c00c449129500f29281c040e50700c2c05060700302d0454046010000c00c11000714000001200401d4103040c00c1e0001c00c40070004440d1034060f1202120080c2002240754005101802c05140b809050003815004c0841c9940032110303000010001e030800c0d65441a030340508801e00c505a540308000c1c000010307075242e40e646000006080f81d41000c0d0300390b680a503180c01c03080c1048076a4044e40c19070031114100c0800282c4614085035070302540d00040348248911202d4030216400403980c0400d4139004440002e542d95180c607080b216a007018481260302c0d0fa105060900d0f4040e00300300501503010941c100d0b942d54608002d04054500c0000c8080d041d0345003000740040e8100c004200c40884525180c00b05003d044202065001428008041515400020784d01d8101030150b4040424141c07008505280e601d800f0000c0b2410030b803d25080c2d40019282c0f80c000050340c0680044001e0368400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 799017113 1250 799015863 799015871
    0xc0f090f07020f060c1e07020a09110d1b020d05040f0e0c1909080607090e0f04060b0d0308061c080a0806030f011503021813060c090f180c0806130f 65
    0xf41d0009140c500c1c101c5412880d040042070406c1c1c8102e0a0603070f071117400d001c0c0e50070b24188100c58000400f000054030172010b00550703c40b001074020082505842c68071401d0002001100d81101c220307030640e42c05440860042c018201501000b502500a88044e10325422a404580d0705000340034600c50700140c0100294074bc00c0c00034281d8501e030440404600030715035840d004011f1800e8182450403c0c0680a0301c00c0c081d050f5014064a0294000d0360b504c05243c2e10541e26640300c0d400c141c4000c10348c02c0c00d00743c0c11038031658007001450341104a05020750010350711281c54007418200c51007c0e403150440109804400c0220100d41c901c204400c5030414001001e59a031012180b02050852310010400b40c0c00143d120710400542c540300d43c00107400c106424000b1211700d00401b008500c20002d0000030003050391074104100c0c1c0361141010b00090640d5280e541c841d1502c0705400042d000401c0d409405490078041c00703e41c60f6108404107400790034080c00d0481d0b880c440140300b038060f014203403200748010341c0c17 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 799018363 1250 799017113 799017133
    0x30703051806030a090312180b0c0409140106020d090e1513020a0c0b0f072102070503030f0a0b03010c050d0f0905010908071407080a0611090a06020c030c0f090f0702 73
    0x180c40003c600583c901500052079180300c0c074000e40060100c0140304402850019031a1022a50344000d426259000400c00f4041e0303100303c0e5401031406282c0040960720b140ca81c0b031a039442c850008282c185c4030103400b114040301100400321454001030045411620200003c112003481492081c0c201c408c00501f0700c48403101424071802260040440040098250381d440001c1c0b2403800340d20358000c480e0600203181441d0410780503160078406419031101c4003003040f000120001c0c030743c199002e8035409001e50b5a64227210100341c41252090b15240740b2249841c0c1030186924051040c55100300d0301d0342315641045030181c80d4000801e500c0100e00501d07916848034a0000ccc40a20170405080e2050700010780f9483c0e00d0038103030441741c4221001b080660046d030b8144020303000000c0e1648c2203648048042034004414424503841e0040d0401e082c0c20014940000c60340b01d4010656281600064080340c803010305000c200400d6000c4000c1c00e07608403c0500101d40000400c5c501c451b8040070f0350040b990b000035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 799019613 1250 799018363 799018369
    0xf2803140d12110c1b152107020f0d080f090105270a0804230a12060218030f1e030906030a09111005030a060501030b0105090904060b030703050604060606030e0307030518 75
    0x5035160303403030f1700c0b03100c024121604a1814603080065100000c2480341005490714002d100c0300020201803105100c0c0c000004d848a208001e0014004142c20a843e00b004444802410ba88001d41c0c1b019041d010350300004103856070501c607552042c1d42901d607203001c100d0341d40150400710186c84404e40d954003601d01584045952500100700601341000e001400748100f03200c0d4814403d8409010f803186805800c100a2400080d04c0388819a400074001640c417040103451031b8001c1c01e0b04c0c81c056090b0044c048504400c2d80045802c41d034a203006524190344182d02c80045032241300386048158040d80c2400401e000a555500011a040c81000c20030852102080007071a50101d003005072001500001c1046007040d00c900658000385400e00f010721851008c1000602240140c58005006d40031280c0064240080c0c1c0e048085400342c00380554542580740d0030110303110081103c00744d5407a41842e40008079944244981e000c0b402c2044041c604148141d94121103540c0701c91843e004070301c400102404130b59 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 799020863 1250 799019613 799019623
    0x1b030c0210090f0f24021507030b0406090203180c0d1b080115060207090c09090e0a0b070c0209150907320a1209020604050f2803140d12110c 62
    0x441070313030340d2405141900d84070701c520603224030170b048452001031000d60a40003d1044803065070943c4440180c0d4038440118010f1030108545903005090240005074a4401d0740194025851040040100408501e6040d074840d407158805401c40b01f00c00c020408116a8200864400b0713410603042d1a17a40e8849a003404d6400345480e840c85030790410410032a894040000134014207102e80e0600c40300020364806000c0041600c5000b01494581400c000d103042d05020391a4180e0748062031903035904201c113000b032961a81842c203d024503407000219003c1c0160800029032003c4c02000e401035a9036845040b1084d80c0c449501c2d109042d0a1900040309030003030241c5002e1921680300080e221604008014101100340030342e140a1413620f0400800742e120300080301c040d5071040e100d111b00c1e6448100030039030ec2c4840744002881c402040380711480d41c140030240305d01103038052109800752a29100da81921944129030910104100121500c400d03d0340b50800e883d0f400039a0f51490070902c000076400d00345 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 799022113 1250 799020863 799020869
    0x20708120108010b100f02030a0c0204090203061914060f0415031a040b0a0b15130b1c0b1002100906060510090f06020309060409020705250302011b030c0210090f 71
    0x903035191071100e1850b00f02005c2c0030b455142103140c1300040d890f0046001e0f48a1150012210800c4100321300c50007552600c0d0881100d55601038101c0c0c4180c60040d244124106074611443e0503142410200c0440702007403a80c0034001c15009001c1c400a003c41400c0000500000000e41f00c0800c40c018000045201c400e6a05001c2d1000505000039283ca4a4071166005004100c44540c13445c000b4031866540ba44200300d5072086200039001da4400000e030315101000389950100421040c00140c0c00804071000780071700f40d105a191405c0c4a03440c00b82d401c2001000c170f80100500185c0c0050050055141e0303030b41140904c640281000110b103621080400e851724076841154000c0344c010748041003510403501c00c0c00c006091901c051810200714100251241c07003207102c0d03040d410307070007140d01c1c0140041480b0008140a15040c040c00892028406550301203a500c002e901003690b100022030180302c4400c0c4503000e02e80c10350341c802510005500b00024400c0144148040001c08070b008500240240811409 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 799023363 1250 799022113 799022129
    0x10e0f01110a0b0402100f0c030f02030d0f0e0d03060e0c0d020f041508100501020304050d050c060406021608060f0a0c0c050d021b1f050a020102090a0e060316030b0a0207081201 78
    0x407460130b8018409200320035444101040b0b01c01103107540c11640f02c040500e0a0717903d8035100c4000a1661001c034610b0103032546c0045441e1801d40c013100101010780c4000850031480c81134031181e03600058182c00700e403400d03c50221030414080c0050f03801c24041009001c51543c00320700506000300740d005c1500c00d8000c0d0b00001c0c00e28440070200d46616400c140c81c903a10180d041c04014031182000c0000f03490b070240740700341c6000308245102c9000700501444450101c25000e003d403500d80d56290300003590307940c80340c03603845107030700600c40c04100b080c0085029407007002e031044d00155946440c003441c401801320211b88400c0215000d50040001c40070301c41115020f06542c000e000b8503512100c0d240080722484140c41c49a004d440e901aa601484400c41f81846c545045c05910b44810f0113059019100d40c030042c550100c0340c41e0000c01c41d19260301e01240684810381c12078411220b810140402e400080c00090a401811400034401c0e014a40040542c10310420b2040d041c0040c6c0d00015001c080d00b038100c40c0e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 799024613 1250 799023363 799023383
    0xe0d030c0f080414040b151803011a0907110604240606090f12020d140f030703030f0c0237060e07030311031606182001020d02010209010e0f01110a 65
    0x4211450201d0301003921600301e4080181d00030780c00000304d07548a200c0c10060003200100d075146198903000d230302d02600c12001d4001d21152140c1509540ba0101000180c1c2c8142d00200110b00c850740704200c40140a07480000502040c2c8881c2c0300e001850b6040c50148449c500c0d401d8510038000d0250181c4801400203480f0711070400c0c00d2a240f4408028a60000340c1001c0044c0180005a95140031080c00103800c0348044c181711803a881d5103820801c400c0880c981d9440001400010103901d039101c0c2d1142107640340204179401300702504a0305e074404107601070304111124400325001300e1099801e44402110890100000701141d80d00c00645074500d034110031036000007108000345034020048090201c40c4001952506010028500e0091008100a004199502d00072002031390039005480c00c464200004a50030418251190411400b1070b081038014085c800203a10b02e94014020f84d1081c2a058507280d21025120f005c1c00f104001030030242d410054191400b4001e04c070f00b40254031101e4060341c0061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 799025863 1250 799024613 799024619
    0x1801140603010f114303121103070f020f010c02070e0f01060c110409060908030a0b15040e0907270606170c0c1c0e010905060a0e0d030c0f0804 63
    0x542110f10b8081e0440b1068100075050385034503841c104031441a0020441104103680240300b011072814215205e421015070200c8101500c0b65590014607a81d21991f0f034848a0060324203184d054440401c052104007800380302140c125405001c81d00c03103403071140c41164441403581c41c0c450b00b074400070b050101c0541c028500c20b0205100216401c3c2e4020108901580d03a54507142c0001c040c0c583d40c0344050004980e881d40301d0610342d01e0340c00440703005d40c01510a00c80300801c0c1c2050301c201d03481075460152052401000156a0411031181010300801c4000700d41000e2034000c1440102000901200944c019428049040382401c01104182031651501e100c0c0382f43c0501c4c02e601290030341c0c1c10410034031404001c8201000d1a4081c07071980300c92041140c0703454251113402d0511345900d0b692000382d0140d0040340c580c1001e034460403940c40d400e070903070314a0500c540d03440c280455803289065510020313504068a00c44e60610300a400e1002c1e11074540000710301100d455580c0740c1c001d440c10841e40000c3c006810 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 799027113 1250 799025863 799025869
    0x30316064b02040b07080d023603060103021f0c020621072a08072003070608130f020111010203070203090406230405100519030512120f18011406 64
    0xa2001012400e04503e0642040c90034040780c010b04000510300000018059061902501510129072071040303810304001440c1c00403005184001002c4002260f100c680c034030b081c0342c0003a100307049030b4014012a102d62005071101801c034032001c0c0708202b8401c00400c03e40068070b0390707401402c4441019004000f407599001c911004808041c3c100c4003007000f2600d0750050006103000740540d03400d60403c80040780c8014500740c4541e02441d003000d01000159049150200c0300b84806100d606021000d990307070142ca42c0e0007a01c48050a6561203c940d014010384000900840c0f070b000c2020340141401c0005856240350030303013681d00c1243c1c0d160040e0000300e0035044a040c24000d05c4050191308044002510f0030b5030307910141e5410340d5840352003280c56101044c00401ca00006802030840a00584590b000d07140c03001c0400c60440c40210307007600c50458640f552540712020740341c0c0c0030000ca006000b251102018444402c0001e8003003d010a4441026550802c0905c10500c01c8401c08074540c81d0381c80c0103410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 799028363 1250 799027113 799027241
    0x5130b0d0b1c0c120c0e04030e030607030c0e060711131e0f05010626190e01241203050304060b061215151204050c10081503031606 58
    0x11021540703c07010a4400045c0840000c101541c3c4101540c14140d5268201129480d801003a1140c2502400c4140212140e03d504940440c41c0d007074583c1c401b104074403000c2c0301e860300c141000680b1010040c410280c4603e00184608160302641c2d0000c41c014003202040101c4007207001022150303694608100c076280c1081d0040600601d41030404409803140307040408015140d6035010b0f00c42e107146000046418455617024a00d400e1000001c100c00e0030f5a0b0a524000c00391001d62642e08003003800034030744a0f405d40b1980c1050310140010443e110089a600342c2c6c072a000a00200c0710240ca82c507107c0142c0d1111809002b4000c000075038114242001c005c03105a04102c803041c103008001c181c58203603041c3c01380c2007200c0b84402e1001612895540ba42000c6080c59024041e1a0b44604c10703100706943e071580020310354003840310545c0d80c200550400742055602e01c504899071074115265140079000c82c040354403c8035441416141c0c0c9035400341d0741c541c403c864507080000180a40c1e284a19034500820844 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 799029613 1250 799028363 799028369
    0x1401090f05060603060d0501090503030115091a16030207180903110d0504290c070810090302060106121d0f15010302150703180b1905130b0d0b1c0c 65
    0xc04100509108010905074440181464080c00d001c4030300c6030030841d0952203210080e0308003060380d49958440320350303640410703a001483c40040c51543d40400c401038103502d0400001c3c03560307007003078900b000b060708060311800590310542c150b024100340003905949801e14110300d0038001c00c002410081034075001c2c02c194003802c860841c9900c00440c00c030200d500101181c0658141031f004250303103040840e1210960001c8094108140408249050708010000d051003e640070740c000e0b90038980b02c1c00048021664814405401644180c0041140ca0b005100107110b080303d16401083c40d920003000252010001055071510784c1c4402e4902d0010441408082803100790040918420351458001400d541800c1204d0b005203000040c00c01d0400d03000c2c02000c1c045003044500407400640d60050180c0603041101201d0040d2440100519040e1080049400d1401125100742101e82041201e0390207802c403003c51020960742e030120300d242d540c4806164842400300c030414184c1c9420340c07401d003000070f069038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 799030863 1250 799029613 799029641
    0x703020901080105090604021b01063318120506010503061810051e1f1205061504060506040305010f060e04081903090c0b030a0e03040b0d02130306140109 68
    0x484111016030703004142c94110b0384221050101e42e120040000c00910583c245d640c4524441d0549000d00f42d0b040d0045011507178180d00400d9212000720114810b003010a101c0ca255407061036080c0126400341e1151041152080a000c03203c0d03886203039401400c84140019240d55002c81c0c0104158507081202551211f6a07200304d0281c100081c41a0fa62010101c500b046880e4684c0000388c40312403e40c1c85034503003a0305070520340d542c4c0c01d01400d12841d02d10380c2100c60440042c40c550206000351541d8840c1141d0380d1103001000380b40d644030510550b1080520b58250300c40d1312039034002800d640702405003001d107000d200006240c2082103100802c40740290300160803814840300f0800810411002c0da0015921016001c207100075807001180280f0f0030a000409404c000c003004207800c4800740103140310b01c003001e4080000e0001243c550703560b4011842a030300483c10810030700f24080500d8003d041508a00c0c00341100480d1039596007011386205a51480003903a030314004101d0350903d07001c0c0b003100760001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 799032113 1250 799030863 799030867
    0x1e0f1103031306030b0315040f030e06090109090b15030c0a09080705180c0c1f0b010c3906031e0603080307051831051302090405070905070c0209070302 67
    0xc2e9030a2902c000e00c00c4a09040d91030303006166a440500041a080c040b08030508080e140c24034040060706c80d40d0100b0780014480402c546154140501110040d60058488200f0313540342009002c0074060b0b10f80200c0c0c0146c0050041510100900d01a50041002c44100b985403d500c100041c90300d0900c1d4800c07151548201d4041101d925903104160040c0480300c24000d04d66141b03008520035120307650a21900b407050039491001c1504500049240903800b94013400501400c82c01140c200c66841e00180c441c00c103c1c0060690092038030850710305202e008060003450f4001980b410403d919990040b00401c2d00c400345652440c1e5580706142e000c190f012001c0001c641162030b000300c0307408002c0241003440301c0061440040b10b0107410f1603000d841c2c020402501c0e8605140c06101147d9208280c4401d021003100d40b60075091140105071182c50044004102c5030080d1b020841d0403800a031080e10130380101c00d004540c0012900070701d4401d08884e25801005003440c81484400b203001841541050b01c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 799033363 1250 799032113 799032127
    0x21112b1b1115011e080f0d090e060a051e120f060106140909101e030204060902040503060a15170f070b27010210090605090f03040315091e0f110303 65
    0x2d2105007030650b4442c0f40d21800c00042580c044c040c01c0c2c83c58024031098820b00180e038010030070001e03042810503519940d00e21080d54134096416120390644045500c80c001043c2031029052010030320f00d0320444003001d01d10010315900800d00148103407a104009030892074000420400030000f490040550345032040c00d400001604820031301540c0440307032041c01400c000c00c00352106e04141101a003400e4800d480c10b0034680300f0600d4525580e104c06c034043ca04180e00040c5907040c43c03007a1400c9030710240141029550b50781c40c0380d004104030070076880041070b5441d0106021115001000b50621710000403d45840070005c1d4500d05035860340550300c02d0030200140040c5041e0703517041c0f030450250442000c000e2240c15005070b081c03000381420880d0091800034413909100c07198000c14020000d4a040da0000c180501d0035030780f6407041e4000944984480d00c180302a000c001c0e84201061030241503844058110080541820385403a00c2c207403a060382e00c8076a4014001c003c42c0c074850070300e0210011072030121 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 799034613 1250 799033363 799033393
    0x17040311010341070c0503300702060603060a020f04050f0d0804151101061413141f050a08071206090b0f0603010f051006050d140721112b1b11 63
    0x220b0020070000031001c2002c0200c0f0403100c0340c407030180c1c0e01030b01e071282301a450803060003580c510b802c80b5410300c2440b80c07001003034501c0030520840710b0424140303523128903040c107000500000d4104a07030001c0e0040c400c075001c1f00128404e400504045c000b56500c10350b502e00620300c0100504d10130540c402d0140d140c079408201044045000e104403040503075526406250810991004202c0801c9103507403c140c4c0c40230808030301700c0da4120041040040010b40240383c0c5031814005040198051038400380d10102c414010380017091002005688100d0713000c03407103400540c0c9082030f4000a55848800781800b00600495103401c0c000d0b40d80034030043e8001c200c14a84900f24000c160218441c4c40140300700020a0b264801147c1c009000340b1188803503d2115040410006000c2c400c07a600410500c0c060344420000f8080d14095440d031502020f0084e41000d500d49100b10304d01e007200e8030032000311040000b061071400141c0180700c81c049554001d448200c1c003104018201e8500740388813014070b40184401200c000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 799035863 1250 799034613 799034617
    0xc0905150c0d0804060e0601080d0909020f0a0804081611011409100302090604050301110d0c02061b0a05160b010f0f0810021803120717040311010341070c0503 70
    0x103400783c070705400aa215801c0010080c1044031441200f80078400c00811040000103100f85500441c3d274512818036500c6513001d04a014900198070401d4003013101d110041d00c44c1c1c3d01e40750450300a5030170f80d1a020a08100131100300188908580503104040607580a6812604030034551083c0300100345403100b510002000c0141100860092681c04140601c1c2900d900707080e01d0203094080c0080240701c48400c41c0c80b001e90800d460a194031800d014100c0c030b00910115459000d003d41c298a90402c21030040f110603150000e442e80c00411800740401c600700b40e200a450000c803409060340d44059410b0181c1070116054581041011000100c010002c1060001e140b121008030703002e005858054801000b0410031368107c000b035241c4100c1c05a100c2c90a10b6030010203810784a50301640d10102004c4010240340110721018050625400b101d41495000340c100e6000180c1c02400c0e44516846001203401c40e404000800400407008403c40c0340e03000c1c001e20019000651800c08520320300140d61115540c1c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 799037113 1250 799035863 799035883
    0x8070f06140a0804151e020d050a09170a17010b0903010f020c0c1c1217060d0f060903030f15030201031808030414070b0f0a021c300c0905150c 63
    0x3442c10705c2c10752000c6080d01e40c04401c22011440c09806405500034498020b90800c070f15a440349464640840d00140c0240700b441d51381c0d90700c2220b00d44542c03140000001c9941100d0709c440c0c1401541055400c00d141c030004458042c0c0700052602d611010382ca8140b500f103901000791103051501c10400c00b20000400105100440c2c0100d9116400d0010034080c0c3d4148100040010001221031550030f40081c3c220987d8040d40d150708204010940d01c0c0c1040040140c51b0080c081c15121103110181d01007902a080128182d000c0c0c200841d02ca0400701c400c02c00c83c0c030310503200c500345104079106004569240c024250000082c90074005040c80c907450f03030700603440050801081d20038071381c401716241340c42480a0001461031000044d10380400c001d00c14036035484200c00100500540d00f03030f640d40c6581c8000c0c001b4031100903980c1d02000300809219150041403040e0031300c4d10390406e41041c1c1510030140114a4506500e0781e9040c0100d113487c2c1488200e43c0031080c6001247c2e801d01c00e510160350001a4003840c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 799038363 1250 799037113 799037123
    0x803060d020609120d08100b0a0302070201051e03010512010e07050d0510020304060213150e0907140d140f0c0702100c140a0b06100c11010908070f06140a0804 70
    0x20003018400201c80d4403a4040103604804010040003180c000400c0450806005413a40c000c241e46201d003181a8404502030841080c0080c040c8171846881b0b507000d06007852060605030300c0c12129450042158103015544178000b00000014486410110420341da21381c2440020b01c02c0c01c120b00c184a88811090003458004e82c00c6d1661003017480310800c081403100d6440001155a4205401d0a002951002c001d1100d01d80220343d00082005d10030400c00d0340410580c1e11300100c0e1400004208075840040d040d401000aa680000301d010100c0c401001c0050f1070100c001040303c0000d15034448004024105005520f40c2000c00003190249421151069412649121440c20440c010345009800d058041d040c1d01242c003034248015000501103007804d001d00e441182d107540303800130000c004005032038503000100488414000909410401440c0a0050400e061aaa20f03150300b603140030002c1d84103050a0440040c10000203030000c0c103011901d82c0c0c54a500785442d001c10b1025000d0308000c2c0006003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 799039613 1250 799038363 799038379
    0x20c010212011802132c0a0b041d06061e03010e011b03050705160303150303020a0218151507020409121403040c06081b0409091109010509130f050307121803080306 72
    0x86071024a1400b03040081494403064621f00740020244001c1c00b40700c03007140c042e0b0302c1c1c42c0710b01c284402c02c030200304204030900f0010203540d59545c1c180956444144100c003134080320220f154405a034280030300124282107000001d0b801490702e509584404085002e04140340c5001e0500c28400e502c542195011107a00c1508280d110191404500130804030310703400d66580341c001001c010958081170340c0d0304c91402191480d13103965156803008200442680d034905a80040b9401e1541c41c1484502d2552020304440c0807420442560003203400e80d45140c00444d011413104401180c42904643c0305600780407440d215500354a403580e11307460401114080c0d0801d110480c000920381500401070300c44083c00e00b01405480d19581c5000d1406000d800c002200e07aa208038041c072919081c50305000d4100c4bc0014004404d54030391060764203ca0324a6031007a05c40b00190441038001c80d504100411200f4070072608444100a41500100014551111b00e070450660010030004194030400303032500507504480c503030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 799040863 1250 799039613 799039649
    0x131802190e01271e05072c030703050d0e210c0d140d050307030608010b03120319180204060905040506061e090907260d030c03020c01021201180213 65
    0x600c95072403d150248069044c512010b550680707080e00c03100c25080120b0305000c0c0d0b80355600c0503100d001c10241e00f40c501d0104400035021105001018081c92070000d404d464401e07407240c646a0a00b18520030600200d1000805031541c0c0c10040041e42040f036400311500e84002500042c1074403020f022144c90301c503039102c2c14400244407003c0c1e8080c080e000004202e61400100c800f020740650001caa9800c0820b160110004420006000c0c0d402c0d01c3c00010003600c6004c40c0300c05c0782d54103504081c011031104415240041d6440e42d00f8801c000003503441903200d8106508034810030040d1103080c0c000c0c0044508002c2407000046c40001c1c240c0e00710f601110f808000c09141c00d44800030080d600c030300700d5000321300e1418455111000700303810b01542c0c2c44121229000300201095a542000040104825808649032140c0350b40720303034071111101d042841c000d460703c6040c411050998000c40e0030509003521003401080b91440030700040d071031819490000e6041440c038400c110700f1844640706602074428009225 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 799042113 1250 799040863 799040909
    0x80c10140f0d09050f0f0d080f280605040c0c080d0c02031c0516050301030201090b03130c0902030f100f030209060613081e070b090f131802190e01 65
    0x1648000760b102a007006400c02c94205155074601086070001113001e02601d0700601480404c038004c60050b107846503070b1103894400e00100c540720018091102912611551032031100c482149d005039500945002c60303282d007442c04100840360f548201005000390024a44000386c24241030315000c1481a00010700010002001d90071480380a2440342407000100c03d90a502050303a0145010b00d441c0c5100c009482441f510607034080c842808060302040080a04012841b0181e0046a010038210480396203121030782d0720101045486d40091002c5900802000051300d000305110b0f6125410f508140c90300351401040041d040c10a000190142d11000000f40d540c0c0c40c2c03c01101c41d18801c8505100c8003594801c105600c034a0507500c00300c81d4620484046800d076030300003989000d03a8503080070189407521070320802245044c007142043d000a81142059013480181c82040720044038200181c4021049204010315640ca8040e0b804102c220300c04140325907004104914190751034040d0404c1681208510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 799043363 1250 799042113 799042117
    0x331e0109270c03021c0c080105060108191b0302071a0103150209030a08040306020a0f14180118080c010908010213030609030912110f1f0f0306170106080c10140f 71
    0x1075084942e2140e217040d961901107900007290300404a0b00c14203922884168207a410545509000800c0c420200d0007006402c01c2c09007045080d40c50006a6032040020841e440c10704500f0708000c07903400300d018401c0c0a40048034071600402444071040640c11a550703500309800110004900070749c089814011354908100500780250040035103074681d55246030131740c069404010400700180106150101684c0108071100707400003013841c00f81c10804000c0b8888403ca01c040149410410410703201039010100c61b031454080c01c1f040c40500303900030503100050208a22603000007903da04c100480803d0a03840409041640da1240d0085101100760034100c9100c5504c1c0c01c04c40300c03120f144441c0c40c104000b05c0c412102111050f503c0800395142d000811950704400e002560b018040000c45c121111300c5a070124402455a0900050040d1140640894107041a03c801d441c0d030754480c01440200810000f0980707500c01114084000d40c4860001000c210a801c403511404034080b0348040000b0310442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 799044613 1250 799043363 799043369
    0xd0803070207121b153002030a06080d0905010212180a060327020303070204090212010204090b0f0312160f020d05030901170108331e0109270c 63
    0xc9008220101404c00d03403456140070b030710405450740c00400090104d01e040f00703050300f601840d128140654042411008100c040d041e02604088a108145004403510300c00f07036020740416140041c8060a10000c54904030700c1010007010300c00c00301000c0040d41e9000610420141c4e1035010103448160354510050a0b01d10300403c240c0c82215090045079113985039200401000c001d03400321020b0144500c0344044143c1d0440080d40542041210001608040d00020344041c07000d00349080d0f0b510340c0c130005400ca8019400a840c1031380c40c2c40a8081c1807510700c4a009403403e0490140403000d082c08000041407192200b10041035400c1070100c02072040224000003110b4000d4009400c00001d45450740d101e0340410f4082c0c1c0421040c1e102c0181d1192140e4a0314140c501c0b40740200030300138503400c070351606c51200d01140c00c0c050444842040b40c00c0740040c2e02d60155044244140c0501a0000d00c50917003101600000c0c4200d281c40026951007140001042507082e0301001c1c0e140d0b1040605221143d00c056070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 799045863 1250 799044613 799044629
    0x30a0c0606051011070b0901201002130503120307091703070203031c0e0a051b06091003290a0308300a060f082d0f06041e020d0803070207 61
    0x140504543d40d07042001408036030301420640d140e017912954410654000c0e000007900056403c440c2c4180c0c001010341101c0780580b04800c0307900305808074103500143d074401c0203e00001001c510301007200c6d050400c05425030484403e003c0b402e43c0340c55000205003204600c81c04a42010381d070f141e516550405d00c102c0c0c501980140039640d445412828003140c2e520109401c030040d51500002d902d00500101d51984134660000180000442c2004038120005c841072000e50301501c10880340350960b4541c01c0010440040340c07400700302e0000c1d14000f5034420464040600e1250309070200141e40f5501d08840b0416030f0340c0004141c0c4c4925000202c0c0c201004003155500ea0186408403a2010091002c6c4040c861000f8a074284041926610351540c0c940f968402c03c0c80c00c0d07001c61700400b8601941c1c80040124411000c4295a401107407083c1e61400c2d1600601030700c1900b1903001c0c0b100380301c5c0300203441e4007495030b810b040d10100c5a00e50200d0304481d50240090400d01c070201c08a800c562007401580010007100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 799047113 1250 799045863 799045879
    0xf0a02070c09020d0203071d0a06030b042d0b120303060405040611071a011707172a090109020c030a030506040213180e0d1b2108040b0117030a0c060605 67
    0x213218404000c0d40159542d00100d0b4910304030300c01d007842034000d14031151b901411401d03545140200c2900a004428402588a43c4a0003603e00d05c104010514000704400d084540c1107021803012541121020b4401d180600c02980c40003c2428000089980141007940c0008441d41c1e1828030600400000d045805507060000d0101c0901c154290b400315403143c84a030400d1680d036602020020002c0b1281442900d4000c04003c0080200403507100c6070b41c4a00400303403100a55034072054540d402a552861050220002a07140941040c007126409007000f440304620341000070a44035660700804182d0006c05480310001003907900d490301983c00c070203001c202c52003016884400700c0d140c4003800c403401d5451516060010385240f00010750042440c2c9240c558056803250750150080d00c0740460400c1d281ca80031b01200d207104074540f00020f0b900c41e409640780b0364281070903c2c1200e05801c2c10381c091034900010180d00607440320084101c0340c0d042a203052590380075049242010182c1102c1d840301f61b00c401c0c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 799048363 1250 799047113 799047127
    0x110703020703170d1112150a290304201c020402070204060f080304080609030304030926070b03180c09150f090112032006060111030d0509030c0d05030f0a02070c0902 73
    0x40061b04030059595014981503680e1445141203100100d030280d880f03d00c0c88010445152001ca0020b0224a6001e083c818408503000740007282e8800e50301103030055150030340350340650308220b07126032100402c888003c07021200710b2629460030f024140c041d01c1079600090071011503469511840c0144021180000c00a91340c0f142161260428410400c0501a6000007802160003200b01c0340b08951680700d10f20f129051a4500181c0783c0100b0150007500e800010410100504000c1d10004007038651619640f07290402c0d81c5d42c03210f4076201c0461031a034481030101d002951298400d584c05285001c9034080302081340005640c1002100c400d03038101241100102d036040a18180c0c038a09400b0703417524039070008000440f0845c2c04550300c500390582c0162022400320346c1725144401c914810001102e040c20b4040e0012811184107a4905050781d000050f1100c4d020742c140f200c1000c904076414554118540b025205092400041544d1140ca5000030014208881d8809a8010307000c848001c40d1100a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 799049613 1250 799048363 799048391
    0x303180507092304020a0605070305130e010314150a0506060f03010b0706360309051905040615080a110c0a0309050411042331110703020703170d 64
    0x3d000c81076440e07400f6111400346504840b040d03a182c01943d029106030710280c07401500301d4468005540031001c021701041603c02440c0b20031444400b522000d03448050a51451512120001c0710500e0525160404e4031090090000000c015920841411010800d81d42d82400101140300703070b40c19002c880c3d5000c8000706d0082413440150030614807410b0b08000c10001c0100d03940c00001440d031404401d4640e01150b018010300d84000200c000e1007030400030042900d500000700034680c00880040b1040c0d401004100d6032403d40215070045c4480320500c0009450104018900300f07000308241206900c4036014070707410803420116444001da88040d9812205d680c41c009012801c01d100f0988203c0c200006418260108000c4608807040401c43c1c0b00310244540e40b4058030100198000da11810f5001c1007000b400305503c0058203140d244180500880c0d03410b007131108494610b20008102c100602c5100006900007802000350794221103001c140c06042c564640c00d0b03110390765440420074186501c00d40c8210f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 799050863 1250 799049613 799049621
    0xa08040804081b0906151c0b09010b03040210030c0903020607050a08040803040614030c030105010305040c0305011109040f051b0309100204030f060c03050c031f0305060f24010903030318050709 85
    0x2004c030303420707010342d1549810031406114400c04c845940c1401c2201e020480d0364807107a080010a80d00000c16610a101c002481c04070090348564003403000041000118540092981601c668034103003004551030650300103060300c0d040d0000901441c80001c040d001e011080103460025640002195a59074507103818075202e8009205a4001ca80210601c03c02c00741c0081c16684117451b15040c1e40d007180c0c80c1c1001180500310161050316090100100800414402e0250701c803040d8041d0606582d4400240620040f15403401810140c40c3c50842400b20054041c44494081c05038000201d81f2501d589400ba810904060b0311307058000d00c001000410410b074450f0054036580110804c1100c80b00e5800143d050390812510640306100800000b40e4581d90701800312240b002c110a0a8641034807903031801c1c5040010f0b83c4403800141140200300c44514801868041041c69080d443d481c2e03d03000001810701c4005010007818540c40b0003580309980f8440c1d00b00f000681d0844202c0354801e83d900a444010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 799052113 1250 799050863 799050913
    0xa03060b031608030a030c030f05010801050105180408070303050403090f030c0509160206010612140c0d0c1727060f090106080d0903111c05030307020c01080405030a0804080408 78
    0x6401911007115000304030824840c100c0300c3c0c5401440c80c0c9000407008074010060340000d8002c2c5030b0742d13082d00b0081382d005108a60183c0200000040c403541031804020ba5010b5421b00818040c0504081200240d1000300703070f6103050f0b498100032070507803945d140950f011002074025070108080d0800010038480100307148021600d042c0d5070340302c03951600051312091602d0880e07480003591050004201e4507209191543c072442a454001400300f4689074581c01c100b2082e03030441d410080204508800390041c0c415400d21a1560514a800b2180c1c02ca807841a840000c0040040c841460303440c0c20315008240c4200da076000e014064070100c0c5231070b4030740c80d900400070ba4015655600e4140042020a40020040d015445036100c4084461030351342c403080b81c5d04040003116007205c2c5030b80c031000d01e0200320480d40c90380d80e20078809540c8901c0c01140091400092040305810042e03a10240f04c04910007004403405032182c0c0c64011465552814200098482c0c1d03401110507125050b51130b01f20303180c846d0000302c0b9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 799053363 1250 799052113 799052119
    0x90708070b0a300507050a0f0c020a150503040c090203090d03050907050603090114070f12110c120c1005010f0902072a080c03070f0b0a0c0c0603020c1e190f020a03060b 74
    0x3178540000440f0700e8002c8464806c0401d41c8580035440300c601030103010042070702c01000340140c41d8845444600d40000080090701140c2e010045c081001001100b01c009002c09210850841c03400480c0b046d65200b40b44500c005040d0750f0000301d42001000d00c030074000360030041d103104d5881c28680b00c140c0c02031000e1442c1c003c4042001021230360301440b500c41061107142c2507071075000302c50150340c4038001030180140031302c2d452008018441c42000c061004010441d41c2d40d94140c0c82d14001000ea600744499000d00319503841c644030051040d95589628441a00c124480043c0c0354000303441d280d44041d0001c44000e03601411184640c080102042c0840252401c07603060307134158850307113090565604140c0103038040a8043c45041c00001542000b8180714507076407502040c0030950f92910001200560009030000e0380024005031001410000c1010508a81c030161000300c0500000946070180000000340000b0f00300480d00900180613000c0380c41c0d0382c00a10f4011000e5403031604030020050171204c80c0c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 799054613 1250 799053363 799053371
    0xe0a020f18011701080601171606081602010212150d0c091b030e0307080721080a0506100e120114130506011a0a0806011124090708070b0a30 62
    0x8045441030801d0f43c100c42d4240b00074000b59091146646119014031580701091040e090442c00d0002d184802c2c1c401404103803580d201d40d003055040e03003141e00c22904c941819a801080400c2401c030961490742e9200b01d01003000b103040034040e00060008070350102c000e4200442c40b40e010841c4007140d031002c8081070000880540da40c0c0b21100550030340d24a0000c80d80e05410074080785002c01d24500091000d0b0703121f203c11004907110080700400e9002034504002c001400141040305a01c2184030b01c0d500650100d8030600d0540090800802408412800c540a071600c070000d0820402c0940014001445480e41541d0605d0a070030504012040080706507010b1060b1030002801c079486010800481030003401c05440c02c01c113102c0c00d40b10200d0181c481d40c1006100406490203040620000742d0060b1060440380201802c5156903c035a00d010300340d09502d40046104100071800003680c01c0440c0ea05c0c1526036190703a02c50304241d51142990f02002031441210b0b602080c0303800d921032880310313040c00010100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 799055863 1250 799054613 799054637
    0xd0e1002010908120a06050901030305030406180f1b0b18090112020a090e100c08060a0b0324030111210c09060306061806190809010203040c0e0a020f1801 68
    0x303090350032940b005030030702c601045494200d907085461158028003080e03003c582a55078001050081c1003d03841600010710203c1444104006800f172081400c01e0f26001c9611032065888a04161ba41e1146c010a2641350700c2881d980030043c0300c040c9005225403129584c4514010075419682422400250310412100c0004240c003440d00075082541c40d005022684041d080410301c0c0000c022010024640f4802c0213030160f007100c1a030060f00e0202d001c650b564170850800400b40040ca610981080410500178010400c407045450b10b040c50000c2c20300c0102440b00710080c00700b401404404145003500c0000a8882d40e4100540c246c01d50f110303100880d441c0d00c0e94442034039000b01d01906044645c07052013000403030341a103040006080140510b95110880300074400008215610510001181a10a109a00703005400c031180c0c548c00b41e48a0025840c601d416941c3d10051a582d024040302c1c4885000031602c2d00840b5415902000c040b01401507440c0c66540710b592468070080c90036400680840102 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 799057113 1250 799055863 799055867
    0x100801140108030403030c2103090506060409031b060e1e0d0201020403030c06050c130816140a05040908070c0b0d05010506130e181002030108010e032701110d0e10 72
    0x420704075000326003e5130602c1c1c00c56400f19455005000c0545040da40700d62020b08031740811040001130240c036140040c681ea0b041c90003500b04800185145c2c8120700c0e0103d2000482d0b0000c2d500c1d4040e10300c2d02c03c90035a03007402c0d140c41c0004103245804600d41c0d105506405c4da044200c11483c05080403a003080301c00448080364104d0a0b48124000100040c041c0c0c0f031030800081f850781011b03400404c85900e41e801c20519502c19051600d1982c005140ea50001105030102c100c0d89004402802103c0081802c04000e00c4c042a601d40311449101d0040303513940c44910030f2142c40c00a4940003a4060600c03c001d0703650715102003043d0004c0748001c8165140c1000003070750b85800d00440c0d21002c154210395400c82c2c6001c07920751441100910340001c200304280d490b20000d406201021a0705c840340300058481d410b1071101c608680701d441210116620070800f00000c84000949074000646819020010150300d00c0101d540c65070981d09100300703104103103a81d00030341d030410b41c10b03604a041a0768001710300084c0740c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 799058363 1250 799057113 799057151
    0x80706330302040203040c0504240906030809090703110c03030703231603020d0f050f0703060b1b0c0907020109030e0a21081204050601060e0a03080405011115100801 73
    0x305480d032503803034404000605058018541c0300740a000d120f035845590b80301050a45604d6030a922019212101c1000c003101041044400750440300c0702000000e0955031101c1103403040c1e4038094450200b12000444440c403d40101c01c0c5400b40281441c0c56814030584150b0703075001a5280f00c00301e8100b90f80e10404100f01038030502110000d07000010203898882e000050400100014401c064003040311244e681614000e010441c04014400184ea19000d20741d626407000250240b801c05041642c1007007a1000d001c01c1d144440a03101004680c4070984001620f0204000701594215590504200e00c0540640c41044074a00076120b400405400400300196442c1a004a0312008c080500d840032260000540280c1203105a03280703458680c4200100300c0d01c4104076000c03682035010070011301144e43d01c01c03c0c1020603001541d8008481d41995507082d117030300440c0a030a040195004900700d1401040201c206901d001101c0112241046000c06554100c0da000380e0a55608200318000d828a002c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 799059613 1250 799058363 799058441
    0xa050c0a080403050304020a052d0d02030d050d020405040f020a030b03010902130b03070806040c1728020d12020102041e1203081b030f07120b030a020603090a080706 73
    0x5107488503990b45a605940c113401c0a44183c0e04281032000128250f00c0d24013042c42054a05844030b01c050300710207100c01000c2d40700040c160007400540100b1006072000902d0b44090021800d106813580d144842000003402554070540d40079040c520340300c0071091140d00405d0440300a90302800300141c01014142640d810304402508140c081c42020300e005002c1d40b000802400040036103d00c0c55030f032507141d454528265030550b003110407414100582e0070701000040e0801034400c083c000a18a000018280050140460314212a8120b800c011135480a450440907030380440049643d0a150200038000d40090003034007820458820302c84c840c40310000d81c04d411601e050720101511851760740c0440701c0c0ba9015042c1c03074481815044086015250350069803243c0d030b60141c1c1100d24580610000c001d80120212034509518010729240c00e920085000e240b40760301980d0302a900d440c1c41212602d4a80c10700d07400b03010002c0108035030041200c0e80d00128401b00c2803929000101d04018001e005e8800081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 799060863 1250 799059613 799059617
    0x10f03020306210f010e0706030516090306110f1c06060509030c1c0b040f1b08030a0305180d090f0806010602060a0c02100606170114010c170d060b030a050c0a 70
    0x80283d400c8000c15040010005014000e4540780018219010300b502d4614082c1102c076000040f0910450703034140f00341035001c52008a1403140b01031450014202a80c00d00024101540300c02569042588120846445030003040b841e60361a120a407101d10040b41005040d480c0c00d040010014505200380c094a084503c018003408044031030707800304880442e40c410030101c0708864218a102184900800500c241d01460300303400c15444500d050b40b0100c240110302d02d9031821068007482010030000c02d0381c4003030b07400307042c00115a1520007502c10242003c0c50841314074400c05084400c5682d1040c1310744200c440d8030000b0105541c807111500e484040c01d0281d100103a10100c00a0040620b5401c010b400c151540103440750030741c03c100001f0558500703030022000300e00840e036826132081c1d0142c0424010585503000207440744021000800b60a05080c010b06038000c08042c0d5007107010320104507410814580c004114003a921004a050358208654503540d02d07180c14001070146902c1d10459048007200c1e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 799062113 1250 799060863 799060879
    0x150e010602300f030a0516091e03080d0e010f0605010f120603020a150806041a0d02040f0203090d09080f120f0c0111030a0b0328051218010f03020306 66
    0x10180424801c0780441120070034503041042c40b00c20002d8020018010030603070003139880c40c1a20100d0180c0741c0240c5221500c140c010700502c4081d500c40200c20650300e80e23404120004000c41c07030445d00304015810280808000003511811400c40d0b41c482080018213000038801e9074038524100c0110345891190a0104210f505504280741c0b049000100d6444146800514aa100e03000301c0d03100200e6401c03c00015a2800a20070140d030007047c2c1903030002d000c6800307001a003c0c082400035006000c0410718081c51240d1041c1045540e142c1040320f1080c40c246045480385405128595541004e00c0c0210201c0c24001c03011035240f501140200342c40c10701800421601d00440b1a4007600e5100802030100a101072110484802080c006d0f2605021a4500c032038980c10885030000c116144040e82ca440b903884022103240300103166003907c140301b4180d0321800c05070075142421414046091440d8400110004010071110344155615041d00ca00ba691070f004030b030b030721002a400c900c41614081d6100c2c2d19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 799063363 1250 799062113 799062133
    0x2205100f08121b07030c0e04030801050d1203050702150a050412020a080a1202070605090a0b10140906010c05161503180204111c060e0a02040320010c08040801150e010602 75
    0x909044203d40c0904480c2c1130f6549803296a003816858101e20005444901844185a80610540d000d0306040f00c04402c0c140c02680c7e004d040044140d200814107441d040003a007403600034021020280310700c000c0c40340d09250481116004090445040340c06594403900d0b240b066200141c402c6819a010501500e48513520505541035a5012140d110f00c907020402c810018409010b16030080c0b0030000181800b11071840c09202c0030500800c8000b914040b13090411505407684c0c1040e161080540300c0f80711b10b172070701c0004071a03071801c002c8050142d01c2010703041000184520085d03c115205030703010a9035002e82d03202c21401d0700c0d0000300d114030f2490190004000f40c5803907840740741802640c030122481c19400103500c0c403003801d440310b40910059841108000c2d00110f007407402d92242c500c020031494207007540c1d070b182546070700c0c3c0401c0440c910f00094282c00903401034003950300e8030b5007244215844941e180c00d5180a04054400c03005a2202c03c5800200403000c003000030305a54982c2c003c1c1030300c001c2e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 799064613 1250 799063363 799063387
    0x5090604030b04151a010806010e0d030e06070f030f0e030123100e070e0a0806071b1106030c1c0c0936020403050f0a112205100f0812 59
    0x9000c1c0040d2900c1901310180c00b040c0c001d5205400c122200880c1da00c60030b280c00400505808001482c0f6070500058134000101e03031340c80d10300d415985503041c140b000e4100701f0400440c4d0a0b0140c07010040c0014001d40171a41807680105c041d00c1c40c216259204d49030340603013900b0300d03084e6500c030b02040c440b10300ba40c00070000c034041103803020f5481404100911903650b61250107054507802074402402143c4c000d14403504d94208520400b000e401e20000604541c01e16072001481c248049030050f071104290426082000300c1a1074010440b94003c00540c1c503420081720315038803070307210004103444121170003a030b056031543e02d01035845d000840f5203070b0b880654504554017034041e501844403407100300805000342920301840704c0d070940b44280300001a02c941c00d52401c0351608401c60115400b99004400c408001501e10700b000081a4050751070b10a54071003507030520402e0008413400e4060a0a0400b0001e81000c6110710790f080342d100b003a00003a00395640c0742458851041d19042c401c000001c00c0b2501c040c80c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 799065863 1250 799064613 799064633
    0x204020c0304330f0c33091101050a090b041512050411060a05090a0e0403030c1707030207060b18150a050618010e030f10050a1107031220190509060403 67
    0x2100740e0030014880017565803002844255540d010344e859240364101c540074650810b0302c803001e800d030260800041d0404d445004001c025250042c0c108071300010001200782c4202889001003848829161300e42d9280c2a044030780c00340181c000000039441c0030051120056600505006680240820170710a0f02801400921340c4140c48030710a000080000140c0c0d91107401822000301b1048a5581a5080c64500101998006040c960800c402400d4292220b03801491151b00310307940381001030342d501030b62030300382c1c081c0c205182c0c8164070240d403024840b540c01110204510403004580c40781c039800030041c1081801c580b05d000e8250400000d105508020741c80004c0807000b01c0050511184400c030546c0041c0c134042400130081030f550012004508800d0311405143d40120300e07a101030100d0700c031000e0076140074059903002804008681e10604260100d903404415000181d001003200c64806800c0c1d00e4140e4814180001981800c4054802a034800c0d8180c9410000050030130f481c051075915500d03004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 799067113 1250 799065863 799065887
    0x105160f03091e030203040509090309010818070f080a0303060e22020f0a1d070c030507030810050a080703150204053105070804020f0102072702070204020c030433 72
    0xb00c0700700100c03400301c02c007400d2011954070a0b17004590300c80c1094280b1004107009012108281d2051203140081d0381c21903074069000d81d0412001c00da08202e011160315020280d40210103c40102202007040344002c6040345402d4020f807014400d69903180c003152000030049030a00d2403c5485422a20441502a0012681030000380203500e441c40350320000322051210342c00140705100141801070800c01c280200380c0c2c044402e0401d00c805180c2510080d2841c410b12000a081090820004890450b4814007070301030040903194070b41d05521800840e940e0a01c6000c1640d0213480f40b50796001d0007116008075400d9a0001d070507202c04102c42003100c0d2800d030724040d81d002030182044e00b0014140d200c0c03140b20310640d034507943d0070a64141401882441100c01c0c551038119040a0700902c04240091250069034018070804408074084580050080c016014029840790000654940c40380001004d802501d11903140010700c082a0010002500131680205824a00508110b036629004150f08445 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 799068363 1250 799067113 799067123
    0x6040e0106082d01021c1d011a040e01020306030c010507020321090a08211303050a0606030b090a0309060302030a06030f0b090c0402180f062a0105160f0309 69
    0x105516101c44504099a10103024a41c0716400003ca1481c1d4a10790400c108141510085103000b0400c5103c03207140440f81480580c09403142044000aa1381c1e24440054491090007040700e44010450850b81d03048250b122407241d800d01c22480500701062007164002e602c010b00904405084800640d00c2e0b4001e4001640c4c0b500455568030300c0e896142d00010100240011210361f142000401c206501c0711642181c4800d510540d210b6a4141050201c4034528803c1c140c107945441715610341c2c3c0e010340e8080d0001080c500601000c0c07410070848e03030440c00503039104124103441d59940c40c1c4917a0f918400a200940061100c01d010800b0354000d50055400c40c0240c4000318407943c07030f6121032120320400001165482c01100c1001801c41c020300840007008002c8400354500842c002d885460140714503565846002d80300d48035140d41e95004200c4044059444861621711601c6412205c0c111005078803040e69403c4c031001a00071106005540c0100c00c1548443d80400d0f1160011401406002d40450f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 799069613 1250 799068363 799068371
    0x6091b230a030804080a02031002160b10051210140c03071d10020307030905010e0f041a030d0804110f01050307050a1107121a04020306130f080706140709060806040e01 74
    0x10103d580ca10050000d80f1307413500101080e02880c81414504007480003010b0316244180540c440f94400307540d0100c2c03829040a070040282d1070700d24118940350311503800198008240114240324000c0410018000d05007048104022400038000c0c0c0502581220000802d42042001409442c000d250050b03941d107183e00b254070030b80032010120b1840c0601c200c0c0b403405a440880d60100700766008420308003801c002c0c64a0b6500010040204004c07050300c4a0b41d80c4101d1300c502402802c14001c0c3d14038180c812004086134490444800007400e203d105460a94040c000700c2e40312007643c10000c070034178211441079403140c1c6560b8460310100c0701601706007410001c10441140402850204014240103040500801d04c945841d80c80e008445004115001c801c507540402004090307917012030700b640c0c0101d1005003c081410740b45424102c0d00c0400000604209020801d01c083c800380e6413195190328030038480600d00d512000c1d015646800740341b107003800140c40d400002c1e103039040641004031a0301d400c10001c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 799070863 1250 799069613 799069619
    0xb0a02121c110d051e060111010e070603020702090109060b03060127060f0f0306080304150c142406031b06040e01140a06140f03060a09020706091b230a 67
    0x9002e41d0010035201006a00102d600f40103201c051080c00d4001d16240c0c00c2070f00711700f01d01210001e1a4001090103050100c803e0701160314080030f4014030181d02500b402c0d6052182c80780c03400790082d000b894090340500c84070300012801c001107100303040c20340b000f1040082c2140d440782c004444204420007112201203000002041204810403404050718050701c44000c0d44031f8900c801402201c800c0564400c0600709041040544808821101950040c600d060302c41090818182d03880b0145890003000e508050084d001c0103200403808010f06811503095501c042d10074802180501030640d1083e82c144c000c0d00da8020040c5020010040c0400c000d003c81c0e0070f0945d2a25288141c8009911500f1401c0e5881d414008904c0c150b00080090480b6080c2200303c8694006900796034080d03040d01c101d0140c1c000022481581c0c50b449881f000b00600f6800390355441141c82c008014218101c01201d00d0052918001c16413500d00074a802500d001c003440e842d000060781c10200308030700040c1040760040e0045a002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 799072113 1250 799070863 799070917
    0x302160e040636140109020a030224041e14090a27030315061106011701020714030703030518030a0309020d021c030206070513050904060b1c020a0b0a0212 68
    0x79040f8014000f4800301c580685052039140c45642d8461800c00342d2400203650300590310003401209903501540d08402101031056010207260300c824600c40d40240120300000e00300c5440600300030881c488081c2c540c4041e80d607411004c021030a52045607000034094002003031840e655101e688401c400340880030004000061210551101075410303400292110f1104501051100c40b00c801000289020703c4803801c8100d000e520b411060060414266901180b210030000940642c2c8806030000b5041901c000740c2c0111a03a039503c807100490200342402c00007041046e1082120038030240b0b08029519100d41c480c0d00302d005285841089900c444140c00340d2000d45c9030740207583c2507016205042002c8807141d04000c0d20344100140381400b0010100501040e81441403868821a0b4055501e84030585640c5003080103040303242c02040d000200c2e01c0c411100e82c0c0340040c00c44e0701c1700d00a42c1d9600c1403544641c03407a441c2d80704604880015138402c580310381034207171034000502d40c0c003a040c0186481c003171000c100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 799073363 1250 799072113 799072181
    0xc01060306050c120f1b07030215010906150f0e010507050a0609051f0b1c051e1b0d05032b020c0601090e030306031e030d0203130302160e0406 63
    0x42035a040c140410009032140100851581000301c0405c40c44443c03800400001c03000c0c10700d400034803810310040742c400708240c02005282905d1202c001c180c042503850f500360000424551160350060000c501ca00b40034640981d0380389010b074082e0f95443c0c0c0c01d4031911006480c4c2e030740504000c9401e4418040041c000c10305510511007111f200d0700180a60f810000048082c012070300203107400e540d26000000c907095450780007454410902200102c1809001c0c10300c82d08040040b55006001d0702041540e6038503140105505607005008061511418007070000c2c4150789180e200001d2845d4402c101c0c56001020086000d81401c020b07017442e0111501d00301200051740c10100b01e0251581c801d0005225040503801424000301800c0000d5042d49040c0c40000c0d40c51015560341c1e0a80c2080c0060248606004c0c821240c10881d00c1000355500d089c0300c0220324810142403c289c0041c05903015000710004440114011550049452039460b120b60322a140123040082c00440b00302c042c00c6448888514180c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 799074613 1250 799073363 799073371
    0x1509060309022d1309210c02041d06070807181d0901020c030409060303030f180303050901110427050f01140607020a0303080a050c0c031b0a02120d11210c0106030605 73
    0x5c1815034081c80c1c9412002c02007122541003080c2d0071039041c0c03101e40c4240c0720380116070101c7d00800c000315181040e5800c19070110801d00c190084804000300769400c001c40c0d40c0209140d50b61281000052010799603400c865019494003090071400340005a41a808942d4100c0c0700b1900042c50088803142081c6981d01a6100d85081c0740c60705805c006054061080b1101100881420703c11510105a0660310307607a040b10040c1072595400c0402c0d10b000c400d60080a00007022004556580d032070300510400700d40402505104109102882041150700703000703003400780002d440d0181569007400c24403500307403440d401d081e90460000d009007405a5a040d84401c011800303038482010340c1c1414a400026964000e101d0f480d40001002040c2c52400c00104540c000c80c07103203003146c000e183e0303030300c0c18600340320906601075400344250441116413500401e600214540c941c4078070544c4004944e0042d2a021411078486002180311020780a48d51808028146c000c00d040c000030b0b0042e102c7d40c0309030403180103071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 799075863 1250 799074613 799074649
    0x200604030c12050a1e0306031b0f080a0c05010c030e04021314010c02090130050c0907180e07030f1b09090605031011040b041509060309022d 62
    0x16100014008000040e405610302c0385440d9207800071394140600302c41c0c220780d40c0c1120307242c50321904100c56110f940014051a0f00ca0818088aa0041416815103a283c018403000b44041540080c40c040000307210071015034096002020980340200540d0f1418426500b030f0244000390495000c1035449100030482110480e40e1514a2401e00400c545500421072005040c006542114005690b8644080d81114000e050032783c48400707801041142954003581128248880036030844c2003001c0400c904010030803d441ea0740041ea00d0100032140005400818540008548810b210341ca8060300c0b02640209182408101010081001412030380702c0b040002010410550030540190f2015100000f4240000244410390805000035201d002100541d070296989804407442c0b004690b0988006140c8942902d40f110b80d81c00c1d0101d101c1120900b040001100c00310081041070007840340740c44042d006012600001300241105503c0c1181141d0341d508a054003584506c1a42c1c2e8110070460700340c0308 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 799077113 1250 799075863 799075877
    0x12060d150509060a110a1202090420030103050d0903200411030916050607030509060706150305011512030206240d03120501080706080a09081c0213090e0d20060403 72
    0x80d1340701800700d42c502d0092400c0c49600f0000f4484940d4040741a4503120701e8401d0050b604e0154000143c0100b4a640030954458891500b61144d04a42c2010798100d90144082d6550500380300c00407199401c84c1c5c000140340b0807081c102c240304414501c2286034030f180d0240001940020030f0030408100e400c1100c2144c0940e00030f081910001c00500d2900380105016140d00f42040c00742c0d40d0141003401104007844c007544c404103601081c0060754100308a42443d60b61001c1480b5240d0410341c0c082c00f8018030204501903007200020340040e131204501d843c241c040d40500b0380c0d6151800001010300102c4401951074140300f002603c2555100000410340703220344c03200c00702040b0003c0740c401a41e4051b0720819079a00034146c00c101c21034000040a900c103020200000308550540b60207a40d90241c5c0d0612204041d50750041847c0d482994010708002c403440c0c40d4810704941c0c5090700000d880072096048500c1d0010b8a004041074003c840f8808460040220780206003e240801d0b442c01c6c404a03800d800046603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 799078363 1250 799077113 799077121
    0xf0305040e01120614060d0609020a090203010e150a1805070e04050a020403031b05060f2a1803011b1b02131b090803030c0a022508010b010512060d15050906 69
    0x101e0b00c50380020012040d40f01645e454201c00203400312000c0e1a025101545400709c4508640d82c02d9441400b6045501e0304540f2941c40380c0e403010032424100d961002c904642400c0410b20b2400c440c0c590120741d51001400901c5541c07090803005070038041c103c04180315150031510710f60341d0742d4000c042c8a000500001600d80b465401e0041601c41102452120403400200107004600049190b5030f20000503144550907403120308003c000d000700700c8090046003980d101c0000005200a0007856002d1240040c546021010030401d4225142904000c910308400c044445c0b42e140100120400444010340c05100c4a80b5a004256035075030002c276400d4440c1d91a034004c1443c442000400f60416094038003940c25606141c2c001d5502d20015026000c0040c000c030f12003801a02c03c1044000700c0245080c0703082030b1000c1c43c1c07410140c1d8229000303a0100e542040d09502e020351140f010f0704e02c0700c040b201189080362a000700b80f2035040c078003100654003442d00341300ba00000c284d03034001d90b40940d0000c4024040f81c0380c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 799079613 1250 799078363 799078373
    0x2090d051522080a0c1a3c1803130e040303180c030201050702040603021008040309060e0105031503030f1c150b070201030506031c050712020c0d0f0305040e0112 71
    0x301003207411402c1440e0380086000710381400d040c0d642c1c001030741c1850b020341146400c10030b26852581481e2101d244503501041a01d0320b00651010110841e0100d011201c21500c103a03030011842401a0001001e10074002030984440d6800f030340040c001801a00d250510000548450746270756044070710000f01840901c8201030307040c4641880351a000406a43d81385966644641170130712844042c0c1040342c0841c00c88155a6264000b000660303008021500c0029104c001800180080b40d0560204641d03070300000340103004800580d01290140e44881c55560383d40d00d002e514080400f0350035058070003841104030306124040246003c01080050702411b90150859105542c40d0710a4102205050113081203210485c1b000c1d59100ea40c2401c012506031303030b0003020900c1c004120619518035500044810440358004000f8041e460090662010f02004101d00343d942d2074002101e02d070003116040f203d10200341f40038906000d040c428988289070640d47c08550b2510482a0000d404001c0d04e5003400c42040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 799080863 1250 799079613 799079641
    0x30f0705090c0702060403080715020712020606030102090321072a080d090b0904111c1503030f0c05030906040f0501110d05031306140c0304031b08070602090d0515 72
    0x210750b140700c1c03a2900b80140e000c01d6060080748801890080c02166138130801c03a2207100240c2c00d4500d04011500e0307a0070342c10480d6442e840c0007240005801400041600c509040c000c660300e110b00640103110425915980c5050521852151040e1003400c0c800403001542488501484109105412984016800d4090b50010081d4010202e80d1700030b5230803800d10b40c5c02148041c200d8042401003030b02c5141840209000e0280300c000081030400014107414480c800307035414810210910030411800112040094030300c0014000580403030700103481c0d0a01d13507200d003010000700c034440c10540b400c2c6000540421003642154110b00381140035080184815640109400b04010841d002030054a0701140f01900c0ba10001d0495000488941c01d00802c3c801180c10440c110309455031451192302d028010318005420944080380094080100c039080c988070046903800300754026034007602e00042960b41000a500c100c8000e60040040c42c46140844c000784810100303400e0142520380a8600030980b50340f01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 799082113 1250 799080863 799080871
    0x3140106081902031e040b1803030c03040b1f0608010512160b090118030f1b080c090a090b0f010819170c0a140c01030c0f0e040b0a05030f070509 64
    0x400e281003040880c0c007041868202d4200012401a40d1352a801416030001c07011001c0b80b50b01c402c01c0781c148000c00a040d0401482240c1c1c00180488581c182c0c0b004031b440b07210a40302400d0441c01480480d003c500d440c620540c100840700118500c1001245c50220701050076408200814a10001080f060800072117000ca1490f007803014004184480560042c006094041c2d091150b40c0483c27040c0199004642c080d006406000d10300c01141d0780c034501981807194a5100301c40b083d281e800282d00314080f0810f05c0b0241c0b10071101500b1030259203400c0c0841d00c20000d0502082e603031141002008a030b450003003c0e0140014904d0315281d0f606003480146070104000c00c2c01080011a0304080201c2c1c3c8441e000030040070414030003a614202d06200900d071600080703000e00805040701c029462010f0004003003131940d1003a2001d0000007111141924041d420b0300070403001c511800c000020501d1b00e580801c018140041c401081c254407100445c0c81c08800c4c0e1400185035100c80014003040c50321105007984 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 799083363 1250 799082113 799082117
    0x6050603010506270c04080f03030915010b03010b0c070b0a050a020c0906010e0d140102220e010b03011403010f050901230105010c1725020918071701091203140106 72
    0xa0152002e0000c10702407510801e207414a05404c0100c1d40050f040c3e002c4a00800d00c84086503104000803012544a81c8207135101151485000c20328042d810822101034102d8104915840c11a0f207081400c0e0480d610940d40c0c03000c18064000003089480240c009040c0d0020039546803a214081c0f00006842c1520b4215810310512148041000c147c1c3d020499510a0900b0b6880d5841365900b441c20903030b81d20114240c49041d5001064044030005050080490340301c0f8400c1c0a5040d03a580d40c0b0a1100c14400e0040841102080006201440a40c008042c0d09400036000140500090240d1000c50310192900c00c40359443d40403441c60754200e103402c98144032003000110301a5142c0700004c0c02101503020028080100c0066010601c0010801d40381c0c00d0140a4102c2100341c403400f01102d1450380040c0803445207044a012464a0442504580141039000000d00c9a6400c18480480141011000f201c00d5034035901a900027071300c0c5135500203240105031000718018040b040d614011400c16000202 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 799084613 1250 799083363 799083379
    0x91207080c041505030a030807080c0901020a0201141e090a08070e2d040503030711011b05131e080c120303040611040801020a0215070306080c061b0a06050603010506 73
    0x4000004544072503a03003411503001030000d0361040c031442407480a42c02950300d40a14105002816000800c0c248501d05e20354480e040390b941c0f001e1505042c000c20400500590200c0405401940181607518841c01c5410790581050074440d04080c14001d02d0690420000f8086074030320f2070782002c44a0202030405030b0090042d56041515401c00300c80018030100c680c000c50607000101811a2440c1141065139880300c2e105440c00c1c1c01c200e03560744d100340d42c0600001c6020203400c48200040c4581c1c5686d030620b4946d00600e501c0700c8400c903a581c00480300d0001c4446100b4000455108501c40e901c10700780341202019526103045c212f1400c080e2454076481c06643e174807454018894005c412a40c0c015400303040040d0400c40c0302c941007001d00031a0461401c9610018003c1e00c0b5540004541a180042c149141c069aa580d07504600343e030300c5440b07100c41682c400c0c0d100e500c140c5402c80117080111564181030300c003900048116407800e120721005a85560341e6800744a82d50400307000b00f030b6001d40e040e60481 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 799085863 1250 799084613 799084619
    0x22812020c03070215070f110906150d0c02071e05030d0305040c2306030c03041119090b060d020708040303270302040f0b1f180b030f0c07080f091207 66
    0x2540742e100f0924028170456083d10300301c0850b0360550903920a0313034024200a00854091a002060801c0111207512401c44c007000914145003414614248241032089a0b041814850615000d40b03802500c040a5000c0c6032000303c3e10810503001d8918642180200034003c0b07140c03074245030400050780318010402d81010200030225100502705021980410400480381c141c0e440340d140040580034400c2c5c1e02442c00006c0c40084010403001d94040e9008401c0080018054010080c041c81501c1710b0080b02401c8000411800e8080d81c802c940c1c03444040c14852810105500445c202e91001d0411609180042428010325078040750403200d0000302c1d8002260301d1740e101c1800300900c480e80300092007103465502d581140c180c0703a0014100c040002e01821110380400d1880ca0040d1400085100014201c02051400c001805e0051045904e040550340c5140c03100480329581040060606841440422206001680100c0241038641805d14020f03144c400c9182004012450503a100759141d020075024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 799087113 1250 799085863 799085887
    0x110d0608030f04061209050a0609020907030b030c0402210a150b04030317040503120c1815120709080601090f0b040207110f12010501090c02010507020604050a02100302281202 77
    0x4401342c82850905183c1911242e40c0240506040e0754020070600461031110104245074001003102442180d0025290750307070307880803811103585d0304013158594000f48034000c40341003503801090709100e805507070401810342c5800d107008104140c07081140140c1e14489141101108072820000c1c00c1000c090b1840c00385103403070080029800000c1160386881c0d60002c01e0810400f0001c40382070607201052100e41d4604034a41c42c21541043c0035012030841c0200824580f841c1081948025058840d0304074248500008445042e034801800102404034a09010031803042c2041401d0003080a96808510b168032000c41d90255680300821a0040b4010300030324002422901d60062288810b880345800c3c5501840019150b4014003c1c0c4078455107400b0000c14080c0090f000301c1011007040e0000e10103500c980c3d104982e0380c88202c2d40504a07030031a140c02e00061506071400001c1c0c0c1030071700c1d015007480c00703544130307403200c00d800300c1c107558040000c4024641c2d0b554104004800c0709150030310441c14507070040f0320 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 799088363 1250 799087113 799087117
    0x12181903050d0f0c110d02070605030a0203040507030506090d030b06030402061c23040605060f0904080a03022505061008070603020d020417060a05010f05010e1306050301110d0608030f 81
    0xd0a1003008500304001c00015400058218025031082c030224051000160501d01503003141502c50042907000b0004500008030380040381c10656440e40780d0341c2e0f2410038400a400c054021a031502a203c3e0001c0070450410605002d40007103c003030a04511210005000c6072800b4a405004900038400c1101580d10a801ea0b1100c401c20890b01040020240202c0001e180fa992032a03542d039003075240b07540c546110f105180e105034800d440c2001552503503804c00a4000b0a80702c0f0b15030111500300043c0c00140c241000d09001c09084c00c0240c144240000d240703050104414031900da99980550130406d0000800c100c0742c0040500055403012800c0c05030f0ba903281c80f0540185000d01d90002201c071a0002554100c90003400205410308091001a024ae44c0712002540c00b146258281400814040038030151401180e4058460038020401d40c01881007107001075503820712043c2d40303250008141c0c40a004404e851260711154956510002c0c03030b000d04031290398000c190b0316841031209000c09186402 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 799089613 1250 799088363 799088413
    0x30902010c020405090c090703060602011a0f060703030209220c080c03070e0a0e100f06030b0306040201030f0b0306150118081902131a0114162003031218 68
    0x802284c0b07039a6000c40c85141404080205030090040c404006500c1d5140d4070840646a41d60b0013401044490070720b440e40340412841482d03024a100c2d03820100717442c0540081c21424400d040140c107054a901c00100780034100d50211048100d0b16540072010704552180494039103d40c10000303e6810038040c490428000108141c060114401d80444c1c55510416188010074200c0c2840350705240545a4040c0c40c3e009206092102000780f1003c554a4000c0c054240320075000b070b0003403000341e80c0d035001103000d403a0041051100a130740784c20041498800740300a91241c10400d1349521380320405000100002000076417600c60350841403090181c0d200c00f29003141c240704002403055107000103000281c2c00003840a050a40d140c505480186030400f030500c0002c994400342c841149844448640d00c00354854180b443c0c0c090010310394104009200300018a011020000108240c4110344e4042803540d808040ca50801c0c0394108100300031003050040828030884401c018000e00301510410120101a80c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 799090863 1250 799089613 799089619
    0x4150501084e0405040905010605101b11120d02011505040204030203070302130b03030c0105040309050603040b0711010e01021309051006230909161e020304050114070501020a050d0c030902010c02 86
    0xe03600c2c18558106800e0320094040140704110318529880c006000b45001d1180700e0003101c40644039080c0074010100c03200070800310610810784000c070350342d40e400e004100c01030700354400020601c003014240c04000360074031900359030000640078400400c2c01070881400e52080d8030890042006000586011941508072941540c2c0403082c2c4800c81c0e41000a008801c1c0001e805102c04102d0b0a40c03907005410541c003c0d4060740700c0b41c010a45035824826a8802120040c10140e08100800c0606115400050009024600018012001c40307422800c0e1380c00304031891580c00c0c1c0070380207001c04d035917910840da049074544221014032031a00038003400d0f17001c0c22000c11014422020303008403140907201c200c9012501c0285042901d02d00300101690304902002c54034001400800605030074004c10300203030a9411a50002c5052a140c8001104c61041e800d41c203d80a0344148482030008009002601010185803607a42d00d482d25491094222400c1c1c00d200d504150400c0000c40251342c0254155059070307016 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 799092113 1250 799090863 799090993
    0x150306061005031317040317070803040f11040c030b0a24050a05070209040803180a0309290301090b150703080a0b120703050c1918050415050108 64
    0x802c6000030301d004503134043c00039403841d114000d981e0b0000d0000c0c015207104207514070010040302c00217090b5000c1c484004220034410004038020070254411001031900c80d2081401110503c0d000c50282e07003c0b190860003003900e0340c0b06000c1034235010340da100c0a4040c0b24200340603c0c00e4540d10b19000c2c0c00700840070060000024403000402c0c480c2c0d040342c241c00d07005480000541414903140d6420341c0202d5044d4141e2ba00104c005100c40c00c08102c02c000e058040d40d0303003c05c1c541840460780c03d041198038060566401e250549a2104406000c0d50080c0020711001882d10200e00610601003481c4a0000500f0010400c0342c0002e500841c020382c103c107002c400000c1c10524100401d020030b102180c07492461180701e100100f08000001c080078041419210002c08034600155185450528084e10f1021440c80105102100301c80d40025031050080c00b2000310040002c19800c112082030700180350035000f220040c803c004400c13520900384010307001e2000c203070b640c46900c011002c500d50784804445111 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 799093363 1250 799092113 799092121
    0xa06050c0a12051e070203280f0615050604350a06060603110c060c0705190308040b010e0c0910050d0c1215120b0a060b0a03020315030606100503 64
    0x10000d100701203500c00e492000c045049000a8010b4220300700507110015080000b03070310303602c01e41c041e22140380e8083c004241120b403503880c2140920250026814107503007203800d100070a80341e00883c0a058007071640081c0c06803d4a40d5404c54207180d802a40c0643c004010030024880c003010032140001081000c1840b10340004902024070b24662030014080c070807640c0030800c0c0300e86d03540528220380140d00e040280540d984401f000c1c3c0d004646004450340c000100049034442010003d00d4100c3c880e105449102000c000100f012074403a00041d030000b40341d0000c2004000c101d12001e4098075a58480c0c3c819403500c0e035041342c1c051251400c014010021180c1143d0b03841d010390180d40712403010103030030310600d58624402401000d40062202c061400c04d264003642540e1a120032056450341c15024815a05549665001d4440601001181d41e86c8040001356201e00d100603150340d020030365026a8030308041074068111613681c2c4005102e81c2044003030001a54072910070001481d01402c0c11602d90765 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 799094613 1250 799093363 799093387
    0x5030f0f030d050c300a0b010c2009040506180c0f060d060b18040f14060616020a03060f0e12090d08090901080a050601210602030a0b13050105041a0a0605 68
    0x1030041707204251110b0683c2c5020119101d50301031035540007405042c440d80c1d601d55140181c2c1c0c084107071140444c3e107101c4880c1c0414110094400d0407501d80c030300d00c2e00c480380b488041020103600b141c5c00d4990b508500d0500c108001000d81281c00d104070326005100c00b41550000176800020800e0a52003076200045070440a0820303004440148100d15540b500d880340d07040080c04080e02c48502c01c0c0318034946181c403461010284210520046c024810821544e60342d0144060340d40a4620b01c0340040081c8800c1c00140e980e10f0021020358400c80022134140c0c0003050380c01c25901c07800903810300b50b00095860105c480410040d1680600101e901e500e84d2302d00c80c00d00800d13512504000c04d401090b13603c00402c05020000f01c0000b480d01c100300715109680c0c1c0d40301c41c1c451100010140d83c81680032100c0d100115a01c7e40186802841c8e241f0002200c0d03119000007041c2500d9105440b0019840300300400c10392515100351103003500c43c00d0f6810032003481c130700000b070700d0b00241d005000078080d0103c1c038454115 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 799095863 1250 799094613 799094617
    0xd020912010609060503070503150105040504020d0602160c0e0f06040c0309021e030d050406050a0309020f030d0c050d0507020607020904110603010b0403120302070f0b0a15030c05030f0f030d050c 86
    0x40c03100c020032105031580504809080e550040354021720a00c0400150b038100003d1140705190544007400b5544d003400104070141001410a0303a014110516010100b41ca603c020310400d158000500358240140c540700c0d20100165003c8903e1141c0c1c2e00c1007094030805004031a51060007260006580007600310264020105107401079001080d00e0031180c1d1400c0581264203c1070340840480308000c10b044000c544520443c040d41000640520041400c03901913004540c03a98402804c03c2d40e481180e90100303180c1031055071000002a05e050b1000c040c40018803514290504a00d0300514100c0380d03801103841032198500c000c5c0078114020028040c0096046842400743d0300070055981c95a6641e48500760f504030b408155a101c40e96480c0000c554064421603c500e6070285007400f0740c4101d610703042c01502d00241940346460b16220381c40040c1c40301b811038074051842010f04c0e290711800d010a05180c0b0540a010586035409000b0100042c400041510152255420082142d03515101c10341402c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 799097113 1250 799095863 799095889
    0x4080d090506071b08012d0605010c080c10051311040507021b060d09050a06060602060126102909060a0b0730020f1f0b0105040b040603060620030d0209 67
    0x294a130280c0c29009801416010181f020f80605195804243d04500400c840769442481d0200b5500394808000480400c081e04c68228600c1c10b0b1a25103024104502c103480c01283d9200326112711000c00c1e0704001400c04959541181030303030304004038500b020300a90f41d1000c121074400c0041c41900410300660712030f01120600600c0756402d012200c3c541c0342c10350f07031341d84a000c00312042410034101184141c400540780341260302404581c4480442c61843c0f00751505000700002980c05101c0642e810420707170703000d440d030400c02034040400d022450040300000131040040b650300c1211000180b02540d5500c2c50382c2d01c04d030380142840c0c6030386420624042c1411107884070001895004003003420050010700b60388414507003007a000c1e2078040c070800d04074940382e007080d8124031862141c0c1c54540201b000c0941c4981e95116040c1000c40c41d00e5140c10084c03505070495441640001d885034802d21025600c0b003440b621080224105c40c91509055952580360b004408101c10130316030203d42e0f09140d079540c2c0d070b03070b0185 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 799098363 1250 799097113 799097129
    0xc054920120409061805060a0603020325051c060b030c09130c0305100602060f0f0a090b0f090c01050310090b01090e04151b08131a010b04080d090506071b 68
    0xb03155910b070280c0c0060412842407180b5100007000d0304088441314080e60b4450390b00145104485814000181e0080d0070242c03268202182c00400d101c0d008584160a031090190380e01d40d1900c0f01600d0b880c813440700b00c079295514410383c00c0c032000f000007041e41c0c0d05503a00710043c9000651102d18079400306107140443d00040c80d5090501c5184a5016015070085004a80d4a00800182a01c414040c1c0e900d42e0165000103010b08040c000801c03c650201903640c01900128001c110740314103072201801e4800545403038908a4400007440700c002003c11400350084406e007040790440c07800c07400302c4004194903c54004060b031524541e00303050380b2072058500500234510042c440390400e420700c00459044d140d4041e031101d10b4507031400350f6400214142c600741071711b551316100142c0c0c0704075000c80c90400100c4100c0300407181e03050800484040e0182d1602800c100144640c403103107031100840c40c041201c40c850050002d203c0c828403c60f2940340c22510300c650800c3c2001c1040992028624040c00380f80c6c80346e09 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 799099613 1250 799098363 799098367
    0xb1605070503280309030e1203130308030a0b0a0503060703020f0d0615180b04120203240f070f0507110d0c090c0e0910060c05492012 59
    0x42c031050b03e150a4481d400c490b0101d0b60785198a1030081e0104d4a940401030086208860b0012032494030f500314004000c18102070728208843e610b2260043c3c0c40a070800c0398203000100c104200510140b282a405600858030307880030a14150200342c681c100139000c0d108054000807a02c81d001c0c0c00d1811110440740000040059039079842d04502100310050103000014600c0034a8004a5015007001c01034610341e1703007898906442c3c41c1481030260030110f001c0742c15025407001c62030b141030700000c144200010700186034010b01c0c110460901d041401002c9030240054480b284070301d80e1380701d019103840d1540107006e0b150703024000002894200003500c00030000a991840840c9200c400c0c1c02c840344150858075203880c4500c484040101004080300d42d410941c444003020401f8500c900b860340d0f00d1a002c0c400340d030085c0310b550a102607000d000d608800d080c450031004180200b61504001000400f2640d1550582020038000400003100c05002c039080b50503040002c0e030801000d0000c03032117000000b03040d50303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 799100719 1106 799099613 799099627
    0xd03051504020d06031b030209160813020d021203180904050a0b0c1c061a030402130c090b0304060b0102011d071e0b0c010515030a0b1605070503 64
    0x403902502d13000c0000204a003940181110010310700443d1480b400c600600c6640d0b6005000031005070b120509183c0e14a40c032042c442c3e0855441e4246010600703043c0001001030f201c482000e0b5100024100194000300c00100404c5962410080c2136802c0980d50100452460308580241c0300b038100401c0100090460140180d0222402c0d0941d410071035003040500071001c442c45454100c0b42d1b200d0050001e00e00300385100c0a244800180c2e10700d1841c0c240e002c0342d02e00d0301d500140c0e5043d80d183d41d200e81700103000b680c0e4031014000c1c2181040c0c8a2515090000c050488005910302551809500040d4044c3c084000801140420001c114247c9001d0129540494031540000000c0910002160b20040c140080400d2078020300003207218141078040c0411450b0046e0141c1c82540008800d5000a0307501d20b169a01c000080c00c44080c0050709001a509031007000e100504a020000d540 = true := by decide +kernel

theorem cover : BRFrame.Cov 798920863 799100719 := by
  have h0 := BRFrame.cov_init 798920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 798920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 798920863 ≤ n) (h2 : n < 799100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
