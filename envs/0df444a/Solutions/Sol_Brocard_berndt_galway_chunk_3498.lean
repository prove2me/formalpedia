-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3498
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:50:25.278725+00:00
-- url     : https://prove2.me/submissions/a178f2de-aa0b-48ad-ba33-ed809ef166f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 628956834 ≤ n < 629136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 628958084 1250 628956834 628956869
    0x30406020a1215170705010206040f0602210a0f0e030306041d0a060905150f060d1104050a0c090f0506070f3f0e030d030b061e07020a0f0f 61
    0x4460b9a42d90480710081004207445a04074400003800600408600075500c00100d990031000154240035140143c00a1009540e20780e03404101121341c407003c80380b00d6020b00550f44290b0034000503403e25112654100345518000600200322070240c075010381c05600b4a44803075251a404801c49130070000640b8045241c0c0b040202201442c03440c001c140945100b02c903400ca041c0000b0745e22171612188100c080d05c0c5140b07440044028000b4040e140421401e4422000c076079076141c500c1980021610954844520050000000d412240c00b1594a00e046031100c51494080743c3c44a00c40d8040c1010b082c3c030040c40d40c20070021a405006440c40145224000900b11007400320750910700c860321422b40080108030368210001c1640f40e04880c0004540030402c0b0b403a0f030541c0d01603000142c603000090b00422550308214011000740031016012a00700e241007110008807086500c805000d04100b410760f59440f207840c8107110030340f90345900c03400d101a01f42005002001da600f1000d002c441041c0300100702941d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 628959334 1250 628958084 628958087
    0xc1c0c020105010303120c32030f010f1a04051306090c0207051302040e0402040f150b0408010f020909040f020f06041205060109050702150402130e010506120d0e0d11180a1a06030406020a 82
    0x1229141e03011042000c010031800940ac001c6e1507050318500315002f800f10781e503803e140c00d100c11000d61420703850000740400d100343c2c10030b00f101c050703031201ba0440440d00507a180d00b894212194107400c080143c001020601441c07c01c0c141c180c20015030584114a441d03c0d2908203c14108042c100038419511020607200702d5059410000b9030b4050040e42c036200c40d0b0307607000d4850b0f41e5101c1d1041da190303035003803d402d4400350070039100b81c600d0001c000c2c20380400c0381d89a6442c1040d40d14205412a4401d850340360390001500c40d80301600140162650142c000165400c100785010016800b040016050100f0480210340c0410b845001892424500446032183d10014030b00c100003a1400e00c00398500302c0114107140054110741d010303200c152001403401e030304182d40701e4941c00401e505c40040f4004d2081d1201900307244e004108000d000da010642c2c900311b1800000c04e011120b11846000006d900d05101d00c03107640340701d8451824003040c0455032812081011031101c0c0001400a41100c0c0e01165a03000ca030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 628960584 1250 628959334 628959407
    0xc0c090a09080f0304060612150b0307090f0e01181101140c100218040b010905130b030a0b040b090a031d13060b030901110f030c1c0c020105010303120c 67
    0x1d50740b2509041d210191980301c080b01d0341007110240e034000c4c10001d00050b820914003081c00b016400181840c0c2c6004180c602602620321108050340600c82d0020004185405101e0301210105000300031518018040c01d050070b440000c0c241d43d100c1c42e0407682400010b485200c0403109c020b801e01305620402110b100c00110360080d44948a814090b06081001e041c0159000f40813115100703e20308250000300c010300080310082c0400c503021039040341040c0880c0c42e1000141d40420b1100c200452060065800300341040c0c0407030411035803c82d5002c01c0c001000340b00c2d00000d5000c001d490061007a600c003510010900d081031111140e0038900b62042c0074a40d11800543c0540800d10003040c0f1079281c0c1d4000c16049a4821225081603500c0d15079280300031072018007200c042d40f84000145066446030080d10701181c1c080c550b4150705002028561110440601541d2103114454000058542c5981005000030b4080000110100c0c0b40240140a43ea04415905040c80000e450509503048000d03002c41c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 628961834 1250 628960584 628960601
    0x130305070f0812091203301e0a0f020c0106031a010501020303070e0d11031509060106020109080702120109020d08070201020c090603151f082505090103060207060b0d060c0f02030c0c090a 82
    0x10802c4031100d40e50340c68060b10f120302141a00b15031002c80d88c0710244442811504840540581e41840110303203544602d401c0030080d4450110014504009041581c1c02c4500c40d41c0304030395080c60100a0090100315401c2e141c0181400e0014618501c0c1c6070800401285500012920414113040d03c41c003480018a5115980280074045803103c1e91100c00b0603500d1201140c1d4182a44909000842c0c043d00c1070244408070760303000e0b214a003020030316401c02181403500e80049140703642e2078120b540540d03102c00b0031004580c022480144e880b0483e00009003426400340045001c0c10014090041079140081e03e02c20030440080102261348030208050100f04084c9403000c2115542f03100402c00901c041075000003c680300e06c18288105103400712035440c081604c5501d91120500c8010070108031160010510030344261302c0060004080000101010070040742928800d13070390f072a031983c0f4642000e43d489509606000541c2800380c440340c1d01d5a155504107107540151044000b09034101100c2d0400001c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 628963084 1250 628961834 628961857
    0x6021c090327080309090921120703150302040b01020a022215060c12020a080715151a0d14010e041e0804120206130305070f0812091203 60
    0x2400c00900300242004500751030602040d103000006240d1001d550700040444090f82c001c2d5003441036141c1040308a950041c00c21480d4060401c3c01180e4101c82c1d403045403440c841305c003465102c8010101800e4141001048002454a8030125080341269011544100da0303046074042050284e240040342001040b540007908101011240303514004180285900c100020100700186180c071450306e50900440e00c6020045800d1842d4000425205c0c41400440c03c9030340116441851995140003543d48050401c0c2c0700d4440c032100102070a40c0900030f00b001d00b6420044902c055052607411001c04c010f004000280280c005000c6041c014950084613403110760072904506907a4a6407800310b410380890701250024290915002c00000c422080c07680143c0003c4504c3c00c090801c1800f03541c843c40503005a074441410f00c03800700c03900a043c1d01c10700070354491005000b030390b454031080c40d02440c41604030030580d0700803c0c10325007017011070000d451055504440d801c01640c07000d00c500341144145841c1c2d00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 628964334 1250 628963084 628963091
    0x209041503150e030f120402030a2f0f0a0b0c07050603040b070f050c0c0108070c1212050112020127030819020c04230403110f1f1806021c 61
    0x41405116003241c1d540001525091080d032079100e100c44c0d12480f030b207039030300d02102c00501c038101c0590192044940c1c070520203402c82d100071100d6226030340c040861319419074140c1d0290ba140c4035038061103103550307601c14401d5840301915807041000410032202800b4518111102088501d10684200011707001460040c1c11745942c2d0600b800e040303140700d1044803288041800e003240c41e444203110740125110000300d1000b41038011240c00c01141c81c4280034180008124040ca000004604400409a80c412054464040c4c03403065102200949005a006081c0040e41903200300242c1d811180746500c04044810301d02c0003e83e07131510016206041d0f0009401c1074400300b5000c0c08407540000052025104c2d400320b40f0800481d504000581d4159411040d18000d00c1d0000801c5074511080e042d0050304c642001010708224a038402e240c442203081c2100325034000e5041003e007030030303100901030104039200091020120b0080722a208540340140104480d5000a82c0c9441c0ea483c00720760302c3c0d440031090050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 628965584 1250 628964334 628964339
    0x504031209050a0606050102210a020a06140402010e010503070c0605060a0b04030804030b1f0909020301090b1e0f04030801060f0309080307094101020a060c0512100501080a02090415 80
    0x340e031103000034021038004e4604a0b0100d003942c00020f00c400c040580d800d803d110b80c1d003c501000aa40c0144000358150301c5004500400161070340169130b040250908800040e00d098000100116404001181888810000d001c0b105501c00400d4030300941003000401d25840c0d100c0841d04a2010b54820114007002080100c10800400001d1007264013810010091f9110b200c004200c190f01101c0807a0710700300b42c1400708902801c1d44c1040076894002800001c099001c0d8540c0c0b04540000c035003000101d94911040f42e00c0d000700000da2364010200180d0902289004d54024000000602400040c0120142d2001180b40720741c001c200c0071a48102640d85038103049801902000c0c403401810394100e500c100c031012140760851440b40810500c00d005a44014640b1070002803000200f101d4114081c041090011030702d14060b240e29913085aa855694903000300060b42c10800c0030302800317100707050300500b00141d03a40000c06a41141c00c5040041c1d031600c0000c0010014601104850391400442800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 628966834 1250 628965584 628965593
    0x2f030a06060e070810050f0d060f050106030c050c03071707060603030f0833040f060e04050c270604020c0f0709060f05150705070503031c060f0b030a0504031209 71
    0x890110b504400801820b501d5007402540d4220046a4000648103008010429807411043c0041c13420707000340c2000340c000801e856800581c1c040030140103107079450380010010756915200e140000320b0300b45482420500c1c06c15065880384542e40c0d02928948007101811911200c5404075011243e12505c1000010b68030301c2c015180e074005514a40c003083c150300010302c0e4865a810074261000320162119419520908520032042000c03000c1e40d0459590020900440301e248038420240c1040142d0081c00e2078103150040c0b4208244001ba8018100d920182c0300216401c07004169105035500c1c00482c0ea520301003c14004d00034141d00d815580f044400560209002041440581300d0604c0d0611181d500c40c00504003a542c44e00c80c41d504658415150301c003d990b40c10142c070009120740e041c3ea0071a65218006440d5401a440d1400d030a000c40b142692840c0320741c85200000d00c50401ca000034645440701d900b10b24000101408039940d2202d001908140c42140140c00b4003030381650802c07c18015080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 628968084 1250 628966834 628966841
    0x7030e010807051602240310090b010e130f02040506041404050c0c0607081b0a3b0415080609030406030b1c031110180203010f0b2803050d050c010c08042f030a06 71
    0x1303004159190042b81d0501e544240881d00200b90090a100160030310503030408003c001011139220b00660074000802d40d603568a0041000303020040c8100800b19448040000308c8501410100c80c1401c1003029201c080c1020078042c1c3e0040312410300450341e0b99154002d04c0106d90040c400c02d00380c4030000d03080c42d800c1e420140700580031404511003200707840080101c000c007041c44510301c900601c590480c1015440d058020120011103030f5100c03026a80e0b07070300601d480c2080a9480107000e0300041818030001c1c1e8548141400c401003240c2e0011036008208100d03010101f40480542080b4550003c03800340e66040262030f1100fa4040002c00c14804884134907003139560b0400c3d089129500304211502c0105003401070541d1f007400141200342035184000200749407030107484600103154050381d000010038070920004401c100684c60ba0780e030707840c18001554211104844401c0a01003c1c034180008603030745407140c1d1003103440b082d43c0f00c0744580c40320842d809013520112002e80c1485105500d00c100700e110741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 628969334 1250 628968084 628968089
    0x408030411010e01021917030403050c0f010606050a080c09030703050705040c110c1002160e01090b010302070b0613140a0905070f080309091b07030e010807051602240310 75
    0x1000880e6440701801121084445461140140d0040c94075000b45c0b81c410784001c40040c4202c03d40304110701400d189031010f400895080d400b095010541d080c01d0107060002042040302400204071080c1440c5016040e030092031084810003a007600000c1c0d101c00001d08441d40010002c0840e514242d5915045540e00b407076001f680d010754200b05c0b071903811500540b15116140c5540f000fa1111103110b40500480f03500350381041c0308620980784420400002d40d007071310380548030110445843e5030404010b80c0543c0c0c0c80072082810988100903d401140c0c80c420202d0f0006012140c1c0100d8420040c01000540103004010301560003000500c4500350f030552106944600c5601550039039566501e40d110150030907c541c0d203d5400030800b0305580d107031090506034411450007420b840021503000541c002d0b0400d03101103020030b5200312006c0141d03810a00e05540603602d413078080d140ca0240b0b41445a20424202c00a0190700e044022044030842607241079071070112390115640340c3c500644010044c11251 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 628970584 1250 628969334 628969343
    0xd020408191514011406160b01050f12300c010605120a02090403030b1f080709090b030307060e03221a120c130f06110f06060f010f02070e04080304 65
    0x42c01c4007480340001d8020100360602e40148a110f0f84e18113110185003091060000e43d0001c3c00308071301d21504c20040e1090780f07060f000d004030303119640c14082400000d064070015244031703100385c4e05485440350380051003841c41c9903030100c02c01d40000c0c1e6a40515040f0402c40c01c03000500e0b0003148407149060158000b13411201c04965000000e021150400e8954641c100c0203908541c2c81800600070a0180e00411044c10000d0501d018490022492988801303201d4004400a0180d005010b0090b900041e01c50261144410030400c800750b1100080d500e01c0381410050000da1218000a80c41d50144190382480240400c0203021000c4002801c000d040340f03008103d6440c40c22820707410b500701d140050f112100c0b0b4101c0807541030f4403030701031003940740d04104900903142441c540003003142c0c249081090000c107403d0f2200c3c1901c0034840360550900811454103441641700c002000101d5070340d09000d4240481c20700b0507050150440100b00c0c1009074070f401c525411401c2c11300b0b010800c860580254030541c0039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 628971834 1250 628970584 628970603
    0xe070806070201140a18170c0706090806061921080d0b0312031302042a0e03070e090709020f0f160b010824060103021608040f08030a0909020d02040819 67
    0x410b07945c14221088413080c10002d001c004034220014036103640d00a040c1001890090400c1050b444140c80c0202c540c1040f400114020010041c1e60001c0151507003208003180c0c1c06030042e00808e10562040c40c0f41c45103100d414680741c2c01e160310f0348000c5098038000740c00030089030b601c800607490304001c0c010400c04180284942800382141d46550000d4a0003144041d12441404d0601e07000c000142030100c01000c99090066065540301924403402c00300c0000d1902c0e4261541002020181000c44a5110b91200d02c0300c0010000714040110301017099400c07000c80107840304105154000c403401740f040080c0d0300e000e0014425803d0361241c80002c151501c101c0708082542c2e29181403648441c0c903a520038100071813410050b00b6000c0303002080e82c2d010720185001030612410941407080410050825540614006024411100c5189800c000780c403070503000394600344605200600301c076254130480c050303c1d0b400f0405800b00512501160000c10100d4200d80340741a001003880001c0f01480c1e81220303101035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 628973084 1250 628971834 628971841
    0x30a020c06161b050304180b10120f060509040206030c190206060a090608340609030c050a061b0314040320040c210b0603091608030f0702040e07080607020114 70
    0x841c2100d481d06613074400d018508062519080003060306030b01000c03444481c0c40d07010840060b1030f040d40703844220b007080e96401c51500c800802031048031045016510050b0034105c052000340c0340d42035210b4001c4e505a400603030302da4441130201c0082c040d0700011801110403041145149a00146c114046d460407945440184d43c1c500310304080301c481c2e00c16100f02c4c0c0c010003803812964104003a0340d400d507032841a0314480001045e2011524510541212001c290880428000d003c020700c4200d01421040d07130b00d01c0f14a800c052000e00070407110240c000d03100400041c06800c041c072480050640c03410340c0314165211502d07841d08210790b5011080c016003001e1900130106071860103006614500c200ca803124106280c004940e12050360030f8a41100c0345644900c005411922410029031140580c2c078007414001c2039001c03058211011a600c00c00081d80140314219503601c660040f02c041035030480b00020786046014403541415080d038024a06801103038200300b80d554041d00b002c0c5405006c0c048000d1150f4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 628974334 1250 628973084 628973117
    0x40e0a0b060403020d0206070203011d01020711090709050603041a010306090605130321020405060301030507030b01060f090b031e04030f09051906140c0304030c260d0302030a020c0616 81
    0x2842c400a540504c0c82d4080101501f841c10040c854180040c001007035175418094140501d030069100a10580c1d400541c40c42801220360000500050460b0121144d081c000c1008010a520f40201d62141000001040800c140507142c0564400d86c1d0780026200d40e52810104010603200740140da260b400c1c6800959240151030a00e440769506454661810101d002d01c16014460040d290341010343c00c001c04901b0f50764400145009610900003009224114a40758200d0314040e8054428403035000f0104070720b280c0021001017960b11405d4410780725070780e1000c012840c1010746500384084c0745500c2031100349039010348246441c0300325407a40a60207541c1d00c103000c07440034026189803d500c0700020900406100c0d10110181c2a0030a54060501698030440d07400c41d40b082d4030454040c41c0400c0100548014540810b0000b800340c402c1440e10b050380c061850300c80d0400b032110010036500000007001044264144c5000b4039485049981d240303051000003c0b04505110800e001c81e010558240f0b605 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 628975584 1250 628974334 628974337
    0xc0914091501090c02010e1c0f080906011401120f1401140d080d090812010801050a05090c090405240a0506030d0207090b060d020a080610020f0a26040e0a0b06 70
    0x840074020540c055a28000e0f5520080c185451014119500c4640101e07040404201210348086030800d02804d041036a6030180404101140c1042070002010801c00d40c04c40c085000c50440d007800d0065407825660314012230340e072001511010b03040c40c94699525403003c050f5203c20100050b040c00000d561740c9035460140c01d2000740d900503038441d008804640010340c0c0c0c0005480301080d000c0010440003142d65403030380ba0740c02c1613007803030950200c0d80300400091209004180d040303000640100402d09040900a03103402c1d10030011406644441c02080801c142004111102c0000601108071b8860f9100c20801140c0103036010000e00303041070007140f07ca180c0030030602c8000001d9001021035034642402c14001e0401c00032804d611840600034250044628001011a600c00741e81c0d15409207044403c0244c101d15081002d011503004500403010b440380010040303201034002c0d80c400b0660040c4280c0d07080010004c19902140d01010900240700c070343c0a0191405480e001c04140440500c0e2400c3c801103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 628976834 1250 628975584 628975603
    0xc0c1814100b0c031e0c01060608130b100f120201020f240c04030605040809100801030305041806030512030603100e150601120504050601051023090d0c091409 70
    0x3640007020400a420900004008081452083d41e061a072121402581080d0440c030311010300c1c01c00a22001000c1080c4643e01c09000142001109402c0005d4140c5a4086400000b0107d102000100710850a02d0442c030000382204800c4074401500d0f0f200c00b062210b0588400c03405403151501440c079400010030f0100fa1b081b05140d540201c0140c5c1899001d1186002c4e1a0703034050002003001101081c01070041070310650050320200c0e03581e0030344e00074090a011030544c4c6804000d0201c0041c00080c1d44001110708450b56094030504c040c000e4100980100950f51005140b0b1248800352000703141e04c1006548551021407d03208040c4458641c40c05941e002942101c881c1c10100c00d00c2c07080ea801c002019049407061411074000340e001550f070400c5500a490903651944400010052403034154074500390710202d03144c070103e58000d005c01e003482e44010400150740d1070b001046100e40e6403920220041c1c0c0a030080c0c4221031450741d8140c514010160560b807180303421000d000007260108000303640d415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 628978084 1250 628976834 628976851
    0x190b091203161713030c051f1403070e18040302010e0f0d0c0f0204050a1407050f03060904080906030c0c060105010c0807032f0c0306060d05060114010c0c1814 70
    0x480011690315070003901d91451221803110b00503c10040b450300313424080710103584038a010340c41190804003004072892550ba24004000e1800c085c541e072140c0e015600d03225160100580765203a4540d40825902c8100c20100c458114004050002c0f40000522038280500d000385c000f009000b614103000c6441d50406400f0403a03940c0710a143c00c2d44a481f8546140701680555442d0a20034060b80c00201602c0e0103441c07a000d121b840d00708075080c1c0c08a42d0245078000400c0c2c00e04038500082550108003034040100794a00c0360074140c0028084c450680100e64480c1001031540350750b071404100c04507064000c800a01c420b84103080001c2195400362000380f4040f40c1106240b4245011030f40c2c100c070180301401d985100031812021100c40c405004211110004051002e40b1850340a103050515000340244110302c62100c030700026001c10000304100703054039215012003801340c510800603140254000d81c020600c202c800380014159120714064494030500c900705001180c0403102070855a0303400c1d9060070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 628979334 1250 628978084 628978117
    0x412200307052809022b0506011b2118050102070b03270d030b01080a050105091902090319021201091e030c051c080901050c0403030e190b091203 64
    0x1d668003c04502525416000a280b0300c040c1e0700c410591050740c00a8003248507036941c0341810965400c4426284102c0c0b10216020000d80c50701c2400240048103c41d2441000324442c1c0c030001c1401600d9500c4441300390f0004d400c0d1050a8046070040548021450358022110482c601250661010550b40100c0c1d40c400c0d403090444c0c0701c03801589050700d01c100e4a5034114000d00448501503105025617201188151800507046541ca4009000f1600c01001c0401c034518040050240740ea5115206c0d0304800c10203a0f80d155018180b015000901c120101280d040c410101c954880400c1d140400260b07134421358030f00e09001c0031082d00038265991098002c00c40c0242c401c040a2158001900c00d500e24024a03181210120fa41c90369800c14000720740986c500910305104a84858000c510681c0000d12a80200018504071070300d4400d0380070714000241000704a10182e201035450b4460403c44003081e18956240503903400e035400e0154408a4124003d0381e846001640018006c8161681c0240704019007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 628980584 1250 628979334 628979359
    0x30e0c09061906021c0c12080613090c260d1812060f060b070804050f130f0603120507030e0603131202070815060d030309050102041220030705 63
    0x10122031001004150001900c2210b228188640ca03501002031806401400201c2142d40408051345000c000040500841d0400800001d4414644100c074541d036140c182d030f0030f80724600051020524080b00c042c4007800c050601041c001d42510780001ca52182c080e042d2003021507a03520700c03404012944c1000710741010559458040c05120341505000200d0101088680c0340c1005204000a00f00196003165031214a01c011a82c148946c5000d0508440f0b0030307040c00a036958440c101d120354020a4080e91058900f0310031504e50000d00070f0000c050075814031007a64803180003001040079200c20f9403164600306100ca4107502070012100b0950f090340d1a4605060103005004c40c1d0340c0b016002100b000c0c030303503103000d800b04070034012840c805c40c0d440d4050505607203041100c515010f8144444100c0d0780c525414040f950355000d43e490440c0c0d915050208135541507051040c0240103903030003c03081c05c48441c946010881c002c4018484064100c11a00082c5080c20a050351912035001d4180c01c80d9440701032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 628981834 1250 628980584 628980589
    0x2106050618010504120506010e06120d0f020c0406060e0102060a050123031204060c12051201090b0307050910061103070201020a0b040813030c090f14010b0a170106050304050d030e0c 80
    0x10021441d041c10402e103000d603540140c0b08216810a0151001d803c9080184400f12100310f1f4140c1103081210a000940d018003419511070105613054018041c1c040460442c1a0081c070400282d0000104100324181e540d481c0506000018107042d80140911400190742c0310103445030f14107031903008083c43c102c02c0d51015481800c052036220a41e140c03180184030030442c0f84000042c0003a2503640c0d20611040003d20308100854140c1400e041484014040e010039000f00d0703801681180e0700d06001142168504000c039081c030001c1d4010a030056024010041e40c110080b41c1001228a2a0341c0e2101e4001c01004650304c038012410000c0c0103801c01104240851030503019690031500800e0601d00c1c1c4a504c91801c5000081035201700c64003000000200043c2805120740603000105071014004921101c0780c194a6840500544124400c00b08800b10306074400c680811154501d045401c4c03081d6184c0d0009451600112400c0b1150700c1820344800078103220340034400f54148907200900402c0351000c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 628983084 1250 628981834 628981867
    0x705091203070b04120809010513061d0f061906080c010e0a0b03040c18090203070e070c17040f0506041a07060209060703030509010c0c03051e041521060506 69
    0x24200c140c4014040c0c040410451050ba60207213104601c00d030003841c1c00d554003400600d801019000607916050800480b900d01000a901607907000d40b0000b840640343e81c000c2905a44400d50000c6482500c81c899001c100000321603000e001c40c1d196200691203602c0d00d480940d01e160141110b650001b41400c42c041d40520281c00382d400c0c008125800e065200d9000300f90302e0308201e8007a100e03006c8104041113181040000c01d00b1428884205106072030181d00440e90300c9650b44281c1c041e2800c420001003245104130580d804040e44002441d0505003100082c42d5150498040c10400385d00c080400242ca2030200103e070304580036400c41c518140410322020656401081c030550350180c0030000c010141d41d50400074080107209840c001028241101102e0868440e00d06400070b10402801c8030700800d030440156480500100104805080240c00804082c0100d42c82030001e0714503a25806c060070341050f183c5600e00e080800702c0700c0c03c4c680444d03800c0c2601ca452081f55044a8200400900400740c1c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 628984334 1250 628983084 628983109
    0x241c0803100b070b01151d0f030c1003060e100602100c050405040c0f03110c120c0f01060305030a020d08010e060d02010311030109090215040e16020a051c080f070509 73
    0x810a000559140c22481e2a80e03c003c0084841108007401804071096036541c012504c00c40b4079001800d803007040500c100c1e5903003805809208000160310032105a030200a403440401c0007604800c102d055004014014000e24012034100880001c009404518038a940b0411280550300624880c0210141c4d200200203040b007545c100402008080b42c1d6481b14000d002c00d104103a170b100303245080b003404001c04985401c0c41c20f014030329040113811144000044c10706041901d0203841640d03103442c000c00528003111a20340220650901c900001800808006029003031080c2c3c0948004d21803400044070b0241e801d00403c0007201c9900017040ba503040024031180c0d00307072040c100041d810740c0030464140d094000f6800600d095480309a46011403c1c03080450415441c4607020a003460308100500c510450300600098400100c41e40c2e078083e840c801c001c0012059044010740e5490380002002081c1800d9002c0c03074801103040400480c0b141e899a403090341c4501c0c02030380c40b182468850000c02600141c0c08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 628985584 1250 628984334 628984351
    0xb03030a02031608070501091101080702160501031a0409030e010f0824041e020a14120402010305090a1a180607080708070203091f082d04080f03241c0803 68
    0x103010050000b91b0074070400e0070060141d10348030b034007810f617200041401030000c200c40e0440d00182c5001522301008074404056403c242000315200104c04940e0304030920214030b00f0351080c01d090303481040c540c0141c2004c0360404282d80d087c00c00e840b0408141d588580c00e0b42e9070b044207034440e401011f10704c100c1d80e110703000f4100041000ca07503540b1040380d15042038041e1140e42e01e0707164005540103805400000d0002c0d40c9204151a80c1491010700580046040041002c0e06250711100055841401485074000407903100d480509020411a100d105641c8111941d0086040c10300341d040d413500c80059000e03c142400c0c4d64140b081d0790741d020100ca00180141c041415480705003c81142c6540e4801c5c40580402c041c00060520500c0007001044031310060300d070f0381000109040c0142040100c0000c92420384241580701315603100da02d403552080c4101031241500388404014000380004a03c850040080415050038200d0111010002e101510042c2003101e1030400900742d0015800d0000b450744108403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 628986834 1250 628985584 628985587
    0x80c190b030a0e030c0c0909010606170604021c0c12020f0a0c030e04330803030103060c051204030302070c050303032211091305070e10060c060603080d0b040b03030a02031608 77
    0xc8483c4076142d6045082101e00540040410380301a04146000e580d00030040d00007401220310701030f4003408103010b010910a40303a080000140050325035804035407e5181507102500b5104209a80600510150410400058015051407054101c1e40241c0c2c1d0110145560140741402011096035404031600e800c03414440700031000941aa128841c244114425000b92002c141003803101407040124203140e40303100060001c0a101e00e59001055134191ba91004000600310001d80d010344545c040c1c0d00c000006100524100010036078036801414110340b00700e05a40c500354031101016102e0000300c40c403e080d00300d11401841c1905410300a200c40074018400c402210f504400402c0d0f4491302215180b0b16291000b086404102003004a440104856003a60400e400d18054003524a03099208182c01c000c50480c0c10300902c451907021100440d400007407d40e5421074091400c002c1c2c40f48480c040d00c500e1901115107071900340031003110a03048059015500e000d0041103082c94000002c1070541b8481e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 628988084 1250 628986834 628986851
    0x14010c031706041d1e0a2a1e06022127030a0515010e010303051c0e0609010b0a1a03160c1403090a0605090d0b07051e04080c190b030a 59
    0x1410f120080201564050000340c5c4981d4606500880c084814803102d9201d200c10f9800b0520b248144000044820450140203911500b04a20580c0d10380148252050180105048180c0c1f48500011120141c00f6620b03810341d02ca070003281003c1c00f0941350001caa07080101c003da40c600c45404800d4a00f03040c001180484004000c2440c0440300d08084032254000707094030f9100c40300a0050343c0140401824459951b0550354010010f000303044c1172360b800c00c0419403e10000909030f08100d0001c1c074141c0849000f440d200e071205010300f1203107451034004d903a0390002081d08006903e90300380d800b200001417031958480910824801403000103c000300080781c1c41010001c0e00051103000041d400754011a12510841c0400525520340e074030900c1844030811084180d45ca8284480c900250440040101552190400d0b1858810400d80c01140026040c0d018215001180504250788480088a131101082d20501524002c1c5001500513024641c80402004d0004401580e101c404448003045540c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 628989334 1250 628988084 628988111
    0xb0105060a2115080a170a0905010e04020904090f0b0a020901231603050306091003120c030e03030406091802130311061b030a0f0305130b060a030b07080114010c03170604 75
    0xa0f190300030700415084074141030244080400d900b4403094200389003900d0070080560141c03514400380b242c5414030021401e078034a0380c2d540d68162492590090000c2c03000c520380d45001d9a0b40f6002e100111101038101c6c2c081803070540580309075a0108410703109e03094a429083d204900c81b5001c400c854107200b1080100c0c070109000022401d070818401c4d11200c0d2282449010040c1104004100c82d1201c01c8182041012800a80000001c2582418145a00e440ea0300301110501913051205415100026000900c96400944c50045035030941850700e4042d00c1d028170707106074410701c0141d48110203c2403050001c201c0c00e49100817000710040020b4944040e80301000311203401c0c518224900c0e0004200900740e1030f0001c07446015500035203000c001c41e241040c0440002043c001c0d01400c18600300c80015010703212054010080c5400800e49030842c6400040188009000d02640816075400042c0c1000b40d40102c03500040e81fa0300d6102c04020030140801e006001c040189982d034008d0704d03021200c0c2e00301c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 628990584 1250 628989334 628989371
    0x30d030b0f130e15240a09021c05150a0905010e040201111603080414010c03080c16170a0f0207050d060c0c061505010e0d021e01110601120b0105060a21 67
    0x2089031200404c902d19040c0284e0b40341041043d1036103600281c1491030400c3c4c1d501e4803800350a07252200d00043c1c0311200401c20880000d0500c40d50004140750006020301c81d0704002c18030071f40b41000c50f000760550340c4402c0004250b800038807071325030728541120100d0019030080c0ca10b12035100c40141103072440d24045c070008264000603130080d2891000000d06001e0710791184010f030a110400c2c06e020002130f05ca030790002c0081000600070000043c002c16a60034030907880d0100d011140d040b0948110714020450320440d940d1000b6041d5002c900100007202085001007100001c0314001001000d80c2c21070fa40301c002c05020340b645d00341c00704000c010711705000030300758455004410b80c1e41402111030380c102400134082c10710000c1403e1150303180c0343c2000d0060b99003030707408034401d41d00311101c3d01c0b2901008010380301607094011400c028000c040021641ca400079450b424558018040031145036030700c0c4184401ca01c00c10560f400080c00031141b19441016a0190b08005070500030f00242c0c3d030100741504c03400c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 628991834 1250 628990584 628990603
    0xa1212110a0c14090702010513080c03071505090f07030515061507030903051006050f0f011709030c011107050a0204151703030f160516030903020607060b030d030b0f130e 75
    0x7038035950074003d410305000103482da02180d940000c00c00c0c0c0c101441515050030b28148014040480080c81d82891003060040e00c801551041c92075100c07440000060018000468a20055100c0e080013002103010000300c8100b1660450003074008420025105003640100400c2d15411803141a2070b80070f040a08401850314500a507141c1e40e00c14194a0f286040c0304a4039050480e0500b4900c040c4565035900b5002046120201c3e13000f02482c07550300c010707503d19200e10400881c0e404518100034142c0e901000030050312180704000c0200101d0380c2285500b900856038040e11b41d0707000e00700002c014106a80419141d20000d8401050941d540081da50920b40d1900e41110603080402441100002854281e402c921046020405e445121100920600540d0442520009844401000c0c035014400c0300d009150041c0c1f400e0345d50780441c00c0c01c3c0003038240c400f0254041c1c410a02e055025074407a210310842407134003d0000c980d52090710104000640c503034694108640c2d0b10100450080c2d800c00c110b046 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 628993084 1250 628991834 628991849
    0x1b0f07030c060501080c0307090e010e0607181a030109020a030615030b0111030405060f0a1e031415031c0311041514040e010b220803090a1212110a0c 66
    0x40c041c0051038100103407441a07010b0788956104140740100c5a0713010422800342c5803c07800004c0e0345031900200342d014158041440c1300303d00034101400b6486034454241c00e26551003003110441c42c0c0c1c0d1100901580f800100741d03102e4812080c8014002e4002540040c0400b076039502e40401d48a84640b8170b007101d03041040c0c00758046941c8400514865810100480c42044404017550a00f40f80c200860f5240c4141c441c0203500751400588118aa8025233504410202d555480c41c08003d0307840d80680201680d004a00341704082d071000481110390400000c081100241c0a40001d85850480c10903907403020210300241034131814050410b805441c041d00041048080709407100703002442c05400480360356114500003030200400c2c4129410b48003900d0444280e650295611006240d1803500c082181038428043e00603500001861040040a00880c42046486260540d40c85101142c80c0003d030308010702c1c1c0b501c007880c4400040c0c0140c0c0c1038024441074805407610708540b03030b54511842c1c02507040010b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 628994334 1250 628993084 628993097
    0x7150c0e0f0420071b08060a060909020a0621021903140906070c08090d0c0e0108010b031009020609031203151813051c0509030d0203030f1b0f0703 65
    0x1146031141446140388800c1d0b404010041149200254019850b580d503100c880700001d14504100e80ca1208200701481c500500e1a1243c56400e4151940401e4540700512401e0040c0401d40e588a8802d000e80607030300038800310555150207001d5440603280c204001e40c07190965500da55040c182d00051814400d0000b11521003941c515000d400c895581e201c059141e0300700000c0000c01400082e0b8242c1007421420324030544183c601d0444281d10540c521940c00034031030350400080280c44018a02514007003c140c0c499682c840d06e00900301c071414465241d05038000740c1180001c110950008541b64009000b482c6860501c00200e440e04101003096000300800104200340b0102c081198284403c044031403c036083c1f00c6000017114910054a148000e858001a0a041080c10040c1074580da85442e102c110040c46500c0113005ca07086465034601a000c1c12690f9090540301004581c45840800410303000b50300c0b05c8110102c0784989030941c00e5220004c105900300546180d001d003448500c02e99851 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 628995584 1250 628994334 628994357
    0x30207030b070504060c060506300f0d0c06020903010f0c090305010f060f211b0302030709090b1609030c0b0d1505150703050d050414060906060102060c07150c 70
    0x70940e200900d00c5040207014441402001d43c4038644501b015081540401d1a4a40341c000801000c105442400c8200e0814003800402c1050fa107441100d400c0e69043d290b40c1e0841e044500d0b160031000d0020302c0094402540b40b000164070b9030181007100c102038000220708040b08104000c40c1c01410f201d801049141d1030420401509010380c5a0015100c2c0c400d020b4186400d2550203c07154600034052400441c03410a040403c84991140009801c0500710b4084d0000c407001c4030300e007600350101364000d0190000104483c422806200350155102004c15075542e075018401000e6101c00d05003100304003450100101156803102108050800c2d08075061b956000c0c11203150403100004039110080c40b14200070403455645900208801e0130086400703035201c569280444403445246c0740314030101d10340010300091240c0783d20a000301e404100c04881c00c940359841126651482250f0725070041e40601e000074008042c007005010038a00c030303000c400400b180130190801500c2042601070005108140d08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 628996834 1250 628995584 628995593
    0x110d08010314010e0d03050c27010e0108061c0201050c03031005011e08061e04051302030d110a110a0b0c060a180510181e051501060c0b190903020703 66
    0x20420a00d0002c0200400303491003049640ba40382502e0380c2c2c0d05260383c071000128030f0086a42110001090400712440d050f104500012120414034005800180b400c41c0061195000f480c0705406210000c2424a140f84e00c822000c0e0882c0d1040422810440144482c04a80200300041d6018486810081c2d8403541001c00050800d040f881d11450122400c2d00b408980940202a907a00400c098400d541c081400036140c0c44041459180190802d15003410031050003500c61140e81003510860a0320441b06201000711440a4022020300d0180c0080b4200800581c00c40440c400b0208094100071580365107601c0c0030b4054114400d02c0300315030002750800c8054503803031044003c048150128402c100015444081d41d820103e0b102d4a0703a6a502c1c91003198405242d407109003a2a8890110020b01d08160780c0740c1100c10034a107048605d84070b0010300951784054001c14506940742c2c2e564104642e00e05171500b5407003c6018140d000c0480d002c20741d00f480c0d08003602800100600a0700189205881e6140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 628998084 1250 628996834 628996853
    0x5010806060915070b09011103071d0a050a080303190e0319030902090103260a090e040501090f08131d04080d06030b010f180b09040831140a060e01030c110d080103 72
    0x40d131007100b12342002080f0340140c1002c070081240d8401b2010b624600440400300d40a645540c00c46035004000d00e030009220040080118401c440801280010607403601d40c10302a51014400945030b07800a10084407140718915196000c41d46e180380101d40700d0107503008038020076002e030004d4400d55542114444801080014201d0360744013908400c1ca040c4458000a2901c101401900c03038010007080070070240902500301c2c20006801c85034010101d00580341c10040c3d17030f20a0203420100003403103000003400a1200410032807460301c0d0030107090f10354a5039203000c0f40d41c0c440980c1c0100da55031040301002040180140c940600541801d1200d00340c1011010b41e60984810004040399040c00700e00007080d180c0d007940503080b40d40580740e65290410b031210040000200782002806291042248999160030880d800c1206c003529441200700c8001400d024004155004500c0881c41518501d405544030794841c44409005d0700e4070b0030f4020003424500c0c1c11311040c44c49403400181d80d0340060060190401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 628999334 1250 628998084 628998101
    0x212010f05040b06041b08070e010e030d091505070302070b0a230901120501050d0b1003170a0e0415140a0e040f1101080403080109052215060f05010806060915070b0901 74
    0x2840d078420003040e00008040702d0004040d80e041004252742140664080c42c8069080f010050541c1d2001038a01c4009118241c2c41c82400007400c1d05c1d610702d020150051040b51801034055000e00481801e080c403801080c0c0c030503c3c40100b000940c0c40541d019050b0b108a14824207040a012951034400000051032016010341a10341c0500d0540100000e80e94081c808448550112003000c80d641c5010340c940c05c3e003460354000340002d2491a9041084c0803050001d02c4885a562114081030b0040b906120469800c0c5a40342001c1007103220074042d440c0303500c1160460784002041d0803996a1a1400100c02c2c00302960110340c150804c07005d5030104104141c000280031028a403510852a198a00401c0100188104407141c1e903500d0105002c0340c1c1c142402001d0001c248904221800c01d880d10301c1140b40800008440d441c5800e101051405410860f242201e034141d40380c502075140d0b5420000b6a0780183c000d164401c060405e0484040d00c407101070031b920380c0940d841c3c0780a031601e8000d0b10f00390340448 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 629000584 1250 628999334 628999361
    0x5060405030604020d0303020c060901090201090f08192301090c09020c07061103130608160518130605030105040c030b090703031d030f060c071b0f030212010f05040b0604 75
    0x6000500440c0c5000482580c03054045079000c948a0040c2400d80c024490b0070300c2e100a5001c0c80041202c0908150031868195200f070340e508030550b69488000c0c49414090007420460b07040401c00c070804440f04545001c04078002c8140740c0a00d0300100710100c80d041c074000e5448150351176440741814840583c480200601c041d0f401546030240940703820f5203582c0d0b280110000d12801e425039802d90300c000c1080c6c40030700c2c2014508565160b22240060501001115501c07402c1c003050700481c02ca240704400303840d40c1c0036006485100d168800720420800c1d4680c03040d240c00312951000006000d036024042c00740681c2c00349002c41d000c03a0850030030a070441d000800c800352941c0001e0341040000e6025650b41183d5640000c1e640c181015034000a0904c00341241014582c031401c03060000d09240c407401040b1040c81049440249007000e500c45141800301e201e4120180d080782010005030030800c032401200e184071000080d0340d00044900c8000c4130b00507141910326903c9142007100c0780c1028854803002c42c0c1c01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 629001834 1250 629000584 629000587
    0x9090515190807060f050f0d0509010c02150c0d0f110306010908010515040902040e0106060e010e0307081905151f0501020129010c38010305060705130314160506 71
    0x300b000080d560a0184110720030003504448504205200d0300556035090014040955102c0c0c001f071922000d0003040da42841a03520b00051840c0c02400040c11202c42e0b81da900031300d5250750700c81c4840c4416801507100c1da00d1032078640d080c0c1c821100307841c0b144078132041c1c150308001d4507402d2000c0010300f26401504000010303894a0240607108020b404009940c8204580100710603200d80b005c2005070240c440881d08642c24441c0100f105074002e245065a85d5084e40d42000340d06101080541d903001601c94408140c00a5449513031005048040c20061030040d01100c198000ca0071140c203a00c80125a103800c1e42c0d04c06000070b036500014081010083c03c0034402403114600f19150074a05c07070909087c0c10707d040f90009135101c150b4010302a40c541160400c03038000c1100c0c107241c22040c1e00d10300c0f500c00b00c43d101121800411608848100b6034180c0350050020942c07940c1c4c000d010303145903010240e0100a48140c0302c001000a00403454002c0a03c281b40140206030700100440020508540203d80700c0d600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 629003084 1250 629001834 629001839
    0x50901061d1506090d140d0318031734080106080f06010c0c0801060905040512030f150a12030c0605010906080d030b0613080f0c040c05040905070909051519 69
    0x840342e42c2045420044038195603421008001a010031041c5c080201600792607590b01c142000c000c141007404c1407680d20188030020011102110280c0654802804104040d0b000301c6007000030320b250761380611035003e07484400e90720b50b080c1c010907419100160b94148814480d00300440e440002c40b40104460b04007403940c0d007810510103801c103100401050400850311158018081c250990300000c0110320300800245864400e03a00150400302c60aa800344640850f0fa0200f2031407600316413090720311171002d06554a0780440041081d03e09800c2d642d00510745000403031040500011441c1c40d910070b031581c00285100b03142c03120550742e051340100c2e4110b02d810410040b044c03012605c001100690f140008400410f01c000035414010004d8110f803164454101189040e80050007052010409088031040180300c0c1c10070095441000807440041c405000402c5104440d030040c0382c02c01d420b42030460ba0a0b8498084800300c4d10700315900c108003904980da66040e405c03c941c84d904400080215074200a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 629004334 1250 629003084 629003101
    0x52d031903051317010c0212031e0a1b111504080405121009030c0b09060613020f07051f2007030807120207080301030c091803080910050901061d 64
    0x20094001070148200014540040c40400b07061001070318101c0c000410410807640564000d21300c40300309001521030090340c403403103030310060a072441040b4891864ac50000c508443c032101080c064100c3d400140c65501c0485245401c03692034811200b103540d064008110030b08014509070560504000c0c40900b80c05100109900300c04403800d0303460907602c0c121030302008051985440031751541444414903000800c010144e010314501c203218050085489617403190500a52101402d80309683d200d840412100707544055070700503044e040c075500403990030940241c0320b25080061a00c021850b001d900c1c0c81144440d00030b440380c3c80b48070040807000150840304000320303002842035000c041c0520001000061381c0610603000c1d001c0c540b802000c00e40d02e40880307143c00c620b9a042800203c40c2080706102c0858065114403d4801201c00002040b9114080b91800d8444810180002200e03010b400848401c151060080501071840480002130f05490151030f07122001c1c110600010301c2004100b44800c12 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 629005584 1250 629004334 629004373
    0x3151e01050310030b09061b030c0307031a061b12040b1b070305071e05040209130c140408072402030a0f0c0b0106050307020c01031e05060a052d03 65
    0x608003820525680d450381100c0c500407402c07642c00140010203540c200204140041041405100d00d00884ca00b02c0081014083e01400100c5406800000600000c0c6d01940700350804030400180e071050160076400c20011800550149010641440e4806000c0d52074400030041014400e21281181e41407a040c08450007040c803d126980c09840c590a44801d5801c4081c40f402006583c00001c4400c07240e555210071110700d481a04c0c440004d2024a40054039007041d0003111000301c2c0081a101c544c2c80103081740002418803808410403c02d00340040d0740271000e41802400034061150040c1036440c034101c4403024010300398000012444031320240055180d0008191644071000341000c40c51500160001ca40303101d208840905501c11010000400c9034001e801175001c0e884030350176220030050100055044e40d036419200100540c6802c2400344010841d80601c0e00320100038100c2c42074541d90400a82a0045070b0003400c014048002034845100090202c003083c0f060560241c04144d50b18528007242 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 629006834 1250 629005584 629005639
    0x14180309031207050c030d171f090f0f020313020f0315010b0c03070510060e090a05030a1d121c0809060103061806050103030306080d0203040315020901230315 70
    0xb03100300800d08104000703041c00381c80c0900c9000340c1158400480164018135800d240000440381000c00b0b030203d1029104280446c1c400100c80d400d0340060361408141d80d00501490109000140e520750100c2e0010109000450041208034202d04030f410319401040803c54a072024544603a0020032540c1e89402c5c5a4034090440d0302c951505515400e010044906500c00d50200400c1409269841c80c00e2071000ea200000340c8022004400300c0b6038880600c113540c1d11407110083c00c168000c1c8201400c0511910f8a800045038000c00c0b503a6811084010810100c500a004034003604441e641010442d02d40307090403400959813800c0c40050030001c01d8203850701c1e0180400340000da191941c0c4003a204000034041c84190380428208101d607500c1c10f0080c010103c5024104290081024164100b4800016141070780c4e003010710650094000200c00c002075100707105075414001c01c142c0101c0c0c07a2246100c420790324103000080310340d00d2a040d07000701c025880000e10320b4440e007844480c2072015180544607408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 629008084 1250 629006834 629006863
    0x509040f06230a09050c070b01121110020c030f0715050a0507020d030c0b09060714133311010c05040e0403080709080d091517070c0303020d1418030903 67
    0x21034000903004160b508890707030007813903405090109000c418600c40300103006c5a1301230501c1030403e988599400060080e0240058075080c200c0b2b8141c42c2c0c3d07203009013002005241c0b9004844140c050a000b190916405a040900e0340d08955402c10801d20080d1681741215030324900369250000b02c1001030840c0c01003c0c40039002d4004040400c1c00c00d401400705449260700140c0c418050b10b03100ca40190355142c01c5400b400010005890700340303e80c0c3c0b0707a404c0c3c403010310301002807504a0381403124030203a0300d1503255042141c02e0b070b03c442482c0366038441c40c0c030b071001c0000341c3d0701c003040c080d14440030341c0c2035a03108560030041110400003080780144641c581900a0350601d450140d030303111160102c8030b0f80403d401c56030590107503200713a4140bd50884070003021611080c00d400324000d403140d000e8401c40c2c402c0c25a092007210f024000345078a40b0a044c5508404c0c070a040050509500311451800c0b10b0a80b0700041800181800780300035008480001c1c200301d540d07107000798940240b100100c0d460b10b141e40700c080c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 629009334 1250 629008084 629008139
    0xc03120c02030d0603060b03070918020d0213020703020a0b010501090501050a0f020109051002040e220f1a13020102100501080c0f060909101d090d0f1e0509040f06 72
    0x12034a0300c00d000300c1d00d0280c54603c06020190b10303403c0010042c448950350900c81c0c4505100000c10900ca03004000e0010071a092403000842c1c0d80d0280f11001c000071030200d074403024543c410b60025001d8130240040320302903030041039200700030700d405802640180c0189042c030041c02004c010f241c0e0f00074111801c10b07001c0c0c50440c2803140140d00607405481c00380402071150040c0b15400c00c20406d40d5018200b1188080380320b402c0c98a58072481c80c000c500100c000c0310f89511104641c00820070031f408a481c0c940c40b030180e409001401c1203011a803070400341e4003c4080168402404255a0b0401c440e0017200307503141e020046549091070050b0380ea94454010b90103030f50a0182d03650300c0c4e560801584c06180016001100c0303031804280422440a0b01d0003009028070009010340560991044454424560074005040402c080752065400c600411522007c104080441a01580a550350001c0201c070715140c007511000074600700021382da001131044214511b064030030040c0b182e480030fa00c24044103800746107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 629010584 1250 629009334 629009351
    0x109091205070303091a071d0a091e0203010e04031e0807031d0114010f15232505010f1808030408121305010c0509061206061c1406010c0312 62
    0x3136000d0001e40ca13024003d0802804500c0a280d48014014841d070320a40c0d440240e83e4103020311840c04d450102042d500b0890f0a01c0611030003001d0303403005000b0500340a442e8065064a800c4505990098002c1d03443c0e540c0c1c0030b042c0010180c00004148811150068203070666a400344000c2480c1d0005200c0d10816031034800045812600540e56100e010b03400b4000c0c030400400b900c02c410380702c13400e01c2001010400c180002416940d0130103008061001c0b41e580b221300f00100719107100848a40e00e182e035aa0041008080c00c00d00311070040c01c0305007170700c0c0014a40b601303039906003a82190031003400e030304031380e0f08010351a44028a000340c43c908640d4002c5c42c0c41e441e5152800c200b0020b0042c0202040d080d2440018003e18000c40c10809640a129900034403036501042d40407203103800b90403030450f00b00b0004d001201c440341803546a943d0000020700404d00b060a1803468041d03000b5103a405030980d503a600708842500d4000d26070594421001c2c01d100788a200b566500405410464448250071607982005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 629011834 1250 629010584 629010587
    0x71424040504022a190b100b04080109062d0216051608101a2403070315090b0d0803070c0506010b040e090115301a01090912050703 58
    0x954000d040c016104540700c08030400c08000401c80d107448180040c54904074078200290003d02501c079040c80c64806140540d080d07a8054001d000134205140403411010041f0303030113003401c1c0503000a0ac0700800114030440c40381051404c4a80b42510000620100e40f40c0b00f1078211140d800840b200c410000040c0d41d0b016140c6210740300b407a130f200c0041c4a40035018105500200851980c010f840c0c2000c20358000d2540e02c2c6d0010110354a0301ea41028401301c008540050b860000300d4080d540000c2c10840c080c00c090b4803d05046030b8021640240817954030740003281c000d81041c52a0001d0000d00004026034074035140094108100500002c1c06054008001090706d44103c0a020109a0060488000d56100d00b020340b4150400d01880c10360004050010300c1403c1c050040d0031884101a000d0300d962801c0641800c01c540449100000c004a054408540c101070455818400303030149100c400c0c445051070107807024140c1a4031107035505050803000c60101d5402c4180e540000310341d0510b1a5101600e180 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 629013084 1250 629011834 629011837
    0x1b0607060204031202060c071a060d1718040e030904051b0304031d0108060901050108060a1e090c0c082203060e060a0b0a270b0603070c0203071424 65
    0x420240c000b0070000b04002d03084445510394103ca40a40340c1035900d00800e00b101c1e010340741d00a085041418851010307135206802098000c1000b400343e42e28141d40ba11250b4001c041e402001402c1e1500042c0307421900e201d0814031868000840341803240135804098a5500c0c000d54044c0d07417103603942e01e010034444c1804a140c1d00001e0a001032243d200d1815081c0a0458050510078076000071054032141c0c101c4d8859070700244291401040c0130b0080c2d09040c011503144c0d100409964011a8100d404510580030a010341001890140ca1010749070a0208070415241d1712483c210034040002d803014001001541521020500958240070300e0782c03100c50726600c002203540058041307490700517200c90840020074a14810f0b18000760030b0114002074802d22695409500c40e001d0808070066400f0811810311000b100103000d07292001c00c0001030f00001694a034800e80b006000300d0000401d0a046080503c8000001c280c0d4480d940640240d8001080b0220014240820204050b0b820201d40e2a000300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 629014334 1250 629013084 629013097
    0x40b0601051b0709060b030f180123250207061404180b1f0c02010806030a050106080717011406040c030f0f0e07050301020304031b0507030b0f010618081b06 69
    0x34031144501c407100b035610340c03a0900e40c041c0f80481801d103003011800c2c20604040703034000c50b422000c44020741d6800452044803a15110342000554841104641c40100c0c4c443e000c07405901d82100701d4890a181c6000545c000d2030f000c03004881c0c04100b031800481d580110300901103820b03e08000038118000c13142c00d0054405c40c0c104020b0049640c05010000c0074551005a240b0300540e10b01c0d41181c42941800102070741740400300d00080d0803094090065205649254025030007508603240600959070766402e448041d000b0b0721440e07004240800014010300203031101d900040f0000c000c070550750100c2c3c185448004042d64004c1d0380f80c03141c0d03242c034a01c25071001c40105206c101c1041804400d60300103010703000400c55004140f2841c0d00c04140b40c5410b01c2103c0c004c0380c3c50348520301415000340039002c20700e41001058070180614600080410ba14183c258820404010b150a1541c1000c0c000703450784050004516022511680c140000c20000a691181c0e0b0203100018144c81c5910001a0151040c3c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 629015584 1250 629014334 629014357
    0x5030304060204140a0810110c0d0c02031b030c010c2907180e04060b0a17031b0c0a0315020f0c011b020610180e0319020601080c030303040b060105 65
    0x410003405107903400351044e00c0701c8910b02c1d0707200c0d01c040c42002418442070103000c140390098140107000440356031140310030f03590001c0d003d8102003a80c0d0050f811702d00301c181c041d40415580714200c0b0841c9414010183c102e40451100700ac15176103003000c04c0e43d485018011906004206002074103204020f00068260414001c00e00301c803090307010703414400000a5a405020943d01081b030341100354184001c006032000010743c20304a5640d40c407054003600b844601e44c1c2d00040c01c407501140240300b0030074000c4000003d200a603640e442c54114003107403405802c8000740f507810180c004007144d520090b180003245c0d041111003031505080110030b0004c0c450880e021232504c0d00040d00711483e807010341281e4404001b101107010690b0001c02c0998950f2000c072440e609520100c003051203038840d5560303810925aaa88000030300003242011417491070380030107540400b040525000e192010f0f4100b050a003d41a048082d0a6542c083d502280d681e020103040104142012400501181d1154098811070303040c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 629016834 1250 629015584 629015587
    0xf030e03010c02010605011107030512070f150b0f041107061d0f07050307080708030f0706060e070c0506010b0c0d0c02040905030a12050a0c0914030a14101a03060609130503 76
    0x2c0920190085c01c0034840d0390302050303035154041403009001c9050300489400c5409040c04a409260700109a03200007011038080080381181000b0803012240b040c4c48444d2450002100d0103203404001c818802030703032074a20550804031605040410003080c0e9401c25840480410b075108521078500c20b4000280da00f41451044105034115000002112811218181e06940d180780c0c13960080790320f50030240a510741541c810001c5004090170f500080001c2c03802084005909034550020740c0e2290410703140500050340910207a01400b001b480018014401d00d1003042c907044408070f6040c3ca03201000d41d5582031101134003d402c1992129005511001c1d48003040d030341e9a004511014042100c0d1341d00c030807030300b40c0f42c000014401c142900c940d1a10704139540710312406500d000251050b82400003222038240c0101c561000014819002d200c030303981802c0014201c41762200d40c2c0035085800c1000704000b4203034403001c098520386003c103c01ea00900309842e10744180d1b40e0702c3c01990300c2004131800181640b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 629018084 1250 629016834 629016851
    0x10110403061a040e0c04050a1404081b06070806040e010b030606010507060b0a12030f020f10021b010f0e0f1504060504080c030a030204030317060a0e13020a03140c19030f030e0301 79
    0xc6481507021030301b02da0800086c1c8843c0740d0340e01101c1d48503011070032291041c000300d400308018001503c1400103891701071061644410b001d90411400b558460081084003041c08024901401a40c1c03e680e10000204480e44040340000e555000150100303052150006210050201a8012403c0510050044000141d4410064155100d21107054002503103030f40c0c070b88071070a00c04130f5000d0b80342c4032000c018020410b81c0c1d000d40000707502c0740005d102840c2c110400194400e800303001d03c42d0681c0115800240000031000c645090580c031441e14522900152410389080340328012982c0c2180c1c000100041540e150b141070501403060030002e41c0c00b4880441c8000c1c8066054000b0800e40780301b40e40d01e819412208004908048098035056400001c84005000a100b580b0100b60321246425a1003080c0003560041026104260810340350614401912404404200041034004c0c44c10348121000360300b1070040e0032070b00306c140c04020a80343c15101b0180038984111242852504001c0080100e40c2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 629019334 1250 629018084 629018111
    0x181207050d0b2a0414040b0405040b041b0e01120c0807030b01140609061206042013050d0507090207020102150a0905010b040507020a03110a080f040810110403061a04 73
    0x6412140e00140220f8140107048160241d00030580341c100785014141064204012988500c0f0429502034205076503010050441c1e680e80909070240d80910b02a0210341002d00b0a4a084d651030810702a010913140c408103d40368200c41c503941194008403595440b500e591400300c0c03680b081a4002d20240c0326020340402071150f64000340d03040392080e4a21030007030490710341484007074047c5001c600d900c20018006504803d060075502c83e80800000c2000845004100c4030004490ba48010b261040b1004103078011016042244103000e4042290300503c40d041e1399440a50b40da50074055002c0f51a0007003003040840e4000c009451000205803180c2c2c4051074243e00d24001002c9455003a1070560038894a400c15050034811300b030044c04168094416000c580d1400d40e10f440c10618440c01c2441001d01a401069090010701004400329000c03a50fa10b207400407191400c44108940702c811842c102410a011107201e0480e001c69a00410105000059200c03501c01706030005c80042e005410441004070b0342 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 629020584 1250 629019334 629019353
    0x120106170d030e0106030b0a020711120c010e18041514390f0c0a060e010203100602190b060402091002010501090f0605030a0605040f050a0302010c14181207050d 71
    0x94009035410481411040b83e054281d0342c2d00c1c800a001c0b80b01e9080030440051040c2c000b01020b5020f400d03080c02d50a400c4001c9070718000b55030800016a0000d0000c0c8902c1e40c0c0c000f0200104c401d0840d440300c0705100d80c0280018140380544001d2420303015401122100d58150004040581c040d034244010707180c01110030311000802d449009100114000348000c8106800e00c0075814545840203e0070310380800f04480ca02d5005c6085008076105103190303100003510324001c050080904800158490403c1e071079248216206411070019508002004c0310035505012030b60162a030000070f9807605071100c1e00407130300038440d243d4a1504100c4c00800600c0c05a0150402da048840740301c802c10500004c00c00d0b40c000c0320440d000e025030640007000550080f90060308002d4006000314540d01c2026050360f82e182c80c14645820440c00750751107030030450100d5001202c019003111400314581c54922040c0f41d030300c03111000750300c0c051107462102290410000300b0030a400241002402c3e03400c018000342800c01e0380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 629021834 1250 629020584 629020603
    0x106181a0d0c1b02010302180301020f040f0f080d03230a0c020706020c01140901030b0a1202010905010e03030d1109100e0909031201090c0c02150d24030212010617 72
    0x7882c1003220b9401114440d2944200704180c001c850402c42d601a40114040c0d40442c610010000b418010020aa40e00b031006250442021031030750f0f540c2e4a00380144240c0c02d81a0311096070700409810030401080e010962800c0c0d40711a150010701e80c508003840a03801448a0f44100b0031204003420003120120301e91202c82545a1602205c034043e99a400032030b9101d42c40c9c1c07440c03400a01d5031014a040f003020344000c0d00801005050208400c0d0502d404141550026444401075102d854610825540c000e05000d0150a00303180110001101d817000c241c0c2c0340b0a600e00181020b58613102c10b4031110159082c5c078001c0360000c3c8031031b091002481d00100726043c481003041c0f01d030600780040f80030000000103e8806000740201090706030318240c640002800c15480001c28411240410300059640a0b800481041850700054070b8210784002d100403a02d0501054440503100448a13002c15407a502c24800c80ba030484510350451400b0021394003401c81030380415900ba41011210120f07500102c0d50b07000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 629023084 1250 629021834 629021857
    0xe1c02030306132309070905090a0b010501022415120c040b100206070809010f0207080304120903080d0c1b0609170711011d090f071106040b0106181a 66
    0x20004000310f400001c46001800c40e2118000209101d280c14012500055102ca41501941c0016699460704001c1c1d4101700c622004541005a520b020450300f05401409441300384000d2415404d5030102440186810000041c10000000000c610b010f102d510802842c101606200c8448800080795603600d40900400e031066040030110381540c10a01040d050f02030240d4020320541e150401d003503c0192010b40110000d5407038003110300503910140010500180f01d100102e5480c6070508282058258001070981040a40c0303404002240c000340030b032040015600070005c0d083d07081d49015160b007442c0041c542001c1700408490414032145612814900e405940e0300400c24921180568089c841c1d0b84000b4404e140c101d04500c001d5104035440030340301800c0c0341c200f14400f19a200080c0b402c0411100a0b620490100c01c0103142c03540702d041001071100c18401007945040a5840c0c003243c0720140107220800c4442980518140c0c58003180c580204004040e50340340000c1c609442000d544040d08041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 629024334 1250 629023084 629023099
    0x203151501110a060c3f0203130f0f2d0209090313080a051e0a03080606070b0901050105030f0703030e190b04090501030b07080906040209070306170610150504090e1c02030306 77
    0x542c9000031884102c100119286e6100d4410064881c0000e41000d08016500d2880f660010700080322611201070783d40c05480c490207244074038036101c16589464100084101c0380788624100e00000d126a05d2045a07045554440f150b03948815949180980341403c8640c10862a001502d01400f00304049501d004070251494a071030380702c40d440e00700302c108031500d2158010a0030b50042440f41c408e01e500008014100d40c0382c81000e450b18403111101303454030b0b251130359100010082e5150400284100001010103000381038610784000c1c0030300100644441c010408188512000c41c00c0e090081c028110001c1034a44603a01c0d070028000420090204071894042d41c00418680da02840c0c00d0344c49100707902d0003410181c1d02c42d405d01014000140c10f83c814951281302c003150701140c5000f5004107202440c000d03c5c843ca00350312408600c46056002040c5041000c90007100e242d4001e04a070f042d00e411400105812108041507071928a511503600c541c00ea40b103039070003005030b400700003075005203002c94003030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 629025584 1250 629024334 629024387
    0x7050106060203070209161b030305151504030803060f040c110c04060f1214031803070b0708040e15090a061d071b03020304050904050601030203151501110a060c 71
    0x9903924420140c020f90f0142d039590018100c2c1c144c0100c1000000c5c080c4c40d014542300d00c0805801082c0764001401c5002c262201c0402c112004080352a40c1441000c0310f03807030018a80c01c040300c161440740e40409000a500080083c8580e100c91034000302403d00600f040003a0740095500510b0700800b040420881d0141c48808542d07850180288011303900201e04030342a00c7d241610051483d00c7c1c9500482c4c081629880348501d031017090000e001201013200c0c11003155410b80080509112440c1c000c80d084400030f014035004902e075181520141c036034082c8503400329240e04c1c180c020b100303803440fa1a940c003030950410411401030035003203801216840b91100440e0301d040c1e81f1008001900712041d00000781003400c1220005032410710304030307400d000c0c0c0141d0b0300d001d40f5507011400c1d100d02250150f68581c001c80041003103003000c0122610001c0d41c82101005418946011002c1c0b002c00c50096040081b1035848091103601071001c02e047c503920460400c00e81c0c50302d00d0042c04201040c0b6000480900d082d002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 629026834 1250 629025584 629025587
    0x120e210a0510091a040222051b0304111c150f050105040b031c11100204050f030607020715030608010c0c05010b010203071a0a02070503160c060f052b110705010606 72
    0x75540f0f060340c441c64441408040c0a010208000020401d036445030803c2104004181d4410804404142261011a030f0b0b03d05219500041d2159a0301d01c414004204108004256503030700f4120b070508220781a00120991448034422800d50450291400184890012110509030300a0306140503d0000b03011a0307981c0c508200c200c0d54000c1719507400d9086045e09250300b0003946489880d11110b8240048210b1b06081c0c940c0c0b61030244c5943c04189640050309000e6460880c1e65139140c0f0404800070900340c030f020310009464500c1480303079400c0161a00a400c13429402504980041c0c8881d06c0208464203034010014410100307040c00f51819403030036500c3c0e0250b51011013141c2101da004a520149001c0c1741c1c1481c216414000e003640d03006582404440c00207107091000342952900b64002c01c84900b0281441001a5101e40c801000d104070b01001c403074140d42010541d402d170750006003049131001070740b01074901520400200112103894081038103810364454001d00000b170700a000802c009500c400d030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 629028084 1250 629026834 629026841
    0xb180709030318080d08060301020d150e0a09020d0b0712021215030f030a08060604050306040804061d090606030a0b04061509140f120111030403080105031603120e210a0510 76
    0x203480851704450b01c45041c1d14090f1043e00d4014a000e00010b01c0d00d91103400c2d00003200c001d1900c0f41003125020700700300141005600c50700c2c0c2101400c1c070100035680d03456001a607008944c183c01441d000e2000009260a4024424140030121580d000d564031b00ca10010f1420021088450030401c0c401c40c1150191801e000815540e1218030b90300852800310510030550351110014003040c1c2c4000d0030080400d0644060088c103010b1403050040946860602c40b0141000e03520000d41180c002c0f001c588010745071780385d081d075a8224006480309943c6e0703141c2521034006045007201494109041000000e003200c0086210718268a8036600e082c41d003922039600314081302c4c2d9003010076031182641d01e0065051414220f152010414800006001c6404461600d0190011113094002c260b45000400c091305041c402c808004c2041c005070195a410340c1c1e902c1c5174110150303002104018000c0b40b000055241e44560740c4000c500310080300410303c0c0c0103280603070f075420000c1c00700c99601030480200340200f803a00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 629029334 1250 629028084 629028089
    0x60e07031415040902030f030406081605090a05010c081204050d0f02014803091101080f0f151c1112030313170315031c050d0b180709030318 62
    0x405410303801c40b40b08100800380011141c2641d043c00341d120f0954600400300010001000d003620740708920304d4240ba408080d001510610b4013440010007180d491a9100310040342030b503409080241c020011800d00642900900780401e2031948080305110601c0400104210214240e585090034075403001c2040b800e846101d1151200360840400f40f40030410101c0f004003020310310300c8140070117010117135201e41e10412422403100440d9864560f80140300d2261005da04008080c204bc2607507040000003089507000003000344020034032540214014407805d049000c0074603001481e001041c600b5405440491145110440b55100e030300a48c40040c2c03c00c4070b10700f21500740e010080c60850b540c00c1d004a40d101004502203e0f03418403480241c0400060401540c003504900c002a000700150005040ca0034421040d140240e01c441c804d00c1000c07035404012500c042402450120740c1c04050030201c2ca81828101e64480804c003000100048113071320600100440c0e020317a40d01c041e40044c084030b50341d41158a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 629030584 1250 629029334 629029351
    0x61a0409050a11011404240801360606030209090114010206070509010905090403020a0201080a0e0703060b0414070c0512040b030a0c2706030506100203190909060e070314 75
    0x44000e0381c0403d20703480106030b0b85801070600700310b45200c040801c40a03600541103551143d181024804d03071000c030080014001ca015042801003541800031903400d800078404004c503028600149480e5101c40031240768000c11424038184552500c400e406070203908640700721401004150000686201450a80c407000e4034107801400c81c3c3c2d00c03401401c440641c002e0303040e541401171011000809440b00c500c02885540207170b0250089001c1403000415400c0080d240f00441d03410408500000301000c6101000ca9600a4000a5801841010070042c0010070042040015028104a5070903000800c80032024440d0050396001031745040c01c80da1a002d14000d2044000051000070340030701c0c0b40c0d807058040c80e0751410031050000c51601500f0343c01410340e2034007920300081c2c0e00410415400d03000b082d81000c01103c4000685115410082da2400f0b81003400070111103d000304844140181350032000741c2821441800201c1d264981782c0254030040c0c0e54000000d280160701c00c4205600310074103006400b01d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 629031834 1250 629030584 629030593
    0x3040b090112020903060414010b1906050a030f0e011d120412060b03010f0f06090e03070f03091e060e0d11040b1309150b030d0507061116061a040905 66
    0x440c0044500c41145080a41c50700d50030824049641d4040100c280b20b41d10031400744001030151108942500c0e14241d07418012080c5000c0450715a19400c40721054441d03510b000384c5c450401c540100c01404081001e2400c0a00d01003050000350010340221450032100e421040d10301c03620401e107070390341e2803405400c208814043c042071001d10070011701c1c59070032130051002003011005900000d007115400d41c110059141d4a4000801008030b90080000401d2505001c05c000446c010201d510b074801c400c4020304c42000100b8980c2014010070415000e07000c2e4030b0700c14102c0004520901420007050081c400454051003207100340d07140101031980e40c103600100e661044901c0750180009000342054166014061401c05a1000c0d594414801002d0082c0b0070803200c0d01c00c3c040800202d4140b24843d60081d0416000304440c543c000d41250810790340070100194000f1a081c0007200c038040c4485605007401c28044c42c07018841981c000c0c10030340700b01c5150104031f080741204020803983d8102000b04141c01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 629033084 1250 629031834 629031847
    0x20402121501080c0d0213080105090c041a010c02040e010212010e0403140316030c1b0308040605010b0c060c031512151006021b030c06040f08010608031204020f150a0306051203040b 80
    0x18980187c900200c0583c084c0340b40c16255071000342524012078002245601481c0c49a0641c98a1700038140e0031401c5101203140110b40c000000c2103103010003006801152164030380c03d1403880035411251400c1c2820401c813460358503001710410745c81c0141c40036400a402080d840403d441c10804880c06940d0304035241984410155003035029010500820042c4681f01001c94a0400b00f485000a04d911a07070341c507861440e0a19105003201c030182c01c0440c01c0c403001d01100c819050005141900000082c1030b640e00c03a907841c019040481c1d500c0040c40d0b0007460142c0060210080001c407040070f10103500060704280c0c0d45040603640e007a1548580c000580c0510200c4100d0740241040c0588080b015003035861510315140810082da105034080f0700c0c104046001002008021310038540130b0101200a54500403100000040049000d08082d01c909502050301d90142e8502c030a0658903010121810740b82e02d40e10b003020b001800c1034030a0600a04010f0001c005101010080740d05903141440380310309226 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 629034334 1250 629033084 629033107
    0x50c12060105270d15150f050a180b0301090f0b0a0c021c090b0f040e0a0b0915040e060a05090c06041d181f110304020f010318020402121501080c 64
    0x40714000f03101d810442c0502540007280b5540840d14011654580104c1d10000380c2031800e6002001c0e80c402000348003034020920055a40341207080072146075040c0c0e0740d90340c0800300c2600c008180ca01c2c0e01a41c150701c0c103000e800800441c1c2c4038401c1040d0103900c411040e5074408404200703503071003019080c0058105402180e4110b00071002d00b0f050107200e282800d003450700c824016020340e10040e0406c00c14100803804100d07440f036081c1e410398021003042007400525011404030300705280161420801d80300c141d0a41d04a0340b030b2a404a5100c03c00542102c1150074411b440c40010703d0292003101c005c3c0100b00e82c40a160400208640440d201007d000c007003c0721207008190501d40c0982507980c002d40403200702408010030010540d15243e5804c40d0204c10b00605030081c102d580301315020700c0680c020710400c0050780d41c1d0f00c04001c904000703090100b150030000340003c1211003c6039000758414400301e07480c411015042e420780d201e008000100031106800d48010340b9803000c00c4525650366141000303800d4406 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 629035584 1250 629034334 629034397
    0xf0f0a0e1c020f01050c0706050108030a0509041a040f09061d0a02040905010b03030703030c1205040f063204020405130c0335031f230f04050c12060105 67
    0x14101e6106480512002d02009429500c041c0c82d10300180c0703000b11f0744100f0310210f44182401003a40c24000e45c5098100d0802500e1400340960a0b84140d0740d811080d1a200328500f11aa4440e400400c10044001310180d0751004102814054a01a1a204005607524041191003812589620080c040340140d542040040d010f1440d0484040d500c800003070241c0d850030005420a14441d07180411000b40c2c0420080600d44100d004a418604003028000031418003100e0505103a040280414003200c48201100c58172000402e10f8103986500e0010b4400e1296145024011403003110244059142d40e010380100c1030040001605450391030317404000041512200c104412a451190300313074038804940c600c0b082d16010480d0005030a0002c10054208101420790001030103003883c00384a40d081c18500c0a400c8080e4000740f503c442c5403400c4c04400d9481d0440c0c000c109900420510040c0303401c0c0000384d5107800c2075442c081d0a002c620046020f075809070065401440c40b110b12446060603085141d148c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 629036834 1250 629035584 629035633
    0x905100e09120a020d11070b090607050c06130314030306060f07030909020d05010914191a150a02060c0f09131b020c030705030105010b0f0309070e0f0f0a0e 69
    0x54414001490303004421840038212810f469005000c0d0802c202d0401b0309660410b545048041d0020902072019070301001c141e6044d590181c818586524803841c10a107410690380c0e9031540a0000b1031026883d240c141a004280c030b01c1404844508200c11100603900e00055904687c484030901210501681d51000b92018a0003850003e100f00d54840c0f01c4001c9902c2380d4416032441e511035005100c0d101ea24015003d40b205242d0811006292203e100c0c405d0350050031080008545030301c2d03c0c482c004c07508450503510385001854412040250354451009034003405645015000d0784001031100f8200f04165549100b01421003854080d400003080fa017100c4100b4100403140c0d450502c4aa00702c01000394044030042a00203002c01c038202d40800d4030341f1060f60300c1103100368100001405011004400d44e281c4e41c040f440c01c0c584030b4541c101030742d0404007190007410310300c0d000c07804018030b00c50f8444880d80112191b0782c440e000c940b100025401501e40040b145c4007203901c0203020142d040c48209560380c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 629038084 1250 629036834 629036851
    0x1050f06121c0822050a060203070c0c080703050d081b09010504120605060f0d020a05040b011b0b24011e12020a051e070302060f0a0617030c01060905100e 68
    0x110340003000354103010482c035280200000d8404081080000804480c46502414007884440c2200b80356034032942c800c1044001000940c001c40030a001c00d01030014003d10b42c0d8401849a20103071951180740c5c0d9100e040c802658107219200c1d8050340a801012064042e5102848130f4501c03001d00d98800703600707900100d07640d810480100000209000400b8030608410300c1440089540c1c00c00004010841403001d050520802c1c020b4250b00043e40c82045000031960300303840105000c078070344006a551060720b00003503a54080e2910301008105280440501c0b480c464600284100a9909181401115626214041046a4000b0001445090400030201060301c2d02c01e840c5482400e8023000d981015000e031010a50100d04011000c540300411802120045005810801c003614000d40d40c0d4006454401c80044132030224840e0846034012001030811308034144400e2000e01c410310340d40d609c03082c1046029440d144021078914001d0082038001d0070041c20305d1091030700b0303c1c50191025402230041507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 629039334 1250 629038084 629038093
    0x50717090915030c0102060709170705030307080a030c1404031b08120403020103063807062d090c05010518030d050901090b030417030402030309030f06011701050f0612 74
    0xc030365035030354824840c2ea044585690b2145040d000e2500c1d0051100010381075421040400c1820750380007003000708071640000e503280c000860300e84003810802d464020355058040000c0c518103001081d0f0041c490744205030781c2001716803040e503001c031103041c401c0704041840c2408002c1000400d80604030301d10018409842540c0941d0354081d024070781164131500c4400313038001184c20070940d0703018071505004013101d80724002c1c0050310003040340c9030080c1d482040000205110dc108000c40c50003055509055102e0350410a8120f200324003440120048007000341c0000c0c1c401702e402485020301a90000c20390254005140504003001940d5507080104558104110444000d000703a90410040b4030400c03071368a4203682c48603017000040040c1c00c3e81d000a84212010010f001c0020342d40c40035a01d00b60b00b40510705450351540c0c40001d095100b103c1070668035120b90a00c141d13a400d4085001070484401c0c220680740300c00d8a90000b400e0782c01c103c1d00035043d003000c6000504030303040c404861400c04d001a010342e03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 629040584 1250 629039334 629039347
    0x12050a180302010501090606050f0d090f1a0609060d11012102041e05060406050304080f04081509010e0a050a110117071d09010e0417040504090614060108010501050717 74
    0x2a4020400c1100c16401030303441c1d0004220381052440b0b2080a88130074604549009a81c15110070703580b1400d9169004142e848000c0c0741072101d1901d03110f401c184d1000194441a0b40c17104080012802a03805c02d100d90381a00204201c1c3c0380147d003548585510021000031001c2c1100152402003105040b1100e0101701007200700c0c09840c45c8014000f40a0480020f221f1141d054100c0071022401d400c030500801c400c0006004044e000350030790303a005501081503640c800d110b22450000c0d018130750141e1420703c2070b0f8001508401240e643e0510820741c010003000032200040805030f455450301000f8040385c00c00203d070700206001070b040900142040c100340300031089410707180d00500d01c21500c0100150148c001c802810403241601107032001d08640f40303481075040028a050345131019100070080210881110b4a00000381c0a441c000c0800800c10400c40354039041010150100d05e0001c603511070b500e00000c5003903028010700350603280c0c10fa440740d007000001c1e61000c900b07111084007070740303101400d1215 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 629041834 1250 629040584 629040611
    0x302150a18120519170708060102030d0b030109060e011a06090a1a3a0606050d0b010c080406050909011208041802040509070f0809010e0c1c050d0503100608040312050a 74
    0x8413640b200c190340d440400f14806030400301d035140c003800030f10812603240c0911040d070b81d000080c2c50310314184145c0051640c002c000001d00500300c980d07000b041c090030038460807405c040661003640c45451461364100085024000c1140303e01c07031611110750007201c0c814203022004424050980146840246030302c0c0100f04650154800304802d804400e480400c0a0115500d08002945034981442c02007401441e0030300e04050511300404892500c0c0995401a072155607201c1c244c514449900a20034507511920b03405c0c0103050343e010402507400303558040300010722020700714170302c404468100251031306050500d980340b41c91107861110000c00075001d100200c0e841c1d440700e62140c040c81e5151254001d00030031741009441035000806e8405503034503110005110510103e403070160040e0454102200f00c882030800c54003140750300c0c4c01420a00c602d4040c40e0304207400c100294080c001c5001180916641c8810071510454219001070003d9004100c08071050307216000150006e07240f1a010400250b00001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 629043084 1250 629041834 629041867
    0x108100f090803100623040e04050a0c030b06041d070302060a121a120606030a030807090905151809070303081504020a020607090f060c021005160302150a181205 71
    0x30340c0240751808010030010940c101c880110080307640440c91140d110446c04c0d401242c0141d10034120080c8480000800b001010f002c8091090b5110100c01800f685a04003d0700380714007143c807640510316090788002221002c0c0c01c40ca10300c0c07046200a0801908540c00d05c0340b01c0d000f0740a01e0003846802052002d25548a028000b00140c15204c2c0025680d0550100803025610f49070006045d041482400f034170f81c4000ca002c1c040d050f01420201d0550700c1d0442d0071520318140c2d074030100e40e591421050003400038444c40d08003408101100d4860319400c4c030061a66039032005417181c080e90781c810b0030100002405558500d031700c040114a00b0045006007030114040e6803080d040c540c0181c0114041050594000344204050403070255003550031800c0c101c0c080c06100611b00064468100800210002c600c64400c8403400c40c040e40308505454041e14000e5a80d0b088441c00072400d05040c0300042c400650703482034144400201001c40340001c256103c2001007800300c0c0c032440401100700101200c1c44410f10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 629044334 1250 629043084 629043091
    0x1801020106050a23040e0307061e021b0f12030711030904050403050904052401200703120f030506010e010c140105100f080601081e010e060703050712050108100f090803 74
    0x201403000006500810b4415082041c0b04d4401c40c50401c41c01040c00c000426211402d80c000030000e803250b515440d54000c4d403504004078501ea400005e03c1d05c036965001d0685003000004004a501462004114545503c50081c2f520b00b900750a200086445108103010413031341c80c0300404d59240c8140131011400f910021641030300841c100080d8040c545c10503124aa0740040c040d6502e214101e5111540380b2440c0c1c607600c000741041120381c40503065a41c00100c4480c05180c9030111303004035640b40b500105800600c50101e000c02c1c107a402c148a42c0e070190003864031418059466640036020000191648a06850706940c00010071f1151050a402407040902814031055090702d81480d040c05603110380800e821804094206400401c017080e00001c000c500c00324021482550f03070100c1e02c0d0981c01000d0b01c0041d004a0710a600a02400541640c0102c0c0640f000e0f40e600080c03c161003c900095074002c0c403401500754405080300100c003c02e0340c0034100e0845ca40c200490012003d407690446500140d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 629045584 1250 629044334 629044349
    0x121314100e10060b0301140109150f020d08060906010c051f02040816050d0201080c0f030c07030f080f0103020907020c1207050907080705041809020303030405010b010801060203040b1801020106050a 87
    0x3071600000644041000700c00032030000005209560601e0b103403d103280418461420401c196280c0300050346e0143c852500034001520702d07180b50940301c040091401503944103440150003411241c00141e0b105066980c412080034021243d140c03600e13001110f150b114a0000e64990007403940d40380b241c40d4144105007013210520809a02c943c24071800900b020f014803840100740c40125820003058a40f1180e408400b902400c240d1313807039500d01002d54501c0c0300c0c02a0403d581e502c0082006800c006101c06451b50600994540030701500c4590169400c0310103641c00203210318418010401843c0c00c0c00d10580c440300904c180d1300001c000b1404641418030002c00c0051580000c0c0c8107200c607042c5800c5081c0d20401e50300e06113446041c110000b5001348224043c044e0320800210049114032440d0f00207250180d409021607a4074074003410004d00070610021a40d0000300c24000000382e4034800025201a2000c80802514040c06003800c40c0300100255135550540d500d4400001e5a641ca0148820050100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 629046834 1250 629045584 629045591
    0x20705160e07020a0512070201020307022706060a02060423150603010e010b130b060f04060509030105160e0409141204060314070f0e150f04180212131410 68
    0x801c0034011003410020442c10855102040510105000081c400241d1903224202a80e6580c0c0e0700040b82544528440a9000071401c94024100c0d6105c903104486c0e000c4011060513681c0300c800130004a0700c0351680070b01c010390001001c5000f2a030030000b1400c0803c1a10b41d840c0352020f5105503241000500c004910340c0c01d036145c04000c081c0c28280601c02c06500054020080100d4900000b0411002c049580d070902c0e640b50032401c0c10380c561340c08072002c26003c13018070f42d00ca82d40d0f054005d000d0392014002e64029420007000c20040c0c8004100c40794102c3c000d07120140000307000740900000f45488542503c1000e90780c4204026043c09001d1700b085100c4a4074050350700c03424000090203031000110501480f60b22001044031030355011480090540c80d03807501d80981c059a40014004c006085062039843d8000200c19040c0c840140040c01111078202820792082060b55490089004204120400718080d000044005420180540e1454031801da1140040d410034445403038450801407807984c5a42c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 629048084 1250 629046834 629046839
    0x309030804030e041508030c06090a12080907092a0c261314210c090403030b041104060215040f02041d16091b121d0f010f050c0c0601120602070516 65
    0x230510085038085413403c01801c4d0942243d8600000c2c1042011640400c480d1402264128005000c600c000700031900d400d002141900e00600e5000d070b90031039200c040041c6030b000080302034042c900f9001c010360040c0c00c2c1031881c05400c01101404240e20902c4124103010041c0120413407041c603891020344a10311140d00d40594080c140f24140761001c140507200b040c4001c250900300d00000796010b500805170b500c00140e48983c0703070030b8014200d2007a415a02c141002c0c040740c125070040e0064000c80d11180d00b200d400d840c21a1705984000801c1e200608442d00001c1031001506058200485080400c0043c50b46c14a0508a20341000c030740c0249407049540e40401009850080e004090700c10b82140c2403680350440c00e09001c5c0c5560360320080c5907907541d22040105810107060603040b442045860a46040607105103007113009042d01201d08140c40c0c0b9101c04500103495002c03e65583e110300070000c2c10564240705420521400403041250469001c0210300c001034410b02110b41588407503415001041e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 629049334 1250 629048084 629048107
    0x605060a080304150e040b120a1704080601030807110a0f0e1006080402010c11101e0c0f14070b04031109010501020f03040603090c0e01170c010309030804030e04150803 74
    0xa65034403800c0c1030742c4148800d00c101d40e20101e2911802c034480c02c0c1455142100c20200e8041c0c258100c01a07070240c1590f00d628004580461040c04551085a2550304580760807001c8003035000301c0c0280e01c5076a05c040014000650301100518840b070052a803146048400320003d04041e040340c20040114502100401c0241c1c1108843d503001200340600090042c10464020300c18640100040d04200325640e8103c06e0040ba0300031640e01087c0540158050012003102418080b2845050034903084400c41c08034942c0d04c0b4080202081da8400d01d2500c10346031039110507454131b4071030900d066180161000000c8454411008100540c0300b0060f138006414028100005c0d070744168446070541d00070b0850a81b9101e0301000305c8061340d1490400155038021410030b000d503070380030307801c1482d04024440001c42d9184004038481c0c0b00d12400004c0325070700c80d4031100450076200c42050003004510100003080029001d00301d12050742101810004180d41942e90601c69001107511401c0c0c1a04005403400390007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 629050584 1250 629049334 629049349
    0x160c060906030e0304050f010c0c03051b03070812040b1c0203070f023a020c130905120f032404110a09090608030901030b01140c06220b18010f0603060506 68
    0x902e01080a0b45c18241340c0380c0445c5800c03501120150400800b0061401003068501d04032000e503800070116520b0b000b40c08125088400914002d0340700744200040003d00a04c0004c078001841900c400d440e0509241c41000009508061051480780c04400100000b803902440514810700b0f540e0f54124500c0403509029061003914001804901c00c4917850740410001180b42d010360b0300500f05900408520040101e0a00d41602c54036a07200b000003035044411405504100c40e00e41c010b0041d1824150741000c030350000e108407440b41103a400c0c107000050351740000183c285000d0106500301c240000c1d41000150488940403001a0b801d8400f003141e084c455030000041c0003500c10b18008000c00e40c100030409649001381c201450400da110f400c00c00c00b6920800780c07400c0c00380c240c00a0a0301c444a0350380c01a140d5400f280c501c03050341002a1040f0344141141120a826500010740c81020380700d003484510f10300c0181c81c8440056498503201c0c44604c50501c2000c0003180100d10004860414000b0018107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 629051834 1250 629050584 629050601
    0x30702012d210b10050d020409060905090f030304200406030203030d0e0d09060c020405070905090901060510170f090c03030a020303061314150a0f0e06010e06031b160c06090603 78
    0xc041c40c200c0050810340391314a0008a0703400600742103490380e151302c6445029201f242c0024910900305070000681041503002180145071b00015034000c0d0884c421381c10b13600e01048801806100c0e0035210940c00d140311a0341c10907003510140002c2192901c940110340395500a076001c40940d0b03560008039804403018810b50115442c0b030310b0b0070311807945807080c006d00d845942e02002c1c4c0f00b1699030010551160140d0901001071401600300780d028581246074600030040c5100b030754010030003111501e44003441060348030341030207030b50b40001465200c031840049032860050443c1c1480c480c031140c484080e03800300301a01d51015250300640e07a03440e0070414050451903940d8142d07103544c01c0030000601b51106620050b40011b02c501d0746140a650300c40065101400307503024904080d40118040b0f4110750000440f4071512080c0c80e56800c44c52070006101d02c07480304441031682c000d040804515124191070007070010035100308480c007900801d9140c1e01c10f000000da002c0c0006c1030204004200480e0140a141d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 629053084 1250 629051834 629051897
    0x30909040b160905300717010b040605130507020c062a030a0504300b0601030c0c0c05060702030c0907080f10030b06060a0201020d050403030515030f030702012d 71
    0xc0350b910f84408185440e500915107035001e20b4144011400300503d180c2c42d20000c025030304480110742d03141f0506603004550000b1a480d542800011000c3e4200760103074808540015040180c045a500c0c107440003040054041030171402006e1425006030344a00c00762018a0041c5110201400c1d00c440f0003081c40d1709030300e152403a0b810a000b0440d665801405440032540300910003038030b0016503500c0f04503900b12200c00c0714880d520074040c4002d10030304006252041a00380c0f0100305140140c40246c807248420300c80144159030b00e07401032105007407071005000e24520140c11074003000c1043c0001440080100e813a00005000070080142c000e60840d0a20b40081d00300064024240c1107498601c1070020003001070703016040000d030320211380d4400d6046550782241c2003030030840d038200303450020043c2605a50303000380e171011818050140d14010400341c900007021002145081a5036005548104500610082c2c0d80d01d66080340c400c011054402c1c0d00120481c0c2da500710300040c41800601500c1c5031114014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 629054334 1250 629053084 629053097
    0x201182d15090f080301080714220b030705131517070302300c0901060513031101030605090405070503100209010e0909010615030213080105190e030909040b16 70
    0x340400d80c00c0d030000c20005010100811996101e0030404151005000002c0091000000000f508900803400700140e403c1c1c1044956085007103000c001d07e500c1e001071642c10710780c941900b001c03445025901020b815180a0107480403169a880040d0031a40c0700c9a0294045481c0c0401d20b10141000c01035030081d00740b0081e105a6020340c9000d0b0356913421a0f01000f070003191900148141114410080d020f82d13402d2803000c40071294a4000e4039112101c451807503000e0005600040b42890140701138070314540000016901c100e103940c40354500c40c10311404c0c6506140d91908045415102d11081c64401d500460041000c1c034175090a051510b242500072a510a05c1070100c01117603a0b0210640d04190402c5640078902c2d1200000c160051001390301c80898021500a030050594050300500302c0c01401000c08600a80e96000c0d450070785104031010070503000e4600b050b0b80c06240b1079008070340100c01507003100d0601c007101020854a0a09076001d44c1d816800f0000c0001c40400d8511140d102c00c2d2600d8201d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 629055584 1250 629054334 629054423
    0x30608010923060103080d0203040203120a12060608090a03031a33030c030708151f0e040603030e060307120203011412011103010b0705191101090b040510050901020118 74
    0x46250307004104031f680c6200d800101050039075804000da1000d55015141aa076101243c10002e80105140c5100d0b1580e00c2c200302c40014800e01858100788030f001078901800b07035144559002c60083c0301000c4141c1501195000500194540045d540201d40b03031141450085180c0d200064900311100b600880c1f400b408000b0030494518071801d80c1e8000c84141885a4680c83d1103c003086500c0038440c03000e0b0018411030034001510894802c10204030600e80703402a2501e052001c0c8415038240303000140114903203584018040c01c3c000b00031640030300c15203404a500a105148203060780d100f0783c46407081c086520310030400c40c034109013201030418002c0020131402c600700000c803026010500c50380750804c01c04516201401800e115010401604490010010140f854002941420461600e0004075240c0002c038080d001602150141c6100400008000381e2810044609902180c0140e046540b00d015640b5480803039002c41200e1840781d4420000d080d19007030014001e4445081841c41142a020750 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 629056834 1250 629055584 629055593
    0x4360c0e010f0302040903022a0a0e060d1205190e0f19060311070512121012020d030507060e010e0f031206190f030602030402090a0c1e030608010923060103 69
    0x1102200e40c1502c000c210046c06003001d900b05180020300388803805418241c544025460088001705580440302005101e0710b40a5100405500f12002e80c0c00c94111f250030300104415007004e07105407890703103031280c90100350020b6030482021402c40070010590f180304050035450112224004032a0035501c980c03c180d440d0025070a10b144622518040c075680b074200a50f0703c00e030007045518031508481140c2da1801842940e203095400303120348a8428100714081894003000080040840e048540d4041440c4020340030001e6809420400b01d0901008000440010703001d400703504400103101d000040c001e90320864a0b400d00c100307071602e03407610707042000701581c030b05803a20809030040e805032914040c10700360314900c1307015998036081050b50010700540001041075540003140715138420b5030369032242d48600110304103031458071180a01084045175000480d44517200075a00900c081e14001c41c8403031785d5a01003404c5400d424015185100f421005950940304074280389420200d8000078812907166444 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 629058084 1250 629056834 629056859
    0x3030403081803181c0b220b160c020913051501180509030d0e0607090902040b040e0411150c0601080d0c080703050f13080d0c0305030604360c0e01 65
    0x14050000300500411040305c1c1c807a41588950042c44580c00c010249a80c01d1084c08084215020351044008210110400da1041d004085c0c0c1a4482160803680c0c840d04100128012003a04040410011440d200d0140c2e8038005020b0049050074405880480107080231800c00d40103403006400ea5048100401c420440000580f0a8030007000c800030742c1d91035001c0e50790300b54401e90391140c0a80e170070640301c1c101504012a03154014076664a51866017942c50300348005170b000310f204e115850301041c0002c00400e541c001504d5403080c03265400c40b05400044000a15004041800384c2c2d40c0103022030206030b090010054180900202c1d0000d021004410380020001395200703200500a28002c145242018007402c2a9480c091080c1061901d40450b4851000c04117445d11031100c4a1050701c15480e01540030312244040180c041d92050300d1039464a040c80040d119031130881494199604075914500da0b2010420269001c01a12400348401c030305102c11112250380042c0000000040100b1602c00c0c81c06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 629059334 1250 629058084 629058097
    0xf04080c1207050f0109030f05070f080c060304320304051003090506010b070503040e01291e090a09020f090109170c040c030e0607210c050d0504050c1203030403081803 74
    0x113601e03400c1040031030012a0f407092240d20003082c010941a82c141004004a8024103a44619a0508443e5554540e169546004495030b0b50490300400c00320f000f08041c0d1012003a03400d000d04007070303071552640101c1d01d46500300591240119000031506001514050a00a201d1001460244400106034a9581d160b61044c81401e0605c5030005882c0e04208051080d04c0003040b03140225409903030f5502e2044900b40b43c80009080b20321303c028000f00c501e000301080d180900a009200301100c55009007502d903942c41440000e9000b0750b002130000710240b80d40001c0200713940c80750303c040d00c0f08104c0001504100346130300400050420141c10940c0d6090001d04012040d1048901140e21041424282c0c010400d0203c030070f1550080b071041100c141e8100c2658485000d99800d001d0030284100780e180119800000e0f1100007403420800a803085000d908410342040c0504151100f21150f640054030034031101c05901e1b40d980000c4104000d064000710382550000d00007040b812150200fa5480e5124451003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 629060584 1250 629059334 629059339
    0x5041406130908040603090213061d0402030f01020409060f050f1509060712360b0d020d090f1203180201050a021c0207031b050105070803130204020f04080c120705 72
    0x1031a001d0242286400981005403c502000d41d02c030b85404d0010b0240c029250309034000d009141500ca12018280328020849012089284401c04444c040c00501c07a0081c1099074580b040c1c0c0b44030181d5400a10040000700f0784500001913a501d0400040d40b00c80c05036103c50720a000d005040701154407010510056103050700e00d1256650503440001c6c540c1e000380c80004d0500b02d01128244601030700030490380d0200f4000400121000f000d92007030404190000317094056010041d100b0132a05000e00050b009403082c6038005400c068002c0c9001d411141004016030b0b807400d403403c0c01028070010303100c0c40c0110291031609016240076801115a0303d00072a0000703040050000354002010f100740041e401c203800c07010070715040d10600d40c8020b42e110082d0100369400310480440c0f245ca04040c5030794004940040c0c40301070414426403a11109034000505005c002880300b100000184d070703144000c0a401c074420750340d0794032a070400c18004e180107034104850b030040c1c030790b03000c024110280001c900040301c03801c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 629061834 1250 629060584 629060599
    0x111030c190606030807030c350a02100509010501051c030e060c0f010e0d020c030c090f1e070f08060d17031b030a020702030d021606030f0905150402010905041406 72
    0x780d20b0030b10010b140360382c40984458070200e035007400c040c3d200c512103590902805502d0740645e40200b446a0401900f55055240070390b1410941e0000c01e604042d104410640c01919542411060510180c030800c071401705043c0d6550703005120520b400402458001a001d801580554031550050402c800c0071030224483d0001196913031010104008010050703240300f00034011102c2048405076920300709154003016018002c4010b5031801c0c009036894039414020250942d40e280c900a90040000c00f60000382c00c10300000f0081c10800d22165083d0150045076103031054243c0c0c00c14020310070790001c2e0400f4800d0030030301080404955040e510f00b0500c503440c0c0c1d9007070362521040b2aa13251814080c411030740150b804010400b041416601401303039940250159201c079810814100c2c1c50f941c03400c2c444050f0780302c407001c1801410700c40d50180c0b9000303a28800009850ba2941c0b941498400c0d0f00c0c044440c0380304404100300071542d100c0060b0005100c00e41c0c040c00480010b507031f41b01c00d0314401040389008051 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 629063084 1250 629061834 629061883
    0x30a0302070c090c0903020108060616020405061215041b12060c02160303180b0c150703090c150306060305011a07020f060c030a140304021c02131a0111030c 69
    0x2c84941c40018001500100081c0750349400140c03010f40d540c441a400304d030b841c8000429a09000e411a880429000040001c407412036080100600d0040c122a030003040c007024141c03200c2410000d5400704060310304003880d103140c40d190805505000d100a134000e1200c0380703010400721411907104000982d1126010403403078031261040b441c0c4108540c4038951031446e80ba0010505421a40a0909281d9001140203c94455152003218400c00400c000759610048242c01110598202590020803500c0c010880c03050f1910356078901056504500d040541d06017220f681d41d50184520001040d045c102032099615000c0c0310160b5031400d02c15640703c050001181c01c2155982120031140c2c0390002c14281c0c44540e88841075a03640c10410f051000714924165403d00003803030009407449030b42e000f0304090325002c2c0402040354201050500700e0b0081149103440c00d400005014082d040d444141d42c140c00542024001000611042c8901020790020004590114408039013968407003012040b9610000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 629064334 1250 629063084 629063093
    0x7051507060e060c040812210a090c12050106140906091003080318010506010908120c0709020c03130b03100311030109020301091118011811040305010228110d0e120a060504030f020609030a030207 86
    0x14154001050400c0d2f00e00c004c549688103d640a41d090b002d0802000015111304049408541d401030b40356120340c1d5003001174003078a0444402644401c1040b040c800c0c0700d03526a07540801e03401c240c800b96641110402105000d500c244900c81d8443c03001d00c0d20000e07091908401a403900c00c444030300b80c0b100c5400550001000e03000c010346e4006090812085655181d211040794680e08030550000c40e984010100050b02e449100c1074900944446902c1e036041c7e850b40c2d484440980c981b48010f03030595203a500440145e03800307214880401d0f00a024001190054404000200d5000c1c3c600d2044680c117035006000e0f0304080b95162000d00c141c00317800510051064440076143c001c80c2d100034202e60000580000300c500e80500040f00c2c40170341c8503000e6410ac1c481000d84800d00c40e5240c148807580064402c0445901c20003170310036404800750262042c0e00d40f1200103802c00251500a807000d948401c280820583d011300c030351460980398405000c01d03041a205103520ba105d8070050004241e008186a003d01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 629065584 1250 629064334 629064341
    0x91104081603030201290d030309051f0b0604030f02060304173105030322050a09090c050102010506031c1205160e0307051507060e060c040812210a 65
    0x104801412201c220740c10859450400000340070490042d402c2c43c2c0d0b003481c402c0d800c140150762060306c1542210000406400c0c0120903414a00941c201900e413060760010410600c100e00b41e105e100b081915020f0031001c1480240c0e0300282910f0300402d802c01003040440c03164412072140300d038101c1d4115506d4885080c038044903002119814410640060b51148104044807040700440c5103400c0c2c4c1c42007000d00a0076a01e05189841a99015042000b00d004481000c0c0d441944c0c481d4a07661b0400810b40761400304000310069046003049503a614010000e0002a0521300000c000900c0240b01c1c9140002c0803a03200c050210070081005003800e80202c0003030186155a1162080640400c01454001001c112040c00441200046089000480c9407428007261402c19520082c0168440380c40d40995075265a00c6071000369501c81d5100d004d1b600005041c00085e025180850056803201d090002045c24140a4000d4003441038040140e4a0480041809104c5200b6411591540c9984260116028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 629066834 1250 629065584 629065589
    0x1150b070611070b16030e01060501080c0319022208070302150c0f03030f0403170c1e090303070c080709090209060f060d060e09150c18010c050105010602060f0a0b0a091104 76
    0x800b02504c042040c0500d074100d01e582010b04554060041c100d0220b4100e080301c1c400d00603580010f119000058444803600002d5802c010740f40071800203000c0f007031418822600b080610303446c1d11a200d141d024031110b603861032401030f1840c3c0c00034181c02d9265a0005a080c0c04c0303940e40208004c004224030320000300610001260301490001e995407841c0040b14004e030030004503401c80c04116a06e1b19003007058400d01203075103c2e0501c5600e59281c4203001d08854242d0240007035201943d8030030801700b20701b038030f0900242072107901c01c515000119080a14881c01c02c10b0381e41109001c18030b40f880720009030b034452200b0360300a5811f07030f1031940d49040319010405c0d81c80b900080842450405e8000511107502840b898071540c08402500d503441c89000d29141046416a0a140e0701d01003404041c4802c000b030801030115810505110180e0f1b4440d0395800d0035110264041400350700301d00200b0603400c0920003a2a0310007400d420401c081a90580000da000d9402d010305210b865030703013000007607000c0448203c402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 629068084 1250 629066834 629066843
    0x151403130213110d0c030e0a030e0d080d0e0c030616080a020d1401050f0103020a120e07080d02010e010b1804060903030b1804020f0f010f08060d080d0506010201150b07061107 77
    0x8000c0a0f440e01044030340c0500b4031006282d00d81081046503070b1082c442c1140c0c69442401620094040b0703102200d07564824500384e0382c8403034444451070004900800400d583c00441c44045070310200c035403107942440003000c90180603400c04810003030000e417560011507249480b41052134158a070b0610744d0340240211650703807079180e203001c4070640700c0151089068100d50049401512030840b4000450a0340980c00041000c92207242d100a210714076a00002c21400b104030440ba034160303985170880d04d0301865a603407001503559042078109007042030242d908020b1050321320304440c80e24403100c002464070003400a4031581d0780e040003604140c8030750400c190400c0d00404014000b2169111050001400d84007240310b9001484141c46904000c0040340862205840c0c40c50f00f141100e00507100d2000c000d0003294031100e00e5081c0f00020f402d0700040d0520070700c101000240c0b445e000c0c00182c21200b01c1d140c0361401000490f0204410031204003110041540104007090700110802024014000e20720000c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 629069334 1250 629068084 629068091
    0x809071211031204050109031719090611031c050a0e03040807060206130809010c05030c010203151003060b0412060e03161505040b0103030309080c060907151403130213 74
    0x20140500754240c011045402c40c191454100e103031440c10818421445441c2c045003410104102080750b161928007849030582c803003450701da044084100242d00044444001c038803801d10600502c0e80c85040d400710304640200031846c000c6003038480c05824655040d581d03004c1c1d4070348001444013016030300110354141c2800d040300d842d50748428801e5120811130050b000148507000000c0d880c0c00e501c5078121442034128605c54a00240640115100300c1200400e0719644010450440380c0d882c01d10003148100c0c0e00072511980a182c5000700004080c0d03c1c0e03000d404241c101942070040b02000b9045500710b812140b2b038070710300c5200b514089010304000001d24185000c081080342c5034001c440781001c1c0951060805200c1c035860b414542c012900d05030380c06066000100010300009000c0c4e4401c0f0714040c041c0700b03440e0034040044010740c07600c02c04540400c401c4d00500c0c010001140e20741c1c2010940b503281d0800a000709540c011241042c00028900108008606405400c0d500c402c10001141440c030f480a2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 629070584 1250 629069334 629069369
    0x2040b190b0c0d0518010302030903071703010303030e010903121802040203150307052409010512070c0b130b0f04032003031605040605121b04270615080907 69
    0x9070207503044144a42694081d9000003200c2c10310807800c40d5040e62101103030070003000001004600a41000386205047e1100f00010b802103070318504522460460341103455600d604501e130040549041c1c2014141c26810300306041e001030381000810b00c06000a110002d540303050031504148014100c1c0000c2e40082c4000103001007101e0586c40321490102c282e01311014140d84006104803503142005080c45d02001c0303080001c074941d40a00812211405141c0141442403040b031048000c00251521400300720b80007502010045020b41059004e09444078500e172010454032520441c14008241c10120100100010105030080340c00c0c1d41d4181c10b154104800380712294000b41d89074000c0c0d48030264940182d090025491140084605640c0c0943d100e6040c0002810030308051040a03025400c4003600c10100403031601440301078030003448180c64840b205020320f6005104006900d40d032104032428500240100c0c90200e5901c00081c860380b814900c103944a21000381840751542206d400051900700e0b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 629071834 1250 629070584 629070599
    0x405190803041e02130b01050f0406020d1206080307080c03070c030c0317071a090f0d0f090e01050a05060304150c120c210b0301020d0501122d02040b19 67
    0x9036208903c03405840da120a005841d581035100f1512000354031a10194092440c0b009a800c480350a600604000d410040003051500c442d8120703400000050740030707101c00304110341d0122a00c603900f40f454108000302801c08680b103460303210f90316000c4c0c10b1070783c0041d4003038181800700200e40c02c00e034015035024829601c0789810810003081d48426100c031040da81500b0840700000049806035a03000d1030210105200c2c0059068050004140d14113602803a40b40e420700e5801440800c003a0040d541d6240c2009074500005071214a240d001003981c2100f0030f005000d141c41d51068001900c074212265600e030760b940c1c54500c000c0400809801400d5040040020219030800c0100d101e4a942140510404030581c0c0200c49180d03000302030701071306500703240004020b000e245d201980b25500640090300e403806540240003550310070b03407000c500003246400c0ea40c01d21000c072105c41030301008400c1004c10b62915405511100b20014400b1740f080d035032008407017031660798a009401484034004c50b80700e407950345200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 629073084 1250 629071834 629071837
    0x70608161e0e010c061b113c06090d0f030608060a050612031602040b0f011e020313080705210d03021308150a0506010309051c05040e0c130e0c070b04051908 69
    0x140000c030340694a040d03d80c020104119521811402e01c400c01070260341c000234010060702480e0200b00d0440c1980c07a0041c00c0034042d5a00c5000c0140007410440580d500c000c0c02002c140983c9410145400ca05200100c0c021800700e41040604a0210741e41e02e480b400919008100d0741902200c3c80001503a81d60320140b07412005800780219000c106c060307078903014850700403000c00100b40002d126089085140b402110101e4a6070305900c122418050000c8011b03d25654a80201026a20100c4208000d14018095006192440500b0b0720940261084180e84070070905082c8145500410720455002c46504464010701c0904211050a43c50300f0700c0c1d88c0c03109802d4481c0e913019800c2000240155000c1d0003154145988507004140c040341000d040348000c07469803110380801004020004884100144203801019035145807907a0b020b000c50300d4002001c066000c4c440b06000e680410400090f00005c0d04c424a801c80110b0340380e0b503191710f4614100002c05040c0c050b604040144007090204000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 629074334 1250 629073084 629073131
    0xb0619270b03090102162006030408030708071b05070f082125080d050901020903030d02031003020a060f091e212a08011b20070608161e0e010c06 64
    0x30194042c00010a080c0088e9101c2240d015241090030004034642c0b0344035a01f85917006525150400555103040021000045c80b0502030300c2035840f1010601c0380543d04950080100808402403000726841031121404041d1040222150f100104030201801c80c0c02100813624031903800b00b410720f41c0c440d10300000f02c0e030440751040c00c0d80342c540000240341035414170803030748541c50007001581007240325100c6001943c001030580e550711111280000058440382e104101620440d194220201681c50004056006c15440903281440628000c21008858003c0c4010780d6620b22036600751f41c404482c1140e4550b128040144050400d603400c04410039400d811140a56299145080e66a680d1840601f40c80100c000400300f8007100100d00a114081c0c002800206043c603031075075040303a412a0450500581350302a030045482001000b40e144d52407091896045507604100b80380065074202442001e1000c01c02d030061105007201c000c1d59a00843c81c090825a2010b0b060103001041a251904d94a051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 629075584 1250 629074334 629074373
    0x150317130906081b01080118060e10170c1f0519050c150c0f0702030f030a0315060c050706110f01050414010507051e0d0b0619270b0309010216 63
    0x88088220700c00301013500d20741c040416504c4500a90815000c4000c0b000c40252100021756540000121900340c0f503825882000b80e4010020705074601442c2892000c42002c0300344040d0880384c0c5564869032180040c0807401901c61030020183c02e40c5005403200d03c2041451010151080301c602481da90003401070800090745800ea0700504070102c3ca0010300745040d221440015800d01c840005820702c600a071074070a0000301103881c4918120103150466220350b0070752001948480c7c01c4c1d507003001040c024900520780352910300d0b4029015224507840f90180c0c0141010400a000a00340f010000c0003003011192240c0000c1200381000d2500d01c8140300722600c000502e50070580000c078054020001d65041c02c110140c0c106007440d0000c40d10322150301c4500e140c01c030b85035500c0d00040c3e140c80312405000d040161000c1c6144c08144000301602d41104c41c03041c592080c540082603400a600c50320b4980881da100c94125890392036142480e40a400792862251a0100e80034591050189440d001007603200759 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 629076834 1250 629075584 629075593
    0xc0204020d0f1505101d03190312060b0f07140f1f1d0307080f040e0109050907080105070e090a061a0304120503070c03110106050622050415031713090608 68
    0x4903001c0c48014000d80301210301107900e41c4d42d54a812200106c2c09004207070006c003074176007c0300121000310640315221015000620a80e16004100129100f0b500150110710350031814804220309120903445400340c014949582c01e0700c08030007202c04100f03c2002105000554024803000386828105101c03d01844d4080c50070010551000601c0075103a00604022401561500300c8903100d8000b690b00c0a58004401c14040100003180710300d0300c110a01800148030040760a007002440c01d45007105580240c4c503a40d240109002540d41c205218400c280b20a4410b003455a60707040066004201c0740d40300c2e40759040e6941c41d22a02031000c4004610542c80380c2546506e40000c9401102c4c140000c607040804500c1d81c0303d012012030300070340d560031a40241c034001103540d94454001c43c04907006000c041010018201e011603031200b40d0401d0318003500782528100814050703803090744640001440080c0c040b8482648007840107030b03180c044845240340034080440450b601c40c8060000d01c44c0d4400c0ca03545028 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 629078084 1250 629076834 629076839
    0xa03081c0f0f15060e060c1c0f030b0306070f0e0604050d030f0216030507060302180d080405151e0903030412080702091609090b01090305070905040c240c0204020d0f15 74
    0x45045142e801d444d255030391807100c00a04030502480781e2050b0511645441460f50955407902000348142d401001c540e00c81b013106594880103800e0310440c00e43c86109400c22410450015806021204150801c1c60720a208200c1840480c4852290750060781d00f020b44540035400741504003521414160b8280e088540c80c0000784600700d80160340713000c02085034020f520100f0403140310fa0080e05215482d6901d240070200300300006a4803608c0c41400f16040e10300402d040040b0300c3d045000742d081401e00305080d03180c8902102290a00403020403040044a00840e40149944040050790b0103844141c030007d54480385420070441c19044880d040f4400c0c002c003000036291128807107400c2507200841c3c4400c80c12504141400c400342c40d2074055103042005c402c4000022504c104040e00c02007000700f00024040c1014142014410410b0f0400451085510f00703140341800b0384102901c1822481c5090445d205680c80003034041d01c80c60380b080c00120300300f07501034001c00c065501c03250411403a0b03502e42c43c101d130f0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 629079334 1250 629078084 629078111
    0x2701030e0303091e0607051c060512160b0405060301050d2a05090c07050604060b0123120a230403090302131b0813060509240f01090207020a03081c0f0f 67
    0x34100d401b800000c1040c440000e1000900046a00c141420040480d880780c907100440e000099102040000b540202c440c0024000e601500002804080141501d001d04000100d90b5070320043c45014090388048002d0824403d8420b1824003044400b40501858003103102a1520309a060040612030440d07a404603901092120417250441d5029020f130039660340302c0c1c540c0001401d01240c0541072003403044d042040d2400054401507441c42455000d5110a101102c0041a003030040c24040c0c5180b51800703c14000c80d1200c2c602e008203003100183c1403607644510742190040c10680c0002e40102c490b031f40807000400769410000c24241000c99400b50305800d480204e0385080113813602076055240401201c00f1034055001b00342c1c008150801c4a01344005440086200c14112043c00561542d81040c08041c0420742c0503c0e004154401080d410011150006190141148001840c0c07880000c0c1d03034020f5908074003011007805401142001a50a0024401c02808800440c00c0d1003a03d041c2091341d050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 629080584 1250 629079334 629079343
    0x9070f06170103330906060e0903120a0b1504170601031e020a05090903090a0b07051203150307091e0207110907021911152701030e0303091e 62
    0xa40d1661216441646141c0782d00045a0001605903001c03104c00b40681041e610703016407010304207214200014900c0542c10300804850741c42d009a400b4181030424412440c40000981d00c1460130400034814a4075654400b2008202c1c121040d42c007c46c00410241a80040802070b01c120f405404201c0201d030301da581401c0d20703103909000080003603000040e4944e80084aa181d80d84a0344042d01d039130b01607a00d0340c0010328159800c403003904140d84009807005441c00c204d10104000c08110724510b040031038590314140c50346010140420707a11008000107041c50303079a2001081a20000d020780320402d403610001c00243c071075600070700c40d00c031910110343c2039450952080b112200e0b0400050003000c039102041003640d040191050046101d002100140c8182d200f440e040c0580c810b079001b1040034800700a12980f960120a0300072082014084062031006204402014100030343c810034a484580005070020040015414410705c8003104108610000080c4440003501004c4114000410f01d440305648 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 629081834 1250 629080584 629080607
    0x91a03040210020606130b060d091110050301030f0201050a0311030a092f12010207020a0b090109051005121837030f05180627061303031101090b09070f06 68
    0x816442260f1080502c20303a4000e140e100b00c02401c00e071410f184009e0000a40e0200f03041510186c10749203008106203420302e20841076184906156042d90702d10303150743c2d640c0c40c4c60300000790621a0004100ca07016109038440213001c400070795a2a101c0c10200003150061440390b074121800505907996030300c1507210300d8281d040030814002031040f5908070018800e44101f02400241c0540d020300c09440140d403020b0000001e401d05d20041500c4a41050005008400d541e20035402103003514200800c55600100700c90240003424011122915400191985001100c0c8041c94501861000208404211000001d0030071003c42804e402c840802261422001c803100050200c0c40184811b101035001764050044d90a10300d00e94014014040d0209190390721020b011210f1098007020105811031803001c0c0014054140c9105081400be2085290900c1440c0005018441600380524101500350000c1d80783c5984120407441c5410b001c0d000075a510360310b010340700c51144040c03804990140b1a4211010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 629083084 1250 629081834 629081839
    0x40504050108060a0e0c06071b050409050a030e040507140705071707090614012309063907090b040905010c030c11030c03030a180f030e1203090f010f091a03040210020606 75
    0x2401d0415551146010145194a901040e070780c50001381e169158403800cd0341a00502c00752a20303024a10300200700761419001d9078442d130f14000c14001d10a0b0301403400074a1030613991015680704558145145410700a500403030446074030305000751601d440800d8020440b96481014811a074882d00c6041c0c0da20b03808843c060006039010443d40d00301c5a42d058150584100c1024240f51046032404500503a100ea0394110440c0409650f04a5401c0c04840c0c695200031400c090803000c40c0704030380507078403000c41c3d02c06d04803680c1c3c5070030920400ea0b54982c414200705a0000003007280150321000074020741045107603640400d501410303000401b03102004680385200c0d00e2010750714554036007803140004c0c824114400084040c40c041310001441c0000c0c50340e84140070b611440c503600d101004106e1802445020410340340c00c2404214402d803500d01d0b0207201d8003002d003031900d101c45420104450342c02c05940184070165840e41000c1910342c0401c000c2d40130320300940311610790355524181680d40d0704007556610b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 629084334 1250 629083084 629083087
    0x810090209060402160512120601030b0d06020a03020f030109060302040c0c0c030b04112e020703050309060d140109050f0c090d0b0421180501080906011703040504050108060a0e0c06 80
    0x1500c2d03140c241c0c000c2a94640c8005484441e603050b0311014909445144042e41e1160000307905421b1034a103404059008009107000d03c45001c0d1000414260012604003c10050300854044035540c00313901500c607240014416075031650303076440284002c1d00b100e10040c3d014610703103505400003520504681c3c00c15500040c020030007a00d50307554090344071802031059510061091908405079101c10500321094882c042d03030300c40f00c0e0146ca500c4600b814010f107000150360080204000040d0080242d50b5900e02c04c0f290715468144034840c4030f0182c8a4086162611420340c0000304503918280d0090b80101902192a40c041c0d9580c0080f0a2600c0b904124513807010780b101c00d500008120700d0b481c0364418403e100c18041c441c0c8820304696504a85003190001c0f8400950010a00c00b50503580ea004040901e003a04490400d000481c0e00d410040c01600144c000001c2140301240081003260004c0c50040c00c1007203103680d1140318585613a01911207103a66814512562000540020780f4850018000c1850303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 629085584 1250 629084334 629084341
    0xf1e02010b130c0507120507021c03020d0e0a06080c0412030f090f120803090c04050a091b061407050a050712060e0f2e0c0f080c0415030905031c02040810090209 71
    0xa07840286c0ba1070070401c50200000001616004240249005910005542512a4a000303824444400c40300e2081281c14903001c2c500e0741c3e610310030408651581c20f20040030303203404010001c14403442c0c0044046110802031340b001c241e0b02005090340341d503135661103031002c9482d00e9108810039958850503074050380c03006040010844000066030000c1c1020100c448041d02036012409840c2c049842000141c3d50f100b002d8103002c0700f00c82c00b90308004071680070a903044c04c158000c2c001003400c0c03942240c1380502150710700810608114145c3d1681d00701d0210782015039030300b0501e600e01281440c00c0b038515090070020b800602000401809a101d1000509100c1c841c15551075040d0a41d00c0030500364550070940c4c5448400e0600c40d0180785a0304d95141c071070728000c804004d4002c4030702521120031100c04000070050240382000780e0045c05030380e01e00410750610604001e899801654500040c40803040011450344040c0c1e80200110b541030019502864100c5000c01c007190100c91019402c1004032001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 629086834 1250 629085584 629085593
    0x3120810061b0c0b0307020c030a021e0111030d02180f010c02010302160615080c18270102030709030606140a120c0b0307030c03061a0a0f1e02010b130c0507 69
    0x10210301140c600301080030114182c43e2038040e0400c540c08050681400070503c0495a8103100c0c4419000d0103800a10b103001583d07010814022560024210101a0308881040c6030302c95104c59401d851221300b107a84500108443c10029408070020210a0980341c0d00c100840c181501d039504ea0400584a4100b0b8070f20a0700158003940c011205640b41070100408100040c81302c3c0320301601132071041030450805041984c1c040c07401181c160303424410600614103c4c641e038081c940c41076100c070254144090000ca040b0518030001c1c00d224001e43c56500100400c080346030311000c3c15003124040d00040c8044c0e680c8840902035188101c50940d00700500003024841d1201e400d100e030128510907035105810300d07070b100f240c1c0d101364000b566008000b030b071a028504656036144c0100000b41084000503004503070088500c04140c0708080a000910211842c1080e05901a1110160144114811b42000004840300a000305407003500c05100b6001c150201001440324440c58107507aa090f2112460010103496 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 629088084 1250 629086834 629086847
    0x1200304060b0f060a0309120c20031911180c04140f06040324060e0a09051e0f1203090705011803050106030b0406140c03150d0b07090312081006 64
    0x7419904025041c400500f9070326440018030b1081401c0e5000507103005680b9204100c1e80c42207017030b20204100c46031000301090b03d400e69807030840200d0318800d101c8a4028040b07400c044000380040302d800701d42c02c51481845060700b40c0360072090f0211013500781c1045900c0d41508084090341c0c00d04901d0022301007402040ac1c1c06550b081882401803003c0070405224000449135400783e0002c0710031031440c60580f040900d070140d0484181d201001e051044506010009000e0b12000349042c0c039058403803824900b800030070b0085c2001c001c40c103c0c00e0751102103013440240e9519889881100340c0d01c5a01c04941610765024150380c0100e0311003000d04207651a1000440e01090901c500383d400711501480000014030901c10b0300020741c89002135284924090800c00200d454002100481c59004010406000786007001ca07035101d400310303d003a420307850060081081c414401000810300303014a002d002031a2f03040324a410441c6d00c0b400071341c0d00c14070410200320780480c402e80c1c2d183d40c600407504040c05901d01410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 629089334 1250 629088084 629088101
    0x207230d0c020319060c020706022a0112060306020a020d020601080d0c022d0f09040b0a05090307020d0813050a180c030e0a0f03091a22030b07030b030120030406 71
    0x40885130a120707002d21000b400c468110044030301a541c0d252800c00710f030f010302000c002003081d0300142407212444141c0000c050003440382c4140404111554800070707030042c4a02584070f90611000c00c4419104d161910095005440100244c4156000484e640d81300141d060b0607103900324060a0100c2c41050140c46030000660300720b80c040c16505541c2141c00124010004610a00001c400f511940c00f09126400744808a00707401000c03d10104000725223207020070b07600009080000180e40c0e03501c01d0321328158010504000d6010450b000b280342440f03c004043d1030701d9442c801104200c1ca032b54000b00a969102da20900089403407110780200c03149071a9021423884c108074100410704400b114890341c100f90003074004585210700180b141c0140340c0c0c02601600030b80135a580140f0842d02e4180c03481154014404025090380c61649030f024078400c0180b00750011648480e105c1294102250040c019003c43c16080d402503190643c01211043c50948a0f9402c00b4102d040d54903644a50f1109405440c549 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 629090584 1250 629089334 629089339
    0x24020f04030b06012607171e180a1b080319030b010507020405040f030305090c0303090f0f0306240102010504150b011e02030703090902030c041e05060d0207230d0c02 73
    0x40c49454500c0d030b50140c01c5c04110040310720200091030020005000d00c0c403551904003100043c9010090b903110050384901841501c4403019080341d4422100e2030000000404503079190289034084001c1000c2064050010400c407001d0748052600e84409903524010005080d111041d0724022500503802948420891030040c980180b804070389402060a503181a1011950031480440c0072050541c10f11440d07800400150150803140e00c4800040c0da00d000700c0c04194480c0007005010811a80d540402900503171025090380c4c0f081ca00107014041001ca01c20500c2000079454651407419807043c17240c1031040350b100001e055501c0c01c40d40303200010301200d080981881b68007006c000103c0da8071422400d182e40e440d401150b5602461a00904801c00741c3e000c80000b40c014414045413021480a0714162407201408258544c1b61003c6155011a01d07030101d0b42000001443c4203102e2826001046a180a0540d40f51108070112014010041c00c401091064001074240003a441c0324941100819000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 629091834 1250 629090584 629090597
    0x8070314120c0405180405120c07030b010909051605090411031e0102190e031e10050103080405150a080406020d1103090606010f09030803010e0601030e0a24020f04030b0601 76
    0x25203a1000c5071401c0c0ca6a5142c07410101d4100b110b403624003985440c0400c10011700d10a8141541c401e6a5000c000c807090340c02c41e002003040041c241c4100501c000554102d80b22589950b51514841c00501020109031107501036808100041c29040c041e0000703d4401034030f00d41080d5903949070b80806004282c0031950500442e00c0c00d420080403141c0d401031002c0840001a40d13605011140d104000c0b0303188400051101d8104091070a039000f04080d41e0f090040b41181c82244015002541400c9000443c41d40c001c0c5814004424004c0a47c094403d440c0e040c0c600720000b0201580d418240d00420b1000000548480000703000100381d50040c0440126800740231440750742002014200b500115050b003080e034009401c1154942e07011500c40e00c19441e80c02e01c0e0b01e0700c40c01c5855100301c500c414090502c2c0da03030850000c50000d901c00d0380035801c269070150641e030400c0c40038a0f00c003440c0c40c5d0951031351452a2036050f1002102100d4130841714440f4440c040c480c6001e00d143c1d100c0224080081c442414404c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 629093084 1250 629091834 629091847
    0x61602160f090921031508210d1b09030203060106080c1804020d0c0c060c26151302120601022404080708030f01061706090403030905100c020106050112020708070314 73
    0x1034046100d42101c00c5a04c0105079101a486c4180081405a100046960200c0c0850424903200f135442d48002148000c40e5039241544e40d00c0d200076104440d000d003403000c07038031544048407a4081d90a109880c400c80a4030704d9030b6a80c29044544003001d0314002400282000710509900030006541c0000310301030400360070710903107040200496244031340400101c6c200f068000104800c83c0314452105445042504103403401001501c10780300c0c0e45240001074400b1101040d2000c0000c0500c0d001c44000074007100421a00c00c030001701035004022007906d80c0f448103000c0344266002154607000301076991000d403201e02950380e032071610b414040d1090f29030690800030400880c00c02c400851040c01100050142545020380c0181403600491040084440800c2030111603592404056000fa415207800302d0607400d14100a41070520038840601e80c580b800c0241f07042c643e0107400c41412990241c0758400c1c02025850b003827060703203e520380040443d0340403c15140001d0003140071035400c0600788582c900303100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 629094334 1250 629093084 629093123
    0x10614070f06020406030c1e0207030f0804050904110102150c0901120b09040507080706030b310509010c140c061602070807080313120b010521061602160f0909 70
    0x740f0170303000040000d0b140c84030207900c1034000c06001c460420b40d0b20500400d0080c010029203030001804011f1044840681b0f03c403e001d0701c0307402d40b809040f00400407030080c1014a024440c00d10840620390242c00f41d0b4803079007180980e08981c1480341c004036102616005010004441400080502c482e45903514808c005494543e950340ca842540300f20010101d40b402c0010241c94410301703601120806007415034414054032940210342e00070400c10f56400400a40101c11000403602401c0000120700c6c1c0410003900c0181504441e000300f083d0344402c80001e414000b640f0080c810103040c2555980701c00045149c0c9844070300050080c03905441510f18a40d120400c0c4c60405106501c118100d61011404400e226040c000d040020b0500c01040c0d4041c445690315681c0c81c2805100c1d05201d00961600b05502113003100081c2c80d03003d041710644080b03181400c4110303c0d00c040e005441e0014414181c441348201d00c00d1516200303490060700e11218191070103011034040c4c0100c29027221400c0300500c00c081810f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 629095584 1250 629094334 629094337
    0xf0c1d0607051e1c02030a03020f040801090b180a03080c090f090103030201020414120a1b09110c0c1504140105041d0a1505061c1b02030a0f08010614070f0602 70
    0x1501c01c42d0280144203480e80d070305441c14056a80c042604d003102c02030101c49680000c2200c0d0404803505000d0b0301c402d004041d0796068041c50740480d459500b4134440c142040340000400b4420328501540b200b0807101252041d0b80d80050080060110f003030180420004002500a0540c500006040100050095010828504c002e070320440c0980e4004c01c00b4800400b400d41c04101180050303a65000d811540c1c4100c945d40c405c564405800c28070749902e03400c00703441030f4520714010380001c141c14014440d1134100010150b0124000074050300134000f4802e000c3c80e060f540380300b020005881081c282410001c03007480aa410640b0581171000401000842440300f42006508421a030010fa0305071420140c00c805a48080d41030180c595400701080c0140d5039010b0684290142c009002c01c0030300c8400540000a109050040400d8071165140c203540c164000000c00550005680c2c1807490a660bc0d000c2c0d840500070701070380006c24082d4281c0c40403d0040b60150002034003580401d40e00e02403030384448049 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 629096834 1250 629095584 629095603
    0x314030702041e0c0305060f010f170c1b011434090501080711030f0f0f1303031701031a0910050103050601080705030601080c0d080f0d020d0f0c1d060705 68
    0x403075441280c0040181c0d141e00c540e18098400c5d0505014902d4090001004841c20401090610141e419081c0c0341030300c584803800003414408501055401e01c4a80882140c001d40c00742d00743e10f100a106109100010302a014100d49503074101001a150000c140b0049a03020340d8901e60b4440548440109400c0528503128450050312154032507070034040014403840c0001e02000a0040341041c80010881c004100e411114201040d10b441710302c03917000c99034288544002d038a0300d004d01040710320f40814106030082c12a8446e445c0c1d100c8000c038510b9580c180c43d400344000740112030586200c4030742d010102c0c5180c4e4407242c0740d415900b1121003032107800d0440d05e0a030030690b000c0d4003910051258000c00c00802001d4441200102401d600d4001041d661b00d03810400a400790801d01c0b00c3d02c04001000c070a503000401c22511040d100c00300007005000a4014a1015018900b45600740010140502c03a0000c2c514882e0b540e0202464100341d00f0101c800040c00e01500200b080210001140303040c04034810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 629098084 1250 629096834 629096861
    0x1a0301110f250b0f010e0f0f16210203150306070207121109040b07030606020a0503191412100906030b1f050406080a200a0326030a0c2007031403070204 67
    0x181c0d4104a468191b030000105000206026a010304c2076075800381890940c8855542120103620740c036a0030803104c520303e1200c5160b50303000c42100c1084102080e000380d480740035140e4a2450222507030041503555103040d0351440142c1c04c4050300344041c808401194600c5800380603026035081b504004580c04803800c840590b00094407905102000d80e040c0240c2000300521310080c49039000d81d44031140c51b4410105000c00910340821681c20650050410400d440303111009162103105075405040c1180085540032074030703884000d01244110480c402c40d07058075000041980559251210b100003150501880201d14010150000c1c1319610790040c1809440508050030305007c5602c1c000841d001241e80c4400c0b85a410004807146490f095100300c01c0f01d4000c0e00700e601d490742d20944143d109500803940c1c000240000b08000301180c1a07008549071998a03903c1c0d0480142064811a1606a25000c0c0340c2d00c0c2c22020003080403030103015005800d55401c0d000e40f807400025074002000c80701c940e401800b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 629099334 1250 629098084 629098111
    0x60409090b06090601050904051504091506060203030c07060c020a140a0b0c040e040215070c060c02010e01110631050c190303020a0b0c0c011a0301110f250b 69
    0x500700810311110940140741070300e020b00340b8105280041d2180c0501441c4a001d250307a50000f80d65802c0000743c04105402c0034004111024280c20070b5845024580c0608119070302b45500010018400407c50744646507001003581032200c19940d540260003050300301402c52040004032004100603103c602240c4005400504585000303160812040314000c1c2a00c1d001c500a01081000c2c00d000310006034002e0707040b11141d00400c3d44030020f82c0c150242d480041d00c540d00f001d078086081500003948600080c003d0301c42c200395400340301c0110f0701c2060240060300c0c039401050110f10404074000c44810f8503520035401e07070508852000c0000800043e90390940d800da0050310710b852281001850090820060818499990b0440d10003139990380401e40d0040c0000d4803071000440b00c50000d02940c16080010b0021300007117891102c44400c04145260881c8a5407a05400e600c0301020030080340d0781c0410610000d4140030314411181c902d08070b84503207a0506a10b5881e00300c0000c0021031207900c1441e0700300340d56 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 629100584 1250 629099334 629099351
    0xf0f0102040f240f2312010e1501110c042310060c0f02011b06060503010c032901050c031b01060603051302040b040f0207050a020315010f0e0411060409 67
    0x50a2001d250f07116000e500f214480222041d80301d4040301025525a08000d50084e4142d081203c60500a1811031104100205240c80c804074000017010303c0d140c403074841c1d1442d9881d580c0060307030480161909075591a41141405a5501855203011010700f01c1060f00c84030140040414251001c1d042d81c04c5402c064060f141640c001200c0e040358103c400820141445030a0140182260000c1c18015080e42c1e001c80c0711208681c81581401905240e942c940e6600c00a24a4000301418080c000d0620070b50810303400007800c034030910a03840d48005080454000400080b4900c075165000381e80141002010015019050b00c100010150800040800b4800124449505003165040c0d0803000c00c150901e824840440c040721204602182c04843c0011084420030004000b0a00c80410100540c00803c08005025012034a50f811b1402a030943e4900210a012100144400d0184011500101c1c50901840010418056015104041d102d03902094034001500c1da0300150701c65510181c556080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 629101834 1250 629100584 629100599
    0x1502030d1a030d080606040b0703030509071e0b0c01090218040c120c09020a0c0b0a0b040f141303030227031c2c0a0b1909050f120f0f010204 62
    0x1403241c00c203240c07010345009040003400241c480c9408403a10701000000700110303505a80b0201200d00400010040b103584005501d000380180104440203400b40c01011000940a40c0e003041c510fa054156100d901d82d40c9051004000e416041402140c0c00d565903a00721030010785500d840d68028048500d003800c01880c0c140780002c0444034680010807200800380c2880d0004001d1540303602621100003000d61907042e0f82034100c41d24044400c0140c0607030320391010300444d010140d00100303001c00b003a82c3c14801100b100c001c0034141c0e2214407040c421000d42000191602c0c45100350407081034803034074000d0b213004c0180c640a0b61055901003161161064850700300c06a2a0800101d001001c00809c0540001c11621020300b544d4000015900c51a6a45e02d40b8015140500715890300084010000618a501e444a4103138a40006200c1000c050b240d800b400101d60081b5602c1007180d20041070a140003210805115941c000482152001d00ca200e042d001045001d000040120001100068880d45001c51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 629103084 1250 629101834 629101841
    0xb030c07020a08030901120b010c051002030a0b2b020109080a03080601030b010f1403060d05010e0304090b031b0d0c0b030a0504051c020a08130f030807020306060405060f0d0302071502030d 83
    0x4141502d6000700104030b03181c2d800c5a585c1c0487e040b150400100c0701c0c000c3d00162001c01d100c10000303004e0300542c40b51401400c01940614002d01c115542009180e580c00c0502401c00d0548001104100ba1500784014000d41001078030000340c030602d4500c0089980f01c0003245400c482c1d036012804210a030040003142d580c144200702041e002480d104103d0141690045c0180308015100c41d00c0d0400000000c5072030315024914550503900100810603248100445078072600b0034000c40c5041418080805103c4c5400a91342140c0300b600002201e00c2c004400410041003481d2400711400381e0421000601d150064014500c5507008040200d16454103140150800c22000368401054107221141c482290b070000c0c3e2000f0496200c07286565610f1004500d103c0340365203512120049449100200411a2800150854038800c0e41201c0b42c9459040c100b20035500201d4143d41c00900012a694161601a42c4020300074000c3c016510719944800800e05803180204111000d41d0000440d162151013920 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 629104334 1250 629103084 629103089
    0xc1b100507080f06100e0105090307060206400c0306090501150b040f12050102040909050a0b0c0906071e0b07170912030402010503072604031d1c0c0b030c07020a 71
    0x5143c2845180204c0003035104501e804001c0700b00a0303101424416640074804035254500010102c590b03180d51013500940e20309040354060701461801100424941c0031000d02440001c40c0f5483e5a90300c10a0340d000c0004140d04038040c1d41001850b0310010200740c05105683c030042c020000426083d0390345500340480c0707c16030302c21041030b203080104204840ca803540d400241c0785006961101c0a0443c00c1590180c055500701000e007514060b1918200000017518800c020b10440849420b40d0f20700f45021194043d103800c440d0010300801480b0005a5814442e80322840a450f00000b6110f00b52100703814098200d4054001c542e456040302201007a980206500001031402041008078440201c002400082c00c028140080400403c11850242502c0c41600c04e40101c1403d80400b0b4a03108102d464064405801240e803604100100c07541c4880d402108641c0600340042c100180d040150100d0840c10081d254142c6080300400d202141100a6000e100c5041c9115107805207401006050310595 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 629105584 1250 629104334 629104351
    0x5010e070207050f1c0204050a1413120509060c1519060b04140a08031603080a0b030705061c0e0c040b010c150c17101514030c1b10050708 61
    0x2000d0400c260340e152005002003120541d1000c4005c000c422419881400c10705c402507204d418503040102d0940c0691006051450300341c1190311036201e0f84004040400b8042d006080c110150110b50304241c018002808e40040252040389007a5910b402d46040540901d1030540c07508080040c000789480300b002070100400102010441203142c09070824007031143e80302d98800a15884407409144d45c421011200429121080d2a0b460740f041403182024000003504602150b0030034089809000e49102d030440007071000c0d004182c0f06041c83d040000c41c1d0042889880b0b1080e051b805844500c0250080400c0d038207808004044801000c4c08100c1921840341e00541085607050b00743c40441c01001c040b00c040c6200110028409a0b020011038030800040c00c001000c0003c3c43c148030f14242405000d808407043c01c013620007000340b8411304450421503100280d65200050002c15100b803005c038024409442030620700d4102c0b0308031840300b030700f41540c494222803825900c1c4104600160040c200580c8800d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 629106834 1250 629105584 629105593
    0x140712121104090b040e0d080403090b030405060a0b03030d0903090e09010c0923060406050304020901080304151805030a080a03050c0301050136120203010b100804031b1505010e0702 80
    0x507a5600040750240303105115110742c42d03503540c0c0c125031110b5102c688140d1110083d200d0000c503010000e400c00e0740c19581203001a810700c00c00901c9911310317400d4034000c5621030080c5c1400d441e85045003000d04050b003012a814081040850035400751032040c48020780c42600c0700f25078540351045136509030710002c20b03030509030341080342060303aa5a0100c4c0200c10344e49141c40c0101c0d048071140348040e50310b14200780c60741c011000150100d01e4542000140d40302e00d00c211074105180e81c031941411b07128010740c491441c20001011a01c0d03481c40c0668070480c100c014001006640e00c1c0d543c0001b0303141103046101580c12410028505205542c14080d00f6030185442c4003062640d450000000d0000100741c617100200400d4840010b01b03003c25250360001e06404c1400140c1480d00e0301c100c40d640c02039854040380300390300e058200001418041c541c408103003160f0720303039280c595a036032002ea0f000e8014045001d032080c5040889000600c2078202602007201e85100003c5e29030400c109140003c2003e006d84055500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 629108084 1250 629106834 629106851
    0x30f02180906040e190c0f0909021002011103010b1813090507060206090c01080702010216060c020c04050f0103140304030b09070e07170c0a0e1807020d05120406020a14071212 77
    0x20320302c8807003025291103181004540c02c14241240294004c0030f5440041e4400107881241c89c3c100d0410a03000300c6424241000020080e0f088072611500030031803040500042200000403006019090707803140c6c1810098040d400040d40da20310f5421282c010940d114104014007030100094405080640010982400c0690201d541c4469541d0713098108034152001500c0c141c1b00390141d49100b0290046405e058215140c800050294201003000600c1109100d0209260074021240541d5514100c0c09290f4250b4907050000103410b4801041484104000000201d0180c03801e481a520000503107690750030200507008900000c1c0c401800c000810116030078851405000070b800540c03000a6503950701081c02c05a402c10200000690b211309226030b1710220750102103000f4131810f01907083ea10744202d614420742d910f00034142001c0c003040c0c4403800140040e41c180d00031305c4c8802c5681403400032130b80b4405102c3c406600110381150700800310780b1007a010941041242c200564100c10500c221719 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 629109334 1250 629108084 629108111
    0xe0607030801180204080a050c01020615060409020c1c030501050a090504030f08150a0f18023f040807061d10090f0b0103140c041b050a030f0218090604 67
    0x18180a070408850050050b218080fa680e0304650081c201711040c0d40300708800b0709020392100750741c06126025001d40300c0002c4001c0680c03151a074503814000c00d803606160034010000d000b500151030203403062041c1c46002c029510540c0010311803e80f5a50041a0340d81428144100d90405510103642c140c102400d010020390800740ca14035003203080c41c00910f01e40e984948413100d00c038800d1449412500e105d20110311b11000e1000c04041ea042c10318010070051603560180124400e4042107a1203003012203020b80754088440f09402403100d25a8a2a18520810b11642402c01c003501d003180c5082c1c00181381c00070441e0601400c406140d010200c071102d0b0030405007030390b25001402c411854a50f924034a0340204003001c8011154540c000d61444074560310381c03031300e140b8000f0200c6403044c80d803081c110301d01c0191525018103000c3c001d25603110100000d4041040e02d4503045040c0398400c0c55154200300705018400c0c401380410001084008042c4030b91201840507101e009880715000354102a001150704 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 629110584 1250 629109334 629109347
    0xe03091302090a0f06111c170403030b090109140709050901090e0a1502030117071a09060c010f150603110306061c0501061707050304330203010807060e060703 70
    0x35255003030160756410100300141c030b035a0240d0001d088818103030300c01141c419031013a0380030f2650506c84110f450000c03036030941769000c190387c1040b2000183c0b010203100034010740c2100b07140c02a20038240840c0800195000940c412803d03001070000d95034038a07241d0036850340944002c0c1c11500c1400c0c40c00c211810080071509007141402402d20703250f100e41e9000081c00c0108981440c82d60041e0035540740c05421001c40d000381d4028466000180343d861045019420b001c14900122034003980403240c2007442c082105d082c0e40162645030780c000d03018401619204421b0040141240e80401d0001d030b040020100c0c180b06164581126041500e08540200f018505c1000c03603410041c01c031389058880c00c0e00c400044250804000002c0c420f4100000041d9031904444400c00c40d501c1e02080070314036601d4440890b1280030031140500070900d006140344400d0807841c4030604a02031a410450701100b249000400c0c2ea00c01ea020224940c81141d003003110907403203080f034228242d04039605407a1909503103008002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 629111834 1250 629110584 629110609
    0x220b13090525020307061806050106090803070b060d08130e1b041202210610120506060409320717030406120b12030d0b040b100e0a08070807090e0309 66
    0x414842d000761032800d070003041560003580d44820240182c0f0b00d400e0303540f500007241c807000700e40302401c000c00030507200d01404040341a115008000e600709401c6448000d80c0c08005840d60741c0003440d210064020400040003403030540e14802901080501c2c256a024039514014440308445030f0142403010300c4000ea1044504541c603101540000b0700d00b030700014120345454100018000b0314044030321710064000c00c905118124a58220141c256961041204400702050080044c2c001000064081c9081d92082540900032580720740c5039100c9090302980055000f0010490401c00810900311303110400651024051213914412410124403400341d90340210b000d000c0901075200007061868150b64080d1011403001444100c40501c40c1d00c1c4951a81d000a08180d681ca00340511159941004d00801d00c1c108000780c28110401210b680407a1000d4502300b801c0d030320134407508001803180e408101c400e01400342003010388141490072109a0842310403008085140d00240302581c51580e682d202c4056 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 629113084 1250 629111834 629111881
    0xb1b0a080405190f111e090a110a0908061501080415020702150706050609040203071a0f04060323010b03150d02040509030d060f050d0206220b130905 66
    0x3607038403186051420100031820f004801845000400103010240b8031043c5118068040110002c80b51400d000700d088401200c0c9080c203080307060780c001e28281136034070325403010b4481c0c0001404443e52665044581c000b03050280001c050310014045036105000080e0448a1a00c3c142e00c4d03201110300207080944000c0001d4283c03070034411094104201c5404980c5250390042110100a000c1c0181030308a1700700c0300c0140c442c50b25047c0010305a04010400d0b60055400800400302189406900084c2505004002d18000010700030361441c420a08060405410705803404178194154690708a81c184580d01d01c075905024503401000384180c041f01f140e407c0800340c0882e44800d040240070589500c60f04030000e422a10344001c010001d0804400b80c646900417000500c0342e281e0b2480c00b115010307250702840b0341c0203c0c50b0f0b100c0401850620010f1500805000100090040c00c181261501003070350311411301040b00080701c104c122415510030000d040408001c00c114201500d40800c00701c054483c0e0740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 629114334 1250 629113084 629113097
    0x60313060216080d060603050a0510090b0a0506040e0f090a0c053007051521070c05060406060315141902130f050a0522050606070210020a0b1b0a 64
    0x120302c1207030101c01948003a00a814982d6811840c0c550b2801050b80c0e1007000f00107480c050100d0441c2a250007011f0242e102000801ca8107402c1c601d1400080400039011940310100040c00681521034802400c010700d06200046030600d0021180c11800380010107041c3e01c2d030803041d40c0d00300150000b00301c242030390000e880d00c4250003203c0341d1403483c103c060b0040411406841c440c1c0c40301203400090300412750324107460440081d9500c0690181c1c900402c83c2c0b002c0d815400004441400c03020005140e48902c8926140180141d10b40f28207041c007105840964080742c490780140305004035000110412480400100240c00340c026981d10383d0380d0042c0505d80805581d549125202d40d4a0301034824024200c00e483d80c00c1652162000f0b81041944201401045140c0700044d09107845a030506d0915038980325440352441010040d001081c00070500350f8805810f1054a0141c0c5402154481c160425002030118130102d007084454890014400e10b1500c04c903c40469170001e0310703015590494a0350400c070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 629115584 1250 629114334 629114347
    0x60718150504170d0e011110020f040b070f03020106050f100507110303040807030311010509060718180f0b0d0305040918060c2102040b042304290603130602 69
    0xc540c544260f0340100d12081e0103d00c80d070100036001c11a03480b928495140c0600d10100a8019200204040010320f016004450705400804054005080703041c0d880818a15080e194403150702030b500034000030b45e6803407080d00c80c040070036409109080103043c003110504909005c1d800040c41c41d81c00025104100040441c5400422226050303403007017060300509581c0c440782c48014050355207441d84400d9001454001c42c4410115040c49a5030143c6c045102914840c4d49800051301d03003c00e1408110304550794420002a1940c1c2240c204810b2016070001054902c440c4003103034103503500050540c1c4200c00400b8000000b0350408120f0f8111514810702244c841481c0c0c20720b850f50701d03542c900031f00458100709010303504691000039006603618a080c1c2190254962810383c082703010394021002552001c1005000d420180c01040c01f13101c000110728109140340380c0114094402c4001e010303415103e81c5c130700b0240312000d01d80011403248040c2c1d90141985405420300341e18515090001e4481c17940010032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 629116834 1250 629115584 629115587
    0xc0e03031b0f03032211040e010c020d1115042402030601140c0a0b1e01140306101d270a210804020402031e16030f061214160303020f06071815 63
    0x8204200800408c9065030101600380a096100030200041c094200b8101d10740340104040441c0800745001096515a039100c0700200043c085c1041e14070740c025031000c45581c0c100d20007000811400d400050380f80e090110002d4a014081502640c00c02c5d4280f0400048640000d0102e80141c0c205442070090748030a90080380c5070341c030498a0f5403114507000c00030130b0b03817843c5116407031402c2c0080d0103d0b075a0b503580d85c1011001c00f8081c001c442120b01d4268034840d007e41030b00c59440d000f50b5452600c07100881e801400d000400ba52084a2081c1e8014000000c107029420101070386089546c55640310f202e0300d403d0001c202003c020310007072186601201007007185480d50390000e0030810340d070210800d0b400c10541c9895081c203041d850000203414481c04da0400c0c05030380101d800300d905106c80111001b00c0ca0b501d5a511560700c5039030140324411403687e81e076581c04106107400154065000780207122182002e817424084020710040a010601000d9848000100c103640101c400b41381d002d0300e0309040080c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 629118084 1250 629116834 629116853
    0x412090f0b040302030c0604050d080705031b0f1507050f0d090602070b041e150222291806210a0e0c0a0303080601030c0e03031b0f030322 61
    0x10000d00d0302500c40c0081190100e060040040c1c03402201110707580032104c0d0802007684100d0060b2500024031903480c000155180b030141413400c2c40b800c252410801e10404002d074513801d07032031010100d510449205401d0f01d802d0206440005030641024000c1c504114090014405d8103c88801903100046021020010b603100402e0264040402d543c0c480d03c07030900d420020020340f0700b0340e926001400c8241c0395603d1040980f0119510100305804443d20346e00202c001d400121140102000c0304401800490403001d9a20260203801c100e41003400c800358009a0360399911125003440b56041280080c0c5030010350381132142d55400c84500703540c0c04006450f92400841f00e400405002c00d00e0f03081c803a1241e11600040c2c0f10310f28680c00c60307500480702420400c041c2400d00c000b90108a903080458200c2d4400c0d002191003420b1403c1040d10540841c0c0030900d5603200c02201c0400c020410302070540c0702c1c07007405280030441d01c8100850940c00d040421108603501045505008461540c140040001016 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 629119334 1250 629118084 629118089
    0xb13090b01060f0c0b01031a010b0702010c060c05070c0902031801020306030c0603090f031201060f030c0c110d050a050a1202150115030b030f25030b0a05040c12111503010e041209 79
    0x8601c50350350381c40c1141c1c00508e21400f24a081150b20300210302032010000791621207070141c3d512101c4032600d8858000528940e00700c0000c00c0020856140030441c12508080140044000160342e841c00c10780351426844502752a0b0300300d03401003017070261b190f0740007c81504c507030001c88610f5629190400c09500c3c2010f000805410360001140700d02001c503190074403e040310440d0320303038100c8444486011401c40364100c42007404034059490103404140400003003030880002070407003280c1003104c2d00c2e201d1900d5a07032007003120f40e0750003054032500300007400307548004d421207a00003010031800048075020070311014090340384c1c50005444006a840d100750004241c00401a066503da98501c074000c54965098903082c4840420311121000700c43c400c0182031040b207410600009480d1100c00c20440a400e024009481d400c920400109250b41522400608540315900c07003101c50344044280101d42107070301510b07181d50300140700400c8001d0305d03030150070703403140e0311140307003096507080040540300300003640c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 629120584 1250 629119334 629119343
    0x11030115060305010303170106050a11030c16090b04090f0b090102070c1503050117330709080c030105070e010806030109170409050112030c080a0219060b13090b01060f0c 75
    0x42400240c0c242e0960300182c10303240603035640b000d01c0c0ca805080c0c12200c0700a210303200014504200b8481c2042c455081c80c010800c46006076442c10034000c14240c03609201806009400700c031164100602c454038895404d048001740c805024040290329000e18800b541c1801402c501d0315440000c24920b000c4d8103e4201c181d00c0b03620441c1181d12904617402c0340700942c0421001c01d2804001103480c151000244120107403481c0141020345100c16480f0801918500c0d001c1140c2030315030140c09c520515040548030300035039070352a040c0380c1c54490303081d2403c84000b40042c002d9140c002480798050b8000382104400c40d003800d1010721390303c800c40403034010900f58070003502c0c08414124050580d10584006e000b26041140e0034013642e40c9030410400e9400382e0110040105409095150000c0c000c072001d801c021003507006840c000d60000322041648103209100b200c481e9528a0785007a50301c0d04851080911480354403c01403401c143d034414440764018010141400000f0b820304041074800d038656000d180c0d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 629121834 1250 629120584 629120621
    0x130605060a0f110606030d0c0c080f012406051206030a0b09010b0f040e06011203120c3b0f0a0b0d02040f0e041502091c050f010b0f060403110301 64
    0x1050340240345078071107030380100010f0f00e0403031a00000800091081c050600200540441201ca100039036000c0150002100c03542182d00f4000380ea4034042c0070500c0c41d90511000400d48004184209107080c00002d0311a204000303c4906221940e484030540381400005400851140c80701000079191101f42d0b00010a40c2502a00700b1001103410b40004072000707420303512030718070003110400c010945950906103242139010a004020000d1022011102d960107400e0954001c00e08107200d4080e507031081511804644c107024020b520f10f541842c1780c8503c09100d00490b10030b040c4000b11621142c3ca0f1181244036034506036503413481c0d07640d02d4005401840e078180401d996246218007580603409c503101d0408c00030140200015150f107175407101c0d403099910002c03d140c2c4804040d0410000e4100408040d003107401481000305209502180341007540c000c0c80100b040f80c3e40480c0c00e909407028203003018080c1c41d1091107540c0c0c1e620381e80300399020341e03a1060f41170801c100e920021a004000421108171031004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 629123084 1250 629121834 629121847
    0x30a020708031911090607020f010905120a030f0306080c150d1409151e040f0804060503090d050a0f110c041103040311030a0f1b0c080706020c030f03040513060506 72
    0x106403503d0b40074078031048024016082d110b056501c041c01100d20a98001008102407001490b11245054088005050001110740c03648003041504201032189680d0740d0086445009041e08100d8189000d9030301d250030710406007003414141c0c07128440c00005015014034405070101042c0f02e402d03510321845000c030401402880100f011a038070341c00d0b6040f01e02070103035806000155450200292181003040c542e6540000154409080c08800520a4440302c00d40d003444400580e042c80107100814150f0b072665141e00b0304903049800c00c150380c000310b400d0203c100702144a00c0c1d00304032030601d40c3c1521300382820038000307098580d8200440081401d6005141880b54804465000701850040c0d00035621050112046c40c06565030348600c0c001000840e0540303070743c80c022521684041e4001c51010941002c0450a41c5e10001e68041d282c00010b1107810614051180a034100503a010042c01107000780000410b00c1b006544a00c668010980202c9101d200c000b04a54107400813801844c02408041d918407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 629124334 1250 629123084 629123101
    0x200109050f01022508040302010804060f110306010e040c020d0311090d050f0622080304050a0f05010f0b0d020a0b0a2015060d0507050405060d0c121a01080601050402030a02070803 79
    0x103024102c000e40c80113000043d0300a03601c0701d800d40d11489501100360b51501c0d042d80c005403180d40d40240111090341e10384108900c58507480c020a01d110f41c2c3c1c800156242e081039130001d0032000020401390300481c5403220780300b41c1075400903c0030070088a84c01c001840d43e11145a01ca4580b04200e101c0380c021180302d0b0000e0070840000341803145007030a8030584040d034031406000c0e0340100103100f008910462000290002c91905001541c11034410011100c0e112415900c418140441003019181c40c2d54812030b240380d0300042d0092603000302c401c82e0840650b4081d0b9000a11101041c0104030751800040b4940403c1400b070f2031680b105613847d00c0c914410190968041d40c0e100b414000681d40204c8810200d40c603070800000c000e007030b958440d016011b180c0c20b006c1444000c1500074035141c2c0c07004180f6100c0d404100000e0000f0050024051000d403144514288500740c21100e0086a4800c5480300c0108081c03000031038028151001101c01603a41d48805941c82c0203801801400307801d4100000a002413031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 629125584 1250 629124334 629124337
    0x1106040504060f06030c1b0201030b0409020d0c050a06051c020d06170a051209061206010905121b010509010813020609040606030c2c01080c0d02040b0a080f07200109050f0102 77
    0x11000341d03406100000c10146c0c00ca8141c085e580007142d1000740d40403513500640c02604110843c80000d0320000740003a56400045030081c41ca8402c0d0b544a201c40814065400c103140c006010b0040d6060080c0740910300c030050055542140c480c420050b41c0416403000003a1903070070a030004c010190503098045402050981c41e1004803d00316224427071510107040c046213050030f460309444002d0040703040c1459000d610101140092102d410007440d4030b40490305584c0d440e4813000d1031214900600e01100c908116026600c0b114450034184441408818416a4000c414607800805c5e0a601c1c981c24100f031012510502400340c4103980a42400d2010030101da15038480c1507081e00d181e603070107110b0a0441c1030004115000c05100206c00c2410744510075540556800754010f0703842c8080a15044c24958a00100c0e0010303080000709050001f203041950b5401202c0941058074103841c0705071400d09080c05801c80741001b004031010800389042c241900003e40c42000220b4002099480d04100740d0360b064002e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 629126834 1250 629125584 629125589
    0x120a02030c010b0f060702061b010c020d031103060a030f060b03100b0103051608011406091003020712050405030d110a0506090601050307090e191e0f17090306041106040504060f 78
    0x10b62034209a01d0151400d031a2101c1c006801604003071800300f140c0c0034031a2541c46400701c404048450b910701c3c0b41801c000d01c50011107281c4c0d503000d45115206c10000034265120038002d10b060280900c00c0c008940d880914490440c3d030b1101c4000300100702407419802511030010b0b51640343c001d04040c1e9115285981005600304001d9a041185980749680030084004044407100050440001030002d41c41d400c4500c2404440202014200031154000814070380320701c0070b0140000d0700400c1841c1080006d207a0700c4854000c5050090a240c01d001c0826a215202203e0101300300d0b080120b44001d060520000c00c0c1c40b078002003624807500d00800c00139920182803147c58028416035000003410340d0280f00d60425014418080c01140050490050381c5088401007030718014140b620801c00440303141a0103003030324443d01d09010114110304121100500c0b203a1400c604c0f200c1041010030541c1d01280017984a5400200d00094250110100780c203409a5000180c00c50324207400071981000c420450b004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 629128084 1250 629126834 629126857
    0xc11100501050f03060f06060901020c0a0b0a08011a12070c0f050618030f0403060b010e03060106030b0301180222110a0915020307020109030311121603020c010306180e120a0203 78
    0x20420030240506541c1c80044541b080c0402501c008070b800791070207100400d001401441161904440840000c10150942c0c0c0501501700b0006140f503000c50300404214010440214080364410305c40c07803603079024482c04400143d20b83d98000051180750103441c01d40d41e2660481e14403105d6a0f0140741c80c650307500040d65143c0b140c83c0340070314540e0004000800c46042c01e201d045070f9824a4655503a1002030403e07c9000c0e410300040240c11340c0b03e52030800c4010f0081007203990100b00c020b016402c1c036007110f050440c0140b482d2688081000035855140b0403041e244442c00c031002142c0d00c000c0c4c9017070003000c1e100c298990310a400030b03480c2c3d01c256200c0e600206a5141c0080313040d050440410036070341c0340704031440240410303034200b400c1010030701400701d00c0c00303108211090342c2d00c5031140c0c40b03502e4180c1d102003080c1d501003000302c83d882c00b1b142e8108003900585d030080c00e080103030508240e203a2280f0280c00c0b510b4200c507030329440d042d25540301c1800900310f026024032600381c48031232404000c1d4803a04606c0720802c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 629129334 1250 629128084 629128099
    0xa050d0f0b04060f05060d110d0c120b031c081302120307030e0904020d0803041106070f14010c08220f060b2407141903050c010c0801180c1110050105 66
    0x350013a48130f42030000c0314801880c0e82d141407905804ea6026051541c0c1c0012110024001d0160f0840d490084040107501c030341d55603026070b6442040c0c604a905c1d4600c420301036030040320340166581220390807041c9143c0c10700b803c652654510940c48a00c1e200d41100942000a0080701d04201c0c0000000d080c400e0f11a0300d8502d01000080c1c18000d02c4031040303c0181d8440c2c01c21030a01c0128038100003c580190003290380b600341100c82008185c2ca0340c0844012903031069166201c2080c805014411245099444000d012a10280100031300d04903000d060004130390543c610b00e03044071104004096120303900100f2507a8910702414010010010801c1142c010b03140312001c0d032082452904130341042001001c165003000308680b540c0d200144400c02108881c410301030903d44880002c04400000c61080d5141c9540c0c9040007012801c6d28150602007050150781c000503c0344030500702210300d00c5914081c0000d600718141c0d0049500410307041480d03002c1d009031499449030a0440d003016040c3c45090354040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 629130584 1250 629129334 629129339
    0xe0a0c0e240a0b0c0316080d06120b01050907112d0a03080f06131d1e0606060a090e07120b01050705060f1503070605070218090307080a050d0f0b0406 66
    0x444403005078072490395000c020054140803003441d0382c001e0140d1a41d104101d90612a1800c454011034200301c0c000d0b02c008038041601f0704403040c103000709005084011002421780310f0503615040000c0e0b060103514460070340400001c803181d1007044409007074042c0074101d450030348241c0e00030522542c04141c0701e0100050600c101c042c5110000d00210312690603030310311446d035480007080700c1e400c80301030819940324800004078000342c880ca015150300360705c0d008600d92440d010b41c90110b180030000c0c0781030b00074004000055070909401140e500d51000040e103082c2d540c0c43c0032040444129102e40c100070b504407088030602c540303590b0290105208420001e000c000e800c56520065a59001d00c0f900100243c1c401000101070386103103003205400c0b2440080040e000c0008030300107410b140c0d660b00700c80001040441c000065103044011103801d22814038034422181025240c0c00e0b140d104008010389a01c0b00004c50094051040b0201c1c1e10213001101c041085c1649903003081d001d0008141d202e4815407c04802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 629131834 1250 629130584 629130631
    0x6090210020d0507031d04090302030d1d0c060c0a05030a09030b0a090b01060c11061c05100b040509070c0203070b070623070c0624151407060e0a0c0e 66
    0x24003422900b96254241451210343d4200c4510900400d0f426034620086034a0040d42c865003d0310040900c66005181c0b600d102d0031209084403054140d80e4003000c00c400ea840e42c6c80001090900385848291403a80d44d4802c461441864041c2e1074500a03c00c0c40000307005191075070300c0074000003a20f20900b0042d00b242c03121141001604c0103000094001c20143e0010060b10f40203140000c8520300c103401c404002c404030301c001040c50f086810f0504c96002400c06050310040e4500c0780036071000c003101003582f0b000d080480d0104a80914021240515549008680180c0c041c0b0400c105180d4028100c3e8407150b155070340f402c0343c5d8002003005c89a081c10149040d070b01c443c2c904650bd1581d6191529161280d5a40300120342c0c40c0d0031001d054504948c0e80303800c601d2591942803100c000610740f855440032103242800c01090700001400003801c0280811034001d041441d9411240029000a0046241c2d80c07908101030030480685130080c0b8400700480d0001c3c0d00700f4102c00c0c251140000c2c205058110070754240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 629133084 1250 629131834 629131843
    0x901090803031e060d0b091b0111030f070c090e150a02031509060d050105090703231203040606080d0f03060611030730030603060605040902060909060402090d0609021002 75
    0x40c002d41c6040b092410408504041d010903900050080c094910b2105c07a8490840003101901c00001d150400e030300c08c50650301045580c1c031002100380380c0039012286401c00c1c43d40b6400313446404022250005040003e00c03110b103c1d800060124003208000384503032008103503902c0c100308204a55029180000407a564054401d980c4203030701126201c00002c05200c200401c0c694014840c0343c0c8500e000c0d02803030120b802403040900c281d070b11200814196043d070404542c9952840c10340d80c4140c0140245626040d40468400610313034480440a0300d9440d00e00d003110240c50943c0003036420b0710502782c40b07102181d4445013100400202d500c0400c06136480d61001c0722031001c0e002e5400c08989c810031440001a041d0440d0050303c035400303841541c280144040702d00345140c03421000c2000a0701c4a07810700c1400751500c5940300400003114200601da0b4541d0101d00240100501035114100080008125850f550103c405080c0010100c080401e69464000c0082403d6003041c4c4c0030700c03030038800b2413441c500028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 629134334 1250 629133084 629133091
    0x609020414011215090902090609010609060c050a020d030309170f0a11100e060708012102061305040f150803042d030c090903031b0e060a05040f0b090109080303 71
    0x46181007004060010f45250320b076504101c140030b0f034a4020a41c88a2490344000140981c010003081c0710249004100d1400009082c7d2841081030704010410280c2096104003242e580b401c0c251030108a03420310034140000010084e40103d174103080c903001c2643c5075200d0790759280b0642c6100415841107140321198010707144480c2900004121101c0d103d8003030343c00343c1c0015909600f1200c050201d40250700c252528401002215446842400303050b9402060160250540b00c0800c0c40d48486040350414654290802034050b007400070385480e503180680740b841c000d44006841800880c1e00e00e4171020052980fa5020100c0c0d40710502d01041d490750200880c0c040307900440401c1c0211403100030204240390441c411410120315030344000300060305018068010305001400141b50f840c0360401406981c0000841c51601035601e13110741400e0382003181d008a40c403064a1003034a405002c1000d4405102e6600f00b03010200c40e0f01800282016007400825001100381e998101c42991240502d031b4030302068 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 629135584 1250 629134334 629134349
    0x40c0f0509011b02030d03140906240102100e07060207060206060d061d1009031116091505150405010e151602010c2103150f090e010605060c030a0306090204 69
    0x1040307204201d42c407072880c0184012200011400100e1198000303071900d00f840072100042034841c0081a8142c80200107076501c4411080035288524002e01080800c1303118050b04001c86c101010040340701d0b4030801c100c0162038082007080001070320302820355585400511a480040c400da44011030700300c3c4089611801640050050308090016a8401029000210f0300f0a43c001001590013401c3e03130700f00242003203540e44040000e005002420010008007510700396001c5540100309064060385080b410804480c402680090709500e03a0382940001103040d40483d611207407030b1070380d2210081000c008004584091302d6001d045c10010307050140440004d031000b43c56031414845001403e0b0f080e906080380a10524003907490b21081d644502002182d640401c036403d541d0f059101c2c40b070340c252003010360354000391881040480c6803003540c201042450203a8100103490307220004042c8001d40110300584002003c55490307410700c0e80296501c0c0c0041300c4103030001f414003e000070a01c080d88211015034050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 629136690 1106 629135584 629135587
    0x5150613030312020918040510140f1008060a0903260a0f020306030c0f0d120f020d0e150306030c12010903020106080d08041205070b01060806040c0f05 67
    0x84016503003c89204100c5030076070740c0d0764400e00d8095141820001c5032694407450311500305200c105142c0c85150602a045280300140b08041e84100c40d0342d0005038090341c0d00d5610458000507445649400d80040020070b80c0b1440b160000300301c2c2d81c001d0400c0e514001503207081c040303082981402e4154010015042c040003e125000d413051203280800103604500f003840c000307501c511001042922039a0411804405a02c0d00000c1ca000f0680001d81e03079046805a0700c001e08503a1100c40e0030740041c011032100c1c0d0340c3c07180143d004002400000d050001c6522440310400c1196002030500c590601c102070a203003840d42d030710003a0300c1c0390188880040303a11809481e000c0d0070745240e030308420700c0c1741c001381c66440c51182d00a914540c042d8020300360070581d400c500400d640d548505040500a90192000401c0040d001603030540208001c2d502000b140102e07a104036984042c902100d000100d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 628956834 629136690 := by
  have h0 := BRFrame.cov_init 628956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 628956834 ≤ n) (h2 : n < 629136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
