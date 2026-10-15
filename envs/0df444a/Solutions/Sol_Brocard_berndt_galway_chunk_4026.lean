-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:05.773227+00:00
-- url     : https://prove2.me/submissions/ac70be71-36e2-4445-a11e-6ec5622bc7d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 723920863 ≤ n < 724100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 723922113 1250 723920863 723920893
    0xc15130f0e16201f05070509060a02030405030307150c0c1e0c03020d061d0304030807112215060e1e13140601081e0408030601051308070e07051204170408 68
    0x12080b00564100e068001c0c4911410300046030002c445c001b000c107505100c0001507060600140c6900080d0380122494251a60700081c910340003900e0480f0030440f0a04c0510303c801042c0a003540280c0d09040120002c000740d951080c100b078030402d01036040c800e182011420300c05401e90000003190094803200c1903000b14284040901040704007040196404c94510802c10000002c9a0031a90003c0320319050510503956084020818120a03601000419048800407564202040802034000b1b00107503446000045011403090b07503221f9028030014400703c900586075a0f1000010524030010b100035491a480000c210543d40002e0025251074901141e204078902e1303414a00540313090b26000810f50703030b4004a00c0e84525180300000f52003040c2010500280681c0d001c0c40e0000414103115041010300151820481d03803581c4a40020b030311264003048645558900f0360b40050341440c100d0700e050780e105040001d08030050801000d480210000d8030343c40c030280c400d0701d01400306c1c603040c3c3d5400401c40e289 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 723923363 1250 723922113 723922123
    0x15080d0206060109030302030405011404211502120f091f1a060306061909080318090105060306060f21010909050c10021203090c15130f0e1620 63
    0x6400094030031100851841c0d03025846180440364075500461a16091034011a001504443d000050322000d1101042c640542052500c68000340c0450380e2040b241030408600f17841450b419034001d984100030315650030036450b1410358000c40e01c0d02420115240c40390800e240c00117509484a2060118140c0100d40246e50056a0480a1105001d4000340c0040400a0609c826150b042d8040e40800950107010301404100c1c402421a0400508095450304020700f103031b00c038050200c1c41601000c40f10989140c60b2a5060161101780c2d0342c03900354600800800ca0b90f120b102c0c1704d0b00c908000410f040300e001e8080c02450040c00c80e001c1030000103503558091100506038028003150580642810740010307081010042d01c0c160b83c0381d40203041c035845c075074401c2c040741d4070241000c4a40c0c06546001c1c1000c0d120941440320580740015020f47d04d0760039030320142050b0b01c15007100c0f55a00c09010100f0145a0300182c20340c0000920b0301c00d05081e42c3c400029184600540f01c02030300e1100c1c0010b9840d0701280418 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723924613 1250 723923363 723923383
    0x3040b03130b010603060e04030f170702030a03050c040f0324090b060f120705041d060c0309071202010e270c040503160e0f040507030501140403270603020c011508 72
    0x9400b1407180d80720841a42507074283d000340d4034089103484c002804603214001c0802081c007682401f2002d1072203407226403007000080f2281d00c05640002a80800ba50f4188183c5030700c02401b91415040a041c010403140500842c44007070414900e00301d58021032900d010710340d2000c0c0419001080411079618103c0001801124003c1c45401320311529005070034082990060300250a000c2e0040c1400d0504100003030074041001c07410481a09908125940100f00444c0a621080701080d00d81c0b0b8811401c501d000307826049924012003030400b0300c0040c1d030042e1010024080071101040305ca14481608201010850072210420005000b40000020100010b2098039015800d4582c40d1849011050103c5403d1050b0340008410500140040c5d16261720290040d2086060303607451943c94488500f91100c0048602c80c1540c40807c0c40308042e00220050501e00b1640b10408801c56440711901100546200c1d64081c1600001c2601040b0385c21b40c820702d01e50b41060b18010680c0e4481048603941d1407194 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 723925863 1250 723924613 723924623
    0x30415020c01030b01231803010519060f060f1211130f05060408070e0403020c0d350a0e062203350d0216030203090a060801080a06090503040b0313 65
    0x40e20030401175118501e0a1680c0358801c0c110404c1401c040000303903803a8002059214a82c12210102106503001c4c024107000f140c40001509112a0546c000e0040700c030301e980b22002000c600c030800c101d0180c01c014800c119500300e08042c0034210011005001a05009040e01c08003000018000060700030600080d0544102090568100d034456051000074403641c06414001c2c1d00411041120701514400158440e1080c03040d20b0410002c000401d0900c0100b5404880e19010010f41e03103905031404003501c0058283c00d02102001e020f4012400061068060010401070050b08000c9103031180c104840c0c050142022200c502c0c258400f45414201040c003041710780750009401341e40708413a0030850080742001c0d4031141104084400ba024170a40c00f0b0f006200701c198090264803008040c40d00b5107450f441c017a4000d10750b90300210040120505c000d410410074004044010f000d081c41c0062412032a60784480e000134000c1c000d080c070f0381c0346001d80e6001d40c090642c000b08010019890405403032aa03803103a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 723927113 1250 723925863 723925871
    0x20717041212110c0f030a020a081c080c03070804050a0212150603070b040e071101021606230c0702060f0408070602120a050f0702040b040c031506080405030406030e030415020c0103 80
    0x1028040302e110b0a01000e0496942c1315140030b580c42c5ca4107109400f00c0d950028229603c0704031580c00710342196000c1d408040950451071075444500e03060031364a00c4848561820391507034903040c00754118a0102400310010000d65400040401404002d5548000c1c1c00411606410351002c0c0400d580d0488101c03c0204142500b011411074100000e4480c180c1e04c100e1401410300b41499a80301c600c1500502440801031005e5803020480000e1000307128001c2025105140c03034001e8240341060f00e10045200304005071090890000106483c00c1940000940049a81d29143d40c000507996024a803240200003030f0000300091103020019050b401c0301c0b0302e0f8090755072110414086040701d015600e62440840c104004132400c214205000780501d5100410006444070102d0210f411280c01100d980c010940e02e031541c80d503105513100741100910741454250040d2406554007a124026440350105044e11100740f592041c03018002c2d40c0c0503100d103404000d000c804140e0001d50310005010038a01003031030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 723928363 1250 723927113 723927143
    0x9030406090e060a031b0b0d05041218180207050106080c0a17150402041e0902040b0307230a0e0f0709060f050a0f1413170a030c03030207170412 64
    0x8401c400c1c034410b03c00140310030422880c64a840b0541181a143d401d003481303100e84080341005047d4041c00d5402d010000000385464a46081c48601c41c00112440501c4482000d9903058200343c40c0000a0380c1021081e5910690070b070b074410010f8010000300030843d50811002160342c901c0007070b1544651f5012201c0c58812903440b8200000300510340003ea505400c0001d00c0725590410b10300c1190464409031001801d66800b00e105c80c518150304000c12065500c03200005e05602d007a0140c01c21030201100070303001c07003450490041100c2d030b80d4800003910381c201c05045200903603d05140300c2c010045022281c409250030708940d0400303041103400340c1c0410074488000c00c0e0b2500c102d070314010900c07450f29103030b15000d03601006580320720282414104001c0b0f150505040b122148001c0c118086aaa14085840c0d003004030301d072802650015808d100d035000042c29070110358006000c150040c0c141c280181e0321180c0b03060800c01020510302a0502c1280002c0019030104d840c01014402800707914003500a6039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 723929613 1250 723928363 723928379
    0xb0105090a0b0d0c08061c0510060305060702010c0f0e01122715020a090501080a110f040801110307360605030a0b01021f1a040c03060807060c0209011511060903040609 74
    0x174003070322655006510141c81d030400d0f2400da6546101b0341d005a04558014144511040582d00c031604102c07519004a4103019025809020714807c0f000c95080280320748184540003440e2100c800c24560400c0010221a07803501040c9d407000d02d844560010107060113185c806c09558a500d85101280c08080c1c0c091200022000c510030388034100003584e00d0b0403489190400440b600c00c0b0190202c10400d58414610711001944c500403c034030600c45150369203440c50105801d0840300300603600301007040c00b0420800304da0b41c40106801096400746070107051b050780c001e5050100c08110404000d0807900b1a001c5503072500130015503c0b079036030000244155404440120b0f05c8000c4a04140c0c0141d6080b080350b048510260003801000300416610305031900840c0003d0251411181d030440440e549000c144280c0500b407050002404903418801400c1e1080c1c0d004c01c408540c140b0525500e20001c005284c04180702d010381c0c0b0105408881210564288050f60a40b039038010b10428011801038107001079089 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 723930863 1250 723929613 723929627
    0x1e0315080a02090c160201031a09040b010f05060705030910140a0302070c050301140a1a0411040302270417120a14330114030906090d08190b0105090a0b0d0c 69
    0x105c000c15240100300c0754019006004c4e02d0801e001910340966096060f6142c140700c0c0ba214a01440e034003c01545800ca001a07030307200d240c00c0303203004180810a20000c83c03c000100c072202d03001698000c00c0050100700484007040c0d9200f82d01c07000840080c4040c2c0a03981a0050201240910303107940c141d07a42c407010142200e54043c50055041900000107204c0b9a040c0e00120441108101c034550395030300e40c8005011224120603c802c1d54502203014000d60810182201e000900c1c805108807d146010f1010003603100108024006010340d170700d11081032130301c00035910214004602c01403641000d941030806400e0381000410100d000c440025407000010f4400150b400b10210b00ca50641b2058102440e18564507034118184408030794201d004a04d854000c40c410589031002d03151900700301031183e080000c02c562000800200da0140106451000301030030011007114030000c0c8289010005948a00502d1b000582c03120440000140102c0c2180080c0484602100e0030000c00081200564a503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 723932113 1250 723930863 723930877
    0x150901021219270303210506010207031119080105190c09060503040204061a0c0f010c05030f0901060801020d09022704080d14071d010f1e0315080a02090c 68
    0x34000c0045000d00d0540284201c50081c50340e8000c1400307183c5245280b9442c00c00381d900441c0090340c820b9161205c0c20300818001580844542c090080d07081c841e0000355108090300014000c91800e492101031680c0301c14840524201741d205c1c04051f030f945c2e901c0850003408202c90390b44816040c1000e5001505140c450f928120100341c0381c0c02504d0303041a0048a0503000100b040340c009031303220f0011801d030111603540941c50098851a650316482d2441241c1000c07084170304070101d0781c1001c4500741120381090659a02c00b4115a20440e1580c85003401409010181e1010400354400110403600c00c3d50340d002922003034000d44140724107140070350182581c048510b00b202030603658200800c00042d2100010309001b031891034082010100c82440d0612110207940e07160100d060b802c2c0340c0840c0c0900015031443d450090030104048031072100050803081c0c1e900752115441040040c84c2c940503001e540900c45018a0001020105454400065455240081c10780c031800d0700300c0000756031094007002c981039 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 723933363 1250 723932113 723932137
    0x5180f07030f0e01090c030318080c0904030219032c0f040209280e0f0f07050c12070812060910060c0f0b090109060b04090816050c1509010212 63
    0x240380d03a9200114000c01c4000c4820312440d885112101110009000d02e03000d10740100c6681011524514001d42a80040c0e90079454001060380d04001c1d414000c6180c642c1108180c80c0002143e9592408030708058440d039100722103154a80c0303079000345039002c1084c52444101a0104884205001d07030401c0c0711040401c0e41d0b5205504040c81d10241c2041e401416080c0000760200b400400007030a1401c088413001100c01d03500020b44030030418119420003070394014898481c9481c00303040a4144405d901c6000300030200b030180000d007249201030f08101d2050b0100308a052151195614030b0041e025134041b43c522181c0321510f10203d402c038500081b442e40100e1448000ca20b869203418402d48d1009c1e9502d4064441d241d03018002c0c800301b1120740d000c910a03030042000140090741854200f013222501488075014500c0e0042140c00a018881101c003410710380401114032201c02d241552074010303007074030160700041d88485150044000c500505203001c826001c0e5219401c0c01c40001080303018090080d85 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 723934613 1250 723933363 723933391
    0x30b0f0906060f1b0d20150916180b0a080607121b051e03060d3206150f0928020a0207032015030c0705070e010518 51
    0x507042c40c1c2030008007100e6803500462801e241c1081841c4844600000e900303902c0d600a42d0725615401da0241e08003542d00140d80d050201e940140105a5442c0d40c0a0f48100c0c07403a00010104039910300810034001d001c03900c04040188561100b40080340340306260a01e107049800d2038020300350751800303022181c2545c2004004041940e2075050845000c405041d102c00075650704c40b2060718200c1c0c050030902c070510380c07504c0e659560b2803e241520707101500500110340c0303040148203100450f42c0fa4040003c0320350b00200740801c8043c071103999010041c805000c104002403c030000804822012600034404c1c0040c440140603803d01400f4052800e03613405400b90300846400014a014842e20400c0300e245080b40300d02c0460320b104040c01070403a0721048100000d68400c079005c0081100c00e50420316000d1301c803c41700a1418410002c20441181c41c181c4407142c80b00031002528042d045030035501040d82203000c4510380c5035100c0003049607250030b000d054060400c0c96419103d458160b00c096001f40c50000345d00b0b03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 723935863 1250 723934613 723934621
    0x1060503131b0b0919150e040e060f180705010c03030f0902120105010f06090b0711060d06090c030e03120f15030a061505030a1e0305040b0d06030201030b0f09 70
    0x181e0312040c004812551150210842016500e541d0714840c0541009480903544140c81c104002c200c4003103040b00c910511080d6824031103c1015042d000640c040e44c2041d888080d55880040c0260181447e0744005201706010001400c40411103d40650801d09091000394000b81200d0344584071070203018041500250f00c200068030030340c0300c0040014520800141070540d9070000320400113a559260032a0744036801131111703400480c0094028500350030036804003840c20340740c024240a0420060f10280707801500c240c03075440744801c45010058045c02085034580315206c200080401c90400c40c0020315100480d00071190010848800c42021034890200d50b862800000d02c1c180010901ca00396140829401f040e910b0400003081030364400c04010600503481103040d203007032109503c500d2003035200300c906d2030100d0200e18410300700d4030044410000c80d10311802c096945100320343c002449a0400521803620301140d504c5003058130300c00d07a01480141c96240401500003045150700d948501c0800102e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 723937113 1250 723935863 723935881
    0x190e011505010f0c0807060912020c043b070b0a0f170621191a06010207050a091107020a080a0203010f020f0a0518060a0c050d03090b0a05040c0e07210501060503 71
    0x30703200e00d0f1f10800d8081141101640c0c1e004845130f4090b810301c0981d00485120307074989003c1c01141c1c066400190f00e201c61800c900d41d100c00d50000180070002c01c400003d41101005410300101014100150182eaa00e40304840020001c0c3c585050010000d0403500b18030f283d40c40142481400380710000c0c03842d480e8041c100814103d6103100c6400e00d20368491100031410080361540c103102c58500071030311540d26502203d03e6904810b0024216411500248028007544d61280d03501c1b02a00c200030b1002454240d01409550344e8801d13024040d5001d18034400000310310740000b4452601034400c1d0028481d800b00c414182003603001d1a00c0850601109210611205101340c1c09403050703506030110003902c18061800700c0c0781c0350700c040240c0d00040e01c0c40e1050424070008000d0440c1c500c1c09480d00300010042929074401036400a08920051030700d590114050003a6011020040c0114500005042c10008409801e81800080c6100d00c40039040c0d1000103682c807841070303074121109603c600345142e40303002c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 723938363 1250 723937113 723937117
    0xd09050d11041401060509040e0d020d05130e010f1502060c09060f0409050112020916021903052101080f070810050c0421111215190e011505010f0c08 66
    0x26950415030324082040f501c0c6441a096009000c1d41d00d405950398004424801591480c200c0b1071032980c03018030440011580007402568483d0607103803c54980c0f0485600c0480500c44c0d522408910f0240c2c1d0001c01c5c40040203e1900032a91501c0d4540c0c80007400c04810790f00e61350201e91005501c0303170034003016040741400001440d0740968602510301e41a12040c0034800c88900307030024066003180a0145003141010028140c02c081ca034842c1c0d881042d12404000d40d07d00780700700c1ca48001c03010555404101405201a500c0c0544240718601d032107094466811f261007800d20404580340704258034042c40c8480800c1000a960903a005000d040340b40f0180400030703041c068081243c4036000c00000403010401142c2110000080480c0c0400d02c210b800c10f110001c5402032031520491400703a81000390a40014041440030003c04540c480380d4030204440b10404005c0050b985940c10200d070402c1c1c183e41944500c6400100c080780070f9000c1d031903400448078103040760001c80114003c0c0384a10f01113814440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 723939613 1250 723938363 723938393
    0x906010f2304050405010305010903080f04170702130203070314150105070b0603071a07150516030e011e091a04120c0c050a03061d0f0d0e0d0b0f04050d09050d 70
    0x81924500b50fa5a00498101c0303009030300c2504c07503964032244c0000301a8003101c095009102007c00e1030050405032144000301504051003803100200046410440d1220b26442c9601c002c0d001c41151289012030300900601030f0058020041c250300320001c0e4124103031002d2040d0320081070b503030700e410510583e840c1d006550700034084035450305c100040058620401d181409250f10300d54502078440b0641c0c6080000d55102c0b000c10000300c1d0800301007001c0350a28540c0c84c4158103081ca004140c0101a010040c01040210314006c4071040380740f07010118880030740140d01550b105890380303a14000b01d0701028544071416140240000e070b4202204110038401e0303580c2c1d08034500070201c0200d1155590300050601c0c1e01030b0320407a0602c0e1038000c0348035490421410003c01441e00f4000d052070051070b0340c45945a4a0f079000768000e100c0ba50540781d00340c1d1151410b44240315031151f12070701d403800c203440444091101103600f240e141c8951485650814070910005c8100c4101510310a0940d0084d82e4803110048201c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 723940863 1250 723939613 723939677
    0x7050322050f030f12060604050d0b04110613030512070b070c08040504140f1b0a03020f040f0f230102062e0b0903010e030301050f010c0f050f0c0906010f 68
    0x86202c9003426040c0001c01025101050741070383c0c2c0100d40c5111176050b8000b0809889030710180302c00c0107282c07680308080042a61000020090740c1d900d1603c005816422008141c0200d4086030414a000d4103880103401d4a0180c42100c940c0008243c0d8900c032032040360710040c82e1500760b41c0455240342c02540d0102c640f40c071840c0d0346800c1540b0b5101160844101400d100c004081d10410300100113001c2100c40c0c1c201d1098551781e8406801d2040c007041c50b108050004007015800914014403101d00e5040e41d0140482200b80c40d0f032700f5641c605400c1021603e000300c069401201c4c0051a5051521407030056010b0103030050f10040d61162030112101c1c0003100000b0b0710b0341d007001c0b506c2c07643d1030701440440242100040380758039400f40c0c0040c1404c42da80c64403d21410761007040148000d5890841070980305009280c091540a0549803030b0b110a4104900142140301b50502c0b0760080c48007080800e413402054664100d15941c0c0310045408146416945020032098000000b0032001e940e28a0b5440c8056 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 723942113 1250 723940863 723940873
    0x80403080c070b0c03030a0608061b030709090e0708161a07060b0306040b10050109030809061e0304051f060e0403030b1f121b050d090201021c0c05060705032205 71
    0x80d20044100d138070580301071416410000402c8444000ca100e03040180154100404031450040c040150f42848108412400003011000800140c4600d0321030001d4180030300284903020390046843e54900b21800340f05c0d80f501491202108146024005104440490580030150101c40170410350b00e44c01080d05503503042d216908064036803801c02165010340d1082c9142085894500c02c034908104090300418104184004200701003040072050340c800071803ca81c026031310500340000401c0342101c48505038680d00088200014032402080e41004422030341c10030300300400700b008820201e6409004d0380240130400c4000c98040380c401e03806044550030141213601405905011400d880700070011205c00030743e6105c13880c00100301c1401080003140707200030302c10308034000c424000d006402520800300d44590303910030480c00d583c806c0181048020003501c04102c00c540c059002464044484030654446c42500c0101c0c075804d10841c1220b00c202d180540500d03140c6001c0b4101c040d4541608000d94040c41a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 723943363 1250 723942113 723942119
    0x50621160905130b0c0f0c1c0f021e0c04060315050c04151d0a15030e0d090b0d0207120305160e03120702130e0c1c0b070809030d050414070f03080403080c07 69
    0x6c540200382c1c1c10f8804000700542400300c0f0000250070485961a010880c0080d000c17040c590b00086d000390240180d507826440008108825850320b0b600038100303907105080090000a000c41c80c0c4441024070401d000c14055569100c00c240d450340704a228011110121019900c092442101d089a0f03454104070006a5000c00900191441e18940c00403130601c0e0240f0501807007030f5094410000005420409041564031382c141c050060b620a00c035801c500f4400050740c2d04084240d5044031807541c0e00400e0347d403103004c0d80c00004000342300460f1503007902e80300481b20b01c0c1518055034240e082c2001c01030060181904030005480c0030382044c10704981011681c084140510498003e0014502200c0000c240e2107454804202c03e8841740112480500e201003a40000f0a400d2420f1982c460040d0620f054151101d40d09117185208600d00c6100440c5000c085c0810854941c0c00310304078901c403a003100c00903501d500200300741d1900d0348801005040d0400c01040010021006030198049560a981c100b0350b0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 723944613 1250 723943363 723943387
    0x150301170601063f0f0609050c04060c021207030c0513020c0d0e0414130c2306030c160c0503120a0c0f02040213090506040c050c0c04050621160905130b0c 68
    0x84014070b042c0d01c4c0740c0721620b0342000d00c041e00c10300d801003a0001080c4054200700c2c076103004610440c0200d00402003180754600a5450724008243d08801d08001c560b003241d500d0824030552002400303400d01c203c444490521488100d4001d40300400e6022026003038030100a681070710134510446515802c075403540e00014406000f40ea07410321441c0c449206080303100113841c001100c3c0c40160041604040d1100020420421149a0f0340261070183c0c0d041e50390f43c46400c003400703080c05000000705220b03500a13810340410245600070380813034105601f142d0f100c2c0f0394407032025401d014540f842c00c0003850202501c00812000d101400c2c45a00150005281601c01884a604011650040b4412a4594003400040c0c14140f280141e0740c1440d20740700f0f052aa0701900e40d6120400240761501c00c58403000868940d60ba40765030a200e8012040360b03442c2004500c284261984160512905024948030300014083c0050088034803031800b202c1008000074003030b680c0508500f8098070054420009000d1580420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 723945863 1250 723944613 723944717
    0xd030b0118030309150c0305220f0803070308240d2108010609050f06030a1521031e0f081803071a100302061e070215030117060106 58
    0x15003ea5a603034500c50500c5480d1000c03d0307403501405c2c00c0206d030140d401c000c241d010b41942c10300c07480d20310390040c01001f0703034001c200e0004650000846045801e0000810700303000401810a64801d80350a2125519146079481c4e182a50300140c10000c900d020580c2c66103040d1404000c0036100380078411801c0e280d0f034800d880080b030784034110300030a501074014000c9942246d00400203020480d68004d10406030340100382c19000c0900514141c584420313031b40c0890310707801140b80c014140d01c03400300c403650641e089018525001501c06602003195080b08c000c81c200d440e07500001091003901e900701078100d800002c807180100207240c2038a15190030f0505800440c144018100d140c02203420f0404009201d503690206000586180c92403140c0240810050300d412090312070890300b030b858200192106030150000f52064200003984007801342000702d03106d14550051810303038011100f0000043c1c070b0589441c0da0344000317001d04004542803039a0051422155920440d956400c07088030784803202c0100300d015050b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 723947113 1250 723945863 723945869
    0x3151008150408040909081902010b01030b030a0b06011808060f0406051f06050c070b0d0603140f0312060d0b0f1f06140d0908070b100e07020d030b0118 67
    0x868420004010503401081a4924224400182001414295500020307407149110f000b0b442500d603c282406c0c00003071020b6941c0e8014050000c0c2c102152098020300078000d254403103000c43d00d000e103203111034200001c036004017551082c9a410103880c0da00054544000c0079080d080305003001000031404140520407103000e0b520050b002d02941c2006c1ca005420f803803008010214001004000e01003465851111608a4803507041003a903416003c0021410014507802001e900f03031001802d131100e034100342d01c50030890b802048040d6100895108042d103408044a90100650003070100300300a50311100300940059004100d40e0012820303a032445101d54048800080380da0102003040001d5403607444c00440d6400e440080c1e150641840d03005849600803071342841104001040766001004c1035441126082d07000f010b890780b296028600070b50095402c8541032203008660000003005a103607501640940784a03000b070300c14850035050840003041c4092007141045a20400c42c2c000b403440194040103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 723948363 1250 723947113 723947131
    0x23060a03021c0b010c0212030f0a0c02040b040b1e0d021201090b07020115060305090f0303160e1504050933010311030106090e090304050303040914070c0b01090b0315 73
    0x40e010082c0500300c0609022048200941c02d02c0b00380301203680d0111003020040e03411130742d500d082080341c5209480d5000304101ca404210002807140c00440d080750050603c00d100b2101881560040004e0109070b9050b55981c1d80c0003d9051506100f00303010521910138a42e0107018004242030329000204400341c18034912070907954401d01e1100744a4011242c41d40504140001d00100901a88a88500c48503206480401d42c0e01d02c0850743c0e0001c103100d003006081442d03048a0722810501c1d082d0010ba140801c0d47e00210754009941d030b40f07a0604086407441100c0f40850f0b01d0505181400740582d00c54010302c1d0341c216120420410789888000014414041d52003e00f1190203804140007404a0717604103c5d6258642080c170040056030f9104014170240c540200e04d614240c0c5584480303524501980d0025035241c000480c0c00b25015009074000720f51b0b541c200c0c000700c103640c907070040c15a00103484000c050060b100b44401030210075580d400c02014040040d08440c0340901d0008120300340241900d00c5d80c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 723949613 1250 723948363 723948367
    0x30a0f110301031a01030503031303020304080a120f0f050313030c061a0310020c060a02070f120f0e060c070e0705090d14070b0a1d011b1a07020a0b0123060a0302 71
    0xc24801002e45250012540504c6a0030550543e00c64644e030f404001d08080070b03041c0607180d107020513100380183c0340286445021103c414001c0d1521a543d01c15070707a07440000a0000407818a034501c52000104503000d40d03203549282d0340303590520300d1400f103031413030194140600c203419440081c04501c40c19010114201c1c0c8106418000c40c1054104002100f400301c400d0f005106901c901540818102c2c0c00008a64005a03952003c0c5041c110728060712038007031701ca81c0c40c0e23110400c0722613081100ca8291725400c0c0d464002c0000d00704200305584c0210341c4075a11a60007a2414800c2c85078841c3d2a5422403004d00b4164200480c0000081c565140c0003001c444006006200c409110070030030810b0040c22007081c0c060f081404410000b428503411501e80c107070044e807440d03440c001c030b9014814902104d1518025040c001001c1c1c10182964044184802c58412410780011a1180701003170900103103501030f60000203030741f80095000c0c1202081141c40000034041c0403480320755440e64014400c1a801d5203000da = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 723950863 1250 723949613 723949619
    0x90109020a0503070602060105040216050d0302181e041a150405040608060705030a05060105042c10081522050a110409020d031116060306240206010506030a0f110301 73
    0x4030001c5001d0340014040d42c08400c2c14004580c0200c1c0b0f65064a20640300180c40e0500d046120120640f1003a014009000e800e46604102d540764004101045444c031400400031600750030700045040680d180326403000800700701101c62400c2d0700910194001104281c1d036051003000010a00c103021100c05e091007000042c200a103040a0185400810701f04018100b2442c00510260140c4001081000210f40d01c2e0700166103a8082c100f91005012000040d8442c0c110206580d0076030255403011140d0384080c040052100355841c01c207201a2070302500a0045a07051040c41d8503090b2000e0440c2942c3d014051107124012a10410034800034001c2d00200807141032400c052203600c2112050764021402d12094070b025031620030303000108903070501c0d0402d64001945007407030070520b40c00d90318070a034014030000050f0140c1c15085a0142c80c10100761000d507100807903802d183c1240030340745100907820480040bc910310300b840c06141d01c00780c84980850850004840d450441e100021003065100000c030040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 723952113 1250 723950863 723950869
    0x31817030706060e070804020112090b0f041b03021e0a0b0c0d14040f05010806040f050406020c01060501081311010203070507030516060219062304060204030215250204020c0609010902 81
    0x700c0f0042501c00c00e200068200301c400102000001000607040c4404500c640750901c405610460540380c010344c42400303c1c140800d86080480c400e03601500d1820f580030b58000328030010780003007049130340c000e040045064a81c82d1008480c030501c0d013070360740c404019000003c41d4002103004200e560003602c0584138000d40300f00c02a1141d000000043c01c1403c091105000f035001e1145181d0646100342040b1100c0e558080011300648140700d42325003c2401c1a007440200041c0343c0290003421060030080c0250341d140c1c801154500400c649a00c0c0568031410180c4c08103003c9902c08840326410700c1500d00d4104a0749409140c40b94651085810b43d024000881501c8510903240c0d024120610203818040415100c9040c50b010282000d40000d5550808120390880c4041c00c4050441e1140d00b400c5c0c6283c076040c044025002480107a000b90200d490845809030002d003100e2411391140b00050424607041041103185016010483c0c02c50b0b401c0050b415510001c001e087e02c11075540d0004241c00400b8418 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 723953363 1250 723952113 723952121
    0x30b09010e070f0b040e100503011a0405130b04060b0612040302030309150402281a120a0213090203310c080303100b0f07020a030308010e01080a080304031817030706 73
    0x80b1500039440c181070008807454130480b01150300c03924149000342c81d40c10b0160443c021b50382c405a4150318050701c185144103290f40314442a4000c940400c503c0c1d49000c820003101140c3c29000341900d424500003000520190704c401e4441030060030042c10111051001c88549809540a6000d41c1c001b00c02c00001800c1080781000e555114182107000b0b040550110303840f103404c1c468040c3c1e001003224002c0769072100c004401c030040441e1103843e400030f00e000c200c44902c0c1c0d0041c500303034015108a4000411005240c021140981c40d04045d20304a2490f040d00d00d0020340000d031000c0d0704004900c0d07002c2004a0321105103514907108044980341240c032803400d62004440f0b540849040d805c01d20800c01030000c00fa11510072191003d44031507880051048c3d00303a403441035203002036015017403860220a0545c061044c2d4180d81105c04845000d0340c88101c0c160f07441601c880300401c1401c003040000e000a208400021558a0010b0f56a41e06500d8000c600c1c40116482c90401540d400800e01000740310b46401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 723954613 1250 723953363 723953369
    0x60a05160f0807060b06041d1b040611010b0f180910050a0507081605031f050301060305011d01091101140702031b0418021509030312091b01020c180a06030b09010e07 73
    0x15006e46403d00e4030b1401c8030803558a16200700f04202a5001814076540e5004000010441c000c085603079135103442014204070034148042003250320f0050b804500c2e0078495115899010000d0503155240c07058007815400d858003c0c6130901500484c081c80c08903007480d000300750040326604400b24092505400003400d00307000038992400095504404442d040d0400c040366000035550804210b1031100d011850f04c110b43c00ea012640640c644000002803040650120380c804010b580c81849078051600e509003600c00c0720602400d030b904a00e108151940c000c0c0d48041c030400f041d502c806e00740000c5030000790034420101e01000491460340144601072a01c0c1c4580c05411802109107068201241c02107508030104a585604035003000400c8841568200240c40185a804900c050107150203001180c40d4030420f04c0d81c6000d01c18480700050a07600100c0d111100b0071003e007481038146a40d250602844801801000a841c0d841ca8080702184040d45418428010b1302c00116400054515081c42e102c40381d8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 723955863 1250 723954613 723954619
    0x170c010f03021611010504180605040c0512190e0d03052d040f03020a140c0315090c091503030406020a0b010905010609060815091501110309060a05160f0807060b 71
    0xf18a000c200034412154015000f00d00c0d186060001e200689142c8510f4000344540700070b5484030009000690860025504285c805009801c00c9400a480b6030040f43c040351000c2800700005181c440100400d0900340d0100007001c90b00607002c013491030a003c1e1071914040001e48031020007110303101031001c02c03102c45140c1800c0040d0440740c2960b442d0b01e60f80508020042b100441d418400d0510812020703202c03540007143c0441250442039455510254134008a009010303c01c07c4140075060000c07014032540c01d040182c032005c1141001c208014000502a41e074180c1308881c400495142000078001074035440d0010407841c00281000e6501e040c050344030f18600d50030308006024440d44420303e001165001d003002442a2512505000500b140c0310070960042c040104010042c621840182d4060b41d0a1f00e036074104201640440e6102d220343e01007260030820401120780e00c02e2041c001001702c0b000c4162000d0b042401b542d1a100701001c204001c0d0b4040c2408200740c001c2c040c1c58498075110340c81c11 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 723957113 1250 723955863 723955867
    0x706060510050d02130e0c0415020a1509170a02010212130c0320100f11010905120a110f030c0f03030108060417090a080d0e0f03150c04170c010f0302 66
    0x401c5009059200710011404925000b103a01e005210002d000b00c00540000c0100c41c1c59460103005455080d00548a2100e071000ba4440402240e40045a960081c80d040820114103940290038017002d40b2552104882c4a4000010404480c0c03070980546102041a400903a54100740c0624000101001e0802e840b8a10745044d0308002440d9444040c080300e03442904029001403000282c1c404005005909402c4030115014032030035030344130a1200c0c110700c20303490341e40e1036403071562a484c201ea918403001440d6038009510403644114600203040342440614000030190360314061282001404d030381d0701d0301c035510200d00c4400c01c04042c480b4411303504511740118115813522021766545d100150003c4c05185480907002c103852800c008481c0340b03250182001c0c0501d980d4803100359442b4540b44100000608007100d04000349006d00c1c000c000b030140140240400a180c484498900c1c00c044d180540348c002c100000245000c47c4055968099000c5000e08041c800090001d0010001450f140080600c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 723958363 1250 723957113 723957139
    0xf01090b01170a0e031c090c090e1b030309030712300f1b050d11030702010509120c15040f0b0c03031314010906050103060c110d0822030507060605 65
    0x528400d503102ca510500414508940b0b88132a046219040b0100514588041c0401d0703660314907004010040d20600190350b086030303038410b20001c0b521210380d41c85982d002040c1d000011a89080c0c54400c13090001e054078602405100000d241c03020310b03801000c030800b00e00c41c51001c0c404000c620644401b090301000581580c94203000b501c110783d5185500078003c2c040401c20301d480c8a609015000310b118200540c5c3c4c10103900381b65a031074200b82d119000180b1a05131005009401000303440780c20768180c4409041c42d00d0031080020b000c0c0030101a089600c100d008111072551b441c08065008035125060302d648034203280c0c1070005c01000e6040541d2540041012030701c8404c0000c1104d50244200c0d00c1611890001d141c640070304103003008051219070900b82e1103030038013a5950000341200c1c401c00d810045124903003c01da41e01c0c0010100650650802c2d8040365a039806184c441e43d2007003429100d0b00d0b800003c07600c006481d0614140a400052000c078414041040b1880785c00d025100450301e00d081084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 723959613 1250 723958363 723958397
    0x1c06060e0102061f090c0216080705010e0108040602091503040b0a020a0c020d060603171b070e01031514240f03030912011806020703120209060409020f070b0f01090b01 74
    0x880a052031615031004c0a01c000c1518203201c00b4006000e0464041c01240340c0140000d55812103170384e040003644617071800083c03210b50010f0720404650b4182c5566a1141030704005581d61280100309a6086400300416840c030386e10f0060b4280b0a4154070542c42d101c4c18a030603d051750010080c40c407160350740304020000307100780c010000070001076044446071488582c40c50218090a6035520080c441d214415403158182c034040d015085640c0c0005260b80c00d040100c190030b07039444841c802c2d956410b07075000050010038034800052101c42c20200000c80c21080750038400000035821618804102008900c1e460640c8501e5648401c03540203d07013074000c40700400006038491151007046132007500c1031135220349544400c0d0000000c3e03140c680010801a805800d01c2800b0794087c0d2011000111b40340707500801e220a0707109031400031b00c0107413000781454140100000290b01c800e030135652003038042c4030700800a00c0f03110890303214200c03000394241d0652500c5455030689003000045414460310300454280d041d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 723960863 1250 723959613 723959623
    0x70f140d02031906060f0e06071104051e070503041a0403090e06011b0506060301050f0121062405041a01020a0f020d02030a080c070905040809040903141c06060e0102 73
    0x5100031401a52600c034110b083c04145864502c4004090900e1800034804d500420465400843c58035409030b042c820b1810081c07180720f14100207054600d5045400c000307081985c4202d0303010540e0b041c045d03002150301c8c40b10603031806c003244c80d10000381d000410032041203460000c1c4007000a007014102e006040c1680d000c0c0030010340c1d00a1610400c81c142c0040e00d0b42e072144620400ca20707001c10050880a004c0c0c28000d840d12800c139001406903080c00c000c2a00c03800c0719419203040300c0703c100140008440291908550061030807095404580724204014140090400450071456840101d0140c514002c01d21007078444203221b80d00d69060000c04490280d0f0003044400041d644202020066a090f1000804130002d8481c01f03509849010120810403110780000c1c5001b00c00402243d0f0059501c07600802510b42c12200144440400e000450b510300f4240c00030240c40340710f0b090502a07030344004820700b81900010064070002d81c01505205903410701d8801d40d000b13804286402d101c15244100083d54030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 723962113 1250 723960863 723960877
    0x11150d063f0c0b0408010b03010e0f1c020a080d0c2703060b03070b03010e0f0f060f0108070e0909071a0414100306080d09050907080f0a110d14070f14 66
    0x32628001c05004008020000d00083d01e002003c01e0f071119240d070b030454020000000114002d40c40d11550100700840050056428110b80c8018904190480c0507101006c0c1c04c284841c042d442010045400a81d80001405111001460001e01540035031b4000b0903240759030b4451090305080d031408010b120140481174080d41d0b0001c002103901110180428074046090f8407000c0188408000803441d1090b440c0060300a030140101d080b002e1300d5000c0e0014000e0320540d00207034030001e1041050700365402543c030039902c4074041c1880c15040c3c41d400d010036440c880449240c6405e402000b030502424044801551555200c1602c040c14603081c00c0310018100f110301e45482c485c03040c101c51503030b1840c407a4000300c014100708400c0c0c034410880210003501c44d00d43ca00a00e0f2040c03107550001400184030700e264521401d100148003000c0d80380d80c20303400d0007016114403a09940d207042000700c0200182d030140e11180312407441814a00d00c1d021a0083c100848061800c0410448801440720340b24040191540 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 723963363 1250 723962113 723962219
    0x120b1c05060a1a041503020a030f020a0812090904060b0910090606140307030b0d05030d14010602010504020d080a020a0206161a1513060914010302240711150d06 71
    0x17000002e02e02d840603030300d040d5100075800100c01001000300004c98504a0f245442510407905058940c106940c940e0854018548100e6090040c90b1507440e01003402900a4042c0030300240346284400401d100c003904a40c0c03258009070003030040041c02c43e54400e00c2c005000c02e02d4140300041c083e002d00c8841c0d120203000c1c2c07004c2644031891441d040d0b13a010710042c10154028100d990712422201440c0c003905121810100d40c95a0000008515006016491090b9401080c0f0400e0300c580b41e81d0480c0e10b811480b0301c04118400c3c0ea0481b40140c40d182c0060613030100d21202062207201c01d01d89200c840c1088507103581c0025521003808070701114a69015680074084924a01c3e400810002000400442d07000d400580e003000c0d404495100c064a620707040e0381c001d80f4811003460104143c1210001c03441c40c2040110020011140400d043c00342c051850100105102901d21000745825071a070030030300c810130000b50f440004010074001c1060480f8206d0b45c0c000400280b1546214400c0040c01c4440070103d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 723964613 1250 723963363 723963371
    0x6010e07020327030322050312070b07080c0d0f0f1a0a060f12060306090203070e0c07020613120803090d170c0913020f0c120c060601120b1c05060a1a04 67
    0xf003260707070a1099482c1c40400c105080011001200c68610780d8980744101c41c003e01a400e4170312440e002003005c0300c201c1a00095155101d813610001240d00751801001c0521300102485400e507940304074000c96021507008480851500c6e0b640704071764101d8003038990704100420018290329580d01c0e00912401207402900300b11041841041d410fa864048400380b10021610b04600801088003940c411888240284d040710b80c8192180f400c208903c100b0b841c540c4108205021450052400c0c03070041001035442001064070035a10b141009905060707040840e0350410201c10044135010801940d13105013107504d054a80e00d0f82e820100203e0700c4010705041c1e4400300c00145048a9142c3d40c4c00f100868600d400d0443d030b10310842030340d0300d21504119480035031801100d402c3e0024003560030541d000301e00c4043c06441a40c4034040192418071010740840c92468803002c030001d1587d01c0c1c4100540e5400d1941c00c00000011520300b140c24503c0060000600510702003e01107220f15540c0000e030b00c0942078500203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 723965863 1250 723964613 723964687
    0x4062301081503330603070909050106030c0303090305120708030601050703030b100302030106020d1103041418040b0106080708070e010f020f011109032103040f080c0a0506010e070203 81
    0x81500c81c406403060b41621809020100c2c0c4c4500e403000c881507021440800415a400c0d16104c0c2042a0545401c1e41c1a4400103044c0f000c0c5e41d041d800005810b125500000d0800e0b902d5580902d600440c7d0b2060340800c0d19484200305100d828407016058035480c455482c81c0c070010340d42e4030b01c040c0000f50540381004008207000e420103009034441441d80c1e80c000c0004241c3d0303080d88401000f82d4800d004500050150200e0900040d0003580100118190070010f54149424140000d0380340300b412070079543c4889080301400b1140b1020111500841c01b4500d100403560400b400a440307100003606000802140000308554030f17500c1350340521001e00910b0540d400701c1200c2c038101c0c034240c420b443c40b0495518118504e22500c82c0000249807070003058080ea0380c4100e42e07030341010303842078821018070f070042c02000080c0016401c61089038809120308085c41c144124902c2c100d10300440840100c961f540144014842c42441c151810740c0045148020b51400000941e1081c01d030b503490000c201c102c0d4a85c0e04d04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 723967113 1250 723965863 723965881
    0x71107061d0a120f03030606020703030509101806020a020f01080124021222080606090f07050d4704020f0702040507020a1e03050a0c0212060a0207020406230108 71
    0xb4070080c44079210a682038589400d001d100951101011400b091901d03c0004440b80040b84440407641c040e21198108101d03007040c0113500b85409207003000c01801c228400c1202e1601132000740600542d4bc0100f420b242e00b0301c144000790003200f1702c00b4140040c42004010450514a07000ba00f80400705076005003100581c41a440c20f8088590601e1781c4a020440d14a910003200150354252485026170740215540c0392115261030301954020341081c101d0000911204d200841d1580040d0b4a00d01249400701c0c02c1094000c031018454801451810304428041c5c00c24000303c040c5144c4591402100b00b42c4c203082000c00d6010b102280325005a40114441c40000e200100303841c00550045c109000c275161011000b52030760780070002150080c4a80d000300742c00b04001d8049030055a8561111361401381c1f0020151100503c3d80402c90b440f038400f4118881d03070203041c0041801002001d0001da206e00b43c600c100019a11940c201000300e903445090a0099045200100710001d0f00b03003032100480c0c45030150 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 723968363 1250 723967113 723967129
    0x13021602041112010504090314070317042103050601020d0c0804030f0b04230304031e050115050f120606010c0221060a050609041a0a140f071107061d 66
    0x102941c450b01d06080c40102c1c0c1555001002c80d68142035880c26aaa201c004000449446403809400103809802e9022844c3d00c440c01070000034000d0a00740e80c009d4081c0703207948281908031000c844203d03103580742c25020440c0314180c05560843d82001d00039803828000007540c0c2e0b40300300c1d141000c00c11030400700b20900c84440704640c081d541000c00c4401d030b0666410301001e0360788113840454038050503000040c0300462070895500c2540001307028600d8203140d038440c4022034260551480003401c94140d1800010824490a034502d41c0080510340e400707141008100c583d040c4884080e018a10416100b80d02ca140462000ea01020900300707501c0e59511400441c40c40f060f440b8000c62210540082241c101400150452140360001020300c1644d4441040c4411503000384c2c1c008121121752540010a03c1e00d038001603034000d1140400140100d040b548580780701310150b6006450b940c1d003030207000e6016800442c0c00708400350100200002440d00c80000c140d4811910140111152a4411038950f03540c011 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 723969613 1250 723968363 723968407
    0x3050613050a020d110a090b07150c0908060702070f0b0408060415090f0c090b010c15050403120216021003060305300f180f030a06020d0b0901060f1403061302 70
    0x1000304a41d2000140041c410b601c004a06c00c0420740014001178241c3e020030454036081c0e070000c20348440c03120401489020f880c0a00315142805026800442d001c402004124807c1c10140d00400419203000b200b1040207110f5048412141000c07c8180000d000026199411503400700100d074000c0540343e000d00c000c29403000c000300301c82c1c070001d4100184907501c0300c01016a020208100010a00c08006681129007408020301c903031200180c120030040b950307111079807090180c1048181146207500d001c089900c1503410140c0e080003440c014042d400c0080b84e01201380c015042c20803259055485040e669504540203515400c0c04100b000d02c1901c901610184a843d4005a03d48626000c44c40600e19001105014162040340003280b00b5403401242001c41c200015014180c8919243c0300c0401030340c070150120b510300d502d412540569465116500340240140c1d603072001800c01c60100140000460011429506020301c14003440c0c0d41c6440100c00703510354004005903902c440d42c444071074240700345d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 723970863 1250 723969613 723969637
    0x10b030601211b2001181e02151e03060d0f1104050a0606021c0f120623120304031208072010060603020301082d010e010c0f03050613050a02 62
    0x103c607030200a400c4400c081c039101014501100038080d0351642c03802c80c0c00c0c0540724802c0500a445140110382142c59440444102600320301003014260007246080054412000e40e4210001d004580f82c4490400d580003025080881843d60410784002422107a100b0b5000d0000d9140042034410031960a001e030f4024680034006010b07528140010700c1c000c0a441c4500d20141c00b8001304521b101000740000755a43c04d4584030b01c039150000710030807105082501441000300341e81ba400400c9500306110091003801031b650311914000081024440c1582d0010243d111705da00c00d000c1400000c40c01d50b42007106926510380220b0360713a2070010455100040c603050415586200d9000040700b140400c0c5441800f5188500340030b15565410110200d100910810110303402902188071120148502c4292082c00445460701440e8010240c3e421500b0b03031a2900c0440c0e544001821245800c40f40895107030100b420200000e180090229440050140c40108100d039203c00207070001c401541a900c3d040011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 723972113 1250 723970863 723970901
    0x20f011205100512060f010911092e1404060507020d02120606100c0c1202061b06041104111b010f060e0402030f1c2d0512010b03060121 60
    0x2d412a02444140d500070140501030111943c107954500050090103421008401c1080368a4105450002e1100100d85000080d08204002e916528641c03102040201240240080c410fa180d482a40740c2d1090f0400701441910480205400c0c500800d071400c441c40390910756601c80d03881c400030f0707100804484002d51140c20800b40c161005000a03116101c0d1500b40c0c1d54200081c0c1e07d080940d002245040001d09000c1004000d000301d031002d200350407000c1c1c400b40440303090220a1003140d2400e22800d04c0d0a1060388214200300c1031103100c10400821580948040022540c510f6074001944201100d65440780c01070742d0386414011095103d40e1540d01e600c84100903040c0c4800000c0d0a101c0e0507030b02a44a84034408002c0b118140219602070890031520000416149080b010b1f0755001022240340c1d07041c4100482c3d04d442c18002d5200c07540b5610580e031059135030100c0c060101882d003010b800c10300300381105200f00045a608a04c044000c0c042c113180310310030f030480c0481075405800011108161000d171 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 723973363 1250 723972113 723972121
    0x80c01020307030605120307020f030708010507020607080109090b070e1504060e1207051c0311030d0b1f0212090a1206090302071502211201030c06020c0616020f011205 74
    0x640c040d41c0181660368042c0005130b903620400001c960568501050754104004005c010310706100c0540c080c11001d420f48800960703034020a4210303201211542c002d81c01a00401014641c003c101c1405092042e0f401c201d03403001c58980d000c110b54005c2003036041c0081c030401581c0c1a036541054200c0e0f419101c2e0313095551a240c4800604541202c50799034019901840201600140854100c0c19144003500c0044507040b0400c1c1140b03883c013208810b8007485205801100001818001400c0c20040407001140d55442442441002061711402102461082801038413442d40454500164000f41103400c0d20780503a030f030004001400950111540c48140040c01040081a4002c0c6200f01d0181e000e075200e141c1d13500d020713400c1c2010b01080c8070300680101441c5105000701000043c5a0004800c0030b07814201c00e100402056a07082e0819144065148010800f5682c1000341304c64821003a15081d00b070000645020348032112140000344500301c5c00300003c0003a44103549161040f40856002c0c406424 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 723974613 1250 723973363 723973387
    0xf090a14100302070203061605070602030f010f122415090b01090b04140904111008010305012f0d091a01081209010c030c030917101a0a0314010908 65
    0x20302800814003410020500041c058043e10030707110715030b0300540a004540c2c3c0306038500d003400c403c0c030030510203020301030007960301058942c0b0240d4815046648a44102e50518110300300800160340800410904503102c0300029007040500e20311241003502c0b400f02d034600307120a0f00203091a03800000381c85402842c00100078580e500910074084007030b01ca0501090311400725101c80e229a0107211180c107151600c0414504080348010307070207405102d440c4003100d08a0f00040002044040b0300c00090582401482070003820720420304e0a907404c1d41801010103101094407600302160742c080440030b001082540c501646a080820410342c80109403844038403410020514400078014408144034100c1c2020091913424103e5041010503110070000f81c003a0341e01118192001d110480c1045403110000070050017013800d42c2200d410740310142002502019401c0f08072444c61409007103420510f04e000e021072310355a1542c0d080c1c0350400703024411a01040c20031409032030403580003405102c00290b41c0c443c1d49 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 723975863 1250 723974613 723974639
    0x240f0f0402063a0506090115091202010507020d050318041b1815020a0309060216050405090c0406091e05040804050105030a0b19080c0d03080a0f0908030a0933020f090a 74
    0x8607084490b00c1d0f00343d82303804c001c001440d9800e10100100b89600c0c1c0510090303180c5c100c0000d4003481450098a00012070f80170414040b0511001c503910b6102250403000702034429440c108240c1700355001c00c4843c21414080200a4520100505106400b40c0d807000303d0b002d400384480a800c00c0f400d49004101d040d80000d42c0c0c2c0b488a40300790001039911030b0101d0715070301c0850714506800c10030100c030500e14280020403009140160080249100c1c003201401141c8507030240780700410446600003020701031021840c0c0400015140540d490b482e000400c0001103110051741c0a07200d0a1a00c00d40fa42e0380c82d1003401c0106280300c406c50740b2542c509540040801006142002d445281041e01c0280e4010024041c68100201000b00030402c0c00001803003c40c0703c2d901c080011a40c030000401c07072180540300d104c0d407940241c62030080c0310f885629000c1400000f4860b800409460306080306001c041070000450042c1c410140c40c2e00e0758000410300c4245d00484196603031590000c0034440f40950b5101801a11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 723977113 1250 723975863 723975871
    0xc06090f030a0c050a0b030405030d0b030a12082a1b10090503031602150a0f020d020f040504050f070507110a150c031209020d080903240f0f0402063a05 67
    0xa007003017040105106403c00c0550380980e80c48001107080540d0011410058409455040c2c0c06205100580c0c000c80c515024422522419468030000b900b0b00c681d041c0500c40c030106107005503043c82070380f40242d0007610040751103c03a00c3c0c0f014020003100c620b00ca135007000d41c406242c0b0000b6041c51007410034071801000860042c502c584020120192000341030383c50340d803042c0d03055804030048000501401d80d540c001480710564494014a0070191407403c100700d0700035141980e000f550100f400d00040c1428419250407032500514522140740c20003008040b40310300700d0020003142180142007025114504058041e08002043e54000900b0712030040c40404018403e60000b005200c10a9036038040d88501505990050084c0145203940d4039104410f80c05200c0540d00342c81a00700c10001651541c846d1241120703146003901540c100f481650709801c5020742511a00c02c0701e4403d200c01a03035007408031143c40323030b071100099075006d2115207000315050b9034010b5420102c103034150030000592540c403144c81 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 723978363 1250 723977113 723977119
    0xc0615190608062d0d05070b0c010204090b09040c1202030c0d030512010f080a02011d09010303020f01140717040204090203010518120a020d11030409090c090f0b030c06090f030a0c05 80
    0x300510f00060038081040c1c90107140810b2600032240f541803003a5501c010360300820490b036020399070784419501580441327030640d80c41e5804201071043c2940343c01402da010701e0498182c0c0369410300c1c5c2c13644080e140b210700c903500c55204107628400454505120408110300003c000200002c484d0034054526444950a4130760000100d001007019001140207000703440150b40101090f903100d03801900c0301c621001480c400580e800d8030004c215a11491028082c52090340a07000c01c45068001c00d0940d50480000140c4547c81000c00c5142c07544421a20440504041d008046403030324000b040c001c10500f10701a406508140401400d82d8400d0b140c145034038030002c102d5050500041038186580510014080180c00200465140314480c3c3d030302c0e8901010040c2a0b80ca42903883c0d01e21002c0311181c0000301c8000c5400c1074204000b00c080e00c80d02d868076007159014060b030f17810307480042c0d220040300c902c03d441580007144820b080d8881d1814180d61010140869030300e07082605082c5550141072148503c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 723979613 1250 723978363 723978379
    0x60f09060303110708071a0c0d020c0102070605041202040209010509031e1603022808031c14040f021221030115140403023c0f060c061519060806 64
    0x407200f0002001000c503072008001c0c241a60801c0c4403c0c1c45001120080410b0070802d201c87c0041900c18045000d4203407032a001000c2c0b4170414000a418402a0342c1702c4030074070209110411480b42c160b05401030040d411500140c0e0b61907100010395840c011a082c86400d40b145d02680d141200b0b08041640c0700416244c12a5243d0303007609564804150310f400000d4000e24024000d114103401031040c0a81900382045200080381c8406015145410040340ca003800341c0101512014000f80c1d104081c1090880c0290300543e1915440d1202c1100d200d24000f805100140304242d201401404440c0300d4800e080c8000e6980c1d040d0f080340281d507400a000e0700444402da1200c1c02c040717501a03021500c680744c8a45c00d50f070030030703186400300002c014201010301e01201442c8070383c0711945400e5800101203248100e4103e4001001414004003542400820f40222010810703080707410000942a9030103a100001c0352601006000171843c2030200b0030001e8050050f11001048290700030351014412003041c3d890f41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 723980863 1250 723979613 723979637
    0x6240a0f02120403021503060a0513050f07080906070c0303200d06090203010f170a0f060c200304090209040f0c050415081018150602010b010215100e0406060f09060303 74
    0x20382c00c0c461848001d6000004210640035020310f14080d6a100314014000d00400380c1c0c0e10301243c0442001000d012405907502e08000b01d075503c18400e10303013040441c500700c1d48520349420455525480609000140110b0324550800c05103e90894403150361200c42d01c005036011202143e02c5504122a0340610034240040032032105618402d4030704807211118a4070f001c0745002c01c0c4c00507103019031111500501032380c0c00350310214403507403d40c0803441c0c418680040d80e0050064000e200d8044c0703100c024100100160030f0050f40340300000740c5050710301c4800b0051355250007500040c0100482c2c8602106030341005001c01c1c030340c2c1d04240908212869900003100c100528042224602001c071101c07090016280824000d2480394602c0c03032980d400542000448181401508054042ca54040c0d00141c2d10f440c240c0d816542d062142d000d03101c0c5031505110490503c0d006401003825a030045403501c80d400400541071028031b4109030300620010b2007d08079280c0300c3e11140080e001d28001078003c2142071402e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 723982113 1250 723980863 723980893
    0xf1024030e0f030f0a090f260703031e0207050a030501230106020a06090201170a0204170316240e01020d0c020f0604060b0a1d011d0103030806240a0f02 67
    0x1000c2c2050000954a098000d01814030160400d01141d070400c04512800314040e45401400b1028160003201c584c0300550f038182c40e00354210040d200702c881d03401a01041001035000312281c003c41003c050740035112100144108d140010a51102c3d6000f003040600005000c01984200e00102c82c200040c550307e14411421004088280f18100061340021640004514194000020107205250900900c070981c3d41d28410400306443e00700080b68009405c10800d100002080b801840b010b01460807c080b50410300c0d0301c10030320030002e0324480245162138a03803d800c0d81d22000002d11040200725800b8001c0d0143d0013500662070f80801c491074611132124803070000170914516540381c0020045540da5a072101c019204015295070044582500400c001e020a05020164950070071a0071040d0f15204030050080d081840d00326440f1103031401030010a82c0401c601750b000c94291021032445a00000700d408120b444407511010240110b604280198000c0b0b40d200042c0c003030303400c640c5040200440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 723983363 1250 723982113 723982123
    0x615010f021f02030c0c0102181309020a05040906110c0a030201110403260c010207030507020f060f0a030504030e130902010206012705150a0806190b06030f1024030e 73
    0x1804540c0010b0101d920009801c6800942d40f290b215891541441880040f0714266005102e80312a0328046085c900c0d200d0130000149400324800203018081c09100344c020441c2c2501034000e0318003864480200f50240702d180d800c882c421003400740b40c4a5aa10041e1000c039102c0e508403004600650170015445004a0004107590507650403d290a00d464035203000441e60b103048011b104520381e41400000d801c0c580a1014140c69802500c44a5544410784100180140345088043c49200d040c0102900b551242c1c056a401ca440c81c1000140317904caa00b02034605501000004d540315100c0e40f007000b100d50303058210f40c1081d4800c7c0c00b00c0700c440c1d0300d46c0c9080301030011800c00600031100060040d18a00d241e0380085400400c10040d0008000c0280042034004c190f9402a410952112080c040c0d054410a4540c5c0d40e070310107481c2042140100782c0012290f220161094013520121000700c0d120308034000420004103400080d10078040c80110101518218141d454030100b403410039490b8542c1c4020503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 723984613 1250 723983363 723983383
    0x1917010e0328021c17160f050a02070b040914250311040e09280201020606010c080c100b1203040312050309030d18060b01020c010f031a030615010f02 66
    0x701211203841e40c1898009011042c01c1c1c00c000b184030300002040b520060500c81500c83c2419030714402d0405001d000b02e40303210400740140c074445444145550040790301504208981c8182c4c545690795204802c0100d1800c01c0b83e800050401c1c0d00002c000030300700e40369401042809405d02842c6c0e00d682c0c4251107122940f500035489100c0c640d900e036030100c1c1d0621aa004c000c1c6802c00201240c1003d8582c12034402e901c0c402c40310340100b0313440190070b030702203015140d0300600342c28141074000e88401c69940000d4441c43c010384218180302c0b2603180c240402c01644295540425400100c442119a041010002c0d003a10064a4015051461225041c04001c0229400d0365002000d019054664034070807101d40e400203141ba101d60000b800b58520300380290080401c4500141500803255441e8102902262407a8105605540c407000d001078941e60046051507140b50030b0708001895500d10410840b070300d00c0700c050301941401035034208500303070368501d01703502ca505000e0740c4840344820041c1c1e099944600a034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 723985863 1250 723984613 723984637
    0x51b011409061506090307090e0c2107030b1308070332090607030309080403030309110a081009060b060c010f05010b25051504081b2107021917010e03 66
    0xe00443e4450805800030b040010b030140460700034a580300704d00342c01c4844400c80642c468110109020580c649050f000184501e000f103200c103a1f040a403003a5540d00300901c80100340b00000000a6031440c19410942d407240d810a0b12a50f41e0005441c00900d41c0540b50300307480103807080080f0a42c00c41d543c0e4540540a401d02d42c2128603144030502005090303000220700b18109a00c0d220312200051805c4068001980309440c0411a040c1524004500c80024000940150321656003000000800520302180820610000a9044140c20104042e00036076520383d40004001400d82c82003401507120319044c00380c1000412a03662140308501042c444c42d180b1544c2031944100281130a40300e00044080030344604102da0140310400310b01c00300b03003c08890a544003840072480c00c482551804603030100600d520080c10010044a80e05510800b1450041704009408290141191200c8201c03100f489810740340301e42c1c0e89075034600d070008190000751440700700c3d42848010445040000300340c1720403103404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 723987113 1250 723985863 723985891
    0x1a0702150402060f16050c010206040b0105040e0a0b1005011b050c060f1606060e0f04240f020f0306130507050909060409120201051005090f16051b01140906 69
    0x2000c403a111524028000382d03032001c410032910301c640100400900c010b44801503902c11645443c10614101240c010805040d07400c420704201c0011001105c207815100c040300d0015002c00c40c0e00c1c20f91724207045c40340021311905022050005550200001c8421104240d031407999051411013124410503009400800350b0303000c0704c2a000c0034905280038141d401e2100000c603041c04464440c40c04040310310801940d17101ea4a441c18072010115040a5030700c450b00410340081400d20b42c0e00d0300e07078001d0300c0f81000e104880134403088251031540b40c000000003101c156040d0744074917060f04442280d6005903100c0d845074a5040411821070182e001e135500c692490b80b281c90400c07082006102c0c0c1c06200070300242d403056444000070006400d004501c06a40316550000a040c504115426181d89041d040a4401c1180e1400c2280c01c40803a1005540506201015500110404402c2da01e50107031003584a0441c61a21a85416840c15488003030010801c07a81000f807a00d6a01003140c031242c05036078108440d844 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 723988363 1250 723987113 723987133
    0x100504063e0f0c120406170405060601050f0d0501080601240212030a0e03120708130b0103110d0506010b0a090f060e1504080d0507152304050a0b131a0702 68
    0x50600903041080056406502e0b0110680456044c100c030703840888202000810b0a120940c0e018030034400e1038035050343d500750314180742d00c4107a956500104014100440042c0d11041e40d00c1c82403d90b0100307803043d5418402d9585600c24903855020034028080c943c8461410362440300700c540c08296000009401404551200560010840c0d0005000c4a649a2100108000500204010a039031082503070146510700700780c0c2000740030314005040c4440c0d00490f55060702c0814031402034035044907407145240f07800140c0c900100d0140d040156020701a40602d0000041840d007401c000c18520a00f540c4503104d180d141c408172440f1611901a08000606403000c266142c104804400705400080c4c001c0d6081903a68540d0780e05e044002d000c20000100702194010403c0900121003c11200c1040d00748130703c00720307007071150120780c03c2c0100c00407030420703980129040c00018040c10721000c1d04034403405281d03d4000d031018180b1007189000c881110012200d03681c00e43e401c100e6a07000755000d5020301040b8003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 723989613 1250 723988363 723988481
    0x10302040b1005030a0b1f020f060705040807270603030519260a0905060709061206120b43030b210f03040f0e0106030b18070210050406 60
    0x120311803c2541012481f5410449001c2c512540c6a6031070443d8000c00043d28030000040c14114043c10103424040e051106101b50078000c03030030f0010ba41c8146445030400d50042c0c101340d802c205c0920003654a0340f8184002c424140d10000603c41e600084152043c24001d0403000c6a0301440a0005091041e1540c1510000a1205189a00100c1620f8041500500c07621900c0c02d16400f650702c0404941040f5003044481d4000c60144207821807507204210451400c0b02041c01d10701c800000905c00301c1880002102c8910000c40018006000922580f180701801520700d421000d404050108801501403011564801e0091900851024040030110602c400c11b9902442c03607003030000124002d610140d04002c504001402c0100ba9410160043c58a020b00c0d9900c00c14068100d6010075041180304905500d9030703020b40d080c0d01e00030505903542e81c0d10f408080f070074145903c204ca49090306040c140000e1281030b405c060420080c0c180e00500701d103600b10002c0640c80c1c00701d0820640d12107001112034905 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 723990863 1250 723989613 723989621
    0x103020d0210050d150f080102030f1f0e090606012a0b060105120f040218011212030b130603060e152e0803070c270507020321010302040b1005030a 65
    0x161420302c14200a50f2419030b8040d074034171400714048400c001e107080054900c01c102d80c0c4020042d52000310b01d94200b00086560343c010041002c800d030f614030707070700341004410807040d40d0700500c4003400005450410720051900d8890036521f0500041c034002401002659094540300424182d003542111a4101d907101660720f5001440700381070010500c01d001d80e4222100c4e03810320170b01c3c0700d0405481c58681481044000c2202d4422192110b00b0240184440d0080400c00f9040c2034200040d44000c440d8101c0440c09800c03105126034000f81400014800c0c0100d50300800c05a1380328101c1031241f1100d11080a550343c80500c004032020110302c0c081403a00460001003000300400100c1e035040540f40298034001c444d1143d026141503800083c1c02c1c020700c09041200d001600c42d010382c0c4050341201c010001c1d59aa0038282035040300b80e6610200310668002c104075100071100348250801003c0c40c43c41c80145210911050340141d05026034106a494400300070102d0f048203465840c2561a8114540c0040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 723992113 1250 723990863 723990889
    0x127020d170c0109150b010c30051b01020c19050f0f060405011802010806040e0c0405010b070c0f240215160f0801030506011707120f030212030103020d02 68
    0x205800c05800740c228404403004001c1d0020500011808410750702d012036401c01d45404000116103131014620560784d00070b003a01403040d0080703100500240c415244001c4800103154110b1142101c00c0d42101c01500f00004e480410000d40c0020000712102e03146030700340d116640034160150015100315404032429070002440074080c0302241e40307072180406a0740c0740403120010001640c0c0725030104802c0000074003d880344840c0a0346c58881400080d0b00180c569040640900d100d035850784007880941e14100325601c00d10b5401441845103503550801d507007a0360310951003660189141c40000c200100d2800308041100e14600c94485510101441c0424220f031030340801046002c0c00c07842a07a05021340c0300d101d000390194800d1060820b010b90b400b4000c5000710718030905028900e00100041030380420040c0c11101c5000c01111030041111016042c00f80b507801580302016107150040a024020303050030340039407080d0202c0d441801c214030030280d03901003407100035444a9514404801070034501000001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 723993363 1250 723992113 723992123
    0x60907030b0703021308070e0117070612020304050c04051828020d210e040e011406060d06180501060806121f0207020405250e06190c080c030901020127020d 69
    0x7800c0e02e803c1c0c07907410481241c1c0403040d01c0000070010300c5040d00c02105144c411107034400822400b8544140545a8dc0e081003d1813840c5a0110004041c00024885241c41c0c84c03008000300303c0d52800e090f01e000d08200c080c0d00d00740103200d08031000300b120762100708107190804117804040001c00c0580c01c201c000c4028010480e04111460496020031159440f0915650510385802c1a80303c050014001161001c4140e0a600d0707050203c0010f00c1c02020381060f400c502d0503030722181c0e515081160a8040c2c041a40003c00c0300400c0411411282c03c1c9a200034107941c900d585492158680c0820044059400c900818203a0042010701e290b24489003079441482d00c01860250421803140c00040407a0000c83d0407000c00384040559079141d8280380703003c072000c080600b04003440103c8040032880368020f200c443e0351407000c141d0002d00321902403064802126408118155604080b0849548a40208400501642c02c00d03200b8220382c100802e40410703040c00004d15042d00f001a40800203550702640c8c0540b2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 723994613 1250 723993363 723993397
    0xf270507150c0b09010b01170112060908040503030f0904050a060503030307053f0601020d1704020a05030a08370509010e06040602010c0815180a02091003050405060907030b070302 79
    0x4009148407055500c5041008000241c10440c1d40001d03012341c3c2003051520322907804400501151300e255115030551908038030001240c00c50303032400c0711261085400996041c44003084041265180800418030107000356828401a11ba40d400c0c441919418011158160400c2c80041c192510540c060000d0802902d562071244a241000185005000314012403610300074030580340f84407940e105a50031950a200501c02d0440c1080010511900814504c02d48851403012405565480c22501c001e010010709407001e2b601140342100456000b10400402c546002d0b844d5120307100381000d25404c400c6206000540020601c3e81143c0b41c2c1d02101d1803a0600c10b40340c00d400e03000e840b800041c1000d03045c10f03000041c4002183c000a80308040040a060310401b40ca080c20040d6100d111400f0a0458000000d030100e80325155a000a03009502d070031900404400c14400c11719915030001e50041e03010340c0958100d0b465006050f51542002c0c00050064640c5034017107159984203500602c82d418007858064 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 723995863 1250 723994613 723994637
    0xf0306031709010815030706110a0c1202030609010e060c28020607021207021503190e0304030b06010806091b07020604090b1009060c0201030c120f27050715 69
    0xd010030a07801100c00c500c0700030422035400d5810080c15508502c00742110710340c618604001a546840a0107200c0c200000251003070345034182004407100666010300c0707174118562200d007040e000b680180c0040e4464410440400d10041c4184034a00b41ba001d5040a0891940c6190024009031f0149a10311000c0500c0c0f2900100c00840282254402c90a9405012a800c04110003494000c45220710740680000f040039a006a4418200009085407481c5890b201e80c0c0b080c102c51254030780c9200d5407401d0780c204220505146801310007132041e81d00c500203038280d5440301001102d04d9142203581a40020f000800301c1c000c440452842015100344a4540e440c08075980c0c082499a00240e100580c2151204d106009034600b80048215400061034204c044038505000188010703030210019042c9a83c43d412640752500c03034a40000303001c82c000000d0112400d811950b40007002e01045c440c011114003601e8881c0c100c04040e85007003190b0808010b15005051010081507400003c00d00400c1c0701402543d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 723997113 1250 723995863 723995873
    0x411030102120604050a0b011e0216030305070210090b0d0905100c03061a0a0c03140708040e0901060f050a1a1b061909080a050d060806150f040c0e010f030603 70
    0xa2041c10b800c08808407036802d10b4002e0005441001e010340c8255801c095130f142d0940da201c0309920043c0303035090b0307400d200380c441070000e034200181c540302e0454489071242d022040c1a0084000c02800e1f2080d82d4048884030310318421a2040d4031030040c10601c1c182004024014020ad40104500700e002e4003d50b00000c5002908404039203a41600c1e01c04a5140e20301044a40421510b42c0c403030022500502d842c21320b01c00d4009001d203928035001814008070071025030034486800d00f034402d407075400040c1541e515100c10341081c6045048030340340d010350b0030007a000c80c805103016180c1080740c102800700c0305003074200094440b044408218030700c610502804a042110040c80103c460205c000e0b001d48440c0c1003c21900c841c6500c811408001c2905190600b0002a01d01d402c95500a103180303000e0f925998440c1c862400b901196008010070b2061505006000456a00710079500d2411502c101c001c090700c10611043d240811440d40115030b5940c6013a9555000e0f0400890580040c44d0004440c2d07140e9441d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 723998363 1250 723997113 723997117
    0xe070f09050d410c09011203080a140406090b062d030307020603040606080f1c03050717010602060702010f090f08070804030b070503070e011d01121e05070e091306050411030102 78
    0x1c0c07070601c508854604030300f40d182032081c101001d409960414031513040c4a645030400400003402003c019145d40051005801da03440712416020038100e541e01424a400c16201501d15a0310035a581c2c000013001c50014a410300e00443c0b00304800040f44a1a0180c186900351601305a0000f80c240c00100440001a559500258801e42c46250b000401c1810040c0261400f00000e42c0707140141d00100b007810070310211801000c009001c6103004110380e9503140b070494985207107200e1210980d5401c400450059000301c2d40c3d0344a005c00b94020400c4502c00c0000100f920300c14007028011051a400301c50102d0002802003c10364021220b41d407a00d540c3e83d40e06458000201c800000148022080c4150282d1111079030502031000d207800060314440f181d10100c04041c0c207071101d042c4120a0016075801d8241e41081c0f1540f4540400c042641607203020300d90141030111060b200051070389003a980145050501c49004118548011000058503a43d031402000301400c1a07a40b1810074290007595030b02400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 723999613 1250 723998363 723998453
    0x50a021006031505060d030915110d08090d090303050f0d0b120c010f2c0f12070f050108040b071d150703120b0105070303050a0608070e070f09050d 65
    0xb41203c0c0070741c2e0100c10f00219103000d00304502c5101103d00100c0803e510190038000d5411019060000c40c0d5100780960384142e4880d100303c500c0c01030720160b4580380c1e080030078180303e86034080a8401d010200d160498140d4a24080140458801c0c448051070074102c1d0302802c1c0c4210f01c92000540e400802000490040c0700031502002e95102e03566021055038040031202c046030a50600d995071040d08641518441d164180340382c80544030090300209035903076003c00100c000c406048500301c0f444501072940c8850180c007174982d00101b49140001c0030b520807464188070315081101040f9a031180c1c0d43c01c58210300b0b0242103034043c400000c05040f103a40c2d80c100070510090210038042da80c0c0501e1078003038045961001182c280e1480c2c5960b44a175a42c02078112115640c0c58600010140c0d141c10001000702490707042040c40c0d100302d580108143d686450140e0085406440342503119030090800c8651000178087c10340c11514518440d0300103107294a048045d00d08040560508500d403102c60707032a00300c001d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 724000863 1250 723999613 723999623
    0xd110301030f050c030c0a121b0902040608160c140705150301050907020a170a11010507020303011a04060e12210a0f0311032a07030302071202150403050a02100603 72
    0xb04480704000701001495140c0800350050504400054000345c00001e40d84580300b400301c43e42121008111724040d0031460103200d1900d51340717165240e0350b8031002034006010308008a2403540c0070881c0d040091030b00c10040d0b40c495440c01000710f52691102e0382031150149698a910415401065950b2002400d4000c00c3e080e12560352a90306d0b100c00c000781c0361409441c2000350f401c909216408140c03520305081541c00c0000c901a07950000a00031103401d1859100079020794a4a000c2c08609031b4044021030484016100503960885d10009985462185218180203c0c888148103145801d0210200522005070b0041d00c05410303680c046100720f020804460300a4080000b1a1214a904000d003002d00d607041e458100006003110030110114840500b01284420000020300a4180c41e003102c010742091030135416468841e14a80035000e5006808100d51300c42600809100d4180300040407102d0710f50041c00000c0035181e50300c055072194002c0d0130100c218090212500440c10440c0a804010340c480c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 724002113 1250 724000863 724000883
    0x5010e211905240f010b0a0c06061d07050313060c0c0210030915020c120304020307030807031205160c1b0f2606060a0303030b030109021011070b0307020a03050d11030103 75
    0x1420ba103a00483c0c5500294000041441650741071100103034103403036010b1807507035070b60520140c151504c034220480104110308011000c50401c1e0203443d840c1004000889012094580e4002510b040c041191000000310170034001710040b03803041e046201340740071030f0070400d40810181e0041802c0345510354400012030380354207507e0104100001d0703800403017040070811801e001e2048016520b40c00054a0174400e00f06c00700100e415540c040c00340700029030340200040c0c0d81d00c10904e00a0a0b650902c8c143c0c2034003528050000780b4050100d85900c501343c0383c650b611411074946940f105c02c8200c2c40200712508500e0090046440860241c1c02c1e4054800380040001c4410308803a08002d00700900b06001d1503401100c248020b68454140001c1501d6050502003803496440300441e006004601c00658489000d039018807005800503600100445003c0c20340d521161134240c1c200d1310303200a4800340b0040c1e0280f003041c008644190050503109000b40c0000c50450104000440580c0085c1c01c01e131044036907 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 724003363 1250 724002113 724002133
    0x50f032205030310090c090608090304080303010611100b0901030609060608010e01060e090c030a0308130510020d0e0a0203190c0e15010f1e260108070f05010e211905 73
    0x24600b00c40c80141740802c4180a0724520010040003001d282c03040e04288003002020400b641014420380340682918001c4a450703603500c0f0070007010403603801841d201600038805200c000c0c2d04240110b031074500d400381c5001d180380d286980d160000e140c950308c1665459650500402c00590031300405560b0b089200002c02c0c0a4240704c1381e1000d10302c011b401610f40e9030200010000645000c60525032282d0507040c500d03080e0382d0340c4001c1104043d14480050040c05a81000c0c0e000c0c52165010340b5220b0b0828000f0014030130011005030f42e404002c03c01030341c1903000c5d400000c81001440c03c5404007a00c545c0509a890360390b5880030b207030810251541c0ca2003c584050a00403964455083d81c8403c0003031074190482d080340e1003400c01141c8640e030340c2400c00105110a0020441041040e60229001040c401c0c0543e503580c907503510788442d070090038003142d1140300c0000c0542c801c107401d240c9014000d1041305104c801307804140d000c1460300c92500d1715024105c1070f1000c0104180701230841d00d010710050101001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 724004613 1250 724003363 724003381
    0x91005090f09041509020312070c14030312151c0c030308060306040b010b073008070314010b0a09050306131205030c07112103180d03050f0322050303 66
    0x304940c0c4203024050400030040400c03131000c1c3c410f40943c0400320002d0910070a00109050409500b070104000300c2c00691402003000c4084060103e41c4203d42040028588100305502c91069858044003c4c000b000030500c92820319503030307507442c0900800702c1810034282442029040e5002c0c0c0166014414030703200708140b42e00304443c0c030361001d400c1740900300c0c0c0d251581c1c2c7e0185424041c015445070395001304e064410030428002c0c01405541c0d120303402c8841201c2003024040da450a403e5940055080008141100d000380240381d461a000141e9a0242e03080c01103030f0820380c206206a404205241e00c0c001025101409214001c400100b42c00c1518411424140e0034107030240c61035820080308208016400103c082521034003030b0702c16079465906900b000080c01301901141c108d003d9401d40e01d04c000400800000512950640340518554184620100b044650311001c0140c04504200000d0304904407560085521200444c141500310302c1184c1807000b00c0084540c00c8a05a2002050280d915 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 724005863 1250 724004613 724004629
    0x15031e0607050f120a091509020f01030507021905070b1201140306010b03060904020d061a0406050a0e16030e0604030c03021c1d040603051b280b0f09100509 69
    0x7100b4180345150003943da4030008075202e50044503081e00e41010114000744240d030420251103421003100c450070340f80703243d00000410307048008a20448100402030b0341d650083c006d1a10941094002c1d058004039803d8100c1800441c441c200c0d85c3d400fa006003c100203003644050084d19800c154044415810180c1c2040d1402450039080d10a43c4103c00400c0751400b46d104503640200140c071880141c4d211480071420040c40100300502c51400d00300c00000c500031007818002c0c824800c071024071a6640c1c800511407408803038007642c0c210b8075a90002401030f019041c0212202d80076031500107540c3d100c01c00c0141c180310082d40d0860000340b03043e403900103150307041180c103c0340000d9481c0210300c0c0048403405070030b00c1403180514080c0205140240015034581e40301c400215001026207441c01c04c00040c02003104001000700744951690340541203d10b00c0700c200154141c90008024019506190300d80c50309810420765a80c0460040000300752540300c041000d56076502039192903071191840c50400c1405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 724007113 1250 724005863 724005871
    0x70609021017180f0703030336060b030a0b0112021e1f0c0c0b121021020a05060a0f02011d123106030606050f03060915031e06 56
    0x1103044500014206010143c10580240c0301c103900581d4040d441d42000c1aa1050111500414200209040d016000030f140c000042c0d4243d4202e0224140364051000c1c010740001c940071002101d50000b80e607903807000c3e001c85802021160030030441d0f81c1d400c80c510000d07040a08400c40200141c0d045041c0305c40300f00b20400ea80c1803001c00d200ca810700410030094131440e0104482c030315428131541e06030158114861003030308032031600c0700c42d622003002c911240d000e41040200e0340d04000c00030700c03150003160301c01d002d6450004000c4c0c4410f64003683c242d205002100c0a03030f400405044000340e1951440018401054180c0358880c242d581c48601900f1215404928603a1100c01031a01d501e1100207d9000c0141c10007282d12510340c0c4030000410322411600103035544880032003042e03444c00710440b030f00c00c000c0300c01a5509000264071090210f03202c1c0107081600154040c1030003c5001841d1000d00d15901c83c0200d24118400d000f07801c0020b2426080114150701202500d0540d20b00d00740c14044540c0c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 724008363 1250 724007113 724007117
    0x1206050f090a171c0603020a0f06020d0c0503190c03020f0c131d0102042702040303090b03040203010b0316060206131a070513090f0b01080609071b080706090210 71
    0x6407500c0040261108005080140100e0344101d02401d4450780106a900200d1024040c1c1c3c0b0303800c0404403400c0100350502059100b540000400944d458880c1141c8098605680c0600140000c44401b038a155a4580040392140400d200d0800c0c401c422484041c6c1c0e01d5000da8030f06441400b02d00f4040d00b401c000703044051064000003120081521440745824410b5042c44000402c00c80c8450031420001c90640c0ca901d095000040c0040c0440101c1c010402d04c2030a802c10001900030b95030200201e11031340c840100440c0c03000c1c104010340b00150b4091540980040c0001c200551104c000900f461a02d4001544010044000744000fa90400c40c00c0c1e0b002c0d104000d400e12a43c0d40e5210303545070120390078055048101c9000011000c0340300d4410740740e4815450009020301a126003030f00028103180d000c03003082285442107600300b96110b40c603410300642000c0c164901c16116050220740c0200b50240040c4041c903411110000a20580c008018490003000b0020b914213203071040050a086d03240d42041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 724009613 1250 724008363 724008391
    0x40c200a05031605160308030106020609060105010c031b0c09021e1215012a0b160e01030e07030803040b060102060603030c03090904030c20190e04060c03060f120605 73
    0x80d0000040301c600d01002c403503145101e581460070740d01e860380d080042e030217680403c04000104035802e030203541a03a0090b003c0e26035543d90b400c0001d60790b420920030940000d01c0617801c040401e0042d1803c02002e68071103800c0200041d19111014603064030380c45687e500d0380c0014480c110f40c40700d203da140e08045000e400d83c41e0043d4050205100710024091942d41c0c12010700c06000ca89c090a00002c01850b07009860281482101082404091903242640c82c1c40e50f2500049942000c4a544803c2c80080c1d291511070400c0c101c0110000c10450f541a80148550407021000c00d24450245204921803030304481d441c508070000a0403e030014188500135407007800480c0505402106423161014241c130494450340d82d500342101c14050300f00014051103e2100741c8030551003a0032a180d826007064642c8103460700d9100d44110a11803612a4000092064020030009003580c1c110503130400c0603140120300c5e26180ca034420a4242c3c1680404070402005009100300255800f81603444a40340503500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 724010863 1250 724009613 724009633
    0x40f1b170d09030b0a0b090f10120b041202070803070813060e0612071e080a140106051e090a0806090106060504030b1914070215010902031e15040c20 66
    0x142c10000c40d03000040100c40041c0000714420304a41c1b003203803c3c0e64000d24007815030902c01c81804206000351055086914070100100e015030b2400130a10640d94011540c1003c2c2da116180da1a84e599240c0a11045000e1240d0000303000300200060512280215901556018410403140b2500321a43c0102c0501c42142c600e1080f039a646425135081c042d80d40e0300c00405a8407504c04480e034203007401507800ca11800b00c00301300600d603021036100d124468240c01041406009010b10f844508244900c0e400108100007550107078546e94180400002e07902581418a60708000098075110281c11000c0340784e0102c0d0401005180900805000302040d0400d42c1c41c103070a64035941300f0000c00038140340d4042e4590751488143c0307030300f40e02940c130700019101c0007481c60901c00c0c0000e40781c20010745007c0c2404108030002c116640c0703500c01c030b9004914010144100c1d08103502000074846000300f0b80e03000030380040c800e025981c4036805071102c3da0800365a4807400b0211003601c0208a80d00e44488100c6500441041d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 724012113 1250 724010863 724010867
    0xa02030d120f0b150d0e0706120c1d0609150f070c090e030a0c021305090c03120909130816080a03050a0c09050f0d14060f0f10030308040f1b170d 64
    0xa0003031036020000c00b954424400000c80003902c07030030140c55603c3c847d8060024986034810b2201100812014043c00021007041041343e051103005001241480c500b8040005450044000c2a11000251007284100440308001e0040d07080041400005240010f4200400001c030b5621070280152000800c034004928808590fa80a07012010b000d01c11200070940540da145040c070038a001040c030060240b4600184019216010510428068480c031400c1e005600e81d10000e440c0c800d6406801c44420303988005185c80340d101943c400755840107040182c0b49804282c1090150014054550980c0e101200200201107800041460400900c0c001124101544c0700c1811003c5500c122101442098104006201e03101800c00003000140c00d4200c8182c0000080f40c01440f4680c0e000c9440200c0e40c031000b0450302000229018940d2420154060001902525403550041c6c0641c1d402d5841c030034142c2da0404100c1c1c1081c684400c00e803030850301300b00c443e003103409005428007010003400c81075035420740c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 724013363 1250 724012113 724012129
    0x2030916050d0b0a0f0f09052a010503060d142b091503110d0216020a051c0f060f140906010b0a2c03011e0e0a0c03080306030a02030d120f0b 62
    0x100529158503100341c1800d2000306d0304030040c0c41d00301d42e20810141ca103524011f961802ca50701005001451080110b22210610600094100e0103031201861580c3e041d0810803d100c1c480d80c00c8500c6c0582c4080c1c001900000c00580022903621038028003007100d241400460040b40c560308800308500302d182800051060400c0003001c140b6424007042005031380b1000106802181a42484079101080a101019806c2c000c81003150003507658008494460040c480c9034003081000704108403402c130000d4000b4201155008005e4061600050491035000e5080c0c01d42d05003803417401c00801150b061110a610610060b40101200702c105894150a000090035014840200c0c2c1015400303450380da007070340200150540460f10010000c004144031003403082c650300007000c1c400b0f00d103a140008c4500d0318100050400e00b450380201d1385a581c24690396620560350b00007462940c040c0218910140140c03030070081c1d1480110700303031039190850400580170011980b030321918000c2c560030029111017648034048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 724014613 1250 724013363 724013371
    0x609090f0b07110f070608060f0d0f050a1e020906030a2112062709080412060b03060405072d03173a02030601080c09030705030102030916050d0b 64
    0x11442440c0d0b99105016a20f45004a4844220380544030b03219902040c04038140c4181e58907600c030007846456083c10b02c00405e980116a5030404c80111092001c1211242e07130b020654800d40c11502c0c48540e039903501405c03415080c10400c9400c0c0c2c8144400840c9801e8002c02d03445402600102803101040e01c4240c840c20480055144138030b80e00c846082558840d035080402c0384200b01040c0300c1c02e40e42c0d1a843c900807009031040c89940790a0100524545100c0c00341ca44070b2130f00640900c3c142401c201004820100c2100111951652140440201d0310144140b038400c030300450181c0b40301441d02c0e0400500c80d6280442c8075009502d40000003400c800c41104030240c0303070800700b05d00460303074000350030280da01c1840e0f50280d50409000e6000b295003103106100b040c806207400c415a5402c0d0b40040030007030b400161440c1c0e0105a5010009a06606030400b81c440d0190060460b04580d039214042822070b07109540242c0c60340c0001d44c0344410349068100e5480144810343e0400154201902c42d031003c10b102074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 724015863 1250 724014613 724014623
    0x6030218090a020c0f0c2103120a1814071a0d0b030c1e010905040524041107060209090606120c0319060602030717031014030a0c0609090609090f 64
    0x700803840d900c080703606403054a103d903011a0480c0200c181707043e941c1c00000e54440d100b002d81c80d404004420b1090400c18590314160300440c00e02104900900f100c0100038a03010300e0b0381d43d856003011004040707140c1c0041a4041c4049a00f01e4082c07a0709141881c0f40c54200e0300d0710080310f540000b60307152442c08841200c00a5400080d111658100003070400000e0071100f0b0380002507181031a100d20051b409071442200c02d0f21010071542e510750034013094480c12540004c400300c5402c81e680c1c1d5084401c40c3c4a0301c03207174018000140c035800e51214240079081100107860355603021601c0c0556040c81e0307400a8211604455081c00d2141c44d040c000c8041c50010002c82102d074021000c01d00315070b100c9100340000c40404c0c03004d1050a8494000944c1c3e40c018010658110003d800796011002020085034010780003181075240d41c0e4148603000404a0701c041380c054241c4908a114404a0169444a8090320751641c2d030804031483c0189041c242c4030140c000040407032501c0307080400603101440c03a050580e84a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 724017113 1250 724015863 724015879
    0x20c060a0e0d06110d0506040504080712110304060905030f12030c070606051806190e060d0f0803010e040c060302090d17070212031b0a0507060c080c0d02010c0906030218 75
    0x410702290600c1d0003554010711481c140101407030620016005400f0807000171008004540d1511700308004e40e0f1003035a000d44400c2d0308100001c00f18a016214450000f210300304000400c256428107032a40d88268003400005140d24018440d41c80c042c0201162002414000c12800c1c000000740d071054400a032002d0b038032000c0040c01e43c0421441c5d80180c0d00a140c000c02c842d90444e2040e41140360403c0440f2014494060079810025001c0c180240304151108a841403030240d6890041c0140328030420402d40d80c1e140414980e10000e4a100002d5000c0d004000307480c03016081a2511418141e85501f04409050060084d030506454007441061032a80000040e1031808610050f01041d101e44130000e900b110480144402c2107200000415500101d02007038a4005d905001103900c940303001e02c0c000d00390f4100f030004200407480b9600800d03c4e18000c81c1150300d081c541c01c555a15110310680f541025035141c906201115800511401c02018142425454101ea20300c01d00405c904c6460a14400c4141c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 724018363 1250 724017113 724017137
    0x15030603070315020a030b0405130209070e120c100801150c060f02120f0105041107060f060f080601050916020606100e040c110d0f0804031b0f060203070f020c060a 72
    0x2007001180000d640011440507074400310741c4140301a500c50024000444c0c1011140c0d031103030a0a104040c860b0010401800c4542c07a00d03030802c4030341c0c1c10103052340c000c004850f1200300003662088660904091400d008003070744a01c0e501071042c1400c0c00204502445952001001181c606400c80e000e12080351600c0c500e03240052402c2c2c00140404000403000510128220340c0089001111070301a1001803030520701e50380d07584100415141c81e51103034400c42d001481303903500113a02a00202003901c1d0800020440c69180c002922079002c2e580e100034440d0740000010030090400d101aa60401c800c9441c00f40402454003001c0e565800280505004131581d0049103916841000c13404a01d2200400134001580854001005141e03e0400c1c50303660b018034005502410301800c00821910030795112500d0607512a107080d1a410201803024403442e00c4051001c000410020600784440e2242c41c0040e141c0c20300c0d41d0010714507071481001105562102070002c2c0d4980d181c1c0c0030343c0e4103003c0b00d2506004800c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 724019613 1250 724018363 724018369
    0x350312090703080304051006090204140f06040e070f030b011b0807060e0d0e010e040207020a05010c1106040b1b0109030504120602091302211012081605010507090b09150306 76
    0x60a0ba2014024040110038070080050200d414420390190b01e8050129a84070859030040303115921170782806c40714201c1c001c0aa030401c81d05801e401000102410b0400b50f49115846005501f100c0100008140e03164981ca080d40510403a034512030700f880d001f0103528007000011019880141c3c090500000030484500f0801c140e0400c2c15014408000d6419440e050200902030003203122001c1c0c0459019003940e20682050f109807000741d60010701c41304034039281c980151282e00000900340c80c2400d10003d5241035445110060008191056115545540b1203080400c0a0b8403d152070301c559040c942c0d207401103944502514240d03401c40c0b5444415409916184009201c0d065280e40c1259503031418014a18041e8050326864420350a05511030002c1a40c0165400044135255400700c03020f4230902c11160b191038030182583c415502545400300c0a01007811410580300119850b03911070041120440d84a00f401008040900c202c60a152400c0300090144050304100c0420850220028110359 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 724020863 1250 724019613 724019623
    0x4060309050313030c06020d17160c0c080c01031b0c060513061a01021e1207030522030606171c090f03060207120507050c0d1b35031209 60
    0x103c50286801e001e5940c9140030070004c000d070704c83e83d409401100007617000c20f4022205420a00f202d240365103c1592040000c00080000034642c0c800c2001201114001a0303000710580e001e00f4100c0010280081a10001030548500700842c1d0101440c0412444900f40c02240b218002980110003007000e50302e002c00c204004580140c0a003000741007083d003014004080d0308070307080c0c04030a900b070b120403010408000d03401c48407451701416941e1205502d6000c82661002505004e0701c2454602e20f80985019100990700108042c00710160490104000300300c0c0314440c0e00e005102c1d003400d0080003900b504445855486507000a208209425080301c20140701e801210090050440200c02507501d9003402c0001790403500085035607007010307000c000706540a28251200198010b00070600c07081844240801c070b403610f4004581c0c0701034442c1e8551400e141c85070300030301034141d2040d111030f00c043c824408610f02c0d03601030b031170114951f11080c0c00442d0240401200c55540403568410225103488540c03502d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 724022113 1250 724020863 724020877
    0xb042004020f07050609010606090e090106030c0b0d0b15070209060d050105130b070201050c0f18060301061107140a0e07020a0f060506100e01050a0e0a0815011e0b040603090503 78
    0x803510000b40303004140145009021040e0140b03040307910503900c40c610305007252100c2c0240b80c0810003620081111401c039940310b9070b00804141c00410b140381d603582d581d041040190000030464002040c0c5140b991800d105100c01e210044070340e64142e44403203000e450148220200039009549610026581d911148445402d082c0e01000800140c6885040c00103070f21045401207852248140218002d02e10502800b40640c5410105514111860801d01210341c81002c0340b04445402950301c000941d10000918003c03c030a0f240e4071101c05e4a114490f041c030300030303070017011200a0840a05140381c581061080030f0b02d42d0300034801450f48420606074642003580100901e500304196183e0200702c06600302c030780212003c0d40c40e6002186140b2081d25880e040002c440d0000c0c900b17200b400340b8188540b0b80315081810140c0200251911400c0742410070021159082304a2011401004801d00000808800d8070074a6120740741c4a0405941200302c0c800c43c0700794800c05842d68810382c1400824000c071055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 724023363 1250 724022113 724022119
    0x1a091228210819140a020310080a15180b073504081605010501030809150306090a05061c0f21090902071a040b0105090702010207350408011410030b0420 67
    0x2030b515207856280c011f503000f01c500d4640880c04031030001c1d0310f0703c0009100070304c20b0340000c42081c1240c4081d001402001000d800e04000140e406400d004039240c13514490007a1f5940e03851500307452211072100b038640c01c282d8249841d421007001e1116241e20f062513058225030300200ca155181c3c010300300b100b00c19aa008025041d0b52034100000200b108090080031082019503401c20b07601c001e007102e0040e60004507945a0046024000100e03846030300d52010f9406800141b00e0a890841258002d00340c0ca2050380031240b400c1020811814850444203d07041c0510344400c1c4100000d00c0c2c0f00060510441c0d20502d030f01a60040f4050081146485842301d0040b0b04500000d40ca107003c2c06c08440200c4280b01d02ca018114103c0030400d041e1040c000c0301c507119040321490700440070254400101300c401c44010558810051307403c1107803980313090040c0010210117001113903070707155801000d08420014003c0004211101401c00010f40c545100c1ca51103034000000000036224415100c0c000c1d0580724201da4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 724024613 1250 724023363 724023401
    0x408030a03020301091103070e0409140706050903061803070305180405070c0201030506030318060f1621050a080a0218120d03061a091228210819 64
    0x1003440d5065002c0c50485d80d41050030700c4200707016502000d007488181e686200051603d00303c48814242a0003142201d07120b524074600e003000c07408043e804c085064216a000400000e0b080b0050703c0c00b00120b5401c481030f1341c00940012003031000b10f40ea0340310300d28005003804000305014100304d00e100d001c03200702035020304280514a40040c00400115030640124042890140072a54a00300002520b50240d484144c540207241c0203003c101d415003255942c08050101040290a50a078031417070baa5505104206031a07844005030001464001c15200c18000c111060102e0004980c2c801c1c0050b411111517900103984044030000002d1613030350043c82c00c4c0c100708a604241c0303040d5400261010703849210380d010000725031903510102c81c8294080c540c0000f41024030a03201c89240890030342404155200450701100d05d1011460b8191541c201d865144400d1400c0300d4051050540d8192540394080b0502448592a00c102820520014000c0d4901d49407000c001c481a0380c40f6401140103440080800b5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 724025863 1250 724024613 724024627
    0xb0a061511150601020c12030d06030b090f0a0f140a02101e050f0702062a03030a1d060f060f0414061c0c03020103110f1b0607020a0308010e040503040803 68
    0x140080c001800100400c1c0710b11141034814401c40c080d400d00a1105a0143c400c0240035010082c0c03451424081c2c4500e40010000c02c2450903151107111f00a500c02c0c4489011850130440c40e900305888005511029040000c0540c00100340d0360b102440150701c80100b04c159000c0c090725900c2e03d103500c5002904444011a00303020150081c918513152350420082d0b088500401d88215140c1c040c090003e200003009102500051130280081c14400009004426048080642c3c00640501c50324842025810000038403007c00c1c414010b641003440c040c16000c10400b500903000e696004010a803103ca51100c6001c60503c1d6106100c02005030001482449000d54005104a03550381c2960918400e0740764070350b441c101100f0410701800395500007503040e40e0710385141c00540c094810300c0c030069440c1c0010040e400f0a468040042c08603074180c0b84c011491920400e1000e0b107800c101505075400d6601c45030380c03000000d40c08688241500c2c1c0c407030306206498135a0b1608600d1409140c22214050001041c50 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 724027113 1250 724025863 724025867
    0x1620060405150a0c12092402070303050604090201050706090206090607050615030a0c090f110406050c010f1e0e010b18090706210c020c060301090c11030301080a0b0a0615 75
    0x154098103002c5040e41e2981e00c44041400031200c05142d0080071032410815014544400d601c030344241c3e80500b240760018007895221840c940544018800340da079000c60b010060550510070795030300c6001640d0400ca000d6807500007a00038000c2d1000203008649030f8070520115107402c8155181c41c4005051203485000520744641c82d50700403140161818506c001a5035240380c00100e01010f69000029a40395508049500c006460000340022403962a0441071500780e0031a00148001c000b950303502600c484125035070a0a60322044540c4000720309208980d120f001d6603c43c018a542d00300200025418400b5250741d0140c8403004045a20445100c0c180012580d41c403015407051001c5401e807004661919000e4400c812841c0c11950428241d80c2c4504400c00c09a100e00c01c2000e290041310340280d619400264554401d0704a500d02c40e480b50b64030782c3c0c040c0e0010f408001001c400e0018504660400b50f07840d9032540092405001c2070b114001042d004211540301c5070141070718440700c0385408030500380 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 724028363 1250 724027113 724027123
    0x9060c020f04142d010b19111009111009060302091804050c090a090803160e0301060b1e1602041104030803100303120c090e0c040807150e091620060405 67
    0x8112010052202d42030404804e40c600e07042c1c03902c400c078283c1031203d80f007400c0340103800c00643c4d102800346451250800319810072500903000500080860815654500390703a01401d94441a070203480a00354041120350401c03481000d40b111443c00586a6000c2000074044000d480001c404181d00703201440705002020070300c0f51103180d00f681c417010252907100da1007045a03000720700034000d0303030b0f0a00210703244d01da031902c841303980070001c1c903010f48015030501c0080e00711409540302801240c0009002020762003030410440398a501e4a41190401404260701000c048041000074400c070303603518511020003108001d9401854001c007009031280303050342c0da151000541d03010640100d14020b0f400300e50a540c0740201072008000740d0b1010402460402d0340b44861002412401e050f0405010203d41c2c3c840c100403000003014213404628810148c0000035000c1c07461401458002c401020402c100e90042c2c1c000481d1080707240c45d00300407078100441070102464607080c01440600481007400140040015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 724029613 1250 724028363 724028401
    0x1312050105060d08180f03150109150e040b0a09140a0203101e0b030f0f070510080106080705071a07120f0506030c04090206070c03030f02070609060c020f0414 70
    0x200801040c0c580710100200008034940041100c142001000000c501241e0b40244d00d00303019001c0410020324030006414014a1803451201c400c1e00390040203040c031503005240580500f074000c415041e00302454041c210a000303001505003055a00030680c0180e81d80d0144503403641042c110203000c801140c0072a12610801c50076880707031040f50020b85503440e41e481507080810301c40740c8a03071410364418900380c094a440d10f5000d502d4007464001004030101400403010315940203007d421641d050030b0400490600c034807024001c02c980b1400502000da088041e182d0004102e04007151160801e240040c2d41600c2404c040881c25011014070010382d8101c80840d001106880080c420010300c10002c030100c03442100d446a240c2e00000303c2c01558107184d80550595800540168038001c1e0301e888800154010780e00c1200000c1c410580451855030503c02800130b04003e107800f03c0010301e4040000d000805444000c1d1041190320300780d64059913140c2c0503102c2c1d80c0d04401c46211500e0b000d000d52001202d151 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 724030863 1250 724029613 724029623
    0x7050106140f010305062107050a09050c0a0c051c0306061d06090d14060708091501230402071506150503010b120c1b101823031312 58
    0x80041030714418078140003a603880240c2428010242c000044000d0100546480d411945040c17040d184a0000c00c21024210030a07401070040300e02c4c141c140140807410780e01c07030b007441c900e0101402142100002111900d045514041c0d521070a541801c41c1025110701242d111855035143d00d4101c01c2d05a0044c0781111469112810491131030300d444103444030400c400d0780e440001040b06400601d0320990f41c420850041128000034002e0420251401c00d09480314404650780200300b040000080103144001c042e5a070f01c01041d94509011000c5083c000d01c000c00311584144014142d60710780e07606503050a40c004c208406103440b00490704004110364001c007019410315810303604604c0d0046d82228122490100036510707110300d407104c0c20070101d8003425401c090316080080c0740c44040c42c421103055511154001d0a66040300c0a428000c0760410f034035011121030083d810f036000c54001090040200c0c3c096000300d640070b1070b49080f00d007944030701c03d20300c80d01c22130180c0c02107100c55039042c1d0800d0281c425 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 724032113 1250 724030863 724030871
    0x12010909330b1f030c12020711090723070f020301020a0c050607110709020a09120503030f0a09021e030705040905030903101103041e080a0302031009110906070f08030c070501 77
    0x110b0510414031544405000b9000c1080e4103403410610943c040c220545c014900f0010002c0b04007240d0782641d0014030195402140c0c1032041c0d0700c4c0e292009880b070b04080c2c039042c12010840c860811410840030700c00d880d01c0319203001c101082803000d4012094061607004008554030440c24102030300003100e10b00141c40c5841127000082d050f5003d4030203440b29600d0440200a05886d1000c0f4102039885101c0400c01c01032403403030024600c40307040b29924039903201c2c0001c3c1d41c803444e112842c0a941e60700204a2a40182820540c0c0c1c0540c0700d00c03000d45618901103040d4000c082c050808a81780c00c806501c49604585490820030034090048098407075140124203480501b11003034400000ea07031008a0815011800308085400242811514440100e112404040d000b005446185442d00410b4404010a40000802000c0513410709580c015203918202001231041c2c0d080c40c40098014800b14034002e080014070081804452201c04011603072240c01c2659030300e484021145d0a0300100d208603944c1d170070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 724033363 1250 724032113 724032131
    0xf1712070b16080705070f050a0507150311090d020402130b0a02010204060e0f090c0a0c05060112150c0e1507060c1e030e060c0703050c01060311030c061201090933 72
    0x11815049000b001d0545d511402c14017603840c2e2500030144081c0840e8140b007080d180c140001d4080c4460341c001c00f00d40a440714030604020029041d42d10410f0140400c00003040100040d075141c1d803944032030b5034051382c00507103402c03e00343c003d03014041eaa080b21001d040d0201e015501e0f2541500140159009a034417442c4900d6000288a041d03803180c1c1105511218500000d00e00d5080c0b400074161494041c5007400001c446615420708001080e00110b040801085940c003d00c0020481c4002250a5003810040c1c01d005000040200c032141c620140310700c82c0303500c810005101e21000d6036940c54010404100c0c3c4202c038800030300300031a4020000c100840f0f28950803a0039009214000103204170380c0140c1225941c40703410380c030701d584030000442c1401420301440c0030110302485041c02a6104403040d0050320304c5e20080500e8217003001e030b419110354020404850f00911168140e0304480840001240042c002e250800801c0881c0740210552600000f14404290070b0000101ca130380c0c2200410400108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 724034613 1250 724033363 724033367
    0x90c0305101a0a0b031b0a08040c080f150901060530060118020a030609140720190201090b0f030105040c08151207050d200405010f1712070b16 63
    0x90300c10b00c1503441151a242003100000300001940d000d9001400245280702d114070251098002c3c20010700015030305407c0000700441514100d001d09000002414141106000c8690317485101c48424582102c8101140080b0800d4008501078000200750080c2c809500d100c0c0312030b8001d1840740c3e10300300c805031141003046200403500030705845c407680030180c914294406d076801039402200140c4c2007503a2844000b40c081074901c41d01e200c8881060030002c0504210100030450031041c03040d00300d080120680d61b260514005000b980d502049107c2c844680c00500050720700403d03a50042403010000611221040345540045058543c211020450380d6140381c81111404411114200c909404207044070700d0780b42c070700103032001c00145004a4048070303168004240e481c03001d0b080031030340700c905050340000d0000301d071004480c0980107990401c03a80d0b01d88688000c030480c0b684900202e017002c142445241c840e060041000c0f03145005069907540d030341e5142a80041000b111211200400d04c0d4205014038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 724035863 1250 724034613 724034651
    0x50a030c03121e0b01050c060c1606020304080702120309181f0e041202010606050f07062c010b09060105030c031b131e0302012708100e0d05030106050d0f090c030510 73
    0x1518107000306511327901c0082200f125031090798008a4101d0b00215040040c0180c00114131503845503804d26100c0366184180510b03000d0001c6d859000350420702210a09880341502103003441c0301c41407080340c00e442d82c4100c480c0d1440c40030098074052445c450003064024000780b5030340c01180b00304180c1d0041007078110220300302c42403070050000082c400c2110252102c2032134041c0103094007a61000900b19503490018810080481c07903803201c1c0c008540c0005014600f8858024822801e90303007610310345413040009080b8800201001880440440884c02c60610b00a90031074420060100340da80301d05690500d0b00e1000d06206d8611189400806440800c02c02200201100e40c180c6604968034007113869034444020109070b280d03900240190008862008002540030301840042c0010b020500e503035001d04190709620400e051240030030041040c2640501190007000340d182e80011071525054090000d0282c110300030308a078072152404002d2180202c0c04403c9070351643c03000c102d1103200208900c102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 724037113 1250 724035863 724035877
    0x903050f1203012c3d09050405150106090e16020715030e030d0510050102071d072114010503070315050405070f121e050a030c03121e0b0105 62
    0x19501440100500034005414002c64640e024400c802d4000320300d000485050200c400312040080e07240010000c28440200004555a90312017038031120701c2c00100c9400850342e2183e111155a52030005003844020f00c4000701c450001500c501055a503010020f1010180340030f554050941d24000c01c04120a07262405159480340d00a007081c0f514044851202040466100c8241a111001084039100a100800004611400001e990f00345250816800031007a08000c0c150750044400340b2030795404002da03120700c100da0303140b40c0041e99440104840300b05240c40318000001c0e15080580300d034283e0b5004401450b42d601c404004176a40ca8042603035955007888060145c1c1d4000c01034079112140703500541d0b07106d8020011961080d58074404501c481ca5103503c40c60804800e00c0b02001002101c48110540c984900354114800703285460301500d4003044c00c0300a00388550705580d1400c050040010100202184004100104d4240b1201b002400c41c1d04c03901c0121031404005c1c1c0080c1d030003031082d1020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 724038363 1250 724037113 724037143
    0x15040509210d0608060a0b010e150c0a0206161a16110c0603130c090603031d03010b0303030a090302011401030503070311010615030f0b010806030d0c02060f0403030903050f 76
    0x7100311400e5940074040c01440441010304002c00c844030030102c0038081c41c2d0080c09a00000c0c8213600e49404070a0440f81550740980c1044080304410310107640310b818110441100114230766451140701c950318549401030100a400c42b001003089650140f40241526909004900400000d8440b13196094004012600041c44140c20b000303940c4803d124611510130400d0354000c94184204072000a0040c1d002241c03244040c002c40d02200d01005184510500101200002070124600f560350151041c240052414812102c3d004540203a81e402d410840c41000c0290a03295603007080c07104400a04400300b4254095800c02c0b620410001b40382010504898001d030195040150b20f42d400c407112581d140c501489076496040105002ca00043d6234014000540c070006605681c140d0a041514681031020707051140510400c10340341c50126061409041a24103032240c0855480002c03120b00800a1144503101c0c007090200030150080001703000e40303028000700c9000d0706005110303650782ea180f041203c0d2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 724039613 1250 724038363 724038373
    0x501111501090207080c06010803030108100209030c0607050307150506040b01020a2001020759061909060905010b0f0a031109040905060121020a1509080a080315040509 74
    0x44031800d54042c01d007085c840c08a151030300410500552900d032007038100e01d440c0d40001004000c0b4500c108034092a400030703194150308040f03210000980700c911120030039015640005000c0104242401120340d00ca501411501d42c50f403080c407800303000348411566603024515110500410b03600000c1c0c00d055003a030100d8a07107980704094051145c490201342405045d4400d4030400700d102c045c0c0c0e03140c2e000f2400c0c50700003811854208030040c2d21050811001045460408819000c015035618030002c41c00803048021017540d103440340400c004290f00c41058120003407411000c10b040910790010f00403079040c40c50620484e6200c07203c0d503e662080710a0181c80a104201c1002c81c64040e030440098101d401004030b040455480100d8240d42485204031340940011005200c0414040311f200344502d815034201c0780e0410580c3c01b040000f4028000d0303d0800944090034042d6038815520040504180c0d41561002290b500c0c2c210015041a1540820300c203203c24040224101032080300d105d8880c080081c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 724040863 1250 724039613 724039619
    0x30f140408132304050130170d0e0c06030f0a0e0109150506150306010c030818030a110105150a060f0216150215070f05160f0308010501111501 63
    0x8042c0c0d1202041c002c1500341240c0010303d0654100890811203142182e007041001c3d614100070484805802610440301d800086000302c003611000c4004030155481254441400d80c100039440c07041010702c1c080310010000c1c100038440c00035001719040c01100400c0311417028810040007864003040754801065041d01000600c1c807603094020f8581ca00f9050b000240c400c4281d11185030500c807464501700c5860f151020312080e400c110441c1d42e0030503056203c480c114142100000c101001a42c00501080420400b291810400740580301c202019042100e03030358400801c026050300040f400c450b00759460000091020520f0040d540e4881c0d100403c07820340d140c2482170a4401050384401802148201e1000340407040511000344050045203000c0b2a02200e0b100c002494441c0c04403245500030246001d100030550000800110984642403850300c2d100f0000c91030b0381c403020f080d00c060404581c0d9201d01c01032503082240203050f208203a8418041c1c1000006595075210140c90001e0009a140010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 724042113 1250 724040863 724040873
    0x8011104093c06090204060804150c021b011b06090c12020a050907030b1806031e0c01030b1309150b060a0207141809010c0f0f0e101101020307020607030f1404 70
    0x70b400c02a40381c0000340c401c0d11035110f0000c0382c129070000d1000c92040c000703000a1210990480d140080c509500703010b00492480025203840007070f0300f0300b81714001501c84056560302800017960251100081860211200c0c04e0120107000460010303a9244405500403c0440300c0110300813a440e0003418a01410780342805220540c2c0c00102607008055503031140031074071340d03441e800300001e1408001d0b000d84600b0078604040c105048042c2c070088003150100381c0d049804020032303001c05d07078102400c001805203a84004540101c0d040100d002241c1c6c41c0540d5042000755022200704546034002d0104482d08002c4140511481010b071240e001da441518100211040300c0c084038101040900501102222210109412101526140c07901c2e5154007445001c5a800a80110104000e00d4101c80d0103100c440f0240007000310241060242503200700ea905010300590600c1c41c55a81900219030764605084000c0d02d64006858240000f030814248060480c500c2c040c1151084282414904a84490380c0d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 724043363 1250 724042113 724042211
    0x2070c081203010e151017010501050a0801030f030e09090d020d080106170901022233080a020f0a081e090c01080406060b040806010f1d01090203040c0801110409 71
    0x5800300540741c91102480580366083c09902c2035a047d151100d90441b003009034640d088050308107034104281800b0312300f004c9a008046a0440360400451441918603003011506009980d4030250460340140a10668480009084d1828407641c1d080d90103d41c0c0012044500005c203110340c100050302c841c2804a0301a403071241c550002400400103150075044505403020341c1e8805884500b4100400c0304001c0350205000442411040007000011580380c0c041c08031a40e022009210308114030080000c400702903642c101c03900340c06000d0550362143c82c1440c0042c03040c0c0003160b600d44c008400d00d41c00c0040c280003802090003800c031070307010700000e011840046401c004024802c0e00c544d40c940c1c00c00500d41c40d400000f00054006030000d40044d40c142801c080d807201075948407502c400d096201240c143c186c030a40c11415070307160010160b62030f2282e0801d05d94454994010302c403594a003440c80c0401c00110401041200c0c880a400c1c08494403080102c00c0500c5241035103c0403500c2c581c43c0090500820013 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 724044613 1250 724043363 724043371
    0x301061d03010e0f15061c0f03020a08030a2a08150d02190f0b09060708071a0a0204080f0f0a02092a03010501140901022806050a02070c081203010e 65
    0x1c000200c1040701c1000901e05000d400c4c190b0156000031441c5c0c0420b407103c040041d406041560204540c04088a041d1201e0410001c01780100c01c1000900b01050f2003440191046500545180e44071b0501280c4100202a400700c1109820441c01d004002302c512410300003405001611910599522556040e6000041d6040d10768032503060b08000c001a60381c0e25580342c01c04c075031b0040e1000c56402c040000d0070700c00c130940024005c800e080c014006e00da520201102e41c51a4080c81250b1942c406207002c15030704410300440a00300d00b00a0811001c400b540d4080d00c00c541142040311400071500d4400e84e29521450391140454000900c00c03000f50508220554000d103c3ca07030500d1101e40c9511070302a903a0381d04c55400150f00c6c4000010005580d014910f000d4852009441516150400c00042c0d6100103200300c10760750420210103808d1400c4001142400751b5005103041c0210700d48003c04100039840758000b120015140784c40455000f4001a1041800440c94595131440c1d007000c60207264100c00030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 724045863 1250 724044613 724044619
    0x3140609090a0b0a02040e09061b160f0f051002040e010b0f090a060915080106020309090a02091009053c0a1a030f0a0b010207090906060b03010605070b060301020301061d 75
    0x10b0340031000503002d4644070721644c03000400584171400c0612200481070050411042c640c41102440043c020f8000300c40c02c41c0100e0400b00d9035a6003420202d507000741703120300058400d040d0030700507005001c007008403400c50074442c0c02614600d100c40150380742240078038005c80c501302051034014814101208008d04880c010b01642500b4400c50a0000da4200d0454200d20001815590100020540440701d00145200c909121045604002c0001e6681c0140e0100500c10a01440420152082903040b1220880080e01e00a407410071000042c00041d03041c403c840c052050300d0004130001e0484010f180b40356510100c2c150001e95070910400941c0c001c19840c9030b01503808200005e9200d0030610002d140100d078001182c81f4a44002414191070004104131801800d16201e039040e6a404500325040e00d0403864005442ca42038140b60000b030107a43c118003201900040007140d4181c101001d06600341c81020340342100c0c0e64801c03d040c240d001c02e1291802160b905880031071a400884641a502d29002e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 724047113 1250 724045863 724045873
    0x50607020d020415060e040903082a0c0d1b110d080d05010f0e0708161101020f03010915091802060c0a15020307090815040204020a051605010f0605010314060909 71
    0x50380000c0c00b210071001c840034443c44004c00400c4070f980c0240c00341c011000e08540401a00c3d41d07d403009460701380010003150322400a803014071101c0d4903101040c00c006510322105500d54651511a82ea251000d00700080407070244001034204101ca68030261255900c1814030100c9480b00050080104075400100e40c0030405019820300b01c4c203e445034500a141c0d18645806c1c840c42c08540e038904420283c0801d0411000344100026143d124480e01c8012606140c01044030b2000813031640240114105100000c40020000481c0300d0390b030300700b110700701e50103015a58499034031303000c0d14101c071000c2e401d200000d03911410002c09490000c018240c00000241511407401d850703600c204c50320169000d0803600a5002c000c0c07110343c1c2e60004001003d00120b4000384118100400103000c540802000280305540008038058030300d114000b91a0300171804e08071501036003003a14180d8081c000d580890130805103080380c0019550702c0707801002025107452018040648449040c4507080000800c444214415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 724048363 1250 724047113 724047139
    0xb03010807030314040815100603050906070f2a1a2a0c100f0f11120c16050a030311090904110411120f0115050f0703021f020d060501020303070905060702 68
    0x42400300c4100e0040d002c7d05d949207440e1000c402041103006401141c1090307d44800c208840344005409900316291b420040301960007181d0480350341d2350f1183d8050000d01c0c20380070401c100658404104216219051951031004003214074040f1a0003164034091003040c403032480e44981d50721042303207104461220701c5501c1d12002241c0d11340380140c001c2005504130341d1084c0c3d08a039100144175040e40c0054560b400d110441d44030589803021f0040040d49407449d0018004906c0d010424000c441e022030108034402c0110394141003ca40703031140c884003900841c0c00d1040101460740c0500885600d00d00c01814589192201c2d00e4842120360392500b020b0b0450366031401d400c0140380c072402820103114001400c00882c0303040d880a40400300103030302030058100c16103d80c003046508041941c0d0414071840c441e0381c8078241400c0c200c0c50041c607210000c3c0c28000b0035040170b00003071003070f00145102403209000340a16640c5000480c0c3d41d120898003030001a0344c402d1305000c0ba1820300300406007580014820503076548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 724049613 1250 724048363 724048379
    0x4031d01170411040f11300f091204121b0305030c0c03160806130c05061204021f09120309170309010207090207021509031e0c04060b0301080703031404 67
    0x1058505403a030a803c041c9400c03051a25001e2040b2861400c42c3c14401c2c810541c810741e801d405426424400c02d80001600c80c0b2036601040004030002c06640062440e05210401601c10141603032019100c5c01a280026003440949007210210307003099400000c0c0c20740a403158403007840e080d455103440070b001650000100e034040014060140c20400603200c0c104203d0105450b10000c000500e01045180404002400010840b280c0c040f0380c1202042c2c7c000107610388003c40445541140b60700040114030100200a48602c041c443c3e4030076103807043c010f042c01c405030b030400001d10030510001303400c0f0400384001100c59049146aa1190a003482c0954031500703e0003c03850440f0401c54164404070f82400e1941c2c0c1080120b005020100d0114603005e081d8000c10064180c22032200e051007070005014000d42c0f0104009450320705040c81c081d460400c041d01c460b4580341c00c80c8071184200d0800c400401e916900e2400c481c100d4444400030410b00d0304e0340c0d400b921050903441030b00484080a02c80019244 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 724050863 1250 724049613 724049657
    0x21801090c0f08010e1303050c010c0203130e16120612050c090c1c11091903060b0a080303060409020414010f0e070906020307030822081902010504031d01 68
    0x48080398000c518200e42080c01000030710a460b15208000c0b1003401044000b080e01c08180d0401c0e52400c02400001040c10142e40c00d10640c074803841150701e06825014100e03030100150131500550404d17841c51039900ea1110f0364659054030203000210524680144950003949004100c0b02038020100c0e9a640d60180b580c403100144000f0b03a5541c000741240d02035881c000312910f07805407541241900b420411403402688510124100c2d000d10b6a594076400300311000390503100e070294002c003031141429003160449034944a41c0b20454180b820702c5140c111600d040844c40b019205024021402d507502c110801010702070380c1105a030460f076070f81074000c88403415100c1103001e00a140c1c00001014a0302c0c0440324810030040621040001541041c88420307804001c64218642506d00a40203031180f9141ea402041e4118845048800b030114a900b04420030b005080c4000440c52000900100500c060b0b0a0f14400c40d0010b0006582d190803841c074440c095540d03128000c042c501007606000155002c0689 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 724052113 1250 724050863 724050869
    0x7081902120103150501080d450503030a050909040c031217010608010b04090e0705061603030509010b2202121302120c06030c09060c07060302041509140d021801 71
    0x500740e0000500910941e0b001d00400328100c15803c2200358507207080551116a00c080702010441d4103c01c040d1010300c2680340303200b410344604503032050b01030480c0d80038455104200b046c80d115900260000d250f00e0b0210581e214202961609454400c3c100200070000314000d1044801e07400c5050f0100105420f501180729884c01781d125642d001f03007010060b070311000d0164007200401030103000600c0700c081d0310130a40301110f46d9000081603590308a150070b400c0182c6504160f4205c1d401044502903228082600c0d048180079071000c1150352103035031109083c0ca20520015410100c0c2418010078181046035030010361900820040c1001c0001c0c561351105d94056503084e19040c0c480150a00f0341c40e0400c50003424811000003070400c20101070100d101408000c00322541800c01040990203611aa000c55403000700e61002c1c0c603011511440040c0094105000d0200d001140b6141303025418060740550702a600000304100f81d0845010402211016040c800c9800c014041101901c008280d80f940340030b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 724053363 1250 724052113 724052137
    0x60a03150c020304081212090a03050a0c0302030d1109041109060415020a05060a1e0e0c09090a08031801060609080715050904140601020c0d0218090304030c0e06030607050a0807081902 81
    0x6154000d05c0b007d0700215000e41000c0140e000f00840b400040e0f00701048400080c02420807080404140c01d0030b07415409000c00018403039042501c0210303041c0080004142c01e001c100c50404c25495605001290fa0248008054016404002c00d0000341c1642d92586e64861302403044406004541c1e440f0b40c2000f00c1a00c02c0d54a41e615031030300c00e19102c2070480c0c10070583d504000801c93f06021421003540e07103890f240a1800b84000001050401c4001c0c848074410b00d4110551540ea030500c854901404400c06201c10340300e518100011401500c5880d448086a0300175004040e5141004e42040550461098110510108200c518001e49841c0501c40c0d45056007208000c4500d406000a42805511890984a5405818400700507a0f804082d00080c140c00c210200d501d544500d000d61440c40745410141000c1034100b40040e2100d0a001d07006d10503070050301564556150007001f42c0d41c0340074044e03000300810b81000c00186039a2091105651203003441b0104004140c134580050200e070700204039025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 724054613 1250 724053363 724053367
    0x4090c140a06110c0d08040f1d0f010812030c12071206051507080c010f0e0703060c02030406050f09030a14150f0c071e0209100608060a03150c0203040812 68
    0x9540c68041d00c040e000301200d0070041100088044001e844900061001d803083c9100c0442d0f1041c029138030203980252001c00c164040c1c0e6602c49640700a600d4039018140341034555203000480c0c0b003443c240e4031412560b480c03008000581d154111007006400c02816821041400d105048010030094080c6015200d20b407105520700030100a4001919116000325019812003a03215054802450454420f03582280302c094a4403003a040c41d9015140d04033361a1005030401821003484080400c0880032280309130000c001507541c20009a03203c0c06240702c2c9102280c1c05104000310315006a004114001c5c0080903180c20244035980d900071403100c15240c01c0d00360b100f070303042d99035030790400f1800d50b0481410180032001d46000b40c2c1c080050300c00d0f2040101441c0000b000340c246200b0300da11640e85a54018000c084618000600024141e0035128840011340c0c6c202c0400c80e1414480141c00c150f036004084034054601036200716002c1c1400540342021448100b000260f031800c1800021401c00c44181115 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 724055863 1250 724054613 724054649
    0x150f01030203010f0c020c06071403070605060901120209220512040f06020a020619200d2601030201030b130f0b030c10080415110a03140c07031b0204090c 68
    0x1600712080b00010b04c1105260040400004d078001803607540d506003c0700c0036036032000d983c038089101d0307001da1008a642d444040b034150204480f64108e41e2003004151130f45070150b0703601d0019400f90341c10030a000e500615044c0100742d116512240035040c049544001140010250b610149800310541c41c44441e010302003024810424003c000c80001e0989200800001d14075400240711803180450714181303100751038542c4c03007a107009900d074020203011036081c0ca4404565081d460380300c460303000c0c08500148064103000c2020070750100301c0c644040085540030031f03a801d59005500811483c0c3c200c1350b0008900c06200f032980400c0c0200803072609000f4001c140c45400d030781814681080c003001144903001900003002c0541d131003540e6640c4140c12004c500340c14810041030f030006001c820030461501200042c80ca5805030981c0120452240d0521100c00766600c40501007000c0c0036180b40200000c116400b02409600400720782107200c0d000520005011038075a403071212050340750b4005024026054015 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 724057113 1250 724055863 724055869
    0x70e040f0216121107050f090901060b0a030c0906081909081b0708011a0306042a0305030316080618180601030b090c090c2b0c0914040b0303030105060a02150f010302 73
    0x480003003000e0380c4c0204181d41c14840010040105000782c00d005941710300010b00741060035040a4001c00d504c5030340d244d544814000c01009403280745100c4003c900c0b0650005400e5110b0079000f40306280028140c0103800109420101421054900340c81c0c0c00405c0c030109145101191803820380d40440b0000b040303d10f2500804900f502d000c000721654034983d80840703840355200415490b40c402c3c0c0c00307032003800c00e0b160130380b000300490301120340d65103a8031200342010040100c001300560240c1c20700c0c0c04003886022001e50444031080102c850b01c1c1c10003c1404003d01510210300c09641041500300100d1014219030151132401c42d09074070070b9966a044500380301d504034060080009220050381ca0401c1c0b8a00103010294503c1186643ca40d8040c56207107140b00c1c2481541c4564001c1c584520510555400450003044084c45020b0b95107541c1460640075040d1401e4800c2e810343d0300c009405181180e1906003040801d0304400311140650058040101c0e840500280003841220190390401141d4114014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 724058363 1250 724057113 724057127
    0xf06110c09010603361203090515011811160312090b060a080a0302060612160b03011e180b0105130e0f0703150b09122a0108070e040f021612 62
    0x14034001d995400c11034042c14808481d5003407090741c004101b111601d031011400c0b0001c1c10010409401da0165480401c00080350003990381c12a681483da680507940702d21052421100d900c0300100c2c9003d01000460004400240a00980c9019041c1900f00082c10a0f5040c191124a40221141a1000b08100340c030b1406550f1003010b001800e0050143c1c5607a954041c2d0b554074058000ea104030745680700b603050a2400c11181c80c0f02000001c0d0310420300c0e9545000c0d40740740c00a0180540240c607100c4c1500d25040c03000c20031402c50b4005d1003640000c0c81400c40000040180e1525141000307401c200b420740e8416207a19a100820301113a900080d450030f10b01d05034440c64080d2005003054204801c2282a0100d80103d05c1a100c0d9040015658a0450000b07074140603041c1680c10306000784040c40001d98004d081a84030709140720b140948140800b00119030401040380d0100101c0c1c0d0000f014152428250f00c012442d03c0300c54001403038014400d00d0100748001c1d007442110071250340030400b11030b6030744810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 724059613 1250 724058363 724058411
    0x360f0f1504030522032102010c11060c0f09150a0e0103050402100f020309280f150c0c03021c060608010203090309120a0204091511040f06110c09010603 67
    0x18815030389041581d801081445030403003400042202035000d44082c2c0280050400030341d4040348016009400040003060a004c0140c05800b40d460a080294694020307000d0842000381c0002802e050b035104003104a00360080c0c080c41c0e41d4902d003800f01103200c0d107030144903540301681c0e50f0480740c0307458654400030b1100c245480081d04146c28401030000588406000b007803003c0c8242000d019070b1441241c01c92440c0230b426056039002d0302c60580340c60795070750404000d218840f800784845c0d1002e07151018000500d42610900410714402007072042c800b803051301e401c0c20380d51040c103070007480941da500010300c1e25810800080800e085245100100903c0e4400c42c002890200000c2d0f0442ca400125141c503400b03030780d985900940c848a5039035403080d0240705440764580e005000300a00480740c1000d0344141003d9000e0700d160392500050100347c4c4252415182160043c103403c040b420304104c03080b107114500b016103003520711078403c0d0b842c4140d45100b1854080c06481d0f40010700e10f00e10003c64036140034062 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 724060863 1250 724059613 724059643
    0x61107080703030e0a08030c0c0105241018030c05100c0b0c0706060b0a0503160305060a030f0f0606060e0a09060302030307080705160602011a0306360f0f 68
    0x1100003001001a01e0310250036090006a4560781d1001d036003481d604120050104c10000100915950b80c0400b40c40525003a0b0000c03c030340e64501d0103008040318040c074010154a10700c0001c0d4080d14002050866140c0c0c0c619040090080805280c01d02c86d02d070b03400403140aa1201c030140140c1c140b01d040c4020003010740c070b010801d0151f20344861240c814060b09180b208000054035030103100164100800510000051134ae0341c1804080040098100b41d41d82043d080341c000c8400c42851090007014040c1c03030000c2c1094601461a85c5800142c286110110351000c90b02c00d0100c04500188034030307402414039898402000f6150810000c01c9103040e0002d101c46450500c00b800036880c004103035600c1d1580050300c1d40e17607541c1b281005883c1100071945140326489040000c140300e41c0c19005095404011903207078080741108003c160311000100c45101c12403428000b0084600c42e94640c12541070322080040b08000300040b551341c18048000007402981e401000a20a814070801ca41c3d05800485 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 724062113 1250 724060863 724060867
    0x50414010519090f4115180103050c1f21090f0b010b0f220803030103061a0a140d151104030b0f01050d030e131a0406060203031e04050705100203070611 67
    0x14a955640552111045c1d4445401000216841102410703200f04100017000c03120341e0111074191140341d0509001c101d81c2406440062030032428800540c0100b00060300002480400c10031080355206142c1032508006c010407000070b01d107070313450b441210340940c02485030103217060f46401e02c296180d0040c0c2c0440361003030081113020903080000041d40c20030324010000b4580d2521320b4091012001d80c9402a01d41c501001000204200c219031002c071022140ca07854110b6100980c0c10440d21125504c03070380c24058007a00d1042c10310314094140c84c0c0018442d2841d450901920440b03601220802e00040006d000001001c2c01440b01d281540b030742c0968000b00c03440056050801054407410080e000405001c0661707142e030b10a42e41c468160504581002c0100a01d0b00a400200c01040b0901000c40c0140c0c80c01c00c010407130303a1003c81100d10482c10441000500602c038100300d4903808005105640c18080d0180c007151036616503045944004a40c0c0c0196254172190034407008032160701c0c060348014030303003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 724063363 1250 724062113 724062191
    0xb07060c09081b0d02060903061614130621061517090d1809020f070201030e0109030801061209060e03210403020a0b15090903040807050414010519090f 67
    0xc108407400040664444101d900340c5c0c4045181400780205455041c01000c0c1085003039041c14009400e075071100d40d9600c24441031503a8840c0c0c180300da58012400c400141c4010310a99025020007846000c0b681811034101e84403240c501d0484446400a4140340b1410305405c0c4116404182c0c80d500d0802035410028505101c60b5665907140340b408500203104500310001050886400440c000b03000c02c02081d55107031284402c1d905a1f07030088904a0110b40b0b0800810805041441a0041e06906864040d2240d00302801900c1c00110550040c0c421030b01c541100c800249540038640e1034070100802540c41d403c0c0c5244007000130440e50702c250682000d2000700b0020aa00082c4404155040350100d0166280c3c011013130601003621fa00c00d5040070b00c00040c0991030070004010001c8401d4001500c03045910380c0100400d941c4902a90361a0070509001031007a0301c0c0c42c41c0c9141400c0044126031002941d602102e400340d5048080004c20241e50704101c2403034001050000c540b0141072503070014041c074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 724064613 1250 724063363 724063393
    0x409060b04080c0f01120905011e0c021513061a0f06070b010b030612061e09011416090e0705070506071b0b1f0305010e010c050922060b07060c0908 65
    0x103020a103125881c04c40542110740d0240b0403aa000c240c1e200000d00c184051401c2a50281401d14080000707101588401403e0810610030f485154000d9806000c640125554032107600308040c1032011040700d002c12001c0021030f54411400c9000c040c1d0140041c0c2c1522b113080010540c041040d15000d1f100400c140f5000501210100741510741400d03000d070b00e82e25001e0201c1c4c5170f24000d855900c03141c8219003c0c094900d03003241701c40c90185115500c21000d6584d9441c02c6099071902c0405294001482c0c0c00b2510070041c1100d40030414259240100c03d2640d10790b010103207a03c055401501103a00001e007c418800c040c01034980c048814203110503858100f144540040303a01183c0907107402c8010300858410038a01855004103074519040d0540d003a2207003840c60007001c40388400c0074550b18001e00c0c1c281184c020015500203032001030503900c4000b050703403200b03011030030120b001d5010940d90700000c070701c01c0904409003c1c114001d0300001128180341e8000341028600d50820003d40c1c0c000c02100c0c2c6a41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 724065863 1250 724064613 724064623
    0x5010e010206040f0302190c1e030506130609020604060309230d051e2802030f030402090901060b0319060806100510050c03030103030903121d0607050a1208070219150507021e030409060b0408 84
    0x14440314dc403880800d030b1401d00000411880d5002940101c0c000750000d85681e01da04441900307401912030b12030400041e14407017030f1140f1107511480c041e00728a2407130f8036150040000e4400d11096002c0c4242d14a002c068560260b8000341d192050500040301c110307620300e640b408070500111a0f00096203044041c1e00249500d000c0200700034403e0b6405400248a4030081d00524020941c0055039a140d040c030901c00020b41c5010140c82446030700c2c00c0b00010311071100044241c007410018808520090619050003541c0100d0903503201400400c00041c81c110300100003c50085000c1d5417880c0d002d9007585401c0442120400742d2408001c00c0700d1031018030311502c90313075142030003822a003065444c840380c0341c02410a00b0624020b0110520711690b000c003160081e562903caa00c0310e5098038616540411502d0651841e404d02400070069200f80000011560703000ca600041c15004071800503200354181c507030000c10001410110f03040800c007001401901e001c1c09001d0004202118105420643c41950b12 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 724067113 1250 724065863 724065871
    0xf020d0816020a060603230102070b010b03040c0806100f0605090906121504151b080609070c140d030e0f10020901030b0a0b0c0705010e010206040f0302190c1e030506 73
    0x7000e400540c580116000b04000c2d84400d41c401e0f42403103001d541e82015643c0c429020744070aa1441352101c6000b80350018401c603003a107544403200b40d48990030444000d2040d00000c204962556500c1c8011659510411205e44541200726211090604040c4400c4c3d08030850703401001844030034801001d0560b00e03495800d6001c079050310b15500e5400c1d40c000181c0f80400741d254900302451090144400c2c454259141403449950000c1403019030051401c640702030316480c406200086d0300d00046821850711600e9180c01464901d408030b1208140d480d8103001040d102d003064000e52049454000540c0c15000b080380d050125005040c034008501542502c5410000754040c960398002181040d23a8000d48c80318554480c0600b034841340750384501d640c0038941d000c1c042c880070501c0344480005142d84221580320301c950060740540317401d45440e940d00345200ca5680040301503000b1540007a060301e40141da0707002024002c0200204184c9000000c8034100310f00401a0325510890005102140000501c80c0e04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 724068363 1250 724067113 724067131
    0x10501020c0906010c1101020102040b0f04171c0305270114100506070201030905030d0203071d0d150b0d120207030218010608012303010f0603050d031a0402070318080d0f020d08 78
    0x6c1015100c00403802449240c2101000070b50100f14003210341d40c408058007d0300c414a01180482228108a594880c181e41c03407010380041079000514018801c1c1c011541289000d2050418418030306502d4a0031b00c611725059450740e5544007101c5448404880407508002c0408080001da418130000c101c507807003040c00280c1459141c003010380c1007002c108100c440548080504545a00f0441c0c1c0007080b140c0202c40d071380d1408040f01408002484c022080c035028950000f00a107401ca41e0140d5000a042a0100103522401801c02030b0301040546500d00b100c4032044d4054080307079040d8410032600b01050326440c0e00380050000140f004c42e0300070510a0541e47c01002c112480d050901d00300d17144d03181c81c009a5406500300540711340120b0300c541145003900d2141058400341c030f03180f9100b20105d89400644541800720446458003c1c10242d00500d00d007402850904e040000308000311004080a50200f80d403139100e000c00c00044d075030100c075900d107a04d124405031110406a1500070b1405001400b1004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 724069613 1250 724068363 724068383
    0xf050f0a0c052203021e03061b030103060c020a02090c04150219061d0d02010c09051207300b06032503060b060412140606010c02010c110111030c06010501020c0906010c 74
    0x20b20343c200e41c0c621002142c1c024501030302907800210781e1741841d03a007040841c064452030b4007080c4186000203500f0a00010790480a04581c0303152611406060020b10b0388040d4028400d9900160b02c540c921948180d17201d0541507075552078241812440d641c20360aa03400c41d0015401c4454480d034008041d00300c1c5410035408122242d8041c2c0d0440803200b400c0181c600ca01c207102034812100d0b01900100881c008540700e03503892a41e644103020203490325102c01d03400380d0014601031140c22811100703100e075030781c828040103042458240031407019681030009031600594682000036924003080400f50398140c805136043c030008010403088400141b0b0200802c0d0507124581c11565032141404d49009014840c1407480b18112810036155107015030312401114085c2c1000180c2c194003a05046140c10385c1a940c000c4000c40544400d01c800616060803070401800200400e041042000a4402000d41300040e0043c0d500d0180060701e403900006a5500510031081000842e81c0c01441c400801900444002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 724070863 1250 724069613 724069657
    0x2f060103080304240b0102060a0b100c060f09081e070206040e041e0303090606170d03150911190c0f02040b030114100303140f0901050705030d0f050f0a0c05 69
    0x200c5004c914440c0c141e14a036022850240d4075a50b41009807225000c2e0255401620b480c4036200540b4010340000307030086001040d0a80e080d00c10f03081c03070450a008040008610700d92851010648005039000d031080170001c1511001640d501c115070740e0420032100040e10300300305039012039003d014030700c2150201003c8200080901900e02d8600030b1030710101c0d10100c07190f8024500a00101390400f000d403942841e0600218034612424042d00464010b00001c00c140ea00300042200a0302e5030014600b00303140d036604005441c00650051034000c10380c840742241c95a0644d00d80b041c020f03d904016204010306901c4008c041351301d00707006d225460f40685002c2521070303000d00464003408031249221070052980003080296605042e843c4140c0e0308ca44c1da101c0c0c041e01c0b02d40004081b4050588001d07407480040120301e0300d960003080104029407051058904010301d8400810880e007140d20074910715500da50070450706442001c41d10340e01400e0340c0350803c078129124000030400c1c0074040100d2403003804520300c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 724072113 1250 724070863 724070873
    0x100c03110a0f1103010b090604200c030408190c140d020d050d110105091504051908030601032f031807030609020f0a1a03040606030b072f060103080304 67
    0x980118100081180c1ca411240d142c100c00c2c0004546040d918079000c044504400d01e418050034002c80d100500000d102e407503050400004040d03e014884c96504074800c0d03210700d03040d084054080440c0d1400a182c0303035490441860f04080340d000c3c5848041c105101c4440006214113000c0c02070303807107681072640702e03003e600c01081c02407580c02400781d403144d840a440b00c20040001001043c04040c5d681d0710584140c19800d00d42600e209480d00982030f0440303a00d84094900c607482165100b4029000c5800820348020956400e0855035030640d10341e0400410001c50396003601480030220070400070b1200b04503548800512403841c8040e100e000c0040003004c101290104042481c400f83d44100f55040655680780440003094200c01c22030103a000ea8030050704038136113001071408603840183c2044000c1004a00303814550b00c000d00485420790394840110220f220700c1c0146100398400d4940e41ea441e8241c40c00040b000314001000c001c000480a07038170400200102c3d5075411030342d1021581c1e80780d4880d880d00c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 724073363 1250 724072113 724072127
    0xf060504020118082d01020c01150f0f050409060b060c10060e061f02010e0d02010911060c031e070f0506151e0603090703023a110607110a18060e0105100c03 69
    0x41c5a03030b80e47c00495103062008040d800005100c0d0200c1c081a040380d030300c9245410380084c47c41180180400408100701c581455000844964401c00300090030003080000036909030019400307001c0c150300c991403022801d10030b4401e601c050449450400070f117182c104009100690403040800d50320401c4076041584c14000d400c09683c450014080c1ea0045118600c028001c080c040d03015980102151085215030810600719546000048050b44c0b0300080401181d4140403044100394450314200030020124180c240301050142c400e0010301054105840ca142d24019490301c00d5104e0306a244142e40324a50101c1e500341e00040954007603480b9658030b01d100c0c0c100942c0d5400030b034206100c0c0034464400d0340082501c110806c18980710944c0c0200441da404050020318400500380c60640604036014549070024018291103205070014031805180800d611072031030790044420000d00040701042c3c3e03855000e03020160000c10100030b1035601d00000903004d41841c000074414003c00d010355030240351041380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 724074613 1250 724073363 724073443
    0x1050409111011032b091a1f030803090d02060f012601020f190201060303050d0504062c370312060806040c0b0702100513030f06050402011808 63
    0x1003031301e840c0c460441c106100d00014500803514800b080001d4038010170300348102041e20f5040141d00c02c1c0310314400c0403041070940103001c0310340542e2a400003065030300481c4090b1001c6d5210303050719a1a410b04030215868485200300090a541148040110554001d403040e411204081c0185000b00f8400f8005038480000c03504420381c1d54000114949070028900c002c01d03407203000c4c047e801910481c0700000c030b00300d030300d903000060001e041003100c4a002070780c942040d170300917000e9000000c01c2254540041000c01c10100001d03513016440500c401c09010a02020340c240001030010508032508035201c2c0840380750b1510025641c8144a44c850605100e0620242003103403515040100586030303146123980700411070f801c4480e40071088000c1802040c00c07041c0c42510b603019040d044100140348007a07506810842611802c0f041c40b03040000400c1c4003108406505001d401c0002d0742d41800c1c00018400800e2005485103036450901c10040003000080c149450090704080c541c0040130714492003a24013541c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 724075863 1250 724074613 724074647
    0x40b070c050618211207020102191205090103020903010f0603150b0a0e041b081507030911041113120605060a0f0b0702040207120f02061501050d23040804030506010504091110 77
    0x70094071785044200c40100000c0b0300036021103001c054280d240a005011806004014080c030321451141d071030081d0050518900141405410041c1b00310101e800c560600020b4140243c0301e060801c240a11b840b581503914000b0301041c082c008000002c6010b4000f50b2180d0501100160005030034042400c0e542d43c038031010101e421946554130002c9650340d0728111516810429080041403082d4020310805030160f80c0a9122416440300f0410040200907028010101c5441040035000d035150681a01d03000d00f036010401880340030302d0304200b81129002030103103000715440c22083c000b84201c03d0300c0c24111441460310341e070745402a1000c81c001e40541d0200410103040c050001c482150410b10885800d1241c1d42141c00503965030824088000c840d641490110303000300604018000d56800002c4400000c440502c000020030302141384650085400b40c50b80100810309104101c1c061049a0042004407001e004548079034030784189100400d205140700b0800364019681c682e000d0350414040c01c6000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 724077113 1250 724075863 724075873
    0x80904020301080a0303060605032211150a18030203031207050d0518010b01020a021509012304060f02061006030b121c031d030706110f040b070c05061821 68
    0xd100d43d07a581d0b043c0b0784049000ca070a003080410000c4c0b041056900c03a2500c9101060000110a100c00c540700c42040c1c1039405050410a66010380c9665548001d4030f10118030899581e00b404a00500c0c404070700341c040074807000100042000d40e07000000c4e81d6071030076802e0350348016440b0343d038054031548660404011824144002c2129068400a908000c086400001e2000d000c0500049846800c08480250302c40c400340c00f0010001c03221400751a0410b0181017103d4011608141c0050668092040c0a1140d41c0000d041c070010b136005c0c1c03142c209440d40d800200018141f0041c075088004990003150308040e03490880400559504800440402e072142c1550032042d0007078000d4944030401c07d40303900071034101181e0344009800c60b0605004090100c0155044c20f0841d510351300a410181c0700e42c0808941807000b0380481e29030100030b10003486a488000e546210b28503180202e5005a48104d10403581841004400780507084012244c9a04444040402d6041e50200b00c2da10360200c05540240300fa = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 724078363 1250 724077113 724077119
    0xc0709360201091205060f0604020c101b0914060702010c02060307031d1203010e07110706050c010522170f0a0e03160b0a050a0915120c111207080904020301 69
    0x485400311200500030b0740c41070030498075591200200092400010042e0b07104100046403482c0500c06940c012000074405407424641c00000d900e4102c141c000104c25503038400c5100b584100d00d0325603079034a0203941404e07444640340070700402071552030000b094010301c40000c0e6023085a100303072a20482e9a40c0100080d881e030402142c000c00a100c164041291881245201c6c2015075001614800300d03000c0f00481c600c1c584c00c128021200010250844041c495404030b9803013a113009100300c401424503036651a8566601c501803600307460340900030848080c0c0181d40710b04829250020444203e42103521004d112054001d0000140720340c001b9002c81075400b046403003542d58820001c4110b654120100c0740c004241002d50381001800b0321031840d95406c200210b409950146015003140940c60800304145542c5003051680d00782c1210200c0005010040912100c0045118003e83c0481d14684401030000042509540e1000d4414412110780041005010855120201c80072090007400564882d65 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 724079613 1250 724078363 724078451
    0xa0c090504022107090503030a1d06040305031810090510021c0e011701052b0804121406010e062b030306050907030c1704060b1806040e030c0709 64
    0x82d80f00002034034103200000c6085941708000020a448009010b145000e400007000e980f140b49a5614955411401a100c03086564910150005500650217199540511440c084000ea071114226208281e80c01208020b0b80e44414074209503402925070ba68641b004041c00c1e407815617880b84c41c035030358079600110180300ea501c441544c81d04042a00e8a01c0f55040100720105c40f0b4000b40940c4d40c008451840400e51200081c40d00c3c0391011f80101002c1d0010584d41740e03200140c1c041d8001702100030005000b03504011411000d8000350f40e034400a0310700c650405510203041c01e40544500c0c4940c28480e503020800401d21121541d00d40d400c1e1140032051064030300a070180c241b611070544903100b143c001480b070318001d0050080040507039440542c2d000c0282e50760030031850090000d40b10315545190244440d181c501c4102c0d2141e028500400080c03410a0422040d40c0e04114100b8180d0001d10007003a00160001e112000d0321084440480d0031214495010004480162000340c071101a401c0026202c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 724080863 1250 724079613 724079647
    0x4050103090f06240e090d030506011206080303010e060f0d060c020c0a170706110d1d03030304030c02040b01020106080a122106060216120f050c0a030606210201080a0c09050402 78
    0x4c000300801a034a19642c41603803040e4001140e00c818250000c1400e0440317180b00b40d0005901c5881410643c000b10f07440701c00b01c42100c03190f030003481351548000014170007208582403440d40070744101d0b41d2241c04409039002ca00e08150441c4010191500d49030041002e60080c0014104000c014000c000c50580d103003003c00400314280494881c0b40a11040481c03103a124250951507110035200600c0034003002d400c00c0303c0f811058000c410140441001005c0d13a50b50a100940c05640250b031040031500c5540100800c646d001d0301040d0542e0f00d804030030018503402140e03407500e09800011101d52260343c20000d50350380442402d403120070341d030100200c06c1103411540424142d640940c01c035030544210810325080d4100d91b000d03190a0541044050002882c2e02034030400840c40746042c4d407188981d140c0800c2903401190000c90f400c2d80c8034a0140480c0c00403500b0003010840c074854412100c0c0c0d9580000c0d10003a0040e201c421a107032600710401d40140200c80040090102400442d5030780a83c0504640d13031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 724082113 1250 724080863 724080911
    0x11090f0a0b0f0d050702191106040f064802030a02030d05070b01060f05090628030b041112040206130e0a0c0225091802030106080a02010207060503090304050103090f06 74
    0x4903144c0004588102e10000d804034217402501c0c1c2c40c0d0040441d54070f03100d451a007641080c55000204000c04103042e81d03920485002040c5944845050300b05075400320710200305c2c2841a090300d00303071800c0071008400d00f000320b442504d05160810201080f2400401d09124035407034040c0d01403040348805404554400e0081c0b103901c0c0201880b0005980300c000c01c48200c510404c04400066091100c0c048074500070f0000c0c00d00c0030300791000103a0b0304103070707402c400c0418000e00d0410040b950b280302d030240b00d0801d4020310f80308210b4004650700d805590008001f41c800d0142c40a40206008034200342007090b10b15000c40038103500d03001502c0610340282601c020340381c3c0111600050003007686051403003805510041620361290351001d1003504002c10100103052a12986400710210016a0050b0700d003842440060654000640040e03045030001a03e4460a5404101001001c20410005000110070f450664000b440e02062403c0a0304001003101900000900200c0c90040c142d0b5520070140d02149030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 724083363 1250 724082113 724082137
    0x10e010302120d05030105010f020a0605010e09210d0207030504081506120d0f23030405010c02010e0316021c1e0b090109050a0b1e010303030204060206060411090f0a0b0f 75
    0x2c207506441d50516000100450010710052040d50301500c1e52409075680b61040700d81000141d01c402080d5282070b400420803400c40e400b80040c604042c0030b9280c0030017110b1203440100c181031402407440e209081e4240d140300d0380410150308162085040340c0080c000b10045602004c0003059a4842800a4a03814828404000c085d201d0f000c0224034050800082c3c1c80d10420b80500000940e0480542d5035001500c116800080d60240c558401441c010341c010b20000401440a040203401c54521507009861a0302c144011810b098641001d10041681a01d0350035184242c03518000d5200300840300200000c0708003000110f20b840181600b40030a014032400b50380c1d80c40704c4050300d0803a240f07080702411680107800040041100d0f015a15080024011b898407841040d1101003c0050300b030300100c000940002d410081668100030f100d4200c0812682040f9008075150028181d125482c2524042c0b00f0f54200790310340795580340c990b100070010710304a141e450340341c00b241d00c48617401030168200d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 724084613 1250 724083363 724083379
    0x21020d02070f21060f240e010e0c0a0504050405131109060607110a030209070210060e0106050a110106081b0405180307030c141009050d081902070218010e010302 71
    0x50072031101c0c1400c80460703a41c0441400082c03074580f0340d222124000c6800791042d980b0358000044d002d44c0c511401c596101c18071282180d00040200211050f002544075440c4030306c3ca4030042c404d0004000000b43c0100c01d807590196200038000080d20395004540c8881ea01c80c4c900300802503900c20110400c0c02c100d12070b0120085c02c544a40802c210500143c50b1380740c120900b48850400202e0403103041c1e80c291070007060020b12564990010b070b41c0040031100c080041c0c00c0940d0808002c070190048101420031940040d140358140300d0002c4c154060142c000b4200540d5008240e10843c0a5002d44045c0040901350b500507140710410554130000d0310380c1d19002e546041c0001d40786441d540020500484590091442c0c6540c585007198031840c41e120944840d005940c0d81f8661082c10001440084030b03030040402d80d40d41500300340e4180344913208003100327000c00e1104114960465114011000501440041e00c4005031b00209286011f80c3c0400800003d074840080384d850920290b00d0304a038401c440740a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 724085863 1250 724084613 724084619
    0x6050a1701060503060d0f0b1f0b0c0309060a030e07030605011809020f010e03190f11120607080919050601080d090f14010c0b070c060f020703081321020d0207 70
    0xc00d154400d100d088002403050012413603e1800d802d43e44a124040e1100d000442900d4581d02e1755403105403400103d5038006040d142ca00c00030400400000e1020003c0d80307003801c21514a1540b02d106001910748154000606082894007940c40301203048504411a4901501c030300e00300000748403e0107120303489075500381c0c0c5000711001c9028011a403640500b084001503a003400540700d001782c0e00340c919854000e184074809004c41802c080044036004e6824091420400e003400c2065035602c002e80c9025891461149850720000556a80c202c5007515041e02c041e40c881d202e460501b818112a0b41c040c42c0c40c0c0111009011002513103a06031140b040075500e0088a40e8020b40c0c0211841c0326500d940c5204000401000c0e90b402d146078943c0d041810045e00409041da03d151449004030784100116030b50344180420b02c151032007a104200c0380360030210b181c800c0e680c402410f1080000c009442d041b5600f00c1100401c49075503400466440b40915008410928805c041c0d100d8522103c2c900c01446021000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 724087113 1250 724085863 724085897
    0x1e060f09110a14061903020f0d090308060616020d15021305091609090b04021b100c0918050901090b0115080912220f0801060509061522050a06050a 65
    0x5a514a00010425454500017454049103040c40c0e16240e400e055080c082103803414640801064900d126000001d0320664500d00030300318a0000d00154080d030f2090180042d22100180b044800b150102c60070400305216242015604000712184d40e041400403600002c1e9404c9038407041f00342d91b001c03504180965039102448034010a500b0380301002a405500030028000a0b030700c0141d0b0072001810152501c100000f64400a80c0c11f0042503d581e80300e00d41c0e801c00054944600031020009181c5800002d141519485130110342c00251802c090f620404140c0c1c4041c2540700e0580345602c00e840c1c07151076030340d081c0200c4c5440b10b10f0300a00100301c102c4001120360101040300108007101c024a64204001e4003080904850304402c0e88460002c2580c0100c1d410b098001050024500a0004070344642498248950303003401424160040d2070060b00400c860304d40d40c040d070b002c074804030b601031400003140a103488920005600c4070390005010140400c2080e801001815500c0c0e540e150405442c02d09140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 724088363 1250 724087113 724087139
    0x2120105030d020a1e0807080a12060503070b0c0c30030319090318080102090a05030c030606040903180806070f0206060f240d060f060c1e060f09110a 66
    0xb03180068114000c020009440715000e2003404669001c41d907055041c9551b04210743d0700410050311607131400300c0e0a261403503000c004d020408074152000c5c442185060301081d980d500c10b0090f403d00b2040411f42198000e020003200b143c1c035000400354012694a030440141d80d020103100425002c1000030041c4041c080001203a001d032441010842c8440021450000240b0b0303d040102c0420a040381d901c1410301201c62030310080d00e0081d0005942d0068501007000d00403e40d03101c94041d400c81c0001c440710340c0c0c0108442e54818803d0f5808078400b0010310b0200c40700016017006034442c054240303011603500740000d001c61044800707884030f004803040d43c401a07942c1c4c802141e4540d441826000400300c0da003040301c82e030010003000c0300a04211140607220000150442c595600303166580d24003c0121a00601044004100710308095200142645441d01e00828100750140b00c0c1c110940c5c5e0000304441a8013005103042c03022800c02c00c22142e49440b0b000030001503480c510441501c01301064001c40c0c110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 724089613 1250 724088363 724088383
    0x314090415030c0b072109081c0e1027170f0c0d081b2404020307090e0712050a06090506040209100807031103010608010504031809020414060c1f0212010503 69
    0x880703108820021079446d54a45200700d140300810400c0000020440030420941d141420616025805034030300080c01040f20200c100d00f103101e11550140d4000c0242c00c40c0300802140c15a0011020103440c1c2d4400b240705602d241d011016854011070702c40001d81e40420b076131142480d044150b80c41d22001c4810401c040c50080c1c1c001c1d05500042124420404070b8400960b20011140300780e6481040186040340b065250000362400b00710160100401c6180c2806603c1c003501c00b03000100154282d20690035903601460099580480c20130040405100c42041070b200840e510035000d21038413984d031078825203511003500c0480c080e00e000c1020a0060810211481c16208514010b01a403840c0d43c41f24013051141c8034100380c25558070300c40070803040002e00410b407265000e0348070f441444510065603245260039074000d608041c4184010700091107440341c031040320071046131702548414108403d20b042c051004003e06079910100c819010503051500a0102022130015450103a0f0340c580a164a4403003a030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 724090863 1250 724089613 724089623
    0x70c0821040b03060315010b0703080603030a0207061b150b01110f0c13020903150f090303040c2c1503151303030207080d02070b0a051e040314090415030c0b07 70
    0xc0820b0010880b0310b4091039000a00604498140407000e01152521300c007a0803107508102c0015107002403580180f00710741c000d030080d0b00540c03070300302c000c50000c0d02ca14081c001d0008011180502c4c000e01c84000480f007100c5a0072058482000044003818002491b144000e2400703d40b010040c485c2c58074010461184524400d0044c01c11502401c0800050440260b80200742c180d0074401415680c80400c81c0b03a170341c0c52561842101d182403d00c08074484e40d600415110070780e8010001c0100044a00100c042242e81d0035100c20840341c01d41d842e11080007460200e0a110142500400100f03207180006d80d411038400b81c080e0345621700d01d801030701e03040401214140d4016000d0514500060311035030003014a54042c0e01d509007840790b0b0800c65800da030b07c42c0c0419501e0b40451002d124a4911030311555030020036811200014410301000711500c00c038010000740c00d124a040c05030950800d40001c44946420003031007042003100ca003045e2908112980001d0b11840030b80400415140c0c100c00888007a25080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 724092113 1250 724090863 724090867
    0x11a09010207060f09080a050d3b040b0303161203090b06060a031514091006020c04050c0c12032703040915050901170f030306060901030e07030503070c0821 69
    0x803c0d0207540701c1c0c2c10050b040c0c0404c40d21050001d0300d9a07040c058101064072500103840c031841c0c102e0380142010300a0ba091b506003564034003c502d0003501000b00140c60014800c026503044c400100150091101610705a0140800035800d1107003401e00603240b00092054030807900b81803111000320200c8900c018024920710000001c18038901e400006482c001c809840c000c10541c0302002e81d0150f0807030991000c5211b440020142e0b0352850078a0066901107001c10428000c60300e086002582c60a19002a42c000c55441e008641451880400c6038048580902203c005c18042c11141c100d60f8421580304191410a5000740c00d40032010140c034089800700d03401142031034101641000200500642c1c40340803007100d20005904e40314401494001c01e254201781d006003070b00182e40c038200070801c06c112100c2c0c0c100b0420814142d0b114421342e0700041c0d01b03203400149100340854161400403981c1000d0420320002c18080e080040f100422000d888914013600d000301404040030751302c100d00310410204030b502 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 724093363 1250 724092113 724092119
    0xb040e12180d140304060906050f0919030b1603240e0a200702040b0406030b07181229041505071b1103011104030f020906060f030f011a09010207 64
    0x110345400700c8034460040624210a441e0f5503004031070541225003103902d0300007280030401c2c0f40d00000028010105400c0051414400e0034110740c4600c220700000b03104640d800c0708030b50300003c40310741708016540c009503003402400c100084562504482d040320700024100265040031450071003003a0a24981e48203603540307079030a0200103180c1000c01440d00c442075030f494500d40702c5450001c8080c207010340300d5607606030780300707202e0040c041a640d040f2400d500483c1884070801c001402118070030381c04101480c1002401c1070f007a03031414011010381d2010018940d04600032040c0b00803800c03281d4520708015410345a6104400c25500c6070f0108850290404045070107891100c58142c0045601c0165032034442c0a0307030110841c0c89003002c8840400d841c021000c03003c845442c2401d1180d004140b80d08005181064a140d030b80e5070f0030b03551413a8000d000f40e4590000c515551581c45c1079518005911444a8507407a200043c404200024400c14018500810f80c40d014004a038081398941c81c41030340a002d0701c40c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 724094613 1250 724093363 724093387
    0x9030312060102120a1709010e15090703081306030e19030f050c0d080105121b0609031203130204050105040501030f0f2a14120a110f0402030405010b040e12 69
    0x8030003020759055010708241104903101e03140040c00c0c00020f43d12180c040107105a40040c000ba0000c1ca070450680c90710300c0c1000020400100ca101804030031010441554403601c0c079504160b0160f0009100d50008030390a4802c01c140c0854200f625041d41e01040240c0002c0d450681c1c0e1210070482c11402c202e10100400824400c0c07854142d540d2700d0742005843d00501a1090b894004103911450004204400500c0149000722094880907031040060610248101042e103000851a0310319226000000b41e100385900d083c84031144141080f408642c0303034940201644081841d40c103080344a1450b0100215040c940340c41614140d030b4100031481455220350f9141414462100001c0d91030756030309030400020f258803005100100900c80c0d90a56103a24100c164030300d60f402441c01d940b084075180d0501858007130005201c002d964100c801c81c0b00c80c07182c990100381509402c11840d0b42050002042100303104054020411210b4252800c11900000392000d5840e507092010400744001c080281c040441303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 724095863 1250 724094613 724094647
    0x15060507290c030714030603070506070204090b1f060503010303140d0b130905070801090209070c030909050408120a060b030a150503060a27030507171c06090b0402090303 75
    0x4505010a40040300e8a288441c4945045600d4100e1540c008200444103074070021200441d00b241880301d00354140f4900281d19074045000351402010041950019590341d038000300001c0350031a1280446042c48035400e80c04d1221000b4041b1060200040082d11380d1045080360f04980d0103607904490b468070001036005682c1301c6d51540081036156007038820582c0d01c88103d01a04500a203001a01403c41c0c54103904042d056800047d0592602c1961405a01e8111b1310542c0000396240ca03960300d00075480d003a10803402e40e401c41e50009140c80c04000c1006111001001000d12a802c0c18031507544000706c800c152030090007410003107141400441c1c1d6110780d540200b03052500b11600900210746840100e40b52480485021038483e44404644c0020084000da00401c07011118002c4505030b070a40b0050558807401c24014000e585d2000d0442c801010a020b980d001c500c03031084c1e8184080c131103c0301009040b0600034075640c035181000140c0c4a1815200321172500e203010f405981000300071b4200c50560 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 724097113 1250 724095863 724095893
    0x1080601060e100c0c0b030a0b090f0a05070917060604050a0c0207030611071b090507051809042301060f091e02090114030406050103050c0405040206071103030f0a090915060507 78
    0x4001c040c0c3c1c1c2c500014140918100146c031401c6451a1a89400d5400d401a03811916041e8010041e03241800b590030728000741644c1c0302082c080045469101d07131104488052440d886820361824132105011192004282c2c0c07405080200c90034400d07600d4502603034084682980c42c3e1009a40400020400107640340c0200c583ca6940a090a0900c905902c40d400310700c0007002d6200f01c00e1000c407800d1207800b50034403e02b5044041442c05d1818040c5070083c0b914000d9251141ea4850340d1103c00040400c0000a140c0c107048076008001170510540e22042c44c00781c80c1c00c1c090000c0b00c2d0040040400c803010184100e882c0c0b0380c0c0001d00a41644044601c0300002c2d0f00020703e0310304021203c4e03074200d40488224025070090b482102c00151540c0f4604040d4103201044006074842ea0034802480702595a090540d004a9001000e841500441f03078002442c620484100c200703680800b00300c103601c50350410408800c4403070469082c000032244928181502c40107005910200300c040c1304880100c0d90700f01440c502c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 724098363 1250 724097113 724097117
    0x10c0503040b0a030501331101020f0d020a0e031b0909010605090103120306060503100b09040605190e06030a0c0608090307021e010e0a03080901053f01080601060e10 73
    0xa01916071103002d18582c00405004086510b4400401c2001c1070b03036080b00d41d440f005800c00203260780d607114002e8010701e081e0140380401ca022281101d408400398102c503690188025041e5444800c01080c1d000f0390841440c09010585034030b414a41800c4c085820031f0001d42004000c3c800d0612641045403000014086907030b150b5071040d0105d00d0f91214803199008e1401107001100c2032a01040080075591560007603401c1100910512041c1d8141043c02000c0d200c428490603201c0e03200c80d0101c3c00500d070650009a001d81c0300140f0079580740c40740b841d5505030b0702c404041c2200b9668410a0550f10320490900070411841044100685445001c081d40c001c4141400d50b881c2103166000550b00080d09a03004a41422003c00c02001c0d43c1c011b034908a00c580f041d258598060301e0f42e25040d05078091680581d060040c00101007022080700c0c20142c230400c110b05081640c11920a4915101c2c1c880520031690440384180040750031240014100d04807141a030700c1c940c0b40348200c4140160640301c0d05001c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 724099613 1250 724098363 724098367
    0x809060601020c012106060801050a0f0f09020c15010f231c0f0b0a1d06100308030a0906060f031e080409092121090305030a11210a0c08010e06010c0503 67
    0x41203460103401b0090205a82c1c2d503400d0b504007030805c1410306899000850040100500700248540c03030010b5421525003040041c2c494012a000303504009140707005408048400300040f8148003400040c03819245408090b1058a2003544000e5000b00011030341035100031600c0c03d01c01c41e0035003440c0c2511482d21075181da4007030200503070b00c000c086070b015903800898070b448205995070740c0b41e0303044003041103400b010082189042c400304400007818a404040c014610000002e114907140303030004000154800700401c103660780d400018055131900e01040b2900c14400c200c0c40d100d108041040028140c11610042c90309241c10310400050815542c2181c00c1006480700a4040103103291010211440b41c81c1c90407040c0c1c00e880c9041800c0b01c003800c45008a460080c104001c00e500005403076110403104000103100a0309821400e10f8020100700381c01c021844030100e541c040920003290701034403140e04140440082600203441c00c40c4240501945424800300007030003503101c0c507418910740f409001564 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 724100719 1106 724099613 724099667
    0x607030e0616230c0d050d0513150e070320090106081e130524060405010506180f1e030f0a0c181103070e010809060601020c01 56
    0x21612070100c00c01d41d003001d110b403041320740054080c801c079207101121a07802081603000c2c0c9000a400c60402c40802c0900801d10004900719512000b40b0883c80340284c444002450b420040d000303280700d450000008106420414000d00420f4007140c0b010b007801f9804d1040401069010b0b0080081c1d031010003180e00d10540d028001121400c22040064881c0c0d9007215024900c05030241460003840b141e25014046040b1700b05d8520600307a20f284807681e0340010002292001d2007107580201701040302c05840300858a80d8020520700404008150710080c02103541b0520209640600c40394031240c82440c0d1400300f10101c0d154040320005d014910150344c0c1e0324500c5205104520140d10b00700b8082d0100c0c00550098180c46160a041c0e07a22450321010041580c0348074140c840c08119000042010301c000401c100341318407c103030024140f43c9045401110070030100e4481196107050f034200c1e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 723920863 724100719 := by
  have h0 := BRFrame.cov_init 723920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 723920863 ≤ n) (h2 : n < 724100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
