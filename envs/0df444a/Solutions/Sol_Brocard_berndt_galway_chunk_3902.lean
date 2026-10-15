-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3902
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:00:31.650975+00:00
-- url     : https://prove2.me/submissions/afe313fe-996e-4bd5-a1ef-4305f19e1140

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 701618705 ≤ n < 701798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 701619955 1250 701618705 701618711
    0x110706090c12061b050f0d0510050406090209100f0816020718090201021b060706150305070303112404031808120a0206090309090609130501050c031e0103150f 70
    0x990400703429800c0e03802c034043e42c1c500c0e100c0c0b6141c0440701809001003080c02040c10100c1c01c4c5207102000c22281d014424041001950b03900201e045103051642e003900818004005000305a19010a203010350010030340240500703440b81003880d5607401038142900c503030b140750b8541100f5502d90520501c0c00360104251015030143c0e10b0046180c0380b00b6025441240080d650100c0c5400c8144002231409030300005844028a03864046461030b43d4140894280c113410a1b004603840038010320841c205421984010241e210340d0310000100b41d00294100d40c1c00c0c000d80700b0398454030600c019040280071a0344021020004010008000078051036003141100c22100f020444103031215541841c5c42034100c1c1400c208500400c8504c41181d042040660143c0b00c9000356003071010900c00f05140d9180544807520450f40b010000f65035500750380f0582d8505e5040303070082c809403c0030107400300154410f40310340020b29418250940503401c800070407130489901841d02034041d0030001d10303400184187c00b010041107807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 701621205 1250 701619955 701619959
    0x2101020409110421060e0610182a2c0901080f1c110703210905151b060f040b01080d1e0c0b0c040e0f04080924180f0301110706090c 58
    0x10014644181000e031301642c0110f0412705032a00c180006660291640c1c20001c402e030040e400c01a602040c0c9041c50b0003002442c840b00800d48080040b5400c44081c1e039902004414100d02c1e02c80d045c1000141940c5007085640c880b42516110310001b40790640544c00802d010340c10b03c00c2c8010040e8003125034541800c1c9890300342152410311101e98030644141903910503a5400c52b4500116403c07c035102d0526042c0340b0316000c0809c0c01141c2c0b40c101d040e41900c002ca46c1001005c200d0101c402251445400d86030140340000402c0fa160301c0540c1d050351100c4800c000800c000000284803204145961110300030381c507070010910080b401d502140020008582e02c0d030000038000e0512640584001442152100d0510107003208041004210402165815003403001040842080720042041a0799580c041000102481b1418800504025060500060005007148104840705d0030010444281d40c601002c4001c0600b039a91928142c0c018040c20051107000031125404015440e200d01180c00d050742e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 701622455 1250 701621205 701621231
    0x19032a09050f04061d120918070201090507090e03030f1032010c08070605070203040b1603031b0509061b03030f0708010b04061706210102040911042106 67
    0x85064810b0081d5000d501c0902c0300f008030901929409420031030381e160390404114110b9640c2c021a00e14141d03c003400003404126600c5036010b010407040700382100d155074204150000c1c003c0c0b1a8020179910f078090007c0c04594500b0300d0184005005100c1c0c000c5085460306044a00000d5018282c4449007102c00d400050210b1843c6e08a0031b00840c5100040e0f03000b822a0800d990000700061141c10081600c044200003040c190588800715000840005e007690b8101080e40380d403085402a02605502048101081d2207185008032641d12a0f41c05000e400c6883e14841180ca6415405401052003030000a6440c10070001a0085011a48400c000700c03508a0038181168002c0d200e6034005040442000030980e0001c0000d03005101a543e490311b024500100104100190149044414a04008101c2650719002c245482000380c00004410544081940303001b5401441822040e50803c06100c80300100c100035907048420082608500200c100203019400c1c0e641e4034104d41e50b640c2c8000c401245 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 701623705 1250 701622455 701622461
    0x60a08100213050a08061602101a03100b1c050307020402030a060f0f120803091c0914010309050c010f1403090307020913031e0512041119032a09 64
    0x21031a861001a03486038450186860400741d504218040c0da0108001c001c1c40d0030000368640c1c032030300c010742e00611000309078001c82c20920700d848107030002414854042d025003030051000c942c1000450440340e00040c14910201614000600154082c00b8422013810180440d00c0401030144500140c03031801075247d00040482e041078038444000303a03486805100c2040d4005256010b0b0003203000c040324107440c0c2010303d079440c1904100100b200b1404004030b1080001045840045004c1d030410305854551080000c1c40c1071158451080d9600542e0b903401850350181c4500c00d103642c0c0000142070043d01c0c0f0001500c000e2007103024902000303040e0300c148002c5007101010354001c0c2d034020051903440107517004000404e103003c0e01d0141650391a40070080062340120b00031220f0441d5450300c00d80b0142d003550544150062040440c920a05c0d07004010030845d940c3c5641c101442d048510b00d100c0d004160303100c14110224007000b400c5003621090240c0700c042185040007692811030800302e030276071038040c1401030b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 701624955 1250 701623705 701623723
    0x90907091109042702040b040f1a190e01030602030c090907110606060f1603210203090f0609070618090c0305060315060a0b0918090d0215010e070305060a08 69
    0x6a4002062841442c41c0c50f000364000c1000035030a0b00750125000d0b20b20b04216500f5000241b19503600c162034000d60701d0700d412001d0004000182001044041c0780361000f410700c4403004603c07031407602c01011085241c010701030090306c40c000120b048a0b0b00b5940c4d42002548041c0c803194403400180070000d402d507034040600d4410341036070741c5104503420b900e4030f081d1600d03c002c2e0440748aa2801d02c0040b403a1880c14003030703503480b56615640d1406003c0d039041c103440c00c2c50200191180e00403200f80c66440b4000310380003180212046002c8070315007c2811242034640a0984108156401c20b540400c1418466100d00c5070302c419003140c130040305584903008012034958284207804031362a081040078604d030510400340318441c558012005460000001480204d5078002c0c01304003903000ca11040244c549011003035840005804902260800003440c5075110307100c188031001840342a509194128032040340c0c42c122149031140c100307113444a41082e0060300d002480306402c180d002400049524042041c400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 701626205 1250 701624955 701624981
    0x90406090f050d140a0816030605060f070b0112020f0928091209060e060a05040909050f0d050702030604030309020609030a060f0608070b22180f050f0f0609090709 72
    0x512090007078020344810413404144a20385014800740c868550008149640400b40390301d82d41354203000303400030350060100f9000641c110b000172818043d540c00f0b20000b40350080c00340303000b4043c2d6aaa1070841040c84248600290003082c501c01704140b81c10021812900010b0071454098103c1e241c4080050480c1a440c0c1d07901240c0d29141c041040c4550b03a1010150a0807500c1c262210303d04186004e000450409210740c0944000926a4102d900c244181e90240032850418480018581070084d51100342c00100c1c241806211040c441482c094012079072117943c0940030301031503540e03610181c0081c08a0401030380c0141c4104802c2c4603e41e02400741d203101a01c542c40004018080c04030501c211640c03500407042551111006010042900c41034860904414502c5801e4803501c8584005022140e8041c070390100c54038080300072031052500300e0707405401c243e00d04100c05ea40321481c1004200c8103940c0e880a0f11107510101e8864140b01440c160720440e810308480070960b0b0f803400741044524034034403c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 701627455 1250 701626205 701626213
    0x705010906091e0c06050309100906060302100f09032418050f07080714030319020a1104061d0a0e0f160f0807060e0120060f0a0c0e090406090f05 64
    0x1008001c04142c40c0f20482d00c075001c030022028500c0e52500c2e03004440e4013510040c00004000154203100411985084030403400d8240107980d0185440001f4040500049220301d0014009040d8680308642549102c05281d8464920901c1c0d5102e83c51020500c44034607007605410f80d0126070050b25401801d101c0340c00d84040c02c10282d068103100d800c0215003117807180250868001081105000546c0da07094420708000800d180c1c0b0640002450f500c41c0d400740c0a00c00c4200e20b100f0101a4021420042c2036002e02c0001d1003480f840030400003203a201d80644034018031007203ca148001c41021100e80c0c00300ca040030000c2c0c0c8600c80d882d00d1b49040e00c0c07214a0011035005490000b075141c9108103074801003040368801c032019828000103a071258070328001d110802900c01e22003e003981c03148080030400c40f04050701100f680440e040040e140c0f002195008071551656002c00c80d40c0308548900d000500f42a902c10145410300410800d003550054015180c0c16200c50651000c110b0f426485019188180c0c006c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 701628705 1250 701627455 701627471
    0x501200c010f0219180518103c0f0b0a030b03010b060415020715080a0b032802040e0706050304120309020a05010507020402120108071a0c10110705010906 68
    0x9103094410880c40c010030b0764014008414090700301c0301041c00c0e40701d030345c2030841c1060046840402c1c1d034011940150351161034a440c0d0881d0030768003007089006130030136081c0118a030b49855011428542450392194030490b04114100300f20f5a01304885643c01c207091814400d5030780c41e02504600107d540040100201c0020030f103088640611800001d031400b03400034014011100c000130b0b030318051841083d20740142072904000c20303882409a08044c0c084880c13103020142e0f45590060040804650300e220861800c014218140703000130311004804941d08001c0086a520020101e600c20203844c105c0e005502e440002284460030721003000600041d54034a62285000d040a900b20b042d12055001410710302101c04004d130b110705007041c060711400c0c244144d54201c41d10110f4001d100e00200c40300c80e024500c001060015010811000301d805492400110b040300624a000500c45e003004140e55a1151801400c8020182c01c041e40080260503500c0c280300c1c054076030b1400c1d00d10034242212459514000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 701629955 1250 701628705 701628727
    0x7360609050f0a050609090c1207030c20060c090310061d0f0408070b150619020c01050408031603020c03030a0906080124030504020406090603230d08040609050120 72
    0x24101408038203c4090603250f240070082030321307849884e00041c01000c86d030001800c1011518203d440001801940021510348048014010903494100000081d08484000c4280c1e160110484440200074050803482d15010360100c2d4941c040c20a031500340c015404d0b050254509482200002c14100203c15242c0004e02c400e07180d07502c0010720030280415904144000321300b034501a190001d50000001e01640c41e01801d41d40c142c0c000031030841e0301c16000503628104001041d0484100b181c29001c4800c0b0b0b00100005407010701031802075480d180d100f80030080f001c064000480314a5400b03030042d2884080d5810109007180e001c05580c8000c500c41c1081040390b160310003c001c0c010301200f140ba0f43e27421103401e03129982001c030021700e004140c6c44c4e10106d8150359880c1c0c0603400520380d8000411106943c1d160a400c0b284551640c1806040c8800d1961920440403800c10a00d406665039180203940d55a2a030000b410141015500c5640e901c9611454882c0303201441508154904c41070f46480017040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 701631205 1250 701629955 701629969
    0x302071508090f030c07120203030904020412060e03030c0a21020c15100e0c03150a090603020f03030301050d0201080903040e0a050603011805030322080a0f0908060736060905 77
    0x1040c14071391003007080c1c0c124260301040100641d40038540441a02d5800d000086c038501403802400d174064030005001400028030300003801300b188039090502204840441d01916401f04841003d0026010885207031054407401c4a03500c91a003618240b51034448919115089130801000c44140d81d01040c002040742001d0700c60301c0d038466510205620901d0400444140d20640078240701c1c0785810210200340c102c98012028a85c440024100c503600a41d1800001e01810a601c8143d0203560325136540640760401000b10ba0607980d020707000d201c40e030030306500441351a40300402a203420300013400701080c94045400c03042c0c043c80f5101d0010609041c00000c05007103030560000001484454581d200002d540030003580d0b0722242c0c8503840e55111074012480c8080ca40084001010703010300182090400360041e1581c01c0c070038140c0c1c0d105581281c0b150b01c200ea0780d03201a00c4040101e031208102000b90000c0c490900b1001041c0444c035400b40c82000c00707241d034211154001c032001ca00904e101b8040c50601c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 701632455 1250 701631205 701631223
    0xc0111160308010b03010501140a020c19090b090907121e0506070f03331802070311070602190c38131202040603021008150d031b030207150809 63
    0x58aa11719490b11001800581c0403070084014141c000c01c0c1c22001a000b80081b007081207010b40004100c14083c3c0e411081d50109028001207a071801c00d000100e401c1c20031001e440740c295103008082c41410900c4403051140401001c480c40a2249104a00c024a600010130709920404c01001e1a05040e10042c02c901903040c0e4410400d4a00b801894945001c201310780c038141d429085600400111048480c00c02c6547d411180d0203003698110080444640c2c4d00621840340070341d860080f0401d98940c2c0e82e840742500d105450040e070000d02030368544240c1007204103c2c14070841290710002c0d5540c0c410902c0072106100d00c591301202c028203c00c0ea2030000d0f500703c00141050105860701c04079010b180c0468086002c0c1a80d100700c810510030031500c1c4e5500090142d600101090303207282034484003d0500c0401c40756040381148045008180d810070002c8851016410788070032926604060184a481079000803e604500c107090000810007941801010401340560301c200340c600e806528907140281c14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 701633705 1250 701632455 701632469
    0x14031303060b012c150c0708250602030415030902040c0201050a0c030c1b020a08011b030c0c0c050f0a0f1401020c090103081204030210020a120b09010e0c0c011116030801 75
    0x14404d091030030400005000041e45045402a003100d070146000c144034014250252a0341c4035081010034a58000a104000c0c4480d160504112004034010400007544900c20500075900c1800103021030f9005203040c00100c456807134002100d5a154000400ba0b4200d02035100c0540d40d50000e004c02c0d0942802100c00b50b1013581070034030003400c4c14080102035500f403d01611544010304880350443d914610031400038081180244401a1b13110584008008130f001c50b40042840d00c2d9460241c28001c00e03144581c00e4022030f6400704030f40340000340180d070a000701c0d0142c1c0c05003010902140c01c0003001301c8540900441b07500c1c1c3c00c0303014840002903c1d01d403110600e1807044c0302c0d00d001080001c201c241240c0d2070048a49181c1d00b10340b282c1c40e007a8034000814005c401c03030030300101e1203403080c0380d0007800c0c0352160385012424801200c002050001c0c40c20207005491902132990001003150300032900800100030082c000040002c9020784d0008941c20075114030680490800d4544140340c0d11800c0d050251040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 701634955 1250 701633705 701633747
    0x1b0106061d010e0f040f0b09012c04050706032d0c11010204030c12030c050d0806040627020a050904050c03010905090303130209100302060a0c050d0306050d14031303060b01 76
    0x700d00010704d0700790003402143c46682c40e440d000c10251005d420091401802030800441941c5540391204040309421500b5801e443c42500000c4201390181c6d0a4011904400a02002410901c00300c010381094400401c1d11119061030b01406040703c48040201c00c00340d040015402c91012000300190030303c5015604582c018030080c000300324142001c8003110000941079425801d2850152400c0c42e1140d401790181c0640c000c50381c07880e5000a1b0f410b110780411601005015100c1400340e0095080c60702c5000001000303018611200e03400c0c0c0c01844500018203003541081c0d0401e00250a491040341c0314807610001000402850704180580d40d0440c03001d03000707182146419400d590b6290b858403000b0303102c0c0814601044040c001c07903103080040e40d0060480c40c0c4e40d00c412100034000c00c3c00c011080304c15116001035050b2041c464030071081600c500410001148005490f07903070441e10b4158006556001c1001041c01c0c0501c2802e1440c015881500007103660323036001001528000c90280525402d80d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 701636205 1250 701634955 701634977
    0xb040c0f08150c090411041401080601032901030e0d020a05101404060908271905030304060518090112030224010905040609080a0908120703141b0106061d01 69
    0xc000c24296102c0e0030070720f003641c840300b8403000100600002100d02003666800980806d59141046544102c4442a2600147d030f403900d02c011070854014162000803240525130b0740c40344881c80f000c40c0c01d44900503d004120000141001d0381411741508580c001341c0d119403100010024248a48038002c5041c540420803d403810842c40901c140050009009035501d04013801000104029540031075038002660b40c0180341225039003c900d00c5401000d206843c8904806104001c810b1010180c039006000b0358102031030140141d500d0781060103000304014100400d01c1054540c1d001240c020140c0000c0314602035080e00b00a4200044100e039002c0c0c0c48014813000154802d8503501c0390458014410000d20355a85d410f240c00200400c4000400c2c1000000e1220f40d25a8414038400964501805844c803091451101c03e80520400c2ea0045c04a0000c804001910210b10003400a6003404070040c808c00140f04805421240c0580100b00401e40c1d034141441000c00d031110b40702d50802c0c2070a204010070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 701637455 1250 701636205 701636233
    0x50c0a123b010809100507030504030e31091208061003150302212b022a0d05070303030c09050f01020a06050a0906050a0b01110d050a080705070b040c0f08 68
    0x2039081d401981031026203004114503103070801071a194124400410030081c10030450040151809a03800e40c0011058081008645800600c520240c2ca1505601032800c060004421a9001c03603103505622966840e40440840c1400b000300c1c12aa00c0350f83e40c12614a0311004101e0400c2d00040300504040c6031041a400c0c1c00d24042c0c03610b0a503038044900f40c110500448001032000c2000c11b098041d0300420b100582400514035800780c44050031f8044490b400c4249604907603c8400c1c0d8040d07a810b6070f54102c9501001c02c15005031844580107072031095007140c292581890580f4650045000036900d03125915400e60284442c006000704581c030120304c1c069040001d6940c2d410f0710b005801280c1e00c0c0081040d9400542c0318800c0c0030385c06442880240b40882c5a400207051382d904a40c080303507036144251600c05011810b90300b58100364a8540c00e15400000071180300400a03c007105100c0200040340200310b40480180c469071003001c40caa9228285420401851a80e40c0180e041e58004480b0034544 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 701638705 1250 701637455 701637557
    0x706061d07170a02040b1902010c051c020304020619020a0605130b06010f05090a23090408071103032a010c020706051803160f0303180e010501050c0a12 67
    0x90010302d512200591500b01c8120000e108660041000420014041e00546041d035111034180b100d6400070888030b002424160740c0e0f88a00141e80042150710b02d00d0042601c13842c0e01641d00315001510b03482c184140711410450006c420107010015904c030300303030070401c1001c0c0e4007070503501c450058a84032000805a860b11703080c06001c0d12940c18440603900188015205100384d48605030b004150710300c556a42d141d800e01900e00c1085218260410040d079160609100e048503000e1a84012803915000070b5494500200700c01320441c80e41808100488210007508650071440484400031190350b2503054142c0c10308407400d0603000015174000b035104004050300076007602c1e005a00104003800075690030001a0403c01040700c00cbe41880d94202010031103204880008080d284030f030711030010000315004882c6641d20f01d0b201702644013024400500c8070707500ca28003405c0011075030400c80b440407200741d8800d494035406040850024034128127003650050343c148250400b6074003944840a010599100c6a04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 701639955 1250 701638705 701638727
    0xc0c1f020405040c051312021804031710050415080c060706020f04091e1413050c0a15080a050c0706092306090c0d0203060601081b1c050106030b0108040b0a020f0706061d07 76
    0x9089271000013906240c0500828000b101d20105016494034000c0340460440389a0302030540550b1a119403880d001c8889880602a02c07511402003410316102c2007003000941c44000304a4209409104403440c04040c50040c00c0682000c80001c1500081d5245805ca49010040f0500d0b403941040c58446180c10141442074020098030782800080c120ba0038035510700440060456008400c200c00020200d80200100141d20348550710303105540c541081d4042500d02c00d84d84a00000810400d120003d034142d440000500d1240882c0c0c0030132800c8050317000180c1140302c000d00250300b1a000b0030200080c244074144015000304c0e94501542500d030003090380d403e00202005d050100040129201c14040241c20790403121841441d80d80d00c880c00c0741c103c40325041b000104001ca080c140041440d034001d008944040006a4500c042d560f20341e10f40000f203c40140c0142ca250790700f040019100d0300414000e115603402104003042c0245400e211420085034001c191254001110a2000c010b500c0004600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 701641205 1250 701639955 701639989
    0x3030f01090f06170a0c06170a02031801050403090f06020d170408160804050415050321040b0a030e060c16030e0102120318060c0c1f020405040c05131202 68
    0x1411a0704009100041100b500007002c401a002c0720040395904c00180e901c02c0c2031051500034442603548000f5201405030100c0a111702520380d000501c100c01960266030310180e0940c80304070680d5400245400c4a005030b8094000614a480c00d003e400d581d900500010306c20b0b4801040d40300014400140fa9a10542d68000142274079404502405116000e0300c0300d40484150011a40c1034900d000b0415621a11688d4086c0c2d06080d00a0a1642c1d0300507142c2c22100090081c2928903601c459840c1940061000e2070101c1c54148404211404180c000e428aa0b007680c500041001050810514290340244187c00065040007100c440740c180c0c80e005100c856041c00c1c0004003546180041c0d04204074840304034903000e004804c01220110740b521270010300c0c00745030540d04035440d40c04648101c1d10940d106100f5650206400707061403000d44001c1d41b044000d1810040c280354440b8005016101c441c0c1c4218002003020801c2d03240c2200049920004204007074604103000c0007980072404c44505403180d01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 701642455 1250 701641205 701641211
    0x309030325050303010611150412230f04090f0e150a06051507021206070914060d06060e0102060a0605100509130f020a0e06040806040206030c120a020702040e03030f0109 75
    0x40800c00d4541c0306a800c01e540310003903a81300c0d030715142e004244c030f030000c1d40451291080c1d43c0ca51490000070f91000d800355070410300461441040c58000d07104032103101c0075824503404440300e5114082041014020000f0b00120144d070311440c0040c44000d031004409030141da40e00c0c180740c40c80c00305000503401c045480e07001e401c500c1c0e41e500c00070010004c100d187c0c801504120342c1d000d20051110504011b0244038802c481c1401c6101044854a0b6074100444070000032400032801401451960880340c54440f00051800d0715144c1d02101000548401d076100700e0200c1c420140303560440d85c0612009502c1601a80d042100a14100c00078140c090301c002e850040c02000600d40c2807a403100307015000300504400b8140308108e05003402500950011180100080c0b0f200c002c0345882c50924200c038111200c00000b00f2445d2120740030082103500180c4841004142001030f08024035018202903c1940000340058980000e80144000d42e86014079000d0150001c10810014104000b100303815140345440c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 701643705 1250 701642455 701642497
    0x103060903090810091709093c0403261f080a110a0b0705060402040f020919080d2a0302031608070c0b0915070f0c030305091203090303 60
    0x42d0303680c00300368020030418001ca4982500342d8440390006110b40d4803505140510b03943c510f81c0400135000c4c400160b5031140000300030074001c11844690a031101164220707903180142c025800b81d80c50343d000f07600e2105031069008110078903801040006101111061060042e502d100703205450242c02841c9080343c0700110b0441c000400030003951800750040d041260144405410700d40160034000c98800c0c030800b0b0101c004101090110280c0e07821035071020081032142c42c2e42d4200310103840d02c0032541e5500c035428000c12031030340c0c0c0d6800892003110318071915a0b50303d800c0074502420704c0340481015040c021400207414801d4500c007a03040d12140c0d00c25070590800040d2408074203506c206400500380e40b581405803c28080ca0900034040680300c3d01c9146561a541c01c150b0340f0780d00030404804d901800c07001180807100301304401004180d215102041240005584011820410b500103800162000c42c41e69401d00b00126000f180410070f4000318103010030480029074034407410303040c910098028404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 701644955 1250 701643705 701643707
    0x1437050915010611061b04090b0f04140109050601050702090f090a0c060f02060603070e07140903060a0b031b0a050d060e120a0914060f0702121b0301150e0103060903 73
    0x442007080605880440c80c0d03595468004000b4101045403440c540a0300d000b00e508804010580c1d0171040442d440c603405c0c07034a007c0b9800d005003102c5103540d4000348841040e20140e40c49202e0841d1844045c11038150a5042000d81c00c2110b0004180c9414044100040f001507074680d244264440410714041c003c45d0b480505090500041c910300500c041842c60011407030503041001060800103a03422664990303900c204242e6034000f01d02c510041e1081000c042465548220091889074031860b412a10701030710600440c1c41e0450884504840d2640c1d201d038551185000d008441058000c04405e0115824900001d98064000e1043c0c40c802c0c07811312000400c006d296080207048828a0042e41e8001500803600c000c2036102101c5140014414607011421400340c040c00c10041d04040c1c0058103114100411029a0b881500181c2e44109a810346041c0c0a5082004101040c1c40748070b00c40710040104180741c00d566500034041c15584007a0070030b12004414100090440743c10842c041048000d80c10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 701646205 1250 701644955 701644963
    0x60f1d040203370b0a1203050a020f0703050109020f01030b0f06180301050f1e090c010c060f0213030c1409060f041b08091212040609020a0914370509 66
    0x400d43c2c81002d0440440140041c4459403501c854400c80400e02203c0700500030024512000c0c0075169601c0c6000400304013191041e000f4100d962403e004030b03444081060096442c0c10540d03441110b1341c0c0e4460702e240c021824002e21140d81d000080c00c0500c4007070103410001d02d1610003800c00c039029000100302030b01da034000c4402c8140404000750080007079082a08041c07951a008032480300c40840e0014a06203903a02e00785031103105091410241500d02050700045511080c120382c01d0b1000c1c7e80385c0c1c030444501143c40c030042030381e139441905101005265140140340003003030b54018001080005121078040e201c1404107503000c1c001710303200f80304800f211000500420101c04140071861501c4c00742e40065400c448082c0c05901404100c5103043d0f0f504000c0d003400d101d2142d01c00c81c50700001c00440d00060b41a0001401c84d0701c010110443c1d030fa04c1d146060119806014010b0b0030600c140c0c140700030202c00a2905c07a1200380c4e40ea0001420180c0000422402010f850b07020105a9031400a424854188 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 701647455 1250 701646205 701646241
    0xf0c050c100315091401060206060a0905100b040b09120705010509010c140a050304090f020301050d030f020a17090a0504050721060806181005061c05030f13060f1d040203 75
    0x20034040070b25884004c02001456a1001005641d0307240001081c0603000140d01da20910000b41a18000e0307041106a0000c0d01010340000c0800882020100307000d038405010304054502c06000310384a01c030322801c000c1c00000f0a46440a9504221028446a64442e08032012044c0a08000c05105000d107803480c2c00c40c0008000c503565008482c803440c1001008001041150113880080c0081200c52030080e040b0f100a20075207902ca8031004040c00041c0c01081a030310340500354019149050410b4442e94040345c5644101c603d01e03440020711020528040c00b80c04060002582d04001c1450100000381c90441c8410491b29815030300d8005103c1c050117600010082d00c00007054072542c2c02c0401340413200c159a81004250390240d0192650032001c5c600c0798501c01c1c10010030204214410300804402072880361419600e6000400c0821509081900108070109141c1c11401d04145400401000340c4440750b100002c100c05040c0d6100050004940c85e05110300c01c6030016603907159240c400182075904 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 701648705 1250 701647455 701647481
    0xc300309030a0303051e090607270e19050f070318080703021506040209010903230a0c050a0e0f070f050c01050a090c090e03030f04030903020d050d0f0c050c1003 71
    0x340c1c070b40800c059054000710b0040314070700902c00b02e0204040d8604816041181c0b00070307a9901c4100060442d03442180d00f1080326105103640303445a0316002d800500d5080319040703011080c1c040424040102500180300c191692034840400c05801e003c50242d01441c80641400205611075031000c042071109140010000d60082c0b205541e14141c0c54041e46840b1420420f19821481c000003130300314240380c003c032036190710141d65004100c5e0650391410b061400c42e403003a407030300706503003202d2420f1090402a03484038900501c00c0d0402c80e0315010030484100069000b400307144c0860814000d02e500b4401c2982e03003100c00c2e4100848400d5101c90101d0303450085940c400090b41c2050180210341803a40d200d4060320b40521850802aa00c400d0500142c580540c030100a81c1e2042002862202ea0140e109420512919001e50055a29000905850044103096070030f60440c031101e070121504100d0081a004042c01c100c030076080303181c4440c1c0c3c840c41400700c07050141503c2c01041c01e09504c2544001c81900d08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 701649955 1250 701648705 701648713
    0x203031209101d030915041205070503010b03011b050c1f15050907020304060c0501021e030a1b0c030309060f020a0302040302280510030e060c07050c30030903 70
    0x8000078050342c80404500429401e8500f4400000c20150481d60104180d00d90004525058000007440030208a0200ca0a03603c042400007140401d0064000d40001d030103400140403c504103000c2500b1034001c0140d031482a0b15013840100d88100303440042801c68401c0c20566190300c44100100d050042c01c05d142d103014180022095240501c69001000d060901c0c0081c00d05103031660107100c40180180d038881c016a1080c0020032030345115541c3c0411051044001500300001c0c1703a0041210003110340e6801600c03101000f08054003000f8840c03180701249040880c95045480240542007050008000e4201030701e40003d1002d001040d0007951b840702855200315030b0785140d034034000d00a400600049101c1c4c0850b105106411030f201a80007d140c006041c6501410310b4403040000b0069003101c0c0b40d05258031040c0b1019100001d011a030b1150038100009a03075440b2514109041c60740c4080007600c40c030004241c074442c803924400c2d03a15541802041e000c6501160301c4105166000344090705a1600c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 701651205 1250 701649955 701649961
    0x902240705030721090311060c0a05070b07031404030f0b06180f10142107080604030c0b0a05040f1e0209010815090619090f02040510030302211602030312 68
    0x84e0390000940c11001d5442481c80001d41002164009418800034005e0114814800c030700346011001002a640f4280450b400b041943c0d50702c3c0e0801c1705c40c2d804550f07070f52400700d410000d05400c1043d00e10685e030f8a40941e4907007401c43d542c10102d210345d403001800c608600d800140c40b9444190f10390120441850f90b0f106546000f03403006090031000c4402205104514100080302c4003c030b000020080c100410804800c02140c034107030170101da0000049428800c501002811a509028990095000b80d03131f4000c01400e94281004600e4001c1c00000001e45040200008a4004400440d1280d44002d4001c1042e010020f10780074404900fa010f98054081c0d800040c40c0309000030080780c526056004200d00d5500e0115013621540e0446555403050110a030100c103100065000c045014032601041e00000700139000f04e4100c0d20201c4808015088000040c8103154042004014040e008420071060f86580c060200321030240000d000718200e00e01c5070a00844d9014415112104070350058941185 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 701652455 1250 701651205 701651213
    0xc0609020105210a0b0f240f04090c0306122303270f010804031b08040f0b0901030f1505090c070b0405030318151501020c040614090a09022407050307 66
    0x2480540d4100e81c540c1c90b10700035055034107090380c01c6804284010190f15184e11115044040c00011203040750007c0e8041041c40784014690001e00060080e00d40e00081d6582c12045c050b0840e0329542003021001d050210020002d841c4400405000ca17a2140081400d004100c82d6483d40c0030743c10b0955548071449000d404100d1242d400c20654000864030640420071290040d00c0707052090b200500004c2c000e10040d142c045807d11800c01e818800c443c1103280075900d00c2081d01d450300c90341000c000b00800280c0c00c000b5680c540104840003001441c10091601034501c26a0950002e2151a010b4100c50300060264230b079002c20b8a8600d40c00400102d0145402d28003507443c2e520480304c580381d00003410191000968001062948451100075070748090300c41d41f00803c40c807078a80070301c2411841224506443c5450301e004d0305009150401d82c0400510440041184820000b02144002481d01c511100940e551491085542d42100048034a0740303920800d60401d0301c2060800740040c440080c0483c00c00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 701653705 1250 701652455 701652517
    0x30301030818450105030304300305031e01140d02120102070318081c0e122e091109042a03030f020303070e09060627100f0c0609020105 60
    0x40400004441e0341c1140503940f0700303030b450203010b00c40e05a401400305102090200c46902c0d101c2c000e501c00c22980310b502c401c0107025451515021030000310301005018032500700403c06142d0002001c00c0d00c4840d0f041c90500d20044843c1c40c0800e2252000803d14425502c130300c66513181c101c59400c000d65035403456050143c0700c01c142644104040101d11000a002a40810080e41c2c2d080d18003203004c441c101a11046442c6802461340a40c003072001425040c5080e820084440c0482c3c1d261003800100b400c10001c0050038071292100e129540c00c1c5404040010380e4a01c80b14504001151051141c0e199424002a0074419900740c030300c180d040850201551a0706d02c201c030300302da00c25952a550301c41c803540101c0c0c8030300042c1c07245404548500c6902c92146050441d095000c070006e0a19400e00d02041c501140007882040d00c501c40340009100c45500303003410500016030003140d051030b04c160807800800804007490705202801542c0d03250726885c2168801c0044070801c0040c0b04540d440c58889003400c20700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 701654955 1250 701653705 701653789
    0xc010e060d150902090f0907020613060f0911040f1103010302130e06010603150b0702130504080d15080d1e0f0207050d11040b0111031803010207060e0a0c08030301030818 75
    0x210f0b01c0409001003c2d0700e0102c41c2144a23080c950f002c5c204030b0b25070828048494260a4080310410340380e081c0c00c2003c051350701c0b1381000140180d034608880342c4003c0902c011103c2202c04540d0203420a550001141c406204582c1102e905643d100000305056410100901290785060241c3c01514000141258180c0101c005007070115403130340000d030f550345540d0240c0c410210000d4022480317403940184400c0650003681e00c41d0186000d245000b003160071110864182403040c40101600d86028040e401080103190401d00e543c3c1460410304079051000114101c05520101c10004401c510346400c1e0306c240312010050402410309a0744450528001180808a0410300d000d01d15101c0b120b080c640c4078004500c2c006011101a41c80c06000007452850b500e0505100c0e43c141d9002c11400e000244036210710180510000003a00042180345090890070100d640001000c2e40300748010b0000c200310008175540b0505208080c60000b09010108076403402a48440600d0442c91880221030f0012038400c2d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 701656205 1250 701654955 701654959
    0x120f030309070b090916110d1d030c010503130c080307060905010f060b0d180b0c0702011d06030f1905010b09040c05040e041e080307021e0c010e060d15090209 70
    0x40d502c0c0e00f6050080e000d03906002d80d00511210200e6188440041e044030081003d141ca080030070020480b00e031900f070a044c41c030400544060b80601101c202d03105a1000520210050700801501000090081c00058069404544640e0740c020800c4500d640b080010404001920740722400c0381004801000946802d5842c0e500384014001c0d4940e80f071003201d050380c1c2040413031410003031510448070041550000c0802c040001c4903030240414100040380703114000c2d281405039100503901c001440c0d54202e03080011036110408004230300307664100a413544000700324180f000b544e42d138440340348040180c4040c0701a00e514100021a48428030303c010304080409880522141c00d0210b030481b62840741c0c0c41000c100c10105c030003140010b601e4140c54007050300301841000c0c0e411001c0d21284840e9000743c900074050b920400e8042141d00c0702c8818020840031071805000f030060403600103890586815030a034442d00c00014032030000c2c2150380c00301464112114002c000c06403104c0c2d8250003948004802c40c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 701657455 1250 701656205 701656213
    0xd0b0c030a060806070c15060e10080d171303030902040f05040302010605190905060d140307061d030d0b01030e0d03050105120a15050405030f030403050a0e040b010f0c02120f030309 80
    0x301e14480c0004004d405400680e480491103042a218240c2049442d103204640301c0d1203c40000b80d48801c01401401202c0050054104ca807601c2d000910b00020b81541c0e030180008440c00c80321425100b221030b40c2c0300c248800800d49490301803034210024042803000a500925011030f007000c3e080c25900c06841544660001c000907030720f500402c0580c0501c045111805441580c080c006401c1d150082d681200002c1c2c03400495064035a00c030484c800e000d48201c1029803000c41d0300c0041c4041801031003000100704001c5030800c4407551085071a440b0316400030b4000760700c0c1e03000c2d4541e5074800e03401804840c294034192562414030010040140c035080c85454440c000030540d01140c040c0118520302c0c0d190740001e0300c0007a141c0ba042500003a0030300410641d081d020611014100410b0800218800e40c442d54503140d0b01d803900c3c4005400c3e400f0801040b4011480c1c4000c0030070b5039030040a039041c0301c4a80c0c24007000d112000e10014050203014040c2d00b00b80c1c0034410915000b5a40000554024140c140541f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 701658705 1250 701657455 701657459
    0x50c0310091107030c050f060f04050c0a03020a09020903070321030e0c011b17071208090a0c0b07020609150301080d020303090c1002030d052a0c0d05090d0b0c030a06 73
    0x7000c2900c4400100c2c00d01e80c03004024800c0000c3c0500d4803a60014800c50548030f07400c45071024907091180466000c1c12407a40c01040004101c070920101e191410101c0351b581a940c11500450880d60184c00303140034195000500898980d01005480002c560000441c903400c1c5221003201c40b110124101580440d090034808440d480000c1504444000180c1d17078401c1d52810503200601c080d0580500707464018500c044003650302d17891001000e4039030007686220000d0011080040104200a2100b601600701030451000150340d03002000483c0c526019840d201c007868000204984101441c00d644840d070448150003100e42c82c40594129031108043d80c804146812003aa22440120350031071807a000b104416010b8a041780548185040a10440c0c0c20401511446400c581040d600b1380481d50640c000c414010f50001054036000030050700841c03c0c0008a64407543e07a881880280060100128113071005403101d524215660341c008048010f40c1c18903040c0b039900341d40141c902803186030a041c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 701659955 1250 701658705 701658719
    0xf171008010c030908072603090d08010e10060f030f0204120501180b0606070f2f0d0b010e07050c100614041407030e190c09051f03060c12050c0310 65
    0x134411042ea0003048161904070710b82d44904580440c40010200c0d054140d40d500c3c00903450801035441507d07010000d000d01d03e1011005041100140d0102ca62480507900308000515020000c00032140c150a005954584c41c0708141c001c0c0020021083d11507101090000340200c11f02180402c050044008005983c0c1902d6110a103c0c8500000f82810408901140c01410301400916105000d4040000c1001c6140da80000104011004442081e00b451800c1e610086d0b039452840004012250717000c0d00c102030740e11006e4409052040b441c8002d071a000280b0014015401c41c0c901c0d440c0c00080d90310802d581c01c04140101a24000c41585010030000101181000d1003400456169905112026590480110007038030103014500030303d010b465a034400d50a414072182035054410390100800343c4c1040d0f0a50304450006141c0032903900f88006a81380702c1191005038094079000f070310204041d41c50100540707540704d030200c07a664224944000c00480c0400a400b65001b080c4001072022070580e2040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 701661205 1250 701659955 701659961
    0xf060905031509010902060304080d05070e010c1407080601061e0e0603040f14030a030204090f05060d03050325030e250b0717030928050307030f171008010c03 70
    0x80c107500340c1d110445182c40303200c2c24002c86500624400005c11041a1503020681d1038005a601700c8004202041c018a00f841c03c2c010715038055007500d460503442c502d01000904001d09044042d040c002010095a11514140031400203041141c08542140d6522000101140158407002c20744890080c0f088100521550030401c002d40000c04043c1140c496454190b00c0d03c007000001c880c44414841d400140300c1c024030203040700031815100180c031585401450019526a24240711805141c4810024580e444200c5200c009401d454201e851390b40780b05402980034029a4a01c20741009059020010cd506800050600d21802c00f0fa84034030020f444d005542c03400c80d800180c07110807a600c080c8401c0c80400c0203405114020700c07242c03040d54503a01e00722075954400d442c0703803400f41c129828107101d140b03c0000369455080c5602034075a80200703035103a1644034000c0341001010001819400c2501a124000c144146a404402c5200c2d5082500c07000501c4035661054105550a0a4504010501070300c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 701662455 1250 701661205 701661209
    0x40c0f0b03010b030c1b03040503071205061303181e06030e0d08060a030c0308040504140727030210080f10060203031f0b0301030303061d070203120417130f0609 71
    0x2100c0c581035034200485480150070042550b0030b8a101400022001d0802d03607400d1040500c00005540d6490030305040c14100b032030940044031640e0001c0090000035800154040e448150074024401000c910f1504031a00f41c4550b40d11500d202503c980818242c0c00c1030403074820341700d105608114445c2c0e00e50003501a550705030418041e581001c80c413100ea4030700410b000c1e036002a004112500c078035107956803900d41e500c85070010f4400e940017240620050030517125a4404103101c41100b41c8174680180001d007424404c2c2480d200244400c0140b61503044609090409964003c0c985e40413344151030041c00103008944440401c550240404c0114419011600644546501442c43c40c3d840003082500149290403a84059102440c0000c2c03851219000d94042c520a54000c500140382c0b810076102c0f94001124000c0c0c0b40c40c14000d0003005038000045400c5030240f039203c100c03142d8560900c0c03007504c070100b950005c0c3c1d190002240300710b154461075480306076090255098080c0c3d448010032600c0d941c040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 701663705 1250 701662455 701662469
    0x90c0102060a1a1203040902070b06030106080307170d1b05220f0b0c0a0812090c090f0403030515120c01080f0702030306091f0311011d09060d05070518040c0f 70
    0x4507203e4080c2407140b000c550011540084030f00d4280e4424602041b0790008000b42c804001680a0190514080c001d000040622400850420029850304280ca8507e10a000a01d58000038400a4002280c01100001d440800301404402c40c020019046900100d4a8070080000c0344a0f800b1185d009030703a501c20f8424181c140c1d41c40c581042c800c45420340c0040343d109507600c145515240041ca5180040401d40304020014959081608540b40750900100c0c54a10070a8a4400c220090000c1c3d010540d00c145c00d45408181515081c01600035010141401a04401c8202202d40c6c3c280d0000ba6407522000c00381d0340e8284556802d41c00d00101036060b0381071301c0141c00400110700d80c0d1906040300c58004c402042c40d800107451040314401d14070001e07481262014400120050607603004803d041940380c01e034082051091a000004281d0000100003510440c864645041440b46c00c02a0301c0150102500c181d509a80d00c0c143d003070703034000c040340c3c116038900103403001003103202c5260890710440e510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 701664955 1250 701663705 701663741
    0x30b011706101b0c0509090d021b0d020a0801020301050118120f050f01050708180f061b120a15050a1a0904181a0106140d0203060a0509090c0102060a 66
    0x5510811044000c052684010090740010740c040c03d848104181071a03500c540341c0b8141d401e01d0002030080585008201c203035070b904118070b290711443d0042100401c01c0317094400c1d1030920301c505001400d1820b001001940203e1052004240c0d44415801941070b00d4098907800c01059114100000079003050140c0000003c01c0e482071000035550014801003540718005480250098034486821034404854410020303120300b00b030200520109410f41102d40d242005041203007809030900d0f54031100505101e440480d4440c004910892410582e0040643d100c44a1081d0603c0032440c0040d02c1c0f40e440f1201011005000091580f90000c034040440398403080e400194a02128406050740000c60300741d811540764030301d4402d00305429201c6501c50341300b680c8458020030030b4000c122024005800190521031a8011b08944d020040256083c0480310340c4050b0707581e0746950100e502ca13181c46d40321036000740c0e00b6014059414030202d41000c1d200310a030300701c0d000c40d984e03110240180c503401d00181c0e0302910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 701666205 1250 701664955 701664961
    0x115140a0b0d180f03030504120c0b0411011e031d061b0d0f0e060f0f060f060d1b0f02010c020307081c0902060307020d020c060309071e080a0b07030b0117 68
    0x80303a600425418281e82c03c126030700303d0040d180c503406040701c240c04800003541c68003040100074005108001c011b0003442c000c81103040d030341d0780c2c071064180240002d804100311200c078109507846025010034032b6032041c0070035114103c83d400180180420507017107001c00d595100303008083c0d0400a001c80c89115080030642c01d13a400c01804010650144181c00351098807510902051805401075150b40720b003882c01002c541c80d000e640d0042c4540b02920a5540149040034040b450391001500251440110713a07040d901d5801e495400014107000c0100090113441c14621405039810010881d84001356800034045500942d4040703840b071098030402001810180220126062100c002e55884030165400151604481c0c0008a660300b08507580f400583c000e50503000f0165043c0300180785a4801d4079100d0071030419080315500c0c7da1840c041c01441c00c5684612022581d04185204010010001500d0f08101c6a0401100503142140c1050210b4104116294154400c910030740c80e00b012150b40115a031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 701667455 1250 701666205 701666227
    0x4060503040c0e01062a030801050609060702030105010308130b03190915150f080703020d0209060d1e0b0906040f0605070507020a080106050a12050a0b04140115140a0b 74
    0x50000341081d20b00300c001000101e050819014042d018000300e84030407000400440f81030712501c403080e0b040c074a03480f6811180b42c0000d0b00501c1c0315041d1407044541d641c5406640011aa80e40107010001c3d5140d130820b0000018444800010a201185088075032016600c0b420b800c2003a200640345452620380c24001c070400c10445a000b103000d544681102c1083c0c00c00104940f040d030340d00c1c3c518079180841c1c046041084100d400c224000a20000c4080e0154520310340029840c1c11461401900920307204001600c0d6640d00c90b5104501c903440216000c0154054441d24040b603690740d030032501650010042403401800050f40c0f132003241e02c5a004e043c4041c16980d1080a440081c0042045c04800d010745070051f9200c81c49500501005c4000042d994030b80b004000d1400303241d40c00b10103550319200001700410004103150306002d400c00150a04d684403450048048068140c07400010b51070110b0507620803544880f10001c494000c8001d003481e0741e5000801c402c195603449058034a52040002c1a002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 701668705 1250 701667455 701667457
    0x906160309060e0d020c030a0c091503020d0f02040522320a0b0a0504080d1509180605060909070905100801020a020304081b0d140a05010609150b0a05040605 69
    0x41002440c01080044899882e0700682c0d5125051000e550025594114029410032420484044c00c030018409601c1c0d9840706070b00401c0c58082d0f806c505840b081c01c0b001c1c0d03102c4200c1041c02154060440d100816040c28001c3c42280c0c010b200300c0c411410080400c42c118803403000c445034090480b103100c2055000303681c0d0846d034803900e8031340d15400c1442241e412052071000e940c40034500c000da40a0240c6112502c0d00d030625040092900200615080c14040860007950a481c0c00d60708580000a0b003500d003038514072262030123a01c46030040f41015403500110132060180749406100380401c5c0a6174541c0d1081116139003003221800e085903c40c1d4010007040542c0d40100340c1205111842c18503168641035450b00303a0340074030307900c40240e800040d0400c4480c0042001041400c0b80d41e404420781d495090000d01c00d050300500c003800d821700c505c0d00c1c15501c450074485400c52950040007040170740e568100f003101500300d9050b00d507880c074419080000c0700750b00e82c4211690400641c1d916881c0c07a0030208103a5031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 701669955 1250 701668705 701668741
    0x1b0e0105091201050702100e03131a0405040203180c041a04020a14070b040b0106110a0b06011209051c0e0f091b030a050a110a020a0201270b0a02150906 67
    0x80071201e0b001e070740385000081c450715019132295409442c59801c0541300c0815138501d090341e0112540100400c0007220a1513090340159903040816050031100d140ca000d03454041e90300000d5100780300009006821144400308a14410b4a2041e9144c2e104c1c0841040200d9091000d5071038034805035420340340240b403e940100500102030525090740c3c2d50310b03034454901e034000010498001c040d0409001c10301c1210b940741c1e17004150350b160216121846c60300305da4884400f05401091283c1c050080750700c40c2e001d0411044110140d0390100301e01c500303030704155940e01e0244141022408551881d00300d154499400940030f50406441c1802c009000f2040c00000000144000007410040c03401031740b0404450f00030340c002c0301c0309840410181010081da904841c441c88a07040e0031007041201d072140c2d60700401c5001c000f80c0c09007000014560465001070b40ea01d02200c03019004600c211010a5209005003c1c2400380c10742d5017141e401480c2442c1b10008490701740d644001d25801f080010308441519140409 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 701671205 1250 701669955 701669959
    0x33a020c1002160b1b0d09060e0a0c0f0603151701020f0a030203010e15030a060f020405130501090c0c1505041b060f11060114011803140a03031b0e010509 68
    0x3485101c80300110080741c00000d40c1600e021250040141880700d9000c01e140c02c48034000c107844100c04212201e00c01e902c9007034590005d4a45a01491050109507880507800702415019144d5168103440d00242c6d000d41030042040d10102070b0000301d03d05100c1c0c811017850043c0c820300201400c0c20900c4000b440a4039001a03a1150740800c01c1c0c10b50f205000c4094182e12003d41c80141c1c030395060101c80700071311000030403e912141c10618841001d540001c0d20414964001c4800107508055a0a00f0040d00c2141c02141d0400b280614100700d214990344a02d0480c0c5240604000020b01140708894000c0106000fa082601039200c0000c04107040c1c0c080c0703030020300c01c0c020221900034102003c01001c0c8254000d01c04112204619052140c010400504408006000e082c882d810010f42082c081c49050002e8100700e040c05513a000c51103404c0c00300000e9904110703060420030014182d6960744035031349421070011b030804400191008151201c1200306002c5c1d21900c460796150801101c00d40c1254100c07075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 701672455 1250 701671205 701671213
    0x301090203031606060e071d01090f0618080c03120a02010b2d03010509190318030606060906020d080c0d09020931023f033a020c 57
    0x6035002c10080c0014103001e8643e01490710b8608060046a03055070045010050010400c41420752040c1269200b0144440144d074196074000101d560341065081030690350107808012130030a8200303900c507410111041c00069269122024a6121000da11700c564165000c0e485840040120002070060681d90741b000281d0202502c00103a2880f2001420039031000710850062891001d555a800368454240c00a00c080e040c50f000041ea9007030707684450001c07846015104410180b003100064401c408406e24036030316984904201c0024640780c822900482c100c618006052400811500014032807520794120700e0f1f641104d5528181d1001464040d000d984140700720059840350021402410045151480702c1c005034210715048441600710f028901415900b800141e60350005581c1c4400c080090400181d111350507803091401c4a8400a00049065100c0d50540f5000000c1e000d80c900c01c00f421502c01c2c202e0400c1c4507a9075494001a1085040b5603903000031704600b50020b046041f0b48000710327 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 701673705 1250 701672455 701672471
    0x809030c010614130504150203090a1403040e180703030518060a090501020d18181d011401060903120f140408060615121609050406060e0102100209030703110301 71
    0x941c00c41d20140c111401c90606411214640d090000904040811620041201c3d050607241c440d100741100c0e0030b105480b900080055820b4400b8003120340c5030356001481c0840c121801500580b00e404c54052202c0056000000031308402415207095091902c141c00b4200d000e0468038212988d40c00920035220007190001c113084c858862000078802d040590f6510f402050410000908080080100608010140381206811118402444100c030740d01d090001d841010084224041c100200b489200510804c0c05092500010f403c51101e1403000210340c882c3d0ba8803440c003a5598401c0e400702502d101c0540342c1c02450707103020b4140213210074414100009103001d607801c403144587c451b400c1078400da00800140302e001c1c200681d8100d0740005c0440c403142003481c00c02c2d8140808400804002c1c03580404290540814091500b8002404010f4428803280c3d45841c0007810394618442d90310300621034250341600512803842034401c0c4c4100240500405d0f4a541c03155020407406000e001d5040d540e46c000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 701674955 1250 701673705 701673727
    0x1c090e15060a12090b070507110f060d090203010906151802030c1218030c0c03012313060213060903021804110105091f0e01020d050301270e07090e010b03120901080903 74
    0x91301b48a80e401e0380e0380c559102c0b07003031078400303406610b1690b214011101e50380e07003046960760751094484008001400050700310160000034007414118034003a0180d0700d86941c0b0810381c80000d114105a07495190a16135420300b16640e4812440110368100e811707402031200a0b80380c80383c428002e8000c00302002c07601c00448180d00d9641168003010030182103500011040e01e0b86c0c03d0030701403d041400d000340c03101a066808450359031061002840c8407050a01d00d069481000050f40c1510070440f10241418503594441c0c40c003a1010000d0701060b8847c4500895010200701074039002440350780c0c40104a40e00c20b88020040d1820703086940310b41e0703105418162090a01b042905505501807035640d8451548013484000380c1441c10510001c4100042080140007104000302460f4a0098041482104045002c0600c00a00024000300d10500904800040c0006c258201c0d001d0001203200811511085d141010f54803a0540340255400d841444100420760007051403d500c80d100409482c641200860 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 701676205 1250 701674955 701674973
    0x5010507030c02010608071527030506040c050409020a050f1201090c0512030406021c0c080c0a0303061710091b0b030f0c12181c090e15060a1209 64
    0x6000d0001907601d48142d0206036090061000a200340f00c050b00c40c15040c4245983d66900742c800c694280520201e0084401c801a411044010311809410061a4981c604661650300942c1e00b0b03151103084140c042441d1070f15220b5500d08a9009000700c085a15040510800b11410700085500540c08c0c2d14807401440e080c0160170340140304070708800c0d4031810801003084007000d4a8031502d07181d006200c20700a0303a400046c0002c503c4284810030103204a008c1c002c03510919050700050880d940410304050300d0f40005280300803548a600c040c0400c0b030f2210549800600268010016584030b401c42c001001481d0b0b1001d001d50f400340c05002ca4045113524030700041c0440360f000e0a1a401c00008000b07803080400d550390307080f4911040342441d041c00038400b01d1810b00e01a1406000c030500c00e05400d410002041210780c1031002c400611440e83e0421000341142241d881210081d03850700e000501d9091070601d82449071907004001070b00b0016803101c112000c1d4007141d0000440c90f5181802c00115840348 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 701677455 1250 701676205 701676211
    0x905010e0f010509040204030c0806091501210c0b1902030c1005060a090c05072d0b060a0e09030d0e010c0c08031317030612060105010f0f1e0c12080103020105070809030307050105 79
    0x2a41401c40d640b0b810781c42b6151000c02802403860350041d80c0c0340b40c00d1109400c403150440d10402d648a00303602220075000c0b03882640000061000300c0040000405c40e0391707100030708050032042809040d40310000501380c0c2c0364880d011801500390011100e02c484074079140c2c001c980040004d00507507a215203036100d0782c1c00c03119400c4941c5d0101e42d000c5009420445550400585181c050012000c9107031505d1b4440c0702040c0360400100302c410001c00041d0b481d1110344109005016400318040316040c4100025101d5004181c0f060401c1c2c10554107090854050046031001205641c61568007400c0e038640d80503c0c3c00240070201c00303104540e0240d01241c02d5003480c40241081c0b60306640c2c4c905182c0208065040b403490342d803450340c10000040109a81124130031501d4103141c2004141e11540c9102121301ea0300c1c0c5c0580d02c40700c41ca086c0c1f03200310f0b0300d0b4041301203850a4402c40c1c040060800d010b1080d560706909201c02400146c00300404800a10b4000244c04580301c080e00712401c2024650b51242517840031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 701678705 1250 701677455 701677463
    0x308190e042a09050a12031e081801020c10020a050409020d0c030b04200c030405180403081f06050f0408030706050907060f0212090a210605070905010e0f01050904020403 75
    0x180541d40e0500744600c403000304900c09040c1104014581800300d00340005c4c4c0d00c24030b0500c0d0303003118015090600843c4126801800c004522064040215001c1c21046041d90307041c69a0540546645c3d500605100f110042c4000380000c000403060802000080c0d800403e01707108108080c000003460480e01d0010704080c0e404108045083c07088484000d0403100c079207800d80d11a0381007800281300700802e402c80705152007c00c1200c5950741c1ca854251807440c440d40e8400b507042030b41e84d01c020007034480401123607000e544a640c0e046484d4541644000c010300b8a07012601180c6411902046032a000700000c100004044805d9424295900502c03800c44d002440e090341c1140d2580100b0110103414007102c80507207494282429180015400255940c0041614481e1031000052248207669844685401415502c40c40d008070541000301c0e203030441d03501070111083c4e41088045102140100034400c1034500681d02c1c82d401c10400030420082c120002d030914180007081209907481d4490340014030142d802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 701679955 1250 701678705 701678741
    0x80f01060e070507110f0a05030f0303060405073006180c030b031630030507050f150604150509010b040302030609010203010302012c03030d06030311070308190e04 72
    0x260800304030992400601c11020068108400c800103020310300024171010b4207544560020b00b090000c01c1d15840f1640009600d446494102c0500c40d00c008020741c814801a50240469200c42c1c4050310900348560520384450070600c03205050500c0303607040c2080e0790030314680400c160342c0c1c407281c0d000582c42100040c00f80d239444405a000c400e40500805140342410780080010a45410001c41c24003102d0084500100c40d1012560700401082121800c0c1c2e5004034100400e09058070b00900b0b998416442101c2e903001d83c415030013201e400410760703821744070300e91080202d26600c072020000107204044110660308400e4001140b00e884800e00580680007107401c842da194210300405140040003000c188450780100300600050740d00002c410750480d84100135503070007804c448403031100c13510704910036401d48008145800210616003050f02280d0181c1c07207a180d103464210141c1e072240810300003e0014002088076892600c0b41400480840c00c691404844210342030300018140c0b50401c103c0d001c2501 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 701681205 1250 701679955 701679959
    0x1401050d08390d0206071d030f030d0c081003081e130b1321020d051060120f030207061b060230070207080f0303130c080f0106 56
    0x10b020012025204500c1c0000e1030a0315040c0f4008180410005001c1181c40300136a0403c016241000700c46085491081901d486640312200c482c02803506d883d5000000c0d9058000c03403025243c0c3c0303800106807600000341078601030350710540d401c0d1320300401d0304c0743c1034580308002c824401045000100050030500048607602c040c000380b5444908a140c00036154000000c03203d00c0b448240000f200c08081d419a81603290800310b04120f03042445541c031540166041084002034100000e4480c0385030036102601e034640203421100081c0441003040700b910a1071500e2103030410718403840008111120310408a4000340d840c1c0c200c0303030090070403000d0841b1001000c000d210101501417140001400c41480c4c00d00400b40d031440e5034003c202200790040d11041e400104180a801c40160840e01794840d04207041000d45075608841504404413106001402020008150004003044a0f00d11060601c021419925595624912644600d808480c04400480001005c20b01400300c08110f0940c1000010310034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 701682455 1250 701681205 701681317
    0x806190803032701060509060f04020c10020307020d0c050d0305090718090b06040e1207060605040612020307050603100911070b040c1a0a05040303050307030e03040b0d1401050d08 79
    0x3034018105209906010301800b003500e47c1d40c1c00603030040302140e0282e200c252100210b4000e22402c1c800003010700500c0201e84c410308040d00210300613030095084509038404c401d4107d4081c1c0c414040149240c0064082d50a46440f035000f6a803c00261401e8030300c9596103034000d03d02c2d03c00080c3d0540f00f5944440500c000d11600010480d8890030035981480004072410144e41c8458880c540c404540002240940c1400341d10360010740500b0002d0410012191110501c602420005200301d10a1181c1000420b940c00d081d0242c0340903841d00c85201c01001e040856450103401c003648206940c81081c421080451500c2c00018004d41c0901006103815082104c6c030713998140c401c03c0c50000c4030400c20024907040e51280458040700d4152804a0303ea4580f6802140a0b00080e01040320b02c0c030001ca000304910f04030000602c3c0b162040f030720030491000b403007000c6000010b091081c50b60100401211070041441c4c1d80050940c4d001418240040507001d51100504060b0005107544180e103e1030078072500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 701683705 1250 701682455 701682511
    0xa12020a022a060418020702030114010305160503030301090e0f010914070b0f1206011e030c020d02063702030c04060e090405070923010e06040c090303080619080303 73
    0x1640c100d00b122441c15000502141c1c252150740310f00d40308090301d18a2201c04201e40d034155250141e00500a0011030002e00c82560948002c4c0019101405054040038000d003058548804031a0b01034060744c1513a10300343c80100109000080c1801c80d015950500302050000c2c41007200d01441030b5541c800020301908143d2501019400000d110308041015511114058060b03407100c40c3c4018010301030f43e403450012942011a4402c050b81d00d034040141e91000c03505500301d00d1a01e109542100c3e10f84140250880e0345400684210018141e1112621640740c132100c21700d81e440300100724031404007108004c3c0c08200e9004a80c9005900d1001c142402826446000d1034852141242e03803110901341903e41607118040c5229060b8030700d94540d0040d14100780c080c60504540d40210081401e5a940e250416040600700c480d1403180c0c0c030b420340d54000c0d1030150300c200d415250980c1c1c0781c08059548600317006803200c2d514039807038030040038490004403048100011446000c600e1036810610b803d02d03581d0000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 701684955 1250 701683705 701683753
    0x922050a0b091e0c12090607030b010c031418030a050705180f18071503060905100815060109090603150522020103200301030c18200a12020a02 63
    0x2c0352801c1024031154014400b007280e0101d4442c280182540c43d401c20043c0f1900c078000070b5850500c0e0450420448401c0442e4051003000300b91014027800c4441d10044900d850206001404070f0001d44a03030740c207141d0000141070021000080d074480c5218840000303150a5240000700d503598041c2d5024041820065494000f00c440761450b000c076810110013000d0f42d030030300420329403d03000c285084070954a000c01c03040300200000f0051640010b07868000501a01c135500a00d65401d0130040413a01c61503919443c402225502c2c005030148500d0307a2248400341201030310050401800c000045004003c0d842203200a5104041c4042c4488510500005440c4018000075802529482414601386004000148203609180006641c1d6584101c0c1c0e848400901c0340d210f100f4004000801044032125a41c42610a071004a1004d5854401d800094404110700e400c20312142199100b00d140b0068080d0070041c00d2420b01105901d90040c08000701c0c0c100e18843d400682c00807004946d034a002800340c401d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 701686205 1250 701684955 701684959
    0xf04051203070c0906141c02090a0f05250f020a05030406030204170604080d150b120603060f060307050f030c031015290f120106091701021204080922050a0b 69
    0x45d580790031104500389003c149890b010ba0031207000b01403007250403018400700c20750080209007642400c560040040c0b4455441c0704800d8500404038480c1895600ca0f0f4502c0080007042c02107188100e00b040350000e800c00811015449614100300028800340301410151401d030f038005031100c0c9081200040c405d000901c001058010f0014400030880050803900d051000d41008a80f21076142c01ca00700014455001da03100d06004540703484144504010759019102c101c0842d0800e40702e074030030f101c40003100303440c1c896040d44034950070402402c04030880c402040008003510304001000c1c022900300f581c070f400800c00e213a5803442e8007498400c99184e07003170103050030030f0100c243c103005207110100c85040074203040e1541c0d0010405c90710058091b001c03910b4040b800b44400103156541e80e40a890070301d6a004c0c0301c0d90318000d61380b104000401403090f5401448003c480079500d07122030315000c034182d1010203042e80141915810300d002c607882e4403c054046400c81e0002035246440d29020003126210300300b181c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 701687455 1250 701686205 701686211
    0x304030807030e1011040e0915061c170c01050f0609071803060b0301020903070f0513050c070f030e0a120c090e070902030a15030b15040203010803040b0f04051203070c09 75
    0x30044200c00991031121041d031310300000c1d940c11400301a85060243e9805003141c115408100190b85c41e0114441f003120050f9114140582c440f2001c01c40c041e001d00400084c2c001c14550004081124200040410042000a2450010024186801d441007211074525006906041c060b090600081b40d680c400480d10b044c2941400d074002010141d003d512000d04113945500c10304c4150399003941242c2e0305820003412100d0030f80d59200910b5a020b098810203125440041420200300b0081c0503262045081040b1035140411755a078180c0000d00109085d030130000c41c10003c0702161603021100740030301301c5e1001d44c045060940c07510080e8681c17235070490481c50b801c01314904001c00000405006456510101507140c2e95100e01000052440e80c01c031644440040000200303010141c01c4e0340d400340c0302040708400182c01d10f13428402a444203100d9491540d10800040000800174806049034101d883c005902d031607524400600b035510405040c00c01d58000103180d00030448a0090000241071140e014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 701688705 1250 701687455 701687471
    0xe0f01030c0e0409021203040f171c0c050709061205060115021509030909070806010e1509011805120706020d0309030e1512070e040c050301030f141908030403080703 73
    0x3800c0200d0000d902d402aa2690100300c00c5585d40440d9410841500003169203c83e03450b20181b003100e116124401e0f050490058031140301d00040b0f0141c009030b10075010462440d10000040b03400707d45402050350b01d4022000041010001402010005c14907515131128084150410904201041c1d1050800403e5903014003d8142c0206200c1003250350401520525982d22001c1815486029a103650043c0d004003041a8107800c4262240910340a030b0fa01c82060910305e091128200b1440b400c61000d030000d20516001d58400d103141d900d0b00c03504803290150b05640707a006c140c4186a0601540c426000030b403040c040703940d04220007072110080345401d00c01d940540e2030291001a01d1038056008006510300b05580300700039400c640b51140c40340e07180c20362454030f01ca009100c1c00c650310ba011b00c01c500300540c14090b50300c500241e9058075080030613807441e0b8280d59202ca03600b0b030041a41c1519030149080e10700049441810ba00c044a00404205640745010300d070007050700350020320403018945402c1c81 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 701689955 1250 701688705 701688707
    0x5012303150f0c041203080406060b0a02120901020c040207050d180e0c1e0307111207051c03090506040f0c0b030f0402040504150915050a0e0a030507021f0e0f01030c 73
    0x40700ba081800c4005408941d254100c80b4259441150005c50300515425071900c100b42e4459800c0703110360b0050a04004650f21074030f4400c488d110368000039005138060004082e0405401c001084001c10500403621081c2e03080000c101a03820090040d20160042058948007c1d0051210041003081c1921900e40c0c904041680c0740070705c0c000c0c0030083c078004085000d5461681506100c1c4000314052034103910f901d003100004014540b00c4006151074000c4002c1e06e0070600018040e100050741c008041c0200d18100d82c0b48040c000802400034040680b01d00c03111000c0b0303c041c004a80036901072820b00140002074103000c0e60400095000c01c401c2802002003117400f54802409a420503030483c0d01041c036864505106941d0105161800c000c01c1c47d18144404120209001c950030441110046c005a03546003c201c00f2180c0d8000720400d540c00c504501d00000340310358010034040784001c00305144507480d0382c031444450081c004004081600040520002d140100e45070900940034030302480325940f1000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 701691205 1250 701689955 701689993
    0x5180a0b0301060312030f0603020a0e06010e1002030403060b0613060216061b02040902040f0515041506020c010804030c0c14130917070f06230a11070b04031205012303 74
    0x31720800c040c0c3d11900108921942d4200341c0003150000d01800005031280d04082001070140e5415003c2907031b040d0030781e0030390810055004d01c81409401550425240d40c07945806440e4500c91594400000c000794003008405201c02c2010300001e81c024079a014080d0513000328211070b90000740c144500c500805018514009821038071a605035004110003500b840814081c0c071440d1850540039040c0002c00405080040c0100340c41d60703045400380921030307600c1101500f0703099030b004100050700104011203040d4011803000d60801c1c403038588503544248680390318051501c81c0d006494690050f481d41580792610305c5141281d02601390301000906120355858440640c1d01038698030384030340420a00709118250028102086c1c010000340018012480301040d0000481450001d203054680401c510204070321411a4506d00c404007113140110130f48407a810741000030011810051040b035196900c1e042406000d008066844910f43e100d05540600c1c00103ea58803c890b000380c3c060300100113490a550 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 701692455 1250 701691205 701691233
    0xc0519080a11010216032105030c040603020c0f100b09180c120709230921090d05010e0c041b20121c051006050909070905180a0b03010603 61
    0x10359054810b009040143c0c244504169040c088074001c1070000240b021482d500c42400c1064524032140f10f55030b000580c1c00b0700094074030203035040b003c1c8010301541d03019078020080110040c00711460b10b804d034100d05240280084c8101c5140d13440e4a604845405c128032a43d402c40742c5c1d81c017096502c030b0582c005541c0d2071900202c0c041c8204400c505030b0549120912a607000f400240740d092120300c521031280c450b507440c00c2165030f03402682d41c0700080b03405c80f0100e803c1c0e1000e001032042a10500c100381d02d001c07007900300310002d9910202582c0d604000031800d00c81e282e1400b075048003605000c6000001c2001301c0b040c2640301a0409484403540500ca540030365104c15042041544010761001e10441501d40603503032200042c0c810000804c40d030191040400b00291004020050041d961081414400c4060510903040410018807583c050784c504000c075584e00c8202071810207982070380c030710015484101540d1100701c003031400018800080214000c0c003170802d8080c0c000f802131070701c0c2da555800c012000c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 701693705 1250 701692455 701692463
    0x60915150c0a030206150f0901060f0e0d03020f1b1005030a020706060806240109090f1b0309260702090403110616081e0a0e190c0519080a 61
    0x540d2101245050005881003454820121801c60255160203940d40c1c0040e9603071b465400c8001c441d80560b1500307040b41030203680050007a03140c591034108152400000201b160040c0040d00031031503030541f9168665030105004c2c0d4024200b114103e4445418141121061404080242d0400001d510b6000341c2817068410762624959039a00c21a201c0b000303028500e030040000707041400c000ba0240001400e03600945a2f410783c42e8217220300102d5460780d0010f52680c5404152298410001c141c0e0541c4550385080da4400041045600d94401d01444460002000d02117680c9881e0281440520050482c0140149000c00091161f031400300c01c00b400f07081c8001303115003806400141054400c00c0058000134156040b1459801c000426142c581c0c0c82448a10009040400060882c091416074484901320040117503203588814540d84c0103061680445841707032007041210302c158007943d80b5400c0024040e02c080140380d41440108a02c1511114500b020340c5d02a040500c285132010a480f85482d81c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 701694955 1250 701693705 701693719
    0x90b06190b0f0702040e011409070806070e0303070c0806010f050a0506040b0c150103030905121606030c030908030a020309010b0904080a051305120706020f0106030c140415080a020405060915 84
    0x4200006285881000f800035042410030703042005021054020f44c80700007000003280c9007039680011143d42d84140f445103007000c5d03200784045040c40740035149128141c18080c0540c1d240c00e09544400084080e140d100110039071000004000003010903040d0406400d0483d603d004042c03401c8005000c60143e8051003806110000f0048103a07441008580c2d07107440c10002d5041c0c00e43e501d0401604052862180a00483c06800842d00d4500045200d441600c5091000401d8900b4008110020880c0c0c3e4007000516542d40000303800718907030502641c46010200c00150756490048940342c25180704c541d46500500d01001130200241d806815509000180d29101b5169401401c9096903034919070b01007030304a184440c0c0c40c17030111804600c08041c3c0b1041d8007200d0b1607400507032032103080b41c88501c0081e114000682040c4401c0c6450b00c0b207022051801030003c600c0c108120011070100d40198000111513000359070007011810a40100f982c0820100e81882841c0f038084c1c11516901c5500248500c1146 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 701696205 1250 701694955 701694967
    0xb06030c1b0a05010b01080a180f03181806050f0d0f0f060504030309142118041b110d09120201120507180b0a171803070303090b06190b 60
    0x3544414040a0307030951422560041e6160408500030440e844405e03000a10840020306000b80900a8421041c8503042107445ca00d1242c4507070b600c1c140340900c2101003009880c04081242e2340450b1690291104079079842d201e109680610045503408da214074000c010b036805001d80d41d511002030401081d0001c660707803204001440c2002014900910040905180505100506506605c10f4240074030074000660341c2004c0111081d81d8407060b41c102152048181014261408100060072180080c00e50b0000541444000501603a42072880440090880c0107680550355200000c00310381031030240a8000e26403000e02c020201c103040d0094000381c021000204046922988640403d80e94040e010465070808200003040c0c3c40c0801c840c041b52603d8490301050319956241203451460080e268110700552005888404400c0100214a02240030040d0815401e040c401080100d1017990001a88039444c940345102203070203000107000314580c08044404161421210040c2c1c2c184201240d1909 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 701697455 1250 701696205 701696227
    0x100b0301152303041e150209040b0414073207050f0109030e1503090c0d0c03050a0503130e06030703060b0f06040e161107121e0308010e0601030b06030c 67
    0xc04a862002161445032416001c000008000756005500c99160700c12078803e0090801114449403001a09820200740c540404072007e9008011801000d8008550000c5050004049030324141c038503145501e200c8100030060782d0100103000e01000c0250b80421314080404c110070902030454200101c032000203929400d02030f04010400d18007022100078000e0384101c3c6002402000c079508101d000f031040740f4051800c80c07020030943c1d200d942c1810003800007811000800c442009040001d0b00c6590b00508040040307a0148400402103000300011561454074200d0348002c8034031648404032800079a018070030170750b030040f0f003550031240c1100010800420711400031794400c0c0301070012684000c0c0028000380c100391000c146d40c801e600030800700308203c0080d14141c41c441c01c0c1d11030291840d0090002803121050810b480040c250140121500500c0c0005e10741081d1048844140c011034200c4004001009103820900e601410a10f41801a80c0c2c119000c03c842d404040d250140d103650100d0042149 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 701698705 1250 701697455 701697467
    0x80106140c030a0c060c0203040803031b0403050d02063106050a06050a081501060c0b0a0f2c06070f020a15110f0d14040804030b070c06050109060e100b030115 70
    0x90300202050342e90300c83c4420800303000740003401c004482081c1842028072550303001000303440490302040095880c3d0b90398541c02c2c03200d11b1401c500100704c0c01c206000c04004581c0400c19144403400c1c0c0e1700288114103005034110b4444031190310300c526501d0104e03001d092002c4e82c9032521024035400440440c6944881c1e0042d40580005d4114035000b2203003010010360319030700240100203400c0801c080001c83e600e40c0e401320b45556410300003410441300364000c140b100a0a07803004070580d440e980700080198000c1510901c000307a010305505020010094055406000e0022075001b0403941846503100000c50b03406520b03414444406000844082541191103146400a100f11030008130300c541e4a20001c148450316411900c0f00d044100d18041a0700d52410012030010f000b0750300610300d40e08241c510390b140050341d07038020b0070f0b07104000d00d81c84a980041d040e4000d150190404990128241c0d0409940c400286c000038543c0c80510340311b41303080010400d050b0840b4199407851010000e1500d41340019141 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 701699955 1250 701698705 701698717
    0x10090228030b041109091503071a04080303070306080d080105101115271b09070309020d1101020f01020906070b0c04080d0e0a060e010f0509130504080d140708010614 73
    0x2c64108813000c0740800d02c0380d0040c060383c00c0032031754a8680d07100d02c21405a6640000491078140d800540d00340014403003a00d2070450b07100c203030a50700c1c034181d25032920f02c0c29900192440f902081d01c8200034010614188000000080c0f1031600038070540c5000001003811988078410014058400307840388940f0401d008045a4400780704441d0110b0400460801007509200c54041010300e0403000099442404038440504810050150140c0d80d03400c0c0402c60305240240052043c03540e100500e50051300c60f100c44540b414059074007140802400e50000e41812011203914025901c100500c1c402641d540c0240d6843e2038100c4070035040d60751028025101407040741c020402c144640540c12031265841000741c18507603c02c2e40c8110310140c2e01c0105543e00300c0c060700180d01084400c0000e0280034810f4001c4d0090240c0109240c00381304030f400c0709600300c6006540c180d92000000503656401c0307025005900d0003d036041100b031038526200200034040314060003803034100000200700c00c003040002e00039101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 701701205 1250 701699955 701699959
    0x30a020105090a12080c1507020d0f030e0d0c0204050a0b01120b060403050f1b010e210102090612010504150810050406020d3e04120f06110310090228030b 68
    0x1606400c1c20175076407a030004180540c00c0d00c110715010045c268040c0394580605a6500240408050103109480021011a1007001c050340c0c1d402c56124454100900c4401a1503a11240020000c1c1c1c018081507550092404402078240701c1c0480d9566840301c1d140003000c0ca01c2000140711886e800004038944191761019002c0d20510074051144100032840d64100b02d00807a04080941a8000540e58a4440d8403126844a070171902c0c14030691096096040c10080d0748001860000c10100140381500710742200e656481c0c0c20401840141000c0c420703200c200c6440c402e604101e51400d0411692039501903014502a61100c01140c10030034070ba0161800134071030b200c007840303015110280131919144070a40740c0c090790b091144410036040c24110b1100102a080a42031801d4104243c0c1194100c1948080b80ca241082ca101000300b20315102da010700d1ba0101c0317141581c03401c01078945103002c031054002001b1b03944100606080c15241d07010740522a4220241c2c6d00110780f50b0032041d8000c010b8440525 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 701702455 1250 701701205 701701229
    0x21c0b0f0f060301180803070c02060f0d050f0408190207031a0604050703090c12020a030606030c1a0c0307030e19091b0306080601050f03030c03121014030a020105090a 74
    0x11000309502141584950408809a54640d9480041600366a0f40e190702d80e185840000405020540c04801960302074101c0c107201803c2c2001da40030400f160701114000d1245040880c0c0114117564602880f504080f460a0346144c50401d5107400c900c41c4107505401d68138204188102d90594000d1107040001d40e0812201004001181c20400b00d40504442d2548107918000000302c1e420f0081c459030aa141d00b101640c00c68130f051078048882d10000010a90b402a42e01e6230000000300340380103180103944623105022450b4640042d90000000c0e074400f03810340140a2003104195600007007558807480e050700d012032440d815407021400565040a0001030400c040401080c100d85d180c000110002910010342c0307440300201c90031000c95485005410841d00401c004110300c0c6094180516100390060560745030113908000e05103181d110700c3e1055001c0500408208001414000c00d20003803ca502e6180450b02548000075107405071071000034107211001c00c87c6c0d07415894024265000d008180c01300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 701703705 1250 701702455 701702461
    0xa0609051b280306030c060f0801030204050a02120a0209030f0a120503060a050d1a0c1c020729010501090e0c0a03090602160c1a07050d08070219030c121803021c0b 72
    0x4001e08121701059803002c2088200040b214032884803c0550b5030b0702e9454404d0750742994200405010050500c24140b6003c2c00707640707030b00181d060025000c0d1007000c000683e20104002494202840d8400caa00c954012008408c0460b4114100e070900e4107140c40c0055603592200000307035180010303820068010295690590410100c240600c003d03030a2001d10002d25643d040c0055102d10600381c2036030a14943e0700c50101e620203140c01130801c0a1154a9604890704103041030010020140740c00c4240c5c11800e0300400055030423001b9100036148507022011180341490800125118591000c0b0400d0f83c0c4404000c00d1045a9050362401c1c6005089801e00d0202410310f01840140f07401281d1100c403c40300406c4050034024102c0341c10381e80c000064003001070722590940740b800f0002c19990941c01000c0c0001000400d04442c05041c034400d8a445240c0301580c2401110f10041041d03410500c800382c0d0703407241c14400e000e1007402101d074101c4415481d22542010342c0c80d8040802801811424102c0034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 701704955 1250 701703705 701703707
    0x3040224161e150614060702040b0612090706030f18120207090609021c0b03070506070c030204140a180b0c0703020a06060b07050f1b010e030f070e0a0609051b28 71
    0x820f091002d0079900b444456118000340981e4100440d001c1d034805010400d0500600301900449007a11000700b0306800c0549506503200c83c0c01c0c0c00c40c0c03113010640015401740301d1143c044c030582d0954040b41104024402ca01d003510f86101c1078156002d080140b5007505880c020b0301c2041903401402d81e03400180409aa12000d010103504170008080c203d200e11b6280080307080140c492350b15440c3c4001c000744900383c40c1c00107018480c5e00051082d10380d07407034203078010015031564042e01503501c0d11070010740414036211444e882140d00410322125005070322119003020a051243c055003005414844a0380c071011803405a140c0241e4102c0280071500705030000404001007009400b10300c0c003640569100c403c039090300c540c481505021003092403885084110345940f08020011150744083c0854140c0c500c0401060b103000c0c100d41c0001400c802c00b0b030801038071039030901a00c1d0041180340b030144001d0030b0400c10007650300740c0d110400e01023160108040590b41d16201c01420b1420041342101040760303880c1c40c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 701706205 1250 701704955 701704973
    0x10e010c05090a171203070c08040602060604050606161e020d0507030c0b0a0203120606040909060504170705151e01030b07090f0602031e0f0f03040224161e 69
    0x51003031184019660011319054a0121080d000455502030145142c541c1c0d15000340343c101500b02000c11084003c6840000d0381140100003070030080c1c0040405151640401c025101d008003201d000e02401d202c221981c110178511010752952242000680c2d024903000c0265104180c100658400110f01051007880004250700098a001d81010005030362113007286a000d102d0620071000580c41006400c4120440c3c8103040d4201c0e00007403110381b915a44840d10010740c0c200b00c030203840c15683d5000703000410206100e202e20106c00b090300c4504201176911040d44900440c07412524050200c00000c010095105425510f9201c0d500c3c122045e584a00341480c811070119031070404100d22807000702c0d081d50380c1c0f1244003c03580c2550055107840031521180320026120768800b00d4011040c0565400d21038040d000e07100c0e0782d031038110301505c070303d01801001441601c11041c10300074807188040500d4101d501044800e044400c055044440b000c0f450401c000e40340107501c80240b5070135a0000760400071120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 701707455 1250 701706205 701706217
    0x1209080315030f060a111216030f06050d02270c0406020f190206220b09041407020a1e0203030403060b090603010b0307170102040503120a020601080a0c03080c010e010c05 75
    0x1c07000321004100741e0185035880b244640b030074560741c0c0503d0001d103200c0d084d44c200c4580380901c190301078104420404d00c4100030b40103681e10080c0010038501b0480d8554144142e880400c40540700784103061402e0007107050002c8445019000f00440200f10030702c48250591302030145080908583c4502c0c00303005424a82d08140a0b174401030166050300d454503e8000390101500103403c00040c0e030b043c03443d400c001e0264040032888405140e05d1103550503010f0b0010f400002480b14000480d80c4800610400c8200c0d98074022201a0001110502c2007803980050740031800e0364041e4110042d074001400030581c031150400000d600d440001400700c20070085401c00354000c1e5050300c200003151074080425090300c4564888603016480288200002255825500d82c081c0e041c5000628181d100d0000c642042042500d00000380f070f00080007035019904000480c01401e200014010f0482c1d65039440782803020500c00034022880100304204030404c01c2d801402c04001320802045502144030f4058016008a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 701708705 1250 701707455 701707471
    0x40807080a030f3b130e0c0d1511120403030c030e060402010c08090f030f0a02011806080408070809043e030c1608030408031f06051912090803 63
    0x40c5600d95810707406024040241c031150f030b601c0c000100c1c3c8403010070018481c070280b40c0c600040021401d01c045d100c100302c0207004001104007059983c0040055407030300076120681030142e00b03100d000c000422915142401d900ca07100001083ca440d0203448000c1a0188d02d8840341d61036005c00500080681590126103219419242409155a440200c58403503100300d8029010034404a4000001200940205001040180800b212a4286c00800d160107074016800701e441d030001070443e003590382041d007202e425000042a481d0f900d003011801804200040d20050241002041d900c1c100440d04050350380c85007001e4030802200412074a100c82e82050a20b8640028071100240010380e8000300c040c038000690240303414510784529042c03c0c401c1e40300d070400115a0f44c660344003800180001c0010f42c0034501601c0032a480341424404604a181860802541e030b00305e070a07080090940040c1903402400713000c012800e8800003610140da004003500011180c45203002c00c10401c00507840d010394001c00350 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 701709955 1250 701708705 701708717
    0x31b061404060f0f12110c0111041505030a1407030504170f0a050d0219050d05090a0312020a0905131e02040506040509100b0a030203160f0f0f05040807080a03 70
    0x30128928035128034050280040d040f81c03c03040440e40140c800e022085000c0c0f90062540c200889802e003160400c00c00c51301d04610004190030122400d024221520101c09011403402e40350107a07240f00040112030750400d001010000541c0c60240f640201c865407454005124146801d25000b0018501201c0403a02d0003214907000052800000c2500d09001207220700b2031401d00c2040e000e0302c1c107400c05030030054107076002c00075020154118151200824003640755151215466203541d41a207800400b5070361550300c83d40d600c00101c0c3d440070f1040c010300c4103c51700594072840303000100c81d0220103070001c0350489030302d110b06030100032903031300c03041d52689a0003050302078001500343d9005070b01c9030744506a0702070000d21060240d840d01411303040e003040c80500c0c1c3c00f0381156a2280341c074003034015a0044000c654040100241c05004007110000d16085240005d24040341510151100d02003220140c00c100408400e00180340c0283d04440c09401031800300c410655680680c21394441007a001203002842c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 701711205 1250 701709955 701709977
    0x70606140907022e020f0c010c0809150c091807050408011a030a0311191b0503060402030a0b090a020616030e0603160c1a0a0506030c010c030512040c031b06 69
    0x48040f81c41d604c203d103015100d80070520340c1682401c44001440034021290b03403c2055941da000000c00070036410684c0b90020914464021024200321001481500d56420411624024030132100102c2da00003130104401c2d80b500035203000324000c01d5010710300004064016060007540cce50400060030490301320600a021030300a170700e00650008850f03588160954001554040002d0203905138100030000101120341c00480c0c140f58015207640c00c0c4064905071020b21940d0652000070b00c510000d800240c00400e030f9401c0c61350100b981e030011000081c007288542c001240f12010180000709841e03800800c1c058564904035952255154092400c0b0f0110b28040302c0e03170400d400d108090f00d10031542d600d00012464140e50099804546522044600300041d02d1a2402c0d41c880402c11801605610000120392420380281460041e4242c009810711208800507400a5801412030705c0d040e8100c0403c885035200d41c500704105040c5508028201186481c0c0140e903503498042203411504140d44140300c00f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 701712455 1250 701711205 701711207
    0xd1106011a0d2306122d06010f030c061e080411030714040501290d020904020a26060f0f0d02030a1b06053108010204090606030b06130501110102070606140907 70
    0x28406011243c031600f02d000d040001c0d000a00e1b10500e607000404031741c0503401c550303248075080000903006081c04140c004818401c2c000300546160150400b4144101c001011800c00c64404615003850340030030898800003800c1000c041079801089001508480415072600004180d070420305442c030340100e1501000140a030b07005201011903400e003100110340082004111035a581c005420048180c0c0c00708051012501c4500c000d2400e00c01e9980c50420310701c1e080d5038110049010a01c60380c0310382080820302a817070b902c0840b50710100d1801c9800c0e8050868007808074007540e446000280d414041c2c211484140660075203e07400601c1208840e0318016180c1d075090320b8a018455411050038858100800040c404d80d0740307003916020701d003004080c250780d0300e603100d007079a203d13802150005860340b10410106415000d0241d104a08541c070340d00341003807043c0700a005622449020304101046020b548114170a40c1220401e94100e00c2c01c0c0700060710b030542d40d413802c07029184a50280420302c3c00a0095 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 701713705 1250 701712455 701712469
    0x5130902120102070201050403080c0118030e0315190914010c08161b02090601020c030609010e0106050405011404090228030c05010c03171023030d1106011a0d2306 72
    0x4585c0c1615403906050441e1241c142c0ca81003075500205644da2811240c0c200c145564070119264840d40d50700703568400c80000d0600709080e4a066004c140040f03420301c060b034042c8121511840704040300c000f40c140b4050800f402c407024107564601c401e510380329200640b1540402054490304c03145a481c01c481440d0101250081000256108600007520300d101c018a4998001c4c0d800841c14811158510510300000307003803402c01d5662800d169503925160f00c0080080c003c120060004840400040d854040e1082d80c2403402c0d144180308503035500e4800110364035115440c48400d034020140c141c90000340c0081c0c80e411607034081a21031440121000900390f02c02c2011a00456160703075000b00000301c0381500e40412070082c0480c0741020fa00da202050702ea1030940205032280004810701034200442d42814140501c488684041101c2458041042d42c40050300c1c6044400022401c050700114408001890117800800d02030341e81082c504460f070304200f1201450214145c816a0125150b1004100170 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 701714955 1250 701713705 701713717
    0x90610060c03080a051305030c0c100207050f0d1e050a150209130e0f0d020601090e0601031a07050d0f05090607030e0a080913060617060301150b07020a05130902120102 74
    0xa5040000600400c070380c3e170415600500606a01c404014003660b03076a0031600181c2820440340d0010b4040e900916001044000d8281640081c00c1c28070300b03100c0400c0d03900c600010540c0c05200542d0300d5070204581c00c82660b810350201500441e8050480c034029440b10b10108003030f10740003c2c1943c05a8091024030031101140703401041450150401480740c1c01429019001013403502800c10b451251079014000d568100c2a541c2c00b40c0000d60500c1c01c04002c454440c900c1828552220005100040c2d0300e007c150b1070500b5811440000d640c0300c980854542c0304409402031440c0c14501c4480c11060580c0229000301b00b040189e0340180e41f060303003c40442e4100c610f1900203600802982d408034104c07100900f03400101401d9040060b905201c10b80584a944c3d0043c800200d030f04006074182c41100e182250001012002031286070300f03009201c603680f110b50151503800580060500210741d10003d00d000240030150840324014200d1203400001c012122099002f0740c0000c1c0d901030965818030031108 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 701716205 1250 701714955 701714957
    0x5120f010b070f050a021306030b01080304030203030a200a0305040311150d1503060501120c0b0a020307060506130614030106080f07140d150f0f05041106090105070b090610060c03 79
    0x10078003406440f040ea00c0e009030803003034501d8050540004096100c2000703104000a0688000c030346075185140c00040c0b088160720a02c090b400a01050005a602008952512040e841c01c20302d140d000c03c0c00c8075103001800c810020a8410010000d04064008020b081100e0040400c500761404400500211800f42207a2a2294508120200d464401603102400020901c88000140350710303070340ca800407135a007a0046286c9805065946080196400241015002001e480e03400e00a480034041d66a02403124005e00940d1102c000447c1034136001c0c614240c981c0a01c0c0e0510080d941e0301540190100309040807406942040400303d000303080051020705541001000f84200f61900c00c021050031282141e540c1e10102d1a20b040300441d0044107528042245040006903001d600d1004600316651030f4160301c10f16041c0f40400020840c601d0b41500d00302e0064403296501d0001f4401240c9510880c88002d2611502c901403040e00c0341c0c00500c1c0e80c0303e5140e154901c40c12a450340340c2610b00b0345500800030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 701717455 1250 701716205 701716207
    0x911090708070906080702120301170c06070b010b0715020706050702011a0d12030e0d0f0201060f05030d210204060207080c03210903010b12010f050c0a0f03051504090305120f010b 79
    0x4c51445101c8441d48102c161041d10403624030a510500700b64030071383c0204801528506051203000e4103000c244141c3c0e0007164141d1a18000c0d6556001c501814412101c000320045075603818001c51030800b079081c943d840f004640c0c1e00d00c103140c407200402003603c103440190b18001d4203140020300d800c680b1071002801400201807002550307071140b6030518000d80710100340c0c9810800080d902c040214240c1229141c40781101e0f1121908000d084800c10f601c40440c004d88c0c400200116200400c49240c0100d281c51b00c02256082c8081e14401e14204114221002d4800100000c103194046094000d64801c03205444485021500f01581c41d9030054620140044e07029145211050900045c0011100900007143c24562800007590301d20280080d020141d4542c0446030a48200d48919580442520032050034807440348001030080155410351001e00d0742c5c480101c5c49940702c2070458035422000074000c0c0030540903071400504580084260510080303e007004900c8036034141c451a410b81e801c8404031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 701718705 1250 701717455 701717459
    0x60403140d050a2f030a091503090c060518090c070203070801090b16020c0402131e18020a030b0402040801140c0c0604021017070e10030b060901050306120109110907080709 76
    0x6100302042400c1144164544c02094907440c1c1c24000b800d011801c03078484041c014035016500b950000303400c44c050304040c0341028010014010302040d0090714200e141c00b40d00c907110890014007064a02080d140d0080d0b00304108800d211000340200301480c4250251040e0980d160a01401c0e07030343d620002040a290800040c00c401ca1400300311051100d03d10440b00c005101d81c0100d000c07a4820492034800040c50300c1c0c00d004001051485074001000700030520304981c5001900c1a81d00d1158210036585600021841c41445c840e4001e40164107004108660f0386503580c0d01c43c0e00800250054142c60500440000c48043d00c01094400c2450218041c100030b81e995402c00c181c20020030844403d2010008074584072401e0345020300d2144130651030340344140185030100150744014400368001c041c02e1007940e850700e0302c40205417203e0300d10a00b0019180e455807000a60340075030907092a8290740c640540c0c942444003001d02d540d14540160f4003100140c90f050740072181d100c822501040811400102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 701719955 1250 701718705 701718737
    0x10908130f03200319080405010f05070b010e130602040e0103022103091003111b061803090405070507120815100507020d050f0a0c050a0f0e070507020f060403140d050a 74
    0x6200903d5001030588928100c820304220740e0422801c0e06880042d0041424003242d600b080b04408070001c01c0c01c0160074a83c4d40e90381c100740307000140281882c0062100c04542c0c03102021070076000c800ea109800f0b54031642c880803178480c3c0c000c003480140d210b46406648900307a003569644144c900307125840990701d840a9175003400a2503908065550426940b030324440c46d642020406056900c542d10403009400b03640541141c642a4081c001d602448403800402604441c000211042d84070107440100792940d4038603042d81c540c045d841d0b000d4264505840980b8035150b00c000b0300b03840351600002c105d40b8026170405204043c050500701314080b5030b041092002500e81703420b40f81d07a520b20070300031640405a0505d040b4108180154100d800702d001c02001d21482c9800c101c4c80c80500300c002c0820308a1450203e040030130310405020401448800651541951510242c0d6102800017800c61541c0c0c035500e03d801e6600d916103101c0f405a9019688602d074200e449941151310410701507558125070948035134 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 701721205 1250 701719955 701720003
    0xa082101180b0102070b0f131a0703081e040c081902010c020904061104060c03022a0d0c080106060915020c0f04021c1a01091e060c0302030c010908130f03 68
    0x24218198482c05c5c0340019003000007001409030aa0000c141038584da4180400e110703541705600850790308103484440208010b2110103407411243c01d03142001082e29446040d1210725040e01500388045486001c110902c4502d40300d00040303c64510846003d1000d80000140400240310002d0002d1f01d50020b08002d4a04580b800781c000b4000c07840000c004400d640054403948c0103074080400304100607903030018160140000701c814000098012140c00c0c0b03080c0113444800c2d419821034819002d15010406016004400b5000380069000030400d0b01d490b081c01911000719440f40407014088440c104400500c04200324030b580783e01a00710040c2246010804c0042c0d0040e002c0e404040313440206d41d10414400c2e010301c008410b00000100c1300d840301c401c0010420700054008080448040d140b03441400d10195607541220041c0c40e250885150a10782242140304035101040b0b290701b030419038401d12803104003c0c07094640500c010246c013039a50040400b100c4041c0300c0600620140c1903544810381c0500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 701722455 1250 701721205 701721221
    0x10e090304031416060206091e0303040f140607020604021c03120c02030f1801030506030a05030316050714150a0605010c0602130803040e04050c0f0d0f02040e0a08210118 75
    0x140561301000100700308450030a200d58000c0c40141c0c07080003400b240180910501c0310040051800074941070004519555034400031b04002c05107a0340c0140700b010300c0b00d0480c84034280400d140a6401500b0300c003500075650002a0b6042c0e10680065044240015008050b2540e10b685a15850310018041c1c403403100600c0454856015400304018401010b2072034401408155020341c41c0e00480c02c0140001401c4400003410310780294815990704010503000020b032a4010304111098002100d00c42086500c3d01030280010140d008659066119010100e0000480443d001c044d09007569107000302401d4501d103215150208040d1a04900403540e160024510f2100e4441c030b0040142c1e980301d6503861513000d54841c141d605007400170301c010041d040c840d0704940a41101c0400440040c4d01c0010703105403500e0401071076030b140d070000801192115009000c0080a002c02d0340e901540341d04140c01d0503882801e1031444050351480c0c41c089660003c20070f505a40c04c0500c02d087c6c001c0520f4149000b00320074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 701723705 1250 701722455 701722493
    0x4030f05040909080d0e010c0518010c1a0603060a06060f0c050a0c17010c0201110a11070b0f070201180308090607080c01020a0512070938031e010e09030403 69
    0x70480451854183d0040048580c4684900eaa42e40c0400410070110f0f22010302000469040c00040d043d0700c0c0d40310040e0354448035010100320301e9410a00040c0c8030f002c000035000b8030001d800200083c056440e010424860041501552015555100c0c0b11086030514010500400c06a0303680d02601031040300c0c4016100d20035800c0b148000303400d44803040703108070a40c801e40c80707503070407540310b84189c1020b0103003d01c42c1d60207000034808426030003102a40d50243d01016020403010745c12030120f10f88104900b40080410500b803550381c0b00304405801440d401042d050b0b02003503900403103000c283c0e2403452060480b03402005240c2085071034020012a648141402d54107201c081c40007010078031081c80140b4401036940c40d965590000c0c04580c07282041c00034682c4081c4860508100400040b0203541c5242201c00c0c0d1b0400c050310040c510890071070b0540c0020300006280401007000c0b10450803515041c894003544540c80030380e44d411500d83e508000304c0d5103024a800038001080020305031007401c0001888 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 701724955 1250 701723705 701723707
    0x1c0204180524030a0f2a030b070806030307120e010306080c030307082a0715030209011409280306140910050709080f100b0a06140904110408150109090b04030f05 71
    0x180e80c885c1c182015003404e0942d021192010914503080d207006410104400c004502105a461516140100e1a00405140500502000007015668140115481143e100550784a50b00d03031904000c0c8150070129005001c01e02c0c204001c18501c00001c0c80201e82040100114036183d1a03039146102608929411020400f0b03580d40c1d4402070090701d0b000c0c1e003010207030030003052a149408107400e41c1410400d05101407510400112120742d07030004c0d20151080c0100394840d0765614440200d806002480d104581d4001035038020b011403030f1082038041c1207030f004900c1032140385070803885c0c42ea04c11010348070108207a018200d615032580707035038200c3c03640036210b801d140039060303650460282015081902c0312007503003000c0d081c2200400103100b0071038000d00548a40d040d183c00d003240500b540c2040380941e0004803020841c61101e555603009410a180030340241c94403999070f001400da4401c03000c0c96804003901a40000b02d5202d03000d214032403900c0d400c80041c01542c5c03101d0310180c548101c5541c0130400c1000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 701726205 1250 701724955 701724973
    0x7030905180a18030c03112814061332100e0105070215091006080709050a0c0c1203060905090d0e0a0e04171c020418052403 55
    0x41c904034518078a0031075090345100740c6004030b098000c5460041038030b15804000d00d100404030750300c00c0307091501c281d060030550365200c524440300d4604440c3d0903009000845412180c1200304200401c00d007140d100c0c1603255002e9400f200123640700d241c01c07160340c02a9201003c8240104044510303044281c0150700794110030034101c0e001078040b0780751142400314542c019201e2500316002c600c40c48800b040310030020031050500d48030080d00c40b00c1242c00f965880c42008085005032809015060b403070242000704104231540c4821a42e111601c1317205040b13004d071074903002586071941406000003001003561140a5000715a640f540640c441c001981c080540da0080492007500710b2040b24018131074440200641c000c440340090102d8400401c4901800c40c000c810003c1d801800351041d00701e40d002c5400c09214440b030001d100c4a00590f074400041d0018243c00d031207070042030f038000e01c2a92100950318148440406440b42620800c0e19000d45051080c00e18507a42107400000540c2040020290741e00c20f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 701727455 1250 701726205 701726209
    0x15080723070c1e0b1909150206090d050a050901110a060603030806030c0105040b0f0c0a0b0403052a0a03030c1205161b0309030201081005120115050111070b07030905 73
    0x60031100c0d0448010304019414064050800030b0b003560010f4541c16441424288042c5076007078040c1e0026150000e003004032807a8042d01408092010f4550180c800004240441c4025a01c6005907a1407000c1d014040700c40c4a581c0c4160200c40c01c0d017400780c6400340740810070001144c203283c940a1380003440c040e06188400040c01c44c020310008601954400901d400d0803010581001c000c0460366043c86010407040000a400b074080d5188045220541c54440b00200c4140d410041000c00040200f480c0404000415805ca405400c0152143e005000e4204101c50304800308050780031000c00c59440304d45c4040009100c0c0d000001700c05414648031b03861002c40b5540d031095030750075140075811105403e41301b0b00c0154003480101c0166111582007500780b840c0e840283c00d141c20340c04040d04001041000031500e0301c88080300001010301a246c0d0324020003400900d8020000c1680400c2000b1080000140743d46c40348030701768254a806406844060300d4445202c5a560105804030180301101e01c00103159 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 701728705 1250 701727455 701727457
    0xf0212060f0a1508150604020c250e010323010f0204061d100507081e030403020c0301060509190209040f1409070501081b1e040602070302090115080723 67
    0x251903040e491119414560b074018280c0380300903015103600c0c44003032040120002c0001c0c0c0000103200c030003070300d00706071654408500070344525500c50314944280d0086150100700320154005220204401804060b2188200c0014a900b03200c05040d110212145003034154030600e2006552801000006031082c2c03451800043c0d0f04030b58031030004581003c00345c2c1c552040009107824488412100d0704c5a40f10b0000e00a440d9005d40d40c8058400e002c04280d4000103d141038402520180b01c9403015282e150502d00296961380d040c3d4200d00a501b801d0b000501d43c2800000c050154075004840840c6580b65414040250449100d240d84203031258050014407000344518107580510300044052898000c250230310381840c83e070019040000260030049510901450300041c0d41c840c4812503030320303002c0c50705045070840744520721081e0341000200000c81e60b8001441208580c0309131280a0f035a80d954405c00c0b440c040c40861030000c611081c00107804544904103005128064030200f06410540600030212 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 701729955 1250 701728705 701728711
    0x201052223031e06070f111e1006271103090f1603110f0609041d010e060405060f0408190e0a0b0c0c060904180503030103030315080601030f021206 65
    0x1022101d1241c103405401d082c081480c0c1682031181d0340038010402c05101c0d070380e03c40041c0250200100d03080912080c6110303588070100160342c14101c6d4100c00d244488880306403000a610300044c8104102d6802c0342c601030140c0c01c100d42008402d048610605030520034001c1351240030362000c696500c0e84500018400000d9030007150008014100a88145861480c0a4540324800300c0c590103000100000f17a070b600c1c0034801e00041074a550306000036050100d07409018940c060740d0300ca0f04000000e42111900c1003407258804c4000024014503000c1104c00e51504020f8401826680120b00040c15180078440300c02e400178402c03101145080b161108800d4083c0e141e5020200059004200c8035051070003840c040c001d07041c0c84100c01c0c5092045098290350f403540c0c02d8001d00400d0b0109003481c4030f503103c2d4881c0c40300e040d100c94441491140b524150791a94801d00048000c40d16200f8060581301c0e00f603a0850a440500004000603401c60b150040702c10881c640880e4040002c8041c20fa28150910840740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 701731205 1250 701729955 701729999
    0xe0d03120b03070e0933010b0f090d060902090a0c090905060d1b05010e15180102030904140f0a020313030c050102090d0b06091b04051306030501180b090a02010522 72
    0x1e290714403002c1c00c00e0307150104a44840307003c1d190011500341d18529031b80c40c0c112503400c01e0003a039460040640004a000d001e1030a580055070743d405070240700d625040340c1c181e940b003104c400303c0035560f901c0004200c030f9102c20f400d400140056070030300001c1443c6c0d0005803c040000c0445809502daa40d607110b10868501d019811944d04900810895800c41c40c2c01d448020112800103559060b245d80311458080d000e840301c2001403402c0364419990090048400d0403801400520261f41c059000d40c0040c60191204154000c8070000200740980038401d0381e010350482c034045203501540d07890890304003118000c2a990381d5030070001c0011503030ba00c41c1401340c1584200e0740e07440a03241203c04c01c020503000620504400076016030345d0324018014411601a12022581e403031040b54207040c1035008041c0d54000a100350b1038060709020041c4000d00141442c0d00c20007076400c241c3c0d941400151244207140000b408210240b200361200c441004042c5070100c01000c1d4501d01c190348600804111078100582d00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 701732455 1250 701731205 701731213
    0x20303040801111c020a14070309080d09080c03070b120403051c09020405061813080c010204080f0615060d050a1401060819020c0c3d0e0d03120b03070e09 68
    0x50821860101d40b40c0440130807108509104480030080d01c1844044418210308400086c0710342054003c8103103a01404807082250f03009a000a80a400d400440c080c04038075115007074000100303103800144030080d5070856014a041c5a072080501400300d40103041101403042c280110320800491040000075074600d2803010494505c1801884216400506132900604816004140701140b491205400449440c0c3c48071501d800e500346600725004141c040501c55000280000d07540400060450255500d8002c0c0c41d0141c64004d0110390020340040d51a4100509000c0742700c1c0b581c1207070b0003d68002812071b03010441408050710078500d400240c002c2c50101d1040e0082c00750f0807d080d075540e101604026003c600c0c10b444210340d140d0302c4600c000030502c00d5031444140c1c000c100c11407032010648048007200c1d810343e1140c0550880340920500e4404001044504001c6961a050702d0040959070151203c0b003d194940c101003025101c2c042c10303140c01d807250b0303000040c101e4a21085203120700803101c050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 701733705 1250 701732455 701732467
    0x21140d15090504031e030e0f1c051603030f02070213050702071202060f09150301032405010b0909041110020105060a120803010e1009110903100513020d02030304080111 74
    0x214010340c954008804440c40c0c881000000b035040040681500078021a040055040380f40450203429000080c113640d00a1000021174010001100520890f00c15040d8102c40e010b884102d4090050780f040c0b034800405203d501c000b1a0180d8403d910000744540094900242c0c0c0e000708100e4000d00c0342d00207000f95108100210287c0c1030013214050300054a103110f070302240e900003071224000d14a1800b410040003d5030581036680c1d40701000d00c0300045400396141c0d80e50742041d00d01e41020b88040603255125a8280400120f6441907a050318400c9400703a041000942c28080350b10030041c411100320b240d42c041c5580b1a6649216420444a1a4004a11450031206120500304164000081e02804030907000c00140341200350382c1507450714602408103603200b003031040c9103103401d90210881e149031548068012202c0340c020000108140c045410060000d41070b80101e032821a5051581c2003414040313070041c5040480180301500081c1228117054a6550003402c40c0d013260100130b1300103000198 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 701734955 1250 701733705 701733731
    0xc05070515030411060906040b22150e0d020a23060324030106120201140405060a050304020102010e0714010c050f06180d020d080f060415090203071b21140d 69
    0x3804c4c0b43e211055031058180303455400450b000e801240510210f45002203001819803205141100394103080ca090060816a60a0708103044c80e403030000c102c00203c0a26081f003007810440303140703c4d0040d07016144d201c5051401c946140031407248100c030520200940c42c0c80f8443c2e80e40101950140801c5800101220f00515501c0d0f141d04080c0c143c2402a41000420003600201c40d00c2410040d8080c2441c18480204410b0b03e0000d100d1030300000c0d070000300031074a030304220b074800b010b503229510070317002002403030001c0f58401e9071070a00d0f20402d014010900311140c1d0952050030900c22080c0710710b0440703107940c04a052042c141700049801070b02c1e030034800000e5821450204030782c0c01d42030342a00151003607204413a0000c162940041456085043d890045526503e4a50110701313080700400c5103018440e201d085c800301a500560b0311100040c3c034443e80b803d80c08007002400da11075610a00301002e4000550b02d5454201c82031484074148420584501d403580b40d000014000b910a541c00082c9400c3c48100c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 701736205 1250 701734955 701734973
    0xe030d0503180f061609030f0b07140306090c0d0e010204091b0503100909030e04020a082a16030309020306250905010210090203070f09050402040e0109080a0c050705150304 76
    0x4507400140d01c11410080c4000303011500316008010700c000f80c05c68010320101951400c02641c001045c0380c6141c049030060044010b505400f07001c0e16076800308088070041f41c201c0c080c0020798480360302641c4d12002c20300c201400c40050208424210b400314007280903004c0e1900b2a08a03a00004c0074a8031b0b1130814408629000038650080001e0424a0031424500c42e0116400300038000c803d12103648802c105c05042c0540090704240c80000e205550f00c40c84034500030681d0a080e5448407422100c54400d00700b980c02c050040d01005030115006080c10550300c140414404007000907410b0503690302c500c01c056202070060303e10034044503900e017501c809803007100f8041c00305286010042040d00304e41408503aa020500078074445c1d10302d41c0441c2484041c0002828203000f684482c20910a51200042084c900c1c1c00c0300384a98000c407420000c5c0c0c0c85001d605030aa60ba03050000300401e81c1086100fa01078050401d04020034020421150090b442d24082030402030000300402e50050048200020080000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 701737455 1250 701736205 701736241
    0x70b0c0a1203090b0f060109030c1508091b01051303020319050d03060515030915070207180b0307031b120b090d09080c04022503090f06030203150d030e030d0503 71
    0x4a4108040d00d40c0303071580001e20744c0140c002c0301590b0181020507207d82c410440f04000d1a0004042d40141e560340e5074800740440410004000303d1a00300026810450228084c081003800304c02048440d02520011030301c583c09920a00c07090345155001102588040100080e6118241c9580c0246031403401c00925140c0b000040b2401c040c24040103001544540240c00000344c164003582d602c80c1c40e4002124104070301c40c0b60b40b100d040010410442410790005883c0304907480b000c2001d40c0d2411054503030050b20a2460308503010742c0807003401c20014103105241c80c22014410070f225840c0f0745405078551078501800095444000c10380034001408002d0180e54803209440c00c0400c3d94602e480503c40c0c4441103903407414801c6901051040c0a11000481c1542d82d641c1c4040c01840003045140107022121103000702d8521201c0c0c5080440d400c1d00034401c682c0250076445c000b202c443e42d154100080050700d900304904000582c1462500d0791000c01c40c0c10222101e544505803a0310340310a8864160100b9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 701738705 1250 701737455 701737457
    0xc03030903030801091a041e140619030503040b34060e0303150108130b010f0603060e070516080f0d090b22080c0a020a03030305042003030912070b0c0a12 68
    0x71011400710004a0b84465688940648020401822108081640601c8c042000c1e8115041900841c0c03c80c202c13441c603901c580c23804c036051841070303220001c1040c05a00310b01000b025540200401d000f00a840b0000c0c113545000e606101d00c1c0b440b5151000205102c0700481c0107616080d01c119801080031a005180540056030001c46c294900303500110a250041c58000b8103011030500810b54034103d92851b4a40c1c20b4028600a03015652501400e17100001c0c0d1143c000001c0c5881404a0302001c0803804c580aa092070b50b45a05203564007d2500c0c580c941d03010101c81c90081006250795101c40c881c01380420703400001c0e00264440090030a920b1012008012819134a03207000c2c0042070440790000c0400d0360b40c12116080d2191605c1c02068030700880c000c1c1c0a0b51210200c0c80c0002095030682010744214450032185d4980340100080380c00d4881c0e1031118030361580003803148248509089505050710810340c411501c00d1641c95603031902980c0010b250710303141c0d04100040001e2001000700800c0e00991 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 701739955 1250 701738705 701738711
    0x60f090b0901052a0f060906151005030a02130e07030e160b0c010b030616030c030902091303030b09090c0102010b09060a030b0703060b0a0e281e030c0303090303080109 74
    0x600d5000900034881c0280900c2130503200c0313000d0107a2202d900b0ba040038a0000754100c40b4018082c020141c1e80d010100c4078102d16108041c001600d81150000d800e05050002d072046c040c41035140300039036617608010451000c5950901c502c0b003003c150b02d05c0500080c01c8040303259805061480c0c00900b40c0740101300d070000590205880c4404015081484d400f103c000c40b150f5074680082c0b041050241089000295040c8903400602c10b902c840521181d04440450314108a401601002501a40c0700454040d503c10000000a051740e0088104040190f210785000540031040c0000110b212005442603c3c440d80414204006543c0901c25010700780030883d541e84191400030002060701400d03001c010b00e000c0409010070740e44c9010f50440d402902240710003e469170b005010052250031541040d9100d692400c501c250842090018288040c484e01e4403086034604002c0c01c1c261400b41428140d003c4100c1180020204031003801c3d050156120b030340c03109806407950600030310954060700321400c294030f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 701741205 1250 701739955 701739967
    0xc08060a03030807110304050d03030618060b03160219051c090e1609120b0f0105040c140a0c0804090c0305090607020a0b07030f0f0b0109120506011e0f060f090b 71
    0x1820019803640326200389030040d50301d6041001c40f4118000e540c49149c00c50340d0306c0200002c2503010303007082090781c00c02c4030040c180c13103400003150b410b0301c00b1071103a0f0076081f00400116844001003040444411660700413903428840c1c0c122489080c04001d94140c450750001200ea451000510b01004060f1505107054034000e801d10741e114110140c09019003110751101f28070440400e00400f90000200041c2c261140d0b03245544c14403e48002c812039a58400440240000c24545017521a50800c044c41d5680c07815034810f480c2035000300b9071184620300180000d5621060028078620020405400758180c00301d05800042c00280942d440504101d80b40d4101c64200941c5030741c00140c04000c10340015840f045a115418140c00403d000ca5640c3c3d0118100004070b10418026080591001820b0713880e800840e40e94145a2360010400000800d02d0b08102c004010902c89003440b1420f1038180a60807250f50341e6030490b81074174001c980c802c101050444403607421041d0407041d9000102802007005203402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 701742455 1250 701741205 701741207
    0x30e1f20121e12100608040f02132c0c030a1e060605040c020c03060c03132603090f07050303030c0f0d061e0801150e01060f05090a03060c08060a0303 66
    0x90a1000301d440c041000c2460b090340480c440c00e0181074068400819520840b102042940760f10449222450303080521001941500c624409131007182c201030984803103a0706030700700001c07211400070850070b880e00c03010100121114404c050a11840107000e102c40c2030808030b6883c0c1810195100984203821688441d8041041c1c0c0144944030154a245510b10747c0c002d20701a0010085a08002d400505d00802d60b500b8076000036524140001c22001c4406070f40d165480d0800f6880101c62220301013911008c440d00190443c1000800511520f06102030503080f0190540113400445e5180b60f658404241c101c03108005000c0840a084190091451403600071b0039088103101c2c4111032124110001088005101180d11580c0a080c0780c040c10840400c0030249000808008e00950245529001c0a0040e502d00304a86600316000600404030356881d1000585d0140c600888800501c2400c0200403080e036144560100a540309650004a044082c48002c000c042d0090100d030194410f60403d10210f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 701743705 1250 701742455 701742463
    0x160b0327010e0616030e010c090e0711010c0e04200405061b061e011d060108430206041104090c0f0b18010804030206041e05030304060b040c09031509030e1f20 70
    0xc1d07802b071465480301d9240e0310b5044038510501072104246520300705500f445039034441d000c02842c001c02c46082c0001d00700c0e40e241492800003c84120303031062081101f0070250604401400500c0d212140707095405c404810701030300700360048a0381c3c40c8440c154a91032615480003440c20340500304030180b00410100c0760038100d20341c0001030006410702ca800c1e40001c41c007032228580c8039103150f80c0035a008008402000c03017800e400d405140700b207200488100c0040501f8400504c2900c125048251074100e00200b5080c40014001008180d840d02092280400d801d24090a43c00090210400302c0341d540360010080084400680503081c108013107002031002090780040c4290300140c00580703184000f4400102c101c124a0720180c000d169000c0803040006012141c3c2c000d9101d070009032030134003083c20010700441d480d0722540002031095003c80c00d14001c03a003003030f8001900f862290924110340e09035880042c02d10750048241c0b14000480002e030100d4182e00401030401a03402d00e0648488201c1e1410340341d00c1d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 701744955 1250 701743705 701743709
    0xe061b03092e051602030f0a051b03031209031b031e04051e0402190503150102060103170328090203070e09030f07080d06030302160b0327010e0616030e010c09 70
    0x2049804107102042c4c9040d0301c07201c1c01d445d600408842c800580740840c242c90b000350070030a0f505401340c0f11001a007502481030f0004c00c220001c02840c40d014282180018010700078040d44030b18031043c009880c0c50303520340d0800755000b03074048000c548800e04400380d0501c20b0703000454850245000e110400c02912800c19410b003548502449050038112070010400078040c3d0400701561a641c901e1089100e5003080046010b800301c0382003d0424941b810040e681c030602803000601034507801402c1d15402122034091900194503a4902e141500305010624440303089242c0c015030395a41d00301860840c5820403420700144140c003d111940e2820030751454807070060003020a41c0e1103001820008000c001c0007143c02074036248400300708203a128103000f9a2406180b100007180b0b5000400460362002c554140c901c40e41400b0410510300ca84d405620503032104d00445026650b4840181c120807003003d01ca0140300d01003c450308580090714040c000e06507403d802c50440a64503008103864900c0d80103000b242 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 701746205 1250 701744955 701744957
    0x3041203050901180f080c180f0a110316030b04092a03060203010f1d06130e1504150c05071a0415020a080f0906060d030e061b03092e 59
    0x740782c0c82da01006a440e1086083c1c0ca43c00060b00c4940482e03940c2d0080d6403c000d440240f000c41d40c0c01ca419a043c8000788621902484e6480203150000d070382c0c00c0541c82d1090340301c2100300d400304e188401e06482c140e42d50025603c84800c0c03141d8000030311070349905200d588081da00481c1c0c1406000d09030345030650407004400d80369220581194254040390340c44a8214025984002e007150390350303900c0404071600903050049002d2400c0302600f91101c808410b0840c4c2c0600c0000700100c403071031403018001c0010204411680c2c2203000c1c20407203c9400e41d07a5140d640c8a103000d4804002c1402100340d0003c1101c980703811030402d10400344507010118202401065040c078000885510a072a0303800c00c01041c09502c6100006c042c00092000c02882e07010031118048d030b021071040200c6894000700540c0750242150410b4000782c0b0072000c000030030700c65012a59860302c0500340518018155049540e800046069000391f0344c0006944445070800b00050b9205940001d9681d0111141c006850b20444c81e10720707098 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 701747455 1250 701746205 701746207
    0xb0f09060618180304090207021f0e04020304060b03190201030608030406050d0509190507031106180420040914010608090d030c02010b060301150e03010507020c1c050609070f06020304120305 84
    0x580c00d201c040625420f04043c1d1001ca075162560341c0d03c4400650700180d022409590741990144c005c12001c00b10391060307449510f0798480f0540e800b0601009420040003941c206031a10030301a00e645090014444882055008011004c5180000f4041e05c0c0319921040b40e07948100000c00c20103504c50269440b003030003d0804240c0c0d48401180c9864030041481641803d08500c4003002080b2001aa20040300d1046004403810f40d135020401000d40242280c3c120504107940726440395140645c000542c40b68003000c01c4441394544003082c1080e80140d0040d0704100e650f40040a001e00030180a00d004200a1400d01001c2c9041c10300c040d2030394200c40031601419207502c0c1d80512305000307410505c406400034060a80300e40c1d644200b00c1c1e60300c14800d68240418030191401c0f009080c180a1280f1030241a001044102d2030901070003240c83c2c130030070100b012500260030341000a406200c10f0b400f07902c03520b0045c0105420a1519020401941d000c0015540200810070040e143c03200000d8001d50103003026 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 701748705 1250 701747455 701747461
    0x1091707111f2d0512101a0306191d0a02181509060f1c0c021c05071506050102102901051209012304080405041e090b0f09060618 57
    0x900c3c540001d201100d004044603101407040302e43d21901410a11002514920461b100c0301e6070003101c0c036130300e000709807403030401101c0510003141503002142c202c2400b4050f15442d4640ca004c940082c1c030030381c100d0000d0724107200e1402c40e840a803100c4940c1040d040340d01107282501440d25000c0010b551904680107500d54001c41710000110b01c00daa8141001800e140d5030362907500202141d66000c0300348004801420011000c1c4d000880c0701d00f01c104d1107039800501001192140110402540d00e407040c080000c10840c0300c0000d031040724401034031040100b004c00c5642c1458006801c02c0070260415400300c1c680102041c4182110498211030034904c5035446074840c00c200100c40511800907440704200b0020184110281d0562002e4020341e40c6000e41c01107100c002c0e038240700d41714043d030b8040e004010504c4207010524159000b28000010505111080041c010081c0c05903034040c1025134500102204000c0c1300901285202c0d07008803644042d021900d01940040c100309101c2c04420070700c021201c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 701749955 1250 701748705 701748737
    0x100f0c02010b03120d1e020a0306060f261f03060e0c1507061107021c0308280f021c06090513031b0503090a0e0414030901091701091707111f 62
    0xa0302804c06c101100542d1307a42ca22482c00340c0544007a00c0b841000075000c140c40c1441500c00c4d80340c162500d07500704103c035a0032010700c01000b0400e800b40c424441ca900401810062074041030701680158402c3c00e0210310380286214540c14200e10712005030150001a0700303183d030303001c03084116441240d0000c000600800604000382c142e008280d0f000f900032600f003c40f40ca050b084039600c3c05102e031003595040300c295161224230320425407001259194039803d00c103601185849402821030403644040050070b0404098002610801100c4140c0d80c0030350380c02c0705002c2c2000c0c07406103561040c08e95841da440000c0541c0c00070428640e00c1c040c8041c110a6925080030007a042c812201c04071030007445400b02e0707601e42656001004e010b841c1203504000003c10340c902218040141c1c0ca0a00050319510310040ca889840c940b00f4180901545a40d5a0384039400000360304420030590729500c800305d403500c810882c68440c200541c541d154038031500e58540c5884854a03214040300c030030f0b905450315805210791440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 701751205 1250 701749955 701749991
    0x7110312070e0406081608010b06071e050111030906011a030c030a0e060703020c100b1c030513060c06150b030c0f0c0a11090a06031e05100f0c02010b03120d 69
    0x3480e90f000d0b040401c0018001ea000422101ca40c003041d21400480750f4030802d403401c9032001e0042d00d8220b0310611901d00803503415900b0100500a084407603020079016504c1508442c0d046410b12080034020060042c01c0070104142c50241221302e030010617003406498614500d004c024485d140510b03000002613140201034004002c14620001101c3d941d062084002c2c020390450b51010500740301301004614004241d000d0310a800c0409494041020006540146a07905101042c0c00b40035081200d5a51109004802c070b006028603941e03090040d90038500303131081d5034101003031942c03901400c0024400e8a54030002c40380c1003c60141c102c0d81c1c840c400421001c0714010010081002d01696403900e09010310060042000e89084490914595551004e901110660700004d030542044100242d480300400380c0c4015114011400c03560301d800705035205401ea4000b4404280340d1504e940b42c2c1c1204031340900688460000450141c0311603040c01020f8400c5028445510310020380741c0050084400c1100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 701752455 1250 701751205 701751227
    0x803090a20040b0a14010e121504020a06050a080106030209012d080903070b13060f0e0d03060803310e07080103020a1d0601120e070f030b0711031207 66
    0x382060210807100e4004280e1060707100001402941042c503901050300e000c030b22107000c4e25100041c00389482e450100440341d02441c92025900540e5000320003140a20420180140e005001c04100b2103140500c107104403421580d20075400c3c080706000c000042600a0050b5040d54581d20b80142c49405240c01210500350030b9414a0010144e49042040d0117182980c0841d031400c0c5850352290790720349c03100b010380d28030426030003500070040e03200420b40f05401c10000c8203119005d25004502200e41418a1013154500701e940c110617031180c0307407403801c058160003039500410380480911308110851032004107100480505c541d1450103840ca810744c618170042c00e28040c002d50400503c25190071000503003140f1080c00b05030b11481180d14006140d1a07225120b4035845000f0800b80c4e0325803240d0340103540c2000c8916080b54010344443c54552210820024600101034850403001d18034a1400c1000740c04001901c03d008204000304164018a0004100c4500c1d040e01e900b10203c0f030307450781c5013107031080d00c09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 701753705 1250 701752455 701752463
    0x9030807141b03030901060602121903022b0e03091e0a03121116050a03031b05061303110606060307050d0b100c11010f1b080c190308010f060c0803090a 67
    0x703064031034002c8000101a600c00c1804400030482c050f04d13042e090713a46400d1010303118000c0408101207034416110300e140710064900d906000d03051070112040a65607000c5020044400311a005084c0d190b07800c40e0054140c1d210518001c0d42c80e00d040c070303c086594207030607503100f0009200280c01c0400c0b0380c4510884030000e5422900108c404103103414020000c560003101c480c1148182441d103a180000c0c40385000c100e880040c00d5000c41071440d40c054031440c004c03003001d608412070102c42101060041c80140e02c110750f001407046466500d403402410b907040040031a442035221400f000055102c0d1021030303401814074200b181d2140d612081d0031003c0d004031803101d904280b40124a010300d0303400510044e05d29214800c03041c8602c41d00801115207001090011002403021900f034011044103585600c1503501906c40113242c8a1068040f5150001d64040d10300800e40803c207107028998010042070240a00e003480e50a03a51170100c0042030740c1c0b4a1540501072400000110341c034107104000842c2d0180c0d00c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 701754955 1250 701753705 701753737
    0x6040b19030b16030225020607050a151503020607110d1205120109020c0715090302060f030105190e06100c1b1404180b040503070f08090f040903080714 67
    0x220b1401d20102141940c06800c0315121001c20400c0e24001c2c000d5600825a190340c002681401d4501d1130f10310070102c0d50582c1c00140410804001c41c4083c8400d5540f940240325200721030404809034002c403100410380c90b20803521590b051005981d00002c541c402a0041c0c0c8121900e9409400140d4070300000c80005c00003045c043c1c1c0c8895041d044009040d0400e122a003042d404d07aa00c8013280d05910403a250080030b5006101c0500c03003c40030f8691080303d19040d14081d500c0304c1d00c0342d000c0366055104d080c8c403c07000100440104103601d007000e440040515000e83e4810303902d1514100f250074440203014548a580e00002031800340d40b0a40c1400f0340a078001d11842c125480b42444038091a07440c0c0240601c50704003c201c14002c0c28030303008418200b2a166542c10310070b20306031101c1e0700c00c210240041f242c602041001c03a002c107005510f41c0941350300078039103240e1340c0300b481c0201b060951480796500d0141d820094500c0c0443e03000742c05d01e5800008c5050030b00c0503009481c040e4000d441a80c0a9040c0485 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 701756205 1250 701754955 701754959
    0x10e100507181d0c040e1803190201051506130311040f090b0601030e010c0f031112090d08070e010905040902041e0608010b3102070606090b09061806040b19 69
    0x46010496080d0010301492402c3c5444012515000f40b040d4040e0b003005040030300c0420308050000001c105a0609002620b080c100c0110010840c00400d00c500c900603915070045c000c04c4001554014891041200c0140c41c0507600c5100c0d1003600228800a4117140180d00325100644540e00245903c43c440359081090310307100d20700039400c24001c0da00c86000074039000641441240512510f00040d2481e02e9800300200c8021049020302062461407011032010300100c2001c11030b45030407500481210020341100c0000031002010b0307a000412110030041141e50015844c0d812010003000d032001550003080000160000c14007420300c05010492a414039101150f00480c980d10032000c0c0c0b00440000d00588448104020390030581000c405110b91100c080c00715286c40001d035008400410440142c140b1401d03458403c1214090342c40a00d401d030b101c8421103040e142000ba01030303000e241242c0c440c0c40b00b402e01071559440d41e00140300034080c0307907a5020441c140d43e070712804100d00c241c02c2d0240d284090f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 701757455 1250 701756205 701756219
    0x120f12021201031a0103021e04020405180711060c0d11120a020d060609150c02031207120f031b110724080601020303190b0f0402130611010e10050718 66
    0x3600c03d00c03050f958198150010298141c1501465040740c0d0001c04552072403840b00645041c0b4118180915801030782000006000d845001641c1c1c284082d80d480750416140400b0041c1614030060b880e4945604503c3c01c001c0505c82c0c400640e442142c030b031800000c41c0d040302c00d803d980500c10034070540c1a000c1900e080059215413a0000c0c184051124070520415a940200740d901302c219015084d61a1107500804603a54400c090041e80039000400f00e4540c60020020082c0960000c24140c3d18034030292081c4100c50340100c102c020001051400700042c02d0000207840c004503c24030300504100c00344000d40c1c0001010000d0381d014101300c5001c00644a60540545036058a8001c4d601c0170a48040000f43c0640c0080143ca00c60505508022803440040e030414004020b5181d07040d500001c0390135401690340740c0f840500707102200a029491418182500a0540f00790f81c010001d090781018000c05007040c0110f5680c0000c3d1071100e02207500d8660320400e8800c14a80000700c0f9410800e020005151 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 701758705 1250 701757455 701757487
    0xf0c12130201090f0308250f030c2f010c030e12010209030d08061e0112020c0307050106051002030d020d060312050a09050603010311130b060c07051804120f1202 71
    0x4207100342c8814541c1513a50b041d0000301d050520020b404c00c032042c000c1d8000b5100c14512800045040c0303810103d01c3c802650384081d40441040c1c01d03000203a10f048900c040183e40000c003040c081c96190600c000c40b007041100050344654010081c100b1006401281c20903008007006a080c0340000c00000401c410300300124001c0d0070130602a27100b44594600c0c0d414044c055000e050160344090042c1240034502030a505000c1040d0005a040103101104542642e489102910b1050b003840091507881849081060954101c1d4002030310440241e104100f1301034000003110356410362040c000d621034845003010310050840f98006001034075042d6004510641c840020071004020b0348a50081303d0304d0300240310f02c600090100406034a030118078072050345400240c50880030b86418010555018140c04034000350045281d48646038000f51080c1310600d0084000e045030840650034840c145010780302c42c2c0c0c1240003030074080d0a21952810803d2003d02c9a40172480b000180002950380b000c0d1110000c0d20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 701759955 1250 701758705 701758741
    0xe0c0901121b140a1401050405060a0909050f090f0f06060409030e0306090a030801080a0201050a30051515030a05041a010803090114181504050405010801090b0705070b0f0c12 77
    0x1c52281560007040c40c880c6100e5034204117406942c5c49081904080501485501441460040c0300c45c900e8001001c1c0264007910303118400074144030540c0e082c55807500703280410095448611742c100200d81c5116400004699501c80f0003220003240100312800d0030f40b0300c5003c5c80c8400b034050141030108440408000340407a1030521960b903540460b80e03102e9001703440301246100280011000c00115200d10711030100499034044010380d2468041280345164010342c002c40301c0c0c0c001940c4440400c04628009941c4052503c02510f045aa048884040b0401403100500541c4510349ea503001c90203210801c0c0c3c019500c038041038000481c2d0350711064810343d00d0b04407150881c002020071002c1d007040780b0302905859041003440c43c04150050110100003400c0e0064584884562082c0000a2140c0e114080e15000304151000041c0c400042d041c28050310350018940420b100040149800045084035090382c058656140b2002d55101c2c444106854400d200c01e07110381c01075034020700c4410580d4081030301e2 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 701761205 1250 701759955 701759959
    0x9091303020601051c0813090e0c01030c09050a03140f03030f0f010f03080315032503290f07050f040305160806010602100504020301090c060903060e0c0901121b14 72
    0xe256070b070310301c1080000d1040b0812403d805003041585c100041d194800f03040101503041000141d1358030f5400c2074003102d000c0300041d50168004098403115580600c0385140c40c004d2031a1040d01c1c1810400480d8040825101c000c00800300e17031528944000003401a010812000310503603550b8101451913100e070b43c00039202c2c1e444c4d10a022000041c0c49070301c046280c08403944218010b08664500d24070b00642c1d0017101c200b43c1c140c0542444c6000f484c2051928213010044800e001a140d800c41c1003141a40c03180c2034521019a041502c40c203c51074040c41c00a610101c1b40080034031640e1140f01c100c445002d20030341c0d20841e1001250100c104840480c98a5040007501e01079150b2550320710030030356610300a00c20800540c1103004401d49c2000240c00403540103001800100390300034503544180699400750703c28000111601c4080c0200300131405070a6844480324004c20341c5550800000720011818400c5020481e07801d11031104104100724100100c44104800340180c644e26107101107a45028400c02d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 701762455 1250 701761205 701761213
    0x170d0b04060614030a0908040b0c0610050a05060a03060f0f091404120e0a03021809060a14070c03170103030806042909060d120e011d0310050c0909130302 68
    0x20126042034820001180c0e850350740c0c031241e000f02e40c03c10040c80d4070103403188200f981c640d00b807140850341c041c00a02c02804041d80483da038520104040d4140400507040041640071881c04000036981c0f041c510701a6039080360500e40ea00301c2403a0507001884598049900244ca03c400002d600e802109184200c50380d1f4501446054540045120400380c212001802c4d001c5920b0b11030035442c07083e03401d000316610150014004540740c2c3c0015420401021104058018550400c518108280301894100a881c00c081c008810303d007c003800003140007003035141000050003058080c948180c0d03202d00600c5445d07585241c1c5507141d050003801050b0032a04503025508181c0c00340340d1a8440040c44000041e0181e50000601821082050040000d402141d001c051102c01601290f011a1206003210780307916042c04580051001404113802e00d41885001303610410115503549000c910f44a180003800d038001400e555080400d181400350440031904000307041d08200e00d50314244c2800340e18901a030222 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 701763705 1250 701762455 701762471
    0x20f1c1e0209010c2d0b06120601230f0d0501050702190c05060a18060f0e0603160c06020f0a02010203060a05030f0307030305150915090c181c170d 65
    0x2042a0700c0795540c9140040c8004c010b03c0c020038007041c8001180c0105454040307108149036440306045100640a0341e07541c10350028480300c2c0c0750100075141d0450342c1d04050000307503152000303441004043e00300e259400d07910b8105d100215900d80046500c41ca8008111000c0b420b01f40c1807072402041d0072146240580310b4003a0b80961030704403031510704605030b0024404034180e043c10181312003604003050020621410b0329124904601c200312141c085c4c56031313507200c00030f0404d0603600906848184284c1c038080d003800c06c2071002a00a40d00310303000c178600342e04000c48220410700e4454000d2003910801090b41074080b542b0040d0316819001580192021030300c11500c552100101b540307600050700d180803d0391040001c00000ba019400c12036100034592186100580100e0106200e90403c440d80e0f00340542c0408c040203680707002030b0003c0d00680f03009601802c0c0010b505c404406600200011442240c035a5807401a600c020500e1000440e80410050b1103615a640ba80350f15801040d5201161030410141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 701764955 1250 701763705 701763761
    0xc26070f050f121605011d03070b011508070c15020310090609020a0503041e05010c051b0715230a03020c100902030a110f0909032a060109020f1c 64
    0x11501e049001d8407010713207091440720307080f03502e9001c01d5000c0364a5500c039001046030a0300b0710744d01c2c07407094000c01c003441d9541c203640340c9a0307103601f4140c00c090400101e02202d540340660006483c2e91012003800c00e030b05800e9441c101380481541d03283c0c0440c2d480c4d0000082103900c800500d038007401c5035400703441403011a4454061105034002c49400d000060790a100007000b04140717509400d400c41c03180d000c1f80c00b0210603466040c00d66081ca2000b1021a0000030080541c03580d41e060342c0e0384060b1000c09803503980e0411001450b5012040c14100030041303800219042e449021100b21012488051925641c0410805c050040e40110b20007185034002d0440250401c41907016181420b540200030340210038440e550701c10b188000ca9003160704450444001581c41d152941d0560043d01188011070319440c1414540388e0070801c51035808c4a8a401840819820720700041c040c0c19112658005a02c0e02c3c80296400c2003405a07502d112084040711002c0584000c00e548200446c1c1c103003c09060300110b00040d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 701766205 1250 701764955 701764963
    0xc0c01020c0d030819021204120e0f060915160c17060c0706020910081b04030317090309180105090c0306030a020f13090303021b0a02010c26070f050f 66
    0x200c258200c0e101100000000e4804c10035130358040941e400b22080700039a103914400f280c02c4803d910360030141d90000c1c441803114503140d4050440c003900d0406001c4070550041a006a9940c5066005178030124044800d591000d0860141c0741c01038090985038004501143c42605640742c00b681d02000b043c202003031031b02c8120502030801d400c20000b0005a240c0c50000341c1264045101a11190f0b800d1148107429510441d100140fa8182d585001e0380d410074220340078a00c1c00c400da00c8800802e0401040000070340050490001081951a8007006c0c1c0d109441b45041d4424070214a0f484236192003405c40e180124510301d0305940302070740c040c0000d07611220b10700254402501c100d40d16070700c0b00442400500d00038284007034221002d08400d4001c26604007210035141c007160b045011940205040b07084620742850b6041680402001303000c0c54440b0b0300081d1503012248009000032209200e482089446010607444080f03031144201c1e907a000030f041400200e0b115640031121030103540c40c0f03802044400070f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 701767455 1250 701766205 701766223
    0x60f2f03061008060a031a0703060510270e0103030c060506010e010c0f0201020f070b1809010e04030503090f030712260a0e10020d060e090102040e0a0c050714030c0c0102 75
    0xd0031038001da10b003501e42910040c1004084a501030141c050102c000b1382800c028410a2580b920003050500304108003405503100f6030441c40c003443c1d40e000014489a40200f03841c000d0381c009006e00000320300340074654400e05c420b60001012604400000410140c0c0540e26120301401840304010548483c001181c180c65030110045c0020450349000c00410b44a6280341240e610500442e84004c800c0100d2900f0030340242e20046800c50085a0403c081440003d0501d443c03400716241c480560621404194090020300050f0820030003100080c0d1a80040008101103c0301c001201d484078001e1504006129400e00d11500103108815800941c5001920305074280c0300c00d103600000c0e90341da030300c604008251803045a001c500c42c0440c841c410104a01c0107109024000801268a031f05206c0d50500602002d007801800c1da1040100f00a46c0b0100302c40190803920344100865078640c1d500e4115141d005224002e0036007051034007601c2004800000601c06c8481c41c805903034542091071300590301e6100c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 701768705 1250 701767455 701767459
    0x3060a02091819151404050421020f010905030301060e03060f0712231b0c030a0e01050c010c031505100816140a0503040c1205030d09060f2f0306 64
    0x200c0020341c6600b0307540c880780d008241d0008503200c6210f86841506540e45048258aa40c1c200c40091012009030310094408101c241c074140f09a0a142e1380d005e009001d01500188021034800101e10755030702c05e0040c040f1020f540e0000344128882800c260f82c483e03000780300d510041090002072815501300440e400b03125810394001194a42d03903030070381668808004100c18441d41c0c1e80340f03400c401d00c02d51a140d601c2c00e101ca4800c0b94005261068985c03035001e01c04800d480c075416041c0040c1c580007400008484040d4858a420b14441d007900f0010380e240d0042c902e01125550070300d14041d001d150326a1104101000446010004a81d00d005220741080c0f403141c0344000404540c0000d841001c281e100000714040c0d842c1290010015180d0b07800709401654501000075000070901c414044101000c0d40901085001c00c2d10b080382507691560349100c1c2d0301203081e9040c0c1b581407903401d024407540008000c001442091003558802c0c1070f44a0703030102d0542c0390b40d41a00e4000b044025500304805503440b1f6600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 701769955 1250 701768705 701768719
    0x190e060409150c020a110405010807031103011e0b03010f0e030901050f04030f0b0f060103110a0804050c031207061a28030203100228140a1e0e03060a0209 68
    0x502061102030a6200390a0780d000c0781d10b0b84012007180ca54030a00c80c06a00580c054101c40040385080e0148203000e135550707407003541490700500c00382078081101001c80780e10030400d04100390104082070141996a900c252861025441074849015a4000c0702065601310000c105d10b488444c00d480480c0c0c00c41d04c820000303610510056403154007800048c00c0d404910900301d030803d42c0d6990351019054464404440541c0000f0910036481700300c1000c3d03900500c00742824080c10a017084c02da0721034040d20300c071141003080a0300410706012044c800d007441e07211301906540702c901441546102e580d02a100c21100b007881c01d054924070444d00324501e03442c954028900c804405220403c0329040d01c2034012820b01039070040000006940401840400716107400015807035104e4410701c402480801202041084045041001490f9214107a203007031002a14000d620340503d8481114840f001050a944018150a100b802c89401c038040d818840002c40441d0b00070395800728824144c0c0540588070b900104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 701771205 1250 701769955 701769961
    0x305060112030203070b04030e091605030c030a141602070b090616080c060103060609050903181002011401030b040c3303180c180b09040f0f08040f05190e 68
    0x70464900340703801d001c0d00c120307030420400d0340b916001d0303a0b0283c0d8100d001c00c11111408450b81815424954001140c15070102000f00e400b00103000b601c4010300060b100200040041c1d00078055a025520300c40388958050b10b10324005105400800f81d040c400c42c094400c01e2000160004118203c50201801030001410120a03544004084070080d000720340000e8144061601c0c0d0900704001c034021405480085465440e05042208548028142101c03c0d001007010a1175890000f00300118030509a0f450042c0204403030089004044d10060b8000c90310203400000705021840c50b00a0043d401120340d10096a5200d881c00e1072405070810b4420041401040f6140c03100342d030961508030b1031140c200030512411040d2034403c41c51170740208441c03100b41c0d0b9409000d295031851501d15071080300f100404c80a200f81002450710a0010710081c46400d22031800800c004400d00a2043c440e805041662610348501c83c0c8038200d4400e0003464002c490350030030740c020042504070702801c030380c014000d1101c191 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 701772455 1250 701771205 701771219
    0x6132007020103060b0f03160801120b0c0904020409021c0507092d08030a2a020d02030c04110307080708071d1f050d1808090108070309021c0308060a03050601 70
    0x500103290903410f250740c42d50001800c958a4000740840700381804e24aa50b4907108240300c00c440d0702d803d1070b80104001800180f2081845030304202e021764100d9090a81c1d0b96410200c000b07648aa000d606421500200300041e124246802800300c09014410b41030120301524080c00403075a088440100042d84d040d420014680441054182007959100100b40c140c4503450711b201c0744519030701004880c1e00000d5010303003807688030f49a044015241d07490794030100c080c005c50140a00001710040e00c200100c0f4410b8045540411402c520001d000d0418407040380901c0d40901c07160021608100403445c00e030009540d09105601080c4038841c03940798801c805c039030b0801d0549110280c80c126500205104030711000b081400342c4508885190340d42e0b0381d5842401071100c0d02a20303524080540507401c5640000d0015080d03000395410441c085c1b81c4160503a031001000c43c0582000f05e0041d4000c2c0c003029034030421111403031140b80e00074040c2d20f450b030080d1554801d1010b03043d41da1101030b1250b000400180700303032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 701773705 1250 701772455 701772457
    0x1303020d050307051207150e1b030708060403030e0d03020a20011509020a09082109030709050906070e0f2d0613080606011e030b010309060c08061320 66
    0x203601600031282400200d0703a0b6540341544201821030304003030200d08141040a02c600d41e0040f4220400244038042e60200c669940c0e400307107122440c01c101405911017942d181003143d400108084e20840d03255051a04002c1c00418080204070344a004803401c0b03e4403c1d00034021aa01c84040b40d44030032142d0348a10340d0f560b907040200d01d50a80e654a940d1002905c416900c0248003403c0030071001603641002801c040d0940c1400d0740110b0450308200c250340081103c6034131740d944c0121040c900d55030310030f0108006401c03d10942c1001c0000351600051000958001a0183c86500d007500c88403031103104d0200f00320b5108071480e4069071004101c40c010f41324855020b08014005405c5c03002070308407102c2000061060300f09009003200305007904000c1050010411080e80c11102c00c1c02c140b840c03040100c0301108008403003404a828580c488240c0e8809910a521407400c0b01d401000c10440200101c000034070703001096a03910f1042c2600021514808800d1240c01c0142600343c200701c1000101c90400a42 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 701774955 1250 701773705 701773729
    0x1509020a05030a030807092102060304050f0a030e0108060a051c02120f0a0c050f01050403140a080a0503040b070806031506040b03030301170d022103090a120f1202130302 75
    0x528000507403500d00300f0038580c0481c401c0d103548150b4034000c80e0007004400181d03c0030724119985a52965400b9148902c0c480c1190140c0340e0907a240e80300d081142ca00403442d09014a0303031080307204910038540d101440b445940c030240d9480d007894681c01704001008070140600c44d400300311000186140d111103004014180e102510b11611100c2e20010346090a8414411084030f8205062600806c40c803000a040038120895005c1845900800000c0c940d018600000b029054403040c01d5694100400c00881d20541c8031030300c142c0c0c4540701100204117070015641241e00550580204043ca80512411840790700042c006002280312580841000100a0411038015507512007002c010f85062000358040d0820300c0e00d41022050115041c7e00d0500c1c041203400454002000c81c109041003084614040c546c05010329841c1c0d12103d40e44c078104588444010080c00045210380740243e00140c0ea19071040064441000e9002c04c03801e24016842411442e0b41c04c5101b401003030006150808007007007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 701776205 1250 701774955 701774959
    0x150f0915031b18050103050d1b02091939090902030108012a02030405010c08160b16090e06040203041401060f14010c0302060714070b0a090302010c0903150902 70
    0x9009035a40ca520b541956820144004152210010b101071100c40e1140c0d11046040c6004016a61440d02c0b0300da1a01d460905c28000c02084080b142d0003182210700480c10076400410301c01c6142030085104107101c0310070410300000e034284400300300700c002150341c0a00c00e4440807030116031080b0444840305c10884200d040c402840001303c404a1800424805103000e40044000050031030b80c0c4040740c0c19036202c1021820b501c0d189600d007000b901d44d03000c82a18112507083c00c00881c00c0116280560740f40c0036002185e00722441d0b149241d810f100c80402c400e405040c0c888046003600b599500122103036942d6000ba600e40204040c046109070810741e00441e4030a000781e5460b40082410301901e800d4615681c4440f03d02c1c0c0b00408280014071802c0304a05041909083c1424142c0007554041e40315040200362806000c600c1c513000c400e0f2841c0304c040300c03649a403040040c0401d18041501000070440218140d005610f400c00c4000180e01074151007040d81c0e00044801c28001042039080301910445808907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 701777455 1250 701776205 701776241
    0x31605011211070f0302010e0706050d0b0f03011e05010605130b0a020c0a060309050d08190b04240810020f19180e06090a0b0d0f0606080706080901150f09 68
    0x2a4282c2d000c0e402400c2038601c1103810480c8541ca03414000d082d04c02a8035030710746503000510101b00c00c0307400c41304860110b00304404c0810b40d000510005500e04a80104268240d401c0c100d941000c0140640d1104402400007010803050f42c980004803858020071511401ca030315442820301030081c01d18003800c01a117652045500d860380580105048651660100020940740d00700a000c015042c004c3c0083d603040c602d1310025505c1c0c40640d81291030040581c0312042a50f40203d410f164865411a2000c150f0b20104480e103514000f402c2d9003194841c2c8105209800f400c2440c880c24004c2d802120b000340a25122207050082e8804000480720000d041c01051144014940e80d003450300b0340c41500144103200446501d4642074041c0040d080d00103000150043c50a80080c80503920007820309803164220090540039105031414000800c510781000900c1d2289440c00201c2e59842014a40710701c01e035000034840031610342199090713417595003d080802040c020051010303000c5544200106220080c0b11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 701778705 1250 701777455 701777471
    0x12080904060f1701050a11120915090307030318051c020a0c1d151020030c0106051e091803130609050102070806040804030803041b09090605060316050112 68
    0x1185101c0d007030380720f081c5002d04140a0075030a0310030b1007410392240041a09100345410400445420f00c04e064170b04403082c08203030202d80d00c0d050800070703201c40c0552840c000c905410600d880d942d40b5005040d04038006800d000e01c401c3c0e201a0303e1800c4688a9100300100900100640420202c043c145940400c6108841002d00070504020a00004141034010f20101010640c00c802d071308070340206140046842c040d4604650384494500095903030003450308041d101d5000341c50700350b400551150464644000314000305aa84198400802c9950440b100240d4815010320700001d81145d401d5127900210400c0050944200301c0031142c0480c0e0050b0a40b0314043d07841d807401e0903070b510903040b4030000b42d0003074818011560104882400b80805400518603441c0996507072945100e06e00004150303240c044045010414500101e1000d04030a044030b082070340c1c40309010300c001c1c614008140e800784e0804000c070f4814200452410f00800c075040203100864140001942c1c4803c440d42890040c035034401c0a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 701779955 1250 701778705 701778719
    0x141612120c080f21070f030f060504110924090f120102030f27071404091502091504150c0c0f0b09031018030f030f020d1e061208090406 60
    0x1024107102c0d094040340c80c1c581e48044600001301d5080039108201d0048144009503401000781d030000b0f000d03480c010501050f12800400600030580c0000d0300306081080e8442000e00d00c00c00382141100544403403100c14042780b034103030202800a41c076240e202c204001c031000b1030916941805801c3e4028145000118407602c1040c04ca0b403048400400300e500e040c05122100d00030f40c44801449003001d0710540c6105c840c4043c1a107420b540c1c414a401401041400040b130b17100d5820050f00a908920482c60343c60881c590403010707512891030f1034407e011840e488140241d29900b07441c00d48240200f00061030101c82d01c180da5641c16000b01b5524202c40300c800041d155603256001000d0110500000c0d11507142e00281407400e005100c44c000c00c9800e12800e074605000d0310410702031064061402e1611041d040809038001c0008000b40d804003400001c030103001c5112a004050103401e824050b94416501e0300504089401134028001c110501c00c07245804241407002802c01c4410003000003502c1589c0d115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 701781205 1250 701779955 701779957
    0x30f07081e0f0d0c1d090402030a0c0b0a0201060b13030803060a0504110a1403010e04021c1a01081b061e0f0d0506030d0c020a05012a141612120c08 65
    0x400c0800d10000140f240589480f034010f21100403800d040a4558640510543c0c0c00c042c00c020307001c0d0142c0c01082c0082c1c29541c08100004200b07804c03401c00002e03980c682c0c6070707882c06602c4414041d000d50b0906000080b00d00d5100100c915100750345410a24031411aa6001003d61004e04010f80c440c81440002c1500e5a891061403428a045410703265540000031b005880c3e132001c1c20301d425043d0402e00040201030780c41c5080550181d811a103080b07502e41c64a07007000e2001a410f0000d1b14046087c0c0c0d8610040303111071304440c1030321403000803140313061400f501c0c42113a120740030b001c0354000e0381c144207100041140c40104040c010700e80c0300460600320178408040e6aa0000c43e144020152101c091000a05052003500110b9149180c5107000340c0b4943c0100b020f81109204031030420100c40c120184490901104031610140c913540200c0d2003a06003042c20001140b0001040d01d40124108601d144810b205090b0031103143c0c1044018622650f110b808a03403101240340710a00c808061002c001400d908 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 701782455 1250 701781205 701781217
    0xb0d051b130204030804090e0a05070f14030a150f1d030405040629030618070905090106091a0a0c12030632043b060702030f07081e 58
    0x30101600c0c150030000303985180807080d4040c0d40b04200c1840841d00704000c4030103a80d040000070900c1c800000e5a14542410a0409065401260f10200e000c051100350300b4202c1e284030b030505400e6043c50003010748071300281600500604212101c10040169a0483c902103080c41900255688400d61810342c00318a400a8200a4200040038090383c500b922900010b01115140e50682040c45030307009a03810280f822140e10410003000041c0035035a606101c141c1c50003401c628000d141881400901046202d005092082c40c90000109a2921420300130080340c22032840740c0184c002c0750040c043d050303002112140400503102c0303061000ca8009407000c00d9112903541c1c0040c10520b08110359000541d4001c00c5070795060b224148040c0136035035500701c4052083c221000154442003e901341c0058801100095403581001c5c3c0100ba10b1480500c0c1002c04990760055580950714110120784078810802d082c18941001d005440c0819583d101500110b04038000701205240b4292101a0f183c0140c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 701783705 1250 701782455 701782483
    0xf07030203281b020d0609030309020411090109060806040906021317010204030803010b0c010605130c0809010b1c0809040504060c0e0907050d090602071209080f0c01020a060b0d05 79
    0x284041c0303840420709807200906440800b0b00003000750410001c148003854001500541554001e08043d595103d81c0100b004c1e9000b00300300310707404d1a40380c040c1c080c0c042da0800364410342ca40301074440403201c94022546031000507991070200c6402c041003a510b4140c0030382688e420683c1c07403c010700010a503200426504004440051000e845c2000300c1302c040210450744a079590062100304000b400190a0740d06642403540d080b80c4407600c4008460040c100c681c007a80d40484c003040000000340c801d0380100c5600e089555213544d1503880310886800d90315800134a80d007110300c8044010725480400c0400080a2150201514202c401400170f01030761020385090712400e83d241e266041702c0d0b0f044503100b1400c1405940781d45003450402c01c05001d40c040c5480c428045529024120104031195040310b08030342d840f036071201c07601d1403a041c010729200c1c450050b40f10383d100304402d0074401c43d40047e0000d1102c005074020314101100341d5408000c1d000c410500d83d00034961500400010300c3c2404001c509840d070b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 701784955 1250 701783705 701783707
    0xf0907120f1b081015180e06040605070e09090c01030203040302160308040f082b020a060204090b090f0103110415180e16050a1a0f0c06010e0a1e110f07030203 70
    0x505840340d08006001c0101200703540b5203005170701111090700c4440c00300d03515103c10700d00d00d0140c072580c44041c09840c03000500d1801010104000c1000d15802540a006a176071031840c030b1000901805006881520700ca10b00c0d40c8803605220302984240c004542c064401d2061764503a0901a519200c0d0312602d420413141d0b048007142c2403000040c0081c1c0d00009244245c000c3c03c0200c08850841400410422114103032841300700e04000d19402000000f25056001004550341c40e0741e0901200104182e42e205032150f000d0314007245828903400842416a41c001c840c20b0070f2280032a040000038030b032252403804641d02c2d42000040030a00c031030900c11182d0f403080c400b0900d40b410b446aa414640c850900100b2203403085030600450319064a0340050ba00002c0e50318103446420b0400202d10700880a054082c608002810300038600c1c0841c03503504a071142210780e90b00362031300c100110585030004c00c8000c180e60305184400c04906680c00c544541904080d815203440a24040703030b022980140415005a40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 701786205 1250 701784955 701784959
    0x303060306151f02070b040b040306151815170d020705030727110a050d0c0c11040f090506090109020f0901060206010308180a0303080403080f0907120f1b 68
    0x1401e10450381e0000a2450740380302038a54800107000361145078003000c1d01c054034a1141d040755008010405c0942118400030f03484035550b4812044c907034098002118444c1c2012000400c8805d4400082c3c151004009560445005481514000c240641500000d02c0c070044c000548140d200044903890341e05140074103e80c02b05103a004e4a800c20a0f400503021303038032846c8100000a03460080d410030b661296a0100a100b0510f81540079100c0b00000d4490050b000412909070350300324006000d07684480c0d8050100103c2001d0544002007420300152443d10030900404071858036a100500d8071440e40800101a5003a48800f4a00131048a280c0c081d699601000015460840c00010450b041183c01038020360401e0002920359406200040c550030f004190700740a0400c40010700200407000e01648101580c030b0800400e020415076055001c115641d000c141d4560310800c1403807060490f00010b09a140c500030031003600c14070003041650700c0c468400149000405502246082441494409280c28 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 701787455 1250 701786205 701786209
    0xc060138040905090d0f05130914091b010f27060509040b0f130b0d17041721090a09020417060601021b0906180a0501170718020d0b0306010602030306 66
    0x159001e0442049980900303005c0b9040c2ea801103000614680d1440e1240e103030010000000420240d075003214810506040c5240b00c142c210040c568440c58450040303c40c0182c10300e400030103a12055090300d00203800e1300b0340c445646002e1409440500a80d41c012016544100d801f00104040f80e04014000b40001503948141d14050280d564100412a08004040f100380700003901e030b62000c040400340a858240b002010360711990444055a040b0501518501c89003c0c0080d141d07109020300d182900c01a124040c42810001d14500405442890200c0c1c1d00c0310030070442c407a40c210303500d5940d001020000c0413801d20f400b03001070001480460149a0305481c803812460070400024210741c110b40c44050300c0501d041d003441c03101c50b0881058414528603155403000c00d030442d14800341c00210711300030824440d4040d074580c40a412558104c25034820b110854904c2610f90015104200038118542c0700c074074100c1032a500610a009d0780400010380703018204086810706d0800d0b44804003503000442004002c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 701788705 1250 701787455 701787461
    0x160302010e010302090901030f0c08070e040204060e0403200c19050901052409030c04021b1c12021b070e07020106090203010b0301063606140c0601380409 68
    0x441c24203040d4100030000021484800052002034803560024110005001c070307114900001d020139030240d48a01c4d4803558a10035420080d101203024502c1c2181c001400e0480d41c0c901c03030155900d0f640c1c00381d210700c07015110b8080a41002401005019404140c0c030710b039464200b01504c0700540440b200c24a0b151400b00300034100c05034041c81c010f0034980c1c0300c101134500d000c00035011050300704442c6445e00d003e100400e15250307a040c0c01e1a0094800505200d032541c11010301c540e0601c600c81110380300d14942e5252000590400220404903014010015000240d50040d04c105050b0500c18243c0c4403618509500d8241e00d80d00c11003945040e40d0900c0183c55085c020100a2b00300c01e44198615454209110000e2105208120411129049004640f1002012400c0310341d00310220072184482c2d81e4842c0450b128901c518070200d21500502d07070f85070f0343c2c0d001a036502000c0e240103000960300e03244074112680c201c121011505890220a600023020500a00c0d207041e4041a000d40c8a9003000201411 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 701789955 1250 701788705 701788727
    0x10e0307120c090e030306060a03110f0706180305030c090f131b09050f06090102010b0a091a010c0503090f03071e0905150a09110c01050405011a01170f130516030201 73
    0x1c4c0c01c0c1280e15000343d03000022240c10104c01e5441303d680e8210540120010012000403110080300000d001c0215603220002e007000c5400b86e401081030140c8126a0340c049920400300401040041c000282105441c2d800b500c4c2402018103640100c0244000180c20381f80c500000400066807071595022503451480c2120a01da240e080040c40c8904080005143e01c05040a691084c2c07000249803d05074401c1d044400003000103007010754030030f40350301841d03020785002c0046041111140808481a40c851395006503140c1c0c2250141d881c0000500900641c4000f0194003609841341d41800601c00380020062043d01880c0c42c081c00031213040400034010349801078410b070641c3c00c0707130400f180f120303514000003004a41c0c5d9400c4c00259060105c940c282e05014154190085518080c100b01c241300c1c06400000b2100002e0a4529115010b00010f454008000c00f4171480b21048000240554540c100a15004068490551800e54940c1d42e000e01d0804040350f8004648107420042045581004203030803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 701791205 1250 701789955 701789969
    0x20a03050f011d121c050711060606070c03020609030a0515040308070c0228080f0c0a0605040b0301060e0409060222090c1b06180807200d02060306010e0307120c 71
    0x628100f0740144075664800c0002c0348540c00700000f50b440c0d000b000d400b81e5240c1010ba245000c1c8031600d08880081d060941d0074103400041c3c010100002c15501c1d1590440d41c0d144d512004e4540c8050445d005c0c0308103500712100158241c80307034904142c04900104100342a611000241c42a1840c00e40b400820300340d400351041082c0503100344090300680d00d660010b00743d00c24051310300082c00703840314600c20000315a80c4550b82a02840040d0600341d10701180c803500c1b910b000d6864924a65441d88102c070140304500c1007000a140900c01031290300c0c410128007498030402480440c1030701075a01ca241c100d030f008a843e425401d03500c0b90712150340c65095a40f07078000c6c5404c0e80104510b402c42e120152806220440d1442e41048503200b0008010265000700c620380704000002183e10b082c2c0ca040807650b44000c5050303401858408108440740c00c20414002c0f0740001500078428062141c0c00d03c82c10360000341034030303050124415828000e520100700010050854030705c0f1040003805070404200320b51705c5410500d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 701792455 1250 701791205 701791241
    0x110a060503060d1707061d0c1c060504020d12031a0d24090215030a050a0902030304091e0f02120112150c030209030109050c131406010c0c0f060c0309120b0601110a020a03050f01 78
    0x30b4013034052605029842504408042f40e20740d1203100154980700501d00080000000003890307985107505622034055500c0b0070070500c524422800820114a40c100380080c1041407e55128002540b403006440040c40b0740302012400550130345c001451a025601c021a08042c04400c019404680d03014540d002481070504122170941070f00800c1e2284501e014440703520f6144c4c101c030240040112074118610100007c00c00c8405914144400a03500000d240020016246c00101342e041c0d0200307004941d1070340070051071940c10001c05400d002d0221400d03900140340d0b0922444009413020f004500c007061145010f840e40101c1d66040007200905100c50302c0c9010301e00300500360048005554160080401d090110500c0c01d54945032000015581094800c9244c0e59800109940c007d029001010311035114811040d850744031560108410b000090b0150b2550070126215500030401c01e50000c0c00300061352400095900400d0540856500c202d800707500c001d00000d001042071140c0300da1002d14503040c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 701793705 1250 701792455 701792479
    0x3170103050d0f05070b0c0a2a1103070807091a0607050a050d0e061605162c040b161e0513090501120b10030b04110a060503060d1707061d0c 62
    0x1041c03030030320007c0408070310342d10010307030200650b014856000c000c0b614000882413660046802d080a1112110201c8103001965580259854080354180980c3d4400c0010b005142c60491100040c100540f01214100700c1c0001080c0180ca50000500042d40940020034400344180741840c80c0c084000680010400620381f0310216682d01c908661400205030300e100203030109801d00328280100c0050541a03000b09010000d200c1064000640c0060a4411912004241500e0040c050441203074000e084100940002c3d82d680c050417807800c40c4224518240e00030aa1040d10031091a03134034001c0d20f02044003c25007450b03591010038058007803d0322690900c6035525108030b040c0901109403000700601c0c0c580b8000703642503490042d800c008542011003000642424102410781207007407050380c0d00401c0400b00c00b0500d180030b0000c03280110303005014044000c0d40c90b00d4208141c4800f074014044a00100199404146e142c000c2c1035020020b078261800441841c0d02c0310386003212070ba40072405072042e4009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 701794955 1250 701793705 701793713
    0x50301120609080d0501030506010612020a0f03180206180a0506040506030f070302070501050a1e051510090e07081f0503071202030c0406170f01050103020306070c03170103050d0f0507 81
    0x34059540e94414008551880c1c0c618146940c2d00440d2283c00c0300500d042c0000062000005a550480c0c03080e480d8141110107070048032042e84219412203002c1440c18030743c0710200e0711a5104001220b05007a42888881180d4005a020351010503120402160480b80c0181480e080304920018003003120090324140c50304010511a010041c0008116541180025125802a012104410b41c000020021481c0c00c0c41c2c030030010300c03500d0803042098440071085c12402001340b01d150f00800030500d00313080400f00c0d00200207030011910780850030045268000111004e04090041c01450540c565036464540505168a0a5a400300c0c4401050b80964108400d4a022031000b0582d070811326450404a8030f4000300f0b00c0d142500c00c51940040ca0620009071044500401001513207640040e00c0d01c3c403545011490a0704e030f080c00060741c590003c0003c075410078010b0040d1100140f181c1840341c80710074000c0c148980c2d03210990082e54103400084a030702c1d41e00d9110040103c07290003401c1050501c803032526 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 701796205 1250 701794955 701794979
    0x2070b030603061b0c0d030f1a0d080c0f0a0b1e07120c030b06162102070e0414160801060b1204060903030b210601080703031b06150b1306050301 64
    0x114503a04c032988030101c0750300c0070f12204842a42d64040200c0c0d459000c107034802401400d42c40c0c000030180345400c51b2000c00720b00d03c80e40d41910034002400030304000fa2548030305109074044071017204140304105404400000520002c28014040d8550742074a2600d83c00650611820500d801e20a2401c0e004000c201508407a070f0040d20303090404001050350f0114001e8004141c00d1a80a0744070601050340051000044400b10140c2d01c10800b500e808041c0c03032031240600385e0541036000035820001e014404008020394440c0c1c03160040340001103c000700082141822009000041c214136070383e2052000640901941000306200220710b460040050b002242908001c0c0c002051a034841d020002071500c2500035607501100104030f01a000b4218403204000c0d107003440a04801d014910001920740008140d10307003160740544445990b0f401d0304000308081140c03000202e031229525400c400c0007502c1504038402038039a449803c0e54407072589203201c0e01ea000c154000c80c1080310800040c40364040d442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 701797455 1250 701796205 701796211
    0x40e0f061e0112020309060702120a090515041d041205030103110918030a0207180c08130c080312061c1110020f011b080f10032003010905010b0102070b03060306 71
    0x1400700309014110300102c0b107000f00c08518580300d50000c810b01c040710002054160040d01c85408647c155100360301d6040031030007500c180314045a6544d03000c00c600d003010103041d140302440d1407401e0b10b800c0c1c0341c1c80c80401c01035644541d240501210003c000801580341caa252941c1603508041c5c1c01c4d076146680707a034660101c0d40f40080c0038456100100b4120b040e454403003070300303040c450090f20b466110f43d08001350380390700710710884010144403030400342c290742180f05481e504083c0b562130303600a031740e0288080d242c0481d18108403010802d1003000540349078280003400c81108036499406040c20f060041060360844001480c034038060704440f04000914012502007186070941d00b8048110060740c0c282c3c00c0c1841031800440340c1d400c05054018003080034200090010464850245a0b1118400b0409440c130460f403000a54010444c2030011030341990704145500294a100180d04880d030000c40d095403000c441c101d885039115040720034550380501c0184054804a0070641c218603107a80080d40d130384005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 701798561 1106 701797455 701797489
    0x412050a060630110f0d060c020129030607030e01060509040b040209070203130b1b0102160c140319110603010e01030507060318020f01020c1203040e0f06 68
    0x1500c0c6400d10580c12010202d0018110030501000010145c401a03001690502501c000707100307401141c00141643c0e0010a009031240300602e0210b200402c0888000c42c05d000d00c09040e00c00080c869407010b5035140200392648820090760041c00240c212035046002d0504100500119030309081c0542e00c01d540c1c419056540840480c0c40f8090940c0f00520f0481d40d042c10000c0101c03108c00f60102120442284080030354580c03000e422a44246450140030744048440c005011007080c3c480e00500242c001441141181d00009890741408858071300000a40c01d13a03030302403000c421080120444040c004a5072561540c005807240c030380034402100e01e03200f1540046400c034441d0142105070076111480140508c1b0a508005942e400c0c001607a0442c41443e20f01a083d90703a541503032594a1151014540d61418412668000f86d0010007081003500003c007807050585440700c00100700d0f9a0317 = true := by decide +kernel

theorem cover : BRFrame.Cov 701618705 701798561 := by
  have h0 := BRFrame.cov_init 701618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 701618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 701618705 ≤ n) (h2 : n < 701798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
