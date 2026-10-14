-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2415
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:10.821357+00:00
-- url     : https://prove2.me/submissions/c2dc0a85-1d58-4402-9ef3-6aaaf7b417b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 434172661 ≤ n < 434352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 434173911 1250 434172661 434172709
    0x180905041b06080a0c03020d230f06010804030c081e09100801150c05190309030212010504050a14150f1006090f1e180b361513020405 59
    0x81e0b03002c1d20034040201400c0c030103503a03810301d0001c8a010341c0454404040400c1c00300310b45c03080020b00c54120031080885551a41c01e600015080b04400041d590143c1c4e016115050665569034040703801c12103104084078111414803032078111884507940e0407601102911900d07140c511480078802c1a0101030058000c01003004010070581d040c03440740c0e07040030b03000385010503104981d401c1452903c100407004110000e0001d1941e000c0c50f5000d604c14003541d00c201c844841c140380c1840c4060030398070f0a1f00c019180d60020101d43d000100121100000048420181c81070300c220901e016620400c1261511030b00d21030310040011165011015602400e228100f51030f0180c2403402071000002e4030b000d02c903c081206038542484c0d100f0401010018003c545a02403180c005000c0380c0c0240102d00021401069040d024540b0002c070202016401c0840003a01c0300d940303003100006181c1d1840540306010b00c07010300c40c00c645142c650b480464000b41090f60051380c1e651500c02071012490351690f82010340d654803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 434175161 1250 434173911 434173919
    0x4050706031109010e060a02010603121d0619121b030e0c0103110703140d0c0507050f3415020d0206010b0a09030b0601030b030d030f050f04020303040302060307180905041b 76
    0x3060400d003146170103071015600d6000000b0168014029a04090115060360f101c03e4035030b60b80000a50b4410110a4510350001c07080000d020050280d00403500c840c0d104400441d41181c802c4540000c603540c20342c0c01089103602e0500f503078040800811441e000075203d07401046050401c1003110b200d08030030300c0c040015100460300c031036490040e4000101009a009140920107031300314251241d0281c445010003617011100d60150156205017000c0f2041d028020421245031404212403204040e6091400705480644201500348507080b0046402d4855000c3d011401001c0000e00402e000680d40050820300910031010740391503816030151035800003c0008045455010006204482c1d214415048980340c400c01038024000c5400c840e03802d48200d1072450398076980f50300402e480800d080c500700b080761a00e058031303214a002158040d4065000300400c2005041c02c000465000c803061810b220f07800250300da04140180a984050323540ca854000340010b20080340000f90280300c4960800b0005468 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 434176411 1250 434175161 434175167
    0x12010e010305061303020304030c1202030610240315060e030f030f0f03060409020310150b03010b040b1c0207120311120703051003020909101b080a02070206040e0405070603110901 79
    0x244004c0030b00400e001c402d07017054003c0090301c0140d0350000440b01855100d4401c04000c5000b4402070303110784100d101082072071402c10581c1c02501d0a010304000007075400d0003003400c0310343c0c0401078104042d03075440341400c07101c1882007a078003501c03007640e0341d001e01d507000c070109840e22090801c048426041001220040c540701c80461fa000040d4200c242d4036a910080050300800300500c01079054010030140082c0102198031180c10b40c9a00c10400414544030308080741140424014109103000400c424030668101c200584854003007203c480035000d1811120205a800c114411070b014100d9580745c1034003503014021040300400d03244586042070320f907480310340b00003902614403010b056860000c00e40403444240c1c0c0300c001d590054441540342c00c0005285030744050240c0035811540c034040304d480c0e044011420003c00034a05580b02c06498503910940e00080d0711145080380c0c840410880000c207024642e517801d01c21400303a805480c0442c41c02c5800303019a50024101c401c185400c1080703a1441c0c2e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 434177661 1250 434176411 434176423
    0x7060503130b190e0109020910030308040204241403060a02090d0f03050c010903020318010807020d050a02031303030201020c0d0302130e19060f031202071802220b12010e010305 78
    0xb03003040b1424141d480d00c5141c0a40041c212510104150034240942d80c50031054220b00016442610030880c65540e00c00c0b0206100a24000100040d40c05008200545000c2d0003042c0c55900500000080c1d6100108503080c1c5e65595000d0210b004451080b4a154601030086540c400300c014000d624081d07004002440940d0000300090240b010002d002c000e040c800c100341e83d00c40751440b00810070032400b401c0207552500700c4405003074038589101e807148040d40303d1003849004645680041c900701d041c0940581c9c168120204000440c4420b10918224400d6540030f500210300030740006965801300980b46041c0640c4481c0c0d10180f500400003400c500c00740f00003c1048441c81a00d0721055116031b141003103940c3e143e03440410745a040c1800841c00c006401c140c0022a4402e034011910312030079103c1a616541140f00c3d008950042d0b40c0d00d03e58000440d001400340c601050050300c4400402d0442c110404643d401005142c0000b2955100c1c0c94911132002d405003605105400c810740c035503915540e0b608 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 434178911 1250 434177661 434177663
    0x9090601030f090203010216020901050301381503011e21021503040c210803060f18010306020c010609060b0403110a080708010c03050a0902091b040801050c0c0706050313 75
    0x1542e998201030040e6030950280380141e40c020002d6695410486907003890340a50314040c1e1065a0600001407185014811311824621031002a502e11020850006d159032520682003e04e40d0b10080c124442c1c0e550111280e03150b1401904103441c0e50500540c41e1100e5101804071003140a920f4040c041000107582c00c0314142000c820031040d441c298800b1881c800915100de800f217110120902013007110440414043d200e0401e40a60b85c501c02e0700031030120800d200b101510310724041010a030745040480203400142400f51060034180040d00104543e0b0700c00f41e006841c07040e030100760b5010f442e50a0245030300900c2e0b004001c0c0179182c1040200c621910840c48014000400035a2148883d224201e85070000c12410007941d01c05036a541006002c6e100300882070700040c2c0382900251440501c3e1003041c400d10317000390043e030482e69860315002c001180c0540f030100e12101030000240f046401d0003114403c1e1100164161514841c0429510308003072600710000f844003c0c8200000303007007410000c400359 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 434180161 1250 434178911 434178917
    0x30308040b0a0c1205070215131109010f03060b0a08030a030501090b01050405090a0c03090828030e031204020f03030c010b0a0f1a030402010c0c0e04020f0303090102070b1309060807060206070509090601 89
    0x5454206c0140d1604a07000c0d100d009020202003080019203400c1140038030280100c4954120003500420410b12100900980400095000041c004500d843e030010041010190041c05400d40303031a20b542c50360700031034410000640c80340014803503e0001d003c0c10100a80070700b00380781000d00b000d001030f07421103000701b802c80c82c83e0b43d60113514240c91081d0002c007091604442d0072545c80301c00706110014012044482201c44101e07544449040c3e04c684a5101c00020301c0000d5030404030040000c507015200504141e0307104080c0f402e01004d0355814801031554101d5000001317050104402801180c0c2d0aa41c01001000010ba80c100810b0036014040700c0c10010400d0a81e1760fa5866100607600b0004160000e44403c030400e201081c0f41048100890040e03001700d908079882d0b2024010190b82e07104044a407801604160b0007045a803803040c014105e0084035a801200c1f6a0b11914020308540781907010849a5010b4842000080d8050000c5a000325075860800e01e400c40941c049844614003904181c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 434181411 1250 434180161 434180171
    0xf070b090f030a051b0c060f04300201030e0c040f0603020906030303071b030c1a0a05090106030210050d0608121909080d140706050c0d0f060e0c0708040f030308040b0a0c12 76
    0x80000c240321200c11604007d28280d11110b01468001782034000c1c0c001c0801e07180300040d2480c1d114603108140140d00d01b81c40c0c0910602c0035250f00450203050701d81d002622500c0343e902c03601d8103941c8500404403d54000d50340000d416103103004000015101521103800394008005000e42141c0c081e0356014400d842004a44611080c0e2800711146040780001074042032500c21600d011640f00070400d0302503444203000b80155124800e10a00321341e414070000b540b040080d403150402501650140ca03810500001c000fa070595503000090904044040300c0c1203c0e000007800201c01c80c40c186c4015003040e050b01c0c0c40c401240c1072603a425680c0600e10004400d01020100546e1401091800c41c1c1c0d0a55010b00c0621007414003242c42d40094003c050440e003100d0819540c3c01c003958081c400c1908035080e110f405849038903041c40f900e4480e408408103440310b003030030040400c0050f002d140310401180b0030740c0c84ca00c0d585400d081c0130381c4c0424082d12042650b4100304d0f00008061307011040350100070360700d034000038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 434182661 1250 434181411 434181457
    0xe04080f1b0102070305030114121f0f1a040c0c0b010603020d020d18030206070507031d04200919050f04241202240a0e01050f070b090f030a05 63
    0x1010aa0500007460729800028154101a170250165040360b86d00c010201451843c501005541c081c130540004081d404000e084129008142d0b86846c0348001c0c060000f51000443c201400343e40c14551001d5041480c00d80c01119814980704081c3d52180c14a0191304501290365003140621061050500b0581c010030f607441030280c10360442c2c2034490500010000306a041d01e400500c028030071401c0d005030190400054283c0d004034115480c83c1d078150344d03900ba144100718401910145500d00c0036041507907100c9603100c5003c1d1100c01c00e410380c000c20500d51600b03008010010f06103c88011600727229500402044903407a00c411038890302100b1100414003045044614400c0c10b02c5403400d41010742d6900001440e50b00e48034807030b150b00740244c1d90200c1c04010109a890340006080d4120901c01c420051a00101c1c46203807102c5490505240031458281407002c020015040032800341c440c1c1c4038400902206050030081c3c0c800741c820001c00345080140d0144061302c180540328a000d81e82d05585a100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 434183911 1250 434182661 434182687
    0x2060402031207023007150c1b031704170c0a180906050a061802040312080a02120f01080115050604050607020a0801020c0309101b0f110301091101090e04080f 70
    0x100d4036070384040c0042d122503401c0c2160040b0218001685d040c502a03c54040358070200300a0350219120603841d1051910380c03680d01c818840030b40c401821121044840c01000003804c04061202601c00100786a84640c20070016480c2500c51010001c0d065200131000d03000c0c0e840d000146030440d1402080007440c02c010045810252041e0b000051500746000b00b0000200485e903c81c00503a0b900d480000c07a440d03110000d041c100d104501014040715503220384182e0141c4a0400d185e401506041c0150810601c400080d9207002c064031602d408141280051015600900c100c0b18982003c40c001d102c0b4074540300c0400c1c8588502d008160240320009105410b43d1111042e00004050007070003159980001c3c018103480f904181403252140115040d81c04205210f0310300c804005580102203c0004525640d1108100820344101c07410301366180ca1702000c2d42c0038441c050f50b81d806102c102d00032140d44000141640c03400e40104040b10404401e20010a40e950203450aa1940b0100150f031a84003485403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 434185161 1250 434183911 434183929
    0xb0f100317090d151404050c04021e031e13120509060408060123120d030504021810030605160905130608120c010c03060305150612070608090d0206040203120702 71
    0x3164000052508201c20481984c41100844814140812541145210140c3d91060035140074105034850070f4190f40d2440c0a40c01007000d000c054106040746501010750b0f480765001110103807054440a54403181c200b800304081c070b52040c8209950300e0000c0041c3e59016030351240445501c01c1010101d05441d003500c88070201c402a10401c400c41c1c0c1d4a42e51140320800005502d860f52000c0b0710b4902d98400c0720300346002c084440d080104c025180c207201942048009000c001d01c180d82c805031007031800344032040c2c0b211343d180180342c20344a040c00f190035414950300307441000e031032100c8451103002c481407160f40c0060300d90309844044420b8042e640c000c0c0000400b030f02081e040500c0c24045c1c107030710b00044890744004000d0300503140001c0c08040d5600b4015405c50b12244805021500419142e440322140c0090013130380540b0050602c461814081d80c5186842815080040841c842905204607a001048260400da0345440108440d180039070100c2d498030208010100441d5010880c00f0842d500e80c03441d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 434186411 1250 434185161 434185177
    0x4050601051503371e0209010212070f020409121103180d020409050601080307030e0f06090f0310050702030c06090106030206120703140705071e0206090d06020405030303130b0f100317 81
    0x1000d030340d001c06030400d01300615000841107a03080350103074115070305007150080d1008038205030081c12103070210048140b0381e948000401c40d10071480014680040e50b4030300c20245418050510404c081c5001c0070083c03c501a0103100d41140c1c2c0c4140070035000b184589840d0546203500307445415122426102050103000c3c0d54500405134001c030000400c080310000058a5401c1c0207a407400000f00000e030902040c12100200b40760060020800e0800702d040c440001c55901001408540c403a156441860045400a9980b035005820005040701e211104100a9400116880c000c100b0989160f0001c0c84903c45c2e02445282d11003d1000146894004e5100c0140e1002d102040d40c190303d401e0314010107691100c03d0440c0d00003051001107c0d420401542e004c10b45a019050f1860422980c08000d0038000c65a412103059408100118142d00c007407001e94000c0400103e400c00c1d2260a141c070718901c181c0200100c418000c03074010024800741c808400380840781c0201036108013142000000c0054400d5034070b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 434187661 1250 434186411 434186491
    0x60e0d050d0e1f05030703051e0403050310050402090901091107120e010f020c030c060c0106030206040f051017042303030f180102090114090109180504050601051503 73
    0x81ca4480c10b070805041c0303481c0300044400c86809510f41c14011a155000d880325400500d09000113030360140240c2c00240c01c459001702204c074000703030041031304c03c2440120380c2100060340110074401e0b200e010440341005010211829801c12a00d8408150400390520480f6042da071941b68441484107000300301c600c03c40d0051490000e181c525000605440c80d4520694000354402e030303402c488107201080720300d68110020060003400d070b00c4804015081d004034906488a540e200c5002005a40341c0f0300601c002c0c280c0031305480065207003504101d0081d140400a4042c0071501080401a0206024103a8410b40c490f851b010b944004098140003180305251b070000610001080c42031701007011038000d1041c4025220050551004400725003070340901d18240340030403407044040101c188401e0180c850b0070410300d40861025511400042800b40e078411602e140d82e681c80c14001408401e001e0a409003206a98925082100c6400e2a00703600c001080d0050803000303802c3c1d061801c1c00c49002d541ca240711101c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 434188911 1250 434187661 434187673
    0x90305100212180a030c0501060b04090e0c03010c0c03051602060d0504020a09060f0b07110a23031603080306010e1002011a0a05101d130608190507060e0d05 69
    0x31400002d52004010300045076484000038100341d0070b420005040b00040010b000d44808a690030340b0362501001c0101d4065407960b4000c05c185511401800091405684c08952044000071550801540d1100c09010b43d051002d40802150405a0815200e0381413408981c2c64002c2c6105111001c0000030081d407065001494a00c0d6030119002076004a00840304682d906070365070321b102c00b2182c1910554060040040042000608a00c0038041c070074050003285110b25111800681829241d03003101444030030300402440d0300c1c000b400144108140030344c0102140b8083d03918112402032148002031154200000154a0f07901c03c25000002d490098034440d032074a400c04000c0c0c00390101e0440000e18882c2c401c2c4100c014034220040c04100c0750301400083c00c61012032012500414900c1702c3e0310f00401c80301d030940810307242e00e29601c48000d80b000d000140d45042c4100e284c14941d40303c42c850b0b510940428141c3c00f00381c01181c100c04030f0703180d4104024490384000206480b20104040549140996 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 434190161 1250 434188911 434188933
    0x801090525090912080a0c021c11071203020d030605030628052a03040b0c07030c0506100f090504020a05040b0f090910241a0705030d0b19180903090305 67
    0x150110134036101d01d85480e05580c4d40c0441280849594401900c0180c0c48050800d00c09122140c01001c41c04291912104114550760007515002c0c0399440708a440283c43c44280c240350f03040c030004441003028502440980d01c0c0c000081d07a14440681100d400030b1040e0600070781c0c01100d03250700105400d180380a00c0b0524203c2c84120315607025581c40444819010802a070558400e41228456688803502c601c15842d01202c022907600300003001c07024000c400d54540040343c41085101d100d56064080410446e04000303441d07071140e80591220a1007800d040c01e02005a070f8084000066071001d48001981c1e6090343c1c0020386a081000c103450300700d07100c00e0501010f001d02003064440002c46000601901c800421a0980c10324040600702c41c5038640c100c14415808401c180c1361401e2803c9828905003c01703502d4190459210043e6514500d95811000542d820805a007000300018010340c039414a207420500c0000010b0103000c828550740d40e100c1442098058107000d00616005001c841a030000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 434191411 1250 434190161 434190173
    0x1020c103c0c0210030e03040e060303120f1905010e0a0e12070501060509010b07020901150909020d05151207060e030a12050301080c0603040816030311210108010905250909 76
    0x1115000340e008020b842c00421382c0c0b5000e409040d041404c5140114903107458040d515042c0d80300603204580c14003003000700c1d0568114048840e80624008a007084103420181c580500141990014281983c144801001400c0210916135400503140d1070100f00c40da44410504c1c28074103503e1854040b02c034086440000c0c0f240c1540305806886041d11201c0c42c0f640c0311207400c020f500401302d00a41c041401c400521044c0102d07414008541114204a0540d9480700726150a070780015581080290366036040105001c013601c2400c007000d0701915160b681d07020455002e030702c0b500c030b90144009200d50164681c60540381004022003e5400880102d541d460b110300050a5074400e2107041c003107110f02241110285400000c4900541c1e1010805203400805c081e15170740d1080e84941541859581c00e400c00c0c1e0200003100518004004d02d00740e020380040d0403510b008001c01a041201242c2c9406c0c5030200007203000030942c1021110000710844452040040c0c030f0000e14a0f00700c55029804d04a4000400107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 434192661 1250 434191411 434191427
    0x180503010c0c061a060a140702091e0f1b0c0a0804060309150c05070204050613060f08011103090307020d0804080307051506030309010f0806130501120201020c103c 72
    0x1200700700034401001380b84441103003c1c403142049940004200911207190b0300a03602c40c961901da280d409800c0c250141c00040701c1000444c1c18641444460740318026030600280000e0303000700000318a8440741060070340c104c500d51440d5001c01e0808000200b20b0040401000140c2195a0020100703645645a060007405031804440494011035045d0701c2c600640c00d41e02035228040c0303441c0d440c142031400036002c000203000d019028036005035107403100d40a01030a500403000036110154042d40901d1810318000e00710b0f070320b0480211700da540a00a104002c0008021105401d404403000c00a1241d2410100700510480d4405441440b000403044204280403491440c6002003032423440043da81d1100785510303840341022450019050008a403500c0380140e15090f0804d00c0508250f07402c81042da04401114020703013281d649400c00c171104900f1580e0400a908290001b994081c10301e01c1d02150251403070f124100c083c03842c001c9030130441002100052a8184141d4500c1ba00c000d94070b000000608410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 434193911 1250 434192661 434192663
    0x30507090225030f051803060403020f060604090c03060b0414070305010302030d050702061e090d050a110f0d120212161b1404090501020705030c07090614060a180503010c0c 76
    0x1450900e0300310030b80d40300c500031100082d0542c5504110650443c4200e94951007038424105540e02c1610002e8603441c208034491140f403280d0020200101e400c4542440c0074070081c0303940e03c100d05001840c8001101e810b00382007104c0d8000c0000c25010003800016000d02091a400c030706186103070f010895020b5040e0440c81c102c038029415941a401150300032210303071142c410080c1d006030b410807007041d0105e0241d1340030407250320490b01740b03003400d9400000440180030030600390707050b0f1721000c040014002e02400c400c0481c14125898010b6040010102d000151100e4014182c1c0c3d024041c0d81d0101c41c000c1c403401e00b03652416000160341c0c40440031092381e152400c00c41914405c49401e14080c041d40140c0c2c500040c1d48100801300442d145440c20000509000e0a0840d00c0f0354091010100107803040000d0801024a540903000c16420495088103c55960744941074801c0580090f0f512a100c0d40c04581c00001d0520700303c69a0b81107004e140c03904100c183c0c0019095031074424403000c110317131002c01e001d003176 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 434195161 1250 434193911 434193937
    0xa2414010f1401210b030708030a090807081e16030b1602010c270308030702030a081608070f170a02190c05060105010e010908060109020d0c080714090a0305070902 72
    0x419100c042056000c4030402c0d8050100303503400712000709542c412201801000c056603000c250903014101080c1400d6441e4424680b5034000300c2c941800582000e8800302038003405008001191800030742e02d6688810942940b8107044c0720040b00001601440005039440c0f1610044d548181d981c074284014000448201b1203408448448804051041c020310600300c10076940c1c104039030403881c43d00c3c03400c240d49081c80401c040e028000000207080c0c8405503215031105d40140d40c48480001020301041c1e00140110454031881c8040302806812500d11900003c403858104003e090f54441511031951280c41403060191030820050f42210726001040c0415403116105000080444141d81680f2078001c014590781141700103020701c2d4405c10101900c12014501a01c03555941c1180c9414100d00fa00320b012500c2d00042c003840e150446000e84100c02c840e43c6084403c2c0e18107104010100d01500c056117034104000180c5080340d9032980d49801c00346403c6001c4d03480813659401900002d6001d400c1e5803082c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 434196411 1250 434195161 434195189
    0xa1b08090d031e0203120604050f0f07020f1006030203070b03040f080d02090d0c0618080304140303190c05150c031501110312041407060f0c0203011b0e031501080a241401 75
    0xe981041c9c09040e000f01308008046c4403a4813038031441c8a80d61001007840c030851040540c140040c507001c00030005048840400001d00ca801c60050506000d0345411054400204005010020b03554490190080c0d8004110b907480382003a0055038003074810500290361103420000000b043c0207440c0c103660700b00c078031946130a80414a055038221003101188141100350700107020800c10010060f8500c0b212000080559103072007240c05903c654100c001840d44d0004c0c100c01d00e00c0c3c041213001c01c08072414107801c9045403450726040f042c107074041c0701c010100900740945054003000359000b10703e00c00743c0e804524242c07a00c0c1c2441c01e814400b607a000b20ba040d20380c20800c900e150a00880860708105842c0707555250b101110281c901580d0400841c1c0040360190b5030349041b40c5a90a98070003036544409180e0722100e2011420f400c051614612855140e040c0003a40010006d011000600c00d901c1c41d4000c450501d03507950411100444001d4400942c1d856090082c01c0c0396030403480e1007940c10b840600b040c01314 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 434197661 1250 434196411 434196421
    0x80310090c1205040c120c0608130209060f0a0e0a140c04080721060203040c03020f010f021c0c082a0303040b06010305090a0c0b0a1b08090d031e020312 67
    0x205640407007044002007080301c01c0b504541140d039002194000e01484085110656811001e0341010030f24005a87d042100b8809112440e4401882c5401a001d00540c1ca03404141c1d07000141c1002c00500501c0c41019030381c60101da0b54032030368801c078000c25201c82c100c4014a401224100507040310701c603d00a042407c000a5440303440c0c40705540c1500d020400a15016040606000181d00c010f00348808241005280000145043c001503128510401c2d10001c468618410f01000d51080110b07a418450000c00d141d0300c5a030b00107482242c5001c038010036540f110780d1400681c1c00c0c12900300d0141c014680000c82113002d00e81084c60000c0c00104003224190015004104c507100d01003a02c0c01042d0f1060305011400715172103030300016004043c48060f90400c051598a12450810325441011100b0000c00d4030440244c00880d9010900d5035008082c001c012983d0364507500f48541c810007880390b00350395084018944a60b5071011100c2c0310003007000ca04022204007958941104000c00b01e02ca428400040f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 434198911 1250 434197661 434197679
    0x50a06050303120406050c0f04060c021527010e0301020d0e060105090f0105060a110607030b1c0f020d0618030504082a01110f07090204142403040609020904080310 72
    0x1801105203c0c0b120f40e815201c5646500103054086d200820702c600500000d161304804000900040c8825190184008141c1c410b106841190041e00c000c1d45100740005400c29145108200c25440303200694007824150b080180d49884155841030b030550710208282210780c0c0261f004e818062126000c44407540c0c0d0b42c0c3e0030004200030850f28000484001d00c0100844e08060000e80340090391414004c443c0d03e1401c030054540b4504944140000307446002c1030000d400c5c0369401d4200c41072008000b241c7e410650302e03985858045c0c1d101c0240140010000c08043c42240d500400d18042100202c282d4034944e800e00170b01c0354105018026042c0104840302c2c0888010766244041c0180d981c1042440391034200064a0344c05400100c40d22070b004400801003078000034030005000d8800c2000058940e1304007201c032070600418140c0d65005a403000e00c00a621002204000380f001e52141301255290744030725101c40505a07003e0000d40042204091108000d12a00554450020200072a0901c3d42e12036201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 434200161 1250 434198911 434198917
    0x221a090606010914010507061b0e030102090a1e0e07050c12030103170702150f0706061403151b2b05060f06071e030f110105010b0d1d0d03050a06050303 67
    0x1d404901a400f0800c80500004c65002ea031000504119080030103545400041d180320f60302d00d10b000b0341c010182c5540d1079004045205002c900754000c509180356900031454030f0095004407049501040c0150700c80702240441e10340640400d00d4110020b0400e400301800d280c0020124901900461041c10b03c0355500c1001c0d64101c0340c00c4800b00c0d440784c00207140d0500503030128038140d03003010103042c0c3c055030345041e60018040c0508003114156a0600c50410004555580d0001d80c9891840c01c00d0400c076903000204421104900b80c544e5840d40c072012400742d15036210b20035a260209000c40e0340029180c5c230300403000010b49400b2581c110080003540b501b01319141240d0207540000314900d007003583e0a0160103011224442c8002c0d041000020702020b01107850303a81c1c21000104551074100031250301c5092142414001e00080c0440d504000303521125008541120030003503502c035080760001c3c0c40304015140804401d016641000b6034210000c01502c1d04a450000307103410b041c00080c981c2800000c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 434201411 1250 434200161 434200171
    0x51905061302030604090c140310091a0601110a0503090405092409010902090112052401051e220b030a030e091528060807020c0108221a0906 62
    0x4581c911492499044009420240550b6000759591441c2400a140c20f61103801400c40481c0042030036070a0720415181c16882062090041d00f0899480d0009140f10341100008000c01d40d030070300796511900101c0c1c8000b487c0da20b081c1c082c46000200400e0003030101c010f100c40802034500b030080c1d0f40c4030080c1e00c2d650348040384982021400c0c0351142060a410140c2036400c400c00000100d40e06003140c00055003d007080c5c10503440c101e1915200c070308005c41081140c0d050000558070000d10810700a0940c20441d052046601031443e145040c59408007159541d1012000148031048142101c1c6054500c1d1607100c0c6c44841d00c0d460103507e1800f51500164901d0610741c996261014404a44140954020083c007019104103090802441a54079001201d40c411009401031a1110340c14581002e80c4219501010502c41c0320028092459408a0700e031010701400e0a2540340f540341c82c030a01071040355000c038020f184c881c1940c01e80300f08010780d40c51180c007424030442d42086442c2c40c00074686486080d070f4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 434202661 1250 434201411 434201419
    0x20904030e0901062a0206160b150a0e0103080f1b0c03010e0118030c0206040305030406050a0f08010605030a05090f072715051207050d060b010206090d140d1107030305190506 77
    0x101d00020105900704540c00d2028046500f4282c01b100d240003201e640d203502725817183c08442004038000760b015070b200c030204080355001801442e251014404003018007010744070850018401e00882c071018112038004003404c0c0c0c80140b1081803904c00b500d413119520107034842d5080c0711565140540501410005d0244001e03a0b051080071aa029140c5c010701c15003ca801120601c40000484c90a00140000340600c0e10b40170340e2146144001055145401020000c2c40304840040c000c01e548a400c0d40d501c94a25440081c0c1038507115482842c0c1210403c00340400d00c140200442d142007116102c64a200848803101f201c0080c07c41d81c0d1065998181180e1a02031075040d00304100d01c1c0c01d6031034030900d030503103400c0e00d5202c0d4031003000c40c404000c44101940d009413078003140b2886580c10080a40c1c003d4044001d03044090091000921410389252010b44c18440444c0c0b621a03120968004041e5407440070340903984240a103001f40c042e180c200d07000d075031000b0b558082004580e600c1c00741c10b101e414020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 434203911 1250 434202661 434202707
    0x1022208100e0c04090c03020910240503010303030209010507050708070f08010209090a1d0a0305070b06010e22060f080d02010e030a020a0f0602070f24091505070507020904030e090106 81
    0x40c0c10302005204e01700c4c0a4650500d01c00b00040943c9a10407954003c070a201c8018a616082441341001280c0c1300c0034400c07524007000440c100341a03000e001d0300e06483d030503d07025030b480c4241070048940b80980c040181090045000018030602d0024102c0c04030390301c00c2c0c507a000940c5c0d6450030500700e0080070300e00c039003011010001503004078a40d40b29404038056000f000b41c2d050364280c80307140740c4070384102c0c1200800c00018611040c4010511000d40c480c1003485c203044503488440105000a05464440d2442c3e81502920200241036030000c90150101003440c050082d59aa511075a45040c40401d038050351800c01c100c0101140031044519003041c0381c0051010750342a585008132402440800d44855909018510005940d801c2e42ca60841c007540f008804540041035403e18404186201c1040070300d00404038001884030802030400c600450f0380000c26a4500304261018402c600001354000000e400b00002c05410102850200c04166400d040ca80c4e00c1c0c420990361100000301c9048112401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 434205161 1250 434203911 434203933
    0x405191a161e0507080601140d031b111005030f13080406050a02070b03090c0112180209040c26061003030c11130e010b1302040f051201022208100e 65
    0x2012040302c0c0751104601164040302903845003030805900e50812501c0d504140c004004d01c84065014002c140021102040306900e03694022389002220101149100e0080c0e450b00e0500c10304910007500c80f000604903004288000100a00c10781c403c40700f403c0f00604d10404605a8000000319002d00d070750103070a6910301410300750261510b40104100d401140300f05000482e081c0859800345010759840030003032a140c1e140b8030001d010358800364044140d50f4500310800850000040b42440100d070103981128030707600c450401c50a03041c0303950800000b001e1a0751000d4a070b00814041c001e048282c030000e0b501203031103042404096000c0d5200280c002044100301b600807807050f00d0480e4081d90300074440b02e210350792400c05400361014103880080300d9655a001101d5410001640c240e40b03410b80c0b208610b05030415000b21903849180c085d0074044c02c102e103042800c092003581200c601d0b4009040d10007006033b6012400306a42e003d03004462945c081c03035803501054038060258080d00c0c040200a49003040d02 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 434206411 1250 434205161 434205173
    0x806040201050a05070606090c0504050103050a0b01051e0c01021204021c02030615180f190221192a020d0806010305092401140a030b040f06020405191a16 68
    0x1024091b10495907031080000c50040a11600d405d003900ea484040e1540c0c5007600250807100001d1942c0c1c1c01c0340c00c00b0000c2c03a20f47e900138200d4450000d01ca018100c502c0341c080700358145001c1c8201c0d0104c0c81d8800603440038001c5507011254404c038802c440152142e0307880c843e51201101c03c0c800094056204002054408114050800010b42e020f0400303000050004c100724480312060381c000c0c00222401c4d09101110b506903a81075200d50701c484043d0315226506103030712aa0305681e5944040d211001002c60340e0b4154400c01d005d5240e00302c50b424810502c840096000b4900345014188902003180c29108500b030012640800c951407580380d20704199039402c0150701805006191a10320b00a0004200040c68034200b4681d40000440d25800c856050076600c40c006c00502800501c1080e540f01d0400000d04800c240d1a4032980c04803074134a2000d0030b894090003a004540206c0c0e03000815074620056000c0140c1c04904560030680f0091042907144d1554000340b141c3c00701100300c0d5482040071408221 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 434207661 1250 434206411 434206417
    0x5030604020f09031507021605060d0203090111190305060114220914220c03060b010309170d05010e011202060f093d0801090507110f0106050108010806040201050a05 73
    0x40710b030700c0c0741007050b6001074202801010748400d400c6001041c821440c1d41007018109803042100f01a40150404000443d18002d000040808540020000310741c4042904190b40c01c0c038054241c2038448940d21400803600012b00c00160001e843c11000038841d42c4038000004908400004c60f915150f92102c0c0c2d0900c620b0301c14100300b001c0c0001c240004805003a0b1103a40000500c1072496441c5050100c0e4407052015260b80d455905070842590501040d215044002141c1d880040001e0038076000700142c0191000003000b606030100d9010809503441400d00411100f42c05437070400c45aa05c076500c900c0351042c00c1c002c0b076507001662284180141402c10007001490b5404264178100340700540001d5071503401041920300c0c081c050903030890f500f4040480d1140f4000c0482e035031031a00c1000c1c4d0000c0540f2014864501003507110004654502d0183c8421200c102000d0107541940d103c681e40140602018402d45000812442c00003c00702c0c030100e1080d0090703034140e440d01d1803c0502c40c0c003110a50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 434208911 1250 434207661 434207677
    0x10060c0c03080315040b040b090612070b040b0301030b0703050412030c0504030b01080312070c030804020d1104050c0c120c0a030f211b02010507140a0c05010e0102040f080304060503060402 83
    0x8403400c0310100c040751145000d58821505a0f0385079900320a041c041c4070a403040c2c151214091070070918004050b0341c8020074240c1c4900c044e2091500c88112802c2c0703d20340100d41d405410350220010300070900e0314202b0020b505880c00360242d0851a264841c040b01103070030841d4050f007164514070707044100921170b81205075582614a001d6040640f01d84500e00c541c802a48500d10036440041c81d081b4000c0388400d90342d4000c0440c103182c0342c07582c000e032406071000c0d400903c024404c0c0e0b0410b18140c1044615421111540d00280c0208040d1518002803451540004801c00c0c6a10484100c158414241d40032580c000b1602005405007070110764080d074221000c6038541c0140040003541b8a00c00e92071030301980112032448000328521038504054003440000101e40e008690410702000f01e4a50460b051310a100c0d00b05e44041c0d03a0340c08032181100d443d600d500005255500b850480138000f58150064001d0701e42c2e05003170040d005d5440f250139541e4030540c8200c1c00855410b1001a21501d01540907280340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 434210161 1250 434208911 434208923
    0x510081611030c07030203010e030a21060e0f0906130218070207080d0f09060e0d02010c05100603030305040c09021207080901020d0204030807060e010c0527180115020610060c 77
    0x180710340200c00c07411504070410082c0303242c3c00310f00c00300f065140034004c0c10703e64403c44015501c0e00110120041c4410001d5481110b08101015104001092a03000742d0041140c000845003074100220110541241074640407207a00c102004601880302c60300540d800030758020000d022040040407041e580c428014220420750080f0540043c101d401031000444c284400d40d075007050b685041101405007038203a00a18100903888610100c0c44c2c0305c59031510078540c0c0908043c2d8070b94640b441c2141c42c01030301c1072000c15118100710340001010b030590400d0f80198401c0d044e50316040d4030b03806504203e01864180ca0107074203004021455450180000f180c1081c070f050300140c03420182d80005c50685e44240d03c00c81d0324410005089060180e64491061041d10110090100c0030007d00020b046c0c1c041d00301d800d4001c0030904900041b064003c10902d11034040600030101340c0352032240d44004850244180d4000ca1264001c041e0300314030200b1002d200b52150103040e036145091400449410740d0240044800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 434211411 1250 434210161 434210177
    0x7020307200d08070302010f09080405060c071a0d2304170906040e06090a0c090510030b0405010b0a020d03050f160c151505093c070c0c05100816 64
    0x1107621002c00750060030f800703061000d58602031460024212002244a8061030345040601000102080c0407a411104200e64854903030717815010f03042c01e161855000c1e0703440e50440481842d00d440400301400c050080b001d410001c10510500400c0305c401e841c000d140820369040c0000d0002a4501540c1c0a140c080800450408001c3c1002c60709940c09600900301800e004004c100e01d40c5000031810380e02c20303800307841806101a5424058803085050060030701c60562a44280b560074841d40c014842000020014005540d41d0825405147d020702c1c030000060240c3c00030401343c00d0190003005d0042031501d44e0526185e5a58070801c0b1410068641102002180d03a03c24000c2643e031090100b01101c0c10b80c0014998040c000f10450020056204c280101075180c01c110a02c0c815881007691001010340c0020b41440300014000080c2e1111124003205800400b881401680034921003c101e102c0d00c040001243c0316401c000d110040324245200107070038400002c20388862070081011428040c205604 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 434212661 1250 434211411 434211473
    0x90203010f0b030415360201021b03010207170c01062301350f0117070e060f060307021506120309130b120610060f08150d02040501060e0f010807020307 67
    0x801d40d802d004203c0400200005d0104034082020105000e400c044052506140941d40c0080d485032110340c0048003801c2c1c1d4090380b807a2b64500390100c403001503124505c400c0094108a5201403a045071400c000c0035840c0400100324000344081103190064022001044c10308190700450785200c0d0821074850781c1011004a42007030404040c1151010264050041d4500d8030740c01507035466405910220072400002845001c0e030601040220540d240d08103503c0e103503981c4101251aa151848803e0340049002081000c21503001c18190700c0c6408110000e01d180e101d09080000310394071940220401d400c104040040c51801d00004181410216004110082070348001038220690152a18080d0070070410401c11038000102c542c043c01c81410030340110911800c1c01000100e0082804000c00a41030f03d00c0001e07502c0c50311071358107140c0c010320501856071184001043c0e03140340b4035480d020320008415043c0d103600800080d03110b25250390085041174296202e02c15580a484908003012040e041210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 434213911 1250 434212661 434212703
    0x6180f060c0102070b07210b033f190e04060306061202150a09060809010f020f0901030e06061003111209010b1309030503010e07020102091e0406090203010f0b0304 72
    0x85a07058001000580710007041c10304e1101800c0052001040007410010342107404400c0705001512500c024000400d80070000100c0d1a01c1c410f0000d0485000406c48074201603880f252010703100150100ca00c0307000e081c020081108a000c2d1104980101891000f0b0aa00c0c41c8a641c0740065028001d102042c059901d443d000110b0f011604200c4d2104461644101541850303440000e85620b181500c07490000142002086402d286c000d641c00c118642d004501e8201003500807104c90903200b0350440d81c5040c011804100c0b40e01100e0302c5d07400300c0d040c90320740d02c80c5200c0414860301c552030181516040d00c0036005c00f1001401e0603030342e4070800700042c801c0c02035910040a0b06481000d20301d0000407080004c00402a800040c0301803040202d0820386410002a40842030b603044540340405007a07240c480c0c071400e0740a4011319241da50012014802140d040484600c001000e100580b01000201e8907401014140d00c001d0003407030300380500e4240070403650083c0401140c0c054000c0d82038903014454035400ea = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 434215161 1250 434213911 434213917
    0x1b09060f39050d020c010504030c0b0304020d050d2f100c0c1b1d011d060109080f070905180a230d1814030606010c03140f041d0606180f06 61
    0x191143e5202a881503d0b00e03030100003a40c11a1800d09055040625566a80c55034602600801c070750180040041021519071038026503201d40d110061303400403404200e005019480940c036482403034035025816040c459104c00490301e1359000302c0107405240c820740000005022b007640440100541c047c91040451100d400d00a140c64200c085030013200d00d0320040e0700c1c0d42d00d0f001c4041c0544c485444010841160600d42004c0000200742480c030107569000016101e440720340d4840d0b256400b4a12406400307031000300b240c2c003c0da9076100040206441d54408510b81c15041c4d8010f124580c410304003000841d485400c2c910340044d4036403c01d900d5800325844c0e03600b880f0001c02440b000c11064400e5500d0360841000724000741c0001003131030340e00004201c00a0798659018040b50b043c004202141401c0c1446024082960020180c400340e4845141c0b0310564550f01034440d51400801c01d2030911004601105c1850181c03900524036414041c284a42c08503895492403220341c054602124000356072604000f0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 434216411 1250 434215161 434215163
    0xa05060112020c0c03010501060212041e2102130e0c090a0213080f0f120a11011103011d010812031f150306090b01030605011d01030e011b09060f39 65
    0xf40504135992400e06007991010380048096401902c500b02c0e0070140c03031080e5022140112544410b043c02045400d641c09595001805240c0344400c0c220541040340003495942442956071011070743c0e01071010710071240c1807414241e40e500305800c18192031800c04401074100c2032441005203442102c0700303050010f034441c0e07120040c4c580000c049510241000d011031943c4080800141c400314400c00c0002c0a01e101fa0500d103400e009503000c020300f0700303282540104e20401d0841031080c1c0ea961115030304642e6202c86650201003010480002c00d082034003051815843d2050800c5900390344aa80d00399503445030b134040740c4080c802c00300400100e060300c0c80034a01d03503480103132030009100303085c002d07040140c84012004505150901c01d00b0445640c0c01050400c184841141e502c960140200040700174103441c00394500150f082140c006003050050582d82240400d9407101005613076280400d0f580c481c80d072070021000c00d100101c0380c40744150303901c0360015020017078603840030094818241011002d001c3e00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 434217661 1250 434216411 434216413
    0x603072a060b100206011505030c0d0c020102221d0903070b041b0602031303030e030a060609020d05090a050a032f060109060605070c121a150a0504050402090a05060112020c 76
    0x10051070b4074200f1602c1d00f03c0c0480c0502c0940065070509502d450f400300000e2026007004400000074181c210100c003a0b036035000640002380710004000034000d010350040c40384074210b800b06032180310030750329410300403002c448551201241040e50182a40382d8048020294102400f0401600e8009046d095100307100d584200102c03603c2d0f0242d10923140040c105504040203540c0204105a801d03500c401c03074030b02240e90516190044021810200342271240c1c008004007010308002c40480c0340121034002d030207090b038110020403065a80c146141e94850041c6400b034601d401011200001c00c2c03186800d031160361100418040703d003514000c00c80c1c098404185210391a0448070041c0580000d40c02100010030301441c200b400e0450b00e8644103490211480b40b00d030380a460505480030005200c5c507001c8140c21203604042039140141c142c07001e0800054030b0b28496450710380003003039074500380c4103c0d03015680241140c0e0b115034681a10380e000b00b81c043c100b1814803421084c0045000b100780003e000901c0040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 434218911 1250 434217661 434217671
    0x3040801050106031103251e0c02040b010f050322020a08060a0b09070f0309060b1203071403033105031306030e0a0b04080d0605040212091603020603072a06 69
    0x144024200c810141c01704c90252400c00901108681c0e84007480101c0c5064071121a032101c51820507121800c12a000c0441d0300c440608214850350007107404248140295000d011840c040700045640101641d05000850018804101c92201e661104005d8100c122401400300c00d0a4000541001541c0c0c426942503100720f0412254140d40c0c081c200450909503041ca58038101640040c1c0694440c00c0350b8801c150303449050030280b182c180c00c001c07084040034150b2007a004080d50707003503100d51120509a940c03070044290784440500c00800c0307903c5a2a07018036003a03200d00000d0401c400d0740e8604140041c43c0010b0761007101017141440240380c2c400e0001c503090728080c071f4034002800b0303a61042009009a04220080804102210b15541d480383d0b2146007030365941040a00f13007000f8021a0405504584003080300c18190001604c2503018110080895114080e005100000d000c2c1901002303410880034404076211601036070501015030f81c0c04585c014120491070801c10046a40c0c5c03004c0e01c8680e294 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 434220161 1250 434218911 434218919
    0x70b1602010209130501210c090c0306030219030210020f120901120f2003041203020c0a120f120e1002030603070911070b130c03030c0807140601051c0c0b0318030408010501 76
    0x4401d280e00d545101030362441f00755015119080042c0742c83c415454115160407000103034620960141e4041d41e4000d080c5850b0190103603079610003c0c0785000880c054000310350201c034603900000d030003403040541078006d007035080c0484031401c10341c1c1286100b01c0c140b11031040c80c48585110341c010180c17080005540003400464541d45403518000e40c2c500402012410010700001c41d1181e031565002c0622402c0c0035a0751040003102c03e18100c000c171409045450034001084d00c10342e000c0b50314241d81a50707a441c1c101c840c0350f050000c42180e0504500c090390b03501100461641c0d021a40182d80c0c084002410f44000b1940c850b002130a41e803a506540000781c000284460420948211094001c00e00011000d01c00c103085e034034001c000c040340c00301400744140a50410200403840040b600c525034002014800c51141d4200e80d0f50325542030045500c5070034580e900890310090240a140c202c0e4100c101201c1007841d100304a03500742e202030010700080381c4410f400c0883c036408000500007080c21800008207036243c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 434221411 1250 434220161 434220179
    0x6090d020d05090f1e0904080901090518040b0a0e07240504050a0b03150607120908120d0e0102090315010906090902100815210f03070b1602010209130501 68
    0x1c500d10800034440284690103041d1603098140c0344802042d1072002000c0103920480103405400c0c490260b01a0102c0d007084104480d1001130182e81c482a201c80341055100c0e0200240b180d40303003046807051f032048030014000c15403421f20b00d41c101c80007501c0000d48058407004ca0b42040c00a400c01c0071007540103055444403030044501980980454680241018146000034074115014400e492280c2004400b007200c3d09005c908080c200350004001c0c980d0b80c2242d28010a14140345040030001c203260070400601d046011512520ba1324560112901e030500c0035000d44014244814201c90079942440403004a0f1420421150040540800481c0a6140101640944030340360400348166040005030710068441840c0300350540c0311800e000e40250b4800f844100c400c1203100085900200f0401140700c1d0350261090b042c410720303584040d190082d40c600740440da2031141d604000e048280e08400160120440700b074400d01100c00744009403401340c104001410b450140810030085c1a0345000400030125 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 434222661 1250 434221411 434221423
    0x9041e0221070e060303161505070917010605060a0f030b0a08030705120f07200a0e0a18080306010f090b03090705010e01030b152a01020d14040b01050f0103060806090d02 75
    0x10b0b07045400200e11340040442d869004d4a01d004410201c10401c10040100d83c006400f0343d00c00c445420030441ca044140144090028030a8105a6020401c00502c5603018003902c0107548001c0e01031880d00900c0c100c200d40030000e41030003008160303646a14003503558031500c00b20001d00d188402962201510705240d41001c4445079211011a81004940b600c40c081d030043d210311039040f0260450521380d4500003100c0e01000ea202c6070307120b00e4100000c00d02403401d20501e405503400040411020728000e411000d44248450003800c1c2180034070015120b0344c03096405400300c03d42450100c644544d50203028005070003c3d02e5091b1039400030034003840310356484001c13004032690904c1c06010900025001c81d41004030280c0c8031150a000264019071410840f131020041000300003101140c000100c0c90038002c3d00b14021480300d4500340b5507502820b0f20344d00c0486002d10b400c08200c60950746010200480080300d0f804040c1456229a40007414a0041c080039202d50205070142c110110200b0000f41029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 434223911 1250 434222661 434222669
    0x818031e010c08011d040303020f030403021005010f03020d020d0230210d0e1920060f042c04030206060306010f0803120a090606030305040e090601030209041e022107 73
    0x440f5142c01040524018099010070610800c1081c0d1181c0f15810103c001c1d100d10301600a085200100f030004043e40051b0040724400090340810071b6136215400540d5002d8030344006540041c928194101510b06001040c0840f407000b404c00d24291929410070303500d244004100d0b000c0340140c15003600820f0081c072002c8072904c68044c0110305400d12843c040380c00e024034001d5045188c1c1d180512621610104105586407024840410380100c13a0f140c40000c10b1102d1094901202d8030215400c2c0e00d0810805a59a407845101c3c95030078581400e000d040740541e191b0200143c0c0b0000c14007c8802001a8035907030145000342e004e0619450400240342c40d114040e03100100420802c4003c21403000c0101c00e803410b41401d030528000940b01c200070000580210140940880e1a000e400010543c0100090040319034840c00c6001599038140100c3d02c4820900c00030790010380c2c1d4030020b400681100d600c1841000d100440450188a54000c02c007400f070400da52102002807006d0a110048007000100010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 434225161 1250 434223911 434223917
    0x1051f0603020a0c03030b030a05070902070c0504061212030209090c04140d120c02030c040c05090102070603290103091407170303040c170f06071206080105090a0818031e010c 77
    0x1007860343d08000d29562a800004c0c08042da20708901c10f0960b001e0281d10300c95a084022640c0c2e598035040114029444003008540f42c5945d0031000915080c00d000c0c0208440301030840500c481c2064071608102c10340c540000c0200740c1d00300444801c41ea501c01e03030140502d1180ea8020740321410100c1d090702c80f8442004840c0b01d4008041d0b03400000700141c80d09400c03a841490241040b0072244007203841c0198039070000d40d00c182407041c844c143e558444054500c0c80826030071920b905a90342010b40c11911801a10a000d40342c03d03c8a41c50040075603803445102d40e0614001400c035100b502c0e9801020004581c424650300300d04000c004071100c0d00050070047ca50b0360059461810039a07200d41204da050700c1003411540d00380c0d41003400400180140c080b258a06020f8445c0343c508a080101400c4003401d9115205160403c08907100700148180c3d40310f00c80140c01020091034944400c0a150404550036029500c52288500d483c1c80c184440800030b1889000e091404c4c0303210000e242540c1d05201d0304070030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 434226411 1250 434225161 434225167
    0xf040e0915061c1212050f0f010515040303050306060702060c010b13020c03070b0915010e040302120a270f272304030c0605040b04050d09061d0d0501051f060302 71
    0x166804650b0f10040705035012034a0543d0030501d80c802e4603030b2685940e440a40d546400104410a9001c8100702c1c46108085407500607680c9620401040041c07205001031107201c244004c0c03001a00030b000954000d080142520f0078117810f0b900082c410b60002060407245c1e5110b42040815080c0304c00c4101a505540d01e003503042200e10010a50780740130303151001d41280c09100c0410805031051001aa00b1072145035070207000d40e102c42046010203804d4804400500c100c9070071006100c120400d40e00da5010729604c20000e21071b1a0120243e068141e0032000000e000980c000840c0081c6400b40b030010000e0b1031800342141503030056034038085181c4849142c000d04044e0580c0000e40720b8120003101441c0800c000280c0c1d101d86c102110030340b56100f03000302994600018003052040c591181e510440c032407400c0350004844c0741c00480303c04401e4450440400c2c0310038517044a00744002002095060060812403145c580c68aa4600303540007a159800d0443d48034038030400180304180400c014000c2c1d8101589 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 434227661 1250 434226411 434226439
    0x31707020c0105090a12050d020706021605120f0d09050108060a031212061d0103050606040c0e060c2401081603020d0602030604021e031014150f040e091506 69
    0x51601c440c030454504000000400020903030ba00d03801040613081100842082114070301d030050b41d528683e01c0d04405881417210008500d07100140c40458100003c04401e5560318100038400e81d4803c540190501c0c3c05000405001403030200210031200c43c00f0f656000b0001c0c5040005003001c04c01401c081d004d1040c01000b400401d401c54142500c010305443d14450165030503121300d0041880da04107000034a0115071000707403d050100c91b14160b900030b2050741d00b07a4441004001c101d07400802100e01040d01c141c94080076103808130141c00f04503041c9040c0d5148400740a01c240040f00c4d000c201c960701d40003803401031065a2080020681c2d50b180e44002441c1e990454000840d200072803070300100190380000000e0700300d0300c8640641c0d04020f9400143d4201083d00c141c0400d66410480f50410381c0c100380000021103820400341080b550f40040e290032050b602c1500b01c541694400ba02a4000b11003c000009a6415083d01140305480d050040c11100f025040144440040074050a10454080d84081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 434228911 1250 434227661 434227663
    0xf06010e1f050c0a05120d0f14010510020102120a090c06090602030d050403051903050109051f140a080a03020a0b070305070f0f030b0a1d0901091e05010b0d080703170702 75
    0x5585040341040c0f9122100b08814600d82080c4580c020928040c034440070890500400180c0602d06103100306000300006100c0d05011586400d84410072092002d0042200303041110441c5004100c51001501e0990325a0b480300419100b510f10380c0100d607803a0042020300010112600c090f04651030f00d02c4003d1f260a0009590b40034500030002c0040d582c0d0085001c16011704112402600340206503075804040100140c0244070901c100d1100c2c500303040002e00b00b1500c50424200076840d5a441141c040d04001d03801c3c82121203521002d4010000a10204035803000300569803245200740e000b4502950036142135074075130402620f0f540a0505107000d2011180d0410007900a000036882d14141d0f41e000144101e0142120b07900942e08450042c00100d803965840003000e4002c120070440e54400d8840800c0d1600325801010b0240c0b10103295060a43d03042c8800e41144010b500540000c80c00b0b031b4070382e800561070000500c4104ca81c82c80005120040540281c0215100e00a01c803100c03a5602d4240c4001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 434230161 1250 434228911 434228959
    0x1d030c1e060403030c120504050f07080c011d060f040e0103060b061e03060409200a0b0f0909040f05011a01020c0108040312110c070303200102040302061e0d050f06010e 74
    0x101850303105d0b031050170a00c0c802d540c00ca01d044078550042c002c50805040c082d88071030304c40b01c000e2810b008088001c2840400010005e840c05070617980e0310320f18000542c3c80540000114846036101204105003400c20190303d001d44068016090902e03815495850700703400700c0f0384141070f4a011305070900c440d00c0b00104400705030340111000468942d072582c4040000e8005c000b01e410003400c0341041c24a0107410303412400348c00b2a90344162252006192100305224140c002e0381c45c00e43c0300b500100200e8410341000206950414400e810f4000e13403035403543d20702d400d60b50002c0b079191480111040b401d40c9981e040001e03900500080c03c20345414141a18010450544148c0e040c0141d91030f888800c000040c94000c07180ca1050700d0050345c0d00300751a031a00601031800c011600c0005441d282d8880c03081c070010701c220b400700c0340c0c010304c0d0925000260412242441005222481061081c80098220015402658071451013408009260b03d4503200250940e83d00d0882140103d132855228807000c0001444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 434231411 1250 434230161 434230163
    0xe2104050f030109060510080c0a081b01120203010b0717070b010302060f090d080c01050903031303201014010812030a0213030f0803070305160f0e03011d030c1e0604 73
    0x186010015001c0c01190150200c5040201100d241a040160200307440d8018030a48000c00309171070b01e0401c004100308121055000c0d0311640e8100d4519401003d403104480000558181800802c68560070303010403c0f60000d0340261141240001c40c4001c0000d60710083c5603070b5405030300c0181000313880e072900d81e40501d050000138001c02000401803101d40d842030958007242001001415a60510300e0052425040000f4660840d07080038041065180c0110a41c3d108800b42a10f07072000b50280d0300c04960700c40c0d1b46140b85241a10f60f10343c1c000c04005c244400e0050399440c000110308450004c3e98584650b00503802000c0c02d0700300059242400750120100c03a0032040c41080561655000c4981540403c901c7d80001c00c4000301c1102c10003040099809540300d1441904c042000c1d40d54203061920380020701ea07844000411190103d204640212022007400c1400f5000150305c0c488403902038050080e46024000e03560022600003400002007064000110030200c407002116031b1140c046a4031480604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 434232661 1250 434231411 434231419
    0x909020f1227070302030609070302011d0d062f2a030c01140405010f05060117190f0605040b0604031109180d0906020d020609070605090a0f090e210405 67
    0x30220350010300b4080c4a240d82486a1144400e004412414954461203071104038000d00600d00055111788011611400b02ca0301a1641c4440641c52415110f041a40010495002c1140c2a00802240007880340b000e1144040300c2000410603005d090560105060449881980741041191080c0015800381c00011000145000030240040f6045045000d0b04408560940c6060701481e8000e95041c0524004e0780900001c00c015005d0f10158006e0300e07400c035406808078074030740c403c9005024660a01a8001149985190030009000c03988007501d90368446803140341c1e1119000d0080e841c1c01d2164415270742c4200e0ba05460300b0b203103a89140200c0d000308240d511a00602000403c2e42d0b40c4101003001107000e1609403000190f1581c005890341e1894001d0900511502c80e00c4184a0300001c2d00600030807d020040c09018901042110b45030b001003c80c64000c2e80030f440000d0b04041c0198010040c000070140892101079403107100303103406082180028012403044812120184440445095410640e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 434233911 1250 434232661 434232697
    0x1404030522030c052110180b090606011803120e0111070b0307090602010b0a14030f0a030302030f070509090f1302030304030c080d1b11040902091303030b030a0305300106050a0909020f 81
    0x2805200180f0032005012301074020700010090b6640000c00c00610501c4241c070744141c01c0340c0e0ba00e031017012035a040c00010030241d40a180e000300c560188283c0000040c3c14500840355400b03190005090003a5030380f103c404250048244007c56401c0074080010b8805440200b200c001c0440004402e901184100c0b40c2903c600712010007191018000700c00c0742d40350780c011a0148025460002c0c02944126150240c4800c031602141009100e141103401d0b60350000d2565009403a410030340815400302900403081030740c5011440d40180c80c1030000d0801140600441c968284c9042d1405003843c0b81c0c025181c0400c0b5127046030728144c401c000701c1800300c140c00c04282400e0100d0580468020041c20f03001a610801c034000300540303500004c000c0d007009442a07400340848484a0107050b51f8a003480760040c040307a020b01000d001e007500341a0540441c0c20112127084200000c580c18110440d082c0c00c27050018400207094410541c02040d1040102042c413003c529003000c014520100b4003440912640c007007450 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 434235161 1250 434233911 434233931
    0x5010315030f122a0807020d0827010804020303071b1d060414010501021f02040b070807021203130306020c1509061b030105010906050a0e060408010903121404030522030c052110 78
    0xc4c81d07548c5640d10000c41607886116002c1c0ca150001c00c0a0307210411a8841400c400c2c5521501c1c90600550b0b01400079810017210340d9601601d840d07100e409500d1002d412100242d05442c5585002c5807142081107103901d81804c0040c08240c03001100d82d0381150618000400859900007818410024203d5904843e510a001400701130f201d80d5014480321003020030301c1024484140000c10005100b22151905441c10040c415123038041c41d04841c110040502080011803601c0d002001c40400d09800c0d40e40c262410f136030042d1602c10031790386460307194010003c00c5190500301c0c203c0b00078140656242d40c110741c0b600000800154081c0103600c2000f50119480310000d024080343d1180802c02002c039629181c0324580103000b0069003009900203202c1d61280c403079605151246803400921070184482907500d6403030075205071b400043d071500c0a0700c0400050492000c1c0c034420f1000381d84600300445945150004102c0d01c5402403001c03030355840404017a003030200e90000e145401c11031040808035205c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 434236411 1250 434235161 434235169
    0x100f1407020a290c030a0e0d0e0d06060b0a08090f07050609040b010e0d2a03120e0a090213170c240f030a050702210405010315030f122a080702 63
    0x507110941e9100f1000c0710a01007001c110201951158407104000c00c002c14012001950380d1042c0300020010071902010441d65040291000b25011300544012441540c1d072421030b0059030107501c0c6000050a0602884901802400700020201902c4c0003841c007a810100051418807c41140034450f41d501c0c010082d140c0d000340c1040320040b00c01041904822204d04000b0300c511100060421070006000c40d89607440e03814000d0400f40c980001582d2000c1c6032803a025511503000c262800d034080b14403d00041c4408050008005100100c2c644032040340c501b00080e0160614001d07804400d82042106681c145c0300c106841105590340d10491507800041c4c2018000c900c14900c0403010103900004005640305950412400b40803640c0c04c81e02d09400c1083c0755001d445240111020b0848200801c102e150300c82d2308601e00c2c402641d08040841556542c802c2803261001808403440040c2104801c480c0c0c4e080100c4007203802c080314020f00b00e03217150089a9003005501130010b0020350041003010554031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 434237661 1250 434236411 434236463
    0x1b04081218040e0a02030c0a03030e0423040503040f0b04030b0621010e0102040509070801082a101706010302090d0b040503090a0602062a0901081503100f1407020a 72
    0x18064000c01c2400c0000f02c00c180c0302c00e040a0103902a200d440c09806944c10000102070803a0b40564130b808000359080c00700009020143c03984100340076222251030b98101c070007080c10300540c8501c006507621840c0140d840c0c2c40107295480903480c40f006000c20070124101c01402035000c00100c400440d0ba110380c2d0401c0484d07086021030320000d0340c6800c00d00b040c40c1005600500590760111500282c83c0d4440700100c501d141e0034004c45165801c080c88038000d101041703c0d4907452501c5884170802e00d030314001c081104490b48a030004005800c80d007124011a40009510380c00070020710701903261402c1c0f81c000c0707005074040301e000905003021030001400b4408240251407101d03200030200402c0a5640c4c2c00203603200350654403440d40b140d07041d2031000001e55680c081710402d6409446581030402150042d103000c1380003010240404080365918000356010f222a0400003034245c40000e100b56030701c007000d044842480140702d0100c0c0e1041400111070700040d0f21090254800989456407000340342a1031a10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 434238911 1250 434237661 434237707
    0xe01091e0f06180608010506101e0e101d10020d11070e040c08072124060b03010911130b0307050c0d020a031101051e06060403080409051b040812 64
    0x21080c1c004440c80f0b801a50061400c40d0190002486261202e500308100e2410780c207200d81c041500d05148203005900d0208c1d40308ac402d22802c00c0043c1c80c24401c08100c1603000c401c15a070006005840c02c19072042c180342940042c1c00c054030480c81400701110041d5480b8a0070f0304d0b101c140554408001c0f6041002c201e50f80182510b62100c1109040c40d24010a031081680110000342c0282400410384480810034100054200100062212580d4564032580e500701c01c0702241400900c18422804407950049800800302c220312107070f03650f04d0300401d10211156901d201c058601e0411a18000e040c81b400f83e0001d9507400007030280c0d80e81700c0500c20f0751944030b0907c07035481c03a00408007000742040d0007107603221015002c2e4031070501180001c02c181c2d08854080f1402a15051325004109184081541c401e5002c0400703000e0904c0c058030380d150810940c00c00d42c0b000544d240c070303401004440042e0322414007510848903195810281041c3c070003030300c0700f2034184e1402d088140410260f031582c0c00051921600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 434240161 1250 434238911 434238929
    0x80c010b030a0f0204060e0403090b090f0402030702100b0609180703150e090c010c020d0f0303290f010f090b0702040617100b150409110403060e0303010e01091e0f06 73
    0x542051070083d105448240099102e1841c02d2800202280e4840003148141e51560318410090304203086010b040e0090700446030000702403c44102a9202c92000394024a100e4005140c081a620300e44e0068544d840407080c0101c5050065000d20b440d181c0d03400110780d0030308401c02002c2d52401c0b0210000e010844041182070f0541c1c2001030382c0048100e455000d002440706881d0b003198540010340d0408049040203410040da011002d0201d141c8888200145100e032902040618802c10207256048100003525200a50170790303080700c1c614150642010040c2d0078200240f041c181c01002520b0103610f44503c42d0703401400a246411580c80344d120b500a403005400f07400c5001d000b40308903513841e80031207005012a0f2038800359507000d00d031003c88481c804003600892407415040000c402c008d0005650f504034445001d02c030100c002540c900808002e8038406c402141c8070342c5803d4018060641c180c0c4440407491604400d54211a02a8035019100d4a00440450200c0b2103d80442c000c05465101441c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 434241411 1250 434240161 434240173
    0x603030a140702031c0f090609060507061a040e011413020102030a081302090f010603050907180c050f03040f0201270510111614011b11060f03010305062e03080c010b03 74
    0x10307103034016246c005900102e0780e4061031603407180d03010b130b4910a150181a0208400340911000582035030801c041d01d24071480c2c2150b5061002020400f035480c00d5444512a9440b501441c0780c075500e030214141d00100d416916080244540c00103901d070700c0740350810000c1054460005111400606c1d002014540c0a0030414640c90b140c001a01108400e01032100068201408100180310001b850015681e1640281c440e822200400c2001042c2c281c50340030920a05200486210329004080c6110f10301402e03051803210f42c68800103115203507007555407901c00a02039040802e28078140800c0161581502c07000c2101d0940101940c41c0700c0f09ca507240a0074411090080040420008510204c0d1005450003c407283c3e01d07001550300c070301c001141c20034031048282c0800104a10303100140c03480d440682003514007440a000600c06910980050701c440c2e1140c4140003100b5a180c0e1104c2c0d030199000040190086040340040058040b4230018001c01300102c0e05102c0c0041c2075100fa0105070005045480d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 434242661 1250 434241411 434241463
    0x20f190308070305091e09070f0c02030f0c01080606040e150105091009050a272703090e01090b180606040f0e0402030706020c1c06180602120603030a14070203 70
    0x40390303021417000c900644001194030426240c5001d0141d044100414a4206a560f080d04440c1196aa5a003204000c40410440051784050150784503400005000c0e280e2650514000f40280d40043c3c0018029403081104101462a52a006c3d03004942450399401402c2c4580040b80c860040402060b030109001400c03c031400e0708440408101c80d0700303440040e2400e5950328240280342180e13910706407080100002c656030f1400b03684000520b05c542950602d101d400d803100001d0189209008a0100754091428001805500070103401800848400c1c820440c00360007180b6203190101d0311054012030b40001c60a15075444058802400002091800e083d075142890f90015009440980c024010b002021540380d1000c1400e52883c0c201500c000d03243ca6119080620346068004140e400503a10158216102d401c4000c645070316015010140e1284080c03a040201c18901400040c07195004120400c050764120022074030140c5a8040c0c1f9403140d40f9800481d007041c07a04040303110548698000c9007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 434243911 1250 434242661 434242667
    0xa0302040b120a0e06060d020d02032103070e031218040b04050901021804050106020c062809050102010c0f0e0d02040e03221403030301030609030513090e0c010507020f1903080703 79
    0x648500340070700b001c4c44003c0d031034110551105400d40710310303402c9802107034440054100400e04003c000d10250446030021328001001d201811002a408800344002040c4842d03241d120040b0600d01a088020308044041045041c68521415460000302c10340301846207800d5595074000e00320403201801c203004514203e032072103000354407035006c40789100303a14101b41119040170312859040e01c20b10340003031264942135001c000c1190015000307822088440a045603e80000e8501c08100c60f10507150303854424140000a425103004900c3c42080010503220070a065900c10b10000003042d00380c4030180c9003a06800030601402d04030490203001d00c00065180f42e20840d120b0100340c1074110a440e02846a01c5201c1850001e08200d1760541c03542c818801440071035007d0313201c01e50b081d1080c24041d26082c4042c0401910b0b0807503500002c0030303643e10240c128691000780089003540707000f40303002d926040311940000c44008810641a000d2220302800048444424030b003400034503049000c00f92906e946107801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 434245161 1250 434243911 434243947
    0xd09060906111e01021c06142407030306140402071101031d0609070905100b0a03051924080118060b15031003021306081f06051203070b010b0702060f0a0302040b 71
    0x44103292103012013006c1c90b07045208603800d55100c146c0412442150301d0400010380340e120f003c1c43d18135803202e0312020f40c0c4400c1402040f0551081d01c000c54410b2078240f4100c980201010018011070041040e000026081c090754491f102e0240cc0c00500741c5800310358140c0210454101d82e426115040600440341e00c00200d010884114807820f01803581c07003c4071740d07a01c1449445201c4d4004401d002d0304110344e01030f810940d40700703c02c080d000101501c20581c01c0165683c104110616038080800180c60707548854503070000d4500c4900a05c01000c00031010751540414540140500396980a603c0c03503540d480c60540040c0b580c90112a45900b0549441b410340416880100c1c4a10120000a25441014020380c1c00300e0311000301600104035000c91040400002031418521640d4511001c42d1560b200103940c000342ca1008011601d07000149080010070006802c00c1d43c4189061101c5001a030700c0c101110042c51607545061740740c049500007070b00603008a401c0010300c040003103410007184060400f0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 434246411 1250 434245161 434245177
    0xf01060f14031c030f02090d0b060f01231605010c11010e120409020c0a0203100c08010801090c0b1b070b07050d0804032f030c030406020d09060906111e0102 69
    0x2030703620a00d080c00105590760101d1404001083c0c3c40070880b0603618042d43c05840300c20b440d40409445c0080b4080000c04010f682201103a4114044c41401072904104506104501e42801c0214924800c5d400842104800e407814504e0880c0010b803860040030002080e40b5030076840300081c080207030b0516000c0c0c0441c0e03070040106010361801d0300c000d5214400060004040e4040c2c1e80c000e00c0c1c03d0800300c440020354440c80181d2180e1150000101c0183c400700400d000031100c48400094240480900814080d0b060384085050fa0408480700d01041e2031003280003c49020300c200c07139503401903000c1d01382860002c181c25542e1800303680000510240301e14001c1500900c9641510000c4c2e000c0c000540e981d000035100500003d401808010740c120f8000c80d440c1006800551a20310401c0302d03d000c0d40b440d07000c1d0030300b4111500081410091135804102144501d005820310050305410200014520b000a00c0340000704010280403660110b818403003043c01030ba4819051178a0340031084094080c0d4490f0300307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 434247661 1250 434246411 434246429
    0x7122d0b0f010f0509090a0b0f0601201207030c0f0b041a07080402101715040c05030f0a0f0e03070c0e0a0209011202031e0f01030201080601030c020d030e0f01060f 72
    0x80001c1d5050310304403045050b90680300c0800000390502042c0170007544001c1200c051031160f119040c0105104182c100d103c2c00f043c10312003800303160401c00140300806106803042482d010040c0c0301d4400101244005444d045c070743c01d0544880843c02c0454142901d028041d080b0003017000200240702c00c04603000d200310300030104007101c01c01407844d80c40c0088089958000041c0e0f00e1010400500c2e00b404140c02003401c520340308543c0301d2040e0002110500556884545141202002103a41040c4c047e070200220541042810b51034001c00b0000b1040004088842640c0d950281204801c003551000454040d1401200c2d158001454886c08085241c0103c20503024001d00181c2035200c0c600072a8a4240f041e03450030301e1002c1502d1028040d4001410b0b918103104070b503120404010906446030310900030840c4190413940b4500001d0841e0901402c00303410907041006d0244400d0b00060201d03ca006e00c6d02c0c0000f5180443c0d4a42410641001755044195082c540d00203a10500c1c03001100030b9601444c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 434248911 1250 434247661 434247683
    0x1b0905011b020108040b071116031a0112150f0f0c11010515060309071a07060c05040308030103020d020f04150f150f08071b121b0507122d 61
    0x689840c2a4a0070080000d0019503000000b5000031001d10104d071f04003403541443d403555241c40010307900b40102d461103130380b0303484407104200207100301c0ba82800c3c0c44041040410744154100103021500a00861001d007a11391050007204502d140f07988105201412034030100300d030408031002c08001e00056034135400010140041240c4058041c40f5072070040054542107d9881404802e0050641008200c0a0395004092000030580081441001030480c040c0c5035641d1180c0c249044400c49440318200410400140030074000265034004a80c1982d804858007603002c0000c1c400100000f00d0b0040558003e8102068a00810306100c42901a58617020001c1440c41e11990f40201001d0a0385130321000a5031000c180300a13038080c4180c1d5402001c1450881000c840a25408401c981c59036001c40300455400c40d1180c85550101c1084032410840b00d41500031320603a03c0c0d555a980f250700848003910011140b64041046040001211140e40780140070032075000b003000c11070510040001d03a9401404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 434250161 1250 434248911 434248937
    0x3090f09021c0c0905040b0a050a0803040f0f060c030e030109051e07080c09060402032205150702031309020f040e0f04020906060a0203181315090606020a050703020409061b090501 79
    0x140544404020140c4d00c2094140c0f0f00030800002c1c14124000c281c1003841518081056240c50100030081c0280b50700540e580c0d442d0111004240105502240404904210a100c0d041e8020341d10500503030076141494101c1000c0c00041d005140b9404000c09078403607100b40600c0ea10307004024450080804099402c01030b500e040240d00c40031140d841e583d201e41c0c1c400004071140b40950207181c000800740640c0030240c25511000c0850444000d040c0c0c2e07a41d004142a02080001e85003865203c0e00620195080c5820904154045a010300030641211b801140a0400c00013071000d450082c00c0c4681d24040d5030078002e5100c4158130082c3c0e820307070052844500087c07540c1400c804550450509038015842e0441c1484480000c0708034542451b0b00180301001410818528000c54240c02e0041c1a04000b0074a00703c41d2200b110342136440001590007034503041010400c045800002c581e01650003003055405850b0402c0241000031201542c0480c404a5013034a580c4030314030000380c50003a22030184260384 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 434251411 1250 434250161 434250217
    0x105070216060306120212070810020c011d030306090a020f07081b0601051c0309090c08070914010207180603050a0b0403020c0a03020603070f022d060c0a1b03090f0902 74
    0x13a900a6400300b100502410006081500e500c1101d00004c03802d88244030340b20000541071074041d00c0910a440d401180000e410203081c4a01c170075070041c60048a501d44403c1c18103a8503404010a158401d581c4103000550f030441c1e03601150380710f200f18091141d5036492860305820907001010072440c0968404680000c80d00009419416200c0c01001e84010701000c045604111303021500813010441c0d02500010700d61110300410030444602c2e00d40c01c1d2503240c03024004048418603400f600002d642e600907443c450341c0100700300c801d5643e02000303d11802c3c1c0b4800d00d8800383c20b55600c001c2c0944034040d140390500c00c104820b10b00451180d42650034141c40c11081000b1a07242d0b01000e0b501043c20004200043d0144e20f60358070038041030064500c4500b8009404005d1090040c1c2c400d01c074802c503c0c984044620900030b03207038400402c1c071555040200d0311070000c010046000010300e00d0350909425405040c01062603900802c2c0b400c114280c3c445d150210000070b07421405800075500000280c0011403d9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 434252661 1250 434251411 434251421
    0xb1305061914100b0f0405030601060305040b1003032109020603070305190501060e0108090c130515030313061103220501030b0f09061c170a020f0a0f03050307050c01050702160603 79
    0x2042000000f4242002a0443d455111030451298080d040000182d5602c0c14803a0358000c10441e14001740d1850305003000044070100030714088071320006e04030500009411500c5a06c0352007000144480302050818954018280ca16020794030031004820003a20b04d92581009100d50203031404a825850921f0400044d28000e00895002ca50b8840405240354480d40d81164003400003000c50303110300d04500108808450082048094649440401c01d800a50030409402218185d00440c80c01f0082040d40202640b940540c00400a80c1d404003031b01100f01f0015140c10820410803850310040c00d50058404440b0f40c41441d0100b03081042c2c0d00410310340700d100c4d00c0311102c0180c40004555208003c01094209200c210000040d42411090210b42d20002c1c4040b280070699580355200070791301000e8500340008480d40001e500c60796240d00001d07410a0081c1a8641c5424a0741d241d49a104081e1614010004094403e61806c0d00f007180c032907400564108801c4100c4001d050b855221101141640c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 434253911 1250 434252661 434252671
    0x3070812030703020708040b0d0902041a0105031602030705100903020105060d02130c2006150a0b0f070206070618020108010801060803120402030a0b131103010b09040b1305061914 79
    0x2052000030305443c02500100380007441013a010303140036105c0168059907088a1840310040e9500d0342d2200c11400d0600c41c440349a0031840b42d8280741ca008400003009440300034603044034048051810305045000f041603034141c03948207040c0c0e01105010008000204451481a0015804d08001c038005042201c0400c0f8400d4018080c081101000c0500b203010700b050700c411804109201002c101080b40340179001c4030f5000e240e030241c0164100400d880381c0002c08409003600c61413020204101f82c0d040c90040340e4040702003007113842e120344071400002d046004202c0054522814080c50070030026042c1c0c000604140700341c84421040c1d0702e8541aa08031103890051607615801049110300c01a5504c610540c0144020104c0f0242d541554580d03522000541c1d400c0514154011100c04200c14a018001554000d600170022840842c00180d42c0d10005040500505801000724003410002050b0352207503030b00001115030314107010b14a040740b207030007044140b0294507140c0605405046906114060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 434255161 1250 434253911 434253943
    0x390b0a0204030f061d2508010c021c050403080d022106031905030408010606030219050c2d011b0e040203010806010312051b0a0201110a0203060c030a0b0618030708 72
    0x142c4511340c0c0b8080200040400c090800a102001c0d028510b800c200c0d0f1402101c4002590700c03403d61b070082102c2401c03181d40009a060341002210b40d00540d00081d072810410300362528082d0740074961f00540ba584a980c0010f4405030b40040c582180030700ca60000d140f0b81b01442c1180c041220b490305040d009802c291b809130b40c541c0040410b20400340b0500301e0300045a001d00b058034681551250034900311000750b40940041ba030041034588403120001041c204011441c10802c3c9407510790b865681c1c541c41107144007032528200240303048089400262030101291154001c001102d1562420305040d581102100001185408d4001d0360b420a40240c904894034031004004607420340d503072050003078811000e820400805019004200d0600801245810050006448102c0d00c0740001044c10700d03255207004003688074040c8500140c500146c50740d8040c0c50440c00f80e807213071075071101d880c0503200141d04107038400404110f061441002e10309510b0280000c90440c3d07011a519000345880e520f00001420203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 434256411 1250 434255161 434255183
    0xc0601121a07081801140f01090506030a2f120c0405070e0a0e06010c05060106170c0a0509040506060c0307060609180f120509040614030d0302090f01390b0a020403 72
    0x84559100804c0d461900800d002107030340c2d10403a00c8615054003c41e82580b003c5204401003040141503ca00d40d0000c070180c0260030a844140ca81110107086030070111100d4100f0a0341e0380d200152140c038058041c900500c004220703040c60607055600c00c52190030b64400c518003000308242c94015900c0440c08080505000035207840d241f80c10016240040000b41403140311001a80020070030300010303020705080c0d102e40f04920940d83e00700d8000300c4c004041ca0103205003040100c0c0059005401e44034165400c880104140d074030390021506a0042840c80c1816110111b448010805942c00807402c0c0c0d5070084003049210180792a00c0120039681e1000b030308420448c440c040200e407145010900359038082c2813036880c1c143e81401150071144d0f9540401803203103c17210140c0d141d103420301c11224819a50b113415820610900000303a40d00c09019000e81c140000142e0031128001d09111403040e0340b04001034005034040d150310710f20340642211800c440d075800c4040080e1050031180309031400e81c0e40022100403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 434257661 1250 434256411 434256421
    0x3041203060f060c0813080615041103040b151302120903041a0d0e0d031a010201270302010f0e0309131107060e012c0708070b1e0c0601121a0708 64
    0x26030808801015202e040d0b081005c2c1b80000c20b0140040014421000140b541d480c01c018007440d51982145020f12860030f048420081d1001c6800781c2e40c00c03540180348031205445e480a060024a60b4644040e0090614030103049001d00e641d02a1a015205076941e03500c0781d903034801c030765224440d03409510b078501060590005400414009046042c800500c00188144038030281440d24031040c01c10b00c0007a8645414200000e407248504c03034600741c00e00090042609010003001c2e0500c9140d513004c02c1c01e19000c0c5050600d4800d400107000d0802e004e100300000301400e00f000e40c482d4042018507000b0a041c841c2c000c0a002207202c0c015a45001d14100c509188090395404082d140590f500c0a841d03407507081c0d2111041c2644900080340506904022207003040a01403030610f10603500980440d08006d1040003258882821100c407400d0300b26106a100c15000b90408c208e0292280e03029941c82048008502c1c0030b0240c9018011a0081e410440c003a035000c402d0f01c5000e2001c8030344000148030100810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 434258911 1250 434257661 434257667
    0x80d11030f1620011209050c06030702010908030f1e01080712020d0b070201050f06041103040609020a23042009011d060a051e032e0f030803041203060f06 68
    0x41115401c40078040c41d4244107443d040e01d4245903803101038850700d03005002101c0f50381010101d40d42c2c0a241105004020440d11056114407000824034007036100000041c03087c5101394002e40c022503000101940b0b038100081200300b80030007201d04401541c2141348800402e943c074108107040f240b5680040c903d40e42072000c0c0e004041d120510498024910f4866100000d0207080450b00c2005035900003c2c5510f020000000030313400151415008034a0108510b1840303401c2030440e54031070b8029a0119010002e4808540507007200d52006600b204401c00d955003204007041c84070f01c440700803a0240320700707903003c603507428660b6126a400126202c00c014003113a42d4042c04032640c0d6040d041c17501ca20031400c1c10000c61310310b40c41780ca85800054800aa200b0480c0501210311045114010307806085140060f07096107106800b8414a800200705003042060492500c3c5100103060048000414650f9a1900f0300c2c03250070503201141c41410000080c61024400e2240c40c04035040d07028681c0078180380a1040d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 434260161 1250 434258911 434258917
    0xf0204030c0f09111608090a0806100b0c0d03050c0c010c080a0506060a0c1101030e0303070203270f010c050a050304060c111e01110c060f0702180f010b0c190b01080d11030f 76
    0x2240c0300782c6e0501941007650707078038102c0000a10b44070014189515016500400314407040e003001c1c1541c0810300019400c040e0003c0d00614890007070400140d50b494400da04c401e06c3c003910002c94120b40c01c1100421030590b0100c0d8160280e00070b01c3d402e02c2540c580c03908101490080e1000c071400102da0500341c002054400040e80c0050034103040010700c51580c4d641c15406d580c0110740c5400035078000100c00c0d02c00c030800c1d541040c8021407003450715582380502d000a2034400300070500a0400c900c8a034414107000d002d00c040c7c2500c90307100c0d04495942e079885401514440305883c4c1921300400703202d2100d0040c2005509641c01200c2111010707100b42c4464010f461140c11240d00f80032034880d480711461540c071130348024004604c100801c161100c00034030400085024800005c141102094107224401401c05130260656042d01c007d80d4071120003550071450070044804240c4504600455035041c0485100e41c07506807480341c0c0559503210a0b9581c156992941004102010740c0108000b04c0882010006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 434261411 1250 434260161 434260163
    0xf05030f060405060418140f0114010b070c0e162c09071101053c071b050d120509010b030307020f0d05030a0201060617190f0f0204030c0f091116 64
    0x100281341b20300e041c0040a40080c0700e0044503440c0e900044a5a1700c681017048070341c0c1914a40090014908005001001110611402c901c28401260305020007030943c00f44809400449a1303400c0515000d840d44411501038143c410108540e064646803241894040700112800c80c04200600c10002d0180310703420390001d000303004000f4090380b89c030070b0a1403e000e04c41c0182001d9006818842d610081c0c0d001541e4198445034128000b10001512403c24105095106007241801c2c41c0318020760740d800d000c40304007000050290150600258046401259080720000c01000800c410381d520700c881400c844007112080e5060b8014000400103207890980103030303240e0340600400270189403550351600c1d5802c00919100076075166101400142e500c11940c81c158405044641c00f5401e090300b0140f5002e80000c1b0400c071268807003142c1200d946041d00410b03540400d044003150754654a05051a020145028192400e01d030080c001800c00072502440740f0042c090402180b900e10181181c0c3d41141103154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 434262661 1250 434261411 434261419
    0xd0f0209040201050c0106171c090605130f23310e030406020a0b07020606060702190e090307020a0f030b18010b0301090804091d032505070b0a0f05030f06040506 71
    0x1c00b0790890001c0c0075a00003401c0c4582030301503c95009100c41c4c2827000c07220340010003e003082070f01c18910b030340141902e08460003814800c1e550707a62a2100c1c0c0100c40c258000d401180031030900028001d01c0207190b24009605198240a1111448104443c000001da80c0400c24281080c00080e0002d03071400e031401801c3c031001f000078446810980035085400c90381c080d0b070250b000844000148040c3e8407415500001c43c0c80948280d01d80200040e0403070283c1c0f00040d0280f50003482c11403901a1200da4607018040c0d1010b040c07103038a00003110f1780c1c1d66840f0480881c011b4580c1100058594486142d010599038401c01c0702c2c6060b5aa100c81041140c0501e02c070f00c030259221514002e40740c41c20f200d400c0c10903001c1c2400c16556812303c016801950b21007107002e901180d20401c14007a40c00048217035059108500e040300d0481d001030034140c0c0c041d020100003500501031400e0008041c140c00c4024146014a500d800b00324404c980820385044c00101c50f0b00e220030350701d000060140e2070300c0d41c8900c1e44000020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 434263911 1250 434262661 434262667
    0x1b0f030109080a2d020109020915100509030f1c0f08090c01050901050441030a110f1305010f050603010612050a270201020111070309120302070b0c07050108060d0f020904020105 78
    0x140d0f0504540d100400d1040151f550ba000e10005d40c24036020745603016012400b10000890200045103102c4480544035041180201b41c0a0307a0350f0f01400240340c1801100216a041074905441034240921014000003246281d401c0b40c031660301840c806803180b01030f030000c0c054420140300107640a9101501190420104000206001000c0045181d8010076044a115400309074a10303014421000e21545242051320940c4030070f640d60019004510a030700001d0315145e095030401050011210405141c1c0c80038182c508005540c0d03180d40305504803203e440d131900003295a0020b000c50f5110a01403080080c0742441a06402801e641040c1e421404c0c80700c0000d0204441c12500036480c0c03a040030300f083d280440303915206642e424050240820300722445079140400e06c7d170f4040c10840d428803500340e4598820388400e05040c000d0058200401c2d040301003070351310161800c0b403035262a0a80101e50200d20f0480105141e420600d2036072801c2c5501540c52808400d15408110510720014401c0341002810 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 434265161 1250 434263911 434263967
    0x14040b131e0201020c0a08060a1a04020c010b0414010b0d05070e0604060f02010c02060c090409080705031201061b020915150d0f23070f02010902031b0f030109080a 72
    0x1d006800074040701d07014100c510109440024101403141d01240e10412401e08103211004011030f14580005100a0008650862821102c1030014581c075942e4814400b181480c019a4190040e001290302101c00704101851038070380c0740408400b8011405c00184c01c0c42150350b00249948800c1e00412581010000c80c03c0f1400007a4950340580c01020000e0648202e42400c180c090145501c540d0050000e443c1520742003181410500034903014078030591303d880803481441841406c032480c03550000192640e540c11308032440f039454001c2c07041d4800141c0d800481d4484c0f500b41c00c0c09801c010350041225005866000405030804500721489601c100105c1000085400880081010a00a08010400c180382c0c1d1111002c5501c640b41c81c10320440e010003450040d0301c90701400c80c2d05c0322950801502d80e0b940740384100e0040c004c45800941510415641c0d41040e19446403041c44000300f01d4140310350391a0300d002c0c03609039800010020300610061144071409401140e08010b105a9016604c10700014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 434266411 1250 434265161 434265173
    0xc0b0c070504090c081c02030306010c02010512010b03190e031c2318010213050103050c070f1a06030a0506220203100506040c0c0816021203070605090d0314040b13 72
    0x5040e108131004a00444100308001040c01400a044060034000a810b807109001a40f207100003400b15040050107000001107a0040041c0e507c41507280340a1020f40da160000c09071168001c1c0d0700c3c41740307074007260b24181e2001405006e07414001010202940c00c08141c42864001c0c10ba42c8000304807003580350445114018201ca0ac1c180d01410745e000040004c0c14008000e013400d00441c5e494003402e074010003082c00c10462501c202e0003100d0080ca00083c2640c0c882207007c0443c003402074024180081d160003502800701c08041d0124456010f0745214443d141c1e00e00b0156a00400c28009019822640008928030080d20080c0722000901000520460180e400a81002c05044411003201c1e40c410a00c4498100343c81410492851414000c4040029450b01034a5000791056010341c0d68900300040c046403100219207004841d50b00450340c481c0610320b40000507050480380800c0f03174821012002891403203070051066038680b4034071030740c12500c1c1c0c0d03200d07002d800c0c500902e40820302e80c01601050024039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 434267661 1250 434266411 434266421
    0x30b0613020a031a0d021f0315060c11040605130e07050d0b0a1d030d0b01050409140910050c0403062004080f0c0901031a0703140726040c0b0c070504 66
    0x140c0d42c00201c201021402884511001c134001d8021a0914420001030703c400c1c1c800748840da100488603546500319a803c80c007407c000c01d030249080182c500001150b0fa00f00100c25145403040c0310182c0316000d41c0081c00300315101841125841010321000c02c4903a40a82d11890300d118541003529400754030340d8041060056081e804075503c203255070400001c05081e11443c2030104640180d40c070020704045500c1e41da40100540345d520b25a40d8183d18903240e0155040740c000380120300c0180f1440200100181c1c2c6000c0403940c181d0345000d080c600741000040c51082c10320549203440318a0500307055444140003031514040c206040c0c6408138640001100c10800b41c401048910010045044064050340c1800300c61103036030b40070749641c000510005a5003409540c82c0301c0201d44400300f07983da0f088114080d0a90103030103446188131509004410340d03c00030015a4125601007980e07910204030404030701b22404c607409000c50900e08001c3c0030b00c031644c200400010b51481e01302d9525940760780004007120 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 434268911 1250 434267661 434267677
    0x20310050c12090703030503071b150504060e010603020307090b060906030117070e061c0f140f010c1d061b030c0304090507050a0e0105090a0305010e060405150c04030b061302 77
    0x41d001068044400080c011815070104400e009071110500c1c50b0703070182040c00042c003004107100c3c4400c9202c20003c04070f80f1b0034108035040400b040782103101400030340003450207071010354006d410100110240329050041404895026004165503858103070081c00600d80303c03e40d40e50000e802c00651900c2d0f41c82e5409540684034895450148514100455140c1031603a404681c1c1d8403001c00400849513103104440300700041b03841c010308141e19545460301c6e8003039a010000307002003515602c0e0b45800e000094460f206c0301042008001a0076401c0085d2107030a41d0680c9903404a805040d243c00c14180b440281c002c1e071445104420718180c014203401c0c199000305540c0505a4400300b402c2150092034022640c118070142070180c0b8100380154001c10b154064421641400400101101c6580700da2030200000c581120007003069105e40302e162600e0b60010b50707054400744204080360140d00e03248800a070182e1500703601949080c1c5990341e03401048400a201551002603042c1000c0c04510b140010a100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 434270161 1250 434268911 434268931
    0x80c1e0c01020d06080d0905150c030a080708130c140609030f030d0b0402190311190c11060406051b0109080301060f110c0d020603040809030109080705070608130f02031005 76
    0x8442049205080700c0c1e130345e03102c1c1120760b100700c1901c0038881c1c20811910070340e17606603006044401c403200d0507442441114401f01880c400000c140301c4803603021861500a001940d64400d054a400300d480c1c0c1140d44950001e44055072102e81044454910b40d03840b010013102410303803030400d2107500020b420003550355405040c41d000021120200d691a210701856080126011410840f9058014928a84200d180707003d05a0fa251280c2a2f1440c060a41e000228500b908240c0d480e80200c0050104a0402c400c40b42e2444c0c3d154407081c0c5281030000d68040d10b4030790f6506402c0c0b56041086071030002002d807401c9003030f5584200201c00702e040180118040c1160384c0f56860150181c000007040d0703014400f001d40d12034204000c0c2c41119070310107042e00941d64040341d40d0f94690f10745040c0810f1520442200651561a060840040004410241c56a00d0144058440f2141d40d564150b40c0d02d031080318155140f007030402d1210b000035100d00c5089001c41c000740844410451600c1c00500701c40c01601c8403481 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 434271411 1250 434270161 434270167
    0x100507030207080303010b1206210c010224040f03090305010510050f030106060516030e031006150206090706050307111213080304030c06031131080607080c1e0c0102 73
    0x91540400001000380343c914001c52a56141104401c02d07401151150440c180403980031401c1a40c5403804010246182d0701c50460040400c280030395a84c0c0c3c8816402d0160044142000c0f441040075100881c02203005500c9007250303140c6d41d40030b86184508000310301784040d5140c0840440c000b440f43d18420b21b040050304001174100790401800400e8060414440c2c1c2c180300c82442481c0c1d012059030414000ca60707003a428141c0ca0305d02074407410101d08a603605441251560762402d00950091001c80d07840550784014105050002c070303202e00302255440c103154040041008403034400e0009551100b518030344100f51150070074155061000c0b80303c0350882000045102c99003030030108418070080002e60002e5240c01d1039660782c219400300d103219102c01e02d940c1d6900c01c20241001d10803250941c1080340c1b0f48a203081036070540081c0d0348004000c90000440aa8041107203240062554001c020503200c40308245c3d1103140005056014464803114800a02c200e10146400000500081201d80f030004d61 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 434272661 1250 434271411 434271413
    0x40501110111033d050a12121404090e070f1d0c072117011d01050603040317040506011d190e010612030804260703050c0309060409090b01152c100507 66
    0x11510040d0701f003014029003008114000408003c80703965407840900b4544129180b03049082d103c0e028a1313201342c00d507500f0f11000c89089400890f1040c01d640c804c22400c428292614031040317003d40f02c1100c0f140c8440890000c00c40c00e03000ca001074403440d48140001c40f1040004c2d11a410f010102600760808610004003803d8141c100c07040450240ca02c1c840c0c5203001040b03080c01030310107100600c200c038001e100020101e02818450a040d000450900ba882d0016003018548940d0740d440904c0780c9440c604110034191507903484ea01c1c0c124000c080140e43d0084000b01c041c0500003c02c8620034480342d41d0350300ca10000d0122525418840c40c103000c0c2d240c4045a01c0d041c04c256400968030b11401c000c00244144100900d0032040a80e001d06405182c02a1180800c03039a01d4510700c035075035003190300c17440c0898006090a000c2e0018101c0604c12003081c0c8469030380d5401c2c50110200d010104000c1081d04080f8001140120f1083d5070200b440106c6681400c20b8202003640100e10a090380005034000440300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 434273911 1250 434272661 434272669
    0x50609070602060709050103050c07061d1207030e04022803020c01050a0606090b030408040f0b18030105100b0906130915080f060138040501110111033d05 68
    0x7080300d0b00103000b40e80b4084100500480f01c5000e00c2d07062650340c6000c0780b9013400000c03e881090340e000508210300100240c1103044074007540110171040c842d00d0182c1540300e94480c242d508031541034998691881c8507004000194111619107500c05454081003884414500c805406940440d1001039690b040038030360b07500b9030318010903009509051460402c00ca9030300c0740c494801c41e903116030001e0302d0f510b40e031610365214400d543c440002044d82d040e001c90001c200320014059110304e4841c40c1c03e00e03100d06051500743d5400f207540081e4a103038060204040c0f100e0070300078040b0200003460b6a14081d070801c801480690300b07800c03440d03c2d5030340d4141c00840b0494841c1090003900300400100603910503021200d0b0303a80014042c04850040c0d003e0f4051180c1c44a0850010414102c4d00e500c0003420503405071030712501b080c8035036400103a00291121181c1810b108a2800f400c01012540c91a52500042d4200b07201e58404a003858802e044000c9a810368095120545440c00a0700b06400e89080300300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 434275161 1250 434273911 434273923
    0x1110301180203040203070626010e070801060c0b060405060303040b0d0605011106090c040c1704110a0b09030a1e12080609180309130b03030a08010e01060507020d0f0c12050609 78
    0x42107810303104200703000240c0d07400507101085909903e051a401546040710340121a002c2c80c2c5102c1003030380342001003401e07080c881c01a0b100d44003d40d1015801c1c0e907116030440742e401c107280d4098040440704011458608058000c264041d1000d811a4500313543c0340240f1486a102c070540b440320b2540da00c803d002070b60340070804c82000d001d804006d10300390800318103554071452000e040c68030880d40e0b40d105d445241c0c01101040590301000c1c0b850041031a150070811040071280c50008c1c40b03040804000b00b015a050016039802d000301500030038042a43d65100160400c1c0841040242c0080225035400540039601e481508881513541ca109410702400b07201000d40081c003c22010308003401d0a41e050800001529078030300048402e540c1e10345d5224041d6006000d00d0100c6a054000000d0706091660031040340c9048034540159040740c0d0307981d10700480742d5020b01d00e8029400416610790501047c9c110301d20b1100f9502070442546159500c170711014103012403400850717903500b154041002d0f1403828403403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 434276411 1250 434275161 434275199
    0x5010f0501170c0703090e0103030e03010b190302120f0303010605040f0605030610050d0b1e090615030c030c0c010c0f030b030a0c05150705012a1b1101020f01110301 73
    0x1c40c41c80e414011101584140c40140841c41403c40410038400741881104800014507145c41c0c81041545c481c10002c220180364a1a14082d6080c814100900c0c00d1901c4088803004011603003458032400d640c200300c40028203402d0610a032007038410030034410780c0500c0298003c228a445e89544c440c81c150b070703400301880103a01c00d00c18031005004121150b110703800d0100b100c2c1e1107868990b55031180c0310145001030000060541c1c10000209550005046131102d40c0c04400b070488e50030701d02d070355203004009480319000042945000d00340081040c114041d03003d035400c580040003035400e200795040d03030a00311440701c001000090075003031810138110342602c500c202c10003054020b03010344407281d250b1f80b40145a6200e010301035050090301040180e003003010307100a15440002071005d05c602c0004454507503400340c0b502c0030f00c0000c1c9107543c050a000352150720520188802c84101c4101e40d4480c4800a00c8400d509410b6000d042c09041d0300035402c0c8150103118480581d9580c0301d50408403440818044188 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 434277661 1250 434276411 434276417
    0x504020a0801090c050d020612010902090a050d0f080702030a050109390b090301090c0f032117040f020d030f0e1c080309070b040902120c07080307030b060408030a020105010f0501 79
    0x10710140450402c003104421744d02c046c0c411101000061001c0b0f02c19201d000040e05000d0202c00001c43c003002036800501da4203a040712004d13505034aa81c00c04c224258001c10007850490040d410394005a030300005068602c2c0003d040d07404441c00d540701c540c2940c9040e44210f5200401001d02e51103446014000c40c03903080140c2180d0014102c010009030900b0755070280c01c900c2c460115000041d95402d40010b8034041e80143d012401c41ea0718810480c000d02035001c00c07941101500b400c4034100c2c41c00c080c0301c0751900942d034a0042802e0000c060b1078074483c010f0000e661240f9281c0404d40942c9940308218001842955500801d02d0403080043c9251220b002d46031040310080d9081180300708203c60203660a8200740000d42d43c0e140e810905150040343d40c0b1040c0540e802040c006a24401e07a07003c3d000c1c032903a0039001ca80c10f82d14090310102500c11050020407440003840490143d51182d17121003000b48019150070310f00398590002900d1070308600050300060307440e080180f208207424031001004140a007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 434278911 1250 434277661 434277671
    0x13060f02010c0329060d110301140105191103041d0a050a0b03030403240504051501050d2f03010e0307050c100206220804060c0605070e060d020c0f010f0504020a0801 73
    0x4009a00060300c460400c2207113003140401034000f50785003411074207014444042046820f07404072080034503800905c117414100030403203181c42d1594001c408845203103c0146900081c0451204140c42030302c600c002e802a00c1c84240000300d9000c030410312040c0c0944003a11100c0315480c0001261080c4e0304000c11414145040030560030180e1070020548044e031340d0200f0308082c0c02e0700c1c203500940741c00120400080610301b002c080c030040c0800880c0400c4c40c0e200b01c90781d4400c9684c03110140000845071800041c102c00845143d0494101406820031050703040c2d204881c0003494000001c0d0a43c1d08171280328000e0f03040000d09904101007040300d02201c2c0f506680c128012503146c0006500d0f40380081844003261001091f61100503285889001503a601181241d29252200c40c02002c82d480f09400701c80d01031800300403d0740c0900072204820746243c0180308504e00104002948043d4000d951041c40c11300c550608003201000a000d040071611003c4800121450f0900400980300a5503002140c907900d0300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 434280161 1250 434278911 434278931
    0x60b0921031801050c0703080309101e0c03091b050f04050906062803080d05130507031b090608010207030e01051602040b010c050a0311070902040f1a13060f02010c03 73
    0x40103403081d0030400c02da0114030710030010041e902c40c443c2da45040620f01400340e001c01007090000142d0701540c5600d04480d0090284c0710a0b40444008520320b4200181d00c0442d210102d00607080300310407501c58a0007051185143d83c5d003130401c88448100b20a007030890792040c005400d003250f088410100c200c1e401e1215007480f618054952801509041c014117104042082410200307056140d045c2c17500047c445466946d0511403019044400e00202150030716002c00c130701c402414450780750280c01101a03e907052131507481950b00d800000c030140704c0d111075850004412840384540c10081a41078000350f9034468074900100f9101c14505003078180607050151400e880d032400030300c0d02031990517a8001200114040160f0341c2c0c82810300300502d184519805003041551206400f1440d6030050101e442e055126030003c0281d0080340a00e0180c500c603e80300704000ca213480264600d5a4020700458a0400031039002207407100580c010001050801c003400c08403d50900c242c1c010b40c8680c0c1380410083ea40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 434281411 1250 434280161 434280163
    0x27150902130f02070807060221010501021504060b0d030513120b01180902061809012106020d0e030a020d17190c0e040f0603020909010903020607180306060b0921 71
    0x802801c2107146681c0d60400c0c154080550304842201c1c1d007040e01a80c580360540741440295120618400765034580c801480003500070f100195069075416000b420000b0035a0f5030024a40d81c0003803040d50541c0e210042504a62a030170f580600c000e010740e40b410360742c56110503c4180f02ca07203035110030b5101180601000200d0803011046065070080510401d246407440700180143c2403030a006036024000003074034611448024201740514100f50340c054400ea985401c040d484c68030a41014a0075100e2611200001e00590b00820b1082c06a1100140329880105014607503003007040010301580c40300700c3c1c10564070703080300100341c52402501641c100303450101c2c0d0801400c09003584034091a9291008446158003d503015800018050406c012403c44400081d0191581e48800d90003808504086074840b113040c0078a214840d0107400410050302c81c400200c41e019050013408002c8059040301200203001406507400415203140e940e5150380c500c40405c2481d00c0c1000c43d0141c1c10452a00305107020324 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 434282661 1250 434281411 434281429
    0x1090315241a13120f05121c0605060f1605030d090c0806040302031603031d0318030105041109040f140c100509030d0807090b03040c03050c01050c06010b030a27150902 74
    0x5001d200c0403094090f8170f040008111560b100800c280190205c0301e50000d100e0001c2d09415070300c2c0c075468814003e0310060400b164503034080c0540191040111016410680004001c44913440108040080c1d807034541d0760a54001c0c01c103074100700341c543c14200107000550302c007000034001e4440609003030305090b50080e6482c031540c1c0ca0a407030f0007145d4055600b418040c0c1e00801c10100b600c04404190310600d0005901d0f640300b0500800ca0f251888400c1100b400c0520916201d1584940700400c480742c07120410030790160040048900d070420480c0800080c600e0228580070345a40401003000d1920b141c10010f0800014400c0010003000740000203c2c0d40d000650641c4200c407608241185031036491f0100c0d0003401e00e4001080ca00c000006100c10080714440e0031080344d000b901542d1113001008d004642a108070158000c281e4014070040c01a002004000d5401205100c0000f03141000c040c0840f6003400c0c0ca028030b0300c1185600074100148181c48880586040030404100a40007a560009420302 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 434283911 1250 434282661 434282669
    0x20306210a020112020906190305160509060306030a080706020a0914060304060b0a0b07050a020f090f040b070201230601020d030606140c011404050a06061401090315241a13 76
    0x14030a501c0c01071543c29034100c4c0e04010000c1c1c07c59644540042c401000c25142481650010b03140c440024031450508695480d40c5403242e80f0340746010080010062990005001c1c941e06020380302c0040f00140c5008000c2940c40c0c440c80001d0307100c5c141c00a02134402d80700d50b444100322490500740d001d1070356603441c100d039406580a000096031036130b07031000700c0c200c040b403504244055000012454144000000c030515068422155090032074040d03c10301003414420b64503181c0950100000ca00014072a8030407070340c00f90ba54400001d66038560034416a0701004122500000c00111080c049656414081c0400300c101c00e0400344032941c608440205618005884009024000720b014507c5c0311080d000b8440f88014000c0100c05402c090805070b0300c1d800c044a040b10070358500b4400040205220007030011403181610356a00c00c902e941c0f980005245070003484e0035200e6440c880c07010741d511a50b81d00c5240303542600d01c0d4100b490030626052403505c40f0070004d083c2c0e25801d00c0019034006c0302c0040715041d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 434285161 1250 434283911 434283917
    0xd0903110907120e070806011806140616031434050705010c0c08100b010801080c091b12090304090e060112020607240207110405040c0b03150306010306020306210a0201 74
    0x84032502c1102805e100941c4c100d8a0240541000081c808840004031210307221101030400c0010ba48024150203190481d9040e6080b50050212105281030303200c402e80d01501a0411150218240b000c4440c550b2001b5820902004250542881e0842c0f81c0030300c2000310300c0c00560585c100d1541d103881e40c0d81e501c244181030401c5120280c24040009400e08000240b0030a000c465400980369865030182082c880c20038001003042c40000b030700741c200003002159a5006801c02c1d50645400590341e4045a05080d0403521000401a0060081e80160218801c43d0044041d5448506120100013554410000201107500201c0188101e6a503284411003282c0d049440d5540e076425072a11012603d2400b0741003800344216030480280c2c50351500107100e0148164003404580318140c0400c0112042a80d02400517803080e2030502c50210084000c40c1c00ca014003060101200790440082d2425200b40c1044403d95000b2080c80301c1c9050655800c40000300500c050340c00001c4410310244c0d10a4030440180c10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 434286411 1250 434285161 434285171
    0x4150e01033602040f020a030b0d08030c3001030203010623040515090a2a051b0c04020c0109150204150305060406152106050a0b07140d090311090712 66
    0x290003036410302958030310b5000d8801c0c005c014018124a0094100e100c1e0b800c0841d0400f0301003146440c00d4140d80c0c0b4070b07130350002410741592a074050f18000cde0740043c100744100e00102503407034800480c02604884840d03190302c010056903056105050a5803000c0d0f00a4a01040000b000c40b41d410040a4501030000d007924002011742d1000101b0f40c6651426044076080b56004081c0131010341e440c5c0044200618001101c050745c004003401442d002510545031000500910010b100e02150019480b0000b501c081190705403024640020100da01901c5040340c0c50f95220441c20070460742d643c054803064803030070046003858070f0310102d64030030802001c012007019500e5001808581d6160710840c0604508520b114811041030b9010b4039510101111032480c030588503074890351019600030b8105441000d00810b02d02407411104006640008104030340c00f20385228035080001c002c0201055105035903603101555451414100c6815010301003240c081c00c4100b080140b1580c01042190410100c4200021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 434287661 1250 434286411 434286491
    0x30405060906090411120f04080904240b0d0609150e130b040804061701030c060c060221041a040201090e06061b010b010f08010f030b07090b04150e0103 67
    0x400e12550305070941c010305e0302c144600808000c0010b0202c40010000302e669988034a004001901e0040300c008107240401c10517605141025041104001743e01e10304c5581e03d14041c6455030140050740c2141078170a5005c01c89407220501da0203404000c08400034100460392501f20f080c080361032030b8041e03c00e000142c0c0703020440c2000c1c4401c400e040d40790001030440341c6050a20b0318454650251283c43d000602845600003a80702e136101307560413a83c3c0104034840080c50007005441e54400650240c540e07960a01c80a80c0301c0700e401a11184066429980311240c1c505443c01d4000582d80340f80410303210000508120050342c02000078802c1d035549100112040e5035580000340703288200415203412511405d00300120070415000410120003d0700e4004160102100c100c036031038404d1061b40a2104403c2c010400b042e0b11408454009855161030140c0d0380d00e03140c000e459075100d60301648210348045581c05070785511030f142a10645003444e0030f00c05548281c5a00c8032a4242c0e603d0007a000c2c0381418061 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 434288911 1250 434287661 434287669
    0xd052212110102030c0a0809130509100e0c03160609080f0706030b040e15040c05100e060a0207120506060907050406020d0f0302091e0a0b0306061b070b04090e0d020304080304050609 80
    0x19052405c42c20071503601094510304180d0a80010300c1990103003424040201421046028280c450f100c900002c3c0b1401540e041c41e00d01a00650590241500446d00c84103104d4400b80640e040207002c036a880464030f0b18200000700104c0042e801509950080305e0001d114031408143c00d0115002c0340b80c04909101c5080004008146c440541c503424802c607030300c2008803407405088074401c43c050790803140003d80d540305204107090002e100d43d001982c04090f042d545d1800034090321424500744103c1310015101e450060003001c02c0c2d201a9240d43c08481000f419103000500c55911181c6403405904042c030f2b01201a5460700003047d03020502680101550425210b50305840300d420008041070380e049400320120058500d02d100b494050907a10101240800142040301e00400014091900d000d400c00c0f0001e882c0034403900c0c44503050143d4076002070035100840182000e4050104000313410742e08209000c0c0307400b07090003100055400030300c0204075002000c0140c0d070407100c5c141c62050395030749182c00003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 434290161 1250 434288911 434288917
    0x4030c0c05060c0606030c03010e070b0d02040b03040b0910020a080705070f0503030115020c03120f1c0f050f0703050f1609050a0603020415020102071112010207050d05221211010203 80
    0x1034001d40085181c40d500030340010b113a40100401c0d4262244842110141403d0352405080400c4a50141b4001c01c044003990004102100780d0311070050809032140c1d0040c1003a40305490070385001c0003020a02c00179240501c010384105101e603000b10702c1c4c01e28414015003664001000f490900c40085440c105028004107060b4100da070020a403640c940e11410080d10f6030101505460051082c0305c01c00358541000203d80101500c180b9007182014034407a03054005520214401c4c503100ea0040340102c0c003020318020400d20400192000c105881c0043d246c0d80c603044001d00303403c00c2604003c240903000821580842d040746501c1c100000c440c8503c001a40c112455501464005014a600107550740d0306902a0050311090280e903110404090012403c0c0c0c043c5c020068212000c0ba0003140003882d251040142c0c880e0000005420300b1140e4961600b080e03290401007002c1440091201d8101400030403042e81d100c4158400380449042c85813002c010b01d0f42050040c00246015128901c5a0081042d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 434291411 1250 434290161 434290169
    0x90201050702032a03030c03031302130f050a050c03070f0302030604090b16031b08010b0a110d0306140103091a040501060509180106060903050307060c09090221090c0904030c0c 78
    0x2c5544000b8031000c03030036901c0103024141042030102801c03181149000320447d034806503940003d50450704c0c8c42d62031804118507480101c0c2d0240c00c00b000c00b0302880145c0200703941c0d415400740004503071501b420040183c4e040100010072681041041280054014a480482c0302241c40c0c010b84070b9489030007041c0105807040d0040c00c03101c141000c000030410032805c401440501c7c0c0da8140310103c42004944a841d106003086408603030b00800600c00d90204a01805041099241888500d4010f0004d981480c8041c044500020307260701e01407145000304206007641c22828a020090b42c1c4a584031180740b130310200c401c2128150a040031a091040075000b001c0a400f00605443c0306040c488101440c1918008403403081d03500b80440080e8141c00f0b000003004407604100a0342c9001b421707a644900070400c3c00c0c03001043c40b25092001c07441d181c45202400924440c41006102c0c00d11181e80801d50000003024840658030482006405883e0345d0540b0340c204d41d143c00c1c1079005400c1880c0c209460901c0d600 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 434292661 1250 434291411 434291413
    0x30203030412030221090c06090d0f03031d01091b0b0d0207020a050604170601052e0207080102040f0810020304020f060f0c2b0804050d1409040c030204030c14090103020409020105070203 82
    0x841c02d4400001c0c45c1900e0301070344503001169018900c0300c061040c0b0340110080c01c1e5100c0f50030a64080031030301c0c030658080050300ca8940000c1c0001000282801d944140c2060a441d80d9101c40e110204130038070780c0d003074964030240e5104481c80e442c003c4e132030031648600c030b0394281c54540100d03a001c21911040c003c0006030000030072080d00c480e00d4200c100c5503003841e03080c4150940b0030700000050905140e081e540040401c032003e420388402686030601640120ba150104500c07480500082c410001e20152001d440002c00c406442440c0a046524180c0700403151001c051040040c0001a50348050549a420f403d4802548910300e91800311072600034000c0300002801040c1c80c00d8a22400307031040d0110010450048400c0c0c2480030030032641e40104940007403803613102e090700d540b165001e40a07040a40c000c002c40355145c18554008102a07803074101d030980100303030089030034010030850b40403010141c11403425002e400048040001c40d400010311010b03002e150b0701c40b0160203592142044407502500a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 434293911 1250 434292661 434292697
    0xa030902060703050319110315010c020d0506062d1c06061202270711010617070e06030a03170a02070f0c0e07050702060712020309151909030302030304120302 70
    0xc01d01a08175881264800c0040c0c1d1120703103001d0740700c5440c454000194082c80f0360070f0450780c6480101c400049401c010a0600011501c4000107994503481e100c0f44078031450140040e42040414403081b00b0090601c03458490140d1040002d04d088440c96600f0782e0000c807482004801100e165404501d020080901102d0034400b0104070046606050300741c1d00c0c801e40f03100d642510440341215000c0100400c58a40300500d0300440c0c0c2c031921401c80841054520000015090364400180c5411002924111034642125034100041c074910301c03201e07500c080e00364003803c4401e0190394000e1400d00c40c902e140d103441d0091008680c1744000c684c10748501d0f130b6200001060242c1103083c40c51080110b4440c4400c1e105003c2d0010340c200340704009a80f4003c0d800f13401c203400c00400303545400007291882c90101c110705c03081c405a50645d49500780700c1c640307802d0080110307a640014000704a20004c044e5071202800801c100400000354008202d0f507000e504060180e101144030340d07084019100303d0356415401c2841d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 434295161 1250 434293911 434293913
    0x120d0201020c0c040c080402040b1f12050a0c0507060e1903030b09070201020a0923061605010e0c0904061d1b0315010807052205011409240103020a0309020607 70
    0x55005102c121596000c50b100e40b41c50b0030412058039a5131034554000740d00007012900608150300240b00d070b15402002811900c0e212440c0c040210703036000c540380c002500100c0a01d0405128881cbc1c980018540209120014843c00c000d0500c2c0f040500081c10f0540d28540c99034941c00030b0000c00f80c109000540c0d05134841a80c10000c010b098030303800240c4119085000702e10006e00501c01c0f20042c0d5180c0e145c0880303c1d403403c8141800c09a50803d9060030000c40303040d40f141992040006d100c5211203a92103640c081ca281801421034a00040118170381e4007800b002010b550715031040c240c3c4150f06c41000b20724000541c0015040c13104c080d072540b00c280b0401c0c0988694180c85186105007840a408950104581e01c9003803840e00401c3c8503c1c142038106600038011403c3c040c40c241008640318100300074110482c9001c4c41242c809074010b0004481a8100700380ea81f4100713242d107801081c082040031100407459520202d039500c41c44102d05141e4005200340c1c005000b6005038a8454000380090703211170803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 434296411 1250 434295161 434295163
    0x2060a0201140f0f0f01060813110d031106180a0f14060c1c06120305030c16060b130911040e100906020d110f070b060a0e040302071509050d0b06120d02 67
    0x1615884524131504001980c10811102000d04076421a643c5001e540c98651080407041d0103a241551050302150f44103003151541014404030521176a9020a883c103904407240c202030300034008410b00c0d0440402900102400181c032101a500034050550700e8966103803020700198080d19000c0907006034020018580c15400142c1792042c6800320842001e4081924070301103d080740240a40a8400c501d1500401d20176006140c0c441c5445200038075000381c00c0b041d14075400d02d000c42107906c217884401d200d4103070820b0040709079000032015062044642c8c581e00c002e080018421418043d5542d41005400c01004009446070707a11034040400c00c2c02464202000a0f51040c2c88560f01c40f402d1000b00c603000d0342883e007102e0040303800c511b0450a191495403400c2c4642409031030b1540c0000c0d80480400d1090000d0b0501d4000c3d8425001445540d1900c0400003000600d040d02c04240300059104008a4840410444140b81d000d00103005a65035800050100035189400d200240704045501c184290 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 434297661 1250 434296411 434296441
    0xd0216060e100f0903050d0c180803090a0906051e0102120c03210c1c020405060f0910030509030d050405010f0204030c030b061e01120902130606030608030c0303010302060a020114 79
    0x1400032001d0125943c00b5800d403054450751440100018030400030170032021181c1c0d0100e010103103540f0f00104801e0316030310041c811203413a4022038401d030000100e10b0100d140440c1080010304c110310040c000c0514250008010240c001c15100d801c0b1100c5500d142c3c00e0b8400c1c8500200c4480d00036106448100d0b0f10b101d01d0356a0007210940803212200308140100b076680d80c00842c031460314101c1e048e281514114105181e03c201c2c0c034038000e805030203210200390750f03449401804d8048420640355031910a0402004550040d402d0040c051624044c02e105803000040300316070807601c0710701c0e01052545807850440c2c018074a030440451024030126001c02000500315580d82164021112111350361154030070059010b0164400c113000d8481000007052135401a8828000f0009074117002030030700c1c2d40360042088011402c5900c01c545544400900c00c40e5014400c40000d80703611402103040c111461545542da10043c04068071510340462080d4101b0306c00d40160314081031480911b10903052038421085150 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 434298911 1250 434297661 434297683
    0x314151509100e191803030509010f0b1c05070f150206011703031512070933030602070206190906030506040b030a03050a0507060203010b0901021509030d0216060e 72
    0x41e0740032001c00c0a114441c0c0120090354020212041c0702e444084c104591590181010700c04251600c0c00101c03015071452518540340e0103a10003103064075045203201d0858003d0300c06180400d14249441025465400400e560303c0b034411404042240241803103440d241480d031101c1100395800d01d000c10750420b40340c611007003181035030225510703640c944000c0c0460001d0520343c180e1030350003400004c490b80b03001e4040e6490001e001d00300e0384156400c001040d06054140c2c12502489483e0312038070726821910911000e08400102c61a020700e00301744140703251004144000303417203642c02180940542d921801210340e00e0844501c0072500d031001d0b501c040c000055500c14200424030700300026070207040a00520f001c1c1480103020b009902c0b02c50790b094440780c100450800820100f48032032400101c0038030040d400fa04909150366180d1014130002407506ea00f81000140307203103d60081c002101c0c400002c1d101d141e0501c0b0000f6844091231009442c281c041100040c00301410722900c1c01407020045803002c1d0301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 434300161 1250 434298911 434298919
    0xf0702340b07060506010c08090d0201110102030708160e03030712020c03030d0501090b04051611010b0607051c05040f231e012a020105030a0b09040803091b010903141515 75
    0x541c5e4079001991030554542c1d02410544040080000d00c1c54801003000e149841414003801d6410fa84c0c8140b070032a001185c103000424540024042e404082e443d034060214a40e2800e620503c64910120340c881c0034100d03009280e2590fa44104500390300034442040c521002904581e168903c120580016007001e02c034400b06c2c40e00d0200c0d08030190500740243c030301c514503a5420740c0311140d1013281101c201d0060b017030113011956036030740c0c191255450400510740d0364020b03801007003040c81000c0700f00ca08801112a0100b032140400c020001012410b0351003086800c80c2803e4204c030b8001c90114a14848055200c6601200010b4481c411a40c042c52003d24010283d985907150210352134100221124004403143c410000c0f081071005600c100700031341e844013804c42c3c08120031807150045076048000361802c64034441c01004000c0e201c0001c00007140d2400c0044014614401d10708000b034500700c4d0500026194041034443c00c040d00c40f080101c01001214400d0101d61490b106400905c1c0708504081c0383e00c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 434301411 1250 434300161 434300171
    0x50d020a0b060a06050403020d02010309060203011715040f0f0f05070324090b01140d02040501080a03080a0b0a1a1309020901030b0102060903030718030b0f0604050f0702340b0706 79
    0x2443c240348212005582c0a43c603541e2810741503800300110402032400490415840d5856040002d0260001c3c6000303100740924007c500784113550060a040c860000c0500000e400d50421010602180404100f00e810140240c074511141c185081c21041c42000a0710710300c00c214000013040300300031880750400105101d01d030f0b0940342c94415805541c5166000f5101c6401000140303c0b02200d03010001c000c0d81b004004507a442c5086e8041001d0b41c200340d11208030750300f1000c1050203043c5c106214548c40f281c00e0b002000300e0342902d00000c0c80120540910154001901c214080022410003141d5091614400a50443c1d554100e4a070186d8458510203000078208040384145500029a407070003000840040c41c195a80c8503c00c43e01d1500c111a00c0e0380404903101d000000c1241c072008580504034884120102d071402c8000c0c401910720150007440d4075603900f01009038003940450704c001042c0155403c1c2d405108064004041000424107413901711400c10000602120300070000c0c40e10b00c1c82110103000e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 434302661 1250 434301411 434301421
    0x1104050c1c0e031e090f0a0807030f030e03030d05040314070803130203030405060a0201050709120f0b0c0c01110c0615011407020409080313020406080c030c1903050d020a0b 76
    0x16240104030300003511001c6151040e2400103560040c0748041d61040450b801c08051809a07140c581c0c40c1e2138031307821110700000c804c01c081c10b0444c40086c0c602c1c425501104a245024002591024203100c040c050400294020703040601c00d11031a07602c2900102245e4907498801601d400402007690200c021070410346c0320008143c60102642c040c160070550043c00d40c1d40c0c40400c10025541e01d102203074540805c00c030115103996400d02a250100035540005002d241105d00581b206071550005640030a450300c0003000078140030000c00c0c10315030050305910962240e036200c001c20b000c2e100d0302041f15400c0500401d80100d0810141c1b9a480049040faa0030361602281c5d1902011964440c40c0060b15009040700700340c074044c0c01043c0b101c5c406030000420b4281a101c01010750403c0e1100554041020b9503042035103424002c2501904041e00a00030607100840000d07603420038400d100e40034101d80e54115036103003903030001c20f0011a0810251307001d0840308400292560000034044a08800d5030000c58 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 434303911 1250 434302661 434302681
    0x40f06021803100b100e0a03020301060807060e01031424030729030919051f0509011406092d090a05070f0614031f0303020c01020d030b090606071e110405 68
    0x7403c2d60101400c6035440b02031741d000444052088510301030300640407000010058400340708410041510101420290b070804000400a20090b0380243c100350808000150508420141c0e68101d905000b5050356080b100399006042a4000c2c0103030f5040c0600040012415001c0501c400c4400c005103440c01001040380442d0340f28002034038001c0040d40808445016190700349101000300e8000d204403002450100d0040b040d03454544071391140720340c44405002202900b4010381904100c0030405801520303044c0080784e408a4000c0200c0c902840c600b0781401c1c4031a075030941d405d01035413400015407a0310303003200c0300f60b81d90040d10b9040b6481d00c46c029000036180c0d4070409000544103990b4550241500c030201c40da6141c3c202602c0140290313000c2c60103082c041039046203c2e004600c02d40140c8610224000064145801e01a1038000c2c1814a0003910701ca60f00c40030a950b110a00322001c80e110f9000d400d0550030845588900b0904202c501e0740b04090054010900e83c010108440510030390b03030342009403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 434305161 1250 434303911 434303921
    0x40f020c1e0c0f13020a0c030e01030e0c090c0d15031703010305030a0503221101020601080c0307050d030c02100302030a06210209250305040c0b190503040f0602180310 74
    0x20062981100c2e0740091503141021001e802910020103c8052203c01c100c81d2080342d2115000d0300104242c1d0480c40c1c10190002c003080c50104013404c00300440c0b0400c110326a01c0d008174220883c0300d00b100c040024204003d00080d02c00e502c103141c10400202d405075507030700c00302109400b00341c40d18054035040401800003602184c0c10703071354808055824681c06501c15034003500701801940e05000348950302e00205c044940a408201d0052005001c140303480070000e070400e101070300804103c0e00224098003007620f0002d050b004541c016613107180035070014102201d08100701ca10095204814009817482941e00d0b801650044142000411485503038001d9001c40c05103c000720b0040d00080c1150402529001090390380c0315080011000c0c401d0204414202c2c1444000300360000b00350344070b01b48428440301d10440b4001c0d02c0605032040c40c210201001d403801c401000c901c4400c0110004c0003404000c100c134454010316a000d001913490b01d214000c205c0e803107000381010b40d0080c0305155115050030100c0c015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 434306411 1250 434305161 434305213
    0x605060c0a0318051503060906060a21060e0702072409030b27010905070e010e130512070f060c090f120309080f0303040b0903040e0a1a040f020c 64
    0x14010001a40d40964291458681000e507030f6416110016294441a034a41e03011000f10540941d2482c2c0700017000b20101d0064100f0380512000c1c4512107030103421007403c000b28903001c0d0030070704844078143c0c6030006824030307811541e802000d041c240301c200e40d0000f03010030030380d090080d049610a000082c50280f45407091000000101d990a0400216940c0c1d03a14640102d0004680e054000803007241da0005918402c000115070b64a4030020203020f801e02c20300c0003a0188181464095140031750004200350068090309102500780742070f408104081080310064184020481e4507017040c0d05181c421060000810b8640ca0b050207142d000d07041c8502d00035415102c152006211a80c00c111114180b00f1142508800f8814600d0700412002d00411040c010100031100540e600d1a003031414400034040500250345650003031209201c0c41c103c42070350a62003882d0031400a81c00c44140c403200d01c00c0308070407030640d0481c0c5440c503078a51422190b0028900d5840d82c80c03c03200e100512114041e031003551042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 434307661 1250 434306411 434306413
    0x519051005011b1407061403091509031308030d06060e030703080c0a0b190605090903030403081b03040b01080607022a0307051509150a02100c1e0e040605060c 70
    0x201480309600030494180e5a5101421403c40b030816039855003a04e4414400500722039200a030200541d6500c2250782e503928546500580c114209001030603079951900000110400d9044006201c00300f081041c0c0303a000071901c81040e5055030f68040181c4941c000040d146e82103080c8040800c0c0e00c0d0188440140504010b4010011180340d501c0d101c81076002504a0000d60103207143c080041545064040c1c0180d1090347c0300907484511242da202200c0303031540040c0c0244203100420120700300c08802d80340e00c2a0141010079280ea03481c2c0e044035a0349141910100d10100220501c81400000c260711810784071b06004541d9991154537080e6a1400304444c82d826440801001c0c0b90800045488180c07030120140032551843d81318000284082c0000c1e140241c4400041001c1c859841d15079000d420b124200d03c0b5040c0303058000385009444400309056141d6190325208001d0810b0b1044071550501148058401c1c91601080d5000345481ca441c040c00b403080742000c0010070365103096401c0fa403007148480 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 434308911 1250 434307661 434307691
    0x302041116150515030a2415051002070e0a05090313090e0c011b1401060905010b2205010507020d020a0302100504051f080f070c020a0b071b0b0d021615051905 70
    0x552504984c0d00c200000b42c0e50100383d5454000760300c4423030140366980400c84100003445406c290520036403d01d42d440c00d0086502c00002000b424000e03000c119040301a03054081941d998130004149140300f40c5a0140400c0700303401c0009405881a400781001040c240c059031102d50310741004544200c0c54118055a040c00209140c5c009000d0402c4800ba642d0800004100199104c225608494090744254102100080c01205594001c4014803407204400d8106503000e0074480020040d01a00100074004c025465001c820355503072291080013140d00030011070101180c80390042154000f071043c240907840710b01c0f0b8120400d00c807100c60b041c02400d56803149401c1d91521140340450b0340c0900b1a030140000c500e12a009600d07940b13008800341000c1c4044a960b00454600b107030303410488090081c004690b201050008012400840f01c1c8540d0f000381c0980c0f901c0d10510760600b81c5614403001888664444a14014883d554222034840e000515011140700040034043c0150303242290346544500c542 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 434310161 1250 434308911 434308913
    0x90718020c011d0c0a0905070f0e040b03010f020d0e0601080d03151707030c051f0e04020d051f080a030507030c03122a020102130302041116150515030a 67
    0x6902800700751503200000705007440303545841c0d120740c10024203595550300201c5024034039060a0a9920051074250010441031620200003000340280190700c03010442050319a4a081d903c0ba00300808640300203000b00464a07643c00344900941c0001d415103006070501010a400b48804a1f45a040703c03032000281c005014585811402002c1441c000405d0420344d50010901c0140c1c4019500f90741980b00003405642d0850603e0030f0017901d15841075105018410040401100240c00103582c04120300b46076100ca981e00002a02a000e036802a02000d4501000c009090302282440d1a2400c801e80c9030381c00c425101d00d90f003610340362100f0010f40411003c01c04040000d00c03074152007040d6802460f2154548000d0004501903a01314803407080002c10103203045a1080e072407845000705040900003107150035080143c0152010040c400a88119901c54a0101103003000048840405181903005848103092030089202c118104a4045540c42e20b8001106042d91004032614144014010803205040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 434311411 1250 434310161 434310209
    0x2060304060e030714071401270801091a0c040e0c09040609090503030f010609050a231210150f031101020a02030d030b03060a051006050c0c1c0201080907 68
    0xe0000c80741a50389a200e80000b0310b09001030044107210b140380f403110b2040c140745d0030701d46503082d01b0404408141d07521120041c1e81041c0f06210303500358943c11201081c0d0f002c1d58541c02c641213500003519542441d41d120108880380107409001100c085039817560303840300b150915030b5002d107008680035601034002094040b64504003504101100510115080c0c0e103c07020300301600c0304088125400e81c00070082c8100c0e1412940c000d8090800392502ea00c5c0c00e8035200000c1e442046520842c46ca0a40d021400700144410301044001594040c02130781c240c00c02d42e020240e98403010302c2d02c00c0c0c0c440e01d40551442c40c8840201614110348040f00d40040362411611080c1e0840b0b42090b4181c19440380c1500540141c8060120068050081e1400a00102c8640903d801c0610080c51f80340300760301d800c0030042d481201c0c90104040c2d405929045440b80304160407035140000c52000d1a50100d2444036580c0350082000350744160078805c1e038410519441c1c9001190b510320b80e9010f443c0170008540c03c49021545 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 434312661 1250 434311411 434311417
    0xf060620060c16081606020c0c1e040e07050a0b03041506060203250c0b030709050103090c15050d020d0501091109010f03050c0913050703050c070506011214010c0c0c0f120206 77
    0x1004881d65171070301d652050182c02000402c10120b0b0203d030049030340c081800c414403412110400a95864240c0142c03001c10f040620818002103109650311240300280840400004028000c05030480c1ca900f500c0c2c141e885400d03001290100d17071501c2140c80117074040602d40180c0d82100c00c590000c42c04c01544c052020210303c034007050380c141802d01e0359040303002c200324104660003000341450701c1d0350345d062040c070040200715150001414103052008003000900407080c01012100c64000310951004e04030802c8509214a810b04134240740089411041a91250b0001d0304845012008002c4800d0f1580d41030464001e10789420301040410b94009030b818000c0e084242e003c8405d0b9540362604142c4030010308501080c1e090090684d07500c100300561160984a420f40290300018500c0c1043d141342c0d50199601014060001e00d81c03840c560017000c02802d40403541da00031085d0002e02ca0a82c0d0030340b000b008045180e9050301c7c2800c10031400035281c154450690140c42255001d04140003140c1c0038015964 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 434313911 1250 434312661 434312663
    0x110a020409031e0c020102060a0b01050706050402030c03030c0705100f051822050402090106030b13021e0c0115060807090e090c060a0207061d10120f060620060c16 72
    0x12810031003000c1c000018100b41d010f5030041e10340020a045a000091034600000d0142150528126411421340c0e00b1205a41035140d000b88007051a45e600d00c0868180300031440c09a8251102142110340c6100104400040d6141582d840018801c0b41341c040301c00c25144085080416420020a001c8043c0e07100c280406040c06010311000350480215851000203d11080d89016560014081146410b040350360042c1003e280501004843d0303000100c000381c201c1c113034800a40e40020040c03a80e007074200000410110904c2030b15150f04024010a02030400f08000140707209c410b110118006010740c410b1801010b0b03580e10b508910742010081d800002d000b40501003113203c0c00107411510f64400300184504040ba41c007601d0440d03d1301d480601940055072b2855000d40003504801d070b01c0d4a694100c882e164031f5501d41082a50b201c888040000d08561220329444c50401174042491a0000b040fa803012080034600300310848a04072640d140d47d0301740c5180003004010040e08554024042010100d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 434315161 1250 434313911 434313917
    0x204060e010503100e090d1e1413091404030e09040b4308070318020906060904050a0b1c0b01031115030f041a15041509140412110a02040903 62
    0x6035200c040c170212a04048894404a5100781c01140695500c034014902c60400861030300008140c03607078090000c0d8080d409140c5c0c2400c2c0802d030030301051078504010380100070900c01000040c8200d000060040c404440c00e070080b9061040700303c0c1f82d003010700003d071050341c000f5119416a11519555002584201240b80680d04000b42d60010010011060301103407188041800084412200290100b140240800c05241c607005400b000e034205441c1e00c44865070304842c51102d5694440004585000c2c0113202038009150070f08000f0440d00951105080d44011500f00300c081c8000940c1c0183c90640c840d00034201604c11004100151801c0207145403a00001c08211445250311070300c2c2141d0700b0840d1240b980d03140c1c1600380420310080301c40c402d00714007000354004042d24220303104101c004204d10042e030046591740f100700c0e40c2d080402e0003100580095001441001c5c0c01d110a001c44010654041d21044080b48a4500c90740c018003041010b0740080b4080c00c080325068081000801e071a030429418 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 434316411 1250 434315161 434315191
    0x2030601031d0309120712030e01051b010c0806120a140102090d0c141f0f030609060306060509060418030e030c0405090f0d05160f02150f04180204060e010503 70
    0x4080e41d920304803071400303020314020f41d1964840300402190040c0034400300015000201c0a010b002800480030710381c603405007801c40d2540000d0300100c80038429041e050119208110700100b101c5019002600c0d06c4c20642d442c030a80703458440030092250185030000e401d0303a2094600c2c800142e00300010003140070000d8001801c0200d010301240b0700004010f000c42c1e041c82c4064091107200000640c000540d42c0075110043c80b40c05001288100402120011003840300980c80d80680e14400e0300301a0141c1044074040c0802562450000054103583c0103844c4100300c3d400004d903a6007890700c01c81c40165144003c01c0b001c0f030565141601c48200800c103645d01030044956003034054555001d001c0c000d0595400a0a524440c070b80e030740382050740c3c85148008001003008410380c004082010070044e030b500102400390982d07281c800180d1800004281070442c1070046410002034114402400031202402a009810103200080ca4202e00c81c9004501c082100402e400b050f651050000d503512000745440703525 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 434317661 1250 434316411 434316431
    0x260f030307090315200a08092a130e030a031a060f031b040f03150b01080c0d0906111905091804050f06040605060a0e010f03020103020307050f04080a0606270203060103 74
    0x1820070303170303840c0700010000000400c40d00082c4d00c95906548400034501400c0c41c3c900340c0c0071880300340c41480302c2c00ba43c01645a04c0700c0e44a0350384800503540800280ca04002250710010b480b0344031740010354101c001c41c1ca40101442c041c00803051400d00090001c0c03605103000d904403100302c4190400750000ca0404120110321407004070540c010701c09041503034400c02d200c501d1490041400380082251003c45c0b03080881401240c0d8201d02c0e140c0e000300307420243c2030700c0d8000000010000c5c071208601074905410009040400421b00000708030782c0101042d40b40c03801c0d401040985062003002074403904104000310740300780340c0c01d003c80341504a4410390903a458480385801c0c007403400c0340986040d10020f5680342032090381d103040514500102605090710500750324001c0d01140c4540a4800071741415000800996030502c21804c8411401d181b03200b090b00d440c0c5030300c1555500c41c00d07110104c0300c0c00e00c6d204011840d2113a400d61080038030071080e29408005804440c1101941028160f0f0341459210b12a00c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 434318911 1250 434317661 434317691
    0x509190203031209030d022206051e0a02010e1b010801061706063a1a0117090a0210020609070b1c0e030c01180b06010311070f0c260f030307090315 65
    0x2003c0303411441207108c540c0410072180780507a40741d01c00300c14080d00304020240640190040107011850841560b124001010268054180d400701407206000c1c4542d5142c4614541e11004c00011003aa00c01000d030b03880d000150342c811030007800b00d42418400000602ea03468010014166030840a880c964081c2c0240045002d13400c408079040d0b4652408011540c100b01c6900ca00f03100b04075000d4803240124003030000641101c4e1042c0e81140c021078907200003588460200468105030f6130181c201000c9a40005000703465160584240c0c134a40110080000c00ca0300c0e000680d03000310110074078900f26a071207503440780041101c0e0040e070402c2d000510120210290078442d4009000f010500d0341e203807900038600b107034881e83c0081440d810f0604d050780100114002000307640c581507120180e40c005481c5800c000820800030341c40303944000528039840300815000c04c541080703011502c048a03444d41520505603142d0004030340280000d8140c0000700041101400f00d5141807600e040d0000352620707003c1ca41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 434320161 1250 434318911 434318917
    0x190b060f0708030603250506090a080a0b09060916050910030501051003030e0a0605070312090f2d1104020d0216030323010e191b030509190203031209030d02 69
    0x94807510030201c100001c0341400d0000c0407080c1002420b0254031b040c1d50b5144030040d403007801454001c00300407a400303100391984626800645819400c9412801940c81e2050510004403000403450041e8008070300b0510b40082e0355020b1400e206101003555091006000c0b51203001441c075064540c0d40c010000c0810000c2c42400d01400209801c118070f03606500b005444040e845541e80c0c040c203421201044016884000c2d56241d80d4180307810440d48a0300f0103c00051315407039070003070045511142c15904102c0682d170400d901c0d0308140058680c40208000c2000b00d2002148050410b8081205214142c90a540100a00d0000d0f01d030060038070f0000501d2403101e44181d602140401d540e4610100c0c151480108007443e1440279044038a00d6060540303070444100d001d40302e607494400f0000502d506520a4102c002d040c2c1c0220072250100001c800c00602800f0140d0b80300000d402848441c40c5411000080c2d0401141c01038000c500d8601d4803c0303e00c1da1810014040320103808103100d040e1007642c140c001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 434321411 1250 434320161 434320163
    0x120209100f0e0a290f030a0902270f10030b01080a020405091f09060e03180f060a020309130612140d0903120305060f1201050103110306190b060f07 65
    0x51a003030044009000d0702445400020710f00c1600001000c0114902e0000c403050785074461484a00224138102401c80c0d2400f40c2060503042d07a00100070485a0400741d401043d656008640d12050440d804608115810701c0344003080b035581c1285c000441005414035015040005280488451a52a21200d4001c0c400b82c0055196070024680301d019803500e4000c43d03400401c01030284c041e200804170240711154450086070b40e455120040c95052002a038400107920b030440381640d64956201d90307040d64000101d038020b44100b507200b0a175243c1c1d003030107400d68482402c25002545065040410800c85400c11810780e00440e480d03100100d1602030102c1d58142061140a41c4c2442c02e8404544904040140c0700c040c0400c84107007801c001080040d034500d07081c0106810700081d691140ca02040e82500e2403030210b90000710320311190118000560203941240d02601401c10401d41c1070f070415495003804d072001240d0791b00018104005980c184c1c44200350309401000c061a00640c0450141c03680c00c5404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 434322661 1250 434321411 434321417
    0x50711120a05150c0a08040f03031b050c100c09120f240e0a170a030605040e07030c0b07020117101505030601080912030a11090d050105010f0f080d12020910 69
    0x401c844100350f8515259411400e00e4450301d00304081d5a20003000c810008001600600101c01000300307060007940005580c0f1100004040b035014000c402900c1a03001a244c2c020038032442048601e4040d0034424a901d91449644481150b0320304112800c0750401c0c030509880d000244045040011184806000c510420340010401c610341503c504e0308840700c4812828807500002440300016103107007445440602450b00c095268a03d0340c03412801003040d5000b642c0c000d440d0100b006216003001882200b141d2145a4040700d043e2241e0441189028500d4000c0c045080c0d0b11030720154140c40c4003d20740c44410075014400b210755600c803071056500c0300d10b84480820000000c0c000f05503070090303040354803a02000062400b00301001c2c25a64a1200401030388016a03509540340101010b54200c3e21450001016120f1208035420118020301081c803840140c007244580003d030011403100003104030340d8020041c003050744560070285d810400c0e000c1d1425409034200803c064036038880b000c0084200c5c01d030b5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 434323911 1250 434322661 434322673
    0xc060e0114101202180c07020307141509060313020303070611070c1d040201032301082b09120609140c0a0b0f030a0b0102120403030e030c0a06050711120a05 69
    0x2c0300700e42c080c40b58101d040300000c100603050260700c550a10f403c04601003a0607030a26502c03410242103500a4040081d814080d0800001c0c40700c6880d5124000d0b4101111100d5030200380b50f207140d0f070920840b110300e0380000d0140009403c0d803070010701901a031800501541d150460326a82c402c00c0303900040d150141c0c1d00010a120302030148900b4500003600811014940b4071030340b01ca0b440707401140104000c0c10103499520711213505c12001440c6440808586000c0038075619815070944804030000c80c0502440902a1901c12181c09513a030b81641c50a070b00c0b04016141042664150030341694401d60701d090b12403442c1c00015220407802042e88092401a001100c0d50b041086050071156000214200f018004900d000d2502e070200d0b03400a07001c1c480003c00e018803c0060741803081c41100460400c00208001081c5500202c00048a00084064410800620040103145100d80c040c8200050702440f01c1c20020792445c0c3c01c900d171541c0040912854000d83c40d402803420041c4c12084855070807079 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 434325161 1250 434323911 434323921
    0x46270b030a0618020c1e010f0606120b030c130c0e102003031504020c0106080307050f01060605130b0306030106030c3206070308150406030308061804030f0c060e0114 73
    0x205900482606441d005610b045c0e5000090381d40e0b001e5036450803c07190076210861007218001d621001d652102a041441003aa4075100034208000c030b040319005060814655a80343d107400b00e502c0010010041000c1003a81e48501407800820751b0044030418040074a00c070304250f54805200340400d86d015520044441301c0e038900200035081e541c0450302642d000707005008131280020003141c0b80710002e80700107840b44100c8286602500c0103031b0200d00d96000004204050110204d501c3c4500100d04000340301e040e80d03a0804503514401c04e0054071001d0724030b5a09204c08940d1600542d0402d50007400451015200d41391810901ca007076101e550300804210441d8450a03003112030940ca1051001340d600c4e0443c190380880e00354400c8100040c100080c180020380440e05002c04501c0346c0c24007400421941c0d0300da02d80500450000d0351641d01c40c00480d2001c03c003030305200d002c49104551550303804d81c60301d030164801d56030b807000741d202250754540703506400b100100c091240c002d02600f904001d4540c0d00701 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 434326411 1250 434325161 434325179
    0x403020f010506030601090c05040905010b07021c05032a0f0601060215060d0b0402010c140c090a0c090302040c12090c0521060f04060246270b030a06 66
    0x40a0322180c6904103001c000080c3d0340400c095044031510600422081d41d0030004035132500c1184c114211092500d030000c12417850410250545030301c03c6e60741c0d10441140420325a840098440000c28591003001400c82c904145100c0d600d07004101c800010541c42d03020051424030000301d220490b00d50181004100c0d59078104007031501d0b20210b500540450a1100100e0070302e403403289015065040c0c0c90003160869108040416400b508041d402000d40c00c11a045902c96000303021540c803520700c0402003030f4103507550f00c9080030f925400d40f2030710380761803440e420f1001030300008a4020a03c03074500500b4060b0398081c043e4041c524855009075090718140001c108101403d00e09150f40c1403007480c403a01e4169000500e20342c1000200b005001701e55110314028019205880003181c00c1503070100180c059501340086a10700f0162003400c240c00703000d50103c00f2a105c5e180b48105002038800900c100640d0303140c0c240a100d9100b1980c0070155280c03614040110f41c0c5c0290751005810340d54510030441c2d070ba2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 434327661 1250 434326411 434326423
    0x804061206030b360a020915090403030906060b250302030d09050a0c0e0c03040b060d021e090106080903461b0804050f0f040e0c041113180f06030803040302 69
    0xc03001c44461400320810f0062542c42c0d0306035000a010b00c0c90171008c10180501e2800500f4001d000400d0405580751528004004c0d02c400a800c07a002d60070040c0114907800818140c0c0d400d50310002404008282a041c45a5210107450040d010360204100103203440403c0e0042020242c01180104060b422078509040c2491190303200e02610030141c02400b07007003551002100d400c0380e00150b02a01c03940368040003454041000c003000b035001040b00c0a01d0307002041151031154050301110344050036070740d030181036032021002c4034248003a8204010a1a60044016100c2001ca0320101e04420110700000700002e00c164996180741c80403e0b80b483c0c00c0e03c40e5803001100201018040c0c2280004000e030760360700c0d82c1d40124019244a00c02007000c0e00f0b0b4544881001ca0071200009000b40502a01100c106031070382120040700380240e09241d694041c51036040101d9003120700314a606502c0910780b4080124580c3e00400c5602c4454807003c0d07081e1100143e024040146004414880d643e0078907207006464a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 434328911 1250 434327661 434327731
    0x1051e13030c0f06020606010818060f0a0b010c1203090c051206220203060f060f03060703060609121502071505010603060603141e06151201031e0804061206030b 71
    0x806021014003580764041171107900001f0a00300041c0ca6140c0e001c0402036103161454041c8a03218000401c030b8203200180d07200b4040e00000e03500700950211540111400e030101240603000081d410100e40d105840313a0b0201102c1802518030300240c588950000700303508161103003c5d5155222000b840007420400100480484841d903465107a01c42d1540400e44507031000740545040000500050f2031038840540f5001d904100a003524601e00e0403200240050a10b4040e500008500107000b08002c44036540016059400482141007004502c16100c040c1d0b10040c0c04981c0d0200078454404440c00030b001302800b0b0400b640b0301050440c1003003002801c85c1d0b50a800080403954200c1403003000b00605241424007402d075601844195100c901099110b00e111119600741c1d42d00080351503070314202c0c101180c1a04d11501c044c41c80d0034452690380031040d82e100d07400703401ca0004110802c2018041c40d50515002040b5402060540d90f070b0b2528440b1110455818207603c80d00d03600350301009058541d203501c035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 434330161 1250 434328911 434328929
    0x100e0a090506090a0b1f0e09010629040905070c1202010506030d031b0c0501150305070f0b040e0f071709030d0501051e0d140d05040305160501050901051e13030c 71
    0xc040117407508515440d02800c042c04a046880512510300201410000540400d03540f450041c140850903c0c000c0c8581d01ca40303800c03e0418603405d140c80ca005103c4903603d0b000d0380a0340d8180f50034401c204000b0440500701c0f00c1441600c0d036005001540c002c0d41e0348500406170b000002c00d031030020185414900c4c02c94641e410586401c801c003800800512240041c0d001d2480c03c4084503840c1d20707026005004038402e14503101c268120000400c04000b4a103c2600d40c49210f80d517109560300c440b8600750085014200662060b2400034024000003401ca562050052500d00e01c1d107450b0580d10100c154043e07071001003030740001540d54501d29407030180c00d00400e8280e400395281440d15502c3d0000c00741c1015510b114420203c080d02c2441011510f00a0300d201c02c0d800d0322032a50380950042e00551003403004a9003030098914410442001e41003000860700c040c2c4442c0c0c54a00c1c0e100c011600340c1d2040004035180004080030010080f02c40300648080b10203807031320301d81c02411818a9141014140c0c080110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 434331411 1250 434330161 434330173
    0x1d0d0f1b080708030604091b0501030e010e190c0510050a0f0c0b01062106140916090e04030c060606050301090b120c06160519030324030803100e0a09050609 69
    0x440701800c03501d200e0b0304080e150b616522001d00040251511210103010101584502e0140c0206000301c08210b80090f00c0030820049040841030903070302e41044c80f88082d0013001d5402041502c1e4070813400b82e02e11540440c0001610748002034001d1040703400740d0f00003e0002c107079100ba450b04035010b04542c0850f410081540b00c61950760302802081405010104040e602c0601100c40204c050f1207a800c0c03855400b0f1000039140c00313461a0300c030440b4403000c2c400d401142c080307a00040140b42d2042441c1490380e4040c13030313a03041c41d0300a11a5030000c1c204404100400d400c400104603603115100c007a00043c2d031585c0e07980d4545803103041a540c000082a02c03515041c262031018590004800348411400da500303a0700c400354032410341c1c290b07905130401038014002d05505941100401c04a8422103201e52810000440c007405150141c03425200c1184234140b00318001e101146000014540c444901c1044034000c1da100c0c83c824602030380907204401c441e602d0704d10350020050f01b400540c2d44418030310000c0030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 434332661 1250 434331411 434331413
    0x3040c080a020919020f18150301121e1505010e0610050d0c0519090f0b0307020a02210a080c0d0e060a030b04060b0703110c010f121d0d0f1b 62
    0x81190009480f070360000e14200e0040d4443c0c51942c040d116030f642602a1541c80b54214051024070041d08441c903803080c910340c0c01c207101c000723005416603058480d0580c019619100741c0c8c0e2414441d254104031140b150044404140c0050b844071503014518002c51030104565150000c0b440362000c000e0a11807103490b401d10016a0550300006454516464034800725038840311103001d56161140d03001c11103ca40e04402809051504070320031108590058400402c0c1d075640c2c1c1c2c01315040340803d40d0803c0043c0c01c548048000351a01003c1e1480311210340504507072000c18000c070a0316100c1080320890320303810082440d80c220744040c4400071500d103481c142203101c8007003800001c616201b401201c10505984019201c055180d076030144c0c2c05024078080c147e50380c440904024001102c0b00409459500c100d40b0b1080983d44150000101da03ca1510b40c0e424010310307210f0300e601401c501104814201d03085004110081020415010104082d4a50f121010f003000070083c440514110a03c1800c200d100e4920 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 434333911 1250 434332661 434332669
    0xb090f0319061509060303090e0901020702100f171006020c0a080c010c060905101b030b061b030d0c030b030f060c030117010b0a08010c030e0105060a14121203040c080a02 75
    0x415407550000b40007514010b010074520520b5290313000240b04c6442c0000220406402050b1038003610060310481d04103035038290004c0e01f47d1080c80802074100d01d8405003000101c0c00765052000381e00311410103585100c1303100000c008020044a5440304280c030300c04200846501401036402e030348800d503221b420007428151038665456560a8181c100002d0078441810f000ca99413000c000c451707214060b943d51b50000c04d102000381c191404840004500d459051108501070300c6105900040608800d0903d2003200c103180e1a00c11000340c929260000300405181c0c00d203103214042000c03255850004071269040103240c82c100c641e4410f9896940400240b01400e005002a079044500c0942400740e030003407603980789024101420301c40341c10501503400403a0550064110b500000244c2da82001f18401940410b400d81c1c00c151089074000d1554402404250348446841d140c0000c050110b100480d9054106403401c104e02d07003441c404000c04020b000070059860740600060646000605d03107010300e50009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 434335161 1250 434333911 434333953
    0x190f0f0b03070c05150901050411010c03020c1002030d05100306140c0d09020f030114070f0f08130204020903100b0306010b270f030a0303021c11040621060b090f03 72
    0x2d00107108008a4000c10020200004038003100454500a0f0b1030030140e8445000c0d02094078211508907502e094205694459410180402d030987d00414400413601d003030010324080c039444103085000c10800002941e45034050399020b06416410420a01d01e10305001048400e12030000c140050341c2028020f42042c800c044c0c410a0801d00f80c006506d05241c800203160045040000b9055402c0840c05034081041c028286e00c211110f84074900981c1000b00201d94885a16070700f0350101e400e034000324044011800c2111041403014000502c0e003d600d200092501d2031645d11404901d444a2081541e0304050055a0042c4084000389040c441da450480015141020091800440b00c0d4034440d415643e00c54014a030a03405029109180504d09004000c3d40c0079140d242c5034a055407031074400f03141283c802c82140b2402e4080041c05c02e82441d84c116040b110720541c4080078245a00400c2607810203210302801040380b5000b16540322046024000b0f503200c1c04070034501c070341c0101c02e5000200301c0391100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 434336411 1250 434335161 434335171
    0x3080708030709090f05070e01020606010f050304080706022a0a0b1503010603140c0f030d050703120f0204090c030f1a0f01030615030c02151006030515190f0f0b03 72
    0x20384a95540b50100c0b11100d595000311303901410301da03246040246076130280d03000b040300e5520522110031070f17001aa0760380810b9640394001104249900e204620a001858001d03214030b0a0500c0e08910b900e03901c050b07030400304407004500c0c00c05c1921042c4000210011701e0000030f05004c1d10800d94261504007200800800040c40a04104034500f40c6580a5004601031075000344000e010505018003a03543e1501401d409000c6d010203180d40016280010b4051084a2103135280761511240c0c1d9021150504400486944281c84601044c0081c000380044c0000c0e0254100c0010526107050000b003c0d2074003080c001c224985007a8501c4a1808441011610940143e9544c0d521002c2c1c007004030002d1a15a02110b01d2861203031280104035456001103000c411180d08a8644080b9441030007500345049d1025050314410301c20410840380203400c595489101c100040e40700503140e0000c40c0c0c0041c10401034402c90100c2d09021301c10356100e0150600070f09508a0315848260030900544c1d0507210242c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 434337661 1250 434336411 434336423
    0x608010b030c0912010203190b03071e1203080a1b080a111e0909011d06041a0303030405150114030c330306040c26070e0d0803100f030807 61
    0x141d9581d00c59401c4500d03e090281802c3c12030040100f259000750820b607440c03540f002d0002c65020b41c85460b406403401c8040020080c2a80078030700300810400117410404980c00d001607c40c00908155400e0b400b00c0710324020f40354502d070b91809046400072501d2920240110744250782e12007450030360084400343c0c00b40e0f5900c000504d400265a140380390740500c4502010b520700401c55148406520700280010280c00d491589039a600c421795840001c031348211002d0001ca8030340000326180307495000314940308070842c1501c071a0308103a4042030555000300c0c1c05507250340c4442d19500d1040300ca800500d004020340c1c2489044541131100103034803800803081040c401c14024490480180078441d0f014038915050b510443c203070400482c048100d07013086500c4d6104614100c11400003031700849000e4a000c00400c0741210880560400302c00b0300b0006400b0100300f210301001d40d149911a0401c1c010818003a80e4815207c0c40d080c1d4032059011000d420096a004024400f0000681c410342542d9180381c1c401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 434338911 1250 434337661 434337667
    0x9010c08072a061b020f0115051810150305070f21020f121006030b01050703350c04050306060616031d0301090b010303020613170f0706020c061008070608010b 70
    0x308015025080c055002c0304582c00030300d004d200d03860300055051039071204000240b04040300d202c2840e080079514860aa00080480c5400804211401603698456403012461036080e889514440c45464401c1440340800d90700d200307000000303411090358503900310b01d8a001515901c002100328980c407c8a41e480681e0758011880b250442d1003001911070030640282a031020b8509004d025940340028802c43c0046854455800825481403041340c0d14640c0545809204245144840040c01c044441d268084c000b0424038008603881020014019005003c00ca0b403a0350a0030101070402e4000340c03043c0c0c81030b0b9003004ac841c42041000141c4208a4042c10030006040f10002c00e08000b1000500c52640b55217420602c00410514030303400f40c1079a000e40c1c21581a941c038800340440c3d0502c50076010300346c0c180c0e00301c0e0f44000c0d00c0e488005116001c81040840c0c148401a40e4210998000c544d440100d80c0007042044500c02d05125040c000340600301c0100219450814054211503040c014804415400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 434340161 1250 434338911 434338913
    0xf07020409140a0b0a020a0c0f02011b0309140d020312161e030e03030c2e060e0a110a0914010924030606170105042309010c08072a 58
    0xda0001848540007070000b91180401114103840d09083c0d01d08803018203420000c1303040c1250501c03d580444c50541c88143c803988407512104010080d15404074100040c1c00148943c45034110200c2c0000c0c0d110b074071030010090031300d03900d50b5100c00007111031401084001842005682c00251074101d01c04486d100039510b0701405100c0448503c90780d0007501c0c0c5488238a00c8401010780ca0062030b00389001e5507440c520700c800381003015164071a4004116203075002d406100001080341100054122034a00840290300040b41c46100362a103941c44902401020307410803034109158050f210014880d40141c80c50b0400b0042c010700340750514010818a5600048100401e03401900c0c114090700148490405405002c4260100741d00c0300030b0000c00190401c240000c1850080b240c142e0040500c00204070760760709141c00c0c4030043c90403c003074404510408851078048040300f030019000324503900010900c2c0c08054005040d458020f0b04040c2000701c84012880c0b1907040401000000c0f0744407507600d090f1525 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 434341411 1250 434340161 434340169
    0x6080307080324120604020310050c0703110c030a030c051204030f080f070b04050c0a0f180b03031b03130e0408030604020325020a0507090e0601120602120109020912010605060f0702 80
    0x45006644e084501000d043d001030702c0015045100d14400c60032943c00350341240240040d02c01c2501c00d540c00034401c0c081140028000c4d82043c0018901400315007441038484002803610940c10300c150301083c400c000b9181486010b2020000203000b0450745031074546580c0e28103602d03000c11440940f400e0710101e001d0b4071584540007250030890f00726046c4240c904050415503100c00d080700c6828400ca04da45030006095050300c015400322000400e2040c580852078203104003503c84c4c410740300d926000802150031050702100c4a8402e404049006580700d005041d040b02107285da42d00000c2080d40d60350100400200400d04890b80900140e40151712625001320070006030021410010b178000358200068550b950000b0548400ea01038002c40c0c420035510003500c0c0403102a20707001c08441e00301a005001c6500c004140d0030601d44508001031414001c0b000000c442d501c00e0b081440000c0e000191259141f92804015014030f608a000700400307440c01d00001c0c1c1600c11580c4100b50254003103051000c0d545c07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 434342661 1250 434341411 434341471
    0x606030503070629131508060408040312080903070f050a0b0a05071202030f040204092406050a05010f0c0201030b0f09010f0519080601122405010306060803070803 72
    0x6840421a0b403030300403500c0d02d0030181c541d29203501e914221160080070a8030342480e980103000e0003d003143c100ca8858048100c0070b0004078010791002c10042c2000260f82004201c642e10890085404689071400e41c038040076071400310007040040003039075420701004407000300c2120840e6900c22800c4d40c0c0000c861400b681018010328000c0c105948c1901000b04503885a009a485402d4940c2c0709040d0050a90300398040340011b40321011002c54000002d0300504050784112945400361003454006481c40c10070f0b0148100205d44200c6294860300104a49d0a146103144083d000909207007030b050300340200003003480300703282d001070304040d280c4111009a03140d40701481d04c081009002d0203029030f1104000c00d680c9840c0d100343c6024148590700e014440904428090640c1d00e880302501c0140d01c0c11541003000b080f84c02040c0d944100006080050140d6000441c0758220300c40703404626585182061b4085449642c40b213201e64004108a60004008500301c07980810009080c2c25141c02c10812480988 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 434343911 1250 434342661 434342663
    0x60f100b09010f120f0e2a06030601090e091506151804020d0c05031005060705030d0c050f190905030f0d031505180f01091406010c2a03061422060603 66
    0x5413820520a05009607a01b190800d01610340894a441d9402000900071200441803281410740000c81031400303107840002590800380502d0031522184d1618101c41c0c400c4000d844008a9034000f01c0720040842c000143c80764000e004940c01c44580f00041c3c45800390388541c900c000c038a041a109921170503030751ba505031031820b441a0303420080c015160030f0261240d40203a900f1950048010701c0060586002d00442c0e560319400f0000c0c605201d064201d0601400704104030009001060005a600342c240708082d102c4008420307680c6c80381080c2c00d00c0150281005800650003900880a0324544840010340c4580d604910b00d000a03e1b03401032400c031000c00006421440e48000500741000d0322102c1d058816010304508241c14072941d99522440701110340401b4607601c134011100011392030f50701030400300720071078080d180020990300b030110010b007180003400144c422140c8880d814803d100b801d120781311a0f613009c00700d11040390610701e0500c80c1014440d414221b020031400702c000104083c64011000035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 434345161 1250 434343911 434343947
    0xc2209050f0708030c06011208041211060f070b06010f091203020c090f01060807030207020a030215071a091b0a15050409060f05011106060f0603060a0b0705060f100b09010f 76
    0x303075120b116441c4c4079400340e07035403031014440d04001041c00c1c81d00322101c03011030313074400b0360680b40a10300f004804a0701da1492043e20610304400f02c46544e51602c2000b00005207125007020759030760491a1029000300081c0000e810808581e5050040030b80040300301058491054040e2140c80312407400300c0c9007130002124582c001850b8000d00294072282d01586050301d02981710030703a50f40d88000c000ca0803409030130341c0694064600c0c0320410141c1028072034101c8041d894220b0341c1ca00042500c0b004107121900710000408100e03a4208880104140220969220883d0300b01c0e14070780e18080003030300501260240031002204c00c4034180c03582e8050001c88000b00510a001d001d22aa10360140b034450f8158030440e40855401803081d5041280820280c0c40303036400070072002d09228964140521508000c11050300940740c02e2000c6000017100014001880c480d070010000ca1030802807a100102d405009a52200300754002400005040404c1d01d103080b0080c038003803140c05045441244c503100503064501d46 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 434346411 1250 434345161 434345173
    0x307020414010305010e0f07230612040b0c1215060903071e0b030c120a06053c010c0b060402040522110f0405010e062a0c2209050f 58
    0x12142601d1003a6040b640664000c01c007043c50408159240d2580082540050300700c2c4a052046650b203007407820082e203030040d440c55902c86841c0807800755072201c0c5448a10300414020002044900c034811907124008941c46428001080c8445a1001028103400070481c3ca980c07408800b52281c1d8192414018014104c40d00780f5601d2000f00300d0480e408002d0148030700b8043d8042861001c4908890003200c2e5003021916298054000c03e1031503102802c00100d0b1501d54000187e140d0b20300700800d21144018110a0700c4006400c001e010000700380f400c1420000fa0405402c1c06613801a20785034003941c000013043d099580c1d100000e4000d21803a04000c2e031010b802c001e6404200d0400a5500f0802c1844004006841080b07240451500520b024000c00c04400c2005000d507510410b0303240702005000d410345041811001180403c0d00955581c1804c0d04440c14000d11b070150100040042c4480542c2c0f0302040e00c01100c00000c40402507642c00c14a030b91660241da040000c2009a00160140700064406c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 434347661 1250 434346411 434346431
    0x9030209060612040f060c0516030804020109080f0d08181207060608060c072a0b07020103090816051005040b0a0e10050108100b01030b030c04051906150f0309020109140303070204 79
    0x100d07041e4420010385103249001d20303047d841030040303044070031120050500242001075680c01301e4441500030412410091800000906000100f00c01e0203080841406401601c0d014600208510b00082c24207039014100c0001d2190620702140043c07070602d240d46c02560f00d4007542072003806400035902c0440075100d9401041f0080b0000d0000d014020301c0355044402d0300e04002c000035401c03600011400d5003118002010814410800001d0500c944103050224034207205481c0c9090740d4100034030117002c004c00c1140180070444140310380e461540480740c042105e4103040d200c60200200c02420030110650390205d40c1010712040200c1c1000e046c8102c402c0c08650f0311100c1464981740c004441e008da09040c071034100b620b5800382c010705202d100050024036003048400100009000064244a001d54002c050a020a43c0c0c44c0111805441c1d00f01d0506041c0c281108002e1486200c240030000709454584c2c00801070303901c0380b11141110900007104000d941c90b50f0029083d07220300c4000a60140c64031503070350 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 434348911 1250 434347661 434347673
    0x605180f0304030309051f08060d0219030309050a0605030619051207030309051512100e07090626040f11060a08060913080316140c0102070b070f0903020906061204 72
    0x583c0c1c801d95522025a079260305103c80b1080d40301c035018204850041030f00312184140441a84840c008068040480990b00841e8520f24034540c0c03c100246503480600034103800003803040c01403509841d00d0144503d00f5100070300501025006030b00c42c52449524030f14142e0b000c0d80413405080001d04140d400a0000313400c1c0d5842d1000d1000700c0c04210320100c000392510303005101d0318004071200d00b401d2074592485016001c8120007415018081c0c80700c10045547c00c0e91800040c810350550f00c611002a00b0404054003251902e00107885020140d10141c00c15989841c903641c00c154402c07503c04650041e441c04a405061511078650404800b0904914040d841b01806015080c02d5504074565200c0101d95454142009000b40c4410400c20100d4494988036000044541301842c211480c02038000c1e034480503a1084028111582d00403a0301d0090001200c1800d0300181142451600041c840174013030081e08003484080d01c184000c40020300c0f9078644e08215040202a01980c854910741440e03c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 434350161 1250 434348911 434348917
    0x100c0308060640050303090409080f0c0a1505071b0c150909060e0c0703180306050c070b0a060e070302180a12030908210d1808180303070f0605180f03 66
    0x8540c3d40c0c1441c220858040c54a600003d05644d00a00614940704000052101500e851541100c0e490802c024100e0342580c03620290a50301068000380c20240501d003031031081c1442c030600c0081002c0c608001c0c04001a0030902c1d8815044242ca05100d0041d45814400b01d039103e568006940381c0304030101c10110660080b03010007a918142010800142c9403452514105402c40e4400c045102c20040540401e0103200390312040544444455111600c9075a0581643c2050307440c00c00c042e2000c50302c0300401607021720380c40c0d02c48c0c5054802c1020300d140c108a608402c03406000d9034103156000800c0d0250400003400b1200351072002c0c2c502980d440d901c4d5495031140c5001c0409800280307002d407021030190008034880803001c204450702c001d0403030100346041b01c42c0e10005481030300642e582045002c03041c5140342c100d0814000c040c042e4031250041c0e100c041c0f1442c201541ca1280e002089904001a000e0700000a4503070000d20001301d42e5504a4000d046030b0417a84100c12034401c900c80303080c0c814400001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 434351411 1250 434350161 434350237
    0x83a051201091d0604121808070b03010f05091015030e01140f0c0a0206060f01090e0411040b030102090105030c130506040e011d1e07030f110d0b100c03080606 70
    0x22162201000104042d01c8410aa60040c0741c00d55a0f55121b07403282c82540b03000a0380f40070480c0d000609036a40e03011440c1034a80e903c0000001d0000c1b004001c4801d4041c400b40c0189800c0e10900d2952410501d000071131034680c01804480051182d403171a15902c65403049005216000c000c1180001c410fa460034280c4040354680100300f00c3ca800184241006e4042d22600309490300107101a4aa2000300002c002e10512000e042092040d00010200d011034442c5001d1801804558591202c04040c07000380d07860300d8001c0d80260f0040188039000e9030300108076903102c05041560b5841e00d02c03209010195030456072103154070860106000c1a95907694009a04898a8600e10001c182446580c40b004501c1181da030302c02c010a054508040c00441301e503040d44002c481c03400141288030040380350110358410003004a082d0004c203081603402507074402d182c82c0001c126804400001001c2c001031810244000c001d003084096030104401d41c503403105488031084c0c034031941c44d540000034070b44042550200e61 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 434352517 1106 434351411 434351441
    0x30c15022104051e0c04090602120123090103020627130606021002030c090d11130b030c0d0201050406050c0c060c07083a05120109 58
    0x5449000d450116030500325a081a04042c2c0c64a01e802c1c035400004c000182c0c00c075001810002d008500d00e05c0864011405244900d440006409803045100c40520424008600000783c1400707007000c1c40300d607012154840c1c0d0400412090a8083c8001383d08028200004240c00081449000e290240d28801e07003403c800b03a00205420180d00d08a4554490384c800c824445190305200e100e40603103075005c00f503055041c062814074036481103102087c420421660100101710947c030b8401180c110043c501851402384054940c0a40100040c1a100e030050300320740011032400710f5a0000c03590301a036640342000c2c2440f10503600381d404400980814413994032032401ca661500000c041585c8506c02500c07a030307480c01c585640361001481220703041070b0004000b403480802140703418244002502c0300d00e10700380000c84190351a200b8003d101d180f5840c624000b1030402403070303004500d09020f050 = true := by decide +kernel

theorem cover : BRFrame.Cov 434172661 434352517 := by
  have h0 := BRFrame.cov_init 434172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 434172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 434172661 ≤ n) (h2 : n < 434352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
