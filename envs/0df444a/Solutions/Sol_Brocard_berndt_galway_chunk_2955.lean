-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2955
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:14:31.190578+00:00
-- url     : https://prove2.me/submissions/100b617e-cf38-4aa4-8be4-46862010f10e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 531294964 ≤ n < 531474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 531296214 1250 531294964 531294983
    0xa0312030f05060303090402090a0e0c0403032d03020d060b0a0c110f1f0c050a0b0a05060a06090515090607080c060901020307020a0605061206070504051c0203034003 73
    0x391610414407480f4410100540035510707003081c400800000b503000407a40c2c1d83c0615250400314034613020300e070b18611034441c02200d01c0c8c0d158214103003d4403101007482d4100b89410100d201c850300c0603080403944082101c2d400c0240e290300c1c3c0155142c000d011141c108603901540802d20b138904903440b0a1480449010340210b4003101c04100c207001c8003a010f40741c82d41d002484641c110b0040d42040390341c43d0205c4454036000655510603560541001140d4000b41ca22985500500c032f003103480f40c0b103866084a4100d614000c00340c0b82c130764050103041262041c1e520480c4d001003950f5109440500302c0c0c107441d40040c0126034a40309407510740001e0300070012140c190302c40c04c000035040b400c0501c201ca00031a0290000e01d100c0d4940d9640c80089d05005000f04d401800c01181d87d03003011300c02c100a0340079440d40c0c1c0b56680c40f00d0505081c05036030b110080a08018281c1c583c08000541c43c0401140c14122030715010582c0303c0b60070400700c40c030340f03001140494408054a96440c00ea80101c4054020341e8070460440703 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 531297464 1250 531296214 531296231
    0x325050418050903090121061412060405120309070f0305010c08060901060e22020a0c1e0f12090302030d02070518040206030f1506040303090f05180f0402030c0a031203 74
    0x304940044078443c8050340f003009144025030080c14007480c0d880d00b002c0d103080c81c501c0b106440800e9443c1e642c0090080500c40e916940300f4680050143e5644860700020041d5290a854803a500c16480b20b611254210000129582d40700602503100030b03158442c4241e041583d00d251140c005c003070300304810001480d5100402d10070b242c02603640c0e0403100c1590754421074a424000704440820400210709094160141c030780b006401d00c0c0050302c1d2103140c3d5141c0c1c40b81c0142901b0651202d41541d00f2201154500366051000110038054010302c4030341100b404c0000700120302d02641e800c0b20a800217540f6200e01c00c181c1064540c005044400c0e00e009590390050564081112046400d0a8800a500001c1030000600d0702e1807081500703602c2111200c078902c4825510022440307079400b80c2c00550000d01c0c0074105006401700101c042005010641d82c02c9030b0680510f003030901080014002803503611015004c1800d5603002c21140c1c280c824020084240b213981c034540350315481482074030f0700301103402c2c1000c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 531298714 1250 531297464 531297509
    0x20a0b06011b08091207060207061209061410060201020426150112050f071202090601140d060e010b09030d081503010c1709010b03061612050106210209030c0603250504 74
    0x1b16800c075240e5400504800d4208841a10b40100f5451904110343c1e842a050300407803868011b03501500560720903010300d0304140101c10f043c4880c3e5009031056a0040108100300030080c15070031811110840e12403c0441009030460800c5050946000003624580c00031411741848030070600ca0910a030304072203603e405190392903155800c07442280403801c8001d030f521000d03040c02490b00e0b503c2030701403500046a118a2210721855008072001919481e41c2c2c0d0014003042865150882c0903022102c042400d0481640010b0b0b640c00046d24070400700056100030842e84801950042000701c8014000d00824402140c000d12000020100ba03100c10040004200d0076101031142c211341da000a4080d00580d6505010600c501904c549030804100300c0c51003101c0001030a00c030f02030113000710343c0d2400500c042c116078082e900d440705402202c01a01c1048031020b50b5030001144034142d41c0030b94015480b46d40781920030b0703e81d02100001e60350800185060700200e5502000500540315052a85440000d04203c2d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 531299964 1250 531298714 531298723
    0x181103041b15080a0504050f0a0c08190c0306020f0c0d0e04110313061a06040308040801050f010f2c07200102040b030c07061107060b01170403020a0b06011b080912 72
    0x4040440c81043c08505080c6494000c90342c0079016900b00d484580101d00700515214505105440007007515405000021080c04040064896048489101201034843e1a2641000c1c400209056400160043c240c0c00c907205484138284024244e51000f480c1000c050170b07288007030310340612172450401c003425030003503480c2038a00810306070341c100d40c2c6000c4c40ea0703400e0000c0c2003100e01c02091200c0391035001210f03507900300140091440b13a10210f8845140c0845903003544c0015028010302c1d0291001407003500c130300c0e28600c0100c070080c2c1c882d03075910b05002c2240080c1032007240c40300220300601310421043d0703500811050840e90300000c0200c910184400300900700e00031801051107030b0340200049013401d03800c1d001420855010b07a40006004401441e854019849a01c0c02c4a0107611100c01c1c5940703613004003204140d40607416484065103010385c0c00075181c1844140c0101015120008100716901c00c18204441c040517503000b54541d40c003400c05240681205401900c21600840b01c807695031004134 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 531301214 1250 531299964 531299999
    0x303180715020c040506041e09120c03020d0804080f030c070203150c0a080c0f21070201020703081611010507020a1106090102190303110a050c011a0a181103041b 71
    0x6000d44040e0000c0300811000d040046c0250343c0c4a5115018016000c8400d044c1407000710301c10b20009090a038a1070300840101009518800740301c07001100d000801c0e00425241030941c4103103055103541d5a586000e01c400d01a036a810a078446c008002c00010540d034100070320800313000300c0c100c030804816140000c0d020901200e2600091760240030b0824400e0280c000b40360026150311140b4100700304100045410381000412459803200b040d990904144131013200c0e40c1240c400e100945c51301c10b940d03c02802c00d440c00f4100d071880a50761181004028400c40c18080c00f28846070003840300e4148148020354544511400751480040c60405401521b80a07003180c07910b10040c1c019000e5030140000958165440c3c84d810b80506403240512901d1044e610010800e400c15600c44640b181a43e070406801c49417440800c0301c01002c20180e8444076a140c4032a80e048901c40f65180d0b4400c61801020809400c2c007000008210030044140030030080544c2000049a4056111201c0d240e541c82902c1181e107400c0307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 531302464 1250 531301214 531301217
    0x1d0f07030f122a110d11040207080d050403050a0809072909040f0e071d04141608071401020109050601050919020313020f180403031119090608070306240207080303180715 75
    0x1c400c1c1b45503402c01e07402401700c15000e0903199081000400d0803000752401140c0460000304001140e03100690000b030400d8000e14803030014105141040d400d00241072000c004242e8060080080304503030300001046400b40d49010700140718203003d906004000e41004000d132a802e018010001c503030920004201c030794036182d42100c0101a1a5901c130b60144080b807070140f47c1780e4059000001620030703070310300e5040003004d07604024180c2d40c0c034001c020b140b020056001e0604590400c0b1020000c0f842c001a0303030b819078204855450b11070b01c480340d91004d48080030392840340160010040181c1403600741e071044101402910340035038040001c3c081140214840318505240b02c494004500031910982c00b505402c44040040c51500741101014907203200302180c40b5000480c0c1040900c030399580b141c3c0c0d05030000303181e0400740f154030b00341040000414840c10382d21404900541e44ca91207a442041188014440c0c9002d5954038140b00c0c8840e285096800e0054580e403246d024000744c0110700360301100c43d49555 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 531303714 1250 531302464 531302483
    0x432011a04030b22080c010b04020306010c0b070504050307170f01020a080a0209130f020a02011a1e060f03010608090c01020303040c120212011d0f07030f122a110d 72
    0x86659240b0f90100140c500c8042502c00034500c119284030b0800b526641d4021002581c440341c1146240c4e007500c0401c000c050085005009114807640c11030740b41d091280d41b050351260702e5035800b201100d00c1d000e17981c000c0350305200700b9100050188440100510040c020410345070003c0710303203006900380e1040300220030004e0440b80000301ca00b020741d4050541c03944d0080130524065840d6034400b058030200710501a45560016000c41901d8092041c1c2244480c02c44e200c0c1402c04241c0c00244031146083d960a5014219a07607009030b07036550300c080710310400c00e09188640703c0d41c50780e07030080450740b0403107500c9200c0c0b0400d2a00500f960001003500c1c0b040c1d0b80710101d8640c1c0382c00d04515a12100525a0498203c40f080e20140c124103400c2c09000ca061282509080307850f00301c0900e481c03410040070880150740e0450f0009001107180340d5225504250440c0342c0805420840c80c0480c1d01e80300030711030b030740c185105404150052058502d44000c0207006016502001c0c003880c04000200c0320b42c1038010306500c078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 531304964 1250 531303714 531303719
    0xe010f0b0310050303070614060108190b040b090a0e160312111005040b0a11040b0307140d050903030105130b03060115030b06210711100b0432011a04 66
    0x1500055a0003401d8500342e01d0810741d00d00102e481c64000c5c0504440b60f42d00c95030001030580f04080711035400300007440c15042ca810013203d10680225040c508100080c3c4035450724400303844503048140d01020151503980709143c245e901e60020140100e40031218000e0080701c0100150190a040540f85c100183d201c00240b5006c00780d5000080742200e06017401401500c02005116210311740c420783c0105601f0322036180607101c9000701c3d03e0300c690440c620181031009000e40081803084e281d0081c004c0c10240c200401d51100941c0c140121140e0040850524080050002d000b1000d18100d031030641d001208180c045111600352101650a19010f50054004100341d19035218000c4100026040c005120520034000c80c0d281d521240400c04201d50468400001d65600700042d6401100d03454555080c60414004035251002e000442605a407038503040c0f840e86e95240d0100022004854050005205000000840f40e40213146904082507600000030388454841c51010b0410788241100d20309130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 531306214 1250 531304964 531304979
    0xc1315051f0c140a0b010608090a0b0105041503020306040507090f06140d080f0406020105061c0201020a1403160302011a0114070605090c0a1706061509060702130f06060305010e010f 80
    0x641c14000d80d0380780c100201c803221030b400030700100804601407402e034000c46d81022130103481c01e08043e04c810200d034410880140840c000f5040207040d9030301210003017103214140320280c0d80c003441c1d1703040079500d40901c506010403c040001c1a00441c2c440c05000c0c00204241c003204021103c143c480c0000710444550605044c1c40d0a009007403a43c1d1195908508004400071040a9904140c01001c0582c2d03540c0c00340f001a24082500c4c2b04055000c081958107803080f580000c0d180c0080b034400070109403040e02490b1540c0014000c0d2401007803c03a503840c0350707008030b828000c0c080e040710b07100d469541c0510b0000780181c0d440384600c213031a079a003640132a180280c01e98860006002c0101443d4260196010714481903903117010a10007403030086051170080c40d050000c1400c00401900e074900c220341013006054880d242c4000d0300c800c1541241c00e40c0e151500e0b800410508200d22a40b000100e00d000042d0030344a140741c0c4180d09894a03a038040003e681c031401c1c1c07288803080a0107003071000e260583d001c00444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 531307464 1250 531306214 531306227
    0x1801230f0909010905030d09031709030f0c030d09030c1a0f01150905030601080d120c2a0c0e01090c0504080a060b01090e040b070e011e0f020c1315051f 67
    0x1a50b000000214900151211030030364015190007010340303460f810301e4820705910840c40c1800402890308003180c0e08101a00b65541c5c03080014203110081c0111710000f0019040c41600d501041e0f0701024045148036160040101c48014001c075907000005045001c119a82e2400380d11484900c0c595003056428456504160548013500707034200002150007055540b418800385000f03140c0900142003200c21540003030100d855110382d09500c3c03403522070017402c0990300082001c483d0320341c24881c0c029508002c070311586010301983c0c09400344605840c00550380c941407210034101d03145540200109003196030112542e10940c414003481d64090441a004a00c5d80c1c0e0000c00452014188100030564880c07290806e21021107003030303483c203d0150401011507040f80322222030300700900e0200405038103402803400300c41704441c104003000000d030101c202d0380380204819101c250b002084114440c2c54806500080c00310703441c60126803801008006202e0070b051580c004040e8982d8207e446100d80104212001d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 531308714 1250 531307464 531307471
    0x120a1d0c2107092c0a0f020a03082205032413050601030b070201061a1c0b041a03010b04050129040b0313111225051801230f09 56
    0x80044038030982003464100882d0009004019001c24000c41225002d4415040600d0803080c003944020001c091a03004a5101100b5900c600d1444080c2c0e000d0000c030300c1c40c15094000030601040050580e111755203080b10030a08200081001c8066034894081c151034040d001030ba070b00c0030f4400c040c9000d58003100b5208164403503070300303100118652902d8540500c1c00800380d10682c0c0202c8030384148004d9507030a009203000b50032080d800d13444401d99031852040078400c0c01010040c80548807101209480c4581029005510050080c05129007850084c0100e03262102142c4c40303503203084407004607800c2a015180c121202e2601c1d0007440c060701c00d0f0806543c01c401c00c0c03400000204010106415020202440c014007105e50040004940c9242050a42940398419480745006109240a4100000f4040405481c80680c4200720390f0040c0802c0384504203801650740a41208400305001c101001500e04a0f0603101140011103031700308400250100c00c01c0180e0300003022800d503049500b0100c110941 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 531309964 1250 531308714 531308749
    0xd0215040602070c0b0a030b040b09040f031101060b09040510080304060c030c0b07051801020a020f040b22020c0706030e0a0b060102031201081c1409010c0c0b120a1d0c 74
    0x30b085202e1355044640e0245410400d1500008610000d00d01c1d818480c000c503209050b5020411201060005211600f008000404140790b03c1d03c410100340c031591641c54080000700080c000940c079402210859004010098000ca04d4080024100388000390a8030840304000040c610341421302ea001c803014160840c058051000b5440030000013034041c82c01520502d0160b540944449098401c0302c0d01041d4605918119484040c0709005640c3d04661117500b2507040702c00003480c0000c20081081c0403c2600000c20001c15010026001c140c95002440c0c24402c00d800d41d01050b40f5020244c0441e80c01c150b030510250700481d01d29001684047e0340d69001081401101d007804240000c074030386244242c11a480d5600008001003d200c6c90245402166919041004038007100c02c1e050402401040150360402a07007200450a004c00d80c00c400001e001c407080c800f41d50301c0201c0d064041040060703c0b5094403c2c50108401c107941c10040304501c20111a0018080c42c503c410104002c00c09610141c2da03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 531311214 1250 531309964 531309967
    0x240303090a140d0c180b030a0c14030c0402030c03070306080a0507060804030e0d0309030311012f04030503130f05010e06030f07022409070f0b04060f030b041d07080d0215040602 78
    0x30488070403101008040030711200c45d13100c094411a034243d840101240d802a0b0040359a100040d00d17000380f00c820f4954010640c000890841c1c0040e103040713500b150f080e402c00d200105028003100a1001103100310180c0c1c0302848010303034840d0050760312071141501501c103405c8010244030b894482d400550700a80071380780040c802803030b000004032240300da84000c4000c075504041c02c104041d0080c0800011036076050007080400c40070f5141c0d581030808407452141c6140b801400c00c1c000b00e2480261400340d074110040300d441e090300c580d1241c4140014000e110009050f04c100060f5980f091800c600c04900180c00d140c20340d00c076040451030042d0045c0c030b41707010360042145110101d07500480c01100c000406030a080682080d00d0b880b410503100b900301c2010f11544540501c81c0f10100c400302d81c100c0304103151034243c1c4a10178104900070300f0000e25441d4454140210b5805801030317044600d01b000401c40586501d1a56038981075603c0d020741d9040005604440d206080360b480340a180b5500500420740507 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 531312464 1250 531311214 531311239
    0x9070909020306190b0310060f0909020d0e01063809091005031015091a09040602130b040302180906060409050c0604060f0f0f120f0e0105240303090a14 67
    0x141c811685c1000386160004410400200c8507901e08000030700f400d007040c10200503640300c000d00d81c04e10340c021280c0784ca070002170210803400194040c640c10031601d00204035071f946801c0c1036501c10506604508041865104041c848880107006c200d0300700030703000418030b0007004009204020000524035282031068003000a0540c0701031014074460000d030070000603008245c2c400e0302605c0aa40d0841e41286144c4402503000c2c800105110084003011101d18459556901d0300304064415800034031642c2d6000d001c00150039104102502c1602c1c07085400403040304901200300c4510504031103444e1035a0050300850040d0a09501c00c40405000310141d9100444010100d1019402980610009104c64640002860b40880310030410703a010720b02112000f540c04001003201d40b44112040c1015960455200540496805100090354080081c002032804c00f0811140400511480482510240b400d00180c500403003100e8400300000c1c007100401c0d0500c1c240941d180f4018068640044210159 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 531313714 1250 531312464 531312499
    0x40b030d020d0917070603021b0a030306030b01090b090f0a09140703060c0807080a1a100905090c070b040f02040b12071a0a0e010f180f1409070909020306 68
    0x294503144010350002c040c44184404002e2202c445036000e182c40c2c0b6420962a03200d03400c00f05600b01103450524001d0380318040703480c0c1c80c1403800071050710090500c01c0c0a011010903405402c040202c90148201e481540c1e030f102c400c0015184000b040d554400c44074800642114500396449030000d850240c001903401e059a100703201c000300b0005102407a0702c1510100100001401081003044207490b20700d0315424006e202410f600d1010340a0504192140d520090410003004486c1001c20000c01e41e11544480c078001500c41042800307400d00601c1d41c440003842d0404c00e01c0071070b55100e511081990559643d03464040030341081c41412684942c50b0710500d440d83e920007a94200c84482407000e000c0540c54043c91085a502000c1c10039a28071051161100d400d40007030101060710402c1c00c0c401c1b00c41e5041c8004486842000407030f800e41081351040850000e0504030000c066400807c105201c1c3e080810802104040884041000881c504414405035015402450304810050162142c00003400354 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 531314964 1250 531313714 531313723
    0xc1504090204121101020a02010210020a14030f07030f0c090533030a051b030105090402030f0f1506150f0f04030c0e090613031407050a0506070903031205090714040b03 74
    0x10030944100f04910b0f000340b01241450685203e424001000084a294000f0f51201c0e5103082804855a0109403803407014021a402e0341100100320009a5030f1034012004020601c050300d040c000207180c00ca1816100f2420310502080b059640c4030407001e1840c20302040485d120042c00c4d00c244003000d0208168042c001000c1507034070200c001c1c0003626403074400510411902d000345208128504600d10318880c0396a0340c100c87c107644099800050f07a031340d24000b0905d0500505428142d610512525680c05c2c0d02c0400e00c8208001c410f10b0120140e102d001c20064403501050980c48080070802c142c0303e036000341200034010141e0b41030025042c142d8035190780c40c1c0d2840640c8204401c4107000d00300089128141f00d402e510030364031203040c4105400707904d008000124451080d49034000010f08181405030801850358966400000c41d4002c1c0742c10345000b0900b0400b844101c0101d40c0610700d1131083d103918041d8902ca0f500f810010030070340c0c3c606100306014941c1d65403c1c0d0380140d95940c1d00c4400791020b02c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 531316214 1250 531314964 531314969
    0x20f061308070f06021005190504060e0604110a0f0317090d050f06010608070804170a1107090c020c06031b0a0309150507110106290408070602070305100e0c1504090204 74
    0xc0f00b01001890880c020f414014084c56030407805151404000340104214928041e00c080550b00045958851a00e540242600020010305100d10820402080a088250205100f0944166001c10342d120000e00e605819800010000c0c214040e580884043c0103004d001490341c01040c04000c405103459040c10100706904100f8242c00c0880140310302d45d080000c081d080314041c0381c010003500e425140d00004a03d0140d03d44400540002c40d6180903120749035402200c105081a03900a47d550498500180500903090000d4010304c2d0980c0d20500e40a42501d216080b088000700c400b90352540c4440c16940304d03c0912060603501c00c2c8810114046004001c02000b0b003480c00a4170381400d50000c0c01c1041e804c14440b03107aa041400030b0000091448040d2b100440300040c04001c09a1100c1416240c00f40740c10402051107071480000300154001036030002c03203015006981d50440d64944180603143e40c83c9c007240d0594040329156010782403503090f981c401901e44011606180d1500802410390340580d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 531317464 1250 531316214 531316229
    0x60f0b040306060f08030a030504060204090f020d05010815070e2106070305010f1203081b0720030a030f0f0c120e0103271b030804090c020105090703020f06130807 72
    0x81028002c000c0c45220b00400303821004000c2c0605860030003920794a1040d080c0349010162150301003000c004081d0143d40152213a490240425070340d0f50440002500302c50344a800803424230000203980030010a9101c000114280102455503c10000391000d500d008d54807600910058004160074001e1450300c04000c030410007415950400540c0103041c2c03030043c1c1010510300b10b12102084032034001208500559854181fa5000d60364050080c09100070504062811500008000c1d041090100121010048952141000b040b50034141691500c1900006020501d04070111868174000d0f909004801c16600e8030040124095540c0c3c550b5034541403203200400d1001202034115a0140103440c0c1107186003a1440d00040105d5413000038070070300b150242900c4629460183c4405034000d6007805580c005408594882c0e481a00760b00525642e10244015441c0c0703404030b108104041403150407650010040b08100036903600b000b001da480b09071030410700218607600250340b09040c0000001000300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 531318714 1250 531317464 531317467
    0xf0903060c09120616031505030106290705030307271511030f09010c0305040305010509031c020c1518120a0f0908210f070f060f0207021804030201060f0b 68
    0x222000c3c00711200743e42e800c6910319005401000685150340c6415840703040c40745000300c0c3d00240081980e00d15040e6400c0304c3c0c0c055007030240109094104861000500b5000f10340c1004101441070306000d54000c020b0018015002040410b000f5845500101c101c0c5500112440200b5100e0302c2401c821202603000b125a60701030811220150341011075800c04980b0180034618043c0c2001c141c0070f051060541c011f040c401560301e60400d05100c0c1083d64003440e44a402044241014000075582c0d0f000b412000d100b080c042041082591102d00945036411000350040000109240d4030241020300107203080c0c208407090202042c086020400c03a2081c81d86450a140d4030016150002c1210741001034007014408017100801031400002164061000c1e4055029075806c0044544101c5208000da540da0b802c1d404900c8409006074441c1d88841d0601c40d00080104d110402071003130507070164840107540052000c14521402024001881d4407600c42d00c0005034981d01d0380d4014102c0249600b0514180c0740 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 531319964 1250 531318714 531318727
    0x1602061c021602040b01030c02030318030c073f02040b0f04091a0a05010e040f08120c09011d01021b030c06041203080f040f080a091a090102070e040b0c0f0903060c 72
    0x8085c440c207460310000780780034000c20980900195903403201803c403034440d0b00c1e0401c603907010460510a03130703502c04001e4040c0d03a41c035607664103688400c00c4812010142c0c4c0e4104000b1400380004640c0403d4149a0302203031440c2100280c08010082400018654002c0c600c0c01c0b4041c00b0f50784901c1110200c81c4101004a288402011003d9900d40d0007031100e112503181200500c1000701681129520a6010b0420000501070789001c8a07207002c0c2104400f85a0841001d0100d03440d0b91802815050380b083e170341d20320480c200e05690620024902200c1d80940c00644d2145017a20451008840c1c60307101074119000100e4134030104030b041d841580440d08042c1089200010194403689858004000b050f02c200113040c1621480c11b641411600148410343c00220383c4241409204228002c15102c40262104004052007409a902100c84640140601000480c0d2011002081402981c008800b4045c569030f0742152420f66104540c141c0e12003100b8084940380f546d00704a0710380708000410b150380d107a08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 531321214 1250 531319964 531319969
    0x315060617061c030e0d0f050d0305072f0706090f080d0f2d0807120203010e13050712030909050106111b0f0901081c051602061c021602 60
    0xd007401c04000704407103281402425503e10640409540308030612107000103881ca000e40b80c010101900c00c1d0011039903c061002c2c082100003444403940070f2003d4440c2840c0000084040341c800f11604400b10380c56150700d0850208030398151704001c0c813a1500c0100400c081841b00c1c904070302ca9102c0d0780040d50340d5005211100021404500130f04a032001021902c40100001e0400350400e44124100304200300403c816425100b174081c01c6806206003480ca2102500e030080100204540c040042100da01220610b051144210ba0499004020a0445881c1d2492080340304000c00815600781c41003180c0810360003104070b80c40e90684d11a0320760500c2d141c9009d03084806d9440590000342409825984880210310101d04543c20f160580c034043d9058108000103414020613000c5690044071000020500281c005030100c200100c0030011549042d40703400c00c80b86880b42a9411082108520740e5500604110001c2d002400e101100c85d0b600703c40c242ca0312000c90300841c400541041c0340500e80400e50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 531322464 1250 531321214 531321227
    0x40207060510050102070b0909101d040201110c01080c090d08030a09030f090501081302060418021b010b1815040203190f05060d02060313080a0f020f03190806030703150606 76
    0x903d804c1c00500080c0f46407034602401801604101d038000d00c5500006000445010b1410014090019410743c0d59000881c1c20704c1e00714000c070f8040303002c6030031028a01d00510000a000150620582d220003013942c40300b005000350b8004040261300b041090074440f000401080240d44900f805480c001543c010b0350800616204403400c045040c051300c1481030140d40d82c810066540315504410700303000724000e0302c08034001e4400c0b903001d0030350f907401c1c045018028000c0f600200b0711114498220768141d0000d44002d400c031307065160f03040c4d840f00c070340c0c0003a0819079408442998400008038408924103005004030b000d992040b18041030328200d10704500794424140c0310f03a0910102d0b03d4020042c0b45800004508400e88419019200e9000800041c0445204407000107185c0d502581c142d840310340c008009003403a004000800098001c0000003903030700c2c40010a80f04050300c0000303c2c00c6541c0c50002c080c0c0300e10704060b00081e0180510032000c4040341d0b1207000000d44030090400040d03401c1c036050004206 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 531323714 1250 531322464 531322469
    0x1902060c06070221040608010e06031f15090e060402090a0204030b010b0405192d120804050a09020a02030d0b240c0106170706081e011d010e090624040207060510 71
    0x150001401705200180d44940f2050540b03203400d4900103591111030001c2d203065500e0211070400a00200034013034002854014007465132414000c03060307180c0c503410420280c6180800464490303009070f0004000d403402c01c00007500603950140040c80d05840303880d00d100c400e00c00d8005104844c4001010031044c100082e070303840003c202d85200395041d410302e10650620500740051281c0c00324012980c0e807400c040300804000806c044a103170041c181491030103402795009803207014455911a000020b00c12241e00031280003030a5a8040c51070045ca48824400400c03514203e150400802c0c14120b00000b00e244c6a075100c040140355003922101140611402d44806801c0100c8500300e050b040000b611000440a05403103035403e10500645c0c076443c2441c81c006182a0901b024030203040001400340049291155803d00d03004c2c203817400ea889203000d10351590f065940d074690381d01c840c0c0090f088108903545007205a00e0000e040185110040c005000c1e40c02c1032006030740780b66030f400601ca0b41904940c2e10100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 531324964 1250 531323714 531323773
    0x7030212011407050d060f09060512160315090f060506100f050f07030311070c061d1327080c0c0306011a0d1d01020703080106030e1902060c060702 65
    0x41908030400103400c8010f0006401d0181c0031900c480880000d8100101a0000c804941805030340d543c04140a00481d20405004030103061044054a402242890f14401c1c42c15032244440d10b15a10094010f00e901c5907815040d0b81c80c006580040d0034184c56055880c00f400010801341051b40802c00b41250305001030302480204814449800d801c00f0544203407074084044943c54411a080039800313084840c1c9008003810b00014440d08102805615400b606c07142e81e10080d400500108401140300d00c0d40080741d100c0528440034001029a4004829084141442e840445220341c07a004126290703c3e000c441c0b0800102e9903c00c83c100c00c010344050310700c0860003010507500d04050b0b0003d007150070144941c0c0040001d22480d4214146d00050910b05054120681a02c81c1404a90007504401d900303c0014a02c0340000903564841d024904c2022540405044003000c0311044603100600341e00d089070402400d200781c40c4004414800c0270721410154018020808810410000c84c14001d5281032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 531326214 1250 531324964 531324971
    0x10b040b0301021c050c13080d0909060f050d050c0307061706030102030606071e0c0b04090c0f050f0a0903141501080303220321150f120b04020112050103050703021201 74
    0x40030311000110140010f225207200080301c0d164804061250f00c00e0070b01c0098000101d440010301f1410001d5512341070b08142e41c40032b01494617441d0290076524580325101340701310300b01e40c24042482c015803010302c40780c469000c8848020b0300d00013181c144191507005401207081c0000c0421000020349585520140071002103107586040000180719014100300a4220070f0004e01d0313001007215501e4a400801e820440c035002c4541d581e1447c1c5825407050060584007802d2045000d441c500841c0c1a00d4060b40c180c5805003002c022404e012032941201d050001007010500c8000042480415a500c0f42c2403080d002d8081d11102d0043c030281c550042c1e10094141d40100100080c4040b81106204180e03905444075040c00450b041c102c0d007410200d0040c50035500c114001c0598451140c0c441d0356011850030034940c1c0c45a0b520f41c460614801ca200300103550042c071501384005000307170040d241d01510504005285d024090030820803200d00b60070407a01a440751030188158980b0251414840c0d001100a1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 531327464 1250 531326214 531326227
    0x3010e0f070902090a0906090b1002060714030907050409080403020415030b01140402040e0f06120a050a1b080307061e05060f0904031b06151502120702030a0b010305010b040b030102 80
    0x641d5a450354030804900c5940400d0b02c0f6103130f0b641d18424030002c3c050440140052500c4152080043c001401c030070f489600040f2000e59050b001040d980e00c00c1949403101c595450300003200c4100303540300518000303041c01803200110b0b180d661032180c050b07140d0051115a0b00d40d41188148003c59004d07110643c151448040104001000b0b05582415119040000920500004042406030155800505002e10042c3c10030440038840d1a0451140c00121042c1c400842c0d00501e07251175680d00007024005404c00d201c810b000c41c65040e80302016481e00107407492407a980d41d05060031900038001c21038115480301c0c40e20013003492035017000c0c092045061382002281481d40016a02900d90164680610a540700050030306001d40c23000d00c1d4140b80010746008065540c5401c00c024100006601c00c400516080400c02c0c2603400c90030250484590010652490a508007a0f0682c10804089a1620404000c000000c03c243c080e58003c41c41031001045009503d801c00003952441361465000f80c1c41440314 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 531328714 1250 531327464 531327493
    0x321040b0f0610050a1404030609050c06090312130b03010602071a2802010603080409090c17190507090906020301050906120c061c0207030c1a0f0c090301020c010c0302030603010e 79
    0x1440001038842c00e01c4c13035454480c0c0009a654221101945134401d9010a000060240c03035040318034014032031015205048454020403055019409216030141e0000014011507000389000303100b01d03640062a06405995070840b014203038401d0f00318000503045140200105190b10072090001490995034900305a175100c004261a10286503242c0100b101d030201000704c0c0e00030344c4804051500010116036035916481d0b5140508807251040f0f441701c0200c00f00042061000007014140c1d03003008080c01c0d05038010600040551b0320f0780416140c13401f501c2c40001c0d40c4c0c8814450202154410304000d0707120343c901802c11000800017000e03140145040c104090070302002044041d0700110488a0640f150070100009503002c08100d400c61105100180c480c081c19040514204403510420048641e00d45030318114107100380540d12440780c50f00010205503000d0400014180224001c0c00043c02c01010054890a6542192201001c43c4d40041804141d0400b8061840d40200082c000c1c00d9107040440c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 531329964 1250 531328714 531328729
    0x1707080112290c09010f0203041211130e06010603060605090a0e130807110316080613110301021210090603080f0a140c16051503060f01020321040b0f06 67
    0x10700819009907000c420800c0804500419201e502945500d2010314000619000c6540100101404900001d0400d24010300c0001280d043c0d410f9880c800b5030f40500d50340c64181d1507500540031036109500007800d0b1460030084c441c1c9040200c1c600020b01d01940360900280403a2038941000f0104039042082d5012612040400000c440241c0002000d9543c1c444000241c6600b00000804032140005c0e13003c14080c02c02e041c4a2212001c400b81d03192000180c10611070000d441c8504051070300044001041c00f40c405002c0d20060780a4002144450b2202d0700003422039001014901c85034102606104c4038034041214000580003030041084020708585402105004080c1c00b002d40c1880010380649142c881c031011071041c3e40e288020742e01ea0700080341003621420041500c0103402c0350100c1c00079071881d02040c072500109403045001c0ca991039140900610b0001f1207035030303410352004100305401340c110001144681d00e401c20f020411402c1c1460107400100020341518210401704003402903036501c41343e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 531331214 1250 531329964 531329999
    0xd031d150a0f14040902210702070b0c0c040e0607030f0209011d0f1801150201140604050a060b040902040e130b011710181a010b0405040207020d02060a17070801 71
    0x100955040310701d1104550419021007990700c3c1c1c42e400309002030034403201d030042c000d11000e0002e13000010b00c8840f188811070000312802001688083c9013080310241c424010149540c640080c0c03038981d031a410101d8195090450361a01c960f11210821030039035858031810030340c092011419841c00c1c1412000822115a0241c080c8500000c1100829556a900c0d03299182060287c00305000602c80301e55034448410920440c0c0842030180220100d051040c0300301e4600e0521990804202d4480303005110042c0001403002112554a41c0081140315941e40a00002d110324080503a4035410300d5480001594050004191040c51000f0000080c82e1201c00c3ea040d030781324481018540780d0f00c2440e940391101d031851080d0041d1800030a80300f905100d4280c12180c50194010751541035034180f80040000092040301300d160010f020a2100c1d1a0a80080c21503078001002051400300302d4001a49c1584240e24032001704901c00500c04450a14130b8001c1da000390030341011102507141c410003081480741c84 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 531332464 1250 531331214 531331217
    0xc11010b010201050408090f01050405031501030309170a080306011112090a0e06030303070807020a12090f120b0109050613050c04030b45010c09060311090102100f0b0d031d150a 78
    0x3c42c80c4420b80e4466401c5c1c2f00100350050403a0b90390b14144900c0d0001c0d20342800141c001400c00c000c00b0030030b401c5502d16810b84040726801008024584e03116400c4c80d400260400341040500c40c40305110768020003240c031700c0d4201c85c0c450300d42d42d400110400c501413010758050301c4442c800c0000c04c1419078002c02642d900506600340b440181d500c00b9000c13030070701c0d000b01001072459200c0700382e5003007066000d801d920668100d0060701e100251694040c02e107407003003008010071030344030b48006002e00c1205402080d00b0000241911810400d40c90305401940d50844452106010204003007042c008070500440d0020900403000c500f841d0750126094101100007541a10400e46541c03800502d0b1420f041c00004c8601c013070080100c6a80030300018000d0010b8030a0f040002d0820144550b8201c0c440200c5900f588144c0041c041515540b4445014107010000c50403465614010751400341c0f039a40440741207901c2030b501c0d181d40c2c0111000e00748802111813441170240c0300c42c03244103c907250380300106c2d00034500a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 531333714 1250 531332464 531332479
    0x105040c0914041d0606040507030b0f100936180803060a05060d0c030e010c020d0c1a0702160801020a051602030106080f010209130504020604061409040c11010b01020105040809 78
    0x169000f24003d868640894808440400ca40c03540c51000412000c1c02020202e8040c0910f4807030311000c0b4180d400c0403114a0740000402d2000425103000314809180d00414202550400e65031101d4009d0340c81005555101d01440c121800b001501070074030511072a200c00c100300440890343c00d10b00c01c101007100005018920020114080380e84210005004007c02044555655544010103010b4048400410b0210b81003481543c0a5041800307004035024195004080300801d001049410882a600079200803490001c11410030072806102c5114814a40090824400043c0e06051103800d0741d01030085070b4414095119600d6100c401c640300c4440910400c110070002e400000d0061032030340e0060f5460302c100e01c9102030302e01041d00a0715141000300d0794125210300b00040354080c2c035021500290702c0001000b0a2003050b01411040d201d0210760044241000c0c252004542240ca180c001b030004200507003003040e22a1401d0103190034241d400e10080c07007241800c1c0d5030815540120144244210312 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 531334964 1250 531333714 531333749
    0x20604140c0a09060329070e0f0414040506130506160522170703020a0b03090a0b010605030a0501081c03020a032003040b060d030f1d0d0311060105040c09 68
    0x1c119603820a20024120800b843d9101c580c0300c0180014441144c0701ca03014030161800c0c000580042040f81680d12400d5119620284221107800190340c00e180d200c0d44040080465444c0ea11070b51101e05d400300035a4696080508016242107c0104107111200e03d1620550004002241040c1c01818580c0081881d043d00c0e08259014016400700c08030300700031000030010003540042140101c034085400162184440240c01c2e8a0f51114000650810703c039040410400c88048002c40e400352416055504100c1603a661444c580c40c20707405940040c0000c400e2104050b81d602c00d1900400121004140e0303182c0d10031200114285008542040c0755000c1000000303103002e608080c150b036440469909400c8211001c00d15260400e440a803800744044002a80e68100400e003c40340a0301078481c03210204071010215078107000c0c3c06034102145002e440440d07268844248070780200e84261642c1c12441f0903070b01d165240c03000590101d0320903030030080ea096040d07410040e00700a0321a2400741c40c00b100b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 531336214 1250 531334964 531335003
    0x8060c0712110d02010615021b0d141c030522020f011e05040305011a01080a1107020a03060b1305061003021b0703080c07080d050f0a02121801110a03020604 69
    0x100b40c50a424114022a40b406824650644c0801c00359003000e41019004860b00f82e04a940f04030000d4500c3c1500d41c0c1c04417200c003c3c501850410500c500c03840c010001c12462001d81801d0003100c0390442c0d84040d010022055a0b501406580d52184122107120a2500c0d1040750094518840d200640590903250803001d041c0d20034042c1c040318000105034007040c1c2e03408020040c41c0350702500c402c1e100795182c0510010000d0401c6003004503228140d64010780b45d01c8014004005042048005003039400401c546001602c3c1c00c80d0010003180a6203000441c91074500610501c1c801c0c2c0c82760104154035120400410b17031f441203001c55608600c1c5c03400584501540c01395160102a01054808038811950000104840f440090021425a2040e00c510a5448900340d07950080e901050f00810030130301040400b032000344050150715800d072045550350504180c842482c1c4e0b1285416220ba0701c1c07000d2051186581268002c0701d41030480303000b800d01d40c102e40c40081d1104400b400007003c0c807180103c0e610301c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 531337464 1250 531336214 531336227
    0x801061b020a051201090212160e1501050a02011e02030a0e010c0f0507231c140f070219090506031506030d0503091c080106140304020d02010315090f09060608060c0712 74
    0x225400f40908501d602c009883c55550349c2512410301902d4004400480c80ca00160700f500d0144081301c1c038941100b90044015180b6030810003024013199600c9110310030301d800d01000d910300103010404c01640d0f401c2c20543c50054400102207180d4a0381059402141070785d20110000f042c141600c1c01c1d0782c5500282c50b001c003101e5240c02c8406402e00300044d51000281011485c64010004494407001018450350282d42c0000d4988001007d0607046c02440700040286008102d400d1009000341481c1c400641d040c50050090340102d0205136031842000700a0508028000983c40c2d21858400d0301d1500d1030000341c0e20b0700b500d60841c00700700c03000c800b0035807550007040464107030002000c90041c1d0785983d0000500040b030910945000408844141c1c035544000012640515000381c2404507429480c1c00560242081294550b048030302c4020008402115210700d0030704d98010b440100d03070140e0318103004c016600e05400c821800c0c0c21107000e01c6490402e59044a010552084910700f20094008041d41d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 531338714 1250 531337464 531337481
    0xf040f1103090106060305090f1b0d050102031504060b040e061e0d1a0604180b070203090d051e060c04090b03031b030a030c0509030a2d030801061b020a051201 70
    0x18504048188442c1010640007001622172541e401c1006559002a03550380c1c0c1b14030140d100040d04902e00c468a041000c8800000c03c41018004101a103101d5882c1401c80e0f004031142c075403000d24680e0b243c070300b0f02e4140545070090850440041c1824242181d5403038028000c1d00d0b09102e100c82c0300000d10742c0d00c68580010103001008012140301380581c10148482d40114120030044424800001c0c02460203108501500f85035400c6181a0011580c0395049100050246420744c4003d101c0b03100340396100c540007800076105030082c20110201da00c812020070000c1d021108503802400410000361242c01c280d400b1201d5000c40400c01c1c03030741c2c2008603066120380d4180c924520101c2c05040c0200e00d00000400103c2d20031798040003001c4007800110f405002b10651154103070003100040003c070302403610070840c01c848500b0707149001c5042c2c2d22003400e064080c4400c801041040d00100807080d00850f90084d030b0f86c694200785410740c5c0740e82c0c00a08110142d001d8507100e0701c0c82440d030071040d010941c0107050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 531339964 1250 531338714 531338741
    0x702030a0506040f0b0a0216060c030f0c05040812032a0403050d0302030f0f010312030207170703091d160c08120108060a0e1204060e030f07030303020a0305010506090f040f 76
    0x42402c0604107111050b20910b010707a0b540b0070706804640c80e86c0c4d042c400c480394580f0517007140079455075940d030300f2010b130403144001c20030507440e0141205071104510810151074900e8448950310b92a10390307074604003c01980b40f02c540b040103200b005540c40030b028007034004030340000f0b425040702d00400c2662000d000310307040541a807203a1803c50807407980640c010350061580c000c04500941e03c0090241c00d00000740002443c02d002a01c10038203490007500074005140c4503020002110f042c0400c0700b201c80e00b050034164005a1031860811410000031a80f440410144c0c0a656280c41c00700c5c1200000041a0060740030086c040c1c1590051156060640e10020b101803480c1c0c0c225650703000c14a9070b406050f140e40c2c80301d45c41e0410340100030701c001800900504540d0030250800d0300d005c0c4c0030703038500300c198400365014080c198445c0200c107000d00c1b510000c0c52285d00c005072202c040910003030032070700141c02c428040c0344200140001c5640e00541075a84940032540860130b00207107243c42001e400c01107107615 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 531341214 1250 531339964 531339973
    0x6070b07080105010e040b010e060f070b0901141e0f0a06050915040f1a060c0109050a050a06050714030a0b040b120a1205040b0a1b0804120201320702030a05 69
    0x403158000d41c91030481c0c1d07090380ca1008000401c4104000c8030750414038240801c5014460400904000c00a41703292101e00c1000c80c10074450352918400c00204035a06140e69661380d1004105100e44943c0a42002c20044864160601c0320b0404c00fa0030400f80030303103062040c0d02d000524401c2650300b00d8030182c803000c0d100b4081400d0036021800f058184000140c851414481c81c00e2035042140709800d061204445491780b090000000d00405a209640541d000e540700d0040402082d820001c202030b0320321030301c0180b100d6642420301d041250340c060882c0701000303110568000840c500038117403030300302000798000a5800414400a4002c1c1000a107458000b4030125981c800c103400403d2503000140910000c6c15458100f034400c9400c0d20990107140c4540c10b05000800d0242c1c460011190341a01201e8800d01c0c2e00c2190f201d01e08150480d90044241580b021042c00c02c6507031044518420144ca004140960f91301841c0192000f10700c0540c40f03004201c049038007403d5590070445180f189030098241c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 531342464 1250 531341214 531341221
    0x30403060e0a021809010f15052101140a050105012309040b10051308030703140c07050d1103100e0d1b15241206050a090210050301080c010203040e0c0906070b 70
    0x1202d02c0c4c02c4451071030780e520380030040c0007041890081e10500d010309490450114200030400c8403e0100300d05000009010b07030144180d900b82449110300780d0005c0c09400c2c46500e41a00b6803005d84030140c00c114104144560480104541070036000d20907d084056a07446000110101c1d0040c4070046110780d0150300c0014680c0c030345070000004c1c0f113407a1000394481605600ca20103c0c4e900d11076840000e0000e507411841c8a680700c080b601600c0001c038000d0503100b130302c0e50f102d0011b192074440303900079504a070380b0b2507001420345410416080d02c0101514140140b0310136282c401d40350304440d146001071081f60440850001e05003000c10090b2540416007480e500070031809040100550440c0c07488004d1181940d800c080380000713007002145c8003c00c50502c400390581d07905000d0300024204081003600c2d02079900c016a103010f001c1c010b10500d560b8081d101d40c0340c1800c170351410030700c40801410740d04200000c0c0000d40c41c0012040d80585410f295564403100a8003081141c410070002030718415094060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 531343714 1250 531342464 531342499
    0x209090f0c0c1b12070e2701090615050f010801170109080f03040c0605070b070e0a0b0a021605120601050d02010e0a03030903020901061707080718090609051503030403060e0a02 78
    0x140e0007440c3c1681c408030313015144404569905d90b180181700c210072031603002a0f90603440c540340c4140501d40b603081a07520f09001c07106509650300031074100d45c042c1e101d144100300c103550118890000d00b000c03104075056425001c0060f120f6036040c0a2100c000400c90b01402c500203003500401640e0b580320601075500d000406812a03d6001507a040b501c0e001c8014001030300d14456401d071100c030703a00000c00389120748808000359403100809144075002842c015002504178141c0019117444010782c2c002d4424842c020f10361188800890b00240e101d401c0d01d0f440301403407440000e005410748406813440082202c1030300050b00c00e280b00340d4a4075800b4001801c040101a8041c001c0c0044a01c00e039105203180e40c880c141507494007000e00603004c0015907080007420f09407081d020107801c444503060010009506204540c024405c0789c00980f0f6440d143c0d80100300344000d6200c0c543c1c3c0300c5101c4404041d1980c02c0d0740080e45900c598400680f915444401c02c035958041800010395060f4010030462012015504 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 531344964 1250 531343714 531343753
    0x1d16140f0f0301030212010608030f0a020a080708180102011e020c07032312030402010c020907230a080c040b0f071103031c1b2708030c0a050706030209090f0c0c 71
    0x3041b40162044070807400d181e0014003640d81910010301c003850401c490444045180c4d04009000c108511032400d40b80003151804000b4050344e03008103000d90ba2291569040502203d01c4040503045a14003400035240c1d12150103c0944444407600250356004607070459460b14200d03410180c121321054003c02030500e05050170a800b40d10034415500c14483d8207012005130702007264081d001c80d040810002c01460b01120140d4012040c0c1000c01e03d4070070183c1120018082d0400b001c0e00c01c5400200500090342100e442680031b00c0b12040c003803a0a0412182c242117028465402c201400c0100c1d110081209144010840703100c060b049036201d2101141465805d0072420b18810b40d00d03d4a00304007440001000a03110860b569101c501b0004103006840c48101a41084070024203e281d80209060318144010041303022004010b102103001401c00b6810310510b5440742d801c1c1481000149200c1d00c8200e070711640b09190340c00c080302d6641c030181103880c0c41c030804408644c00c2c02030000c00c1e088001500d1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 531346214 1250 531344964 531344969
    0xb0a020d111e070819021008071706030a060f02090102070f05240c0d18061806140c030c0a2a090c050c030706050a0b031b0f0105070515011d16140f0f0301 68
    0x1f00d022a88220000b03054a0130b104c15910140012204044441d200120381c1407180c0000c070141c111000f4980e980c841c10102e03204c50490300a4250001a082425a4100054006818840304901e841c5190900041c04041030185000700c111140403c011000d11007003da030000c0c0030b0081a540d1141d01c095008080e4041c44050380b035504107400c00420320506ca103001480601c1200610350401c0e04209003514681489a00210305803810051680d02490a00140a164030381400030700024901d8500500c0c002070441240c0c1c10301c48164a90303101c2203080100b910840d003440000040c030100300b160031145e601c41d00301100746511001407a0350070418580e00c414442c4074680b004124001d801000c04d515059848450000b2441200204085182041800c10f0f8048141010f91600398035560b95810841308041c09a4101b200400400c900c0d0001208840800071041400c00986401d500b2004401c9c9607074144030800507071081000700d4040010441d04d00030501303151107481d10b01144030010664001d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 531347464 1250 531346214 531346219
    0x5040f06030219030e0111070f0515040506160e040207051506030d0f1409040c050403050606010215040f141f060902030103050c011b0b010b0a020d111e07081902 71
    0x1800094510300c02c0c820b0310856114a01004010800e601c0304030003406000340740708142c1d5070b03900d541001071500100419038144107448a04001e034413802c10a00700181d094400032810191800c00000580c0469895889050710040c210384200410088030214400e0320301070380052000444c3d50a01c8000982135802000003d1914050b40d908002c2c9034442540c0003002020401100d0680000b074020124034180d02000c0000c10300b03204049000800382e0340548040300104000080600034071005100d542c1d4480c40030300042184c0400c1d00303051042000d0060001d01202d0141c2c41c08410020002030a800300c1d0341d000101d8410071164600a1010860b2158020741c45140c50380004001c0003c0c02564100c0782c020024011007603088005598101c1404150101c50039141070000c00500302d484100d001c0c10700e078205d2580b00c4007080c00103441e080a00d101401404103000c9074084100000851456405819400000e032142d19070780e07181381c0042504054020b00841a5030049844c1d9050200b075854001c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 531348714 1250 531347464 531347489
    0xb0c0c190210030b1c061407180e071215060906090e070e120706021f0b0306073507031508030301034814010203030a09060b100504 58
    0x8051600344110908500035000311825030b002c10841d0103584510303d0000003519440e00c2100340f1301c06942c04100540220b4481e69100007a02d02e14084500c101d9001c281403d003c3d0203148051162203110000784030354003101002100003503a483c80341c240d4284404203030900b80209440c400e201030342900180121000600320180020300284200c0602d01206c000720055070007a12107038000c603410040d40c4a620b070041001c0d070030180d0402c410001e410083c40c040e4050007107140e01142030100c9007030001034807500a080013031201d0150b501042c003c0c3c0245450401c0541a02d1000341403102c2841007440501029a9400c0001e0b00604a581035224200a40c0d0400003c28042d801c144903d148bc054900c0e141e00600040c00040c85889056260010f0407032469000c4202ea00c3c10910381c040740745004c02c2680700100c012a03807050302038024040c11915000f01c03d01030044000171741c1ca000c010104809561244007060600c0030070f510032884848050b1214003400d000b104043c2c841e83c001e101e0000d02030b40d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 531349964 1250 531348714 531348733
    0x1106041a090f0d060603110f0108040b040f021018060c03050a030f0e0a0b0f060603011d090106210606080601051e18070503040c08060105010e06030403120606020f01140f06100c0b0c0c 81
    0x8c0a0113031a0794a00144c4900502d9150340c7c941c0101040003c10071292441101000c5015a803419002c1c06191700d940c1d01c80b10035800c2002c81003900f840c664002070610614200d44070009070004180d0701c4103001031a0004080300302e1482d5074003400420b40d00d0040c9009401c0c1040a118529a1081c0720701400b0340300d14660f899120510a50340b01c03d100d1942803641d402d0000c054180c5061103641c0050302e02c0e00200d011a15080410400840b000900040000c04083c507003c000703150280c1c40040003548058a0075600d8071000c69050994112031504960090304a60400c0d5200c0402948050901130001d05514080c10041c045038801d550940b6108541d81c800602d85000250b0503041e41c80c1a9540500100000305210090b000580f084041c080165103841e0007401e80d02c140d03030090100e0f9000b010740c00581d4441a0840da28034042c080a08980004c01400f01c13045514248c001c070069961004066035040300315020a600000180020071207024020805c0c1d41002411040311a8419112040d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 531351214 1250 531349964 531349969
    0xa030207021503011a03190203010e071b030e04020a02010608010212041a1302100e030111220f03030f020f0105010b1312020315060d0b09010203041106041a090f0d06060311 76
    0x244217030030381100c850382da40700c00d0842a800746030400f503485003030500c01169a03030b0002030b0380090300031041c2c8a003140d00700624a039100203003413607901013046a99808080307500c00a0000c1c4480320302c1406960005103018806100f58040c0b001032200c4402107407a04941c5100e0700360391205490a54410142e13841c014400c1410071221801102803807499004581079900f400369400a400c0c1d0f05060058100d409101030b20207004d02c40c0d030503102c81103a907540d6061903411110601145110036410103801000c0c0800c0202908040940303415040c10424035980c00e0040f841e11407107080a924a5003000000100b41c02d40c4d0014200e15a0401c089001082c0c4800c0c00801d048600c82c8040c0d0b065021603151280b282c00b83c52040d81280015041e5044100c0b03903180c2c6051450203940020340c0341c3d400001c0200340940c0080620304c80e4002c80d50107240034501034a2007031000407c017082d48491400100b40d1155540c0c11840f40405c10042d1074800d18050398101031004141c94401681c030000605000085407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 531352464 1250 531351214 531351217
    0x3050f010e12030a0c1e08010806130b010b2d0a030b060c2d19380702011404050a0218060a0e15030102070b011508100b1602060a0302070215 62
    0x220b215420142555100101c03240600555a090414030003c440098034403041d5003400d9140c24010f85541c840c0354507190000c1e15040d40100007103601d203000c951950000744002103150454110100003078a40100140c1d20f041545031004034021002121250701e010a02d400c0908072103441030710104a1000c22205000705880f03085060a01c0380c00210300b48048410707503c000b050f00c0100d4090503480d260296912441c002245015540d911080703180fa01c100902e03108501642112603015044000b40184c00f01600009000b41c60f1501e5a40302c00119100c3c03007580040000707201341a40301c0c3c9508241c14540d40750100e445050b80200103601f01c00b0f04411048043c24001d01b405803015284600d0300e448850090009442040f10403c240218150350707030240007030404c55003d200e56802652401c1261102003d85284d400f083c03000785401c002290041840c0c400840c0c0d610700c0c0b0507039204c0c0900030441401007202d500a40c008008a49110351030340c10342c080c0140b24425035840040655031010943c16 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 531353714 1250 531352464 531352483
    0x13081005010e0115031b03060905060411030118180c030311120904020f07380c090d110901090203011409012103051201080a110d150506010c060603050f010e 69
    0x501180004115528184c4600c0c84a90781e10324000801d01840320001e071104240d40541d400003503c0e040301748044000e40c4502904014100d9007041444007400b2111045d000520401501000d5260050402415500121880441400c642c10f0b030310301e0703458100740000c3c0500003076001814103004e451000000140d66400104603440990520312080d0400000c1d42c441c005040c910b810030310903a00041d11303241d0740c4100040e07d001304120740700409545100c4135440c003a41a00d0070040005020540d014901101e02907482074500c4142d200b171504056080b4a1000382180d04060030310300000d4900c000303901440c140c84040250071102d1b6518030420409200138020081610039003054200c0e0001d03031618080b6018402d0502d03504110003220892200f0401341c0c01959140c00020508041060034401ea801521044452005051041e00c804504411020643c0d81d034995400c0458030680c0a2904007000b0340d80618144405500d9140440c1c0754030450640410350740c00c00304541031070400802c0102d603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 531354964 1250 531353714 531353729
    0x29060c121c0b1f170a09060c080408030604020306060c0f0a0204231303030624090501092106020903012c0a2402131203020c0a210204111308100501 65
    0x2074188443c1818860203031286024010700805207410000c02400301d024900c10410345030006082542400d0000039644030400d40020404007030300300310009071000c2c1502e40010041c1c40050b00c07580e480021544a2050303416800c194030815045c0b20600b60001103101c485031007a40c0a20201e003500541080a0400403401d880e400c0c81c00c03000500804042610780f400b18041d2401007007003542d0f0083c041c1c0e1040c01504150560090200c0c0e84100c913003114600c4028282840c001c2c04091a1001e5100c181000803803014280c0d0f0302440802c01c0c0050394041d502800f400070020001800f0801680e2000c80d1840d0030b504004c5010000c498200c8004140c2121580c0c02540380111145c80750718140d5a01c1c018a40401265403e00c44000307645070030300341107020340902d0840401c0714442d03060103031400c420081c040c0c0c0710f02802d0348288860301141c90600c03c3c00c6400089200c0c403018620000e4040c05003000000b201150210705000f40210b5041c44804a600070001c0e607c00c0205800410700f44e41d006d0142d443c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 531356214 1250 531354964 531354979
    0x5070b04230c0a05090c0403060e0618030f03040303020c07030219051c02030316062c0c100e040b01050f0d022701080114010e0406061d010329060c121c0b 68
    0x50b4201020800e9200690740383c958906601c9585540441d00303cac002c0d01d0b043c0c1d070007a000c104060000358941010240210001c608210800b9441321051000800040070140c010071804500032041091034091607000b07100c280d0782d080658083c1807a10780c038401c0a00c2502810202d0f030004c0352440c41c070540c55402034007852038041c00400700d107035040c450102200d503d6550451402164030848402440c8200c180911060a003045496854860714061a603c20101204100c40e40e13030b017084080e0302d048825034000c02c292183c9030041c1d40e540541188010360782000103a500d102d01d034030fa006103c4440302c48101c40c0c80030b0104190314003200c3c006d0b4606006c07814400041c4404112030928000056051403c501208003c5001c43d09980080d030251012910340381c0c1309a90038413003982c000c80501080c41c5c20404442d4608501044080d050000c00d1600c02c0040c2c0b03030b6204d8913510110742191403401d0444651440580c3d03500340541c403480110940740c94503540359181c2c07e45401914200d500052060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 531357464 1250 531356214 531356219
    0xf1915030f050a051507030f14010612060b0f09041b051c091b0e06061e090f150706110306030c150912151003120503040305070b04230c0a 61
    0x1208900701090302035425214101d1101c001075001c03c45039580c9400900d051516040c41d0001505407592102102c1c04141030082c280310118403014403904680302d515040c80b0b00c103024084000240459048154a102c000507912000000400200300c0113001b901c04100f000211040611100c01c250b903100001039003082840290301c0c1821403402502105a000503058203a5a100d500700381d40d1004404c020145c902080100410f201c450ba43d0010054900c1890414128002a440c94141c010000603000105d8281207544894032403082c443d901a00e801d44a141c0c0e10000e8125401c5104210780042c1030488010030f00703a403e0140c80c040e01028000b00f44041e801c40c20041c1000d11000031000c001018411212560781740c4008070b04d03072241d4100cd05036070001c00031a0503c041c1c000302202c0444419000c2000001c6d04a01010020251854000c1d225240da00c1c003103034140702e02d10b07007c2c011000746020f100030b00500041010000c03030360711464000c90130b13202503141d11404401030140c0d021003e80f604 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 531358714 1250 531357464 531357473
    0x8041208190f0212390909131e050d1d10121107050708060f010e070507081b0f070b1602060f040f0303140310060e180f191503 56
    0x10030400c0c810740e001508000461891504011040744d0f01d8000c10036000d000f401c490205840034100c0c115174013030071003441024200702d0090b00c1194201401450300030005400f546000c00350f45d00c43e90b03010113440c11540c44039100b84101074550206644e180180516074002c0da024004400941144008660001c0031010400000405c00c40c1046e09000c581401c114043d06584201000303d007142040c151103400c142407080c6801c84a0b0041c0341c0d540c0c40b1806100e00000c0301441d007811202d000b5030b0703684550784900040719680200c4100520b1032038040384516807400c1000002d51a4216002103594000c40040c02680d5544075200e0800d0302d82c4c0c10891120205241d0082c4558940007a04d80d80c64003a001501c103a80782c0c010ba0000313240642d101400d00805502914255091009150290031400c02142c1c0038a580241c0c4220818044410410102525000003400c1042e0702e00072040c145190030814050000801c1307406a000b145c00366141e41104090b8800c14008010350032a0aa2480c2580c0c1d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 531359964 1250 531358714 531358721
    0x111e0108060402210403031e02040b031812070b06090c03040f0b070207170607030b060408102703110d17011401090b0301090204050109051806040903090909030804120819 75
    0x210038103a06581621005500c4d101030742180194442c0d900042c80e10304802c4c60b02c2a69510086c015030343d50040008004052210060b244c01c031001f9140b2510120303100c503c80f4545600714446000500021030740b40140b2818003d40c40c825001035a18920a943e8950407000a00c0110b50080255642d506410049840008041e80c04112030044600068a078040c03030030825502609007409074000b008100401c1d500d8018015101401d48655083c1414440525102c0c0d820f0a8685400c41d96042c400706245441340804007a030645903180303032050459080007040c81d2407808002d1024440c6280d0714140034841c4120011101c0c0d2448801e116900b440c03941c0c0414481664800d0420800400206000d0060b800a5008101d408001a596480c00e8000b500005490b401140300741c82810b000700d880d401710201d0706d511a00458000502c3c0f00981b0307095a001c0e00b80d42040050a10f402254400c00d40c004810501560280780c51070f16107204440215a812800c841c00344100c0d200008031004d0007070582 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 531361214 1250 531359964 531359977
    0x10e09190e03040b070c0603050402031b040603081204060c0527030c030601180b0312040e07031d07050325051309060f02190c020604050112020c0109111e0108060402 73
    0x12001c034144004241c0540b868005412100e0200000502c0d2010052903085000007800e940c18103019529054000070b803a00e41800c442890b50260659906850f69264030140180d40d01a81c203a4684a0103010f418a001c4111000c07101365281149000903a4011015181c20035240191484082641c004841c00d4070403850340c0302d4251151010900d0b0a43c3c0a20070b45010f803c2000c6854200d440040c0910181d030410403685010b41c0000402500014007078007210300f40c2e000135000e010700d13440b10f00c0200d00510440100111795819008001c0c0d0816010841d0b80071034100b281111480b1420350f078038050a0f030b00300355052080d900310001000302c2c1c100108100c0d40c0300c42d001b1002a02e1005500d9403803d4070f42150b0300000c15070340060b11114482050401c180d4058041c681707e00c5141641e4003181d0540f05d180645418444140c80d8400441300c540c045070611030600c1c0007800901780501d8003201a1000246140c0f10f40985510707581203900c899064404000142d44049180d210801031000035030066 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 531362464 1250 531361214 531361261
    0x170a051b09030f24010b04030203030a050a181806240809100c081006300b030f0c12120d0f090203061501080c04120204150e0c09040b010e09 62
    0xf40740301c045810710203074526503112041910003511074440c1d11080003050f0841550301d45c0611090025840004c01c0c1c0c1c40350422828014ed88401d000d50a95620408420480b0110043e15021400c0040030613052814800d0102c1400f42d07949035005510050f00d03101022b150040f49402d0001c00b203115609650f007007003400040c0d5501000700103101080d20000075084012501d184248403028002070490300051a1038545050403540074101c0321545103040512080100700750300500c1d007131002c40c0c1c06410700c00d43c018201c500010b14125059140d120708115a8801ea0814085016611010851891706000c1025080c58603010000c0c0c00300514002500c103d01c10b030f4070f05400005803010044240a40e04452100110f081040001070051030004c1c50f0030840b41051200300252031019400b11062641180d02155280181001d81d40002c07040d40f024103255020010b100c85944040e008040c641c00c26503061216400f11401903440740703042056a600240c55500080c18000325101c0e0b00203d0908 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 531363714 1250 531362464 531362473
    0x70218220c23010215090f0a050105100506041d1f09050a0f0e0714030f01050c040303030b06120a150504060603020a02010b030f120a03021207170a051b0903 69
    0xd8180480004000e6000700c4403011180303002d000d00740080604499a01e0400c1c00007078a0000d140000f0b40303500f0380d140c0d21400d04200c400031a09240e024031025140281801c115101c0749030b18103101c2d000c2c0405490101c000619940082000d06101c0c08880903566104034648140c0c1d03002d2010b15060300d004040101004d103a203c00c04440d114464010700410b840c07080404d5900b0036020311022501001e01c010b12182c41e142c68080040004120b01048414603e000701807a0301100c08241002c6e00b0404081480d4a00740800c6800b0103440064815280643d804000840c0c8681c20f000d290321030111400e4221005100082e4040303081d070801862940824040d2100540c0c440208050700c00756080740d0040381d00407a40c0c0301a80c0d0309105101c001c0e041100109480051140516220396001070070f903135140c000290701601c060103901116609144075855030302030303c3c201038001c011200c0d910162680101c502c020800149050061500802c22011051030300500402c40040a5000000203a0980107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 531364964 1250 531363714 531363751
    0x40506091e0a090f060603030f08150111120c01050f07090311040b0d020d030207210206040e06010c170a08090606010918060b041212110c060a0c0821060402070218 72
    0x13544188031141d90311814021480340e045140107400300800d40812420040403200f0000c00d01c20b2121a00817409081c2020b03032401c0222118103051194070300c40c1540714000080d490700040d5055010307900c42e82c0140c12080f03141c0c40d8180112901c0d909403001402c03074861b85426107003e1030981e001031311400006004002d15222680890240740d0070100c241e0240e08420303000c000e50140030401500114400c10105c0049541e507000401c5d42c0503a018103a02200040c0c00a00c1503402518540d0780c15030084408070f0211a116016040d550010319150000364690000c41c100010000b9102e01510050312a12541c1d81084403942c4030381d40a1282010340e42d290040050940d40220003071028181c0092400701002060800da0801c0802001200400020404127a4240404100340300d40000480d034041c0d5610803400f0440b54035010030030181ca4404006000180c211441152102d00040803491500c540e8a840812089020301080a9044101c0c80764594490f0b040c0040a0380c400200d00c420040d210303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 531366214 1250 531364964 531364973
    0x62301050906130515010f09060914010309140105041a0f0f0603030f0f1b030a02060f13021503150a180504060e030406021e03040b042102040e070302040506091e0a09 73
    0x50007175640d81060034040340b070b50485580c0b11054281001490500c40052407800c0c2c03000302000d003a4840d20f4074054030400c0510141e0710030340001150a070441e24041d010080d640429000b440191400ca400718448a0b01071200100c2c085003030300c20640340c065072007540c4e507110035008014401000c0c0ca502d40410011114841c15860140028102e5010710b0343c0c5550141018000555283c043c00c0150340c800e100c5104216130000342554003505034820601c05454070065003440315421a0000d52000c1c0840c032056401c014038000d144204c0b00e070f034019500800e5003c1440a00900e900403080b6802c4c0100280000380c040b50001504144035042c000b800701c0c01e0440450442d006a0400c44c016080104515186000c02100d0034043c02218051440e05282c500032101c0ca102d07134403540d0400e0400018485502110810946a041d00034105000d041e500911158680b4410300049200f40d24100114000d41030012145102e060000301c1140464020a180910400002d111081140d25160700c42d0015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 531367464 1250 531366214 531366221
    0x5060906060a27060e0405101205010f06060807080f06130207022b0c081218130603031e02061303052a01060314010c0c03030b06120c0706230105090613 67
    0xb10400d0041c030645420118024144540d00080e10320a1f8104402e015080307105041300411520480c4485528900601c3d00e94050800c0540d0001e1051510000048a035007051800e44030b16029a20048140c2c0d8100c120132490a0a0b0b0b1000e41124498684180c2c8059540c014102da60005214200c1d038000412045840c0c150300842514002c0d180c0c0c504010801c2510100c409031501034003905a0394440c001c13180d564060011804200c080c444004001610742101241010040c40c50602501e6142d0401038205c61040709408810311004106003d05440030402d1801421b1090681c03000159a0300c04031080d400c0a5210310b002098003517411054100d00030f1803951913140000103d07050349182010303003120171a0031440300c55905101101e4031055114840861496160400080c102c400c0404114a40075500c40070007030039503500511011000740c002810820b0301c00d6001b03008480100c001285d40a03e02203560b120040c4010052015107440c10f000fa40c41840580110b81a10514459000740e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 531368714 1250 531367464 531367517
    0x30a02091c021f0e010f0306030b090d0f0512061203040f0909030806010807050a0c050c03100b040c0302090607141009081810051c15080607030f05060906060a 70
    0x101c046680d051030460501c0407100008601d648105140301000d100702510001d0303101e40d268108620031480404840c0aa80507101a58006044c001d640c03030180802c5550f81070030507105005c28142e070300d0004004d200c2e004a0344103820a01e540f83c80e03621504140450441840700100c0c003800113110120780c21880c00c19500041084030030220b030102a030709001d40b900c01d0141055040000d81c10400c0070403508034046450045881c5409a4480e115003425030914000c503034039680c98060b0460f4404406650b4002d407040e900101c1e001c00080313600c004107408170b100c0c03080c189410030024400c07807020856100842c81c08216080640d00009940b0f24594219807842a04aa5061010032200c0d070041900c8400045040c05444505186c44c10003406081c50092446d013980d00b66204004003200e0800303810400c01c585074401c4011a89403034081035500d443d07040b203000d00080d1401424002100b0b240c01854040c0c403019005e1384035504c42d502070080580c00904503100340142c2ea01c141035555564a4281c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 531369964 1250 531368714 531368749
    0x40609020405090304060e0402040609210512092b030c080705030a0503221128080106060f05041a0903011d1c0e06090d0f080d051006050705060c030a0209 68
    0x1a11810721b00040d000d401103101c0700d409944144003e100050b000194001600e229600c01c0303e200040c5110000000308800000300b032800303030908d108010b0b603030040039200300c0004688408194018040e000406000101d0a01d4108103514000022a009000008006009101480c5400f1040d01d405145910010f03c41001443c0082041200000021103010340354650250010b040d181ea121805440d241d02c040ca8481c2e0071046501028007540c20046c40d100c0d40c615030403411076555441c400e0003030199110344d0b000315940c00c495049881c0700794100c400f6114050723118840c410411842c0203040d0801c080b500e815642c0c52040083e0051001480004914440000d00725480c0322000011040c800c0d01040090001451241a0070780d504810b83e49c1304102910b00e9024444581803444a00c484001c000e043d00c0c0d000a035240b0400e0075900094840c0c44c04201c4ea0140c6695844c00311114801e220016040e42c00c00400310744d0020111001b9900711000d28400340c2080e03108800a814001e00710002031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 531371214 1250 531369964 531369967
    0x10c030b122407171510020c090408130e0c0c0105160519120515040c2102030c090607030903061b0f030c05040b0f030603010b04151205031204030314090111120406090204050903 78
    0x3000d407408030141c91001c1c01903c00340c4481c41c8d071080419588080508010141070000c109494401001107a0f00000d042b520000c1045003803401c0580103507071010b1919026542040001010016160f218000c9407641b9a9024035044001e020100c030311075070204900c10495500815448000b16002d403c1c0907541d494a000340c00c0105504100c200c1c2e69020150052051100014230303803440c02a080f4101c49020a00980c0c1d0f40d803803106944031486641002c0d83c1c026004030f056014564850152030540780302d058104026890700351450314a03040c1000c1400040c1c421301141540c103120750858894400035003005400c00d41c60341c0703003494150880b04010701c1c64800441000708500d400d00a0814060b01a5030420240113051000c6132004110b001d550a40301c1810000390400c20100202e811116213003551118600f4640b0b001406004620b082c01100551540400d58002062203030700d0303203010f03140301c01131801d4240c548a5124290081c0f042c1d49196541c10180d000d62940e000d000c0c45081009c0140d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 531372464 1250 531371214 531371251
    0x6142409100e03012f07050a02031e010525050d1d010c0e0907050703050a09260c0906031b01140a0509190b07060b060903010c030b12240717 62
    0x40c212000c07100000c003d400c940300340001040d2185e10700541110703848180c0c1d594100c5800e0107440c000300003100a426110341c0e1030b001d4400703034454441d5014001c000001d01403526000011001c100a04c80f611070fa031210507929000d0580540001c00c01031541c0c03000070440807070b0303064a614407504e4521840941d035154000c0070180c0d0f61000030b00300303a6072040340c0440803802e02800c004d01070700443c0c0340201800720024128200074041d030714400040560324103112540001d0128000c84003841640e504151288023204032091401520310782c0700c1d2101800a048110781c0581c071445180440b82c03402d0510040411105e000a81c1c41c00a100c1c02d00d142d140d240d0b4070b81c880c43c00c2c0a281729410700400c800343e088034002c1c071880701240c0490f0392840d000b00010038041602c0300081c500c1d00c55152955030641ca020720642e0b00c903030950405405007008a40c07500396141c030103482985820544150381c0c03460305403020080504e500c6500c1240c0000c051302d42041200300b1100b08a641150640c1c2c0e20444c0354800b000e5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 531373714 1250 531372464 531372469
    0xe0a02210114120a0804050909120307030902010f0201090f230f06040218010b0a2001330b09101704060608060a0204080d21180606142409100e 63
    0x2034981d5503400300041441c0d10713094603015118001c90265034403a2a551010501c00392041101603201e030b21905e00580c2d2814a03141c06070060030104012030208030103c8031001518010700c5400d185d81c1c0c110407804444921503443e6411f4245900380d41420070558110003001c001e0400c032601c054001840200b040341030500401c4a0380c01130b0401040b41d20142c10040c03103060141407d544920000d4100700c0b40390709030138002c1d43c0003c200d0702d40d003010341d0318104241104110320f0401204d03044002c1480409020761035142c3c03001019501540303c4a10b02081000018281140300d01080241842d0107000c44151622841d0410425101500c0c0300361950014010008140030103504510030304011843d2514040e03105860300554400941841101c511031a90f002040e102240302d0b683c113403010405580c00740e1078030448004c0018180c940c5403800782c0114118112480030008040c001708290800401591034954000c804608000002002d00c801c0c1c5c0e0a40f16003806601c0d255490b12800e01c1910803000303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 531374964 1250 531373714 531373729
    0x30a1202101d2b0e01030615120c0f050406080402040209090103140d0e0a05100207050604090606030b0f0928091104150302010e1302040305100203010303020d020102040e0a02210114 80
    0x406418144200c202c1142c514034185910f6485811410840b4403044103900580c001c0400e54494082c0301e0405460340300d00c40d88000e940b6256060703070400f000311075429003046408041d040729060100300200300030b0110901440040ea0710910081001d490b000340f541c0480c0360f80000f0303842103414a440d074100c00400c1006100706001c03100f6030b01e450b244201000001940ca0521446002d005104084a500c00c1c0c6100340409405014003600c880c0c2e80c0c07a52203541c0c50081100c2d110f4403000034606080181d803032070520081503040c0c0c8000c1a82c449600c821004c100c0c84203042943d014200c04a0b503d1681c107410034001c0c81e164900451552074000994001e12003a00c40301d402100b0b14a11480c01800183e0f042101a280040e00f0b070303141820020340401e444028400c2d600098500e11800a1065003103150350019416240300e035080d20240309000c002a4280e014900405220009110015a1580d11a40505a1103122034803c10000304840c0d0b90b04642c880030380009103184104003517480300d800d210070b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 531376214 1250 531374964 531374983
    0x13050120130b030601080c0a0507020301111b070b04060813061406040f05060907030b01031512030f05041a07020607021906080c0406020705040c030b1e03120306030a1202101d 77
    0x81d0043c91440c000700000d01e440c100501c01c401750100810804402d91080082c1c802c0c1e6980a0006c204400301413144370010b400c0b0010b03403800a120a20303060010a001314a002c12100b0b11141d00d414581040030950703155030020300302c2c18441800c05c4580c021607610b0060500d00d02211429000604002051105a859021801110340d04000c14060359072039506045500c020302e490000342c3e10240d240128080d240700040301540341020900401d80742c00ba42d10034840c582c843d48a0701d50000211200b5547d50050b0310400119003200e1009680f4801d0a030010100c0c0d0b440144468a091259800a000c290710010070009200c45503405109041d0004440c0b9082841c040015080a140030b40081da203803041d00030980115110902d90542d21700a0b003244851400c0240b20520900a070700070030b41c08a040401c294428811030801c04024120102100c0c09000082d010342a910f203192201da010701d60a81181e821803040f0321000c500881c203489117243c0545408013100c84142a520114905050700 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 531377464 1250 531376214 531376229
    0x1504060506160b07020a05151f2105030417011a010804081215040e1f0b030c010302132c060a060804110a0b030709050301060b0a02070e2212030c0809061305012013 72
    0x442e010311014072b88820b41d0030456200d5000b440c030020640341140c1580115400011580e07210394841d001c1c981d040d0060741443c100b45500d65208030402004603901e4005070741c050300701081045503401704542003030100d40c0452021124121418200081401c03640c400010210ba50002d05024901c2001ca084504151190340e13018420105c0b8400000d44030342011424605145d80041c5410411000300e92610040140340d515440800b0031004141c19200c21007240b001d00210040042d4540c503021100c9000e4410517503c003d555901c55032450f140e105004240303548110304c901d00107030744581100218814006e541e03130389078803d281409050a4400070741008400d10340900901881e41d9001480c0001c45410241004498440d0b01c0f280c00d5844400a42a2000903022118030600c4400600c1541c0c0100c203a40410400c004128110b030b0529040e145a2480d40094001c9400c1074200c030a4100d6a501070400000c83c0303803080c800740c422110b1010b11034030300d58804521841c0f0b80303110041340d00082058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 531378714 1250 531377464 531377521
    0x130302011802090703020d0b0d06020903070f0b0a05030402060c0a140d140a030207020604030609032d17060f031b03120408070303140c061504060506160b07020a0515 73
    0x1d5400505002401441d500c101940031030b001c09800314a4124400e4800d015002801c0c0b8411400d162001e50701074070b00e030707030207807194031400156250001800b008a1750159022410641c1d01d480c111010340c4083c0040c0d0303200f07400b8070031103061620905c1107406451041407400c2c0c0b2102c1c620001c82c1008004c810103010f002c03101078400ca16000400480e001c40480303180041c5c0e915100e02c0068514010b6420182076a0301c0c049851080581005544100d801c50f1501c00c105c2c400c130f0043d6040c4000e54140ca05001540008214a58182600000d07400020003018590b0081c048c40c04603141400b00ba40f900c54000c04030721541464203081c040404001c910b0b0007214501410890040e9032032619110007420000003c45118130b40140406480c52802d50009840c89401c10345a10351140c0144c9210920079403400d0b2000405141c000104c1340c2c06026880c43d0b40d442c4850b501d680d4041d1800500345c2003580140e102d0080040c50a100b100085045003414101b5810203920304d003443c01000745a81c4142c1c01 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 531379964 1250 531378714 531378761
    0x18062a1407122105072c0f0a090c08061008091207080d060b031608150103090501090b0c0d060e07140705120d061a030103030c02120c03030313030201 66
    0x80340300855140c02d401c615407040000c0d61500864100c0c0f41c111042c500d580f65843c0010030250b42d0b4115900a8283d695144600816860b401c0b2407a500030380c00c6039007180401016100707410310180100035580010100e50f00155551200d00654542c2c0020200289104d0200b00d0f030303032414508103c1040064a446880c030704d8001c0c40c0b04c1d41c0301d41000301840c10344404581e103800c10110b0401c0702c50140810a091113450380c3c07541d581c2003940003035405070b076407403048002000002c9c8514611403081d00ca0303046c40f043c1c030b0303060000540c0201080c01007920b80b9500e40101e200460204030746980240c801010095540100010300030895106410084489811200f4050020780c88001061400031280680d561011903240040c40e01e0700c05200404000c4010410080100480c5d100c0e0007116085141d41c1d03080e20300500c1902d2144001d02002340400c81c100c0c000340140c10b281480107100000e41c0d040b1000780c0017520029295030412902003003500880d000e800b08250f8280a519070b102ca0512880d080c0c10b6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 531381214 1250 531379964 531379997
    0xb01080a050c03010317251101031e020901051e070b0a090c03020f030a0b04051609020903030a03020a09030812150f0102100b0a05150301030c121518062a 68
    0x8010b12014045010740c01d4842c010803458001c0b036000c40901845050503c0844007c070841e0f10050100703440d000e00c220f0020300254024041e0354220800c0c103000f418190040487e820094000c00382050401009000c5840310110000001642003448004251100303c0c40c42d003d0144c3d40018003a0f00300c98244415100041c16407003504066030b90485101c80c82040301c102084c60007401480107040c541d004414401030240105948040c00c07480d428260605803581c203250705074030541c0c0f00303070740c065004108078190640b00343d0140044054515010f82c0d420b0703503500e40e101d40d0782009840b002642004014001504074424000749900001c0e920703c8121504100040c1d11004800c0170144016210310602490f9034503494100040c2400400c5000c049103811044102a04240000c466070710074480701180b103c0d104c000d07250039190301404c1003035040064000140582241055030488050500b6000009403541c000c100c161a102580c40c0308209010540c2415224044480000d20102080340340882 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 531382464 1250 531381214 531381217
    0x81212010e06130515031006050a1401021f1e06051309080c0d0305090c0d0c031b0f0306090611030705090d050c060c03030f060f0916020f0304090b01080a050c 70
    0x41d0214010303121681d07120008202c01240320203282052500c1e15003000a0700421025201d28802c040d03007103d60400200c80d641084950600490b0f034013104030201040841540f10311140c0c0802c040c4140e81404625040003212041d91207041c1c0c642c191110f4140240d0030200104066a98030101c0c14004240b824010520b00f80d5010003545c60b01d038031100a031080c06141401c40b00746004a9089420019200700c00400030101540c179107110b8003840c1240031031450300c1c030b00c581e43c000d1300507503850900380c95039076001c04212a170b00ea10f005c004034203400010700c2c04a41e50a480110300076040443d1180c05841e190007258145450941007501c1442440740d4154010141c607002c5400b0383c0c0f01c07a03054200d8140140303007500500d001540404c4c0043c05001c0c020380803020714050024030b00c031650507480c3c80c01000714440c10001082d8008100c0c1d00003c840d84008030480c11401502e0041d501c1c080c443e070582a0855100b13411880b455501d40c084c1511750b5a0243e5280d60000c0c44800c10409410300c9001e50800307 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 531383714 1250 531382464 531382469
    0x140c040203103b0601092408090c09011205012306011220070317040c1505030106080f2224020c0a0f052802100c02090601030c0504090204090608121201 67
    0x1803010f0440040c0f0035900490019016082128075032a001c4610102030601100a1511800281d00040460000040001c0c09694140e00801a1801e43c0c2000c5414001684031001070341d00f50740b01c41e60b84010110705076451141d07491890060780c0741d240400c0050300110001c0008400a85030101500070002035086021050311008180c656982c841d050444d031085c0f40074401c0e400c10201070b0501003041040c040b400100c40c0781d00f0108085440b000e0003500c00303000921a08001c01e00c400001900562400320140d071001d184244403d150481900b00001524a00b000300ca2000806140341c4c081031884a50b00425030320680150700d4a0b8bd80d6046079101e0041c00e03070043c2000d003015884010044c1c1400745400c01100c40546803580042e802c1c441e8804401c00340280e019500b0640390468480c407514030241c0e10340e0041d014400743e0b228000110000e1020404540420106010100d0042c00d035000601c000c1008207000704107035041240c8582404070324521800030300001c00003002142c0020008904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 531384964 1250 531383714 531383819
    0x1106041203090605012903070801060c14030703020c0906030115031716060902040b1c0f06111c0b06070321060f08030c0706110703140c04020310 64
    0xc00324100d4100341c01401c0103040043c074081c00c003000030813450800000008201e010361510b100b16018001c05910f14842a84e202001803440d00c01407000318040c45a01c440b640c8100326400d020440861980d085410409081b070040e00711201040061800500c895000b1004134020808a500420181d45428151000801140c1d03281c2084884198500a45041d14003000000201500c14505800103081110049200e54540307505003d050400c1c1c0c0d81c041802805d0300c1074119807515071320fa00b1540d00400800b15511a207481c101500301000801400541401c8000202c091050384010025507170720001103401032209000c940d0101c2e610407008034081c03184002c4c0c080ca12000c1201c0c04e01030480c50f088110480300311100080c40c114004014034500000206807250140c890f40704903500702003c040850b03d81c2c07261a003400812860b5200c1010341350b51408480e80c01300c0b10004036080e41c00c129500301200541480030809032154520300c41c2e40c025034140d6190030342d10313404e000d81d480c0c102802d00b0310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 531386214 1250 531384964 531384983
    0x70501030905030d0e160b0301060806041a150702090c0c0618070b0417060f060105190302210105011d0631030c060e061303020135010302040c110604 66
    0xb8030000744200da012402801d400c0c070000b9604c3c1455031390703000e035008000a1022400d0000800d5005002901d040e940182c1d6180c02d2a1103200410000e4140d48030310508012601040c400c2c599501480c4120074504400096110728042c0104920400e006281c2030000c0003c00c500e600352080800c1d021703800281e01100c01407400c02410500e181881c00d402c82c0b400e00d00d00180220b9030900c0c1840b070303e03440c1c0c50140c1281e50a0783d608001c0840f004080d81c4880c0400d00504c00070210301e100400d07000240100746030060500182d00d9284100707000e0b00d00030f0308800c00490300601155a000c0d50030480310852501190411010360f01040c514825565a1400803820014010782c40380b4264084000301c06440140e2070094036400c0031941c2a001d4801c14000c1165480640c81c2401d003101500c3c400c0a0450500b0183d515640054507905c0c0e0400d028500141484d56440c440c1200507400c001d2040050728002c00c56040d072061008480c4084058000d200c4e085144a50201001400992142e4494540f4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 531387464 1250 531386214 531386231
    0x20a1e030c03080d0b04180210110a0c06030c050307080f1801091406010f050102070306021b070e01081b0f22020a0c0b011d0c0c070b2a0102090307050103 68
    0x12200111641000745200d82286000040c00100c0340603002c403c00380101007112226100030441140d844400501407040080f4210004d4507250b001160114458108404094090001c40c0e0030644811011658140348200600000c0e5251150800150743ca003040c51a500341044080d00740c2d84002c103002006501d0400144580c6e402444004a000084c0001e1020176490314200719040100000e01420344618000001c010030200c202ca0100c580680140012505607114600650b0085101483c40120092204d40c080800c20185004094443c0074143c036505040180d82000108151080c0c1d1070100c01c29040e60355901d079a80910b00c00b040301c084209406401c82c4c0d500d40d075082c6e661546006e00c04502480310703a8200c0c1d048181c0910070034000d58180c0c0c03150314400f00e12141c48045030a0f00e4600000644802c403210040160401c0101101c442c20380c0c0d510000a29070006c0721b040c1e00456800b81e84403000c0301c0c1144c0c0e907580c6180e140c002c0d81040700355000f023641e0300c00c1403050904154490198 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 531388714 1250 531387464 531387509
    0xb070203030f040303030f05150d060f0e0330010f14130609021b0a05030403033002190e0102121303080a0905011b03090303050d020d0e06060109090603020a 69
    0x40b02d08149548400544559403030a0240080038421190203805082a0000e000a40b140756100403145000301030905d84402916007030000c0c140c3c0800128003556611181d2a80c440400c064010121a0303161150341100860504801c144001d01480d40140310302d006200a19506e030f0030781c003901c4860340306210080321715000074020661003d500c139000d450721501103440c403c550014000079000d05d0064111070703100c000003941e400c00c0d43c0b0050b289800510080c400640f1860103294209140c0c0d81d200348020f0a8105105082801c10050703103130650000f0021340900100704001500b8030786042459500c4801c030000303525103050038008641c0c054002218106d59804080e50310245030840c0440d500d94610200c050150714082c05294042015101040780e090900710040c000260715503242005585503640a80309a0000d10700100681e800348403a0001c9203403840f5060781401400700500090504000240400c80c45400045d046801c1a0051015884515441080b100c07200d1040f02c0f81010701e0705 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 531389964 1250 531388714 531388717
    0x2060706020d0f061406270a0308030a06090e030c060f1902071a0c040b190e0d030e0a0609081b0307030b01060e0a09270201050d060e0f0901020f040b07020303 70
    0x18510000e524020f2152440c1800d40c1c803100c25100e0403036110100e0240a4104101400b8161042d0700000c420a00700b4031b0070410781884083c032a800762100078030a03100c6d0b440a030300d50402c031944e20401c3d030f942804010000050080c65440e65100c009107203001c0074032230703040d0703c1d02e100904210009048901060085030050003001a00314500c1c02107498610500d4101d0107002d00031503241c3c00701c002c0004600b440e1040340c00c660031620701541d0a0701d840175004040b504c44000c1c0c4035010520010070f01002e1207890b542280e1001501c40d5071043c1c40c02580604100340100f030f035000003040006002d02131002150019441200042040c0c803032003c0e007100710000307140910a400c02000c81550700000904640c20104116280d0b07812200034400548418411041341ca0003046803181c1d10030210310300210104180044803040c0189440c034580381e00c0000c01d80030b9508562100d030460f988401000b007040403094120f500100885c000392700d0801d00c081d0700140e500980c0a0800e13041d1001890b0421580c0400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 531391214 1250 531389964 531389977
    0x90c0a17251107050103060612110403170306090c0f070f11031c080a0902090103020108060a081209011403041a07111504060b1504090f0f0905060601110601060c0206070602 76
    0x4404480d80d90720840002e108411056205203144950003001c9100e43c020f0081d00290f40302c0395164000d4000740c03035410001d880f910054001c40c1c00204004800314150301e00da1030264183e04481662070503c4410310428004c01007090141c40d80a205990003050044100d4500c20f4110014943c0c0e50340d01e007003007203101508030f4900c1d030f145c4111108200000c000701c85000301400d03a41c0b103c02c0b1564415650805030303802c0610080d440001079006000541c0940c402c2500840301400880f002929400010701d00340c44082c44114052002c01d0150341903a000d00e0094140c00d00203100ca0031400c081d918040401d000021640440c0d42020024000c1c9110f51100c105000f80301e802c40740c0c100d9080b80c014010a00c140c1c2c06881c4541810b0260382103040c4414010b680f482c1c10030180b031810b0301e0320b22803000406c5021030200304a0340b58010200c1d501c803d4011000c0840c0240c0141099081400000d0189a03004007410721940140300100145904003024160054065907400c0c0c1c1c941452612500922800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 531392464 1250 531391214 531391261
    0x12010b1f020c100905180907230d060e0c1c020105030c0705061614030f0c0a0201061e06080105090c040504020a120c080109051b071b0312030506090c0a17 68
    0x28251405942d071300900640c12242c090319001200d402d082c00d9480b03c200c0881d0810440da01c2203104004200300854040e80850310300310084040602c0b8000290603000c091410340303000340c03215030442c000c550502011a102404132013458040d800c40c1120070451b0540c0001030b05214000c40050040000401200c108583c0302c1e0945880c1c0c40c065024803804103000c6410000a0300854030a424180c90a0441f409448a2449020aa524901d101d541d5501a408520455407103050009915500c000d901c180e1203103240029070410700382880241a004142d000a103d040b00d94103201031684600100c0d0203599080d034000d41d80744044041070320000407104210084034640603041c5102d640c0300c41a6070503500307441c03007d00103900c802c00702480208210004c10382034003081081000040c0b08584180c409201841c00100d019565210f101c1812508040c200110343c03244200545031904072002a8000500410682018440140140a0031154044800d603445410118041c600e099050340c1004100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 531393714 1250 531392464 531392479
    0x11407110a0b0a0e04020a2f010f200901140f0405120f06100f0e0a1d0307032309090613020c0114092118030604030c0212010b1f020c 59
    0x12a40c4102090b409142c08000184c28a910342030645854022140324605590310f41c0f00b603221807000000030b541009503003140d00e0010840034411900a00840700e03c02621400012094404c40b18900021401503588030004403c0044035056a0000c0f00703520b000b103800300b40648420b4420303c0c0390403922170360304020361220305000010140d8000203101c01000281209542a503103482e03a0f820700b0400503020318860340906440501030040b84044880d031010304c00001042c1d540c083e5004c030003200a07121030581c46400006004080c544c109030225500d400b46000e1285421306900f0702522750040d400c0ca10310030b641c1c04004c00c1c510344c0c074100174246284000c0e00440d44c88050001c003034000e00e00c59525a9594402100040c0c0c00702001c0348000f0b484840a48055540843c801000e49039803003141c0c4120390610758000005152404c00c8107600c12482925294018001c074010030943c280701c1c80c2907801036810f0403400d541c0381e1a0401009030200100c1501c42040c51607200c01c0e4140f900d00721401d50490030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 531394964 1250 531393714 531393719
    0x312140d020d06061b05030a03020f0d05130b010608090304090b13050703022d03010b131d010e33010210090609142a0a050907180503010b011407110a 66
    0x640f54802000c03900903446009580c4800a042da040c0b804441020700140c00c14012810094025002000c0056551950628102062002900b211003d0700d40303131400c0012450703081c204103800700c1a40c003405041c00c100b405450180955981d80c4140c0c064852043c4c0c58115800d81906d075102013030200f040c04041403180346003102c0d0080003500503021044d100405180140d002d0005000e01c1540301903162810780c55607081c0701000c00d80303074081c1d500d20a0301c196219002855001600400d660700a81038040c005075450032034000e041141c0035012240b8201c0305103c40003848103201090710050f0103940d152010504c140d0060707003032103110107522403550f0818a640301009525445a804248211030480790500b139952000d55804d04041444112028041804200070341c00003086081c07080245803e0312240c480740814550751042e1003e00125040200c91040b1801c080040d08c064401500200540d041800000308440b40300130007501c02d44000903481061040014994000310800b0700145809903 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 531396214 1250 531394964 531394987
    0x1107050a06050703050c072127051305010501020a02010c051e0106030507120317040512071a0108010b06090613120312050709060801170c10030f05100312140d02 71
    0x3021100070f00082d1400c0001031082d40d124040c0d4034855007103515141c4103100480e00e403900003500a131500a010340c0d02041510480a29450044901d10704145a0218540b106004d91008080b498040c1c7c142414014009642d001403403500150702483c2095000166090450030032140d05080303192074041c2c03020020395030415000032040f40d200744110798100d40e5480c0c0141034003414050040014055011072109556001001c50b002401103042d141c40d541c80171900201c07503108110440c0e0000903c6a541c10140064101a005006200080c443c10681d4000200c1501c07844446c1807042202048241603441c407071281c42c01074112245800700000590801400d504102c84c50b12004a00b407400103a042c603c01c1c98204d0803030f8000c0e2180317000e03642007954400100c0040c029509031071140c0ca4140741d069485046c0b1080140c00c82d01c00140f00080450620282d8900403c4902d14020f1402c0800004108140c07081541d8110715107082d4200d40400c400003588030f518664514a030000c0303a401d195a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 531397464 1250 531396214 531396221
    0x90209070306170601030507291602090a0501180e03070605010e01032f060904023a02070b0f0403022e06120f03030b0f0607050c030c1c03031107050a06 67
    0x8400c0403c04a10000000400c181e4911003400024203640000108100c1107020780c52520107070403640401c245030410036801c84059003007009900c030250940740e220010b40c01d11809094000c402001e01b0b21040d8104142803640c0c1190b0951136060540d983d1910701460800c1c0240c8500c2c9900c91000d0085503503441c15140c91ba0400e020588488201125904103404e034035100750801c0229528007421040e8410422485410101c030194200c2d808029440d84807074680c2008030b0262f817900c0341901014600f801c000030b082240030301004281c41000b604000c51141d216441e8456409041048980d03110328080341060061825240301c0b01404041050144e242c125003500d650b070150701009a15500c4200c181040682100644103441a517901e0000c64400c1e0050002d0850151464010344a0040402c40035480680300b40e42039002881034000c3c0d07180511080b20500e0013203c900c2183c0d8180110f00c41d11414124004050541d507240d200b4000411001340c408803600801614a60b0308281403d6000e03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 531398714 1250 531397464 531397469
    0x1050106020111210408040b0d0504050f030906030f0a0603080427110313030203090d14060a0203011802090109093306020703030e04060f061d010c020f0d06090209070306 75
    0x50b50030030528402110180d41680d0549840449164456541202100400c20041c02c1a0f80b44101004081183c210f25001000395211221001401e440d10742030550600c84491101c030b2454004114079802a40c0e08800e0f40d8001c003052000c80d4458699100050007400c06600050800300040790024400c400e1900405120b14941c0a148040c91601054011142c1170f203c481003808050011403140544840d01240162107401102c0c41c0c10040030000d4104207903101c084401c9444c8800200c1a10703014040381e80c0100303c0031025411541031440940740031445452141c0c03550303400714840c04940c2c0300c2c1d0292001800c07016010000d003456030806080d8900c1c1d1040e8508189026220843e480c238000843c4802c13070300c0700d902401d012800c0d40d5003210300e41c0b020141c46030f10903150b0b000440c00000e284a018014005a00d525040c640f466035031b003101100d0b480e40d80c3d040c0201c00414502503218134505040520703003165000240e0000d454008010900440040e402124600030003e11a800d540910b06 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 531399964 1250 531398714 531398717
    0x9090a0e0601030c1d0721060302031b240306120304091a030d020a02010e0d06061a031e15010e0102010f140106031a1c02060c0109033b010e1305010801050106 70
    0x5c1600401c0b09040000c0c8280d45010000300d802269107030140411031112603c2c4180345c1e01140c8144c0d2500080e140800641030611000003002c040c188500c0c0420820810340d00c101e400d41e021070720360010b03083c050200810540c0035501094580a0101c018000c070303805070403102407c003d02d520b4211030800540d41420b9690084c455141c10fa54520300008140c11015030595503241a40302150074040705018444007101c8240d1281c1c1c000c00c0240798106040c0980e2810366110340c42e850b0200700311020f2140070101c000900c1207901071000a0120700101c0100403400e007000240b00b10305800407401060f84012401243e032034075050600c0800c0a81d0303d51704898140da0188415980c01082202c0a5000d01c4160740c444100701282007515448012240c019000405943c20030400150035800d40e82010f5045000661400994841c6a980e17a070705010700095585405090361140076030110440354a0100d4180403072000c1c000120b55500803d651740607444542842203580da241d06a01826003805400d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 531401214 1250 531399964 531399989
    0x207020a06020a051b131802100801080d0302030c27120111071506030503070507030611031311060408030a0903050d080603070e09011d06092109090a0e0601030c 71
    0x907000b48000343c02210250802c000d01050440391210580a1400400c005e4100c4402c64410300300d44038a1040c040100181c1d2002103403245644100440c0d0a2a10049801e001c1407100500082c2000140b441c05000103040040c3d581e00c0e62a50a03a4038051900c40c28000804400e982c00f425026007005d00310500c00395402d907050b100184000c3c0c01d95050403ca003108180c10710105000c1030342c030b02d80b00c048080811000155076440f03454250465200601c2503896601040c800c1041000324850f40c0113680d0900380e0181581000c0c80020358101091001500c0c03801a00c400324941c0d84e9000c11603000b0140f0380d0450355905c00b2014040c0014500388400d0f00c442c0140b4006116160007608020700c5050014007810202e81007a1445c000c641e1701070820b40d0750790f5981e288c176100c84008071800f42d40218900f0042c0440d03d4244001403505007281903078a284880701440c6140180b170f840560343d04220403540d000755030b91031800c50f50007030132070309220001c07481480c00000034843d03840030610960340c1840d090f6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 531402464 1250 531401214 531401219
    0x4060902120a0203060c160f02061e1e0405011b02042a09081209090c0f0d06080d03090b0112020f0402220603090b130839070515030423010207020a 65
    0xc005001e0050a0301c0008070501c040030000301000c080c04121440140030301d041c02105400100c481cbe80c003001c6840642000900042c694507221100460310401096452400c0d0801c00000c3c0800300c103a00e042c080319261280c002c00c560380ea802400700305001a41011200d050440301c0d1841c89161507850f00401c100c0c0c0404980a50082074a6078200300820781c1500e002e2111060200d825030040c103001460a050085516405410000700051640d502002c5145401e085a060400d001000034800f070502d0100e0440018060040070341c111032940425400e40001400414000c00801d009558001e00c000b4035140046044005905104840d002403100035844040c25021610807a5000d0903d4550000160b0440959500242840e11484042d070801c8031649400d888803002400b200440400800d51201000d24072491800b403050940c024031645140501084d40400c801c19029202280000080d042c8220600d000607215880c40f040d011800801e0a402e000750001c500070cc6c814808003000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 531403714 1250 531402464 531402481
    0xb030d0503100914040212120a090510050901120506030109020d0b2706040809120102160209071407080307020313080f150f060d15060806010504180c090504060902120a020306 77
    0x82c0200c0b0303020300751030131010749880e001c1040441044885003114410b8003c0b1490381c0010401500122a00340c444188440c1000200400c10202201500c03c00c142440310169682c0d201c4800007503c0c03c80d0784001066210341c2d002c00d0143c1444113002e50025031454800c02080f449148151007109529508000c2e031b40102012051030929203804411580b040b40464040b40c0040c00070205403c0080c4851000410b0581c02d0782660010501404044000d414640541c1405104c040d800041307403800d204456140009a1800e014464029095040200002e0340c0c1e240204100c42e2610498010701100320740d14855240c2e1410710075030440c9035020310110103000300980918640142c842c1810040300d980e030382050042040c500d80d01915805022810b40c580c121a900c82c01010380381c030401402007581010240815500d010000c00d8034100d2940416000c54400c4040b031090341c00502010820362924185800502100c000186d8043c04120054191500000340039400d00d10079010b49483e03039900d0700d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 531404964 1250 531403714 531403721
    0x801060e0103050a11030c09180f0111180a120c030c0506030c2203060c17060307141c0506010b040608070206060102190302030d0617150621010b030d05031009 70
    0x10040113540460a90400a07401d840c0011070718030050100d075901d01a00000540008050f6001c9040350708041407240310010600c003c000101040b002400f101c2c00650a620b902d1064051844898190042c1004660b4401c4c0f402001401200901503405c00d46040071503030303d21140f000b1a10164070034000509400c00c10b05984c41841c80300300c043c0c200004c65944801401c16100500703813510b0181000700000341c01e40302d51010301c04981d032100402028074640c5081c100c005440c451003507000d2041048100c07803408290f4050001034400841e282001c00c0345c0d140d10b03003550320010018052903002017000d10221000e481110800e42e2005410744401d8000c1c0d0b01c0d81c1007520034500680003452ba284104a010000841461007481104c3ca08200800310741c04944058004005011240c1d418070b0a103401000401da428a440520071024105100028a40400000c800088194501c9104030404080d0b00c5981d8020000d803d4508079510a4001403407031340101e420540c6d40800103804115080c2511 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 531406214 1250 531404964 531404969
    0x1806020909072a030528091e09090201021e0c011106010e042307060201050f070809060106030e10021902120c0607140c01020a0206072604080304050c030d0207030213050f04021002030f0a090801060e01 88
    0x15a60f088c0074100103a1802400d800e80c0141c0c10b500c203d80c802029a444100400340e00c1c2c109501a00c0281c03003440004100111160705c07554661f00040c011301580783c40e07a41c0250029031200740c5100c0c14214018017502d0351303151100c000e0980200d50000400701d40640010b071103039a801231400390036502c1c0d11f01643d403140103640c180071650200005101c0b0500079404090000c01c03100450b401c522540900380266071100601105a424101d0184200750701048891503035904084807030b0816404c443e10555071003000f00201c0401075501ea10141c100407880c01c0b20460340c1c4c0e0100139595a2181440a50781c0c3d002907465a0014010401400f4a0031400a9404200300056041b2407262540d88070403400360405401507601c2e02031184440003a540c10000000705110640140c0035441c5140100000c2419207901005410b0401c1c040017240000c903443c1d16401941101d9000c0c0d01ca649000403880d502621035040c25010000030b115580981141c2104101c8540304028094152202c80a0302c14900a2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 531407464 1250 531406214 531406259
    0xf030a030f050114120c1509040c030b0310090309030f060c09050406051810080624031504020d0510050703060f050319080d1806020909072a03052809 66
    0x75101c0da040ba207001d040007008516100c00706d40101800c9000502d240b0b400c00000c0707650300c400054600c02400c1c90300861050701468202080380d14130074404682c8412003440c61441880d034598005e000c05000c0c84600d00515080107687c0d905035140d203022001000f6a42c100404651003840c00601c84c070b00303070140105660001d0422800c00031040c450002c03003003000e811088800140d21001c40c1c0030100b0022948258400d001300203031588940400303212054141e200c14005d400144401400d2502c4075000d40c3c01c5581238841d4040c601244c2002070510860782c01e8062018207103420302c1041c95258000798159401107083e0307240c150ba01c0f4100b581ea40045150100c0480310041e02e540490360340d6014002882e00104049501c0c1307010b0540d90192881d0312070403103201b075000c59042c031641800c8c01400da005c919801c00b103140307078043c001c4a404418082e9803500180710800364001007502c01c000f0354841032091030b003460280040c03200a8035026143c40740c0310002141100001580f101c40d410004413034120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 531408714 1250 531407464 531407489
    0x180f05061009140112090305030118020c0d05031503102c060109022a030d0b0603190c0203040503071202042f0d06270501050427050106080f030a030f0501 68
    0xe1202d0140406400343c1c0103814006412103903e0b040e400390052007001840780d0b490599a40c102402e448441c00c4030a0a0360025205002040640b0310005409400c907099007040c42e01e83d610b0313181c03000c41403c2c1e0024440d0540220352642040503125002902d0030b00410304265001030000c082c00b2180841511481b5007684510700401100700342d94018041c1000300750000740c0c24007800890030400c85030100400855400040e00d40406803481c4980b80503c042180d0700c500e5410411b1003a450f9800026911001039a90880980b840e0f008000303d500900004d03080ea0b0340c55a5034050307070302107900c0150240e0156081400005091071a8503100080141c000c10222500722400204000c5401c10301154071907650f0780702c01280c0034a0300444401c0b5051751710075002c01e180340c0e5440750060b100c06034801c5028600b032140220490104403040e0280090741e07110103d007000f040c140309016026a034440030060164040c0c00d240d4600100c01880f1000f07807a10240305201881090904480d800d10a02c000c0342c20 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 531409964 1250 531408714 531408719
    0x6050919150e19030806010815010f120b0409050f0f0a050d110a14010219020f030703080a140c1815300a0603020a23060c0304180f05061009 62
    0xc1c1c0e80a0b980c106111411075807100b034982d40303011400300c0e81d04003940480c0051080112669018102660210800c240c51521800c1d00f40080d000c06080ca40c050706006220300ba200b42025294030400f003140c4000c3c828030001009041c12a00c5a04030385542210380a03041303001c00311110000d034450b41154000000c3c88136005040c0c0480d29180d03181000c0c4910b00810900b2800f282e91040c0704011940f02d200010391f04c090340c803403624016071202c068200b90b400c0802601c403c0304021040d2400c250b01410000d10590354024407a00814845e0280543c1040c08000e200002c282c1001401c0e04006500c024000750854100f00041d03071040240300700c1000401c00c412584200d0070403804800800000100388846400007400d000781101702c0300c00240903544d800c10010351030256a00320050111000d070040203006c407100c00c03107208803510005004050020f6160342000c01001240c0061016941946605c0d0240c41544060001f5500310907407030341401c012400f03074988070700c01002c01075994407043c500c80d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 531411214 1250 531409964 531410003
    0x60103030c11040606080106081b0307030b13020708210f1501050904060803190e0d030c080f03070e10030b010f030b0d0b0c030103030801060c050c06090406050d06050919 75
    0x78412a811142205000640320307040e2281c0c06000060b02090300c0d611040c3d07041c11001809040010841e15801c2010021501e040b1054012240c0000203840c000c6007240c08000400c1d4409a100f84140d000e034070000f41c000030b2111400181400c8400e440300c011201c2103032802e40380c104030280c0742281c1d495000d00114041e406650840042114107060240c2403e00c9600054102c410f594000c030307465080020f00848140100140d004941d00c142040c0c0755141030f5001140c1d802b0240d240c01000e0103070f140406018013040c83c0c00d03551081c2000340143e580340b415510080080f40215905c900549004c0301009015000b40220402c008042e91342115054032520224090200c10944a8128404c0e4440a0104086041d070721f11500340100b1440c0d507540b41d450001d00c18801648100100f252460129000402c082402100d641c03044418984500c200000540107182a500c8154410f101c0701c0d1600411100c0c3e00610321400090060b1405034110320300b0000c482c98a0700008210b00b04040a845801 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 531412464 1250 531411214 531411227
    0x203040501050a0c0516081009050c0f060c3a0503040b06120109060504050f060702030f0706110c0a02010306060503071b080d05180d090e0f090c1e15070506010303 72
    0xf001680f0389284481082e8480c2802d1060b10b0605808454000c00244040e40e41003001881400810000300102c1086450707041d1030f503a525106510031324102c0e0070440a542c842e0152041240400142c6004642103c0b0101600c003c1441b421a0000c204c3d80828104800a80811104d006e035268a8699522036aa403121100c00603c1c03503502520072511403002034824814000c041d03226203400030300c5007440d0820358a8010b508400304500c0d800401005200c0d540030040d1130180012503591500c8040c5403510f9000307002c40740741f850003100700441d101004241c0011141e20b054001c0e2070070452143c0314001152640b03c2295503c002c0394512000e010f402c140b60313900c11581d5004041803800e144501b030408064400a90303080b40c0a0a100044038031b03401c402c0c4a000320740c194130b040404440f807a0850004161070b008000011110303080002131001c0c0000c0c04008101c083c0142a103070100501c01401440405940c0d0300b0740102c003000f00e1841030000800454124541200051200781e285540840c0e14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 531413714 1250 531412464 531412477
    0x9010f06080406382b0f06050403200715050c03220f08031c052a03090c0108130204110f0d02030403030f022809030b0a0b0f0a06020304050105 63
    0x10f59981d103140c0c034501d506822114003d0046100d07901d01100c600382001090b0b80014185611550034488500707865100da440c08900141c915490031007000c3c090402242001c00e0b9400582801e086c01e081000705a4854444e43e1120f0603038511a0740c111b4526a11a51002c060040864010b61500c0c6011158090000f40c0408003500007180d241901c560484880d070b038944a604801e2601080080c40004403180e0003201910800d0b0013107013010002c800c142ca414240700e03884001685c1c4c4074081201e01d2040310074100d24504100708400005040ea025078800d5000300ca43d5410b5000700d4108008646c410301880c3d024400100001c1c0c00c1d80007580800c0014092080c0310941e017074007040600c1400b01c8001c05810700301d4541c07c005849150900340501a07460a83c2c000948510420101c42121000c2402940078a0000503501c00400700300001c0e90b455501d60409044400345104000c96010941c10012000074280e8424041003030704001e00000003414050391025070002d02c0203212651003100038110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 531414964 1250 531413714 531413723
    0x10212030c07051005060a0b0309070501050d0b060a0206090c0f0307150e0d12090e01030816061e092303040b0306012606010206060f100c0501090206120103030e09010f060804 77
    0x1400d0040c3e941d1500e40110115035412a50f00c030001c0011924008144200074a500d0955620711300c3c12160190700c9800f00d00846052100109034a252410a07600101c00c6150113060b03180d580482c2c0c403000e582c07030300101d071402070a11031132101d0a181c1c01c9c50a541e401d105009001030010038201540d0782500c000740d19000301003161442c5080c1044d40d0710800980c000d0b0060320a403039400c41c40d000003001c003096908580b05582e0245e004000081203d022120301c9046104c7c01206030300c40d0b1410328003901d10542d4a40410313103c03240c1020410f920350300c450f04251041c0c10595010308900283d49540c00c540c0032010b41c1d600309000400420600300001d691101c0d05140040d03040d0410221141d030a034580c9004076290044d1010040c0b0395804003e401d030002e00841b2000c03910100100054608205000414200009000b0450030404250480e9030311940c010419500c031aa1540341c400001c0091009900103048442030705400d0030041d44140c103890445180c00c10b00c0341022030541d29101c01810495 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 531416214 1250 531414964 531414967
    0x515011d1206070807080714030112020d02030d11010b120c010c0501200307021510170106030b011e09020c1005070521090c0102030c060a090f06051005011b02010212030c 75
    0x200300d12042c4440ca00c1502c0ca622614240e0030060401044984010b0607403051010310407520700944a504190b0341180ca50411000021a42c1e20128504225004c00290544106d0003000712403604000d0382260301035101c0003000000041401c00880f4900f03540c2c000916081075002c800d4a51080c0a01c0040c18022400410411680b41e420000c03906040c500781e05044020040c020902d0741844482e10811040c0c85c0d8200b24140184141030a002c203116061240c050040500c0d4518000e401940045030880d090001c2c0d5a950207050440440e00c0307905290f00081c0100c0459004024420340303103140d40301d40080c020304c503000c07012200600002d0040414444240010f14044010202040e415407090000004504008000910b01018034207101d0542d00141b0038050f0411f400a0200d6002140a0b0045601911410310310440c2c040d850303010f00064184400c10005009800c445400c99400703903101500090641a6078075080018840240103800c09215820400d11060156070001030002455 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 531417464 1250 531416214 531416239
    0x9010e0921091c0507090c0905030a0c1703280c02210c0a05061213021302030103030e0409201908010b1503010b0d051f180515011d 58
    0x20514090000d401440e01103000403544190b0038803c00c1c0d03035820340c42603d034100f0840c0d050f9559a100c441c40d000f03035045c16555090750b800161094490728001c05024094419000150600d0990f0b02501d006042441000b40d04500d0790260004c05c071071801403848130711144084040100490111210303012000c2003402500c18025030b40d03045803048400f4503180182c2c0d1288650032418242031030440401d100303081101c01000280c65000c2118a07070b039180e11544405503109482c0d080c1620105901030342181e04030004001c0c131081b90b030046050380d01a0301d13280008c2e150341040100f034480c2c2d07030001040c2c0c40c1c034030061900640034000141401c240040c0070000ca0408000446486855607024845580d100c05420040d42407011044100815180c03c0d2031a660402008800340e10440d41c80c14070700b0b030350f400c0051485040325200e1511a103140d050f51881d9a41d41c1c2c44010714006550b500d80210f0b1a14011403494031145180c070790043e0301078442020100c1c1010f07480300d030b0781c103480c2c5495045200048074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 531418714 1250 531417464 531417493
    0x5060f1309020a0e030d1d04020d14041a090105100603180b130303061202010509091003050d030b0310151214030a0c0302061f030f051f1d06040209010e09 68
    0x307000500104d50f01d00c8200303004182010314285a003190582403102c0c01c3d40c00070310604110000034440205441c09a650000121000000c2105800c0c490002c85010140001c000901c0030000307910a04000310404da0300c4610b2504e00f00d03102a0f416160460600c1000c100c614040e401c0254445812440048540c034180c0343c151400368110b55903170380d00d1a012030341000c050f014415140a40302c41034101800020316800038016204852140d0300c14420080081c10186103458190091039001c41610888140040040c01600600d45418840e0084080c503503500710342c1744100c01c07100c46181c86030b40415240400c0c483c540c010300081601c079101e0801a903041060100018100d41c0740d2651100d00c00146410300a05144015104240304010500250018140c200c01042503076041499402c60309400e1400500d8241040124103c41e54104c0c049640304000da884442030701611060b0413034011290304000d480f00c40c115002503100c030b0390100500840e0200b4081c81da2000004044411a401ca07052 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 531419964 1250 531418714 531418717
    0x1050108090c04090302100608011e020c0a1a160c24020c030c030306040c14070b070e030f010507090807030b0f060328031403041e0309090603030e12030405060f130902 74
    0x45e40542c0c0f01401e010f03020308041c410380c0000c0000200030060248201d200e83c41466028142c900328035004110344200001c148041f91115611241408443c0b401940c00d0250280071201501e00403c1017082040081c0150201821546d02031500304040c2880d00e125400c40381d000c3c50b000d010507400e200000700000304200804400c2d13000c000031a240e10380503080005580005403103070208619032030004080c01d605070603504420b03480f2003d00d86603542d582049500350740c02c42059900d445580c15284010106501060280c002c550783c0220341034441241a40d11001880020070518450700000c49000c1018549030f0030120050903140c2d09588804c400d240080c80e1100c40041c1c3e0100380c0b0034400c040d084241c00d804428a0080341e4118603042e107030a12400301851401c0240d450514012040512414240014020f502c0c1d04001c0030b5141d0070004c241490080501740120000500c40c1110034001080d201103520041400c0d15101400d80a000c4940000450541d0180040c901003a02c240600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 531421214 1250 531419964 531419981
    0x12090f030a030e0106170304060c050a15020d0b090631050705180a03030c0809010e060c100509030304020d02060c070305010f091b030c09021303050601030b070f08010e01050108090c04 81
    0x2d6012909800c00e910081c00c50b8010b6100c01180444804206034054000c01a58110382d254100031403206c070542070890419401d0503000b42f482c0300d4031004541d20701a66010382403003401c18100300041c444080038400c90b0b16050b00c0d12540320619414209103c01c14400a40307035590800800d09403c0e0240f540f910659030107894600c003241011440c00320b410350b603285000c0c0c0704004940761014503103951400707031080798540f0001c0c005000001d00d407403580e4010420003601001c0a00701640e640300101d10241c45041514641e05050304040220f01004400426240900e80062001c5102c522030b5007088040d0f4005260003011740286080040412002e102c1c40400c000442d4010528446074600521030007036650b1010500c1003405d2041c0042100081c400041d00c05200c0c1c01a51003103250b8842c900719110f5800184144280d07070001c0f00300000081c2080c002c151903281c035145055030240948040100f40151401c03c202c0000410883d0b200d999102d420460361030584002c242c0202c0031070166240754 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 531422464 1250 531421214 531421217
    0x2205030c0601060f020703170309012406020d0306080607030507020a060603050c1f0909020d090213020a08060607050607210905160b13090b1f17060603070512090f030a 74
    0x800104180342d08011030004030482171002e010810b007035a58202c3c1c02460000e43c000c01060100c0015400142544220711001da040c4c40c020303040c285990b141d000c003070322030140c1001070264040c10318000c0d009000d10415100d024015185130781d80e45200f00c0050800a10300c20862080411a0340801c0d15803080d0000355000d030024000b00c0175a035041c461030720701c2010940c1340850302d62190320383c45500942040944100e8480035a0301c2d4030b06072108000d4070320070401941c003542c0c3c3d02909012000d15401001c101025484000c403a03075a0804203c0c8600880390050000e4004400040490744200203543d1b00012606d04024100202d045c102e0845543c11030446060f8014400501c601003120790050007410084402c40c80d0030420380100d044412984990180b59031200300c1069250b031400f102d4803100340140c080443e0140160b00082c05800060781c503284401c6090007088031400d02804072031103128161925450310740481403401c0858802080d4840074000d01c4440014803a052004150b045180e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 531423714 1250 531422464 531422473
    0xc090b131a090907170a0504080d110c0606010906020a0602031b121509010501020a021302040e13120c081602120f030a031b0e10020c03030703111011032205030c 71
    0x5104032604040c00e13030400e00c140b4411150b20303150a001895444030103407a0114441e200c614003001280136042003809490b08201f034580d80c50703440701c01074548810f12104941954a6100056855140c1c600031080180c100101010100350103030029a00301c1120407210701c0301d8400c55015080c0380c220b0856852250300e150140560031141d45100b07100900101c40f02800c81d45003c0000c0c0d9545c015090007405000c01c800452080101070781502e000b405055410150383c984001c5103402043e404034102e070940a1031808801e803921504504a0041e4040354080c90601040c4400070402d444240c101d03442031150b4010329200c041031103032902d041100d00045803a40300440000d41070324400300b40c0301d0458850f00e042c070900036480b40f1f20680c400e84c240e40e041e6003100203000881c140360480300ea103501440b00040d10410036502100c0c00b804801004162002402c03c2c903108401d030f450682a0f01c02000090011580805407000c480002c50811007012100f90201c1d0342e1181942c00040007410243c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 531424964 1250 531423714 531423727
    0x8101a032a220b16080f0304050a1203090309050108040501090c03060204090b030c0607020622060e0103050f09071406070b0c07051204061713050f1608010c090b131a 73
    0x55060b907401401440010030641061204900d9002c1c21080100032800e1540040900c002c0b4011140c1c4524860382c0956a03107070030700f00b499551007229001c8501e402c11150b0030348100e101c0e2154160780e07541940c91090306441e040c01180d840d00302078000d4805540c4c541080d0002000103842c0001944200300158139549001080022919903d074080d02a42094001c100c040e501c2604581d4096411908640c484802a0098100c1111807510008600c65800301158140d00600303800c1500800340e8081c080d83d600d002035034560100070b030345400f110343c040f450612002004440f82c3c03404801c0940414107146858a440c5028082928035140081c030004406040c090107000c10360088515240c0c26181506e81000103105044e20321800d400d4603c1c15001c9903000c441c0706001c0492582150440b03074009140c41031540c4418459446400a40c00700000044506042c09003007500c994603150400c0d4545400214540c59101226202640c901074902151200c0180411003090901440031615a00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 531426214 1250 531424964 531424987
    0x70b09010b01050405221407030209040f14181018020a0f2d050a03050c0901170c0420030c041401080c0304061a15070308101a032a 58
    0x4503104541410440200800d00c50b40d1104002e496540550f0100c4d49000c00451003444018014800c2800c1c1d0787e00c942090280507581a0050501d485041328100600346102d4034040440b04000710b9554001411b00000311107000201d1240744400402c0d0564411002d104a040100c170245800742c0c0611600c40c8512087d818040711070806800c12a00c0059501e0518610211380703155400340c0300d4900b003130000d903160319542c40e09a0030040c1405800104843d80364980180c907041034200c024041c04421000240b061107000c248100001c08101524180c002c0c001400094000c280e01c409000da292110b51622490b020300940c491410345c4c1400b03449506110301d01288040c8000100d0400074000d00b80268890520126074101c0d07440400001d40010000d1441521303072034581030355408101c29509840300d00c0300c240205240c41c03107907440c40c015945103010000c0740710441c0540a040801000407404144002004541001d115200f0700128202b0094a100c81015013034001c8a40760080b400680c0c98 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 531427464 1250 531426214 531426221
    0xa12021605070503071a18040609021c0c0f050d06030f080306120c0105190c061a0f030a050d0302220f1809030e09071205090f1504030206040f021302070b0901 70
    0x500d000c41c0a400744916001b0213400d684030720100103040e500e0010719403294903402c0304000c9240740b01410610200c0da48465000080d04a103244000204943c11014108807091080320303d030148a4a51020780e540500c401c0710182c00c4119210210b0355140c4001c00440c10200783c994009100703404507680d900e820000e00032440700550715855a07a0004040d0704990380c020f4159800c0b02565101002c001c18400011103a00c0c0b400e070400f0b0302c41450019041032200b40e100400e6900c2805071500d0051030080002c0c10b50320240440003501e00c2d00210343c000352441c441d03001010046e1a8112254a00817889070001030184240d124843c1c66088000c00c000c03a0723014050480780e000c110801008540c1241d2000741c41400130307048044c458005400029503403030207460304101d80c0400d100208070a1805143d2641d884000090840840c80f4680d0b0100c0b00c039010600030781c415540350303000d00421348407a60b0305030701c5111070b40040b13912010705501a40c1d01c00d13444c0f01400c0c01034015910000f95081000b01d044c00c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 531428714 1250 531427464 531427469
    0x12050c010e0303042115020c0703120e060403060b030327010305130506040204110408010f020414150f031509040506071805150c0a0501020a020609060f0118020a1202160507 76
    0xa801c00d1004000100c540603803000074403171350032030301c00e03003501500d0200103040c3e10401303003046a4400701e80460340407000100001900d10844072100001c450b0041600c000c800c050728942d000c8000c100c1032000030015009040e034017038040c0031a4100004954034038240364665641c081034901c544404c20266905000b12500140101c014060905c1a0744404d605c07104010400381c0126118401c1c013091042490440d8000c01e1140001c11801815410b0075008c0d51052103240450f269041800d292031520300301d20945194144202e902c1e0141080107410a6000100000d030030884841103404640c843e030300700c148951b10404c090034031843c200c81d000e888882e81c0401880c070035640ca00309211301d0300c90010014141207100030f25a120305200310040c1c6000231000c0000c100b94004140c6106c81500098100e010300208000c0d28402c1e40d8002c06101d5541092051142640c207038015541844a1075004000d58162407601880480f078040b042803c1c1e900405903843e551003540e01520030300c6006d1140001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 531429964 1250 531428714 531428719
    0x608030310090516050c2803170106080105150c0307030504241224060519050906190203072a0e0c0307030b06040312120b01020d020607030c0912050c010e 68
    0x1801c003d16100c0d65413855206140034028001560704114600b008400c80010074a56002c4026000c0f9164000000c071b02c0c24102d001c20600482050614150360089045e03405950b11b07000113a19082c01c02400010040345c1003842c0c00100603483c03002c0000c3c80104503150203521030a68441c504004840c0c840f0302019030a900c08400d0041c59661548018100180c0c4000c940c0426046010000410041e140020b805084001800000b03012600a0068a1540b0f240c1100c01102640200309842c940324005000e41d00c0082000841d01c43c11801008020070045c5204403801e1085a03030b190119040c1d212000013904d82c111048a010130031b4030010801424001d184060181480120796074540000380021043c0f64a031000d40342d068035000c0942d8010764102d0180c010051413404040c0458000e003220903601e60034461f0b0815154000201080c1680887d40201820355034058100d00070040c07525000c08200c41c821002a403542800f13a5040061301400161000e2a09240003600000c0c002800a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 531431214 1250 531429964 531429971
    0x512041106133b0f061504030609022707031a030a050c03280f05010212040b01080601060f050a0807110312010509010f0f0311040b0622090213050112020d060803031009 74
    0x11820030388440d03d136084105850380036401e0700c5000000d182c0d400d5007110200041d80100d00001403041c6d03a04002c0c01540240c0c0c0d8803202602c0001102c00d81f04d603021010a42c502e030b11000c2100540300358081c0c84d5171500050030480e80181400000c6c10f004042c8029511035120b40307045152481c0501880c4500000103030310385240d1a1155a85070451049940030700209001c1c6800002d0100039011103c260814401e0240103150520f01109400400c0c000d042c214450b2000210781503024107510807a2000a480d041d0038900088021507800c600104600e08008601c0d13140141132804001810b00d00d030403825001f28a40c1014281302c0a058140e12528151442180070030950240f0002403098136041498107007400e06410100b00a400f2941085420690001e0010450750740de035014441c600198004400c200d0b80d0320290400e81c0203998100c9044404050100415801000c0041314450020070140c28816021a914100d1b40e941c1e0001c3e00a4000100300080c00c0400081d04024110360030042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 531432464 1250 531431214 531431309
    0x9010c02010e1e030909040321050408030c030402030c1215061f0804030c021309151b0e0d02040c05031b040b0403060506040f0e0309030d051204110613 67
    0x1103079940d05a416443c0301c0003024000701e034081424400c440400c800079041041a00746480c0003003440902d071000d01840b45640844589562060082c2d5000e260004041410340d1103a10307000e0000c1e840504101e80c144a41d0010321066210840c0e111540d051000203401040d2a81e441024a9038005140c6413203400c1c113001072608141d6140032011012070b907280c0f0440d5580c1b540360a844c0e01d040f00b20701075840034040100103000207480c0c0110390341c1880740d00e82c2d0700c07126801c1e0000005e0f00c281d060800d003151151862991010320034400e9205405004281010705e15540e0086411595105011000606c0001c00c01c1300c001c080445050502002c07a003014030b01803400c0d00e00d000c240a02c1c040240095250130104105640300e400c000c0701c82c87d4040d4100300c4014507058480da2a400300c12494000c4c05404102c444546c01002900d49141c1403004180555585070780740c00102140000d616404031042c4000104003502e00d44000140c500c074000a00c0c50b501c1c2c0d0030348204005030b44051503400100701f03d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 531433714 1250 531432464 531432491
    0x20031308030306030d11030d021b010516030e01180b0604140c07060b06040e010e070e131b05091503041416030302162441070f08070c03140609010c0201 67
    0x8032230307211505d01d200603204c54248210849030002041d404c80c20f58284800e00020400b040c1002c480154641c50405c0908510150036090320300c0030b1134a8142c2580d0301300c0280130032071503000303d548000000c10000d11859418100305c444001900c0c28010005c01041c01401c00c1800c2c41040b403400300465006007070a160480010304c08005014045000120801013200c10340120142d00d6407907401044c400021114100c181d00038004c040b01c1c0c0c0f00300181c8450f4102c002d4010300850350601c80261086a07600c41c66075803124190f00141c4201c607084900000402244014000080f20090700345101c9840ba10f1401c000f8503264003107445022444582c182000755000800c0b2445c2c1301d8409030492148206000d0081e950450f20911220704405001303190066062048680d1049904402a060841441d18040c1202e401a03000003884445003076611030110b140c850180040511903541d039400302e038582d628039009802c6000c080e011a40030006009900000780607520030200d00d48000c20442e00070000307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 531434964 1250 531433714 531433717
    0x150605121c020c09090d0e060a09140a0504021303030909020f09040c0e040501080f1b0f010c0807060908070302010f200c07080714100f20031308030306030d1103 71
    0x351800d0a800d05444081d500d40284051900d0580082c036510700c92600c0070441da01c94075445a00000200032030b810000520f03000080e5890503c00380e541c0e4070854201207041d4049082c03805199070109882000282503512030000703140f085000d65004d80303035614524014100b403000d074015125150042c4500b0140003044420703100e404404940c0403c1d550b00c200f6040d5110b401c2280c4c015001343c03c01001040784040020081c81142502c0211004500001c2d60051b40c1c2c100c0300c45440c0d1040040c14002081e41c864008508102c1c010010285060038541c4c40c0c504440725400203c82016010400406140d0288035170000480440018000b881d00d546800705100c4150803e500f0b860b5001c100410101801c21080700a00b041004843c80c4a4031203005820045460100d54410707480b0282d1060201e200e12036101c088003103511400c1001101c1981255000c280101c4007020340300601c2503100500c81000100003d000110145540c0e041c64400e0509020016025600340541c1c80c00c2080d140d1b40000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 531436214 1250 531434964 531434983
    0x12070507030317060603150d140303010807080c090a0c0504080114010501092403021b01150302031c020d0f1416062316050c16080d030501051c0c08010915060512 71
    0x500d0002840c01e0b11002800d807010068003d0820b270a46541400190703800001141626072280849000d5542d03541d2042d560300740e50b800b41c1d4100400802142c3d0b0f030a500e8102003046405c2c0d081c00b45c20719442d8468607084950344500712201522000041100d940c020308030300090a40303070300c8041d040000100010784040399038140c1c008245d8001500c8206072084c40c00d1401c40c004030300c020310601e6075030400e21108030910701040e4424000c10f00d41c0c3c0e0082c000510b001590204540160154031982c3c0c000f51010f1046d003140c4424425505408542d182e08200107128040001d80142035010131400d1490403164042d440038414150008000607500c42130302901d0f8403400c201103003810303454a82c20444081c01810500c203154411b00316070020700d0060100900c160740e1078004494180e00b103028101c055541c03c1c0726864000c1c81031065078503285003500d400c0d45001d018580c5502c1c030590341c181c03d60840e154880c00745c1e401c04050080c01020310710340c02080c00806044480c1001030015001e41a210007085 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 531437464 1250 531436214 531436231
    0x1407150806060a0c15060f030c05092208040f0e070f0203090303040b1e030711010b030105071b0303140c070606080a03020c120703050703080d0c030504030f030e12070507030317060603 81
    0x1c0c0d44204c02c00004c1135070000003417441d5205000c40340d9a80005110300050b40000c440069201e4030224241c1840f24495100d84284011284d50807480d4507070b059003400303045003034550040030480801c00b60802031454005103420030000e152071411070300040c001480d030301900085400800c100e5455a4000040c1c07010f80344490001075035981c04021200301c0403242039039412030741000300c104402e1940004021600c103080300028400a80100201400c80d5411595000030404c0000014829001801016103c5119050000d4005000c06a020b00071070f00703c0345078601d01c0b0005182420031030b0500503038000b0503540c0010724454049681c040e49401c80516a640142000091b8480900c07040207940029908001a40d042c6512400c0c094481c1c2d2010011400031401d202c9030558080c030070300c80c0f5403144e50550703210b00d000f0700d00074411000b82004c500c5a142c98840c802c0302d070f014044051700505070144648010303c211841c52801410421200c03099050076101501001155200c01040381ea002e0082c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 531438714 1250 531437464 531437477
    0xa03020618040f0c020102070c06081012030e1e0310050f3105030304020109050303070507050121050906070311040609050402090d1e0506010f080c06161407150806060a 74
    0xd00780414010004900c2c8100242e0034003580c0d403003158042d8020b00056015240401c0070701e89880d000d9030320702020b4460080d98850158100f0006081d604041c012620900e0401c024070740c203030002603500d1000d0f0b5004051a00804c0004501e180402c00b10400c1c83c4110303414030030341c0750002d03144100503002490301c02054810740120500404000c131084c0c2080780c5170700311008041141007840e900e4100300da0490215188800124003483e001040c0d6600640c0b00e001420914109001150703840e40f035030b56000500d012070004c41100d400e103004030342c401c4460368014110740c80c0640004054610b00321444044c080e0401007442490361001c546810340300d041e6809a980d48000340418030311200383e00003806500b0310300f2221680942c2c00c220100850b029408491050342c8400184000031454170484030f0703540c040070700100c0c0e606100000d0081060701c1e200c146103849050300ea0352041050030809403003603007040c01d0501c410000050891080300141c60005410701c1c0c01408552b4903c00e490000c03052068 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 531439964 1250 531438714 531438757
    0x42927040219080601140109080a11150a03020d110430080a0e12010e0c1504090e0313151209140706030608010f020f03010b13080a1208060a030206 65
    0x40b400204540c2080610031881e5450703403420040e4550b00f00780220b600e900c11030502c50b42a584109004070075941c456014200c03892940d0349030746a501d258070b0320b1a00a1742c0e0b510080001110807010b091035804c2900c2c05a070300d14080091500b1200101d40344110001c00344424040d80511000e03015a801d03151043c8a0700f802c402c01ca03000006030040c3d0060440e5070019440c010280d012045240d019020740340f41100e02d1a10309264241ea101051016199001386108603880c580300910361502d84103180c41c14580754031202860300341e03041481000e00b59400014500b20020701c804050000305181d040c4c05030903c1030701030000d04500e140d40d460042c00e070301c075070503402403000301c50986018003440403c480c0025a20342020f4040d04107481103401c40c0d464030007584c00898050007103410070002507000525603802c0171200110781e0414101581a00000b800114601c4002c000680d46140101072585203032a000d10002c00e84807004140c02e004030304040c001c2005846040c01c0c2e444228403814a03140f06e04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 531441214 1250 531439964 531439969
    0x306061b051e1c090e06180601030b0402070206030709051c11101b21050c0a1b090c0302070b132d02030a06060602210901030f06050429270402 63
    0x70004000c5405404540c0f060142c3c50390450032a008a489030404035001e5685c0b20100701030360b0403404505d10744400820020351150302c00d0b41712012114000b00014104452034011902607001122804003042e010141407055140080202c5100720070391030f010034000300c6551440c05d80c1403509550b41c0119030300b00e0100f80d0035000e01c2450090054054030b20080645500309507407003403e080780d080001241c00304409013540c0325600f02c5500c221680c0007803d000d8204e80d11110031a0250354610301ea0003100c0408035140e0018050517032803903461354015031900c0c0c1c00d05281c1c141410140c01142034039003100c00100040e03c041c3c009800181d05903001140b41224952400c820030354141d000b5414082d4804010800055501100a81e50745901f154201844003889884009036280c24010b2030b40148803800c280d6100b81c0242d00506008140070880301ea5510101d010f032121204002d802e0322a1407008500801c1d1450068550388089611000e11003603010b4002c0d44c540317420403801140308020001415074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 531442464 1250 531441214 531441223
    0x15080f0a020418080a120507020a03140c01021209061b18130e0a0303020c060f070c0f03091205240106050403060237020606010207030b151f0306061b051e 68
    0x31343c00c0a40c0c140e84040398200148900c416000c59010b031071401011442180c40000da101c0200d5058540400300440000d442a071a001000954103540d001c0005103c915158028903020b03042e41030050036030b418590420b0b510307860a64220615800180507111119944100c1d004204400b5540c40c0038441004580c1c00c05030403110b070028418400e035284407041544c190300519080c160a402d80c5c0c0a0340b02c864510300c00302015540340c0c00040d282003008012a040440400e4007500c0f030306225116665510501907002d02542003a1040c0e040b803032801c0c0d4100242c00a8406490940040c030700d00358100340d0060914011808043c04255001c83c80d11101d5030b49402c103184070050340400c94003111041004001c3c1031151240c1a0060150f040071848030350000404006403036119981c0b405035692060941c4811a038401e00550180482254a00c000d40f03000004000f10010303a4013140090070000f0203800441d0781d40c1401203007010141d90002181c401304442c075803103016503542202c0c4500c803c1d010b40340 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 531443714 1250 531442464 531442511
    0x30403030e03130501170103030206041403040e0c0403060f050106051602190e0108071d0f0403030b09191401030507061110020c01090b180604060b03031201030615080f0a0204 77
    0x30340c07200107240343d00314803030282260031104241d0741c803802248030000c1400e8586081c030008025a10030008280058001d265580c090024981100c1c2010b56403983c0f0070940d007059542d01d030700900c0001d040c001d104c064040c0b42e000c601207101c24829135150840c0144a0302c200c0c15945045200c9000085c21036031140041041507a080d100580401e84075641541000020700c81d070503007882100d400040c80b84d1201019440d6501e410011116070340d4407885203014907001441241050fa4801d0340c07140395524205480e02405040d000c408800c400306580708126800e01850701c1001c403203030004000140000030a181900d22500d0a981240c20000072203142002c000150100e0500201d819081130b40158000620a80513840f200d0751502d80303d0f0841055950040d034aa50f60300154000f43c042691a0080d02450380043c0840c0e2401d240342c80c2c03801010100b0b81040b02e10f0f03503c69050004241000f2405400341c201d045c0030b41111001405c40c5641c40707006100007802952622038170550f01d034048480c400d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 531444964 1250 531443714 531443741
    0x30601030b0603010f0e0d020f0a080315060d0504060b0f03070806010312090803040305010f06090501061706030717071505030105060714070308191808030414150a020a21050301060503040303 84
    0x2102a48041d058840d40142021f01c0184181c4880391000480016100040b13900008138502d50745441c2185c3e80624405108142c015a0400040c4c0c9807a03000d00c5203a110f14010072000444400d12020020340441150307545120b82e0082d1400d1202d40000310300c1a0459130b03c0140280e110f04070300d40980361810703180e0000146000c00f00300002844130640050400d070007880001c10000c0c0e1120b00c24011200d080c0216030004040c4810308004004000b070b49908200010119040d241c2d60b200030f8107041c2d0030301400850f9500135107003c0003140c15241e02c226426402d4180310342150b0408012820078011510043c1003040c041c00344043c401000c2c00b062020303681148180350b81d028481c0342d03480f40c00108045140000c07041440321a4007205881981c05480c01c50014501d013518000398400d01c008000780c040e52140e45402e40e0440d0740d414000400e00020b40d42c01602181c4264100340020b10308000c0028401883d16550b401d84a42c09030072030713064030a141070940e01c0307072141d0500b10010f0070a03101e20b24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 531446214 1250 531444964 531444971
    0x2030c03060f1b0a050318071809050106080613290c03011d01030302100209030115030501090b090d050901111f02093a081e1c0902030601030b0603010f 67
    0x30701e2680703162402c0d10402d4000c010ba032a040614003d4039040c41005003900018100717001080400c0301480400c400382d9460300031174844907119243d42d922501c40912203100c4642c1d818a1408100003801020000c02c1d1080180005203480b149240c0382d100c2c0c0ba44020100d85042009442900d00c0c20b1417081003c483d40ea0380042407078510b0041c0890b900070f000d00d641d11a104445907006420604405040c0d0341d140d80039081700590843d007078000e0b41105154583c19500d51200c1e4403104681c00c808001540204008504007080c1e003064590510b0240c4000501e030824501e40410a804c4002c48032205170030700c1c0c92030402580030040d40c20302686100a00c02150800d800f860f1100507900070703000c060411150003224048002e1342c5902d010440c000f010100c8002107070440300030b202d1491000458010500e461070000780341001c400c1031800003d03040d1440d4010810101100f00c080440180c44c1207200c0801040605400081c0c0d21401440000d1401c411a8001060b5481c00e422a20354010300507800d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 531447464 1250 531446214 531446221
    0xb04091a0c0f0a02060402010306271e0905100b060304200d060504120f0c170901050903070e0108100207080d0f0b0310140a02130e1005130207020a0b041a0702030c0306 74
    0x17511000c0c25141a80000c2c2400300c0415481d40310240c4000415100c164400c6070740110103821702504240009955904a81050440003a518040c40315a2032050000c1c20500d140110b10008440c443c0301550b0080105000b080001040b40b0210f11000070400503403040c03c112040042c98500140500601060803c814003040050254440e00c0143c0f483e01c401c01113030310034441141c0d1119000e2002d03100c00498003441038500c00385001007080003018540a441c140d401d102091070001c003544100700401d4000f00401402500740200c5e010b810ba5040194a4800301e5214070205011b03040f104c0040d199191000c541040c41c03640000303000d18000e0150b50300300d1908607001000700702408401e003095180d100010340240d16403081b00c10030100150b1212901c0d003448140800f0724001000884a001183c02c003250690b2000c604d840c100e8110000541c0d075038068818412440319960140790401c0083c8014404102004203100b02620102c1310542c8070402c3c4d0002a01d8000040b0303410350580100e4060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 531448714 1250 531447464 531447467
    0x12030e1c030e09070305090d08060a0302060a020307140109120e0301140901140f06010903031407050105190b0f09060f0f0901030308091213051002011d0f010b04091a0c0f0a 76
    0x7000701c003100301d4443d0725036900e605098040d1070044402c410a60070041e10044068000d07400241c20444c0500542035064480c5d000c9903a590081e2810700140e4004203205003000301c500c0c100280c20752118020b000040c09942c4103020340c1ca801c1c1001007484130084281e88503031002d40c0600e00c4200140020403075800c216440c2c0c2d0081444810040508041784006041042c0d1588014010041a941c1c0200c040c5903403011501c0c00c0614500f41e002560810100c00801c3c0c0074002c00b030142400c40d00c04480d0380842140b10307003220621855103005100003640e00201d941c030141c03070540c0700701e043d103840f44000f03a120001807501c00c4608001381d0048441d0008801d041d40180a188901ca0103411100211114141c40354180108480d010250004000902641c1007c5c2403464001d83d560001181c154201076100d1004400002d0781d41c0c0300d6010241000904100740202c4080c881c040d5400c100c060780313503121403100d05284401c01c034806201c0c0020550050b000d204071201c2c00583c0421585030140d0180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 531449964 1250 531448714 531448727
    0xe06070c020a15110d050c0708070b0301120311030703080f010509040302060423030708070501060e0907030f060e030a0c0b01050a06080c0f1207020c01081b070204091103010e03030109060f12030e1c03 88
    0xd031100d1080110102710318500140d4101600d040039000390031030380382460024002d04d03031880071402c100980b013100c04000400c01c00b91020381d2181e00c4642e660300c0d100001d10106581648000d10500c11007081c000802e4010410503003080e00501e201e0038121015001105a0114144c241c0503440005844401d0250001c090305032140308200a00000b669012021a100c205607003240c56500700b05800c0001442030f2400c068803074482c1901040c5164040c00803821a042000480d020994181250f010819142c0b44240500411900802c01b1418443c2c0100038140c01000000101c00019141c0c1c44a1404402e9071240b840d105441e000a180c403c034000d407a00c017440250340c00318a8000c08103101c00d01204072030760503100c03207142281009026000c01024001d84035003901c000004140d0a034a40d1003c0c096004c55071062002143d0f20b51611901100f01c5126038031200f106402e000c001d000e1140d001c0350000c0019010714006059443c100001120074080d100381c80f0000601100050415410a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 531451214 1250 531449964 531449977
    0x80a03020f152e0e010b090301060e100909050a0203060910060b0a140702041e0911040c090326041511010509030409110c030309010e06070c020a15110d05 68
    0x140c4400201c001a1801d16540543e8640365211120301c050310b0403e07424000100a62040151410f101e50f20004022000c1c001c2e0031910310f1000002d240300c43c4c1d0600b401104001c21410980404a25049240c403550711124000d40320500d031501c45100600404000880046030028151103072401c060715000e0780d40f2112141c1845031400d0032400110350b81001d095851584c0e80740c40c2c0c3c02ea9401c060701f201d4003d0744942c100300da00540d81c0f45c4d10212880c81c4100c0030000301c4021000283c02c121400c0940c0003200c1e4406552146042000d04a4010741c000e074511300300c03580503905581030344007040032506000506800c0240b030301d40400e001511000101e19250216440d0b2500310b5010004c440140c00d03207000b282c42c5555a401000100300c004200d0380019145840b00c51460b060030712800b1041c0c1140c3c010384040ca11a0f44070100c1e22203010302402459080416818455943c248a0b4040313100101c00d48929400a0041c1441d500e25074010014034010303158400c240c458020045401608070b82001c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 531452464 1250 531451214 531451243
    0x3050603160807031212060311040b06071703090a2f0117070509030102071406040218090c0603060414100f092a1b08030613050103030503041506080a0302 68
    0x88107a0303038441222042000c00e4625840c080e102c1d5a0442c0ca598884112101c11401000155440c2520318041c91041c41c0c042d51180860000307118140003080300f9507010314600c9114140400ca80300018100040404590060041060b01c0c0d40d1313015205401c01986010240c0b90380c084071a865400102d2501c0c1c102c801c412400a00301d6125a2401124404204101c001000c02c04c1404103014501420180c1021000140098500382d80c1da51265080c2c1342001d5907400036400542072100710310b024055001449044010543d0310700d40101415500c04083c14100d016050000c045000c0c0d403500d4000e0010500300114018550410001c0700f07403280001d214540380e1106808011607007006034014042c041400014001080c00072400c20340c4034400c1c1009040c10300c10064102101e100c05504040460f0f401141590744038580038081c03003a003152060780078145074500f400600009821006803600300740c110702c0d5020b00000c040038003070083c04903070055000741c07140d46039010815500103080d004e5807111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 531453714 1250 531452464 531452473
    0x40609120302031314070f0f0f050114030703090326060907030c0f1b0b070804050d030908070b0604151502010615140c0c040207060c02010b03071406070c03060c03050603 75
    0x9240880c00c0f40400d40e02c2038180d401840c454004110402d114031007810b00c0105640e81c0b140e884106100c1c003050b59100c2100c00d00203400c2008001c040014101c0108400c1c20641640c812503000c0324800e200042c16102416076500408040c1886104441c1c3d0143d100582102c00081080601040c8241201d1181c401c1954a0010341c07041e01c00e01406290401c0390b1201002140764a030180c0c0d8100c81425500750707811181451402054030120360300c0c013408650301e0311030035414107007003641c00c00030700742094000c1c541820030140015140d0402c4410250700f00c0d05d640341907103c01e400140a00085080031821448841001ca801003c040c400807a045543e0007c01c04035a481c1641280007074650481c402052a0002803903050f4990802800c1445045040c0e450404500c40020102c0e04400d40a45400ba07076000801c250a07024480c490401004400412607030b8544a15080c3e42404c200b081030203030801049043c100060b4604060155502c20000e100403201c2d0b484c020b0013454215030b51480f0344107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 531454964 1250 531453714 531453743
    0x11505030613240f02070605090d2c010e270c040305060c0d0209030a0b0105040b033004030f031206060302390a0b060910030b060f18240f0a12080f03040609 69
    0x25a600c0500341c0003080d01c44140c91848800020be030b010042c000e81437010004803e1a2961407075401100f42c602410203d0219040e1401040a0701d401010340148000c00c110600103e4400501907905c4980401101d030303281c542520b520080e000c0c088510750140f08001c5a0b0081048a003e070070705881c0c05232410030001c4900c104150b618810f039010f43e1a0991281c2c25200c51100c01000d08558102654000340340982c0e035540c80150514800c0240d0006250350358a00d0400403d008040003082c442c5000e50078080d41c0d0f0284858100e03082900f1250202c2c13402a069902c01200e8108180003180302030b6039040c019030400c803a03800011100740744605070000000f50101c1c8044503030801d0707a4001c00c0b04202561581c040c400200d0a00d082c160303009540041040c0c003401d2200181748101040c0e420a0300a5612010540c0700d203d000034814800e100081b010250358076101c80b1002110581c990340003180e03a4070b0074071142901c02c4910003001240c0000411040c001203800040c0c1c0c480c42030708580081741 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 531456214 1250 531454964 531454967
    0x10510050a05090711030c030a0e120c090415061211100807050309070306020304060207020a060f170a1d07060f0e0a0b030702010e011505030613240f02070605090d 72
    0xa0030302459500c004111020320050820104055004d10141841c0d18920540c0100501c1c0d900b01c14813000441d4070000e007048245074800021014144103a6085604003000080350762030f4019201308c2c1d406083c1c84d00c005010306c1b07104840301600d140000b07401c02c441622410540c4000090100554004070840380a010f94280007400e5201120f0390755030141d068462000032159a030000d4003000c0d1500c249a00030000c11640c1c030056000310310801c00180e03034030424818080c1001c0345900c40c8052080f20203030315007a13640100300360003103030b02c64030340f4040603564951064018002c0550041c2d152070412a842e0194070009080002e41d9042d07100c03122203402d004000c0320240a100540703031f042100040d0802003440349002645d0800d44600000ca8100c0d22a00c083d400c482d030142071145030b9503a00b84100440d0800380170383e542003400c600042c034602045481d00005140c44003000e40c600145413424075141c0c0320f15400392200c02e005410941d500c02c0310b401d25002804080e1b803007440900400700303181e50b0207 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 531457464 1250 531456214 531456241
    0xf12010c091d01051c060f05010e0f0603060c0f040e010b0a1101021603030207020102012d0e0a0825120822050a031404090203041b05010206250c060507110105 70
    0x485000350000d107a030038281401702141d00321081070040c0c1d00040710a0000b559a0042540016402400142a43c0b404540003204040641800524441c01040c04000d840c0441d071241e00042c20346da516580c3c0680b42c00581144102d80c003243c1c0e4500c4100000c910495840d0040c42d00c00300030307510070301400c0c211120f045c200c1c0305002101c0c550075024154100081c0c0039401a1049034014000041c0e400c08103066202c680f80d10715003841c040f0035005421106110284599607048101e00028010040c4a6882d41c10a1040c4d5412006800020f0700c44450882104585082640e020300b600b500d01c0c150120103004280700382c4101c200c2c2010070044c0c00b42c41c1a2150040c003e50b41000040280c8101034a0945d545040090710751880d1000304000308294105000942c06944281c1c042241004800796410180b503146d001981150450380a000e040300420012a0010500b03e001d007425046885094801d4041010020701180c180000c121382c40c0d4000400302d050214010083c0666034a241c5507544a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 531458714 1250 531457464 531457499
    0x40e01090b061602130e0d080105040c030209060f03060f0d030507061d030712052515153b0f010e0105010c140f19120c020d060b0f12010c09 62
    0xf0074403404502c054608480c0728000c00c000c1c0d08000a01703020080b406400c000b80c500c141c4010410b0980100200c0c1824445c4020001e4145800c5042481c01000641948100c03421a00c3d02c040202c007044555640300b0785601c148800420701c800c604058600134056802404056614a1500b03180300c0e99544902044110404848043c42c0340c1459a50340c04840c814480b00d10080150a10010034242043d01090301c010341d0441c0501d40c00329907460011280584c080c82e00030303020300301210000444a034800d0ac500344c41e66a103007051030302080440801c0c0030310f01c00800d51000114846040030301146902d0030b40100d0401102c030800d40c1e00c80141b4503207010207116013800a0709003041c2c3c1c000306203420f10707442d940010081550b00c4484607400c2140f6000e9110403e6a81a101c141001c0c104072680980400480d00c50600c00c3c50282d44d600007940349006d4a002404254980c50991aa039403404114445c10b00700618110415002d1500c2500070700c90410302e1404101c003450003044607998004c05607034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 531459964 1250 531458714 531458737
    0x4030c061806080103080313050610170d0507140a151b03050403020309061303051219020c0105070f05030d06083702040c05270a06030e0703170d02040e01090b06 71
    0x2e883c0d03c0c546e91a0300e00d50008002e101ea00c4e05c1d22000300300154040c46614001d00c0580081c01072203060040c0b101203074141c00d112134000d912101e01000065000402d032004a6041008400408038492010f4100740c402c110092040c070241580710305208041e44601c0e11100011120b1240400a407815022200305a8000e000b40e0300521450000703141c031000030300a40e03030000d804162255903039035514941000f004c0075110300b68000c1040c5090650152048501c0c07082840102031082e00d81002800ba8072403140003401416030154804140003082048402e42200b42d9400c00c41243c1d100e01c0c4584520b89286030549002442008071480744403c680410320b42e004c0f03034181821401950802005000e050b00000901c2802c3c40f078002100500202d05c00b66140c60041a030f4151607140800104017426001682072500e005c21045840c40b0014428013525402a240603da000000059202d400749a007943c001074000640401c0002211440c941241c0075003006100b40c242c1d0a040019a006910107181c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 531461214 1250 531459964 531459977
    0x60102120c0c03030f070506061c0201080c0f0a0c03030f09110904020427030201060f08030a1805060c0c040501050d081914030a0504030806010206090c2404030c061806 74
    0x1040c4038600080451400c14011220300400d0034020a003545c004510840d8603410101340241400b40a00c00c0c035612000440c1ca086c1715200d101184110089011000790400032014000341802080d88225100004d18452141c1ca50714006001001a80514030031400603003000300580d1900070b540200365400d903000c0300d0110040503060030701c0591180184140d23405601c03420f20305030303840702103142d0824847d2424054221a50906010b401e46401d540f0004e1101d2200b4801c12502ca030200c140c44c0880c2c03051500c40c204081c05c1741c0740515030200350803650344560300007030700c25501d18001a6180040d0050f1000e10180c1c1c0c1e07031020071040f98100100a8589442000b108802000c0005458030741d14a40c20001c00ba8a0a020240650303002140d81c81074159175002400b080c15002001140c0c014401d20003041c06150400b140e58a402e03452890300c4c081c42040d0300c2c000b00c040c00898103c0049030b14401d040e4649949043c10403e6021324070070170012568000201c042ca00003003041c0e00a59081da03c3d841c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 531462464 1250 531461214 531461233
    0x1090e1f1e0b07060b150d051e0403030e0a0c151803020a0b360414060109050d03050705063301020312041e03050901030b030106120b0720030a030b0108060102 70
    0x114941da2095401310742299075a030624107550f95081c03e03c8040340f8040d0300280c491010803002402c07a5009800f200d00b00ca0391402201104410300b4495a201c2e0b4145000701e4520b00f121201e03880c0545603a03005152001110707001c9200d00384004880b002030f1065136000440620162280f84460081c00044d401c46a01d510501c008400c42c0004c144006a09504090106003400c0450041d800d56144c2003408414101000491600c1c0c01900c0e04507000412900660400900191020260748100c038056110031903003809040c081d90684103c69009000d403020362415803000581e004144590f01041d8108507041c1001000850009a04400680013146024003181661490707070340003481104d601368090028004a0b9581004004007442903c6681c1c40c2c441c40d800150603a20804006802030385403410401c0500d00c0d200300540000d07086005502c241c1c032003040c01c4401c030345250040c81c4002a00d50304203201800c004020059411170f60f802308000f40c2d010004403400742c000d03980107006900000d102d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 531463714 1250 531462464 531462479
    0xd0905030c121903170c03060112051806090703050105011d0c0d0204030807031d19031403070f0c05100507051005060604050a0f0509060a0e1501090e1f1e 68
    0x14420391058560499072022843c0d100c00d034664003004011070000c1d620410030071240520920a940000b40028000d04601c0c1c03c41c0000d02e00e031074150019108d40c0d12840412120308050040389450411982907071541d2911404042d510249440111403640c6400c00000702e1480000350903140f5115007401e01c01c192507420b021070150b08440030040b50b080d4208000000a07040100400c1018401e40341c00603a07100c41101d159007081c0155005005040080802c01d20454913154030041d25840703160060001240e446a91450041c860001c014605e6946006c4c14402160f01d1642212001c40700c0020494501100300c81e1341c0903002d401842c540c07000074030450200fa00e420080d40400060401c5080c19691030008580f0700c1160702c2030024a050741000d111030b0400051055000070706942c0d00911901d00401903038281c1008000ca82d2aa0b182034054a6030380c4100341030001440ca038882d808007424400c4a10000590802d01e07a038408081c110001401240b854145445540e002c40c44035415280c20301f0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 531464964 1250 531463714 531463729
    0x1503021e0301120b0a0b060d090602040f08071401020a1a0403020f01020f040f0b0c030a050d0209040218030607080702061501170109150e0c0703030b1f030e0d0905030c 74
    0xc103140d1500820303111006000d4a00103180246034160031030352007602600780403055a4024058075541810003100d00003507201c039002c80d516900c18541c001549412030510900034091a040b03003111062808000686500000d074030010741c1c0144103d1003c40f04404016079071010b44220003012414890302c110b41003108840c080e64841d0081c0107684000481704505803c9034014280040700300c0c1c0110b02444500340524131100607000700ca442c14900720607010b0f003941da4000d8050860030030034001050045001941c0596410b003802802c2903464043c500d848618800403800740c180203229902c0000c100a10a000190084c10b0a8000c4c1000d6200d40311031407904100b061905060015642c0300482c50100c54910390300174080c00c4000910306c2a20800e05101a0752944200c1150b0055400e10042c0254102100c06aa9060a0024900a00e10082002d880c00e60044481c41c4080c1c0405403020358154021403140302c00607054a4103e03280f0142a10401464000c03203070181d1101d0007080140c181001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 531466214 1250 531464964 531464977
    0x31709031602060a111c090f0305070e0903190302030a0c08060d0308061207140a0b03010303051602130e0d080a1e090201030e0f0a021e061603050906070c1d01150302 73
    0x1070017030580d410a60903240b41040d22480000d080101d200e036410300f180d10100d0f21010b4060015208941465602c80d2640d03110107001d90400202e844012a2248508004882c101044140045108a04640302a000f0b4104039200030b5020f00b0301d0f140c00c011602c41c1110b140304042c004c207101c17a50440d070f803800c45884000031700840d00000c2000c9040f16184080000500601d01c1e10394584c551102c1400f8001c812580d54404420b180041c801840042c0d04070301070300c403180d48000c802c10f000c0d406070000940c2d500c0713a15640f4200c1454424070407404d9101060016603002c207520f443e010354031048400b004541824003818844034114094035160f17581c0d0b030420002e00c2d005250102d60641101e6200d41814100d00d0003a00d81d0384800103900031410600c6400100c040b07001032480d01e02c2851030110f46184100c07540b0000c00d408041c0081c00f054090019142046006842c0d0754841d50726280c006500d801c3d500070801003e09200c440b071458080003007400d0503070300b0200c4440c0d8403050b1050150080d40044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 531467464 1250 531466214 531466217
    0x30a06110f27010309020d060908090a031a07110c0108060d12170609060109060e030708010c05040f05040e031b070911090f010c02011b060b04050103031709031602060a 74
    0x20030546040692100180c1100b0b000ca420042000d442c1d2055040700c0003810410030b041c90308040a600c00740c2d5500e10384d90754141d00420003244181051800031618400c0003003040c0c0c481c6103035902105103c580b2000000307000344005540c0c0103032507904054400300c030310442011466001c0d00341d091040d44256034540c0c205002030803841034005940e0303d407104d446021402d41d001400c0c0c04020100e190b410b044840c6c0046080d43c1d1224a81071010000301001407501610003030100510380388a40d034608210070001460030034000c2114100c10b120080c15917100c0d10518040420981001c22145004d01c145401158440c004611340314403110107460642040a903040315000d41e41001441c001c0d2b60042d503103503091142500741c1c1d4094100c1003002e0041a0203100e810045080d201d200180d8000f558858603120031090700b501003a0b2481d0540151070125a840d401909050000041503040074070215101c1c91948401590b035140a4040d980f4011200180030501c00341c0fa0950150804400034284a01039 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 531468714 1250 531467464 531467467
    0xf010e030619020d0e0a120305040b130f020d05010501050a08070b09042a0c03110d090303120f0e06090105091f090212061008010e1212100329010b09030a0611 70
    0x61040444c1211100050361140e030304441c0d048020007481201d001c24462550404020905090320340b181040401071801038040024441042805000c0300c07103002c9640d00811910640400d8604140078000070300c9428060454884042a104404074000050741c1c0c080e003545050030744200c10000a818003045140d0040c1e00302039044c0c03507c081e000c01545415002d0310b62a8003458245401000004112020801c982140040086072a0300407402000c07a50140780c00c0340720755007034206d403002000c1490a5011803441d29020a01005001c40d8951140340207600821140e0303034040318030b900c0b05009040e50031240882a100310340030a40764030840c0428000f0b4014500d124491641e113107091415a02103520382e51035802080400302c00d0140c01d00c1c034040345020f40301541000803032007201e014054070000c0310f481403000128039070407031004900203513001424041c41183d02e5018800e01e014150015080e1120040003056100300201210203003400540101010301098503158001c1c000105182e801960 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 531469964 1250 531468714 531468727
    0x6030615121608010902070b040605060a4a041b090618060902041d0a020712080711010603031b050f0f030c190c0b030a0902060307030501050f010e03061902 69
    0x20901003442100c10781003003045102e520701d001c1e00c0140b05a011882060041110b9400030b000d081c041030300194489004034898640708001aa01041c079001240d9442c03003281d6aa007003110307001c0002c50380c0c5800c070300c440b48444008200c00784090041c1c4180710390801507404200005e18001c1d5008410509103244a9071a8840d62000c094811075031020b68484e61515480607501240d12840008013030ada141103103803502d084146a00c2001800e1074202d051401b10000f103001915030112051154850300044050a00110185c0b4006040c0c0344040001e041245102144205200d6142501e4140d06e0f403c81d4001494440340340040c004c0000c650034050000d41400c4440d013005861210001c010285890b018505c81c010320b40700b40d03150a41100c0070301e01d0419000c18108002c550540e010f0030b00440d1b8a5486102040203400c288500035046140001000104c99141e48441e0680b00c04441c10072a0b0081200112600b860300264164550817603000714460116005403a0a41040c12402505008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 531471214 1250 531469964 531469987
    0x9061603180e07020d0c0302070501050d0f09080715020a021b060d0e0d14190e1906180503150f1b07060608070f06020a080310180c08070e06030615 65
    0x1025403000008030184001d03c280c89405104031500ca0019152020030802a918025038175001882514103101000500c00484855600450700f0501c9120701486103d48e54a060805a03204800560340c40b8001e810740c4810f030116000f00c0c0d5404815a004142208180e60100c11602c0304808103a44903208010441c442075403070040109130340354007019060b44407100b98050070303400b04034032440503207101000400c01201d08943e61805441c8503180c03e00c0010200000724107102c0342414030001602d141203002654075440036006d403204001800501480c2e0b50b07101410b03595907560820030341e8181608001006507d059210940c03000c40b800a1807014204441520050350002c2001ea036002e8403400180f007411001c120100c001c01486581010f038a10f0144000e4960101c010000c195000010124091b1f004414186010303028400308100d544001c140700c00020011680100b000c201c684001968450003010083c0c040003016016518586c0c0f01010041c129200d810324101c5014140008034048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 531472464 1250 531471214 531471257
    0x1030e060a09150e0721050601080a02030c090402060a08090316061a1c080f092206060201060b120615070308040501050f0c0703031515180b09061603 66
    0x480340400005038510745800e01c00c041054040c454808642440c2141c15190350006170f903000c81c0c1c01200c4410840c0000c81001956800948002d06035109040000c2a94200030850408942c421000ca036900540c1ca0240709440c101180c00ac1c0d03101400f4802907401e0307030069505d164041560300990749000b002c0002d908000002d40015900c0550b52080c80700030b040c0c2c40400c034641000c109c990b5854000c40003040c0a8508160070700600c00103000c0758181800400d1000e90b0001e0074020050303044500c0043d1030080c0303180c040c05c10340c440c40d0030407000003503150040c031441c4195000b40b00201d1074029482c10440400c1e0015100c1900080e040079240700c03e5103000701800d0442c0c4a59038404503030400b410121b080d140080c24400c90000c6101c1070040259896048850940d49401c0c0803504814003079424510b48040d5101144511400d400c402c421030740101b188904015a07003a42411945980c428029400340001c455009203081059080e002c030000c4842d4041846450201004210b40c09c640500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 531473714 1250 531472464 531472471
    0x18020a090305010e150c04050a0512010603020a0b12101404240b070b100e0430080a1a0a030803060d06060b030f0906040b060919052a1602060901030e06 67
    0x35049a0400c0d41030041d0403c0b007a40250700b806c440f50500307007040c0000d51120307401d00c10984a45110707040404814130a4000c40e0042d0b8004003010241ea9651042411a91104a9018509c48640700040c1d01000c0e0380040b000f40c0302c5210740010351b000c1440a1000800b1700c54885082000d40491480c05624041c0161001c0d1140d0760076161105e0241c906031550707100c0503281d20240f4501040500840d14001c9174a80e200d038010020408842c800c4900740045109000184503419404400604031500410018069090013004200c04c5640320120b20040e082100c0650740580103076410804a411003007d5900142d00170000d03000c1303691560f1a9030803940b01e6448145081004803c00107c60003a00b0880e5100c5801c8014107024a4541e403044120030005090714030948800010401a031043c00c1503520a100d03005081200b414a0b60f46420400403981c0c0c19030812400360020003040d4001c00c1502c440703c204588610300d410465080040542002092a0402d0798071465007210000c00c00c00c5030b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 531474820 1106 531473714 531473741
    0x3031311060f16050601050d0c03150605100c050d0309020d0f1103010e011b050901080403080c07061b140915090f030a12090f18020a09030501 63
    0x5580214035507441160004140015980070f202c401c203ca5901a104a4000fa81d9070700401400703020b200c100278040703040303a00204006000894200c001d0b41c1c1d2300d40b0101346c858641c40070038104a450b03414403001a9a040705807090003004d02660f82000d0032840c007031050040540101e41c4012130070364010700f03201820954200784082d10511242941000b0003c1c40105036000b0203a01a2140b0f82290011842414249110500500c2261703a4084181c4842d07d403583c0d9034a06031205a8003c140440b400b400300078603c005081e51084c8142d43c424908807008412030708034000c000c00300b0071b007114540a0f8108641c44c440d50f18005880170114800701c01564594106000c1680e4182d41d00905070980701c0d00c151402001104e41e441c0000303544c070740c0c2e41441003a034510030710303074600c4481c81501d009220200019001102c690010140d07441c0d1410a0b100390b60b980c0e602c00b42120b903d03880180 = true := by decide +kernel

theorem cover : BRFrame.Cov 531294964 531474820 := by
  have h0 := BRFrame.cov_init 531294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 531294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 531294964 ≤ n) (h2 : n < 531474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
