-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0911
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:53:56.85622+00:00
-- url     : https://prove2.me/submissions/ce570410-f373-4041-912d-6dfa3bd424aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 163669064 ≤ n < 163848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 163670314 1250 163669064 163669073
    0x1121404030c0206190206090d080c0a0305060a090e0105180d02070e1801021b0708070308030a200d050406151d1012050c0306180303070e03031b06040c0501020102070519 75
    0x756154041c10000c1c0c43e50240005002039031f10241070303d00c0d0046100311103104040ca0322030100300b403191080200030780c10040c2c00072040d000f52501400d0f80341d0060403008007103074041080c405c55646076180f1001007001d042054100700407030381d0804000940d8002101140c026030300014490201e450380c0c0200d0031155109407464800d032030b6211102105500000e0010740d10800128142108139504017a158039079600e404103a5120036920004294a41c03c0c40016050358103580320306080c040e020030136070040300d60340302d002000e5121034400c42e02940e640003880705000d21b511921007400398a80081d0340840c00d0080300030340400350000050440305c40c4030008a071140310f0f548020042001010418514800f8a040c54583d100d4400d2070f070103032080d00300183c02182012645802d441240700a9455500c80c000c0c12135005000b00c0d242ca40502c02000004aa50511010000942ea510000e04201d007020325140c00c0402d0b01c0d6100d0b07811603006004000102d0808a44860303400301d54401c090b4400c50900d003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 163671564 1250 163670314 163670317
    0x60103150b160c050d0b01050909060906070e0d08070303090b15130b03211902061302041a1512060405042d06050a050702060a0c02060601050a050d05011401121404030c0206 76
    0x842500301703440080080811100000c400c1c1030b82d0f4212440380060380c4424076140e40b480c00303c0380c03203000d6032010300440c0c0c055000b4070200054000151050701308035400c1d11402c10990042104500203075a0b40d10b803005002c001c000c01c581101e4189890500c480054002031258001e0140e0f60703048c2a030392000900307666400c1091018880c01c84055104180000c40014140e4201d0300000680c0c854942440000520124620703100390380d41c143c0b440c03c0802a80031b010052400c0c2c4e200e5684035004020151440d03072284841d083c92900800c480d0f82e100d165980d1708000f00c40140909000300c0c2000d003408001418055060051596456080c05041904130320039090800d940d40608424070700300a00803504029081140310b101a03808a80d62a00c640c4404000c0300c0b100c048500040e00040041070130b03907110b20010072808000389081401d0503544208c1004075042a8080074000002c0c2402c00d40c2035801c024008003180003e0b004100c110349000e44480385200c010801000c101d0201504021507a8080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 163672814 1250 163671564 163671569
    0x10e030705031507121812020309040e0f0c04021303170d020a0f0e06030f071808011a1813060506120f0a0309120c0b030c04031505060103150b160c 65
    0x4040300d001c002c00c041c01c2010b00303600b613800c880050035000710091131107100d011345070b01440f2001ca0060454025119140001c45002010003140010440340680703541e2806051008842c0c03001922202422035441460942e0341c0501a000b140140080d40c802c80341da407501d2045940000c0f910704120304028000d07900e440b9101ca03050515102041455100c0d030300108298082e003068a07080c1410000200f00b0206007c2182c01d02a81221580028000c51244004080305031440200d180030340d0300d0306100340c207458100240342c103110070380d0004001a241481c0007000c1c080c000d81890911342001030803005c608000310400752200d0348680100b03c440d120250500e80f90b80549080d038021036130078800c0c0c588a41d500700083c4c000079148407000c100c0710482c14400c858107900501490341c1e145024005a015040240341081116080c4030010101d0500012811901110840001c0300d18050001408441100c0d0342c00a041b081c552040c8008104602220703012030003500080c40c21a454034003848588403a8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 163674064 1250 163672814 163672819
    0x80f0f030f04020f090c07061a0307121e03050a030b03030909010801020d1b0e0f1f0503090d05091e0a030507080a05010e030306093909101d010e030705 67
    0x10030028030071690100740960b1084401268401e00c11003000b02d807010a5507529a000d80070090304000a03000d512032400c840c90306400c40041c010400000b070030480c1c17a42c0208400302a04810004002c0f102400c04d00741c2002c000301c11360944c5103450060460094108400c2455507030442500299400c0041d101590703c0101460301540e15152802d0103034001e654180500f0341803024a0340f246420003415400c00819640344020507580504028040c01d00c941c900e9007018910b603050202d1200b00d100d90390142c102d074448568034140004440c0c6012150a11702c0d0820205129034032a0f940d80600f202c420304201881810b403c1032b06400200300109079400141284591040000ca01c034010406094041c0248001c200f180c103140701c0c840c0c40e84012540c9c617501803040070005004404a0710790650740c80c8000001145001c2c4820404403201c600400c05108203000300d000301d13903490100c1da8200704004c18600262a0341c248803507a440248011032007810b10401034003000141e20200207010040800 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 163675314 1250 163674064 163674067
    0xc050309060d0b130605061e09090f01030209010f08070e0901180303050702120f0f070f05010204060305010f050301090b06100c0b010f0306110a0206060d0c120c0f0602011107080f0f 80
    0x342e504400081401d00080303801540c00104c00901640c05200c0d06040fa02c0240ca020f00d401080c101640354225a01c1000e1240d030414405030700d064944880c07030f511868062400c0c0c0125411401000401d680591158a4000c001d00c410301c0f1003d00403507011300302d580c800e07203800b80ca45641d10954054143c0621a2202c0c0861400e26030a05915030800c038018900743e0260b800c05e1076801c5c1c1e10b0070a80301e03252244032102c030104490849994010000e05e1514043c005000c4403d03101e50b5824207a0744590f12440010b0703141d20042c011040f051611400030301c0100c000b0060f880b80303644c1e92580f07a90001c0c145446407000400c03074a003890145881d00e1100d0781c8450458010b40c1c4a50b07072103000d2001c0340001d40700d040c80c1c160f8000609803460111689140d03d90024006542d0b51000c004050652074000c0360015000e00c400110120301211402006110740c0e01400b42c6800c00b882d901924580d54003210441e0704204d0221403c1c800b050403601ca19030000542603075a2010401000240700d0170300c252005100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 163676564 1250 163675314 163675327
    0x3052a03130321020309100306051206010302010f0c050c1e03010e060f100b0301030b040204090f0503310b0309010212070c1110080a0906060305030a02160503010c0207060c05030906 80
    0x610760021010380b446240485940e407102403034440c1c4000c18508a8015900401030f1100c0c601e880c0d40d41070103034041c078a030105441c1d8450000c100a03886c581050002c0794003060041c400c642e0001c0b00030303101c1d10b2189000c94051406440d2a035507441003180480c0103044042010b500c01e01919050390707081c50301500901405003441681d40d583d45045030f0040c1644802000710703005c071110198060072241c29601c11421a401c40e180c0c070102c204007500403039210340d68801400015940a080c14040b500a2011b9500d0361840603006002211a0140900c2241901a420301e4207060406810035603403103944150301c1e907a401c008140284901d0828050142440d810081110b600081320808944103c400302d4500d031800040c0041c80b1044442000416141000154020029400305451a00405011402503030701c0e01c600d4190380c4030382080b5005800407404030b441164503002a00041809600800c0640550107000f5105d040ea4000c86080014512000b42409020025200795000040c040c3d5541d10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 163677814 1250 163676564 163676587
    0x105060702032820030703080309030418050718080303180c0414061302030405070b0304030314010b0a110304050303040b031015050912060f0417071b03020f060703052a03 75
    0x901d102c1c0100c1304244281c00e407241c440254070b504004007a0140c000c120300e50441d07507000340d0303a00300806900d92481305010004030813600d6194030061841640c2d00088608100000070b0401c00c10b84682c1d44800084801000360000001c1103030350182c0c40d40e030003144c2d4200c0d402086050480f0541038581c4641050401210b512014001a026079403c0311008a21003c220401e400d0780801c03100074146030060081007000003404402160b10910034a8001000044d545e0401540352082e00301281001c8003240b88911250480001624070301054001c43c1800d1030000069581d125502808009074408800b060207045002ea0300009030038080b1112036480c640340030040c4103030040178040e8450071018200384680d03000482d00031700800c280814030b00180c0e503a031101c0c800b640307008000d21b02e83e007010400c03000401c04005041c46801c0140d0001301100e0324500400521405040300a4890201000050b002a405c01d00320350b450046103503804588100070031076a0510320340700e0138012540400120341ca60807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 163679064 1250 163677814 163677883
    0x30702060d0b09060d0b01030f0c0803031510030905030904020d021c020a02010b0108130b07021c0509030c0405011d0a06050406060512071b0212030408010c09030b0f0402010503010506070203 84
    0x460082e101001d2940c4c5800810070083c168190151020228000500c042040c4001c4489410301407004c1030f0400c1e5840305420b1443d442160031444c2806410350401c0c10389002205800c0408283c038043c090202c09448040e180d1140940c924810ba81c00a045410010030703030141c0d80c0c401c1600459980722401d40240340007039400703219010015407030304111b0030466006914845c080d904209844035460200c1c0d8900246981c084c00399000d500c24418021b20b00f050880e0600601d0000d42d59940e22008040189442c08001030380b214070a5052100500046c0e5619440c01580c0f4181c06a81069883d07465131400148040e420164201c0c0c1051000b1030441d1304200188600d000208900c09e0580e60070004849440044c484041161512040c00026213010044040218860407c1d42c0c58583e850b08a03a08541d004d003a50000b2031b410b04810800d11a20507810342c2c0c0160950700b0f0543c1490640d000a0842c881405410300c509030110300201503480c200103542090182410303000c20b544800b42242d000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 163680314 1250 163679064 163679081
    0x703050601090b06130504090609080a020a03110a0302030f0a0302070615030b060d0209061003020c06090a03140a090302040e01020c0a06020306100302040803030703021b2d030901020703030e03030702060d 90
    0x90b0b40c14040ca03c6410f04159084071441c2c1c1c1d034004500c50107420701d400c0001606a001040e1502e60b00c900744d20001c40e94141c000c001f141c1c042e0f002032003914014074010b040d1010402440d040e5030802000e80c1e02094003c41101d1600300c2e8103000c117540711030103c1d0170780080c05900070142c010f030300c0c001135035440404068025046c0c9000380341c46051f41d40da03001002048a18044001d40204883c00422500d003000c5070151404807060a0250400484a004601e405401c48024000350300c50001e038414150441c1c1c803066801100038010385407aa5074440030b000306140e484003d0149540e4400b81c00b000300b00b98107542451700c4c484145d803450f90742070034100c02035001540c10130310030031030301255803c40e40c0688200c9040b40d0140780914116580d03401d00390001d4000360b070484a001019140724130001c001344243c000303046210410b11450b40341d40200c0400c05441c03500c0c0b000d940c0e000700b054501c40c0c1e8000031460110ba506190040802042d034020a046005801c03000b07401c00400305c0c800302441e502e03810a040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 163681564 1250 163680314 163680329
    0x21006031101200703021e15030402100504030c05091915060207050a0303170604020f07051c030902091b130902040e07090302012a0b1e011401021b0406080703050601 73
    0x2e8541030b1814103650f24500030f24583c05204108010305104044080b100d00302c000d40d4840040001c045014002c60041481c2c1122000041000b18503183c0c00a400400c10703031a00342d00702402c56459214000e19402441d10139049000081d0980ca0700f580009080845a1001c1c880501031100071b0340d00704510702174038001d07000382c2e100070813542400341d820700842e6015038031010f0a41845030003614010011303100315040358080101048502020b802070402600c520020f00940c00540301d040f807046600014401014101180080960b841040280d0040e524002c0d03141c41507550b1f00340c80c681c0d101d40319816100d580c0a00740065a004194050b001b21008800f075480155140c0004890074046404000e0214250300b4580010006501c0d440c1c10384100101b8a4617050907540b02c10b12151000c036209204036a00d003c91918008210301c3c16801000000d0f1100804000000040e45641c140756003008220b0700c801076140300b40d035181c0014000341121410307a00066100d041140c2c880209005940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 163682814 1250 163681564 163681577
    0x33090212010e030f030a0b030303090d0e0f01080c09030a12050403140f0a12120501030605041407050102100b0301090b0103050120090a09020724022a150601021006031101 75
    0x90245a0601540100c854641c0183d481c1c40d40c0d00190810340c1c2c1000d001da04000d0b6584203400d1042d241000150b000d03040d11002071007006000c950003807404c4607080b0001d000d00000c1c1c2d00a0303956604040704641010700070682c82d45a50360303100880d142800607000501500d4030301d911001c440e60060014401d807802130703d140c80042000d24405544101344c40c100c800581c08406644080358017807418a07000b505610b030030110f80180c0f00410301603440a03042590050b64901c248010400618200302401c951700c3e010340a403c5c0b500c40080d40300d6201002269507a9101e48408400d50380030344c400750000ea070003143c0031100c0d61681002402014882030b603200400801c1c400403100d800000586220102c000c0144c1030340d50034a040800a900710500480311529040c0001460200c1d90940b540740f107183c408010b0702c4280e40c0c3c0b420424507a0410f00c00c01401d91101804c07800e000c000c22201c84423022250811510303210200100d18010406921001062030488080304118061030b001d58500c009aa828 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 163684064 1250 163682814 163682839
    0x309281712040e010b03040f060e07050a08010c080601050309071205030703090e041101030213180c0f09060c080921070306151203030b0105090d050102070204180807330902 76
    0x5030003901c25809850010410f0a004005800b902e00046601c980f0a401d11001d80003150703103113000d440d01d22600120726040392005000c1c504010780b5810052000d0002400606545240500301d03141c007404190401c200080041c08001e800c00800d0020501a5003003020501d090174015100d030401c0004500003401d00c840020540c2094a00d94000c0fa0400310006030302c40031400650003503000c000c21001c8000d00400c000345081c0d41f14400d0924104043d008528000103040081c5041091043c0e1403d000c0c00c2c1d401131080c1948607030400b284a500a5005980f040044001420b245a6480d41c010000c90b6214080301c0c00c60200f0b0b9501101c0c0b240700706000240100d00001a00001400303002010655442d076240030910a80080c0c2000c28181062458200d62001080302c1c0030f507040301643c2e0382c0c0d000940d81c801c50800f0310614101c040701030007400314901c1a030340b0b1138018442e0b00710180444e2001081e0721002c0e4004451001844910701d00650703119101c00c52000540710740e1409030310074004960507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 163685314 1250 163684064 163684093
    0xa1a030109050a150b0a1b0812091b040e0c0a0b040e25030203070c05070605180307030305040303050315040207060603020f040506061605030d020304050303091207020303092817 78
    0xb21140c90f64180322055401c5d040c600100000d41280360300314200603002101c001c10351030301c0124250603402210090354620350480510046003020742540c910760310003a00c20f83d1502c03605400641c0040101d4000c0780031000d00d0200f610304640210764a40c4002d03031400000303628481c40c3c0104211034103890991160759078598403405044c240d8003d01401c0e0050354017107001e02d1180e80150380c0071400c4e0500000c00e04c50754a503286040c1e819040a40401da0024034607011008600411020f140100c00412280b400c60760000e0080c0524030008040c81404008641c1c1550f14110034003200724050005c40d141c5103039042c514082e01c06880107071f000e5448080303403106a0405005081c81039401800040c9000c0c01d07406c1050400c284001d05480c140010f00529602e918503000031401203005000030740d203a00f003058290f800c041035142c0719940800304010a00042e100441540e0001034121640301003e800c80c0359542841840c0001107508030607140e00858041c03000c105491943c0142d00c02c442550009031032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 163686564 1250 163685314 163685321
    0x190e03071a0702090c28020c0306010f0b0a0504121a0901051b0a030603020d060c08070903030207031104020f07060c0305060a03050606040f09080406020604030e220504020a1a030109050a 82
    0x1c0300c1042000c100544030140c18110b40564100703107940021803804100800468120301d48501c0009690250305102c0280c550402126a05080440260050354900014452a206103225805601e40d010403824480d80c0510107850003800080c40c62004190a0701e807031107110488846a0154441a5000c1042d03400b0501c0f480d8030610300446100664810308164428903007003281004c0415480e12004001138075071080c02e03d11180316110220354154440000ba03c7e0080c007c012500304200740d80e0410110b9800903c42d8226508012040250342180012801900c6400750451a03420300180e900c04116156100032304682140c0e80c10030141d2646402c100202e8411310014125922182c0400c07074a281991003090b0b0551454000542c40120b5500c0c810244c009910040150700103a04000a16402121044400c03d04403456440c001c10b102c0c05856454a01c1085a14075076030f00000340454807241440d602801940640c00310a80c0705001404130f56109000303500c00e250514010a065044900 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 163687814 1250 163686564 163686599
    0x30c050406020d20011e1a011403060117041b092d020702120d030b030303041509050f060c1b0d0c15021e04030b06010c1e0503190e0307 60
    0x5024050500e030480044501c0846005614150303401c400d2091312450b800d00ca40c101e0030065401c1c4c0705c150110a0100c07000c07030791400113034841044c0000d07642c0c00a80c1d01510403d4070521110440c0d441c1c1d15a84012a5040c03044c01c0c1e030542d0451076400f030006001c0c00300c0408903080411101d044400d40c4a455071404d56081c0d02c2252003d411000b041d00d2002e42d00c5203400303a40204600018140341300c680000c0c1010b0321181400342c29400140c3c00345103072a414080c80300c0d040c03000c2c0c1c01146142046e6481d605448042c00000620755070340c81c4610200a01884040d24101c5103c0817500c0314207040303040140d1030b80900740c0f84c104c0790500365605801803001310b070b8000c00b00c600351141d07013040c80da4be107a603507501041440560756907074200490844c10309602200e40c913040e452410503494500318070f0000501c038000b1744658144810005e040f0005880c0300e41d0701003a8455007164000148042c81d00c9891806107a2100c0d8411f28119100403c0baa03000f07004801d0950201c0441e51582d0341d4107005403011107505e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 163689064 1250 163687814 163687817
    0x605160e060a02032709010f210201050702130204080c03150403080603190b070305011202030604030f11030c0f0c090c041a040b0703120f0606120b040209030a1101030c050406 77
    0x560311400c0c186044409000d41e00500d0058a150000a8280041500141d12282002c00311a110510304e0b0030141c00c002d0141c4102030301e001400c0d0400004070029024850b000401ca03074140d90080c21644a60156105113070301814103070040c0d0620b01070101a41050003070070780301d200340c202641281c90002036948a00401c0104249181c6441e00c04444100d401800310360036100f074840301d85414401e50b6040da4094010780d0801b4141c20003982c020f00755041a404407442e0b50491083c5805a030300800c482c1d401c19414181015006107200e416a600742c00390b04000f08601000c11901c607519804601c1080b006800c1041d1f8003c02c9442d030030031407101003d50320745900500c1030200784145c04588440021003001039416074207181c0d07a200c0c092203903407004030224001803d85003e0980d4440c2e82c06032076111403001105110889c10020001c180d0342000f4043c1c00c40720740310a01c0d0052a03c443d41141c40102000e0305603612490581016105805050102800a4078003811030044901c200159003c1d50801e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 163690314 1250 163689064 163689077
    0x4151e1d01062403090f06140c0f0d0b0102010b040f0e010c02030c03041509121a010605090f010503060a05041d0d030c090b090112020c0120090f060c030c0a030c060516 74
    0x1a007444504924180610050603566024170740442d0000300d05100c52403250a0100b18a44411001d100100c3c0142c02641204d000303105411001409800380c4001c566000400920310728a100100e026095240e00150884d103000740104034168650040e02800d180d420013030100c8140380904a903284100030414405400034801072000c0c0980c4883c181c4d00a01c0d504d06000d1454035614146040b6468801c01c441d0050761501d084485070001500034010b0290341002411301c0c4545d000300d0601c00f03c407504c1e941040400000158a039442c140c0f080040e05026000f0000c110307104107104036a00408000c04980c0c0329248600003054480d01401c451101c2c195070710340d0428032708144522540c1200740080e051080c200c46064031f0380c0e002d04c00f6050b500a40300c00071030004080c0b410100c15280c034010520151404024007150742c1c035a01c10700440d403842a01e04942d1011642e03c01429805014103001c114047d091180050540c0b10860607412801003200308019102d4500c121005100d00c40c0b03001c0071525 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 163691564 1250 163690314 163690349
    0x32091c0b0f0702030c060a020901110d0f0e03010609020708120a02091c0206070f0b06130e0601050d030c1a1b12071103040905100f0f0602030304151e1d0106 69
    0x40700006550000040d00407079041c00016035029041803000c0303802400e0950b0125541000307691008041140310b0b01c44019210415508000034150105000e12000b0b001c416070907090680c0302540b0078801840c01000854449609151038400ca602020255410000c80b0b80030510359032503031080f14002600144042c0028446038101840c80101d200166480442401002d0224403504034000504e8400c09444c001842e02d6403c10410514844112441174036000708080421000581c882c1500d8085611040035030407854200d40b60070010720010203481001e40418401c1000c003000c1401078115440c800c10921286149405500a005002410003080c50208e41c5441c05000754106a0034003200b524509074443e03c00c0015070b1019601801d054510780000c0100d041d45c5007881024010b40035030b0105441c40c0c610b0003552800090300280c006a03112914010055156124040c02c03901403010316940611254142c0042c60034002c0c00305095489484004062010b200d03800680d9819481c0020610 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 163692814 1250 163691564 163691581
    0xe0102030a09150e04050a060503070902090603011202030f0a0302070609150c0f0c05030d080402030c010f0207032a0806090f0111040e09070305060c0a0e01020a03090632091c0b 78
    0x1601c4503c881408840b420901a58a8030700400b40304c0c0601c44000710344140b918040c10705e440c5066200310809807050000c542241e0f01d45d012281103070080300c6075100142c02400045c0c00c0c800b0440010a80b4850402280205a008200380b01218055210b920b5480e83d2104140c2032039140000e8440002d000b49100b4002904400c82c5600850103031110113030060303d88010a25102c1e40500310000303d0343c8041007004600e800c01014108900030710b09012203401800001c1e40d150b0303c83c000101192480e01d6510380b01d001805c000c04002c464404011b00c89540e6080c0a61992000c1e038010000707010f1010b540c86139071014060440c0300100301e61706c24078107403803c2281c102c40e22001d010f801003809140b6001022481c200109030261184841140e034624105501a01c0b03500c410309414195044808044003090f00701c40c02d00100c030b24504210803a0740401e950b40c070312144001007901034000603c0300841c01c52403c101030702c1d0303115043c3c0d001e1f1282d0448a050706203d0030300c00c6009043c0d4040400042511 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 163694064 1250 163692814 163692839
    0xb0304080a110c030f0a200f100c080703030e0f061b0703030908030403030b24071e0210020708070911070212030f070b060a0504021c020306010e031501060e0102030a09 74
    0x803421080c0c81a241003d000a400c0c14805944c200f030542c0701104100078000d01c050b401d1805041f145e200002c0d800f4500120760800c1102c021a41304503e80c0d00000701e680c0c007411010300c0540c0d109164030f075500c40c5450090010b142000100c9454420b8880303000c0302410000715507001d590070212105000c80e288031009410351240808504142d200c07a001e0000810503005140a58400c2d00c7c0410401c4480c6c1c284101e4020010140100e400034903a0a8003113003c0c1011283e0098011b201000009400e4110305904034030000001e4001880800c40001a83d020411400b070b10403100c10b50380c4180e40c900e4400255a01c0510f10f00814104011180042c54070844d00030261104405880c14481034588905450300500d1080d502c640790001004180e141001c1d090001e0002100d0031402d0006107106642102c8038070324800403072640003012030307030a80c05032344003c4440d2001021141e000300d050032002184003081c0705000200e45030381c90424031580084166205000d10b659509d00a81c60b044160000c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 163695314 1250 163694064 163694087
    0x1e030605043903170412060b030d05040f0306050a0b0910150e0a17010e1b0102010605092a04080d0309020a0602060c1c060e0103110f09011a070809030321010b0304080a 74
    0x4404200310014908907441b82d4250b5141c0102c80c00146244500245800c0100030007008007041003c100504c074032f00b00c1030f08a0003502d411201c0010560380e4010064010603c418006611281080810501d01c018489010940341c140b00803801610600b241a54545440d0303c2c0550320070483d90701400b042013140c0c11096100241c1001240c4411401c1030302e03040405011074481c0c22444018401d0880d602401014002d100584082c6442d1510b458508540d980101e6003107038080060080319107500850b000d403409004141c0c15186049098500034005085801d01213005a40d0764900248080c00411203a200f03901c10b0441b0b5140112110400c4884e0740042e000c114a070340d0303800b000700700c41c610034003641e0195200d6001d0655002ca0342042000101c00301000900c11050040148481c3c01d218040e50442107100034425114901840d01d100f00340a0708441581520021840c4403444848400038410300302d0710b507400c1d910350341c0322000c9626a1000301c0b000362800e001044084142482140000030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 163696564 1250 163695314 163695353
    0x30a03080c09040203090a050601051f0e040b03010606030204051f090510091d01030203010e060c16020f04150302120f154201020304050a1e030605043903 68
    0x140180c0b1200007400c0b038105441d201c0315944440011010000200301e29409040229403030450b100c40c0300101450402a01200c104200d4006010106d82d21903402014410b10002d000b8040b4503211b00d0001c00035085449801d10902d5100b4015805c3d401c0d0351161402e0412980e1040007150800092003480c82d80d6003003810401240c035400251031034060038021400f2161405030411035146004140c2519100020017400750480320034005400441d500b12402412421480681100180005910286403000e441d030414280704904070017022603000041540d1085a120390030322041961a550754503440c90000380b542c40075004078480a0388840c034587c012180d1180007000010441c031030115284003883d200d01c40b689d07003c40c4000a5011000401700c1c01e001e00c015400c0500d004000341c00002a4031070344015442084081440201070042800a59048003041c00b050509140007411220703000180c841000c0658218141c0d00131409168080302900750310341090307605645640615000d030b00036022 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 163697814 1250 163696564 163696567
    0x90209060d0c1205070303112a0102011509020309010e1629070318050f030606060c030f070c050306060a0509041b1509090c020c130509010b060f071a06030a03080c 72
    0xa2140d81c50f81e2104642489403020b0401c2c0b520350702d0080c103071b40e00c4000154402d070011685501d0400352400c0704240d03007000d110b040c0034007015400140e006019500007200014445074000ca02d921003500158011240d4030020844c0b4000e80052684820002008070b9a080741d0700c400304003108800d08034010700702d003406d2104034100700844146080d900041c011000320302d00c04000002240c83c0c200100052606841d15016118802c001076216000100200d214401c0405e9841c090041002510f5805060340c40c900c1c0d80d150b040c14044541d90b2188580740c800c0c030450300027510320b007058000c25045610162660f500d43c1c071665509460740659150303040d803c021036040059040307900b0101494400c115210b010025040070742c1001a41c02c504002810340d03221800b030342c04946400c0144030503403109a000040980340e5014090143c251449010f40c030400104401001140e04d03c001c21025124110026030290340d0122101500b500310b80d210341c55008640b144002c1790043e0f55080d40304000c5010746 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 163699064 1250 163697814 163697819
    0xd05070210020d05180601060f140405030703260405061914040605040915150810051011010e06071e0509060f040302031902030d1b050601060f0e04090209060d0c 71
    0x81c1c049802440100c0400d60302c1e00c0074845c660b0308a4601d1a4520000400740105604001d40036001000c00c1078500100400342561205920b00c110075038007e020028103581007640e07281800d440d02c10300d02c18501066034030307441200911140c40b02118212031003e0304490070045000ca40c0c0c0d400d941c0310384104051005d801c10181c843c41c2d0940041014100c0e6071a0316440b10b0402d9424021075400780c4d000141c410914809000b988080004d15030580c12a15142c0f1701c1e1b5684040714200a110307a44055048103000d08030302d0205401881e030030354a00c0490003c11002c482c4090050795200240c03050008580106150804400711a4141c4e0051f40d190400e18600a1048041081c0f580701d0b030071142c2940c0021806004500d014090441c0380541006000030b5421107400094480080b50308074410303c00c5110350030a170000047c083c00e50b020380110550780650795034035024110542e1004c1200004204821031103652038107220700200f1a401030820b08840c0c2d200360a01c19141002241034959268140b0300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 163700314 1250 163699064 163699093
    0x10f14120109020a030b040b06041e081b120d080601050a0e0a08070302030609160e04030306210203010606020a1703090a0507090c0e0109080307060b040b04020a02011517030d050702 80
    0x30900a2220a40c01a52404803038401400c80d0000004e052160b07080040680b110303511202500d0a48001d442a00b02080c4c070b14181c1c1c0445100c5034800754550041c0650640156001100794100b80015150b507000e81d05160070083d281d064034250500400c3c90712010540c5548164064600701a1504126403400b018400040d59003005034800f140503407110070203004508061007600e82000c144001000c42660121803951205190302903903403200d29000c0040d092502c250040c400808411000e01c41110010b00083e5281400c0503059001c1d40c01c150b000900948001404001c158002d103454041d014007003220344c51a44003500d500c440344990743e0510040f034003e0001c0300c01020070391000550520340d03d1010301203506201171641880400c50b4100306192020040380e103580e50010340098000480c200050040c010100c0c402d410510105185007255015400320341c688001980710060155140ca26105d410340d1000b4548c840c0c0c105200100302d20801d03800072a080502e43c01518100ba020000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 163701564 1250 163700314 163700347
    0x25090905070302030f0c01020a080c0c06030411041407140702210d03060906031505060d06020c010c030f05041a07020a020d080a0f0f091511060411031506010f14 71
    0x809646a4211810400452404011040c0212150b00c00380ca04944072400103522064004070207400b0aa001030f03801c9485400b400038501031000140381649a0900d800d00001c015030520260740213a260295201c81d107075181c02040c0c421607150b42ca01c1795600030881ca0644a0700010000c030b810021084400c0c40720074070700032050f804030b1508004081f080000d040007403d0302d0700ca5010050403498502c00340040b0300c1390311846c02d104510440205003a12051301180c401421900054041440032820261a04064001505c0203039259010b10240340c500f001a802c90700c055074002d00040c0d082c41e01031440c24010788481d03408281d80c01a91350032501500400c58080b92450100e4142c400007400c8450103801205d40c5401300c80c107140058880c01c02c0d80f4081c1c0851010f00074081d080d42400786080160b4802c008201e00b54920b2000d981960929141003282c2c81c0902100750f1182c0a40c280dd0060706141d211010703c1160144c0d80c50640800069044d5965000040249500c0c003040154443c070191420 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 163702814 1250 163701564 163701581
    0x3020d18110a120f03050307051b0d090819020f0d1506050a0b0703170a020d0f0e0106170c01050901030b06030f090c03030406080a270b1e0105032509 66
    0x1014240c18804000c1040c1000c19800c140301a0840707441102c00704d601e04c115a03225940c5400c1180d50381d15114016500360007031440c2441111803c0307010307590000010407040103203140ca03190301003141d4552010070303100c01e400303118990102204043c8001500e0034401120140300068120100c213001502c0d080480303610318404210094035050104040d00300300000c07100400c2802900d500f041000e5078020452000390b01007a9030090b000020500703039038050381200e04801291034208100c0d281d845100d005440c51810342e40084d403900400290300c50304018150101c400e03190161206600c10710041da0150000301c101810140e441c28008101d0f2103100c010340c00390080655a0701c8130b01d00005240d2421040b2042c0c54042d810500041060715003041d8802d0700f2200306100401d141c041c02e4150300000c014a541042c3d400e403081c0c1401e0501c00010841400303030200030b0325225002941e283c10800341000303118041e00744d4007401c40c4400e00c000704e4829405401c07442100c01c801d41d0b580d00d01c2800751070900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 163704064 1250 163702814 163702823
    0x20603010f05090a0b0f0d02030c13061505091c060b04060b07140d090306090213050f07020c060703140d0b03011d060f0f0f071205010b0a030e07080d03020d18 70
    0x2460038889443c0602400382c3c020181d41c0f040c0190035034040890406c1500d0301c082800303410b440042c0002c42d9001c0c8030002d11194040c20080c01e400c00c40111b180070b04100d04c0350345a04011000500742180c0b05200315084d121010380a424440700f0011001ca15540044003920b076140d540403503004035903980c00b0b100000d05c4540c410545441240c1820010b41382540c178203064951140120900c180d811001c108110307504285c0c00038140c405400440c0c0d0605000d800b4082852400b070410604d11608480329000e100740340c1c03c580081c0030301c000384900792107031030303000b5001c80c03e00030b41e145a0039400b400400c503100c0100004110344c00f5900101c0c0c00c0d80c07143e80d50141041410591401e14040402189900c0a0f62058444c405c0c01d01803603184001401a04007024905a0000142c0c810301540d460010345812940c100055039440300221a1600040382d02070010342480280a002c05001407058203942108014040100c0c030482c040d0000d611003901aa030079a00c030505201c007029030030b00f40e68a0318000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 163705314 1250 163704064 163704089
    0x60506030a0b0310061404200c060403020f06090a0b060d0203070f0510051606020a11060109060f06021501090b0d020d050601030317160f030b090403020a0302010509010b03032502060301 82
    0x20108050503c130741210f0884040c0d03d442d00030800e420f40c2c80488804180144d030002003e50811b0101e00c52456108201c40d526040060402e0424500041a03441a4000d40c260f610000128079140d03210741f810f0b500510707580d1081c000c0b40082180068141d401000c006c00003030041405902003828200141d01070302400021030381c01c0001c0d0a00ca4040c044901141c0740917031030040510180b480040040e13002a260380d6020440c3c50300303140100445407020401d03604552140d82d480390260094403c5005031810f20f202c1440000e546030001071b800040400340e0100951507800c0401c0b40005003d42c0014550258246203814090f0310f92031140009180200c0c060041903055090143c4809412085440c801c90f5500400a080d8076008000038884041c0c6020707500c84018410460207050011221540110050180b004060300040c85524240c440e070001c2c0040e5440611003401ca81186600d40d40513001000a0251102c43c0c60f1203081400e503041e400c54454403690049030064009030445c3e042c0044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 163706564 1250 163705314 163705331
    0x110d12050a0b01020307060f02070b18010605010309110907050409090c080f07060903061808030106032415050d090606080706110604022b061802040e07080303010e0406060506030a 79
    0x6060055580c0901400c0080c88642c500c080000c4d40c80c42820000f504442d960030b901002d011468048030800e03030700b01032440310342e09080d80c001607814907080802030558a00340f030006035540a80074106042d07801a0405008041e00c0d03040c8443d9a10007407144003002410040855410403611a9404090154030300320003c901303080031280f0b041401c00e01c51205a204c85400c00c5150b901914800aa0341d01c401c0124124145620313601c004007224100514148012001051540c0e1582c0400f2600c00031031b1851250100740d100c2800800240d0103240b8070024152400c455190242c4000d2a000b006240c2c0011001041c0d1078a40840342e164000d00d4280e081060200640e07640400600121501d480c054000c0342070940c0000c8401c0e03120032141d155810100e01d0400c25030550900003d40703030340140060003001c29411801a80914440c1b00b00e01c25442d00120b0302032020001206008c1c0d5283d2001549580d0801c0b600400e00c0d038006104492150b150301c008106a150100514010500791101007620f14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 163707814 1250 163706564 163706597
    0x403030306050a080d120e070e090c0d0b060105071b0e06030d050f042d06032702090f0405160308040501170f0402120a1703010512060112060b01110d 66
    0x74115840381d032290001c01024080c1c020045200302c01780c88541003001000a881c401c400150614141b8100d5900520500242c0f5000c0c84480318800d00200d801d030f0b540901c03c4820009a0520400042d041c80003034030002c0c406500030001860040d0003402d43c110103060b0001d1080a0320095042030600f0b0000209120807410104000b200360344a034241103007000358116020159000341d200b0412000d80703818860a01d800d1101c0c0080300580300b514900c902d9500d03401d010b40501000100011414240c1259000e00b15030ba484946445074001c000c007810361544124600c100a001d0300035079a500458030300d04210f08001c0c8070500114032440c0103039182d03807501002408000140180380f640348000420028038801040b40c5c03547c800c1c4e0480d5040b2100b200a0369583c5003148011005101206030b403119859941e403000550f0403500b04584041141c03a6800802780c07120701c00e200f6000c000700310303c03110300020f40103421135003854070189821540c0580c40e00c408c0746400702c01d406d590f0205159010401419 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 163709064 1250 163707814 163707821
    0xd14030a080112030e240a021c02010e0c0d060e060f0402130c08130c081024050904080c010225050d020c010e040510080a0c0801140402130b01140f04030303 69
    0x5161110300041c3d0000641c4028003000042918548a81c03d071b50760701400380013242010450b203c8501640303a2224040307500656620003000313000480c440c02c500581f020b148140942c00b12814800c010300f081d008401e0030301000031405241261019200c000c2060051002c1040318410721103502403000e203082c68014090401483c043d030807502c1c3d040084918201d900312000c25000010041070034402001c80c1040c090390b00c01070300090064010030070090f00c1300ca220b401c40c2200030b98400200c1410318036004207203607105541c4a01900642158001000301d040d04e0007411122003442c0c000b41c9000c44221072102030340c04000c2011219544020151b00f402401c01001729030345224001040034032407650001c0e01c01030180c1e203290b101c0c0ba280c5000038030480c9906003450091a1381d074204e03406480340d840c0104a501c15230198640b590310340001c0b00305010074032110501460700585a10130b41010524400060114414907a060040c1c41003107460a04008000380003a19652190b26159411071034014241e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 163710314 1250 163709064 163709069
    0x6030606090308030403444b01031203150509010504020a030213030f0b07020606100c05010902030601090f060e09060a05040c0305120a030612031d0d14030a0801 71
    0x30001841800e00c002250401101e810a4143c01c10350038007031501640b551680c400490162142e00b0159441d942d903001002000140544506a410141d440c0340b882c250480c1c029006002303d41c1b0340749014034000b0104108000c0841c041411181c0c600006001c000c3c00d103400e03882121107003405410092080e516100f1140e040e2081c00c46080280e28010016003206c2041c0601d52017240c0c0020100c16240c040d904a481a00e103a4038115640d584e607042809001072548015583c00a072000000c907a41d20114142d0f204030001041d043c060480104120740b83c60700b8030400c440300c0d0368402c01800903039020803109000301088500461100702c2d000c00d40041c0c2c0d100e68801c4134032540c4131081c80400386c408603115034000b00c51200080c3c48c1c0e03102d0402c05050212544094001c3c000c3d8040d0000c1d413000540288148245600c040c082c056844c0c0a40004040b1005c0c060005402e15030130040301900d104a00700d8554000344072100c0030320540ca03841c09030389444114080650000070388510362908010038600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 163711564 1250 163710314 163710317
    0x40507020c0d08031f030809010e06120c030a2702040e011802120a0b0c130e150d03031104080307020907091a0901020a140d1106010b1b100c020706030606 68
    0x2040c03040741d80030800d50340d05410010b16410000c400a00f25020f6a42503010300c44c580c0101c00300440c0d0f81c1c2007864165000c94005800101c1d1600b400b0541d00301601200c2e00e58424910f08100e550b0f0355085014039030000b81802c4c1c145a21903001d640c1d00d05e95080024034600068002e2448a01c4510401040b0368160103005a680d050818603030b801189802580302c032035015522000300c0c05501445c03605008802100400038401003040c0301d0382c4030702c0d40054820b04103a080b240400380e840380740c8003c1c28503085804410501d0070300031b5400181028140c4046e06846810086500442141c0741c11103a04a41c10180c0d2550020421006501d04440b04039000003460404d12801404e10002e5413002e00c100d0101d170707203050740001c040d00306074400c000000e66140c01c4568900e07402c81803280a6142c000c05e141c08000124440c03003503001d00c440420b606048565510f602850400007006040d8007441d00a01c0c0042401142420138880010b8000c40300230201503030281c00d440703080c020049d0450307803075820120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 163712814 1250 163711564 163711573
    0x70c08060601170702070e060f040603030c0b010905060d06091b060e0114040b0405061b0102070c1706061e010e120715020109081803010207150518010209060d0c0207080d050904050702 81
    0x134200d0b40219603030301559000e8980d010a1385d96070010400703e018209429800900e010800414540c3c00442440d03103520407150a5240d90341c031840d40c81510029194160702000001c04000011855400305a03c18030824401c00c00b54502d501280e106502c075400180401c000e00c0b00c503419903034840e81a440301f44008140a0400d030802468a90600580c000d030f9008090001d4440410715a866503110600e0750080203560301e5500385070004242c061071140c00c0c901d0040074145e201d420804512280300e8031015101d061402c14414454100070856136000d41844844071101c48107469060b00310700b4030300152005110851a00058883c140e051010110869140282a000250f0318200b04d416103049414034246940911001030700a10811000030540c2c11001c8800c03508103456004a0302c234401d00110f801140040c1c4008500741e1258407030a90307108504200e01d2059030626071081103890001d01c1169015034480c001e02d45041c101c00d0302d400209030045443e680c2450203001c1d0540c0001d8900c041d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 163714064 1250 163712814 163712821
    0x4051201020711010503090a060c0e1003050906070e0d0609080a0e010c030c0642060f080406020313080310080714090f180a0c080105010605030603070e070302070c0806060117 77
    0x2d101e10300380f4a541504004000003c10040b41c03040090b1381d21141c0001d81000107040c041c5018180b4484280310074041c000300c0c211250403500a100d824400d0600c800549526502c5003012609003140c80640c0b0750080c9010b0201011501d50701c10303044050701c1017170403d68800b2854000780c060b640c06604030703040041014450300040e9000c2000045c0650083e408104080d01c0190f00051215085000d1080d041101c5510340c22125001c01f441205d000c02056240a901e910003111082d07000d100d00008110b220010800040055005603400200ca00303400b64105078654038501d8540c401d541010b0400e8124134107219946084c0701100040803803400b2140342c900b481c00410311b40030008041c0608400400002035105074080728106e800d490b000c00391034101c2154641f4100003c014007860130b4541ca00000412854001e0040301c2c01a00b0090050a120345051f01c0c504a0307140041c018000c041d0203224240001d00c05000003005080342d42c015151614001d000140002041d80b00c26049001c418240b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 163715314 1250 163714064 163714073
    0x120e063f06010c0303230c0d0608010b03030a0e1f050d1b1205130b010807080606030a0807020d051216051009122f01062d06080601030f060b040512010207 68
    0x309001e0703160402141e03400b5210880e10451a81d002039055104d540c5e010000b1f010f038800c000b40040540071400300480d40c0c603901c1503402ca41c104219150140d108100241601c0c3c0601c448840c8800004e0885480d01c4041030040110790400103000041800460800d100402500880c0f03808807a001500380903801c4464018841884120032904056031080801c0c036601c118282410300d40d802001409441d655030403e69668071851041000c40c0c0245400300381103150103d20812502e402c4094035007000d0042e0200314145c08046800c641c54416075526041c0450980090283c0403c1941010302101c0981800d40c1417082e51001d500384146409900300001340f200140860000700f600d4500d2241949091030381c1090544000d241711080700004080c08a141500401c0a40d078034140300100c4207420100c032081c1d44039035820203240170704855424000b03980315514465228105240125110030b034503005108482e040d403ca041015030003e014401800c2902030380f00304441000c002c600e0012079458 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 163716564 1250 163715314 163715327
    0x91103220c1a0c06040809031501030f1b1203050a0e010201020a0903110f060c03070201030c020304060503070f0c140a030207060c0b1302060c101e09120e063f0601 72
    0x2100055031101c2000c440c2e080c400000d4460781c0030001d04945441c28141400c10081d08148900d40c80303032290140b081c43c40b020101081c0c0c102c80d444503403a44490740a560382048007215280081900381520400604901d406070141c8070540241c4502e651340103400c40007440c0b6910b1101980c15a80100103090310203910030740000441f9045221032540d10912800250010401c81c12a030740154085000100044040000c0c00560f100343c0741041243e01d903481c00d03a203e028910aa00c0891000e1001030303990b0f8021101c43c0e141c0c0009140c0413560204a9580581000b03c941f642062640841520f804050f01040600d016081600700b00c21002c5043e0381e0a00e80901c010000d01e25044082c10314401c5454940c01d843c104220407054403190380c02c060741c240041c01c03210100060300012600d1005103110510600c440307607421105d9060a084403210584600368000322103a0002c000300301200d0b411041400c00b100104540f10f210b00c5400c18070f04100c54040c040700d100b61086050340280003041ea0402e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 163717814 1250 163716564 163716569
    0x606010f050f040f0e090616030b0f0604080a030e060418090f06140f0a11030a090c030813060908010c02070e0a02070501020a0503160908190804091103220c 69
    0x64040ca0512100804035100d004034164202d4841011070082160520080481d00b6140e0700010818503a0b0b030151461398a40b81580e00b10050120703000820f00c411b00c41c1e0006922a82d001e01201e0303810100c0c801044656000b5806014a904194042c1081592103080d03140c59000442d0400e0604d410040c01e8040c1440050300740340140d13901c0ba4080c0c10040344030282070440780c04c0081009030348000040b441c1d00d010b00b2950118030280c02c01c0003545002e920700ca403001003081e54550f80d00f15590703419418014051403105582a0541400000019515000400403090305002c02c0c8412482c002003c0d04440e0241c120490303a90405100300d0000d68002070300700031211301c1a1103e895880300280d89000f40304004000e006035000040001885400c00b004501655003900c081401e681024000c840b21544c50081c219950031008248914140c0c100000c4100c1e4041d58940c1e1510381d50f10482c90494100c0210140340300d44c00320800c51302c0c242c400b1944450450107810100302c0344a550301d40140d44c90a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 163719064 1250 163717814 163717817
    0x305060301050709122105070308070302070809040c05122703030603120a20010b10080f07032705070f0503060702060f1306090303050a0b0604080a021002031207230c060601 76
    0x417458000d00204e8140d010311007010601c00307004442d4240c0010442c0d4051081a40410403003004902018820f1089640b82d40c2c020700301608102140082001030003c90200c0410468248082c80301c0c410b0a00d40c5078014a401d04025000024948007000c03007000920803055682c0080c8204505521301103807507002145090911907442000c040c0544103040504100d003034050800020748a107840c1540b0030f070580c000172908003035840d070030b12000c0f5061a421034051552203428004074200324001d40004102c0f41d0402c01d910000e804000d00c0700b03081d5103140381c269442c1d403081a0030401d2070440c14140006c0c02080d0003404940c5402003004e942c1e0b0801920a0355200d0301c10340021000082e40da00340c1a100d90141c82401949003d040040103441c1c255012495030786000000703512858620111030840e81d000020300301d100d521303408000c0340c1203c0180103815404200b0003075190342c0a40c07440611424054aa944003461500d40f001d40d034590881f000c18880d6001c002c0b8100401001840d0355012409 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 163720314 1250 163719064 163719089
    0x50f07050f030301060801090f050613110f0c0102090907020316030c050a15020307090503160e0a09050a0302100c1d090703060905070207081204030f02010813050714010305060301050709 82
    0x40c0c90458501407000800041030b000101c008246180d00904a0f0304a0315080414428400c0d8152000101c94055501e1980b150740c014031500c090b600c0382c10822001a00013005814801d000c0c050704c081d036014107040e442a03580003e44a046180111000707800402901c01141031625004403507031031580340a800380c01c0c8111030030a9004c03c00100074007812598040c05d40316001c107003003601070040d420686d42040490000080844c0f203040015024810010054090500e6032819000201c4103101400c1038540300e071910010300124004001c000c1403603101e54020101c03894080c20309401c030b6400c00621020481610030344c903500d524070301008203152800c4a030301c5059268200144c00811040c0e10000006040c102084203464000c6845822210028141ea101c0c030548040141d4074031590000911040f224510000554864a89517621544ca85416200d5190340d850300d0340341000030350040c84072282c100080d8071556418001c071508403605074024030080c02d1566003d4640e000e14000c041504c0d61 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 163721564 1250 163720314 163720327
    0xd0b0a06080d0521090d0e0f15070c0902030402090601030b0103090609030e01020705060408060a02090102030d1103071d031b03032203050d090b07110d0501050f01051c0201050f 78
    0x24036400440142440402c44080c492403040150aa0704020408420411034843d0407950481e1368541c54410003401018000e00c041d0110180d0388040741da170016070009070103500304400c2d031200700300e448981c0c0350f01c8011a00c0d2440c3e803901c885100243d4020b03a4596006105000040c2c03291004160000002d003030103d03026590100407001001d82610113040913041c640340c001850341140b54104403030700a03070a640c0f50503151001d00c40305205a1041610740c0e07001c0c00002d4040c2c01d49901401000105106907440c0030000118a015140c105030a003244000020034040b68980200e10700c1000380309101414880c01c1100c00290f10b44800708400c00e108220740001c03000c290713024001c4071458440030041d001e0309070040418820014907400300316001c0c41341c0082001c00d580140e241c0d000711921f03d44124a4410b130390b550410422003440c2125000f0b4000031403880051030078040d041c03050402d1280c960a070340c980010080c000ba58112140f50383c5032030100c10005070b64845d04981036100f200245640e03410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 163722814 1250 163721564 163721581
    0x12120702070b09061e070b06040f021c091a01060302040e0105040c0f0804170d05160305040b0103260c030d150810050619030b15010806060904090303060506032e050d0b 74
    0x7117103802c070040b402000a03840781009104600a4090403099904100c98503074080480124841c0c00c0070f90551042d0301010340b42c41c82003900401360403441030000640040000340e000d21b900340c003030b040f1a0101e60082810721842c50281c0704103005003030444062000118190000e890b100c02c00702071108111086e400101401030f041c0c2c9541aa294104800d0f584d80010300c02030005100949046c00031105150080343c580f842070056034050b1703400c102031480c264a181e8a030500600c0180701d00702001205016184441c000c0d202400302d0104043c041c40eaa01c0c0051030700c4085440350010158148510f40c0c0c180804500014600c42c440420400000c1649580c00010040310604d400000003203101403021040068089403503008281404450396645188001514042e408442054000307106021601644c40c0030341003000524040d0400107840d0341c41c0c10202d0195403003290450703911842c1983e06554940c00d51700700d0504410303401d1140c07052410b140c0003030b242060072034010b4900000d120211f54001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 163724064 1250 163722814 163722847
    0x14060c16030e150a0c02091015210f05060f01090803030c070311100c080a06061b0f020312130801060503030702040209060c10060f120506161112120702070b0906 71
    0x201c145054841c84d04940003051805481012405010b8610224002e110f904105070152601070512a9411155401c22103c4150255001c10b14140d6444021111f5a251103144d004903101c99000c184d40c0361000500120320445c2e003090f41044408a01008500c0700030040c1ca4102d15400d0780c0a070344207601d00f021980d0145511040c4610f0180100419080700705034403030480984a901c0300a50f03035454810850803210701e0300c84c0c00042880440024504019007032085541441402400c1000d500758010916008811044440d4001300042e400100c0e05100e00440041c000007009003e06810000030070303201c0c0111800280030303940100da031800301d645502c203a80c0c0508050007160100400c1d202410081c0425108140300c845428102280c031001d19094000c1c42034204006088a4588684010444034500903050400c4110190720560220905c607404500074221580d40d10340384118050301075940090130302400d41d403020b601005038540740020742d02c50308000c58100c4e440f0600c1000c0c1d078141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 163725314 1250 163724064 163724089
    0x21c031e0219020d1d061c05041109180c060702062107030b04060608070c0203070504110c0c010c0302060703090302100509030c3711060714060c16030e 67
    0x500220315103942c80c1d580000d0707218001841c1d08480c8540300e80541500c104000132202210001d101c402420107052107030040c03080144640c258002c10007020809000c8850548080341c10300c081c9001e000591a09038861500030400800040c80da03824000459901ea088101140c01540041048815581d039070040c0c80c120300c2c4d0719205080c9412220300e02427002c030701120034401103131800c01030246a0a1900c609011350310302d620f079075025071184076080d116020300060881c0d151080c2100419180c40c2d90250030748251007140d0040d220307486800342a080040c0b40585a0405c909075125201003a40003031095081202400c1c0040c2c54502070900700c2c2070170640340c040c040d81801e0034103203d0014000030060040944d0701050307980c40543c00c81c890061410340c8040e04c00202c41000314440c1d402060381c1c01c18000d40709011102d043c00c2c8090200d1050b8001d100300380c8085103607446064050380103001d1a0361015100c51280e18041083d0107034038011f40c2200e000307410001c4001c40144503444085c1c02101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 163726564 1250 163725314 163725371
    0xe040602090603010807180c0e040203042406050103050604110f0c0a0c1d073612030806090c09060a03050a090c0306021317070308030c0f16020f01021c03 68
    0x1502c0d80c40c0d03081c013980c1d80407d1213804000d070806082810440c4061003025050324855031480c000e81c4c4000104000b0750809002660129803001d0410b1030000420b40811030b01c1780c2c05001103400b43c5040c0024048800c000e0216001e242056140c00341760301100e044440d600000758803035450380c62220880e803400310b5886000f0024850342c980455500403000c0f01d00b9407034080c4d02e07075010161380e0103030119003921482e520403004c0f82c07510f15a82d001c01c21100ea40f424810030141e080694907038809a048074800200700c10380208080000740411b6003403c6600c60350201e0310981951600064102144052282d02040c1d003c05136180301041c4207e1094001c0400c09070440c8030440c0741d90300c81c14094000c2d0301591410448400350710340002c0030801c09000b1603510508401410030f40e882e6464101082e88000c0084050007820001c40c800030511402a04107503e4505104030080c0c05c138414801112017195019042d94800d111660212040800303d2074101003a140c0070900311040f81401100c156070894801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 163727814 1250 163726564 163726567
    0xf030103050303060f0d110609181305070f0303090909080409020c0114060d0206030a051008060a0b010801060914121905060f0601080106170c070804030503190e06040e0406020906 79
    0x3070100c0000650b010f5030086414040f880c41180410101540b4540010100b074290100d0403941d2a2810140400107005811103d408a04481c04051084200c0307110b00152165058081801070801401c400b0f0306410301500b0149003180c80140c41c400491003941605074540f100a1300300303c44201030360010851580d0654841d1414200d00340a4000b4078402000c4608040018511b0300e40141104c004940180115103151a000b0400010301402000f8140401e07018400107840c41081202c144682c080600c0041c00501c0c0c0b0300014114241a80100b08002801c0b0040c00b138003d81110811042000b1a1a0030420500c000010308142102200c030071444a150713410300a200b0042500c620070109030010144035680c40d00190f0303018030203005481c005906070300c110980f040d050714681c0c0c00100c0180340f44d0500e44142e440164541c0150421a556040410041d00c0e41e41200100d41341c0da030032400c092260059040c0030500c9405548582440c03100f0103400b0030f0900c9003a80c11a414144041c0c54107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 163729064 1250 163727814 163727819
    0x9030311030f040b09031e0310050a0e1b0a1215050301021305040516022a090109060617041203110f07060b090106261f030507080f01021204170f0301 66
    0xb800140030498003039583c1d5040c04000360003184048120f8030b80350150300b03201102982c400c1e00c1303840e0ba41000f07007180c0c05c02c22615800321f00c0381e0b030310000c040c010103242000381d10500d00b06074091480410000e18081200302402840c00c4160070040c0300c1000081200e0001700d007104114120a1000b15074442601544005000707a0641d19a014440a444054a0070b00c19034582d2000048000c899013001d01c0184c0160f0307802d409245150450b40c41126001da000030000c04144001100c0110070b0b805480d00320ba4950b0b0800c201e07500040a824100e008692001680c83c1a4407034202120401d5034881c20135686140f80202c40000905031060040c107500c0d126169045071a10b07000070a0300035222071250f51604000140640721740d400407000d99001d0300d40140c405440000043c5071102a08040300c0c55114600c00d04200165000f00c4015401040105881d500c1c02c8800c40c2000e025004007030159004014000f458101420f1403038000da4009958415110011442400f034040c21115500404000000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 163730314 1250 163729064 163729081
    0x1409041b0801080c010203070506220b071706030c1f02100204030f110904080d020901112506050403020303031b0c1509150105030624062701050301180903031103 71
    0x846050f0b0315a07a0485030000000401643d07a8010008010010b40c404d03800076210640700710505003006031031403214000c050565200c2a14079011030300d0340001842103c440e00c0e82c520001c855900f1103c10b8015040e29004000421700c04041010402500165695405500361007049842003c0b542c624046440d0358582c036081e4100000007100f44c60307010268515070424038203127003118050741e4403070300d114540078074014090041d4014151341414081d0812070400300020611a044a10704000c400222034040b410030f003c000e0503207030021410414203010500040e04e00200311303a0864014403c904d4014041d00c1100d006204049081d185800352030041e408841e4002011400f9500311010745034458003c0043d0300c00c1f14800d11407107515a0200001c240481e40c006082c070040c1d8103040e4a420f030007000c840800d110b507104580d00703100000d6001d0142100c0c1207001c4505041c44003440c2c510303d154074040080c10440c1e518000e2000302951b03030241001b01070107079000555101c1e408900b03640b01d1908210 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 163731564 1250 163730314 163730327
    0x10606020a06050907051320070311060109020406052a0a030504080c040510150e040608030d050a02030402010804120c02150a0f0201090c12020109230319031409041b 73
    0x1210094180000b044d003580b4049108030a480c03003d00001d0210703071000c020501038400d50007241034141612000300e0260a42200908000e402900c07980301050740e40d00c2c034518040741640140c142c0743c414072043c41981d50200450b15001c20100c00300312040d030615880c00341224024000480e03449042c014404154008000d801120840400d031101240700806000540304121a006801030f00c0020500030300061500d2902d01e61182d150640c0003424100128048070740b41e820000c1d1070760001c00c0032580c9a4843c00340551040e10300380c040d411810141d0001e4990369029100514861200e801d1006052003a121580da958000b4045d209081e004000d50480d0361040c02c00000080d000b805008901d0f00502074100d06681c4000303a4440c0314034000b00c10358081c0d44101e0480c1049000c1c800001c3c0d00a09c100020398180c40c0c00511214502c2c40750802d803414080e600180200c0c100c945090021a420504821030000080c41d02603480c00d0ba68005070040c56082c0d07420000ba080742c840c04d0840c07948800b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 163732814 1250 163731564 163731583
    0x5040204080f0609070f060507031106040c170c090c03061305070c11120a061a031506010201180507050103020313060906060f08030f0405060a0908030c0c0a090207150b010e0301060602 81
    0x2c080e0303900d54031140d140e50340310030113409411210707424014200704070b42c880c40040c8007013406880d0000c0710100380c140c1e041c20840300b90f03401ea075050038400d402d001c2e00460302e0350b244001031028010541070000e440070a10a5500030000010420007100044581d120704059a00d05400700b142000700c1c0c9420b40c0c01902c1c07002c040c00103440d4001168035910440c20000e0991101c9902e4400038010100e0b82d0b03031488090700c4404540e00c8100b440d40107411645d03c003084407645030401420b40c0109458500c00090866000d10105c800a0b01d184c0044c20209402203a0242031f1034003841d003d070352035485d6540080318000e51100202500d00e8607060740b051061542c0400260340032901c41d4a50241e45050a079620302070030402c40d6869004010070051b502d40200107110031030144c01c2c108a0180d6a4107010308540240141c0245d9030130a0020080c14a8404410405882003000c11410032030076480e050f02c00340b07080d1070304c6100a99134003000d07181e42c0c084c01d030364554040f00a009200b05074880c10f00944582c101d6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 163734064 1250 163732814 163732843
    0xd060e0d050304050d0503061f1b030207140102070f060507170304050f01060b03190b030c04050c0d0606030c08061e040509010c0e0607020f1311190e091911040504020408 75
    0x700034045d04244034204484c042c1a0080c4900707443d141d5501c21049124100880506008100100342c900c0c0c0000f00d00b59030503030f0080c0c0241c20720324a0020b0322800001c054107030504540000d0824003041a642140405803080340c039115031036000b40c1ca4518070b040c000ca200c50240000202c20401000b00004503424031021200080c80b04582d21081003800d800241d80d40001c510703410380d24440d44d400076032040900d48001002c441030020710344045000c1391025600c48801010001c1e0f00c40e040703140c1d409250028043c0b46010440004002c4004220000103883d580c8242644000c25414100303901d4120b04c0c0310340c000d20030011400d204040c1402000e5006411000c01c50b42c0703664107000d2602c20300351120541c0150144091941207804c03c43c85004e818154103010356285a65203c130b001c41d10281018182c100d403498403444201d032001e00101040429244103000001c1088843d10124911200e2010354440220328031000c140c0c140300900a503080320f50020320110b00044d500c50000f98100d5607003140d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 163735314 1250 163734064 163734073
    0x120f071103031303110102060f0c0c07170c09070f0207031502130605180409020d0305030c070b0403081e091506010927060e0c0306090a091a01171b0d060e0d05030405 73
    0x7040040e42c03519402c1360034a91420801000401c503c042c0c0000302280f45200082e03680580e01d4240090480c0d185045458007543b000f5445096030130300103409a00040c06081940e402280c00300700960f10100ba00006040e01c0200040b251403100f55019201c01d081000da03007600032529804000c0c5583c004c52000c107401c00b10039114281c1c5080030702c100480c25402030f107880d5011429880540320755201910410a103d070412074003020921001c0024040c91280c0d80c0c82c442c2d410a035409217040803500ba14140c44c80046800d01000002c002500b16209581d2a02d91507681d80e00710050396400c1003584a14122101c441e20b100e2100a0480619001810540d00b0081a40c6600818114140c05c03a0094a21a010001b0910618220341d031942d0004000c580402e0000c459501c01d40e5201a00308403102112044006010000311300c0d0100306001803000040685480301507801003803443e2801c10034010300340030002d1001e012040c2c110383d40c2c0c1d01e5010b044174030b0b01100c03143c0104103500485050710140207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 163736564 1250 163735314 163735343
    0xc030b090a05150a050a09020c03040e040f15022a031309050609090c06040902030c0d0903030203040215180d0c0801050c07050c030309010806060c1c0c03030b03120f071103031303 79
    0x40c03c00413a401d0340e8018002400140c1014141c000940c00007480d41c040c8d110501c00001c1c020b20200a047c45103104022142d0b0889039807a2406840c2801120078040500501c140310124034000290500380da20650000c011803841d05400e8218480c0003016141429030100104411189411070f40c0640007e42d584c0c14141e0340c03401c00c20344a005000e101980118200000c10900510340c000d1500b01070b504200e540f901d03140d44075100880f081100218046034021040109503c3d1803c0c20002c1c4440a150403480c2c1080d9499401003108010707070207403080b00c500a0f20001d001140c0840400382c9070f20b0000300441d04110103013070101d4001c0c4401301d40350310035003c0c0e50005040c04816100340300e0041e150913200b900c0f81e804101d507075049601c222000d8442c0c00e620002103031083c000c1e03582110107502c07100030b4a0f00f80d0a008066407450304080f4002d030704c00c149504010545c0740c105d44200051460f01500d9040c10725041c410f10300018403c543c1444042012410819400040341c1100d200750b440707030101b44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 163737814 1250 163736564 163736569
    0xf0605090f010f03080a0e0301020a0c030e09010503030d111606150801060602191401090b060406050603160e060c0a05030d1b02060406020c010b13020d0509070311040c030b090a0515 80
    0x81007401681503143c0b007510100300003403580000e40304904c050b081113507001c074290b804a42240c0101508500096660141806241c0c1021144103c1841034501104960401b000309560707110b04440308245981c0c400b112400c1101041c180c412544030076000760b12441c12800d0540183c4006011000d600c0b804840000e5070300b005200d0311084459a8010b02175183c0a40ca81c0c540742204601c0c140c4110f90214510101c1030028480d201503c3e115000306c0c2028184407007031008503070942e04014001c06041040c840d00618040c0c0d28000008986440c5408460040200b50035018540d60b52855124600c00c01041027804009080d611030b09030380400c001061008892042c1c400e00201d0400758004c000400c001c2441c640003440140c010b0400460780281040110f200f8014114911000c2d590108100c01c17003550701c0c0242904440030000911040d800d588a0103036a00c10f84002502c519911001c0e890058020742109410b03560040580d0b0145c646021042c000c1d000c115900d040702c0030b032110840c0092 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 163739064 1250 163737814 163737841
    0x30c03140a0b060f0d0602071a0c07031209030504030f060902030610030f0f17040803072013020903101a131104121103010c180b0405130b040f0f060509 67
    0x1560098140b9115403509401c0c012240044c000080e0800540103280c400b04410307000603d5050304c50f0090f24448018081c145801e03a402400b5025490700c10015080407a074089000540c500d564007000900362914541a101485603501c02454041100700942c1400f40c0d40d03009c070708030600a03801e40f40e00c0d2781c607880c1d40c1802d00054040203152407141702403d004208050140c5208034818032201c07201d840c00c1e11904007550455808800c00e98000602d800c10440510408040c10325120140100c02c090301000a401080c108501000507901103244000360b075040041d80752008000074100440b400c044005441e419020f1041030245100b4041c0300300348110f42c418100e940010500c69810503080c02c40c50b0380b0720050313810203a6222004c590603607941c0c1e0b401c0c82100040c0000e82c4980c40c0b01c1040011504c07648a0782d90005010103002d0100700046d44460358212198010100006a0605500002030040000761486010203152010302c501c0b070012075008205445040718140d40d80d0b911080e960001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 163740314 1250 163739064 163739083
    0x10e060604050a1203020c03030d06050a090e061924050936070e010e07080109020c0712020301090605070513140d03050327030403031b020d02090c070c030c0314 71
    0xc400e00210800c0191001444d1a442c2440b0b40f064079203284061000030f2a54104884459059070340d01400c2200749000d9210100500ea914004c1c0000d0101d015400e8803100002c0058be480601d1207002e46c0010000d5100321600c010144480f0b885005031107541c02412094011035000301140b401107030820000303021a1740540c1c181e0340030a840310160561083c1d00032002114401d184280203001c6002c00f50f0322a000d004e4500100d41c07880030700d414200100215010b82c04248154410041ca00d0605070224980040e5000091a1013801740c0741c0c80460700400304414054142ea00d0a400d120b00107a2000040130801d500035807500e482906c4521035010b800054014642c84000e070b640c0400000e0041c0069907108131b03496440070300c489013031880042d1145e01000c0d983c026000080c1c203008041d000030040440c0342518519610000160307000c00c1d0084520b901c080d208120802c0004c00807005c0754100d41a943d03000f020f10441039964a88444031a0050108451444104070010048035000861180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 163741564 1250 163740314 163740319
    0x603050a0501051c0305090a03080f4f0801020a030b0406060509010504030209100f12061a0f04050903040b0a051902010504020d1202120304080904050705030105101103041a03010e06060405 83
    0x105840313103a6080c2c8881e40103010954000c0209140040406d200b440505800b80243c0c0d031050b81c40803441c55408100e145414400c4080041602c44013980d86900304c2102011210f1261105408410070b560110300b20300e920040427580006070800301180e00d5000300c510301209460500500e911290141d910b4050000d0580c002a03040c8020030162030040c115a800c6480c10590110031a2200c04140f0021102d402014003500d00d8900c500c204040343c030a6280580c024446007003000700b80000a60005003280d8083e102e503440d000455201c5c034041c4125002003048003802aa2a525072030042e0064114501011700c1c9030026034507292003401800b4a52089034014502c03a041d4907660740340e031000201a0500000c51003042244101040340303a000710300540c0540d40d10341c0ca0f2003022081000b0354100600700d40400c0810300c010052901c40c50560001c410f840d0500c4000076400400084c614061540700160695001a648001940c0380c00110b0581d6200501705039a90b03a00024000c185c0708521610b83c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 163742814 1250 163741564 163741609
    0x30f0c01140730020f030708070905030705060708090f04150e0108190f080d060303030f0f0e030a050d091e0510090f06050a0f05042d0b0610050c06010603050a050105 73
    0x16182d04800721810303081003c3c0c1c0070050034801072502540041e003044038034602144881e400d01c00c51130740146008000300011402460344a0400001c11001e004208004100e454046010034143d600d4503031204400e24090310070402c40c1280070319950281140e11403510304001303110001c54481c4c800720740c2c01ea240d40c0f1100c224a406010382d071410580d40c1251021b4070710f940c081c130201d103014099000e418010750007a0b0700411034420b55851141100d9102003200380007840c1c17010b84001d112010007034500b4400c15040c02507d51031124080d002074194404001c00c0441c1410900d031513805030780c52000300540200308071105814400119801c480c3d2120000e0503130490390880c031001a003960403980c0c1c0828120070110310184841201c070107842c410790341240c0311030250b00680c00808040003080d1100501c6c2d0041d0400401c2d6898500111001900a5001f2122489140000c45c01901125088004042190348541c4c1d203940c020000e150607145801c000341003400002d29844d042c288650100c8a205066 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 163744064 1250 163742814 163742867
    0x30c020a050a0318030b0a051e070c140705060309010c020106170c0d110319060e032104053313120e1212120a0203010803040611030f0c011407 63
    0x184c80200348503000825641c0c8144003c00020303140c000043c0a0510554080340a00381407070b03038080035030880a01c84804581201048003040d404902e511021790403608100d411143c85201600300589600303c190000000001d00910300015400f269503e01194000c22810342c5580d8180141e400302c1340d004885034401040340c540340c81c1c4181c0c3d2420091194030b212064410080c080307810505443c417403000c8030b64500c4904050060700e014490100a040b00910b103000d11000e901c103115822080c01203458811800080c0030403070b04100d101206050404c5040d8645000c0024401c4c8081ca000e000c1e840032500b402084403a11007003c0010f046030307c000038031480c1001c85001c9a807102407010039a400380d01e41091036070200c401e101c0040d4080d0071541859607003404811907a109500170740b2880f2024410001005861000302c10364042d5403107071511a01c900c050395130345071a6006040c0c0e188411040010200b8001c4015840300300800c1c61925150301d203558160050714507200c00e4610143c2e00404d070924 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 163745314 1250 163744064 163744067
    0xa0518270601020a02040504050604150606091206021210080f062404060b040915120c05060a03020904141501020f1c021e0705120f1002180301140601030c020a050a03 73
    0x4992041e018812500d0101c1160000341c2a01c40c1910240d8003600b08006010607c503803208007551141c02c200003400003d2600e00000d000c2c0f646481010114141d03041040d04116454046885903c1d540c092081c05050081019a5000c07170303840741421170720a04908510482002c078000744100100003818400a80b00401c1d1004902130340401948a41e59000c04150001d058001c1c1000c1e000099002400c0704c080c80c8800c104a119400c803480d12490601d0420004800890b144191041a40c2460b01ca150210b0b0940c0607000e81401958000c0c1010114008502c020488a10942d114a4940c40c04c1034800c0041e0384a0389006100602500f01c84d130703407003c44170070110802080784103441101d4151062004900b0b010480e05142589074020300c00030481407911000c00c800f1091b9170070150500441c6000540d035650440805c00350040c0d004260507408a00c458240c0040c1e04019000307200c0d1090080484500303100c100c035602d004c20714010b0b4141507207100295106686510000900022009440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 163746564 1250 163745314 163745389
    0xe030405041a03060901050a0b09011a071e12140307091e0305010f1506110d18080d020a0201020d03140f060303070f03021b010507050c040c090b0a0518 67
    0x482c2c4000009803082c5040c079141003003141c3c8240c403184000a01414100c0c000c070161112100c007a40b160202d807006000c0c806641320054140303624202200c5e0ba8107003500d803803049585140030854081342a89070050500480c2ea0040c543d062403960b4070760043c04c0540c91140c0601082c0c5928000440902c003c0c019142c2024402030201200010120388035940c0e030712182921b101c3e05d9130035200741c0c6800c2001b04041e02900800094001400d141403c110092000c55440410300050740411140c072016101034025041000050b1441070305903100c41c442c4040103581d0b0034480c0c0c0220300520030350000e0652740c1e2103442007540564001692009644440c404d400291001500d030952500040241c400000c3d54099040030b4a0305c2500580848216003d0b0030030340c1001b1841082c10b1000400640c00003a8010582840c182004c41d0b00280c01c880c2c403a412030b0388640c0c9070000401550002101000316030010701420910200c60744031000402d105042c009010100380da803105000480d84050400700c600c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 163747814 1250 163746564 163746581
    0x14060c1309020a05160302100609060306050709050603070507020f09010b07030801150c020d0501020f031810021c09150c03020408010509070f12060b030303160f020c210321010f08010e03040504 85
    0xf0440b080c1d0540100b11808449c2d0a50000000955800b410010070489025041d0301c40d0041c1000702c0741307500e4103000c50f205100c0200700000700480000d4410841d030354883c0f200400c40c2c004d001c0c10301d19a15001c40c518150300201c410740104491400025071421200ca100800341182d940706000d0100540c240203081c41040380440c0c80355028002900c81610050245101da4101400b080421190850f9181080c2d903180b03410902c0da00420211510101d2031a500e034a0a0300d00c000080c0010311b9040c0040421010790a40e9017044c10038140c19121f0343d042c1c02510546a815008110030f455178404269548414415004d220300000c004000505481049020043c001c010108000d80550300203400c5070304c111440400d06516201840c0d0080d403140e02107690328070600052001c140d03031900281000d22a41c041d480310b880000301c4044660b000b030050720f00b81c90404480c1d4840741c4c0544004000100b003405108440c40000c070300056042d10500601040c40c03c46000b652429003400c091002900901 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 163749064 1250 163747814 163747817
    0xc060f02071203050405130b0906060a03020c0a060f06120203060a0c0c050d090f0e0603060103140c090a09052103060409032a02120c030309090414060c1309020a051603 74
    0x8000001d0110002e16042c06054400c2d03456540d01c2d0b05120401c00748820000b0840409450400824480c1c1c82d02d490254020000b00c540c82d482d5100624110068407400c00d2403003050150160070390400c217030741c2c01150030f0220001d002d014481d100d03402411582e0748030001075819801440030400e00d480b80e03444009200c0c25403070039606d0301c541038403524a040000c0d0403500000d030f41c60100300000101c07810400080e100c00d00c5000c240d8140361340040d0355480180000341c07275001c0c1803072400d4803c44d007081410303000100541189800e184c14640380e07004040585040e5814052039000c071240480c41d02c21010304900005010f42035032201da09200091440781002c4051108503584000000b02d40c1c1003904c41c040d00b40407002a4101244180801c8008104902c1c0681d408900d10a001da5008130568544400550f50441581d5850a0a8514064440d0045098080d0b4000d111786421074030010000d444007018182c17500c0b82d403100e507641240300d24601040098410301c88144c003600c41c0075400255500a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 163750314 1250 163749064 163749073
    0x20603061207030f080d0b0a1211220b0315040c060e0105091e0f03010c05161e0c03030e061908070c05060a0e1e0303010506160807060b09060d0c060f02 67
    0x1241e590051903540e0100070f81785c10741c0114014400d0651400f0b1040c48020a403440240c1d03d2500011a2038035508190082c00f200800300004440d864200e10f40c02d6000500d1200503016001800a41c003c0130b100380300e603000c0d001c0c402c481d4207204404c820301402190f100c40412151490440100e400c075800c1401c0c181001010005240713540d0352200e1903000503540015030000803040004228403495511401c502990600b00d075059200e8000c0b00b9541d11401c1c44084c07004000a502c2c140501410220f03807a100249410180320a0014443d01107040d2480780d200c2028174075104c810080e0900400c0c81d10f40840007a0320020505c0c0c1d01c1941d8454011005061501c3c00c02044c0d035a060402e54101d500381d2242c0e07542c07002d2060b450303020882d08003036080c05802015400900039120b6200e12050003224000e0100150304600c154079114201c1c40160001091a00e401c03551400f28080d0400080ca580310700e20f140045082407a110307051a03030803544400c2d40c00e07000c0c0ca000303002d030762005054481d1400e500a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 163751564 1250 163750314 163750319
    0x501091a07120806040e0a15151701020319061202120a0507060f090506030114040c05070813030303050f060a06031d0a110405091c1b080a030b090112020603061207 72
    0x842180710b01c101d90a40e200e0088034a00f21040c8000c4400710f045a40e41c66106d880f4050114443c0c45000c107480c1078102d0f0224560940e10b01c0d1281034609a40104980da0360f01400948101040d4060b5005580c0e106101c1c0e044043e18022000b40c8485010318001000c241d030b03804d80146400c03942615414211001c0c0c4881000507142d20b402c1c52a15807120010500c000000e8001541c0109500c2c003506085070124110350400034500100c01c98481d0300c500490b0b980341000704107400380d025103d0340d6074080041c075a22142d030711016507000210310007200800d04082c003145442c0010041c142c4030b8403010701810f048500d440400c1f00038003200c1b0712280d0000200c00d8081c040003418451100081d0156440c2d1085612507424441112001000e41059400211042c00c28000c603481c048040b0b2082e1401940280d10740c80c00c50317134030301a0410007041414002804001d05405800040002e1000c40303051246a84c1d543c039402500c103e0100081d1300c09020030015480345021082014060b40c000d00721204130b074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 163752814 1250 163751564 163751573
    0x6070c03021e0a05011d090c040f0b040e0106030b010f030c0e06040b0306090a05040302190510060801150806070c02061b010c111011070204090611030a0f06050a0501091a07 76
    0x40d60359468800c407079881400c0110504001422000904c030a11307094008600f800c6405401c0003140400921441000000c994503092a2090742d01130b01903001614900c80d56403105540300d602c117104604504c030804000086650181c41075450000040e15450007003000b51004a00601301c403041c0d5000e00180b0384406540e61140000713003001d0401303801070f02c0c4d90303080c041c0400021401c001c21510080d03080608000010fa400b060103c00100700840c60090f8401514050781044110b0b0000402c00f4503160340003d150005400c0b01243e140c0f0004203080543c1c403640d4481e00c40c00c0c211003205c00300324070011071401400c2c280010040d15100030306d15880c040400c1002c0d400e50307082d1981c020000d0600c0c0e04282c0050740920654402400d07210040201c0c91a03101c126007580140007001c3e100d030342c0c3c0340006d00038031403150418203890181c00301c9650780e8901303040311034020315400c0c0c0440001450014081414100000c40f10181c41c0c0584413032512518010b402c61108100c3c405041031103609104540004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 163754064 1250 163752814 163752829
    0x60105100807051e0c0f070902070c03021e1f08180d0c02010210020f07031b0507050402091804150f0203010506030a0b13140f0a18080c07030b0906040b1003050c06070c0302 76
    0x1505080b010781380003803282c6c50781403410b8170541200401e9881001000c00291350302c0581011664140e425450340c0a40f10000c03025403013803621458000500c014040b00540354010145409407258544192549511a03c1c2107034400c280d2010416a00007860060307101d002d10f040301d41310340c4140b04440700c00d000c015862003030760424155803890110104140c030400d07801814610008041e040464100703420b6444e032a5480310b480c8503282c0519800207002441da25134180c0e00c401e11440407811516070500303280040140042d001807600c3c003407419a030032107091860700890781200c0000304010b00715210942824024441801ea21358001d482d4403c142c1c4801481c02121803403d0138055001d6540740c00d41000010b03100084c04650000d01e000601c1408140910340c501ca00da80120030241c1703522001040d80c1c900400c5801c054000300c580010803019440004440340b00d28860300c00805031b80c450b05200700000c0c800e03000051094200c466061050300300f00c07014200003400b40c050703000345560340c1d004101c60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 163755314 1250 163754064 163754077
    0x5070f1b050310020307090b0f041a0904150501020615010c171b0102090f0402030403050a0c0c051c060b0d0f030c06060512030c0705030c0f040f2705060105100807051e 74
    0xf441d07000700c00c12107440c1d0001406001050740c0d05005103400c211192007480d034400e030b01070317540201c51002180040e500054140c0300c280a000c1c00400600c2848440f1401300b0241c0c1c400c0d18010f2040700c0004044512542510400b0001030312810200c0c0942e81d14a440544000f0b03180c4110380d4244000e6105036101d000485c4000f003840001665448404240a66070030010300c2d483c0101d00400c1800300080d480000c4544852003072030a241684c0c00361600c0d0a294206034015075000342a400980a14100401d40c4c0400a110f05030401010f041309080c072480b08001100685079081c0c0c03860000c08240607580c0c0c81051442840b0004080e03032103500054008501d41c2d072000042c0d20114503c0c030600020800100034080480003000104028000181e0200d0810803031405191035803421404089a03400c070807847c0c1e02030819000300d005092600301540320f646000f50754505c60000002894281180503c103140403607912070005503a200c0064038a94071195091343e03107054455210010511a00c082c029 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 163756564 1250 163755314 163755343
    0x2100c0308100e0f100b0c070e090703120f091e080618031c0902060d05090607050f070b040201020a021504090c2604020316080c040c05070f1b0503 65
    0x150015080041c00003200400b50a40c1d02070a2034244100c2c048180314551100300c038030b00480e183d60743c203070502d9801415a0025498440208614031900070118510080e40c036249085011651441c0d14103903224030521028003810401e21109654610410300c2040e0060381e401c215a1070703030b910030048001d00741c1c1c14a0040829001801800b140d0390500189401c28030310410480c9000c11002d0540d100c1c4a4042502d0b46540ca40d050311006124542184418a4005110715140c2c140e601c00344001e450f0403551031280c1e000c2e040014a80c035018900751071070b14000c1d40195040c2101c59542c1d13582400090030903415031241181c05001030381e50031a0952501d185a81e02c988552900c006c01013134070b50780303404c9506101000103002e1003407154030301c0c8100d8000a41200c1c2d20726100c90010909008242c080056201c101d4440400d503840c001500004014050301c04202a1113800749c00c03200d900030071100600407110a1340c240c022032490b00c0d10906089001514200240e40c0c2d000092a00c01005035914 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 163757814 1250 163756564 163756577
    0x702010f0e0c1e01030608190c0803120403030234020102070501141c1b0207080606100c1511120105030105010b0307080f09120d0e1218060c03070210 66
    0x40001498098510300035401c0c0010500d01850b000010490050400468905181480c845200760300c01c1d00a04000c0403900f0549034a080e444034041c2500464040940d884820301c400002c0c1c00100104890121a400240c5da0b2180c846544c100d0196001d4501c0d1160001d00304541030350302c0e0552240038070580d2194041f54044030b0a1001a061541c0d81d802141800384049500d65500c219004070748144085100e90001160001180c0000b4072030001e8a03051048510340940c506500000c00c041966100001c495103aa03c00d8100701d6080e82c0000358100140078034103c0c9000a402d00c403004007140c403034000071403299040004824203402054060750a001d480004021905003031140d03d001d001c0001c42c00e89586009000a0b09403c0060311001c10103000000080505000b40310801c0d40500701c0c001c4a582e803c07905803030009420a404040614019040c910302c400701000215640341294404006010354902e041107615000300c611900b6902013041113500599603000001040c12480d01c03902c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 163759064 1250 163757814 163757831
    0x112020901080c130b120d0206010f09150605070533060402071e0606031703010905090109050c010f0905270703021611030319110c010c0c050108060105070b070201 72
    0x4100c004060780280d103690007001c1d4200094a6110b843c00d040054200081161200300700421410309890740703401150300070a480510015404900d5174100e40501410000b4162185124000c80e9012040b030032030384840c107604009960040028114040c000c1d13054510300510400a008084215220b61f1100c00d44410040305030a64884640e4210a00f038504500b0b0a40350340e034505000303088568060302026049e58a0b81005132680022015680c443c1d00b190301001132604d11075242e0020b002c1c1184403804c3c0b60004500b540140304580d8181c1d00000107001c80b819103001525052500141e900401004020215443d03c42264104454540303402407840302c2d4038120100d458074030240000c4101401080100070340d8103102c5004020f81d8010158911080c42d05001a11714841c4170050815604100824042c0542000d21101030710082c00135034151070040001104c6400b00d03440e00401182c814041803045500c1502c0740b5620907070605102c0d00d4441980c4400850440494200005070344039900c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 163760314 1250 163759064 163759069
    0x1506090b03010b030105010c05071d0403110a11061e0f0c010e0a030504050f28060807020706050d0e1f05150a0e1506090d0308180604031b020d020405011202 69
    0x1080062001500090942d410040701d10b0841c4010321a5034100030492074a6014083c0c240a000b00901520400d120055580c413002200000110750a03004501c400030720303d0407810045002c00c1c11542c0a0030002884114204008080c1c000c4003400c11820b0f10510f400e41d01078459002046011030000c28561110030007050f5a003590620300d01044245c0250108500003600041528240e6004031900807a9910100c04144411003c8140c0e8405240b80c4048120380c14140b00241c0944401d42d444404540d0b841c0c2c01030f0707610155449100300141d010421110344000f544e0201011400e01e03000e40c2d080d0b000d0398403080303048121219900443c0e99a08240315024001d14500d040e841f03000d0b50354a90072464880e00ba5880c123802805e20983d0300804803d81d1661b580c41c0b08641007014000c110300c192044a08009007090000c94141918440440da04082000005005485185e0680e1046011191400d448250800542d0101d070484400c0d00792100503030729400784601801001d01c5880015589004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 163761564 1250 163760314 163760327
    0x60b040e10150b18060d02040306090c050303091507020a050603070809060601030507140d0603080f0702030106120503091905030706030c0305070905090c071502070f0506090106120f050a061506 85
    0x3102d030150440d400204a0342c0804025030f141e60310a00d1610010383d00c0c48010403e580300d80c60302200064800940401005403c1c0e000300030460054100645541c1c4420034103540e4441c01e00e010394018452568000d030b01c1c3c00c03400240300b060b1000e40040b40306a40c07000031848940013503e903071000c50100820090159030401071150700840910701070042c0d003880370b4042c011001d01e0345507074201d09001482c2d12180906030400802941e00c5565569120429003815a1039049003c049100f0350078a100022807103c2124411034540d0407002442c07a140d404400c01001310403601c0c02079080c001c2584009079a83d414042180148440d880120780c01001c514020704031400140792005010810100740138a44a442d0901d81c04900c0c1e000c03c48e6034502e035042c610868406d104048031201d00020300c0b442044105442c12404500c920100c503540d0f1030300c0c1301640c240ca4950003484610b0030800100c001041c1d0410b520860680128103540c2c9000081d04ca12040d03507850641c814081c4c0b07081c1c1703003000305592254 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 163762814 1250 163761564 163761581
    0x209090108031c090c03080a180b09040b010302040f0905060d050f0601060e01020619020307020c1c06110301080a020112020706050a060311060f0d0c11060a090b0609070219060b040e10 81
    0xf00801c60200c0595645034150003501005c3c0c039054001c00d40544580c052260222101c2c0a660b44400f8a55101e440581c95841002d1090040d4109034614080c0d500034001d40301541c0b0070320180ca4005080090780d00080c00014201c0d58000301c0c1d20842c3d004104184500201c403140b040c060812981800c02c041d19014101e0201811544060204460301c0600c000040040c80c0c1407101581e01d1715415070891406e10b4605601b5441220021500c003504001d84010340070034415182442402484a0f0300210350000348140b14181d003000c1202c00046d842842180c0103094001300c010f0904d262600e6890882c0c804851200b0829910700c030600a01001c2c10fa0448043c4003110341b6440d01c0460f030103006a0380900324200c12030503103500b01d0305030b4180907209010102091204441080c82d010003e1000f0382980142aa500f0501101054050030240c00d9140f10700c1c483c0d002400c14064086960010101200c0240c9681c1d6491b410104a55650300822640c264034000820140c841c22031400121848403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 163764064 1250 163762814 163762867
    0x20906070c0e0c0f1204030e0a060c060c0201020301060f03020c07030c150e030c0105090f0d060e15010609030b071808061806061c0b04060e100e0d0f081504020909010803 75
    0x1400b0139209090900c0880394048101c0c041200b40d0740701e030300d03098071003008000d611a0320400031200400c1c20350340211084001800b88800f80040c000da2b00041e0b08038402801a0b000013000c0d1090045001d000750014040ea96280e02103980d11562602d503651424141d4020b0030513180d864448034001c503807141450502542c200c010300120b10000300064074a101e00c00e0418081c42e0508460390f0710b0381c1c410f10403100039500860240140c07036644540985942d1112100310702c80e0008000440c0c0b03e40301d0207900083c1c80d030203000c400c284c0d00d40700004d441081c03106e185c041100401034804a040c107014808035002d5841c00c40c2c900e80c0c81440d05c07442400c003a0004c043c103000c2c403401500340c0305004603040c407a0000340e0480c0f0014460f46072410968003400c05451410603510801045000002c207590140110038200f07025105080d1685104440c1c0700490442d4a00040000010030100201509021403140b0000d00043c42c007908000400e041c0c0c0310980c48058280c2020035034150121450038100c040ca141d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 163765314 1250 163764064 163764067
    0x7051b0105070912031e030504050d11060106050904090f29090604140f15060a0b031e090102070b010308090f0907090603020a09090e0a020102010614150d020906070c0e0c 75
    0x1100002c10000d003030320411341040c0358803c20f0070a05006401c00344c4400700740c0125108086280c03a0140150038280e5084900b84907541c81c5810403441200007106107038100014120300e07440d01c00c040310290030082e9034540c0190748146090000b001d04507000ca642d44144070701f60907004c80382d8150100b82d94640e001c0040040740030412116401c0424615803066101c0c0800a403068201586440c0c0000c601d0500105c0c400d001080c030f501150815400c0c40b61208603102c0030010340b80c030010b86090005540c80c580031003004111080a51560390015440007261000600f000000e4444140b00402a40b080c1e60301840003a042d181c5060850a406184800f81c620f15014103101e00c00400400702881400d042540c04078660b0349051142c49141e004042c1a01e06000001c03100841a27129522200304034050740c03a24100140b802c503001014241b100c801408209070041802014080341d200c41d0300054034607800c02c40404180c1c4d0300f001402c00d8a014a21103d41e05013803030841171000e4405031038207140160 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 163766564 1250 163765314 163765321
    0x10501050406030c1203020c0909010203010503060a0c020d0e030c04091103100905030412020409060606050306180105030c060c030408010204060906030b0904021c06060902041520030f0714030307051b0105 90
    0x221010703003080b1a040c0ca40c0e08285c030300070b040c201c1c01c0c9806a0007403131788107201380280410000e0540245050f41c808030b081d640c1c1916000c10b2541100c251070307051409a040040808030b89406030850080c54000507090310400b07019031000508039502c101c0201d8400e840c0c1c81c20110942402c012004025092050030025013078292240b555a004510680c3c140f040c40d9140b04085440317540250300810f600040500280d1b0322210068200c0d041210134074007942440c0741c1c102800317125181e800e040300c00c050050316512442e2414088a948078a1018200d0310007040009005042480148001d12480e91010019800e00d107004013038503a010700c050310800e00c40c0f0520015a0706c1d07282140940081b0f40303995440341c12618211002e0030190740304091192000ca07000400129580c400300c401081ea66031101c4101c24900288503000b280b95000e00303550b000744054195103030540003d1030441d00078040d103200700d000c075811a0314550045030660300191000c030740d09400b0042d2030140c440d108800c030000e10071445c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 163767814 1250 163766564 163766573
    0xc0302211e07050d090f02190509131118040302070807030b180a0204050103080301051809060103021c060e0703021e0102101806062c2814040b0901050105040603 71
    0x36464196000341000050220b5842c40c0070b6004c541c00e066092005001120141c1080f400e2503481d40c02c00da0145100b101c20242aa40c107485601c1070f80d1008001d02869181c01c412195100c20014040740c0700100c080d00d01040ba5034044100b10201140c01c0301e480d1501d081e14000781000815403101e000340d0f0001c841400010340e40c00003207a00562030310b00b16114861200c40f152400b03141d0350019410928000011081c4403003100298180c40080e6041c0440c0c0508070100c80c034002044950110300d4200300c005000510300b02058119400211001c0e401a44103602d52108850501c8450200740d80420010404c60414081d16140900e09c07522050703969800c400040d4444040540c030390300c42c5644200d998403202c6c40c6600c4c0c180c11504103404029181d205e003803010784028590700039440807000f0100ba1508030f0703030242c58a100c1c0d03081c88000c07001c03e0a000c040321a4103001e41800902181c441c140a48100703851050a440345005044580140c100080342d01d0840f8010780085000e01c0c180740b020700106 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 163769064 1250 163767814 163767841
    0x3030f050304031e050d0c020601080c010905090103020f060712030b150301030b040f02010228020307051203040e0402031c0c0b06120330010f0603050109180602030403120c030221 79
    0x101d103000780c022104070300e802c1284c183c4520070503501b031039150180709035142d540022200c0c10b0340c08280440e9100203406006542c61641d62042540c4000c2d00340043c0010309115000d512802c0e030141103d81800815034840d0711581c009140440040e594404007400ca00d04414081400d40d5a100c01524550540d1100044024010006005200d0410f50300c0c086900c00c01c451503580311540790544000444500700c821403903400b0810385c0700384608140851217217001201a060161560006c2d403a00d894205054500c01e00204283d0b81401000d4180081020901009050007096980d504003c208c51408058000d0701030302c0315001303003221b41683e051307050008100c4140201001101d0183c000c20751803000c0f0192600501c00e0440b0a180001405000c1a0b40c00e0301601c05540f0140f005a0b00d0f40c110004849580e0b4480360030050345180100414820b500464004c2e002e4980040b003001c41d0308001055403090601800042d0380094140d03400701e021054141d00c40c416048034803040c00c00f10345802c401c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 163770314 1250 163769064 163769087
    0xe010c0209060f010e1e03060c030f070c03020c13020d0e0607141b0f1c02030a12020f0c0601170d020303160f02070e040308310303050907120b0103030f05030403 71
    0x584a8080426201d81c0038460801ca4070170014000003a00044002d020040f01c4c05a84480c083d101d010080385d1450301d4207007500d100e030701898050166941c030f036807088401040b10710080d41580144080078060361903000c0700f016003032800c80380581d944003030b03c1c4100121080d507114950103130010814402815400714810460310303503030401903480b100d0140031144203051441c0f5048407446000d080c82104100411006c0c0a1151000110000c500360042aa224840c0070280000140849030a0341a051a079019110b52a407031260103040404098400f454102c0a822002000d55407014809041d0810001005c240784184083c509606280010090b90300201c000710040c800702c40c4064100034400c01401d03005254000284029003064103000c0d160680940d03017441400040d503c084003091703007038254001c1c2c0d0550394942071800d0001d0300c08a004200103084440e160140032000251400d8000720424800c0c0144812001540346180291000d41000f40082c1442400d204000c040303604071031103444 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 163771564 1250 163770314 163770319
    0x1140f03100b1c050c090705130e0703110a1121070206030606090607030302070309090608100e19030207090c0801061202160f150501061b060e070b190e010c020906 72
    0x81203191240040d0910a8000f0001c110200e024101024040002103007402510203403801d003004c1d21109030841b45032040f441d041c10342550741d2108025400a005c00207620450910380003500c4004c41181c11000c0e0321012501d0001100c0450101382403c00b40100002c2106000780700f911080341d4204503c2c1c5000c1e42c00040d1180e040407000a616440e070104580048900801c1d9598483c6c003894090021f4004200c103400041c107206c00410944d07160320914040d070740400001c0121400c11210140600701001070717440c090194281e01910f0813008108540fa540c402d0300949200e50a0028250071922403624044c20840d420004004e9136400180000c0f01e0011b00002507a1629200001c4110440c480c10042000769209852001d0010408044080c00c1d204031061141d81d93312003040f50003001c0c0001703803040c2c8102e0300113140024a20b5407140000d2071602081c1e030426a560a403942036900103500d503850000324100021011984038000d910010000d0078200001005074002c80c0140c00018043d60 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 163772814 1250 163771564 163771571
    0x203072309040912030b0a0f120c08161d01050109061d090408071103010911040903030605060a0504030b0c03130b070c0b0a0608150408030a050601140f0301140f0310 73
    0x80035400a208072401000090400e004151962a148050310b58100c4e0000010703207408288a8286013107214034080f01c00c1700c2d0380060110f003000a8217070320000e100f0003119008907540001035290b01c1403000d20304940c0c401800121862400d44203650340c5014040640001c01c08800510141c4c0e0414142e206882c220b02d01858500301d00368440025030f4210745e206502090702c078200300070421180000c0c0100e6120300e20087c403042d420403c1c1400e840066100a205810340d14501c00030341400c0d4082d0345d942d0301a00e00442e44075601c03000b140d059840f122075100018800030301403040c480050100754202d402c1084140c658548605151000d01541c14010042070344480410178151080028404658204076403c405040061841c0010401403190450078020f1010b002070410140d90517a01c229041544280b642c0d441031b00d00b00050400030034003414030900080030012016842c0c05000c400b4080150165a5410001072490969070300b0301592248030000e18130045c5031004266a44a20780d1400f010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 163774064 1250 163772814 163772867
    0x507030225050a1e1506030212010b0d02011107031a2502030403021009050603101a040f030f030c080f0c150105060d330f06050f0f0c10050906070e0301020307 70
    0x340044e541d444d10240002480a94100710b441042d44600110703807003203071005010401d40c07520303c0c269030310305800503444200c664000300594004c2c500400b090f00000f065406144c0c6a40c1c0f021940c0c4802000d02103100c0d0894200070f80746581c0003840040c4543c686010040c08403001d0000d603244194003000340294144915002405d015003000c41c060880108a00c2e16854101c90b9004000c0756449203507501072200c1c40282d07400781090b08460545901692036201e507821903c0b00812581c1900e411010000054120808109814081c21450007079680884d500d4028400203032030300760201a0040782410707800042259688401c1117823502c001c0004041105807800c286010210309280d01501c2102c0c0000108001d02a1900c01205541410303050740d00040e100c2c04d0407521400f41400103150750a0411900c02c0224001001c3e14081080340121900326504440001c02d448085e43e80620a03403243d014042c04640200c1801d00917841a0021800c43ca84464010640e03030002c28030004140449084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 163775314 1250 163774064 163774103
    0x91d0102090915030a021c02100801060203090d050708070f140102061501080702010902031c08010e0c0a08090a1703060102060708040c270e03040e0a0c0e0603190507030225050a 78
    0x481803c17903001032081503803400f084450204525a550201d01c224020700078080214041e40d0700605030741e01540114104580c0340c3c01e11800b103014220940740b03880713800400200c0f0a41001032802030030a0103c9078000310b1400006890400c1225400360664002c3c400300401090140e00880b006402440e1070301842d00da22100364014180740b403019416008820180c9144041c102c091420000560340e003070f1090782d840190003140901034413000c1903c5030410050480900c10041d0a4100e00d401c02560072148040d9074898158055200f100c07081d050100170040f41d5038051100990081080c2884007041ca0a0780d1061414101c034021044c01031002e800d2803400c0340094500c858401d2181808024840b03041402617500d411034030800d000502c52000199a4942a014000100800d9120856402c080c0d40805c95240c2006148203100c20301c01054000351a4180160b5000340090b0303c00503070b201c1c1d000070000c4102c0c607a85003074014011628840c600259000a5040340d0130307003000c040752141040d94039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 163776564 1250 163775314 163775323
    0xd03091101050f0c070e06180610050a0504080a050c04060905070903021002013801050c0d080703020c010903030f05071103030408030606070506040c1e080303071202090a091d010209091503 83
    0x4130300c410b40c403c0301804215403681ca00d90301c1c003070030303040b208400c9a201c0c110448402210864038650030001600f0704500c298018006080c1e405c5c2c0600301030b801c0c951151869490300c03503400d800383c803642d002c0180100d0300e060520400d0050601108103000d1440c000c41d020b4801c0318140b00c028002c5500003150300001e4402e600203400c03100218062981100402040c813418800306202000d0351280340d520742e00715030250381101c4050003140040c02c08292000016030b4480b0700103066500b459000c0010250010b000c1c4180b0712500d00c01d0303e000074441c0118034024111500140010140309a40d604901c50030400000c3d41c0d4801d5121400c50b030307256241400315545014404001303003240300350402e100c1009808011002640c40402542100030710300800100d0341441445094125042000881c502500c6565040207842c641003025107010700c16000700706807088650140800d240d61309283d50340c84800b4890380f00940c00c070b04c00035800d100c944400141d082401800341e400c0405071500d00d4042d52014030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 163777814 1250 163776564 163776577
    0x607050d05070f20030d0f0e0c04020405011d2101050414060105031f060504020c03032509090c0c05060703020409050a02040302030309010513080706080712060303080112020a1e080d03091101050f 86
    0xc10a1003090508071f480d0000d401c0007002000280282c0d001e441007810640b081d2012600c0581da06001c3c045807030f20846c0b14000c0e504c038054001800710f40030034154900142c0710b4040c0405c0000000e9914150a00f00012044001a00b070960040030040129683c0000e03151203545c3c54064050096181020f800c005200a501482c0c1041c000b00b14040c2005010016511509004040c030b498603101d9200d6000c01201388005501042c4041814801040c3c10350006052401d0341c00c21101c52081a25404e1411030110b890700300080d000030b420300106005000705034005182641c20f46c1071038256400603031070740282000c0d94108074004c0f41c0c60040ca1a41c500c14001440c0b9141901c06060704c87c02d00401c00360341160b1030000b00d4008601011036000903c544000c0325055a5690349907403d1800040200c040010140e81c0500b614030301081d400e40041d96005080404a41d00c48004e20b8a5103950a1908210307054060510f42054000802c00320112000082024609645d950400e801407c0315402200c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 163779064 1250 163777814 163777837
    0x3190b090103050106030510090b15030c041b11073f0302010b040b010c1205030c071406071b110d0804120302060402040e01092a05030607050d05070f2003 68
    0x8030000002d00030194050301c1505c0c002ca09480300030f210840b01c0b40c2030350261240200b419804100040c01900a40044a10701a00a0544140d26070040005c0d040c0d48400c1c0d06001d001c40b207220110a85d40d0850700c1d005412002c038016100003444c2000b140c5421064908001a25504c102000d006101890048102840c2041041405449420024020a40d11060342e00032403400c0c8a010765980500442040c695011002e0005500712600440c0c40f0340000d801d1410040f8103104a00020780c80c0304541180c5564000100320701d18104200034038072508040240090807003e036040f400701d2000e040c102070f28032007540c001c001c0a00d1464010070901c07035070340407401103018440410704240c1d010a03c1c5010714000c807428041061249140c50072905403180041c09080705a8000b8982e12074913801c40c0340c0844175a6004030481e51100403e040070700c00c8440030005080016492012441c1c1d11070070f82c2045044c601400307980240000034040c0f81c2421080c20844c1c1140c103145269502c10030448072120000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 163780314 1250 163779064 163779079
    0xc0711060409020a03060b0f1b01181a01050609030a110f0904060c09090b0d06090f05030c1e0c1e0406080d0e0103060504090b0c030406020c060c071103011103190b 72
    0x300c1c070b0000e00a402200c6034000190505000240c000030000c1079034400d84004002a00d0056050000c840000740515129090b5480d10750400701d142c040e444170540340b405000c000300641440b01090700318800c143c020f14851501807025146c01e4500040c0103403116845020358a60044400001c2c6040502c0b1059070751100c0c040d0100030402145030800059844c0589901e01d425031a00d055005a8945020840e00400f8649001003c5905500305020860041616005101c1c281c4c0750076046a00210322000990f201c0500d590072058070310311264070f2944050140c03403403000a0000a10b0220341c1110710218101c040420280b50341d4651091004080c01000c40b040a841752001806094040900d81d011034034059000901c1c1c03c06014a800e182e50009202100d81c0e22800b800106400162050701c54513030a00c10000144410002d0750b0003100c1030b0a2803921040e180c035100b0308170080030504a000c0d9040000403e021800c0e0390650340c01000500c1d06000a1400000d035a00502079440d015600065 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 163781564 1250 163780314 163780319
    0x110f030117071a19020606060d020d06030f05060415020f0304020103050a0e0d110c0a03051203090703051b040506040b0d02040e190c06200a0f030e04050a1d01060305060c07110604 79
    0x1c03482c000c00d01130034402060805851042410b0b6110001110035035044001040558078450066008100035481541c0c00100f581d221340b6086420410107000b00c500303902240906c0240240c0419001501c0f07890700d010b500c2d007841012000c00c1c0740800382000f41810785a0012461440340d0360401c00007444000100c80291141030301c024003044190303410340001d00031402804003d0401640300c80507660020b000f440600d500000c0c40032150f00082814209000711040440090b000303100110f400d140001341c0b05035030b00b004800c110031580050483e5100746d2400401c0400394540104900c14150100d500080d00d04140000340d00b055401039045c2d01400003502c078481081888208002a90502d0342c5066a840d210140d80520b80401003000700340da8400490603002940340300042080030303c00d10344141c00400880200341640d2047e00c1d0010a40d0b141d00079500d040745407010b507410190b801d070000d010301c0b4a1500d4440c1c4400b03001d008070805141c0003070440240701e8500a200d00f40c21018014135503a95 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 163782814 1250 163781564 163781609
    0x17040c0302010305010501021635060105031209030a0b041403160b070e0d080306040f02030c07050c0a060e0906030a080a1715151b070609030204110f03011707 70
    0x24440e01040340440c0c6020008240b41d4070001e03607078240803401c10403403441d1424941d42c080340c00c0907035038054203d0400001440c0b02c1c2c407030080d4845079000544014244d41d410a0b04050920b900c103003c044403031106010190320f5943c00500d010150750000e550b2100c1c2e8840741010350148604201d0b600051200081c0c122a0f03100d105d145040180c02411028515119101c080f03842c485800c1d0076030340c001000c108240100c2e551400842c0c2003a001403000404988450442080e43c004850541110502043e8407003804003e1100700a030b40c2c811603200806030b0801c007001e1f262848240400740200403180c00514207442c200140b0800b582c228400688030311400b000100b40003d440513007002e8036191004100d441507590389070740e491003009017080c0503000940c031180c00c00d40014460201001285403411600c840600c05c0c1030181c5442c2d501c9a4016003117005110581e0003034620b4030041e0804200034042c240d44032040d41d040d140005000200358418403140c0e49400d00e540c0283c00c0b00340800003038106a9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 163784064 1250 163782814 163782833
    0x6020114040f350d0f02030906060913050607030605031608100908040806010b09130603051203040809040905060a14060d0602070c2111010507020108060405090f120a02070b03090705010f1704 84
    0xe004400d1000c5401191701905a020035160003115034004c001003100361502c0803146a000741031803010f2800005d681c45440c90144161401d001180d5500e07410300c05800c05100400f820080c17140300101403841c0c61009503440e41d180c082100000ea03aa441c034402c01100f001160010650740d821101c46584400c1ea441c815801482c1c1c8a04c142072071451002031500e1806240200da41060180020341080b0b110f41c00c0a074002003040f00d0700002001032556076901c601c01c1d6110203000e40001c0c0510315004080c9070403254034403996030780c5450190400c2121f0351400c0072100d910b54000e0003d030700c0c0e12187c070f41411400d4060700700200100c02c5511001e010782070641d036944424003a4030031500030321801c0300540d0207108032100130b40044c0500300024440d09003908070319080203a1700d0803505190300d004101410160b5185914a8680e400120510007507810811100640b5040b83c4492450419114583d520042c81c460309042c42080040418600e000b40d40d00d01a22071013810300c500506e000d00e8211140c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 163785314 1250 163784064 163784077
    0x9090506150a0b0304030c030c060c0c0201030b0607022209080c060610050c031b0f0307050c0f010305100306050a0209090403050c060705040f1707120503030106020114040f35 77
    0x11090320055440c1610b008880d1808075803c00031200d1940d22075850032034044290076019010301039002d43c01d100190301c5208014070354199503500c0e01c080082d0310004050f40e4140c4181403140c0b100703001040150b9500c05404c40c0398407500e07080000f20902c18025102410010601401503c00420804000355010908500c60b100c100c40064502d800c040090b283c40c0280c90407805145d1040c0f105504038030300c1c407948000b40e1252004840040b8200c0c00f8152444d4444007003103506400003558942103046c9a054540b001d102400c00348007030b00d07003403a88811522031484080c15868a8401080c56440c0c0350303040f80c1c69048090070b04030b100e04e01801c02070010b40c8903942032a240e10500000400c114482c1c0d003540d0a035090850003100c44e40c41e00070292142503003540800e07841e002c0e1400c0000c840151011004403d07104102541e20303907142c050040d08582c8007003140245c02d0408801c020028400c0500030403036030350111510460402001d01d501c41c50503820780683e444441200300c14480c440e200043c01c038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 163786564 1250 163785314 163785331
    0x30906091011090103050615030112020f040e0a030f0c0209011715090c060c0102040503010f050610030504030e090727080c0d150b1804060c030b0d030c140709090506 73
    0x3a5042220326050480d00e1400b89102c0800c014850b0706040d61181c0c0003641c021100401d410039601d00c1c40d0303404140741d00a07840140c1d070041403aa050118113210205964410044404015801000300502e07103070090b011005040041854894901e0340c01203140300d06141d0094050f8500d50384038909450100b820101707030500d81c072400c0f8103076600600200005100c0c26030780001c0c1407a0380b03404043c0b14403074006c4c2c0186a1695000e0001260301e890910811121194014011410381441010b100c01c01401e0f00480c020903081a04120110b500101c1c90319409a060b02c0d08012642d454a0403201e45c20240c0407220b020088074030400b44414040038000a4692a00c20b90b0f81000146003000300721701094000400111106980c100d030213161343e221040d0040c0140100d1030308559500070010050781290304417a166510100d00710b01a9251041e903003401c9098070400c80007030031602c000e0444000b00c40b00801e403c040b003207007448400d0180459001816400300911103091146000d6449401c211000f04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 163787814 1250 163786564 163786573
    0x10203040b0a0513050c0f120303090a030908031213020a03061404050f070513020307090f060203070b01090501031509080d0e030918042001021e0312070801051309061103090609 78
    0x13442d409508103a41550f070740c0301c0d0041c2081041c41341401442c603c00c17990258030500c0c2d003140072602c2030240021403164010304040e014080ba9494040c01440103034210194950082c000c1c0d410440c11100c6540e00000140e44d82001883c0321300c00079243c1b98641e080142003900740703521090b640244003d40303030240d4400c40c15107000c0000964029515903a0348283c039448500c5402040c40b40c01203a004680046071803030441c4c03207141c48240e004c40d940090380c04000103920000e8000b050101d410041e42c09803156400070710055145488082c100f544200b1180381060399450940d08000044048415440c407400040c000e1a01c2d02d00031a45a41040c04554045c102c1102269841c0502900f40d910032603100203100074224058129000741d04404010714158419502040d0900c0c0300b11000c808080d030301c0c1c8020343c1d9a000c90408803d20b01e0002d08400d00b845a000300500040d50340350013030000403c1ca1580001c2030803a40c00c02e40064164015075004180d030000600c40d007080e0100c2d00c036208040580072034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 163789064 1250 163787814 163787821
    0x309011b02060f0606180402030a020c0a05060a060602030a1218060c0306140604030201020d0503130804030807111504060e01050403060513030206010e0702030711010e15130b120a0203040201050408010203040b0a05 94
    0x203c00b601c03462000401c8141901c6c0401c00d50700c0d01e40d01442e000300c2c114a0050034180860012841c0c414020020341e0150f20900c100501103026001d058041c0405202031800c10348401c1c409490554241c4000a85c203455a0512051040c04528440c440350818070502010b4000c007000360091407240510100c60000240104883c2040c0c8200c8040302d034103a000305000760121204840c2c0344c001511a503400c82c4034180312008103c0940181000c6d60040e0030b5103644822914203c1e007441b801d0702c0b886020307035100540143c045e501e080c2590b080f0b4040742000324802c0481d1004076128800e5800007090b0901d00350030b000c0080c0070f281081d08520303c69001c0b034801d030340c03244620580001c013240e01e180185d208012001c0003440103c2c100c0342480060500820020541d000103000201c2203e41c410520400b18544003a1103118020500516800f00701320325000c80e400e0445070850000706420b8001e600000800d0859206030200d400901101e4000c64581c2410f24145052203000c1c4c40003540d03541040c010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 163790314 1250 163789064 163789069
    0xc0c15051210210f020f0a09090b06040506010305100b0f1303050a0b0105010203030c07121e0c0201031a01050d0506061303060c090e1501030509031b061f080706050309011b02060f06 80
    0xc1c1d09065030002c2d150480b00804d5420880300010558104d604800e102c0380006030368055000300064030348120340c0240180340a500340411214024507aa0415081a050040100c0150041c405803580600306603500c3d400f130781d132a41080c07040c0c0e41409103007c03084c5800401d101e070124007090b45c5880390184144507681c030001240d0f240025180b40301324907000c002078000035009208040d556004c03400d218a480114a040050400003092241c0216400a0b2444219030b81480b8083d003424400c100361205442c0240002d000340943e0310b090701c44513550300214505649403020b44106004500010305031640f24600704019150342800c4a0100e0352000d07010502506401c1d03002c0c454450100b03405030740070854004401401000d8060720350360101b0841c0b01036119440c5800c0d01d41400c040028031050070604000103102c0c4074804080102704004006122000012400300111b6035181b81540d03da4413042200750041136000f0640310402240c440700f001c03031078001c10100d20511402203201c0c07040c0d0f6183c06 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 163791564 1250 163790314 163790369
    0x30521090105030a0207020a0302040504061521080904091415070207060c0206030402210c0109090902030c090403170106121506050906070303150b0304120c0c15051210 74
    0x100e03400b007102400055a0350240da4090052207000030f1404036110754a4000c10100c55054509075010b54a9113880c00d02154074801d00001001e0080500c0a549540b00000c148203400501c0104000c2c0300040710102c6940310703000139020039003181c40760344a186016400e5540c2c6240d8425500c0082180b800078410074008030700c2d482111865114101324600d10380c2001080d0740020000ca81c0100503c00440200c0d01500c400c42494002400605011031404c00150120103980d00188504d07050284d030380c0c0141c4002c0350070340c0c0341c02c03060790511190b403150715064811139145920003001d0780200d800040d005505c0a0007221440491000b08403207011140791980c00741c40da01510000c2582080003020509040c0b0041000038000e240006106c0900034520300f01c5046940305070800c100100601c024040100c11031040d00040b030401e80c0300700c0304554903c22802d10300d01c25005140c01d20024840028040c104440800c0207d600e4001685002c1441318948100c50180b6003400154500c041600c545614 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 163792814 1250 163791564 163791577
    0xf050102070b0307020f0f01020d060b13030f020607051002040302100f231c0c0e12070501030218040903090612230a060e010806040201120506100c0302010e07030521 73
    0x3406031030094140482c003901540041c00d82ea0451103a02c042c1300f141c0b03506128100c400c030054000941c0d2076407840046c00c141e403c1a049074056510400c0714400340900d080d40b10086a80c0100030124800403070001920764061054082e0460140c803402c411700e000d9a50040c4280c9100301c0b00020f1041d4028021101940300e4010180464105003011030982c0800e00d400d02e021203008005860a015500342d180306819601d405824240c80d050107040707440d04071a894000c03130425925010041e50b421111607460000d80316079814180c0c001204c0280042e1030185020001d0301501c01e01040300a443c0c004c10040262090380d0008000c6002281e1904041c00744042e0220b464020580203450310b14241e003001009850720310250b0b42c0300800185c240042c0402c074000c1c40c150001d00820300e040d000150680c070b0b020b81e108060a241ca410000c0301c0d03441c501d19840c1d2022a1502c00304203401841c041c1e0050031a042480305501c80c00c41d000040020015081d5900c117080308050580d8404410909020700481 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 163794064 1250 163792814 163792817
    0x1c02061303062711041b02100b06030739050d0e01020118060b030a171902030a0c0609021503150f1801051003114017011d160f0501 58
    0xb45031040104e07000e00f0010f144a20010f10006030200c0c20007207031403e049000344075005600960490aa0f84143d8800c0e01c010303403001d460b22842c6250070341d001449601c00c0b200d107010307001000c603190b444500700001800420503110013000b010803c1c0c0c00c00598501320301d8000400101182da400020b544180a40c0c51540780c448107030620f500469842c08060091004101d406100310354088000c40e5650784009090060400600d035603c1030030405d9041510860030700010b543c0104040c201d80c2e6071105025036030a0700883c0c0003402106900c0040c071342071405541010104008000c1c4000da1a034003803502a000b034100c2c0d01c000307000b070340c0b0051140b00c0e00030a00c01d040c481c1c5004010401400c00c5914054034060900c2e0024800c4107844481c54590882d144c5a402d06140900c070301c00e036800e0112001c000201c80e0f501441007811254034040e0341d00c20b600038681004544c00a1000f141c4094103c4000c000120309090030b002e8001075100e507680c5100940254540080c0c100284c01450f405055081d40e406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 163795314 1250 163794064 163794131
    0x423190302130e0c0904030503040506010b09100503190905030c1b03061305120d0c09081501150c05190614040507090507122301150507021c0206130306 67
    0x4800c020028540d055444501c0d0140b00b4086015960b44c05d6907910a41c801e44403e51281040d08003189803220582040c0e0180c0c41c10040078044e40d4929100140c45407041c0783c581e80c0e07aa06c20080d000312650198030031a0207801c0003007140c10810044040c090000346401110106841c00c90b80380071420410900c01d40580005001c101d0400100700c13007805490180301100d503041055400c0424a0b07200b80c6601e00021703a00c4400c90700391984041c540f0000d144074002007034002000740a020144606126024080220090400f1082d0060911007003a640100c141c1d190740c100e04003400750200342c5c50380031100c192a00c080644100c680c00c455502580d000001060014107000c02c02e8001c080240880040c4084d0b4003031080950f019008041400740504440201034030800c043d840148010703040403d4034500a06480c0742c0c250301500b42c5054680443d44003511010800c0401070140d588403019401c1900011641c3d003400c440c02d80743d0204c0b80300c0d400411007158505c40650718003452404150104070f1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 163796564 1250 163795314 163795339
    0x40902180f092817071b050d02100f1202040306020414030a0b0a0f18050c010e01030e1207080409151712040e04020f30010b0a0e0c0423190302 63
    0xb00c1d03d058044081c03244028203040400b0500c00c016a07003160a040754045500d11101800d000410510380090030f086d10804200e4410341d001800070091402c0190800281800c6070ba1058030904044c204045030000455860784c40e0309001000e50700901034102c04440c2420185214203000802350a5039422442056454584072000c001608000fa01004003d40324825004941110200d20480c54890401800b03451030076400541000b0549000c28145454100c540401e0240460a80e84148102080c1e954518051624169500031508a124180d02d00310080f038500b0903019054007a00c0300042200030103001490800e5071003c8400918445100600041011044c1c1c0c0c802c4ca90080e01c01000000302e8403009011503085022040b95205c801145010512040c034180c446c2c01c3c941c0c824500034081c100020001c2a80c1c1c561a10a404c002000d440000c0c0c0e51104100c10f03200500313080d200c844920340700302c07a20340000e082e0343c500c6910401c00d404100c01400304071b03080c901c1180e80c040c000845124 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 163797814 1250 163796564 163796623
    0x90a0803091008071412160804120c08070b1305070806040305120901090209040506060406050301061202010f020a21080c031017010e0303180106060c0b0a0b040902180f09 75
    0x501030300a07000d0245c81342440880c51052400b400e00c844040482d0a110701d4241c0c480d032014201c00100303c05010704001804046091068001ca0150f40c4e4100104210380c0740c0f43c039441030301c2050303005886084008140040750f4980e141c16907145025101320f441c001d440b202ca01d6201c070410742e0b004001c21401c02510211115030f4004682c480c11840000420301302c0b6030089040b550040360304403455049041046000c3c0390521444029042c150300820465007003404245007125030000183c103100b00e03034007408901413080140c0ba105940c441130451028982c5055540101a05138031440800d141c800010307001c1000c0740030f8900c00c50414424000030342c0360440c0c50440c0002c0172481c10340c0755207401c2e090000003001c000070340c010001c2c0e00c0c003003111202420390306003100d00682045c4200801602c0700c1c070114400d03140c1c0c103401c9186c490000681c408090000b400400510100940220384440c0094240c0340102c422131040d03c46903010208c0d03503203060070726850f4140d400301451001c00b0086201d8080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 163799064 1250 163797814 163797827
    0x6010918050105040507060801060e0607150b0a030b0415020a080f1b040e01050301140903030c030a0f050712060f06050729010b04090c1d060703090b0a05090a08030910 74
    0x1004949900c4140c2070303211142564402c032019540c90380105e0b4200301c250340c001040d9004004511f465040f110120340040c00c1d510401d2030141c410b15aaa13403000011030301d0750140218160080c03411502a44e0ba1074201c5962404079030549400000b150b42c2198003a00f13001f210090b085540d0f4600c0aa80c0c0c0c1503c0e910006005814105400700104000444081d0800200003038545111000204c0d0702d02402c142c00c2d20745000202e48107000803024000024400410349410140031950300ba2641da41040c0780e0000d0034803c4500a1050401c0203000c8403d8010f02020741201e6911000e018107616803078150203580b018414040080c10404c201c00215100407800c1d41c160042000c900c10030081100001400a400e81045060307580003c0d0070080751721240309859a03d000740c00d00c2400e1520720949081a1800d1046043c0076210014811041500c1469124090458211a44d071075010520b0b00a00c0c3c3c1c2c0104c111140192020300d00480c04000020603a81420001007020400000752001160203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 163800314 1250 163799064 163799081
    0x30308090a0606170c040e120f0d050703050402040e0c0f010e01050705070608100f1a09031006180e0f0c01030207020a181a010302090d1e020402040b03060109080f060109 75
    0x41c028011038a00141c50380c0a01401400c1020010030040229100581007888041c00e891141f032910101d54080701020508100300d00000070781907100d05e00942807486078451102040c440c1c81c900005c02a42c3c64141e40040c0c05070703009440401c4038a003c1101e60b5070743c0d0b850203500c0d0751254080a000c1582d600c128006103220070b06152240c04d100840d6102840c180040d04a00c01107080b030010440e2907050b80b03400000402d040300601510600d410340e1403200c0100e41d20403100b211000901e10301c041d10200500802121310750302c2000211342d82c03062000780c240d2544100703a0b0715003441c60f0303959401800aa5018920400783c00303010f4000400d00154000d500115003203070402c2440304009500501c003020390407040303150074000c5a000071090030340d071403010340040503814184140300d03980c400d44a03406040000c0f80c2c0441000f1404581007200311112021001c0250710900028020030030b40030700c0d405940206020f1301c40104950b103da4656485003c0342221086c0c03580050010805960b07130750800300b074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 163801564 1250 163800314 163800331
    0x70b030a0e030c03030411032103040c1d040c08030405090c090301090213091104090308040f0302010f020c030c060901020418050c040302041a03151003060b0418150609050c0301030308 81
    0x3444051241c1203030a41e0030003000850141c02c04010001800440c603c0a110070f4002c802801850321818208200d035040d10500c9078440c06d0100c0010104540d5480300c0c4050080500724002040788010303840e000c08812102110070b240383c504001030000340001a07a05a841c001e100c0360103540e5192196150750000603556900d0340d2202620300c05a2142c1ca10354254103a00b84010a00391a2410890440c00008581c0c501a500c0e203e094404280d02261060301700740d110900d07039414401c1d424102d026042e102030100c1c2141c400961940d28100000003040400008001e41d0640d6030340415581c02c034040d900c06c4c007544401040f50000192001d6110903485404a01b029042603100c0d00410200c802114017034080309810031100ea00e40c82d040000d00342e90590013000041e14605060788105134403680c400240741d15110f140d403503042d54640c5c11121384942c41c0e1800710b89103841030400f015441083c0c01c840b041c0c0c500d050008591900c640c0603540c0700d0038010800514603443d40e6822620040c00401504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 163802814 1250 163801564 163801571
    0x304060e040b06070f0b07080c09010e01111e0c0102060f0f070f022a0306100614070c0b030705040e01061e050c0109062d0e0705040c090f03030207091d070b030a 71
    0x1c0001c1e103105148170400b4007039051401d8615243e4405894280060091030360885d043c007090101ea030f445510340c0003082d400c0c030307200d400100b004800e41c0c40c2170071288181032004c40c0f4009103c0e000c003001030030281c0464240d0841311652240b110803044c218082e210b010100e2007060000d5001d902030082564403c02600c1181c2e1a403d03524040865420140445101450107510301419450b013000307280e801441c40e4004002c0740c7d180850181c80d407035140014500150340450b42005201c070594015004002d44103c19903240f60001d0020100da1040c01200307003d0300d420700003103000d900c0b85000441d510f001000c008030000c00510246d8081d0000c5407039410964807001e0020006820b80500e031030180426a01c41c0e900c100403d60500a2002a0700710724000c0c0c03070100307030702c010410000b07072201129010b9a00192950390031000322812540354101040c203001b1407400108169001407040c089030700c035190070003078002d85d04a40e0a41c0c03140e1090302c1c4099030101109210b050007080085411421281c07002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 163804064 1250 163802814 163802827
    0x106051b0f071a09010804030e0a0302040f020d050702071202010507080c16030201031107031205090f1b0321030f0601020313080703020a06050f070803132f030304060e040b06 77
    0x481c64000071a003554000d030000103003006082c03007010001c4290011003540905001645000030b100d02d200078005400c0005019680c0c01c240c0750303442c1e00000385801400c2803000e1f103601880070303010303500092021800034603013000540b280b03101258410550b403004111340a5800e0640044039981c200301019506c039502000540c20303020080000c80140c040c101d404c107203072501e180000350488800e881a148070110400c411000264008030744802e0120406000408d03450715040240b420403c210b0034070841c40742114091103050440c03284c1d48031000440446940e0036140c8002180421425411b40c6500410b01c04515003131020b503420780d031109041c81102d040104046140c0b50103801ca501030b90154000e4a03003031056003084e40601c400b8060350700b85a803509900e449140c2e030500c1510005082000c0100200d00060003510b605110030340c02c9a0207002d004e4840d070740c603c103031700c6412812a540c0710b07030f407400400c1820088156411240aa110321141c00c40c19424400603003111030b0150b0f03000320f003000304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 163805314 1250 163804064 163804117
    0xd050606042103030606080702030d0e0118080d060614070f02030f030f13090504050703080d201b010c0801060e06070807141902090103060b060706050403031e060e010605 75
    0x82e0750b010360700c03442c032080050200d0501804880ca241c00c44c1c01000800c408200e00140c00000329015141203101c0002c103005105221401020a00000d40e041c3d0319a29030758051180303143c0940384030001c84004210642d503c0100b41e4401c0707480300c0ea004046074141704440104040400072541a400582503e5500c0d0540208609545c00302020404202c40440e0080c100c2080f21405030280901c00c00030003480c00d05488407551108203110061400c5000611580080c0041d00030b200012510301042c0407000384c001e100d09050304a20a02130840d507000e02410308001050203240d03848401510745000c1079080142c101c0c0d0801085d0701a0340c029000304800c0001411100007450403038001e0f9520003829021800a81c103064200f25022029503403010350f60090f0781e4241c0c0c1f0300d0469620110011340804080c1c080dd00e10300a404010302918602000c02c014540c054024204021302000c82102a0203c03240b01d00494000c0e01840c0380f0fa010340da0050140f580108014000c244809101558101901c030740c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 163806564 1250 163805314 163805339
    0x10602010518060f0a02130b0a0c030f0e0f060a0507080c0c1c0803150a050d060504050c0a030804050f0d08030405070e0a060308090d031b030503040b090307080d05060604 75
    0x4005039550740c02c224080c4400b0306141249000b44001e4010744c20441c200241d26107019200301021980082ea202143e180030f0002c000a284020f08603854001c1100043c04220107110305a0210b00200b1010691501c6140c100300d40040081803000e40306000c009200c0141c0161846400340300c2c082050b02c0c0403803240c03030182c02603480001c010f141810640c0140f1030302c0c04840800781c1800c0300c071000000000c2c241c2400c0e240d01c01002c2c004143d4148065000620182c1c0d1540502d4110720707041c0d4820184022070304054030440c081c6048907a000c04010901ca83c1201038400901140801c0c0024051031030040b4803004a544001c0010003840801c1d1543ea0311540169011111035010110070006041d091001d107078400c8400d00100525851902c03038643c14403680500c40e00c58041c1600f620201400749607454401642c41e00c2c60590003060b03142c083c0007503100f0340b029035100761100c3c0080d404040000440710900c1e488004c0d50304214035803000c240608006000603a00036000d03c0b001c6000d00b846403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 163807814 1250 163806564 163806569
    0x316020604050d060f0c080903120406270c080c01050406110709050f040c06050304020a0512120d060e090f0a030c060f15050f090708070f0c0602180a0e040b0604021b0601 75
    0x110020303050401040303040464494038010702c1800747c0b040c20414414004020b0700d40c0c07800c031026040710568441c50000010718102d414901d458030b5054480340c05840d0800403602942c0308500d0842c0f01e40e00d0346099681c400503142900d00265041105020040c0300340c06000440500f0012500714603191801802030714403c4030812408001c4004010034440e900749580028119820894554146600890007038402401183d0103071010210b64040e94004000e000f00c41d070a038007000d03600c4504a01020001d005030380306070181c0100e4000801d02c090360204854500d0321408005250043c0d540c0d078180c0710040036400035507410341d031600c580517094003d02072914019160808061043e041204000000707400c48081c5005200400c01c01c428150041c958640042c071600341210074805042c07085550351085a001080c0e82c0c008140008280920800368803000c81c03c940540c0965160311140c10740c1c28003150050800c1d540382000c5661030400354001c5c414100464002150100110701c1d80d450104203030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 163809064 1250 163807814 163807823
    0xc030d02010e060703050615030c0d05160e030f030d111e040603050106110c06030903091906080106050f030a1508010203190b03032703012004030b180316020604050d 73
    0x180c200c150840810b002030f0364031078080d0800308018102000810751009070480812002100000440c2c40501c601058809010820100b07110600c2c0c0000309101c810000c0e92001e0226152001000f018170b0041000c20000600b20001c506001d0068a0346000c3c05800703254080b42c00c8104400000d10a540403034260110103d18501d5a4500c2d255000f4102da1050341f00504104074540103000c880b00104001007100c00403640191a500d4000c0d1041c1180710395580d2a078040d070303081e03100c018515a40e19032600301c030300340e49880b444d50385d0f03070401600c1901c11099200ca0031101040040e00c1022540d11007a030404841001194040c1c03104505801c83e1b100b5039001002c00e00d404000c02100049000e0001d200c034040d0051403d000304007002810b06036000c3c4003241480101c0c0c261204035102548044101c0041280030441900c140d951400395611a000642d41641c01c40c00040d140b108490020744c5141d0102c0c0110314107403009030030103000e00400ba012a4411802c000c00542503940c8000411a1400b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 163810314 1250 163809064 163809071
    0x41409040c1e0e13210e0a1409130506070809030412050c0909031309020904020c011401060f08010f05010c0f12111501030c030b0c16080a020f06011a0c0c030d0201 72
    0x2c129900d4036031480108111442d0503912009130025602115200101c00d05c92106000c41c21101d6054034a002e01c41202c64000500101c00950340c1000c2941503062401542c844140c2e854624070348050384000c07000070344980e02510104011501c20b1a590b98400d0404054134201900c545982a030708491403c103440300d81c482c0900f94607a03c0c22802c11504070700c1d0400218a0000c41d000d5100100d0203500c5401901c40d0301054001c503a44450301196003410205008220400c0740c11a0000d04207400e00401001425420b40e40d10954042e80d000d50580c0c0841e15030915440c074000c01101d04214a000403900c402c50040c0a0340010030904202d41006a0783d190b80307040001001b20035290958810000c141d02d61000010030100710040b4100d401d0365085032506205a07a1014000d11503c5181101c505001c00c001c01207050045c0c18001d020150915420f030380102400c0081c83d40d4645c005c1c0100900070088940068541d03841d100203104503001c95040c0d5062280c40b10019040c02142a030b0200941d44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 163811564 1250 163810314 163810319
    0x9080301060318051c0c020406060c0326040f0203011806060501020c06070c0611070807060507020406050303130501030f0f0501080304090516020a021c02100c0203070902041409040c1e 81
    0x40600402030f040140c08034042c140c0c0307a16100d05994002004000410076516800300c0002803080f982040c4860300030300180101d03640c501c3c00400c2c482c024a41a800244008881010704000c0b60a0304d01c6000148090301c8a078032151109050116107000807a810740d6a00100c408080b0140240888140111000a4844e1a01001901300b00c2035146041c410340003084214002000c040d0010300b950b0440c507102407044000440707030b40741601d10317081601e99200b41c00d8002005640074008003031040c1700707440074407509680c3d000f85503407409030351410710713984005690034051540b080e800300c501030540b4980440c1c00f50f001c80b500b4080314401c3c0c2203c10703503402c001414005071610380a21070300849108038054040b50059030007520b070213090364001d00c11540c084010140303124050300c180d58a0340080041d00f0300481d012020788030340595001240280191080025001c00a10070780e4100c07400042110303003c031880010001801e8005100715900714480a0100340700094801944041c40c0c0211340900150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 163812814 1250 163811564 163811567
    0x100203270606090a0225020109170d030f020703081f0506040b09030d0207030209070503040f080a050c1006050d0f0224180316090c030f020d0f0f020f1b010f0908030106 74
    0x40700510313801e529801000103c6c0350181040105400748041106080c0400b070314401207414207101e9011a0307081c0410310705401d60100205190b0308400003520f0801c02c600b4210490400d90040c100007801003007840000428101a0340d2003105e01c11700069504810549601c001001508103070411940010049008416400d040060300751402d42070005100c2245141d002031036113500181840200100400840c080044010004001e0f5610000c82c03900c3d10f41800c001131040d000f80384010b40d9446861059951040c444c0318150a6500260000042c0c40d0036480f481c41c4034590080c01ca82008485021298038080f07841182c000075103200c40265910401222203021043c8913124600c2a0041c90420410f061a4211a0221010114045160305440c00203800511b10070505100c01c0703000040d0b411992034554041107848120000410648801c8c15804080340190026503089600030407911424088118582210105400002c10003032210b01040e0f0a5031000c003001c46400d00e0110040c131880c1d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 163814064 1250 163812814 163812829
    0xa2004050102012405010f0c020303161110020706030b010504030b09010506150a020307060b0d0c03080a0306060e0901090e2404020f040515040c110a0f060b090702100203270606 78
    0x2034166607808152035038504c1101020741c0c210300c111814405242c880102c1d0500a0040410158000f0305a0b900d801c080300d02c81c0490310f1250000c6800c40d418401c85000c80c0307482c050240c4080d0304d0ba4010142541001415170040c0100d081040c107003c424440000061480000184a100d210b4008280d5007002028000c501d095451802101d03001030251000b515400000c0d281c565800620104038a080c490104400b04045440508034000341c9401206026007440100b000c900d4541e03041101c2913413503d0444c2c034507110302e449075444111800100042c02c0d540d0001403103091f11109903107150303107200322101d1805038060b13004000807000c0080206610700343d055001006403c1d18180001c3c0f030b24520791040c50350342034460340c441c9960385420f0180d41d104c0c84070190501c03c1b90317003100d8401d0343c14109500c1044490741c0440d079107414051a000142854043d46015aa04c0d400610f4600009141074021f034100a161150050210701c5040000364104000c10030b41c0b4001002d4601170501406102c1c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 163815314 1250 163814064 163814081
    0x11210a0206220b070c0503120714040f030f0804080303070e030d0f02100f020f0c060a06090b0102191b031505010e010515090406080d11010b10080f0a200405010201 72
    0x80c4128019058400030389001c1d42c0c945140d001c01030305510b6440c22400d0303c11035480840503000784008540201c56a90444026000300d009440f240c0152400008181d0a44200c4c010002003409002003000010340807800d003401c0f80d00c1494664100360b210a6102d2035900201c0351180051024014429a418240314a06889900e0300d032424103d00b00e1720000e90703070302da14039540c4027403075910710700354862030441e0b41030341c207494442c49656a0711440016036540d19401507a6410f60585042c50001c0e40014030710500d180d180041e00540038007481e140c400490783c03107a1001614140300800c4072214900108084801a500c15284a0300e08110b5250f0102100c905812a0041500c07450060056075141c59140300e404941c401500d81e640072a50114001c1c040d01e030b0242c600340c40360300c40b00303d10700703030481c0401c900d2410f0750008110007141c0d00d042111201a251075000480c080602261524140e03030301142d0b0280369200041503114075034000e602030741400c80c0301040062000c24240910f41e030a0041440 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 163816564 1250 163815314 163815331
    0x1404020307090b0a020c130606090e040203060408160209010308072001050415120204090b10020325031e02060117070305030a03020a02120c0105010504180b0711210a0206 75
    0xa41c80c1c2050701800720555806851540980401d0508480e482007001d0707410050054080c07003810706404c5c2810040e1586014500104014034008a81c4d00000303c02288a40d800400508a0381c0f03981d21480300c4c641c000740021103000c40340101240962500301001e402144108075190f80e9025030305010007210741c500010b1801d40a1081290303002e170b0b48035080c4c0d010364209801c1001400550201902c101c0b0796194100c03002030020400195035529940940b00300c403000e0b1034040303404005d038004076100d20810000c03082c540c80f282007003814031054098803c0703410310905100204000d6101c400c403031010308119413001a072005006001145e0307405860b0009034803943c010600b0710f055544064070b0740100e400780e104055001c9145400a1300c00c200c1e2420310344103203c100d40e0300d42829612a02070300b024000d42d8001ca0030840c42280b42c000111000c880d281e0407006c058a2510f40c90340c12520303283d6200000519205403118201c8501484440c2d6007007400e4280c116035103003c50b480190070f00c81d0041c0b6a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 163817814 1250 163816564 163816567
    0xc0109111c020a061101020c07180b0303130b030621010c030c0c0b060603100e0109020c2406090a24080d0908030a0e0423070e0a05060409020702060f0a09140402 71
    0x140183c0b6045944402e07200c150401420b4581813001d224020b00036000064172034480c0e08800151640310403003031609840341c09000d2003100c0e81401419600e1103041e50801410b0403480042002d440244013640d0400c1005203c3c04007440440e4900994080e401910300982e503542401c500116018469855081c81600300b800d03029200340c072498016040100307482d01501000000a144180c69103111020300764100302c55016585610500001b501b0407241046184140d5101c2c611849100305d56085041c0504e940a041c0d944040034840c84040c054a00810b082d100c11501c064640c21a807843c1c105218000404166807900d03100382e00d44140d02100c0350602800e10380910009001104940100b00720342011a010300c00310300440c000709415010962001017980c1d008081c3d17200c01841078011035260b6203024000e07645004200c46c540d4230348142075005000304400c02110f08560003908401d80020704050400454001c00701140c2d0001060f040060900001401180c60242041c03044040546003103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 163819064 1250 163817814 163817869
    0x210d0e070b03041b141c05010f0501060f02070605030f01060c060b10031a040501030206070201110c030a03051801030506060a0c02030c060c0a021f080a0e0a0204290105070f080901050c010911 84
    0x410050700304042c4044c030386c2c05400980511009400510342001c00c4a001c000790342e5103100007850000b0111420006004851000444031702c0f0707a0540e8025034103400321070705903480c0150640314060a0302040742c145403954101c40f00d03640c440f040c484106813507440205001c0c03510071440903400c407800d0714036200394504001800903844440c1503510403a03080c2411141d40d07072070814803481d000e004020700380e02d8411220004c08040d03001c00540b8407240c0459050724600718100054084d0341c81103030302c0d0743c120308180711100c242440b51504e004c90314000740a40e0000034080303000c1900c540c40005040d01642c00800d0080441c213102080784414000052040c0d8030074000000140144005407039000c440d5200d1824030107032007042c030203c4400780d030082c0200102c030840c07021103044400d064012b603030041400d07680c3c5002d5401072003103070082540010705030b01090b126a45e520003a001003071114104041030015442c0070b00300340714007455540510410705502c0002000c014031410780342c0d81000c0c0702e074201c1c461 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 163820314 1250 163819064 163819069
    0xd090e01030f0f050304270c0c0314040b031806070f0c0b060117040303092a0b1e0c1f06030b07030903031b11210d0e070b03041b14 58
    0x890640e82e024400640300942410020700070301089001820714000040c0010740f2040c41d180600c021041080e1002c0400038010883d030850b001046004082280a1f0882000900c00c0c20440c0d41201e02c03103151414541c840080402c0340d001101d5800c1c0d0f214202c003090240003030401001c0c0d444603452500701988dc0d19210010455404403400030a191004c1012071000da0046009682c1e001c51080c01881918043c10000c0150444038002e98210980131b8402104050008501045914a645071181280740000382005a40160010030450250720450411609180010901011160000d0180c3c00e0413040f41400c2000c92101c2ca1492072078a04100000b0f101d214206501402d00c0c180020a1215418141c0c013030031090314125040880d1182043da0142c02c01040c047d417500e050121031041810072441010308000d000b03600392000d001d20030318041e0800f0f80c1140d0784401304141515032031541d5088240d10707500107031012140002c4161581d051040510086001041c0d40300300002c0c2c8074550300c013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 163821564 1250 163820314 163820339
    0x3020c1e010525050c03040e0403081006020705031504050f0f07031403090a0902030403020a02060d020a090902130e04050a0501090c050405070921020d0f0809010f0905011706240901020d09 83
    0x8504180240450110117662007441074074010003516401c0b80d154505481d004021510844400010200b01030010401c00d100003403890a8803c060001d28103d1003d4284a50120005000310b45610414a206145c54018807085031104000f02c002e03c021825460810a1184212016240356105020056043e900c6c2060801112a03401005075280c40d9420100d0501d510460040d400c0100081d1100000d40b16a00410502c02d881e542e8210340740d22900004181d20402da0201003601c4c484400340070510340f94400d690420b01c5182200c85260f65039540509407039403104140e5040da0448001c225a0405000f030ee81e001d1a1803410310303040350501d03841113806031055020300c0c0c2d5098031400000131911400301d4a007031190070007030380d0034119414038005505070f0006510600080408040c0440c85010354190415250144c690b04d040050100d000300c00403000078855035000d1040c2d1040200300044004040032213564028842d44c52001c400064540381491412404000c520f21007080580d00e50b58 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 163822814 1250 163821564 163821631
    0x601020316060f05010f06090b0315060a091d04030e0904050a0b06010302040b0f0406170c030403080a09021003062612030405010905030c0105100b03040302100c03020c1e0105 77
    0xca1070560868942003400003018040000d104607450200007007901c0d58241d485904440c047c0d540c0740e440c0d50703c4800c21441e50000b0342d83c101d0301c4141402c002d080343c40c00c20041c06207800c2c140b034140080742c0d03240d408058400b07500d541400c031902c2d01e00600041c1640496040d0f00c070b00090b5680f1401d41410380c0c0c2c10b6a20701d105080a050f4006c8200810b0b41684070750111001059a00030789031315001e0549004006521a1155801242c804641c4440100085ca0014031401010036041d09581c0d403a202901d100c0001800c2c05440355680b0f10460050b0748100e1404c56001d40c5036000281507060100c0488000060141d030030340d4124168560074502800a031010030000040751540c0c49440740c1c03a02d213014281007a4020001d02003c40c4089075a00c0560006102e0b540000003100e80039500e00000c1590320056038040d006801c002e80d0f42410202c59006400100e440d8540149410103042100c0d0030407010107445080d1689224070070951880c2409000d810054960002050001e9154481203485411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 163824064 1250 163822814 163822837
    0x62d120403110f0a0501050f070c12230304060b09011a0d090c030807080a02060a0b0604051903021302070605060616240f0506031014060105130b0a0203070506090606010203 76
    0x5042c907000203a8180882c41908180d24200e944100892400601030602102e01c0c41c02d00c940100014112445200450001500f004003070f00280403a9000300c035040b0f06009000720307860310a04038411002e44440114400c0e8020340e000543c50b00440100255001d040e44070f0030a0103100041d01850410440440d011200f45040016821803980750000d480500382c3c1c000341030f48901180b0001449004401004d41440a078240d50386a66504611011955010070352070300200d00780301c10f0100d4203008402a01e543d01c401070410300c1c140d9981c00102480030742c0c4400c03100709230041400c208111040c0503060708100101c842e181040140c0303165040100d1451806807003058489409012070917548040c204150b03074540c0503c9072501562004010b044155040d03406481410034008901140344250350708451920844030580d01c440004507100d80000e100b2210b4001c2e40303a400906228400010551011186c01550711903806090450500b10000d011428a401c140f0800c2003a03a8003004448038030891 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 163825314 1250 163824064 163824077
    0xa0b09030f0102121b030108100b0f1009050109050d0f060518060106180b070b060603091e0105070816080609040c030f0c0512010c0503040f11062d120403 68
    0x412000074548088072148201a520008001c150340c0400f15000d4810000020f240d0030071a5807616002d035612007440f43d00800d0704018040c0f40300c08015003000465880051010f0500c81c5d00500140c5420010044070b8081840300b50100015600122240c00a20045400b0401d0300142d4071a81031000080c80d009100d15619070001c1d01da41024181601020003600490700503603180d038400780008811042c5141403100001c4000b445110000454140075805442403049844400a0010f642c001403d154002c0c082e4104220f0701d84008040c0c0620b41001030000300715400c1c80e16010b80000009414030503102d25500501103460741207000246c0100003039801000c643d94504100c81c210301e081d000140800c4a03031480070180103550000505031502140c0c404031124284090b030303003241c14002d4100d01007a01800003402160a2910300c084941c05000c141d40b035162040001011130f0710101c0700d540003403000d0340c02600354038000200201c2c0914090051349802d00300101003142e49802400242000507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 163826564 1250 163825314 163825327
    0x20102030f0c070e040c0e1b091002030d0e151302060f0f04030c0801020307030b0102060106171e070804060e070b0708091908010906051608070507050102190c031d0a0b 74
    0x1c00308903020040c102070390100041e0500d80f820a800601c144640c103e0000f000c008100d8150f61281c0009922301ea0408031480d021200d0103018824609905150950209202a40300c1540f1400b50580c00a2498051300091100342924010070601600c2c81d14040007a044050058072aa0101c0708561107101c5019111001c5914600d201e1096400c0184110508500081d92020540203180960141c0d28244287c2406900490b60740d0024800c000001d5030442400310400074444031a13400600c111342c1c400c0c000325200d050a070000750aa66803400241000104000d108442c81f41c500c0741040706002c2c001081c82c05281d48841d000b89000941640030005581d02c030380d6162042000b00c0d17038211204001142d5200350280c000c0000100649141d070900e400149614046907000d0300706203140e220344600c2c0c1c880d00f90450f52a0040a011203c5640c2000031080d484102c2504851100b86a600c11518210900e80148031400d8030f1165100003902188a0341c1c1e0769907501141040e9255035000f680c8692 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 163827814 1250 163826564 163826587
    0x1107141501180b041b030f0e060c1c091b0603090b0c0d02120a050a1406090705090111070e07141614010618090b010806040807060903110d030c09050607020102030f 72
    0x21403580390f660300a282c0000343d00b054540703004c0003810362000d85082086242001c10001035500180e0400d41c0340d0441c0000070f1003488040c0140c8100110b01c10a1024002541c6860b4100c3c0ea00c0c000988000b504204c000d4001c0040d04090b0001d00381615060041c2102c0703903180c58172603601900e40701c1d0f070700d1000c503400d002c007441a4155218250050307101005030418051600041c042070702c001410b40d0903c480f840a034401e02c0320150041ca00540f80122641d02c00c00122119004a20113504200c0c40c8010492800300803c040d0000e0011003800c200c4904081d1700190621682c1190041c0750081400a544040d50354180c4024003500170303c3c004112081d55107410f00409840c0c21078502c51604006443c1d12521607804121154440d20003090b060340c031b840403e0b90700c0c2d1080b50001c00c03000c000c2042800007030441d00030f4400710384241401c0c4e540200e07087d6a07604044d100c142420000c1e9650141e441241d60000e0300400070f0005540315403400c4800d4000079100e10070380c1021509041c001400354071b901c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 163829064 1250 163827814 163827821
    0x50f011803030e12030a0e0a090c08010b2d09010206060108071b41030702030d050d020904050a0203040201081609090911030f030c0f01050106080112020a09110714150118 75
    0x115461060b65951074441001424500b2544015401494000d0f40812841950b01c1590880d14640d1100b5003d0ba00e00dc401907480d500604000740760409000903180c0444045504100e080d0303010500c04e80399204400020714090006010604000c480d0092001464201c016078080c0380a040f0318850b0650f082c00c1415205801e00050703d11203100a002848600020300100f11600301081c20b000f00c00440880180d4a010b08400a0351540050000700d030b41c10700960042040d41e404400140c2440001c0c8001001c80c2c0c4102c8a0241080d00041000110340e841401680e1104a0056079480c44040b03020091007080d082c001c070074145035200c05030350600c07140c03500d0004402c000034222180f2100e1031010b65206c0e00403011882e807900c50b07000740d100700c0601801107a050340c40d1a43d03948600ea05c0c00204520030400d80c03c00380e0b00031254080100324034145024203441207141c85c41e0709980d1113051400701080d9803501e00d404215000060ba522448503913400c100d0441d884440001040d1484c100080000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 163830314 1250 163829064 163829089
    0x10b120604110d060311030615010c15050424050c160302071a1b061504020a121d0d050301050904031115040c03200d0b0903040f080106050f011803030e 67
    0x900740d01140c42a100400d9400c0304e82560304c6030b0751600700050040c00b0b05986c0c601c15103840141100b6030260f0a6154411410f010115000c0c41380100c10f0003060b00c040c4106c42040d281980d400b180701d0070040c41201d022010903144c00f03008030104050b00d0070280d0255280100f2080241c500108040322040c18070801c1118003a1561000c90107109c0f80c42c400c592115441000036100740080b03894083c148110102c0c45034450708a030700701c0000c1d2003071010401c0020740c0040001c00030711403d8042040d002035248940c5500d00c1ba03203903503503400e410b1070750342989068038440d480030030854200014440741d12540c0f021604541d25080070061382d414031a9160500010031041c07410091003104000600542d4810002220b010b0708828821508400c90180c9030140564000e03048000d048403c400100d0103502c852340200f9500c00d590600c0e0711a05d407501000001c0e800b48046a44402d13050029280c02c0c11707080102842400d2044080c0158002140446024400034003030000c249240d21441d19070038810f850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 163831564 1250 163830314 163830341
    0x80a03022a03120406020c01021513061b0e0f03190204020322050a1505070f0c05010e01150905010519170a0f1a010803090105070b13021f0e09010b120604 68
    0x3c04044031018100681061140000511949071101c40030350002c00e110f20800c01d2610646103958450304d0684041c55482340461350070fa84c1d44090042c403050f9100a41c480a500c0d5620280c0e4408041000b9800300c0009041d84070741c0151020b4007a19103d508a07640503681641c02585959802d028824801002c400c0c5039006014180c010040101c00f0941b2260f1512030381d1200c10701d101c3d101490084840403a40b500209041d88031400115000700080000c0c80e21650020641c10502079070b280c01d590510201841c030001034041449404841d0103001e0151406079240c03880c07540c0190003414402c80398400d400d00100c481c83c83c050040d41c2808a44c00880c4c00c0960300074080e040f031504003e00340000807000401e42c1d03140c0000c47c040c0d0002c0222540e50f03e05070f55181c100041c6440d1050380c0b0a008c0e105511039041c4180d0305005031502102c2c040010000110320b0080300a12002506400e81c64580d68481c80c007150050001c07500324030560710700c0c00510030719a00c103a0b02c190100d1700401c800b150000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 163832814 1250 163831564 163831573
    0xe060c0105010f17060601080a05100f270209010e0d030c0209040f020f0102070503330406050702070e0412050a180305070f090209130513060c02010f06080a03022a03 73
    0xb50304141642e05001311080640ca0000c2410341040c156201c1105452460010300148045640d41c44039400c5180c200a40c04515000340d40c0d111160041c440080d401400040042c4a4283c02e641802d100303d00d2414401c00294640742c68800001d1000c031041201c20320920004e107010b4103240c426500c88800c0d5a014000805a040070304007040965071340c00c0102d08c104100302d5010350395407010600004a42018008040100900401c0c941181105c0c00342204110460701c404506481c2810460199003d00d0b4002240e0404460007401d11070150071200c40d141e460f00500c80040d64488004e0140c500c14603140303840b41c0074844211140c00c44a05224001900d51802100b409030205829003142d02c03610800c001d480d40c0d050100c0c180c2c0507407081e07158800080070310950001926042280d0040840c80b25400c0d090303007a41c40310300f2600d00d00111130040c0e5442c0301e00e0444c1895032040b030020302007220041c0400007a5a8000b566008040c100840c000d081291960403210b001028560f81c100007420782d0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 163834064 1250 163832814 163832819
    0x150a020a080309010519021617070618020406060c03090e0a2c2802060d0605030f030d0b010504030203031801090f0602010207060b0103180b190f090201090506040b04060e060c010501 80
    0x1c0d001e00300a1b10000080c0c0c4141003245441200361003101c025111040d00c00d001e040c04e80e02d8400001c440d8200300d0441c400100291000038216101d4140d000120388804c06c036a05660052000b2601241c20075410300001015400119070483c841030115401c08220052a0b5982c41e1180d0207000018184030113600d2610715000211301c41c8110704081e0030140200c6030281c0350000002d0500089010703104205410b041c2500150034820001c040c20100780d240031540c540d685010034036100459880804503040422140c1c0c07201100c0c01003180038038092904500b01811500000c2e1a84600307204151101150900181664002d4003240002e0035079542440d415561054064043c3d44491401c071012407070202000b11315800f901c01d401d901d0090210244548425503610741c840c0c0780113030112141c209205880b09031903d0501843d102c68001b15400700d0103084038030025252461603044944142c070188014440032031600d0a03038040329018a8181c1c4650051303000f1800500c5071a0752144a9401e10303001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 163835314 1250 163834064 163834081
    0x30204060303020f010c02070609031b0e0f010e090102030c0909090a0209011205011503050309090a02120a060e06010e0310090f080a0315090b030604121e02010b03010c020606150a020a0803 83
    0x5030401000b00d44c0c000c1c0702c041d100007822a06c401a900813940070640c0501d05101180ea5079801c0e9041440b1800a02c8002c0e40720780042c03080031011166104d80040c0000184074100d030b0300840642080c0650000d5040d8201444252298091003940a0045442d0400252a400701f08402c3c55001c1d0044c1050a07296180c00d8031000031740c0345410688113507080c003050780c040503a010568000c1360740240c080d600f0002c0d01001c109604070f0107000c0004140e001c0c4802c0300920310040340c0710b000e102207a4001034018549880f090301c1c24402010181032004e421144219610041040b8500c0c540c80c40b00043e0300061458038000032002c0d078038040c182d080e002c00e9079034003140c066002000107043d11400316000d5550305030180546079092642034054001001040000d0300003c0006020385250420213200906200f450f580c00d02080043c9005039140c450189140c1000e00c5500384500241c40907100c0c2d807030481c01003080c0790300c0c045112001410025441196034802d0000030031803640840455964100101c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 163836564 1250 163835314 163835323
    0x1107020d0b06010e01020601050d0318080105160806061e0a050c030d05060406122406090c0c0201080c07020303040b0307030b0a060801060906050414040906110c060a0b0a0b041a0403020406030302 86
    0x40483c04501e101e403000036158000600e01c6c6c122080102091490121079808840d5941300404001c3c200c801d1090210300c4000a0168901c1815914104840c0080c1071800406003403029101c2800344a0410014070704400401e404010b088001d42415901c58012408a80c248900d01c40d144085c00b020a05244e9261190401406903d003243c09115883d21288001d1041140582c010045041e0660074504802049440f15440701403440014500350307501c0c030400c00c1d11030000211002905000290b070071580c10140c02c2c0d401014403102760341014156030100340da9100f030380030389590f9800200000e106d03540309030495010544003405100704140c2d101806071818100303000d1200030540310323080801d5942c400c8080d0f40c115609003080540702131032041030000910840109548081c0c0f910401e04007000310900070000e07086510020301c820303d40404004100c4d602c5140740340c0328441e082010814031140c4015641501c20002c1d036070303080f125402e050501521690344020741260800c00008140b42d000704 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 163837814 1250 163836564 163836571
    0x130b030105130219080907050a080a050d0305060a1809020409050303090d0f0e042c07081c0509090a141024360b1902070303080a1107020d0b 62
    0x31a424080341d04141200264020000e01c0d040313400604039401841441070004a401c10310000030b603651305480701c0102c4c0020501d0340108005a003d00315410401508000c240c6050302c89103400c200c64100703000040c1c1c9680c020312814000e59001d07000c189401d030b080e41c0701c45041c5500420822003202140343c4241c42c0d80049801c2510344c052032601000d0740e0300a600b11008400e0356511098500d100c0c0b41044024a0100509054036a00d05424030007141c441d04002442c1e4201c1000301641490012042c0c03910040c01c10f644158141145580c500c550803400b5261449000c031910503460b5034140018000f000301c6501d40e4108503034441880301c0b07910b01c00112000c1c5c03102a038880030840800f1504070110020310b4000400540014a901e00c0c94456a500c4520024403201c4019400303584000244103a1490700244815540001e54058041c4101215841c01d036440c005000c40174599140903091a60052010a2640d1207040940034001c100007182e500640c000d0550b9144e0040707040c6001140d40c00ca = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 163839064 1250 163837814 163837819
    0xa111021061a040b030604050408070f060209102c19090515060306090106030f02070c030b01171b04050a090605090c0a08011406060a020c0913020907090b0a14130b030105 75
    0x3002c0c4003085580308802c440c10f0798000010b00d891911002c06000091000030400e54a11006000c218002030501c4071a08480c1c0c00f403030307015845221910802c41e242603800210f605201d8548035003601c1e03984d007807010f10903881e01d28111f0a0410080020070301004040000c0c0c981440507903c0414103220551005015025403c1003440044d0100f06000347c0b88010b448665102241d03400400140d0300c44c0d089000803040c1d06030094100485036480360200d1249410403a268031131a401070101602c101d02c20754a1461b641300078000c0742001c0329440c05000340e40000030300854442d8001803901140c1e800010350158000c0003000b403413418580c81a2a030389150340030b85c4106005400090341074014040c0328101425403440c0c080b10f4035224204140307035000d03014420030b40c02650194040b654921014038400c03010840e42401600b22403040001c0c05e1401005402404400c2e0800e0085000190a5a0010785c060400c03117524491504101d0040c05003a01d0150700e000440c42c08103000003d00007850490b5001d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 163840314 1250 163839064 163839089
    0xc13240e010503010308070b0903041e030227010312140d0f0501090e0d050717030108070801050717181002040b0c0f0304150507110409060516020a11102106 69
    0x80e0011500e501c400c2c440030307100d0001400554086154240030030b400007060000c49242981d90030704042c082c11350035280c000000d10342c442042517080420320580061a20781168401010072001c031409010113001c00790450b0010000421058050b0243d4840150511001501c0304d140340c4801014046090302c07140198108000000c81030628011a0b20b02d9031a00c000d045900c540890880c0ea5412040d8103076a018009076407040500e0b001001076001c2d20b68003010b003049905200b500ca080d500003034184400c00003180c1c041d209030716000ca102500a1100360000d00307110100003080740780c401856800f5550600c006400101014103900900c03450030751500b628507400704a442306450303009900c80c400220070003083d81403005104000801010348100301d0020940006000300d400c840145108581c851b645105200d200000e00d000d40b800078000784010003a500044c0d40c0d102c100e400320310f49030307000d04070b184142044c2c503011b80d103d562000d0f02e240400740c88213003030400301001d04001d00c245060a0107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 163841564 1250 163840314 163840337
    0x100c140309121209011a060316050405060706050115080c0a08070314091b040e060109020313120504050f0607030f1b050115060801062a060902030102070c0e0109140c1324 75
    0x11240780c002c1586c10300a040c5810340ea15840c44000c041c07800812401044000c110224450380c42001403c0054000c28000030150f060948110200a0401c01c00003032110000800880142c1c90341226148081c510300100180c13201117060340074003815441d070b45017504c1d09820001416400181100c0c14000b05040280040c000000d010071a150a038000e0007541003040140102c000540086400200d118840b41c2660a1500e40080c554100d00030740e030005400103400c1020f0301e0580d05c40c00f2049000c0300c5c2640303854510b030f0700500b007400d4240612091051402c420134900d070305d05188148071034004009000c0b014407a03179503004501541c015034000c24006400030078a14494101004041000303a030705130060400c10f6419610040200003240c46585414a180040e2000c1c000b0b440702e5071046200225041c01e0042484022605070485019107180044110004074000b0000c2d4200d4a40b15120f541c4507042d940b01000b54125403c0030500e0240c54150140800c00101c251101001c1a0380c0d9a0181d00c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 163842814 1250 163841564 163841591
    0x1806010503162c13060501170a0b040201050c060f0604061406070b071103070503040305281403040317030612061303030207050709020304050a050f01090c05121006060908100c14030912120901 84
    0x4080203234074880340d000b030000d0400101a20002d0381c1080c014103010341000d0192400915016080b10b00c41030035041901809000d00709401400094185180d20f044009001c202180300745c02120f9010301161341c00d40211340c0d95070090007981603940030a02980c0c3d907400741d801c080d81d81c2d80c014482122203101d84900c0904412454517242d0aa40c1300090b06240102552030b0a000d07040342e6500c01c0d00034081003100000007886010208100303082c00482d0381e2039143c45002c02c0000c1441c43c400c010103411150421111246480d80c0d48042c5a1500700140c81c1c50725410b1084c0751020760b0700143c0c00f981c400003d0100344000051003400ca83d100e03404681c00304003000102400c2e00c030049802001154042070921480c030b001c00400300e40c10f5181d01140c00302e000803600c5c042540d005620007004134840040500aa000034810f800d116500864180701d1384850b108000c10503a4540c18240e074201e404004526005028468080034140302c012103a01c2c1c010304800300030103060907501c0c04070030340c42c02c0035070036462 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 163844064 1250 163842814 163842839
    0x304030309090b0a03081b030301060807110604080a0c0f0b130c0902090d060b24090102010609020c07090c090e0f060406050d0201120f0e03031806010503162c13060501 74
    0x284400b40a10000174a543da521001d50042401e1800392140204440c040c1c003000c2000d94000c0025549844c51802c003070700040c02c40c002401040390b40340c020300104808201034800300c07598210340e45460780e000c10507410301811695014800501d40e960a07800d000928052481880c401400350003240c140d5641c8400d100d080b80300e6152003503044904010341d000810f03130990103114000000f800480b513050018000000384607440e40104400c1c00c000c00c20340c40c2c41d642449281c1c040c0c42030100440c5000d030a0010559220024844c0e2214151144400740c81540b00700c4004004007401c420540c5541040c40340700f81003400c2110480d001b180341040004103403614204400741e954040e120341e0700c1056122805030140501d40d956028140d160304902406100c00c1000310321404002e480c083c1c5032403004081608020b010381c09144241d01482d0342d00180700324076070940104d82c0b401030034241075a0604421740d1044941504d1100e0740170b070750b410020100501c80192000c80d208480070081c40c0c2c0c0b41c60040031031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 163845314 1250 163844064 163844081
    0x20c0102160905040204020702090a050a110405010801050d02010903120302030105190b120615040e041a0106080c07030905060c03090102010b040204060905090a0e0102031e0702060403141812030403030909 90
    0x4058141c070100821002503114680003400644094a0410641c02003081ba52064580d42012642e030402c11000410b01d00c40e031407d0001409900789803514000c0000c00c1840c060003164400c440d00c0154008580c01092208019a801006824030000006024009410074070416000e2595030005040c01d9011000034020703508901901414400c9480400800d801c0003071074940c01c41501503811040000740c2001c0c01c024008214441070a1402d49840e107007481c4400c010708690420000140302644d0400840ca0f0300403129000f90381c440391141002c4903000c40f5079000c2500610000303001c4650030000f00c002d10001310207800070b001000e40c103028130040344580d1040ca00000c1c001076050200389404280143c02103842d01d40481c44410340d400d5103003241d100b80d0b50080a404016188949c0d030a21640d002d5001c0c44600141c581d624060704c1c003402059408550500030200041c0c50300021841c080c00444200c40a8031562810303414841c80c5036030b43e105010507070109000340d00000c1e4111550150095 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 163846564 1250 163845314 163845343
    0x30b0a0c05120702070b0c031308030301050a05060304050109120e01021606080a0b0d150e060108010204060c0311160801050a14010b0405061c140105010f030c08041e050a060c020c0102 81
    0x5408802c030308030301036400081c0c6184114014036200080b0303030501c24040d00b000c030746c40310203140c2d51200c012540300140d0466004011030f400a000421941d40c480b48002c0446a0558125980f940c507840c0c114018212504010455210443c000c00000e50150000044034400c1e021500707541026585036070f00c900c0342c0c81a0b800040c91440001c04401c800e8115818000d400b40140c0c0c805545607650000703064880320071030481e564414040a6544082005500400522000318901410301c0c01c014800c030750f020005030a1102c40d03442d40c0c90385001044642c40181c0070141c045400740d141c1c1c0d00e02e0b021700001c0d11501c0405003440082d00380840c05120440c100e52113034604900e4680b0340001d200c100d80024060b40420840200640000700090150b00c145c84054950440290f0504e8009840400422040780801d0b140ca400d034042c0390b41048007a504580c0203100d02d240c8a01d0120114075107624410000c001d4012803036407800f0025641c226000e90012074090301c0b003d15241c40126503c4810980340030303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 163847814 1250 163846564 163846567
    0x31202060f07050a031409030d1401140d02061b0a11040614040504140d020a02010318020f120c060c0106080f0c0a030b06030c2d0f0d0605130c0f030b0a0c05 69
    0x40402e0b00540040c42c2c05403507070501046140d20000620b11115080300c038102c4035000040c810f41c0a4900f03100f503400329040341c54000e2042d4104000b404003950340014641c0128401ca00001c19550350109170390002c64951050500840e142265a48412000320300310f50b0984180007140071450140507a109451524120b4102e035408501000003408002d48141c90704203025640f110382d10b8090140c002011065001042c0383d140e1440010200c1d940d02c0010301400032825400b0006030b81f0500c0303440681900322220188611205403407420441d00c40310b43da620650010b803c42000b101034100c0001c50301810280e50b0360f1a00358807010340b104c410f00c075541e038001c00c1d07440b0038000034101b0103049802901c0038085803c1e456007031000c00c0701e41400428142c2d00f01c00707001c07142c8001669141c0100146105030340d018040d4501e400441d17801140040014080743d00c8100241d49031001c410b165820580041c0003d800341e035140c94050345480e20340816111094071100141e0080d105000e000c10303041040d95000e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 163848920 1106 163847814 163847821
    0xd06030b070c05070f06080604020d060b03070c02040b060403020d1509050312010e10060f0c030212070f021008090601121b090b040e0a0c0b0a11070b0301031202060f 73
    0x41c41001003226040c1b107416801411250884800d032800342c0c46040948050010380305540012042000110812030380076800f43e210b0100b9402580c04000250712102071081600c0b032404040e4000f01ca840c0c043c40040c201d035100803011740c0300b0300700001c0c010003956601d800c6500101e100c4006200140040c003219004004442d00011780d0b94000d00c5907454a0301c054080c0d04040303034080c10b00404000c4041494000e12210b02c1040e50f00c1036150355207000d0701d404510001d42d08000d901402c050b201c42001c96000b241c0e0140a840658000d1100d43e20301181260b208000c54000c0340d40d8483c3e0300d90400c90020000e0341c04080c1040350303400300d00c0e41402024841190300e1445006031a41c0220f500c80b0219204100c41c0c019180210499070343d9022050058030085402e55030000c2521405400082101021000d107060b03030b124868110301444800302c1240d071081705a460f12001001d0b41c010 = true := by decide +kernel

theorem cover : BRFrame.Cov 163669064 163848920 := by
  have h0 := BRFrame.cov_init 163669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 163669064 ≤ n) (h2 : n < 163848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
