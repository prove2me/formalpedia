-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0704
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:14:20.524748+00:00
-- url     : https://prove2.me/submissions/9fed0abe-007e-4107-9169-20620c5f1b98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 126438848 ≤ n < 126618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 126440098 1250 126438848 126438857
    0x91002160321030911062d09040b031c0807050d05010e01063b01021908130e010b09041a091306150302011b0c03080f0307090b090102031b030f0c0705031c 68
    0x1440c400b13140046c0038242c5403040b86400548000010840794094200700d80704d0b110207502282c40700c0741d0300f414441c610002c40107500501d0542c1c0001e50071150300c050141014104000d480005d60090f2060046c2c2d004022101d809105030350b110404520440c1c3d00f4040c07a03000603504840b005000b040f003c40003510030149805d50000b00710914540c50760601c0014998150b202e014000c010194200c4603003604540182c00407078680400e0302c0c03240c804600170742c00220144114001402001a0b101c11102020000c8800156aa95800b40424421003814555034041007120400420064903004403186522800040042e00c24603000d04004034200d0201030b00180c51008e0a0721020f0105d042504000e00680d404002c45036680e0310b585140d0700a2380c0100302542c000c030a014800c2d4001000c10047d02c1340030600e505001e20240002d40c0e9000b0100740d0004e1460a03d911036681800340308948035864040301e020354034000091116078900c214071405002c0e120703088034185050700000708900726142e140e07075 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 126441348 1250 126440098 126440123
    0x2010804030c020301061d16031b110a0209130302210915040812070b0604061d04021203030a090c0506040503071502030906130302091b0910021603210309 68
    0x3801c4403685081d1400f2a050340d46c0398404102c2c07180f110b044c8128100d00c8141509180f900c202c84000100c01e2226190905080260082059694002e00c1030f02000340e240012080d100762304617034070f060080700010750808101d10502945245100344200c0380ca00036002c0302e8100d4116100040c2c000a151601e4140c040c05026402061a2000c2001c00c200b44981105040039202d1079864104102c1c1c1c0e6401145820011b0344a04210272030b18026807090040700c1c1041268905a94940341c07140f18286031b50781c00000b01c00202107541c1c0044005116000004407a01c1e440c0c02e5a662004288100d8113032601d810800c4000b0f01e03854100d08031002c0e00d0b400740103420840d242c03141111700d9040d018520740a50005210303044243d01c40b0009070424002c41c0741a00c402d42d1942c0140540548094001d0070a88090490f403031080c4c02c2d034003c40d40206815103030b030221014811812805c0c0501801d240c0c014003481d44002060198208628241042c0d00f485c14800c038079042016006c8500c5180000d203042d14059 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 126442598 1250 126441348 126441353
    0x20f120309190f06020601181a0402072f19050d0605040c0806041a0a0b0a150e04090501090201110604151505041e0e0102090105030f040c08060f04060c0302030402010804 75
    0x1080550800b0b00c4000c14018182ca03003100c82c110b00c640e0381000c00180d100b03030010815040d0458003180d05a040b510708004407008290600c038a400c02ca0b01190149400042002c01c2103142180703c10b45016100c0c84403040086032050b40380300400c0e842403500c02c407600100e130a14012100e000a0444500401640800c0050369a942c0a0703c0000c2c0203544101c403018001130521030a005091055205070300030b100111a40c42901c01d00c03c0f01808400d40680384c00305031034054030b4100c641000c4c1c0d81800603540c20000425811035000304644201504181010942410400150000402075100342c03640d401010f01d80510315a660002c44e00548510002c40200e06200902c2e0f116288201c40d0b40b0201e58400d0719180454240e4800c2d961006244403250040001071405100341c1e404c002c8080003e524005411000801e5404080d0a0050041a9038041410080c410b50641c0c01844842c090315000c0c541019800a8064225020313038402c0d04048000422a220340308803442154141c68000d0703d85c0b180e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 126443848 1250 126442598 126442609
    0x4020405060f091e0106030515010c0507080304030807050d020a0c09020a021c02060f09060601050706111303030801030c120f030e0d05010f09031106070207060c05100906020403020f120309 83
    0x2500240c1c001481442e40486511140162072003100f000c085104582042011090402c0d4164485d100301483d0005201c40030300c0142d113540440c0c000f40f8065118082904015082c8030107a8000b407101d1000003400070410031528040c00c647d501600075a00d0b8201c03100b0007a03031901e180701c034010100c8100c21014801010540c0c041c0c07600c0b10303072407040380c20414001420000351808082204090780c01603042141004c0d804d0705155200c14004060100703800c0600c0080d099002c2c820000b4541500c5840c0c100c061080e8605441246c0003402c00425604c0d82e90501078814282800151401c04241101103038144503010303005011503001030500190090703910115110961881c0c215404044410110049282401070b50600801d0510000740307a1090b290140507114001c00e500546d030010b80c10402e03515004641d4104680d074030304107911804864030b841030a0900e00b2003c41c2c0044c0c5080504000c1c054140c0c00b03003040e28400d0300d0403c0c60303a883d0030410a113a0b071103400015803a4000c11040c001400c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 126445098 1250 126443848 126443851
    0x901021c0c0b07051902120a0302090d0213060e07020105010f031106090910060201060614040504050c0d0203070f09090207050703021c0b0c0705060705040e070f0c080a02070f0503010e030304020405 87
    0x3031a14030780314442591074210030342040e182d0b840001c1c408544483c0601500352426151781d5036000801c4101d11009598085010f0b000400c401d140d40800e44000c40d443c1d0041000d80341da401001c08018420301c44100008088071302400200032940000602054014460541a100d0340c0f00400942442d603030384c00f183c0d02005000385030050350501100c00c41d074591208075805007005486001e43e1a081040003400c58050b03501210401803010002c00e10121080120f40544d501075601060580c0e846826640e1403240f401da0301ca010f880001080403160340b0600c403440c0045183d40d04240b607561a581e1800303034040c81c84043c2140d0481501000141781201c04111080117130200c4a040740b00c980c4030580c0c401c00495a41c04100c2d00083c0c81800c200d014441c850740300c0d0160420078100342c202a2010201c05000304060240641854900e1070540103181c8001810742c00b142d29a52940c0b5a40000d454030000d1052880e041028400481e00e4a018043c285240c03e4640c019130956075980c08200180c0750 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 126446348 1250 126445098 126445153
    0x601050603100510170a1401030602160f0609020a051005030718120305030415091e0201021c02010b10030c02030a0518030601080610080d0503040609020f22060803090102 75
    0x1040c060024091300d42c00f00c0302d03800c480c0301d489003640a03401c800e8003140807034005c014100391ba107014040d0000401d04d54a041c10740340c10800040c0c17105000c0f4045008403649410182102d250034080008000300340d0005003616100b9156032440c25641e030240060010440f1180010510510000d00d4051081c2c1c16645aa0306650745d144000d41d8071085106015a48441070f0005180042080b00b844411840d0312510400088200b01200040d11a40d50404843c2c0c2c01201c138a0f00e40000400b568800c100e20700c6014a035110380c82407501260780c041d00800340b6180182c0560115200106414000d1158003480c0c0001d8026515101c0003820468056000600030141c88581001e100f025031003c00ad41400382403814000c0200d4105003644400a1f4015032004405900c0f002c660310390943c0c05810f0f40d1b00107030710040201d210700c000d100190194020402040e0000c5045403011090140082003404143c01c0e84010040070703440d50075480c3c581c491140d0341400359000c2d4030b2109500c189810700e44c54110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 126447598 1250 126446348 126446371
    0xd02011b11122a030f0f0307030908040e04020f030c060a0c0201120501060302031f031a07050909040303020a030b030615010c03110f0d0e010309050d05090303041215050702070303020601050603 85
    0x2c090b8005070103c0c2c00180b2804803d0788450682144a80c40700d8804a071601c01c2e41c000c50406174800032082c010310030b9030100c41d4581d9005c00032601190298010381001980310501640740e50302d5500c00d81008900702c4d410b900c184040c0c00907000d01e0a021610324080f07400078120070b203490f080f80e000742ca44018080d0105d04200548510704038602c650f01c40d80380640403d543c05650781c28581d4074500745818100f00e6400c0c2120790302040000884401e007003181384600c0c0f042e46540c0da46a200603500303401a04152500440700408100815905900a000b00755007500c0400090100106243e81c5180490f115190030800602c0443d066000745145221a44649019607426000c40c1c8078a0400325a03005015280d88901d039040102c603000303143c42010502c02c0c40c080040140c961074642c0e4070328100c1c034050309210000404c4000d1b03440900031174001e40090300c0058101c00651601065000c1c0c042c0714148401d19140100d0000da00c0441c40b401207d030107500611550342001c007000f00350f5102030407050b03009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 126448848 1250 126447598 126447613
    0x906053603010207060203040c0b0408070612061e0302150f030406090501090206040f14040504080910031b0203040f0b04050612070903021210060905060d060e03040e040804080d02011b11 82
    0xc1e50240020200c1174842c010241e04ea0529180002c41d8800302e030003907034031342d00103100038040003800250f0705080342c600d80f07008000d0243c00c011410040c0403035004071064061158444e00003400b8100c02c101168400d886e00026400000302040707a602455544864034a070800100d4082211500300c0312007580580000160582e0f25400a402544280c0c031811580180308001c01400401d04a86101c051080e28244813500e0540c0d41c00785c191081c0d112851003a803905d2501902a40300b039101143d103480c1c031100c50007010342e20003000c0d540e508644581c1032135001030301003c608e0405150540c4c04a5002909460a1800000c0342046040c0010102c0082164950300080907940f0a140075000b4500c60010b424622030140c190b4040d160ba40c0c010308052410081405085e4807140119048a508420b00180d032140040b4401c0c10743c030131079212a582c9990382c01400240f0101c640104101c40f90441150b40c6141d0385402039003a00c3c0c410445003505000382c0c0e81e800307403035009138104901d011241c02515800c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 126450098 1250 126448848 126448957
    0xf020c0103230f070807020a030f1803080a030b0a0f030b0c1c110316020f0c010c0c080106060503060a090c0e0909160905061908032a0601090903090605 67
    0x40048806000003c0500248122590800c0c00a50030a01d00d01c0981100109038402030440100c3d03040140400c02110401000718403c841000301130b55000c200d03281e4444260394020b005d4002d5130341c2144120b2401030001099402e89184108590703004000c80b066645548030401280c12001200720116244c41c040c81d440802842903600c00903141d02d016440e030603d00b106107810b00412032180e0565010840401a10400081094421400346030204c0420010f1038440c80c2007070507620038003483d1f007041c1c804184c080d0003001a51003003000b0b558040e00b0582c0d803000380ac19034a14841083c04507a4010310b0b801241001b9240302d07444210317007045407609851a010402c0c01e010607409030080650b82c1d0f080c0000341c58070b10114101c0d10314088841d000d203410b0503040c68480c4180307070b10211040000850012540c094403040c02e48181214155031813581c0d01c1501a019201c0c80d0001c5000908206001c40c855000f0070940e4581d2070442c6960400b56030507003825845469881c2e19815803034402e01035142 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 126451348 1250 126450098 126450161
    0x3011706010f0b091516060c111c020c06030a1a090705030c0d0204180507030e0d0912060e060702070603050c03090a030e04020d060f030507050a0501080408130b070317070f020c0103 80
    0xd206140e9002e103000a5810007100302c0d2600700c654802c01185c000303980072210000440700314a20f2244070b0ac0300c1582060f54203919040c00700072604c0d003010b0b01104000e18003072580d0206012135400742c5e0640050100034100100d100c42102e114010607004c2c0041341101e039030345001c0d2000e00b440000c014079103510b400520041032007240c0040d0075140c6810030054010780c107014160100b89e0308802060001d41b41e540180940c0d44a01490701111800305070b500600243c1c1c2c008079054141030307058030300b10300780203400a4403503085001390000f0905000100700d582c03056004480c80391401101400705107240359000c4440036081100e542d4000d4080c0141d0320903801510034503008200c0c0031442c1002c80c1c514038000e41410401d90019218002e864810840c69810441050f4000c4e40110510794501c04403039140d80048140d04155410b44000c6040000c041c0c0000040740d079a02c2e61405008a90746244c8100e40300500e20107140b0068015000c502100c2d4000c6c5c120055119a0000c1d40341401c506401c440d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 126452598 1250 126451348 126451357
    0x603070e041506050a0b0403060504080706020a090929060a170c071401020c0a02060705031c0903080a060501020319200102070b010f0320030a0f030503011706010f0b0915 75
    0x100c52068072040610407002c18403c200c0242015901c0e18026031030b08501c3d081e28002c0c1c0c44050300d00758644c40024200301241007280c8482c0e0f4820002c5440700c0340c504008040c082c642c05041041494090101d000280202c1006020030001000784c000600300001d00201e034011b80e807550117111030504221500980c1c20040c40c450030b181e400c4683c8030340d581e0800c08944485440060340c1644100016015000d000c04c1d10821245c054400c00da48012901d0054614801e00e520207482c9441aa401ea100089036008541070f24003e40c1c0d01d286640755040c5400c203d0f165441f40d240580e0041100e8041c14404810320007501501d4144520b01d884460950209070444d01160a843d950010b0058200010444414090103038800413100150075035684402d001000740c903110065800c2030450b1455030341044881c402a40c1b14814200340029071a029015030003c3c09415240e500c2e806407034500c204001780440c100c070601d6940c6480035150543c045142e6001c00c075400c1e008803100240c51281c210410080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 126453848 1250 126452598 126452603
    0x3082712010e1002040e0a02070515070504180b09060f2701030b07020d050306011407060f0e07170c1e0307060816030209011706010306170c030d0203210603070e04 72
    0x1150078001c2007081402c01050760003e0b2001031050009001c0b255840e0149a4031510319031005a0f9a4035505010340b03000c070107005004440083c074080108155101e40a0300446448142c100100751100521609076000594003076085131a020014111f860600c11b02006282c014105a100c00c074103140c0c0342c2c10b691204150004044000004004012031070048a51004140c409006a842c1c0e4140041861001a29650401512020301447d06000307202b02c41d00070307a01c018200324604569020700003070040c8031103a61150040c0c4400203031800300803071995450300c1124007504125549208200040c070503ca000040d0308a000c0c80c40740140c504020b1000a08076503107801300a460000c010880407481c234060541018014480709a140e6048103c0c2c40499034048200c040690701c42d80120b000b400070340c0c070400c8940074400e0003c0401001191030300c25804140d059400c4000803540507a6a40f003503503850b1280c9410491390001020b0078001c09034100400505403650355596030542c41601710140c800703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 126455098 1250 126453848 126453851
    0x30c060b040216110904120807120e010902130e031c060803031e010501030908070b0702010e12070303050c04050a051201020c150a0b03060601081b0c0a0305070c0b040308271201 78
    0xb1105000300070b5480c14028500302c2e416201c5c0c5c07070260740301c241da6813010380d121003807050302c001260078a4000c4608504901d0007000400103165001440c4d4080c2001c01e005a0040690300341a00018210307001704c40c070441c1800000e518081c03410314140d4841104450420300300d5552000031850380c100b40001c6006200c03682d000310042c2c803100200c2c1e440510690040b0b05052404c072900f13000441c1d0905441842d50000300840142d901e80c0700603800344c1145442801980914080c0d4000015008094446a4040e40c0c080003540d441c090f2200e880e1155000b500d50101050342d0030451490311003541d40760440954005410140e043c030003246082c0050000f011038000c40e00130083c45045621070703000c0d5801d0450042c480d17400c00000281c9501e070064001c040003e00d5202da001980ca20f241194964054601283c1101005050040094000140840c2d940e0018100020f92a04140a990907681c220402502e49141e00b0003140c1c86681240210071244504a030101c9107989403005200c404a00000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 126456348 1250 126455098 126455137
    0xf050106080f0c0301050904031d0904080c070e2401110102030106031e0b10120b0a0312110706020c0907030b120109210c02150705030c07090f1107030c060b0402 71
    0x250603602c2e280108a0141d580d4240300400c1150342c1d5034000342e000354140c107001c22941000048030044180750b008a90300f00514a05200c100003005005103009540c0100307989240c3d80b0340e000304800040983c0c1000c8d0810320000c80150080c14403c00c035290b060141004100702444000850030780e00f00344e1104000c40da42d400c0618a401e4400c01484010601c01d03030820155a01c1000210345100d02c0d032450003002100a202100d04102d980101d0144500800071114980c3c1c9262559050350000307840c00c00900341d0468080700303071700c0007501c2d400343c07000368011f042c0e000c1c0c680741070204504004000200b09512078094030045e481e900c00c441031030349a0100201d410220382c00c0c16042c0d1800646034264240b2480c00015146a02500807000d0300d0303046458800d2494808400c034443e001c0c04802414a010004210301550350004845c0d08581c0800014046c00111001280440303041c0e4852507103400d0100054800644a50304010096100e10b0001541c0c900700b1002c50104d8014400001c0041b1f152103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 126457598 1250 126456348 126456361
    0x61b0102180603040305031306060b0c0105040203160602100213050a090b0102010506060922060306050f04061a0a1509170f1e0a0f06090206030a091a04051b03010f05010608 76
    0x315407078608040c0c80040c0b55084c1954000d000384401491007060b030040d00303940d07010440560840001800743d031048640714080d0400c42402030000b0343d0100d01ca03200300d01d40d0344402c210040d609401c555458000d007401444030419400694001c1d0822001285184000315060b6940464007028010300d0500040e1081e940001a0071500040d0480b4417812041c00f400304107a6070354101d5134442002100d0380f28241c1d661440f80c1e0141c48143c100918160030101040b00c17450711042000c3c407036070084405105e6840100c1c1c0042460f03400c0e80c81540c002c004d40005004420140070400c00407070791b03498507880c510b43e07840c0741c90b000da4801502d8296a410440354201d00c0081041134010cc910a0602d280565109603c1076a40380201c0e40020325003601c0f0b00c41e00051255903400102c0c0513401900341507503850600c855030b00030100110125540303903581100100a01400380000e1155a0000c0200300c5150219000321850041200d410b40c559200e110351580b0440c00d000b007500038100394541c035041e400c144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 126458848 1250 126457598 126457627
    0x607050c160e0112030314040305030402130504151d1e120306060409090302030708070524091e0307020406090203091e0a060207020a050303030f0a0b03070302031b061b0102 76
    0xc8907464449600c40400344103075001c00718190f045540c101c0455031681c00a241c250090310294940103015010001000f0500d07801c0070040d4030032442203822a4003901c550782c1000031a1400e940141204407040014041d2941c10b0340321015540411440401040c2150115403904640084000ca40711040c84c5403a4600020804203d80240c3d5111141c114580400402c0d50380c0034610a0000143d125002c04003414000d00803074404136040400b460303640001d07040c0141d981d0310280c0c41035a00c1c1100014104d200201a0400c1c1c040d41d17210000e002840303103c502d990a148445012950b2a020400003600142c1e00c61192400400703101101507101d15110800e5400c00000f844214030341c002c000318101d00d120001c40c00c1c40e0315541c0060016211011400450111000d40d080180c15210010500032a402180c0100f4030405003071005000b00650841419180c803e41e01c4001d405601c1581d5409030282519900410747c50094445418030030341494642d6116001c0c40c0e1550981d600040036029113251 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 126460098 1250 126458848 126458863
    0xa05030f16080a021f0e030f0a090f0f06020601120b0f07031b03050618010b04030b0c16060f0c140a23030f160801031a0721020a090e070f0f09080607050c 68
    0x4d104021b2201d0924106441e0300c20300b149184030120020310200d1190183c4298005840b0003982e84003003d45030256000180b0582c0a0036000d4803d890002410149040140c484180e00804a8103203071100e460700a8000340142240084c99104c0c2190109060903008104a40c900359034041801d08104081c0540c2c2e204400c11006038401c12130050002c040c9c000700b1503007120351020721080c641d5a1b907004091603000d03903c281c00d00c0480742510700041c0080c0b1382007852901d040e22000c000c1c4025018003540e000114549884410708180014203109024005508e40a0401018116119110504040594411510081e9200c562024003c1c1c4c4c000b0381110840c004510306143d101175046480b441108546004220340d02040b0b0300004660324840c0980400b0b0103c0c00030070705404d007000e4503020b010390818441c40f00050300c46070b00000c00c095102255402549180c407007480b199000031040b9030800d221001d200030300151440008100600304802d91080d41d0f90360351503485d0f1441200513402c1200 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 126461348 1250 126460098 126460153
    0xe01021c0f1b050d050c0304020108070c050c090a06140307030c051003020702150c120708030103060504050a1a070e061c090206070b01120312020c07050f01031d060103030f020a05030f16080a02 85
    0x1b400e1042000503604101000d410501500b8168601c4501d45440e603d01421100003a4010800c0c0043c030045401d00d420107401d07160403044150840900ca0207060395203840307200140000f440900200712a00b0007a5082d800b01070f20340707000352610b003050700460200903105280c0c05c480340b0006041048444180b2004000c81421100d180c50301e901c94031426940c0c00706000c0a0140b079607580c0414100130341001000c054079480505000102d03062409070f143c40314111103240101d070350b07007640c0f080320700e056412140c0703240408543e01125100098000e009244602c000c0740c10100030450710003ca84500341035402001a81401394900d409482c00402100d6440c1e241e1000500622031080300800100710501651400da803241100d080c4400120090002200f00d10740d84c5a07616111440000302207101410b0341e00036150f00c0840d81c130914003269226041c49002e4540c0d00300b846001e07030030814040100041c0507400b80080d426101034944003040d034040d00012001d6840035610301c0710300300c9103410080d1640307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 126462598 1250 126461348 126461371
    0xc240c0a0c0509010f140604080d020a0c06050408030d0c050f300f04020f010e0a170d080f0f130b0108062401050405010302070203010e0a14010e01021c0f1b050d05 72
    0x5242219041840c80640611401841814200602031f1114020f0364020060b070380499108000000020791110035040c01601c07070518002c008520680a94100c504460f000300086184c5000c0501c20002042c00040c154100101084441d843c81469009082d0221034805031210385080b40342c01071031400c1c0740614603500244540402c084d03040c028025550064054030036442c8480e40000403180c0060b140a420784c01904c8003008251800208100b8800406c0305040385e20314040b03408143e8070759404964180c00310f100e400000740074046204506400050b200c1000c8904011643c580d001000241c0100785c0175030040e01040307502103c83e44e6814a6034811940c82203281c0c03078580001d02c1da10a0340241c41c103240d00092082c0031506d09501c0301d40508180030684090b4800d03498404507400c1596522003003076085c400c140310403d0062003100c4080d50007950100c01c291503601000c0c00b41c40790300c005111003503071543c4030000e00c4651135840b07446040556405035207840300d0108030100c480182400c0e1500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 126463848 1250 126462598 126462601
    0x60b03010e1501021f022a0a060518030a1d0406060503060910080c010e0a09061502060906061c1a070206100b0712030203180703032606030c240c0a0c0509 68
    0x7101700030124030a83c101d081015039201c9600300240d911900b00c1e004a03180c58017401240e03124500100714035400c03d104000a1045482da00c880100148407980050601e803c01c00c0712641c1c060240034800300d2590007100042c103c4403580300040803109650300030b8010502c0042040b42d01e18194860552200001d000c041000c3d003004080340e41c5400306a80e4905100b40b04409114070385d00d0044070002400440018046507803200013441801051103502405807090501003844080045101803141801034200344501c40702c10b1400340d0901c5a21026101c10641448002d101005d201c0c0a51241c11140c0043c003640c10000500c0e010408950302c100c038520000e210280004160541640d4040f044d442c0160f00e07038982400030f00120407074040700ca0491050480020070143c001821003500d030700c038211031043c003015080c1181072400111003650f850307002503507442c14038940982540590025045d04c00400a0001e6151aa5074032021810181380d02c0328070540c2c10411120f8890b40034100036210351105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 126465098 1250 126463848 126463873
    0x16030e0f0d0f02030903070305030a0801050604120305071103010f1a030325020a0f06091d01080307020918010603050c091005010906031a10120507020c13020d060b03010e150102 78
    0x2100d8484001c1030401510303200d11a40184200140d800b0408000c1c141c64045541c1e00d00903649900c02c05002022541e0003000065500e004c20680303007100d10102d48402103a225035800ca50580c0403810454503442c444400c50050780b800d1142c42034480918400040741010a15140d040c40031700310203144030b1f5004004041355003a1602100306d0f48840b020a02401c0520351000881483c3c0a82000318100c203c64000560182d0080440c021101d503c84c28004000341c2542542048500340601c0c0442c0e13104000034001800c1100480b54002c00d070300540f80806440100141c01e45400341c1c0241c9156000051005040c9000d0800c02c1d000313100e04045407103252500002070038942c102d1145e24145680c941020a80b512010994180c0320001812540004840140a070000c5c0c0d400303c00d440c810b8541000100300034000100102c2c02e040080008011410340941040698070419540c568582c82d9600000c56026801c0994085c05490080c0e2005103004415564001e1441c7d01c860704550180305900304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 126466348 1250 126465098 126465103
    0x30607020a020d02060c0a051005090c01080c070609021512060f0102151003080f0a110a0206030a1e020a02010b03060a0c0503010312170a15060c02090115020a0b16030e0f 75
    0x1c29035419036507402207807000e00004000340205052110325015034890003080000c04100c404c80c0f0400d2400030401c5481711248560f1ba885000d0399107002c5100000460002034410001c0c10807103100707540125451400e50701045041320801024510284007041d003120520201ca425540103100381c40c540d00407100440000d617180210240d40b600c00389000e02040849200c80c41040142d41c01c40c0e05265150804405806a644014600c0b40014070043c601c00450360302041c4610030f550011714944c2903845448818009150451020001c8400002d4007811480580082c00c84080749800001e80040c80c44181030034018024100c03a0746602d8005101c08803908038007684d040d2600950140543e540702e801c02d413402002100010302100d10101000401e09440d00b080200e07000302801d44c0349090355140103588403c003105000303510400610043c01205c0c80b285d4440007201140c030444042c1c40391501c400241550580d5440704601c800301014280a4150007051035808407840181084103160f4202ca8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 126467598 1250 126466348 126466363
    0x10e07120b0c031b040e0f06040905071809140106140a0602060c180d21020706021905010b060f030a0b010509030606041a100507060c0c050d0507050102040e01030f0209010503060702 80
    0x410b4000480864026040020034030100301c290845140e840b5100c403114003841e2000c44d00c9003072050f29030000503981c0c18a409121002c0d580607009007401410050020b0148003400589404265601d078080d0118980e000c1c21640c0254030400000c04c2418a410b05046200c6005098080d040c050030800c1803550004003c1c2e408000f204046440d03120600d41402a9100035102c0c4d0b50000c0b9548201c01800001080c618a151000041d48030012440c00140d8503010a44256130268101400711403000744401410900180b040c1c000050403206040080c4094001c1110b1a42c050700100801400003020f100301d003030f1042e0900785141004840400030b030b82e50030001d101c180125111211b83c200442c103c1001c90168200400d40e001c402c01185004144d5008200203aa800b4200340002c9050b40c0500c85138081d07160084040c000081710ba07039040d10b0741e90008030304642d00d640c01c002c00240c07180440401c0340a584180c501140111340c2e0700410a4007c2d042c2c1205101c3d400840a000b000c540028404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 126468848 1250 126467598 126467611
    0x30d0519031107060501061e020714010e0402131517040b1302130501121a0103080415050c0307031106060316090b0f19061815030203061c0302010e07120b 68
    0x49003400803081c0040c0c0078003c0b1540281401d092100108070f40f50044203801d03280c10040c0c4035500040180710102d9031a41540308000e1500003201c0b0071080381d4030602200341030340f4002d4400b40ca0090f0384408964034888030b521482c046d9041008407030b039195010004a598060500d414002401c26031035843d08a00094031030100340320311082280854840c64002c504000300d048040100350b035103200700c5800e2406034034111000c3c100d0900b1030034002c0c040345025040e2034000c24040d00341820946e140742d9aa8a02c00d0341402c0c014107100b0840c001e0b40410041c03038600c1c400c0c1d84540002810010341442c0c01c0700902507920a0300b00d01c1060444a940600c49412940b000d10007080342e11400012510403501a5a180e0300314080e5a03110151303158110040781100c20303a035240b900c1c101500742141e5452095010b0f0556101c03100080e5007513244a03801950700030034018010311002013040c441c1080e6071104039040300540d4640c104502084010300203040100345003000c91092504540d1041626000180700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 126470098 1250 126468848 126468851
    0x71a060316081507020a060606120b03010e030d09080c0a12031b0e04021b15040c0b0711040903090b030403110d03270804030b01030804030c06030209010f0e0613030b06030d051903 79
    0xa0384c00b4401c1001050349038116a04001141d100c03100180080814081c907030100f42000403155250605216008441e00c0e15030182d03082148c5900500080c2920300e03810784820368188544680d1781c0c410f010444689104512307048041003800c80103000d848018000103050449034038032030a0603400203050640c009080341c0c010383e101b80f21a545505c041140d101081c2a101d14011a085103210101081c011f600803500c01c2c0348603650b00340c1d843d0030740306d800d90040540210381714404a508141d0821403502c0d07c28140800c04036203400351181a90811102900052003010143c024924280500c403924000d510f0240414000307206034002c0100400044140460303042000014003d0b404292005036600400d8082c10b560340c1e040c5002e007500113010984200c0e1a0301c03400140710b8040d01c200e1307800c141c041e128004000e8580c0010b0754a840014040780d0400700030030000107154080b514030700c041d40c03043c06440d4441c108170051518008014407002c06018080002800e0058010740b844ac10300c1c81880d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 126471348 1250 126470098 126470101
    0xa0902030f0a0501121b090c030e010b0a26120a0c21020a0803040c0801052e0509011512050c0a031a06040e0a061a0702010f032906071a0603160815 65
    0x76400c03000460380c0d00203449a483d040e59810420f42c075030000703401491a14002e00c94664cc4404202c1c081d64103110b044888480b40420514203a0003a1103488070354449804c2d603c44a021000a00066000419490004411007444c1c2c08000308800088100302c0c0d1141400384440981001030b541d5041464050450040800007078100f01a182121000d000790100a1125041100504105804c0340802c0c8020004888402e8017071034551000c1012101e0003008650981d19150001d8111804d4030704680c02c200ea5848407001046160040354000d00c5120001b607500c1d0b800c50f000804550b2060100d08031403058400014896403841d0a030740a484840441e80410b403540d06650000f845d00380e1251301019820985484840c203844007501c0002d000f030300e90b01b1300d43c40c120703800f1806c4500f800d582104041462a0b160001c8090300000a2141c0015100f24900300303035520390754016600030100f100c21400ca0000c005c200d0400344a0580d440c00b60b40c100c1040103080401c00d1740c03500b20031412048280f45110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 126472598 1250 126471348 126471383
    0x120207050a0210020a0201080c0a020a02040902010314150a0506041d090f07030b0a0c0513090b0112050c0901030b090705090d020a0909031206051206060d020f0a0902030f0a050112 79
    0x18a5103120b40c010b10a21807189842d001a4680001020a902240301d40f00060503021145084400c0300c601da901500c004002913003004014110740c1e0003030741056070b900c4a40e9526904110540d020f52024114800319031810001c102070144142c211a014440905c0208a01406108450042485602a0307a03842d030b115108580360040b2200c21019501c46c0e040000103112218444074054004000300b4820340301c07040d030259160300c03c00c1031000000c03464030000c04c43c0c01c6041e0720000c4000c105240207009144c03407000c1801030350000d9501120040002411b50055030305807141403101d12041e03908040728504100090034034045c0515403401210909190411507891400d4400074000950b0100048522410028090465070320a00321251803e20045001d18000c001207503007103909402001250b40b210180712160000090807030300f00c1030070301540c8080d0350345800040c094107075900010384030300e8000c03140284024040c05c8090100d14080c018410110080c0b039130000f039904402011548071141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 126473848 1250 126472598 126472603
    0x5010c06110c06040f02030106051230070507080609011e0207030e0405040b060406060e030d050d02070204022205011d0f030a0b0a090b0606130e1306060f030201080a0b0112020705 79
    0xc4001007841c003c82d41007200708040f4010400030300b4003e400070418140c5820a03c00c03101c1b8000c855041710750085800300140e403c843c80d20b4528504100c82036a503500300c0c504e44c1a030740d0400c003800c5403503400c039000502c40380c40c3c10820a54060755160080c44121403101448806450440e040304085800207084814140200200030045c000500708024900d06400d0401d49808203542c0588201e00740000011003504c25012941c03022001005030500390b82030070007580e56520410900307000c65024064040503907138601c09080300c1441c80c4c1c07003403a1111013802d084040040300c1c0c103c181400001520014101c00748000404030040036240f00c0007001e0940c001a1030040e0b03508004061207090b40070800302c4000c90700401c601c1c9200d40203401c00b60300c490003003000034020780806895841e181d481c00c00941e00702c10012a0011450362110010031907a481c1c107010799480b600080c00d051780540e02003045507403202201d0782c400040d0404102a80414000a207400321401010342c3c0c442d0003050080911000f0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 126475098 1250 126473848 126473857
    0x610062a12050301150c03020c04180c060302030106090f0b07140a060f06080d03090b06010c020a0906031a0a02120613060803040906050312070b060d141509010f0605010c0611 77
    0x14000502229144030041c042d0b4002d00a8620560080349001780c403901a4440c3c81915500d5009840109402000e000c010101c1c040d018110000158016021400c2a846134010300143e5401690380d606016010300080c00960240c400200103c108010207805039064441180d03203d01e850100181c0179003039601d00484c030031020f00b00510b4510800c680600a51143c0100d542620a81e0b42e181d020031810b404640ca107540c0900003c0003000020001c0d031240c070000107028030040543c80980d4446d0440806c46159401c02c681612400c1500010525800d0b00302e6032000540000750301c0c00c180405450726000000c0c0013075000303d44680f0080324000103a08003002524902c01141e44899581e02100c024000741e00c00c21b0701901540f0b0045521800d424100c0c1c1c1d805404c0014618161615400d0040c120034981080d28001149038045465030700601100b00c4c46821202ca0a1460400e4010301e0f00f16240800344132405441c001c0c080000343d8204680e01c0c85950041e1001402c20318010202c0d14074450f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 126476348 1250 126475098 126475103
    0x71d01030f1b0c0204271407030803090106260a060b030708030f04031104090f0305090411070f02090c0301150804020f0402040b03010e0c0313020f010c02040606110610062a 76
    0xc0b100050000154041c91000b8214002c0300c003030103a50104506404400c107403803030300c0d000702c0d003400c0720007020442209000d202006400304644009603281c0b980f2505800c25a4003500594441e001084911304000000c40038241502e01d140703d84200e015200d030f446885c03460017096680c413801c0c1e03031a050341e05015900c01064444142c0e5580c42840c422811641e1180c001200c0b04003400b4400d2495080502c156101c050348600c18400410503520180c420390420445246e0254441d90800c0000c400030015002c02c0b485400b03200000b2080e0307c100401154002c02c00860000c3c14801000010b60084c41d00100c051141449041178503940049946a018940100e80041c00042c0025110380b00c1030046048600048180869071501c1c44803041c0ca20003521110051044e40c0c20501c0946000564503481030414101038400036075641c0840c0a45c2c0c81c0754046000304c1c0c1d140c0101107071024140080c2d540b104100c5e480c2d00500c0e0a041000c5d040c04a0fa00c1080001d44284441d004c00583c0300c00120035164 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 126477598 1250 126476348 126476381
    0x12130302161d01090e071206060f03060203090f010507091707170303060901060302040605090907110601150e0109030c03030c020604030b0a051005040902030c09060301020403210305071d01030f 85
    0x94640c02e800040341c0c020316a000181559800004003a4002d20030103004040b060007810001c0e10382404c00c0c0e5006101c46040d6820380c1c2d212030000e031070072210a03884000d5114400140c0c40c0d00d010351699003400f00c0c17802800700300e906100400c00b003603034080c1003101510600e0807a421840d542c0c0c007049290036441d400604104080085c402004100040034610924048a02840d035a80b982400c409902461181b0070116406219164041c034207040c81c664040180c0c94000e0306102406000c0d07103007800031381c0300d20a81c2100c0c06403280d110754003000500054000b0300f410840b80e451641e40107080c800078032000d000c22825603040402c40d51107004030340041d60010302400c079a041100d0b801d0001c010036258038001c00030060b80003405040500400e1401e64004000d4003c040e0004240104c3d60001403003250706542c01c001c0840060402d041101c0c0d80c011103a69400551454200070303080790350160502040c004881010910520340450318a503080c1c081c600071400c800c504490b81c0280c803850213418041c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 126478848 1250 126477598 126477643
    0xf0304091d1b21120702030c0303160803060d1a070219020a0506071e0c140a03030203120714040e060a0e040f060902030c04050c0316030203061e031006060809010e0312130302 77
    0x10910300075181490084040c2c0303568512343c0e0201907480c0305942010101c0c4000e09401d40c003088926000e991702060103021004854026a5201d0308440d04c0c1400d60082c42401c81489a01503042103411800400e90815000c24002500050000055441441d102d100d0000342c04041005d4560a44100c40b100b180b0002d0a00e100e1410303139070074802802a4240007161440907012440d141002d00112034241c0c0145203003138555204a04540e00092552040c0b0402e409200040c128910040c8020f00e9080480402d0781004410000c2000c6268403a00d082032240c410700c40410f1031082c0304030006a01000024000c000c1c0e1001c80c4c00d101e95516260b900510f454100310918003d01e00842c8940c1c541400f502c0c5010a1101c26012400b003540d58a41014004103c501c4401343c16910140156008003200c2942d01d0210204007030f00c0d42e40d040040014070030028400c0e140c0d000d00500407841d040001442c1044001040600504401003003081d2007000919a58117040c000d00800d44060141107a68659 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 126480098 1250 126478848 126478873
    0x709090e01180506040b07140301090e07050303030a0204140a0506032a163c03110d1e0503010b07080318060103031e092103020f0304091d1b21 63
    0x100d0390b003142c0c113a551401b0480040c2902d88213131101c010403104804410304590030700c90710600400703104aa400040c0301e10301c004645507800b080918860440c202000d81d80b1414500c80001e45052507907554003d00c0428401d001c1c50345c903041603d0780805881c2c0d0f1486c15060b880c00c0208090340c402402c003500c41c030000f44076800382240459000c419024042140c801400e514020070440e12691150f00d0b100000c5290519015900b203000c030001c0d0103841e1143c25003101c1c2d50003604006450a4090105480d022100079600c1d41d44a02d50650b8601c1c02e00605541c94651851888d10840f0401040703201c0000005101c8110f4440c0821412031110880351550b07101c5c078010781652420680441c41c014520a007201c00d13481a0100016901d4070a2040010301311504501804d104078074048003540589540d0b050404400c00c041c2009250349000415601005105040c0081c10400030b108180c0010413403500381c40c00b04001c641120000da480c445c01000501c2da811103010001e812203028000d08005660 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 126481348 1250 126480098 126480103
    0x312050909010b07210210140610050c030906090103020c010c0c140d050d050907050d050c010f0806030d140405040603060b040f0507020a030c0204090b0f0403090603050709090e011805 81
    0x55591060390919400c1c0d0f256000750f40c043c051114014001650040c049540800c0301c002100d100304540102e079628078400c3c1000003a62185072004104541d0b030000c1180d54503022140000307402c09400d00c2072810003010403041d224071800704042c0c021100002e51142c207034840e604980034018010000c0005072245100100b00e0005030000303542030901e04c0b002c0b1110304400f140c00c500c0340c00b5985407580742030300800d0500c010b0300300101455041e0082d0080040c898440a01040c2d00034840c8004c0c00c00501c600002401164110700c00342c080241800400c207068900141501c5044094141329220441e41203d250191107103402c07260b04181440c3d400401c101c080d4100404000c4111803c0c001d10780c541c1e415100b168001c50b06900164403200f90f503000320b8001d140e2100401c4c000f03040410f08109507152040d90041c281d9012103125500c40400051540c00b03201140544450300e01404039044c01e4400405901c02c502405000d0341d516030010798117881c2540103081042c820480c415030145036080064 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 126482598 1250 126481348 126481357
    0xf011b06090218090c01030605041a0114040b0705030c010e0106030c050f131508100b010c03080903070b0f0406050a093c080403030908070506030c1b06040501050901110c07031b031205 81
    0x46c0441d0906501040c0761502c0e00038110074a554032000804c1070020001120040d59808524241d0002000041a480607000051502c10b0241005540c0c1d1000d04802ca400c45602482000150b45029018400180769104010886908549042602100794000f1300035503024505030404c075103001008801107031154501002c40b200710050701c100c0481041c1081c1611000c40040c0d0014204921400000b8003400d0100e4000109a04990a01c0c9550b07440f02c04250060f91220b40040100040208006a502444c3d40c00000840240074840d0555aa40031400003101d24a902d04019200e04c003006410704090260040d0386c00c00c0308006d040a051400b10b0f5482400181c00082004a01290301c3c000000c41c4070445001810241c80e42e0b40d000f03041d0b289500038000000200f12042d00d100d43c046403c200b124000c60040d00001200d04040240034212001c05010404401082c400e00480940118090b01200d41040d2130071200c41d04506031a404861541005008800601d64007440e03a60050150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 126483848 1250 126482598 126482623
    0x60607050f010f150807080d1b080a0203120a02160305030a0212010b070c06020f030406120603020907120f09020f060904060b030109050f0c090d02010e01020313090b0f011b0609021809 81
    0x13584580d1600c250a0b1240034078024902598080c0100c492020712400c07030394500000e00c902620010031155650501640250402001a403021034003420241a415110760028980f032403c52900c1003210169100c22440b1002a007801000b00c00142427285580441d103448036031161500f159a1595a8499241c00c58441a40c0604000f900499414000942c07580c0d2504050005c609203842d01004442003180c92040103080c680756400040181c0700c4000040c0a9100360300c46540662244240f0411a203a0782a810b0b2005d05004207000540c0711440c0442c07445030700760b5245541d01030301c90116010f440349601044074450000b0000560004952201d03020302801c0b24030301d00c01c0d1a695020b13034180c0603003030245a011502070440b400542c098090f1040c01e50040c01524103003003034901d02c0a41c4105aa00440e031460700d40c0211039032031030302c950750781e8070780c1000d0a010701c0c020400308181c0c100e001d050710001c0000707940d042144150354800340d08085c0c0031100c1d60b0741c01c01441c0074a04540c036010700c1c1454 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 126485098 1250 126483848 126483881
    0x20604151d03251a04080d0614040e06101202030a0b01120c060206010501080f1f0f0807050307061e0302070605240307030503251b1d0609060607050f010f 68
    0x31a40c0c80c0001c482d616000d541c104203020700c044c41e13001d100300c6018405442200d001104112110008000c0e009a80040142007040b8980d841004103210903902c6011526455811920400012407203600c1250155150b03075100500700e800a1001c2443c00414010103000e0144442c00000e071040002040856584100001070340c260f07640130f05903610706003800703001d022442c400f0018101c1104602c003e03034480c51210880303003002004103103003e0002c4690494171400b24080405c0c0703c0b12400b0810074000300026801080d04501e01030000f07101c0e448295041080100d0784108a803828400d4056421a42d08001b003004681000d8400060b01c01640c428482d01584a00300100180740100302981113940040103140b42070569902125646c400c0c101800324013880e030580c103010820780d100b10103060203400315000e4071134148401c0d00f4950f409150007404083c014010083e04e6250111259040180ad4441c540c039a00709240c03150a00c100c0740d0440d00d0325840d00401213140c0d03055030409030040724913052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 126486348 1250 126485098 126485137
    0x106090806061f03180503030703110910050c0f030a0e0a050d0512090a12080d1401030c060e040b04020d090201080105030a02030715050c0f060f010f06020604151d03 73
    0xa9201c22080764a55030004044100e01c460401040001e106420603103000105485280c5074605841c144807070a8441d031380040108075005815200e001481c241e40b035034070350a115800c00040c0340c44800c1300d205810800081244030000004008441c4280c1080040d01e44460007800001e144c4100381541d00c0c46201070020000d800d051010813400426000400f5105520702800c2d0090305a0001c00340d00d030004081880000c2c079624900250b0411803060f04035507030b030304249207c0b00700362540030300b20383c079558000c41c01040000c14081850302151514249182c0e11704c0b0207070000e0300801d0311800041c1c10500004420300000f030701e540034080d900c0c03003600e525955907240c000703041d42e4460303c0c000203405034803100d4148002001c00a85140d40941ca00d0043d1821030f070301840a00300003950700d403da11a8040414041c0030210f180b03805002d00712280402c12128940708000390b403520060001f400303402e0070000c56000d1004a8020445484400c11410b02c03640c50312380b40345d640754401c040c2220302d00b00c14403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 126487598 1250 126486348 126486359
    0xa0c0810060506030906060d02030c0604061205070f02250909030e010f050906090603090a021c030228080a020f031c0b090f0601050a030b0d030c05100c0210090201050c0f06010609 79
    0x1002d0b07034002c03030405c8000c00d11980d030001071001d2103180400a0f0f0781840f5241d050213103a5910300050003e80701581d030790703060b0000b040b11032016601c0c09481041440321070501d0f07442681e80014510048a035501000d01100303144400701603070100c250805180c2c18202030f6440c05058102060341c031010f000781d071103400d8400450700c221103074010b510386564400820002d0384528508039020315005040c0009444a4400550000b102c2c1c001010500c064500a844030105154050000711102ca69400411a8045016041492624200b50018410400480c2085445101708641c4589a42a100b22603035102980c0c0e603500d0301c0c2c1c6640004200103040551451250034000f140501440100b01044a1614ad40c0015070b0960010b500e205c04155851100017000d40d5141091074140b80243c403801c2c40d507081403c001e414070211080d4404d0f0705007418105601c09500042c2c0d400301d1034030b40d47c0024202d01d103440100c5081c0b0420034034140620070880c0d4101600c40114501c3d048415540340c0b42080366980 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 126488848 1250 126487598 126487609
    0x6031a0907050a050d17041710050606030a0f09020a24021c0804050a0f0f020a0e040c1a0403050f0303101d130c170d0e010e0915030a0c08100605 64
    0x28000c41d90480341e00d05040016007001403194001a01c100d06503420000c074500d651403103400550100c807103002300310b507010348040c2c3c02d0244082090b90000c00340a44c5c80c0c1440416268440a420140d54554640c1c0918568100e9440350240755401401c2c480c250360f40d07d0407501c603100401c4414903140100c0500781420760001030f0f0501201800c81c40c9000b094240007054030112001002a00d03c0d0007103c0b507a0000903d00726981030420310560545a0201c040d0040c401c9010b829085203400d010703501c1c00e001c041207030324081d4000c03110203050b14441c0313803588006291513008e1a44010c10510541441c40491a404006988507040807018100c4050352a101310311100c00c42003416801c2004200841c801884055802849a01070400307400d41641c2c9080c0c1c3c140c00003c404003220507810009200a220364411640c2d11a4042440c1030181c0c3d9030b54000150485030040c0c022004000344450040e4a600c00740440180250854115400d450b6281491925003584c420f0441c0746520304440429245000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 126490098 1250 126488848 126488863
    0x10c02010909051b03040f1106030103031d21010203010302031902060403080f0405150c060c0c0c010c0f05010e0d0f020114010e1902030a090309080a020609011b0606031a09 76
    0x595925185600c0c100080b80104070283c4444084004c01000c4098480390303070002d42c091845010052512126070500349442d119050794603124003410001000481d0340b04c11071017a24030901480f203010b104d0314000502d0140b0810f88180c6400c502c540b15512001c070650103141203d009a050305c4600c1780c2108189282c49001c1030007517000c5d00c2484184040780340000030700a21000b40070030324901504c0f440001c0aa000018180d40040c00c005000c0801c51070910403140c014072103480250030204140f01745510784110b1200c0504001c802d440c00380c2440403c00c1d0000440d9041402000440d1590120907110107084168802141d02844469920b520520421452804e00c003070302c1c003040e404e000300302c1030701d26001d86481d080d0804c0001c03d00074100280300850055032908400554269580386c00b408008040d440041982c100d20401005601d550080310062203091900c150720301030410200c0000c84007994003a1034546400c0c008002c0100d400000380c001c41c600841020555a441e15280e0369014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 126491348 1250 126490098 126490103
    0x17010e010509030703050a020106050307150f0306081b0303090619090e061e30070902040f0308071a0703020901080a18030e041410090b010206040512070c12061a010c 73
    0xf013008040e011a20a00c003a043d9180c141c80040f075550395039130000742f0f01a43c44e003150f229411400000342c0e0035508000c48144400490070b05004041c584000341d41c4410070030700907a80c0040c0f0101d51400946d428801c8401d08980140916107034601e01280000c40c2d0785540480c00404e08020300402d90306030050290388582401004601804801221100145e0403d0b08040d08050f10008070f0f0b108095010411139035800d540310701804041c8405103c0c6c58030071698002183e0720b01c1044140508080780d400341042e6500640c1007691a101850318004e140c003840502c0e1001c03482c02c01403011300f40d4180c008000c202c00036690680c2c5074541d4201c9a048803203181003680500701c002c0510300028082c0c0811000c0b548000c02c00034401640001140f541003040f1161b0f030007000700701018813010000d0310400031000000c6c8001c0c0628a01990313550b03511503031030355460013840002c5040341c2080144a800742c05000000c030500041c0c905850988007403d01541c2c8619030019054005405500c03482c040e050164 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 126492598 1250 126491348 126491353
    0x4150e060a030c0315020715090209061801030b0705070f0b0103020901091107030818070603051006080f070804050a08190e03010c120504210207030302070e010e0610020a02040617010e010509 84
    0x1c3c80c45d03031a20b164403d80c0002000580e0248080000f14129a4400018031200301010174410001c0c81001170001005205070302c6406004101e071314510791501d8080c192607101d00194035075225120161618019134000600e0401250f1002c0d080180c04207000e81240d109840400b216605c07841214181c0c0d181c07030300c410749912040c00720f640441c0c400c12295410412160728800800a588034450034041140c2009000c03940b204184003461014035081030080416141510742030511000041801c2805402c2a04000c0d800c000700d01402020700281e604154030ac5605960380c048034030f40d04003600031030400c1400b00b0f1090042d40c490703040c1030248194070400d50781da511804182c4441d110003000083d0007903405035070010f03072013070f001d000341e070900184074810380041605c103145203002450021150442d0781050743da200108a00c1000c08007068100e00211130912002803000d2089241812004c4080d600a05040f8000340c10307c0001c0d032254101070824028003106960b081d40600340d40c015203e010495 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 126493848 1250 126492598 126492623
    0x2707030b100507020a09050c0405010809060903070321060306050f090c030601180e0304121502180d030521090d020106030c050f0607211d090703021804150e060a03 72
    0x19118800815903c0c2c4010806456581c80c0c20201c2d0440d03d0440d90759002c2c440004091200f5070700081e0031540b000d80440184180e10708072441e95200d01640d0002002c0c000f040228440690a00b0340c1741031100316452080100e95580e0074042d02500003a200f80030071500d81c03008105420004165007050b11800350090089901e001185017039148060005103111b596180c1c501b82c2c035103003480100000c1040401c01010142241042e03411078221120140c0e9291040106200d00d01040b620a41030f4102140c0141d0184041d0409503914410199440d0f1404d2201810301100c04441c6005402136007103108039400301c40c11200a81c00c03240d0f01d01004d0800710705008208158a800312402404a50140049013840856525610b41d1002e082401c100c102d4001c2440003d40d90015003c000034008100c213a0001c0c0200300030811511016050400b019000581c0200c070310100c02400365003210140003004482100c00d00001e22140c280911500d060703240c00400c500d407400d90b4048007666003049031000761 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 126495098 1250 126493848 126493879
    0xf0c010f0e012003042403060609120f0212010e0106030c06050f0405100207030803070305010603180206070209091c05070204140c03011205070f061206050303030118020309010b2707030b 82
    0x300035074200001441c8420071000c580c006e5500204203800620402d210980e00d25010050117580c1290804401c01c01020020881c0c8600b01002e501e03115086031140d10248000d00102c2e0304000a10f010300c03203541c280400e103100001d0552084049900031300400300303017075120082105d0620401c10300221400c400d000601092508041030b02808030603004641c0e00c075603203a40b0841540c03c1102d04d540800d40e40c0c0d00400c000d0b0340500030303641070000d162000e005410840e40080c0b014021803101900400c0440000b41c501141040903012413850350b150210350988040c001000c83d03215903c124051410600c2644814070240c0d12140a12000707100e0341d00f9a82000f04c109950b4a45203016035141c807811400041c01c2d404001c8040c040c0800d5074400c0c070510080300200341502c0e184c3d80403170f01a41c004c2004108401041c0c0301400900c809980160b03613a21510035860140c00f5054425030300c03509650300c8030181140c60003090650160111001c02ca5510f601c0c0c01e4080b00c0c00d100c5003a40052608441122 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 126496348 1250 126495098 126495137
    0x2061315020c01050c07060311120702100f020415120905030c010e0f0601050a170102070804180c0804110103150b0c060906090d02030405010f020f0a03032f0706020307110f0c010f0e01 81
    0x752505240d92750306004e40301c024440c0b49c85082d140c1002581040300c55259149040c000e200005070340d001e06503d00391818150b90f11904007180c5120810150034800c042d01c4c0501d4100408003600001260b898040d00c000450092110781b0700c4c0ca1491060796040c0203120008103e650407030380300a03c1c500c4c2d154988400f440c0b42c0310992412002556082007160009850f44c030103003011b40468019060025100c0e240d88044440020040c810300c0030110402c0005140c840c071001c8400d800317183c046214040b0706104040000c03242c10000081001041c90301d8180d60028030b481c40f50001100701d8280c2e885915900da21402c3d02d4260400682040105110701d5004000316064810144100d900c1c180150301c1c498100305d2103420440010f62100001c0506685030840140c07840c84104041c15500d103106922241c80c4500040100313210340100000342140d0040991a4014a6800a03101d00d11000c44c0416220420802c0c0c903804036100030ac0c0c0c2201d943c490010386023212010b84030002c496a44004204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 126497598 1250 126496348 126496361
    0xb0a18090605183607080c0f0315011401050c12030403081803090f0f04051602061005030601090c0c0b04030305040203060f01030206070f06110a05030f1f0e0402061315020c01050c070603 82
    0x190284001c2c500141541005c10500000302210006481840020710800c03c41200c40300c0468801c0d406500c0c909014810022158112110304141d00c8c4081e43c50350040c1e40c0c0d801240d4103004540580c6c400300043c0950781e802140b1032071080c1e8964145550701e042d0a00d00000400ca80c075034551040c0301c03099450828080218008030002c00c490040c41c0c02500041c1600c20480741614040340b074101440c50700d6010048240c001c09008120b00403c0d0500c0d020070b540780814410014140e440d4603404800900400ca0386250780d4103c08449000e03d8281000f9014007800e1740c00b2402440b4040010340b140c902400a103043c0da900030811807500c91981c9840d004051000750a40c0c034283e80d00c05e22008a009400180284105603c90326100d241c414507040d203003940100031b0022641c2510800310204408840041a1085131340100d0713840c1c6440c00450104d000d2402c0c81150100019000300395014030031004d240d60b0b12150f00710340200c40a40011520740c01074103441c00c1c041e03008140520000c0c4c060340100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 126498848 1250 126497598 126497671
    0x708030c030a060306060605181f230a020307050d1704060e010e03180405090708061f050a0f080c0d0b06040902010203070203010f052706010b0a1809060518 69
    0x10a0f16602d9032242070032a902d0382c0c090800300d040027640b55184c80c2003440c081882c00301110005a589082011201031941c203540300400c11130801c0d049500c0320350400e007040c11000c2c01c1e40c80315115040310f007002c0d6883d84403030000d44041c4600645d0030440c5115070802420f642ca281c059101e66203d65403170030060421448405025501c40110810044040014000140807080c1d404000c0e00b4982c03c0c001115809032906500c1c4d0424801802002c0f000264a0341001a26050b00048a070700010b041c07410754950400c9911003040d40e8002002481d44030564291132007101500d5038040d03da4100b082e51000c2c240300411413040e210005190786856804185074600600589280801d80c3d0300117402c444a00d041640035590301e10a01c000814980c500c400c844000a60590041c0c00300f42020f80d48150510402c14025000602c405180e8803e01d003800030690300d5041c1980403030700d43c541c1d4000f0b080140a224000e40629903e102081c45410b81325000700020307080c8203c0b0301000703801c00448444e00b0090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 126500098 1250 126498848 126498851
    0x50d090e22111206190510170313080a0606270c0201090f0b04050d0f080402101b051513150e07030c091e0e0d0e0a05040207030302130b0708030c030a 66
    0x1031111500c0303d400700018100c04070060802840c00c40034509a40d00c0d8002c2e46010285172008004210f1541c20416050302e21122003581201010015540356214500310404000149040000d41c10000201c1c1c001d620311450f020301149448214494209841441052038400c800401021400c00e03540117100729504c500c000f181e100c0049e240c43d00501d0003506c00f128510262020001805014070640e1803815451402003c0e04036032000040c4004805030000c1d1186851804c91051180500862850341310034084040c1c038500705081c0070703440e980c003000101c407040c2c60704c0000f81d020b04051503944c1c02e0503881240502450000030031800104501394601c1100d1107407a4011011030b0041801c030000f408400c0000c6044d0441d45001c401344111080b040410701e01f00700c80864421750120b0880c00e030500038a880b004038101e500002d00c0c401156808550010320003e10341041c1039041c1c0041241d0065204801c1609645000910852081c1200a02550028004102c0c20700c0b00600860700060400380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 126501348 1250 126500098 126500123
    0x60504050d0302210711012a05030906010e06030309130902033007080409180c0503060601170a1d0d021504020a03080c01020c030f0c010b0a050901120302010216050d090e22 76
    0x840600b181c1c02030000e80118101c680c080c40d03c8d5422880841010812450143d00f1400c2800c03c2c91350b41d0f80c041c001c12540880c4100054540d841c10003d540713000740020040c1501030707807580d40345000340420312007640030b40685c44000344e1b00104018004c00c01030a40d490700000765100900d6101039000050110782d41c030400c00c000502c260013030203000d4000f880310b0301c00c0e100740c46240340225520001cbe0748954043c0d00b022080103240d81c3c2003541018100000d0a961440f607548011210050805070007410340c0c042a01482e00411400042e1a0028034807074080b1800340c9000150001c102c03200302e600940c4142d81000602c002078600c0040c00c8410f0090001504025400c0800c03415504108600d000d417070004034510484240901422100d0b1005562448600e810f01d030110740c80d101c0c14002ca858107200c840d009401c0603c00d604952203102d81d001402c40c1540540783c041d45594a41c01e414000804000000c120817030398040c1d19000302080c2d03c5000c001010741901e02ca9030510310380b060b00c1c15401c500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 126502598 1250 126501348 126501377
    0x6061706010225030b0c03091b01050412060207060504031d04050405120a14040303020d030b0904020f010e0112090b0f01060219060c1101020a0f08130804090b060412060504050d03022107 82
    0x149400d00907042070103116224072380010700e203103401c6ea0300891110b0350000501094a03a45c200d0225000c0e2901004403100880c601c0c2046001b0b440b40b450700624440c03411041101341030340a5140c1401e0070b440c1603c040302c5003081c0200015a0700c2980e002c1c016030404071080c0c01c2c50300300c08001d00d440a0340d03041c040900c41014107209070070742181d031007600560401d60b243c14020380d1610414005140448a160990415070046240400c040325044e0600c0313180404803040f42c1c044c1c69107486d41608003030240144406407070600c0444034140d451014110b81d24001040746030020400342144003050a0b018100900360b160742e0003525141a02e5000d2101001c595008100c00380000c0c802c0d8034054035900228888040000c1c40c2c0072004001003928140300c5c0307400c03000440103004c44080b07803a1090042030000507100091070328899940010090713910800906d080081640015200701c1c00f50054500254420006070281d01c56915465015009903000102d80c041e081c100c0368000711249009003648580c032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 126503848 1250 126502598 126502613
    0x306040905030c0312060a1401031109040c0c0212011808090d02040509061006050f2b020720010801030f0f030e0a0f0e01231c02030109060606170601022503 69
    0xf200403001500300140c0c03000038030000810160410b00c02e60b80060201d00d444000c2e03110100d1f5048050405454805e0004505000c1e01a0b07441000c0c000c1080149031050354015108105580c4120702510314040c00f142d6204040c82403850404102c0f80d4990201502da8908500d54003464085030b1080100c00000d0168a0f40d1080718490049400103041e241440d90710078892610a60101041203c01c010800da81d034100c1043e2100040d81601d8001e2900c6175246c20300c0c10707117850710300c4240c144e20115005007400824042c450000ca02661155004c2c400302c0011030310114240800340110307504000783c00014000902100303040f80285011406003081c04000f401211031030b1b003c4100b0f0b031051309060040c2c00680c40300500510310010392211b100c00f030031b40000305805220b4295206424540010000e62402c0c0c3c409070303c0c5503000b0001c2014000d64981000200303241d004080c0062402e5001d40c1c850045030f0007007401076030705030014030410042424000c0d4002e400c80840d0b1100840140000008002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 126505098 1250 126503848 126503857
    0x914161404030501050c0d15050f0d030e090a0903120203070f0f020321160206191d03130905160c0b15060c0d140307172e06020120030a02030604090503 67
    0x28031b25066620f185264031039068a00101403241403042d01c400410603960380140d030207168613041c4d0342854040818101501c5c1914001d1080c0c2e000300d43c0c0020000404c14036404600d6461080d03c0d210480c0311502d003600d00300e00085510f41c01240d1400600c1d2419030249501c101007421500c1241d10300312048580c101810084061851606481e1045c40200e541800e4031240082503480103000c076140042044bc2816140388070208629520503070b40a0f25000c140090f00340c102050100d9541d0310a282916107040440e01c1100c06003403524021903100c65440c041d0b0400344400b41d0f920b90300704440b921001e138028806031041c0b455105d10760341a0550303120280600450003411020300b44181038504007601c03980049910b1507007d001081001031103900800d03050354285407011000e00c26a02c084109101c1030000214074070035100303905030b0914010307194865026904a580244200101e40e541988014030040f03064070390245c20310000b030104c2c00a80c051503001800402c0401c224005d0b844240c00c41d0702 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 126506348 1250 126505098 126505111
    0x1030201050310080a051c0507020109030206030a060302030f0c091006080a050a060f09020304020406050105122202061204031202031603020706061d04030305011d0403181707091416140403050105 86
    0x201c421040110300c000c4800c02c45c100d215041c42342c500904c0d42d00090000b400d0b03000080c842d4001201040c407503801a030182004d55070180c1101c0912034805111a44c2d0300f80c90550b00e20034100140041c50508400c1040004c031811516000e243c0c2c3c5407054101c0246c00300414a0390b4603951074a00198070840200014004d0500a5006a481c1481d006100030b40c2c000d90005030620030100a1003813003c038562500703a44059056842e003a213001e00b46169014080030b44000c1d50100c2d011950309140f00013560b850707014030b21076282c00300c00c505c1a211540a90204640445100c000003e000c2c0005000e0b4005140e142d00c1400002030003500c2c0d01c0080321010384100c4801001d0b002c80304001c00c168062042c40e001d0b0440e280001000e0602d0410001510340060004042000e810340c40913000845a035444040d0038071031484011124a0080982c0e1100742d8400c40d042c003418102c50740d0300b1411900e511030103180d51007104d408581e03900c0c81c20750307103140100c01001e00d8010400001001c14000c1c883d4501450 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 126507598 1250 126506348 126506353
    0x221010902071e0305090603151801180c020706030b0109030b01090606020f160311060d060603020c010c05040e07080702030c0105090d0e030d0207051228020301050f04030801030201050310080a05 86
    0x192030f401d010829400d4408501c0300c902002101001107030308a801d0303e1800c1000c0700c14580d03a5503903030b000d8211401200d9920390001001540c400c03c0c400d1456105050303903c49854074200c840070b512034109650350000c0480140e048a5014800b45110390007441071002c042c10f050412039526641e11019010984c00f800520740d9070301d003d0207203903414001d05040300c00000c002c0110080d4911500d10b80d400034400200180c0b071080c91a02141c58110a5481c5500003550400c08144d56440c0940030f588502109540d552808100f61104c1340030700261415140b1801100680c0c0c0c1e100c100a441000c0003510050952105002c0c91032141424041c0302d11540c00300c406400800048074001d480701883e081024403e42040940f1041240d0005a4008445080340c8407050002040d06503400c10390043ea00352995019400c1103841e01d0a42d84840c28000d00c250001c101c1031362564540113034180c2c250740050000d001800100055071141c0b02079504480d10391400314044c2d60321345503d40b509140d400102c0f01034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 126508848 1250 126507598 126507607
    0xf1f020609060408030f070c08070b010f090207050a02040f0e0604050f0705040e1c1808060103110603040201091205012901080109020c030d0e030d050c030109060f0302090601030221010902 83
    0x155814400d054010300a04001e054a05144d0380350703c03450000800c2022000020300005181502c05c2c07014000440d00314140320365402080c00d1603d2162002d000b44450055103540010b1040c546100311880150002e000d86040c0419070708200c054980c0b140c0d140c0a803030312812011888041440854041e52254004100c8540c801310b4081c1400d03d0350307001c188074070325100e204c1903c3ca0b0041900c601101c0c42d074680c005910541d00b815a0421100e0720114014114000041480c3c0d0000031600e050300d0084103280c1e448801c10040009034441210020300090700480100310142c1e003020340c9000580709a00214482000082030700704a0307008507021045d1000103901210950b0400c0805000d00103a2400394508002000026a01d12410f0b00285890740e80303002c02c0c0074404080c01074810f80d9500503030a00017410040c601030400e070000e00850b07800615160300001c07415414441c510883c0d07030250001d00c6030780d500c83c010f40083d00105209142d401000d2200b800480a002d4414064a038030310005884 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 126510098 1250 126508848 126508909
    0x9050402032d060708040b04110112110406031104030c03030c030e13051f030b0115030e01050106050310081b04050a0b0307060210060e04020607080307050d1104170c1e0f 75
    0x820101070301c00000c2c81030110900c000308040405d1340398000d82100a812001c030403900102d8070560f00081841e0700c0e40c4cd061400d076440c482040148200c42c125a414042040890822051403140c0e11008110000c4a5000c00001b4000c05107a4020750180c1002c0c02c030a000d280216046080c00c00b00c1540700c1342d035082000303000c0b05450020303080e40c0b0030700e141c00807001d045984006000406001c1c5203900a030040ca00800c00e4070039004800c0e0450900c009100700e503500e01003c0c1090700191060240140416004900311200060454901c84900c500c0d07042044260103200080002a200e43d1256483d140c418059841c00c01c548401403402d130b40242400d21000001c04e0880b11540c2002081110880511000d42c0c1c0310b6003505c00382500a51502d40e2030300d900c01c0a40d0310348560250481503c0c2424020191411060042e204907448000d0310403940b039000095648540746001c000c2d5108140804e8840341c000118004402c0c0d07800035100c2305040300c02e50b001914401704550400c500d0700750309040442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 126511348 1250 126510098 126510103
    0xf091802030a1404120e030a020d0b370203040c0801022109070b0d0b030a0c0806010302150f0a03090c0513021c140f060307150f1808030409050402032d 67
    0x8101c103e0001980d29410160341d8000301c10420f9618404001d50700307000c11a10755081c0f00c01c010307079035004040c03101da04900e241c03d0720741b014112000c01e071603640e42003c8001c22008104039a104808140340010184c000c550941c000c2d003000c3c005903441f031910a0041081c62091000b85180301003100c00d151868540111840200340041003d001c58200f001d0821058400740e040d0307480c44090f1580444c81d800312a02191400ca03c03100041d002900d4500005181c03600410101c0c1030303c1c001d42d660914210b00102043c0581300b5811580c1a40904000e018111442688810707003a41c840c0628104a540c2c41001503450302001344012041a40000c0705000d040010f0301c01104400a2142448500f0000f805110030b810000c0000f00c001c665a03001400c3c80d5024031880c40503200062047c0000c0d298074400a0041d10070003a00404600101c5c680f400c404020074644007160518002540382c903003001154805400050002c91305032103003803501c10044480c50000b818980f81c410004148564034803a00e071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 126512598 1250 126511348 126511361
    0x3230c090a05040b0f0616170d0506040902010e0f1807020d09080105160c06020408030304030e120f030412111c03120c080c0906190f0905120d0f091802030a 69
    0x5114604d051040440ea40f15081c268100e94001c131800b50f160002c2c4014a00381b511080307401002c0d1100031650854021200300540b038a032080040030811a07a600d810310084404000001e400300d00040c3e0848114a001c407140d5640788009400d51410040c1c0a0010052110641d00382c0e0250300600001c1001aa109041c0b40040038030304020b01441c1040f590048040c1c00700e841da6400c0000003a10743c001d0182c41e80485004000304800c03a540c9140a09000b8a50112000c110b031003405412000c015155000950801001009014500d018500030469070407105d0728504440040c0d0003100d1a940d6515402c0002880b0340c080d1414900070700d113280040508908254034445907251400310590780740d01100440d48515000d000c40e0b503600000d400604180104648000c803a83e0309201c00d075030703580e01c410b0342041c10902c1d484041e105611a010004012403c640300703070b00b0750301000007941010b01c030340300d009a1100325007006101d05403680c0a20142000da2003040c001c00b44c0000c18803e68048522030709 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 126513848 1250 126512598 126512609
    0x18050604120e01021c0305040f0807300f0e1c050706030c020f0d0e0f0301091109070302090315070c0804080109051209010e010807090512100507030203070c0303230c090a 75
    0x1441038180c0c5c55800c46684103004441c504155486c40010300304610b441c903660002d50000b01d190b80b102c24a00d0819047c04050744d421003402e1100c0b0207504d145040c075072562601201900e80180c41d503070120089403281c04500140340d110041c0b280d82c000c000310310164021f4140c081c102901a02e814004040d00b40d8084415a104550090551428144000c500b0030704040940c60404078101c0100c00044503040d003001e12550552910307441504001186103d40a5810b05680d03070011a03450080c20b604074003922980d00d806030030481c8070704203452242c55940d07403150a50410310301001c00c0c0d88a45400c1d8000d5040303000300360340d500402014440100540c0703e4100115801d02d25042010f000200840010110181840803a0300440c0c0b04070300031007402000d010060402612000382d86401e17036a40700d04002c442c0d441c620740780c007140e82c25100c0e008480c0f0a0300161103540781c8402c0c5a404400a05004400313181c0d05640040ca4144070354400000b80c0615440b51380349843e5041a001c0050079504d69110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 126515098 1250 126513848 126513853
    0x4090c12110703090b07020406270b09191d030c03180915040903030f020a0909180c270504030906020c0a03020114180607060501060f0903020a030618050604120e0102 73
    0x40000fa62000e4503400b80c0c0d010140c140c0c0c561020f480400c000c0d00003900302e2000800e066402c00c2d500e00461a04004202151000380b01c0301c007100d018040c510006403090305000008a2001a201d01c040e0410003803040500440314204044056071400c41d00640000850346d000080c807170100c2c01c0d40b8100180c408401300c5d0540e185d03043c41f4448400040600020500454079540400e0615009520103084400414000d558410303040d5070081c0b4259050151024252a108a499207480521008584140c0c0848030350b040f03908003d00480240307481401c0c050744c60100804040d451030346004817401203200c0d4461145503030800d000a4185007e03611580c0c0a0085240d0400150381c0c050700d080511250700800702d5540d4815529990034030703003030758810b5041040014400100020b81c2d00107812107081d07a4403e50b0451819204840003c05440080c0d44a16800c0301400412a40d038064107c18103a0041c2a48201c0c01d81c1e22503042407070445d019079007d410120001e09882d004207180301190024800b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 126516348 1250 126515098 126515107
    0x50c09040804360c11010e0610080312040212070f0612061d07120e1e010c140a05090109170705120d17180307050f1207120f0504090c1211 61
    0xb045480300250f010280d0125480d0544880358034004e20041060303214250091004404150703a050792180c00303403862105200030f0480040d1920303010083d80c02c0203240d00300e0400710352516000c00c42480f640321007164040c061000700083c42c12900b81154014074154072020a4410400c04000032149640d21801207160110940d01c0051421020150f10254505214004d10140c1c0d0300c1c4001014050381d65107803449032144003040380170703482c00c82c588a034103004c02801032004840701180c010465080e0146080c5042c008841c00c44d0103000606000c81040c03512090789507540760800e4032001c40d565054031a42084c0e80c00d001c10304000e6040e203900e242040042000f0304400304001c10b4482031200c00021200c0381d0000c208210000e480c8071800c0981001269151002402e00f151204000ea441c9242881085070711126000640107984909030468041e0f404405510703401e41d0a0380d4400c060314100310b801c02000c41e1904170b034404d210016080f42e5500200d01120703a40c003011a1003902c00c0d910706a10911 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 126517598 1250 126516348 126516419
    0x201050307030e1903080f01120b07050a170103031809020a1d061204150c0e061209070302040e03090f0a0b161704090b03190302060c07050c09040804 66
    0x20122600300240b03180000740c90019940d520708002044811544d207003c050440410705030b200034000d000700402a140d641d00e9980300c1858005d41d02d449802070403002000300003030180b4001c038081d0000d0296820301510200310720300807000c4101c00343c0045011868480038604030341e0251134541e014000041003185841e0741c0200141015419080d014075005c2c21005400c580e440e07940c00e5401d2000610011503160a092915850384461b09040c0402c0c2441d08000c1114203100b1102040ca500c00640b42d21b26141d10550b191200f0300c030040550443e80324041c00040181c64038440c0b001c1141102d405191911f4000d01042407014156803070300c0c0304402003e000d21814207240d080b5942c8190301e10241101301c1d42881c241203e035035043c007048003c82c008a4001072401e26900002442d260490982d0b802c01490200800004c1d441c5d0005401030b4801ea0000f81c1d00070038000201086c600030022540801090400103101e504110340481d5000c0000c0b40401c4190303e800c144180c011140100010f0910008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 126518848 1250 126517598 126517607
    0x6090608090c010e12160303091503050c070803041a0705040f0b18040519060807060e061c1d07090b0901060f14090109080d0305070e010e010804080c15010f08070f030201 75
    0x24201244120351707124000484940070081c09a1898119120311002581c1b4100981514002e05c0fa141c0000415036000610764400d2140610800c0400035903424034100341c403809a140c00083c8112030516085000c07038480200d586900f441103200307507a101e980e98101680c46c400e8400f5075201c04624003003803117030707036201114038201c2d0b2110b24046d500018a0f80c3c40c182c40344585520110894681886d0080115803140f010a1050035280c0d1611403900d140c02038414083c00c2c0c483c1950710140a4407552060b2900c101540164071405007550001010106142d1902c0c1824200e6100b020459a0303410203203080d08108070124018102c0741400c0c5210111128054404450795031205070a610010300501142c2c000c02e95a070180031850b04035612400034203800f4005060640e652404215041041900c6600c034008200400106940f0401241c032941e039080516045011008200e02514542e140d400c401d13808158000d00b81e03101d918a0305458654094100920307500300c804100c0142c5010700150340c21 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 126520098 1250 126518848 126518867
    0x7050c1e030709091b060207061404120605060303040801110306090105030a05030d0e101b1205010f05010c11061303110a1d07020109050f0106030b0a020a02060f0405031306090608090c01 82
    0x540011580c00d0792450700000b00c2c5918035581005c80e90816001c125a0741c0001c800c1c0503682d081c0c54150403110000441030142c081e0b849880c405960205440d8001040d5400698001802804a90905460f4043c1c02e00f5188502450003140c0f40200800c440c92400c0203850b4018a400d8010f0301512103640c9070980c42e03100e450043c140003901c94000d100806010000c10100810780c00f0200b14482490b04e0110708000c40c1c000d60000164401c08050b01761503d44a482e0488500d040c0c0500713403510382070041d24803400a14040d01c1c00d10940c032164003252200001040703400022002110140d0952070111941e412a01c40b640c0207a0105c20107000c100146c07010b000c1040c0d64164a28859940c10504a0141207400001041130241000d40340165005402c00c0058038410103001881d0f0343c844072400100d0255046000c0142c0c400c1e800b00c1c250001105009402600410a0b030303180051403e4101c094a0281d800b040c00210907003410000c485d800009290808881006000720b0740c0440002400d1a14 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 126521348 1250 126520098 126520109
    0x905060a0e03160c030c030305040618060e040f0f0501030807020109080f19140a030305060301060605120105010f090b07030521091209030a060e0a0303060806041a0a090807050c1e0307 81
    0x3031840d0f407003840030b544210740043d07078071403c090021502c0e481c004005410a1280c900402c076440303800400061b2078020032041d1a511b68487c003502c0442c501300000360030207940400310940da42a25050355202c2e8000c149c081c60040442685d2060303180300043c20110300c1d60000505402126842c03210308804162102d01400880e88400346070fa050805081c080c401c8041d0654a1040d1111007003015015009240304540132002003201590b200d000391303114030480740c842e0386440900c0018859503005c0ca0360075003001d446141c19000d280e110320074180e4641c05114103070b01040011428450031100055030094007001c0011883c11410700c0c052250759800b403070704948003945000c545807030789807801c100240c3e0041d005a01403141034050483c00d61988801d0000b580003c0c02c22202240c182000920940282d502c05444684404001e900c1103000740040c00b10303034080c1c0e180c0c104c0030003180404000d408414000c001070300d0324405030420054080c0c0d5600400155400401151400340d802068107000c550 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 126522598 1250 126521348 126521377
    0x15040609020f03030307080108060c07260c03040e0108010f020403051b03010f02040e01051503090607050d090804091401052416050708060403090b160201050702130501090905060a0e03 81
    0x40507480000d201e0301a12000a030544408401c20612617408142030741200c102e08141c80e03a60f1105c1205045520566001905102411001c180c40a0380e010010340e65401800e10981001d480300d0722141142c2c401d038410080d202c110b80042c04032804c20310944031840f484030030451801d03280d0b68645132030700c546281e4101d40042d03120503501c8544007908481810300208004540d920f441d00d0107580c08110078040c00380649540c8100d02071005130181224012004000102001d40d82c4a4084a0b036512801184080d81e444000442c0021030f100c0282024000360a0042088044844070041082c4164045841030281d60041c0c2c003403282c50f0200340c5a000f844d815159550580183c0d00b2a8010a410001d016100724a40041d4030000420628040c40c426550050309075590b20880d440750003020b00480040c0e000042c524015070081c401001e43c2031014240228075a01d00c0c9409040311030036400704403101c2e142d0310f01c2c4007001810710407564410000c1808200151003101d000b984d90103810250300d00034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 126523848 1250 126522598 126522611
    0x10606090f1518081609050f22060204030c08060603011a0f040b0d050c120a02010e0f03100e0105070f02070b07110d0510021809040210050f3702150406 67
    0x9603c01c82889180015800410502541c0c034510030b0356900e4810700a4110003016000803c1001c010300807a40101c90644903d1010b03110341c6031505200d02104090500b20100254280008020380007400046010f0812559001d1a004000d0704024004160910070791410594551042e003010103010b07126020340b00c4220540d0744034080360080150441107030740041c00d000640704000b000a6170309100a41640c081524802d8813140b9030b910601c50b080240400c2e0000c6d101021814090410300442c0401021100c1c2c030100500690100e8084d1402c0c48020b03512002008001a048070014103458414801440010301d8000320b65218000c45070300070708108145014600d03035510810301c0b05506800609403034100480305d084900035401040c00d03100c0240d248485c84400d10b002c0a071140304a402a003c8906080807400407603456200c9250b040c00c1d01c805000c0311460750110800c5141542c01320b0340004100c0b41ca000d80d150204003505c100d0046500100135802086c15000095420650000000c00e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 126525098 1250 126523848 126523889
    0x13030b060f1f32070f0618030e0d03050f0d0603050f2404030c020108180708030c0105400204021c11090d0201052503080702010606090f 60
    0x200c220342080c15601c5002c640101040c105940c10a450801881d1034160a10103005010f801c52024101481000c800712910800100c2150009050280c801c0b1480051031445564080494420610000e8908540ea0248007010f80001c00441198030403100d2406001003560000c0c410300c01d031344001c0f03c0c980c80481c0050324000b00b03400101c0610f501400303175000c04040c030050340d960380c1c0180840121a251b01494429980c8c01e031030700fa0301891300350b592441c0a8919400540304544040c0c1807210100c0c4803203402c144c07508240202c0c4040c2c0301c0d00000e960741b000400390f0039080d124064068244451800180c503144540c081d0f1503400d074204030301c0301c190241c02a5450424012441406034205000040c4102054801b40e81e114008230700900420190040e03090040850294a07041c03604410742c921800701540c01200500103051059070b07070f08402c2a00344a81902d400b60504120f022603c0d1406215595030207003d040003511841c40d008178528079203501c1c0c1a0703404480c860600c4260000c2c1c00c4a10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 126526348 1250 126525098 126525109
    0x90f130212031e18060f03160c1506080c060c070e09030403120f030c09060207061404180506031e0a12020c030604110f0303120604050613090c0303110313030b06 71
    0x80500380a21110f00c0070303181c5048841d510410500c0c0e07104e0b16a0390b1034000c40c64007000f966420081151180e0940c1d8488000c402203440303076680d150910110307000030f00008a0300305080c0800300c11a10f0124181d03140a4a484c030300b0850980e500c0c400c01d01403002c0102c0c0d080018165084076800070800e0303110784624400d1425481280c00245c100216028001d501700c2d040803a02c28104281d0340c1c03c21055038011001c40d80d0007064002c850050b0413868040049501c980030180c011101c52844614169445260314180d500055000a1081c1c07680c007009440c2c41e05003c403c0b543c22246d0385148044001d0a880c0e030325280c0310728005120808c04410403400c20302c2003207804040f41d0094100c0b8090305150400307c5031504c1424419220b551140c0000724181804015104020040403c2c0703241621144100005410010240e42d0000c0520341450101d112a004503c0c96901034042e02d80010308504005040310040246030703149038400c100da8056600c0d582d640c2d00c01c5980082d80c100568403488006039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 126527598 1250 126526348 126526357
    0x60703081b0a030b010e03010c0e060901030b040f1a030604080415110a03020a0b0901020f070f020103150e0a0b0a080606040902040b120106090b01020708100506031009050a02090f13021203 83
    0x2224441c00700c2c00b68400398140e031010321081002d0701c40703810000b032030000c050070b0720b41104511000a095480c22086810030301d0203030100010504001c07031304c00d4441c80411f003241d1800c1c1400344200e860343c9040d0364601c007200c40c103121b650058001e00750070307d0981c44060051203a441148101d000104d1000003491003500a50351000c030a0081c1e44540c13449040c02962015622016910311102c0c0020400d406014800c40328407864030405581003050944510b04600000d040c00da06040e16402d414400402d01c2ca168070140400b14440c50042c2401340c83d03075044620240825000b0b1003008030070b1080c4003000406640c0032000311008510700c107042c40032401601a182103550000d1003039000b154000c006400c0300b401e444000e2410006400c094004a917100c81d10300c9440200c0d040f00d807103046140c41e9500b140f0750154024044840f000f04115140d81101e04803582594903401841034641145480d442d060382200b203946d01026241030108500039000303a60f0000a205034600d42c8010603400f000d1081d03d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 126528848 1250 126527598 126527641
    0x4020405040f02070203010c050406142a1f020a050909190c030c022103010302010f02160906050108070804030e060a020106030b0702030309190b0a18120e040f05040206070308 77
    0x18480c82e40000c0c24540650841a400c034400e501308113100d044103100d2402d54045907a2913480c0350003299403904031f54560b406900c4606038004035054000d40321402000a00030f55001000510300b101041c019041c86214009005004600400404c005603600000340d070364840e82100c0d21402600c4501d82540b2104410340b00b010705070300b002480313400e0039050390028040c0300c110340944045441401103e04410f101d698000d402940034801400554031800c204280301e032290045030601c842601c40984100c425a00c2000281c2d00c0b80018440c45d40d0212849400c4403d905041c0c5450801ea80c000d001d9009a070b004a01890000c61210030040c800d4120200a641140040f14141040c0000075160b50080352982c00314401c0c10a41200841100c16064a00350006090600340c1c0342c00c0c0840014180143c1c01d45803084208110002095070401c00100c1c030605515030820007404003050105460340a084541c101c0d00e001e0400001d81c681000312404035034580342c00e100e1662000e500030b2000b45200381d03c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 126530098 1250 126528848 126528851
    0x210d090503041d01081209060c01090c05011709071403030702090a0504210e04020d1103160306050d11060d02041809020319150515060c030318010c0f0e0402040504 72
    0x880060100100040050311100c1004950055040d050980034480a12a9006035400000011050401c0304003900d04006c0041c0542e01d040050780d40c40b0f0079925400b0007a60303035010300c403c200b100c2c0d070300300000305294030f41c2c116059083d04d4404005501c2e400703188601b0008010050000742c8035a02481250040c1d54024003460160a18100503401058103c600303c808000c00582c1d6030301509903c01c40c94000440d40e88a443d242405000c0c4400fa402c004c00e205011612031200e4110100400c2c00703141719040341904000898014a002030643d10301d9400140203c01d400803000109080581c0760141110070f5503415034030040a60810f00a12803176000c809a031658074556208040c05030001103150380224204c605d0114580d00254807501c800e1001008013000c48510300c4001c407980c000c1d69001d02e0320582d4000011051000c940140d02865103104203402c000f041001c2c901420380344c120b84c680c01c40002c000d80c20102c1c42c060244182002c81c142401008414900c2c5a9100d404942c06048007910 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 126531348 1250 126530098 126530111
    0x1e060e10031b0909150f0605090a030606080a060b0a06050706050c04080102040b0c0f07050109091a0603070507020a1a032a0d02070b0a050906130812310302210d 71
    0x2e00038800792860081e81482404c001c007102c00340c100702c850a810f507503042041c041d00c18034088013950194402e40b4a96040340311808000089036040c07280c0e00081c0381810141a0b018000d181c144100c80c220200c3d00c0c07040440d400c081c009554800e083e940e5959000f940012030f0745429045110a0145a2003201c0c107600008000c290084240050003031700c01400112049840c3c03982032241c44104c80e008160000300080340400100b1150740000c03960528000c0341390501c200c210302003038440e441203c1500204800094400c214248514a103004017a8103000301c40e1100c0c14001e40c81c07644406843e00320070709007045020241811341171224807003503604051036030344408810108010390400c08003907554005840001d48a4107040c01541d04c0340310480060440340d0f9485140d5542d1a12190007030740c3c0c0c1301e01449140400c16420491b82c0c00b03044003000010706041007c603c00e161258100b40c07032a0040d5240417031400070f0b030000740703920307114001c410320441c58404407600341c8081c0241001c13058410308109 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 126532598 1250 126531348 126531401
    0xf0201020c01060f0611150403050904021306030b10030203040506072f010911010309020d0201110a0803090a02120a1101080c0f0a110705010c020f040513020a0b041e060e1003 77
    0x1800d013022503600b601c41e2810160b02c1e0010544842070710744007000707200c1d0001c00500084c1c0b092004100c9210010320040c1010514444403040314026004480420b0345e039007800041d450300c100030b0442c401e9103207010b51440c5016554551a00b1014041c1800c2c000c0131120b442e610f00340f0f92801001201400e0301020600f0500d40d180d4080c0030034041c191910075a03160b510503203511070f00400e245260080e25280b40d40354154011680200410b241d0111ba0081445c40c2000440f180001e600135941c04008010f000040d00400000c0007400e0165000f0b90710402c0740e14001004402824195002400c05038540d65502202e000940300b845603d4080e02c10014032200c0352a0001424540000c2c110202c400c041e490320019100b00480c200c0c041c1d80300208072020060b5140941050f81d01144551492004400c16030115000c080250008003034100003190500000300d0a0011100807105400078545691908074050100c148007820079026240c801c00c1c800600380280c2120729900c00b44c200d0201d9101141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 126533848 1250 126532598 126532619
    0xb060a08150108070503180c060a020a020a080106050a1202060d0e03180108071202030c0417060a180807120e0a0f050108100311060307020f0105040605071704120f0201020c0106 78
    0x2103410149030720014084000951150703003c0c6200700c445886003803031500c2d620f001740740183c8001400721052080d03042001c000d480f000041d08000c41c054000b42102c01d170750b00c10020050003030340142245070b15000040044d644c1d00d402c9001140d07003c559134002c0800380c0c00869094490b0914000002e41014103421030030350f0000041101f840316008182911004000448101c03030242c550000150f9800c0c0040740c1c0c0a155801036400400c01d001203864940d4462084280d030505030b607029019001602084900c504c1c50040321340d0000e680070801c140709226940c00025001c0d0150280c4511410302c0f541c12924002c05541181c12801894010801d039109402c0c8800060f074000e0900041007200030411f10f001001141c4d0580c2e51102d07291202c00281e000b031084903000188118110b01c107800e00b00000100038401d080c0900e0040c00b02044a190540c4050504a044280c40c101c07180c64400300700124a00307010141d500c0ca0140b07071005025550380300c12400390240003d500d40395440c1010010348900312 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 126535098 1250 126533848 126533851
    0x3020f070f0b1302010f1209050f0304060801120309030807060b0d140c03060c0405091017010b0f060a02072c010b0304021801080c090408041706060a08030a021f0b060a08 75
    0x582c040704096075910301044092030741c02000078007041814081d44120f601911b20450042000c420024000200341c807010b2501c454015402481d800000b014401154405060350250200e488003450704501a03030010301c5282c40703110182c25a400821140304000254118100e0010001c2c5210102002d40c20071160300c900d1144969001e206003d124011030401048507407050307202d080301c1c90509207800140000000001c00b409020040e4640c08180d400174062454007040b5148000038441b18407805101041a070640c0c3d0921401c01400000c4046a0009100080d0346140d0003810340740f1340f41c2d44118011861081002c0803c208000003140c1e401200b4091440359008131400307032001740c55401c500c18000003070045480540128407440c002c0d04100c1c0c14590058441d400326440c0640d164106501c1d45210a8020144d400c0300060002c1440c140119201400703120000d58600000d5881c040d42d9040d5501c0038180219084072400140c03801a4008009038401a102030341d5101160742c0140501030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 126536348 1250 126535098 126535103
    0x130506130608150a050d03020109120806090c040509040627081c02040b03040303020a0c020907020f0609010507050904050a0b10050d050c04060e060c010603120e031507051903020f070f 81
    0x111000060f81aa8003014001d02061024001c0003c56062501303003c0c00105450341a0290b64071200354100045008000c1d07603810016a03076004250a00c4402c2010101c4082c00a025150051105000c60354442c1a125003056020000146401c03044145d80e54029041d038044540d009481403000038451540c00404891254140110000743c01048860480c011405200b00204040c000600024020f900030400d005447c103010303ca00845070300003034078001c0c05c5031300c000180c01c0503407c1a07030300e1000c12900b5000066034009105a10b42400028000d01590b140c42d44550f8071100413413071800c00c56000d0285840b001c0d0611845a11000c400362041e4404551031228925003000203652403e60402d031410b0301c0f180d41e51220704540030001c000701600108040750042d540c1d070500000087d8640400034444c411074541100c00ca00c0c180030141400c02c90600d280c500c23085c0004010300243e0220454072058991000090ba000009100703c00034064241081294080000d079101805010b0001c0c110003031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 126537598 1250 126536348 126536357
    0x3030a0917030106140c010f0f061401030b030d03091113060512010219030506060903100c0216081c02031215040c0f0f1d03010911030c120c04021305061306 69
    0x80c1d180114040ca403009100e0100000c4116000200064819009245400d814400825050882c44104007151808960920200ea07900300c20043d81d00031500400c00b0f1082401c080014241d0140400e48521051005004050780c6120385410890246070160710050b0181c84400f11000d0311030000006c0c222402228401c0600c0a1400d100e00300500881c1c00801161040094003070b01c086046c7c01404000e00340581c4601e052006951548007001442c040b01241c050129502c01224030203800c204505920345162140e00406200035603001030401c440340058007008403c9003000804900314040c807902c00b014011004c041c0003501542c50210001140704540420011200c0c000c1601c20f01d030040141e40100c4c80e24100c2c0746c0f480c1d000d03003800d5000e000c0110001c43d485009800003801c4820401085814010360800103a0500301040b64142010050f1040003030324440c114035030b80e9070070b00018151150360001809800b030040d9490b00d50050202a00107034481c14801c25402101400d40149000034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 126538848 1250 126537598 126537623
    0x50a03020c0d0f062d0f0617030f0a030b0d060501050a120b06090702190f0c05030a0c0e060d06060e07020111041a0705010905160e01080106050922020303030a09 71
    0x80c03402000240030340d0740c08000054850400d50f9504003400f0407001c1000303024810b00c5c4420100b01d01c0258550210002900001d24010b039034070b40303021030350380d50813041844030204522a5080400012540d050030140ea8060711004440c41c110094603050384070b150805040c0010404010030340d0015810388104440007103015840b400700b6061862a40c50250009082001090380d90a219019a80295981c41a9030b03480801d0340307110b0032002c0365001c126406105101014140441001107030080d120480c0036182c10482500c5650116215014210b48000f00d0310106050b9580d040c00c5100c881d07404030701400840d82d034401d0b0110030707482200c80c14050750034000c400b00c24500c00022101a1000782502a240030141d58466143e40c100310001c854035075844142d0004140e081150b100091710850b000b44c032041c1080b141c80403090f010303841030b00b0390f81c1801c60a0200381e41e864411039001b89410107124074150034070781d64864407241c28006501130000009000156180340c01c507640450089001e080c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 126540098 1250 126538848 126538873
    0x221160807090504051b040f210203060c0a0512010f06020c0d0b13020a03150203160201020412240608100b0306090a06050c0f27030a02010909110c0604050a0302 71
    0x2404101c5520000501c0004180090b16082c1d000c95007040310441000901c080c3c81d0300e81d9400740d1041e00b1000030204140c104000c46401241c0e0380860303a04450036401c02c040c0320750100c1c1c6c1da07010160100280b0301000c1120101e15101d0303019202c0b40b60505214100035603642c903512818030340c0d40c004e1100500079550884401e090041c040484140e108030702c10b0b115a14a011198264210f00b03049a00c0841c806001000c0b0305444031130886003002407001a941e083c85200210403240d041ea4480a40e40148010844810040262281070350007072690481419060305c04502100e4009150380217500d0240081801c0c400014031a20515464404001c0c1c44030800c00c141d0342e94012074444c1211391145810070000355480d0880d50300122080d15442c10710020544000c0c051304810403401c3e03c4980340340325060f0000303a600d800f20380c410284c1c05807011103181d80000303180c8a81e9001c6e800000d900c0b1001c04c00c4000400c000c82d07030440b400e0f4003a10141c0c140b81c9480798071080440003e80040c418290041035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 126541348 1250 126540098 126540107
    0xd050711060402010e01030e0304030b06190b03011a0c010203090601030b0a06230609100c0b0109020f1918030606031202030301081f110d0c02070e0c04090f022116 72
    0xe68088000708400e5445a004550302d81031845074504158407058501c2010303c00b0000707080954424204500c1c0361401c4810b21075680040c8010001410780000100200240041207a06459010560b11a0030f83c070289042d541d1710030384a06101641c80042000b9002801064090589104c0c102c40e40031074403141907030b50036100c843c01011005103000358200c800311a40c03101c40d82d15802c040c298a00305607031240001e00c1d1607800c024410204a60001d00720400c400809068090048407508508044140d42c008016000d0210a200702260f102c15911005000c1c01c00b600c2000301080840d0112616481c0ca600600085c0c07000b11900303079105401e07501c103900210540781030b41c100340014a07504a0b02c036090002d03018840f5900700b0141c0d440000b0a2601021002030040c1061058082880302e00907030000d1170400035612000f0b24100340350500808403180001c5504540c0700d0407010941c079100d0b8000000078070983c843c001c103e01800e00025540c43c01d00100c01c0c41400807907550301820304028030685 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 126542598 1250 126541348 126541367
    0x503031503031c02090409050604050303250801030f02010309060507020f070509060108040206030c04080a0305030718150c0507050307030615060903020627030a110312040803191e050d0507 83
    0x811415000c991200a40256001d400c05900080005c80c20325480d0b26141d0400602b074500380da154000104200c440c5c0e418844081c50403030450806810b0010074030008000c024180402411000d00d000380c102560300c40d402428050390000381c00c000a08001d81c019545e0b0014184114490092003030002d200d291140f2410301c24103040e1108200c580c2c55508003c0c05030b0008003840c1e80d80c40c040c04003041c0c40fa020402030b411640300341c803030300d0307032400c101802828100c0b2005210480e01da0641c070522015901c06656289420581070082c0700c12202e14015080c000e141d00001d80510038140000140110b5800407080034003000300d030392030036500c807041100d05100500010b50400400c002d4891034100d0081140020600e40041c1d0440e600703803000003820102c4244094408815060281e0a146003c0c0220202181030301160341c940342c5000361035034890003419408210b51710300c211100a16409459a8400d14900d0104c201a8000315403002d000c540045400d100c01d54079200015410501548a41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 126543848 1250 126542598 126542617
    0x90709290406180e1017060411151b07050103050106090f1415070b0105030f0307150213030203030403050706080609090c0d030207051c11060a08070305090316050303150303 76
    0x81c1c603207800c042099500c40c91800d41d51403041100c040000300482a040e03039a000d01400d10388000321615101100100024050003030215030024414000002c101010403003c031030742900c19110301e003030300700c0140303031a00a2078038190340012400d0759909c181c5008900c0a058034001d8030100203590700c0d10021130b03211040d40501503c039100c42d1070070b20240e103410250490300c034001000107801e02101041c0c900150001801203030504041d90042c0050302c0d06110107801d2126401c0107500307041c00360316450500f01200d04d14200e141d80c0051038030222a014002c0e0009944c010302140e42c1d440c2d82e13240c100c2d545d08040c810180000c00c80c1002ca00c040c81c10000f074601070721198004003002441070303081200c600d80c07000d011030541c421103000007042e8603200f121171078418200102d601c0d0400d5500b0000350041c040c0c007441d44105e03010000c0303101d0140c1007401503805c0349884c070f0300040950b01c102c080c3d03140d4428443c0e00301c0c4618038801420f041050010080d4407030700718000e4070140380d00e01d20241aa40d01440112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 126545098 1250 126543848 126543929
    0x4020a080105151e03040501060b0c0c030d030c05120c1b06040b0a0504080415030b091f1409040f2d02040b030703080a031802060a0201090b0106050f030406050405030702090709 78
    0x62004d084e45440195803c00d000b500002111541c8004110443d07000d4403401d0207580010300320b4095454140301c0d0340c241001d2030a0900c003c10204100800d544500d02c91440016001000704001201007000d0314546483c00f180414400c0b068043c441d6038a600b00c030100c0341e00d440b81c00001c880c14843c2c09114007aa501010a504003401c0c501d00340071251001c900320080545e1100d00302480d681d120036013030190403400b130461210007140c80b104c907643c003481e0402c8000707040ca21111850b54551400b0079902c150000448400c0c03084514001000301000b001c00e1818400000d1203091149081075080001c910071281004003495100c14035449052600c030142c6039001c140484c20300c0034025080034413240324000b84c00984010b150700250039034010000d0000182c0d034448a00c41040130601d00c0501400c80c0e4103150341489200d001d14034152200500c000c1616440b40e011500b001800c00c144d442c031990061030480d0921700442c00902e5050341d40f01c0d440b8400340f90120322204050801003445032001c450300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 126546348 1250 126545098 126545137
    0x601051201020d05040320031201031205040b0f1207020a050a23030706060e010501090f030f030504030b04051f090c050d17040602014803020904020a08010515 70
    0x811101800d060030690381950204492401c075041845003a11a500c240c481060b1074040c03034550107699200341f0b18006d140c2d00820806150136880704c900d41c1120741c0003010700400e205805040700d1a0150340d1001000e104007080242041b11040054803e802500b88104942d03500c07544205e07500d00344020060b29580051000714003141404102d0720441c6402142d03074985064800080745107511034013099440c0e9a540303009111518185290341d006001c2483c2050540303003098541c0319050040d2000800e141e9443c04682c08142c041c8042c0c0d00115080f03901e21465142c5410601e441c0c50b00b030701111210404851400d0410b06d114400c0308203ca07040540404510308000038040c1c0075040d804195840c60310354030280c24142d5884024000340289600225032001c04a202c00e0b900c05d0040a400d4a03200580c28010050500c5909031360100721031424080301c5407809205500034440c00c03c07841e801900004008200b9074200003100c0c100c440654130041c0d15150311200c030600340141000c1d2050035030401d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 126547598 1250 126546348 126546359
    0x1d0603041403040f300317100909080c06060a060e0f150715110910050a030e01022d03040b040b1f03030908150106050d020a02070e0406200c0601 64
    0x420708060103a0706080b2442c090b01e800351940c0c03a20a9612040c0e001c441c0c20100322040c00c40d103c441014180701c00100d002c0305032907507000e041d040c4c902c00176a0341c40c400803000403900149840080000d000340d560800061549040450b29903118172032400760703031040c8d001040007410700c1c40421084615a1340d441640c0011201005251002031200039401410784600142003c00c420042040c0707480703414030b036408500082d5108142d850311300004005030028802c010540d00c900240d4074502d2110b00d801d030f42e58114802c05400502440d02c8041441d840858141034088200e40311200c0301c245408844402c103640d0300c405003107201c00c86d001807980c00751350007180001c0e00003040c1c0313504818001c07580e0101c400d9110010701d200d0202e41c005d60008288000c00c20104200344020011692240b403a03c10541c14031001400c1403045d004000c2016600242d07203048070b4400e2054002810710f840d03c502282c1440c0c20304901401d1000d6004580b4070702a00c4010700026040304841010100802400d405e17841e18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 126548848 1250 126547598 126547613
    0xb15010206010504021804050f090f010921020f0d020d02100203130212100509010b040501060302070309031202030d060e010e13050601060c0303020f03090a030809150613110f04061d060304 83
    0x6e042c09128820b510134a100181e4590040512585407040c1424061600392455481c00c0c6182629080a034902100503000c1801d50b00311800b481685540c020441400781e604910b441c1402d20214028000c249510701c840c0d9012455a102c145694200d1f200134600c041c00c041284020b03106980c00c1d00a2101d5080182800c0307201031220014a4180d80d0311182038280d403400d89074203e80060099545003c00782451925229180c00b40089180450030000b1a079000f600700c0100d4000035020764034070440408518420001c55076580c0025005018070782e40d8040c030061900080c011070320100c681c000090002c0205c0e258501ca11030708075005004c1a440c0050070b036145200c896040c0c0402d0380030402441c0644c50320004502030b0100400400303a03800d46050042c44008060140a581c1d007021815401e16000c0d90803040d0000d9013122110000c1d5071840c24203005000c00405070030507000101702a04d03a4040b90000c2c004443d0b15803600d2035001d20401d01c448202c46190420390b0700c950284080341c04142c1a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 126550098 1250 126548848 126548857
    0x90302090702030c0d02010b1e01080604110f0a080901060b0a0203070b0601090906030503071a06060901050d0e0607020a050c0907120506010c0b012606010f05060a090f0b03040b1501020601050402 86
    0x1e6005030707450050115501c5003403076000410400580c2d1101181641030500b10000c0c81a00296039030990007065407c002840020040d0411384180d450719003000c140c082d80412107051034015801c65540300c070451800741c1420002c4032140e03200e52802d400020400000000c8604408280c2c0c0a1071410074142d507240442d580c081e080038100301081001103210f1080b407050b54041d40c0504001c50f00c0f4070707692400301c06408841091a01d540304100034003100d43c035100242c6102c00380900300301c0c1c0c5460710b0a08100c0185024900e0800c0d51040c0300074045540d4011900b00d10b61809941969807806040080c08002481500c112001481986010307981c17100941c407190300300c0c40514144021011039220288224001e070040fa01031f030810312156140781c011361a0360300c003001c80c80040c2500d5854102258005a05407244a016a81c001811542d42e4880c88520340905409034a058100341c031180c950200703800c01c136411200c4d068907a021401107103010700800d003080016401030000e0ba003084240701c083e401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 126551348 1250 126550098 126550111
    0x31e0302011404060219090503030d180f11180702030307030908070609030306080d09030c060f12020f0a031d060612010e12030a061208070602090a09021c0b040c09030209 75
    0x5039803000b4005420b40701c15040c0140d02a0001603100c2c0c04003040116104809a540f40600c002040f08018944004c8261030385030002000004004000840b0a0301c03212000000519001c0b48605103001c002d580703186488a03030750036245000c1c14030407030303200b91003001c000d44014015034018000254050b12030b8101c10b010b50300c41c0450350304204040d80d911068641804049000c01d0311240c041c4110f9508110b07042c40000350389440d030314003499504d800d144400c1d41d002d40790400c0800c2c090004450b02444180900800000c0110343d80c010820070051181c001c03940c0303a8002401c141502c2442d080b4440742c0c50306c04024002a1089480e0380c000c11101e08408207140d034440d52194400040781400f48196072601109442030340d41c928080380c15400712003a0340c0122084500d90303075074900862445000e444620358003a030010794580540c030004038a184a035009000726400040c20340c940310700030507074011382e840403d01c248180b81c282820841a11501940e40c4001014148104050b15103221810b802c901d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 126552598 1250 126551348 126551351
    0x50f04090f030804050f070b03010e0a060b04030c1d0411040e0c031516050307080f070c020a090902011d03190204020705060f01030c080705010507060902010e04050a0b031204031e030201 82
    0x5007940e422507818400e40080e00400c44110402090005c140500c2c0d6a0091005c00343c020a424150391007038900060142180c52a000ea001442c02201c540c001401751842c020819100c0d0313500c1c50010344804a0340910b80ca030341d040c0501c001a00051005c01c0b07004643c8070b04211074070408901031100034942031507456080d00c5025508062510305001c3d00402e0320709882e5881c6146080f490030780000944503114130400504004004015600441403070700803010212a05542d120740ca4110b40c0c006c08921f002c0e40c0a200704000090300c001ea517114485031031003a203a50007007907080c60101c8603200110400340d8142d0001a445000000f0404054503154801030005003464900d0300e034245080022100072144900318001441403026003203003407004054440050050a00f0b11000a05a0040d250014410b903201c81e4075008682c0a40d40c08080c15101602c2080185440d00f0040c0c042d081c2d6441150007070080d1600e904081c0498421581600d8024181e0071298241410f000d1010403020020380455 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 126553848 1250 126552598 126552611
    0x203041203050a0906060b0405010201110c0a0b09070f0e07020c030c01020c280305070e0c0702010e010806180c0a1701031109180a0f0c050103140109051005121501120c050f04 77
    0x4080d441150068041004010703112390400001908641d146001c0710b808880c10b00c00e50f482c61000054440000d82c0c00300780134031035464004521380b4050654124410500e008030000c5240c101c400d110b17500c200025805c03140c85036180000c0c15182c1703d4045000d030040c0c001e0300c1941018104100d003024502d400000b1450361900c9050160700380019038108a0312034200b400100030705c03005214516000762000509034501600b41c0c3c00a0808002081064144240c02c00003642c203540324403060404040c41902800245412049640264010006000815411f25012030341c17410b03c0344e4490685c2e501440b5a0f11180450b0104030070103d005007020720600c020394038641c80520500c0030003940c1c2e108150400548605180140801c905500a181010b2400700c240d6050f008460743c4604580312240e00144644583c0202805900c10fa0032a0380c120b80c03410311109450400265020309030031081c0f42210a644c071900b6030f941070312440c0e202030003a5a17400c0080c010f6260100da0b01c0b0030504018800101c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 126555098 1250 126553848 126553853
    0x120f050f07111813060f090210031401062307050a0c08060601090504050601050315040e0a0f02040f0203060a06050c1009080d060f1a0309010e072303010203041203050a09 75
    0x155400003804541c4103006810404490030200342a41c1220f0369a03c652000d8a468511002c00c80750544024080075101c0c1c400c80925a0b1660010311710030b401500040a070f40c46040c0240180561841d0081100024000055107510070303840045081202441010048420034891110f500300e51010384490140441402c00140b5014448004101000c050041c43ca04000050305141c450b03844180a02c2c101070400c10b01c0ea91140840340d01c181c1b6010614501000b00002c60002d100c0000140031074458080c0b4001403007003851600301803500c2140c0078400540c40d014900240e00050f25080d4000d00480000d000d40d0340604040d0034282411002c0b00c1030a40d0713040c030f401d060b038403011020f0380c156030001a0b803220b58009000d580d020f040d0350007400c0b8019141980340d04985040c4406454450b20100201c0d44040c000c0d00b01c4040c100703d0354103e9803c191541d015526503074a07105400d0020310303c03015941c45400d041c025241f06a03003100052207a01c107080320540c090310006028000959540060000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 126556348 1250 126555098 126555127
    0x507110a080604150c0c110904140303010803120a0b03190311060703060611010902060f13090c0807021c0807080910060902190810030f03021c18060804120f05 70
    0x8264040c0880a01103109140d8030411a8076400f1003204002642c840b00010070901f036001081da0f40269080c141a66803410303c44c404184800182115010000c000a10b01c6800005001c01160f09000c030141781d251808103004444001380740d9501900526400030f4004400782c8a12040381c000d00700400c4420b940c44c24039042034412111440402c8c0e5500042c030400380d0051000081e1803600c03000b04003005039500041c0c0c09001d600c8030f003507401c80006038404c07520f0142c004460003882c0403901401b03100c409401c0685144404c84868006100b020b046040c02410584200706842a0380c840d15072a807110f2004541c03141c4020703e00d950038401c1c51803011450206104190050540130b00041e01e035004040c00b0000911100120410000c0d4682030013181c02a4002440403a54045c180d009003407030030720341603040c0000b000d12805070b00c04003100c3c2c201c0e00390026014400c8500040d41c00000c99100d110548150f070003035401514104400a060311345901500341e00815a00c075041c0242003070b506881190 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 126557598 1250 126556348 126556351
    0x20a0c0602070c0e06060a08011a0d0e0c18041e0c08190201020f0106050108060d02030705060318010501060f0f0e1c030c1407032105043209070507110a0806 69
    0x8030205000c80c820007030a1070b81e403404d0381c0020040361a0382c0f601080141c024951a8180641940c00c8848114006103070020411900095072110062081c070820f148165250000b00404901851202c104003075940110700310305125a500ca0010b079040018103419040c070069840c421141e04e1030078034002c100d04908101c0351842c0d19540c0240183c951240c400241000205407000718642c1c100081844203a070841d40080e845001604e141445a04900020346803e0440d40410303081280041888400c0c0140f446051303000c1e146000a020f184d90b2228100c4608a00014500018406040e41c1d81424490111001d14007001082c2c98012a40b43c1da50001d95103405a00310f0114410702e45080400c10901840c8040c489600d01510b400c52550b12207080030042d0b003566a088010f009003502010b070294050304c0144c602e5050b51004d1150890040a510850402030760740400e1111400364280703040c00804c0e10540c0141d450138148070300b590f280c42059800c0b501c1c0e00d600c92450000400e04040803c44039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 126558848 1250 126557598 126557603
    0x21305061c0c02030a090302091306020c0d020d0503010506071b03120c0b0604061a221502101e0c0c020301090804050a06020a02030d0807021f050a060e06090703020a0c060207 77
    0x1c1000741c1041074280119400000d00380c06640090000380d04640c0c008001408807030b0160760300710082d40ca483c0e811185804070000109054804227100200500001d07559003500d009808a6103800c003161010303107490109110b5030303a1001c02007100320b0024140041514840c0c65800200341483c2e107941d00c0440410b0101055000a4901000729040c45074548030311350072000640d000c00c00d00c1c0c00c1c00200840014803090450146200207010415000b0511a0481502c0d00780c03503082615403210b040101d05006401040010b110381085d520500d5018454005901c40c01d9500c0400c941107401428060103400c0140e406010b842c2d940100946c40030300a22002c01d2240c0841d40d52941088200101c10a03141c01040455114200e2a001070710001074200104c9058200b500e11581c42040c202c0c500046e10050010764050400f2816079900355800c02030061803046410704c00c05444503501c1a40d00401c40f0441d03404513480c00440c4400740a9401001c81c81c60f1464001c1c1d1001d003a45501050740d0010740c04 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 126560098 1250 126558848 126558877
    0x1b0b13110406030b0a060e010302030c060f21190b090711070503061e070212030a0504020a0312020d1b0c0b0a03061d060a0b0a0c171605010501090c050a0f0302130506 73
    0x41185005c030328492040504080445800e5075415074001c42e940343d400070401c0c1d00a440c005010310980642e4410799100c60340822545c90710321000c08100800420513500005c80d4480c40207842400d541c5401250f01d000c1b006004202c0c142d941c11800c072041c4801c2100303101d4034094098041019182440060303c5000a5079004520681c2c142821181040c000d190708119040001c5007a4081901021240c01c1241e0041c0400c0c980c807140000743c2070b20750036030008221030151004400960303000300d15107402c52000d0b16050425041c2d4045403d10380410304000b041d51b000200e042c00281c0c1c090019100140349440d0000f043c0e80c5a500030812064114400c181e048200c40400c6000d01e40f240c5000094030908200900784620190050286040500c006140c442640c5402007280703071440580b124504240302800c0c0b24040c1d0b0030300e18024a03080c0142450750b030400d034000c864540580111a030310800356590031013030314402c10124001e403c0748123580c13078075042188000f038284d88000c00791043c040d41000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 126561348 1250 126560098 126560101
    0xa030e1906020f07051906050304080910020124050a0b0f0d060b0d0c020d050301050618040f0b010e060307050418060b04090e06071701050609040906020a0c031b0b13110406030b 78
    0x34403813034a2031560159200f002d040707080c2d0036816040c0b6100c004030361160400d0b81d100e44403490a218507002d4040455000100c4110550880b80e05412010743d104800a04441d201c03652189100908158010503800c0301ea00d042c03c02429840344000c10314488452403c90401c10360041c100250f6503294030103d40e0040c04107910405401512820080317258500080c001c0c0210404007400d2400140f20700c0c0d01c1844045016842460341c0b20700307040f603090010420012031034140d01480c010000300c21824001046000310449504003030003124040d0040340c466501305403074a06c5195015041c3d00810503011f4846c4800180c100608010300003503d151a4045080d4507030301138035407601074000c00030030402c000303404110410048603800718151081643c240303644001c440042000b404010b07000401140c40091030301c1103d503002201c00d80c0706200382d0340c42100c1c4c07040c2d880001d2105890f42018018000c130001141d125a407031001d0042d1a4800c0c000d0010340e491140c005011a6050781c401da409032103220 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 126562598 1250 126561348 126561373
    0x1030c05120705010c060f1407030f0b0a030803040b0702190c1404090c0302100903080403060212010b030702060a2a08060f040e03070b04110316090f0207050a030e190602 75
    0x1501032a100040340014114a0700d40f02c0004c0040a42e80c00151000d5940d080340f9202c2c45498200d2090040f2100c0300610318200705400030f000304607603003036402041c2c506020000c0074a0156400021a600100841d045440743d1321a02d80c0891b015110070294410000003d040340c000c101e1000c80c2c98040c10703c4440d21440c182d044054000d4032030305203225502c0d14102d0000580a00d44030016250140c17841049082c40b10005e440d04140c40c1c201418110700480e0001c1003240c107400516880c000d41203000fa06990358190b005060006840550260704251300040b00740042d540701402d03040403c482108030b50b480b00c1d1915008141d201000000030311840802c00d00e801c140d26002189542035400f0483c200c2110305503500c0c3d005030343e001403142030280f0124041c0081d0b00d0381c1e0051240020295030325420080842c14807a0300303d104400050b42043d001d90404841c3d442034030b03840c54001c0c000d401c8440c1c190380c040740d04040794019150301280700030303000c900201007040120107081c2980041a1901240 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 126563848 1250 126562598 126562609
    0x7020102030f0604110712110106090b041a0d0803062d03011104061706030a0212030d0b060310030204020a120204141c080405130b0d0b0a0e0c060307110703020901030c05 75
    0x240154040c81c1002452088445c241044540003504140c00c644590720800040380c50040307584221140d0360821301e000c03446a005074054080f84d80100c1c0c0c1089110001e80d07140905241e41c4003032a50042507452010042901c000086512a034000c007146406c85e0510010410115181d083d1303640e08400e2800c00c4040d090901c035441c4107030f0100780e40508181c039150004000d44150011101c02e002c0500108910b40c07020041c080c01150b008180e04240070006ca15681e40f50030409030301c1c00c0c46d0300346000940c003420b20fa070880c1d001c0c01560005132040d41c2190240700c00380d07028000311810132000c1840307281140000c2c07000e400507120380800c000d0340340e54039000c001c40b0104040310508d013941140891400141c0030000c0700c044401c1a200450241c0141000d5401000607510440d000050403903204c00b0072200c0900301e8418200d9040c01c00144114907001980c078088180d51a0f0001010004110300d113000341039801d0400c40400c03c07510025280c0e40800c4c0c03142c3c42a4000c40e02d4554806043c8101d103401c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 126565098 1250 126563848 126563851
    0xb03010302120c030d0c02030c1305090d0906090e060112051501030e030f0306040b06190305010e010914010509130c24050c0d0e130c0e040c050703080a051e07020102030f 75
    0x2100414050f000c0301d00080d1240303103400546041c01071040c084c0d011520140102e2082d824010104204c1b0510201c0d46000ba01c0105c0b14480c1d607000302c00e268030340d0ba4040d03aaa113082d0344003552510100c50074034022005101c0080d103164180701c05c84003c00c01590541c01050700c0384404100e4403400911550000d025118030f0004140355800520505855241040c02d0740c0d40540200d81c0440c14848910114543c3e124445140449030441c103010415942c054104e0b42c100d52a0782c1e04198641c2e40c4e0028403084a0000c641c1031613094003a00108503d2070300b540f00729000126103c0c140510201c40d642d605803021142d011030000034a61002c400000000d00c261008100c0304e0401a18184540e21016281c107501070403a81801010341011019827035181c0c1100200050f079008200c107600c1d280c0d014088118050100c0d00c11800e004039100680d110342d00751060300b90300d6110100f1030b850b003035404006000e00802580441442c2c19400c690a039002c05104d00030482d40d000181d4a0074520f002e6105e041c0d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 126566348 1250 126565098 126565129
    0x3180f0a06050d020f160503070b1303080a0f062c0a020c10090501091a181218060d090c0303080901020405010f030903090f150206090609060103022205010b03010302 73
    0x1180a08000c025000701c1220f001d80392550005980744000141c0c006203000c1d000f407009140c404038618100b0090008000c1002c940036807403501e001c0d528904c042d500301304a003100400082c6120089600303030b10170360015001113000c41008166503031500f110b101c01c4046100a118404140a0410403490150a015400c90f60541095240400b4000c0095580310341c0d0421200142c0d42d40c0c00381060110a600070080941c2c40029a40600e03141c5e41b076000d001c0015a8040310283c1858254580010002591480c0d000d40050f42410b05421800c000410005405442d0b080007003002281c4190309984941d0900324850101e42d0745840c00c504006000d048024002a4640e10401040c040c3c0d81c1c00259061100107a80ba000c10030303074120301c0d080303646c0f80481c1d20010310305800b00c00120712954442c4030f030030100c1000e9003102c0a40d9105c65010395038100a030750040b450303000700c00144058100803200803049400c03000e0006582100310716000c22100e090b4003602c0c80c02c40c08401801180f0301a2000c3c902c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 126567598 1250 126566348 126566359
    0xd03050a06050d0b0723090f100f0f05041503060e0a0209030309130207050106030506090114010e0610090803030108060411010806010e040b13020301090b03072301050a1103180f 78
    0x42c00d00001ca0b2991221071405401451203500080c0903c1c810b0740030f0b1134403003015140b0500c0d54403902a107a03480d803c04c540881c4602e40020807541c0f2400d040b02d14071f0b0000d01e01c1c0c0d41c052403807510741000d41c3e50803a05040c0300100001000f021401400d00102c030301c41c19030907640004080d480cbc00c4009296003806000e04003054010010200b05940020a03151189822940341100170042c809800083c840c103003000344207508094001003030040210700c6511408442d4004d0001100070080c034041d1003024000e005041c0c1c0244c000c506603050a001aa081d548a0305043c4001034440c4400d500d16042644401515486002000204082d20020b245184000e081130105404d00c14006008603107914035850140341d8442c00040700c0e41d40c040c65142c192520b010f04568958442c8100006406480040c1c0c3c020b102d16080002d51200d550307402d440241c43c100b0715000b46200840111919800207036643c0810001040707076840c0e0842030008007407066400c40400c2d0a4040101480401e0080d581028402e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 126568848 1250 126567598 126567611
    0x90307050607052b0b03070504020403020a0311040b0607050a02030c060403051902040b04090503040e090307080d05190c0e010f0503100306241d0606090d02010c05010615020d03050a 80
    0xa0400501c2a420401500380a034580304441d180020940e8200c441e0481e104003410485900340f11070f030000078540810340036500d4880d142d106020507481503120094103c01a1201040411040341c01824000c00c01440418880d104e580040c903190000030307040d119600f008204008614003007019141c1640b058850314103041ca0740c3c070340383d4a07520721148507030f0413000c004000800c5640c0d580c4a5804100000c3c41009000c80608110b50369810a01600007046206000b0480d015400000d075845241e10800340f510307180105040078060309002d0071140d001414540c09504030110390007901c0300d4840fa5910040901c982500040140f01c8115500b4180181041441900390312840d00c07c09803604484041a21080c040d0b8100031440000500e1005050543e4085040507002d040c480c4003d42141500030161220020000284200480c49601140101c407010065001c3d65025a03080d0141d400000d400b50750780506420b40d00d1001032000103800c007524a0034160b03014892307240c20101011081082 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 126570098 1250 126568848 126568853
    0xd060227030105060901050405090703061a041104050306130f05060f0618010609060e03030706020406050a090e13030c05010b0d06020d0e06090606010804080d0c020d0306150c11010e19030b090307 86
    0x301740d060041c5401540c841002540001040145d40c005640c010130030400403c0c43c0403500d0030003203080c403400e04c12418480a000ba60108000356000d03560010003400041e100c0400000c500210b0300d1040317540d004c00725502c0d00402d0781804084d100e0000f042100f9030502e400002c00100d481c2105080d040d0400d40ca005210380780c1d201c03102e0b90955119052803400384070324030001b91843c010340c1d5004180d50b00015001c41c2040d4000041c0003030803140e84804024684400040481ea00d0484001c0c849100c4900c0c0440424411450000303480e00600001418110f0900469071040d058070040e02c800350000b403041c08402c018450820180e00080181806040c4090301a0316043c0c00303420f26040140b81e0b03000c94103000c41c21040301c80c443e80650003000030003040200179455000b1050f007107000ca480d00e2000200d01091036550040f00840b40e0307400180c618281c0c1c0703a00001c182c04040700d041028054072030300b503911a91150546a259100070401035451032502d4404804010700c00c03120742e0001e0189900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 126571348 1250 126570098 126570109
    0x60504020907081612150f080c0a0803191416030806040b0a120203070806040302060f150d170408030a05090a060f0206040816021c150506030a110d06022703010506 72
    0xe0404181c85c201350b850a00005035406001e80741c40c0c84405a00340400082c600540c0800907003103e103908142c03030000f4049400c22040c40924462000c0d50f400c20040e00c680080d0240e0015038000860a100c0e40500d12114600102d401140c5d1074103884242c000c2d001d041c0740d0080303499035221000315001e21982d402400400c445d81040e2140091080da10740c2d000085507000c0c440c0300c0c0602802000c80300b03030349003509000b0754400c1c090f00c1d0000c1c400908000f0603030000380b889803190301440103440310200c079282c2d560315110440d00da504100b452000b444041421102480240200200b42e0b0719261502d0007482000b546002a074480000c0c040310712801503c43d40c01091642e801138001207403603211040b00b0b1041d4100440203030001d500540c1510803030200300702d61000e895141d0246403010011038941c0000412604191101541944440344070000a65039055544000c0000b030440d107261445682d03994166002200021070001c4481426001070387d40c1c60300c010381824110700900c0103003010008941d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 126572598 1250 126571348 126571381
    0x7061109011d0a121106070b01030b16080103140f07060c03110604020315090f0109030f0e0111060c2802030c060a150504090503071403040611120d05130f06050402090708 75
    0x483c424400706800003803050f03003171640e2026200600500e60307aa45902d08119051030034041201d81640100200d442036070503405034030780301419840e003000c02d03406e5807600c207102804224a21003e02c124290300002400a028131002000c0b9501c69104120719460041c1c04820004044e0760305600401c108000b680d070018402d070640c074285400e111540c03940002503040524034000c0d96600e40c01c0542d56010107500444200e1030183c036980701e11400305908011255200a0980070b070640e44648081035500042400611000f15504440d0107042d5220b1b42d500d904420b5100b9480250b0408202c450301c00d4414445141d1049101e1002c01102021100c01c982c00d0001e400780900a0390340c0c0c100103003009820412502142e80055010440f000c842002c0b42e43c941c42402036000040305c1c07951003220003400184e0020700f011315190b40c83c1401ca4050701c150003000c004040200e440300e00d52160001c61034400801c0320f454020280466586001c3c0148141c0720801f07410301c010007006104118580102041d900c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 126573848 1250 126572598 126572609
    0xc0f110c040b0d05010c1d0402031b0c03131701050121080702040e030310030c0602030c0a111908030a02010c0801080c010309080f0f0706060603022d07061109011d0a 73
    0x10400c010b103001c5072209142100042c400d41ca02030f62029880c0d08032841291410051540b00c118200a805000c02d030701065901600396150030107807100da201d080c1c000d0700b519400001140d043c40d0340c0c24084513211029600c10b44609405070307000900340c04203016150140c0f0846c12103400314401e03402e04011190505002806881c1c0204000c411541c45070001070900c40b0300b000301c9449003010191708804644510040704c035040442000a402800802510b43d0b80c0c0e1450042e01140180b5121170b070394038800750381d056880b6048481c1c05c0000c1ca0740e80724000241c8000d400454942c85a08806400c4455100c030441c240100d0300c00400c0718260001d00350740b02281c00c1c40c0102c2d0100305440e003ca007500480c2140c284223b00840c410000d14601d002a007007581c0102c405100e481d583d0003081c0d040b445030300e00d48409441800c0344d1600b40510042e099032445603001700d95280c1055034075542c0c103c3d845022140700c071001c005520342843da0321140d4114451804180b14081c81c880720005120340c9681d1050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 126575098 1250 126573848 126573851
    0x605090c03070915170f15120d050f09061204050105010f05060702040f0e0d0e0a05040c08040209130218011d070207060e060c010606050307120902090f0a0f0608010c0f110c04 77
    0x541c48034070710801002500000c000d0b0140c1a6040c503031b8003034800c07a4040342c8403024040324003505107a502d0704a8107070040d04a42c60240419459062040b1402d031311000085201003000c0003901440c7d26450014940c80c1240a11810941041c0c5800c0e429a003044e4040da045c0c40210006000c9603a550701291003032581101c0000c0c3c6d681030b06500601424107a000c4044ca4002c45282c84030403600014115814401290511102a11041081b04035401c140788040040d900e038000800504100e42e001d900103040851520401d40d00f07030300056900944189088207480803e004001c0240c41c1d540041d507920351080460030350320300030800075075603a6030713213390b2081025580005241e51294000c440200d21000003d0069035110100688076500c241d8050000412040744608441013274481d81241550040041015803100300301c1c1c3c008984081c0c131403400740341d58004041001d50307503103d540e004164a00c0003180c004500b113030143c0503000700c10301d000910030101c0214828140c041031020f0741d40301c00c540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 126576348 1250 126575098 126575129
    0x403021c2102030901030f050c040603110c07060309021002010902030a02010315050616030e0306040f120e04021201050907021b0907170403020f0c18040b04020616060605090c030709 80
    0x14501c800c0c0201d55001207041054070100e0010660100043c03075160402e8074144085908000c100c0110b500c210342c800c1c0c045c04280801c3c09050311a030806190700a030320b82c0303481c1031001d1400309601b010199807006010a80d12030030501103080c664604441c0c0758943c0020041546140c01090302c510190b1002410181d8070880c0e100081204103d10001d490041c04040c2c0310744c1c0d5124803203840045044203402150900100703000d1450000368091007143d10846000ea0700080d60b803844050032140c149401070110903800e00c1016102c91001d4032241c164450103408552404007030042070b0001a20030b00c00c40d000317550018501c090081c40c81e0410a000d48560042d0399495400310b8980304004c83e51568064843c007400145980040c820a07016602001e483c4002c45201c100b03d604151680c080654a10b00030004004c202c40480c050391280c001342101b45400d0311046d185a0b4480c1c0c0c0001251640d99442c020700181c201480642d0b800300d5500c00043c59070510714800380810312144217020541e1781c000c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 126577598 1250 126576348 126576353
    0xc1a1c020f180307121104062907060b0607080d0b0105030606090603040606030602190212041a0306030708010608150606070209010b0d14010e04050f0d120b0609060a030902090c0403021c 82
    0x80854001e03c80701803201854540e43c0b44c00750006001000b0f0a1145040140100d1080032820480c145502c201440d07400d0015002400411500410018bc881640e140c100442949519004214191091a689030368140340b0080c402142c0c0580c510a040020a0081040549542d0212840b068007220700356101da40b40c0c0341c0b900c085e00882e00010140381c00800c00e80c0c1805440e500d0141a0300203502590320040b130f2083d40d0030031401140705958070703c621100c1500e01000c00500443d08400040c082e11402521041e40500396882c50b800048030740e01000d0496042c00048198a404c46002c803030320303450014140c000032040c020601510003581400601500058070301c0d44048100c45044290034455a900c000b2144298400c4405481501483e84591140c510100e2480000070f40b07500e03005022108600040e0043c0816401150824002c100c44070046d5034100c0501030074007442c0e41c08682940c8034411b02011520180050355405814801800141d0fa03114200800c5902c003d04071708000c8550 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 126578848 1250 126577598 126577603
    0x22805010309110415030b01060c030c0b04050f07080708010c030b030a082a1b0f011719060f150c03020307080a030204120515130203070509040c1a1c020f1803 70
    0x2c40721382c0710b8030b45100108050080e462030002c40c1c2c01046d00003070036a81d071a401c0d104c01454140040c00518066920000100c0c40b6100302d4105019000300d40101b05a1400e45280c04010b4000e4409507000c100300304a0b540d0309001d4041395410074602407110341c890a0100740e8070300218400070059400401c485888840420940c18010744248000f04003200315501c4039182d0541e0f002d400d40306409d000740c81c00c50b4200005c20b4032800e807060352640040301d200c0c1100405a440a48850050311170b81c0c10364004005140142800b408660101c002d91900d08215450320301010680c0380305001700000040c0c0420b4021050740c007040e0304801034a54800900c1d100b140244110b810107034441c400100d0700410b0050004142c0c2802000a0b110840c6464602501003205e4040c00300a501d580003000522a90a041420030342080c8618060280c0a0321440740c000003155820391307070b000c1040100e80c10384000080207000c4465110761104520740070011602201c18030034418403451500a900d0b540d034064908 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 126580098 1250 126578848 126578873
    0x1207020904170703090302040501050a0e06090c091e091008071707180902010201200a0e0d020612100504060b0f09030f0304060c02040e03030601021c020109050105070c022805010309 80
    0x260b80c403980c0c1c0d420040c0303805400c4031801d000680c0a503182400103c4c840c1425024076040d500e2030512000942e4130041005800e0800803c01010200103100d411030684600e1042d000542515440c3c0419401c80d40502210391700c0109800554882c046040085e000c0c0801d80c8800e6840e03d0100b0390b41001000c4500f442c0c180c0650005500700101684000000311a90292000a00c00da00910021031034081d070b1880741c00400661074040b4801c00a080c000b901401c1202e0521201509070b414806454000840e00e07000814070283c00c1e50008200a2442d40f000307907d00281000311010003c05082112119440c054003554490441c0002130024455504204500c07240c5104811039603916101d05004000c07400b2032000300d0241c0c2c240110702014800c00320035039101d094180d009050008942102e03000b0341001e00e1004c0255540d139904840420420b014003403280c1c1e0b164583c03040c07401003407041c04000002034403407418101e0600c61400c032482800030b2207011070b4800d00c0d0100b1083c50504010180120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 126581348 1250 126580098 126580133
    0xf09070c0c0b030403200109050c0d03030b040e060f09030f04051507050a12030b01052104031707050a08060102010b01080402060903030c030409060302010906020d0206060409080706020a0c0b091207020904 90
    0x2c048104820164046800071030b40108140c043c0314162211029426640c0e19840200581c105011840c000c1c01d1010094a409019242c045008400f20300441c0850346c20b50100740c0310381c000b04104482c02598074280b58109004400452070710b505a9802c0700700c2e006034001e4a12683c03000440d420540010401c1c3c404176a04602694003651440c60825100c0300040089008282411600d403100d40c000d01c20380352410360254040075407803400400ca521403100140210248010032001040345940390003003620800d100c0c5c071a1580d03500c0704000178180400c010301050441e0304041d00403240c0c0e64003c580c0c43d00f06a0580d070326071316a00e00c1000242140110640c400d694427001c280019041d406411401c11203000fa00c80081040d12003904036142c400da11800d10150f070244000c107580b03040070b605c010050742c01a1101c50038080d00d030761504140c0c0d10441c40b20700051600702c810403d1000000f074007a00500410010880707913108030405880c5004410b0040d10070000440080c0138041c0e04505144204c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 126582598 1250 126581348 126581369
    0x1804020d0c18180507020109080d06030606050402030108030703081801090308180102041a03040602040f0605090901170730080301060f0305060108040809030703050d03060302030c0f09070c0c 84
    0x318544100000300189000140001c50445000c102e03035480b50044400d40722042c0900c90024410110880070b400040d000d40700711740d40c54000e4404900006d024181e801c0708240b0200d51249141412000d948150f042184620720400c01001a00b80000441d0040c40d85410503507156500d040410315030102c43c0c6000070046d401c06240c0820075520064aa12500040c908180e04401c0065480e01303d001d14010344034150009a07018100d904c00201035940544228005890651560b4031441044201e80c80b190101d000410404401c0c507103a03a00390702500040300545807590300b4100740c0c0c0e900c00750b5102d010600110221070386080300188190221740490301ca8a5480d440d07441c580014194424403c55001444450300145818030a026050007003074160b50381d6001d600d580e201c00c0c400303602c8407500590500c540c1c14000001003091010740000c1c211510000740345450740c0140350070800c032046500c0c801e280102c10f05905560782680c06821044c186020602c0500c3e0f490425520207154114000c980c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 126583848 1250 126582598 126582607
    0x10908031602060108010207080a1d060d021902120f07030306050a0b040806071e05091908010f06080c0a060e03070e0a0b040c020a15020a0201060504020c010603060501060f0c0206180402 82
    0x2181105103041c16410240d0882c0c450707aa94252942c00c0b801541002024a0b000b0003600e102c0b41c0c45840d042c1c948550000303080d050b241100c0006182c65028a46203841c26801086079007085024a000074441c5a50380050040680640840c040e140714840008071001400f14400c405c1c94420b80c000c01c0079100107068000115124081d191468121f8884da01543c81094000747c050340c49007010b1841760914141b040e01000a010b41555581c12000c03201d5000440d4403440c44d03070b03040c050000d10010700010740005071044854040c40191a0f240c0c200300110703845801060456210600e9101c00c555092a02110941d1000006400c24001d58001102d480881003480202a100c1d44140070300402140c4c100840000d0034426170701d07020070003000340103c041d0410643e80c0f80c1c0c86800070f090341082440002641d544603000507049801c080a02d5025a540c2c00c0203004000356442140c0c01750030f0b2420403039140e400401c0024200e015404000303000d00f4001c40d1521010400d400d1030384040000030000e5495 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 126585098 1250 126583848 126583861
    0x7050313090507050c0c010c030c0203100b120307111927180f0210110a0c080d02031309150b03280204060f0e0d050a0b040605010b0f040501030e01090803 68
    0x2039035001d00030021035030b15110125060701e01802c21100424100c401414100d07401034010340e10341141160a07000e201d80e0f24000001a0740500204c0346500303031000001070000d801c2007440002d178210303071320f03070340c0030342c420004100818040d041e00550740000302c03001c01880b01c940c0707400d80031401180d102d50384030103039000002803101030200031010180203401c00f0410b842e4000d0410820140c11032020380f10313600c10b000c3c44000d424030842185954060703007084504012018480b6103043e4031490182c488800e504010301190b03a0030b005204903c10203200031410140c4454110200b03103034502c508242c2594824005e03041002400c003240084c00003805841d201d00d055141000032040111500036600c41150709003032144018802d8805451345990342403280c5030450341c03d441e042c5030910b26a40c40b1507141c2c5c14000040007000800c080034451494949941800d240103000d0311010381020181c40703801c0c000b0348200608003041c1c5044403800d280120f41050000f808038010480b42101030702c0b0b1030000040000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 126586348 1250 126585098 126585127
    0x504052a091509041505061c0609210c1505061c1b091e150611030403060f0b120706080a1a0a0306020a0909060302130b13020309070f0510120c05070503 67
    0x3a00d903601170511190b0b85101c100550805410b4114600ca250201e0090224881d80e000c040312900c62250308540108601c1121000d00c40c80a400c0001401020140104841404806580301c440c070b00034082403c0c134030300180e4110f206100c0143c440c020051540b05001c1148a11461159080c600e1010305403101300e104050039070102c158810002180b03000001d800c0c0c0b4400c0112101c003030b030072410b0201e081030011640c3c042a2100c0c40450320050101101107440ca1140000e000e4850b10001220a1800140f0080700c00c940c0500600d5084400200000c94100000541c01164a880080c004840054035150408101181e5800010620000c4104806a0300510f81a038041c0c49441440f5a1544500c00f600c03075032b00000350841d240102a06100c7c200790841144810024848217001020454100498004444540315644074403070401c81c0d1000c04e03082700043c050030350b49206904030340c00029060300342c108038169210f03a072880c2036040c1c0361080c4151945290701c10192595a50001001c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 126587598 1250 126586348 126586373
    0x3120f010f06020d0807111203090610050607030503220b07020c030106080f1f060e1e0a1b0c21020604050705030c01090303030c14030a0504052a09150904 68
    0x1c0724a6042007011a105000060329405504a940c80114a0b501c1c075400315800603a144242c035a034400c41090001c0d80d048540035511644100004004170303d132a8403048000c50b00d51303006a025080c10010300c00031942c4203084961045001a103d03d0b440e10041c41c6142040003a4000742c58840102d00f84a100d40d40880d420580c810200c00a0040e1600e4031500340d180d844100103014194440a07004101c0e00800b020006011007072070b00000c00607038900d100b9403014405c0b00c1c000d00c010548000d2900352407140703c80d59003100c0340110810054240068074017004840710b014001f80b02520f010b4400700112400c0d15800040080864813104440324030181d83d0b00f800ba10b0440359402912004075040c100095032018a510503035540800a19548040d00144a01d441480030090030100080e4040301403030007540a090020743c0002d82c0d01e45030074000c0c2803040032111850303002c501c1010088454507050841c1c40480c002c136a0b101694070303400312100b0000341e003180b6603130060481001c010520481c0c40641 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 126588848 1250 126587598 126587609
    0x3130c0905040210030c020d0c020607050d12240302010503090a020406140901170a03051c06150e0306070816120e010b0a12050304090e031608030702010c03140f0903120f01 76
    0x811940c0d42804c040d41650507001410b001a403010000e0030b03285114007010480140040d05151030300713040d034840e1424809603250480115000e00c991a03a0b40030326214240c80340f14410300c1c010b0078000000382049100311706d10010f4108600400402e201e40b0307080c4211500b09500400400c000d554407002584022040340308544124140c000004020f01042064542140b10134090400126250b41c02d83c3c04e60400000b0704507480340c4042c00d481c0c500f654403072100030f041070705041c0c41811114400200103000d40a5014060380240381405103264000002e5504410360300c40e0b4007201c1051700340441d81d40040741d466500003801d012050f002458103503c100790f5508180c0b915601551110f402424000d0701c2e4500600c44e0344100420081c070800b591052100480890a03680740c2001c1da01009125030480e141510202800024030090300d409105541031a80749040034048131003001c0c1d5041c80346100a182130410804000040c4038810144102e03010745044030104819414040381036124000c0074004d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 126590098 1250 126588848 126588859
    0x21060a0b0702060405040504031803030e09071e0e0f060412052103041220010e0c040915270c09200307210603030203190e010503040803130c09050402 66
    0xc22510412800c880d4001e8010780f0341440d00f442d11003403200910006100740c040020048040070f404800c0c0c100c3e1401540070342e480100f40e0760000100410108003508410170b02801d8006034009488424200d502c48000307040142c021003001c00401e0588bc0d07007462069228100190114002c0711011800390000d02903421a03c900b001c2803240349800e2081003110014150034000900091442c00180c0980310702840c11940381c000e00080c26201869440c0b05209076511044c2d951201c3c0f030b01704050b0322299400c80b414488008107480d401899921115180700d001e458010303d01da11038cc10002c0320040413290351110019021801c0400024038140195003010f03080c1150707450f81c00c81840341c226121001c620b45034510303100c4160541e070440c810248803154109881c00d624015180b446403d000354060b4020b10b83c1c5024000380c13500d201d80d603071500340d007844034041c0e243d1000c1c1d9004096030707400f0750f1208100b6a030340c44045041d0040700200600070051717610701c3c0010404000303940181e4000d0b40709455 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 126591348 1250 126590098 126590119
    0x60b040605130b0f1e0409050f041101020d230408030c0703030e19090f0605060a020708010605190b030a02040902161a190b0111032b0504051e032106 66
    0x25249500c0b81c484003c1d1103010900046131040c4503e108a032054045101491905d6a205205c7c001d50f80104d40081c0201145010002807024040c288201003000b40301038004103076a910060f040c5801c0402d0244510b0880c2260158502c0d01c008440250100704200da4840722a40303d150b81e0341406002c01c8000a069548120f42410952180350100c5c42c81032407890828102001c101c02071081980704000a07440348000221610350500415540c5040d82c003508509007000003070b5081d6102640a5030182d55150484d400022240840320241c1e0312801420703030b60303807983e0300c1e07180280c00f0390703008400d100d40b00052540000c0400d500b2400d2103071080c00d00c1c1c480b04515280b507115012040341d50341405441c0f500402280d030002d1b800000d2070581410000b520407070501080d460354000b213828410800319000000760701c0301440d8040419108202c024401840c2661311b5a484040200b0003600118a481d640210110188240c9945800301d04444841000203c40280d1101050b030748540103c49820 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 126592598 1250 126591348 126591359
    0xd180201021b0d060b010c060f0203090c030c0603040b090a08030c07060c0509030721080c01140f04030509010815030f06060103050703060e04080a05040803040905190e0d12060b04060513 82
    0xb00700d0124060010600301c0c09400b65180e46003d011040110750400c4480000080000c84900c184940d1030251300b40103841c1d1419207442442d01400942c00d40c0b080d488038692080d1036580004680d480780d40a00c96400a032585400e1603e8004600b800070036201c03001c000c0200103c0d21304040c00e8140d000da81c0520038000b809074295011300c2450200c54141d00b002c40c040c0400508844d18104000e820780c00820070101a455148841d0411980c00c00b20b039448034079101c103003030484640329003245ca800b044501ca82490b039009081ca218100c4014140700901c000a41c0c441e4070800a01881c440c080c00355082155402c0a46888282c1141c03c0c5000c2403921020074980d500c280300303290aa0321a52601d042c151201e0304c445d4816004011b0500802ca1b08000c04951000f040c80504002c2c000f1580c045900d092040c0d501e0030900161451100e45468070f102107440b444001164480b144c00e90604d0348074440c2c1c550000000d4030868014410b003078000100040c044d540720008041012400010f0310405d80c445 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 126593848 1250 126592598 126592633
    0x30f09050409030c020d080904020a030603050c011b0f031e020c0111060907030305090310150806010b030f0103060906090c120b180303010501081005040515130908160203030d18020102 81
    0x302e010b40001c29581c00c41c801804c1040740104098003d100b030038140650340d00014140e902100c220b0002030344800e41041049410071420070f2180b401d0030310044541c0c00c040d0f0010270643d0484050404a8610601030a0501035042050003020b18924151300842d00e803c00b954401410b0b580b01e00081070143d108a8901e03010032240d004d0400280600002482c640f02111140c1000c003010368580203158500c03041600d207104039542c0c0c0002071100d401503480e01000e00e04111050380000311104c400c008000904c0b55071001141901d07400000001c0c0e01c00c03542040c800a001c1d248004208404002012a4511724181c0705550b2a204403034412a5660340202c000031405551440500381e4401c1c0014082503002d0500340c1da000079101c000a0f4030741d03520750009090b91001d540744442024000305c1c02c1441e0608a00310010010305020500c0302040c43c2d9204000c62041055040d01e03125000c4040003155018001c50707a00000002d014000115050010b0300424501c40c0c0c2240940f14041c0f0541c200c1841 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 126595098 1250 126593848 126593861
    0xa200604060503090c010f140c011506020604140d0f050309010b12062d012c0a0c030605030309030703030f0c020405090105010504050708090606091e070914040e030301030615030c03030f090504 85
    0x1036903c0c500b1a03075a8150b108d03925002841e25107a15500d90500c00c1501802510842c02040b4507401000d9a041c1801d2022094044000c1a80113400004100f1001da401410807038800316a4a441503a0340d8905a0707490041c14400e044a030301c0151900810b12041c40064036601600ea4003503e150084110b4401c002880030064200300010064001003111482806000140900d81d42040340c0380c10701c0d045131540302441200c8600003507035900c0080260b19030511541d405000c00f03800840c60681c103480001d50b20002440028200120071035890121031048094890342540a00141b009090051003640038090900035903001300d02e0800010b05207445801e0070750140401202400230b0303455410074403010b03450081442c0c120384850902a0110f43d000d0500034800c2e149a519000c28505107a1056411800c44040d20320550500c0c03103001c01581d012046a045941c0302400051080400c0c0d804403a11800b6400600701c05401a4004140340d001250360308000c01da559980300c040e464208010071540b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 126596348 1250 126595098 126595127
    0x10f05040e0a090614070c03030501050111060a1119031a0108060603010e040809060301080a0203160b040b071406070503010e0109060b1209070f290307020a200604060503090c01 78
    0x1000e00031401d80b42d0b0950040f4141070240b4008034135a00003030100307862500146d4450002540d100303402002c3c50b42c1840b41902410003464040e4564810041e00c595541000e011880381035511100003404511450844019440140c14102c40c0d122011001d401440c0c0b1041c8160601070506990320158400e610503442108003c1c612402c40e401c044110b26100170081c412110b85404010a5846943c1c500141d40203280b4100204820031461040c5410f00101ca00308069400f0a443c003440f0450a59054a00f6100c454150075120200ca080a5900e804a04d52040703242c00b800b4140040c85512100450603039011454104941e6a610200300031144a40300d20401701c041030106012200350001800e400806d01d40441d89002d488500340c0c09100305540c801078106a49491029920400e114941700d0807000710406821480c2103003001e5201d003403130342005282a96200034030b03050303414401d900d159041d005801d1a44a41e01c03104041c060b80e000f070f20300400d1442200601c0c481396214003c034104030745 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 126597598 1250 126596348 126596369
    0x17030903121608030f01050111010902100e0109090504140d020f0a030e0f040606020609120c0d0c0203030f030907180b0a050103110702180f06093c040f02010f0504 72
    0x100740c0d0001c407550300302c407058021080030040a1404680544003841c010b000036004c1d20b86a514050000d4404900c01c1c6040c1d002d0f0741008070000140c0e070340410442c1c80f0400c5040c04000d400400004072503001003070300103009552404c402d0005000f0a04550704100711000e045800c941d64240c416a03440407461403021099105004660000f84101411025043c01810714040040000000340c2500d1040e000b40c401603001e0704c10004d0710380d000c001002110307101c801d42c0e52a00c11744103c80350f00e80b0240b014881c1441119000d030b0086403001c0040380e000304109102c280d1603040038035081d500c858103449031944590070201c40810340051442001c0100000034612035009207400e0055000d0001507604940b05407040c00341002584800e80c61241a4644030300545080c608150b00ea00090800341030180180483c0b01002216100301c00720200e00c005000f100c642c40c901280e00d00c0074400c000560800c039181040107003c100a1002d0075240124800d0301e6028050503807070030485284c01144201031990 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 126598848 1250 126597598 126597613
    0x604060b0105280e030a0f0302070b040e0a0504050a121e2105091002070507030614090303010303050702040f110705120c0325081b0c040b09042003120417030903 71
    0x207010b050100710fa11201c0c1c188080c05039030100010341044080d40040d1258509494a00200755050040390040d01e070070102c15041504080c055440c401e4020551200c4a80d581d01186c00d212081180c00400c9501020101240840b2280103041c0f0b03000307414100c0c4e40c00c000400100001d002c4d83c0c5100c88179601c0ca45a5a401030441c4000016090207081510a801068410200030103030740003c008490180c8024031603580ba40ca40305040700c1c2d2112041c50241c451b0070500c00b0070040030088904482c0c2515041c0e486442a000080042c144149003035040740c50020300031000b40285000e051618003c03019142d45903074003550441148610345048203160020049034051030b405600e5440140000d651204001d0070664504425a000801d04020301c00003407541c030b01e07810080203071220740d0b04251024415000f680e00030802d40e440140004004070846c040309151030390102c2032507200042c028129030001815100704407856001b40180a00e692144010400018001003180c924030b0f0f010f0011f1030807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 126600098 1250 126598848 126598897
    0x507030b131a060d14010b0906060901081308090904031e0207030c050111070b160c060905031b040f06060525050304030b090f030c0102090405070305070c0803091e0604060b0105 78
    0x50b8840104000e91040c25101c00501280340611066044000c0b170b00001401c81e030003410040d4644009000601c20300c02004003c1d03243e680801003c0c1c000040450b02c000c481114640380b222400f03001c0308035401c040708008000506034412201d4070700f040301425400c0080700c501e500320f0301c5050318003025103400603001080006522444401048000030021348242a0300d40c1c3e00508194490060001c1050018150320240200c21007850000c0c01c6e642020010f1600d04400300fa207500c1e10702400070010070032040d210040e81305d40e00b22130310340c0343c920204000b500d840746001741c0190010b080301034046159211000a1465111400c50180e40000c021350a051030b40d9920140e0075401401402540039001030b61400f090200041e10800411800140c0c0f1803101c0001d0200300c480062050341014244010701c02017a0700f01200c918229005a085942d07507640350041460b0160100c040c40100d44c03001001d00382054081459409684124018400b4410758801181c2d580207011600c0e88859100228050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 126601348 1250 126600098 126600143
    0x10e0411240c01090506010b0a0f0c0614091509010c0c02100c0515060102011109010518030102090a090e121207082214060f010b040e13020d0507030b13 67
    0x25015164020100441c845018105540c001c590640040ea443d03000034001c02000340100c3d40940720a60f411820724440e0940100545003082d222001d120f0103170a24014001c1903080442c1e003241f0707032080704170701d061200f03a540d074442d24107601e42c4045602c200425000c2034103014141002d00541c4e0780c010210104d4013007061000da081066414020000402c600141c0140030440b8540c80c0c1e401c0342c0c940b5290035800a82503401c1c0764400c4040f404200424001c581c0c200c400c0e20380c6190000400a170b0505202d011a009200c0c0e040d1041e031210450100080200c9503801400d5584001d60544580d0224200301010034061841e0034151095144001081c0501c02c0d615942e10880d02080300a40d00326800310340d0909000140d060740c441d6450251100f41d032004102c00303a0004070381c504480c010342c034161341c04d411800b481c0240c1860790101d20101300200e170164007207111590010000b00080420b450081e82d142e0b071a00c01160380b40c040800044040f04c18149a1044542002c2045021b046084080c0c1c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 126602598 1250 126601348 126601369
    0x807021c0e0a08010617010f060608040b0a06170304030c090515010c0813140f0d02011e05041707170604021c03050c061911030105030a12020f0102070302070e010e0411 74
    0xa8000c41500e00003d40900c0c00d00a120080c0040214040e0300300c6021b412609440641103150b0080d410184200b18050b40b0115159015400046208898683c501303c200030f004250300c4650503080c1100001e001c00703000320042045912030300e64040f00c540d03128900c00075200b00311001c10400459003000c410740c5d40260199480300d0b00c1007150310700e08100c0940082a00c4400d400c1030520340004001c558079820107050341d114683d82107402c4401d005040c1d0000b414400090203030302c503000040c1020042d8030302078400e403800b805c3d003043c40031241c84044600581c0c44186200f0349800c0c10300c8012811200700c000c501b550066801070320301e50301411034428001100e05000022410444200700080141006205080c0146464502c02e81403170f0195038050f0688201301041c1c1c00c03000b01040100711170f680001c0d803800c00e00d62108c0d0b0500040d00001082e8208003040c0721a40311540001030075000c1690109411701642c88d64040d0810707627600d40c00c0b42c02c0040812140109061803c0200c401c0d2842c00c001c0c40c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 126603848 1250 126602598 126602627
    0xa020307051e0901030e0a05060105041104050a171507020d140f130312031406130e060a0213060801050f0405150a08070801050717160507210807021c 66
    0x82c50907105500300d240d40425030094901e0840041181c1c0300f03569245c05a5100d07440c2c6180101100c0050f52207080d260681845070360310980d41c2e00c00c0c800d41d5840007015034004000040c00001d0155a4140801e40c0c0150036810111038050400031103001b43c40002614050304807036000300000a41c8460075184030040701d1400340d00c00c170180090140c90700920700600c281d5004a60003c10f86245103030107040b2100c0f500280c420f1606115242d0036144031880003c0c1c0c03101089400e6480784280110b5840280403200b0400c0f403a000d4a0f04001c01b140743c94009180c0700f011180140c60865540d0070494024400b0b00a4039401110003503c421249425044240c01c11580c2c41c4842d035083c1c142c800030301c2c41c0030b10f9130000c0c4a90300b1800d4100201202071040960001c038074189002180244980704104039070013486403460741702c03020800700c03003501c241c098404165001030741079100d00d0b100d81068411200e10b8100070000d03003900002610148089421182e03507040e141108060f103d000d005072200c04540c00c08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 126605098 1250 126603848 126603857
    0x7020601120303060b03090102190203180603060406030203190308100510030c0e031b0414040f021005040801020325090b040b0c01020d0906060302100905030c040903020c0a06030614090f0a020307 86
    0x80b40217044030303008500444504000603603070f483d44030000307482009180c506820340d00706018002061101080041000d0403c440b80b682c2e903581c00f00010000c104540000c0d426100d00c03030070311a40948948550018901a80b50401d0550303444c40e0340350400c10036014507500071080c0309443c6010307406604141040d4003281800d111100c4841c000c17910305450004105e02c24003000380c00c1d204c682080c0c42040c40310540d05845042d6407401d9160424010003072400240990940842550300502c5601500c000d00761900c0290350b2414801c400c0403e04e1580d40503810b03113107640418400110300454200341240c9540100f58241031410f1560383d141d400900c1c503031200d5502040362110800f401c0c400e16400c588034250001d0300d01e0850051188281c02214880300303000b0190801c0c41160350008a0007094101100c003c603ca8149190072810030b1440440e41c0d8000d4132005c3d011078000d4040c0c20010079914811071001c0110542d508008481c8400c0e51011116010308000c9480da50f841c2c0c00444c3d2041284c00c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 126606348 1250 126605098 126605111
    0x7020103090b07050307120b0307061b050102030c0318010203040203060a0f09021503090c09070e04050c04050613050405090d05070b091603060f0515090619080106090203010806070807020601120303 87
    0x26080d4812600b15a83c10002e07400100b00922035810452a18001c0340021041041d032241d030f000b0a558001502401c0c00b0f02900c40041c22000e850842d50380241c07035111000b036441e0300301008502c403503030002d4a4850307a80d000c00d0a0210700d1501403003603e2207a9001002070400e502d85800040043c2a4401d03110300c1c080c1c4030100314000d0b07218084034603c48101c0c01d544a9403840c0402030282400c0741056000e1003400000309001100303030702800703008503501d00300c400142c0e0b600d0f003202c0021907104550109800240c08500318030450f407100c1d0b446007160700039038040c8050366a00d40b203a6100d00402c0180d00104405100040106c0d103514011688411808102c5009002400a40d02480091362040701c40c9030701e1b0703201c404c801d1545010350798110b01d40c8010720756400c4042d0f00140c2008001090180252307220315a206411822590340b03c020440c00000304103143d00e034802e142c00703548240141c10851088602081811740b05164480c441c030401d0307010b04201d90a001280780c5044901074194101620740d503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 126607598 1250 126606348 126606353
    0xf0108240316060c060501090c0c080a0e0d0501020901080c040b22260c0607151e020409060602010b0d080f0a0309060f0603030806120c040b0102070f081614030a080702010309 77
    0x1081401034442500c403441c075004ca503d080380540703905811450181703003400c10190441d030300a10b1141d022a8030146c1c25480e8858411304580d50040c03802250f52042000c5401000d00c08191f0080c50030000c00c0e130b01c104840d5500031841045104500c11803080c2c00c0c040000d40d43d20302c0710700d4850349440b00003c4582e400e19a01d019058590065004448011030455800c02d44101e0400540c100c140098038020b0415409403212403d40ea0034910107003100b500c1d803414058440000e45240079440c0c400c14115101d039114000c85004040e9070080002561030b04003420a1031078070003498041c5a611080312850300e51650581081074100d940050103060300e401d400c000140c0b0b02d01451205406d00c03100041c4007441c5040041016070701074a0a80121115013441040100200c0c0d0b2a076181c1042d900412081c2c181d1300101d160842a610440100e4042800851403440204040d44803202070468000641d440d40380726613038103454404150b03050344040c0b541c0b000a049030016048490050400141707900164 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 126608848 1250 126607598 126607633
    0xa09050312180706030c0f030506030c031c0318120509180421030b13050907030b10050312180d030e040219030e0d09030b040606230f01082403 63
    0x9580300e912aa003415003410000004101c2d10004241364070b030a00600c051580050701920f4190981c4007010b445000048480e10100003a00307056801800721128080075024044000c0700c801c41410000e801c207503480030b0818445045424107600004103a0f00f00500150a4819502a03486141c002481c594002d00a0000000032446980906800c10b1508140321400c3e4560b00310a0f03500041c10318082d11a0f80e00d4079820046020901c510000003036a0b01c5d40f81c1c40618002c07440d4002801c1c9050102009510010410800100c0342700398102c884c03600482c00c200c07865000d4016100e03080210890041441e150030401c00381d88502030300345502100b084d5404142070f0390008401402000ea0f45498200099046c4240034080345148080d014610a00b4401002c84210303120181280c94040042018089030384c3c040e4008180c4801c00111814440c00d41031103411201c98001c0c403032041000c100341316501070002284500400120701206240c3c082c0300c1c00c903c41d100311047e6018400c07104000c9684012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 126610098 1250 126608848 126608851
    0x1e071502070509060a060806040c110f10060807030203060c1309020a0f0207060806031b0f0901060f09080d050405060c0705030708030711030312040201050d230f070809060a09050312 80
    0x560301800501d82050305100c1582c1028207054010b255050782001020792017a40c0f42e400100c2150085080c0035284d00c1142c401c65541404a0b95004454050300403880024580b114074000c2141070100035541c920007a01c17480c0510000e034040d0002c00000b10909448070080c0480d08019032070105150b01ca08400040740c01c030241c100003080180040d051001d804102c001c0042c21149492603030ba00d000c0021a171205901c0d2003510118800381410703012a0703a144890b1130000405041610250380d105c0c40102110700e4000c0c003030003082c0000004a580b90b004154414007162035103030180b400d460b1009000d229400255903404d0740c041e1040c00310f90b0355020320054004004001c02151108600e060041d440c1d0284090300e0b10039413040102800c8a10502c0b52554001e80900b0040d848160b00102400603001c40105010045c040c440c80408031145500a10b0080e4030040d00d0242d199202a015540c0a806131025a00b6078040400207251002a41016205500c1142500d0600164406002d0720940 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 126611348 1250 126610098 126610139
    0x703050403021e0712080d11030f09010908070201141303030905040f140604181a070806010804200301140c190207060c02041508030703020105091e1e07 67
    0x11104180030515604021007030f88070003446440d01110160304102a600c0c0310500c03811000c401035003400350610600100b658900900c0c00d44c2031040075054480036085500454914440a04900116004550500c603d24501e0703440400350f40ba0040e80c2d001941d8080c5a000003000c169401c21510180d40300000c441d90007103200f81c462020780341c2004101300c1a154405608100030b40b41100d800482e0141180807030f0885400d950010700d06921840314001c1502070100500911100c8642000e400c4522410038441d05284d601c002c0540c485900440700400283d9018001c005000f21041c40c6c085410038000312403000500001e0501c80c2820803c8000c001107640080c910400300f0440211200369414404480ca5807001d081918203011001e81016000703040640030f20340c0c6048003e50402451b00040c0600f85140c201c030384074106071600902801041381c66140e06e00444441c0d800400c10b13000b10241e00c029802c041c014040801013080001d1000e41d0300e4009500c04d0710f6001582c148440c20355280300300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 126612598 1250 126611348 126611351
    0x115030809220f09110d020d15150b180913060b040f090302011d030408071a0f07060f06050f0604030b2e0906080c060304021002070504020412141b0d0512030703 71
    0x111504120b1045078859a60306e01804410900400603650001c0c1c50031126400f540200e0f803546211036101c001e00d410340500414071507140011440d02105000390a680401e85d40c2252101098000d000511030203807000c09038010703046a00f03000a90b860700200d8281d40090400900e6607a11001030054980320f0074282c1c00f60350344501205048074800c0d0410190704002004515151078179204655408151040d0000060b001c08544150b41c4010100c07005002201d03000c6031188407601f400d000410540000303034030407858800e002406080c8103440303040b101002842e00c0e08191854588006591005080282e41803d00d0107210b0450b020b1581140c050b40764450301e4509500b800001c400302c0d00c03942c01443d001c0d8402801410503985d00d10840703a1255060b41c814102811000e000c2c0d251801540240d54080c0c0007150119090302c00307125040b20350780510344203440c0c0d22030780080507224101c02100e02440310791400041c08908110b00c2c04000c2510550440740c2545000d0340c03818840d00b003601d2b001d0009 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 126613848 1250 126612598 126612611
    0x22d0406021c0912080c011104090c03090507061d030102210f150d0227090d03020708040506030408040b0a0e010906020c010f0305091002070809030115030809220f 72
    0x19541007001c0d60b64000d200040000000640001070080292403103014103201da090548420800781400b650b0080e1510300081c1300d00b03159541048034a4000d400341c01c40c4030345800d6501c0b810521a024500610b500039011301a0b06040204c05c407241500d9103003950074840714903e2280c076030f1400d10013001250200c15409084400113202105070000141c82d18a06103ca503040c01541c43c9100c0074034104240448040e040c02060384082002e882040c3d60280510001390000e440800410710f0340340c85940c0c1103098900303e0714101307400d0b03089000d401409004564180810710050914070011500a80291a0a4203003695400b88103100e611443c40386d80000d00045c00000196003081d004000b07018580060078189114600080ca10304004c1034100400d40ca80d00032804000f018400000e14160410040d5030f240c82d542809912070f800400702502940c40c1071300c1c08550181d401c00700b00503694000196840d10222600700107915441007440304401c07074610042d03c0490580d100e000b00000590b42d002c03030039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 126615098 1250 126613848 126613859
    0x80a090302061b0118050c01050307170709170d20010905070f0905061509010804060e0d0203130e01061d1309110f010503060d02040509010603080c03030a1b0e04022d04 74
    0x94030400d40c44014605c4500c2c94540001d03101251301c421008003882c0542d200d0351003127030850b090034000d103812448286200c1405816507200f8074520a540c82d90580e91070340c01006590540c1e51100d01a1000000c07040e52141e031100d44000760450307225540d80c3c00410b56613150b4580c0740c1071011503400130403d425498420880540540100d980c003070411554202020b0f0109600c0c004d510448800e2410040902c000134100083d5502450700c1200314000c41d10854406a00603540380d000d101f99016051102e00d0014240341285c28940c183e40444e651088501508002481307d0840d40e00020b40c4992041510103110b4050704c0348100d040e026104180e228041c00c014410071a0315240b203a0b041010410030000251140d4469210450b410703540002d85a40c4d0a0300d4900404241c1c0008151800010307400c0074402c000005140540d0f10350364204124030921040303040000000c48400046200807602281d03501d41a030142254111001941c40745080380c00030744082002d03075140703921362040101c1c05009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 126616348 1250 126615098 126615101
    0x9050a0b090d02160315020912010213060e09070219060e06131203050105060327030a0507050d0320030405010b1002010204080c0102010b06030a020a0504031406041101080f04080a090302061b01 85
    0x401300c01024020120074150b0321001020407007510035280c0250005852191600c4404445070106811002151121242200171281c1030080c81000001100807005a20618002100500032020f03600281031818002400341c1120b0950740c400d0319550340ea06024003c1d0501880307c00c4c81600b8203220010240c40034a0f00102250042040004141c64540180b0040d01c1c1c1c0d10440350411035195244070410074550100110702c4603020300400c103004c041000741d051074126010700041440781090b03680d541c821400840c1180c0c00785401052503006561038249115140c0f00542e0001e008100100e400d442d0306002c1100f090036080310b41c006039400a81041840310501400d405044240b00034000050442d0014090707003c05020720100c198001130003445140510f0417180255400004108a0b0481807031160b1902c3e0101c40540fa00c020440c2d00e210a988200c00a41c4202200c0c07610b9802c0f62070b01d48694940d0b4010b56403803420301002004c04809a9200401791846544840e00c6040c0e055690140300d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 126617598 1250 126616348 126616363
    0xa0602120402090c07170309030f0705060601110d08010306020a051213021e09011418040305120c040501200f0a080705070602010b0a090f02040e09100c140d09050a0b090d02 76
    0x81361944c0921102c00040e010a0401c0410a41c0c0c190041d240d86a400f5200d003148600100060ba0100004600082000220300b0b90b04c10002602c4e00380724100c0401d00b0503240c2d0019405040003840035030060002450300c4d0b000d484018424130704103080c08500e21400602160540d954085d028240b0411403c41c81d050381046449418a1174601c0003001c2c003804240c2e480c0c010300031054000c039140c8440900e82c03100304d032080c1c16588500ac54665820726003405081a8030446041c1070300c2d0343c500005080c6016140032242210b01c10b0750740c00140f200040c80000f04080d401d91450041c060011106005103041010100050003486100d03602c00561410500c0c28441d43e10040542e410705080c2007a50fa228000d040c200d60710366102041c00c050418031007000780715a4119000787c409001c2071005484000440c4100303607200070010408503800c0001501d9225040144125444003001600c8142079690400c0c103001e0f109404980b0021055030b80c1c10303000142180d142405502c0a1904c0030003540c100081d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 126618705 1107 126617598 126617611
    0x10905160305010b060f0406051b0105011403011b0801030305030a240504050a0506130902240306180910020307050c010c110c0406080703020904050a060212040209 72
    0x64003440300c150005850540c1381c00d43c074a5590620780111080e00100d810380a04080c0b9103c0c1c1210f2980c0981100e040c43c4114105113a402c0303409001d12b41c041e0003c25495440040180203140c00c440c064120b02c81d0550849460b80346643d0032100d41c5055a41521b0003641c3d0340e40b0421010050048801c95030b07100c00b00503044000b00e20a120082d403d86008035404c0c84652150582e041c2520029580345070701c2071141c0d00d070b14444179050b4400209c3c20300c0640400d5250400c00a600e1140d07654030a0b0742d8900600108100251804240e400c000403019040880303241048088550344807208001401c1c0e6a60003c042024240250150380203511400001d11040c506044000d11420032608100014494a00d0301c061314509401400c0a582440d00200052481d54007040841d40c17011348117031018002c3c4128800031450500040003101102c0e8080e40c200d0070075206004075940d004000 = true := by decide +kernel

theorem cover : BRFrame.Cov 126438848 126618705 := by
  have h0 := BRFrame.cov_init 126438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 126438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 126438848 ≤ n) (h2 : n < 126618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
