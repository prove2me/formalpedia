-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0258
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:47:35.254823+00:00
-- url     : https://prove2.me/submissions/28eea5bd-ac4d-4c7e-bd0f-45dc52c53251

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 46223025 ≤ n < 46402881 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 46224275 1250 46223025 46223041
    0x11040e0303040f0602040801111201080f12160f0308060a05030102090f04020d110a0f180506040b07051e030405040b06070206030f13050a0c06030e0a022404050301020316110d0206 79
    0x4440d0726000e00b4001d1b04203611044520300312940d2102c00401c1d0791000a00c085600c0d4035040c503e0041182401910886864218454548180b041c00755406440026400c1c074403c044041406600e4101031780d0800c51a41c0d180c0644100c0042d00c103176106804c0385000084a207014000c460140e13001400980780045d0ba21300f4440070790801400b02100c0354480000c0c8440070600c401818080c1c0384c6569160004451071405400c041e01d072018280140c24499040c020761719000100c80440f80100e8019075260b00904006040018100c181c4c1c0084040c1442815404e2002019200341c0300104e404205804000c02040010300c50030320000e4210a0078000540079845800d40365500c942d4601c10a1144a910340d101428a42c01c40c400711240c0382c94030800e1290503418442c0303c2800c086030000b800152244d8000542c10800203142c01c0c550140e50a6089448441100380c4000f440050005c2d034072410890744c440749400000740408001000d5000c52050300c9000201020310004a0b00034001039210380034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 46225525 1250 46224275 46224293
    0xb030a12030905100236060306121f0b03010c170a020a1e03060311010c02011706040b0604030501020405030c011403011401050c060f1603060f0b0a0912030c11040e030304 75
    0x9003d94080c00340307540c0301c0f20106113400105091015514081c08180e00141d0341c2011000504010709469503201a020319a181c81c0c0171203801580c200d48076280702c01820741c80c51600070704a1503140c14600e4542c0c0041c420301d498105402c4554204d000384550203107484200c81c000c071000b80750704541181c1c070045940084580c3c01407035681054601158189003980340307030301c42c07a00316008000043d80c0c648003042407001c250380086c40c004d400d20b8004564005500000c0c00d500d02580190b44604c814000325032140d40c3d940c042d040b4100301600c103540321036981c10028000c1d082481218000c1c01044241c2245601c50103000c603812504e0f004a80c05c1d41d08000e400580ca814646c0201c2c14000c0402040000d0141000110f105240e84584590a45800c01610240c0581d81a2910902d1309101040c01608a51750410b4140c814103a26103803644039811080ba001d00f108d81c06210686041101c04040c164024410700300280a500c5a04000131644148070071100741d89000300d4560014008200041c0c081c1c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 46226775 1250 46225525 46225541
    0x5090c03060610020c03060f04150e0d080601030b03120301080708030c07090b030c04060902071401110d0e160e101202010c030e041b030605030f0303090c091008031303020102010b030a1203 83
    0x48100d0703030328001e05d20200b45018003e0f200225001000010003040000c43d1344403030a40141251b0074401007240100c0541e80d901117407842003d1040031400a0690f910943c440c9500640043c00c4a00c444031080c81c2040550080c00b81c02602c0c01050400b1420f00e400004031000040d034100200242460201c009000384a900d040540c1402024146122a41c0f180640000f034a0800300050343c3e00c6552800810210080100300003c0e410010b401c10014a803d0546820310008600468104a0300c83d05a00703010300b21400d1a10082503000100301d010715940382511480021201c03005043c1c17180942c0408000d9000006d0004400481110009101744541351140f6000703807000c25107223070070444600d1402183c010a000243d4618080045203820000d030236075114100060f5180d810103255403915a070040384410701503002180480c44400c00445211300600107001900c3d11140d40980300b00c010280c03444164010341c24142290850314000c5101a41140e01c286105d8006d02c10102c20f4000d4440a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 46228025 1250 46226775 46226777
    0xe010302150906030103060b10081b16021807020d0c0c150329030d0c0503040308070f050106060201050118050f01090c03020c01050c07020a0b03010303050d0203101d0a05090c03060610 81
    0xd0007900d000f61240405940610310808000c01e18280310000d016203142c4c0540c0d403000700442082440b081128807407103070201c0320350101c4250303a54481d0384a51900000c5100c00035000035084046100602e0200700544c0990140e03420390b804170503201401c5440b645074003005060204003ca003005514081003880b04c514101c0d042c042440b07001c001d440183e034411a414102591114107890b030262801b4440c0080300d03404c50811034200c83c4140c40341d0760b0700d01603404002c2040c0c0b8001101c0003404000240003440d6a07001c4000e04c881c58550100034003800003849103030034100c0c40d1420015505070a0007624030450b8400880c08161b0b10789101d180280c0084000c5100340340d0b0030800510078103028001c4c68400c40300d0b091354503900c2000380306000310420560b1084404000c00c1c401400040c0d4003000311461204550005030b1262648250510841c00741e40c0301c00000d0204c3c4001142030910140d51a00c00c010500c000c0080d0f0341d455a80e19182c4500401c010b40c55000080001c0403480c0602003401c0003882 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 46229275 1250 46228025 46228027
    0xd050a0b091303030c1d040b0409080301150207050405070806041109040207031e110a0b04021305090a0203010b0105030105010f1214090a1205090a0303030b041e0c0e0a0e01030215 79
    0x284901081801030142c622030a50010040c9074800d06806000c1c1035082e00d01858002056420704040318004040e0060322442039032174000301601652940c2000480341d4000301555902d50395a5000840519000e24000c050b000726800000d86190034031841c4e11841d925200c0b00400e0351103000b004003c100d248040351510809002000703a07510b480c03014141080c4203803074010b61000351511505803070503881c410030100032047d414000500c40201e0749121695010009000300d840e1840001c01c008048042264006c1c5040300300100c0d40350010b1481c000c0e81c001e90082044084078001120346200900178507002c2448000c43e00045480380749500301d41c41040c6000034030108000721009186005680300807455020140220520075081c09204030422107041252a101806010549a004a200180515544028111703550303e4a800803c40e1582c0c0c240c040b42c0a98104503880000c064184031940001c2e03803c500010313a4103000c1051419030b80b44035090300c141c3c0c0c40e5508001d0380c5901d592040560043c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 46230525 1250 46229275 46229291
    0x1923030c090f040905061608010806060d14010902150d051e06010c03021c0c02031002120f06030a0204050703150503010203060a1202030a0c0602070302090f0609190b0d2003030307050d050a 83
    0xc4240306050041c00035807031b000c405440c44080202421012b801c40703490340c0c12110038040c04d503a031144030310300c036a44c8591900d920f2192440201c2c010162500d010303412801c00c200d002d51240503507008142c075010341c220070015a2107101000b00c00756038811100b4583c1c42c2a42c08169698050030b048883c241c4688103c0b00011001d0030410365540d07a58403041c0115500001103000c41ca801d00c80044540c00085045003404c10300080b04a0f45d00c400740410206041c6a07002c102c0d240c03014080c1140c1c16802030700c01d0000e4141400000e00030462000c440700300c034090b84404039607460180203e0340110001003228400504043c0740600070007880c2d01c201ea2500c07a0700704840001303036000320f03000003400b03250003a040061450050007001200140321002d501e6480040040c44e40d40c56040a80024030010244c00c403100340c040d000c000b007200b080d0301503100811180190030480005001850070ba01d240240040302521000d25070340b804180c6008021a1040c00341000700c028982c00158400e91044012914038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 46231775 1250 46230525 46230533
    0xc15090a1e0b01051002071e08030c160f0501020604110402040f03031205070f1d0102011e0207020414010e0c0306061605030a030b09190e01021923030c090f0409 71
    0x30001401c0c0c001041808124001485402c24003140144002c0d0b6001c60720800c0040d0082d12843d07180a161304501c07079110426090600506080040c1150741c080300c2e44d62402a41d2a503076600f8030060040403e001c40700105800d10003404250803a032040c0c008040359221030392240040512243d07100c5d0044c0d801c0c0300001d504182909480001c50180e04d806540d80e00290303144090303800080105050001841ca034070211a4085108440b2180c0710b1305100848900900403030143c0580100300c0d803d01d4105c0c400d4101d80c07855500600e0300c1882201d0070401c98140c10600404120244156251340d942c1000242300e050161004681c0448014002890550050741c41030740044203407010344055001007050711450790503106101e00b101d000c40d00e03260035203000d8250301580034407400c2c0800c0003600c03000034228034402501581c540001c6c00c1110181d803854401c0c0100940030f840041c1d2004a18882481d140300960350840f030141018050507032421114400780607040703400c03c28061704256102c3c00c0d0404a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 46233025 1250 46231775 46231793
    0x240c0312040501141303030c1403090c0102070e01080606120c0a030303020d0b04060308041806030f0f0213060e0112080706060906150503010509340206010f08030c15090a 75
    0x151800345104028102814854210780800194244c4580e503c1c1c144500700030710609205186625181c081003c0d00400000c0740c0000704c40102440c100b5020040c042e62000114030403c10703070380030b908440d00155075200a900001d003e11800220360050000308500c0e00b400044c1c1d00e03014810380103c41400704204080b8196501607401a0000380d4003141446201d54a8020b1054001c030485041c003503e821515a00002d00c118403030103640b42c4004131118078a014940100b40155080344110328600840d0034581200e045e001c8040740701e0b004607016226000428400d04095078900088210141e080c00c040d0280b03004122410303035602c5802d02240340060181d001d0307003019092100c400b24855152075442c90901070101856024810107000603c00c0b904c0d42e41741075503c9070003040c0f02c440d03541c0842c540400304021741110001d1210b600801003075917078001034240d040f038198410704401030307507035416144d142e010b035412502503504408074200d130807082544610381000344402510440a0243d8401c486 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 46234275 1250 46233025 46233037
    0x907050705031201050103050702010c080f06040b0a150305060306070912080408031306020d05041d0a020408030703030905070603090f0f1e051507080709030f03050f070311010b0f240c03 82
    0x843c0c50200148a20f5030700d4040c01c2e801005600082c0415031046401030041c400040c000107054002c4400220b59035107540000e084000302400c81d00c1d407962200403035040005042040008282002e0104850b030400040840c0b20311490394941d982d040c1030039440e0b45101e201750400d0300d0b00c0031300744004240e4100c1803008001c01b80c1c5020b1a6528203140c2030000e401c0c41c8080d2810740c2480000d00081052003031842e817410b01c058040c040101503582c1e0f40c2501000340902e401504039440080b900004040c2c040d406003822600030011524150f0383c408040f0141e80f1a103000404549584640c0d00c0042c9400088001052081680c0c982140001201c4540b01c07a0340e000642d995030103000b250401d002e002000c2600031005150100561800150150040c0f00611000307100c4c130b0500314040103051242c0290360940317980c4c040c00e6503250054240105032001c0c4403882d903841c1d40303070501030f0445180c56161281308000c00f4114010000e90f0b200150440c0c0c00c02000c100c40700f0003c00c00041241070510003091 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 46235525 1250 46234275 46234297
    0x40308090a0c060c030e030d09170709090302150604090c090c170709090614031e03070602180306090d080c0c0106080d0302120106020105070e06091c0605092109090705070503 77
    0x44c0803040743c14000c01c0c01d0b40d02044640660403010864100c81d600600f140300340c8100300c240c10102482c400b151841c201080c0d114809241c6002ca0060416501184c292404000041160b0107a03c84804010866205400c02003400d100b50004005544d8103820003401d9220302d00340000b40c4040440c0c4001c00400032150000011805841840703498414811100074100c04c1c0c0d044504400da00c0040303913a80042e13510320b0349500c2c00c020000c8a04041001190660b42d8404800d44d00c1c3c00176500c1d05441c8204800200b0f2107030107074000007187e00750002001051507986545210702929842c03029585a880160484540d5403180d60109580c5404c114143d100801a0780041c0d640c100019594002001a00100116414001848503082e032055904001d0300d800c45101740c0e1050a5000100040c003c3c16100ca58280103004001c18840c40fa4462849400d401007a1a5580b041c40900c4141d03c0010380c1e00480c009060010640905260401030391100c0e06040451400400e86c68851854110080b155 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 46236775 1250 46235525 46235537
    0x30f0212091014040f0219030606060806040e030c0d0302090604080f10051e06090c0d05070201060801060807050607080702041d060103020a0510020618070504090f05010b01050301080303040308090a0c06 89
    0x1c0801c0794148a49021820f0803100c1c0300031801c050769507901c0202000c0000c1d1103611860a0200342e021070500d018002c50344442c04100c01c60751400c1c080d008140c11075105211341e241c149010780c07000020049a0905030460040e02218140b003c040c0d000703401501d2001c1c1c12110610010515440800c220f42e41000c0d0440146a090107034a01c0301c0a881008080029442d0031048280081c407117000300c20703000303001201c4445199985080040740e6009541041b0251800c200c184010540c040d0b2042040da6840030081c05401e03101e01440e075442101e440b036030780c00075810010003020914005c05842800c4c13004001148e50b020889141440c10041008a07010f81c120000420440ca8004101d4008101c25256007554002038007000e511a00300502c7c10103210002c000307500b05003005014210180500800411006006061500f40a080d40340216180d40c42c00c2c1044034150b0242d0240c074120380c0440e005510710364031640c040ba81440301600703940d5a4400c3d400300030001394904000a01400c6241d0300c0b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 46238025 1250 46236775 46236793
    0x50d0501050a0e07060801091a150c070902090105070f051603290402100309050c09010816090e030a0c05031215090609040b0106140d0606020d02100b10030f021209 72
    0x52002c071580288144401d1340411010403009400c0301c44541100c004000000e099000682e160301c062000b407007050390002c00c1e03c80e007045020034580940050881c00c001c0701d08240e141c07918a4100d01c120340550380800e500b8400c01e40002c403051f0809447c07a104505881c4610281f1001c080d0003005900103c0c0d210004c003941c001e040c41d0080c824021031028506c03d8009040036000300709a042407681ca007017010b88604246083c42001c00c98010b0243c0c0180805402d07682d034110158450142d1001034403290200b031400140150a40105c01a00209130301840c03402e0440c52080d19540d11403a000c8800f80020b0089030346559909540798411a0400c04019828404408002c40100024403145c803900315601030201040e01908040d05488281c10038100103c1c2c010302c01e024078000c65140052072420040b0120781958040b641071680c4034903400300c460281e0412205800da80b0000e00d4940c00030010044580214800d4100c0d940b204070400005140418440c1200794245080b00c0d0b040d0300754018661 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 46239275 1250 46238025 46238041
    0x60f05030d030c230702100513060e03060c25031812031d150c0a06180503030415020403050a05010b0a0b04030b01030f05010b090108010b0102070f0b03061009050d050105 75
    0x8035840007a4502d01000b026100380e40140210f048114002202201d00d05602c12071070402d81180e01c01a00100302214441114000034029480601100f81103809040700040c180d004120710300034000000e02a0a40c0d560f091000c1c4119000708449000380c2c10000080b004403580403040f1110319019584104154605100f0200350200329440b100d00900811076070701c0401da01046004030000c1c80f20068200d1210755002850440b00809151404c000000b62400b141d2400980400500e02c00c0c00d007800050003102c200c1c801c15840300e501610540007040001c0014210011101c62aa810310005081503101e8948502e42034041d6000ca8071603544180182c098074051034000c00420218150f2890300b410f5984045003094184001803000348803018480c1000020b4100f24102003000e001583c556035241e43e01c50103441030b1070b415800740c000c0440104040c5020003580e4140c2c0c05d2081201e24503200e1200740708a01c26030344c0d80f03d41040049400491642c1c1d60620145159005100214440c20900b070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 46240525 1250 46239275 46239283
    0x7020301050c09060d0c02070503031c0509010b09040b040c0b0f03040c0f06090902030a0f020304080301090e0309012010020a031a04020915160503070c03030e010914101101060f0503 80
    0xd45501c845041c000100c041c4c1c1c48508440c180700d080e49001c42e032410025401d03441c00e100d6800c2158075000200d940600200c000c02123412034400c941d014002038403900c206500b2110300c1420705821110050024000c6441c42041c240c00034405e405400c05195120740001e0203401c13a2880d0661220000140024401c40100c904054180750042194461504401820300d000070300c00c071404d180e00880007030345c6000b05900c550320580300706809540e28500341c070f401c16095201b405081103007031800c50243e103500d0700081035a482140684500d007040390841d04d1042000248051407015119514540317011081e01d001070051840581c801092901c20040c2c4000600c1c090300b03019000b1841440071401d01d5503450360440e0b00d40384d4240c20707943d105079000c00070240f056844005886844001080020084102040d0044034040c0d69400f42007a20500110350740c0f1218030894207840300c114000a813520b0051a08100c80005003032646a00104a000c603083d80c507160f00000070304446200c104510b0800340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 46241775 1250 46240525 46240531
    0x16060f080f0f01052101020a050403051209221b05090f03030702090c0f1605030a031d0607050912012406090b180d08030f04020112060b03010302060a0203040e0106050702030105 78
    0x11014481d460580e00503029844148140c03071090001c03a20a00f1030250514591503c4401c55000395030341c601c8480041c0c030305c2e0b1061204407090b104038000c141440c9544401d50725610b074018104031030080340800710440702c04501c490220302e030740d43c19800d020f07800c1903c0c1d4200241c1c0c01e03480b0385407600c0805040148911051201d40e0082d0810030003d0010794038a804c0652001d006003a07140c0754a440c0d0010f41d814000c400d03541c0301042c074640c218030a012001001d001449036554050051413441e081d04e0068240141c1070b030f01141d00c50700101d60b1150195000d000004030141203285450845540346003500c0c0100500703400301c2101000c00000c600c070b120030000500741600700241d44600d48900000303144920b8150310703842103e01e10310030350703607a0b0741102e03c402e0980040d1031613200e0600700032031091081c05032000c0b0f02248243c110f402c00704d1602c0c0140e800300ca810382c000c00e003160310f10b07002d004280c0c0c851365442c0114002004040742070110075060314040d0140c0d580721500c0708818410b0608444000e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 46243025 1250 46241775 46241791
    0x30b0334030503031609080f2118040b22020309010b030a0203030d051906030501020306030f070501021209120109080304051002040f120201030e07060e0301061203050a08040516060f08 81
    0xe40c00510110390004100c83c0c01420703a5160ba081025450340c202c0300048107404c50140c900034020400e0681078002200c09210782540141036100403c003105004510580740700b840391948110040c400c601c0c0950101c0c110700d0003e031002404400050886090b41c2c540b190014685074003205001309200c0134465542d600c02c0035401020a80d01a0300081d42d070b409425241e03a0280d8540001074111030b01d40700d2000c03003c3d802140c10b010403a207a00d801400307500304880c594000d110700c8421403075211001500030201ca80603005840c100c0c1586960032040d900c03d110064200015100103043c2510900c034040e6000c0c000d00d1400d890b8100b0b454103a081c24400d1036001ca0650060100380078070030488044004481129030f0f1021890780c0c1d44010780180080740785d5299a801fa9803000104a50420039284443d48200c00801805856009101182d50111005000250103106000f02140110700c04c40d0013901440841c3d010040d02c056040c0000b800782c2109001588171018610181c1e000002c0940000c10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 46244275 1250 46243025 46243123
    0xb0a2d0f060e0c0a0306090c0c0b06030d050a12020f0403030f2003040e090a051c020d0503150108180d02070905090d020a08090607061a1f0f03020a030b03 68
    0x548000c000c0e02440260120803c400001401d01c50300c0c0c000c2c0d019100408051005000d006000030016114100013901079600d84042c5000501529021460003007100e015143d2074146112940300316603400c43c10200000700c0341e00308010144041c00c40098001035211360f85406400850340d0004042c0c103900140f8105510060320640090b80010003a24250350102c1807000c4207540300e5032603528001203850080c115005641e0301d85da000c1d890a00d002445046502100c88580003103400300c0740d501c01100c4400540084040010840d07201c4c0881c3ca41062034003100c850101d50140a5505003d64013003200090b07400400d04004101040c091903038030019060142148000268010f503c611400748000c003101e4001800480701da485c081555074254012404101080408110600b0307402caa05145109000880841034030b5500c2034940d802401050341c90031000c1e80146030a034080e4120440300303002d040d01c8401050064404018285030440481d400d882e4800b4141c0c3c10480014462100d6a200c0c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 46245525 1250 46244275 46244279
    0x120609070f0e042001030914100b0d080909040f05100501081204030b0718090c020c03010f0c32031302040c0203030c04060e040905030301080a0c0503190b0a2d0f06 72
    0xb0146400b40003030004900e0b800780000131345004070000e00000c0b034000c141d0081840b035200f20010001e00070076101c10170f990801200541100700551500d0074000103001010402003525103040a9030341ca03811901c01d420225004209955080c02e014a0b5074020303000540c2c40f801041540340811008085202c038103c21031030242540c990b404414401420007044c003120030041010200209001030040401c0d10041100803030f001c2d002511000c4090201d4401d60070006280342940141c46020441e80d15925031003461051141100860031402060066064001c1b807110845800322000710320804038003d03011521402841080111500c04100c0c1045520510801ca00c400511080300c055440078200811311201c070b000000e01411509030010403501012000181200d000907410240d0fa210703280701d001054842e42031581d80c001000d4013200004900c5400c3e000325621031200c1c3c1d04600030020104065454080d8008180760821404062003620541590b0414040c82072000d00c00310b00c1824483d042c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 46246775 1250 46245525 46245533
    0x10e06090c150706021b0f01061406030903070b0718030b0103050d08040b0a0b040204121101080a0b03070504020309030d0608160603050f010512030d0f05040210030b130b120609070f0e04 82
    0x8014114010203007076000480f1b10428900c0c850780300c03c0c615031300100c480f044070709940f0034003070300d258414030b1b041da815480c0c3d00b100d5107403d0094038803500e0040019400c01d42a03440304200100081c1031202800003010000111040380310720040a58000c1c880040d503540765240c1640342c0890b50a04508020002e030500000840c110324040e045020840045402010000018001d10540c2d11896004102d03907242d50400c40740611b051a4548240c8a046460341e803403840400751004901501c2e495084901c050000c0c0c03038650302031070b000541c0174202c905245035507414000316120380d0040c6900e07038000e0241c48807242c074137481c2001170a0726281c00d001c14107204030946e48990040c02554801d8400002020501e0400c100703a0740d0051564009010b05c00855401350300800080e1010b0b400303480303102a20350b0250701a0207403486003000070300040700b8a0740299010b401000300c868402d5110540030604042e5030020081c0500403044070f4041c0108038030f800b40b854444190b5511032201400710508220101e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 46248025 1250 46246775 46246777
    0x5010905100501020a0c1406160506060f010203180105030403030b10270e0103080906070503180310020a0c0b040c150806120a0c03080307051303030c0605010605130b070212010e06090c15 82
    0x889916103a080e6100214000230340ca400f034000501d0100c04030084070070500a00151042c0034040c03d44d51350781d0144415004981f01e00c1a460b0706078405060180b02d05555119030000c550040c0245000207260301c1c0c840004000e0040c24100c07000180c001c880840220f84400090048401440d09920b41a4504950b43d41029814440609122000705641485880391000c80f030741194404243c0365a03401d4451800703420141054040e01900c035020002d40b098600d4422906e9280d015100c016015240d81d903900c0d1042c0c4020f00480f0713500d080c00000150501c4201c540381c040c0495031104485842e100060104800341650b803407038a03900681c005004030740080145000c4c1d03500704c140b0700c0c0d803070390340d240e0640d5540f003100441c005500a00c1800024186c0c41150305460318810300040c01283d070b07298070446031405a80070010900b40100410020400350b20001e001c100d101400030758625062036040d5084440c2040075141d140c0000c01089901c41060191203503080c0212417120803032480908407242 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 46249275 1250 46248025 46248029
    0x120b0c16030804110a081606080408040b0304020d0507091e1802060d090b040c051206010602070b0a021908030105130207050c0105031e041218140402090a0905010905100501020a0c 79
    0x78040001c2c00314052280c1210800c5048030080c00059285a841c0f4403155512103000d4104150411440082441881441054015504064920700300f500740102a030455202038801c0780e00244030010b0500140c81400301400810031a00b0000703d1041c04820319080d02542c0c2e450b07503d01d920f800c0204250300c007810482e4480c107030151580c1d0740341c9106d52040001000d800501601400c941001c0100704035403000c10388183d51081d82d04c0c114859101944035902c50081c0074600168201e50014012171450001402c01001d0074412503901e0210f11100d80c41160718903a0941d50004004014021070030050f44641c1d0013034080d841185882d14640710300703841d0001e00f030615040040c00008100c88220404c2c081300031000c4a06004400c1c01e01d4a000c84c00c501c014400c440c0030446504060461746808036860045900d00b41c20791403058100383c1008002d6100c03000d40d03940590400d0380032814420b10300c076650180c409180700049a08140e503d072110502658082c17070440d408600140300003000001e810341 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 46250525 1250 46249275 46249277
    0x90c030a0c0905220b0a0f0203061f02030f0409020301060306060c030e06090d050f06040605060406050108040212011103090a0c050d02010e0f0a080f010204030210110304140303070606120b0c1603 86
    0xe664444420381c21041c48012000a8040480d0991005001071001c00a0045080d06c0d4104000310800100fa0b050740021240141d02c040c1c10062031101081c00c030070034024006148140c038a0084400300c0c0d800c0c546c20640085824690100040c8440342d010322401d0043d283c0741c1445401e43c40076507801440e1100b055a154020480850b6608142d22004150500994014283c038a2000303c2100c079940d900d0112802c2d21081c0c00e00b03004c2000390909100355015904181e56141c0700399240d4003840b42e0307401c210300111850740d1780700e4110f41c000031045c0145005640072000761100ca142400c200820103a40d0b0002c40c4113400c0e1107200c0c0700503a048400d02960400a40715050445204d0000961501d00e59000305068040d010315160b004a0650007403003a68801c6403076004101c1010400c4034a11441e0340d0b49401c035481000140041000f0040d0414020720080c100e03443d240b070315030f81c603030503601141c3c400c4207601003100307aa0003007144050a6903884044610004c0c101044085c500250001c1600050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 46251775 1250 46250525 46250531
    0x5031606030c021c03090308180a030318050607020304060306060503060a0302040e07030203030d061a0307020a03120b0a030309140405190e0a0804030c050307090207020d061a0406030506090c030a0c09 88
    0x2c010a4028800c881c130390511150b01101c200c48000024000d4816000110009050000069115003409000c850303240c0905004140c441d5403550290000c0c030001c5406030880425122200004004028561203021254059910382d031030103030302500340d8221b50401814000203008000560b00e44480c1201101d0b0104e40110380c0100c0c4c80d6516007024032903040a9010b0000050200240d04260441f000726100e1640842d02440c082c1c20600c4c0c41e0006454600050300a460a038000c21312400c0100032800310300f40d0005010341c030080014803201869000f100491968142080131011200310360403030000c1500d082c001da142603d8245018034004000710b1000341d17500317030941c0d1100c030411502c00c6040d13000030001c0d900d58590510b6009000240f00d01c40c4a8880d01c071012849000c01d0003510001c40d8054400700003134170950740e41c202820b50b003027110814004511030160035a0307660040303000450007030303002c0c0085080503070110b4201507211600c5c5010394410301250b000561008449021070301401000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 46253025 1250 46251775 46251791
    0xf0a02030c15070c060e03160b1209070e010602060f07020a1112100f0212130804050402091f0e01110309011205250f081014090402060f0c0106050a0503160603 70
    0x44501e015000015011401c0b8104c081081504110403800559045007104e0300310482c1c180c0021035200c14041d0340b0300f2000a010200141e26541581c0e6008810381c3c00b6614407139201c030b0340088074820981c0944016480075060041356191001c4668020919101a000725800d076102c0c40082c8941c03203a400d0140850503951080e1544c28400b4000d11050f2013824007040080004d1300d00039400c005100400104182c010550000c9401d5140b0400d55101d1503250800c2d19200400000350090320030b40d9000300342c1012050303000c001986840d03452034181d10344d0303c009044440010484944030082c0031080d4010030491b03200e030387c2020095400d41c40410001c100369450004140d41015181c84003107419400540d11032105030810120720441142c4e07561400d96a5600400d41e0607480103224002c42e400700d0f0704255401e404d0400030954031138005003445192200962032841e407517000280310302103039558510601c01c500e0401c205a00600044000301680e040040484400443c1c1d03124480903da501da1038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 46254275 1250 46253025 46253059
    0x61a0f0a080408040807030507050a0f080714040b090406092006070206030a06030c0308031906060c0209090c13140a0c050a0819060311090901060303120216080a030605030f0a02030c 80
    0x4c0f1800760418074181c1d21503503924500b0b183e9a42440c01101e10401c1700400110b040840c9010110441e0080c1004010091070007803810700c2e40321031155a580044d2509082d4003141c5650b1100b0f4000c1c0d02c141c1e0b0000e00315000b0b080020580c1c0c00c0c02c881c1d02d2606444c1c10480007130303a1904140d88443e80c046481036a6611024000d900404a6600007441c85900d001c0000071700210038050f40c4208050890048001da500191604862060054402041c0781080c400c002d030405d807030059070040ea240d0850f0202078038400024a01351600c17000813806512804008502100c01c02c045400401c28101800700703064100b005019401541c11280803c51224009400341c101120100c24008800408100b540d813681405000c20f040428158080c0b10500081825698144245005c582d019034800415040c4492918040d51003c0c0507455000c4660380401c01090940c002040501d9140c1c50000fa00c2e460310301070505220301c03104080c00e6500148000f00240c1c8002c00e84508420f001c0b600300320040c07000e4038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 46255525 1250 46254275 46254277
    0xd0e0109060e0303060111070b1903020c070902180604051c050a06090309050913150b060d020d06030b0f011a0a031b08061c03020c0409030c02030a06061a0f0a080408 73
    0x14010784010700704040840d04050110013180900020390b2140c09001d401c40d2603594075119481588800b402c10000700301d681c0d55a1103040c03a10074180c9405850168020380051414100380c10104480f40d000070907800c136400d01e030b030b89a00301003003592050b0a00b440c0100184c01045100325116070680c91101e04030401c10248030304203109600070401c200303c103003a0500804100c3c0b00d0040600030800304010951070100e0142c02c2010a03400794240b170718002c80001240240000c0c0034542e400000070301031b50060103060700103000c0d0007050381c50000c0c1092560421805c0480040c15442690000c3c500510110140312a0384041510001c00f07150380b07074031a1000b200206460780c90403c050300401e00603000d0a50040340e0500035002100c01f9007134801000d84240d070b2030000c1c3c070f002005a4404c40b03208005041c01c1d0000d0020902034141201030f1750641d00840d040007150042252541d07a0340f1401e100a001c58140c6070005004190807500344600e00144e04d1441c402c0c003840b0014800450000790811603004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 46256775 1250 46255525 46255541
    0xa0e0312010609030b0f0f070f11150a05070504030302120a180e070f0206090c0d050a08040b030f0106050403021302070c080106060201020a03111206010f0903051504020f090103080d0e01 82
    0x3204800c00366949000003002c2069601080354480684030114440760100103220b4026964541c2451700b61b00c030440165031a44441d00d00006005118803c44906401804840038920303442c4c00c10040c83c5492040c44084400091440d024044184010310110b80d0000382c1d05030314000c80038195580c52120314250350403c054100300c0c0524a501101260784680725907c5400303502a40c461002981e843c40d402c1c2e8940300122040040d0394042202d01000f803502800170303e2114081c405482800c0780e90344458140e0b41c400c1d041120303403003000018010b074090600c00d66030050107545000c03030a040c1550700080124484030040715181d6004600f0100b400300c000403410041c60f09030003c0040a41d91f0b2000303030103500314940700c070003083c07419058491443d10350301154100c102000100c1070645e603e50065841403564001c480400c04248030100028000b04841849040601107c40e031381d01d050710401c01500c00090700030b4040d104500040000807507150998000c84d00100001c1072080c1d410301c09900410400d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 46258025 1250 46256775 46256797
    0xa020408010c0f02010f052203210603050d050403020a030327060f1202130608090307060207380c030702030715050106030b03030c0c0609040b0415060801090b06030a0e03 75
    0x70a102e100d2940004030242c04007801c3d0001d2058030f849620000c00c840040341c41c03c1b01c0651b0400644030808482d040c0c80c1e03a29110b0704100b80c810340481c81c6210001e040940a1084550340c0c141801401800c0004050501c103901d0306074a01421980451541c0281d48401000d01502005030003c0800c80ca00c9000804140c02c1c418440c203503107a000030f112558541d40030002c5003021408050030906802121a03000003020740300e094a207440310848881b6001000c0c0c00b0240801e10a8000040690006100d40b0b80038802d65440240744411040c54204240f0284801b050030185040604000b0584140e0210764040055180c0c2d032240382c1603007103115200c8024450f0801c100198a400721580c17025040e01c20b242d9081003591041c209160b80c9108500c1100b8a42c0d001c1a1070389403918000000b41403522000e807000c41e03011402d00c0840d090303983c101400000911407030300600006601c90135003401005070020a020303110030034001c6080c600c030203428412440d84803070511180e03290800488100d4400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 46259275 1250 46258025 46258031
    0x1505030d080a050709050d12050708030f07030b09070f031d0d08011a0a120906110c010207060506031b06070f0b010f150207060914030c061606051e07080a02040801 72
    0x900200203001d580200c0d01c1040c810f2030030010610203445000881e0030fa4001503e01e51710300701c0030340351320500700014010a010800b0401042001070788a00142d401400300805200042c2044840070f4281c90391100300034001d100071010400503661000d843c1c9400b2216040000e0403176121103d669081c2c1c5c001c0f034004964459041c402c1c00541c1c0c041101741c1207608a8090a0002d10100592050ba02c904941070b0b000800d01c4421903540e110692140e45400d100e520005603002074090030b03103843e4011100b8400240d6000c034200081c00a14043c0035030080d800c5028118a144049240400d040c00c02100e03401004003003800c900704840144130703803001a00b261158400b50395a2200ca0014600e80c000c80e6040600000750049250001a0910035100151940841d0508200031007034007051720104564984a40c1c211408540c440c000204055200c0b14121020340c440303401c00100703072000500149820340e491540c840300740072210035160304204035281c210344035100c070310520700640129040251154a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 46260525 1250 46259275 46259293
    0x7020a05041a0f0d02010504031509051009020315010e070f020c0a240503040c0603110702040504030e011d0904020d03090314030904050a0c0206060f010302040803040b0304021908030904150503 85
    0x81d07801040300d40700444403c52140d54403010700c445448500c8000b80800c07820320042c0001008416034800d107045200740002d0000c01750310360078504481c1e201507403c0d040c0e580038840b080d0706040c0489480d5030240b01600286503d0100b40805215009041400304041d00c801513038001d10074032031280b64190040c44d1082581d1114071040c00411180140c20080004c0743c0c00a0506000f002074900c00c0750045d81c20503400d4540102a006460814440555000304200c0d800c016a140e11445010b607020307540750148c0419100002d4092840c20f9030851115401001d0f016065850000c001c0c0d00036410703943c00c00107810514041e81c544c201600010060b202c481c44541c80c080000015201400c400c80b000d2101c3c2d12940605002c840401d0352540042c0c22082c0010f0031820314050071308813054107140040c505a958035006041d82c11503000020114400002c1c00150703d8801d203010040b90b400b13601aa4050314000f0035a6030b80c4a0107203414042ca4a5400418524075140d0703c804c010000a01035403040e00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 46261775 1250 46260525 46260551
    0x23a0e0307080d0629030708040f061b020f070f0510140406031406010e01080f0403021606030608010609050609070c020d02040e03120a0606021002030408092707050f04030807020a0504 81
    0x4540a405c2006140145035054001352140501404880c02041451070300c0301ca00850306050b0040040e690340c1c0e05900207030002452846841440d1400145210700c00c404558024140318607101c401b05e03554056103042c000006140c078030800701d4900700c62062038a045500295401c2141d00808500742101140c00107400d501908041507a0100b114140002da8404c0d0041da031401c100300078107000491650005240030810501d650b0002d000340101c1e00c800b406190240c0c02c0501e0b0f50045d400080d140c500c01c00c092107090040e8401781095443c103000303e1420602151010700d00130b180c17200300204000b5a10664907141503003801d10760054028840404100d15039503499100e90641e01e0f03210200d01c0003403070305c0c81c0c1c600c01d400c1515141e43c0a482980340c030740028030280d00701030800e9a841d8010041820300d6650700d0340100b0302c070305c40307886910b520f00f0801580551008000d20480a00608002c081c200c0f0480001b00c0342030383c0e44030132100d460740c46500100303c0010094011300e410902d0207603100648 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 46263025 1250 46261775 46261781
    0x80a08040602070504090b2202030607020a050609010207080307050a0e03070e07080a05070813062318060601080412020a06090804050a051e040b0d0b0109023a0e0307080d 75
    0x940d0a9800b1640c440c4e5403030307051000301e07103411501805a00105001c80c12000c6450050300c5e80050201e0b0700c60f089612900041d080036003d881c40009030780004495410060b040c03144d645d000941034000c40c01e00b1102c1d01d9000c074038400240a0300030003078005400d40c503260290301d41c0300130920050100c80016403904109000c51405990802c045019000029480a02401404d10031102a03540071120f0311040700c3c15140d640e20f03640460f0f01d152141510880001e00502c500a02d00381c10429942d01c1c03c040346030138128a041081d08415400540c10841386907000300c1c074503401952000c0c2142c407c1c82c290f9401c0f400c00c010140020035281c02c14190f10700b80001c0d100035109444007203c02010b0709684000f000610a607000100c52400b842100e2242e4515299111850600026001c0142c00341a0f6403090050f8000343c110705403259001c1051014600f1000c01030f190040720380c0c5d0800c003074036488060340300c4100c04030001b011054687c114082d81d0788003482640c590760b90081c6c1d04c0d40c8030380d101800900a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 46264275 1250 46263025 46263029
    0x10509010f0e0f0706140912070312020a0c06050f0f0a0824030703060506030114091005010f05011b0302030d0606090e07020601030803010b030601030b0d0b150f0112020d06080a0804 80
    0x74403420a00490180e0002064203009601548014964145041002d403400c0f0000400c24040c01400d0010222940754070444031801e80300c01c006802c4031800c6140090300b08100000100866000e0748010001075003840c20801694000d06080780c80c0c2d004451088041d1159000300040d1000c00304070b0782c0c0c41c540c0143e80c20b0b004200001da070881c5001c1a91000241c1c3d071003030390b0300d0b070b03243e40202c0f010000305580c1e42c052500008060004a1040030f00d41460003800001d564004156202e0181c189090200b40728141c0589040e4491402c42441c00b0002062032854000c180d0341c40901400706001c140c000c1040721600d24441c0001e0000966891002d008050584176a9515115003000200d0203440800e0b0913041c2c07540500102d083d039080c8829404940c0006100c03505041c0c5e60280c0142a030303501c1d03000540241c40745000141c1464250305450b1100703071800501d80030310030441600d505e50380c001d0a042c242084464005072100c50300c00034000079101540c4014000c4c0a54081c50052182d100c0003042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 46265525 1250 46264275 46264301
    0xc140d021e0102060105040203090706030b0d0f0f1e0206070b1e07170a02031b070305040e0f15101b03020c0d03030203090f160b07020f15030a0b040e03041a0c01050901 74
    0xf0039a86e1001488280c4c03004503500403c5070462081806200d0103030340201e80e04280a854800c1c40003050344d480b416a00381000540348059244010400c00c851182079803c0d0210b101c115051892255000c200c0a01801a00400404080b030025281c40b0144280c071208905103040c007a02400c0074080540201404a9101c2c044058032000840d60b0055008a90107600d02c40d0300c00900c58641c07410300480ba0042c0320200c08204040100260908c48041442c0c001e40030004101c0007070500000d02c4010000115445001f58007000446036851f400146105603405803100c4010f04189030300c0d00700c0c01d180d101c10a41d42d1080c4551644030906501d036010b144900e070032004503240381030f030300e040c2c913588502240208501c103041e5181881600c42c02c0c00507080c580e10180c520300300150403100042460058185d800320004000c070030050b00300350324010f0f4846810155003c04c0394807034000e8200d80b240b0850280d181030100300503030104a0030040080300c0b4a94030f450002c1080b4101121014003820403501020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 46266775 1250 46265525 46265533
    0xf061406030127020d1401050a1505030a050c0120030414030d02060906071206090203091c090b09060a09030210050703091505030f06040605030f06060306010605070c140d021e0102 79
    0x2060f68920340d03500707452003002120f0039500240942c200250112981003c884996119026080e91442402030601560311100046a420b01542c1c880031142400c1e401a80729920550080010840100d40300d281d0080030320340701845103800e00006140007001401c04d5254032000400181c180b45080c40d12000003c110280d4001b4000c05100300e031786150aa4800c00560828008103e0340c0e4003800800b0280e00003050041200355860003000d04030380007180c0d40b5003150001101c002c0d00360511200326958507802e0030304480c1d444c01d00810305001c0c000d10b10080e0060b14001a4a0700d2180a01c4c0c0306030045900800d082030025013000020015001000300310003040103900d003c40c404070003001190310051759a81d5141107544140552840d0000945900d82107a81c640300418aa1010311505490305d403024020626400c00e00c003071501e80101607100d031080020520049000500510700d00301126001e19218005000c010002900030b4aa910025440b060744501d02c014298449800c07900c00809030203403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 46268025 1250 46266775 46266791
    0x311030a03050f130b01090c090905070203030402031005011a0702150a050c0c01030606050703201608070504061d09070f0306050a05060108040506011a07020310050108100204030f0f0f0614060301 86
    0x10b0901312100c8100420131200703140180722100140e80700f854440c40600e1f0481d03070103a03501d59940c11240142c03101401600b0020810080d42020000d0326007000141c103041103990724160000a00150100c40c4d2030021200003004001d55483c180c148580c1c0b818071440b250740e4243d0b0322014045a004500124240c0104584240c031076001e0b10070300084803021740b2818230304481590106c13000008910a901c105401e00d507900549002000140469005e0a40c040d180c5428000038a01d00603142e80010b00c00c1d400c0c00414000b2214004180c02c1c0c0010113008028a910b403084017500340072068018070b5000001e01c0300081840b1180d04800c0c02002e21107800c0155841c6c0700011550400121800b0f4403da0141c001000340d400140e0154510108441440e030501e012540000d042084244416808944850040c07240e644c0920461050004a000c114646031441e0b607100342031801200060100d240c0701e14184140510840900d1f980b80c0e1043c401c10480c6500c0301e01e05c99000c0140e95840c000c0d840e207020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 46269275 1250 46268025 46268041
    0x1c0903090905090a0201050d1d010b1201060b1603020708060907060809010504030c080c0a02040f020702010305092a0a080d0201051b1c0e0309030703050a0b060405071205040311030a03050f 83
    0x4560042003804040c0c0320010507500151015407101c049920025a20a4209c0142c600020a03100000760200046110941081041400b090b0740802c2c81e4079900d08030042020020b100221841941c0c1c203030b2100c0c1c2545082c01c0a03801c0a2482d4805000390103500100640c104003c07a250050340d0380360b260ba150585402c03c49500301c0307804843c01008110220000c5e40030549003000b07020074580030002c1f601d00c180707168041000d56001091032982142c01240035011580c0502a055004c0009001883c10312040c00c1e100d07039511711101741c005c0400400c3e003c0103010b450b640c20ba00081e00076142181c10201e0664002402054211408141c2c0401c0d80c0b44005030460010441ea144105040c03c00703404030303200851030000c0c1084142205503101c10070402c0701c01d1320140b140a0045000d80060401890b1509100c00200380041c00c4170303c52403400040140d0690041203030740010541d8031000070f0703503900c915040d2041c0e8622a1500c11600c804581c8000b02d56150300200d100d4024100c00103055164924 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 46270525 1250 46269275 46269281
    0x8030a080a0b0f19050604060c0204060b090121060e0c030403020705011805060c030904050c120108031204030806010e0301060b0405150c06041b090609020403051506010801051002031c09030909 85
    0xb02c6564429103803801031000e4901000c140e44400b0180d42c900f000c4659503000501d071a4002c0e40018041240100c0000651505210340c02c0100703403910100d49031001034000203180f200601802c0e414001c0c0e000402600303a09070f80c0f01201514201d1140358403801c00121100c420340040f181100144a4024082161751241001d031308020340340480700380d106050204015007a0011800321201c0d00c001d01500b210780d900e50003441d024926010000c0d540e85500c030300761210fa0318140c00c4225075500c02c1010b2804200058403403540907800d450401142d40701c60004035002000000d0103036141d070a20070701281c104a00c00007401220000c031442c0312545210381252078a030003100c0e44d07203071103800100016010603100342504001c2c1c500034030358504d6039454600c0b0360100c850581100e00c40702d501050038003c2041c00c10201148484910700000540340900c0024600d040c140541c3c3e0040c80206a254141d86c000c1090314691404c482d1845c5e0342780c807204481001440010760640019070605c2c000210821148 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 46271775 1250 46270525 46270541
    0x7140c010e12010e01020d02040501090e0f0103060b011e0e010f080f0c0f07060204030803070e0609030606061e0712080f09121305041a1e01023408030a080a 69
    0x203141d0404100c024070801c9001e20303000c240349009540760621031422800a100800280c904c110700140c132a0301b072400052940103140c2050303110460305000e10070341451003404d841c11290f20140c040f607400c5a200048515415007800c1c03c3c0d400d8540d004804055400071f0204a80b903a0a99444192010100080714003180c02c2d14016050403080b80442c106804d440c00819202c0401c0c800f691601d41103039240004c1303a00a610035181024080280600d6903481504032806083c00c40303e241c201490200001c2d151100508414403400c0c0000e0004000121020000c01168a02c0340550325030700f04e400c00034102d000740741c0c0c64000a0003220010725007007420710055002d00801030081c40841c403555000394142d4869110700c03000801d07800e000200d590307403800340785403d0001d130203114070144142080c4400b0814070710f910130218003c0710301443c0720b9a0008ac450710307814841c02241b0151114101c5921711076141c0d080300e0b03034040d2640c46c08110898000001d220b864a1542d07240311680d0b460340000d040b65180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 46273025 1250 46271775 46271777
    0x91306090e0309130e010605060307020f010c03231902070501150503031312080405060406020f060a0b030c0f0402090603070903050c01020a0c06050c121903180b040818030105040807140c01 83
    0x84e070480e540c411101c0d070006440340c400ca0f00000300c103901d13240001d80c203420448494005a105101c1c45e82c5400085c010558201d40604060124071003004183c1c42e201c420310402042610300d40005854000e1002c155a03d9200015085540700c01c01e04120703001c0d103010342038007000120b69040013075207040c00006c40b80c0102d00c00d55500c4401e821302d040c0c00300d4088500c00c141c4094805201c0480c9036039480c1d0041c00100041c0c2c000302001d06414000704d0509100521141c64646425040290381c0c401041a9092101c2110b040204c00f8030b0b480010000e000300c59000e50850000310030021455003210111b4156402203044401160302d0400485ea50140118000c090718480541044841d0182d00949003100001d41922580104071007560040d4100d01443c2030300504841c02c1805954140c410001c0300584200c1258504681d521403a000810141000705404c10001e0448030007820400450300300c4c58001d00034000c0d41024140842240c00c051000d0715900003148511a10010029000d01c90700c1c01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 46274275 1250 46273025 46273039
    0x91b060302091e010e09150916200601060f090305121309180206031e070905011107080c011407050109080d05010504020a1e1101050f0714040803040504020d02091306090e0309 77
    0x44681803012550014140c2e0f00300104c030003e084020f0b9210f2002030710500d0449048440100940343c018419a6800a2912b018101210f02510200085080c2d03041d200036081c05900404249000c0f0390f0080d2503800034229000e8648000004680c49004211049503d4040b48a071078482031160f0468911111021421108011603001402c0c0080611ba00c002c0181c841c0c06412034007240804407400898142001480390380061066607048445e0814040351040203040090030015000c1d65030300d0007450103041c0300c0c800d00c2110f41074030801308840c001d13544200203000b1141107240080c0c3c25008a90214000c0f418800040380600b81407094035403044d1b00796600001c2814554030020000301c0030310300d2000c201003685088040142406140e0055031a004400858070301444000e202c100010145000010f080104000640c3c0003c00e031410340d4400c030380c010b170745500d005000710082c0325090300f00b900701c540c0310002844842e10307900480440f2010301041c41240f092100e0310703480788100200c1c140d00c566 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 46275525 1250 46274275 46274297
    0x9060705042714090c0108010b120402240c010e01060501030c0e0d0c090612050c0f09040803060d060f02030a060f080a06151212091202060409091b060302091e01 71
    0x10744654041070800c2c05020005003800b42108503042803d04540d03080030303948000603455065911065460040c403c3e0741d40c9904081d24465407102e81540034101905c54a440240c8024900840d420403340480103003000baa100c80700e84185018048078100c0c030301c0319482c00b200029554020b000d0071a91403c0b0f41e944180c5c0100d4101004000200700405981404001c0c10100e42030109100321400f0b86401c1c1ca00c2c85804040e0300e4000c0c9002503003100345014000d070a40a840c182c0305d560701e0b540c100781e01c003540e00d441340c3d112804503040000800016013158185903034059401e401c0c0d8021030140c01d0303042c41800b019407940603018113030f6803d10500718581d00030400b03200480c030a40d200d40b00d0b100c80c0c0310301000c0d6541d84524804140040100c150b1320704e002a030b0104005500190504c00070309040758a100c9490164000031018059441010011511071a81e9800c0000d11190000009100c45845180c1c580340d0340010000e4010401c00381c0581c0b01e03491130401e00780200365003000d510300584d60b0b403071001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 46276775 1250 46275525 46275569
    0x5012103181502030d05060625050a0203010504031707020106030510020a0504033f08011403010e0a12021506090103030e010c122105150f01020c03030309060906070504 74
    0x300310303084580484118500802c16001c404900301d030094083d030007140c4031100b02180d8011100003401c1d0b64811401000301030980c0306000800d2000701407520104401c10043d040c00e50820040460080d4107500c1d1004000070035420101400c100b61000103030030300a03a5840c00583c02c0720350b207000280c103903480f11814681c4c1114940080c200c1c05400d181903414103541c0c0d40c607821550090000c2d1010300b0050801c07000008034184000314600c04442c9041c240020205002d0090300301800f0b40c400140d10f44082e215141c4094210404060f51342c03049a420003c6400c110505c6070540500d1001070180c5035200a000d80c188a03010f005403001017291480341d107195070644000c0d07245410755051007201a41d48001c2010120400e43e03484094440180310000605e10f0714035001046c0f140d40c5180d00c0c2200b480400010281ca90401d50b20540341c00d145a1641401070307151000001034540d05100c00030070007000840202e14507000300700400c111125600da0320401d9903980103501405015807596400c1003007103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 46278025 1250 46276775 46276787
    0x12030e01210c0c05100f1107030c060f060302030a0308070809071d0907030804270608031c020d1113090b010807051e040602030a080702060132090906040605012103 72
    0x81c0310b030b0600c1c2d01203070400d07601c850425100c140d044201942d910341d9052103210038010403a1051a441034546009501c7c2d074054155104c60300302400b09a0796820071405010298010030146400804541e2581480e2800500c10030088510350b000400359004200c4001300052810300f60358601045540160115480c501085c6c00240081d113180700350400003001c00e040700000c0018140c4400c03900d81400e007020a205500f004016002d0307035186400c0041140c50000b0040c0d0704100c0c8000c00050400b002400c80c00081e02400300203c2d000307803801240041c44840e9000070504001080f07504200c0d1945d4003480c104441510480ca4041104200040d07205413182004012042c1c12a001c03001e5952003046488a9801540000c1d025a000007040000160800c800660101840c8010000743d0304108080303110350303040d52802c01400c269404400391708005240c102004100540103d0307440c43d1005e440340d40c0e20710545060340c0d030a2a000001c2540d0643d40504003800c480f9201040103116155011145 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 46279275 1250 46278025 46278041
    0x91d011103090307060f110c160e04031403190221010b04030b010e09030d140103021306080309040c020309030d17090303060d0201080a1401060201020a0f030902030c091308030112030e0121 83
    0x3d090b0341c5102c810b220140800203040350b41908401002401c001242702071a00050350441081c86404ea01000000b0754000f403482d068050081d0b03125141d4507800b000040200301a01d24000603070000c034801d0741c4d0480c10900c030604081d0900c810b00380d503682d0724044041c61145000150662000c40c0050000110540000e50072501c1c840031280ba0000301c0510a0032100c140c10b100040e0000d0400404c02d5180c010b42c050300e01c852401e02000307036a02d419103161362031107030281d03440c011900c409103924158000d02c180d540000c0c02609540d0000c014050080100c6104a00707690396505810204440303000c00001c0d03900c035040240201d800f0043c00c1e0015506004010514021283c03514444055100b0450616009124980000d0b0300e80c0f03203840002d410501c07000b241508140c9401e6140c80942d0740060f072011300000039203410406e41c0740d210001c484c00c0890f11000c0c103d000300000001e03c881070410340d056094080d0341c1d000c03040445100116510940c1d1a800800c45203484034520480183e6444250 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 46280525 1250 46279275 46279301
    0x60b031f080a060518010203070c02010f02070801020309010c030c110703020d240504050601050d0b010b0c0309090c040303020706080f15010e1c05010b090f0703020f04091d01110309030706 83
    0x2403441e80d1850300900e445051101141d01580b41c2c0140304114540040c40d10761982000d000b50308501d083c2c0c0b40280441012540a81000803d140141c8458001c0c03140c00040c00c1054025580c0f8600b68503058081c10359803019000082c035021031100801e215021510000e40c658000d00041841c2d034080003103c080e000c0c4203580301194070350b0f07907482c8441200c98852510010710000c951440c4c04e00b011800c0c01c605a0040307006125140c40200002c503025100e0341500e0030030030510703198514107100301d1950003100b4805030000c00074001c3c0003000003281d02a2041343d2080e400c540c0d0036a16001c040351698415180d009010711000040b0b54805024045c1c6134030001c040c03406800c480220000508107010314800c540d02c04ea0f000c440c4c58107100e4280940300c0604019075803194a400c110460400d1258000c10040405034041030822060070900101c0b00146038285d014413040700488851085140c41650700c6941d58a0b0404501e89142100252440360744042c000d50b0030941281c5444e80685270040d07804c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 46281775 1250 46280525 46280581
    0x20a1d0c03060120160515070201050c030408010c050d110f091012060605090909030a02031902010603021807081b090607230109020109120503032d0103030e01030c03060b03 76
    0x3201c211405030700c0004001c01800109210110304041414010064202d0f901a09081c25003006550081e008c8406c220743c280b0780745a644685a900c03608502075600840010350800d903110030aa070344440078040199110100700100038008204241e248502c5102c400c03080d405206940043c54008041400c1d41200d06040381050000c40c60b07482203410396081000401c0380402c4e11486428201c42071588481202e000303601d0800c042c3c030081d55030b00400c00f8042d690031050000002c903034400c1d0003040c02168003070240b84030324a0900404903403078030888491002444400004804a00c0c50a41e2450104c464005c2454651002d040c401203901c11030f01a10951041c0158100b8147e4003031400c990701c568080009421202c0d40b00040848843c0c0d4402d0004d40e0302c124542002ca2400310807aa0800d07144c1a0300e4062113404041381030840e21102204901c0194040000207140d00000b0150314400300b40e804001021034440160304640e1700c1d00404252480c10700015110015421030214080c80c10714290b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 46283025 1250 46281775 46281797
    0x203030c060127110f0c0f030406030903170709090e01181a0c071a04021f030506010f050a0503010b0f091c03031d06070804060f0c0c020a1d0c030601 66
    0x380c0d10344002070b0f21074290148600040e5861140710b11452500c0164201c1c28000300d080d130380ca81d61003401012001d210290002502010365070302001000085a4120192074a540d61000060002c0c0003800c425400b040400340c404d070210034032505003841170941d80c5600a40c6410300c020b100082c4000d400c040c80641d80e40c02180015401c400c0520015441034140031080ca0000b01d00281012010300601d0010300280845000940e200e8210940090b44892413101e40c0d9071800000c42100c088c40680c890782e14150383ca00460303503041d04180d20661b0f080c0c80d501e800004141c001c42e0f1612401c484540050001c2c00140f000380541ca00a118081010041900303000c0e22000041160303141003546420340faa1940e0303031170030141c043c003688054020b102c038040e01410700303039070065110700c4001c00040801042c40c000908010090f4024150541c0a442c00c01c2106200c040c050401815408141d00c5048024400103100364407002c0c00c1c2e62000084c01040320340d2240c241041c0e50381c0002e01102d05000c442c0360f00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 46284275 1250 46283025 46283047
    0xe190e01020d061205010f0b060f09010201060513140603070b0a030f0b0a081c08060a030209131502070501050604090f0b0c04150e04052a0711060721030902030c060304020303 77
    0x211009004c151060100f007801d00e260080c212082000920040d60801501b0185691000c041d604c03e10541c1200607030700c012110040340107084980005a202400101c891140721940d885211041c880c44400700c0681c0710300e020556598170900c59244010010015034901d244240c126103582184034201168010300300300081c41c0000d1030740102c00360364892001540c0080d000303040e11034841030f82d041140d428242040449c9a8018501010340036100365000704040441403400b5484650304525007002c00c08540903808040d501083c4150750960074030000c0360305450240f01e6800050f9210300d401c10038110944d1401c0c03d2140082c01c04075030740e405000029508000d00302c100004152551543c3d8101a0802040107c41c00500f00380d4411030005c44000d401c034003100e080c11030148081c160780d4132000b8500d405861403092029031038020601050000400201030a001d5148901c24074038250213030901422002c641031418060340c1940034443c50140c508007400196007280c0003400b03607440e003601d50079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 46285525 1250 46284275 46284281
    0x909020f04060324060e04170c0601060302130504060b1e07050604051c080921070204020f044203091202060402010801150203040e0c0405120a06060e190e01020d 71
    0x200a603011000d0180c01c80541140c455500b08024000b0010411142400c40a01c81c40b0300040c0300400144548e5029404428200182c4842031702c42c0040b01d21660311054010f029400807444104001a881000b10345458240116020390f11010400b6040112800e5001529281a82e00c80003845c800c224400100340280300c040d2155000b2030081018000b4404040108d14090641c3c03010800c400082c05454a004210101d101e91003075066850001ca480d1205014414450000d40c06480041c90000c00d00c03614002e80112110401500d400002c035102c0907692289194014a1542e881103030a18075158440704540700211034540062821419a00e0521824036030a800000d42d00603801c010440d131b4000203032805020700c8182d040001c00d240b800a0758030f0040d03010300d901d50302516001800f0ba1503180159801000c00400c021902480c03203000c40e40b00c2e64070b00302c296442401c0400100721364940c0c0c5801030150702c50a01a80852080c5c8808030020501e541d02c2c0082550204060240458940 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 46286775 1250 46285525 46285529
    0x1090f0303030501080705060a1209020a0f06080a0b01030506010215150a080105100b0c0c04110c0a080c01050a020a080f07030f0c11010509010606091208190507120306050a0909020f0406 82
    0x103200000c0f40c1d410040b44070714040081e80498400c200c104401400264030800c520040350b2400004030742c20717605100041d812404c58010b0312038020700c15400542d80d030340443d10601800440710704000c10340c1140011420780300e044807198050781c41094546e040384810030741c2541c0030420380e922200203040000060300c0f60b00c05034400f813100da440f442400316a052110f0380c0c000410754128801d01d4802d00d6082c454840c90280401303031185545e034000044000c081d1049a00e5043c0040076114080706a141c00b01aa401590794000c1d80d6180000054900d2010b1084a42d640f185889150311503942d4861a180c030b940040c030300c1080580f01d080e20002043d032809042e90281140d200c0d001403440038507155003104c10080c003001d081c1c4e060101c00c0041c0d541002c1e06105440e8201c500303104807441030030880014850007070000d02c2941d00c100708400d010b600202900c1d4862280b07103440d200d09520b10b0100d0075605940580c9038003090501042011a01c00d0340010742c6284040c1980718150350182c00641200e0f116 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 46288025 1250 46286775 46286777
    0x6090c0903010510080d0f080a020c010204030b040f1a01080307060c0c0f060c0e0a0302090a020901200d090b03040b0117070518100806010311010c03030e010518010507110a1101090f0303 82
    0x9400788000031080c040301b8800e2410f85091a10310318900d070000c1540002420302c00049074009640c203206c0c1070a404a4003d59080760403c0f035030b81400c0c41e1100e5440800c2400b03660540c00c240085580c101c510484a04a41d071080c029800e03c40710742c0300c10000b000b80b03084203014031950b0102c070f40c0022003070000e82c49054040c10b0300090142c41118090a091002405e051058030050340c20710044e92924074154000c0f0b801400162217418010042e103a041e580280d0401000001c4850005101c0008142072141110ba64608a403544c5041d015050300065400a14003d8500014082a801103454030420910351080358081d40c0d541d8085086021080c20401440107110104034240250030540001020310310700070140b0b589140c0700e940041e41c800c043d1070b0402068041d138005161081d040785001c4660000204903604052842c0d806501202c240945a035080c85d0008892b2030140014040c0194081c014101072403041c3d4401c0341080880303421606210080502241c0081c5486100028601c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 46289275 1250 46288025 46288051
    0xf090412030c020f031e04120506040606120f03081b0409022208060406020304020402040509010e160926030706020309060109060806070903030e0d150f0b031506090c09030105 77
    0xc201000302034494001056056600080c8010b5070b0080001c200c54a03c02c40c034050300000d8050b401070f900d071441345500010200480e20b81a106010000c2160380c0594807640d4108202030b40c0e400d00d030a048c0c10661014001294011029010a005031000d981c0a186500b88060b12081c2030300000383c68100380c029a00160703012404840010948082c6442904541e000d80b003900d141008813941c6100c000c000170140e68001c00450215200c50f01078030702501009107050820b40e166030001403441c8041720082c02880c0c010031026140c90007003403400141ca0745412912080a035442c2001d039400c0c00440b24108c40d100422150022804900c00365028070403003c003034200c035454541c165003510550382148803d90440c01c02d010001341c10100d02d1045070745c9802c161800d800f030080000d20308802c110300940000e10a200c03201c0507005c242c2c000125424551000c110040e96281419641c200300031880380d2104d84840418205d24020b131806a2210485070607919103940380d4042420b5401c19650300e100144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 46290525 1250 46289275 46289303
    0x60a12020f0406020c03030309060115030608100506040f090804060507050c0a1e080d170402040b030a080a031a09060603090f0706050a09090212010506090a090213080f060f06040b0f0904 82
    0x40c1c1030000040442c4106c00450a5040880c0041d44802c01841410440d90800008020981c080c0c2c000c000240000b1040e103200c030405070450b801801c01111024445c07803402e41900c4941455108402003030350415070060070103040000558032036202a4060304d0394458414521102d6464803d44c00207885865020200140343d44a01054040207030031501d650342041d11900314003684035803a604441e00d41210030086499030700100d0001e165001301c540d018010341c1588018413019200420808840d50b60400c86d1101580d405002001410040d81d8071581000105101d40340510146402c01c03045002c2d900300c4031185035050310b040c1147d40400080303200402c8404440c2c1c3c0043c0d007032004003042d12040d80391840c03220006088a105016081c810703840031520100ba503c400c05800c002e00b51521045644256064a480740409284241a079900c11070348580342d1071340041001d07801281d0100450300380351034140810001e0091303400c0142d0802c44683ca80f04103542c807104440d00490244c90b061803454 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 46291775 1250 46290525 46290527
    0x102010b130905010605030f0307290f010f0609050f150c1c26040b07121517010608060408071502030f04060e120d201314030705060405060a12020f0406 67
    0x31011b900c502d10981201d040d82a54a501000301d8480c180d10145410105000c0c4104172001f5071100400d01e40010b2a008100c0c0d05241400d200c1e050300d01d220b00c02e440956498401302c0f20704182c0c0c01803075017000245e0b034841010306101c401010074241041e04642428101101945040541400c04812541c02081c8658094000303c11098220b0000b06800c03040c00307a09401c031500364001c0c00062401340e0510000700054402c00004003583c05a040610040341c0c0c007551240825120300403003100c103100725580e00d6040d00502c00d035411918200080c18a03545c6648a102c0c7e40d030412402901e04000242034a031904d18603100451094940c4a100001c41c1006d08000c022510302d40c110040580c03140483d0020002c1b2601969400030b203526021034036800c800e0b10480784903d40c3e240c1140e2210041208030417110348565100550f00c1020a49008240440c10142d42d00072030322540e50000c404200c01d000c02d0070801d00904503000c0c03608100e41092010503266040303a208034207040e518203000c10300f40480303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 46293025 1250 46291775 46291781
    0x703021810091404080306130501060c14070608071b0204020f0d0e01090503250c03030801230a030201050a05070507090614010c0803070804021503100905070507050c0108060102010b13090501 84
    0x80c1c55150b034100400070030300d40c621607038400140010f802a5000700025801d562030300707490350442c0900e840621895949820180c0700600c0300a040b5600314450b4400c0320403050008440341101c104d6900c01c2601d444458007594042c0751025451031042007440c1000243e02ca600040492184d0500895a00c0704c000d00e03a4400c91304000f512200310703418a000200440c030300005440100c1d00f54107800714116840304680c80401c000717203002020b4045090000003450f4200c043d1034106c1c3c1400d1425003c04101c1b90300ca0030038000221010744e0040404000340090751064000e400501c6441c00d00929100b515216117180c80943d0b400140d0ba02e44542052050002103c0c000b00101003c0c00c00c1a4213004503903035814a404007c1065080000030000a0190358500401c50030031401010403940d2410f0071109000303031100380d00803141028280700c00f140525120700704841500e60800302038641b0b1550340d07004484501014294504540d03d40884c00010307a41c03a6482e12000c056600001458503103807400c0c07130039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 46294275 1250 46293025 46293029
    0x309030406141201030615120c05011e081501260907050d08040506030604090209130201020c0108060319050309040e031905030f01090e01020d0513170406051b0703021810 75
    0x1c207030700030b20540240f8040760149905490740404013245901640c088041d500c901303030703021203204403512001d201448004500801a03c0007130341da1080c00b2020480e0244800300000c41640085c00d03d50004038000f00a409200d4000c40c1490056405403183c041c42030384d003d990380b4031320800d8403035400e2200c080030401920b0010182501c1242c00001d581d02c1d001414000d6208950182400100003201a42c0300e40c07101014980c018900441c0342030085480c4520901e100007280580714010080182e507018a00d0148a614018000e041050102d003200041c4803000c40229950b11042c45054101e5032203000303110f902803900000b151900c03005181c038118a510010b40b03009020f000c006000c41c224104607039505481d0031120200e40305040e4004140280700724814040c110380740070700340701c0226510548510418055022498032118840740d4100ca80301d00e01c26203020031401c11420690014883d9503184000b485415643c12641d83c2e00442d01062480c85095541943d0b6400c00058104001c01070700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 46295525 1250 46294275 46294307
    0x120801060807050f0702030106080a05060a0f050415240b0c160e01120c0b040b031906150c02030708030c01060f0e040c050f030115080715050f18010909020309030406 73
    0x3400c1c81140030f071042c415581d496450a07070004070b80045d500c09400030001403840801f22100c04130142403140d25140141c0e031301070341c4601300302030510314844500030240100e42050700c0e440360034001300161000341032219510542401c034180c8a00c0999244034808000e00901c0040b03590f555070203004604080e0000042d0070045a900c005105540d500e00100741910702e0081c44540300c031403900f04800c0303039203c6500c4110301d0789001801042c0c400340701c2d003d98091803500110380100c1c950400c000b029900903006107100020002c0541d06207a1090000042e12800038054030314079a12420742e1030440d8429000d40505a440384010024903041e004000c0081602d10341b0080755090650b00c0100140e018402c0b5440740301000b040303110903134003980303d003c8104442500107200e96560301d1107034507424284142200119043d6200d0a03003400703842114072000860000c0c034030300116012583c8100d00c64040d1581008445000400e0b807800c80d100840c02006540001c40e2038501e4403c0c01882004040e030086 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 46296775 1250 46295525 46295537
    0x20a030b03060a1e05160c020a0f090b0103060501050705060f1005040e1e0a030903020402030c1b010905010c0203040605030a05090102040b03071106130b040b0702100603030305100b0309060c0304050a0f12080106 93
    0x2401c20044070031000702d81c9240c68003110f8811640001400490036810420781d100502b030000411485a6005480b098801e0306e0070311807507a881005642a0040a801415503080003000034a049400d003c7c01e0b034403943c008100e28415881ea8045800c13103c6150501d0000d072b01c00c460090300c01030303800c14000c0385014a030010300b0540015274004002e000c86100090190b43c0200105d0401078108003521400940405003d00b0702080241c918040c09441700140d0f0a54038082d1365231046840032040f40c007500c0c829240c481c03454841e10f007039034010900100502c4565500740004544441c43c18020b501800081e500c1542510700321140711704044010700011194100500f505000640301d458950744540c000d90702076000d40d211701d4141d040903840180d40f03d8062030603101004058155000c1402040d001c503205104036164500c40820780300c1510300e44101c1c0d101d000054162403000c03006561040c03042041e00e0507040d55030340e00803a6000e40d1608558400c40a4161001554010700c2d0707600510300b51400c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 46298025 1250 46296775 46296781
    0x30304030507060e011e0f110309060702150409060605180301180609110307090905010501140303070b070c080d020315010309020109152105060a06050403050709020a030b03060a1e05 80
    0xa69581450740306810a0240115078060660b005400045c072a1669200f030b0301c1140806c038001072081e0780b42030071103020402820502010500c00000c0d25000180507244519110326602000400c01d4004600b10002c10f00304404108000d10340034030300c024402a192070b601e6120220940c200e02550b2002c40d40a03030315000c10314603c0710b8011070000d16140c00c44e50010308242c03a418040c0314211219582601131041e2100011840505c1e0300403403c3c94068002040241d8844029140e03c02c0a182404e90540c13040c0442404204030120305034000c03a560805052614441d503400090350000380780f800195602000f0000640842000c5540e89002442d0030071881046500203404a1094082d02c01c8152640203118540e50040c0540b404074600c451503010b15030381c60000c01c130284c04229481d03405800c0100e40011158021001d44090b25484006401010308025441e8001c1d040000c80104054441c1c0e00c4032441e407001d00c41180207076070b40400424034921400d401c44443c05452140d81c00d040c540420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 46299275 1250 46298025 46298033
    0x5070b1306030b1e030a060e0c0406080105060f010f090f1d06010c0209010323010911180103170a0e04021809010b09060d0f020f030a051609081902190801050406060503030403 77
    0x24000400d890080c03504c0040c450000480e14101003002d004000603d0940c0701222400c00207282004910219030a1003d907441d00c403030714241c440603601590001c03100300b500e650a41c00703202200c6c0c0e00324651070000540c41d51101c0700d419015295024105c1035a4642100e541c1e00340f2110100e40c803a00a080c407003802c1d82d4507804a0344004052001401e64041107040094290104070f1803104013034071f100248203020781c50070410034240c584401e061252030796501b103100c5038001c0305080c0e048035040550010160382110310881d060740610f994004009090219410956451000e85007950f51203103003d00301c40c502410b0140800e4107130000c01007401c041c00304520507500e00c030440d0300f030100f61140440c2d5021543c0c00f010203401024054200e0142c00f208000e0244810ba22261181c2c41c01c0f2801114902d54035029160180030740070305002608040200b25141d4100100e000c9070f144081c01e01c203c0340d1400855420410071a42110b6101c0c0d440390280300501502e4001c4001808040b005940b402d031442d07403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 46300525 1250 46299275 46299289
    0x31b020a021302090607060e0c0907120b010306030c030b0702010522031404030b090607031404030c021215010b040503010f02191b06021209060a06060206070c020d05070b1306030b 79
    0x44001c2c41500501c22064502c80a5019105a004082c000ca5204d06883c50000040e101c5600041d20310300c40c038581000c0300d2601c200514050341e50360312a01c0100c0d8522124101514007040101c0c149074030303010000300040e00082030000a40c000d606410782c0382860b640003801d403500a0907450341c0c10441c1c0740324070710344401d102008501d0741e02d810700d040c40c1c1104d405008074500071030703002030003138200c003000c103c2c10f00310109015100d641150b9080002c14800100315540c40800d5a020340000d00c00800e0794018101070820104294500c4112aa00c400a118040740444260041e40d0480310115041207a0304090041c0409003003040010740c2460800c0890480f010500300c521700400009490761005100180048a0b0b0142c0085080d56035900d04074502d001518180c0e00981140718900c00200b440034584110010380b00194040d102607185c00a0451300044d400b6001c0c1d0348594009540d0001560404c00000140318070b800040c2c54800644001b008007040d50f018070241420051100c80d256a410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 46301775 1250 46300525 46300543
    0x20f04020a0201110406031e051012020d020d030201061d011203030c140c0a0c1710020a030b090109051005010203070b06011202040506030a0501090b0f15030601030b0a03080901031b02 81
    0x1840041c0c64040340e260490240c00180854107a044c0002404105254907801281d2480d0000d100300301038441ca110340350b0403110111200d1030800d540700418441d039543c0842000c0035a000400741c03003000402d5000242c1c080a42c032811400740c2e54940d410000e8011144444260320108801041f4641c50200040303500b84441e4002003c060b92562031030b4400c0d0040c600c0402c845083c0c1101600c030990013800b280d48000490003500e4075104810b00203120360004900002d001032140250449086800d4264043d4010900c4c41c0203168940580a00036100c80d10028002c045104000ca40f506080465543c42e405603005141150410440100400d0b4403081c1d0a400074400e00c1e000300c10307101d1304103400000c0c0516000190301000c000184040c41030a904440e050780c4c1c3e80302c0304000002c0b090081100000d42e542e92a13801225020040c80605007a0015580c8030006040c041007a4a04000103601901180c004460b49280880c0e1074089503818403a003102036088000e0080d0824440c031000c1d42d16203001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 46303025 1250 46301775 46301779
    0x632040207020a03080706090506060a15080721060e0108010e0303070c0c050d03021f02090a090203040f020907052709010509070c0b01080f010e030703050a0c05030717030a18020f 79
    0x18540119194910f50030000e41d00140d050361210814500000541140301007960b45100700800301d4064540003000f542100c11484d00000c100300501c1080d12200c200500040c10300c521800d0b8000d205000010320050580780c1d0354009400390a000d280c1540b1a01038010714020780c035100d20312020707007800411030b50030500720700308207a205c00079142c01102c800c1160042500031603840d680c030b001c258001440d001d00c0031030b242d002d40480001a119000f24010301101030b80c007511000b420003a0021650056030880d0042d0500c0d1600d9440c1e402180103d00103481500005074009034030900e800000135154481009681d813010388201c4200002d54604060040704c1c400c04001003c1030040d4096400c1c40c99065102d41160b40701d42e9207102094071400a100740c903c0e1542859818050404080300b207450340c3d60b01d40c6800b0700301048a44112008075005c5d030b080740d49220800c4200d020a50310300384260014071180c4000e0b036901d011406d0405a4140d03070b24801c140c0d02c1d402e0706840141e03502e031a040c402c4081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 46304275 1250 46303025 46303027
    0x60b03010f0512010e030a03060311120615040f0c090e100311010809010e010603050606012706030207020a0e04240b01090603020309010204030b010311150f03040816080d06320402 79
    0x103d401c180101070101c4100d505100000d81d0005203a010b0f0000c01c2100e02803034112079000c6160052103040280e019258965410200014100b07640140c8140c50a50019100003103001e01d00e150380080f10986c080700070100380d0000080061804108078158081902201d0b403080c246582c0d5003c14481c10f0b03002460500000e4000684084c00c250b120301c1201c044203000f8045291360303060007500e500042d6269400074503007444e203d2a0212404d1039107030b905940c0e412244410704d45070040300207410030a01242d012450042c006049d2019890450189010710244203007160407000d0000b01c40d04030702007912014102448506203070f800040900842c0d02c2c03405c0141e680d5555407901c0c3c2c02849260001402c0e51140d00001c014072112002a0502d10030680d04281d41c020034140e110300d14020011100400a01000020001200c030809440304a8905420701042d2b051a610134001d5000300c07400140b601da448108201036102ea180180b00d40c041000300084161100509628081c1903d11103800f03250 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 46305525 1250 46304275 46304299
    0x70e16020309090a180c0317120604090222060e07090e0703050c0903121b0304050901060e0301020712020c030c040b100c02030a080304050d091d0402090702010e0105070c0501060b03010f05 83
    0xb2078001e002c4100d030003581d03145c1c803003601d03d08040741302d10b603010982d0408940407441454400c4201292800001c00348410581c0c0e980604220280000722400c0760000700340c41c00b00140b40000c80d869840102c0c144404541d650519180001c910310050500e01040091b00c1e0400c01c2d04804004160080c08a2502050031341c0e5207201c0c04064802c0c00d60302074141c800d1403140000e08038240003916248054880041c1140c51140d444c0c0e070b1f43d01032030180690002a010040003024012070000c401200c0180000d070030014551105416054968418805600241100316051606124071482c8400469080003051001c1010640a14a00f801c000510425108080c15503504214041155034050800c554902e0540b81c450344a1800818650215110680c01b04a07002003c400300304101000010aa83d541c56808010091001900010641d50787c0d00110304280820701890b4070900c00c6480f9000e82600d103203051400c558a0703900c4050456000c0c401400aa00c103540c141c01121001c03503104e00107070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 46306775 1250 46305525 46305541
    0x903051903050f030709150207180902060a1d03010207060e100e0d0c080d0e0c1c03020303280905060910020f09060a1106070e0a06020a021305090a0b09070e1602030909 74
    0x540701c1d04070f03501607d030740a202d03c1050b9000818100f51241c0d40d0040400e80b5800e40792500381c0e03d0040b8000c0d40080d040c400310001c00d104950b4115020b070f802e00466000c2c090403000c2422039010401c00d0714501e4031030a82c00d010310790801c800c003a84a010801044444071710a501600c0d444450035900400800504030410f210400040c1c034826454504104988028075000c50307030b51010448610f0080e00e1002c006a00042094030800318a40c043d00030b540355558005a00909000403042a50384601c0b0580014030198507202d0f030714006100b40001c01e400d01740080325a1818104940c000032040c01044403800368070040003600c1804500743c84440e1038681c1d0940a40b1006021300c210301092081c8420400056842042070212030030070b64034100c1160310b50004a80302e004120000e500203440da46200c800600170340c400c5900c440b000c800e5030030742104d59031003401200003511401000d5200ca10700344001c49402000b180c201400d01e816144450140070060340300c0c06240c040501c10250800024114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 46308025 1250 46306775 46306787
    0xc03100b010c05030d0509010b010c110f060c01020304030c02011e0c0b0403140309030919030f030e0307080a08090f040513080a0207051002031e0a0c02090408040e070903051903050f0307 82
    0x42d0340c04002d0f030340c81c4c070654448100108002c03902c581156080140038490ba5018004284503190840035080160301c3c941c05020b05440d90540c01604400e0400541c00b0101c000c0c406035004500ca5951942640d00300d0000421070741d0380c3c41010f40014104d11004403041e401000c800080c1d40d119004605d00e0f902c03800d066030000407600009106000000c2000007101010000f007400220071900d000d4071700d110350900310762442c0c10702006040710407844005012a0248080a401d8440101240e41d42c80c1c40e031302c00ca41060300150040b6254403010800324110b00d000004c800d601a41a2000c0013286021b03154165082540e050187c4034000000e02c1c4072078144288007040203020044d020684402c20706100943e04d82c46004100c544030118440c000241440b20104d450000680e9101400c64499408000d8414805001115001c1c001c0000154501010050318841c5406403102a019072460408a050200420f98880b400d404050340758002074001d825151021526407000d0703143e983d0f00b08103982c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 46309275 1250 46308025 46308047
    0xc0409080c0f0610080303011a1b030c0a0b090109020a2c0c03010e07020c030c01140403060903032004030b040b0618010b0c0706050c0a030302030c04031e02120c03100b01 75
    0x19030003109280b003a001e00002e07000380950118400c07076218a540b42c0660f61280400e0007101c2ea2030f101010105080101c25000d0200134003844000030802c400543c02c540745a2200705420300c2c40d00884411024840600d00d41c50388110305200a0101800660005040c0c20950203404510a4440031080c03c0305800204c8007103840f44004000524103001e042284682c00c00d00c100c00249502ca0005070b051407012640030517200010340102400c5450000540d44100e14402c040030201003400000042001c074090110118000c0d1030000700081d85006141e1202107085840410742070811040002808039031f001c0f0f0388190045c0f01c0031056142c400c001750f00043c03211108002803240d00000324400c0c14000042c040b0f80c0c00301d0300715610950355031005e40c0d850240040701030058208802d001c0c0402e01a800855200f2481140740d85410b80300e558118411140143d14150090070204950850401010304040050140c00034446070b03d01c18000782d036500c01d8500481105c2c2d240c00c241040340e4000c05500c19 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 46310525 1250 46309275 46309297
    0x405040228090306050c0a020607080601030e0312070216140603040f0605090f0d03060303050301090207030e0a03060c030f02030103020607020d140307110306010506030405070e0c040b04060201020d0b01030b030c040908 96
    0xd80300324040802001c080b51808150303005480c110124500d0396099080301c81c03e030201d070040d120315611808180c0b02001e00130a100e051580b10410000e42c50400d2000782440c0100e103008070418180114001e00c3c2c8030a00b503030750503011440c50060100d41d42599000401c41d1040720525a81d644c1c0780b0744241c100c464003000902c014209400e2010740d00000c40c5250f5100401c0c0116401c11145500c02c9003500d9041c03001602280040005001c800444c4e001003014500078208010b000d0700480100f0200344d000d90041e07035025030790041001401c5d0305026011608950341c00079829541142c0025265224030700c0000e110b031400f80c403040108200d00e00142c04410142e030a0380c2d02c071046130411405c090a041f1101c0d22174018240045450300d0305100744c07805980c0000080c00c1c1c8909060f88021441e10241c140b60f4641d0049c0300000710907920304002c00141c2610750000d0307102c00000e00038005440100c240380341070604114001c40c0a440004184054507021a4086000552130500e09014820245410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 46311775 1250 46310525 46310587
    0xd0215061807020a11100903020d021c03050309100c0906031d010513171602060c010e100606030e0a020f040c140d0501060f02010203070801140f03010603050d030b03030c0304050402 80
    0x402c0380e4000c00d08003c2c05003d15820011500c0303031000c1000c070081d000350803c041501610b05002505000c1c0c40321290078030107800c42c02e1010340c07144441c41403004140100c1c0010b000004110650400b0f01c0320301c400e03081c503039410300c5540000b05000e000304059005150400d940d80710100401d0b145071141c40002e905810007008182042000040d4500c00c240064481d021350084800c08040031404aa165582c1304a4407200300c2999400c01441e5030003080c4400856489501c25800b84c0818403d0710341d020072011002520781c0c54480e0103816030380303142e20700003158000d050301c240940c43e1640c5503115802c0490b0005004091200705841a05030b50351160508800822420b01d00605a03009a050b1103864480701c180d5900c1170012406d03444103c0f0600c0000d95020010040d00d418680c824501c40700040020300700900c05800b21b400c4801c0c41c0c1c020340e110741c02540511350a80d0141314014680c90705801a503e03250f2501e10702503803072040c3e10955020380c1c0d00041140c0501380350104c0f0b1200d00030500d507007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 46313025 1250 46311775 46311781
    0x1707170901090b03090c060f1e070c08010516210515010311070c15050702100207090b0f030a1509020303070302070303030f020304020d0201080c0f13030b090d02150618 74
    0x252140c00504000d804141d0381000812002011416280b0a402d0f030f00080c49440c2102040c46450303088070b188400da40509009031986107a03c84045459103074074050b8203813241c0702c03420034051041c6194070461243c0d141c0814040341c615403c2ca117036030600c2d46042c481055858800400d070103942114a2850040c40c10302401014099001c3c5c40c8072081d4241da050000c9004004031210a1040060045c500412240c00b048080381c070150a40190006040c0542003402d0780d0041194251301c1491080141c00c524003c0c0042c190030f1084401411041c6c03038012149d18918040380d650211514060884500000001c1c616044c0d600302c04091075010703041d691145150310740a0340d125158002100420304020f500c11031030025200f543e1146400800030f070440c480039001035424400140c80c094400c0800c1100b02c12481c0c4680c01000c1c01000e5000c420b80307e52850809a413192030281110340c06803c480000c0414690024500c2c54405000300703e007540c0d4a42e600007a126040710501120601018020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 46314275 1250 46313025 46313063
    0x70509031504060516080a0908040e0a0b030708010e03090f0d1403070302060702010b0a0501031e0e0a0b0610020a02120a0210030e19020108011202010e03030403081e03040c031707 79
    0x40c07500a40c41404180003d44032400c1c04081210760f140180001120400050700a110035000a004503000b171170f0040c5420744445050003140f100b15a8062000d0721461040030504082010000030b158a500800c07680300da1410b6942c41c3e20031030719402d104032407008800c0b4650707039040e0a110740030354040ca0040c1040040c45482e52240c029100c01d42c05070050000140503140107015003256903130010000011030741008019402802d03160390010603901e05502008100003203214900c03040480c00c00500c4a0100b80c5050b10380300c40001c1603580107541c99403603211704a4000078400d0000e0b034100c801c040e0f001c042c0504186042c0119038081d52100d030031540c05000d9505513010240403c2c004080c1d8100035030b040c41b0081700100e401e10013030015088400400040000071101600b0038030524215a45611890000389140c009030426508124009003102290407040b01d405540d99207140300c9800c600d4143c840c2c01290505110141401a020841e00d0088560764103c075503890303210b200f0141d07010b50408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 46315525 1250 46314275 46314313
    0x8150108060703020c1f1b14040308070302012c01180804030f050f010c03050115020c0a0303081018020c070509010e010e0c0f030f01030212010207080f0c01020c07061701050d030807030507050903 86
    0x8115002e20070390a00e00c0e80d80324800c502c8c0c00c44081c0d180c40303800c2ca0b043c95075603500d0080c2d10030305003a02155650540c0740d86070b0483c844280888414507502c0440040c0e003940c200e007100c0600340b0a14403c1c0e814908000000c40c0380065400302da130080344c1045200041d082c0f090401d2265480d0038410b51034001071078440343e010b83c0154145c1d56075401030700c0d01c550072a03416640d41315400ca4896110030164030400000e480342d201a94401e0b49580129140e50b5600150f40203100030a40041281d40c0114101d404844208040e600620080b03903c506a9450000060b0071640d0600541d4201035460f40010780003c23843c0200c039840d8202c4a03030280c1e00d181c100c0c2d500d01c2d00c4000780001c81c402e0404600200c0700080500035110f1135900450031511380544507461190340c1d8000340c001003081d50280300f8001080401c1c0282e000030304107511010214011200c41050541d4140c1115100f000d100c0c140b480825400600c0e1a4000c0c400d081c0050306488905c42595179000d510700c4250305115117407034030a401d0f41880b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 46316775 1250 46315525 46315541
    0x1060b0423010c080313031404030303020315010309173604140603151f080d12020a0f0c020103140c0403060e0c09040201080a091502030108150108060703020c1f 71
    0x2410201c102003108004440c05945035401034a281c100340003040142401c1c12a007203000d84a4140858146442c046040c1c3c1500268010750100e5808420495485803c40c00710707100400c00d2900300984c07516540d0740c01e42da86005203004900400809d03085020140c80d0a0101c8102c80d52005c1101001c03001800000548000300da01d0265003442e540b02500b03600b010703e4070b00500d80180942410421510341074400748000b04118021580381c142d00c511898980c0844002d4401c0c0782c00303040c4200b00c0c01e8000e071a844032410390200e964810014891666405410314080590390310700300c40080c5a500040b00600340040301d130405070341d02d80c0170b004000150030020f0040784e2240d5024025104003030b00442d00c2c1ca0401c600190045684000100158842c2c082d19501034107040d400500076140f6180c0f5281d0368078414062072480e50010041c4200403040180c3d24030b965518568400a46c14024041d03120403001e000c65003450303004124400300d21002c0c4105030310091130f00180303c1c000c05c00588100160000c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 46318025 1250 46316775 46316819
    0x9061401020d1d220507030902011403070507030e21010b030d0c0807022b05010b1c0c050f1507050102090405010e0c040608131202070603060602010b0a03080c01060b04 74
    0xc440c80c003166000d60011070f8000b019044800a40e4881c00a00001e40200700003801822403a10200c02c0d034620501ca080d009418550300019191032600c0050b06004141400120a15042c400c1000f001d52000403220340d00e6140c945002c0e4601d0702d40101e401c0345140719100000d15442c034500c020b0140158002d00c0707607503011802c42d0030b0700c0501e0780259418000300101a103292400c000402c05800c00221b4501321069030300110a103500303c0c4c1d40c600030700c0202c160304036150b9454800d08002e51074a60007103880e5002045502d80d0002d203650344c084d40761001e84203085c0141100002000a603650403414003128143d1000d040e9201003500d8064000d43c02440010705c42c0e1310380300010540380c000010302e51003071500407041481c1c07a0800e0020b640f01c020040508040c0c107030f2600400006a8081c2c02c484c40c501a64009013511400c211014058800d075030404800c581c50b0401480040c0c2d1103042e503200326600301c803d040c0c0d2808022400340c090651038000a20071715000400080b0400d032020291401000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 46319275 1250 46318025 46318033
    0x2304031206050409110f03070b04080d020111091e030c0604060305061e0a030602070804033509010207050f0307091103071418011209060e010f0615090b03100906140102 74
    0x11803080008a807071301100500f60111600c20308860303041510745101a400c00401301d804c4103030b548920800c2d5500c2a0005021a040402c0317403419641c09015102035100c00701685400e2100b00d8002c1100b550b07920068001d101103482200360f540e24180245901c0300c4024000710360325038980391b01901403c3c007078074145d0003100c0e0968043c1c9450045100a84181001050030000701c1c510745540c0081d4002000a64050004100000000d1968222200c0c2451b450315520f818071600b03e00b000d00903424000800310031804010303203199a03901040d00000e642040b901601c8011030040805c0c60905140c1242c4e00c00c5281a402c2d83d07103881c400003d588151060341c0c1d03048075503824a242c4003041c0104d10701550440c100003220700d11036000300d048169400b0010070000304100d4a4840300e065902c11601c1804c88d9540d1031964200420324080d0b44083c3c40d01000d0701801340e458a000800380c15861145814101d800301c041096562401c07195801084e8540c03042c0850358580d0945840318402103c200d01601c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 46320525 1250 46319275 46319279
    0x601090e0a0e1c020a080a02010605060d0504060f060b1912090605041401060308090d030201150e01060e1804020d140109050c10030c020a0809030a0215030a060509040b0601032304031206 82
    0x41c3c004400a114500c1e400390500d1900ca5846042a1b0080550785040d5502c40700040f555403201409005d04150403100030a407420b060810300300711070800044103201c9082000c2401103c094000300c90b044003a500f2000c00004140c074081707651002040100001500b0102a4024083c9035003001d40114065040e041d00c52440301c80e5142204c0081c4001088204180802d0489103859018000510b02a00000c5035004c8607035204024070705107800002102446100500030341e40e0060f84901580c400340c6401c80c544c02d8034030301d0419103000200024071500d8040c800e1410801c100f0360041104d9158002880ba004c403e25001c0d407030312003081d9000d015031442d00581e00c3d500d109016041403071159070054030010291b900c2e4035400d540300116203601842250b200400580341c2041d072032000980180b05548030300784800004159180c81e802075100798001410b00002c11800c1031820b4008509080c00a040400741184039604202003600803520700c0d001082006054001d118001c0200313544601700070b4070b9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 46321775 1250 46320525 46320553
    0x2030c060307090e040201050412030207080607021b06090f030d030f0f09200415090b0f0303040e010b16080a050c0c0102010519020318010203070207030b0604060b0306090601090e0a0e 81
    0xc041101d81e58002800e005007040304e01400c0c00080e410500614100b0f00e41512820320703000c00060b112084005900900003042002024405190000b078984040d04500b211069001c035800781c0040b0440c441c2e840042c641002d607681d201c0b41e50300c00e0700c0941551880303c81810046c005044425040e2101401c0400710000d43c034861044d100c5995001300440e8406640002c20346040a00e0155150840e81d01d0920f010328000d00c0c1d40d41e80c001e140ca035030040340c104021802e10070019003040c40180a544180002e0241c03000d111a000d040d0355110703540c0394032542c402d98980d4542003180c01c00351445d000010204d00180d8840024907080004008071200550200012802c80320211024170308668801c03820000690141c000b1038005502d50112001003d541d0081801c9078030680d05503002d030748075000400420040c291000d501c041d04680070865685410884125403000412580c0f29003003081c002071817070780100702038000b401c40c1c003216024500e0b02606400052110381211001d40c42a011090480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 46323025 1250 46321775 46321777
    0x301080c060715050a0f0213080f06100b07030e0604090f0b0a061e020f0601080c030d030b0f0f01031401060908011404020f010305071112030708010506070224131202030c06 76
    0x141d83c40400070305a10b0080034403030000c002c0540395000440c0c40c1c0e8415085407040f030010741010144840c03e1081240b070003004c0c501c1c10307040c800b50300e00641105c001c0204220b5802a054100c03010741c007806a6a003150700c1e04a46d51101c1480a43c0e2124011402003240022070b8000d0b61490a000410482e09c0b03540f07000c0102248241c40f03414005070b05484103141c8405010406503080c0454012600e20170200c610450a00009070403a55955210031100d1850345403c00c0b09060034850b07420700300111100100800e00c2e0041c1039448a0007018031551900590f40300364891020080003411035429543c54100040078007680788240b00c425070a003000d102188070207a03200ca002e140d004041c03841c5121400015000b5080050412003440850081c0b00d100715000e0082c082c103100c1002c0c46540c0d07072070049000b17170100d901a088103000c1d100a212420040c0c842032680c00e56945509080214101080d00d06000c5226903081d42c80e42c482d000c440041c105940c0025480e00c1d078401c4041d5074000080c902807040c6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 46324275 1250 46323025 46323037
    0x1606120606110d120b0603010e070f0507050615010c06021603020106060207050303040317070203030d05100603051509190207050a050114040f1403040b0c0303060909060105010c06020c010914030301080c06 90
    0xb264002040c1080824040c1d0f00e0444c07001091440031440b0666040098083d030402d170f204214400c035510400044075401107426a0700f44041c18a41e0411050340c40d200d40c1d8850003800440d01d030742c0c0901c01072074503802000600d9080d036010030b040d0b40d144604018183c400345024803ca004d5030901c900800c5843c00464040c0540c1c03c0030740114202803840e00d9440508055000c1954411000c010801c09a01d0134030041294040449005c61282840ca031170742c1e8551066889241010700c0e000c144000018035a08050303641400b10b50100d02a190405640c20305400400300400e11403000500d20304020009c2201d1003503501400c02040000300551802c07682c81000c03075000f040100b0900f071160008480e101e0b800900719480c400c49050645508503880c0c59408003030760071038550000c402c10501c1d1801148003079200c0c04020140115514000020703000342d4851800400150b004a00c40360080025032200c0383d00f98100081c1c030f41088001c440c20392a58000e00a2060300c0c000c0b05414030150074501c00b1224 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 46325525 1250 46324275 46324307
    0x120c061d0105070611030408070314070b040f020f190504050117030f0703021609020304060c030911040f110301060305090607030b030d030519090b1005010804050d08091606120606 79
    0x1581030441001102c165200000c11281150360314080807800782d00c00c003d03610892103526515600d01c420b050103407034204a0300c0e040000346000c00ca5000024000301c007a0307800c0f43d070100582500310381c1e9100080209152141480e0130910301e0000c804e18007200400c90742101d90a407000c0000d41d80b29880303415401c42074070b5078140f90750003000f500004200e00c0d401460010b0003881540d91040144014915440043d440401e1060300401401f0a02440744100a10180c0c942020050069151b030f42e04031440c01900914421a900c1203410703072179031503908500c804507203010640b55250b071242c4026000300400d4550080384e10038440040d54180c000d11411060010080040a840740c0b010300450141c00010031902440d902c0301d43e80e01c0c02000c14003802d107803144158415041c07841c000c41c0d06c4030791014a500ca00c2c10418040300740b0010500100d0824040000c511b041e143c0c640d1000070703052400803245213202c080c1c10b001e000040d90550006020020704110902403000c182d4541044511801c0201c101c2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 46326775 1250 46325525 46325567
    0x6030b0406120305070201020319020102070303061202010801060311040902030f0f130b1f05190510020c0105071202030403050a06050123061c0f06030b0f0f160503060609040204120c06 81
    0xf1900560107003490500c140b0480740741001e00c202140040030400104c10161390045220303010160580200c3c00646607042000001c1102030700000c01548041c8200386c141603480310350701c0140c0c851070216406480c040748250364909100e0035009445001321004c01d2010000c002003014629800d0500303020790b8000a43c4582c41c0c56024000c00312100b4015a046d64400301100007460303403a1645003480ba60001c503c0681224601801d022411001703030310710002c641208042000603038010301035584681d00019080715040c5010016403641c4195003010b0620f114214800c001c20003a1340104d0706070391740f0000112403481c0b540b150161039006a0310320743c1d001005200e0194030001403503e900301c0307514040001c02c0780c1140303591880840740250000d079082c8a03268100b0203240010450309410100380c3c03014060614020900100700c03240600e000c3c0c10041d000000c0303145552041b06480300d0343c80040085540b55940c44400c85403560781a41191400e9180c4030000d1784a000d44c00c5441c80c00c203078100301c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 46328025 1250 46326775 46326809
    0x6010e090f031210090509030d060b040b04141302030f09010c0302030609070f09030b07020f01110406091a04031a06010e0d0b0117030415020c010908030405150a030b130606030b0406 80
    0xc01207400c1c00034000104074013507420009801805019060084040e00301944d81e554256035944140c61854208400d10b24041204211201d0b9040031a0102c40200c208415426200800181244405403149600d140044180038001c90802d803000d0043c0e15002c02002007011340e482c1030f0168081229100d9001c048030001501c0c4a004d0346090100b01070502d00004e880d9101d03a254440c811080c1c3d501c00040e0b00041100d020f001c002d20840081d1724000748003e052500d052401800f090345401440e0b114180d03020001c00301d4410409403405143e111240c14920040e0416468044004544a074005443c9034039588a074104500490417041e005a5009100c1e0700f03021418101131480343c1009240e02c4100070004600c1e000481895041687d54080e2920006c03800004080c2c2c591504000d0058208000c2000b460b669105003000c0300d840c044c0d126485820600c810b03070091500c0856650082e500b01014080d62a4a0380300a00350b071841e403001c0050783d10307080600080711a10700031099501c0e80c0c9214 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 46329275 1250 46328025 46328047
    0x2009030f0105060a03170c0a030201020d06060804020d020d03110304030f030e06090d0209090c1e030d0224070903120f020607090b040308030615040603060e0106050f0d050c0d0e06010e090f03 84
    0x3080c6c0d41c181049980603d444030001415140220020090b00141d50200e122050071465000f070300300274401460070400c00c0c2015000100d10f404032b0b0400900c0b51402c0d80c045c030700301402424544282101902501e8a4582e207043c0400031030b040030301c1200003c00305810044036140020541c1d124240107400422202296400e03c1003036000a800c1d126184580404501c1c1951240c6410b5602280d1501c189801d500c00704c181458030211070342c4e40c02076400c080d0a04040145100703080403510496039200c4038581319440b00b40d031000901d40014002c5420320a90600140d04001c0b110b406400583c2113401d070303a4440800315441d050502840380d0511040004002142076038014542065004103058092000803007481030fa503019910081c042612581d040080c580c0369400c450060100b0b05142e8035240010300044081d00c00d080a1500755962a80407171507910300401a117042039098a41001468014500c41da610402480b420001c580c4000000f00c005202155204410300c5500045081c6403c1e429 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 46330525 1250 46329275 46329293
    0x3010e07030b03010609060f091103040302030d1a060a08040308070302040605070b09010b0402120709060512130f020a140906040c0801061409030307060e06090607090611012009030f0105060a03 85
    0xb2505500d50340b50300b00030402020b1071007071030b0003005039058280d4100c0c500744400040d00c103103a4002a00c4c14040c020000440e80110403a41c1044e004580020040c5001e200070074259217040600742c02c05804514034207041d4018007014000c5000c1c1d12140030968511004400760b120b80d025540000300c040c0204800940000e280c90f402125810011600810040c003160407a0003c4c9100443c0617856014008290b40090508010b054540f074003d1425201071184030480c01e000d080c1e4600c0200c12182242448000c03141d11301d4103980208a001c4480e503036083c06840442c9a400350b4407c2c40c0c210081a503e2800d8403038000c00300095116072000b070b8640042510002803c0804004901c0c0403c000c0c5001c1e601030009280c600d10401d00007400c0c040380203115280202c01003401c0c0a81d0b20440a000d00160011255001c640d4a80b80074490f880302c4800407805845508070315a075104040c4c600481a2881034080d12140009a08940620401004850aa44040c0c5819070001d44075601031000c0340e031101e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 46331775 1250 46330525 46330541
    0x3120405150d0207030c0c060212180d020306070305060a120203072108040e01090609051e150a1401020c0108240d0b041203060902040305070e04051507020f100203010e0703 76
    0xd042c64000036410b0103070f034001142200050b10703841000c8100a010804000584503510003044620071042814071988503650300c1c3ca140c01c0004001c254182e0f1005218202e031503024056a590382014500a405048181d4040f846034404030004504900d004110f1840207070000e000b000ca0a1500e4541c0c2082c0702814400e040c0700541e420a840030031000c1c00180001c008008001100d503161004210490703800b50021414642050140aa6007440a8080003e041c02400c0b000342e076214081d42c1e0842554120300d440d0804001c11000503103014249003040000c01c00e80941d01d8041a00e00115503007102207504900d404980a4808407815401030040c81030391000d89036558410454699901104040740c00b100c0340380941c4014107003140c3c180120001015510001d43c2800d0450351500c4d159803413405800c0e080712251700020140311042100701c1d02e2005001881e801740c00c104c01c3c020b48848101715032030030038480d500c0c181c1c0c421441ca2080380d0488031004200c40b03e54450100071005400c02c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 46333025 1250 46331775 46331809
    0x803060402160f140c0609130f0f0e01050f0105030d02061503031204060b012712020a0f0303090317073201060603060603110405060702060705030d060b07060b03120405 74
    0x8025074070000b2804406100c0c0e43e4000c400200080d101240d2451520740b81004a5020f0441440b00741074607145c408242031180c2c00500f000c1902141c1d5179078480240800580b402149084c50f045610908066100030300500e5801661100b40c0e8a44090696446080407604016480f1301c00041203040742c1036940003645002000d483c501256070004109950382034409a84641d40c132000d00c030407036070402e10302210100c0c4000015904500365040681002031481618001150030aa80d411941d40f500c22601038444c6106a00c3e01c180c030b070709008246c1c00e00b83c001118084a1100c0c0314807580ba0801c1681c1c00f595120654032280c451001007051801b01c0c0250407400f4519040c52010508000e003d000c028123069600016401e15100c002015160003020020300c040040005000c681c417000101d81c0c405030140c034002d69400291901a05c0c610038a41e114402ca8600071000c1440801000280003040c003d900074020003160f0410161136656400d02c520442804110400ca1814400341e0b6030102484 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 46334275 1250 46333025 46333057
    0xc0d21030605090f060120100f090c030602030f010b0708030a0905030702040c0807090905010b0a0309020d0b090303100504050621010e06011d0702030c0303130809130506040f090803060402 83
    0x500c00c0410704095007518080c400070785220170000385507030004110100b00e080600014442001484550322606800400103240d03032034689a00001c0015084200166800181d4555070b5a4074145031000b50810390703103180502c5120b000001c8004110003541c0743c42340c00c84c085600e19110f5203142802400201c900721850300040c00741d04050391b10742c41020380304210341e1035114452901d0300005206100ea41c001c00503151410006100182c009015545d112020f42000036448040d4000942c4210003184010a00854482002000340001c0082c5005168060800703600d00e8480003004103407001115110741040c084c0502e10181c003140001300c0c800001281c00010380b601d03030050941c2013040c00d8006c2d08103140d015188030640020910400e62250052000c4d5040c000c03d40c5000d43c80e4403002d0b0004222580901071a021300022604a4080c0440100500d90450101c601540034002c1140c1440c8102d1070100f0b16800b1400314003542001e240c0c86010545076a90304030800000750040c100c03d40c00b400d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 46335525 1250 46334275 46334279
    0x2040b0d05010501050a0902210601020304030f03021b01140d0902040e01060803040e06120a08030c040b0a180f0f03080315030d17060301060609050d0311070b07050c0d210306 77
    0x40e40144944103500540c00494658100310038020041c110380c1c00f4182c1c0030320411640d240507422100843d04a40010000e202d142c6480303004078558051500b01030b0104c2c0400c10140105500022040303080e4440d018003e8001182c100151040068481e07110210b031000c00040406c20943d500900c1d285200400c0041d12502141404d400c45036150040b180c2070f40b000030180300c80510300c811150b0003407007150300c001c8088543c21070b90307103c40c0c041d50010046c0b04c0100104041e82c14200544000c0d04240c154561a040748400c000d0189072510211001e05180f8030380801d020320f050400070203480715030b1704021905145545040180e0b1004008100d098070b0321519040c0b0381e800344107000310903205a0701c100400c0d0300c80c1003030100003038003501681c403036803404c44100030701d64100c50254110341d01165102020101d50600b0303101129410302c115424000c507034011440d00110405030030744501a42c100d98240c034100043c02140c040c00803000d8a0010050010420101079000703071003012050340380200d5125 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 46336775 1250 46335525 46335529
    0x1806010201090816020901050d0206070b041109281a100e04060305150f040210030b0d050703050607180e04060e070906030803041406150609011709010c02120c070b0702040b 76
    0x14002c400711001000000803a03000394504281e46a01502301200c01d242c9591a07680010344520503100020000c1030390030009001c4c0302e83c01f00f104030a604080c00813141490110040c0b8614502c02c802d84246036040b0491030f60040130340c4a001003d43c09032440061000d1600c040226042c1d0000000042100340e044e042155110740c05003000440c403c40c005c21501820400c0f001402e0300041074400c0408205040001590760ba8a0070100c01080b0305000540a0340c1c0808581100321840015095124081002041250010384140f007007001ea955030f01c0d090352240c3c0c8100302a8482c030549540c90006408103001c1149540204902c11006013100c0d4560f40d2280f011054442680c000e451200b0080200002d12440110355006002405c4c0a014070f0320f46101c0007101c810f001841035000d4080800c11803802c0c1d0241c41410000100e26000c2c80320751400645590180c0410410301c0014000e10421701d0003031000c102900c61001c3c40402400409041501c40825504054400d9074015200d6074548516 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 46338025 1250 46336775 46336777
    0x10e130c0e0105030c060703020d0503040c15122715140108030304031d01050d090206040503010e0a060b010306050102030415030f020d020a090803090a09020f0c0607050406020105090c18060102010908 88
    0x100707a92410681a0b6143c041054207081d88840500e004150411000e070000b580401d88844c05406820050b440340c9035400c00828034042074001041c40b40d59803401820301500101c40341c000f01c2c80501c0c140080d182910400a00b282c00c40a45418070035045480300006140005103c000ea81042d00060803000b0224480c2d4681002e0b0721555094000006010074150b201031425145642c214958210542c407000003000c610841f2424550169159810720855603031200701d500503c4020000d02506500e202d2a580710540b44c8400c4038003602d4400119a154003a000782400c8510580103941454070f01500400c3c0c424000b4034540c20965941c540b829407040710b20141c840a911280011303100c210380381d03000e40220702c00d4201e80d41c1588180320440c131555800e036141e01510f00c1100d02507117a10310841c0c2c0c02428001c00850b090300d809a0030801510591040142003114041d0f4000d01080e00c8502402c1e0722543c900c3d1410360403490000d29a10a68201c090160308120103100001703600c2030546039a849 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 46339275 1250 46338025 46338029
    0xb070b130f0f0b070305280f020a0f1101060608070f11010606110d090e01140d02030102030406090b0a02030705090607050f0a0605010f080115140a09060b090108010e0609010e130c 79
    0x120031441d00440240032a400f01c19034000000d0a0410440c2400040b00340c502c400c400c0340382a00c4500460803c03c0d103005410881c04404081815500e403a500c2c00041d00c403030100c04050000810660380491440414014581110300945800e90581c58103c8115401c03c02c0c05001018071030302030441e1807071060921581c0c6c020442070341ca03144550400300d90242041d038991040c00402007808401c1c4440005080114115070f07100b07000000030040c0e0300104004040d1090065070651022041109011090304040032143c0306a00d8031500c0c5c1d0307171009600c00301d000995081c00003410610500320720741007230002008880d0140040b0f03060351012003d0107107410300b1500e045400903255001080180002d20100d809884207000074002c4032460178100700310300a9807140c40e68400442096502d41d4541652030701c0900604041072001e1034a4100002440d4014031400c0c1c005001d1000020325080110b2a0600640f401040300e01c15906e05040d03110544400341c21b0103402c0c5040c10f00b54001407141226000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 46340525 1250 46339275 46339283
    0x2102010c1d090a0b011403010f0e0a0c0f0509030a140a050708060903040e0a06030803180c040605010203070822091a0a05010c02040903030e0f0109050c06030f0109051015020a020907090b070b130f 86
    0x80c6941040d0b0484ac0242e00905810308ca20f0a00402132200c90300a02a003041c09260718081d1b44425580c000079140100b2070101030080d45146482c0142114045003554900b8000c1c0304450b0075541e106c0c0c0c400c3ea100000c03541619150414081803250402d408281504000035a0700841e03981e4490b142c00d1001c0d4000e44271207040c1d00301645101c04090050001d6100b0307100458040019501e0500040d49905ca1040d0060603044e00141c08265195000d03196400600811250502d040d25208003070000c3c14510500c0540e0806880800344034174281400c00240d403810303941c4903d15040740d820301010b012803c6084051503280ea003010b0003440200030340d0403090000c000220340b9201505085003032607440180103010300c604004002e100a0f961160504680c8101c1c0b000030207944a12517600b03050b0150700006151110004e155021960000d203d1a9180c003c5a0030b025907150850f00f83d039602c030703a48914204203209001d050089034211542c43c0d40516580401201c0120a5403401c03040903588070115 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 46341775 1250 46340525 46340549
    0x80a0f0e040f09140c0612180601060804050f0601210606050613090e060105030307030c05010b0a1d0609040201020c010f0306050a0806090f06040b010905042102010c1d090a0b01140301 81
    0x30500c081183c5080d07290120f13202802c0c40010610100e9400e11850031074041c00401c0e0801315460802540d40c00f807180e1000015103489503142c142c02024944d060b107090b00c441c03050594044886401203002d504a554886284411510200344814450611030090780c01da6618031001480d85c45030300046c1541e030381b4401da00074403d003130544540444103900740c01000395011100502103520004111200c103501414038441d802e819140250140128042c00d540009010100060055000000c0c2d26840b40c0005d21019980e100c1080c030660320b1017110082d006030b208501103101c55018840d10b0140040301d18012611a80340c0c004554503025991002401e503102a0070481d0b0700409000281401c1c41c0c44024003080c2c2001d03114981c504506010746010305a44801040411500400400c40b400c0075011505803e07901010103402031a844459030041001061141e200070070007031140e41642e20003003042007140c6901e40c03c10000c04085030b105040c4004440b14118000a0b5005140240049641c2c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 46343025 1250 46341775 46341791
    0x1021c0207180e0a030c0c080d0e040c03090506040305130905010305070e01083d140403020f0a03050304080306190311040f1b0c0809180105090c07080a0f0e040f 71
    0xc00690004000c44045541c03401d4107200580402040040d010317a00740c079000c02280c2d0642880c0341880340a5000350350701d00c14004d0303200c1126006450508a484110340802c5100c402d04401d40c01e8035507614004009400c0b000015002a00a202600c2200d8842114001d043d0311820307108200c0b01c1c2078006590b164072415007041080500049103000d4102c0d20040c11145042c1d001c002d91000780d4455000540c010074403d011008194001006052101d01042c040b0702c90b124034820881005030303000d0b0b0042c0190784581204400000700c01d4a0103505a4802c3d00d99074444e1903c007040c5e00068600c9500c0b14500740d040381c0c0090300b5901e0001950060000c545e554407070303c017040121200e4a50151840e420007140800d2812220401480d21480c0d00301241e07181c0311840c08070164400c903059030354000711b5201800c0c14400c0f8420040c0c181c800990b0305030680c2d110b421b0484440d01654500928160041016005c200e12880c14011034881e28202942410040c07000913064130088045200740039515609 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 46344275 1250 46343025 46343039
    0x301050907050f0f0a170103031e0504080a030e1f020706030b1009050108040314030a0903030b190501200105040b06043e0d0203040305030106120b010e0f01021c0207 73
    0x10481e0812074605000e440c040ca80c000754a0305001d400340440c3d01c1d1602180c1202c510707004211070760071842e42d444d145003103607180d240180c80f0130032405110200c0c03060011590405800b0b9412a000e03106039000800e0609401d90b41103e41002031f818641e08000c1840c0c1d071100300c2903200d04a41403c400b680203040c85a003007850060131103000b401c0b41031265200e0040c04d0410b5810900d50b81c1a20400c1c41d00c0c0e0398540d20b03411b00b61007408104080200c600030010400090049560081310701d6480381d40c05018804400c4d00300310800040881c64100c01c0b80e14242000290f0103071414400d4076001412200e00c0300d500c00c9130a407c4907421030301030790b00c01d54040c10051a4034092246a0190490b444540744050608070100e0900d00184e541c50850030302c0241400500d0b003520207589070290300c01f07401e654030700c0c0a240007400c54000b80300c3d01b40407450154941c050303600d00740550020208180c2d15851062074000812a1001ca0f80003440e0640c0981c40d083c00c1628100f81e4400701045c0700790020000b803880c2100c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 46345525 1250 46344275 46344289
    0x30f060f06120d050301050d11090108010e121201120f060c0210140405060f09030403170901090501140706021b010e010b09160e060a090f06091a0a050306131b05030105 74
    0x1030070280341d00070b2080c402c0c60f103411100752415900c2c180d42c408202440e034940040c8003200305050300d5100104200015240c601508410415850707001074903000c060340360b810f5049000c0c02c4049040d1041d8403006001029000b040708403840e000d8800c0035000442e94481108072540301d55140c006801c03500c40310201100d180101c2e14529000c41460749240b61948030142c545902401908801c814003004c10003141082003030350050b603044403007071554201d0104004a40e0707000514a601040b48520f00181d2503004241c40d11644240321509446c003034480d52101d0096000c074204d41100368880c085100109030901c10308154103681400000c00503c000100710b00174000801806a0406491a164005d580701c4010074000c1c400b41c980549904640c7d20035a0200f00c0c41e00460b08010014400049056000e0f40d0340d000c44081c0c2011444214103420b19010318480d03007030160301040302000401c030141045284440c0384507a605000420003424400072403102213209074403000540104c0103022030703d0101 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 46346775 1250 46345525 46345549
    0x20c0321040b01120206030a05150a0b0c010e07150f051204060509012a0c020604090c020303240108010b090a03080c010605011b0b06010c06060e0a0e010f050601090b09030f060f06 79
    0x42c121800c3d00e1105e074000f9a1078440207010040030f503191004200b45615080e00704145940040c884050b0588882d0300b00b0141e00800c014110640c00e1428200d5054800300781c4900f42c0352254000840d00000c50020f940220807088070400f08882000521185061220303c1806a4800c20380424241064900f580c05c0d503120a4422800e001c00c04480341401c810301c003122082c00c0d81820300317603540f10082c00040d502d8003c41d800030a101d030404120081e80703a400310065129040e850460340701e4112280b40004907200b0102c4d0103010880c03110040c0858002c00002e00708107600248401d0f84140c89588408580e00300b231000300c0c03d6a450340b906121a40e0003203400301d81681081d87c1c4444498a40d00e5420b0712480240c0080c0c148200c1e80388880620007a500001c0103000102d08151203800c0c04202d46000b0006c121400034036519140a010300340002e4003ca80c05070308143d50388401c150400100308082d502c0f1162166152048040700c0c40c94038400c0c08518400c2c459191400039515111080c050032803948 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 46348025 1250 46346775 46346789
    0x8030313030f021f0902030a1a16020307050706050309010209030a0c0501230f0c0a140d09050d0309090509160b0301050108130c090507090504090b061021020c0321040b01 75
    0x82c0895140099460f030b2030b403035008800d480401d517031803d0700120781030071011400035100c0000c003072080038a00d1a9421040c0180031304132641c0103040d6184401c907207a01500c100202640c00520f410082148180301860304440a40d00040c5000c15250029192001c2d80c00c0441d041380c00003504006660b0000b070003841031620702020004504104c95070540c20300c201c2c000780150220100398501d03982001c00c0548500c81c2d0080000e00240700f450041641d55001c024858001408000c02107100d04000200300081a499101c28038681d01742003400000c0c00006204442c0c0d841000c2c0d00817002d20240c1060401070001800da07a650b0b50404e4001002c0340b500900c21740109038450304501c00100030420074012103401040004068458010840d0040401c2d40659400350808664000340f1901c2e46000f400f0305801c4038500304514044200f51010066504645620710441e10002c1c4001426001020380000d418140d9190000c4078003e07070112a03030340404000b8030036400d0412042224801c611409130486c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 46349275 1250 46348025 46348033
    0x3060f090201050405130908040f0e010b0a020607080912121012020a0905040c0302120d02010b01020615090c0f0a020303010603060504090818030c0405010b0d050109050103020609120708030313030f02 88
    0x180c0d03000a03002c2d2080344222405500344d1001c0c120701c924a070307001080300703640000090340e51540e5100c0c68140c0011030183c510580c038104000135a0080500803100030411540103091075a6452a00381d4400344011b00940e014000c980004401c000140b000305070040d5a0340702058103040c1005801c0d100d9401c0d8001110007940c444000025940b010844800c07030394242004100c69441d40b504403002d10003540029002015400075451103900401c9000b1844903035070081042c010403400480e5100c2003074a50303081c01c4da030039a01e0081ca0301b00403591035030104451400601e425416040d40b807040e03104242031001608040018052554540241e000400084406000c16030241d1910052440341c0e013854110b00340190001c0074583c6040c89491090302c8003e0003040701d9030750381c4060583c961105030304606051404002080c03a603814850315040c1c03a0098001814038a5140074042c0700d905c41d4040403224441c2600010ba0b00c481080158030400d8181d601a419000c14580038265442c1c0380032003000d5400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 46350525 1250 46349275 46349291
    0x211506030c04060e0a06320a0e0301052809030509100807021203010b040504240312030f0e03040e0606040e0705070201030c0203160204020906040305010906051f0311060304110d030903060f 83
    0xc4e101005210104210709030000900c241840b040c0b047d07414084200540344042102d0565541050340074030015010350086c081e946e9124004070207842ca20b40381c508039060f00c1a500f039240600d58007204015209040c02490f140b207820000d0107112481c0601c400007809481042210360b418401144840c1c02c541c222030841d41480c400120303600440c05801c0c003496844038001c2c4100c080d2402c4003031009001c00284005910b9003041590b10b801e007154200442c1c1484030303c0b450043c03140701e003d103141d180c14051400c00e410034200320040c0c40082e0140340e11690a11003c10b94103e09003545000f040c1e035865143da610114400501a5982c0001020640d007062040d446401002041005510340c12034005a903041c5000020b081c0f40225000038140b50f1a19403041c040100d140d20407400b4014981d180181e4001c015007401d10032106020090140c1d19005000c000c5007014805107411034454500140069100350204190b240380a00580018210501c100300388005441110204034490400b840110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 46351775 1250 46350525 46350527
    0x2070c1403060903070219030204020307020706030b060c07030b040303060302060a020606090703020c1906020c010c020304080f010507020316020301020f0d0c09140a05010804080c030a0c060e0102211506030c04060e0a06 96
    0x1000700b40019000e101f00d58891481012101480d2000e10f41c028401c54690900e428001e40e0b412103401800c010901d0542c00c01100d19180e025100300c292280002e00600d400e40d0340780450004041c2c0202c052544410005c4010382e902801360040130f48540c001d001c01e01d082410030210b81c502600d110b0606104111090144d4004542c00c0081c13443c0c0003045980d0360484c074061000f442082c100d00255480c004032480c410f0b5012000704215103511040350001c4c140c805085080311380075101580968802c01c07250f10322640010214030820700040005013081101c03040703600d00798000c10102c5d01c0155100d000710704480d04840c3d44006000325811000f05010303c3d0000c2140c40205009550620207040e00103030401070128100e4102c540c2d420241c036144c2070b240b007018001d0a001e0034201c1d6a01d00344400810305003414800e440400305101c02c1080c0038150400708035420b4101520822040704107041450281e00c0300c0c0700031801203103c0c0704016174079171600c0b000915a215027082c640c4210f95440341003000c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 46353025 1250 46351775 46351777
    0x1603050115051b101e110a080901020c120918010e06010c060609090b060108010902030903030103020d110901030b100b030103050d030e0f0a03090e0601020109020d03081902070c1403060903 83
    0x400e01a080483d07540c0e03220412060041c42952003848144102c0c1c07603441c6400c51503000311080c22070003803024103003440060070322054841112000c031505000380441e114007445456165040210300b40014034000014068504040c80001d080c40500f0000800c03a001b800c221040d0341030b0800090705980700b941003200c0034125500c081e10303e80c100424810305a090061a50004d4003c024106007004000c01900d004040700c20300703e83c018080b5444000005080d1441c3c02120700c0b480b4103c01031442c4d40e0030b5a0800100300d0081400307039aa4074248035407100d152189101240a1030090546903034034605801c0d4495000450380003102407103000d00c010800501c00085c102e910b0540e03401e02150b485404e40405280c00307900c8005440b581310b0702504805054018940c03805645101d610f41c072144c0e0301d080c01a42070355400f2000940086407802054042403091450507080440e07201890038601a1442c080309a8016000c2501c403202d462030104110118100010706880c01a409002d4501d801030031a034903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 46354275 1250 46353025 46353059
    0x10e010c061d06010807060f0912080a03020d020d0e01060b0703120207112d010309030c0b1807080c090601030b130e0a02040203090c03010c021618021e0316030501 72
    0x340c941d158442842c82c2d0a10301e0600c0c0c4402c00440300070b980d6030100e0995441152040c0c1000c12050030b200c1c1a40c510032403074038064a620000c1c158444900766545282584041112000c0641c03e0003001380070341c0c6600003410700324500030011660f0361003072100c2400c4618503070084003981c4c4200311101c00650403003c90140c0c10051000141c8504880c00c0400c040d0001aa0f061380c040710501225484021051118407040341d000b04c84c1c01036034640c80043d8101d80e1b07800d0b800303800700d00c1c0d00300c052001510b4054466030041c0680740f80c206407150001e02501c0d1030060740200e02079422004900401c1c0c2000c4040300e50042c800d103418002440080081400c6070018540386408a46608507044031107000c20011140aa018208559915124200c2c548984514901d0b920950801c3ca56402d030510010360010001024900e0f01d00f0701c0d140807508195890002c6868500c00d80a01010394982c500c100f8030320544540c0a906036407440c0200031000041d117800c05000505161a005028020076000a40701e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 46355525 1250 46354275 46354283
    0x604080d030504060e01020708070c0b030f0c09030127060e0106050108041407030f08030603010c030b10121104030c08060f010609061d0d12020f01020306091512030304060b010e010e010c 82
    0x905445508014002d0400b200d200d005c3c942c0002040320812854800608002e4000ca502e1415a500c03a142096184000d8450110124494020880c00c481c902c0042142d4a002000024580c0181d1000034100d19400100340c180d1007689131010911107540119407000c1c42080c0200202030a00b8000fa00020002c6c0024000091041c5101c64841c02044600c020795006108030b0292402860000042d42c4102c94450082d402c1c030004501043c02800ba0161b0315400401d00c49589090303040031124110380b00659500c50b92200d08107419502403c0c024006075020721020040c2c1030402244514100f4003421005485184d00010015150b102c10620155011403030004003105101c601d80c040b0303c03c0d20f0115544240c81610b100204012100d203101c3c030080c95000c3d25070142051088500301d01007241d195401c0f0070500001a6800b209001001c0e1a16000700b10000091803841914034542048404980243c0e451040e275415603048050b00d500201c00b403034604001007010000903c50080100010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 46356775 1250 46355525 46355531
    0x1150e0d02100e0d05060a060f05090603100f0f141e0106020601030f060b040c121506091403011112070201051003021305070306051804120509030d4a0604080d03 71
    0xb0100b80d8494020440c132640201c100c460380d0a041c0b412400800940c4182151005c020030005020301748194154446c18000f40505000a40280c0d041c000d04203000d56681000d9032420404452030492152481004009001070018074010744144a00112103001081c1e0000b601c00401025900003841030659a00c100881310b801140d00d80407000d081e03005034807580181018040032070503074440700c8181c82e8101e05000f84052017030640e032603c280f40e2501035a00003400200303041c8008101007141421510020b0000554100213142508007034002a02002c01110a0340c14081c406609014a42e080082c088110b550145107500050704007001501211401d500c036000a80101d00a41c0440f006000280502c4024040e425045517110412a400c4030b4000044804405461041041d5007a001000d001080144101d240a980d001a42602c07410700810ba0b54403006508000f0303001d044100d60102c6154031751040074408030314590480511602400c828001000945400039194094201a003000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 46358025 1250 46356775 46356797
    0x320a1109031207051504260901020304050d0503040819050106081c0c060b060d020c120415050c03040b130905070201050705030601030903110d081b040b0909130b01150e0d0210 77
    0x450628051024440044101c038040005002000e1400d0308044001018500341f0080802400c08900444050b5401a40140418081400d0010341d10305594041c3c070480342007507601c41c007a03031404039018100b500704003481e20b50004004090283c900908031200240004c4040403d01d070080b840442e241d8020041865400300a208055000c20078601d405020180e40d0042200104082e60003084060f038144500c0b80c00000144c00c0b101541e090f20340051148148003e024006c031456007000006611a000811000034401c658100070b140340b0580910050b09e1501c0d1803004801c40390010310160569040404210304981d12004036584081c0908000603050700e039080c1100c0d01404001d004240380321301000d01452a410200451040390020352103100315004042410181c00b4502c908071000c1c07002c3c00b02c17061629203442ca007980240010301050881055488095120710700703901014000c60300300240702d4800d5105145d0124000213954208a22003690b003c10442081c60340301c4420801da201c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 46359275 1250 46358025 46358033
    0xc0f150f0712020c0105070203090f0312120403140c01060e0105010314010b0d09050613060501051c120507021806010305062409040b0901030c1404050c030703320a1109031207 77
    0x44c0c1e0701d1031103201c0080203207103000d0384081d6503030340b00d042c645100300d08200c87d002d0309250000d5100709041d41c20600a08100d000c0d41e41100a1002410403801e01c010410001e01c8910003038090813404032410300105580780b80100d084450f00c41070f003280d410541400d0032030610081458807a41100d00720500290f40c1c500500008009207060400200140500fa040c0300e6101c8080d0100500d030790041c1c03001c20159030b84408001c040c000104000030080940f50314040440c4889984408a004d05c2c00c195183c1034840d8002100e6a1500f10b060b022030010384117001c11942e240c80f03407075440141624901100e0000d0404402419042070803c0350103080028811829101c82e00443e00014014000315140e50b100c2c9016410710b45a07025040c200d503031381020346119140600800f8091003003026611702d180c50f040c8040b0003422200d0054150b6008040c000c0d80504000751801c054010030780c500301d049041541c0f20106441c04600116041c0f43e003404002e8165401103115034450090320307541c90f03a4400a184c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 46360525 1250 46359275 46359277
    0x41d010e18190c0f0914060a23041d013c0b0406030b1008011a06030109050615030703020406020105090a03080105010c0c0503100902030145080c0f150f071202 70
    0x13100040710701c03c45000440e491175420000c108144c4141600e80e50395120184a802c81c8184545103424103c101c206201c0ba81d401d81032810098081e001294020090b80441400c081c070713251070500c40e07643e00d0004400d00105c00c058400344420385850311208102c1c001c0c0c01c803480511012510950ba5801d00d210f400e13030391980144010340e030200c03035089a483c02400d81500e25103940701c0c00b005542498108601ea00c03076000e41402e8040c00070301031030440c0d00b00307a4104000d0100800c501c0d04120145010074003c0c210382c010310300c104480d60300540d031282850402802d440020b0701c07000c85a07000c10314050000f80c010bc85141915405e29110280d0485801c11403000308031544500e41501521035010501a070b180c21040d8204d0095000b4081020001000d031003100c030660400c4502400785440b07001c0e400b5140d108103141d00341058185010485925085455031107402e8202141d8840508000404024010100f405e070441d620f001003440c0440c00a43c40f800020b000c04100034000d0406034500c55698 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 46361775 1250 46360525 46360529
    0x30f0b0306070e0109060503040201140703020307020301090c0f0506070206040303180f060c060b09090c01080a0b0301020c070f0f0308030601140f0a0c1e08090f0105041d010e18190c 80
    0x182110140c0c100004003514a00f0007942190000e1900040469181d010f1005c0740c0c092036060b036807115051850b6688a80e0346c2c10403401102180000c006210159400340038070a1b11034002c601101000b482c0c2140100c040d8500c2e400720f8080c080034002800540e1700e03882600c0442c0c0d01424114509210740c0090321842d00d054118a8965901903000724090381c0c01003c421185116400c2046100c03004800c02c84511030490314003e4550080310551900d5101c0d440594201b0702c0004045868005680060300b60781096410501c25803060b8400c100e041c3c0740051080050540c2d60321001880c2c25501d4001c142e100c002c19081c18060825400c0c4080d00c41c54003140c10b400d8284503280d40383d13124110014540000f220065483c480c0c2d8041604450160f80070003a91158030405480c80d250024040c0101958200100c0341840014040002c448020b1200d01000b5031440c20b40c283c056040c0b0000b260b040c100034011110540c03003134100840303400000409005041059030f010031910100e00c2d21050503c0b180e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 46363025 1250 46361775 46361779
    0x306031202030a1202030603100e030f160c1202030312060105040e15040b03070f030321110c0d0e0d0f0c180605030712080a080a0209060f1207110d030f0b 68
    0x3840c02500a0740800a0711000782150759021418002c1c030468420b900090721a140e06422502d28042400780c0e582c441c2102c181190152801c0c541c4404440900fa0002c8035520300d0340140388180e80c100720703104851780080d142072808501c0044d115000b00e07503680910818140029080750214a89a00850564004060030040c1e02028074110810104411002150500660505040300c03038928010502c9010348400c41041941d10b40b0b107480884092003440a0092004401081002c1024150240203885c1c5d00081c0c9069031030b1f005046035464461509418820810800c450b0505980d40744a0022001e0b0020395501a8403201d080c103100141150380321584040600000341d00d528425008001161822002d4808040c1d8511101ca0791f05c040d01c800522401d02008071042180c0514019600883c441a0060900c1c561a0200d031050744294044c141d84403001c03621181c160b0205410381ea00486628140b981b001300c1a12840e6a181401c040c481171685030700307000000006507840b6a148900c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 46364275 1250 46363025 46363043
    0xb180c04050a020c0f0a021e0a090c030e10090206090405060301020c0109060617150105010c0c030c0f050411090307050103180203011505041103130312090503070317070c050309040c030603 83
    0xb0400960007540007401d01551030182002c0d14807a0704010481c88103082e0007400d6126480049000610b00142050220354801206000828000b46138415501401495200007580031680d000d02d515102c1e5105501c2042d0b4107110301e0b840140c40700f100380d4040500588011941d901c0b01d0300002d01a00410f03440740029131a200750481030000580210048030741100c20080c481e0581031416866519117417085030301903140c1c4010445541b02c3c440b004082801144024402d40c0c99079503485030903500e07500c04601040512014412071034644600140481c180308413619060040300400d4031030b02540f2400e8141070b0740f11180c0d000c00e0140001d980c2d0066000b0000c01240f0510901c1004404c800c0c020345001314641007650103041e40d2101204e000700360016101d4034000041d5002c5641100044044c1c00c0903482d008a0000a13400308040d09106100b07880e16003542840c80111051014010100010403c03101c2440700852408400c03640300040c2a01e0120701501d203820250041c00280c0d20041071104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 46365525 1250 46364275 46364281
    0x3030c0318050106050a0510050301030b15091e0105060a0c03030b060d1e050604020a020a0f0602120702030702010e0303130308070501091202060916060503131b0902040806010902070b180c0405 85
    0x651100085d500c0c21202800341c2600c0b01c0902c580c0754241c0803901c0c04240c003000141b0229126400c0e0a0b40680e0381d0180602c81501d0a0114200d48000c0c0c0c1c6c0e10806125011b8441c3c00d124689500c83d0240c03d0954416040118054009190010b843c0002c0c0c14191b0b035a2010031903840e1441140c1c602c1e160070f00c084c0020702036402200c0070070b00c0c000c0b00c070040240ba00c404280c1500d400d00803542041226030007001d840800761915040d030110711804035410380d82003005104520250110500c05e5079550083d5841740514000500025612020103100390001c00c8030240c44080100204103581c4c0080546440d040c052504a005200480001e4100b1584441c4180c02550000711030344203d0b0100141e0312914110090b40b541d070f013006d015241c00300d641400043c1c1030011a10b4403241d412701801c290801001c82403e0712100700341a40000750010780000b400d10120a0070410300340184045101145440d021b40c868040c05240909528060310710203820815140007000305a00c210030061013004142 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 46366775 1250 46365525 46365533
    0x15020a050d0f0905090103020303030c0315090a0c17040c060309050c0402040b04030c140907050711190f0f0e13031103040e010e09010c0206070f0318080309160b0703030c0318 77
    0x141071400340b800041680707001003007070700b07190300391328102c80d0701400850443d12224082034154000400070354801030081040344035540c441c54240c1c0a500c0412000a40703c1002030010425031501c0608542c1201030418840007031070144980048801e42e1600061445a41c5000780c02d02e4076000c85268454008a00805c030718048100901c201e920a100c45c8064503512010070f04641d0103240c00c154000300c0040007503102401680200611845641c41c2800c0b4521000050020111080001020b440350003091103010002c00883d0090f002c1320340006062890308a159408080c000c003035541114404c0140810580507804a0308045548010350ba111a11000342c048041024815080d40300345610108250f02c0c0103101d00150081c079540a0310706581c4803481a224444000c028104044c1e0b81c40c0300b83c840e40303074a0051080c018403036292295a400c0503203125241a01041e020008800c18000400021114104880c440d9030316007004282c00c49819801d40007805105084104d0301c2400084d20104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 46368025 1250 46366775 46366787
    0x30708070504051b03070c08040806090604030e01050702030601052701091b030e0c041e091109060108060306070f09090606050c0106090b0a05040504150e03030a061e15020a050d 78
    0x7407881510100100d90f2900d0454003a4042040c2ca294840da0030000b03e09642d200d904000d003003a0282c0c1200e450720b03544403134140c9090011103411043da0040400d0100301544120b00501d450424a05079003000640d400003034480c04c040c41800d02c14154000850344038804150210040c00c800c94561100d5a0b4800c407500c0071349031107101e001e200500b1485000001d4000d1052160b0403202c0002400320a040f202071200030010001003559610403800e40b10122941d80c000c0705020b070310070312a03c0300701044002840080c0401400f902e0605c80380e5400c004d031070b03207002400c1c940c8034405207844003004d2401031040d11624115003220802c08c0c103080c1e011a00540000040000036044002044a143d039840303180300321124800415841140350f441004a8541a04072941180c00707100c4001c0e0a003065000c01049174500d45003080a500007004001485000d82305680040414400d00840c881407440300469060b040d0040840d581704024140741e02600c2000b2144100e030f402000c655102d40000b0000e451 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 46369275 1250 46368025 46368029
    0x6020304050d0e040618050406090b011503050108010608030703140702100f020f06090c2107062106080a02040c0219050f010e0703120c0f0f060204050901080c0d03030b03030903070807 81
    0x10074200810038406013080c1c4120b404a4805412014940d41c05000d007601030603001d442501d84544031081c04010a07055441c1c14002d14168000c83c100c00710421014050f940160700c0030445034500841042040340100486e56516072601d4418181c00301d002540c4514014690069008100440341441503a0851b11b0074040c5016902102d5898810001981d5150811100c80c49142c01c210382080b01420412266042c1e880e00782c00c01481a421420968a0600550310810000305e400f070070080310082c203006224114040d080107200305410407640c0c0b9513600c140d260082c02596200700c40c40d07442d4030a00030003544181003103081020116600701980d8859840c003001e8150352800d80d00705040080003544004482e8040c00c0142c041c0b8622000b61343c035044200d0150f650002c24000c03840001e403400e03c2c1611701d5114040040c0c4850800d010300040c5481604407c07040e911001d1103d0003640c2c0e4001480c03600d9414900420007a8445012034250300a210080d60103104a45010030b4034100032800000b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 46370525 1250 46369275 46369277
    0x305010609021209010506011e12020309010f0b0306040308010302061e030702060601090f080613111f02010c0e1f0e0d0503030a0506010e2103130902030403080c030108190f06020304050d 82
    0x7913843e81054035080f12802e46095010440102d00261040e1a00306150182005418060941c3e581644941d042c0e900c11901002d441c0d5641941e005a170065214040d2204800d5005041c0c034038040d07401424004040c0800f92042c0c80100b8030f203811551040c410000b4003241c11800d42c407402c4c40d40e0065501c280950f01c1d1400702d146240041407801d40252801c0032512154020661500d4164414000c8107040401f40c400500c3d00c2c10b0b03500a0f0311130002c03010b5800440708068900c1e80d2950781c001d08403104c00c2c044000708500c0a2840307001b130391079015500744602d42141700c82840190440940e02010000f900c1c542081c02c0c3e0f5074440a00c8404000340d44a228846400d0025a40e500f0044605542d01c022042d408005120f126080030301d01500c0300e641506d01c01c201d900d00000380c05140300e01241d59224160058000041001b015030100307525410084241a050035541440569a110070200003650a2880308000501c284480854414011034004e1800c540e82c3c10541480340c1ca40880c03d0b5144 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 46371775 1250 46370525 46370557
    0xa06050603030a0507020d0c080d05030405070608100306021b01050a0605090c0307020a0b0901090803010e0a150305031e0d02070501020a08070c230c210c040e0703110a030501060902 80
    0xc2250601204030b41003104659540381c40c1c801e050342004181c0e00006416164084500000709030750340c08120f0b46014010300e4550701e4803454546801843e0441a801010411040205005015021b10044e005a0b68810b4025807111041461801e8941102003d031219608003420301002c070031543c0c0114203661040c0d0382d0080310703a0b40c0315501c2114401911b8210043e8401491344000c21400d00c1c08039080390b411800800c511007031391503808841d0000c0e00001400082d083c14020303040514070501e1508e441591403084d000d4030719124030b0b0b128000e842610f481d41c034040551712440c606030000ca40c907403400c8003011903d40c052400c01c1c43c003e400c0403201e03401044070030340030944c06170090300c4511500380c1c0031030700184402864554040800115556045500c184035009049030b032021a8070648005e8004055400a403026a0518002c5244801e60095142502000c3e00d4200403885205803a0030090030180d1590304400b141c04003402c1c0e800504030394600f03440411503442c0c580040000d101c91486807 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 46373025 1250 46371775 46371781
    0x15050c010507050315010212030a15080604050303061206060f01030e03040b04090c0f08010b030a1802100806010f050a05070803070c05030f04030203060c0f0702040b030102090604060305040515011a0309010b0d050a0605 96
    0x1aa031b110049a00c91230b1000c0203100081041080c1d4001508910304011081405aa00c000b607500d802c200303603421503090300044200440c500b86110345203120007070b40d0010502c60130f100c0081041054514181030415803902c48001e40b02000b001110001c0898000c1207603910f907902007001c028529072111000090031050b801c0351703d03449502c1300b5050700d1a182190307155803180d000d80d0004081f8455a002100c400704504005640c81120340c039000d181c0d54075814018901540014440001c2c2640001445010310402c019594040d0640700003540c0544410340da61034901c0180c690301071a05005110b4803001440f119029055405002140d01c203904503407468503480d61128480c0a04203040000080a122680161500d50811580305902038001440d1018607400700322194841c2c1c1181000c40d88680070710040050420184075400e440700c0d82c1c402c06504100f9900d1001311342014280b0340000c0403000c120450001c2d80814201e001c010510848011300c0c1c6801c1d6252039068030240e43c554500000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 46374275 1250 46373025 46373027
    0x60801030b0115080a020a090302101e031a011d03190c150e040b040b040e031b0604020901050d0c0801090b090c040903020c1903020603090c1507050715050c01050705031501 76
    0x505520040783d215070241750b44030031007030380250001e207808020020f07070706000009620361602958400e081aa10541910420303800e1040030004441400d0030141340150901480340b041180d18000e54003442d1006521107410040c17013018454148442d89402010344140c6400d00c8051071448251164032002a0240e5a05100d20b8401c9020304100203e040c40800749168038050b408043e80980c014000102c003002203001c5001c403070014440030181d50002034500701401a4041090a03502104010541c84c5807a0380800c80800c010701c146030082004242903001c2004d0b242c0c8410244c0100c000800c01401c1e14103101d411010306491254040c004d0400c48519400c1601403000040d401d0b4004001e0390503158140459074840341614403944000c00004801a80c49170001d501a04041c402408810518010000010300641c400c10030340004000b400005240418a00110340a04c02c03081c0700310a1300e801c162668031925081000070b5181c40d04000000390000c002d140140e180b003c0400500c480900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 46375525 1250 46374275 46374299
    0x1506080105011205090f01092618060705030c010c02100b01020a05060121020d0605090606090f041104180c031202030a2007080d030203011e032415060801030b01 71
    0x703254005904000c20580050081d048550804400750807105410b800d4000c49085482c240c00c1141c100c1800c0c40302d48503010300c0e90f41c140e40c80c100b03d20801e458400d12008902d044544401868021031000c9001e409004040c000d6802003d45003009101403801040c4c02034440d40c4030300304000c0340307440c04620090f1540700017070038036605600900405e142d07420010502c4440c00401c0425542600360040c00c0d0058482407042c225051040401103482d0614115240c140710004040313034050f00f012810800d4441403800a190056004a2182c07411089a00844c02604a0f41c0b4040b000d54204030750b050400c402d180d004801c403400b81040890000e00c14800301d84a0bc0354845940015007001d52503035400c4100a940030840d5480700c103d58000383d9844c030450a01c07074030341420400b00e40c1c0400108000200458440d605100d59400700728201d0540da16100301018409424020612107811411401082e900c0760186080e44200f60a119541e054020070910090000315040c04184000240c84141d00c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 46376775 1250 46375525 46375529
    0x1060306050d11041b050c060604050601020a0f0201050708030c0a121a09090a021216080706090303030b0d050609010903110307020a0302060703121e0e0606060a050705010609020d15060801 83
    0x200b194028141c151601d03c01c407010030440c2d50380259590000100741e030f00d207801809982c000b619159180c90751800090308140c00101411b006d83d0070501089010b030ba005c2810100b06d9403010586c1d108207050b00040382d01e0b000e00c4000815001c4004144003004407254081d0042d20310075070391034201400a40c2d0550580e40c0058070b000c030790740c012a00c261032480c03c05180e036071198140044a01d00d0541d5000606c01c0d03c46c00e401908181c010f2212035607801c2d40300e200707000502100c0004011041c50f01000800740c2d10984006020107641d088500c5003503071000f00d50501c19030014129101340c144108098002e100c1d908044012824800d000615030340040240c50110390001d010b407012610355001c0c00590b5004110407001c01102442c08007410200b8800d0000c000c607240c81840441032a124014116a00300ca003500999010384100b01259441c1421105842e56929100f5142c2c41680340c0f45000d0042d9800c003120a81c00801c60050101451780008c42c844103001e0400350b0780c1d076100000c3c2c640070740038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 46378025 1250 46376775 46376779
    0x90b071d060d020903010f02070b181002090f0a15031a1005030912041d0903031005130f02030115030b10020601090c0c060e0a0201030507050405030307021009180204030b0106030605 80
    0xa16140810714112000d8601003041e00c80c098545101040000e0840307840e04000f601050f804a0400c050003400103038207501003500006076050208500c483c80d5983c94454084038855000500342c51580ca8280c5400341c94031001d07040300c0d030007038454100d030700c40c0c007148007407040004e14000f1000d45800e00d90848030070030b0304003804071400034192400444007940b008207100141d00c07030b000c004110740c00c80174028402020303500210410b81c0c80c28100d0742c07240c02003d44815519481031060003204d0601400c0d4408541044a1800c2c00f04504010b5501900c1e141360140b1000744040000203141801108819080019036820424808000c0c20000d1201c2520801401603200c18010b01540c0317440d50006812001c5824403050300311003079882c0000d69840459100094010f000e04038119601030141e1600030505040c8142028105000f0076175034000c1c00341c0a88140c03151741d2440421030180715400040c2040441d06040c4125000c1010081e41c4030344412907015148200004089210780b066500f51040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 46379275 1250 46378025 46378067
    0x1050610050412030201060e01030f0302070b030601080609090f0a06060503060105030d0c11130c030b090906090d21110406120b091302030c060301140a120506010302130608010f090b07 81
    0x281002141c5150903c03104130309640d030b61a800b0030741c100d4900800f4000c510814891101680510f0000c0c01e00f482c03030b07010801081c03051051114607a00450401c0c0c2c840710035035100c0300c940c1d111102d5501d050904201e24100d0300444c40f0210510030b480c0c201c0d800380d90041c1e00310b402ca666180d06059449010104880006011805040000d001d044400c03000c0e038001007500b08aca03a0841080b2046821883c50240465514034141d01e41d4109007283e19442102d0102401052610807501038032094400d00440400111015015010486905100300c107414060100421910310b5075410140d4428002c04022502c3c080e581c1480b14128040c040003084060205040b80d20360003070502c3d60a0791004103e91602896060b4882d036211000614020004129040302c0c140412003841310301034194020100510340c981140c408100f0025a081c11250b0688441514a1540d881803004101c550450541c5500b4840c004c40b00c02da0301c0c3c1100314103a0083c4050310464448034001c3d100d070100c07103042a82c83d000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 46380525 1250 46379275 46379279
    0x9030c0609071a0a0302040b0f030a140c160515010602150a0606050a080901020c010f0506130905070b0306031c090303141207030b0a050d140708061e04020109050d0311010506100504 80
    0xc2083e0181c94910040d0a0241c140707500d030050200603400610000c1c0c5880030220400035901035901820b0228680404518050b00740b900d441e9490b449884140d250600c08005c1d0301c030822800f00542040c081c414881707240e055840d04c100a40300d030307507a0704042a081d00407404624440305500c220003c0324440d88401c0e10f041c20004085d41c2e02140100402d04955081c070883c5680c28080c09a91003600ca648000038141c6850000c100c24000b40c0c100010005142441c504009140003c0e42001d455a44a4407a103d94898000901c0c0c188440850410f011240100194081d001010041501c0c801d03242d00d104089aa41c0c446590300a01c0a6450750383c41a4010812040c06940f10064682000c0d0211048507190400304401d040b08900446100707a0880c40010b81c0c06061007454054030100020703081c0c0d41040916001c0310000381c0c4079030590500c507c000c41c0840e8000e0380003500610340600340c03040c0d0104c11f040181443c021130315a0031895007040700092882c945418001e00c640000c0e1656800d042c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 46381775 1250 46380525 46380569
    0x6030807060b031203011a0417010b03061e1906080316020f01030207020f01080406020408030a02031903060608042904030c06061e030b0c0417030a020f030f09060d1409030c060907 79
    0x1402c0807401c00c0342a0808c0101249828140c40c01c5208080d55600100c0c5451125040c1841d04100074040e030744d040350648250851444810050b50000b00e840c0c50580355281254a103001071050303a00c403048510000900221122450307410705252030085030341c144050308240041d41a882344890081d80044520302504856004448880d0424081c113801801d140c0c50300c1450313285034015402500964004669204801c5c034900c036a1242c43c0c0b06190a010030761820344041c25288015100034450448020328803840c82168840026079840c981101e405428282000303000c01c03c04060a071805420280041008104c0b0b4002c2101a0344429582d4034140c0356444003a5648400751405a071000c0810000401080e02030100140c1859200a19038405034020b01a191009036660943c094009010848242d1024000d4400c00346041e00e0084c2d88030803585800c8028000351242c404104800d10620114141c00000b8180034950101122030035110039400c03030343d5601644650030740f8080c0303454174032011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 46383025 1250 46381775 46381799
    0x151e131d0402220902031b0906061801120e0709020403060b0a030c090b010c0506070f021006060e040209040216030503060f03120304020105090a0e190c050a090308090307050406030807060b03120301 87
    0xd0190550f000441100310fa000a06144a449080350201840c2e15040710503c5c00c0d403011904001c04451207031801d00c54461446456103900c42c040c0c14007049840f83c480030002900300781600d41181c016207000d5915140a9802508140070039103805141601c112002e04084c074030302058a40155550803490b14052201c409071240d851154100300c02840504000f5100f042050b0051060781c0301c040c13110031070f208000d14060488011050301801c00350704000680e0000320f29011000d058602681c0c034041040842c01074800c90100f411020103030940542419400405540a02811540a207541d90725004240d40c45003a05800010302d20100f021400560142000b04505134001d00a440071540d034034490745c0191400c482842c81d45840c0c034180325a528461080b01c113070040700d051160400c014030070014641d1542e4000180001d600180302e000c5a0b401300003080092074014803d00c25151070380b6000b046500301001c12a030640c2802921005480c02041075946060307016041390541e0b2810003180c081c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 46384275 1250 46383025 46383079
    0x210201021206090a0209120a0203010507080411010e0103060b0c07051201020a020c27010602030a020c10020307061a03011d070509010b030a0c0c0b0a020c0c010509151e131d0402 78
    0x13680d030b00b000702c1e82d00c640365064240c180782100e401610240c4218014942501c800a05034070070082c142c800c110004036140c800e40c10002d030a01c2c3c191103d035070b8440160028040381e04540b000000201c1d0030801c0c080002080d50a5901c2642c2000040c520940c00c24243d002d202101405a004013070906168140791021051603004e502085003c4070113012044a041000e802c404010380001814a245540410405c0429001540d44c038000a480030700003034a900a12070003d1215494030902c810010340b00041c80760016008008201c811985070841040c1d00e0514010850383c0100c0c20001003902e400c0071103d04039421082840c0c590703076801072520014803e8803048818001410106808150360382e034007601ca0040e01c03500503170701c05d00086141d2501c032a19000d1230400104119295107511543c81090402d003c00d41a40d440381140d025200071a14103a24103040034801003110507421018400750310071280201c80b1032001100d40410a80600d4048a001e500982e08400c43d00d000c0b542c1d0150115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 46385525 1250 46384275 46384291
    0x1150518090c0403031d10030f0e0105070215010807060c12020307080406090e160219050106050603040c0e090c100f2303060a062a1e21020102120609 66
    0x36080005401c01400340c0e0114074500011500f40b041603040001a0040b80840300c1c0d1072501000360000514592002c440641090748503501100240c0081e005850400d0f41400280418941004004e595140040728600711128581c000202d084020486400780c514599032403c004801d5291695a4954003003000c00b148030030400c000100e1000c1020780082d003556620301c210285003055449614201500c1c8595102e9144610b00c185500003502c2d08400c009030b0340400b8144090305155006160765803025400203000030411040241080c01401a2844892b0740100e54640e030700c116540320401419950003200d18224914118010741a02d4003401581c54943c3d070710101d040f1141d040a4084540c1c010081011086c044c142c546604044040d10701c51506404401050400140c8546003099006401300390020500c18070544004048207422500e111141a09862411201c1c0e0b080c0d515000e00f20168103030b80000380d00d1060085940c00c941c000b46a006a4403618200310f00218040c0817a2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 46386775 1250 46385525 46385557
    0x11041508060f18060a0501050f100f080c04030203030d0504030305130302030a050711060c070f080c0a03060504230304091109090a0b030c1203090a050411040b0901020a060501030506070f0503011505 87
    0x706500790100007945c4510817010022034194500b8017030040b241c1e501c030a01c0d071285440941240c0465481400102c940c2c011745040c0e511703500c5107043c0000912071500043d40502000400c11aa00789542145000300d10a950801140d503685a11031000510484000c0040e0010000042941d1280d4090100c55029030a0b0f0038a036841342c00041c05503402a070419059800001e002c001d290180040900101880d402600d1004c0f11080003c01e2004a4040117203015516004141882001c9400809404034200504c041b50100c2e280c19941782c000d8410244c1890038061208803804c4250150382c0c3c0c0f130704d01400d105800c0e251030003107002526a0050942d094490030400da036031a42c0d072519030381c11481e41002943d5034401110900842c6d907065081240240c1c00c0c18160030810403004110b40c1101c202003285600c40d800d2800403814101e11102c050982810400084280700b000300c1c4007401102a03071200a464910361009642030f020910501107408040b25000c03070458040c3c4010311120300c641d0703912 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 46388025 1250 46386775 46386811
    0xa080307090e0103050d0320040b0708070804030b040506010609060c06180b01180b0a060c020607030306030629042a050d02030c040e010603060b030c0a180311041508060f 75
    0x100b0410400d074000d60701640182005c0190326090710411a100a101040c105900c00019095050f442a0712031040c07800c0001940300d090128034820356041c0c55100d504580d07990740d681081c01c1d9100c070588082d036507401500f0000030460301070100b20080701c01a4a45040d0a106a2130303180040075509000da906403070100001000a440c0d4140c039010340b903031600801e003d00c018000f600c211071681b00c0990081400c0c1c45e080c40304a400019140c0007640c100c40f806e41c1e401030b92a0840107050990b2008201c9800d0481307060b142410481030078020183d4404096050320800208415101c540304101420700307046c48500343c2119040010b90a91050707042c55854a654440c1d20802c0380d108072030300ca202d52401f0406004000c1001c440c54010f000d40c1c40c044c0911070800301041d126120162044140329000194010740318007039401140d44e840407195602d041540c4c3c0c20034040c1c10031000c011034030691a150030302d000c00d08410b10000941340c8010042c0132071303a101c0c05400038456020302040246512003400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 46389275 1250 46388025 46388039
    0x4050307050a21020106050f092e0603050a020a0806101704080403030e2202090d060c020c0a05010c05060402040f09080706061805010b090108041104140f01080307050a08030709 78
    0x1207081c290340b0901d00c481c91611035060580a0b01403e0700140d00316410080d003004160340d0601e0a81810340121051340040d201c4121841d116080182d42d00308088082d60700401c1c086080356504216002c43d01c4c00d2106030f0b29008120100d108900141c0042075004011402508065905440d90380c005d042140141e202160104c40001c8100d400310307244c40b40020103008256001e0b000407201c0305c0594100e03c1c02156003001c4070402c1082080c000703400740d020550048507a03d219013120411b40104007001107403c0050001e49450414071a10b020340359044000030385511858501e040b040d0083e028040319100c60b0701b000702504030320011030075075511043c5107008070758540d00a24490340300d03150000e6022324060740800c4010240010782481c6190100410031070032090f045801108017440c5c62034150303540e403605095020038203140d590480d2500108501307495500d44801c0c02025a485c519215a0b680d440c0780760769214002c3d005010b0303000400600c000809420145030000c0b0300d41000c0d280c0f60f4a07101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 46390525 1250 46389275 46389283
    0xc03050c030d060810050c0706020a090b040305150702030a02030922020f04090c02010912080402030f030c030408070b07050c150909070507020f0a2105160b091002061605030405030705 81
    0x58068200e42d503c0d00200b244070020006a4506a0011000c0c48545802d206120040c06503030030140200da000a415400a40f007840418003030207500e0526034035140c50381003103952045114095808840550041103d1a0001085d6030b0070145550045203064020307000d00c1200355090911400c82c2194565131400d030400c82c00503044048201c10800c0c1c4807440c0c1b00f06a81a500c42c08454419a490000e58030b0100d100c3d000422100304240c2401011a152880400c6c5442c140f0201d4241078040490302c0b4030700807004802402146d04410841e01031b00d032105640401880303000c0c2d00625951240b0b004081c03d0400c806240110030a203031902d400d00201e1004940512402c64008001520001d000c200b10329224040d0800100b0035a450940750307050141d400b010751850004802c10b000c0369602c940400800304201d8013049d080200d400b03c1c903030707a804403402142c002c541e81c0c0b4490429494502105840050240d11511080030400c0301c00401d403a040da40c03a403000d401a034480c08100065000318500304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 46391775 1250 46390525 46390537
    0x3070314060c07021f120509060108070f0e180f0d02031207110a0201120905030c0d080f090303131104021201090b030115050906040b15190302040e070c03050c03 71
    0x98038928003109100400c0c0c1c10540020030401140805201c250007507121403034240d0f8030604140140561121a000c00e5130401d0045201d03030402030414042003c0389a021072090b0488410768103d07004c0380e890303014460b04034860b801000c0c00d0190ba40f000604035816500001b00020004007a40c9031a080c1120030f5090104040c2c051025900014031104003074156500340b40c0c8907402c1c4c80c1c050381d40128070940640b600b810744d10190410028018030b0340c40c85410740c080a0255800400c5951701c070784c0024101e0302c136050710205002003080d40780002d160001400e9002e10400401c40618951303920803202210b01010303588181c0320503c0840380354046440e01c1c80281041d00d00104000d01c5503142000c1c080c1030340c00c02c0c40c04600030790600151041480043c0310041c2610022540d5a072280c0c1c03141d010800914800c0102c0d40d01144105070b28020300080302c02040086805c0c01501b601c6540c03d2015002d80c812486651489040b81c0f0004450900c5071a0364070385070b8424074202d03281504454141c1c3c0745410003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 46393025 1250 46391775 46391783
    0x31b0602120604050106020a03030e160f0503210a03050c040902030702010b0a0501021207030e06120112030f0207060804510b10050d060302060304030809060f09030f070302010605030703 82
    0x119000c0740d96415103010ba1003001107506201943c10010000c0d19401c0860000382850384035110754a40308001e00940002980506030b03c0d2038a9915120b550b441c0c252441603038013070300444d94000309207440d4400064144102d4896503181200c0094120000c2c41c00a2148028841c184808181b079417503400114003074080e41d400460081d00c036000300141070296030301803070556201d842c404040380345200c2510010742d01030606140c072244100226101744210040340340407403160030000c261011f90030b0030a000d40f402030350b03262840841c040f820383e6119110300903c40030500040008000585000b0140403515880c45014481c000c58050030f41c40b0420306d80d0002d04c8480c251100a0000052000204514035405051001510080c04580801c0780d403203c0c0803c01000141c0b12045c4000d68110704c00441c0c0c05407030701d9520314140c10010500201a100c0c82c4081c06120b010950300b844c6210540e001d821801c001d076240040ba45140070195200200803411740d5260140000d40707542c2804290021805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 46394275 1250 46393025 46393027
    0x120302070b070f03110a0209150a091107030207090b030304090c03021c06080f0a0b0a050601051903050f0622020c010608070f03050d05040e01060c021216080c1c020409031b0602 78
    0x4113160107000c0000380548420301e503001a07400b038090303075403d0422504030500700880b581011440c00800c023a1151600003e0155051001c0841254400c0c80140000350199003510495616240d52405a0301001040340d85540148003d000c61140c9511100040c0b00d14180107260850b40711744860620019070101c881140e55107401c0000316418010b41c0c40542c2100041c01c8c403010103603a1075034891006028030b200103a03640001265039016204495143c0100c400c6c020380301d26034440080c040d020440c5c10030115440040800c0072800c11030084030a407049251400840101406688001d40142d858903110307648401c40014916802d2100c0c0004d041030000142003079040d030504074501032428425104102c81040104213144070f4422590644150349041e59815100f030000800c1510784183d03540c8107000b02c030510030341c41c10558590f901b1909002c007525414014032082104c1c0101c41b0318000f6103200154400300052070300b039019000f924401d0600032607101030094090500000c0c01012101194 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 46395525 1250 46394275 46394303
    0x1509140603101e050a06020d1b0f080f0a0315030503030402131b02060402030114040b0f040f060e06071202031306020903030c0601030b0a05150a03030c15050a0603060605030a0201050301120302070b07 88
    0x10428005c00c09424103000404c8019844940141041c0c0c0750204c0d6082e04040d1441c2004001e40307100c18a48003500403002580783d02601e010649280d00c001d1417240442c5c0b03400c06034520012a40500e00c203c0b504007025600b9a0303102c0d000c1c040180b40c550030010055690300401001410408680050800700c0e9001340064a841d1042c03508407103008080d0b0440500f040104000140d4840740c46034005402d0038448000c1e11107140031000381d08001401031909081c1b00a29195800008da10f41c80752295554417200e040181c82208200d110640d0140a0756924400c000f0202d0b40640061940940280441c1c0c6401c41220030f071401c1c04000c0c0c00c00c40d84c4a61070720612030511400c3c001d080d0031020080c203480f4030b40403010000d6002605444003c081c0070000245400740004400c819120080e484c00611042c42c1000404000f0841d90204a81c118030700b01012a1600700044c14039031096060b1595851a400e200c1d4284400c004100c045003144074442d0003040c44944c0002500d5420300c180c881419400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 46396775 1250 46395525 46395529
    0x92c030a080f0402060403120509061908070309110103020901051608030414030307082206140a0c02010213030212070b0d0516110a060c020c06131509140603101e05 72
    0xc400a000005409114014803004d6542c5034211001c4a078003030202c101c00c80003a00705462038050112204c0d809240420401103c10041c03c48042c01e0302e295072583e6460380c0d212400d500301c0301102000703011920300444142c42940268020504510141461414103010030142103150a0391003007240d49a5006c4284410441410360b40b65203400f004029500314a05030900505032007009152002e0bc0b00d540c4010001c0e940c2c1c0e14822a00c054010030144840c00d100804062314141c01d642c0301c2d1070715141c0380107100031a2062080d500d0074055446014416841c40c2c081041001c4814005021030084450002e6040c0390302c001403001d011704480104043c0f40550304540884204001c4009100002c14120050340010403101d81c49d41d400743c00040c403410010012031a05245d41e003000d80002e00043d920407524081000c1030f003254281040e400142d0100002198203440600c00c2980f0b00022000d41e141c249086405154800d405101c400038840c2c0c0c40118101075858004181642d179602c4074244554 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 46398025 1250 46396775 46396787
    0x705100e0603090319050a020606010c020a08010e0706020c030318120721050d0302040e070c0c0f030b0f0a0e060103030815060a030e0105010501030522060b180a0b011701092c030a 79
    0x103440e25041c1b203030400c251030901075221600204224100001c0c45440c004542e9606a44400380c00780364000c00c9503031002c1003601d0f55000e003400f604001d40b00c0c01700703c8001c600c0c1c00802c41b00b07104000c0038030b50458200c9000f8020821904195210725005001011400d0301000c900002801c2c0d41440c0300c6100d19850901500301030104811400b003600411003407003158400a0310940089003454450792136241400c00054400154020740b011408085000080c86501e00b20280251070390310b10340c0c3c40c0e0780760b01801c0d50071500c1503218100f041d0025001040801e01410380d150340140f048080c000007081c01c10004007980c0c00681c04802081d40e4800c1d12040c12424420507014000a080422540c107000c1c00e0084d4604115119000030304802e40c80d402003180c40c0d00009040384003d058100d04a80c10300740b030700440781e0480d020003485203040b41c49907a07588114594840b40440d03c1251310540d081c1240c280103004011b40400220751100864075a049550740d4100ca0415190f0155807100000b078001007036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 46399275 1250 46398025 46398067
    0x100e0106090308030c0c010f050903040509010e220309030f0b1806060a0b0a030b130b10141603020c1f0908010b060912070f0f06030f0504050705100e06030903 70
    0x402020751018000200742200b1250005600c94074503807140c01064105d4090710610300140840c41c104400e21440c081d00002030001c2e240120ba82d40c0c1d05a80750402d50003070b10002c40b034040c500c0e4420a1113000381c1c140380080400e0302e402441c0c9221219125290781c1c940c20b801c00301c1151245102001c00008500c5104007041c070081d40409444281030420014006406500800300c41020010701d98441078042d52044501c1c0901601c5019000c9455403e0801020042d84c0140603100111540f140f80784103404902400c1c001c1c84003c0d04148000d05001c2c00d281701144102c00394810f00340f42e103019568038040c851070b0342403d420f580c030306009920005010240d07030b40c020700c0030303a04240b90400107658440940e040500c1c00e1703c541d0102e00755800702900d0310400d588584814000498040380d000e0380d804403401641e1007510248010b44182c1c41c1c0400304d80d0300321406003a681106a060009241842c401ca5104d0518a0004140840000040c14561043d20b06240580c4001000b5402080e11046800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 46400525 1250 46399275 46399277
    0xc0a0e030c100503070c060e0d02010b03030703210207080d090501060f0323070e040f0b0c040501050d0b0f10050c0f07080304061209081803070e0105030d030504150203100e0106 78
    0x508900d90000b00707021a03845202038003400000310000d15080e2140180011441c1c0004017800b80031501d0f45a17540303031122000118015400c000d180c85460030004100d0358440e034142e807000c80c0010406060050401a41e980c642925006c100ac2c0001c66045000b41c444e111306480300080c41e0909151850850340c590f8030101c3d070743e400000c00308041001c1d01c19003615010000240c059590800758520304105032500320300c0e16050100c0a20090044041e88c44ca0b45900c01e06880c038460300c9800000c1501e014a12505000a10403c6541e219800d940c02104120038050908011450032200151051858122540001d40080b0f03160865a00800c040c0002c4440c0744003a0140c24104a0030544034862405003c2c14841030301c0454500c15900c0c0d208400340e40d00141480c0e00c600781c4c44500410003160300d080302d00c80d2254681c0451260031015100341250030040082101c01c20b120401c0d4050240207005446903900d402c0c80c403c014002d400110320491014079036200079400d00306400e1384610180c105074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 46401775 1250 46400525 46400533
    0x60408011a0a0609050d0606030506280501050d0f050109060c0c05060a11070b090a020a1508060102010506012c090f040201110a020a0608090c0d060c0905010c0f0206030402060c060c0a0e03 83
    0x803c00e90000d0030300013520819601d0140f5498a8103180e4050b150b02d510040403071088104114401035841c110038404105420018502c54500100300203890007809000d60045101c0e000c280000c401e0107400311120320420002c11007000c3da491714800c031104070314907c0210760642c09000130003000b17000e8a07601000140003007241649916442d0a00d000300c3c00001c01c42e205000c041056078900b003001c030003143d90080c0040c640945811100600901041c0501c0104e008c0f44081407880d8010f0103003510036001a901d910319207240b0100c203103403c0941d001804840f005030611800d140c40d071150303c40c8140402540e1000c242440d10004020121030150a0b89030340105a0701c0006945101c2120102d2b4103070f1421070099141c0c21041030824600350421913002002c2e6070382c0001c0001c2c41c2c000540c1c2d00001e0321941c00e00b80d50b5800640b80510390110050030742280241c0b520051030710720081c5030003c0c009410507082800ca408110314000003a0390003001c601c00400c000c40c0f40c80d0701007506c0d940301c00241e02070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 46402881 1106 46401775 46401779
    0xf0519080703031d0d0201120c0509041104060807170126010f0504030e030c0102030f0d020c030d020903010f11030f18070e0105090705070b0f060102010b060408011a0a 74
    0x4624201c0038160b130354110700d4400442e03681941c041c0c43d60002d05042400302e000602589032a40244102030020341c001e611140710380000c6500a00c405591103041040c0502164002003a0301c041004111120792418902802d80381103a2002102ca1009121400c01c5080f0740e0103110720404641c0307401100031600340c07203402c0f560159000c0d0f1106178034080302d40c00b803507240e559004420303015034010001c48050a6403c00203120210201e4801811310358082c50440c1903034440400010190303004107207008913240a01c24606540712440307080102032401c0300c2112003400000e044030100703001d81d40000d00007501110f0403842180d060040d60b44540c1c03500079036207281c0c00038011107014003042c00002c1c1d901402882111000b0f50050101000c641d0f6241c01400c081d100100303018119502d480543c070303190300c0b640003a00241180e0000071071803001810a00011051003080184140b0b484282 = true := by decide +kernel

theorem cover : BRFrame.Cov 46223025 46402881 := by
  have h0 := BRFrame.cov_init 46223025
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 46223025 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 46223025 ≤ n) (h2 : n < 46402881) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
