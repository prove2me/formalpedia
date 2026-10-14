-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1693
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:14:59.204865+00:00
-- url     : https://prove2.me/submissions/35c0b22c-3dc5-4bb4-976d-6e3d70619e7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 304316546 ≤ n < 304496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 304317796 1250 304316546 304316561
    0x1020a05040e0a0f0e0a05070501080408040e070207080106140906041803180503011103070216060815040609020a0806270c030402240c070e010b0909040c080a03090501090503010506010c060b04 85
    0xda249841c43c90107251170005820300006214030125241291104011121407000b07450050085030b0502091200d0501d1a0340700b84d00203000d10484010981e00c40400c4c0c2580c0c03155101c589031078000500c0c022030307090410100d03901440645003440703101039050b0004041100b0400c042c0401c07084c1c4050708009544420404000c2800074000c0c890740703080c8445550b065000780c40c40e802500c5401b0380c5218444a00b200ca008890041c0c4070150a0340c2d5048490440d11901e00c840d0b540b040d5142ca000c541c05290748082d0101c41d0081d40c0e40c0d501c030300c0c0542c10300414103084002c180395500300f2490f410040d8a4140425801000070007203a86944543c80800c151840001040d0a1042c01000c401e5031340f01d00303402410b005616801150580c680d52242c0c00140c10307003070040c60b000f00360400244a85003482c2070115041842003100480b1380780d4464520782000c0c02d0810840009910080402040da4010310105c0038142c214001c020070f0610b80c00191040c01e0684008060a4031802c10211300d80c0c42c2d070300041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 304319046 1250 304317796 304317821
    0xb060705070605092b060f0b1306030b3301050f0c01150f12080a02160b030712050f1302120d0527010c0305070c15030e010e01020a05040e0a 62
    0x120707400d0700d4103006490340e0401c0310707114003660358002e8801030610708807034003c0d180d18030a201d8500c41d81142c842001070807008840b2081c882d15104425031035100c6480b50b601101c40c2800020360103055240540a0000280090415403200c0801d8100311500607110b8800b02107140c110058811820010380301c901451003100b207180c9000c102daa02030720041d085041c004071605030b9000819185c1a151640c2d030028018511140c0c40c0c81d601d0b0380020f101c04000c0181c4003541c0101d84403a04040001c0500f07075400d400859090001006000c0034540091201c8460700d00e1800901c11444c044003070f41c06c182001044031444407001c08400c800d545640c04e440392654100825205001c0c4030319000b400640c0401c040345100710030542c0751059100d0820185800c030405942e004911552510101c0303142c0c00407082900c1108000c5800504021400d912260038140b13a180850000c800403481c50840d610b004441c8080d900401808024503484130880e02070303075032400340074031162a4241da0800400d4400b0102c2e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 304320296 1250 304319046 304319053
    0x110402071203062405030c0d2c030316051b07090c020705030610290a110d0c110d0809030a061401082806020c10050a0e16090b060705 59
    0x20240318401e24034840490240e2001d0001070703038984a11901409101040002891686814040e203125200464015100300700c41400d02d000254a002100c0014440344909460208001e4488401c8540c0345903040f4020090750171032900748440b02d0542c48200c0503400300070f0009844440140502c0402c004210440300300c3d1400d64442c080d820007040c91038a40750251140140000c0c2601d400510b0301e03c07500d1401c000d841c00d41c0c07901c3c21002f155003104207040c0000041c0b0705210780043c0030101502040c521541c035802c030440291461030401680410700b404100304070070400c003c2564000780c0c901c00b03141551446000390880c1440f0000f4000c07004a1a450b00400110b50280203c03a0080d1450014450118009036603680e040c907034038081c100d0a102000031015902030b50f20490600358a00c1c90080201520f0006a0a0030508003003415102c00c084e19911000c0c0145511a0302c03a03003409188007001420008200401c010021000e40f01e240d0245881c0c2107948141d4a0303050a40d149650310008a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 304321546 1250 304320296 304320307
    0x14031903090512010e0d0509010504090e0d0e0f0108040212160b030108120a0f180905040309080105071b1b030f0b0f0f220804050a0b09030f030310060804110402 71
    0xc150828030b02c605841055070480480c601501131003480048403180d0300414814501203000daa9503085000c00606020041c480000c130840c090042c141c403400782c1400303440c0300001141c0c080c0c1908500034405002c2c201c0414000e05690300700c0a82a00240c040311414401d00004801503d0068a4092014044c0300380b0703800265900024041d5040e50040c0042e00c0300302c440590560014041c558180d400a107002145140b00c40c0640c51360410380301ea010015007850349400c0c8210a41d20f00f501d0840c00601161010040d0040a100b0950000303032a02c0c00c04518960070300709200784c03106e16102070145081d001048100b000750903142c200031580000c21603040c0403c0d09000d051031000320790000c0700c0d104010005620a64002c10319101c2c0914855210050310070040d001c4403050544411259500304000c080342c04d940314000d00c8020840c3c40e407501d80e1482107006240c00c2c841c0d20006440280d00c24014007000b000d0303041289040c0c403403a00d041c007100d0360f48e0308000110a02400e40305400c107200155 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 304322796 1250 304321546 304321553
    0xf030302011407031803080703020f03010b0711010f020304091109180717040b180c030f16050301050403140c120d0209010e0306070f0509012304030203150c04140319 73
    0x1d8802030450101e511000e40d5100025420784183c9201750344500c0d010101c2000082c055200150080102c1c030b0014181206488010b01c180d00c01e03049822140c4010070036500b00b01d00b0425060056100386040c104403001e50b030001c0c0d0740c0d015030f0003070b056820740380c410244640c15581c0640e8100d42d001450448030030048003907140c1140094405800241c010340c1c40c00000e45590348400c0c0a6079116441c450f0560b982014001d40450b40030424010b4020340d0b40000140e0b13002c11000003154401005044003c109151801d2801c08903800705000381d0501080001007500040c04403101070301960400d03614500c41c151103051a040710000342c3c80c50004240070f881d140182c1d010f0180c8a234282c079148440b8420500300b6035546000c40f0404c00141c0c00d040c0581c0341611030006000c18540c10f05144e09044008141c05034150802108a040d000340802c080007507140401031003480c2d120404006049061148032003c20344610f020311a026100310303003404240d803020005d4207240181110705d5045460240b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 304324046 1250 304322796 304322801
    0x200304030305180c0108160201020915040f060219030c03110105011d090f0a0602211609060f02071202010905041a12011109041104030203030304080a020d0e0303120c040f03030201 79
    0x2c41d4080f071076142403c6101e000ca0005541040150141c44211499a13880800d140740c001c118401e10855400b48001d103030b40d0b03d6550040305401e0070070b4901901c590811880d000b1900966100200b158400c084488203454243c0488040035050b250000394000b41e070900b0b0b41d120780411440d454543c41c04000244035600c0a580420b01070100403500f400b504c507140815656250480c6490b12074000f01040c90004509500400080342c040d42054440180e0b031082a101040847e01c1c941d124003520301464005601c420154050725490800700340b141c501000082d582c1940b405003001c1d803400c09010341c0c2560f00034600395005040c01172090100c1c0c045a5521064040c550040600a0f0310301c8580592581040c0254075029080241d0242443c3d840c1040002420486a02c00c5045500300b00100c05a1824401184220702920f600c80d45c0355540300000340340c4285141c1810030000201c10090180c0d60200031100c0301d0a00c0540c000e05501c0e010f8108045200d90390040380314200450b0300004054064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 304325296 1250 304324046 304324051
    0x6010f03050d0c230c0607030216090e060a050a1d0a050d08151507050a030503011e180b28060201050109050105180a1407030b0f03070303080a200304030305 69
    0x1181a2042600d54502c1514200c0100c81c004202c0c0148510140d8841d00c0003c812030722001394800c80308800f5126011070000e0748001d0b016801a00002400810070380c41d151210000c101030b180800001c1c40c0401c45645900020b0f0010300100d4481e00400c1c01038000c0d8101164a954405040351084007450003036603920b814400c00ca4890051f428805215801200d0007807140d541102c1280b4000300c540b08110301c1c51294082480451400c0c040b00000c00d000b04941c1100c1da109072602687d0b941084e155800030407422440003e80c03500448144a89000c4400d008042007000700d01081688581c03001030032034611120440044070020001c244d602c01c84805c8070301160044c1d0020070035641c880c00c107242540c40900910f5003180c00010400c01c4001c40c20401036000822220000714a120b01d02e07c285c000c0002d441e0840045c5d02c81424800314541088480c910050880040020603c3c5a030050a441c900911150020fa61501000b40c0e801c808001081464241c00420b96a4601441c0c0500240b805 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 304326546 1250 304325296 304325303
    0x60b0a08160503071b0503160507090e0a02010804020f10050a0924050927010e060907020a12020a0c0801020c2503170403060f050103020f030114012606010f03 70
    0x110021401c1a40c600111810380000c0b03984041c07541d40d030b041003a551000c81031083c3c240440b022000201103401800502098040202c90880900c0b642c100039142040c55085810402d00d0130b580001428000610142815030a0070206000da82e9400014280da00d9411001d810807105141d480503154404c0041028070700039202c10700000c1d140d17903442c07100c481054008054142c00381d0703410000c140100094220404001c0c80c0700103c01c00034441900420524250040c062040401400307502c9107452034640c0304909031a9014203181610f0020b60310280c9d00d8015042d030580400c04403140784240500b0241c43c4c0c00c280900c0d5880d42c2d9915650003035208460409007800303003900008923107000003240a00348150343c6603280114110346078250446d0180c4202041d00c1820440080029494054601c400c010244006029850341c01402600000ba001c8940300ea4900000d07004140c0c4003a86140c1912107805070340904441903a00866004030304100b18469214040002501380d80140481e410381c1e20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 304327796 1250 304326546 304326557
    0x13020a06020a080403061a06040801060317030601120e01020c01020f03091b062203170a0801091107030e060c1501030c060309031704170d090204060b040302090402011b0501060b0a 79
    0x16504001c81c1c96006141000b0a02402000104045801d5400c20b8168002082c1000c1e1840410b50000780c1030380c010350010b18181d44903c420020301900f0640b0072407501404025629515140300000c1c1820304070111745105596038103542240c85c0c403d50582e4040da20160086640c2d0710410001d40041e042190b00c0b0407a80304807090191340c0c0c502650140c03c0300304050300700c40c03c0021408034001880c419801c03401e0500d0790000d00001007010094405003400c1e40003201d980d40d182c080c100402e00e2105070002c0b2120303402e01c0382d685040b0400d141291401501071400c20210400240040d0341441404201c0e64148144012406c010702d2060649040b00e1140414426165030ba090070780035901c41e8a00075022901c00c03100c000300721600b0340e4150b0788103104900708045030041c00ca00c0700c00c540000312010b41c030b03969a03041442141801c0c8942000343c49600782103814a85103a000550701000284028100181c01001c44041002c40492211060348100280030f095155002040184c012444100000c1d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 304329046 1250 304327796 304327799
    0x60b090d0f142a060f303904050409020406120503031909050c090919061a04060e06191203051c022706040f0801020306011106010b04061206050913020a 67
    0x82c21204407003500c1c220007012800c00c840c003007900d4000c0029502c946035000b44030a12509610240292030307ca06078800d03036020100030802d2254180c2c1487c8440d500d1003480e40940c034000d05000c5054070304503003041320041128222440401d01030503040d4092140b480c80050144200701010004e5032246409010394200b102400c08140e00f0395146443c0500641c0200101c1c3c003003410302d510940d6100c5c1d4078004498824160540382c0390106144901628800d58801a858500c46902c40151501c0000c590501c14a4205601040c0c030140c0070b0a094403e02800c100c18010b92840402c4400820000c4034444842d1701d03605015200d50b0004009000554880241412500603442a10b01807103424441c18140b81c01c800e01d08150000245030203a1003101800b00140d81c40c41c61880c0703c003400e0418005038503424008005020300c642c107010502d4a800c04001404480c02c40d105031021203580f454089912000290520000d2425411540c2c01c0760b1030204211100d458400c81303a038a03030f10030740e480207016 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 304330296 1250 304329046 304329049
    0x210215070b010e0421030603020f030f03032e090501030302010506010c111513120507080319083102010e2209050c04140901060b090d0f142a 62
    0x52080c410001c291040c039100501040040c588040c2d8428440c0362076071101960220714050310070704000710500094540d0320a0085043c400c50459003071009030f0041001c16885101c0f1502c070702000b130000c0c0840350940c0782d03600700924500e075558071107425280350041e0036180d803205000b52400740002c1d0055800e100101d001d5512590442c50000d4000c00e110340b80782500010803984100c00f20015941c01e0041c000080d0007040c80395610f0042155510840c040300039071400600b08425540104c4e8550014040ca8a4610340314a82500030b00382e074680040540c1e00e003040c60148221803140111400583c0f40d03085529503486031150b69881c000d0b01c3e0301c020400400e08119115150000b4140940828010440009801c0d04002d14040c400d006842c02c0200c4040070070704442004080f980c001250b1801e00060210a2048402504824104619124040c000718650a0809800400a41c4900054414080c00c114890301c1c030b03d8030741c0940348184001d2041a035200140c481c1c41200b02a901c041c1d0106 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 304331546 1250 304330296 304330339
    0x6020a0c05011110020301150e0f030606220f020c011a01050405060a030603060e0703140f1209180115091e060c05100e100518060103021302042102 65
    0x109039100022095890409004550000c05a4151a014802d1040301e8100b407441340080e6000c0c01040e0a528001404900e000b0f0103120441d10300f80c00b0340142041000181c4003c10b03007960001c015111f40458400d00c04a80c80c0c00c05051000b412030034507040d9000d410350749680051070403100c0100280704108000d100b0b050f050b02ca00c00700c3e0f40483d00070401088030341400e001804d0080b01c00e00300000e11590b030342c403020300b80d4510008941058101345828801c00426003e40480c01c081100108034104002d40220b5450a580d5006401c5d0000030031103031f0460740c941110a070032103a10030341c0280030350b03650302032411264800c001755011440b01500454001020703282c103020720816214500c003003032a0a0007540d6040e24107100b95a603000361814000d0f2110b96000341c0041d809940c0040039081c4158240d1000c640c0d002c5c1043e4041c00301490f00b80c0c01000f0000d6620b0560b0f03012190400c1080c080b1349110000e1060790b001c00550305030800100300e001d804100c0b02e0400750081d9428800300380549501d010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 304332796 1250 304331546 304331563
    0xf031519031101090305120a0212070b150f19080d02030c1f2307030614011e022406030f010c020d0e011b0b0604060e0c09010c020a050a1d010602 64
    0xa45080310040012031070405100c002c00006041442c030407a00c0351146e5051410780d416a601d02080000d01c2020302d42d04105645600c1401820030741400581d54840c9140349024041824812161102411030f0fa1048034081005100400ea8491b44a496025500e541c0b418440c1c0300e494007072203200c0341180740040b04071591000584098900d0007103001e0318103400e0303442c240b5002845940d00c10710000c0d0070801c402c903100e030035484424000c10300c0e1040000341a034007e904041c58150705440fa07080382e40d0b002010b1410403005151010021248880202d28240c5580032500c2070031403179a24002e03010001200580181c501741d060390b05c1d400c07074202107900740c600030300044d030050b0f000010402e8540d210b00240c01c024041450504d90084580441d400f450414400c19100b000c416070500032181303024401c01d4010640042400d11501e80403c241e4030501030740e0406e606000f0824030b01c02c119174404d1400030140400803c90000503072600500b00c840000e0700d182010b0066180000315615000140201 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 304334046 1250 304332796 304332829
    0x607030f0b030322090c05120109111c09020301060909060509060615161b06030b0904020a09090206040b071b060c050d0f05120145180501020f0315 65
    0x10324214031010701d0704018113441040700192402401c0840c4000c0107000380c000c10b2900396240c42e141e240b00e042010303504406900220045103170800801350800c410069401301c111000042c07044145686c0d40300040c010690b002581540f8201c00810400f00b1648000002806070b081003150b55101454103a45042c142c5003181d12800020500b01925088001022201c010300c000d00c14859144d90344d405034038407241c00d45c80d00042141082c805240d1610624108540031a01100181040d801050140c0700318042e140001c0c2d00c6645c02429921020b00b00c6000b466418600c955840041c2004100c0c0b50b0750450315405001780100014401e84107807104202207030040054100050600010349100d65080b0080381032090501211807400c0c0355014085c0203050410295080740b10202c0400c29503903640420014a4142e146a0b01e6a801111113000e0b481c040d0348000100e10b2010709003000c04100b03608004050350b000141c0d40d05107440103409180684000070504000300c10500400c03201e56201c0c00c9c1c52 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 304335296 1250 304334046 304334053
    0x1109090109050612061608070302480307110901080309040b0a0e0403020c0102120c07150c1707060f05070203030412090506070b0103120804080f09040b0406080607030f0b03 76
    0x40c81030714219400329800a40c0248030062210503000c038142441d80c211010005080c0c90854200c8041c3c000f103605070f01c80010718045181002d80d1151280b01e1000303866450b0201c80c0018491080b200040c4107040301808004070007400c040e48650990349a0000342c003118100d15520900080d42007400321786058030b00c40d801860501d400481488000c202881540340e1042c403004002511011a01c209030107980a540500086407001d400a4a032804e00c1c512032583c04000c0107406034203031001c11124141c48080e10a0044510550340c00c483e1410b000030050400e03254104046038100480c0014121944221001d0140d4010000b0b1031084a004a0f260000340e042080042c0000320582103a40b07600c0140c0c00c288805685842c00304015030480c0c6421101108248014000d210404290543c1007009240c0402145050366403568180941e90884400b014041041400c42e591604008039010001c2d01c1041798659030303010280d95207070039143c030741c0801c0c60002c200a0340c0003d80a0030344440e1019006 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 304336546 1250 304335296 304335299
    0x4060b040f03151d0309150421050304030501020a0f020705040501060c0b060307150e24040314010b10030603020f040c08060f010504080607030e070609050a090b060d06081011090901 80
    0x1036980b00c0e01014a4120070b9907813900d4182c4802501110103022040100003141c461441109015819030200381c0d00c4036940040c40100583e02e0980d40d5851415495110500005614a007041c558082c64200500e554000b00d0007081d003d034803120a0920321082d50844144503511014881264002c0c00390030005488500008007107801c0003900e54120001a04645405941d400e41d020305612940c605030014002c04110b082d1440c1c0a00c0c070b100d00b800840032032180c00c0b0140005074003501c03031407000400d200c001840d000c00301c03002035101c440c0c0c034580a0800f810250003000010003c0c0f8803400201d01c40c0c040894045141d061038071404030a44115114001951900000c0201c01c914859105041090401001c139001405001d01401114141c901091854116444134204402d94110300300f0007040b00c01c02c1103903075120903465003151803030138001510101c890007240c0c2510a0548912407207042c56000911440006408600a45141c804000300c031001c1e44100c0d07141c4603030b0b01c2e51580f02015400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 304337796 1250 304336546 304336553
    0x8011b052802030d060b040f0816031101050c150106120e06040311030f0d0e0d020303070f0503040201090314060103060b06091e0f0d0803150f0105070b041403040e0604060b040f03 79
    0x10036480c28007081c0100d9040c01500c00c44a402e03660140c106410344200410100070b2020014004006007134410090a03408000541d0b0624586541c40302034102d500700c80e00024a40d02640480b4192044842500e001500c210041244c0000a100b06800507980c48c8200009500758401c2500e0180d8401c0030300040e4032162404c45120401c03a00002807804104294882240b2280081454401c031241c08515404c20041c424204240102180107640040003088200f59100064984151301420040d07120f441c2c40c00101c500500c648c0005195410203403940d405903000003007940c100e0707100e91414090301014000340b03c0107000b0710300d8440e00082d028003a60701e00c924040101c01d19420217804108001082400500e041d50102004d03981c20400000340104c0c140c010b400d80e417900400340e41802c460003807200000e115115020010b840098000007250801c8080d043c00070b12068028126601c441e1508501040380c0810f807440d5102c5e40c07404000141c81c03e0b2040c1501c084a80315491f100182c0d01e5501c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 304339046 1250 304337796 304337857
    0x209070c0302010f060e10050103050709170304031709191d1e011503050106090b03040f0c0509160e0904080a0516081b06060f030d11011508011b05 65
    0x140407030940d520360805401a1045114007030041022041c641c01504100600f10342e8407005810103410541400108210725411688210441c0e0b400c0080780038010980650030300714003854100400114040c0585440c5080740405052501c0d821902e40031000b24261421409441070720480e201c00c5150a4100f01111840b4521540944800300180c2d0359801c0340c0b00103101810076041404800745041c004a2495818411540548854104603410900b07183c0001854000140010150303507030310301d42d0403c0040c2c1419072002088050400c00050030219503921a40e200c0d5080d10001031498100d03111030345010710313400703000d01c6c0c205540601d4aa58640122115440301e1000d102540c49040980e00188981006201c0d01c03980d008100c02d60340344a00344900704800a04072030700c542014120050580d5010501d00843c200130304290701460300d004540703400340180018130002c003410007000040c45081074202c183c00010740b07060049040c802d170794181c40d98011b404ac1101800c40b1003188044880016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 304340296 1250 304339046 304339067
    0x50409080408060103080c070e010608130816030806040b0402030f0406020c1c02010f050106051309020a0c0c0f08060708090601050f06040902030a0c11150a020a05040305100207051504020907 84
    0x940405141c6034803250801e02d026400e81c8100c9089200061264100c82c080c001400030300701e0540c4041c0c003540b40150091550001420744c039050303480b00562104110703644040b03400c83c0e5645509420031510b981400f41103032404491460045082c000d02845515082c400c681c440c02c10322007860341c00c0e01d45448030002500b041554081611a121a603000d04800704400004102d11b580003150f94010b4070415403d41b40180d0011042c400148081036040800460341415100644001600d80c071002c1011107504406150140c45051010004107540c0e20322103100e415107041d542160310545406a04841c50401161002c43d1504240c1c01440507150081c1e0030601003400812040c101a00c4441c44001ca03402071700e07a078640503503954000750a15000320880c4016040900605200400170301801c0700b03564000c0141640980c0028040b145902031800d40e4041c5801000f228000242078002c08001d500c0300f03100342e510748940706091800c05050b11009100315400781800c1e0440c2c07680001581c111011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 304341546 1250 304340296 304340303
    0xd020c0a0506090c040c0914040e0313090f050c0f0316020307080a0302030403090503030c1e10021617030124030905030a0e12010c0206060d060e0a030302091e010207050409 76
    0x40c2504140850420040340340110254005880c00b43c8080042004480010359a40705004445504101320820b0081140a00a05880100b81d1b4243d411841e0b095126180d88840654100d070300c003080d42c2c401680400d841c512184020031864a444018640600564541d00d00d00c580800008a440300c00000d00e00581c100d600443e82401d0840e40d94031030076004117015800090b40407080000741a800b407a40c41c0104800d0f40554502006a108a80c6580c0e2079511401222044001c51080c0b02c0c040051031140200c0f108110740711844200d80c119400e00f024019a141d15182180080c2070001c00300303c0303049418131381555032034010540014002582d48210350041c1030f41c4245950205006100410300002c6a0351610541c0300f40340d080201e0080003600d00e402d16850701c007104d514182c00040440d006802120b0129809001e8a0401d029200c41c100403d400d01032041d80504254042d005848198000c58101e80d07140c071070803000301d4560030040800303006a11410003005142095800904800d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 304342796 1250 304341546 304341553
    0x60b040b13030507030305190e010e100e0607030203041508101208070b0f101706010302091009020c0102030f010501020c090f0709050604081c02060907060813061406150a050d020c 79
    0x42e81c0c0c9525050007455817098022950000e080c141c605808a40b100c0100014100707081d4243d000000208000c0c0c007103580381d005500120401b095075008100f0810301c10380c000c01c6196540a03a19000b51250000d00c1807a00701d000201031840143c0c0104461440b072000340c88900c161504d4a4241014441140801c1c0d070904410800d00000c5180800214403501c901c2d0003001090602c00c0003d1014240ca901c19240842081415100d940300424080d04494045800038507a80b143e103049a225402a40010320030f42c4005104586040190095807080798001c0b15490542c2e0795400591b2a0078000884583c0002c0390b07000221102401199140c00c040140b4103510016117450204401d83e02c00c0d04965034541c8468180c03e0107010841081c80213050034405400d450800102080e50381e403060180c40107209544001940034a42481c0b9020100c1e0400c0e0b050004044614051389564000e039130707041c00307040c5440407250b03d0804981211890074040d603482e403034000c1800c40c03040250448002b400a170301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 304344046 1250 304342796 304342799
    0x1407230a0e0301020307030c08090c130207031403040308040b0c0316200d0305040501060914010b07030c080712080105100e0603091903020d170c030c07061b05090a09060b040b13 78
    0xb28244007035842815107880010b000340005c400a03011000007000351915600003065509a9265910f150315190603403400580c40341594034042e43c1801c0018110908401c020082209250b0300c00384550181c1e0007401c080e4010340b00d0010100242c40100c61820554640e0b04110f58110b2142d203100701c00d0140e00000f1903000901251241c10700802c01041c1000031340f034400380002e00c8000e2181c20000d01d101c0204101c401200884074035003000500c02c800301c1c0e0034041294400d06004a1032070b0141070f03202100703075507440039071420f041e2031000620f24400040d200d000124640c20600c00010301080151650078013907844004005066200800084040c003901e070081c0c03080b04510410502d5103202e40c001d03118000718000010044a040c401c4005151140c40c10700102110039000c0300d4004880307001d4140d030780d619428544050034420004041c1d07809500c0388880d24980c4580900701240d0222142e05580d9941d8605400f03491090041160005040000700108071280d401042c014003070045104581c2d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 304345296 1250 304344046 304344049
    0x6030f180715050d1a030c09070918020415030c021c02070503060702030a2a0215223221030406050d0c0f2c0607061407230a0e 56
    0x4a04a0342d14010801c04101000ca0a90b18040d9401c0481c03400211950b038241000000d9541808880a5000d90b1208003c910707164071a02070f081c06008102d50303400940c0c01f1220408000c0d0f116100360210111710303a01c01e0007007a22a0103080256089039008210b1200c2000300810615000384441c1c0552080703050004860301d041c05014401c0d0b0080d0003441d150064a00040d104e80d2080b407003681812080c10f80341800103071002034940041c0d010703541e040701030469200c0d1805a01c10303c01160020040700001c0303108101c80191540a4440c404541c00c1c0040d158a20b07a403075412030782507100721100c00d140195107a040c000c0e540e513440c00096000310841a040d4041c45c0c19a88203810140000d6000116410854524010088050058074010008480b000b200030001603c0403c240005401803002c07031035500000179411503481004015555520403454400f0091603402140700711100b9090000342403038000c0041441d941c60020150200707901105441c181e642c04070002c1828050301e1036103110903 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 304346546 1250 304345296 304345319
    0x3050601201915180c0e0a020408031902100e06011202030a080a080603061b030a0f020d06180e0a0b13020d1a040c0b0a02030d020f090301092006030f1807 68
    0x1100d0061185020416038402100151114138401a0030100390070340c8100003c0d00d100c000402c640a01c051031070542c4520324194082d10a56101c89468800441c03030410081039002a12020a000c1d001c4480e40600d28460005075170020f408108140c025400400ca1412024030f40e840852009050b5030541d511a80c5042c4150020b401300400501e200e01000894102044840d4000407504400780e04149070014113000344c4001040085803c0d00c40c1120184240160103480b8400d13010b00040c454641c541204170542c07800c1070001c1e201c0504281c68400d4007400403944040396900504440f815070b8076079524005000d022041280c0180003845600c000c6884c8203030020007002003003071070003c6003000d0801c0e003041d1002e500900100c2c2c104214172056581c0000c100c522030324007d04096201d1524880c00d0b40e80b801101c80d801d0301035003040550010050308444031480a4951081c14420407640f0017800014041210000c0d0f0f00c020060100d0400740341030b44299001d03a010340840d003507240c55036119200d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 304347796 1250 304346546 304346593
    0x30c07050a05030d261603061409010909020d0b07030b01080a06061704030e03010216020102010506010f021b010c150504170f0901111615020c03010e0a0303110c0a1505070305060120 80
    0x50f2204400c4040031b0240c1c907004580040503d0000c0f070b004d2480040015500a44c18410680d00590301d103540000c40d01c4004034010543d0304414202818645a000a0094481500e40301d000032034000c00280b00d034040388034081c1a45d203140e440d0b081041507004d0355000824058000d405000e1a00031610702c4c1c0e07500b40000d0000d000510707800c1084034400c0c07002900f502c9000e8022418070a08130484810b0329400290060408092069180000e5050303006076408440d10303901800a1464481e240348070b4807076800290080b440740d105000d5034408100c060380e090042103820380784450200a451643e610651004a1100e4000140c54802100ca903540c0700c07201d0994400e00303000402c069080c80c110f405001441c07048005500900149118010041d20381c100c0500040501d5643e030494006114180c0030ba40da008075403000c0713400d41401c2c0c1c03d00340c0d0f20200c01c0055a51301e50410780003600c1030703200f0b010b01805070b001038480c800010f000700042c4210741940d8205002910802c485100300300c01e20700d44800c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 304349046 1250 304347796 304347811
    0x30f090d05030d0207020a05040212070302180d0b0f061e1003061e030c0807050f0622180f060e060f0103180f11010804080d020a0e12030c07050a05030d26 68
    0x185e8440240c410701c80e501d1115400b4030f109a1060002c84001311038004243d5001e030640c54010f982d0f10b803078260815a003d64a4050390407940007140582049100200903010b03108018601e4030315550303070781040074208882c00000e0b102c500c8076000c1d079098203042d01201850511410041101a11001090f0003034419042d5583e8810200c0002c1080c012034042090140c41d0392009000110f080c940866200e40c41d032100c0c680515400a000c042c602d00501030301100d8401180700d204690b99801e001030881c0340c1c42400c448020321700542400020598411174044030307150405100c6542e2150108401c8458001c005410305403100410100e1100840d89050314901c14070038018000350b00d080960038545030001140c180183d00c3d09020101c0c4006054800c1d0140300701000d80c0d0792911110458003110120705e0550088001954200d0031030303011026010000f0b0507011a119a641d0354100180c0051a10070b182c0c054201140e1010600c0c030502d806029039000c0707080e0364804d441d5404081da6030141218002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 304350296 1250 304349046 304349051
    0x30201021c0b031f1401120b090738030703061403061302090c090a0b091003060620030c03030106091a0a09050d020d05010e0f0705060c030f090d05030d 67
    0x22141103003040c0101d40c0c6018119030400441140c4030200c4d80e10f41404803200c01c08065002890109401d036004040400000e010903481565210b00c401300b9a054194115005018040010780d400000200c0c8000c848024464440000071094242415100c0c4c450318010100c2d001d441030700180c5140011030082d54503070360025101d864240320380051900e541d0241e20a070080d000b800038020b12250594505601141d50f24003548480303003a40c0b5039201d840e1050740c2081143c07000180440b41c601c05841d418a013034038a0f807510000c4520450032210b0390301818000c541650341071500c8a41018484035000645422203251040c1740a4152468009a20440004000301001c0c00300070045810034480c04842c0d51400c0c141600c41030302400800140c01000d01800107640d00100350360b0341e075001c040e9a6400100801411030072110035a12007600d40c100c44a0343c425030303030f0001d59170510400f140c2c1c0e80340c04e1402075824008a4a0706030781c0c546c0003070010769004001031198004039109200500100d00d082400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 304351546 1250 304350296 304350307
    0x50c0105070305070b0124020708030a03020a05041706010302120a03080708060612010b0703091e030201030b0a05090a062c0a051b0d140f1909020112140a110a0c0b04030507020d03020102 82
    0x3e104007010047c1c072103030440d040702c00c0800c18a2400025a4507480150030007585a1018810444083c000c5900c950b11052550884101c0300f0f2000c241507060364002e40c0c10080c030b041024911036898410603002400250082d0000b07614910030b0312a10303080032000b01078502d49100c100000c40c0114080c1c004402c041c20015441040603000183c0340d00500c2081200c00c100d035280f000c5015411101c0c8400384c149a110142c19419030380360883c074405004014418409428107800700c1008200314018104801c11940032000d00f2014582d400401c4142c1c0324241d0110741c0d801f04102c020300409880440c10000600b0140300190f031071800341211441c54440042c0702640c550452003080005000380c178241702850b0a22045105a6914035080e0000810200e1280a18401202c1c3d001240d840c2050301813406038a0600c3c084481c4c03004d40a001c2d000380c144513581e40b03804000303294414003080501040520606c000003960428400b40e0180c000d0a105040c40c07103d401141103c0007070102280180d500041e07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 304352796 1250 304351546 304351589
    0x16140915030a03030245180702060402010f02030309030f07050307022101060504090b06010c11030304090605010306150813150f33061107080a0b160507050c0105070305070b01 77
    0xc0034044600c2c40300d4a050455500e102e1a25044040c0c01161601b4426299130350560f143c41c140c82ca84180c0041d01d1410914101c03200a40b03452007600c040f070000d405600541740851000080d01d01403203a8002a5184c5175254054044d907038403824003114503010510005015994901010140300c0c20100090070b0107040385561800c5a8464025030f20681c50114080045504281903d40c410f00070700380080b4007c050f0038000440d42201607940e43c07600c000100031031101000d8002108035002a2020703c0060f803902c4001c42c440001c0c1c0c14000028a220f00090301404014080204140c01032100c250300c2250740300c1c10007d9038021a46103808540b1106c2c0203111400c4600b0020320404500e080c1109008060b80c40d24a41c1c3d101e02c42ca10801c01703505d480080510382403001c0b800034840c010840e141c0d01c0140c600341c1d2000d03404540c5507001152540b00314141a000d001100e5049501c003001d800c0b2000c1c450b00554240d00b1141054080003800d0102d07200003107842400f24007070003540c51401c112100424 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 304354046 1250 304352796 304352827
    0x70c18050103140601030305030f09030d2d060806060105090621041205090f0103021b031b060906100b0f0f0309010501150e01080f04051906020301060216140915030a030302 76
    0x30b03103030f81c000d078440001000881d034800309407504200740c0d00c0c000700d060300c403480058618014100641120741c50704880485401e0b610385011520f2030410540d840e0034011a059104403000e6110b1000c0a4006900140c429885080101810000108618100f00c6600380c2c003803e0001100c02d01001c56042014481400a880e0308421a2401c0b841d00624000d100808203490641d10800e0a05241c2c022445100c00c8150070b15050740d01c04400b003100c3d102c0c1d040086c00750b000303009022032501a00030360011131141c1501041007846103091542800c134807450b0018030030050b0b00031900f0404c07100d801c1c081050000c0840300214054401d500000c5820b5052024402240c40b240c00a0018814103030200a0540d8004a00e198044150380f15100250b869003041030900c1041802110990f044404440c2080304950103981622580d608550038040c40c04000c2800070b182d4000c6500102601c283c080403803030030700500c5902149400c1d801403682d0200c0c0104e40750000c0002d08401098010903950210304000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 304355296 1250 304354046 304354073
    0x1a070504240e0a0b0a03090204060801090807061a09070807050412120e09101e1505190c0f060506030c1012051302090610030902100801170a1106070c18050103 70
    0x40b0783c00c8044624190072249248200501d450a00d074031400d0407815923440c3d500410080c25803000a110500c16490110510340c0070950880395140780c8812607420a00741601400b074101d01a010b1106500c071500c09440ca008018848010000204400300740b42850503d014041031041c0c203004081444030f00080c1c2100c82e07100081d4042d07401c903400c1020740ca040c80b14440803148140b01c10404e40c44011f03030380d0900354559007141d80799107036420080c140198002e0080c04001c104601c0c0001c11003c80c60100c1c0c080d151301c04080c103131170300c41640e040c08540964015a0001c0303004048950207010040031403440b60348140320901051005036030a240507042c0c0a41580407404101803001d0081903030008814100142146005050000030030100d81e0090380100b0308a6001400e10b0800f0044a0005240c44001d01664698150034615840706400c005440f00d4240d071300101c03802950f2010070a00406402401c0c081d90100c118600000f103031007100f880408442d4000001090540c1035050240d200c1669 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 304356546 1250 304355296 304355299
    0x1508070203180102010e1509100209031005060f0a03080408070501090b040e0c0d0501030503211317040e090c100215060d0602070b0703060911071a070504240e 70
    0x1442000425a03020084400308060509079070300c80c03034042e00101d0050406807070024091158281c03210280319a540014800d06089044807805402d40c4200802d9004111115405034040c0c0300d074403081d96041c0c024503440b61026000c51801220480007800f4400740da03200740e441c03c2c0002410b20081d40d0500c0300c07070098030003070800100192170044106000d10031403041c01014002407002c00c40d90325284040f1030310001c0c0503605000c903586070f0601e580c80794040c40140c0e242a003c001d00f0171b4082c11101c1d009100c2c020400c100440d2a01c5500e440c0009154240340c03d5100e002000042411280c4070b06c950b000c1c54013180144503003007041040c0034402c58100c9500d001d43d40200007081140b00c1e0300c5aa03a80c4180142c605404860311131038090003a001c0c00354024403503540402003008041c2e041c2d010b04111210701009100d801840c2000c0000c3c1e10907040040c2a07010403401d40d204e00a100c00c07210750407807801d1070070038501503030b41c3c0d000041110701858440c404598580081c6c0ba1a5001c203101070f00e00c40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 304357796 1250 304356546 304356557
    0x1207030f060e011e0527010603050c07021e1002010f140402030d030e0a020d03081014210a0602030405061005041109010e0102150a1e020f030103030c0501060f0f15 72
    0x50810050207080c05200c0c1d452a0b902149021040c2c910f03070b41d0800005c00740500204501414a1071020303100c06491010000d6454100000461314828042c1c03a0081c0c00e1780c000c0078a020300540920401480c503400304034103540300030402c03030081d1191440c00144e0800ba500008001003000180c00684100030440003200300324005100142c1e801064000d10031203a4200020401c401013610750034001510000f940c404a0640c1da00d062540200189100312002d400341c004998071610102e45620b02003d03001d801041c100442410040408250b00c80344005d01b0464098400c0c07a501e0006903031044800319590303041070b411703c607440046c2403110020b01000c079814000595130580e10380203030007000c1e032290400a50441c8000f86074000d101103815226590300310101c501c0d00040d14405844109003401c16a07207031000b441c0188d01c840c825907000304404810103141d80d1a5807011650b040380c045003074a207035507a01400104416a54010300050a0440714420121b20f4007045d00145400c000c0141e00740300c03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 304359046 1250 304357796 304357799
    0xb010c0c0b270117090a020306040305030708060301090c050d02060906162102030a0e06070c0303020c011101020c060106081b03070c02010806010206060f3001050402030c030a05100902151207030f06 87
    0x3a00130490451602e005180304030695501319600d031504907445c1003e501802110248024140e0000045226103450340794640750b40c4440c01070600721010060054a100c00001084c0030360702d0100c160100d03060000340198141402000000c11130303032201c1c200c04100a25040c0e0303c010040c28040a200c043d446080d03401071840312007400781d1240701d08481d8004002f040c0006950559980d015200090b403c82004c5840302e1b10380c90041d58801c8410005030108100c94010b94401030140200e41141525a015041592802d0750540306914060300301c1015540400c0c0c83c0203040306500195106118540e40c0032500c141d14000502211000f410260454002c2004c102c000d0f122010000f40c103590075aa40840325142800c1c2c08044042d1084070048039912030442c460103041504034900843c001c800313884880000328205555030074007201c000d21076001a5960404003185601441c9503500207010140040004c1c40040c009920001c04079000920302c1040c451052b9061244a41800c5807400402849 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 304360296 1250 304359046 304359049
    0x7092405040f0216061d0307051203090a02031b01030501050409110d1514011401050c0d03020a0c0803040f03141c02070804030615030b15060a030b010c0c0b27 70
    0x908500840d801a0340380c4400d50340c034103a1941241c0b810742c00310f44228a039640c02c0c9480d201424510b00700100c40707401c1d00c1c1950000342006c000c445e41c05501400070881c0c114a070007030b802507400007440d08959015480d514005a2000d200012000b00c24030500142959000009022108180c00c283d00a500d05045240010008605030701c011070201d0782440001c045141201400300c00003004036145082000080ea0001c6292509050b80c0c0780700301c0760301d0130382a0100440341c5000399820911103074880e00307040714654021f600074200240d0a1901219084640c0c4486071190f000703450031580010014580014164001c2550a0b0b12203c50b440c6032030030270008110060032501842d9801d260358000740c54000c001845c4221401184e00103000e010100042020340391691841c4019218405000005204d81c56440043c00940200038142420894014030481c01403560b6665141405010900800821801d040c5940213065a800c01a0350f10314142c1c492841405d6100b04d88003047d1003080001c0716 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 304361546 1250 304360296 304360361
    0x1090501030506040b1207030302010b030d170c04031b080f120d02090d02130c020f0705100509130e0105070207060903050604060b030316050d08130201080c18060c0709 74
    0x2228400d103008107940c0c440e50009001009840c4409a000726030010000c500500800c0080c11207000750001c0150b034848105141e1250780481c0f42d00c000442400c2403401800000110540006040038203038113158981d5144c0e82803102100ca0031400001c1040c040181d000300f009610b204001c542c0150218241545106825018080c0e0a0708015004901c0190b90340386c0c10400b51201d40c001305002c1c1d018001e164190010308161081d000103000b42d00078032041340b10000d140340440f200580000e86400100b10219060740000d020140d0040b1038a14864003d900c1e40900215400c030784c0700015141c1403550000e440e0140e264404010700540b050200041240801c8440e8480c1d0011404a481080640064103510485200d49800c141e1182c2c0c0c4401d00500003040000229180c0742c0031030644a40c1c1106040c0440080300a00095403d070004007134440b0007000d00007140500c82c003401c056001e00e00042032a0400048500558800360b820040042907000310556000c02030110410fa04500526005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 304362796 1250 304361546 304361549
    0x2a0319030e121b06011e0905060f030d02011413050c0d030908160914010806070c03020106050a080c03060106170a02090d06110d1512020f120303070903061a0109 71
    0xd041d600e203644120000c081c0546400384019291241d0340b410008010803c03900030444110861280d0000441d044000c05542d5034502070741c6180c10203091902245a018040c01401c0b00c0d000382c0d100d0a045d40c2170328100500074907402c4c140c00204400d514035040303041124009280e080200e51421120303020440104030040c030700c1d0b4152003040320450541810742d0070b00304d140e0029045100e51401c41401c0e00d00301140501750381e0100303030a01c82d0390004850009520828062403d00c0e41280001c110440e0294001a00c220302c680000b0440036510800503111420315484404d25402590151000703107420f0014502400503410300c80095901040358000e400801001c030f58003039a00044110465442106d03041d1015070000003031040d00101a040c101b01c0d005000041203c034180410b16001d240b01509550036a10160085000c826058003008001d00300803c0107a0001c0f46525030801d0305000b0300065101780e5454541010403442c503c1c1400031904640001c2c00c030b0012820800b5100da030b001c81c9010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 304364046 1250 304362796 304362847
    0x606010305061e1504030321060302010e06091801060201140a020a0207060f140301122306220c0b090a080a050303010509041a0412020d050909180a082a03 68
    0x465403c0e0000c00d03c0c000311309040d41146640410004101940722950143c4030f10610440c07020303000c04025035000d40c0d042d0700001340800c41205e00c400003400c1c10005881c04031402000101031256020758000c03e0842a000180182d444e5045080007015400000390000480d4004520306030b4001d1000392140880d000345801c11000b5500c41c24030790b1103140b00c080b664982400c0a42c0d01d594468481c0340d2128503010484200008040c0a4035908141011194051045010344031969820700360640741c2c01740b001d0264261184d50032200204d6915400b410161004121540c1e6660b007c8042045145890740180100c0d400011014005000401682d0440304107851250441d00d6078508480b4140100c1c444080e800803410404c002d010030704048c40108681e6030281c0d1820101c00341c044840b07110740e11900350041c40302004158105408480103178901548000d07654101417507a00c410705a40f0600c4460140381c0c02100303d452680a0300c021404151040e07000310b192200303529039409042103006000703 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 304365296 1250 304364046 304364089
    0x180302010f050c070609260c101107030507050a08060106050f30060109300203071d04060c0f02060a05040c050a030b09100b1e061c020a02060601030506 67
    0x1c600a8040c0c4161180c0b260038030142e480702910340c04000c10640b010710810380e5003035001822041c250481680c4080b8203141c036018210070a8488103108104400303180740010464030703005003401c04105101d1a8040c6110350050a22903242c0010040c8840f01d0340c01101d0350350041e40c01001103a403c02c2c220340741403190100d41d544810b41350100d411030015890560400300c1c010341030075110786111800e8034030032002600c60408c3e640c1c450003104401d003000b03224160780d501e1030b50200000700c0c05801d1181c00c2a20040440d0b411644500c0c1030982e05640c400e041c54500070b440309200402c80c82d4014151845000e01c1c261201c0760080c80000d548010190401e0100c50b960404036050000b040c550501610303029110441e916501d141244604204803080e00342c03402040c03040c0300313822650302a4603003c100040c4200c25000b04008841c0c400806110900d50106040000340c124042100c5420310364103005030300584854100314081e08101004211a0426160608001269a400c59071858408840150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 304366546 1250 304365296 304365317
    0x40b0609030a030c061d0c0103050903160206130b040b0705010e030f030f09070302032d07030f030f1206060c060c14031302030c060d0501050a0602030703050d020d02070c0e090d18030201 82
    0x83c45c010703e1104407460203212140c00c4c5000d580c100143d080708205007a6000c002d290382e00c4003070320707180d0091720841c920303c82050190802500d400e03c054a07a078050034128030199542d80312044010740c8164005030400d80d02243c2c84003841028402c00c0c00c0021000d01540c41d14040c42c2241501c0c1c400205000107008440c00440c02c500c03c1089000e018540c040c04450000166040c1d600360140003c1e852014012190b030260900c486c0031581502b00c90b8002448261800c07160780aa545c00f4101d5103080410082c01c1910500085074004c000052806072600c01c0f80110314104841502c40e004216428001030042d0106420b40000c00c03a81e120044074150040321030345100080c28003150303448541d4012000b00e030616280810b94006412110b044417081081644c6a5050303840340a03180019010580a119140d134000301a0000e01009480c2a0010f01d05040c590307441d808203200b60030640800c5442c108116a40108211241c03005150703003000c0c04045600314100c50410b00d240402810404020803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 304367796 1250 304366546 304366553
    0x91c020a17071a12090318030109020a030b04030c12050405040f05060102060a0b011b0c05030f210702011b05060708100315091106160507050904020603060d140703050c040b0609030a030c 82
    0x35601c56918007a088000b03804d110075007550321f030821078026a4034552002d1000440ca4144201c40035144e001d070641800b07502d5516803001e20b04c0010020b0b01400244d400d040005110007000c0c1040b91110f4460540780c07030a15050200b201c3c0c507055003c074a989040305002a0340c0e00041c40a50008580034007044180c1c1410040b24440300a247c00200c1d5070611071110304000c0c0e1000e821b4291041641154030307600081c54603d964000c609641403a03280050380400819020100400c038460040c140481e41c580d00b461103e00c841800d41003a100d03504104144a1030300c3d4400176203608030f502c1c040c0254420f411901c5074620361200c500c5a0003001e68407148201041000c04000c00e4828000700816160306a80701c51103291000304404a0703103401401008149403034600d10306805141c001d071403203046070340f883e0500c2500d2011202c03c1d182d45d984000c810301403c4081003060080c0d4030400180285803049003d010650f410b00a1302d0b8031821060101000070b8900150803005981c1500d003404000c9103504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 304369046 1250 304367796 304367849
    0x11b0b060301060801020d0b040c030507050403110a0b0c0a03022a010305090f03160b01120807020918030f0408120304050a170d1104050f0904080a03020906091c020a1707 75
    0x602c4101c20394000700b0710001c0b103a4564001009820207132002d0080340703080072044088230000c40b375003800304d9010310042c40030030307040f02900d07007103100103440c41c2c4081c2c0e210714180c101604240185060395210202107020954144062125101d4156688006110b800f200da1880004942242d04250359000020701204081050325070a0742004250f960301c4c030301c0141c4904000010501956201041000003c0040c9903a4880060f1900050300c0ea04115265003004480c03003002d0158803055403000c904902c0c50380c00344018288000181e0340140d0b00c0e40307028499030804012804100035180e00f03004000120f1004a108a0f40d02d0b0310444e2004804039000070001280141014001c110b0b14100c071111840022000500076038400701c0d610341d00541c240d010494000d20450f00104103170014003508401502a8000d03002c08480146030a0030301c601503020a0400c805040309150f24408840d10300150b0030311400d0040601610300071442c51700162151320b80d0380c2c1d082c2c3c860030b070401052011203000141c010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 304370296 1250 304369046 304369049
    0x1914070c0503070f050d02060106080f0a020901030b181e0f130f0b0106020a1a090c01180515030f010503120a0e01050f030405100c090f0e182406011b0b06030106 71
    0x3101d00340c140c54050170825901d01038050002c01501c02c41001040d924001c005581c0703d64581d28000d2010307600d50106201a40050030002e0501d51145150780f5160348400304c81c000d500100303911a54902d00340e803000e0700404c0e0585541c100b4950a8042c49030240c0da5480d0300e5840424002246814070f80c501e060f0800192108015011140007030000c01d08560204940c06518003400001510090020511881300320a940c0030001d6032140d10406541c0d40949451122841c08091030306507940d944000ca5201c076203940c00100400d00020410450890043c2d409014240541c000c007019469401d8840c038502c2181d443c00d041c018000114100c3d030388034204031424100820943c5e40c6034209450565540c02c03251105502c503600307241e081041280703d034404000b1500d0080440c0580d5180c2060200020009002a04248810085944044400c00c030038818034102e00c208045d401e41101080c1c03101c0c140038120504100101c200740031b2400072032a48010a079040b840b4071026071100030009005081c107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 304371546 1250 304370296 304370303
    0x203040221010506030d030b060d0c0201060801020c0a0209070207031a0603010603062307140706020306041d160b030c070803250e0109080a08040e0a0e01141914070c050307 76
    0x407010a04016035040d0000b50041205404a809500d1402400e40584121003c204c1d0000341c28040007503600c59035003180310403203030900000540c140c99000c41403ea1b801203c00740e006610025070300c0114208075103125408034035071018080349415035403010040c542d200740301d5001201d680003268442d03800303610000007141c0c4402c0c2003084428441d080304580f4079a1445101c1040300000003011540504500c20116501c1c0516511b8912243d5400000350009004c483d0072540d512580805070300c40300c1a004401c43c203c0001e001c40c1d0b02c1c103910000b40e43c40d0f030b401c41480300005005001040c5000d0003500d400f203501c800c4080e202d83d00e0890a000d4030303001041c2040f07d07620340141c48a9a58110b074111401006c2a03a503400d85a45410344070342d0f1258050001003003005c2c1084108406100f03041129084981407a000c90703290120302075a42034402981000001041d144d041c004541c0074803904858a0003401003d02400c102c90760065000b000080401c4140142c00b1090810040140f007120b540c4c0e0350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 304372796 1250 304371546 304371589
    0x5190905090f0a0b240c120a271202040c03150e01051203120a0c02030c01020301061d0d0308010608070c061503110901030b04020d03051213050d0f021002030402 71
    0x10648007480001005550102c00c062500b0100351050130400418800e800002c00c3c41d003440703210344103a001c49602c400c5411000740101c00c47c0300300300e141c00c030002c00040b003260380ca00d2100c11a4132440a00700001c0d02046010990300d40c1c081101e00605121808034940465000582040c01d0a060700a05203845a800b805c0699040124035211074a040794180d41c001c0c0c80c01317261003000c82600ca58038032449081d406505d142e0740c0058041c1509412982e6840e2603881500c0c2042c0c0e110095600303980007078200c3c0340842c00003204102909190710f1480c4658904a8060441119039240a8005001801130f481000030305400904030901450413418107907400030701002984148407040d192019280411070380d107100600760030410300d0440030042c1a00d400040803003081e103481c0d0030803102d0f2410120071001e00209000e030340100c1416415041c0b10f0007400d1510101c10125151150030701200c130403d80c050040500c1c80340e4406078005035017080ea007070394000141c1c0ca403128000600a01c0200710990b03520b06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 304374046 1250 304372796 304372801
    0x601080c21030c0f0d020109020f091506070c15171501020309150301050a1a0409020a20010c020609010c0909090c05030f071d040b190b1207170d0519090509 69
    0x2800018207001900b00384d8140d40d00502002e40403400c0c0c95005001a508c0840c9620000300e919000030415004000c0b4030b440c40d000300222010406c644c1180c607054800d0506018104042e030400ca01041d80c42071a440c042060144a03618051660790140021918a0030f400054500d64020021295007c40c0100f459103881c071004080f500c19842405030600079190042c0005100d104003005425001d005100a41000e00340400d5034000d422851160007080420034407842c000d42e22000d80d92404a13600c00100d0081708403036000e1310301840507202e040310742e1601c9074030003000e82e0103200b21041c0c0300040808960400d250801c59854801c80d00003e40c940241c1e8607004890f0070009070541100c9040c0c514805a04040345159281c4004642c0505803135a58000104c103140c0100d001c41c4140388801002911040220109442da50f13103004024103503202e9403003030046041c102204d650300c0002c80020b152171520303008001e01ca8020810610b582c0f00c00825600e4000380030f803000300003424000e4101040d0b072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 304375296 1250 304374046 304374067
    0x61a0307110c0306280908160807020a09090201022b030b0109090f1d010903020303010b0304081b0c041503050a0209040317070f03061202010807080a060518090606030601080c2103 79
    0x810303101c0c1d1100d00e00c017002e0102d115851356019203084e0a810041035810000490788071044100310642c11070350700b1030400084005903034019805000e071140708400a94000c0b24400a0315011300c4201c484000340b10b200d664440700c580d0600c2120b81928615008c600120701c04016160b220982d000040224148a0342c03007410701e6198024031611000d840380d90340d800340000da001e003202d2041c01d028006820400c0148081c4607588025174000b0312500700d007486c1c101d60202d0101d200c06240344050068004030f86c240050700e40380c002c40e0702040d60010300176031942c907558409540302c0131750800a000303051100008003414060f140740c544007490301c0360359030a519101c54010801048034070180301081c0740c5400420848504d80d0402c2501d903040c2c40b103e2890309d901e50252075a040003041444225141d031030109890711030704c0c450780b0304151602c040300b02e60801c040150300b4010018130a900941c00240100301304540000c03040e11011094909410328040760008040a41c0a04203021103072000081900e5030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 304376546 1250 304375296 304375321
    0x403050f030903011b021002131706060a140a12030e1801060207090e190212010207030207030b13030c2405090c01091a0a050f04030611030406061a0307110c0306 71
    0x102904400030004a4280c0810b80c260340e0843c0410001640701f00d010505211481d401041071060000100c41001d030380d00402c01402a4540511400b50806000e2050a007002c3d60084050031500c82040a80000700012a415020922800c0e281c0c200c0506840145405030b003d00341c40e07030406480381c041c043c0302c19030340c008a2600380300b000010300c2a04000215401c052103100e5004070a00c015203005075040d00540303442e400c40d580c04d81c0e22810380c3c0e240c01f0098400344010000103100b03401401610385181400c004215004003c10200c01000c0c450302c000960000d00380080740c3d40452070b03a0070711080d030a450112540000b5a100aa440e00007802141c100c0007460940d288402da032204405501e95061820104400c3c035a0802d80100b80400c601c0785020f000640b0106a07054825818150341e42c980380c05403148104202c0c10b2410000c00d1000707000990007548081d0000c2e403841d03100c0705c0400c501c0da4000d1000030644804c11020820b00c0c0d180f034100740705040003407400070103c0d546418125200000e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 304377796 1250 304376546 304376557
    0xa08040218180f0105040c05090601090906090f0b040b150a1b030e04050703090210050f120c0a0f0903030504050d050109171c0b0603070305180a0602040f06082401050403050f03 78
    0xb80c0f1583c0c00d461000007050080300d02c26980511114209840c02007800301d03801c009810305040c0850081d001c9001301f0f00e4401e0000420318510007082d0404008038490840e140c80343c8060080b410070f4110909a01c13003000400300040c1d403c1ca0180c7e141000c0004540d11240700c0300d0360211000c1e450004003450b6101d030a00c2c0010004903820003090f1100c92003030f021550303412802034104100024403903100b402580544030000c5004803951404070b0302c0c80342560204044650f44a0340d900400d403680c0c001c0c0c0c8480081151070703013424800c545900f5610050200e0180d445040d1007000380c10442002c01c8070039000780114a44c48100380c03000024805c400c02a41c1c00c44020803c1c40c06051148540c52095401414103069001d00300500c0c646a402007100075120043c40781d2440d503114900d61008400c100503804200c1d0060f5001a2100c4c2049002c400c0d00d1010391080d02001000e00510a414101d00c80c07050075003034a6283e0300d09051320800166064056170344060960700452041c0c140c1d15030080001c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 304379046 1250 304377796 304377841
    0x32a1502030711180a0513061401030311030a0206060d0213050403030903110102040e0118020c0d020a0308071106060d030207050a06031406010c0503030a020a0201060e09160f0b0a08040218 83
    0x8200340504180400c1c40c800030f01031024201c011002c0740da124810b51040e900503410124030251f1040d6a00d9100540c0c0c640810a40d039410041b0042092640c415856109500c0d50009035103000050040217540f441d014142e03500c1900860241c10071595000d40d00c0002d112a903006010524050074003900800400100b54049258204210860748042c42200e0075640240000e0351141d00740249400070400800840b142e40354200b04070041814200301916038800c003540109600086480d0003812103001404030014800411001520071201165250780400e0580d02130b0641800c600b012460480c0319400550070102d800f0300464965032640085c0c1e00a180069041030907190f910044504802061016000da001400410000041c980003001080c60500c00030480c20744130f01c08522106400d0701c0032521076012000e03c0346071007505803d00000745980022005403038941035207003078140700f2180348008000b89503001800b1581d416600e100902034110a0018902c0c001c0c038080420f000916818 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 304380296 1250 304379046 304379063
    0x30f1501020a14060907081f1d06012616060e031c030603020f0303090a0611010204090c0507060b01031a01030f150f05090f2a09030609010209040b0a032a15020307 72
    0x10503440e074005161141a180c0d414234008146412070040d0041641c0d41000d14002001c07420302d500254100000c0780a00200d07404411134500f00d00b201d5810010182141c4065040450300901d880d016404540465000341412100ba06801d00040d003040304620290784011002c603411030318a680f561245040e00d1013910505611448041095541d00500401c030740d1100c4072920610140d40b154242e050007144410003d424180c940b540c56007038421104500c800270f180400c1a20034003106014a06178000d003800c00b000544030140e10b0b181c1c180b40c0c09455505054840c200a540c3c030000b940031201040300c022126201da5218010103186100d203101e15849800400081080071581420550040580d00710042c0d581190110f901070310a6842211651001e0600604800303881c14030030144180505e00c00180d0721101842044221480c1c14001805502e04007406d00c0040d100d001d9035030710800015120703082410064044c0050f0300250300801041d0301007407a0310740c5d210307000405804c0c3d040c82233201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 304381546 1250 304380296 304380299
    0x50c0f0306120a0615240e030f07080c010e0906010c060b19080a050d050307020c0409060b09100807140607061824050a0507201213080105060105030f1501020a14060907 74
    0x6034080035a03c03105050340d1121b4590380c4030b000d0b40079a191840d00390f006404c2c0d4401e4101d80b18050308000041d0311554041c0c000343c000520075030b4003030210201d201c4201d500144038280800003e140a02c1000c000701301c0350303980110081a64802e42c9200340c54440d43c5114101c40d0310b4071003241c0c89082c0143c0459003131044401706080c09000300141d0380304071510313070041c15140c03025010000542030f158400c1c1d807074941d1099210041d44407044600d2050111030b010f80b080d240340c041c0c802d1401d4802d80c0083ca440c0f101408200e004d5aa680c119000c403504070b40c000c40c44100500c1d4040010710712010081c892001b00030b03442038140b10f00c0040c2100f80c582c00b40810071035031600c0c03007038023604c10031507107400060740c100390005141c241c0141b29600c0a84c441c0c101d48203202607803c88074081d40580380941510100900c10080d0400034050240c1c051800e2a0280c10f40c20000a035821000f0040d11504102d6012006074203164400c004041800c0d0b0403451030300640c2c0071a6200c98988100713817203515880c05034410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 304382796 1250 304381546 304381559
    0xf06030309051c0b0c03131e050c0103021602012015190b0f09040c0515090306011208040314010207050d1d0a05150a0c0204020a02011509050c0f0306120a0615 70
    0x50f104400e03030400c00441d0f01355199118950369600040c0001c00c82e0000c1010100820f040c1c89180040d11115031000c3e024180c4e60030094a0b040421103114101801001640c45106541544008142d820309050240c410f00040102c91007a107103003c1c0c1e41d41c2c414606c1440030015445103d600441149003082001140079500905440d03442d4182a00181c01e01c4c07249030941842c6080583c801c3c013600e451940c4075110f8001400740c0424078020712440d0360105d04c1c81c0651a06100d03082c0141415614881800c01640d6040ca4901071840081c014004400d00030340440c46c29011103a1069006d01583e100900d051406030084582131034070625442800070b08a1207040034844002a91030003804e054030100d040080940035400b52030803004200c0203403840001038a40340041c0400c1c40d5160000704441d81c43c44d8040d010034115602c51140d150510b018403151410b00b6048400340f214004800340e6030340e11000441c2c1801030400044140e88036400c03600061001c1a03002d50030103480e00036003840469581c0d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 304384046 1250 304382796 304382839
    0xb030118150c02030711030a0209040b100b030f0406020f040b0d02040315140c0d060503030403141c0c020105070c03080d0501050102010606020c0a0e07020705130b0405010f1202090402040f0603030905 88
    0x72010307003d603000300507020100c0c01100340c44010b600e004040350000b4070b281e40881d19040b0140c1e412154903611509018154900d0007610001c1e01103510544c0c114945100480d140100141c009400154001941d02d0580e050004072806040b8000350f0b103546407000161b4400070b6000784400c2c0c5905041381012202c002040c05041c244000f8480200c100707403140e1130328001a5100d0710240b0046d650b00c24001406071418409840118040d8500d6121000e20015641c142008141014515020940c1c020561600007108214103602841d01507100e10700780c82c01c1c040d03079000e076000070300801d1000c1001103800c01c807500080e050f200203034020720201c2c0d59048182d95030302076070b155641c2c0301c14020014020000c800b00c41d6980a0300790b10443d03141b181d40e1400300d4160101c0142d0356070100d81780d65203007a003401d160090750300411003d0485e42c101854100310805000c842c003402803094501001040139550745401000b0541c140c00c42c1007045ca0345e00d2502401c020100d1040c40d01034001c4203480522000e41a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 304385296 1250 304384046 304384061
    0xb060901050a1101061703030901060618060804060612214404030f02160f090e0715020d090b04030807020d0f0804030b07110f0d050a030b03011815 65
    0x40e11030905040320200143c03042502c103100e1040c5076607a031000240c0e01891606040d10340303083e480034540c0ea0030109034480c2510100c2d08464180524080d408000c4804c0c00640380403a20a07140990040d1110f18010010b0304260f4428000401c0590610050005480c0120680b440030160310100d40c50703801058400d5051140080c3d101c2c101e040c17800300010008003080010b200c2c8103245200d00441842c00500c4d945003501c040d4005065462003641c0c1035010000c0ba81c4410f03c40403840141d0b0300d01a4680e9280c2280d00131411000e485081078841041d0800120b0050700105404149a060240000b0b6031120710315229400110b051100003403403c01203003164152500400601d02d440090f4017484098441c030b20341200e0300ca003202d0001001c200100040c201941c03241400381c001d82081d1000806140840c0704007955030f0812400c205400c0c41c00250b081180b2032608003d9298036030704d01c0a40040802d4080240c01d075080c84003225000c08080440c0440c20b11a51944130a0400180f81d00120707540c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 304386546 1250 304385296 304385299
    0x1905150109090b1801120213061203030c030b0a080f21090d03021501090605010f082e0302040f020c0607090803030f1003141506030a0302120a0507081206040b0609 72
    0x400180701100d81c03908003820703003d0003800401800848001540001e2000d81c0b0a400340182a46000118602a00c082034480c0c2d200000381700c1036040800c85da03480158602d006080c1982c0e10005801240286c1040086200040c29409060b0341c0380c01203a1109041c0109400c98040d08801104040310207000c4090101c45604d054100340c0a1070601070a1070b02500c0550a40c4a0b030031035a40070114914455018000409012401503d004005040780d1085095003040c008000100714800000701240d00c5064107180c2c08a01602144414001000650704081d4003d820300600007159041c2d500249100d200200c120f42c0d15945424003101e80541d64014000b0b01e400c2040492000c000d4844031035044542c0120803c61a42d0380c0d91640c0c9004507100801c04190850024100fa21003030220b506d9001000f5005424001c0441c1e90081d10786001201540b105034005c623500440e00d2190040e1140d49901510315681c0303001d40c0401000340f00c0103d812074403031b44c00c107820400f03d404d22400399280307141c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 304387796 1250 304386546 304386557
    0xd0f03080127020d02130801020c12070201120c0306080313080f03090a060e0102070906080c03072c0a020c061f05010c03080a0209010c05010f02040e100b12090f010519051501 77
    0x20740701c400b0400313540101c856584080d002e10114110341040130344800200120780c00180d44401084a1705d09010905252800051043c4a010b01503600510121400d2040d600006858042c1c1d56068004100a030400d03080c82c40b01190701180608900c0009055500c0303641200e420844ad6501c0d5941c2e486135050031b580124200038100929406007007104070108050041d140300319215490030742212003603400020140d000343c9100505040c2485004050448421612060700d0f10004400c000700e52207208000c0003032803000113103e00762541d0507207140860290030b480d07403818000c43c140041c8800e08000145501f4a0200081540c09920500d01860785502c41800ca0740e90500460001e4001c0025181807000620030140003c40c2032040d0300c1c81c0c84035104c0041c0c03501d041c100480605070340103207201c80840d400d00381480110500415513200300d015020300d20040d610807500341d007071032456040d29102d503090109100d81c01848112035505107803120420003450b1394180500521048202075980801e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 304389046 1250 304387796 304387859
    0x10b180907141b1204031a091c12050a020a0f0c03020607200723061806160f050c010e040b0a0605030c12191d10051003020d0f030801 59
    0x81090301030301400c08200c1e00c220103c4010701c0040d0900c005100304561400c0001014002c01200301d19021450714017400b403055501d042509141e0703c03038a0106001c0903022200101030740c00e104182410502ca4640803d000f01d0600b00381140107900500c0100740441c10104900014611420440b9600354259000b04842c2d220300d5070a6448285000a880c111035415061100645007005448010302103082e8800740307101e040105003071a000c85d2404510034681004000700b680410128080b10801c1102c0d21544c54444445040c90f10210050041c24140401518020720101282907039401800ba00c0318801070044074104000c4031640c07029541d00c4503010304203020051048015583c0552840c0c42107160032140100301003500800c80303085030f071a0594401c4401e1030006000d20340c1c1c070100a0780b40c0844044042165030312010f1403e21943d245503180006550340d10809003030b100664000e0114611201d103801e00300484400c0030002c0c1c021840c202e00000c0c540c0614071422500081255240ca030b80e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 304390296 1250 304389046 304389077
    0x7060b010c1502031b22080c0d080a111b0316050d060c021e0c0307050105030714090a0905010806041a060a1e03060c0c1202011103040305130b03010b180907 69
    0x13500044c0094801c01072840a51107a18003c01c01000746281a0385561011303030501d13544d0341003401d154115400c59004040102c07034680b02c03070a0138070815600c030351821344981760400c0031101c40311003100f24100384c4200101e212882d15500c012500c400c0068060320754036040b0500350136400d5498072500c2e410101c4c0007021408500958030800f6403034a52301c1038400e081c4201c42205911180ca04401c4000d41044456502d1850f040014400416003030070f140c0d04520701000050700c9010350800700755000d80d0018202c245a0303500001c07540641a114810012940c6445e46c42e556904119812100307000c9410408408120300600c5602c0f40c00000c0400481c3c90600740c180c650b0581c101000007152140010100000c0d5403400f4407092030407103a4440400c0305450922500e001078094261056902d03014504c134025409004483d40b05416043c500d90b02e1242481400c07076851a41e0056174443c102000200344a4901e030010008074181050410102d0402810081340c2c030002d440319004140b000e28400c10700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 304391546 1250 304390296 304390301
    0xe01020f0f03071709030a08011403060402010f02070504020d06061b02030c01140d09050607120501030c120201171f0504050f01061b080307020a12030c0c17090d0807060b010c15 78
    0x2e1610f03c1e00e84a040300c250300404d01001c0540d5200c8280d00042a0b420240b40d220014a00501c0c1e8504652700d60804940401e0300e40c10003500c0a41007105030a550320300b480c000c00090300100780141c011543d90142400201c028440c0780111380020f41448132090311901c00d8500d2400c4e03503400030090171216500c14015100004000c20b41007150000b880329034020fa00521809544501035400b07446240307401c59000f04144d848042c9214141d20340401840800c000304064010784900c0d107804041c81c000d074001651503d8614259803c541200b408100300c201000f0202c2d1022101140c0000c0d0403500c0d0000c000a8078004c9903910000c005020040040714030690318010502181b60141d06035000588841c0d4480e4401c0b40c1400150384800d100e4004c01290709400c410800c4589010408110b0000740108108090100603140e08010300c0d8450038a12200d0440f250302d01c0050010104000301c0c0f511400c03a4104e0384c0180d07810b9250125004855024203030b038003203190380014056089803c44050000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 304392796 1250 304391546 304391551
    0x7140a080c0a020109050114060f120d03050a021b070806010f08060a0203100305070f180e060f040201030b0a03031806050301050a1208040e070c0606080c1003020d0e061303030e01020f0f03 83
    0x211342d03c078408200450400e01c1080075100d100710b0505514500102840403502074003c0c094000d00c2c04c0300002e8801c0201041c0350011070362b41c1c07801048584448028001038010129519001c9d070041d00031005100000600004880c20002070f204142ea0304c02c40c180600c503252041c1125600b0400c00207a85440b0740d4025584802c041406610013616030712114640801c50304030110768000c0030307018000d00401101108509204400c1030002c03290706c02d003007030300d9040280031116003070301d1803001c1170441e0300030780001000c2c0c3e1000e011302038002d940c0c2c2001820b40381d40001c01c00114061500200d151485002141d040c0c80001e41300b884d0107860038106242c6022440803d54941070700f030101040350f014483d0b995001d26034a59908502c04510b081c10b40c1100c01a51181486600c0008244415250040700282c80d1425003801601e400c0c003400c0c0c00e0b0103000c946001d40d00c640207440801c444101407000a640c0c1502a44d410004130002c11011401c03442030203460102c3c0c030001e1044400074003042c801142d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 304394046 1250 304392796 304392817
    0xc0d05060612240a05060d09020103061802120906040c0e09010906020406030b0f03011e1508010204030f03021006060516031107030818012f030f0a02010507140a080c 73
    0x3854142140e8007001c0c1140d0076030b4506988081c0401c400d1460204502d03d41401c101202e0540703201e4030301800a0094401d44c1816031103543c40c2c004c181c1c15a0b0007540585c008084086001241041c00d141c2000203501c41c0f6070210340b2740e44540100d14010000600d880c8103da00c030721204440703800e1103803c2510007001850f80f601d0f176499541150024902c4c0c000342000b0300c4c1c292004600754844404210807651903c2c5440e00070380c5046103841841120365071452554001d100c0010394940c14035020801c04240d078010040315030000400004102c81500c01d103d00a010740d0175030710521250118802034039031900c90b01c2e0014100740070864600a901d070142401c40e104c0e040440560150744001402c01c00c007a1b0003a00c0ba444007142c440e0300c036040025443c80c1c4140c00d10384058815440060a02c42900d1391000c4881841c13a008005410b1004100301e4003000c50000d0310580754110008000c0c0603000c00c4442800090380203055880c4c0c0030f00e0b0419984042800d8a400d00503030380c0c00d1a0f04d402900b24041d940d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 304395296 1250 304394046 304394059
    0x5060310051b040e04031431050405040809012d050f0403120c2901030f060608060a020d0c1106060f03120a02160f0807030803040f0c0801140f0c0d0506 67
    0x14071407101c02e04003c10003031554031901481d41c80d080c10040c01d90400d402d072050b010441009401c7c8140480c81c441e01d01040800c10140404004c0205051004401d40150360418540000d0000340030010000c0d14100b0300990b40e000c91400400355460400c654603410000320000640079481c128080d6010300a0700d6140700c80d0604050b66610f82c2640c643d80c2d2010704009c110341b1045941402444240003548907050380b404005118031140d034000e02c100500c005402c88404c80b860000f0803000c0c1e085030004041301c400310354082c10071507401c0300254821803021054518120794001203500840407090340081403c0640059603c640038410070b01d402c0105240c3c5805100ca45804120401014005281035039000b40a6600c1c80e002000c41c1c01003c4d04121092451f011041110350b00010f8827005481d1b09c0185251a501c42d403410f00d5a10003000001454041b050070045051201503111441003284d56681840350340315600d08480101058030949041c400400460301e2541058000341d800c0303000035020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 304396546 1250 304395296 304395331
    0x70602070605040b04050f0106050d0809031c020304060e0108070f030b150f070203150105060f0a1701031101080a0506061b0c060a0c0302060c13140d02030f0607120506031005 77
    0x100022200700300e504840d02013001c81070000b0300070104000b034101e01d4804020031419040c440024441d0308d0841340102000c0c030014a00c2c406072418002d40443c00340c400c2ca4190180002c60300031351250001e0017000d00040c141c01c90084550f10921009004580d59101c0d00b4210701c2a0104401800c0707000a883e1704a1840e0442a1390590154010144020814240c1e03840720135910405003020030030141003c03445030900040c8402d541e010308a45072114002082c03551025036050941d92039081d4010210f074040300d20000001e10100c011603040d880000da9030048207980d5805500c086503000d41d44190080c805110140c101400102c20304248010700c0120380e1080c03050f80001d920303540445100c00010716150080310400d80c04125003034100b60142e8800382031484415441c044140709102d0300036500520510001c050b01c079000301e18481a0082c050b2000810b170944c10640d10030702990502c0020300b00f20601107402c2c482c0e100d41401020001d028044401180c101200501009041d101c0b50b50b0b80c0705031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 304397796 1250 304396546 304396553
    0x7080c070f030e04110f0301060503041a0f060424051003062303010b010519030c030e10090b06062b0b0a030b01060306060512180c10020f011a03030f07060207 70
    0x2403040c0d07464801e0740c400c500b0220b110700f0f0000f510050240c44400d4041070115542400150050764103682d403914185489903a02c0c18183c0c0c0d420102100004280108402c4c05440810746010718429030041e1810300801070340d60480c640041d42201008010540c0c0a0709000c2c618050724134a580040d24940462260707228026030f038039001c82c1c0008001106403800950403500302070082400101090a0860130f08510f403680c4511120141180b804050782c032081c0d0701c1040d000e64415000f180c0b00c4400c9510341c410b8101008010105050183c402e1490140002c0740c505e0a0001c0319580780c00c042c090540e0742c0350580c0715489100c50302d2107404415118001d48440e5100c01303d2000065004d080540300d994034055019007101e0305900071000704034003008070f040380704071300783c4166007128000700c0340c410079a00c695403603051104803084d441d4020b00070951190210307800140f042400008030020840c51400e0742d411080780a8040078103405070000d001080584200784054000d16018100252074001c9540d1b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 304399046 1250 304397796 304397813
    0x903021e0415140307080a021003020706060e0112020915030a06020c0f060415050109050f01140112020307031406030706081909080a030912030605060306040b01120e0703052407080c07 81
    0x20820f02c20000001080c062620341004050002c2c0070f820040c196415030b07034000c2220080070740c0040081c503400141020400000b940107000400b00d82c18445669610f4078034103600d103028090240c6c820031140000c900c5902d40c11440c1810800000d000f800d610045a039144040d4005188248450068102070b0b4880c02003072003c01c0c03042c0d2080400c81290840c0c580081c040b200181c010300c140614110800012202c0d9400c1641540c9091404010b41c0500030012207040e800f20040803013641c008014049419010340054a442000021801080e60344006043c1e8840ea284641030000744035070042070018140036002e0301070f11400301c1c0210b44414241c8039a00150f110700112800255130713994060500c042d01445a003985544c0c902840a54500270000d560f03400040d00c1c1c10711480d9203d8080c2c2d15607010700c0c034004441105038814048140341422068840e111403000350307100e006000344e03c3d4201c0b0407581c0044244415502000d074036110200122283c401c010100151242c0400c2101d02068000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 304400296 1250 304399046 304399049
    0x1707030501141602010b13020903011506090906050114070803220b1e071e1b05060615210709030209090609010e010207020609090a1107120f0903021e0415 68
    0x98082c100281051000600307078003c1d1004400459241c0007403a2225612080900d1400b0445d000140e191840030000900400341c2084801841c440075a000036032981000341e410407940d4503041044400d0b0340310015a401810340c002c1c001c261b070301000306034000303500c100145400c400401403041c001c41d510f61a103149042528800d541d050070340410003106407040c041c0d00d1240e0f10754000380c044600740b070940900100c08801c6085240d140500201c45040d200f03d00c8503085d0302c81e85481d840c1e8425035045c115128001620030707078060400070030038016413081c41302101c9845144000fa2008200414a034048075100a005a810403091311000000350366841d10f070b44d00911481020b0150790500c4080c1d282118042c8002c054182d006000e034002681e50642a540d11200941e02c0805a656260105006012003d4040500030000c110841844038015454600007101d4032044521944400300742c514050a03c0700039800011000c001e1002001e0082030a0566409400825009200e17207640b01a640b19 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 304401546 1250 304400296 304400321
    0x501060806181e0d110c0303131505070b040609050c0409080a0e030f07090b04021e03040c06170106030b0427020f0405041106071502040303080109150f1707030501 72
    0x12401d28a19802092041260f001c549094a20040c0340001036140c0340c0d10468007030401d115a8800001c800c080c203000d101c54031440101620764032040c2610350818a07189000751001411240000e2900e1801035040340c038101e42000b0400b0306580c031030b510325000d80752400c0121458016098030903400d85950151a4001d449451165220154080020b052040a450040c4264040110340d8840f21001c201e0b5016a600002e02284410f0340e6000302c0c02a20510b6448620021500200102007215030701a42c081c9118001d103003580c5a4555044503c1c4c43c1e03c00d54201100030f8480100306560290b800000710482c06000400c49001944000620900144441005003100b450380803c43c0761581104444d840200d5081201c1d08142d1615041d06042c07004a50140c140081d2000510082c0901e240c0342000c046015540d941e01e070329000708031b84000e2042c4140c103810190f000701d030702031030034809410746142511609140b441c290390f0700383c940c1c206802c4003d280607007440400491000e0250b03000c070500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 304402796 1250 304401546 304401571
    0x904080705150105091f050a061808010209030d0804050c04050408090a09110d20030c0a0e030c03101107140706170708040b06180a0605030d05070804050d0501060806 73
    0xc0d0801a0a042a42c2450318502c440480140615030b51944180e8000c3d0103411880c043c800c024032800c0d0054510b4104c15441002c00400155295100300c0e44031034811400f58000e040c640e128100f074280d00423200071650581044009200292096181030350040c0100e00302d400c50315a100101c1c088034001d8401344c401e5200000c0b00790072130600c46103910007042c00101c01c020b0410102e406404c0b902071103203075010031625054001031156410304102c2c004440118080d03502d050114131018140d0003526403001040080100d84401d20700403035820316100000c0c001c2c00030760501c42e403408001c051341a02d103001020280b01000219990500044c4201d81030b5005000840c2001c5003c0c14844414405154107280c2000300f102c0103621504181d000355000603085401e8a0303d0b00000c0c21a22148c10b40c0040406440c01c106038408603070406d9003110016019035407042c0ca0031204854500c00da050203403113258100b20803c0142003541c80213449034060000040c0050b03c811205081807410760340c0607a12207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 304404046 1250 304402796 304402807
    0x306070c03033306030605010c03080c07030e100201140f0f04060b150a120501270209061c050403090603111b030c01021c0f09120e0a150216080106051f0905090408 72
    0x5e8140c810032002c0d044c2424040e8816070700340d03002060400c0c02002903241303c0d408260402050f00070340030344282c4540105802d10700d803003860000380280140003c0100c2d40b41c00c81c1c04075104111917500540144d020a0000c01a5030351612080b0281030b0550f082c60f0400401203070210783d25151405400c0b4042c26a440c0d901000303901d0f58140c1a00c1042e00000c0140d41c1c4050340c01103246030299060403c0c0701405c07015031111001d81c0000c40c50301803400121000440100510300c06102e592009205600c20f8540b03080c2c207901e41c5d4007201242c40c012805804901c3c104501080300b404000154003615029044901d4034090070101d03800d98010710021000c140381005c11200c888041e0040b038254480325001080001d01c0c60f15800c04d180100d030b60010034011985a02403541c1c41d2408007902910072510907103c48a800d010096440c0049001034550a44082001c01d1245040c0540c0080b188020f20f440c905107001800c001b940985038800c0c00500144060000b107d0311060b101ea031080e0b029207550340d00d60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 304405296 1250 304404046 304404059
    0xc020f160911030c0702010c050304050d06020703170609070c0c050d0b01061e0c060504030c0204090b06030d050c1c021006060507060c1106010e0c07020a150207050306070c030333 79
    0x461500801e020700350800d100304500c0001070405c0d2004113409103040808003225040940c1144a01c3c1c0000d901700035000c00303410920140f900240703d04c40c03085d82d880180b00c0301c008001000e030703005842480d07204000d440410012481100345403100750280c40b62a41c1d441d500c41c0007901d4100c05880481d46481d015004104243e0007007200da03011038080000036003800341d891000300512961100109041d86d20300104042c18402c4422103240c2d0f038007600130045003516042000314001c089442074400c1c0700d05984001b1f03580c0306009403244c200405004012001c862040098120100750b6544e0171889111194000c3c400c49005880041641e51180c540e20042c42c00c180007030711144400002844000003490700d101070002412070440d40101c0c100380041e11005010002d501c144080650f11400d8404041f640640d00a441420240755408880c1020342d1201455100c81c8100d801e81c000c20030054000000c07034042d400c080c0d420207400d032200441d1108102107803400312016000904071291040c060002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 304406546 1250 304405296 304405301
    0x13020903010207140d1403043017010b04050a05040c030209030d0816030203160305100f06081f060f080a0f0e06040314040b04050f0411040b030f1302130c020f1609 72
    0x1a00038030f03c6c014038201503103020426144400741000b44007150b0341401483c2e2880c0d40c00e03214030004170410848a42d010b0424000e151601b040c5080d40841c2d03a01000040800d0100211400c94601a1080344d040c0c0c40c0000b0440100160302c06002410340822550740d896405004201c1c04540c19254600e071070400a0003c0000010702c810803040c144100140b0510f1020300d140c035090440c0302c2c5004140745d640e1241d504a11a21940701880d51344a07100c011039015007094105204041e6080320360f00c4c688020100003c501c50fa440b480d40444d008411565000b88203198941e031040380c0e41c001040c000291400030b000c446440c0300c1008607070000d0781071008040cbd03c003ca4175006e0303941501c0641882d050600100c2c440c45a4402d151007015225841c0000361501d4008019240c0c0701d850311506c9507501c9003800400e40c0116030342e4088410450004005130090750080780d02c1c58000e402c54080d0660946544c0060080c4544101544100c00c0030700329052040110361900c490480c4034a440c5441c0c1700d000000e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 304407796 1250 304406546 304406563
    0x30c06070f03141c0e070b0408010e0c1008040308100810020301030201031406030c060904150f08070b12010b0d09062904141303050c0111090a06080709051302090301020714 76
    0x6010130803071012807082141c0060b21440b83c206001840b1400604174070714202d030ba40c0c000000940f0100d000121a0010f50005100840040c2540c0303190b84540100f00320741111020b00001318920401060109100e103030202d50002103541078040881d11421064a00001c40310900b45440d0004014002c41d43e143c002d0900050034010b040340e05042187c00a0317110b07410395214a000d0000810307000060381d0b4a0300054010914100c2d5441031a899454a100710079150040c0b450f140314107100014a02c216034103e402100540209643e643d00344501da04095000802c4440025203804500c0f020a0311846a80300c0044c01c0c00302c3d00b9016941c04070881010807404100c078800e41c0f400c0c40c140080c40c8107410f0694407110068001020080c9450160f4460090002c02101c1d0761810580b40300c0152072100a10201c2c400f140d0035848645d58070030894401c0f20403582c03040003880c00d6800300a20f040c620b80380c10340d03480140f00150400b41120040303070072604003800aa40c40c003620130407a03580180a004911 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 304409046 1250 304407796 304407827
    0x8040b040906231203070b100f0e010b2704020307030b0901150519020703050616030609050c070f0215070303020913020a0219021903080a0206070e010c0f02030c06070f03 75
    0x10b43c21039551840ba480c1c200340001a0064000d8140032031040000d1048488a0703034004407155107400c009000441840043c0035031006941100c1d004510b05160780c003518100c801014003a442e003851074001c1d19441602810b40920054042090340702c90369240055882180d465800240d15154641000740244040e44642040030316140c0b0003001e41d07808800c0b074540548603c000e11046840300380884c1740c001664006000b86c02420103000070a14510000410203425075410300c0002d40b0b0310300c1c8004450307081d1a040441d00c4100300c0340f00002c507030001843c1010300041c500e10310049070b060742c8030080c0c2c0001c004400007a030005031282d807803620a11140020202d01c0b0114107010f05544083c0d0b5a4070056846000d079400300303c40800315500e818055800c54580040e10340302640d00d14080b8001e801c14103003d400b60140e00c3c00140450710548540207a10380581d18072013205c540703484020101060311010398160142410703035401c41d1211002441050300c20300140307854030b0181c20010400604100c100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 304410296 1250 304409046 304409069
    0x1401060302090604060305100e090609010c020c0a060e011e0c05010f05061507080702150a121506050a0201020903060c04080d020307150203070309060906050604240317040308040b040906 82
    0x10440d845480680d01a17400f40d00700001c860716002000c6100c2121544480c08503050701003009402200496000d00400d804002030041c01c511050590701c0703079034480c0310710b030091486d4008000c0305120304170780300d40c0d0801814807805400c81540d82e02406400b000150307000c41c0440461000f00842485181144510342c123040001b0700f0a50001075841c03244d072102043c4040c001c6200014044084c088614455009040742c024110303081000b101900201c2080001c12001c15141130600c42a020b4016004240c020100e90380f418a0401d50749500108000001c5660a0000d07852940301080b80500804845911689075440c009142d40340c050071013401411074209209900024800100b4007000c102c25240240c0c07030b0b54035054101d00030050000d01030b0805080c640010240b000355070220740102829281407003c0d10500075003034034484040441080c81038503184c0800216400c540142200c001080c0e00d103281540d203840d10451900705400a610002c00003904000400481c8110b000410491441 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 304411546 1250 304410296 304410307
    0x15040b01051216090b071a07050d02040609030204060801021e030a0605030714040c0f08010b210a1b0212070b040606050603010914060111030711060d0612050c030118030f1b061401060302 82
    0x8140e21100c1d40400300c0c0c0d02003884004070308d00e2400f4100342d40b04a10300c403504544490b030300c4d14020f1848042c0d100603806546020000300e8901da060088445104011154001d00120740d40c1c04101e40d0b00c01404002c01c40d54810010500340d5040c0980030083c080300701c885618544400c04c02c030454491014840511080c0c00c400c01d031480d00029001e044400350f10320103494820411a412506d100b00e0810100403210004004401c00550300c02d0000c9038608440d040c0c071000c50001aa6a00d80c1610b241c01551014040080002d510202c0158001c1c441c5601007921030395803002c5202a0401c3c3c0050a03156280c29201d081c4c01c0007410a95070101d000d2804600b0354908211309500c0b449103820141542c40001305140e5542c403071408a450b00b8001d00c030100030340307641c941c1c00000d602d440c800111f40c50700640140079118503050081c8003462541490305c00c10f40b2080e540a0710b80c80741810615003030040700c001544035898519050641c050140d2404110240413501c54000e0001c141c01001c240340c814400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 304412796 1250 304411546 304411553
    0x7091104050904120909021c1a060702091914150d0c0e07110d0f1e14070c051305180a1515080304090204030c0e15040b01051216090b07 60
    0x400700c3e041a00b1002940e51600d40301c0040741c54071750b03580201054a00008000c800300308101001410300c8010841004001250100030b091500d0071b100c4a075002c1c0040c4aa2409441d00c02c0b010340e0000013004090688907803203040d6006580c1005000401100580100b084c1000b42030410005130f84121420b004605560340c030741c145140349000740c80000040d0400114002e00035004540e1381c010080c101d40e814941014002c1c10200c0084c5d1040014200240561003500e0002d1600d0340484180c035213407021040403656031900c1d0070003101542c00901e200c0d0002030a03214502d0044440444082c00314003840c1980100d04841741800034917080d80e00c411082000308003101e4054180260801c0302040e00140081c2c3c100d10580340e900581014040060009a540642d50007401101d1007040c944903459580c8603c02c450301d400300c90402c54041101c510348030524241d40b083e844004141000713824800150540b5114060840d0044c0030840c140540e5650b66410101060051220b84c5206117001515a0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 304414046 1250 304412796 304412809
    0x140604030f0221070503100e0c010509010c0f0b0a180b0619030212030d05090304030305040513060914090c03030f0d0905030708030403090e011505091009050a03050709110405 77
    0xc405040150300507816021035442d803060840c000703441140e4200d40441000700039260039403442400c1c82441800b1b1603030074802540c020500084448005070820301c105000640d0503500120303034241040043c450190000c0c0d43d00d231250094030300460711080c40b40740c241d030200c08a40c100c6030300704a40203d07110650005082c003008694005410740ea590a0148811285410902c04d40c10003588404c200012144015001019008060074020184002e0311002d10907600da104074000500065410401406242040b91030182042c0e10103e001440b42c0d9110400f504642100100c40e101e4800641400121b0b11b0400c100180044220090352074000c40b018184094410760040c0302c403403526040014144041401520081500082000ea50f86424613004200b030b101d9000780703800c550107400040b8003030940d4007422803070250a840340c5150190381c404000103a46810b803650200180c030800400d40d91100c039480030007148a0340c02440c201313060245d040d0550703c0b10718083c0f01d2010140710030445950b65a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 304415296 1250 304414046 304414049
    0x1218070e131515140301150e160e091801140709050d0206090411070308070c080a030e070306061401030f020705030421060204030f0b10030506010519030b0108010b0901140604 77
    0x1d0a03400315032440040010303000b48105490914145640010a4102c513100501003020031402001200404c945041a2426600450550943c520009081618402502d900900e81414034100f4400c1c0d0100042c000a012554443d565060003428002c0300000d01484800d003c0c0894004d05a1400110042c812000751013007501c50644c01102e8004e64039508100e030581c04001d80f06004000d00c1c1c0144029035400f001007200041c40705000103081e02c1c030444840c00d4a0790721030419450201d42c010304401801100c0c80c0d06000d40513000c4000700244071807069400407c03108800c001e10f002448000b42c00c0f500c0c0c0087d42c614950040104000040e40441110251420000c003034115150340b45610780c8017454070000600fa01e200007008414043d22018034594188161110344a555501260750801d041c54800281a584150014009807902d0200204000f0b04500e0081c10a40d40342c0319030302d0115003a886200c07165500c80c444142c80c20417090390780c0549040c00c2028480318403107010480c1441903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 304416546 1250 304415296 304415303
    0x31f0f0b0907031805030f040e0114150903390a0311010c0f0803040b060a14030a03030c0c060911041b020307061a030303181c0c020907051218070e13 66
    0x2a80180003443c404d54038020076240c0c20204803502c3d402c441b140491580d201e802100b901e224010000100138114241c9403450356005442c488140210340f40241c0709411149606515002c2c001c0e088072840f0600604d1031a04114040b20020140e9036444180c40d154021946401202d015405202103070005100c1604400b003840e20424035030007800d04072110301031400010b044500000900042c0020340b401c0074000c5000700d52844049585a44180f01e400102841b02c6d05030f00446500d0001c40e000358450740c400d0140e400d10030342c822010398802044401d44807040b03640043c480321811003804c05200d650030800c0041008101c4a0401202960782c0c0106107008102c2038a0316680c0401200c240305128841c0c4010f01125100e042840d09045c00581044007100e0742d101d00307074515410f4030002030082600540781d258008241125020310400c00750050420302400410485803107000a28135003e84640d200d00780910542c030511503858180b00450f840101075410140c180050f11000740501607a0039031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 304417796 1250 304416546 304416551
    0x604060b0f2101120b0106171303050426010c05042709120e0102150c04030308060d02030d170f040b0a020a0e04021c1d0c090405010605031f0f0b090703 67
    0x81ca84004015000700b01c070100c0050122000080e00c0909814800e04d903a102da207900d06681c0e04d429049039a0311b4050140390800c4203402c086011280940303000c49906001785002450661188088801501441c1e03581031824079071020460b1040003031003882131000b071170302d84146494a0401003107800e100e18a88000d05c10040d0006d024141001d034007840085078030420301000c40c00b154030083c148030f201030440b9015018500800e40c0c110b0b001706020b4411084414202c1c101800d6032400c55a1040040059070044541c80c81c41000d0b035004c200d41112902180e07140c0c0051300d10360b1080407240c20042c1170402c0c140300d207005020002d817448441da07500164015005031101030740c0340202c0d4419903807651250481d1001481040c8074a8082d81c012481d0400c0d071f801d0065100449510b18101201d811000082c2c120341c00030709081c90f14528a503002400740d40041503058441c070000c1c0c14207041c0e003011111000b20102c61b03048455203000b01c40e001e00d81c0b0030003040404800e10205d01003010090800c0201907 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 304419046 1250 304417796 304417807
    0x123030d0e0613050a06030507120504020a060e061e0403052a0904080702090c0c16140907050d141803030702120a0504030c0b18061303150617150604060b0f 69
    0x808000031140280001070104840c00d1ba21500900104000c0c0d804000140d0303003201c080070b100418015036006640c05426820141d181540441b0410000800039603c0141001008a911481e089210f0000c080f2014075a442d8074501c0c00e14a080744d030b202c4481101007408001c03c94140d120501401c0041d00380e4442e06d240c0c1c0ea070b1414903020f10483c50000d5200d007850041c4030316104480050141c0c20039a004560060700341d1100f6140311003043c407900284088052006205040c511b050507000050b45c20124100400c2d40707481016600208220711101240008014052519280d800d602c08801c4001d54a141010300009444010f032000a118004001400155240c882c0702260010750304802800d10041d03c6800c0881c440c5d0000c100307005a1060300280d4401c3c0c2c40c102040750000807551115a405034555955040034550310103044502c2540c480002441d22060f044a0a19442210250100d03c0448082d01c03010b2034040c1209000e9881c0810500c121030b0301ca000c032070407070300c207810441c3d10341 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 304420296 1250 304419046 304419067
    0x4181707061803080a0e073507032418141c021f0e07090c02030f160605090616030513060c050c010c050310180b06030123030d0e06 58
    0x1e180c2c070041280c2a6001a920a00b41540503400700c0c01090500c406111a0788034580040d40c92845004405444603501c010030907c890082c440c8402d580d60002c50303500b034080d01d90001d0600e8640d61040c2c404d440340ca03e0701d140d010180710542001d00705443c0708101210f19404501e0440c955040d0003010010078074090180c2000030083d200301080b500400c23000e2004d02c4680207440c0c06554641c01c0c60701000080c0728a43c85103500031541307400b50040040940c980307880300e42c80140000300c0301d107829030204111a003414900ad000800502d04031001c4010780301110314145040782c000400c00407260300302d0814001c0144942084c980107000a140c041000d440d00302c0c071312032180106180105954034000c0d604c5070803074010024142250b54007008100c8030071403c00642d100d1000319a100c2400b100f1007001c1c00718080c0d60b4070055400c42d0000000600c4600603020914a904c2a048111240d14900e1009034040c10600300c08100c20b400e5020340b04a01840c0c5c4050b00c04190b0041c000d11550000c101c00400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 304421546 1250 304420296 304420301
    0x206070c110a0314010603021c080703081f090501080c0d0804060c06021c05041208040c15030914060a060f050a03081c021c050604050402010e2211090418170706 71
    0x43c50300450070a20401c040d418050080c0441d03c8224003031109010481d8410320300703c61341400f05420030035030380c0b402841d69421540b1b0714008141130700141d59006000c081d5002184480060884110009510350405540c3c92030200b0315024503100b114ac11000b10002407040e01620100c46850038088861030a52030030360007034050b070a00e6141c8452800e803003098108141e00528003443c09000703900d5040584420031201141d003100c0140000030040c200f00308005915900500c1c43d9568a000500e07519150344841018420007007607034542e070000040c0001000e15202e4000281102e2044c001814540b0b0082800300300e851001822040c0080350f1a05010303186401802c0d240d46680085558001088004540c03c650240848210303140c40002001e80c24180310fa80d0042d0340585039100c3c61040e0000f003000c1c03c44a240211980004200f219581c20894040c081d03d42c62441c880a880b4102c12080c0022903a0041d13120703d008601d01141c00204440520f064610707107092007080e640b0701c100d0400102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 304422796 1250 304421546 304421549
    0x5091603030302090f0316140108090304120f0519050d0504061d03010e060406050a0b06090f2b050705040e1501060309170a050c07170d0c020f090f07020d0206070c110a 74
    0x42600424800c7c4007469031501000094800b0280801880b400c490011280d150040320b00d51600c0c0c3c0308100038000740104aa0301c200c424443d0301034221680320b50342c6042c20300403081214030400d0b40014500040250502c6a1080400549002810030b03142000c024008498060200e46550382c2c1404818581c50070340040b00340b00c071a1b0f8100e8005040c18680714005140850f000305010385040b100da4031901c0e00808942c0300725801000100800a41c00400111ba000b5a513841202d4542e400c001c000d003881c0c10b543c1c00030680140007034406c55161209020503030311040031500d500c0d04803094140b10414604016030650702c16280028036003442d840e1a4640c01480d00e442c62800c1c40c081899201d440e44640240f5020b05401e05407000c00e940c40c0e00da040e100000d10613092540d0421030713248009030700c604080c0c0c0850707000501030b128118201005c691640010f85114003041c02040400c040c06d501040080701d201d1040c802001c0c50314042400038010180014020a9542107505a040943c1c58054240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 304424046 1250 304422796 304422799
    0xc090c04030209241f052d0a02061008060711071e050f010c02010212070204110a0503040b13030e041a1509030706091a0901050415050d05091603030302090f 69
    0x24650a04501e40f40e0301c4202103409640b0b204a10200000310b04003840600280c00418074085c42181002c1c100380e415800a00c201d40705070b11050a0034018401c02c0c070400314200d1040928564409241500a0416400400407a2041e40c10103040100100c005080c55001030180380500c0303180c102901017400c0c01e0b07056000c40c0480d8800f180d12400c07403c034001c41400319070080740c0c0c0c0210080d0398030054130803083c07054010707000da00202030b0356104017140c00c02000c503644020f0000a00b00b4040034008004c2e0800d1083d480060000b10402080144c800c40c02c0d500200340103071020845c811560014800c00e40d2182c4c03039000700e8030381032501c480e034070200c410647c0c1c00c10080c44010b840707440d00811b810355002980024880e100d800c0000400d039008032024001e5481e69500403070040c03083c04c101c0312203a10a50041d41040010000024912521441c09400003040d035a2196100c40803401c107130694002800c0c90007940c120601140c40c0c0d0804030307030341c0d01201e41c903050140c0c4039005100001d4400301e07001c1689 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 304425296 1250 304424046 304424059
    0x6120106030501050f1305061513060306060608090f060403051c1406031e0703020d03091a040914011202040e010e070303051b030408031c0605040204090e0607020606030c090c040302 80
    0x110812506411151281412518051301691490303003403001c4401b651009000c1c1c0e046000858140e80b00000f1020440d000544138102540080070b07010b045030410752094135250b5541c0c0c0d003031250340da21001d01508a100400100602c00b85424800d484030b0016000031b00384040012039060304030450040760031105164604200c0e00850701c050040300f010868200f44a405207044500d800411000000840c2d10000000e1845078255030a1021907050100d09405004810304000380c0503485002055a00f102c2c41903035602c50740f40031840d400b695400540070f540d0094600040c400f0507540200303e104d0680480d0003003640003001d1246401030401e8840044580214a0040145600308009222850598132114124461444600c0c0c403401103016110194004010941041c1900024003a80c803180302800504541e5403000103081347c2c481c1d405482d103542c03200c110564180d002d022050f805580d07400540968075068000030744440c24031860034450028400400c400040c14003c0e24061503016045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 304426546 1250 304425296 304425299
    0x5030a02060a1803170d050a02040609030f170325020d0e0103021b031b190203030a0f030f0513030206070e01140d11070605040b010b0a0504170319110709060f060806120106 76
    0x285145500040e20320100078100008115420001e2007262b048030002e542e2846024219a59105114584072040d207035074012400002074082c00f0070055001d012242c0720742c04542e10540d440000e247c00301e030040c811343d0402030341d08025982040d1107000900f02440e00603a582c100400360701509070b004507030000b984804284000d171200c03d4914607044070780010466444840540340101c0f080301c0c080c40290181c10921041014038011002d80351880314030309000c141000c640c078003c011038104560b003041031000550004149901401215003007111071034840140101c0d1000602070107000301c041080e1030000030351b8100c1e10500c3e038044407541c1c2040ca030069450325281880c0c4c0107400c05480565407610301000020b0002007071070807076602c500162280c609052820080d0040b00307091410100940c00100071400c0c0c10924045400708603e00b60b1566501400214101440d29180350072a00b00385140036000e0046089807110034089441510700403001c0c1d076806002c6039244107050120a215070900382d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 304427796 1250 304426546 304426583
    0x30510121a09010b01170114040213150f030629130306060b030f070207030b0a020a09051c0303061202060904020f0702090c030906060409020d06051b0d0605030705030a02060a1803 79
    0x4080d40e111006d070b907281d409464007016002072003003c1c8514954a0004030401c0960f0825070098408100c4040c0c0c0c009d1003507901d03104861129201020784000510400f208254242c03d0b10624014015440081c014a21b8080c1c0c01c0b218650310380d985868642c1301082c0c00c2100c00000078850007a6510460500c000d80c2e8403e1101015001070f41d131100100880c0000450148c40041c241084a4201e0101c0e1080d44a80300c55000a6010565500c10080d44a10100e600d86544c0d1402e00628040701e890300c030200c000e041c01070454109412403100c01c40b080d131600340560340d49015107510000c01c03100143c0c1d0b46c400c442203080a20034240000d40200072a82044a003424050186204e40a0031055070304079922141008110b03040d08900a60014441c1100300200b5420791059502241e40050500761801c11681c000243c2c0200444c6120745494260a200d40e003014409070b0010101640249000c1c2c2d41540003134800d0203034001c0082081440001c50030300d942001071481c0110340004031a40c02c003c0080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 304429046 1250 304427796 304427801
    0x804090204061d06030910090515090606100206150603270a0b0a02040513020a02100510061706060316030612081812301306020706030510121a0901 65
    0xb010090380c220f09520b403200303041240880b032191200c800a001c840b5442c5400c00014441d0750310031b81d9607125414000e252052500c0344180119480c0000307102c40c1c6421000c00c407460102c4614107003107410950921a140c0781e000054120401c0403582581c40b41d07501c608a860102161000c810700007140100c4030101003003ca9440c1d40c0c0c1d80038440303007100b035a690003030f02c000d0f441544a01d0344c005203043d501c02e035180c50ba94040d0000c4251403040e2004200780450b0b000a40b10b054800a801e0126420200280c03500003507420800015034100380f045141c800c0c001416400700505408403076003050310703a04080d8829808040903049000c8242c42d04074190615002c1c94228090041c8844011040b0340b00e00d10700060150004030100700245800b4045030390908009100746101c40d0086241c805500f0521a0f02d0050011200c4c220340d603103010740c030303128000b45409820350000060500c0d040521025880110f450340a6800400d1000d0b00b422a510300701000d904540b22811807800f01d082801031991064 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 304430296 1250 304429046 304429067
    0x1023100e0f0d12230405040903020c03060103110a060201050c0f0c1608061e04020f240d05070306050607120e061b0615010e010c022b030f0219020d020d080409020406 73
    0x41d618000141900f10703200c200d2034141135010b070030100280010011454a42c0004000d1842031054854001001e00403d181500c203810458cc09142d6144500741c500701800b04000400707140c40240014100381100e40820320441c1d40905502000182260340c0040400103211400000003200040950390a011a10340300150f42d04044d41c1040208101c064124406245c00703503400414050740038a800d07041101840d20034502c5442889a2944000120b058102801e0089414000030402d40ba081200030126040d40d08845d100b2041401303440701150381020300507800d81c0c5909000100d0301c030800c00140035010321003a59161407d1152011440c0b580030410320f014524203004c020710364010400640b14400200329460010328200c42000162a101000031410610b80070f8030a138410440700c030202c0c0030b800100140c0104410220f600c00c840c0c4d0400418841000c000702c074181c0c4c04407588c0010202d803003140c406841140c480109809100f55103084030002c0c4908201159240d07541c85000e0481c000c1d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 304431546 1250 304430296 304430333
    0x30c0d030606300b030307080c0f1216060209060c0c010207080f0d2a050610060903020f060a030e0303011211030303070e0111070e1023100e0f0d 64
    0x4041c0d0008542d401012490101c21030340e810030301118800480c07210b403a01c50351440380d6500c1e100c800c8101603443c144001c098041c051500d050380d801d21201054900004801e01000381d42c090b4039a85030800240702034034036a9840c005441e5140e42c090804a000c0e0140300304482e400440091800d032180f0f000188180185400c0e000e4540c0b00e542c030589141c0b81e041103807036528960044460b06201900c20340c0c0400700c2200c00701084c00c12988100ca0900b041111031800c450075884141802400d80404080c40010541c0c0c0c580f4800382419540490304240740f01ba490703400f03410041240a84036002e50000c0340c0c055558022607032a503954103103003107001208040684450306120100c0c0000e04000c8202c81c4500720544402054040358401100c801d82e00c1001190140124480410170340302800c030306405001404210134445080800101030043c00c140020441c4900b105810140e0b200c940b010b403024099810040c0016180c9000320b82414141c0062950000c401d04000b8100504e042c2c900d04003140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 304432796 1250 304431546 304431551
    0xf0c010b031b060a0c0f03090620030904050720070510031401210c080d08180a06020a0c0501022a2406010c15050103020f06070305030114060c030c0d03 67
    0x40c0c0010701d0b4655076403a82d181d903180c180003001c40e40d508083c4002c01c040603a515203840f40600d1502da11841d001c0380c882c100c00085001c4401c00c0740759803001030110003d1042c0e010f40004180c18000c00e64a01c2001c0b2070600845d100c10000300c0d203038003a001c0f01403100b081000e90368a960b0745070705036904e89046005141c4140f000c4101c01d094107102c0c4c41102c001840c51038541d070460f4202420245048107900c505681c0e0800d03c030045001a2041405100401c0102c006152400d1014006440070900a1000c50000140c0c1c0180000000000e10b03030350001c0c0c010000694032003030788404541c8180303044000b6110b90300000301312100081c0c080420050600030510303074000e18840c04446446500381080321000c4c10307440030440340b400c048084072a000f003414140400240740030340e51400141010b02440d442c042c0e882004005500f02201203150020f801c4441170303c0c03d0719a94010308075000c180540030290540c550b60000b07685964044401103450340040742d840318400052607956203440050366000a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 304434046 1250 304432796 304432811
    0x3070f091406120a0b1801030606060c0f060f18050a05150f040b060303090d03030b030c0619050d06120b04060b0603041e060f050c070c0b1204140f030f0c01 69
    0x2915480340328001e84000b00600d291000c540740c1480082c0000d01110480350b92101c3e840350560300c3c0c01845180b6100409625055032440c02d058040b5081c40d4026800c2c00511900bc80c00100c1e00301c010000c103944003000082403214101960020408004524046401448090203002002482e00941c40c490f804540b001d83d4950300880c0310f0718060342d10700a410107541c08200080c101c400b034aa4082c402804890401c8501c40003d2800311100c6002d402007651040e007545242002d028040105d03906440c058a01203000b0200c480e00b1121038103100c10031002007580303c40d10302c1300d811100050541459440c0f001c10309082603981c4400941c0c08a50b007910300080c182340c900b4881c05907445260052040020380d00149810644454a11821294560354504103140003845205107802150031030b20b483e444148505c0e2810204503250070aa01c42002401451105491043c14540c032035803050000c840c859410090340c2c9000807070094500d1a000200f44090384401c80c202030700700d40700e0f54070003030100c403 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 304435296 1250 304434046 304434059
    0x302070506150102030405130209090103062708041e0306240f050108040206031801050403021f090203070b07080417030a14030f28020705010c0905030607120f1103070f09 75
    0x80404030b8203a405070304103000c01c1140389841005c0b40c6050f000d0050240c580180c210000b801300d04240c0040321401d6a8807282d00e8210020401c0c0c0d4100c2201c8561051403d00a843c1e8203c640150700c1000405100a00491070001a24614100070355114805024070f13000d0140968500d5100300e24400480040340d0000761074042e05500d40c0881d00180c48114503034646400b0b212040c3d00080880300d234844100221500072209104851240380242d0107801090060840112404440001d40194a00300681c40c009a82e01103054030446010810556481c682450170103814010359100d04203040d12520a001b10b580c002c4003d185c80f64199595201d013019620809881d03010980700e2580009084000444c0b20040c9003d01200904020f03040c20754001050070b41c01039900059088480d80d44840701c24444607000520b01c5c01405040f00a80024030b4600c000518030707100f40d464000f00917200c100240d8140a603911012a04540107411942e901e0311050260021064041c0d030030004419a1000540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 304436546 1250 304435296 304435321
    0x103050c16060b010c050a03020d03051b041401020c06130519210c09180b0a05060105070609020609211b01051c020c01021201030507060305040317180d0302070506 72
    0x81c840c080380368220816068075100000c1c000080080e05001060b04c040d40494010880e46180c0742c400e03402000c2292000400505a5a016005450006c0801d20741402d40350720360280d030140c0b4468800903c2124200004030700c0c00b0010781e11707103400a800081500c160148068034406440040e1090b0280c540706820390011410b45101e2002d0035240c0c182c900003101c00310180801c050380640fa501000b641c50b00b091008482d0303150000c41010045402c0c0204002c130648010758000360b91030003000185001c400103440c078400e00700c00500f410341d00d8031580115650407040d14580702c0d0141142c809000c03448540c0c0c1322582d8010315880d0500c83c00500000c10185130004001074501a91503e0030b1202002c421351000704100c0e1841d80143c0c091100a101c81001d101501464400503a402903651441c00c0581c2043c0f40c84d04104109400c007420400825000a46002166013490b0014031a55681000a4012040b6041c83d200e40c000c6071900d00e4150342c1a000b508105000308180c0d03401d5110660a50380 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 304437796 1250 304436546 304436557
    0x912020603060d05070e0106020d020601050301150e250503090f010e070b0d24150203040503150c120103030f030c0c0c0306020307110d030c091415210a0204050103050c 74
    0x500100410005002d428203d4030480c400744202e00b2100c9540e1195a40d02e0b0001d001d8200c42c005902c083c61100c0e00350740c10000c4900500c015402040681c1414210110740031807806000c40c54013180020031070000124400c800d0b82440750b0070b820904841c82100801c16401680c088000c2d2040081a0100003818840c45030b592880034001d02c0c4240c5454204d21181d000703841c51444542c0d8032038954100640c20410340c111003005014072014503080515060030080495070b60400c540c0244024407081c0c8000910310a00340c0c40f0440c038031056654086100360b9206190b0802c0d03030702d000103000004258100c000440030340300a49084c4006114440c003114186203120020307000942154080001c030340740740d0040d5003000007850111070b15540d20031039615052182c800b210009a488581d107a12030760000000b070250039402a14007000040c000020b81c0c0207455000810b804100090199071115900c0045054598450f00c3c0c10042c41c1000701c40000b904244282e07408079040c00f0004104980607403c031039 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 304439046 1250 304437796 304437799
    0x60a0603140106030f020c070e0402100f081308040302060a0305071d0109050d05070e07020a030906030509100b0418060209100809030a0309030c1a0702010c0306080a030c110603010f0303091202 85
    0x91030f0b207058012009042c8504c0350104555082180c5090308000b0320005024000f2846019841c2c10a441440760a40301031074080e04102d100340703840b400c55510219542e0403274080150000000106d06101c0154031460340000d44c018000510f9143e0b2603015000f2910030001c7d92608050072081c248541d010001d482d180ca40060326071901444079150005100840a00442c00c44440301e44070300072100c41200a480440c0560302007030400040540c4518001d01601c40d0349024401414003070003e41d0703540060381070b42484036100c0000708100e4a0350742c414a0800c5446170250411030150400d0002035004d0301c0020700422204021030100c5000304d901a01480301c940066203040f04021084000700900c04c004c40402c0042814480495614004040c1c0290506038a00040c00c007400044e0844000c2c0c002c0034145810010300b040b00020100c0e003420216054101688130743c0041c509000c001e03483e000c402c1d50181c03000c000403900e80100c44060302602d01c41d0312081400c41e107801400c519104c0e4030f40300a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 304440296 1250 304439046 304439081
    0x209010210051009020f12060105160b040f05030307090315021312050a0f0b091c0206011a0409050405030403030219020f1509090c0a02010c0504150f0203130905060a0603 75
    0x1085410796020662001c08048803490301030703c901e1381105a03400421051000b08012410142c0c2c1221840c2d820340005007424481d01c1d180001e850500d0510030320401918821100700090180a1f420f4603c00840d5071000c02e42e03589260940c00035007a050140801d031030b0707100e03100c01c5014003600501c01c81e11074031040c21805d143c10386040680c800403a140304003180c440c042c01c11410300286e020600c2c000b68912800703c0f01e01e00c1c42e04841d49403400d48440280081c01203e06806040150003089041c1901c4082e002501106c1554002e98824412a4048006945420100414444003102030000d0f04c1c420350994040c003a2440040b000c0d40d401c20006507001021865400c0c0501d00550403520108080008034181514007000600c0060304481c400901d07400041e0760002e06a080c82850b82010389810554101400d180e003844184101a00b00c009000c24080d80c00f490317074000c0003912818940604445c507420780703079500d010241209468060161503800c0c0c022034418049d008051400d410f25269 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304441546 1250 304440296 304440313
    0x908030708190c080d1d1605040e07051207030b09030a020303071223041103070305120703020c030601060c110901150c06230405061501090303181508090f0102090102 73
    0x2103072640d502001c100802c3c07043d421080e400240c1044083d01190500007000521804c03a072011080c80c64043c0301c50581c68002e40c6445000701150103030482900c909a40018410301c0d4405840c2c50f064094000c964840903055440200a80009503034060b00d04c100000103150315600f000780d03a05e0007030600440158000740300145e04507200341c01810354003c0c06080400c030082c032100301507880b05500720000d01e152030710313070800042c40001110b0044510041d0020500c2070718644400313864a0707001158100740c1c20009504400d141c801c114040b070a86d001002c1e11103c1d41d5550780034019000086c1c003103c1300002c42c480040149881a50141251100d0001c01002e04a001c000c0f9940320500e402211915600c2550304c0c5c451031221000e003000044414050714500389810880d02d06240107220009089000900fa40300e40d030302030b210b0030882c1d074141810420340c140424480c040624075041003099155030060b60704a16481003020340516040380c1550358840c0c0800341d05090b88a04401340b4056880801e9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 304442796 1250 304441546 304441567
    0x15010306050a0b22060806011d060703030b030c0411070b060907051614030d14090c011b0606180b120a20010905060a0801060f080f0a240806070908030708 68
    0xc2076100002e40d036190300c42d4910200b2444d4200309070010f20028821804204042d40c1200c3c403d128652100c1100700e1200030074002400340e02c00e648ac02410561103040d19021602c040004d0407100314020f10a011160b14950380a125401c41c10742556001b580c2800700d4118100f0400d01406182c15546071440c000ba94428140482d04094085801a019006200391044180050060780c80840c03404100c01903000703820003c0d900003601480b141c0d00080199012680c100d01101752400d00001040600900d500342440201407691010305c11140001803440080281e905c95002207a0803103e90b0038005120020503940d143c00074009184403504410b282d04405424004080382205140540d919600c0310f000c103590750845243c0e01d01050700d15006004040e00108030461200d19868080c0f15841d04201c5803131149806001070014540d036500d500c902416107000c8071912a29400f00d01e07089550b8416050b590a4222030700343c001051004042103001c404000c9605d036a402140c414204210000b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 304444046 1250 304442796 304442819
    0x1150801090908090a0612060b040510030b030f03030705070b090a030807051e0c010510080a0c03021318120f02150103020f010c0c0e010e0a0b0303120604020d090b15010306050a 78
    0x10700c1540c5103070080c071030108680c1d03e0f20b03089406000d4070b1f030f901c500c541000c10100c010703201c2c187c01003140504c0071307c014040c640718000200801030840c0360100d040ca0114001c6818400344821543d420f000000800880b1134202c0d0060054503c00c0304100b5150b81d81c141c0040e119840c0100003070020b005600450082da20035400307081c41003841c0041c0c40c01c03040001e20401d03040e0b01054031544030b41d4440741001442c040d010b24810003024828094011003505c4d59500910f65424040203104540500640c1e2800c0303402d6124803894480e600c0000c40d1403d1504145851003580404080040d0340031100c05d00481c8040352581c21100d4049a482440c1d08540c00c0044d1050985102410095040b01c0c02002c9901850900002c0940c100f00c1c6031154140040410303000030003032002403000e04204c00542c0c0da840010443d81c000704408070b041101c1d01c42c100010702a224224440c040075052400080500c441e81080c2d0340160410300020300307100200030041d01031700c1d4144501d0341d11218503c1c040001304a4031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 304445296 1250 304444046 304444061
    0x31a0702031c060504230709180c12022208070b0423060a0801080c01170f060a0915050102010f0b0a030206030711070312121521051b090115080109 65
    0x1080880c48130340b00c1010600b1907801241c0000c2c1481c20000c0650005102c1d05500c0e0415054680400d445080006855600a407400640d050968514031040018401d10010680000107502036540d212018440c0c04400e0510f80d80d05100c0c68201d02c009003040000074080120b0b0540300410341072034504562002008049540001107013510540c2860f19030b901d2004180d480290780392080c0e903505142c1190318000e42003140c80e0500801900d0840d020b00f202c0c414992046203000000c101e6581c240100707221038260350021440d00d080007505082c00b0031040d088001e9510070790017009442c5414100500382c8212611094000d50a8101800541010360003143d00c40c0f92400c02041c54070740070001c00c0c07410445a00550745014070003c1e00e030700103512140203070781e1000f00e035018840130701ca4989204014036248106000300240c550804040c1c60a9982d0b100700c540c12a00f52064401c0280030b5246e00560881c3e441e03c6070701c1110003c11082c068502c881070307005055407000c0f0503a09008000c401030890 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 304446546 1250 304445296 304445347
    0x207060513050d060e060114090a2703050414091605071a090a0606051207140d020303030f060907021207080a0e060304060b010f050424030207050d09031a070203 71
    0xc40008a82e03511103e40e41d8035000d200d89400280a541d501c2c000d4140401a0885800358440321a40707480340c0e466099480d04103d0581c1c00103204840c2140a00700e610f007201921305038640d50b4054900345500300d40500122480c96020f40c21034400f400400c40395500858801454004000e495907210381302700301030b0074440e200314946a1104c0814460041d00070044071515400d0b8007280d000d1082003a5400340718014507042c0d0b0307001d80b0070340301001058031048076000c0c0300c0d540e0000c0307110705e4041ea403001c08203060160050207603903403070403c003d030284102403c8a119003d8448000803410706072000030481c508010200700b035410588942d882e0040c0b607120301c0b402006c11001000d02c0c00103545520045001c0d510907440028031040705030014003100640750094051000c10b02040000281040c079210004d4584003041e84003040052056000380a60b6001500d10311901c0c03642d81d03c654004180e5019a40152550b07003c120ba0444000c900010072981403005801c180100900210309111421500e100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 304447796 1250 304446546 304446577
    0x90f0304090504051204080f1203070c060b040605040207030e09060105030405150c0f0c03071a130f020d0602130f0504060f06080402040902031f060504090809090c04080604081c0c02070605 83
    0x80115044c005c079001600800f0064004031241c060a4408020405540000c0c0207140e0851030020b0001c2d0204c1c500c10380140c040d5869500440d41540c0e02e80c040c0003e8440240210b455109504008000307220100442d030003440405c0200b070b83c540c010f20a0302c0c4640d50040041c082c1b12040000020f001c2c0001c1c204404d001d4080c4000e19140039000050946d88090f00e00440e02c800c040d050400d4610540c0c2c44031a01c08480c18184410300000200404e01c65030401e114500d040321910102c0e010700c00024003e070034140702003030074941c500041543e4001c803005030000d204210345560412003100c030944034052020340e07151002c0103820b01811701140c1c0300c1d00081001580d00c2c499004030b420300825845000c602282610409031481051040c10701400c0e00f65030400010711740d6941c5040c1803290816527840341442a0005940600280484001d000303002e00740e03202420076142400042d003200e2002c00304641e10001c0003410300076070300c01d05000c01e415500415869203032a0043d1141da00c00a560020300c10f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 304449046 1250 304447796 304447813
    0x301060e0310090f150e0303070c05190206091002190c0303022a040e0a05060c0d0f06050f0d171603270e0a0e030f090102011410060e0414070e09090f030409050405 72
    0x4c1b001e00143d07200e6140c41c1c40c0c840c1e00b10114034080d4100600442040813482c80024510050b07200d00082e01c83e103420940d10042d01103281c0c50180c1c90178083c400c00c0a02d883d00c40e1501c50030024500c01c1141200d109400310340003414401c201603020354641c0550790200301c904d28200c18901d49508110b4002c100141038a226030f082e9285d50742814011904040e408000190040110300203110345402101c11400403c00b280c200400509107a60032003a00d03202c1d180310780382c1805000301c0e180340e403100d5075101a05941d5400d05040f0f182109010680c00e07070208215550402e24214101800051010006081110b8600782401d40340203d030080c1545800e50361341c00640900c0b9202300014250b00c0c040d82c1c01d0984a00d1403000090030741341901c1025a24a03000c400380800d40080d07500f400c00340c0e900c83c28500b0000404001040c024140d41c440251418611002d00c030150741c0186265040910645012520780e1700d41d01368944d1346c01d82803404038423a4805c10041001c41c15550220380c2081c0b0420130342e41d250 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 304450296 1250 304449046 304449071
    0x100303120b06270f010f02100509070506040f060f1b03030e0f010216020906010c031b05010b04060e0406060e070504051509220c091a0913020301060e0310090f15 71
    0xc160040c00342020500c59850200c030f82c940104080c2401a003460184c840303004518000317442d00e00107800c484441d81c40d0ba010814040082c001c2c0005040003800c00e0fa203c0740d0354400640b0045983c810300c8040b81140c121014900d118000c03410544000b0403071f00d400150300340c0d4118020898034414020600500c1c45809076208280010070106a4880d5003580001090042056444025000e90706003e1341c1325245e00025040f660020452408820454000102d0305105014083d500d1000741c0c000e00d000720102f81080740780e44060050340036040c100041a240c0d207c8100c40042600c8090110b6000e1004201c1e51800c180754030407080c40d240700c0d2407d000007030001c122300070b40240d00450241c0b0300d2404016200003501c250152004145040c0000501d40011000c020b0781420801782c0400c000503ca406640381c11a45101201d2030100440d525a0745c0c110080c00000744102042c0329008840f080b008040407801403420292f00440d424201d510140d9034110041e0303648941a041e07903110310309180d24 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 304451546 1250 304450296 304450327
    0xc030306051207030605090d0206041b08100e0f0f0c040c09030c03080c0d05130510261509040b0c030615030c07030905030d0c061509110403020108100303120b06 71
    0x381c0c080b1000030304815065140207001e070340d4020200c2e03d69074000b055104942c2d03400038140390416000340d075202e200c3c14401c08e440509005074114162501c107800309440703030032003681c8410385180c011000d462020030008022615050782800c0040c0e5640400038085461a02d5070100032840703c0d074107000d040340d69240d0307400355049035560060302d6000f80400c40320311600e810301008600c01038510b02945000f981300d18000d080c01050103624000d00300200300f0000d07240104c81c00500b0402160082c2c0c10f40e4580b54004414600031580381c0c4201c0b0740070f040148242082d40b844c40c003950f4402d2003a100c5070740e000d90014094000509156100001304101840c070020341c40207600170891915030503696121810054940903650340258002da018440c1c0819044e4085002e0420b1903000401003507018000c042010058019084200744a280402d046d4041d8007110050003100c2c03007a01c4d6079510f0381d90350440c103041c0c3c41540700140100d5507140d4108200c42d02544802d110807402401c0605003043c2c0f10844d004d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 304452796 1250 304451546 304451569
    0x10b09211f020705070b0408060c1c0513050c22050703150b031b07031b030e15090406060203090321071203051b04050105180a0e0403020a030306091a010c03030605 72
    0x7038541c00160142489424031100c000344c10180713005843c091401d070310300d0b65806004151417210900491030a46019441000c10003442c802c0c0030900c62410046031407401c2c10020b0008407110b00c10045054403904041c1021100e0b0300070708245151010251103104042c08004002c8410156074a4905682000441410000d082d407072100980f01d00d0804d1040c0041c1d0b5590070b6144c8086828040080042e074000760400350040090000742040100d0700d01564424100c100140c0d02800403600c002c0f415400f04064400000c04482c10300806035a104260b0716407040326601d54154004d00c2e030310a40001503840e80015025844071aa2408075191645c01c000f0440540d2000020b44800c1030101140c051881d6020304101100c6242c80c081c46c040002c2c0c124856041501c41f201030660701c00600b41e84420004000f07007032040c0d003a4011b20b410329009454070156181140400c0c9802e50206164105208808003840a00c903d1084000d034000151421900207204608143d2500e1000c643c0e5143c0d03021109 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 304454046 1250 304452796 304452853
    0x151208040b12010807081504033b03060f070e0d0f060213140a08031c1409010b10080103050a02150c0d0e130908030a09030c05061905010b0921 63
    0x14029414804070b01d01700712140d80445000d6002401400d60025401046a0882c1d850304024501003031510481c2c01110710000400803003480c08500d0300b003a40080980800141e82141501d032250368200301c000018806480000008000203501141c5d0700708600c00342806406a03080d00e07440d459641c0d501069030300c5040482c41059a070402000000c101c035409016143c0d0441c1c040c0342d8181031052095503402000d01007016540103a1702c80780c0a08030342d44141c4095841542c103030801d2904084c203902030311008140c140102100c12581e1300e0180700c0d04ca8107060b40d612202608480225408100c140020040c5240d03500781c0030003490810078001c00943d154410581c440365032500214041103941e02d551050388400a092000c490000f8040c07000b20303070344854106000102c0e10014102100c00c80c102c3c1000418a10840342400840c0302c500102d500024804001480240e80340c40c2c030a9030500594500582001e401d00030b0300d001d489101c005103442d80c207d01c01c60b02d9004078102c0c0380f400e4007030002d00344 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 304455296 1250 304454046 304454077
    0xc0a030f0f03090b07030c110604050703230615010323160302280309020d0606080601050a06020d0c240204030c0f030c03030c060908070506060112151208040b 70
    0x380096078101006140c0100e16040c2002841c2039600c40d0803403030b0700c002c14110400d60f6940e00030320721b54010b041030503a101c0f01ea000c40d03c0c01d15107480c01590744c0c03009000580f0a45169500b003140c55000c2d500c081c072400444006070140307458058449500b400140b484030306240d00d608106280b0707484d040b020f402c40340810300c08011606200391031810040e0303411800c108040c01080400b10341402452a0900c2d4160214545c00458411108600601080c00001d40c0102000c250030107124440d00150113680c3e40c001030740e00c540d82e202c0030080d45d907900e8070594015030040c6512001850145140c0b030036043c00b07a031003a225203801c0405081c2810510040e50740c9954082018400d001c80c1d04600d202914112881000c1c050450b01d071000c8449140c8070040030880c42c100d516041108d5a045520100e620082260f194440c42c5401c503100c0a049449500280c002205844000034070b015aa4580404c0400d0f8001e0a0070020b003205122040d07101901c1003241044001024034002c40284444403003803050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 304456546 1250 304455296 304455317
    0xf0307120c0807141615090506010b03070e0306010501080c090a03020a06050d14040201140c03090405190c02151302150c210910030c0216090c030b042306060c0a03 72
    0x43e14600b44000c044d20041c1c0c0a010700c1900401a1200c3e1080e42c0c1c100400e0380107a00007040e52009030031009030088c1a0301800c030001410b500f110014502070103041d141c802001c0d4a2105050340c84074240b080c0e40c0080c00c164080707080c45c1c50303441c0100ba08070f00c0504210300c40c580340d0b000f01d804941aa44180e00007440080e00c10941221440b80d501490145d00c95010f0030f08190300000c05070300301045200b80703c8500080c0e41007401d00410031102d418201510034041454070401000c41e9210784411281094103200300f40c3d1841e4800724461504d010f26140d9a0030320b0701e81c9481d9a20310040c1a00c200d0f04003248205102c4940904800b40403803008400c010075041c00512101d6102d120103403c1020f1784031080c0300e4100c055031403d000382c1e08a041890000740c0700000321412807411001d071110300d040307081417580403910002c0c0781c05c0080c100f40c09031414445c03c503159060104071142c2c06c012081641c416040b50b8a600b02d0a0100ca401c050002c1000d07041020f20016507040502091003180440c01060340c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 304457796 1250 304456546 304456561
    0x1031b02100b0306040803040305031f080303010f06020312070f02070518150607030509270702070801110c0c0609010c0b1f1202030307022e090f09020f0f0307120c08 73
    0x100c2d1000302c0141c019061a080c103a81e0035074240009400181480300c0400041e810341048072644500304a50340c0c6400a0580d5501425103984c003e009036801703581d81c0ca101041840c0000226882c01700103403805c41c1e880e550070604807000702c66030a0703200850081502c001003d035200c4659001d4180b00d4034442a040c200550310301320068a914240c1e000c1c840c140b2050307020079003000030746403481401c0d80d103224054401c82c5640080d81c20300c005403020000c210140030007503034000f1321001503800c000000c01445560403603101c440c0c014118021595031180d51003590b1800c00c40060111140d06060010102805a4541610190031110b030145d86142001585801109031f02c000000c00740455081280100c81c0c01107900ca101d00e410103401034043c03003503c07180a8072980380d036101c41e807010b8641c4c294500042d500070480070441c4140c0c0303030341e01c0708490202d00b0256520072140714014980c0d00920b8149100d860208542004180c24140508044000340504042c01008401c1c0c80a130307528000d501d42002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 304459046 1250 304457796 304457801
    0x80304080f1f0b0d02040504060e0f1605060f0912030a0909060f09020c0f06090115080c1807050702030a080a030c03093504090509070e0907050d0201031b0210 70
    0x2402018035400b11540c50740c108400c1e4000d03500506200004200c0f441814042411503502210003500a481c0000b00818020740364402020001c83d00181d034804000320341783c070365201c2c0314490a5145c0708402a04100318a011402004039451020034603050001005c001120040000d03544026a0000940311041582c0543d800c0c02a007031044041186604010205c0c40c00544d9006100880341d000503042600e40c000c2046002e210300d44030071103406140035031190780030300f01c801494070055044a41c082414100883c0c1e00c1e03d000d00c0030b4062407e06200301800421004003030300c0709050110422407800581c405101403881d01d4000c0040e2076580350020300c010116290003084208140c0780280c42e20000344103248812140507811041043c21840c419031a8a107080811030031100003000400203840c08170358101a110745c40000581310702079510b600e24000c1140440d06048160000310091140f0b1405080d00640e40c0c1c0185400240d0700000302c100ca041c0110b000d10280941d10a0015007041059070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 304460296 1250 304459046 304459063
    0x31103061006080a09051009031211030417130b0f070311030310090506130f0b0a05030d020319090801051026100518060109020d0c030b010c150e030408030408 70
    0x30420008072900e00300b00100500d101405100b04c40d61243c2058040c084d082117483c0c11141c48403070400c0800501d142c0a0025004041c44166441c2040079851001e1800829a0b1049401c0118581c0d002040e4101804650201c80b088005002e041004207032000c1c04000703001043d9520710f5490780d0360024140500001c1e03941410780790380c0d03004100700f00400103480c91000071120700d44000314243e101c00340010305124010a172a0803441c9130000c000c1503490242c20030302059000f6109050059101c80074151107600340080f0344003580c01080303045004440d01e0585200c410051404030b580c0341d00c4424840c25244296040e562502000c08184204004005c002082440101c0310924460a00c44100c0e21f41c110807075040906a174801c001000c2c05282201ca0300d81485c448290340301580c5482da0039000b0b40041c000c581180d07240c18030701030146002c0e10500502075016111b0300345d10112070741c130610003001e0804421481500c400326100c00305001c0003d0400740402c03602031038842d410040709502c0c02241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 304461546 1250 304460296 304460311
    0xc09010e1002191721010906062309060c0f12041503051005040e0a12080c0d0b03010b04050702010b030f120301051003060e0c0a08060d02130e010f050103110306 71
    0xd00e03079104807141d000190ba10990308552403ea60400302424500052124818800030b903040008030700701c0c00406100c070402403036030b1040c4071001d50741c845181c041198824059000802c840031180c0714260811502c21101c0f02810002900d808690380c041002d541044100b0301260b4002000c40d201410144444100c0748140c01c216414285071a1051f03039410f540704030313400070b03d5070311004103c5000c14480700602800d000f6009000740707030b285440c090355000703480401d0303403880c4c24601c0480d103c91203003424074022a41c52120f6810000e4080040f401803d100c2c590640c159610750107135600380c65a0050910800c0e880d0000a0b107100003809060030008440c010340c0c429000304c00949085548402907a05442c020340d420340303403084244026001040207070070a01d91900d41400704411240040010819070490355603c00d455111034003440354166510500a44c003a4400c50f0004800042e58440c0d00143d1040e8000f044212101040070111002030300142c0700c554080000c4046030a01f0004950008ac0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 304462796 1250 304461546 304461559
    0x10f021206030c010522030219030b0a05010f031103030715020c01060504090c060e030f060a020405120f0a080315120601030b1e010e0c0d0f0501150e0d020402130e0c09010e 76
    0x3c3c03100091440c803ea42c103282c80e0f6070707003c101c03440d000d44902058005554003910400c002d0204400e0072030b4500c0ca900c0100c031511492000582051341c24059181201d0b00c92081e0b2442506550b28480480900c030303034564051000f801110085051060b003140c000c1c40411006075200305000310282944e4a80d00020300032030030000601d00141c6812a00030442c1c119113440310341180d1000019091202c40740b003074046841b541c414443c1c0003a883c1d004000310b070b008940000441000b180082d407509200c040c401180d420001e030007000b05003801c00035944114000007100e07010128100150300e221112001c1078643d400b90005000b002103900405800420140b00d82c000802c0b40c0d640101441c0050068080350141c1c074010403200540035056440d0070308102c03001d21040c000024904000c0000340301d021403a21034000c01200440c040c42e440301d0b0b81c0c0c102a0010111400907000d020180d800200c0d0000c52204806c00014401c83c50030485000701d032400102540d03074103014001001c10b504210740034810807 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 304464046 1250 304462796 304462813
    0x5010903020d080d06030b040602250b040314041d0604060902090a06050d1e0b030705011110050c090613030312151205161d0a06050319080c010f02120603 68
    0x1d07129000655903076030180d501559211000f813800d019140a520041a03214401c0600c401c020581d0044c118624140035038500461007101d070000140007000307000c0c10009180303001c103000c6803050401561000302c050700c51745081c0d51410f80e0f050b00076414000c00301e01d007000d006021031032501c5d000304002806208070a500b042c5140001440da4400c911440040c40070000b24910141c05a4100340142a0400c5a112080500366811000350004d0701d05140301c1c0c01340c9840450158040c860321810031545034001d00c0f5940d048102d02004002c09060340c0780c03a800074881e5804565480e002001130501c01b94420381c20619514003d443d46040c06214181903040c0b08002d114040140d500008a500e0321903d8011040d5500303241d410074032030094043c0340502c1c00d00041909281c20b0740e032141c000b110404000150344e892006d01c0840f640740c050303903074990480001c44200e0050035594680441c00f0b055014901000b605005c2d084940e6928034540490300895480e000c001401d0105a02080540140c500c8a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 304465296 1250 304464046 304464049
    0x1140103030f0f180f0503010b010c0b01060e011106100806100b030406050a0f06060305060f0303040f031b0e0a06051003140601050309071d150a0b1c020c010c090501090501090302 79
    0x85a102600c420081552540440c42c1d10410143c2ca855444d80ca0346880b0a464803100403034072001c5e003c0d260096086c1190079101e9449042444589074000c0281a031a9083c200120703950400e8041050403c09641081d588003241408224080d9640c0460821414039000c5040d0030400d0007402c848401002440030021080301c1011282d00940c00200066035a0743e100209009086030b0040301c400c5031800c03d0100300560541e0203180511801c235840344807910014101541ea118600400c151000051800c0001500314005030041500d00c0303502048050300c810303c02050907022503002204a407142030802c00c0c0d061403182c011410078140f40c20b11146041c40d252040044001c0d00b118108000000000c0c2007520900102c1c0190140b8180c0c1c18000d0882c0a9000c401c00d429110350340180a2600d94800c80e150007a5814100d54400b200315040085022100c45409a441c41c2138006580810003100011028031408058080646440d4801828000010701c000103035001181404409103090015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 304466546 1250 304465296 304465307
    0x40812090321180409050f010f180507150e060d091211060610020f0d081909020d0b0a09121709060603120d020712080f09012313081303050114010303 66
    0x10510140c1090000c0d142c420041401000d103050007a102e4003850001045910045d000005105140841480704c11101e410b00c0301812b455a9005115500c00141001000200084520412b1140c113024004040d042c0110704c2035489902a0b20920b0b60715480c503400c02021344101d02d2880c4480c0b51001c02c041d2001401c540d40d04001e0102c41c4035411124403051041d00c01c2001d16001c8070600107a0b4003021076080094003511050b02c0890300700c500341c844001080b001d4882c0f504003940013403a2880e0170b00f40c0d4691100901c030144c5811400d51311251440f0100313440791515003400e4410f5482c041090800c02c402002154060700c05841908030005012550382c001a1a50b400b03246e82c41415030b41c07001d43e43e024000b84149400144000c484240c2040070b550440d84682c41401106084400d40d95400d4006080308c4450304000c07a254550b4109003040760302241d840c0c0d4801e10480c0d8000f144282c503141c81c03415811281c1c2c1e009e0903804512050007041020300685d4044500c0184150b040e50456501500c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 304467796 1250 304466546 304466557
    0x90b100315080706030209011d0f0114090901141008100501050a170a0c09090c080720010504060203161103120c2b0605010819050903040812090321 65
    0xc00da2501c0200c1d5542004503105402408180c0498031141d5540601070b01940080d85c0301400f113a420740b0700101c20800302130749040c14000144506521076070360005640c0107880421408800301f0130320601c103490311407aa4190180c001100581c00c1440e00c0010841c0d40d442c0c051903034080100b404107100700c1c240c000303900e0b4042e244242401034882801c84002c582e4001c0d40085001c40d000554280b11a10801d80d00c0b03a1100b42c140c2d40c5041c2a02d4130f641745070b0103541090440c1030014a000001406c200d10981035400c140034001d010942c0c042c0910190307801d5420640b0266416907000092103499820400e44144035103040c1818a1410b02d1001450f460b07000355035868400044803800100750740c02180850300003d100000402041c03e0050390010058900d14000503100e20709100425150700070340840348101c040b4440c65080b001d80210340b4005e000d026187d07403401c0c0300500c03010038000303001d01004105041c5040c11a40f186d410408051902c40207003104040e118112602e0407000d2000c80441d034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 304469046 1250 304467796 304467829
    0x1903051b070f1712040b09070503030a0f0c080408012c0d09090207060b0306091014010b030601030b060c0322050d0f0b040507030c0803180603071209020613030b040b01090b 76
    0xf04048500b100c041281c8100c00c09204c410b5044410442004100008940504661021030304003c1d1602c1c03c1c0340d80d92281100450104500c02100140c035441102c1200b21544950045420f040c3d642d100030f42034480003500745162465500700c02003800242444121010580390003000806084a000341c40c034482c034010720341c1840e0005000024459140c0090342202c40140440c0d08501e050824903403980d04c84075500c5059410540e0014862844806480c165805007075514030b181c032824015001807c00140c800c1c1c01c81d105021800a5400a00207084402558000e4038a0141000c01c05807148219400c440c1c807641128000e44085440b412400c41c8a550000502c942c0d5140c608040d483d0040d1640000c0688001d90f00201e40c030f40000c000b80540c825001800d02200c60510200072440c001215848000b880b03c4110244000040e0400081103002614240c6070802d512009450740546801c00d5480d01021000d010403c080004100c1c01011684001c00101221078001581115060b240c503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 304470296 1250 304469046 304469063
    0x1b01090501090e130206040e15100e0607051f06090b04020f09060708070203010203130605060102010902100c03090b0309030c060106050f0912031c0f0b1203040b0a02031903051b070f 80
    0x140c0c0002124506104c598004140d00e86881c1e0f035558645e00e07014101c0e200c103070030700c0ea20038107200741c0c1043c1c0120b901010541c2c4501055a40c4030f41400490f401080040d81c95105d0102c1c0444050b42241d0710760401403e0704170104d40182400030442c16038149074641d40c001c920401c00607000000c18010b0b2001c0e080111401030b500c001c2810302040e54040d851020354907520000a00c00c0303541c6400b9800c00c01ea40300c4e6000b0310441d5580380059080324034029020350064003032103074549220320071910f0f038148a1080c00e01c000803039211020f1982942041310141c80d10340c00025001001041002054010025464020300e0002503041422040c080c0c095814060540043e50f030001503018000e84408100c01c410801d800d5450440d017501520320a00d00091a61510116000780c0c2420302e1074482540c58440190b00d090300e803a660220a80c41507800c00304501051240340c10245d030080800003a020327030740e41c0841c1da401d185181101107042e641d8110440c880822040303000400c0020384001c0d150b0400c406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 304471546 1250 304470296 304470301
    0x30f03031504020c070b0f07141b06030c121f0816030201120906090c090c0c0203030909041112101a011d04110d050f01050d03022503060e1b01090501090e 68
    0x4d4039060786500020461200810101c68012010000d4003140c0d0140c0009000d083e40c03c011103840700c1c1d0742d0141d403600202c083d901d06201d04010005503008101058018a00824013004405800064540c2d2403610308400003200035200070300700200942800c030050300755100d000f43c2c03040f03045640781300080c1404140410050425800d40c0010860384d002082403041e00300e81d02e0810164407480c040c0011540c50030140403099449030500d40c21250f4090025894040c140b03007013080c8011300030001c40b0030000b026071151040d2a840c8880c11006052401030a10152203e0070005803030002c105081500c1c24044d545c50144c1c0d10000c81e00c2d144841c0000b4019000c00749000c50060100c0000d0304030302c00d200068081584040c1d521040c8225079061416184da6200d408001c07540300c0c0004080e0041e8408440d5a880c0000c0c8640c81c01e16802d1024802c882d940da035610b02050f100c520780300c1101070300b000002119030111030721518042642440c09500103070915002911808580c0629202110071000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 304472796 1250 304471546 304471567
    0x824040311032a07060503060604140f2205011202010e0105070c0b040f090509030403022209050d0f0813120f020a0501110301031707050a031103120114030f0303150402 74
    0x44030840390703601c45801d0744041c0310035070944040303c0304181d0b4442d0301c650031002884600c40c03c1968001c00c00108058900345c034124410740800c4241d20343e9a80305451070100041070313a408412070340342446080c110350b07401000a003020854005900c866540300d85482c1160040c0e90000e11540c099009080503500c4445604052104000641200603070f004005008a481c950b000d0700d01040b200c8450341445a9590168502c1d00d900aa00c070082d0044810409488a1000d10000c1b80041c8603014000038401490f850361450903400d0300345c0401085040028240306540100f00c2a8881030240e821001070505903604241c0f2041c80440c00200207900d0001001075109000202900b50050000e006650380304509043c250300a01c81103038001702d81c288a81e519220541507400003504203015203016106504e0640d03c40d1030b1844102414001046100c42c079880341501c0c3d0340030303061300000d4080202c0050185841c2641e0500d003c0003a50050040011051505d01001010b000640340542c80e45031121 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 304474046 1250 304472796 304472803
    0x2030d05070e0a170706140f0c2104091404020d02011b0f0c2d14061209070806130c0306150503030a02060604290f2103040824040311 59
    0x1030346903021125903c0081d034140040301d0301c0b0b01040d007441a11001035030340d00260b5601c0b03446400084900c02c1407111044d07004d50500903103201034050040c0c07100600c0c00a4210050300560302801c59064000c60b0501c49884184104840002d07110040b000c81e080503000070f0050604050020b040003184a50304c215800d000100c038030100d07800300c0030b50f044040301d00d032140d2000014010240e0030746d04068440c018401d514144004a400c000348400e0542c01e01000c021880d003000c09a03a0001000c00014101c0316081d0092441403140501410b0002e0811902c2400c0101c06000101451006a644c0c40402c003241207100072a5840000050792001c0b000101c0d2a000c9036502091f8940004140448995000315016100b590103c800b0800b20401600d10002c41400192101c09001d0001450000d81010345030019000c00090144003500d014245106007036200c18508000c1b0780021408004100f41049000d0f40c80458074200401101d862507000d45401e4001c0016040141d4001c0c00341e880f05051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 304475296 1250 304474046 304474067
    0xd03050921150901051506031801060b04080a02030c041a0405190504050d0816050a0806030f010609090507090b0306061c0b01032a0b03071d030307030206061306030302030d0507 78
    0x240c401c030782d00b072110003220341900300c642e22015400d0800003619801292800e050481c0010102d80c11500c62401c1d100f01d1030401c000441e000d42d61408041506070314580508000c00d104401450204024414141411200b694103400303603003080607452250809083c1e4448506040e24001801d0707803010b40c03540b60702c1c625120159010340740c08184828080003040d01c3c5500205501d0f01d1101d901d601103003640161100008200081090207416401442000d0341c0382c001e103001301105ea000381848021800c503405507005509490342c480d44e40341007010a2212000030b02100c41c0800bd84000c034000310b52500c0c00100b09501c075009100d40e822166a094895040090300300d06280b4041d030716481c2160040d0003a20700d602c0100348044111102943d000358040548001c089002c0c00c1d03840340031040d9402001710802211a48804908200c01e80b000c1001c2c00300940a5802050241044024821218540c0d543d40120b682884d9081c4086600041201c4004c003a10400249030f60f04d21400f1159060b89 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 304476546 1250 304475296 304475359
    0x315030b040c1a0903030a0804032601170102030606160f0c09060f0b13030605090c040f06050405160c080708160501090302010b0a030b010b07052e0b0d030509 70
    0x103640601041c03254000381d00d01514101e010702c00c06124661240b103a14090b024501e980350740208010711800b84030b0440950030030f00ca170410907824903a083c05c043d50751403000205540d0403118001004011301400c0c140000b040d54000861450616001143c1d09220390440301c0c0d140305000790340300e0400c10a4500c80804c02c0e0000c00d040c52180d261300c11003000d03100720f20400112070100300b000b24000710424120b4224455140c00202c05a207180d9489001d44402802200316000e01424112035882da80100008030540b100c000030524284800c0008459026100c102100741b80c24541e12107a03001403101c0c4544c0d8021100c1500d45140c0e00e001c1400303114004030444a5824007500c074041200c150404030f501440307900240007414912050041411051001074140c1818a004200f1916617400800c43c00b0701501c256801461203501c0d502d11061006014451413030001c6012203110701c80d1058120690048422014404c0703282c80c010303c903005805505100c2c60000022011030b0f1843d00312034408510 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 304477796 1250 304476546 304476563
    0x32004051212041d06011407060c051c06080d0801261002160501051b0702061809042d03050406180306150603060e01030c03140a0b0c0405030d0801080706031503 71
    0x440d00c0003075620b00508141c40d51345003107050204510750f0140d040002960141a403183c01d190460312508003802e5403c04900c04d20108124001c0010014600320341c01740c2e400240810a03a00d045442487c01c43c1d51000c2004103e001d000502009190072031580c0c4480c040c810110010702c116850301c0c241940c03035800740a807a20001d1416914418412007540143c050f4008004d2956202d0458001240304003040c03081c46001c2082200505d030240140030807460620801d407840b194107010803108001a182030f24080d102220840c09d01440221a6418400d03010094020040c43d0b50701800c035000e540a40c03002e108004c0329455012840032800c0c001190043d00502c603c4640144144441ba01c5014001c00282095400309500e06612151812a5804001e18003440d00d55110701088003158520b14006014081c00c040204040300700403405514040e0034541e440d03180008041c40c02d040d0400e840e00f40a2280010400c0100104450f01142d04a04000c18110183c4100541e00b07d52600014024117 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 304479046 1250 304477796 304477799
    0xf02010608030712020c0d050c04090302191a0a021603031806110901091706070806061c1b0c020d020909010914071505040e01050402130509040b0703200405121204 72
    0xb191101101c508044c40c0c00791442d0f02c00010900ca060030b8100c4014103954041c41c1e00720900e042030360003100c015002e0301c183e5019101c8482c0d0001c4401c03400c174060314144407060000150301101d151017900b105d08100c04616041e81000c20241c969000360001d001e042d03407a1040d01300024800c106055090303003c002000341041a940c0b40569070840081c05000a00c5283c002c02d180314861450b400c9000104003c04995840e2441114000f02c001c1000380c0000d404d002e048642185a8052440d81d43d06080105000d801c0808410042082d400c80d4010800701c111a8000360311a2803d0b11070603038059030b80c0c1c01d0341d03910702c5211809403200010040c44408004082031001501207604400e4a0a420074031100f503d06aa0441b268020380c0552100d02002400400091500798014907000703040d1100f00b01000d90b502c00040702040b00300c3d82074441c40d100c1c40800c052070b507061103440c24140c002d00c8440c82101001d8044903030741c0207a024907406010b10707242980703040d1070030400380320010340031024540d5a6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 304480296 1250 304479046 304479053
    0x20a09091b05030708060a0c0903020607061a010e220e0a030305040c0806040507090b030c2701151b050c0307080a03080c1e160605070314010e07050702010f020106080307 75
    0x31150604065098071400c0c001040d20b00d0040b51180031180c0c07a50003010b4944404001d03900808013003c150b0b00b131150a100c004010380f54074002d400c20340d002c1d00317000408000e06a81640140c20400e4400d04000c190040c50001d0741d2090524000c0c1c101f00700086a828040b0702e40c1c20001c0c2180a001c17201e501c51071001508250303158210500c1603105080141106590b541b64540e2480261001041a00200303401e00519000b0340c80401e68240c01030484607480200710200e02c60711400d5540c2c1c002c4880115046418203d14a1003500414056400c1c080c005806a401400b081c400c0e00b0399940c8411002810303060140400c0040001c020090944508a5541c40c17802d0f80c031502c40900305c0120f002e400000d0480b00d40d00d4107940c0d060740010003d80070320301d0700840d02195900401c0c3c4030b0868801e56401c3c1c804260140300e424400e41660f01c0005081a02c1c0480100160f4140d001c491100d15000400441030780c80002d5907801582820310940b50501e007032060b409030060342c00116075440003051850a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 304481546 1250 304480296 304480313
    0x10909061511010203040b13030e04140f1008070b0a03020408030414011103041505070602070c06080a0b06160f0203030c030c0a0201031d060402060d11031e010e0f040f020a0909 78
    0x1d0500c1d030320b80c04242034840e030902d03090f0300044501070030b44d4000400141c15000c100b10141035a074070a00d0206110208200014221800380c6280a03c0d40f40d41420009a2840c0f084a16003147c07002c58290030f154039002c402940ea2a0341e0151080d01000824028181703400b07a01510042d001c1082900c0d2141d481d00d81e82d0383e4040b1100101070000715602c141291800f0003100b154151011102c41010044504400303840c1a48440800c40e81141e00300f0412000c5030543c034010300900405c2e07541c00d446082000d070603c25200c000b145940302d550200700b4560b0414051010059003680800c40f400c60850500010703085029000f81001c05010000c0d1985481c43c010800d0030031075100341c03010004072940f520384d50108550844003d44aa2020b40805e000d487c0c03100c003401081d034070200c001c030724810b000d02d00c1d4a0503003080d5078800b080e2007207000c1e4052104902050354094415400f00f6001460a00000c4c45600c8000e04045c1207141d0307440703031b03c029034961000031000f80542242c2480200120b10701480c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 304482796 1250 304481546 304481579
    0x12210c0f10151503090206090d061d1f0510030f0c1a0c150603010f060b030103020a0801140a1808070807020306010e060609060310082401090902100503040201090906 73
    0xc04601d8244061010078020782d0403400d4030f8440c031205018100c824400d0340140541c050a0344e109070144080465665901e04130344e0010710840e0082109000f00d001d01c1c02c01d414403004102c3c0d6402600000701001d107540c403e40c070b06241d2000080b0309529902101c0000100540000d4558110490b121060007034031651482100c0185205414100111507103003030b0f50042045650080d0801c41102c0101e046a89074103070000740c01070001030305901f144c240f1422220f241d8000054401e01000400941c5880c40030310006003204002444901c05140b00303100d11610091410803c5a80d8800070a8461008000030320815881035400b9502c0e0300710b00700540e00c0d4025850481c805e00c680d07000032684203400c55803580900c0001c0c04103400e10801c0030800c0041d805c0100081d961072081e4800040860040007001c1c4052008036550aa140412042c8400030b6416000b09007400d04008586d001a00e5002e14201c514180f807030200d440761541d10040340d1820140d448100f186082c03140214120320480354146 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 304484046 1250 304482796 304482823
    0x2120106090b0412030305040201030b040c03140606130b030702070306021305040b030f03030703091b12030206010e06011715150c0106080105041e020a0b0309010501030303050612210c0f 82
    0x42401d540b039442400511541c013850030703a10000340029000030b000707800c1030390030501c14100415962a000046011903150846400000ea103a0755015803101d002c01c03100360001000c0d15401e02c0c1c40c5104241c0e03a42031718580716880380701c4000400a01d2080c401e01115004d5540f14000399903c48107020f550031030079404e014980c4181d01e4140f00c07045e58078001400e5400440d0040145040d0b40c0d86100c1a80103040d0a413080c1ca0140320040011070801c140340c20b05000e80034180c3c0300c0d4442e01207414000e14028050700000e00a0300080240400c681e00001400c0d600000809090096039410704442c1008000c010800d400c20a00006001405041e44c0a4403a01c68600000c000c0c09985101032400d80f10140ca0141c422221054043c94540d850044030034040d001030024011196202e1b90b030281c9a10032501010140d42d100b0040c003c055150103056040301e81110321440d000701c412a4140ca640245c0c0007103548108000551100800c100300340e44209000c0001e0b21b0920101041c0c0c2521410b031807480701c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 304485296 1250 304484046 304484057
    0xc03120103061a04020307210209030601180e030301060215040f02031912050906071112061008010f0501061e022d120c150405030f0c0c010807020d020c0f1302120106 73
    0x50b0fa505040c800d0301d1260120f5602d588100700580f94111121190b0703042c05a01a40810091040d0f80302003105078020440c15651511740e00340d408121045034a95451100d07540c104000400105130f00043e0b040c8007506001e1014000e8655160810120b1a40d183c029054005d00b869400300c10350a00d600c0007494011582c108485000180c201d415109041d2420f40c00a0305010140210300c00c0c0310307102c400c01400341c407806e5602c16080d180d62400c04200c03801030313401c080d24409000e075007003c0c0185018110039050030300080d41000c0b8003610b0403080031005007116541d0070000904a100700440456121140d054416200d403420341c5413403a8100400360f004502c240106d4940418840080300c500c04070942c05404540c910000c061a060700142c001d44480c442032211b81104e018007001041c041846200410b865100307032001400101000341914199005880a80722031600400c11840300d00089845980c2c20384880d00050184150b112071840080c8049480424030b443c040d0784906881d0580c13141c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 304486546 1250 304485296 304485341
    0x403170f01050a060c080d0e030d0609021306111c0f08060904050a080a0e090a060510030b0a1703040e07020a0203071a0703030216061103010f0f080309060c0312010306 74
    0x15508619002e00c101c9030800d0020f4000c0190503c240a50240144603070246480d0846c00012241503c21200c045002c40d0000600c103496851584611001801c00402c190b0420640c0042500030410714424002400703c1d070034048200b000300b400381020108807098816020301d12114024040039100103c0d80100d07001f400410f5080c504503001622495011004045444072544c0d140000d422806441080c03007203640603610703241d50700385600d84698031541c00014100d10701303c00c00c1015140a4801f07814503203040548049910392720103000c2034607440b980e038079000308080c503415107944600c0d1b0001003102102c4003030041e000d034046818500d0300c1c0200c04442e4540e44490701030420300341601c0c005041c0d10302008140c0001c3e000e40c025105c83c2c003044ca0410303d02da049495400960312050305442d1950000001404041e60009040d8040c1690040307440c0b0041c14540f80c0daa4078401c03892400d1003880c01045101c0e008000300100c40070344c800b00b4051029540d4900c1d080c00601042d205500c040702c40c8118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 304487796 1250 304486546 304486561
    0x50402061c2f0a050a110601060807120216060c0207091109040501051c060902012007060206150102070306020306030a081b0606061801030c09270f200a090509040317 73
    0x101c942101021050040c03400c903820340e0a0b10316174031811081c0300384a00c908560102e00c41c2400741c01e000b007040ea11800c2143c540a40000c2059000d11000c0c94444e10510241044e0129140c1c07804055a02c80750004141204803810fa10307002d2140e2090404505100c500e44100d00580302600340100151790074400303640c03524100300e1411100d40191700f0b51000701c0e9408010841941200c0c100d20f00604016060440a011450b800e03041c8a0100b1519030080c45c0030880c156042000719413104080c1d03110300e0a2280703a40001d40310b0300304c0e2001400341c076008404100150340074010300380b00a07801a4202d0b651141143d6100c801d01c42541d00d180340e80a06000070744281840001c55000d407003c1401c3e111000501001580101000c0541808000e00140c004c0740340341911320003200c1c0c145485030701c1d000072400d00905400c1d2200801d800801c20f041145000c5c0b0500002504614903009400160b10340d00d00303103011269007103d940150707480792071082840f0500d038010100300c562a0445174810f07407550700c418 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 304489046 1250 304487796 304487861
    0x20c0f011e050112150f290109050a060305040602090301050718080c091f030623160903080a03150611010b010918021c1406010909051504050402061c 66
    0x4c141c0e20921007078650940029400d031a90002800b52641c006451303031580f1600e00c00c40c2d0107104c0c00c1c00710103140349100c0821b50400e03842c041c50b484240b034041c48590400c1c01041e809071003442135106050312000400c040000340c0e0151019190040c00800044c0b038039400c024104440b0b02d00b0a1406c0b2221003001c0f030148004501e000c01c480011306211040d898040c0d84d2443c4141c0130442440700805000040300144d001d00805902142c40880d514002e124031020444845025002d40c00d581150020406115041100082241d030005d80b4240c480700010800c2c0c001c2c00c00d0b12041d06403030194250100301130b900300f02d00e010342000c0d040080020350612001510007140900828007008030f50540410300c0f0f5015001450307103162002c209452804a008a00c090314080b04414070100e40e42000c1203c40c0d42c0c4501e0100041030801c405104500302419203c100305088030b5207a004640783d20004040d51100411103240102e18410203040740001e14003240185101710300c85848250004950100c0304004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 304490296 1250 304489046 304489049
    0x305160e09030c0a11011701030803010f05030c150703020a17030f0a02161218080c0f011e0e0d2001030e01060e0c070f0c03030201060509060109031a0604020c0f011e0501 75
    0x3c4020300e1000541d8443d4011030303051200c603904002d0f110b014551058052150f90380250310480d003092300c0b54101400c0800e025002d81183c2e0082d0b0040c0a01400c641e42c0d4000c00031030040700e030303440e40d558001820100d0402c0e42c1c201c0050400d240100891106508110095110301d100c0c100000c00c42d1100031400c003e0748100590101c0700d40200b0b884001080c1c0010003500700c0074050401041c846003034401d000d01e04020350300400042e0045640518a810100d014140c1c01000f4641211641c40903c41e0303020b64402101ca0004109004075008466115200c48005458108242c2d070f04600b200c1503c40700e5940284041030001c0d091520b814444241401008103440e041240c9060568400c00008856000450244e1303100d000501910b010680c81074910001e580203500200b6050704000501520f05800380010f4100414680100081446030350400c0c030b2001100b0320302609440e843c0008010f80203224100e100c40c012100b24200c00c0780c055001c00020701b258900c148400418041070010ac600c00d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 304491546 1250 304490296 304490317
    0x408030a0503090c040923070f090b040c03050403050d0b150d0509070806010501170c090d08030f100e0a0504031206091d0115060f0201020c0703030c11030105070e04090602040305160e0903 83
    0x98110305807070380d60408406040c84001f2007101e25256451603144440006a400b051521707a0b07541003000c460815010784d825151880c14144900c0c146075070010100c0c0701e080c10362410741d95601c07001c0d0304560760095440840304148400c140c58a42c0c0c581c201c00244002d540389882846403040000d0a190f0201c5c4083c102d40050311200d0000368240e446a1010308001c00c601080c0c0c00c20041c0c803185a0b03c900406203054002c044d280e840e031038400d407146418440540f1081039800c50503030402400880740c400315405070b0440c0002c945512545004e403000008250302c800c10508001005c40c0e19110340c0d00444600414034082800044c44002c0701c1c1c02c8035042c400400d21f0540400b0240305950040c0607003240140244001494203005080541c2000b1650304110000b5220500303000910829000c004820322040b4000c01c8203013021000030700ba450304655540d000700e464050405c14402247d06503030040d40c000c4c06071810042099401d5003a0310441c0101d10b0400c8580004ca0050340001060306c1802d0306 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 304492796 1250 304491546 304491563
    0x30d02030f090d050604030c120305160e030c040e1617061b04091b030507020114041203060b0d0c020f070e150a0b0a0e030d030903021207080408030a0503090c0409 72
    0x801505503215030b1088000c00c0e00515508860400200100030030b92083c0c1c06641d8120340d0107010300c0d004002010341c2d050f5808041c142800d1026a4420a58410030501c4034100000c0c18069031012900700059441d08940c09440c0900e50010f0100100344404015420443d42c507840b5100c0703540e401c581c00106480c0300550321500c005001e070711120102e28a00000040c0c62410a50303a0700f10202a00d42603408003030704d2000c040141c4c0109030540220303a0000080d0000f408251100c1d94500000c2000a00141c00d603000d0148e0740d822075000f42d0000001d40741e0f214049503502d896203540006000007456440042c0b003840055482d01c50003090101c01e56010b51030700006034803110566404140303a0701a040d80891103e900046000d0060000e1920031f5050300c800000f07044000415080500421000f4180360800e151b040c000390f030110b04944086c902c0055251036007814103024446020b2031304100c10707d02c0000743e860200d03904070007d544a000d0000450301c00d413200000b44004c0c1c0b04000c60003443d080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 304494046 1250 304492796 304492807
    0x140d0b0a020a0306050904060902010e0f0d03080c0d110903070e041a1b07060b0108011a090d050118031701080d0e040c0e0306070c020118060207050105210103060614030d0203 77
    0x2449500204410742e4646400b00d040c0f03484400080a0041c141e03002c0392000d95581c04e074411560054072001181c1000c649660481d80168003181d0f680d40390920040402c4101400107414010500aa50076100c144800b000300c03400c0600300180c640d021034081440381c03160300c0307000400310143c900503403103240d1015414400b85403004130740b04030140103410160b11010b807070718000d245c500400240040a0007071b100454503090900000d014001c041c1c000c81d010041c5909050904032040046649030081a100e50810102c107040060040040510403d1400d5451080c0400e06078840c0d18294046054100c8400590762140390710b076140c0b292881340e008220218603030007a51410f9403280625440768241000e1000d068000641001021107001012070310b020f51800965910070607012480320110041d0340c01c00d0502e00d010390350b99481d00c9894100704000400340303840954060b20941507628100c8074142940c407840c00c00050141c0b402990900c014000d1140454600002d10070100381841c2c01451425 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 304495296 1250 304494046 304494061
    0x207140f1f0204050d0b06120625051c0507080c0a0e01031e0f05192f0c010507030603021008040c050906060f04030807230d0305150316140d0b 63
    0x400c00e4100801c0799800d01001805494000040d141c0a03c1411081c0c5285003440c10008041040180300c2071650054040000d407010106455403d400e00300c41d4210004c3c41050202e81c00c1c03140072030414454510540d00c4081110702d8001030b00070b00044e02c5021a81d070361039021003058051000058005149040324070401c0d4001c3c0d000320700003140d0041d4194000c130301c95000b409850311003079604005a502c078200a10f072000c00c0c104946010b801c210030b00c00c10406e894003515072018510001d448075a1035241480c0300070400308490813884244024421440c2a0001078020403d074071007039006051000300c07032404901c2100110b2085601c03a0980384100d0600c1c0510411080081649401190800c0b02d900340005076000b03000210300c0f0b50407199690400385003100d00d5501d20704080c214007290340d40c120310100740070805521100c52443c000402e5a0b980940129031801d942c3c0d016050b000d035800c10403480d01c1582d0713a01d0958121a80c04200ba603010790502000b0500ea080c050048550340003c500e0f003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 304496402 1106 304495296 304495333
    0x1050105090915010c0b01060c020102070e0106170414013303050601090b0d0b070e0312040f060e03100612050705150304150e07090207140f 62
    0x105095075010070350082c8040c00034296260039105030b0000742d03c0f480c0d814030200c6e040211171142e540e440d44054500268500d0603401801074000118800c290011501d040f02c81580d581010b200200003000b44c01c007070180040b14515400000808606003d01606440c10010f0072241e005000c007041c942080412a916194003c096410800c0410300100e00c02b81190540000803d645d01c2440024400703002d1000010900b92101044c0308249602605110104405a0440f031940307502c0c0c181005a4003481c0b091000c0070102c013070f0902c146441030802d200c540602030100c0340040c8140c0119029100503810030b4401c3c440d045104000e00c51b007048500002c2009803580f216252510480c002244401840940210712080300d440c070030704559005044010f509400c2d1495643c4404da008043d40c458082502d1400440b0701c941c00c00c10703001c143d10341007030341c07520051070154826003002c00c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 304316546 304496402 := by
  have h0 := BRFrame.cov_init 304316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 304316546 ≤ n) (h2 : n < 304496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
