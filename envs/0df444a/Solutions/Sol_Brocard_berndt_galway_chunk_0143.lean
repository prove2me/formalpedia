-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0143
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:05:07.476484+00:00
-- url     : https://prove2.me/submissions/778c0a23-1e16-4fa9-8b4a-92e4562228b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 25539574 ≤ n < 25719430 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 25540824 1250 25539574 25539601
    0xa020d09051507080703030204050d08031608150108040203030c0f030d0b0306060307140301090b07020d030f0c090303081009090302070e090c130c0306030605090a05012403081602040c030203 84
    0x1c22048030652442c00e1991000c090900c030f0200003c00c0490b000561108050003601950b00038070000f403109290390428140100c16500445020701c0c0540802508100140540010340c002c000c8660254941d02a203001500c1650001c1d20070b90f4035100030b01c01142068400c0001249501c50301e00a140c48000c2c000c0d18005991207904075610a400113003c00c14180c4001808c08115046860344050f058502c501082c0140089200a002c407180c04003080096600000c400952520075a010030000c2500001042212007a09041c0001003841004002192060041c6a0001101c07010f95074465070f02c140400031100e6250045000d038000d060100005135040050990041b4404040c282d011060310010320600780c407650401c1070b81d580329000c0600c3d42c443e50208010750b0380400c0c00c0065062102840d43e1327401d01c85100304c0303c1d50700301902004000c840d42e5104045440c6081d1140e00c16003141d6403550135800010b200d40f4220201114580035035682d001e00c134550740c1c81e83c40050703030390900e90090203d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 25542074 1250 25540824 25540829
    0x21908010801140f0c04030f08030f0f1510090806040515010602010606020703030c06020c0601090f0b01050702030307030c031103030703020a03051503151005060301090218011805041107080a020d09 87
    0x1c5034506101002c0420354541c0351503100499800c06882540d6203168500701e80130701d4001410078500340c2400750802200340015401050305403003c0c80d817680e40c03c0c00320b00994001c030f8040b0340810407203020315003504141b00c02c890312005c1c50404c0d40e6400d4031100b1181ca000b10071034050380c3c3c1d917004403c104041a2000b244601400d2684002c0c4103080c20702001a680d0281440014100a00001480188481c0d81c0c1500c0107989000180c90305940e461424034082d001c45145004218a012400c1e4125030013402115181c03a4041c000e582407283e070352401c2da040c1721640001d45c01d011b01c403460210f4012060004610440c89a10010f03107070000c0c0b42000301150700c000c01079451066100300401203641c002800d1196100400b000c140c07107a654603902c500385030065021b150801070120020032000c030960003400c1a00d1071031040c0364042140400448000d00051502807100345200400c1c0302d98241a0810000104115400c511340001640c0c0c4030307401d52102d680507006030000c00c41d0020031644184941c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 25543324 1250 25542074 25542089
    0xb060105040305060112020607120e030706050405030c09090712080a0f090806040b1b130302120304030201120e03040b03150102010605031c081003020301150f0e0114061c02190801 79
    0x701821681c0c0e00e9a26101802001e14184070100250115034460040703070803031035200122450a0f00200c4014220540c0c1e1140a4403034000c0c9180426514071900a880440e40000c004154040620040c000340300c1c00900344181900410740f01103240c105a402021801e80b0425203242c1d20100403c0052100d80c000200000f00310307011604110454000030001c0e0499006624082c89c0c5d1a04a01e0f022400980c3c40c4130130f001a804600e803500c180540d00000110f81c02907540980000020100c0b984a100b00c0c04002c1c08030782c80700d07213150100b100c580c8801d801105400850f890140c40301c80c0f454858208450060f00c0040c4d52002500a580c2802100001c2009030000c01244460100c1c0307019803104034071680c040100a0000581c91150341110100640c0c01a000300300344103aa84a898224185010303401c013044503030000088903030748200800d0488003450000210180c900082020550040380c4502c00712003204001000d8410750b100422459010781485008041d5110026020050513031003540c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 25544574 1250 25543324 25543327
    0x30314040311100309051b12070b040303120209040204090b03010b0907080a0b0d1b080d020313050f0d1403040f0602030c03040302090603100528090f02040203060a1706040b060105 79
    0x61840c11402c0a54582150007910700032100d04110010309400c03a0141091083e01e000b011880910105030f1580c4209071241d0485880f03825202d603442c2c040e4800d10007095010801003010a1084031410000d400d03190f800752900711031074001000c0e80c00c82d0708040c40c6980d554035040b403176280c248586a920041681c04403940c1c54000e90140c46c04a00600805000340c030f0f4001140329a032032400c0309032030513407001c4090460054500703d10310b0303051180514982842002c40400820b40000305a403200705148500341e0303141c2d00709000e02204601804855401210848882d0005600b0060351459001700300c00070764982d0718000001c2603500710b95020f0425034204001103403a41c00003200300d80c142e9806503501c00780c0d03844207004246010380703507022881101d20b04014131410749103107110020f081080c405110000d80348000c52504480c03621030001c100141504800006003800e4014544c0250010321084555a072100b4080b640c0201441c40c04898100d00b00b04410403000340c403a81d400ca9000c1c648103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 25545824 1250 25544574 25544579
    0x305190302031215040e0a0f080f07020901080a0b01050111060103020d0c0b0a020a0203010501060e090105040c0c140a060c1e1413090b130b03031606020d0f0b030c010f0509010309170a0903031404 86
    0x108000313230030780801500c8800001100d007a0199000e0485020783d9019045440d1036030f54041c0c07070fa110011b50000300c1d41305804070000a660340c880d240c0211140e09400203404035900e1036007000603103c0c0ea5082214422245900090941150405080400400c0e0082d0052440a204150840304140c222006108654800405d00d0700c1d810305081c151030302601d000407140078a00c019264448a0300d4001c145000c09034940034506c40119040c01810312444081c4584089407805880020703d01402000000c0c24024401c503443c40341e240c5240000c050130300300380703040307035090703008030084125040040710a40350b980b40d10300c84c20115004106280d0321081000300b00c2022000949034803036007003103804440d582c2028dc414840142c0c1140c5d03000200010400020b0301c1452502c0c0501480c4111a11034042d0380f01440995014904075070420070981d480b00d10b4514104019001020000c1d400e1780c2000800c00300ca407904024500170080c46400340c403003c030036524600d00100104045200081c0c0b40c0400c0c0000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 25547074 1250 25545824 25545833
    0x7090e0712020906070c0b0c01060e0112080a17012c010302010c02060a02071d040201021b03030d150f0605040f080102040b03060105210c030105010e0102070305190302031215040e0a 80
    0xc261a00300340c81c001607510403018001454601031500007070318240c140c0c6d40000e0718a003c2401042552140341c0248403155451032003a0300c02d0001d00c90400500566006080000e0505004064000190030044050b5807000b0300440c8001c000d070020061180e10080b03580b0780708c80c3c4002c041803041400c400e5060543c11030307000801c02d000c0d03650000e01850000c02d86074484d82c0207002100180050a0b4003801550060121407803100d0213807801d80c003500031602d1000144041082e0540c0d07010024006600c0d10030608130000007802c2101113203003032020b00c400104805804803106002480c02d603944a4580d4100318550b0602404c0e640088503d038410001000350740300170401e03207a00c2042400c107242c80d000c400460324080064000000704900706c3c4410040c0300100380026506a0b4402e0340c902c2c843c0c525035001642d40f41d10500002d0140e0f481400b00502215440c800c804042e8420301c1030305d08140c0c1481920120100580b4031001e008201e80060000341021f10800910002200c010b01840c03080380c45 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 25548324 1250 25547074 25547087
    0x2180406050618060a15210b01080c18060d0902300601030b040b07030207050d0206010807090e07030609020315070f02120f03070e03030f07080301030204050105030111180310060e07090e07 83
    0x402e4465910501300c2200503007e128030b8080f050803000301c401e550314091038034402000541e50030790228413810085406003200100380e03038000e002080f04106079014641001901e81000c61000c01942e15444804010b8035040c41c11400c1d448450200e520342c000d58a40031551060120072800582d03c81401040480c00800c0059000340e0090992403103900da20804070080d200e04080506a4800c001226100030303030000c0c24604903048401550022510b4910040580316048000f03001c42c0d2181005001041166021090141c402003c403030320b601c44400c90000d00d0008072201d501103015910703c032030016018000d4513a681e0310680002d02d0500054203113112030001130000f60822083c0754880200d520100212000c07070b241d0b02007254a036092403400381d0060707009002c12400b81e410600000350074103050060a2210b0842e00c40c45d800e12a041401d035540010082240d54188140000c806251740c40d403180030040d0000510060341ca10341564040c18402e907640c00040b040e2441c40070410130591008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 25549574 1250 25548324 25548329
    0x4030503070305040515090a030f090503070513090b010f0905070206040b0106030e2b030609020405030309060a030603080406030606020f0721030302040b030708010f0e0c070201050702180406050618060a 89
    0xb0001020b44942c14104c2c0381036085100c40305040c080d8000d00c580c0c2c0400095000d0040d01c6070390b4110180115540c101c0e050203c034400d498050707001e05414012850041c00c01040410f11100c0050800219201c81c07507111030a0703108000c840b03000b20042c40009014043c403544141c0b03900060000381000d1740c0d995990041441040101940d920401074823400911000740920104440c00189100c501100280050321210200100b442d104002031008101e001f030340c08441c00280518103201b0b44500b403020517403020042034109550307280c0200000b4080c0300500054030329603400054107414444041e25110f5004d030f0034181940580400c00c8400c00c81d01742400d6808402009580081d041e01d001d80c080d010319001040b007481c0c08010444520307480483c2034101c804004c00344520b00d503100090000340300f040d6486400c5040411182c0e0140d4040e000420340944040d10780c0f60310810401c10811454820b031821603420b1b45030130500015160030020f03c480301851843c0c9030502d04040300041d11840d1240f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 25550824 1250 25549574 25549577
    0xf310f020706020703022104030b06010c0b0403030203220b0703021c0e010603020405070509090604020d020c0109050610060c0317070905030a051b0a06120f0b030a03020f12040e180708120c0d03050403050307 91
    0x170b000bd10079910405000d9140c96004804901d41c1c11300f45030143c042d420131a00e90400d00d140580612400d411900e1500001e5007090b0040b40744d4641c0142280030358405940d041c41d040450300c0d01030030301d5494464900c1003230503000002403090440c41040295980a005075040110500c03119205541c0c807205103420860807100140d03105420540d40d4041d010b8903c2114242d4a000b200000b804004120f19109000282600e00d959468000607103250894080280c0080c45c58000440d4111142000640048103403c01b0305da860380c1c0e040064074084031141c003100c0c9500001d8960602112a4101000b00a4103d0b00a9001800c2200050450300c500d030811346459120080d0102c030748100e0348044298080501584c103014110b0402a503101c030241d1440004d4816000c151440250440680d01070320401401e0322140d8440035085205200b12010f010703250302a90900052003001080380c80140c881c003000454462142400d4a41058030501c500303001e00d0b04010400c00042d901104483d84400709 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 25552074 1250 25550824 25550843
    0xc050c0c090417071a0106050712030b030c0607110f010509030a0807020d05030a02030a02060a020918040615060908070f0303080103170c010603110f310f02070602070302210403 78
    0x490600950300c800f0030040c0d900811000941e00180103208120000851a0004001c0c00d6640c4003000c540511600070081c0003180e030b14001654880c841c0e0809011240000c040303d112406400014007158481d88040380c4640030341101c1941c0d030922000315002c81c4000d003009400e000c0720f040829203500c02d080c80242a003800081c1442195030701c0308852405600303c812640ca0748854038000e9607030b5200c40b5080f8054400c21000418151085c000c076180a44081d00428002d80201d502c1500d865018200311034064070381001200d002e0004101308010031890f0385081d8401d180400840c2405040d400c0358443d0fa20000041c00880c3d00421003a0450b90301c025450101c01984c2020341036400343d403079243c8155082c8040081400b46480540e000720108848011280380740304100702108009050010300400300c100e104407034450a1104410200100501081c40e229068040080360f01c4042d040326103507400300703c010074154100460030b042800e40424042d0303074100c3c401c1d10049000724880100300b00c24 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 25553324 1250 25552074 25552081
    0x160f0807080723041203091202030a0f0812160e01170106180314060f0906060102100b040617030c01060e2206020c030304030e10030c121a0d050706030c050c0c09 71
    0x14054101c4428510f040c0f881c1e42c680b80c036100094050582c0400c207a000941c00c09001c1041c5400703081101d2480d134024028200004da0355900340e0066100b507410340b4907600501c0f038040e03140e948405082c880d00c1c400e600014058407105001d03101080154106041009407407200300340d480c2d03801140d07043d1500c90601b10429441c201c400c07035510301c4035040108040311107040001c95420016540740100701843c1c50740840d9984110309a942d40e011510940164800d083e0942e10000d2684100e000d800c020b400820356030303240c081c1116000d106404046859100007180070303036142d083c0303c6d04026006540350a031090170301c501c4669091038203006288110ba04034151100304442541281d4040122a003620f890386010b0901510b155910b00c1511700035400004d500358503904c03c0c4102581090552101000940d480098000400080f16507440d00100502c070050251742d00741058003100c2c80380000f082990300b0244010140c90b603001c8504140b02007441940c0f038299000c22449152101516003c40513903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 25554574 1250 25553324 25553357
    0x3040f020a1a0a030b010c050a0201030b0103110a091701050403020a1202031b01020903120910030218150c0d020622050106050418020a1208030f10090203160f08070807 74
    0x2059035202c0c039031110048010701640701560b405400408441e03101000801504001903a40c40301c001b00003881078000302c0c613107c0158065807100250080615000400c0402d10301c10006542c8003104020104005082c10004c0d07620207000560400c0c851002441070b8101642d0286d41d42c28440e8009110034801030701c01c4540ca108000b5652092b4841c0c1c0103071445d6156426140c000e50180c4143d50080c0075803000c060888090f003088a80005c0080c011054900d150b240442c029042828444510111000782200541d212180315900700c100f4450b16981d4042c089096181410141c0d000301950051030401c20800d038202e26034132020340081044e445000151a2560042c101d580206a10614080b110b18040036040c6000d084030313201790341e155000e41c0c854070150080c4a003002c000740b03080000c0001070260604143c0c4641c2011881902c003040c0b0703440b00b000400342c0e0821a102c0d440154410540180765601c085c00da41d8821103424041030908040318000c290f060001c1010b0148018800b280010b00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 25555824 1250 25554574 25554589
    0x4080a080d0b090403030603020f09070906030905070308120f010f05030304030b06011107060f0201140f06040207020319060212060405060f040b01090b130906050603100905060a050405040b06040509030702010503040f02 96
    0x8920060504a140c9071500c1d0140c000d1042340000c0e4051980024851494140880054000d03229504c03800fa10a242c04002c074068082c1400c11070346070068110001c0011801d101130002071401a80c1e20300d1502c6e0140d0860b11000c0140e1111880134000e900801c0552804001c4030142c2c0c0c2c0003c900c4010b0760390800180e500d0942d50700c100a0a1160360303000103942d94046000600060280d0080c0039201c0d4290307400740c00c210300381d48140d0002244d6010900d01e18184d0b00074601d451024054441f5140545048408541007034015607096030001a0a200d002044180d01c0e4091401c440030806400c1a0020442c09801043c186020355072b100c83c4040d035130380a413072020001c2000040342d80c0d460060001030f041801c0c1e2841908402800d03c0c102107641d240c00025031744900f2964868002d000d203410584406080041c01c456085404401d02081984460203060f06c0749000d10f81c50106ca0030820140070031910010725020319034106001180060384d208003140d40240d00041d0125042d0748500028581 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 25557074 1250 25555824 25555841
    0x240f0d0b03031303050115030b180106030c08030a1b030c03030509120403051507020106030302030703180b040603090b060303090604092703080916051809100e070905060604080a080d 80
    0x1403101080c561400c03e444a0040d06680c4940003c0c00102409081507134540d4081c00010b00d44403c400c0000c3c94054150800389900c1d0308500003081c15552030321034090b062a41e070040c110680000800c1900150000250401030440790084207a00540d910000c0620360b21400040c201a25580481c0f00700d0000c01c08220100700700b0074656920341c0c1c1c0e0700d41a540c40703010411400e001d000314000180c0300750062081200700e80d015009103103031000c241d404864180d81c0e00c01c410b5034144102d6020900b00b80300c20250000d0300351901c001402e02040d00300500c00c00340040c8440c3c443e81c0200b10342d141680301d940949003200c2010501059581081052048042c80740081e07583c8080619105403e15a0001c0201c1c081e00c00c08064400543c985e0304041c00d0014103008403074000800c40d891100304284800e606920402c1041640d603042220761900703082d6000c00c1c1d1223100a0340501403d02036020303544100c2c1e400c00e07000c4401920302488c1c0369903181c50b144020350242058a0201e1000d0780c003000c64000940 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 25558324 1250 25557074 25557079
    0x405040f020a080c01080a090506010e040507091404030305160e01030c09030f0605060a080a170307031b0203030108070f030f0b0c130902040906080a0c150c150209240f0d0b 76
    0x16440e03c51400b5aa551800016035001035041d40208103926810320451500341c4e00400a0300c05a804c244e20b1558424010b401120503102e402c03000100c0320301c03d00c0703419042c0e00f54070300851013400d007801c0040580304064000ca2042c1c4aa1010a88290304094079001e00d100c20308020640d40d031002d00603902901142d0020300f1001100110b4820442243e002c288983e0045600c129415150444103039620b050641c01091b28620524644121100b1800345601120078900481c900350a0090b0790403c1a10550b9000035034400302c01807190b600e05000c00d1014144801e01d840105285855208011a02c2c2c4030107420b440281d0040f0f44a06103900c111444150b801e003124001a58a0480034000d6119100b88004540342040215000f20701207070ba044079a070017804c074582d0039040400742ca0a80300002d410206205103100e0010010f500c800080404080120006855140b0b240520501180c1808000790100380352407459180c9211105032090454225020703034441c41c520b840400101040300038243e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 25559574 1250 25558324 25558339
    0xa020108070228030f05030c0703051b1903020106050301150510020715050d05010906060c02040b0402090d08030604050f040510020306150705030319060f0308220f0e0c13050405040f02 81
    0x140d9545440f5002500c80c0d5114007000200b05800c072010b0105a6100e052110204005000300344034030003078040c41c00040505c044008440d2115032801c46441290707130342025080c0c2a401815020b22610b07000304010340c024020f0882c0300264683d4602c09004040c070816203030485051052007042408090702000f42e401d0410480000301501e40d0300010080894542800004142051140201c0301101c0190b2182000801c0b02c2d0300f0007020b80003418142d40c1040c3d00b4001c020b1565604545030310b4984c090702440350b99003001d505000903120028441902450400c060000040b40026101c0f122840341d2001616501c800c4e0000c0c0400e12094203208000c0000710b50348080c07040200065000b98180c203043c07003603100c2110b046400d842c1c181c8100003201c5002d01c020008198200c005004051800e10b4610401440e60340c010403070710081d04040b035402c804003c180441c40003e07030190742141c000b1440a0800c0403050000c581030195010300ba02860321480070504004c2c000072080c54981e030060466 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 25560824 1250 25559574 25559623
    0x9060b0f130f08030c0d090501080c071502030703020d0b09150d05251401080402010203090f04020708030a1b02030909070f0e030f0102030a24090903050706020703020a02010e0f030a0201080702 85
    0x11130b13a07030f0040a2160018021050b00d0710b46180030b0444081200d0741a1990b04a0303035244581e4043c1c8c0e0704600416100340c094180301d9035080348a480110f00c15401e6880060311860801501c03022150082c254a000c0e804500038405010824600d0301c680d41d4040b243e486020b0a01e117030440c240306081c03401d412070b42c002c1200440d011400c8a640c40585100419a01085041c0c2004444140007134802a015800c2088032020300d051525125000550160015281112545c0d840225900803281d0000c2c05594640e002c0c548540c0d008038880c0181c0e20710055040841d40d01c000740b90341801030004424802d55107070010305280292200c000402d8010140c2c3c040c620400180e5000c5e6104850702c170803091600c8050410982030191403001c406a148040c050181008010001442408019801d1240900c05040003800500003807030224803945c040c1101035400d200240c01d210f81b10100720b2103403604400310b160302d071000100c1840960702403034606035039222941c0c01e90419840d6101c01c0003400009510703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 25562074 1250 25560824 25560839
    0x1805030f0307030b010c030e27040f06050714040b0915030a06030b06031603060b04020705070303030204030b15060d05040204021603020105040c0515041e0b0309010b010909060b0f130f 81
    0x107140b0949880e2010b00800c140f8400444213003441550080114401015003550f030b081c401c03419150940d6132210521700896000240c106c00504807011120b0491101c8000b041108501803150051601c1c20070428040b213941020b40c140c042c50142c286902d0b4003140421156035030949080e0306e0380300c0004041d5a41403490000c40504800e000c2600c00d035200901190450400260b810900c3d6185400b0708555400c582e00d141c06030008034050765019400303110780d401081d018001e40c0d00035440b80c0c0700183e440b403462a040341510b80c010184000340228030f50071131680d1034407411608580b14560b00002d441d80c0320300c006002402a00340c4420480c4132031111404040e0150311441c001e501030300300d582c030302c1740d071141084841030700c0d4400300e0040300091104200c0d03c054010302503000301401e0601a012038030350980c918160401c0350461040e03911a2007100055802005e08806000c510b03000780145418158500e1051140f5072003140f018100107102c134110051440180b0142190540640280d66182c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 25563324 1250 25562074 25562077
    0xb040f0209010b090d080c16061d01030606090905040302390f0105071403040b030c2a070b0a030e0307050f1c0f0e04021e0409060e0402131805030f 65
    0x14201d018080440c004600c0101000903540b20030700040140104d80c0a40d650724042c0e400100c801601881501c407020342e2203801d00429005040c01c0e0b0b0ba04441581d220380c4101c0500351a4403024141740c0780030810702010b40d01250150079a11800000b00c0c2980301c0785803c900e0140c016103a40c140d0f29010603229008500c50640d00d242540c080280b000d9802c20701c00f0050710000541c4c2941c04641c0401030100002c00205c1140341c292020815242450b03990f60012580d54005c8680c100407060025007918030308540010384000450140040031404105651641c0da40e0301400b40e100f9100c00400d585070340500c2a080142c115941400303a948440c510b140a59842001403580c035050f0095440600d091480b000c82c110280281c1c0da219407a410416900395900d20744241629049078080020f2804001e18607034030380ca0402d4410b4800c3e6214500101c520480d005600304007a007450380300c24400545d540522022807017885140c0001c0010188170401c0c0c100c0ca003800000c10034000400e600604110010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25564574 1250 25563324 25563353
    0xb04090609060b03010e060a0305010203070215011403150c0403020307081b061801140d02030f010e060a031a0601030902030a08040306060510050a030f0605040e1006060806090a0c09030b04 83
    0x501405001d44030005902030b64918060412072030001e00040044045801a55411a801500d000c601c10b490307407039942c01c4e41d00449065000d039022038001071482c00000940c80c010904c02c412021003001d480d0009480b0b030240b82503a50300c001040049180c0c040302c1c2d03088500450f4000c0817200010380e54554103444202001d040c4112200741181144c090921030111404a1403003599000a11403480c01900c0c45001c400c1d140b451010140104040c51035144029070203441c22445121856142000603550032400030001e40c0500310b25002000015188961140d6505c1401c4e0013028035507030070380100d00420b0f803040d02950600c548880c3c0c2044c000c00e00c0c0180b09480c01040207012807510703003090240c142000c40c40301c000150100040d100b01032181d07211000200b903000d80403800035500d030000740c151180c1d5042e95585400032807050103c3e03405446004010b1503e414070314050300c0c1c064001654020010198210f650304c0300c1c03032402c02502c602d407148003a5501540485140c14030741005c03041404001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 25565824 1250 25564574 25564589
    0xb1809070902070c030303020c010b1201020316020f0c010c050c0d140d03020f030402090406090c060906120c0215100305100501050111010506100e040e03040803071e050303070807180b04 82
    0x151000704804100340225600c2541081640c40440c2c0340d075800b10003d51154010f0080b95680d42d504420701d990304490032001d581040000f584a0401203070110b90107642d00d40a60644d031003102070b03c01d07510011034804400c0c2c0d024200001e5407816420054240114030f80c00d507921140c800212070401c01244480c10030300c404402180da400050000c10380882c410410060401102880060018680110000d501038400c030804a0310501d540c2d41d055900e4050707002003000c24080381c0c05011099100d141844100d014107010300c400b66544070041d49030600140c0015586090782c000403400001592f089005643c09400c03290070a42d180308a0005110a001c1c82d070006d51201c0c003002043c1c43c1402950300805000308026880100f4150680b0000d110f504800c0c0c21a40708ca20712201564140054401442200003071a5105c00c1803801041c991804c1c02c05906900c0102c2c8200c01298002058030f81c0016203007041c24954440c408281e8400c41c040040b551100b5080d440441d2240d00da0000e0300885194 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 25567074 1250 25565824 25565833
    0xf010606020708030424021f0204180501031205030402010c050d02070302010e04051605091210050105090606130311010519121a060708130b04120209060105120601080402040b1809 79
    0x283c4015076204d201e2480381036151100e01b40407503160059a42c0480d25200c00c3c1c0102c0749282e94100c4020050a081240c0c26822a03000c202000700c0061100b03102030701030544404200c80d604580e2826001d01e8014800403c224001c4002411a4092591080c196810600312041241040402556080d181c00102e0000c0c0307000302d444905081c64000e860184a002074203035601d02c410b9604486035000b49445076841803102c045070b14141000c1c44010441000840d01040c158108000d0003107003080a004540070b0103082080014000c0141003030000d980c1e10206a4440d6010701004075154000c94010146401c5901101400650002d07800c840d00941c4240034000405484085007526080087c180c3d08008200138030300005d10036100074208002d00006e00000c00b0346540003489a40c2254001c280c10701c01844a1100350700d40094000d038008401d20f4003a03c3c081c0388480e03403030852101400d1036040c41a508081003c540d02c0b50001c0304a01005042c007040d4182c50101c8624808003590203110301e004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 25568324 1250 25567074 25567079
    0x7080f0f07050a05120c030a0f09050d1a100305070608060d0c090518030307020c0f04021e030a0b030303010b040611150705072001020d0f0203040801061d0f07120c0509030f0106060207 81
    0x2c80143c2e022551b440e40030f103081000e155000d070b82000b00f1840c82801c00c001810049115515008214541806425810080c54020300080d00044000d01038181500001008100080d400542d140a480140c94042048d40707074a408071700c00c074001600040c03442c18101c0e0f0200301c0d400180d11a9105005100b24003513110001f0b11019207a00c0240e801500607081860803101c0c0b818040e0458104e404054001860304400001072b40d001500700d1300804511200109020031001c00d80561031840038100c01652444d450207280c002c052107035210315000e1101092016105200901244903010210210b05069140c038400040166100001c12101540340c14081c0450791040b190003e00304006800034100b418104c001a60000c03d05995181107100402021400c0602801903000510485c2500317400d00c1100d41c2c503540140b000070080401d03100c1b00002c010203198803062185611a04240000b003456240300300300c800788140080c6603054420304035018154901540b20008441c07265095030b54068 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 25569574 1250 25568324 25568353
    0x50403080618061c0606060e150a0e0d031209050303180303010b070b180a050a150506130f15140307080708060601030506040624020613030507080f0f07050a05 70
    0xb0030301004502c41d08510300010352074280680b81d2800744d00d05500303551019545a5400058980c01d030003e0300003a0b40745104114a080c00382041d2180c00f801c4030400e05040451000030003409074000298403c110141c015402d01d03010300107003206038050003011702c40f000b41d50408681e079074402c1c3d48000d10f00150038005409403401005030781c10303110300000c160710b829102e44401e83c032008082c024901045450000ca41b4511080003240a5548030304042c0c500d507509410920040010419403914881c1000b04002d41d0380c0e101e034021850b220566000150f5101402410030081100e50300c00c14203a0f1145002180c060440e6074101c256480440441c4c01c12521014102e480e00c22622440510380e0216020540942c0207400080e4040005080040c807165100e45c0400c494042c0c06480000810444000c0c1040e036060102c664005146421001d401c000d6590060561284080103441200045015041c1214060485420240944406407940001d052003500e40d0300030007080356988594001000c0a5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 25570824 1250 25569574 25569589
    0x702010b0102060a0b0a0b04060c031202030906070c081903060302030706030b0a0b070215041202010201051f180209031c02010c030c09090507020c030d0e090f06060406140c010204090504030806 85
    0x48103a0207030015071200b01e010005080728100c030355400006d01c240880e030140d001010740010441036442c992451100c2c00e000d8449501ba08991020f28010400c00c0700703d100c005881c5400007510b2401e0a002e00f0942003014960040c80034185010b0310042e1910003181c1d06802220076a80220199000d1594414043e42155011005660400c2140b2003c1010282c540082c0142c5400a03000210005001603802e42e40d9005c1d400043c05101402110400c2d035a091145a81c040c6220004008800c001008500c182c00188551400b41401111030b08d90607070560140c90003954080c044400c505655204020b06503200c0080800541c43c100700c0d00c00c55440f074010400411601d4441d2400070741000186000750000911502c11751050115100e82503c003002202107442507a902c640540700703400104044070201030903416010010750103000c0580e4442c030881e0100c601c5800c0c80c400c0340641108024403070140590821480d480424001104072198025921840c4250b6414215644110400014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 25572074 1250 25570824 25570841
    0x8060409030806090c30060a06020613060204030c0b0301061403010b043305130512030d0203130b01030804060905010203131701150314010b010206090d030b0a0306020d050f070201 79
    0x140380700c2c0c04070f126420608a450b41102290411a01e0420348100d00042281404114000090500f103184c640d4201251060b400102c11200d14200c60310b40503000b507417084054403255080c80255030120400006904841c01581d1048007098a19035600100031203410910400020503059455103200c8070072641113a060782c2c4004002ca0a060500380a954510001c82080c83c21171056812841000324040c20712050f4a03ca60700d8540e00e0307910500003c004070240c0d010074012040d03c0380880e01914003109960290b000e8040060300c81d90341c0d914401e0440300e03140c00680400b950000100030701080c00e0042c81650416211800070503581c100481c4d17680b00e030320750504004400c0d000030b1100c040740510340c20a00054078008500681044000e14179148541d20880385040310040303500ba0031000f80036144c0340f07890900203842d0724a8414601a20b80c0ca60041c40ca04069a030001c0780c0315a541c480c58640a550407203c02c540751000c00820030010a002e443c0c000c150b010010000b00e4051050140050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 25573324 1250 25572074 25572077
    0xb010f02060403090303120e0102030f07110309010c0807050307080d0212010e01051018081006050a050406030807060b0a0306051e0c03070f0503090c1005070b01050f0d02010f1403160806040903 85
    0x9002e441c50f00c01f103610780440e01c3c101864540380c80c1c2c4010b2024090000d036006000102202c0c5160070155805405160b48511502da560010300460b440c580e041300e00c001c2011380010160355100c42500c0c14034194030480701c00500205021900400c21b4483e079014210300380120b039280803030f642c079100f8441507442c0034840d007503110741d01450443c050b038407610004c944d6010072442011b00648031540c1c141444e40020b6181d030010b40d1440c0c00c10451a107400288000c20080d6000c0115a00b940c450f81c00c584100c0202070704060b05d5480c141c0381d90311040c030030750000e40d004401084507003009400b488100c4403101048036000d41c002d0124148020a00443e80914150303202c00700402c41ca4071082e2420782005204c4150750203851314840d010340740e682c14004503020135a03949079a801940383c810007024068120601516070301003408500d0f2200401242030540900340905114200e5070200e071080b0400d4001d01851601005201409606058000c50001661103601035590351805100454411030070240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 25574574 1250 25573324 25573337
    0x3060504090206030606070224070209010b030601050f1602090c0705010e0f030313050c060d0509060106090b090108090102130b0901030b0117010323060108070608010b0a080f0613050a0b010f02060403 88
    0x135078503d0554014140c10f88060508480700710b84100010040c40c18211041042700700041c40c80841c5810009540500f0f8142d0300c0d14290705145000811a014200100c00c01c04000905100143d00f682c0c40d41c407032640d00074001e14241c0b8168198074000d4122001c1102c031507003002c01410100343c020602d5491200407030000c500b5903648031409240b030003420200350744070b00441242118a40341c120040001160a250214003030400319a0249800c0e0140c3c8003804000482c0010b0205410140844000d18424681050203131901040f03940248540000c00075124405880080c0c00c20500001c0d100e03090b001d0324204004282c0c0780064070050a041c98411072080c2c1c0000520000d0b0743d21440c40c42040c0400c2040031400c07803900c5980c0c42c0000a0301709419542c00309408002450340420758902428681400b542405049036002d40000d0000d40702c1007a00c0c5050300001d401d600c070001046a44402c1190501407414200d10501c01400e05628a034002480a003402d40014000150039000b9a815038418 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 25575824 1250 25574574 25574581
    0xe030c04020904020c060103060203100812030604020307030608010510080c010906050708030405030403080a02060907060c020117091207060e070902120c070201051204060b1003051b0304050f0d0207060306050409020603 96
    0x48001d6101c1c0301410fa00560901186400c003004104250295108900050352810510b6800ca09000f4a610402256002800100c401154001580c1e0400350030f8401589075266100d041d0068001504800125031070041006500c0881e11214804c8401c0394050f035200078141d070011900280140201400b00d0001c02411000490f58002141d001b8003e5058a04098480d591040c2903406840402c0c0107130710038400e00901001c203109860080030350b0b04040c0c1c180c031000c1c0c1c00644a440b0341000d22000561060000e10903443c28440100440303000aa91981c0341180d1030518001c0401c3c003243e6815204035003000c502d102452080780c070040d0320903480482c140d85580382c51080d580241d400300d0401c8401d101d070340d08140c0e080c10114011032050300082441940c0c1403c2c0700100c1080c00c20380c000c042c01c00702801200000c10804944600202c03079800da0301ea541d810543e1030155112403121143c40b5400e001c1d4609507020420a00359203003030380c041c05a20769510810003614020103001c0d40c0401d040020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 25577074 1250 25575824 25575829
    0x5090f03040314010b090103030801080708011e0507030e06010f03140604050a14010212010e060126060d020307120506180a050309010e0d140d02100e07030b0603070b04060504090c0e030c 82
    0x28a500c2c43e88620000c1801c004060121300300f00c03020f0b40101e01040800005200211050004001034501c070f1000304442c5000c00700c04110000c546101c3d1001c00c0c2c0d9400410030351442070304400e200c00d2040c4121ba0055075142640c2400b14000d12094940e1544581c58403071030b41011606600030b0350030400622100c403081e00c80c041074954031601c0c010303550343c20007413243c10b1018500024024258406003c081e80b0340392002600100d5441001e41a55000012000a0040d00400290051010b4a0300420004030344042840d00c01960041440841075040c494200003000412600c119802c9001c0f04484900c1e00b5107980d9001030240c001c1c1260024055034140c0c1d48100300151010b100280180c2a10311151506508401540065180b42e00100c0040541c660100203500305403c0b040c00030840001d00c1141c00d910b03003140d8007004040d18602c0300840e140341e40400c5080c01402440e6840d5964507a0b40700090000c0d07200d88240741006041100300f400160140c013011014087c050068624075284408 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 25578324 1250 25577074 25577093
    0x100b011d01210603050a020112090201080c090102010603060e0610080d080a181211010501060e090f07020c1e01090506030123031009050307060501050f0a06080a1803020c0405090f030403 82
    0x5001c811103820901c44160680e030f802210000c50080c40902002503c03400014803d48103c12070f0182039060010707142c0180d0b44013882903440b0425000180e00c480324500101c1c0902995800503140030300b807804201620501052030360058036602258852a90f840c84006d4a401c50550b40001189024000401d0041075400000004c2e11200c1d50000e120000c2e9200d641900b0f00310703281d80c0043c204010b034045594091090a025000d1400d014004601000000301002e800400b210781180c20100403e011900811a02020000c000c0802103080741d02203402a01072801550a40014142c9100040c24202501140c0c180d50b4500c0394482c10b40b4400c0303520820068110110f40e054414408800740aa03010711910103464420342c0590f95a90700b904040e4180c44060704240d00c00c213040304841003a40c3e2000030000844406040080701070380d4050207a8028401c0301035400000819050760b6007010b501161450031340130212400c202c1501d44500310b95a84d081c105601c45103500400c818000310b2a0500b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 25579574 1250 25578324 25578347
    0x203040606030f0302010c02010c0509030a0201050921061015050301171e0f0601090b030703031b08030403110f01050106080705070c1d0403120506061c0213030302100b011d01 77
    0x5010031101d54030750780e403d02c0c0d009606050780140d40d1000301d0303c41c0660a0003440720900151034902d007003001c10f0700005e0b103030003642000a0600030b001465003400d8070740c0001141100d640c50851113110034a0182140c40328822181080c0380d141214000c540c115282860490300703403040da5100c5c19030b0300340759110442268038482c05820b4410355061240c003a0800900d1000306070301001070800c2c0d003884000c00c1c3c40c10170306030801e16246081c0504941161000a00e61048070b0f0540791800c4400411580d1070081910158040e09100b800030802040c150041700e0b180206d01c85100300c07400b024107400f03514200c840a024100004031480042040c0c107104170080c2402c9801810300c02841030b505e003501d4061100d200c03040c1800900c1e220401c0b05145e08041c0c0305001140c5988180000d180400005240344682d000340e45219860000318032419030300d5410340d059000b8501031a080d007612402c010303686040325580c1b080780a04100c2e41074525441070031030036a20601c5202c1c1c14104c0c0d0881c801910b8400c0b203070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 25580824 1250 25579574 25579583
    0x40e15030c120c0406060c0f0b06010c060f0207020f0603090c0f2b0209070216090507051902100b030102070807060b0321030106021e03030402010e030c0a0303030204140f03060a020304 81
    0x100701c0904980d40c080e01040740c03140400080001c0c451070418801514065031144090019035031100010405034003c03903c80c2584802c0d0170314190781e0000143d502400050016020f07911700804000700c01d000313900a00e4042e0003112605a061402004c100740380c4011543d109581d000300307003903960743d09000d1454600b23054018015607030400c5a50014403001050314265501d481174407140c03425820800c0b500c2d41c02035103030b10150044007074400082042205510900c9050b9a0b92000104c80c240b00380f0070f0310403401d0a00200c0d01c0c1e042c0201002540d030354007020340e03034902480c001614a00307181c1442101c00c641d511070000b0703041140d1754aa8034010030074002d04d00c2d00b6000301d00410b4002580020181c0c0303c9000e0540f040c0e103035410100000d1505000210201c040d0b0141d207407080d02e510000003582e0b441a070911b08103105100300e0001c24200f071a6109001d07080104041c02204164140c0c02401c01d070781c0301032501a14035802004210318980300072100c603095000080424501c2000b03800440c4d015008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 25582074 1250 25580824 25580833
    0x30504050402070c03060605040e030a0f05070b09160603061d10030804080303150301020a0c080702040603050706030c0e0301060b041a0f0307031409070e0601051b100b09010803040e1503 82
    0x1203502140a980c00a10111201c4404690a1007042441c0c85410050602500c0810840c8000201260b983c4555000341c0b0a00c2100d8008a41903071141c001c0306c00255101c1c40c00040750070b05285803660b803c282d580c0b10280c1c580301e80c004500f6500c01d00c2110700300e46020500503e00009640350405c58200906244403c0d0214100032000c030380c07180d00410003005c0d10002160f4071320b8240b851603020401c2e1000309220380d0040014941182d0320410394000700760004001c0b81c0d9a2150710004c4e0043c00164070040240c05115400240315806600c401d00150503034030b03444a40030801c07003094201d54580c06940c1d03c4190038802480081050000307002e46030146a0402d10b05044188003600e9500304a038404006070f222010700400040300d440b0550842144001848030506000001d0201e04005010b68108800401d440b5920b059448503a1235144100080d5041c1d146188036180241811181d03140c0210901c3c000080c440c41d0000458088a9628403280050388032204610524140080480d606101c2e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 25583324 1250 25582074 25582079
    0x2e020a02160803041a040f05090603010b0409060b030f2113030b0a15050904020108010303030e0a2009010e010b03010621020a08011703070201050f0706060e010305060a050a090519030504 82
    0x19220300740000381442d00011a16189020098a8039503030110800aa840c030501c001c0003c0c070002c9520800355130342143d0641e5a940e41c0000b09004000b2844c41035881820816401d05000740fa40c0210400f241c00d07000c2c0c0e20b14662002c22141d44400317016400d00700901c000a00e10405503490f000c0e240c40401b0321b2210800c81c3d80ca44600110b0081035900620a59541d072121000e0300140d040c1d00b00a243c00d0b102c0e0f103640e20b800e40000c0d01c40c0c581440302500b415114410017100349024040b2100180e4005202c400311040c40318100f40c074514200d0201c1c003a14288001248440d07095444038102c440c400c80d4945982c1c2400d40485403000d04141c40700c03100081c01400020860603001070420041c490307880003c40d41c5450741c40c286080360750003421040c1d00100320740f20240c1d03406000c0b9604c1ea0045501c203aa00c2d0298500340300241825030055401110a00000c4104a0f0100b500390044000c07800a000c01d0300d03643c0380780044454144c0300030910380c46490201c2026081c01520240ca5001e07040c040c1c105607 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 25584574 1250 25583324 25583353
    0x60a03080307050d0605121504060605030304091406030105040c060e040207060612050d0f020c0f060c0105010e040c080714211b0a0b030c0301050d0f0503120105032e020a02 76
    0x70015622100072480114000d8400207261040a000f45000c6880601280d41c3c103109a8803140c8a0140e2820451410006802d0044c1c80d0815001000c01030b044a9440d03a890381a0700041111041d49600c40c00400040384943c50b050240601a640100300041c1c16490003506a0b4ac49500c18001c46e0426000d21160011401510500000300454010f00b03002c2d50f80340c5495403c00c00a80040e0041c415000343c000081680041c050501c0305090300c0c40d104d02d07044100013a44034062122110601c0d0b0a0000109050b0b6560b1500c0d07004501c1000d400c0681c03900d484405031038450b00d01440d640134080006c00d00f83e600d450310218941e401c08805910b48003004110b510300b000858101942007a03080091580d481c00c050181d0401480d05040030340c19800d1000400d503407480306214803485000f40c103a000c404d100100504104807580001100e58540d0084005015a030092254a00c207008529040003680b29000301382d5110300502000002c0c2009201210000390401b80c40034003144540d00d9001070f140b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 25585824 1250 25584574 25584577
    0x5010b040504060e0616050306040f15060201020703110a1502030a0e0a050c03070806010b1603120218090c031501110c060c010501030606080f0703060b0f04020d05060102010c0e09040b060a0308 85
    0x40e4040d22020800c4d0041410880c076190014042c0059121600000c03142c5643c40016660008421140840e01c0820540c4000c090001c0c54981802194101400105107405500901142c0e100307440f001d09010b041c0c010142c44810202025000183c0c4a0040d03088a600394000c56201e114000d00080c82c6c3c0c200340c2054501600030004a41c55840a0110141e40c035040040300010f100c1030008159541c10b107103070b2031911700909520361400c60202c00c1070020940914012003000704802411510386118038440c4103650040704149004180c143c012560307105605049074452102e03245194560700d0000011104070983c2600089203004180c5504d40d280d9407400184041d900b0840003051950443c10b05604a5640d40d0100845501c1034020070301110010404108481c0c01c044005030450305c0e09c01103952003d80380085503000748005000600301c03e0590201d4041d107800e034002c0121070350301e0605440c4281c0703240005074424074040000e000680400c00345a40804003908807203c05a0304c0d0f403903000c84d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 25587074 1250 25585824 25585831
    0x305090d030302072003010509210a021507030504020112050601021905240a060807050109030311070b03010305030a020607080606041a040503010e060a0c05070807060b01090803040b0a020111041d0405010b0405 92
    0x90340c4170281d01d13080303602e024020150001d090b14044d040f5549113810040f8501040385002420220118034803811900a00011644101c122800116071501ca03000800801040320101d0214a4a5112944146040c070034103108400607001400302c40300c1e02c8280c2c0d812261803402280c02d03100384004410b201301184403d00203041046000c1c00c0d00d0400c0c06c2c03000191910360700040c82950004400700404c0c1e90203400b003800c0320742500308175000213604003c0340d044c403403a900301010100c4000000010814000020200d6078013560a6445544036150200c45404040e20b000d0760042041c88180801100f10700d0480c00030000744001450700ba03441010030f080d941c40515103a446e030080b800f0004c0100035070280e8640d1858a00d0101e103000c2c000d5542074420f008044000d00165900c0444181e183d001c0d000500c060f21003003080f0381e2600e0740d418a04009920000c0031000550a107851200340750782100c2560306544400300490b0000b65660300b04842d420006009403841d40d22015503100549607885103d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 25588324 1250 25587074 25587113
    0xc020a030203030c03070c090923280b100b04090e0a020a1707061106070305090a05060414010c08090a0605040203070b03040606051807080402040b010210060803030f0c04030305090d03030207 84
    0x32580c11b5810111860360882d0300c1860503600301081a00014646080903030b02c42ca0210010307000c803c0d810b0005181c5000c0140c1082c490b006200d00091600c0d40a4104c042c075845a11401202e55a208011290072454403401c161100c0c01e000c00c0c4007902540e0040c8214140302c03c11078480099503000a418807040741d01802c3c040c25000d1000c09074190a102f00409001141800c20b0101c190750070481e40c4940c0104901c08040d650404034010703040500078907400c0b94001007185c1550605003407080c061550010005031540c60a100c410388580200c0341d05206801c0320300500540075494407060090007004000f2607040c01524004104842d02c03030044c5014a014180c0047d8942c2410140b00c40c580e4130607004894180ca22080203c8254031821080e4025415140442d0030215800181c1c945075182d01d45000c030a050080c0440c448038000091840f80001851040f074680310701100050500c502d000c007070300046040100813201e0509402c00c040d0346200e407400520307042c00341c0c40308040310408410604 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 25589574 1250 25588324 25588327
    0xf030109051005011d07021209040b030d02010b040b010306060509090c09030a030207031208010308030613020c030a0e040c09030b0403050906091210050105040605030d03110708030f0403080703110a0c020a030203030c03 96
    0x4109101c044615039800030300c034405e8455081c1031001075551805441e80031010000099200c4298440d5000002d1052002e0101c446c07510120317101a01810004804c0340c01240340c030440c074855612034003640c2c0407282551100c500d08040041031020010005110036013000080149000710b44003004244c8105000754042e1582c60300b180741008541d034400203200100701001006101180c143d0040700c0d0041422940c00425070802d4000201034014a4420326060202142d90825683c0109802c000c107502202d042108011102e0142c5d440302d110300005d810301c145100087d000034000c0b4014091034600a00d200c0c10694a5800607030540c20200002030190444540e43c0e611840318010075000d0041200c090018a041c100401c2c1e0b1041c440c0d1144042548a585109007081090100d6050310340040381c0c5070b03480c541703e54920b410440580341280001e00610003d9843c03132082c400d1010340e011089040b40744c820b00020888032100c0355402a030740a07a10840010040c1d408000800b00100c422000c0c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 25590824 1250 25589574 25589579
    0x70b04030903030201110a0801060e1518030c0d0519050708100207050c0d02060f0d02070b0f07021009020d031124150301060f0501320d180f020f03010905100501 71
    0x1742915045820803105c1d1006000c08000302d500118402e05452030391600c4008103c9d01400540800703601c207240c92a80900040c583c03803202d840c503a0b06030807000c280e04641819820f98217009501d0309400d809490754014021703d00e82da400d48400b11940500820032600f001e901e0304281410058000540c2c200e1550001e200b1007000b00a018281c03030400211060050701000381c0120320b03103104d0070044580b1b0a1002400c000712500c41d90546050f1a04042004002d140c210340480c2c01ca1010f0f903d000143c0709e031000e080c206001d207018810f6465801b416050240e2140d9500751400a01603800f1501c03801031051410b841d5603412010b4841203442540300682e403e06503805401c400340340201030300030b034140041808a9070309a100e6904031442883d00b5400c1c1d50403040b618140004c1c203e03000701704e121210442781c21034014038040c1001540070101000200a15041103a008a180c08000c04038500e41440c00c0140c5003030036610900d01000307070010540e070800c3e6580a09000d40c00b0707019042c039650b03103005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 25592074 1250 25590824 25590827
    0x503090f2b0b090d020a020405070210150305010605030a0c1202060d0c0c060c17010308030a0605061305270a0e0f01090b0f16021f06090f020306040b030714090606070b0403090303 79
    0x201c3d00308031200050201900a204000d4840d400c4090203400b650302c034808103100620030488458000c210a40811400e5000030b098202400c2c1884103803130640c200f040c0440e1500c0d0204030f42d201c042d030114581695600d04050304140d200030716000d981c003440501004009030303642c0c06000e8140c410341c1d950142c4080d0920313100b021517402e042c5803010080858101d42d4001c00c0f12414905581d0031040e5a510396031030f1503048015000a401c0103400c20360115100605409031240302082e22011540a0076039100320340d8848240302c01c0c010403090500c2035000b00e0504101540043d40d034003040b500362084000e0355580e043c00d5840b080c0c03044130010381c801e0420000e00c00e61104990001c4110010300b111104185000750f40d200403143c00c9005461000c0d0f58003c0c013401d0351240c8004e04170104180040c024002c4010029082219418000c80c1400c20303e5805103408210300b000c2c0c8001d0040c09211011f40c03c00d00541450003080c2c0394204000304a0000030400310308189122700d100365111508241140340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 25593324 1250 25592074 25592093
    0xf0f050705091014180d0503040f0e0916030201050a0905090c07050105060301150e0705090a06031a030106060f03020a1206080c01020d02060f0403050a0c06050a05100b070503090f2b 80
    0x3c1c41c1c401c00011180c074200c501c03010030889280c1501c08072a144c49034103040000381c050620a000030510312002400080c0d00c0003510118007101e44000c2c64180316515440c4c2d190f16072561458194000641000a100541c085d0307001d08580e041519240003c1134a5a0108148903000d4590800f1007002044601c2001000d01425a200d00150700a1084100010300d07014110240e0051044440d4090300260b8158450000d981401000134103000d03100d66101009001094061024019108103040031522401c05000b4881103410559501c030705004001d1085000703400480140042007059080c1d00c02c0340c11903005420140600d0700c00703000f8a00303200d800645085043d890a01c15504850104115000301d6094170354490340604000ea640d03854141e007214841220300b0000d0000d8680810700260ba42d05a010510414881c1940201a625008003078254051108000c109600801a000050414086e290000c450207040b6829500a8503030003c003e611404800044180500c0c5020500102c0b65 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 25594574 1250 25593324 25593349
    0x30b1c020a050d05100207030801030605060f0907030b01050d060b040e070c0503030105090c0903010f0c081b09061305130504030e04060608040b191103040c080c0102100f0f05070509 80
    0x2404584590129400308491894910800e407240b0803010400d01800410b02c045000039540c401e0031507880042d0301c4d010700045400e0209507040352401c00010703841e0508105011281e41c008012010300c0d0791b100c0701103025018440304541082402e00c502c2c04502001d009080140803a000b003035072101d0401000e8550503100034442400c010f1441055004181c1c08000c030f90564400b5900c1196564401c00c000360b251281c420340715015880c103c1c000b011260705034000b080704815a9288943c0c0e80f60280c58003c610b0116090340500394080040012030700d041d40003402c1c403009030080c0100456440001411100032801c0100032180c41c1c40411007015480030340307107408440480d0704204043c200f0a0090400500070001000702c15144046200604044e41c420048019034900340038108600c030203190f8035041540d00300e601130000d4078041600c0c10042002c0c02c0340c14041c0c3c02800fa00d02100d400401400b940c003003010800f69a41d5500d00f5461340c0c0d0288503c01d54180d180c0d15654003000050084424140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 25595824 1250 25594574 25594609
    0x21609050a0e0706231201120501060b0c030904050405070506070302060108060604060b090405060a150203040e1005090417071b060e01030b03190203070b041d01120203070b0a020309040c030b 84
    0x501d41440380075040000c0c13036202e4080c0e5010151440c0805d0600150b80704a120810000d841c400000420076201c800b52140c0d071744100c1c02881403541c3d401065505010306243c03030281e500144603030005403c150340466031160103441203078020340c2c2d80c1c0e0120380d072503000d640241c0c0144c10940c018420354208110140d04104281c90800c84640741a40a844034000c81401e1403040d51100040303405565000d040401401e804001c0c9003003019142c0e0301030360301c0e4090701c11800d0241c2c140001842c0c40c2c860036020307811640f02404c682d1066440d90b8400100380101b040d4015500003c0c424034001c500010441082d945d0018009030241781841c0d0081e04c50040046080d04040c1001d000804a450201c0c070101959540510950f4100040c40080d00b0640d80d5042850308000c003207800503400d0121612030b5403602071011038881d680d899101080c600404a00069003646c4042000c00005034210b00602e0401500d1064a003407020140c0020300b6503000501c0580065107030005220189490b9205240c2c1d000384 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 25597074 1250 25595824 25595833
    0x705060709060c05030406081f0e0105100c0503030c07080d02040f050901090e0d080a0605060304060b010314010303090302090703090506090c130b3d08090105070302070803040f03021609050a0e 85
    0x269034031303180c0c0c9110368000c5d50b0030040a44003003140400c451407004162022401d101c401346441c1d003403041112009115641c0321384010048880124002d240140003280c01001031031560340c1d40740c00130105070700c41402180c00b16030400505103082c00e14409400900306030235421500d1440e007400c116880c401030b040103583e1441c3c100040281100007815038185002d0303041070415075849441d0500103001c075610054100700d0000c100000c111503544614843c507406d1700d04000e03880002d80010325500c424040100030603207040052000d45401032030a9440800340c40c0124910490369212428241d0640303962105a11546140c0000e01e040340e2085041504244204049403902c400074002e1a04800c6c0101c441400340740c50800410360140680d81c0c1d1100203c1c50103440345181d801003010303100303e806a2480d441c00000c2114988a4001c9800480e0001c1c2d0140c00d40d1130742e03100c8003108842d0800032010b6215000550340e16200d5030101d10002c201c030007000101403500718112000d95a400c035400c04690032 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 25598324 1250 25597074 25597097
    0x1170c130905071b0c08010c0509040510030f06050613021b06160e06030a020408010c1d0108010b0a0e0a05040c05070201020c0406030302060c030901060e040606090c030b011d030a08070506070906 86
    0x1031007100f402d103500d2071070505008138410b030030901d07240f640c9908490025424100702507066900500244007250b000d80d030800441c0d54694141e814441280001000000150040c0006c60469085940c12400081c4140c0c1c143c100012010200c0e884280074421001c095905101c00001c184440c42c0d001c0f41c03000b440350b511500207000415655400301418452600480420b88034012681541c024001d0b0344020410380c40c00810107400000b592018070400075008403060343c5948100d50f024101d0b855505428200b54030300d034042c1d51103141c00342a55000302024000013030741c0d607940c041d5035803c40064681a035610042d0000a042082c80f0705800c0c0241e00300002040020750014566501c203c3c3e914100c1c0c0c0300e0711406101405803256070b2180ca45e01100006000610555a10060848404000c104441c40300f40406030140d51034a284580480c6811401c1c84848200c20304503c81210010299100150307159103948442c0c00680e000c1d00c035a44094100041d41c0d8111110401400381810040118403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 25599574 1250 25598324 25598327
    0x80402010e040605092d0a2415030903110601180e01140604090309080f03030618060d06020a02030c070902070c0e130809010c0b04030309050c0f0a03020f01170c13090507 75
    0x8001810007540a00303814490600021402c00c13090741a11346103420145410036030110005408d151600049451100c0c042c0205140040800000c079100c00f00c4c0c0255016040324150018142d0302400c1c2c091010000c03030307000715500c1442082d000c1c00c0c030740078501da0307002031000300404550f030f818600c01c00d50f03240000589204003011200740d40301800b103070049450703152490300700c0f200809a070008001c2c0c40f403284d0000c145800840034511500041c0e50740700c0d100b0f2201480d01001c0405a42180c0c10840300703508640895101e0b00208404d803c42c5c012245010818880c062414242d903024904140d8085014010004d61401c4030000340398078484582d080c104811082908003c3c0c250003412103200158010765031340541c0850f88580e4001c541c01010340b0381800c0c058051710101c01c00311020b0050a144460038a03160011401c0313440003510340c1003007600716801d00074005c080720300c028107108070601403080c050102d602d003034850304c0c264126a8840382d2480444030002d440390401c04110b4103060801900e103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 25600824 1250 25599574 25599589
    0xa05092e021e040605030103030806010806090411030313060305040507060507030f05070501140106110616020304030b090f0303130605090a0b0604050a0b04020f1b0a05030f0f09060a080402010e040605 88
    0x803a800c0c2801a40e070740412141c03011010800c640c5190b88000420002209034204020718100c0380640c4500c07481e03075500b50045503001c0307081340d0a90f40310b015000810701007102c66142c00b10140001d800c80f40340080240000b001c04000342d00003000207450324104000c00070244203c01c010482400c1c400c0c185411a80e01a000b240443e00e007604210011840006011003500b02200503440344410340700710358482400604001207a06181420b00c50320000c20b0000250511044241405030b0155003058103544c0d51042d0044040e050b0541e80c89040d0701d04000902c00d01c0218020070030ae114030b40c2624042e142050545000030444002608828030110108144415656202008580c0040c1a50394440f0007802000e44028242c2c0061012494030003400c890f80050213160303d13010103911061065101c00d942e4900301c84004081d60002d0140e10365903000580505500440700d0344a6091010740804600c15411008948000604510500055507000707200070084c0e0f1010b4400b84401803c0401040a1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 25602074 1250 25600824 25600903
    0x12050f010e0411150a030510080705040c120501080d08010806060d02010507050a150b030c0604050d0f0c0b0705010207060f2a051608030103060c021906051308030a0509 74
    0x521410000003800c00505001e42e962058004020040382a08604020340300c5d0850504100845d00e05008204204200c885200403240044001e0a40703909000a00001d4401068040d052107102c100b1940040ca50303005040c00307000c010b001442c66030581c107401026014180d12508140d000702080c00451745032041c58803241e6030203007042596000a0714006240100034040a0103103048440e98105040d011382103408445411812240400203030002c01005108038860360340d1001040404400003080c004078454824002d065552100d80d45890040090384001c1003222642d60010b0404108401881604d4001a042d40b0030010200783e100d0203a00c000050344120009150002d804003040c1c401d108944990b403915000d0a8400d130b032841d020106030403c5c04111a00360400c0c800001181c070000f1140c511201003611000a00e510391600d00003000c010f8801e00112507141f04120104090b14011406100007040000b0307545001580c40d8140611a00107010590140d07802205003052030130038108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 25603324 1250 25602074 25602089
    0x2d240e010e0709080609060a06080304060c060f060f0311011803020d15020d020409140601080f040b07091508040203070803040b1e040503011803080c090d060b010e06041512050f01 79
    0x3156141e00c0c2007901c0030b03400755100307216502c5000d0802c5040c04012a1f0140204031002003842055182c000307154580c00340740a00000030b00701d0b42c502008500c142c0c100c2c0030f001c1c00e000d20000e17400d034440b5140070f0250141c0c0c0054900207201c038114113441d6404500390081c5400240c0c440c4980303040d5400505603484800015010036041540d0608042c5140c2c100c6101114071181195120703594181e10018203045250702c042840002e000481b10b500489001d07101c1d490244600300903503102ea4a10114400c0581110100900c1c08004240b0000080501c031680c0c2450721190300c83c2c81c0078410036142003a40e800481042d001030108201007907110003560303541c2d0302108040242c5003c0203885180750045a025541c55820100c1c10b401c80802902d02c904018001d94400056940c4d80c1c004407241d20500e224103400146202005012465581c055003180105140103c03030420000300003441c03074000c3c5c0c02a03015414071003842500f03036130486050110100194020b01c001e28151502800011052040d0700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 25604574 1250 25603324 25603349
    0x15020a031704110904060b1011011113052e03050105032109060a11061003120306030201020a020d060207020405090d110c030303010522060b0d0e03120103062d240e01 73
    0x5c00704403054104142007500036000c0e00340564a850001c064200301d03c03200365654a0120080342050a141c102c030b88000645404452305480c00341440a0450a02d1850880c600e504800000e1499004111100c031400740e075000c685541404101070a150807203d6a552140c4002c0305c000800304800c00750b40c0da062045402c152034a6042c0000d440c2070351511b03041403040c0941d004000d0714005c0044020f0a49003d5409480802c402035010b44c12140c2500010f800743e404100705100600d84100315a000a208020142c104070007503020070240e03030065980d0340450b00845540e02800b03a1140380d004144059400a04030a0090800300307032244018000d03103005210800610900321250210205000d0356804104407403665519004100d8210a480c140c1c0c690509980008051002090b22442c40340c2000d46043c2d0791035907a901c4010000b44407901c500c0c4480f640351503011882040e030381301d4101030101c01060040c1c07c03100580301485e80891888003584036103012b100c030b0025486647c4c1522541d00060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 25605824 1250 25604574 25604581
    0x41401030e060a0f021606050702070501080708061e0402031003120203040f05040b0f120102090301051509150f040606090509010902040b03040303020c0a020a1401080c0408030901051315020a0317041109 89
    0x48086e10402401d8850300d5040c042e41020001164032480c41900d586c3e0030781d0f10441c0c540004403002c032025540c00b800901041c0103d040c501d000c5c5c1c0804002c01d000e16410102040780d00105d02641c0048845003c042d0710180e0801c1440040904020100c0003807014500e054100100c03a003184030540105070040b0b60f11807000141da110762013a040c07a4000102590308086a880b081e0340030b540030b50520b41c040e50800b008903001d54200036450340580001450f5101d1030b500c017191910f83c0902d40600d9588540d02d902d100341903480b03d1040c0c00240c40940d544181590402040c40508541a44806441881088100003001c4d0080c2600c0c0c005a0624001d40d450b00c5842105103003580c4c00c400654009088040018600303510000085903032030a0f00c9441003940c500a0101690045103c0d10b610b541041120003005d602c6103004080405150820442894446941c0d2a2070308003441140050381c4002405001c1c150485a60b611500540000d00824a826600c0030907401c203181846000300304a0020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 25607074 1250 25605824 25605851
    0x60312070f0501110c07050105040e07121410030605090604120f0e090a020a0305060409030206010909140303010e220309120807050607121415010503060109030503040902041401030e060a 82
    0x1180a41c1c00030004d0240c030340350b002041c04551140f0322101040c13243d060700150342c2d4050340c15141101c0ca0400107154a40d41c2c0d240503503541d071500c2c60070346110356290228406502c0d4907180901420f5090707010006035046242c0f2808940300034002c8141544910304020018158500015071088145400b61900e15008010f8a40800303030011aa84501d41e42d0030844000c0b075503030142c910080107540502a80d01c940092008a40002c4005001a0401d40041c4000840c030307003140780700b1403090b01c0210000307000f080d016040d50400c1e08040c0c140201030040c800494000601020003804c2300418021141c0f0300c1d60098840701041c070030024003040030311101090100d0172050700e0341c0750340110030f81e8014542890020404606001e29615031403500e00641d41d8000710b000a03030310580c0c41030500700d03450b00c80e40015941500002d10250400103210b40110020340184040c10003400d400e8405600c881c05d040b003801484c10b503209802e042600d80307078500480c43c100081c840d400840c074041c001407010a5010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 25608324 1250 25607074 25607093
    0x30a0b01050607080d0c021b040c120203100909060b0405100605040905100b0a021c0e090414030903030408011a12030a0c05010e010908030f0a05010509072f060403030e0606031207 79
    0x40245c141c0c94104c0040032030b600840c14020100d1a40c03911814482100104001c540312012400d00058003000000903032036096000b1500700300c40441141116903a0340541c0141c03110100704446058403500c206000d403e103800b58503003200c0342c0c0300030020a5043c108024140e0107144984400c0940356000318008003807100042010f4225005203517a0744c0610000650755110040c03508071040064084440854454030720141c5500c0028444841c5d9196a2940c415440c1c4640003040140400c224080041c0e900304001d100070301004001140e4440515580080c3c82c0400300c219000d9458500a1034003004040700300c42c0780c003c00d401d1029803101c81d800c1c55401000380d14401c00140d0319107160b010910440201441c45410800d0400003a6590b510074103099440a109007038008aa2101250b2001c0c000d030b1186402d0054280d525021650040d103501c0d0750030340f031400c200d0141c000390b0512040c144c1c14088d40c009981200300900c40c608080300401e03038a141c988042ca1006030081154002c0204008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 25609574 1250 25608324 25608337
    0x30305060f090109020a18060c06050405011d0d090b0901080f090c030633030a080d1401060e040c09080705120307060e060711070608061c0c0303030e0c030a0b0105060708 75
    0x20b00c0c0440302c2d84c44400420095022804a43c003007645000d690362045800655201501c1403030307a43c1d015840c510354171800900400341c422a000d54843c3c440d1814100014035541003051900c005146440c5105000303080c4280ca42c02c00311046500700140181d6981040e00140c2004072280c0c000700c10b0380c3c5d00d62030a007840c1227481c0c0e45901d806103605104141c04025660001d00300c1481800310000110f440240c0d03001400904c46030180c02c4006054081007003180a040403078900c82001c248401c0c0130100c421168000d80003200403d000241d96641400c0920416500840a0421201b0142054150359558032240300e100d1164900d034669540050061050b030320750036840321041c01190000b8407141e454090407640b9000040d403000411182c00d000150b000c0440c0c0107a2602565519060184a407280030420240001c21000e030007000040d100c3da180100079802690b00062044035003582d60304000035072100c1032080d1702202100001c40d446a000504481d011580140e0714165450b01e84018010017 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 25610824 1250 25609574 25609579
    0x80c0f010f051e101a04030f030503010306230105040c050d020c0c090603210a0c0209090a0213090201120c0306030c0f1e0b03071812080c1203010b0304030305060f 72
    0x60a8450030701c25641005015640100003403c580182c3c2054044148086039919004c442183c01017122001c882d00b001488441100340300e250a48a0b1945035014420000031000030b0000801001806804d100d00050891000800c5811420307144e4581000241800b5140c8102e6540c1c1034040740c00e0041c01241c80301d00171248155120121310040f00c1c0c840c0c00351031045004290481c0051943d20b008101c02c0362050a2199581c0b014401a015102d981c008091000600c100c02c025000586d603044507440c820b000c1e1800400d101d501901c18044034001c460010700100f81002d46010050381c00c00100004c114200c130001603090f850800807030140109078006008c1c1d0446181c0800c0070f02d5000c00c450142c5000031001900da43c0c22114040c29140300b4403500381300350014800300340801e104a00f19a00040301c10009100341e40c4a00010b03100305450b01c01218180390001e100c1c44041020301103940da12003c8580103086600d030507268071030307440010802000c06540341d0000e0000c0c3d461203030420207540e01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 25612074 1250 25610824 25610831
    0x705040f0306051b03090d0804030203070b0108030a02010b0a050a0603090c120305030103050f030a0804030f03090503030a020a090e0906010303050c01060e040b0f10050a05060705070801020c151f03080c0f01 91
    0x8900b4482d0092000b0f580d556500d0480b08601c1400b40b807154200c81c05403041c0d000620b507001044d00201e4035840301030400c8045000c100007000204e080c2840b514046c1c07012101440c0c0c1d400440b140079013100c0d041440180240d02c907040800031580d90880340002c6482900b07010a52401d58034041c1c0b12108590001c000c00d10398103131504140360340302020358103903480340040707a81c43c4008403180c03640c3e8000e682581d4001080303d00040c0029100d101c001509020b241800300d400d0300c065660300c1c1181c108580d080825a0f001c1032240a00398403011020042c0b03042c0744510140e05001d480c080e2116414040a03081c07000c002000c3e090140254485801402001004840380c01d0500d004e03080b000d41983da90500d403076081c000c41d040034014110081101c60040c1500600d900d002c00340911030700209001e803064022180e00054125080c0001c045903280c69001c0e000b04042251042c0981c14050490380d003203a10f407984105460606618881503e40080c115038a99001052062501d552280f41080315400e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 25613324 1250 25612074 25612079
    0x21605070302240901030e0c09240603010f060f11100501030c0504050f1504020403020a0e040506090d2309060a0c0c050d0506040206030402030c0d050304080709020403020f090705040f 81
    0x601090a005582c421142c15002112040351040325035014465105001800c1001059940c00303039008414200d4080251140b55444500044181c9400c079500e48207441f101d02e11140740c044444840c54109002c031030150031541441c0c50040c03188964007481c0203000344214000040e81c081c10041c8441d030200003c40c1c03d144110f41405024100c2071000b11040524038001180f9858a402800c0c400ea05800780740c00160f40d07003000c0038401980500d07140e400603401c210200258464180c10750140c80c4800a0311000e00b02460140c2c074250008005a99a07005628808156507100c0307820150204c8030b0840c06d0002e80100c2803209580320350a40282d12002c00684150359580140d03c5002c680e000d060b0702048a69680c00f03104040a2101000380140c002c14006801440e2501c09541c1040c00501250b03104002e08021410703d01000c142646e1039880481c041126880410181700501807445056050510b1940414044503e90070380c01d200c4c0d8880000540340e20710a8082d01c0c0181200001002c140c0d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 25614574 1250 25613324 25613333
    0x2030f0d0c140c0303060f040e0a050102030f160c080703090902040905090115060203040909061104030b10060f05030708090c040501180b030a020a030f06020913020a020d0804030207090f0216 84
    0x7640c003603548003058000310302c49048420003082c3d5803101c0c5044040c600e959100400c000860f507911140d035a0060f5110000b0b4400340d020480c15020340d214400040e5241084000d011010b00002c122410541c40050120102c9610603010006642d00240003512140103140944085080790000d405843c8045170000c1c0b41d91072500140d0180504800810001000740030b14004902796005d5000507a1081008010188060303000580b081d015a0001854041c61381041c5600d900039070080c5c070602c0d0009c00b8060405070a406200050007182080203d006d48000d0103400e07404020041c0c0d050003003d9000450400701071040d0103c00038024020401580c44620000e001c03a01c0c030440d1510785183c4400c90440307080001d43c4240e40e0b07400070080090640b840d03885240542611358202d800b181c00707100303000650701c40007108409580300c81005a15101c83c1e400092910100444400401003420113010101c0d8001c94000c3c01d480070710101191104092008401038031034881c0c01c502c80000030702d0810910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 25615824 1250 25614574 25614581
    0x3080d020708190e03060106090b0a030f0903080118020301120b04140607091d0112081312031e03020702010e06090103061205030a0e0306010311060307030b04021308071a03010e040302030f0d 84
    0x143d01d54461105540540c02415900c14090140802290030800d0074801110703c0c4c000f9015058281c42c0c0850224070445080341681c00c07081e822400305034044014000c0c8030b100346c10a058041418021801c1d985049131040c2008100b41d00a050f00e07203824042410300ca0954150b1050740122000c45c2c2403810054070080c21251544924614262024004c92240d1302ea881e9030790480786544038081165403142c0381e400d045c0c2c0c00010440202c02960030f0010316454032807030507282c9074001c0d150107100e507804d01c0e02c6a00c12038541000c001014410040900141c1c1c00000311016020300362401c0307840300000e1005800900b1030760000f80344d042c12084000d0411600000414501200d56900b600700d040c50024199102c07403e001c020b10f10116010300c0102c50034610b01555015032145000b2407040c0320240841c01300d910210b101d035003100340284180f050000400480000703003441a1007002c10510134141f081c9038003040c0150564801010007040a161080050340d0720102c010446c2d90381d9090b481d101c88000d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 25617074 1250 25615824 25615867
    0x3020706020c1f0902011e0201060e09030a0912150e010f06090e0106090501060c031101110408011a0316120213020f0403170304080a030e1c17060a03020a03080d020708 74
    0x80c0c1c54403103c1600400040d008a040c2c42d40c0c180c40d4910904100c2c5100341c44100c0301c40c40c8000b10f42d0f030340340000b0b54950f21002890050702c0102c0916600c0210910080000700f0300e0704040c0402c07440344107500008034400020000b401c5850b50018004900b034030804d026150388980815070900b840c9010820032034a920568400c44450001c108140c1c1e00d6182005444007403041d280422800040300b0080b034041c180d01859514a80000500b99a0307402541c241e6400c00d03040641c190b99603d4000043e80c00c1411810055202140104001104200d240c41174019a00854041810f1804100e0854031142803050f00303d08851001d41d12110113110240b6070341c01910054585030400c0212510460381e0400b1240299003000499141c03a0280300b00340c3c05010154034048070391045500031503500c00c0b080701c402e565040c55134925582d91202208544010b8015203154410211500200016542c0d01111400c0b268805401911041c680d16070f00024010a40701620301c140c000f9149200f03000c688000000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 25618324 1250 25617074 25617103
    0x7020106140f01050405060a18030803070215060906011b0c0306020c07060f020c0409020f090702010c020f0c130c02120c06100602032a0c0301091a061806010f03020706020c 76
    0x80508075000c21010007800761225012800800040c0200e00703000b402491000c0c0c6a0500c100c10302a02c1d240710b04418216801515000c038003109026456505014150103044804c5491f01681840d2000888160000e000765042c410a600c40c3c1201c1c514200003100526085002f0301195a524200300c030107503012401249042c0280103010542c14002e9002c404a40d01c264018002c0c407100e8014400209000ca8003641e00030b43d004410b400c10340d6681c440038800c0c107041e80041101a1b4810029151411840780c0741041e8005000100b0b068450710140b0740102502c0b40b001c20207540c030311b40580c00d1800d405000d0302004030024090390800c00000342280295500450701c0c2006a60f07100880e02c900440e0031508032040305078047c050414544421500101032001a1802c03101d1a0001a00316400030100b107550a041c40054112a0b40d01c46d4120360005007500c01c500301d42c0030a9115600c1d890018540b80c10302c0b4899610300d00b500c2c0301ba8151072202c0d900000c11940c0348600c0e41c65503501c0314481803500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 25619574 1250 25618324 25618349
    0x12070b0415020d08010806060d02040b0603090c0a050a030321020408030705030406081003080313051903092d090213030c06030203150a051003020c10051807050405010b0f0a0201060e07020106 84
    0x43c030f481a0142c1c1e04803950700d009080d081d00d54104000040ba0b040e042681e01c1621405203c2650b51910011405521720300000c0400075403d900340700d40c90940d43c0c0914451b140e900f500b0000310303401000d840505051204074520001030000280b0003405075400c11a5144804210942081400401801690319070f80720305110b42d95154080784c0041c41d500000740348031003d1021440fa0175222242820240c0301d01d0948108048001030340700d40402000d002d40011303420000400420000d40001d010b001c40c00844803440d4039403500c040c441e95545119a18600e075000400d0804040c1900d008030142d03600003203d007951a0742d64402800303500300790307504281c100034051203880b00c1c1b600e00035220458101402819400845050503402508544070b450324074003904010400d03005640c032441d032140000325075110100d031483c2425880c1c00700c240c00990040b0714080042c050105500140c414900a8a2409680300040e5400328094000c65002410000f2800184611290103409c01d405507800c640b0500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 25620824 1250 25619574 25619593
    0x30e0102180607020a0302150d051506160c0b0304060905010b030a1101210203040c080601081603171315260a0209011107030f1e020f12070b041502 65
    0x16400c07486907031242a06003011403220302450a050000d0401d641c0024103410145681343c001c2090a004220754074440000040c035402c081b840c40c403803140c0103001460300310344a1120b0b90108440344200390f502001c01e4200143c010400031400100070181c0648403556460b0f0501e880c2c24800703840194003c88243d42402c0c4040d100c1c0c00c000459034207050304920b81c1c814079900e81d40103444032403250640300e01620340c2c0d5007402c0290340716000460081d0310440030510345920b011038050a080060700140000e4101c80c0307402c01d4406058034108c007602d400c4071212402d8010080d08107042d101d030301c0080c0407181030a94001001e0040041207100140c0ea501c485004508401c00400b400c4210192520003040100c042158045990f001e4961400c040c102078042a46806074246031040c20784c8101e40c007410052054040014002803800c080445c04407540300749516600080600140406043c0184003c0411900301c103c00c0026074014103150101c1951940c40e003103064030f48002c44240300054411200744 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 25622074 1250 25620824 25620851
    0x90f09150209120d03020306010f0305040b01090c090504110d06050a0b0d05070c0b07080a0c020a03090e0702010b030f0109030e0105030903180f040e160b130e0a0b06040b030402011107080c0103020708040f031203 93
    0xc43d031050354402003b16640e03082ca8441801014082419020021503110114090701c0324401d034000841409190740c2c031344036003590400c00d5445d9030704054040c8514542c10048440841d00390340c14886100710211b04c0760341c1e1480807511000416000f416404115050000c030541240a1074044d000114050100b00340102c1d05036550403400b0401400141c0454080000c00f641e0000190000341c544004261241e00400091030302402c10349404142c0d641c2c0907298105900443c5034214540203083c45411403030480715154a0380900c0b558603081540c0c00c1c0c00d2a01035174031035010504a00c4000d10800c078201c2c017241d01c290740d40d802d45502c10027049001008200c4207c0741c030a807102c502d5180000c0040e1410300800b00c01189000d02919042c0e51104000c1c01d46640e400080c1c0b01921510800c191a4501400010994030100110b404030b81c01640080c8500388000c1403c0ba01c80c5800c0c03c0c003584d42c003030524002d94588110b27803000400940103007021082103901d140c042d0503a4a2a5828094441441e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 25623324 1250 25622074 25622081
    0x1b1101060b180405040501060b0a02030a0201061418060d080414030c0603060906100e0301060308030a0506010f0801060c030c05010f0617061512100608010204090f09150209120d03020306010f03 85
    0x1d00e1000381010003101c0d0b064505a00075a80c0b0522540010840a9840660200940142a0802c0980c1010545c3c580c960740c2481840000c12105612641d035551a2010070720b440c0d0303800c441401a00018001a05c151180c44482c000301c4d510140305a56156030b8000c03160007481242050780300b4007407461401c0c001d02c1c11a082d28000c5c84014540215034803074404101c0001c4200158606104d9085045a40c5e0390b400c1c443c90300110301606001d692840c0001c014001c55100802c101e0500041e040000b0840d5440400e040c1924500d0410342c816403401c0c02e0070f80d502503041000410660034020b4004180f1005e4100320100c80303100300007d0315105002007847d2240c1d012a984185902403c81841851404240b080b1543c1c40b4001aa03640d60b0b503140c0d1aa007510b1071600840f80340ea40020342044618028803034901800e40d560410040100a6a105100c2c24a410040c103076454001c65200019610700b4050f1030703064111001c941c499800000c0140203034204842080c049500d40b0b0400351210b02900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 25624574 1250 25623324 25623337
    0xa1701030206030c0310090504060f0516020d0e060403060227010903050309040b01110a050706110a080306040b0f030a060c080c040501050703080405030405120c03010c030c090b0a031b1101060b 85
    0x10b02d000e055a41c1c11140d842c040c2c000800601e05032040050000350701526110307280c011070040b4808245200561080000d40344040d000090030050700701c0480250742d002c14040341c01542882e09214015400f00040e0550145420103403007144002040311082c550307180d9065419030250b124030341103000c1c90015916507030203220161040d042000460702618040d40882844501410070031052114001004d1804001c0341045584d07074002d03401807002d503400801c00c81d0403500c02d10007801e68040c142e82e01c24a90101408850180c0c3d12001d040130696680a81d013020144090119401d043c4a810014050240c2803d40340104401001140031040c10104460a942c0e068440c640b504000b540e044400c1c0c00c0082c03080d1494042440702260740c0d5507485090380b8880c0544010651400001c00b050308549401c0c01401c181803800760900d21150300298440c017180c9949000300d466641482003030380604020604401e2604404072045a0b10b5000071811400c502c40e00c0081102c1b6440d0429449140f0504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 25625824 1250 25624574 25624579
    0xb090a0201200304031502070302060901050705121b03040b1005040b060306090a060905070e040f02030906060108180105010603050a0b22020706020c07030f03020f150105060705011b050a17010302 86
    0x402c410b508582c1a0180340503056560301100e00d0070303940c0d464100654450040080846800180080515604000c00b5820410203002004541400380000c1c000d4810512605080c1d80203500050b05e0901003100c010040010990450742c2e441d1500c0c0c071030940082101d01240d00381d01c404011500b42401d11415000e0540030b0501803864540004016400100401114890303484810220300c0e9100350082d0340c02241ca23912400d003a01440010001074031740c60f10b695496140f050007080800840020120340100082c00e1803003c985446d440240200c19044114000e0340c00d2800025071151301da44954401e030340411040204095202c100301849100c8000340d00080c403040086400304001d9401030143d02c4c420300005160400c104061410100980e20a0720001500d00c003000038141c041c00007040b05a080f9000c4c000703154234101410040034060068501a0a01082800811409511010b83c1c010f00c031680441030f034481c11009000b6400001c0400000b5845414220001d4001d80c0860590307900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 25627074 1250 25625824 25625837
    0x1406070c050a06020f0c0111030106020d030218010503180303010e071b051005070c020a0306050f0903130320190503070603020f090d02011806030902030d050307020c0f0a0b0c01090b090a0201 84
    0x194035803801035048092170b510192420050081c0c008000d200d1210f0004003180f0710780d100e62410002034101400c0103d2542803500400c00e010440745012a08200c511003402c2003604da450358410041d14680a207040d00141c400080081a2540412140c911a4689079500428003460a40c00c2500c0405004010800d038001161004654103a0700400d07440103443c503044c05082001c3c2c00081060403554026280640e03204180311002100a0845611004240042d4509001c208680d44440b09510024003080d58a042d41c003030080c0f07002811450b010004020144900024000300304117055803142ca4440e01c112240000c81c0f80c000e00a6450100807900709038100854142881084911401304a04101c00701d2001d0349000100003580f005800141e0380022001c0f02031050520380100b6180307207010b1010900030070140c00d90000b00d41064007426110300800800d680302060361080c86411280e1201d00100f030a0080e00e0055100f201503034061046180b06441d8041c0704c548801d800107002e400640c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 25628324 1250 25627074 25627093
    0x6050f060f0313050c0301060e0a0c050c0a0602030a180501050601110105010f03030507050f0f060106090501080402280b030c09011d06091e0d0609020f09101e030b041406070c05 78
    0xf0075000c016501402003064400c038210751400203003154000e8001c41000c50000d4144200c2014500c2880302d440032509209140404c3c01402c1941d0b0880c132800103000300c1d000000a41c2030310607900304540711800d001614007903070b04925146010304001c6800b2400544070345d44e080c03007002050007001e0484000c004000ca4141c15510100d070180d0040b01d0941d00f9120300a005d1001c071804205d19154254100090406541088001021503019501c140d04202c0404140005680d8101c46550304000700039042d40d00002a0104d000d8054640d84000701c48440841008503400c0c104000300102c4400341c5e01c0c000040c00341d048000205413104012a00704100b4098050941007044024000c00c54400884010750580e00018031844140001114802c0e11112a0f00c114103000d2010000b2001c2261310544510b40181c1c0321101d021302e4800c10400c40401208203005500e91940c00c000b030741d04030444090514040c2480b001c0c401e00300201c3c8000740b040100249030130344502d00c00042198008041d21900c0c0c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 25629574 1250 25628324 25628341
    0x1902060301060e06120a0501032105030a1d07030305040609050406080a0f0317072d02120d0b0303070c150503010e0c09010e090f04050609070b07021302070c0906050f060f03 76
    0xc3d4442103007034100c0f0341000f210048003e4101a180f007209900c0002c5819811441e0820803890181003009001c0c0d5902c401008154100090b29441442d00900240c20443d581c43c140a0048102e91504030340191704012052590103001002683c0c0d042c0c949148090751007041c0011244c440c403510303003181c204002c284001141900b01c3c1035598002c1c07401c0b440ba5542d048040398400f01c01c1d180781c0013145030b00c40131041da41c40d1441c0301191f5022564081c0130f982c1c42071070047e4031603e170125000d01c0c151002901e580d00000e0384d80301e410401d0340a0200e9849003540c2c07800303594000c0e0900500549600c41d00459200380d11a0003100c1c161200b403100d0b0a0386450700d2140307a201c2c1c0c214682240c18020082c2c00c51213a80c40e041c80080c4607000d40c41c0407103400c0c03c3ca42482070600c1c3c4064401e2003207400c080000d0141d00800011102481d030b050340c520205e4112081c040001b8000c9072801400072106a02c0003803445842d4200c0e90941310b00b140d58020044030003040001c24490381c2044041e40f14280700189640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 25630824 1250 25629574 25629587
    0x2070b07080702060307080103030f0516030807050c01061701060510090303030b0301060b0307022409150c12040305070c0902090f12210703080c0a090b18040f02030603190206030106 80
    0x100d00c81d54680381040030b241d001489a820848081002500017001001416030002031f0f1082820582042860101e6410304103903602040400581409101c6012500321481a0125201402000001c000250b2102c569501d100f07915a2090665800c0c400045078030300d452200361a40d041c56071901c188040c91350382c00754003400d501e2071461b0381075580e1580001c0d40304c0540000e61258040e0313400340444280341e09452010501419000d1250046801004600c59001610000d007170340070680da646585c0e540c0c40b083d110b44a803140b151300070500b48050104168101d4040c1042602c103c1855155948565001e0128014803000f954020f20601403104141811182109111054000d0b1116640d5805403100d1203c00501c2d04150010009080e50030315a01c01092a0040d1211091510740860310b80010003040c1c0b54000c1940d0b030240001d1144940078500f200b0340c0506006801401040c2021100d14000e410071141103000c1e010384010100d070443c45151aa140075030041401d8116400c240e03049881 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 25632074 1250 25630824 25630837
    0x1080105150907050409320712020c030d090b070f08060d02040b010c0506040c090608030c1b031c12060902131701020409020c03040302030d020313030f0213020c0106050103051602070b 81
    0x2403100800006c100b4602a000300060603040c040c01038085401210402d080d040c10943c00326100c1450f500b44100f42d07900c000e003500d15201815015807a00d00e0900e12505500c11822090703075952410b46074000300041c00b455641b040c0120340340c91009000100c004da0314a80102c0f960755110440e41c0f16007005107451752060360000c00614160814502998596240903010b640903105042010002c114150315401140702605004020b075040a6802051640d1011080d552151b10308610401c1c89217510204460b00300d4401e00d040d5800408420710300900b0b10800910480382c0c240c00d140740410b41c1ca5140c000c482002c80e1000f50005c606242240010054013184031113412550200320010702d00f8203600207401100d00f10005156124554810149010502d150303240942d007052002c10405000d41420004880d040352000c052400e05100103801d2000c03c0384820b224600c085100c4541d0601544500140d58080e20104a651940c1e4150901d034002d8111500040c0c0c4129018014040c000d4040e114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 25633324 1250 25632074 25632077
    0x506030c040314010e0c0301021c05040f08070f030801051f120e07080309090105180f04030302120f160806030a06020c0703020402191701030f0f1401020a030e0601080105150907 78
    0x101a02c0341d848442d903004903007000b0070036074503000341214601080c40300d50344440c0700f10000c61410a45004003500403060b5a04100002d983d0f0300003038140403072407065411055001c0300169903500d643c82c003801510340301c1400790000380d0007400110b680d0030030200c0c00d1215900075202c150341500e0710a080300da201c048960314500c0d684902d602240030404001240c0509009005551180000014002000c4050340428440e00c2d135200c00d1040e189102440d1500115500080081d5a0311400c050700a88900c6200d58417040c1c0301801c2151000345e00c14202e00881a50001c0741c408000e0480403290b0720b2080e0b503215411380108102d90002056a40100002d8003040e0030703901b0080d80e0340c00040481c5c0214845503501c1c0e4044c2c0d101c01c507040d400a03150510300540c03030502d00c4550454031214905c01e03c0881c01004108050166418080400410502810100025541c40c914281c00a000d030038403030070280c118070954001060084042c02107501c224400107000300480040001c0103204100a4401da0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 25634574 1250 25633324 25633327
    0x3040209010b03041506080c030615060307110106050306010609050909060606030604090309030803040605010608010f0b0a0c08090d0c05040e0a02031506060c2e0c08010605030a060f0f0608090303040b010506030c 93
    0x100d20170550240800a0118102800d00c0030300071000d150800030300030b10201c5081303420b416040031a602c103010380e1780101d520304e8440c803401000c1031110300400c10b60708030507072520801d40006039080d030180e1030500740e9100b0f580c05c0c2c000383c48400701c0c580d4840c425600c4507030004043c0006101c9040541c44956102c1c024508054000d9907505c0e81400350348107440075240c80340c880005000d09500648110300504800740344074203851502d0b58042c014050020035174100001119210240034401084c0c907501800100b2628601c00e031071070440300718091442002d004908021081e051404003003480307031034650050050054445840302c0e01507440c0e4010041c0340e100f0340c1481010300c5038804000101c502c0740c03074011410075400300c10704070001d915070700c592140322600300743c003034000d8940c000382c0c44d41161401c1c113183c2c1d1a5100e2400c0b4101902c002d030000d0180c07018103100003401503051465401203801d00c1c0c64200321798a500020503140c0c802160090b014840b1080100960705049000315072100c07601991a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 25635824 1250 25634574 25634603
    0x503060d0f0b090114040302060406050403030e0f010606030c0207060909020703140a050a0201060b0a050d0506030123010509070804050703080a03020f2206030204061b02040b0301050f040c05040203040209010b0304 94
    0x340c200c11030302141940c100b01c2032020407040d081c003446500300d0410303800c0c070030815440c1940c6d000b9520070000304011b04046e2075502180c2014000d822250423500c85c0816a071003c10b00340103ea0003040203102d2030000a00304851410302c140041450001c0c1e40840d603038140e40c20704000590019601c407482c21410060041407400702100c0341d42c003905586006503242561541600d40003820340707400741c2208c64040400c10110706100c0d04901241c18421401a0100709903a6140c0007034010103c0d43e6020002d103500c640300c60880e8440c140b00d2030682d6400c44d11040700e81c890b04022030340d420085900a0407680142c030144081218580940107403003035482e025150019240c0c2c1c400580d080400c8480880700315a82e8504c1d440c0d000c08030407014114070720b011400c0030714203a0b00074410a40695003040c0081c0a080102c01e40d103840d0440180350001500a1202e800c20300604150035108440c10380d00034a600402044a19150003103a01482d002444410f559003440441842544082c108039041c080c840d002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 25637074 1250 25635824 25635833
    0x1e10110f0a08070b0702060f060d050a0506010b0403060f020304080a110c0402130303080a0c0203090f01020a0803040317090a050c0f0d05060106050405040c050304020a060e03030f03010f1a1206010503060d 90
    0x140705074410101035032180306a19090402d030801070f0089055410030b070100f21385421042c18241d071040d030498003400c1c02030b0f8a082540c1002c08a9102410074000c4000100300c003e40040140205ca10507401000440c4403103c100b012070006440c01003038014100f007040c3c1c4040c8178841b10001c0181e0802901c400f82050b90002c0c089900c21a100e16020b00544010070a05030070001c4aa80039005207801d122901d1242802501c80c4240d40340e06100d02e00d2016006803591007000b4690b42c4030342c032282d100e41c0ca041c10708000c0d00307015880380c1d400e001d60400070009178030034000720b0202080c0303038044020314a9040ea00c0030070000c1c0d4480d11401c0e4001c04440c00210200c4d00030440320b4020403280d01d034555214148020704c02a606407042000510000300240b00c01a110245450111005031520a8270b002d91000003030305500c01d40502c2409000c0c00700010612212940406084401e0300c4d50007901a41410904200c60103000a11245c103c072080001d002035000703030011503100d80010400022044070356503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 25638324 1250 25637074 25637083
    0x80c030d090c0504050f0402060327010207050d1b0b060103020c03070605060103050a090206041206090f0b0601090e01140103050603100606020106031b0e0a090614151e10110f 77
    0x12180c26903032181c4000c4180045903640728080c0c41e0070f075024052480c20207426080c0300000b43c0007d01810700000000c1c01681c01052440c007a9145058511201d10300780d01e80c1303020b508000d00075501c1c0c0c0550300c00d05c0a8140034201545071040c0ca5540c0f50007945054071108181c01c80100454140340e002c006603844c03007005100500c0c04034851000098a41451800141100c400801c0440b000b0301e0100824050303521181590100e600c0500080c80c00b418518181018100143c1e008120500680c6940100025200594424034080c0e84080340f107a07840000c80e0181c0020300c9005a0000310820340c01046d407003030f001185d00181c05002c45520401c40300b0f5480840e0982d03409200181d540d00010b20401040d00d6181c43c140720007214100e0106e0170043c601803890005401600b8442d42d50307014a0030800c00d5000801c0d5824070302070500c1303185848003101110074942c030340da80d00c074038594807a58001058101c00d09031282d101070020041200c2460003030710746504402c103e070420700c070b42081036480300360401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 25639574 1250 25638324 25638337
    0x3070b0a08091203060604030b061804051f05100302040518030a0509010216061403040c080d11010b030d0f0e01031103130210020c0105030c07021305070503090f0a020a050409080c03 80
    0x1600c510300c03450b00603101da081c941e200700072050f074800030030500140d582d800003583d00340c1e50820555270701c41d242e06000410001103200170704e060075070f43d90400c42403041c0400d01455080152051010b010710303800710720381107800c05c030f62071601c0d000000814805402c0c1544a1980703d4110484541102d4408542ca40740d80c20081440000030000600d012903542d0600c00c907605c1d840d85900e00c0d1010b40c00e2030400342403058444403460b04150b0100c00a0300380003605007104024a030810564001c0040c0f13180003840e1a180d141a14840e600b0a50170301c095007000030708108a00d2490751440902d021000b0100d44080441500504242c0c646210441040881c4010350243c190035180000007649403044c0803843d0280c465240c02d6420201039203001e40d80081c1120342c0030b00105001c40d07849109100060644c40300b0000440581d142c0000c000b4429004001140075220810844000011104140b560f505503018025040321100100300260308145d000b0204580c440c0781d625041030b190301181031a40d081038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 25640824 1250 25639574 25639577
    0x30609050f100b0109080703020a1703070c0b0706050112150b06070c0e01080f070e010509060402040b03040302010603062d0506010c051501060f030606051902010204050d0305071208090d0c0203070b0a 88
    0x76040102d03d5a04504050000c080c2a03001d0041d152171a00040c181c0c1c0c1c61032050040c0c8944121800050300010f0088601a03940901da269032940c544414942d190403207042200c515141800104000060301e500e108016400800c24450740c0f14100388201074564a2501030708a00184032100001d20505d4400003c0c000c00020007506614080202e07140c4603400480301030a4105010034000044060311517415501c0a46525420b600c0b21170219000f88525400391400030f20100900c420150b040d000202124040d15080c00b80e0b2080080d454803058100c400a5507000010900b80c5140c40250403195000300141020781c02c22021f0349a80303040034044450782c000c466150006102180e04041030f440c1414a6240801100c0d00b0500301500502c079507007003403855400c1120380d04034662003501207030003501d800303040303105091014600031700786401c1420222100f4100c5081c4130740c1c01740714aa03898031a4241e94010b11150a495400b51031440d40d101040e070b00f50041d4030012480a0540d030007407811040c513 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 25642074 1250 25640824 25640831
    0x506040902030906130309090509101406090108010e1506040b090103080703020d030501050d1104060f0807030c12230a1e03030506030609031b0c0d0320030a09030609050f10 76
    0x103510307184c24440d00404001491a503209400040399201182ca81614010300c0b0000b01c40d00c034030400c00d103002d0031b41a41404144c104140c4070301440e01705132683e00500c0c007921549521f0740c070754440500384e8410040004155002d43d00c1995003d01003e0902c0d00000d020f040050640c01210110340c030418240c00503218000c0c002041400c05034100055000240e46203400c0009505040000350011034516000d400c2c1c03100d081001032a517840c0d5200c100146004071b54909281d949020aa0300c0386160310060f034110300215800220b00303080070314400c82584d12803005031440c07507040c2c4540a10803000d01c02c0700c4144a4440341e80b000900241c2006615150540310700c1d880995131070b0060640c1c0c1c00034411406a0403c4040c401d0030b003000801ea031811364501c6580764070040310b84001841d005c0f4040280b0f900c1050108403405054000148010074841d9030f50009124101003142d565030711800100500246c480700003007011400c1c030380c4035109941c414006d44003a80c449441c80e1f07241c00819186424065079 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 25643324 1250 25642074 25642081
    0x20a020907030e060601051b01050f090f0601032d08040308090913020a050402030a0b090c03040614010e07050f0d090b0105030601050a030503092407120e090402060703030c0306050604090203 84
    0x302100c0c265403000480c5000d011031a80d55a440b42c5420014020b1414401c0100392000240f0101c7c640e1103000010310003c00641c9421520180034aa007682c1c042d4883c0103180504d2004640400c10781d060f650084080c0c0201e81403c0d09038140071a0400c2c02c0706d41c02940002d81e000140158004100450090710300759100c91452003001390f26107015086032144013041c028040142c50f040c1c0f41104588003201c1c01a2030f55103641c0c1000182040c801a198020071040420074061003440241d80164015076041117582413280040c8800c3d9028000c00f440088040c00007a0344501c6840101000e0b18aa0380c21818024039031012415a6103050301282c141d81c0c481c0050046003004c00100d03004200480c0d018054a207552540e9031a0310078580390b01d00600c8400010b901503101c0240140b01c0c2c03c08145615075807016414400307030b850318899280b13000502e41e071174001892808241351800341d41c000300030900c0c000c4955000e90091041034020000e141c2c45620000e843e541e420003400051684030000f60743e034035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 25644574 1250 25643324 25643329
    0x40606030e0a120504050307181a03060610120c03140c040f120302011b030b0f010206010f050603090724120504030905120114090102040306050c040b030103150e03030a020702030d0207180b0f030d020a02 89
    0x39a41d00ac400d4516201c5840200c443c1c0c0d00090040d040716060b50300100b050f8141c8400c50381246040c112441050801d40c540500c142d055206044078048200c0ca0120340d19400d070f8680103445a4400e507540c139544040c00b4403e0404100b0940b814500c20f00000441503401095042d0582d90403006001003943e401a54046041c21020982e1400d400d00c05080d0540c1803440300b2413015041d00600f4000c0001000049491600b042040082c0c5200c40c0700c038840740c00c2c02e9001a131a1041a42110004540000c19190a0300070300906003ea81e141d20f81d156694100418802c4003030803510520165901c401155141c40d0803600c286029110600026940340d0440c01c08c4000c1d260060290302c180c8004000801c540340e10001540d040d00d03070085082080040780200c110150411a1840103030340400424000c1008441d070080110368400d41c02d075001130b1102c401c245e032100c07058480e10b00100043e850081c2c1c40b048960204542c0a0010701c103007682d0b000c030780200b4079184001c0f1b50040560700c080c44200661 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 25645824 1250 25644574 25644581
    0x3010f1b02010e030a050c01150806100909020d030809010207120509010f1403010303030e070b0a030f050105010e090411031f0903090512070303050f07080304060b040606030e0a12050405030718 85
    0x32060009200395040c003a240c541d40d02c0340700501420010b000ca0020141002034021201c41c0c54440c03140c2014039151384802d80c0325070041d80c00c020120154480040c64201038003404203480c1e0014030110804a01d40c800303449a0900501850309550308020810000d821031a0b81d444151040e40d526854480c454000350040190f0030342601402044104250301e900300c2e40803281503c1d0b041c0b40100b004015038448528091154014a01d00c1d8400300310f600e802603041d40700011350600210140b20b140d90342c10054904907018074215400003003441c0020302050b049000030035042d0307000c0c04485400038640d1141d80d122044807140b2071070325245d1136907001340740d40f040c1c1d844042e1400b124400340800095501640d51140d034400241407110103e0f080d01500b08503825510031391f410190081e0b90f40380924141001303154032003110384102d191a001040c214801c1c401c1c6004031641c0e41c0205201c0c001612415030724503825030b0850801030b08005c0895561003e100ca04014002007119009440d050008002076 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 25647074 1250 25645824 25645871
    0x10121401140d050c0d030302040b040608090c0103020403030f14090301020f0c011a09010e0403021005011217040f05060702060d1806060b071203020a0e271003080f0a0e03010f 77
    0x50b282c002c004501042d00411100c8610f58101c0306801100742130f203000d42c0640503d80c0881c2d011803011400080680d00171003003d10a0f213800c07050724050400c05005504901440c00054001442910303200210350050480581085295910340d061100b00b00000342a41c0c08060b1001c010503000ca049a982c860900403215042d415107a1070f00307018000e0307003c0b50003040e0510070000210801d001042c1130600a014244003450700140c10700096841d450030001038054480c0031582104002103a01d1030514820070395080e0740c2a00d140c002c10610341810882540c00019051360b00000030480290340c41480e01c82c0d1885020300024590300202c1505150003140c4890303000d4444110b00304580c40000d0400360300b02780059040c0c100161501503c1604842021401c40e4554014407038803001c098001215541d100035008011200105030390f0030004090b000e2483c0300003018090f003404007000c110015405842c584805180c0485c62618a40001c0d003580e900e178101840311a541e0200310303188030701000d01142 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 25648324 1250 25647074 25647079
    0x20a06030209090f150126010308030103140c150c0c030304090501031a0f0703050a0b0d030207090608070f030201030b0316030605010501030b040506090f0910050c03070f1d1012140114 81
    0x201031418412094903480f10188179410459214588000b5820741c00075000c80781500250000151703120b02d040c0030150b0003800300b80c4a41107401e02018499000040080c2c105002030500c00342e1820000125800340c00c1824068510301980c1138001d0075860802c080c0000b031400c40400704055241d800c1441c14807074a4042c84580d504c4210400c400c54802c7da4403550000407503d03001843d5682c0040540080c086e8018056008030002040c0c4141907000400600341c0d52031290411a50b0750b2411815500c1d1828803901d901c644540d10200003644c0294401260490007500365026003a84508100c00c00c48903410489202c1d690320014040c0b0750b85031143d001194002d4804000a00f030400000e41301ca840100034510000442d80001c011800601ca5065012441401480541801c4108981c1c5405c00c6032040c0006014121107034100d841401c4594034404081800c0305580400c6007441441902c1502a0003803091200600448109610441c00440000e041c14003040d410405031901c0180103051403031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 25649574 1250 25648324 25648351
    0xe03070c0503030f1c11030a090b070e1c11120a0c050405010608040204050403031805030d0b09040b010902030a022b110309030d0b030c030d021507020604110f0409020a0603020909 79
    0x200c4071900c500f140c1c017015460f13210b060f41e4507010885001070448030060a0540602109001d45001140c12100e000c610440321104a555040c9046580d400103150315603011900c070170509220150440110740c82405500038680e07003040c0102140c1a84680e080c80740c9664031182c2c0060074001881d1203400503050840e0300b403006500d4940e000340400030140001e0b20440c0d49202180405010307601800040d00e0090a54206420609000e1f031242c0024650750211401c20640c158a45002840148102d610a0181e4026402c0480280080d00010008640181e08002c038003405503280d50151030b0b03004c1070b00100c0801c5030011006d0040c1d45080c0c4085c00e910806009101803c8001710036108203202c2040d001481c1d4114200203803800c6030001e48140c00d0300036681d01680707055011880d07191030303a600d082c910625111100c0480e60703043e003120090a240c0902c0030f24201440e0040100c892610018400b040110040e0006410300800d80d204002181c0c5c0000e1040c00c030f040029090740d00403c1c5c0040f00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 25650824 1250 25649574 25649587
    0x3120f0b010c02060c0a0b0a1e050403050f0a02070308030a091b05060a05090310020705010204051503060604060807121b02010606020109080f090a0e04050106050418030e01081003060e03070c050303 87
    0x203024030600840003403103107038041140b803848141000002035030b541046041c004c23405c1591074280209140c9140101202c84010f540180801c0740c002c4502859156030754900c3c00f001240c241545c0e4001034980d01c11405140000000309000201171070045076103c5000411074100e14288040061000301c6000b58004002d0410003030f680c1c50251000c0062500301996590148400031b03080c1007540102c1e0280710b102040034000e204055020303205803001520482072000c0c50070103a41e010b020803250690300c50005c00c03041c041540320700506904680c1d9404c01c031004402d8840300205443c4100740d90350151040800c4c0c4a0b003241d09014a000030605030000f000b990f003107501d030061244035001011800c0c0f01c00003804504c0361901880c003401040c215060b001141000c2c9400b0b07003c0c149900c9103070b118500306042c04400341590380304c03018015850746404004040380801514600f0000b0038184812440d08400004186030b4050710798802a00005555104454a00034000303901c5900300c640a94414844c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 25652074 1250 25650824 25650827
    0x105010315060305091002160203010b09041718030303090609010501050d03081803090a06030501081b090a050a0b0607030915050301060210020702031903020604030806040b010c0204020304080d0903120f0b01 91
    0x210380640b0180d14000c2050b03038036411010b241c0726640040c0701c480303440050b15045154100c030088030268800c5000380150303200b203c1000b0342a8402d8401038802000d03800701021101c04540204141c1070302d00d04002d80b500c4042d00207415a001110b000440c4e401c180f01704020503200384211801340004a078003561801b255207008102141c000d0002c100341040b032070025000c04080081d40c003049801000d600c656070311848000c014103000e02c01c1c100e0b00c3c45520340d000c2d8646c0900200847d00d401c05000307007000c0e9070f41401d11400362030050102400140c0d60103560400e916000000e144050094448214181c60301c1d1361510280c520071201c0041110500062040382d5001c107009101e00542400940c940b00b10340006420484040c040d0300030b2007854101c8108164002c1400742c0b19034041d1701d4002055580d0002d11040d02c04001f82036001605c1c580c00e440043c80c00c1c3e400b440d000743c0207030a8942841110104001201c29032901600400c51048a07075000760301e41e00a0f00060346001e503080c0640580d0000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 25653324 1250 25652074 25652111
    0xb09070e01060212031003050a0c03050f030a0e010c11090901060303080c0c0c0d140601061106090a02060412030309020301150302030d020f0c0d030c170c070807081506031608010b040501050103 85
    0x7204c2e51040d00000450b41d00a440c019010185410806480e040305541c5003003440701d00e503448210f415024903c2031110384207011058815801454076003098900400700115040c00080c801100c03503540c8840c071540c660710360901003441580050b0000980d9411801d01030800c140080540204090801c644a141080803602d065601026608110440b00310714100080044114049005204030070001403465440221100c440c0c110400366001382e1030b900e20090b260054a5130107908070001b0401000070005601013003100741c1c0a45000140051a5400a825201908049c01152002c80404c6c0f041d440c0c00d214144000081d400140a030300c80740e01c4400c2d241c0b030449219074481d0141c1c00c9040c0c14940194104280142c1c0800302180940c20580242c4441e045900c0614513441491008103904100184081c10b035844c0000500e4000d00c0880e40030440a001000941c15024130405c8604003900c0c23242c00f6018001041c000300c2d038102c51005002c201d900581c070540c101810040500d200b000005c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 25654574 1250 25653324 25653343
    0x610051504030f140703080a090e090a0203071503060918020108011e0506070204020c01090507030510060f09020703030e03030a0209011805010806090405071a03040b09010b060d02160f0b09070e010602 88
    0x1a41c0070f1040c5490313026181008141e610241a80400290400003550301ca03407980f0982d42c540f82280d8882d16502d030126522070200790000d4140e03020213014451700900c0380500440440c0c916000c1607282e20741032600d06803446a501c1c03440402c41700c00c40320115a00101d9160151020904040c000001c0407080c60340840c4074440c40c0c0c042e0300005180001d64945030110b802181a060007032150180324589940d44600d140700684040c001c51781c0844081d00140944400c4642340c1741f80308109420400f0001c000e5110036070440c145566261041c1e00250180040c500c03412440d8401616901c66000140400e068500840300c030300000380b0f05002c0b50ba042840300307804c520180e50316840f035595890010301e0070101d03411070350215141140c0d40f908800b00c9401544030341e01c0b40490481c1502d81030209420303100a880d01d298400d0382400004606c200c903034042d04505681d4184011031181030b07156200c0c0c1c114404000d0317949140850070007603004400c0004070020a01e517000304000b980352400c000d44440422 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 25655824 1250 25654574 25654583
    0x5010617031309090206070c08061014030c0922030908071401050703261306110301060e0904081905090301150303050f07050a050d051b010603150e0f0610051504030f 73
    0x1c0c01600c06541b500010755034159804101d00d90401c2c0c4500c1c103582e44800445017502d000c40160004988007001454000511102a000b041030018807002c002039500b004040d40020705010200881441c0f20700000540035010ba1607002c111414130800a080c00d8464019405811b8010842086a68010200e410b455094901460300b24030028505050004561f09425210709030700a110740522030300e903074010440c4500d108010504502e401015140001d00ca01004074042c20344d801340354109840c40b0340d4854400c20516107090764100d080b024800c02c0c4121200054000703e0802c00c14242481440e00642503181d400220740d00c1c550f401040c600c22074903060750581e008546401000020800c10107a06e900400340c030202008408020120b4100365000b207203496403200300282d085e5061040c481a20b4000c41902c9005004401c1c8902421074914100c0f100c0c480c0000d07411210905100c039900030960315040304421841c1108110a241c80301c5001ca0710014200003c00c00528101801a40305601 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 25657074 1250 25655824 25655831
    0x30507180b03010603030f230301062322051e040c05040e0a0b04051b1611190e070504060c0f020f090c0d0c03090818030f070305010617031309 63
    0x160031500c050074012554903010760900c0004420150031042d48603104150359280d5502c131500c54403455450702d401c030100280c1c5000300b00600030703e80b22316801c0400c82c404a6004a200d080781580811a50040d802c50700084241d0340d903031569149404015000340411107903410074480d881003440c038146407240c10900caa541d401d0080c0d03195004005403001003095000c3c00748285080219900649a4400618420782c5480005030640094000c10903400400703005807410a04081c004100b43c0c05146015580c862502104500c503030342e0308100384056800400700081045c5800c1c88043d00480151401042c008140814040254890b14504016412030340107841c1c4044c0e4004265034500c1c210390942c0040001c0d00704440c2404003c02000002ea05003410007070403111020860407501c01c0400144000402c0014040c0fa250140d288405d2090050594030318035610318880d441d0003143c3d1300403505651500030801940e4510840780b8800341442014510b0b107007407000341115456950244480d100d94 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 25658324 1250 25657074 25657109
    0x708190e030d020c040b030307030804030516230d0e030a080d1104080f0c0d0305090d061d1506041a010804030306080106060504180b0603010506090f040f1b09030507 73
    0x1180351214445000501511503102c1556802501d07a900c20070a140144d040c800d0071340e0319040000840d01c100d0741680d00c022040c1c40c0e50742d080b112603024100707500042040d1245074001c01c010b5104c14606000d960414034000100b80b8080d402c0010340c80030380c01800300c104161039030703620b021907070031910ba600c00c44c0180d590305445441001044040c50650140e4030206000c036501d0350004003008038050f40c2c02101c40e201204e10821003412401b150060008805100d0303900181422a40e034003005100310307030110b0b0601d0028125507400f8030003600070420354001c83e594040e581e01402e995401c84802e44050103920340c09041d0106202000c0c0000781000711080006040c1071003903101d000507200103c028440d50b99200c00042c03450300b003405200303010281081c607190040703a50312a4400c0007001410503419a03280c0010055160002c5804a42110000f481ea16960f69244141c20b015201d100c000111612009200640e082c05140024280540304606001140340000d485080704c855503070303040c0b0904 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 25659574 1250 25658324 25658327
    0x30405120f03030a09030212041a030717280212010608091c0c0b070503131205090a09060807080303040b060618090a0c03050604060501050f090f12030301030201020105010506070819 80
    0x180c9a212801c20703400080203102d074013607842d001000b01c28000e40c2102e000b0f000154801c000c903c26441b500f601d0114070f02002c10400250401386602c0101c50034100c0d801c80d201240c410300910105ca0786400b03082c154440e041c0c1804d5144512240041c0c1c11421402c0c03a68510b251411000c040c0a40400c4c0003071503000860880713041140c1002c80010580d810310790074040f03c01400c02401d0700d80c1141c01c401240c0024842c2481481a01e10420180318182d151800c0b40d12400748610071007003a001005000c01070b0001c44d4441c200702d00018404408c0000c0c000c0e240c00e82079030802030590010030403034104000707100c0881c40c80c5400d907170402c00c125066562040e202c4032100b1000986540300ba0802121020000c04001552000d80703191071a86041c80300780e8400080100f100c98501485003c00c5041c00809061b000c0b1b80c0241144150141240f0b0b801c403e43d20008082034403404a85909920000042c021941d0a004581c01414103485031801c161441d95403480c80e01810184c0c015440382d112800030741070b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 25660824 1250 25659574 25659583
    0x1061b1b0302060d0506040b010c111908030414040b03060f0a0509010207020907051324080a1808071203020406090308090103110a020f1204050a0e07090302040f090318050303040512 80
    0x110b900401c110b6556080c21006005800226103080c49185080350594940d40070782150b105c5103074401885140c0041c0007080018002c410080d240410601040220720481c01700001c20140420407041c20b0695100c138200000d598075614454000c3c2c0208040c0001150404241c82c4c000740c070146d000c115555891042c0e402030003100c401070f500101e01c030140240b043e0044001c21400c5581c1d010341e0003007500e0740340b030440e12290404007109801c0c07084850703c035940c07084000ca6003000445d8130118000e1103400c46019507140000080c0c0d10b024000880e4403c0151552540411a607242410344c1818a40807018184625500c40030f05008400100000c0c941e100b42d0100340504075039901c4030303154098003000964075001c003508070b0042d01c1102d0a641600c2d0030341080c4d40c200c440c020064000e80d03013004010108440c0150091060203c000400300040c0d856000b0b00f4a44201c10034002034203402424014080e80741d54500981e4220807003002e10850704c3c0070040b6016a00103441d808801546c022240d49403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 25662074 1250 25660824 25660829
    0x9120c03050f040b1c05070504051e0a030503030f09010b090601140904060e150102011107060b0d05070b1201090507020c040b0607060510150503070206010302040515040510060801061b1b 82
    0x40240003d000c40c0c0303208014040c0105500703141106840c000c106070300000700c820603920000410000d100412042c589482c1c0c1e00340361010b5071810460551003001190b0001c1c40d03034104640350b40010003004050042141502d602907550030083c40000f00000106229210280c504c07410424501c690045503840001216082c210140080044070303900c0d24000c447c18000d4903484d40803a4228480802c039031050140c801190f50b118225031800740c5a988040040c8010308403141c1282d050b2494501050b014400035004008460301c240d900c0e50b00c168003007507140058102c00c882d58034000034001503540c00140840003442c19100000c2a86404000900070b00603504020006400c0201300f0208640000c1c1c0d50301103c071147d90881c000c07022100f0660301800201c80c0c440050b404100100003510b010340140d0b810002d000c214a40c05c070409004201640c00403103900c942c1004009080184aa01c20303c40d90040c0b401d4a00500020030001c40420b039000581c1d005010842061443c0f8034446125861000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 25663324 1250 25662074 25662097
    0x60b03070806030d03151404110301080a121103120408040506041e0504090b0c09040207080703050c0c03030901020a062406120b09060d08070302120d06140409120c0305 74
    0x1240d25012000506940084802074024021110840c134040d000b070040c2080700041600701c00000d0700b0140d0405019018183c0e9941c4251605d04c101c800c13104000056003c0d00082e000307802404403608158100c503480d0380849040180e51160700d80031030070100c1650000d001c00085040c0c503032643d041548150003150065030303100c040001e0004000c02800c000014030203400300e041000c103540c0c42c2040125a10940003401032440e2074002500640c02400801e01404010401400c003615602c2d030460980080328100d0200d400021144000081004095181c01045004506d80815100000c1d145c071780301c090083c8210744803080608603005000ca80d11001c480250704075a0580d444100428640c08580c100c042c2a1600480c2d60351400e00e0200300d8420364000e80310a010010503540d09402d035216000580031401000e0703030070300a10740e6000200228642c1201c0810800e0a209030b81c2c90103081c40200760710443c038080581001504126030058200310a041c0b405a0840c0d40c1420388084c445d0a10086 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 25664574 1250 25663324 25663327
    0x1060e0f150d05160c08071a0414011407020309190302030f0a12021b01050c1e100f02070b040f0312050a05070905010512010915090e1029010c06060b 66
    0x11504200344000e4900410901d405210f29181c411010048640303507821400002c1c0e1925000000c0340d01c00c0001c25205115180706c040a16aa41060003414001c1d9004c68a44507401045050103100f4010700441d4022901c2c41e20260601c814003a42d40e228400c1d500b80251004079000c40c50100449450300150740142c2901c42003940810003584404241ca0200c1c0d03064400b21899144c9840001c03a0a40d404c5100d44850942030044c0054540340c000030785803455442807185004610300410144140b900d4910000c0001041068115003641c281000046001d80f0522141001c1460700202c0c54116800400980038817540d07040469603d141d0310f403074036002c40c1040280140b02901c0d40c8424400c144640e541c1e0107035501c5800450b034610400b080c6030400c41e03102c4010b2020a0055110301c50399108040750b9803d040d90360b004074055136801c11304440300707410024a14424011074060b118514010070001c45442d5140c0c80c07070014050b03c11040301d04000c0300015101c200704c0254044005000f0f400e0306107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 25665824 1250 25664574 25664599
    0x20a08010e070807030b0f040606090c0c0215070305030c0702030f0609060f070801061d04020417030705100905030406030c02011d0c0f010212161e080301030614060901060e0f 77
    0x224040d001c04510341c01c1d18490150005001840032034034509a96009001d50700b103440f1102c15a20b042c0e405407059848940d540030000d402130852207000281c0e4050b8542100d4808240100240c509002220500100d4100507420010b9840000c403a4003490b5200a2510381104d030011030b00d0718001061191044c420031081c0888010b0004a071842080503103c100002c2e521000d04981c4c064080c0315a901142c200310585046204440390381100c8400600014101580c0c0e00507419801100d5610303c1c0c0e9034000180c0300060000c180140200e9145544c811702c507600c0203a940760398031f200364803440003016516004003151b00d00c00e4226036400800071020101180d018802c1d152207909442d41544a82038400202000394004107520102418214107941440094292039004e051a8507080314082040c030311440c0004074000c910200c8d10701400f502c40c1c9035030441c80c00e807040307401c203000d11a41e202c0640100a10ba585142800b4151a054680240b4500380322000c6074071100030b80300f565809103982140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 25667074 1250 25665824 25665839
    0x50a031e15090507021203040221030f040810051302120304030804090b01020f010b0132130f0902070b010603020a0e0d06020a02100e0a0201050306150a0203030402040e030306010206010918020a 85
    0x1103600752500300b9400c004a403116142070340d4403046000e80e500300d00000d1000070094907003445045440b000d4420f103038150900d4280b07624110385c0003e68046001340301140034032030071030104050100041210310400140c1080ea6803148001c2d4500d0000b17125407080c482411251209109a81c015544a26016120b0383c5072803c4002502940a060f030041c42000020b0000a50500034940001d00684890011080071540302550340910200307518400754600b041200c45644800401182900c031250388402410000310000301040e5500210200e4010310134040440e05c50310040307046038002d0a0040c0c2c0c42182d8138064a03088801072070300e130b44481042603445c07c0c41916002441c0c445c990707500351041a284040c1440403104d0460211415501414403100194010340003560800d5001300820f204000341007040091398001140ea00050f0004001e000860509010f070f45520746a42c00514194500680000d6840d54144121140c00d86c59404214500340d40824405c0d5454010700100005030302c4280d07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 25668324 1250 25667074 25667111
    0x170f0d090c03060c0c0c0302090702070e0a270c0608061c060c080615030105040c030e0303070207081c1e030204080f0a170a08040b0402040b1c02040c05030601050a031e 74
    0x1c10340b43c02c1e081c6a001c2048a1040381088500c0c3da020341d8601143d0700703503000d00c0440354000300044258031920340d012800501301500c881c407400c025500483c499a0250138001f030000b0a4007011030781e1015101103400103044205000980d45945030940c0a0355410300010007040710041c10b091807003c01d04aa83c1031104580242c128040a52501d141d00e8590400307101042c60100300108040009000603c60b524144d004564101010724012a0b00f013401288541540d0068130b064016078840d2408020800c0140032000303030094040c0c5111192010280082c02c0c2d144611001030301030b141c1a050b40e6181e0700990590300604054000c81c0c51403081d81e44111741d01d0391142d01c1a140e040402111800000140d0201d41a5a44a64803219a0f480320758884c0352607840a030007282e1080c0c03100c0c42880e603030322800c5980b4500952818000d840d90b0160050104071000d403803101c81005810000c00131980d130040220ba50b210380c1440c0000f44410450320a41c18039184002d42c50b40c080c20808000400c869104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 25669574 1250 25668324 25668329
    0x503030405070f0609050409060902040e0a110f0a0e0907090c0302040e0603010603050a24150e06090601021e01090b07020a1205040509040206090619020f0c030a170f0d090c 76
    0x2c469003183c4070f43c0040080b2101d0310034480024001d86003405141050380200500700c0c07250101060306511750340011705440313483c4100701280d40110783c3c80003400104846007c0e041c04c15195003592540010103d4280d4a80b4040c80301d080c2c4802c804503026a00070800c0c1e600500901c2001c0228403941d00300103001e0340c0705102e582c60010a002c00701c0e4003032070180b0800b01140c0d84000201004040f41e522503a00c608542704405015034500d12941000b03040380100c40140c08070302c0104811a0034041030744800f440203000940a43c05130820020b00e643c001400c05441140078000b010300b03080c0903000a01502d00c1443c000c103001405401d10840a0700001c10807541449890703d602c24002c512012145030080e40b19155000506602143c003608050005001d049406495145004080341071032681c4403200340a140142d01010020000300001c1c00f00440301300040b400b40c99070800030340b6046508584200718005550000541103400215803040380e0748010a80c1003440865840d00b4204045541031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 25670824 1250 25669574 25669583
    0x10203060a080c090a0c0c05010f06090522060b030a05030c0610050d05031801030216240b03030f2101030c0e0a020a0503130201091805010807060504031703041b0305030304 76
    0x40c41c0c0410403000105190504440180ca01c42085d6140c04252000d0484c04103500140450268200c0204070f003800340040414224101103052803800c03079000304803000181038200700f55081c0004003054103003e2446005540007000414520818000a4208440303684010f04910001035030120244020510354032a142d0301d20098a0130350b5402c00c0c803010035800741c80240075806c204016020802420010680c1d48810b160042c2070103080503558400c9603500d4029110700110070258007a400d80004042c1030100842030602503000c05401107076580c00b0759902c1c099015004100790500150216880d070581080142050381c6503580e0404c04505d00841c01104902d504400c005114480c80f4002c9a81c201c0d460707a5424517695402c401500345045440c022030411091400c002502a500350814007030342c004000000d03607549000e00d05443d092081d44518180701e003c1c4410004918044101c101104200c0f880c0b035582e0740c3e04d150424407036036019249440e2500c020004002e110000001d14443c9105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 25672074 1250 25670824 25670839
    0x1009110306070206061f020703020406080c040c05130302010318020303040315110301030b0414010603050d0302090307050a0e040b1003060f0915060e06060a050c0106120c09181e1401020306 83
    0x14690103d8a4013004c03140c040c0c0040440076450034401c05031548070b069003410f01c1622902900c907800641a14400e60042c481940010341c803462070718062051403a13510351030410318900083d003c41c80c41d510703a40b88030182c103150b41e0b5040d02407102160a00070342c1040e402411f0341d540b503440b4a0302c0350740c200610600c3c10000d0f2034084400400c0451200700ca0590360800141d06184c0e40310390303882128031624a0084419500c5060000016404004c001b41d24012510096144d400070014540f070220941d01c580c1c4200c88140c0100a00304007401007582040d000745a20b40586e90702e00a50040201a074001800b0314609a400c8420380b04641c030046802c0c3c0300d0482c1c48044125008501c0a0340c0389170042c0300c0f4900f8070701c001c50340901e0800002c166104050501c14101070900c4c0f211401c450300c2c2d0740100140c010360103500040001c07040c4404041c0003901e20800111007501c401d08058041c41d403005004000c0404c1c07058141c0341000b20b074410240d00480c0600c0d00f0043c2c0344028003075002070f500305008010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 25673324 1250 25672074 25672081
    0x3050307122a020904060e0f0f0f06010f171903050405090105040c081603090c12060c02120412020604090c09031b0b0f130f150801090204080d111009110306 69
    0x5004080340002c80d14482148403081c1c040c2c08010ba00030010300211074882d40c640900441c0c0505020041600c03079020084c1c00b0b02488284407605200e019032081c01d50b600030b080144811411401b054041c0d80000c0d041ca4119000b80008910700782060b00302d5038610b44060500341c00c25600200420a44400f614440026640c442c10f01c400e40301e503c4101ca02003002100010048410b40807000515001441c0110702e800743c6460760140b0201c84c0c0c1181e212664010089000e102c2940992220001148010b101c0340b440c404500e000350141e8081d40b0200360219107a0015991401e05803805051100d03170402030008100c03009817044005120848102e61041810341c907201e0b00390034030400c451a22514900d0081240039018103503001c440030700c2c1c03c011154408162180d1f060111401342c2220000984100c0f901c040292000b01d0580c0500d070300c45d00410050025400101d42035020048509210415400040d44107051006000324207500500d040c0e440e80c03d01c10409810450324000364150340413901d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 25674574 1250 25673324 25673357
    0xa0e0307050303250302070f06051909050102030a18020306070f0201110c0a03030608010507020c191502030714010902060f0a0314101a0f03011701090f0605040614061f03060305030712 81
    0x25450050423a281124241010030706c2900080d034031024004071000703d002403580741c0d421110099000e940070780d0701204000c400c000c140b090140000c240c40b50021100720f5540001c2d500d08008000c0300420250114000d0414001d40180d01c41c0100c6880c403646515403852055038405008006600090905400103083e01c4103204107400b4011982c043c226031080030381405511003001c000c124509044e2100001d00031500b4840d001c1010503540035581e100240d050180301104424000074550345020040390059549404555140303102410043e2036846650040d002011802c50702c540d52401c06041140c0d29455255810a807850300b1407040c03503010000880043d5016809160104680810050010a500f450f0411122030740c00d001103501d4046945181b000008450100c0c4c03880d45503400d2100f005460700503c1401480c44000d5025450103600003145141100c0381c00c0980107102140484180c400d800c40d40155411004490383d800d01d901e0104071240c030030340207000002c0060034501d0604 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 25675824 1250 25674574 25674577
    0x30103030e090a091101050a0207080d080708010f0807050f010302070204060b0c010606031407110a1a010504050106030507020c0906030f0a0b040b0601050408100b010306032f10080a0e0307050303250302 89
    0x21781082086001c4100c50f401501e01c0e501c40850f90043d8802d040d00018215010050b00e5204000c903641c0c0c444a060001e4040d02c0a0410303005044245120f090900c6200c0703002902d042224000c90713032800219075080040c1c000340315410b8065009410005d000c1580c0d088030006051054443c0c008101c0385540313036400c404640c0e100c051103a252140300302180071503200d03004921013003560900b500c8400300282d6803074180b0540d0240070042001d030300004000300d103094410140100a1400c2c14403103417401c04402034680001d1803140344540d00ba2008618a600c04015024580e400d0a0454580e01c1c0e035420016205a000c0300c0485002941034006081944600d0a490880351000014105c2c1d548030310500b0050800103400604140e40c4000000106400c44050094162815158480c014410114070480e201000c02540190021180c0c400380603804a10700d644003030140e80019801850300c1c1500d0940c8a415009407039884080103126220003038803c003d6000801d00306c04000b0103c031070700aa06a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 25677074 1250 25675824 25675841
    0x601030e070e0402010512191103130303090c0f06020f0c1f030903020c090117070f0501140c030904090c080d0c030c120207081b040f020f07081e030103030e090a 71
    0x440d00030360000c01c42c6080d0400459002407050600508001c0b80413000c881c0000100d075180b19100341002c02c10000c4805105004164031189001031540c82e060b0b242402c51070103280c00604155445040d0f07820b00545207030010181c8400360210940743c1e503075200255240d000751030030360075801000708410302e616000940303010f101d04070a55504a5800b13120290b00600500505400b980154031245600d540d0f00501580a0802c0f1780400085207060041a80390007034507041105201e041c00340034081070380c000e1404d4804c0c0c10b125500e195105202e80602e402c0d4000d0302000c0b074016040c024100200100c1d80c00d80015a6640c1c1d003110910285120300300c1d0583d12007071000d000f0651a501e04004101988000018401603004548150b991754162502d4a00e541c0c02650007181e844500a00c01d02e014010200c0400d4000780079410048a54454000c51150500042442c2e400054840501381c0f10740c0d403040610700760842661a90b03583c0c140030702000302098145100f50b2600c40001ea11100031302c9404071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 25678324 1250 25677074 25677101
    0x1e0439090603020a0b1804060312020f010507020309040b06130e0105090703060b030a09030309020a090f0b010203040302060d0b03100524010c0b040b0702030702060408030405031c0503070302090f060a020c0108060103 95
    0xc2c0e081c5017506004141d40840c1400d50240e00c003c030140215102d90090700e00840c0b00c0c2100d1554104002c07802800c014030411148110303410001409a519400000c0e5032582608403400112441c1110015425100d008001d070450302c644200012a00036110041d41200c0f4240c80705c1d07046a49035141181281c1c0c0c5801240000c540a00c0410407200d415840410694840c1c100050f00340131980000c7c200c40e0b5507500c010b0000b0344400079598003680500501ba01c00c1000e000640c103007170440d4006605401950a844840c035918904818580c0c0d04000a0303024050041041009040c018500b5001d11100040c0e01c2c5a40944102401194420101515a44c0d00030b01070a015031200d90341d071a0320b10005450941103101c14458000036a603090024001030a02800a598840ca80800d05083c0520b450380541e162125401c40555150050b00300d030b6004165141c0160748050200008801503428100180c100e10089025403a95800081c480703031110007621200711582d16a4011002d85504460007003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 25679574 1250 25678324 25678339
    0x207030c0608041707050607031a010e090702011b02010e1b0612090717030d050f040203100f18030f0305010905010f03150e010207031805010203031e043909060302 72
    0x3007a54454a06a43c00c103200318400c44000c0d806084180542c2c010720b405440c1a0402003d000c6c0e215054811811032044000e82105004038040010303049803044402d9a0090b0708003030026010910170b500c070b48202541c0c20a02b220105c1003400081c02010501c510303e48034800e40d03101180e105a9009a600303104001401e451400000c541d048880000c0940004a284161640070a02d03890400401040000c880005e40d240c801c91048501602c0000d0700911064546000b1300000d038401040c3d00704501c403004800700300c00b40852080030003400322080750002c08080303200e29000c1581c4200048066102c030b54061086980701d41306041207030001c0c4501c03400240755480400008192000008412400c5100001c29076003840e029426a4414041140051485c000120041c40c01c140024040c210a00c015401c5141c0500d100c804005003d40c44001488604005010408402c4004010005c42a040100716001c0c00c02c0f0300c0602580480c0c40c402d0314964101003040302651003640b00700e035001070100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 25680824 1250 25679574 25679579
    0x50c09090103060f0e030d140a0b03120c12030a1406150a030b03030f0c0d08090307050705010804020f03010905010204050f0d0804050f12010c0905040507110705120a05060109020304120207030c 85
    0x90014a03c204e01401083c0d1036003500281d45400340301810349244005408150001103541011a1000c0100340c0c1021520b000f01c4d04035151030024229208030104035205543e03402c1d200446161040c4841d03002c108980020421a1b24400303a0005154102c013413440188a0f2101002c004d003511a00380c80301f40380e410038020021003905c250010901c4400160650303281030080c903140c0030f940c2d2251549050300e5102c00c0074203018990040c0410f501c00300c10b10180d0f060071103e5550700d0311010385104d202c0c108a04c0070301203819075848005038880e41c003009000704a0a00320380f40140c041d4001e842290321401070115003000a00344201d003020303503950200b0582c1ca8a810101013100c95a140308215401600c010316541c1084000d1240c94044840c40d00c6003110030749000200300544200515a00410541400348007455100044c0c3e00f068960456100c2c4c41c2c15007032000d5518003103962001411912510000140706130103035000b140101d011329508000340c441d107801a40e0301c1c401743c03000500c510001c2804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 25682074 1250 25680824 25680833
    0x6090402090c1303050102091503040b0a0504030311030f01030b010506120a0203070309050a06090606060504050d02041d03120906010e01030506010608100513020a0e040501080307060e010e070305030d050c09090103 94
    0x115500c000341c01601403c006a0400d010b69842c86500f0403034030340c3c0d400542031005190840003040c06e0015030000601c0c1d85003a40d03070030780d01110191400600980340c5c1c003c24109406071300482504000050b9594903440c1100b500a60b0000a10003035804018040c008550f5003004030807503010200d200c1c07030701c0680d880b5180010001d5000510300810075035210354010018000b448080c0c0c889000b92804903180c003035410060122035082d13008200340300040000700443c0c1c423420360402106030101c50008070140c0d407040d280e03100006000d07000014000091107808080c195580c29002c2da0f42d1804861003682c90307031311100f00070600b070001420581c00303d001007145a03c1b4010f141c0e80840c4007003040c6417841c1d40300c0215400018801c0d0f5451019004620900c5007584080c070520702080c212014030517949803200301520b9101c2c200e400340c0300320780340c1c0c1040e495078100350017410040d91203004484846943e801c1c515280e82100c55441070385170522000c5a0082c2401081d250b0f00d800c01003110b00c899181d940c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 25683324 1250 25682074 25682089
    0x2040602030a0e0f0d0804030302061303090b09040f15060801080a031e050c030a050909060f01080a021305182e0e06030a1203020307180806070e15040603090b06040506090402 77
    0x361640702c400740d14040c0c3d650702e6090001700154481c26407541c0b90b5056144c0603040c6603004009000000302c0d21010404a80c0c0284100d08451884c0c200c1ca0b60f805149020078043c2040440f00d01c0e10500308140c000d99800c42c440c0c403d044070303456640c5e442a80d0700d801d44c56072228030710240039000076a0445014000688601c00d0030100b0a503040640c07406640c808803505607000740203000d000c500c01180124044c101820380c2940400100c2e0b0600b50030002800107006058054060b51b88240c0c08a400d08621600c035040e0400340c04001d081c42c1c03007080e210203071040154048840e0201c00d000c1c0c02c000d150401a07100c94842441c1c0300e0364101489410480c40781d02c1c1e50001444154144100307000e00011600f400c05200301c1060699003d41e49140614020f001d080703030f407130000c42a4420500200030003000841c2c10740d0080c10600d000740035480030000007001c0c0410349240c0320708500001400512150103901c100e4549114101610550740c0d0801000200e030821518103800c600c5072000600180f41c00740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 25684574 1250 25683324 25683347
    0xb03070c170403060c02060601020a0605071b0f05070b0f0702010509010e04091b050a14060d0605031504110607030c03080603010f0606020a0507080303160302070203010603020402121005030102040602030a 90
    0x580900462003603101c1d61000100e000c480018088006028800d0103094054148003909500092181c3c0c1803d0000039aa500306000280078030b503031600441c0450b8860100aa8034510307201031400444c280e410114124030700c0640031241441148000038103098024155a0721544142c803150424403a500152480d60000c10424100000e4024107011940c03903200c0c01e0002c82c0111010012500181e6102482d984582c208600c10610302408000e9121102c03020700000c8002e40380307643c8a0700c0e19a80500505181d40000b50706000f030304041e10b8060b00c00442280309901540c0400c0c59007145c2024080340744102c40c0c0140000e8030303001000010a000f08002508250058000100b00007981c0003002140d589030800c50068000203604000d1140c10840003020b00700b04006180741d030801c0407241c181400503442034414941c01141c3c0006659084d03100e08002c54020300259500c1109418401180000b03c448003074140d044400403e05040c140700342e4013620f140750019481c280c5111000c3c0c90f80382820 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 25685824 1250 25684574 25684577
    0x1101020a0804080109050d022802060712080901060504020a080f100e0c0c0c040626010204030c1518030206030a0b04020903012307020a020109090f0b0306180705010507020603010b0307 81
    0x655401000400074002040100102000080c40c0b58803454810706000c140541e450440d8418000800030514010004c4c00343c0f4118200c4545103141807010030a14000c8401c081c0411582c609409480384d0001d00e00e81c890403001e0f00820480703482e2010481203001d0a008500022611800503107003e02d20b800c0706130402c10401281800c69078903103104150020450b1514444000810701da003c104c01080b00c4414403a08030740500005d030070701d01e84945138040400c43d06410340940032102c0703565500f9811240a150020b42d00c0b6440d903150303904900d604030b00f0425200014000010004140408449031040d603034000c04036480d648508601c0805090604081d99005030308107d61840381d502480740d089007400c11202881140c2005070a490704010040416042d50041490140140c0e803001009003603c3d10f007100050b00d200f018018000401d5100095900740c0b2807082802000381100241d80105c6d5641e0045a807400e80302ca00464403400b030079030002c1d001201400140680ca00c024060755002409 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 25687074 1250 25685824 25685833
    0xb03071403070c200a05060f0306040c11010603050c010f020f0706080a060506040e0609091203070f0507050d0216080c0108040204020717030a02070203070605030601050a0309060e0f03030108010615020a110102 92
    0x110780390b40b80451102c4e400249065214515100c080c01e00e0a4040010002151010b00304041d0915440d810310000b48100e00c615940d24400c4200c60081d05001070b00312001000300401074a07440c00503a50802090420b002c1091f100340c6400d400c2c4009600c60f0340c84010340c00742c2240340c03030030409555044014100449a80d26181c01052a45546018000a200905403014141441c4043c042002070140240302641c10106032001a00a0b000440350000e4091826809001d9130141c00c82d04c03030013031190007800e9000d0708264000740b0307034000f0703141161003155840e070b42d890307a520451141e0710440c01c010300b400701300c41c1e100240152501b640070b000340034010740c0e0040c207241000c42c60341e071107610071075401a006074086220025401d0030010040a00780904286103142440c2c00041c00314010402c0b02020191202c0942c1c0c01c00c0203a0300440d02a02c0c1e0001101c81040d403020030107490b0f810034094001c0319031034410000307065114580d0390f00b40240103030040e08840307025446488e4009019010981540706 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 25688324 1250 25687074 25687097
    0x809030d020c0601151412040c1502010b0906030601080a03050f07050f060106020d0807090302120f0106090f0506150702090406020f1602030f0d1d01120504030503040308010b0307140307 82
    0x1007400202100402103014040355030400c1c84034191800307009922010415a805851040b0800038201c070300083d030310211300740380d566607203445403a902e500d81128003014450390741c410f4900c1c1c054010a21070001154616440d80d10001410b6540009100c0d0301420750041d506100401c0c015802001e03000c404003441031500000da22801c1c07818085a10200c03942e4040001003042607412301c0a25018801031421003001c0c2040320303006201c1c1045010181c0f01c1e400700c4105d080030310700130030100211010080080c004035545a00302c100420049545800c418205000a10f4914003511380300e83c001120500c860612800760280304100e1002401140d100f40e0030040c800f9040301040c00350107258a0b00a003004001220320502d820820700e9a54940c1e203074400442c40c0e0081e0b030800031520340e01d1200c03410078524024445c0100c4400039903503181d020341481c28043c007041c1036103c1c00442c4038074000d840e140010b0b41d980344459450b20003201c2250000b020319011203884d03c2800300a40d0007108902e00802150ba = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 25689574 1250 25688324 25688347
    0x11806030903021507020c010f08070f110f010c0509120303090a060209060c010912090b0c060118021615110c06040b040f08030f01060306080106032001020102040e1006021b0f01080903 81
    0x907061702c810300541c0c0314524045040d83c0c0403070007004c1f2484620b8805c10504009401400700d100e101150014800d0300f04c180085110108031030341815001030001d01c203081c0c0074a80681a5070001c0e0006004001e8003c100b1106480001100d00840d5a50f0041c8090b003d15160b820080d08603d4645a0025041045c03440c038500034082c2404042c001e0a2508142c0560305015009500721350240c0a16842400008414000400e03c241120412401e11921120820401d0001c1c4504a2100c15260300c400030f00c8103000444168150888159104204200b00c0c01c0c10061180a10070710310855901090002e000038030016030858110b84070f84648a50180b045d603d498050300100c0e000400d04041200401c00c40da41406400005c01c04000204200350550719a4900c94075203030841d4903403030b00c0317544810000d901c00d5048a000b408000b103101117504010a0224140410b07104040051107414500ca2040ca201c5000c81079851000f40702c0688200858010740b0320940043c01606240020300c401100507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 25690824 1250 25689574 25689613
    0xf0702011d1c111501050108060409210504080304090906180506070c0206040e040807020f041b18050a06020312010503010c0801050f12060a0603050708070501091e1d01080c01180603090302 83
    0x10744d11040d40d00941c1003100040001d04c00402c854461800c02601c0d2010070002e00d03030220306010102207180b608030002c0e01036071a40b10b154072400b160700c4002030000b000f2409512112195108107418850640c015a08801500e148040640320b41c0254011415450286000031b901390310180c8401e00703060396003032040c04d0180112400e40390040d002070004110700d03101200c0c040400d0106d8040142c0144447e07201540c003007003d100824402103d64008414002c10030900c0100350040c100000c0580342c05e0029200c1d048032030070f8031030499004004581840c0c1030007950000886075071404aa44c0c0b17004100641d800c220107079250000b55104141c05840e5041c040c3c90301c01c1e01101c1c00858102c1c654901985041040e510590301d981080700c007800380e41c1e40151505d040700c0c00c4800307c0d0303025400341451000904441d80003009001c8200e1814003d40182d01c8101d04071014042907030042d03a180401912107010f030458081c05000043d0051182d107003c0d070b01c0194028007030301c11074510054900d0754070b800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 25692074 1250 25690824 25690843
    0xb010f08120c070801060b03011d07050417030c0105040507030308070806031c271a09060a05071b090606030b04021e0c10140a0c0c0302210f030f0702011d1c11 70
    0x2180e00000c014000d01ea4000c405640700807500300c11002b20324006800410a001d14000e03003c60003407403c000003a03008200107071490010900000c00070303400d241c42c003d566141c65120441c081400500003c4101e40510040e52103614041e002c1c0011200e0410074040e0720324a0360180c1c0920140090781c180e140310311456084d0300150301c0401082036080412021055004405284c07200501304030030360340c5856110a40b488160a03090460702c68120b483d0000c1d0146000860302003a82d103140000660282640190040343e800352410040190164180300591240200c42e1110800da50001d55074026500d00070070700008190165450007801018000507985c0070900b02c241d410b442d106000404c4568422000c0a9880f41000c02c0544a02d950103900e0740e150511445440c480d54442c03411500307030402110801e01e01d6600540d030700e1608201500407000c0c140c800c48019880d14001c0c5090040070b010031039288042c00c00070320039000003c403030312240d030120001482009082e54528440b0071080210324074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 25693324 1250 25692074 25692089
    0x3050f0c1603020f0d0f0204090c0320011d0303030402101101060612050603010204050d06050703090f05011b0e1503101e030b07090e0708130813030b010f08120c07080106 75
    0x2001d8510f0040285542c280402c56100e80c0c01c04200c200000c1490301071150f050760540740030030081650308091030f08000b0b0b40e002400c080250300c12103100340300620740b400303000340c090f221260180041c2000341845820b10715295010b610420100b009894695001c00071440b0b50b142c002405911081040d0940d0851303480341d40480d40e40644031414460340d02a00c0d80c04941500214100b914060002e80c407080c5000300034001d15524400301c0c048601ca07811100c2110703001000b20500c0340f20f500c3c020340200b03180905115440010110340c11079601c0340c1d0000c0064a0000c00401802c01a072880030001d92010741000211840510001508502d005241150304106020b120000789181440c0c1c080c03000050001c020406005401e00101d009a01400c2e0001c00d2480c02803244d903038001540304a800d00c2c41010384508008603140050020b603011600659200c0e02c01c100c040c6e6a5050801d81240590141110f036401984001c0c0d83e89e003003e006007100410034400c1b41e030701d203998040807421070301d56410814 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 25694574 1250 25693324 25693363
    0x1271a0702040615020601151205010e01030506060d0305030601180f03060504030206010909050304060503150405010306050108010c03110a110a0b010e160e0a0515070b01090504020108091903050f0c 87
    0x39482c05228140003080302599030300340d2052000c4002c2d2109014040c0e41c040c64032103509820300c18841c0c4807400700310034640010051542c540c0e0580000ca00c2c24441201c132481040001186c9083c800c2002e40c070103038107807217060941e100c4000540d6200f00b80c4240c10112981c9139000102c140d4061814030041d03009900000d00c40c10b06040c02410301205800c04525141040b10180000e03e00108960840d1300b289010b5489841c1e60300d0103810300d00b61801d15a4030904000010040c40a66403045040398031601c02044034000c14441031301501d6202096681c007036814091074115901500c0c010b1440f07103071003054803401000c0765500c1c260200203030000b0360400004d904009481c00da40c2031b002d01300c040034202082c4a007255800140414128020b2030b0052107a10310300310301c0000340e4042e43ca003984e1191100e001580c41d14201401050100d0b002c0e030005030f0b45004030b0652030000c81d20403003c00d648104641158680d40b800d03135117588140e00f0b0680d05142000b2546c90241e0900c80d11801030904000780707 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 25695824 1250 25694574 25694587
    0xd150504020f0a080303040303020a12020a030c030501050109030305071709030604030c11010503010509070e040605040c170a0b0307120318121103240c070203070e011703070201271a 80
    0x10b80e80b520760300c129000b00d034a036109211680f00001034961265140c6070249c2c5d41d100511088501c41c501ca200e40c20f40c036001203109c00c07002e5050780240607075100b180d03410003150b0390322001105d1880c070741e22014011400400040c1c000c00c0d6221541c0900d210004985842c003940d01001c82d15109003100c06030b0000e090b540216003040110740920002060900e4182d0a550502c400181c0403c0050140380c107200800106001c40d4485400c000d00900c030060040015446401000c2e160304c180032101104000e8400c002070341d444913441480d907240c074050028040341e42010501010703414045420750500031031145d00c00515400602c41c201610045800020f20321580c13070404690310103000040e01c2900019182803245204002c46080070050401c1c5040c1d5480c0d44100c00054420b00d00c001e50540640700c40495059440803d45040347c00a00c1303080c1c03056504000d419224007651030001d0001d41500070300720b81c0110486501300134241240d1180039081d03450504000d800040c00490040d5240807610 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 25697074 1250 25695824 25695829
    0x24070803070c051006060503060f040b030f0318040207080714030405130b01020d0212180f06120f01090b010c02090a0f06030303050106260c0310030c0f090c020d020a110d15050402 79
    0x1150040c45485000c5c0300381380c00d204006d402c50000500040c0660040310f1b0060312a92140c201c803540e82030247c1600d880c55024500700b5103030740c0319044c0800300e0780560407000200d00301482210811904500110b0030091190388550f1030300c1141006444a02c01480045525914000740744554429a1000140000030301c2c0060700300a044240b0609541103445032142c400181412208114440e02c580caa40c40104000580c0e401500386406422100201c0c3c1c00450711503050809008800ca0840d00001b40e80c0c030840c0c0410354041001103070008401c10401401414021341440d000a1000400b10b0102d8561007030304100c0303156500580012f0f40351401004029040001d0030112801c2c600b0324001c22040c03201c407001e611400741800303040c00400400181c2c0e03403680e074008801460b403200300d6400869480901080340100d0380074403060146801c0d0b00e2300d8001d000060814004846030081c0540c0501501c4400c128180c2c40c00305a04142d01d0803500c40051240c29010007603080042002541d0b0809005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 25698324 1250 25697074 25697083
    0x70b04030606090b0f040b010212070c090605060c121b0a0f0303060902071703040201030e07031101080a0207030e1026180109080301030602090303041205030903060702030924070803070c05 83
    0x1983c2c800749403030f0032003805031180b1510030151242610f02042c89211500101e203842035902c6c510120910105101041240080c11003040382d880307040a12425403541d080200d00d210b000c110b84030a0f800650013424a40d00c00c406440c00e0400e581200d2141c0e500c806c4804d08184a80e01d048544210038201182059003500c14040a0f0000c41001c50030f00c0d0700e543d92198543c2d0140011220054044000f40440e0305c6500601400d1022505980d0003907581d01d4004040140e40c0065800f1502c6100020324501d82c41c420303240c40580607590826088149824003001d00350301755500c01080400c1c40001c0b101c2004003c00001e21700d030701c4400c0c40301e480d000b421020000031443c9440c0c2d00f641081181c0300850726030750a4a041d2500f1000050303441c0003020000b4554429070b032281402038440c0c00d44001f40840880a082ca4500079825942541d803a100c080341c90388600348126511a2020721610004d51040311050100c14111405510380000c035105c40c10b0341c0d04100ea210001803542c1d074850041200c00e01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 25699574 1250 25698324 25698329
    0x21090c03030807031401050102030702040504020a0f1e0503031201051908160810140106080a020c0604030809060603060105151605031801020708150a0e01020702090115032004060503090708070b04030606 89
    0x5c0480302075051100003502d070310070318101034070494862020405664422101030014454188a10342c1a07036141244440040d4504012025054070840020b6a040200441f031030461956402d5910760300741030400003241e01c000c405030780c00581482c0c003042181c8200304c3c0d081d451101c48881c11b8180c0c50301350500d150454811f02d40f81910700300f091180318405940070082c15180700c1e0078488465076518440c0e0000340590084500b82e842032a081c0014190088000ca003d0f803c400c050760113503a10b4005140c1c1c1ca01003031080a4100f8200b0ba20343c1140c080c1030001e000e100b031a4518403e5084200d85506155820548a040d50100b84d00000c0e40d0b190717010000c650007003110402501c07070700c0c11081d4041800c0c4001801e52000945415616030b5200c42036045a00c0c65600402107003455850b03244885000e584500d802e0082498901d06028925a0ba1401900d06400c3c841e441d16243c200501110039400241185038079100e08274004c19080014803078100981000c0c1f0700c81d41c80c0c501e10b003404002d035115607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 25700824 1250 25699574 25699601
    0x50c1305180714070f080405010e0909070501080a090501060801050906070c21030902040203040312060f030507050607051606080420030a1b0503190203010b0402040621090c0303080703 81
    0x2500c01140340600700555980c807124504080c16018041d0311a00c00c80c0c4540c00008040c03e901703c44403810440114064400c0d90420b90b02c603034100083d8801d000c03500c181601c9409050340300010400641d0300c580425980712880c0800840e500825a86035403c0d91030030b03000500c4a075100d0041142109042100c6d681c03041191030044c1901c5134a4440258800315501010307092040d42d514251a14080c4c0c00024815074050400c659a14103404c0c014003a21454400c4100300341004400200400602c5200381a40d8010307001d070011526100030040710340d1002c5130442da540118034004042c0340400300c3d403a0040440d40c0f11345074580740c1854015030400c5501042c01c06a010010515116100059210100d50384103804403071004100300d0b220044180c551102e94148540d100c0344858001403400000003600c01d500910240ca448000c00099000302d0013101d00081c08203118001540c401052448540b04ac8540003034810341c240c40d1284292500c0c0c1054001c00c10603414041111740c544a0740d075807500503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 25702074 1250 25700824 25700839
    0x80105060f090705030703051e07030506090a060602030906031503071206051317030601020f0105011502010b04090215030c0405040903170f04031b21030603050609060601050706180204050c1305 85
    0x96071018213680400350070f8104140e640c41c00101c4641601c45007845080d124100904240342c5a80d001b40035000842e440c40c0900000b0010515840c1d45020701c1d015100560065424014440217100240c0c0004020014001221000d4052610280308000150400c003090315070441260429a0030b0f204050100d0032011038406002000c1244900a10952542802c0359503486d00d817a80100d00c3c1c6180d10881c5000d40d480c2000014001981e6035000c802e8910302e070000e02464518000300021035020050194004c3c803800a83c100e00300d01c24009651003403510402c81c1c20151070340c1c0420225404403004034041100080c00400102e041304009601c140300c42c8481809203407541d00101600a805002160f41428481000401003d5004090384100c805c2850f480c1000700316000f8040c02070303031206681a0050801103410141d000c10040d11490303040e1246882c1420a60b10140281f4060030a683c0d02e250720007030080180c1e46c1d802407600408601031300303a40ba00408142103055025075405207100c1c415 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 25703324 1250 25702074 25702081
    0x512090609010804060902040516121a010804020312070503040e06040203040c030215040306141e01120201180503031305040e01020903100b012706080a050c16020103060f080105060f09 81
    0x98000c1107866440e001e01c3e04038226116841c10304050008014004d6005081c0002c00090004404d40c14500d001940e9500c0c1c14013800501c00e80403142100d02e5440071841580d5011001e500443d19250014030242c21141d100850642c10749032504103400403526a0000030b010040c40341c109800ba90400d00440d01180f4604041c0e5607c42c03076840d03520009014640c420f8480d82842c00740e0050310003c6030000010711441c1054075801c80c6041044880c1003030680d13062129440134810340c404074140c9450039058210980683c00644050891845036440240c41d00c80204081d1001e0000e0600c20800c0415051001d0a100400080c5c0c3c4c80a0b00c8983c603a8414011000260740004c1d42c0c100b4440c0008001403500c03000c0004a54880845260035400f0040c2c44807016141c80148000d0115030640e5111051303602c80d62441c07000e5880a5405000c0d4650911000c22032502400410507410700c141000110540da84a00f03114001c203603404030809954550402c41c0c1ca01f030038030452120803c101c0726a00c40d4034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 25704574 1250 25703324 25703329
    0x601030b0a0e0712020d0608030903010c09030201080f10031502090111060907060c020402070501050903070519150c0e09070207091109010503010b07030207030501330503060c09010c0606080a051209 87
    0x2d800400b14010418031440d581c00e400e081d58102c0e8913081040105020031070f15038610075600e620140401d40290318021003401c0740c0e0b100310804000d40754140e503401d16689801e83c000450350005000c8240d030070201c4200000103508550224031005801d500940c4922124001504440031100b10110b0740d0004820440000004100c14040d94503506004840f01203500200d0700074000c200340102190300c0c1001b8007002c400b0001c0901403440c4264200c561070202112003881c5040c11900050081130b2461640170107141542013885d4080302840c160b002d0b0a807000001d011054281c42c0e000c0076030000c1205000915980c080d404200c241c000751186070280480000340746100510a0040000000c10b211080510900800000f10380190090080392000c02210b00c5ca044a010200382c0400a1a51010100c09900e140030441c3c4c0000c0182581c1d98501c0300502e1b1030f070701a0341d07002c0c1046203002455001414a20658020380403580041c4032907002d91429601c1c10018001250780400184020215607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 25705824 1250 25704574 25704599
    0xb030106050f0909040506041e03050904020313050604030509010306060305060d06020702120a03090509060f0f0105160503030405030406020c06190c020f18191103130305120a050601030b0a 83
    0x4803264a070540c0e844080d806040e52a000c0c26400652020000c000d0100f40071002840b9405240501101c4d11103c000f141d00441d800101c03403000f00816000d000480541c5447d601550780602001c001100ba006281c0d6210708210303044608901081000c1000c90303095a04d8840e240107400745007010051410701c440011260f0300d000b400180083d400145510442d1522004c00413006007400c00c46907241c10a02d80944802114050280243c00c1c0100050a1b8549884185007224000e0110002c01e0804801100d165000110100c0c0910528014400181c400c000031849213004001443d2940c2c00c0c80d200a00702080038140e20320881c818411140c51040042056030701300013a0800240403592031010032014080d0300d0443d648140681d0440d01c5001c2081c01702c601c581c408880006040314144218130440b00100d4031060030030400d00000c3c0c010184040300d0390845000382421404c0404601028401c908200c8155400729107801c00c2c8007075541c16020b100940e0a00301d400e254964203006255402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 25707074 1250 25705824 25705829
    0x604020703021504140303010b0a020c0103020315240705030d060905070215040c0f180c02010621050a1202070806060a0e1614130e13050a020d03050903060a0e10060b0301 75
    0x40f0540101090400030140042e000c06006002560b440e9a504d040700e46164102e10b0b01040903000301e0150302ca85600c6403085a20900c02581c215225214070005c1c00807501e920604000c0090000c20300e808040b0742c9a001d060190b00c18802181d6901094a2040640c0c0c1c10f82e0040304c1c42818074051000140d00800e000302800020295045150364500b0441000c00c0c09601a07540d000352040040340c51000b80c0c210f45082c1c2c00e209010f00860741c0c1107804038202c810314802d552003400640941204008100701c20300b010b0340901c048a15446680e00e60440d000c4141008501681c803c40d4100008072060040c540d2102049404075286403515040a01d02c9000500001e014050300c6181d15030301d80102f406210305c520312000103844201440405018040e54055450b241841c8400a08108600c1c0c02c0601d1603a4420098083c00019609001c50800c00440c101c1c1030081c10b000313200d0b15840c01c00000303104000050010940304d00c00020a810640c500c04100009410810107116401504044904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 25708324 1250 25707074 25707103
    0x60a051509011209050a1e0b040b0402040e070602070b07020607020604060306050913031e03091401050711010908040905130609150b06090904171e03010501020d0f02061f0e0403080f060402070302 86
    0xc1f05202c1c60181e001021448004089103410014841441407590b1203512840c801c0e05d00b0000d4002c01005030755500010b00c90940140e10160050203044c80d240054500c0a02c0030781446e00740251640050001d4105400040000f035440508000c6442c0404103540c1040404200e4204c20203140c40041048590380f00300600001d5203e526070100d4441e62180c6c241941007074001e5801c4500e260100e028240c01e80b0540009083d0800c0550510313011700c1000e000c0b562010030345141030310f4640110042c18004081800880040c500718011a1150113007022092065084664040e41420001d0441c0c1c510010507004032400e010a5400c1c0d00d404100310b81140e00311915241200d00506030103500e01c00d1020201103d14100203c80500c3d0015000c3d506076a401d800765201c200028070100c071842030304410b61005a0010000c610703203484c084030740e42c86208080e400c05a51a21550080c00250040d50304070000750303021080240c1200c05900072600002d04403800d5251800d40d45000b0341d41c0340407581149 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 25709574 1250 25708324 25708343
    0x5120309061305041a03010509070e0a050405011103040309060f0311070b040c05030a030c0506070c12030b0102010b06160303050f01050a06030509010e0f0703171201060305060a051509011209050a 86
    0x1055050209042c0000b0180200280110100d04110684648040305000d00a60a1001013100490046a02c0f0185c5100c148585299a034000300c250282c04042c0c000d035003079541c1c0c1c444401c242003960000e510450207501c031070004620303003903004000e21154007280c000c0500d44103070a02030343c900c0c504071102c481e000743d40c4a510b030b00c0f642415800840940e224990500c2070003540303010190052002d14003e8082d03410b851007951131071800c6e224446d0744000101410340e00c520090a4502a5121461f00d00041c400015050210004220f4a600a005400b03144254421007400c059250281c00c0d0f101010061000322945844007203881a4480e0050000b855105c0001401249003540400c2c0c1c2070719040215403240041500080d1144010300058420055a210203401505a00d0403a0407030313468211480340b26031038604100e006000203000c042c2e100b084d02c00006070580c0c80303001d05002202e4040700203a8905004e800500714941d403c4550540c41e041200b54001320740080340740c6401d1070300f00c0c1d040c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 25710824 1250 25709574 25709587
    0x1080612010605030709150803090114030a0b090705030103110103092d0803010e040c08030711040b0102100f0606030e0f060a1503140d030f050f04020f0604090f02070302070512030906 81
    0xc0740549501d802054041c4225a0b000603d066a80c01c520310b84c1045a05d040856134950710010707200c0c46407043d4140070912158600c402031040e5801554441c51040c800160040d030070001900c070340400e81c0d08030001100800140b09001c0e01e91883c010400e0b007400c0c01c00513021180e41d4108808109251807054a4152a81a140c0c0140e941c01c1d4003290307400821940c3d21368551800c400d000e5826501640d17034504000001c924460008126264950030120400e458040903041002070080340103414114020031000d0320301c1c2aa03900800303541f150324640101c0c1c03050400500034100c808506d5991a03603813100360005040e80300805d4031500600b48280100b82c1c440030081c568001651688001c1040115240002003003201280786509108103030b900340f01c2560000700c0e41d01a5001642d43c0d1589050070780c0410300600d448100c800d00740707001030001803d15940d078200d0801c460294441c1d005050300014002d04150307062220345c003d003034110342c0001c20400300c015040d03483c01170155980c0071b5000001c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 25712074 1250 25710824 25710859
    0x80708100503100f050603070635070201050114010203090904061505060d0f0c050705031206030f010f060305070801050118090203010f020706020720030d0509040204090509070e0f06010806 83
    0x35005001c0c09800c803004070281102070f400a00540000a404c14640004a0101d00d4081550340c102c8a082c0c2c5e035030240d984103020a0a4001071000d1400b0089035918a58880c0c9803103604144c8281201d4000280f2580350884514015a5810a05d41150800c020b81059030341e41c118a0350300300b50801c20010740d4040c940b480344034054680d0402a4419804030f01c0b00130081181c1c01599030740300703012814454980045015900d44c060b6000c020f100c1e0300f05014070300c0503010300000d949c2d00840007030444000c5426000da080c21030701800400c090058a44a042c42408030811124008002183c020010341d0f01d4007001049880d01c29421030240ca89619806096640035048000c400540140455945180e40b800c40002d500c9040c08071242040b00d46c2c0d14120700c1c040c883c0c140380b001010300a0401020f5a90b812207180e4099045207034455400d000101f40c8500502c681c0b4410103990004000081c103141200341c02d224000c100c0d6141102000420107540da02c00710407500407209543388034003555410403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 25713324 1250 25712074 25712101
    0x8070605070b06040608030c061008010203190b03010f050a021e0a0203040303080405031207030c030e0a020109051302070813081e0c0f0102011409010c090807030b0403081e09010207060b030607080708 88
    0x6c0000944004102821038020100e0b42c04d01030002c2802201c43d241da1048bc141c01d03030004845540e55007040c809034291541180c3c120f5a00303010003c0000510a05c0710100c00122013055820900e0544d01160f03012070242d003600e12a0308800110820703410000c4208000350791f03100c1d5020040402c03c0c1e440c085002c02c0020410f443e1112003001d03401c0c1103450f00040040c0140b030802c02c001c1c0024200700f412203004202050491486070180d4038000c0d00f50404052111603940200460001a0f0810501c0d01141c403c0000d0004052503521441c280c1d4505103010b0720f40841000420100d01c04008035400c180000103462014441c1a510b4040b052000b00040c0c0c0100410b0803200b0b0301c03c84100030409018819405250800500d0301c3d544103042c0c4945400d1380c0c4d504140801014042100c02140109000d5002182d100301d507038004101d00110038480c13080140c1e0543d0f59140781e03900801c40c601002914090301504000a40003007040f840e01d0700004010305400ba004d44117200903980400d110320700c50f60 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 25714574 1250 25713324 25713329
    0xf02060c0a081e0c0601030b15030106030602090108011d060d021219020a09020a021504080405030d08101205060402010e040e0708030409060803040f0603020d2c060108070605070b060406 82
    0x109840024141d824100358541c8440400340c504010000340c19009607101081da540c07515440010400c5a0965807200c8540c44050301c19a210407580c4010000d65800f4003501c400b840c0700d010f001d40c1301d80c0b0303420014001407410f8000c1c05500d42c8104241585c24a50324003254018012219028544c41074004590101e217582480700260141c040d05841074030309a15420922403081c0d5030380300e24a548034001c1c41207015041e9071000603080401c42c6d00b54504400c031031030741283c000d4140038680faa4400009140916901000002c101010200880d0f058a2501000100384c03003000c01001c0766555843c00d80365000208000c2c18001d80d40f5029405445607805007000b1104081180c081e241c4070100e10b0360303e40091065044030ba0801501080c130000c040107850480d64056031141c0103c0c04c10606801941203a030b80d410580740d849091000e012020764600307507017130440311880000302e0003e2a03250070300805030000310070f40d800746104001382588201203a95254001410501c5a00c525000801230140c1d90b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 25715824 1250 25714574 25714597
    0x1103010305010518010209010e010810120b01060905010f0e0105070312050a091104020c070302010c061b050a0e2202090301060e1501080a05060d08070503090a0b091017040f0206 78
    0x40004020008158049401401e460f1039440100e0344241d42c2074283d1040014003400514061001052940524411a0400c0e01031f40600c0341d60b80c4400141c0e000305181001504e400c42c1e1030004100c130f80c2d0010b0a10015140030f1a00e030302e0804070120007a110f448401069070400c640062888103041c132940d0b000d031558680344024401c5080c510010300140441801c280c80c0107080a400303c1c0545482d100310f070080f00005019110703207891600103641040901000740d504544a90a0aa945030300c80c1009022020315103680d500c400190074010f10480c40c440c0307414010001801410305014804210902d4041d00f0b08025030380da020080030031701400c0c00b03500080700b04105c2c01c14041c0304228400e080d03031102020780e5404400da42c1d070000c0b04140c1d042994000c0d080124021000003103020709008040a03030140086a1520100e00c0105d8125103044d0f1107000d210b8004240181189807500c100b000298a502c2d0082c91540f0307001190900741405880200780f440807440f110119240e01080c1c03050340c0c00c034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 25717074 1250 25715824 25715827
    0x50d0f0c0207080d08010305100c0507050303070305070f0503040c1e0302060c010606180b0301090b120d0917010e0316110901060804020a05011d09040615030311070506030108100506010311 83
    0x5a0902035561110303405a07103c28010b8040603c00300707204140d81030480360020010a1501585400302d030040c20801408020081d003003111101056003000194041c1c11a0b640000b0b1501d0950001442d40443c1d0394205d04025040044c0070105401c40e0640c0203441914000044003110900290308440361584020740098020a071801030340750652008040b81c000b501c88d07455440002c41d000c52078512501441408080034030051040540319031181074100e401030444103681000b40441850510403044260015640c0302042c820200c01c500000c524540302e0340207010960f100c1c5203142e101d00402c1480840001d103460801c1c180700c00c0914000e5901400340c00c038016541c554500901a001c12182a40a0a100d42d0009400e505c5160100164805441c1005140504070b040200c11f0308013500507122280c481441e021402c0d407805146c07004510079124071100c80300e4200400d0804c4242ea01061103010103000400400c88003203041460317a4148980000e40b517413200700503030062404441d4000601c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 25718324 1250 25717074 25717091
    0x309040e010204090501050f030303070e011206080f011d121303140d0306080309131a0301020412020a050f0105030c0a02011b050703020c0405010513020a110307080306100804030f050d0f 82
    0x40640c000c2013a10344c0040c3c1403105a883d0810b00011302080c246140e0554401c00010ba106480b4141d000a40101403600700300080b002030318201501c001d900502d4194200d80c24031800c20f002441002b098540c20802003030814134000045031a00f0121070f030718171100780008400112141101101c0b01450b80301d600c4031099011100d92554941b13610f010300020901e400c9002c942d0f0030380041550700f910030041440c0104160070324050301030045000420910041100e885446907020300180011740318040b801022a00c650040140201581e440640220054281c030b0a2a9034400103c82c1d101001c0000d050340d450046000300d00406142002c9607602d00550903080da0390303900c6801070528a000360f08440c2000a4402000100c417001c1c07182d180e110202410b0700403d221940c01518008400d8201840d440442030320507421340d40000000c50390810b0002c200022441c082141f03d6651203245001d585a161030740d0050822062218030710280300d004264668040c45039007186e8103c81d001d6005000c19031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 25719430 1106 25718324 25718351
    0x31208091b010309062f030c030f060a090c0203040612020a02060402040b010504080109140115080c1c02120d030506030d020a080d091b05030601050d020904030f02030904 75
    0x41d25003410b040802d1003031195961003400000e040e0443c0091a036100e00c414a1103094986d980f00500500042514040903607510482300b1544803065100e00000803503100080e0b001001c0c00f410400c0d5061a02c4d40030025000321403c988031612540d00244004e802d901541e00c0344c0300142d0165000a0141c40c2a0300715612210060500c28035040d155038615003580c581031020358010042030641d00950b4001d2080d001e4140c89043d048201c142000c0301d260711800c16a0034184101d410b0b020b0f240301c114113500504030300c940c02045490082c4508403040d840c0c03080e000d44200801e142100040640c1401700f03c0b581030143c1c80c0d026082d41310310350340c4448054200b0501140101d0b5549081400141d41e2084c0382c8200324101e0b9000a05494003007010b00e4041c058103c0d5000e620102c24050041c0c46803040c481c1c0282d40340c2080e182161102408074030354080c003000703154042d0a1818501071b50 = true := by decide +kernel

theorem cover : BRFrame.Cov 25539574 25719430 := by
  have h0 := BRFrame.cov_init 25539574
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25539574 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 25539574 ≤ n) (h2 : n < 25719430) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
