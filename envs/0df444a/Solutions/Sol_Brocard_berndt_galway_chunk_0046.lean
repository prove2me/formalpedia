-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:32:37.192232+00:00
-- url     : https://prove2.me/submissions/ffcdc549-fbab-42fe-b6fd-4351c2879c95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8093532 ≤ n < 8273388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 8094782 1250 8093532 8093537
    0x901060507150614030709050c0a080403050408010f02180907081303030f060e040201020f060f061c06060b0301080d0c050307081b0a2001020c150306040204050901090203070201050601020d05030403 87
    0x81031000c200d0620000342071584810b004200e01c03940c5281d028940301d901d03000300c1c1c0309001c0e00c100403980e80114811640038004c84425641400e44416098640850152040e41445800d10000804400900030b549080301c1440c400758440c9885604001c00300210503009200d40101810020f813243d108a20b15403188440088145810140c03d003500103014075060040e0641c20708001140301a8034661160090341300f80e0890388402a01e6148688405007a2401000040b900010841d1450000c6e8040050804240b042054a40070350342c038801c1311801c0d03015a100083c040010802c103281440a90090307600341c108207403403c40a0f500c207520ba100d450740c0281801c80100b0101049202a5600c5241c040b40c4411078101c0c83d05c0303013000c03204485072001411200000e1154503440d940b022890101031100030b03050366030029800e02001c003180c0005000540ac950300344800a066070303600110307600a000c040401640c0c1e0a09010090940b9402080070f070542d8000f80001010f2580001240d0348940c040c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 8096032 1250 8094782 8094787
    0x102030a171003080403050606010f0906020d080c0408190c050604030308060409050102040e0703051609050906010807020c06070f0501050109060308030a05070201020d1b020f0c030307080f070c0e071b0209010605 93
    0x940e580600542e0381e400141c03031808041004000c1201c0001c005010741e200762070765102040e0310300040790144028041c250041e0080031170441c0c194002c40600c1e03000980c8519050926440b0600c0b2440e00407203035403c8401100d10103110040c0026111000081d01065800300c2ca014155100038210b80005440c840c0100c2d90342d18031905012003903055a018012044500280e42000a00180948019180190340385103100d107011040e4001c0d4400340031640e002d03142141c1561a04010741e50164018014425805035240c030345d4031603903040e00905d001845034810b11414000741c1416401c6a105070009030100d4030701801803010407400406d8036405640c203007004c5040d0b500c0e068102e0290060680c3d0210081c10308208081d0741c2c54000c40303091100c210b0350868500106101c1090399905a500d0400d07095002041403202150006005041c43e85e22641818680055651005a1103809511581c1403c140b0420301842d035034015186843c03107180407507003084541c032900000d594820610901c42400b100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 8097282 1250 8096032 8096041
    0x7020c06090609060406050714010903170703140c040315060803070f0c0503030403030c021801051f020a0c081e07050f0f041d010e01060503030c0a1b080304030606050406050102030a17 81
    0x240e01c03c0724581e500141505444c0c0d562420302030601e4000035801c441240032040e01d03c03080303407052080108094165581c1300825040705421482c0840c0034100100301074448010051f10103c51515034018a04000003a50f914554100482142c44031080d0201c0503083c00010001490000141d404550701301d00b0100c00ca101900e00541444c0195000703903018000840c000042c5904940c214820078000d4800d40403034428400540c0487c1c10902402c0c0d80207850b80d800440540b40e40e06001c008041c05d004039500807100d41c83d04000c451081d800f00c180350b4004581040350340036264000c2c01000800e0001c0c090700c1c2c00d1000045903141c10070f80b86405046001c4810341c480d030b11900303c6203a04071040b102009103034003900c009002e40701804000100b9800c00f030001416040c000110ac511507803800207444442200d5861005448480c1c1200003040c40601020480d044c007480100010b5218840010f80d1510b45001d00c0705403103895104074195003044c421034a2003500700301015007900c0c030000c01c518543e44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 8098532 1250 8097282 8097289
    0x30c08011a030c0415090501110303100626040b04050c030604030e010804150903090302100c03080a0c0c0b100305160612050c1b030c06010905100603020c0c10031e0507020c0609 78
    0x14652000d585c0e484403c05c896205070300301d10008269036003a40c8010b24a0300c03560100d41d50384000d40c0c0c0c046903450350a00070803089110303000e40c1600300c91f02c680844000204071840f6400001c269401c0d5400d034814000e00007000010001b074401c0745015005010340b8686030300c025200c090401780300303814005940001000c0060740e802c18801e40c1c00c0080c0c01c02c0310142c20309008014110034001240910001c1c1e5208429074022918140c80e1035150b035550210740e64807d044805010110304400c284144c51040d50b00080941c804a48a080703070480c5c1d003115500c0c5040161402d807400c0d05e003121000b0084d2041c0411548070b5070304040300041107408600c070740b81d0b42400b9207a44981080d8581116004245508445010004004004025045a8003a43c070f4848e4241103403070503034001c020303455503450811105019402600c80d2200300c1003039607030100c0358002181030260a80d03c0040001d50355100e00494100000320f0403c0c034000c0c04820482ca01d4a00d4000e5a1500f448002c4c9118032008502e502180c2d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 8099782 1250 8098532 8098537
    0x308030c0d05070804050f0c030705010302070f06050103030503090d0e010806010c03020a050321010b03010b0417030d1d010518060a0b03030702030102070503040e0c1303020d08090a06050901030c08011a030c 91
    0x40946038200120f107400d8a0080500c40c068400702c030640074001491450880c00640d4202d28030004028112107850240150000d61001100712514804003891700040b0300f0521501d0f00039030103900c03110368070301e0101021404c041c04110b0780010f100c03a418208c801d60b40c0c0b000e5425440142800d01100302105410140d1601618a00091080c84005a9036511944a018106850805000d00055070b620b9004101c614002406283e06a1360284010003644000441c0869070910a505903407a010354501c0710026030307020340300410201164232141400345009105403035110710541040403030386200742c4180740c888030040c0460300b05684640d400481c80d0b4052089641da15402402191342d454103252081c1c40c0d0b002031084080d1046a0760024403145c0c1c4074802c8504d01010f42034840d09590860b030801030b4425620405985840040c8020043e541b196441c400140031651200c6840e4040c903c0010181c030500d0b01010308025001d001000907110002c0c1500901034400f110036102d6a6200c400c100c0b60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 8101032 1250 8099782 8099797
    0x20703050a080c0c01050114011106060d06051e04050d1209020a0902030903040b0c07060905090c030c0a0903060c03060302031e0a02090705070b04030e031203092508010603150f060305070308030c 86
    0x15440c000c0005400c108c03815440c90010400c2e220700101c00c03801046aa220003040764016042108075900740000350040c1e20190380003203d90031510301c0420b031590483c005402264205d03542d038440d8412a42140c2c0082450346c4030000300c0d4091180d00420750101e48071020381d114802001f60044041810740300e040c030599000d40305101c0840d40301e44840c41c2441e5190280c1c0728100100c1d10203030300881c043c00c04a00542c4101c00907600f29107143c03a01040e40c00584d0100c0c2d0131404001100c0c1012001520038042d1600b1020680e50100317207681140101070401c01440b41c1c01c6580b0f40c0000800400d540041b03581d10f405501104c084196a807041c0081c1c0307561141e4800141080107040811003013640011040035428400e804954040381f0141141000b84002d030703128411544900070b0000b03d400725031090542c07850f0040001c2010b980e1000b03a203003904da0a810403941030030840940410b00c6214800c0350040500e1031020b204480c59a2191511014140005000c030785000000840c072140740c0d011900340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 8102282 1250 8101032 8101057
    0x30a03030e0709020f1216050f0a030b0d05061006080702190203010f02040e0406050105010201020f09040b0f0405070f080c09100c030309021e01020c0306060a0b07050109060c1110020703050a080c 86
    0x441c04105080b24046e401920281c1c800804100071461410140c82c283c1240d601c6901d0f220724188840b902e45529810043e0684105602d1344901d44058549604e180c500c10301c10b400800150401042d403c001490a4110800300202d0b80101316895600080d952242941e0810040c804a132500210b03000d40b100400f4008040c2c0005400110102200c40c01c0e0b2290f4000d62003007146036220350049080c0d11400b070284650004c01d0014284034640755126146000c802003080748400003403004641900d10485226010440200d03c3c4642d0b50f410070355455000020010081c9042074101c00582008800b4003076400b0440c01840c2c000030180aa405841d1440d001010210fa90560b001e40c4802c51660014803401801092041c812030f0070005007041c01424000c0684000c5414003500c09041d80180c80240ea4940d00c41c0340003400306000d03205940300e060043e600d1075072611800c401c1a1600103205200480c040c4104622000b090340041901c07034a4019103080c110513140c6c80c11b14451030041c12142c410 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 8103532 1250 8102282 8102287
    0xb03030c0a0312020306010503010504020313020d05010605190302150c03040b0f0304020414040218060d0204090c0608010e160f050705100606090f060801090c270306050c0405030a03030e070902 85
    0x60840d0002a074441d418442d80c0c0b07000010641c202000140e010503140300780480c4c01400140032a1901d40c01950f40134140440e41071900949400003208000c0742c0c00c0a0326980d54030760b024040c0c3d0170200c848580d1404011710201034245503501047c440c01c0451191084082e0109140d80414424011200202211070000e5211041e0200016849c0d0060340c040b071080349859425854401c01c080c00301e100b190014180440c60262800840c2c606600400d100c2e0b00401c0b000070080140d0384e0388120b01d5540d004509030f846c42c5007044809042e0050603000008078030411070400a0040e0148110503c1007218504010f40480c01c80059825000b0f0340310050060061030041c44407120240c1c850403c03280c082c0d90b805030380e0381da50740c11403080103e500961000860a00050040c07075a160400400c000c49880c00c0101041c001b415074080b94203c6c2c0b411940403013a0f88040041c09203501560380c0014030901824505803a04002a27501c4000b41002018503440d030402c0b5581040610074240280403d180965 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 8104782 1250 8103532 8103547
    0x507030c031401051b09010e0a170105010302210a030315030b090d030b0103020414090606040f0e04050606010f0e100c06020a03091e0302060c031005030102040e1e0405030306130b0303 81
    0x20a407040c09480b141c2c03c1d86040c0005441e580d0441c00c018541c604046000d1800c10000300440700395004c0c8095a810811401c000540d0003040d907810009a0401400000c0c00c1d41548104446100181d4110307841c040c1402401101c5030012405510b115418103001404c4850004402c888180a920180c18800d240b000c00071251000302e1224407400b8035039001c000e8100f81c800150100c3c0207038021040c1c00d0f41e16014400301410311040294000c0750040145003010703611070142c03949210715040004184000414001007110410140343c1007402420181010308280d0307802000f50344a102517511176035075604040c0c003181c010308188140e507401a00c2559501d444841c05409014444401c83d14003444001020030b480702c500210b5507465159001e00f248e0b8883c06a140190741010302140c0514002080001d41540c0034030080008008104000c0028900100c500036455484481c41880130f07035160403c0009007002c01120f50142c0d08803190307500000e02e01007038001440b42c424015003501c400101c80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 8106032 1250 8104782 8104793
    0x30a060b010305091507030b01020c1c0c090e03030a0207080c0703060b1201020310050904050f0102070b010f05060304020d0b0a0f05010f05190f0603090204020d020d1d030918040507030c03 83
    0x403888102078074180526100c0c00445559422080c0c070f6940341380117810100310b800e44660400c9007148014030490381600d44440004500c1c18070402e50340c8442c2c5116a030141000700f168000f400030004414100a408071320300c0403e0b201d100040030486010360003d00f00d400c001052080d10303400707640301080f110020307143c3c03038490018541c50050030303c101c070340c0c010010400b9014002c407449007081e0918044020310b0901441400107010340200da560054915100300b00009201410307009000765810181d551418400010403d4103800032801404108108005030310341c45100b0300c600c0d038490310b9100ca56031000908402058480099131009040c00c00004110b803c41c00c020054030301c129104189014000c020340d41c50350f86845401d03046802e281d010006030340240c0c091401706002800140c5040c000194400480c0e1100b209030a84a6a81d500304156809100c2001e49a1b0000b200035460a408100000c050007024120a0045043e050001c0d082200c2802081c00a680c01400f028a00b510780c83c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 8107282 1250 8106032 8106041
    0x40f0905070504050a020702060403110109030503030403170a060803031611030708031b07030f05031b03070f090603050106021902030a060e0a0b0a050105010e060c0705060307020114060904081c060302030a06 91
    0x54038421820113001c2507800d96241b007101c0c12035034001d203554a4585550b4401c031003c0d03000302000d03050060841002004c07460600085214621a60300c16194a107900404e034444880900000f000b245822014000250000116904007120540c095020100e00b1400c5174007081f50b0103403400b10b0101148030410014a00c001c3d50240b41c10045000c1c48007418072100910707001e28580603000802004001c41e050340590011074019140000000009000c07400704d0086500c107031100000038a001402d03e40d4240d0100e200000341405160900003545030040080d176903060301501c0740300300700b00d118070a0465400704040071849500420a00c034100221040320386410f0300000035031310091404000b4030200854810203041e00c0058540360703e1485180144100c1d038025084210b0b041c4507082002c1011340c1e861015600c47c0c440c550000c10400000504081010405404680a401610284000180c00e003040d2281d102d1000489001540e045c01380718007030041584065090301560700105e080c800395420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 8108532 1250 8107282 8107289
    0xb0102010f0b1c110d03080412020714010f1101050106051b1212060d0606030c080d051204030e01090e010b1305090f04020405070e03060a0603051509030f09040f090507 74
    0x30401c03038541244034000e68405a819a510200000c20303000c143c07140011082032180503104401500702d941000c1799140074210429404a02030f5400c01007017182d0240d01140c61082c0e44041c01d0b02504d015100e0540b05944102039040c01712480015140034411041c03155030000d0700d0004d000307070750755010090256480028184a4481c0044941c1d0a180300020118162000ca018452402c500c4c03c90701c920403140030300b42d29400303081c510000c008120b06000d1980610701403181c040417146404e50311445c00041c101031105005050200681c0c000308540002e607c550076040a0039001c56882c0102d4003014150410000d861130321001090345010000030f041d0200031107010f140a41d4981081120748138085420303034211405203001400500309034000f41d40080c3c0500b03082040301d85c1c00c0e00290401100703c03522038419a5541d01041405000c10041e090140c00d0f4464603003030f08040a080741c480c442c240f008200404c001071107912035101c50740a0b0503031641d501c40c108500c0035545015500ea003207510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 8109782 1250 8108532 8108537
    0xc031c02070f0305070909020a0510120c020106030209040b070302070506010b13090204050603130602090607060905060105040b010503010306051b030112020f03010203060f040f020c0f07030302010509070509070305180f010b01 99
    0x8001150205480c51600e050760313000002070005900d003a0801010340b18101c01244c0040d6400c40000392601e541d8007408484040e511450080c190030a030117011101000c0300c2100716818a481040542c890001d02c6d0303085078001440075032a98a050302540a48900c2c02c0003440341c0300d2440005003032881e840203002c4003240c000380000d8055603600924207074021070152590001e0100041104208451441a00300b84288405820800000b000801da40c200c0e0b0010360304507841308002e070104442848224090081200d0400404c01d4040000740503001c14000104020794450105401410100c4010344204c049892103035a076031249980b050126545a04a0140440d6240c4004618041c000c0d28400c507800307410040607031030540800020300343c0101c8400e29039a00300b091010010051094801060a01d0000c02820b451860002d0840c0c40040c0250059044541e0600c0180d81d02c014454125002e4940801e058403480c909002101d419090981548550030906040f136074190003030a8825002d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 8111032 1250 8109782 8109793
    0x5060d0b04050f1005071d0a050301020c07060305090a0302150702010b090103030e01030c0801061211090a0605030907080303150103020d180b09010e0109050c0d031b050c120102190f020c031c02 85
    0x80400031707180c0c2541e010021502c0103d2014412546540c0b030041410b00606282c0c40d2640e0380e01003401caa020300d072190082d400c00320062003e00d4060103010f0300b00078140010310004215072002511550086403410f041c0300c81c000810791a500c00d4100d415140b1004004034010b50b90792078060107040500020502080c100040c1d61388040c018022181210043d480fa10094281810716030020015118000c102c040c091001440c9a00e46844090250600d41c032019500d051807000c091500380c10754080442544100208001c08422201911407004282405a141c10038004100068100e5501942e418402e030301c0c68105015904c00498004e440110003005603820a000c09403d035284c40390301600661111000420b1800c041d030078047c7c0a8024905007840083c69142035080751700200d0140c41d903900400070710665180294000d04481203040007146400701c060300140c81d8484101486040c840e108d813020b903406000b0700036500b6986005081d1825529407441c1200c0d00000c02c0b26020051088 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 8112282 1250 8111032 8111053
    0xd02120612031801080901020d0509070503070806070504030204050a020c030c06041b1d0408040509010303030207060b01090e0402090411040207060f06060e01020a0813030f0602030402030c190905060d0b04050f 92
    0x21085841aaa64400a0251020100054941d0030006d01540c00307540d4200142110320f01140315840c0600c030510041c100c03040c41c1a0401d45003a025803c83d14668000805009400e5003000c100c50480364180ca01045656410070403400134044c451801d050b0703000010740401c0301701d0041140e0703100d103116000c00042061650085071002500d03000d41c0702c1400081c6417102000012301c41e00d43d4420702c50400180303840c2d11400030612401d0281c2c02100801e0f00845c40d50f0403c5038034041c0d503207241e4003840c01521507032414211501300500640042d004051490205091010a104c028a080c002800c15941d481e05850f100004015480c4036000c80c0c1c1c6054400b0030f4240c070804212105460507802090090000d07102c228003513004650701642205c10540c000002850101508416801070384016281d2509005040c2812120200e8034410001844520b61400940031f14800b40d44019000147e1555243c000c03d0b20010045006030408901208100800500051802c903c0400f4400d0300ca10012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 8113532 1250 8112282 8112319
    0xa02040f020d060807051005090301020d110c07060305070509041d01180516150f17010603020406030b041b030f0902061303030f020604020607020f0310060f06030c020a02030a0f03050d021206 84
    0x80ca40503551f8007040c202d1003140380303900c200f000e080040c00040006241a50601c811803c80e86003101d02022241e0214044800c08410b208150040205003418004c501d490b80005206120740500e6602c00c554443c00b4001c08140d021a10000444110080200c131030300300c4502a40b84c54100d801c5641e44100200e10440d9094660000c0071140201d4095600a0070181c00390759640030130014408000704100c0011040042d881843d0083c001038400607541c0b0701304440201951400c09865010780e0820b52030b4422240c8200324201c51080c0c42c98002140110111050060044e003107010394810008507414600c0c03039507003d11904491007030711840007601c460b1348240d1326000c0c1114081e44c8150103011b403030058102a0201d07880b280d801400e07910402403d914200c119580b940018480c00c1d4211424004030750035104005401915000801003413001782d00080e52613613a400024038402800c91319004140c0202c060780d0042000728010f545035210324103040d00315101200d51703600c12078150520b41c00310308 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 8114782 1250 8113532 8113543
    0x2030907060c0c05040b060f040e040b16020607031505030a0c1706010b07150608190302010b010e0a0902090f0307090b030706031116080c0304140306090d080a050402030a02040f020d0608 82
    0x35071004402c0e0a244c9000100001445000440f44c1c10040c00c0000028406400b00280040c4c800d002014880381071070f06040c0c0580d00e0007081c1c00200c500c2300640314a00c40d0001b40082d4402c0c81880c0110798034100f03e4841d80c405001c1c3d80040e03090700c1521140020031141e594079005983d0881916041c0b0901165042e41c0e945c020301c1b50040303024081200d500402c58429804802d06601c0a001c651265164000d5251110410a046080101151a008050742801480d98400003486d12155070031850300080c00c0b83d07100380300c0d000b15a51b0014420740c4540f42ca080c601c280c40300003010f554199a071400d0110240216214042c801d00481c03c000c00c42c0307030203481041401d49081e003807035080c0f28034522941003414000600b510010300034049181010010001032000d0314207014030340d03110518001070501d401005030542c050350304040711014445a11109540d0b001c0b0091070003180f9030b2118008a800c0254a18010b9002810078418000b0000341d078008142e81281020b04000b0144d031405040d4880 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 8116032 1250 8114782 8114807
    0xf0607090306020a02070b18030d0503060f040e010e0604050a05010501051c0305030702010603021906020705040507020a230a0809100903030503010501120609090f0213140c1b0f010203090706 84
    0x40d0180d0300c1070000c41d099034040d182c0c2101c18011107040e10346407010145541c104558410f49410081d44403400390405002e80d03c943c0610b420898118207180000405004080c80302c41d0103141d43e40401c00804500b50040400100c0c0142a40d003d400c090030030940360000c140d0305403129800e01c2d00021b0300d82408468513605102c42005562688181c0d0b030100d41b00d500151041d8110b6498000100150ba111016082050069990303007010911306070004c0d003000d8040d40b005220b02e10305820054107e4001c075245a1703103a842170341c0e038207020700d0b0781c010303010443c59006426014403513840740e035081040d4a4000c01810341e0403101526006844901102c00340c00b14000100041d009000401c03d650049d8031044001c0c2d203141c5d002c500b807a1545440c0080314546035003902c03a05840c0d404d91066052440c0034500044046800740220103220540c0c0b03200c00170250044500c82d01c0020300c0700c0c9140034901e110b05015040340c19191088491010316010307402c01d44040100d80506800000c1440c002c6d026485074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 8117282 1250 8116032 8116037
    0x15040b0309030c1c0f03091401050108030901030b0405010308040510050c0d02011406100f030c020703050a0503031e130b060411030702010902090105040606080a05060d020907020d030b06070506060d0303060f0303050403050f0607 100
    0x40120080c00c8002d0504207c00725008800220f01c40721405080c01264045c112210003180c032801b4a10004040d40e11062019020380d24120042c03001c280004102e034142c41051364041103002d000c8c00110b83d00c1c82960510750032806590240281103606402003152180310160100326a1a4030041195840d40880303100c0214a580a40c150f444d07020b504004000001e600603503030b0382980c0340c462900301301072030070111050380002080001d4036600420600a2260444200b015890300e8146c80010083c0c0510181004402c10000313407203683c80d904040c502f00d80d24124151241403501002e4060047c0d104100e2040c0240000401c3c035041a01c01c0380d0454020360356840d0b05840b06560500101707006000d403900f080b07181d010500980c891142d43c500030082d642c020600301c0d01082008003100c0306003182c644980010410341780800c800082d6107820010446104500c3d411034130b0150001c001c60350001d140701c10320510001c01e0603000006001117901035000d40b45581c84a0107410340324541207403031602 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 8118532 1250 8117282 8117297
    0x306080d0806031e0a0b10080304270603080903010501090209010e01030911030a1b090207020d02090709030204180605090304050117040312051302040c08040201080615040b0309030c1c 81
    0x34a107101e48849500300d40082c050760141034242c0c540f900e1a80803401202d015a1103004c104d42044640302d66107500000c0b2031080c80e0b00c02c0c01c100c101c0d40c4a20407440381d0209a40005040368405000c2100e142d0362080540041241554a1405800c01c0e040906214846e520300000050003603441d00859011100503034070000081100c01c015001081409415501c0d4507030150f940c03503251010000c0c0300c4080e0044c40203050032484c00c03407103141d101d8843d000405002d00601c602401a00c42040d08166240c1c12140e0202d03582d11000211600305052388041c2d4842c3c1000d290000900c100214030603d40d01540e0140515524506a0b80c1d49100702d20502c4c1c0040e5400160943c030740b400c1d155458120b4402d1406c12000b02002a1220903030724107a94082990018414480452901e0300c151000e01c5190300300145140381940018000c8080105581e010b580c00d8520344d080c1200e414211800f40007104421900c03418020325055aa8009000190075481034056110b155105110b0300c10740c54000340e84005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 8119782 1250 8118532 8118553
    0xb0315041104020c100507090e0702030a020d050906130308030109060506130501030902010c140706080a05070f031d070b03070e09090a020f120a03020c03100c0e0402090f0904060603020405010501030608 89
    0x951201c0c4d6454114050700070804035404240c085c060280d02070741d441f1030284e0304220b4454100c880c003034000e2087d076004000c3c2c01c060540200381036542100c00c1c2401511004084003040317441c0305c1d40c880d45003481c0b01080040300f08281c2c980618183e40c582d9004102e0f440e120070920003940700d1450b9014105400c00405c110942c400e8129505883c410f1400d04501c540e03daa80001110300101c140780786030081c03041406001d5010440707a6001c4013070a018003440c01d120001400040001c0a12401c054450107251341051401806240c140e00e680100c810f81a950140c0b021240c1068941100140c0d081000e13400c145441c240a501690180000c2c20b140c4074580c0c200314402c41d0022003030341c228030804050502040c0501040550a010703070040c04d000301c040d070205410829400da203049424034002107a40126400300207500310f00d40030b640040c5d035040e4980c00503212401e84040c2d01e0340001c41200300320401c0b14981090b001c507842518140a141d88420064064800500038513130564007140001d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 8121032 1250 8119782 8119789
    0x506040512011d0604060f0207030c02010f090503070902030604060602030903060c09010309060f0212060108012105070317180306040f02010e0d0c06021501090606020d050315090106030b03150411 86
    0x201103212980000401919981c1502428440c21140b040303d07401080c104024003126001d0fa10320420b802d0403c40c68002c05036400307480305850460181c10007044507200c0348400e006828010240c075009046805095458038640040d50040358454001c0e800c1801c009007181c0000240e943e40d58004019003441e648901940303c4a03042081110304061310f0301c9054020a10300d2146403c101e01c0e5401c003507902c80003800740c0d104091020f0910b50402120308010071820441c044c1101000c24643e518644408150826074a0039100d40c2001e402a06c00031034510714050003100030110900c074104c1e11078044001004064942004079005403481e21551101c03801513103d00c90003115100d0042523003080684030303226400903c0e1503170007a070003581c801c4402155125070104850700401079800c05000507810100020740b1041c04404c1c04080c84030200c003003046019803000c82c04d401c0c1000703401a4030641e500c000050241c00c038050058042e00940b001c0c140c4a040100350036118507040f43d0361110402800781031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 8122282 1250 8121032 8121049
    0x28020a0e0609010f110c04020f0304050105070c050c010f0302070803070206040507060c0b060105030a020c0105091605060906040501030e0703050d050901080a0b1e0301060902070614060604030525052808030405060405 95
    0x4840c0303140030b80d04800c001b9980b0352000c0c000c1610040c030b22944919251915908449001d44440c06000401c0d191600003400000c80900c0c5200c00c2ca0004078030540700006078040d0144802c02014000d0110030005440d50004071035204030300130b000b2211800e64a10b001e03152000303c0d98000d00190745c1d000001355694066401503411042c0319100514260394620384500b11003040e40c14022a800c030038000c45921104400c820b018107001c0720100c0c82d000c01701c8001b0f402c62044c1c2c4285410b15880700b40d4001c0c522014050040110b8202003a907001d8210020000d055500000b0854041038213000814044e00280c450148843c038094480500c0d01038200062441901900e40c4941c190340703c20000c6980500750015101c018030449001c0786143d10302000200340c4000030201c0d8000c84050101b04040b550005409943e010109100035a4443c4281c49035107075002c13504402e0300304040ca2000d011982038603042220000c060640700b0070040d07c07800d80c01d880303200d28420aa84014284000c4c001031401000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 8123532 1250 8122282 8122307
    0x9060f0203070b041e0302010b010f03020903030904050703090807030305040302120301031e140304082a090a020306031c020c0a09060501090302120304050a030c08010506090c1228020a0e0609010f 86
    0xc0c04d02e4090071400d0454186540c4400c120012307511656002d41c103582095030190380c1b1406003010350238070b10b40d440401d41d640500200325100d07075182c80100748418003942c84003035110340254034140e584045040c094060502501d0032070040c4503030402c14811440342c0040e82d0583e58801d003845c0722410410401d1540001c403d40a1780c4000e01c1043e0300c922600d0403c01400189050b1000e44440a50203d00d00c1d140420031003d0910300044c0b400c2c0341c0c240d9480080440d888042c040c00181c580c2c80c1c810110f8a0320b0784001e080301400d001081c03040d00310390300081d44105480b021940b0b000c41c5521494444180c81c0248501e0380410055107050006152020540320214003810440342819540c84c00503803005200d900030f40d00c00704c070001d0034418480d080c081c49a004400740c40441560a2407211344a480c850424a542d041503c000030941c290416084045282c040350002000f0b140091084802544006102d2001c110b85c0d07560410b190070040140d0b003d01e01c058507000c1d01071400702d0040c1c404080040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 8124782 1250 8123532 8123543
    0x30c1203030b03030d0b030c0301060803041701060306060605070204050604090503030a020f0d060308030103030f030204080304050d0201030207060c030e010c020703020303090108060d080a08040308071805040c0504050d1209060f0203070b04 105
    0x80c0840307060f2010405401c0a120b03141020650780fa600040c5828810128070050107641403420038044940008120303011501119841c000c091030b001c05560042c031186d04010040c1c0d050040005800350b110001d410f8241c000c4508100e00d8542c031082000b1921004d0008010380c0042c00001e40840d8030380d014201c400d081000852804a080d2036078030407514240c204480c45030000c4010301c141980102c10082000040c1403c514060509102030742d40e000310701c2401e00c81c4104440c180d08591194043e64101903221809005030303403e210b0068090304104080031250762812a204642520001c0c551080740c5d0040d0103180760090395001142c5007003006149a80040d0302d0034080e00003803c444001c1c040c1c3c00c0c590340d80c00304c141010316005144250180c150300411180107032940c4610701a80315681210021100003800b0703c040f107421b4a06000d10390140d58082a515852414820204120b402c5902d4996680c004191103401c00d440c9000c00800d61030040e0300901c03102c40001d40c101d941980050189 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 8126032 1250 8124782 8124791
    0x1030308070e0a0902070b09030313080f07060f0b010e030d0e0f041803020105060102060105010306150f120903020a0b01050411070b040602040504020c0d02070605031608060d120804030f0504030c120303 89
    0xb400850608080d5501c01158194001088001d00401e19111908100e44a020b186107040148a514108c9051600640054000a01000c6143d40ca00407150129030156003130014401c0307044060010b10011441a020401c01072030a0428940030400048400310b80e103801c00e00c443d0b004148021500c020318417541095503000505086010440030321009403013940080b13224070304080020f05100069001d00e05050901405010345803030081c009020703491030301d81030007207840b400d0046408071078100c6d02c414503034a460344c00001d040d404240115143e0240f049144540d9992051108454440100e10070900d014414100080d00380a1101d030000d004440241c14592210300140483e4801c0d010640b00c0e900803040a010103405010000041000d03040032404c500d08042e024003810108150305082184c4103002580c0e0750355001d1030024031608000768641d00514994040c2040302c040c0d5003500824a082d10380b00c0c01030f00c83c00c2214141da80c80042d1030b00c03461600c1d0200559401c0c400b4101c1c149a100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 8127282 1250 8126032 8126057
    0x31c0506030109020904050307030905090613020307020106031b030b090c03120c0102040503150115020c0112021b030f0c0615010207030b06030a020904060203220f0311030c030403050102040509060102030a080103030807 96
    0x105c240c07460241e80550055582d42c4034a10b800382c116652036001c0b5010f00e8034542084039541d135562a84903045907003400941d99a441c180b00f28014026030304001e010300b02420340c41ca00c01c1e112040010540b44a41c03191801510380c5161169600e40c20141c048c0d141d40603e400004c078110200140070b8680308030340050706150315100043e0070300da0080851820426604010011026103904140c0c002e112070005e445420107480c0000c1c94003071600446c4a07400d40004083d0081200149151074a821110540340c440c020034988203416444484009200e00c146004503900e0801e07041200308400050f0001d046582c5036544144801c10001d00c4664540a407030224400350b107441caa840e104038414400140c1e20b150044034404214880204251072101003065000011403900e4032a1080381c050902c09e01020203c42c03030502e981300d038180f0b0541c5404081800000c0007015000781050700c40403a84070400e43c1e24500120780ea07000d011412000035460400410200e40035081c00ea4000c0c1c0c981c644600721010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 8128532 1250 8127282 8127289
    0x5031b120f01051e0906041106131e05030d020d080c090603150301050709030809090c0403021206040308060909100c090b040b0403060c0c02060a030506060d0c02010507020c03031c050603010902 85
    0x503080c14030700d0346035111410400c14044a0300c00d0444000c2d070944035009800c0162050781c0d9444020401401e82030170481c403c03455907070341094614000c042d654840c4c0041d210213120b403c54450b50084a01c24403031503400701d014035000c01c100d4020b0b00280d0080000124541041315151030140c06c85040400c2000841c40c00e0f1164002180304900000560081182c0c84081c1801c49200038501ea080280314801800010320030412034100d00002c0b01c421501b034031920b41c0100b0354400c50b80025801458040c9110140c00f000c290b0074411030081c0c0b1019810358403c0e040c448070388011555400b4980200d44068804901036100e103400035040e25012400d29264920f90305a60301942044000304008030f070800400c8028090103004c0041c9103491014021360f80e000c9005070081c20340c2001815291000206980c60750015070700100380359a814001c00fa420100a03000380000c1d0307451070050003512036070025030070004100c98916200030a064008040b900c02072005280280c503195265403121880300169a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 8129782 1250 8128532 8128543
    0x30f11010909090b09120c0c0607021f1d01030605010c0b0901060e0a0608190302070308030901090f0606030302100c0504061d060409061503150506030a0b030604050f010c080105031b12 81
    0x14464030104d40141860031029213446540915051400e04c100030007030004070702045c41110f40006a441d29160b451030310008240740d000381ea00029a80201a01c105c695a000c00403089181c84110350601e503010400044040e2049801014049101d200d403100016848a04140d13102c1042030000920b50345400e92145407a606541c82e402540d20740a0034003000000340702030090b81d4480c580983d8001c40340d03a0069203525440c40088c20100c008000114801000c3d040310b074186610114031802402c080c035105000300300c1030005400502c41c1285501e40300e0300c0761080810301005a00d9a0b4102032401c00300720f07018100800404030581e00005051126129400134101424400300003144036820107501d07203c1000e07005404d204250401d840381c1111501c611190003601c3c0e0030b541c013607079960f6402a8040903003801d514a507014440c2104000a11901255000403072241200a21940300c00c100c040390140400c2c01796542c5a0004205804440d80c0302440442e400340151a0139040071707a140103282440f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 8131032 1250 8129782 8129801
    0x90114090f0706020c03060a02030903040801060906060306050103020a080c0c150a06030203010e03131e05061209060c04050307181d010b0a060c12032004120c08010204030f11010909 80
    0x1076001c1541207401c0c800900070706014002a100420080c020900000c2d55080c001d44004000e40d80040802d8085400b4011900500500350007444420b0380d5200360b000400e070f0707881154006490410040780540c0320b4001c80b0b24601c010f036a0080c4503200c3c3c80b50022182d0101b42141901d00c9806106864003070703405081e5114020140001605038034500516094920285500e4132a81040201c0c07c80e000070314200c00251035207401d08000d4201c401d821601e01c0c02503030f00081e034403400200b5140c000c4048183d10b28481d800c003600340c036229110840801c4150003940034036070781500405c0b014010b2896200b0404140b0304400c82c0810000540b0784c3c0b1011810030301942c0c02880e51680c200041e14101040c4c1038005121500e4407141d102c80f00d46608900c50074172070050007050f071240d05024618007289005004d02c0f014100f01d5590b5036640307141c1ca038180c080301800c80302c005d10510002120301041c4250340880340c0003080f010089806030f480010101c02811800e040c003074404000700c7d2040c0d0038401d48412 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 8132282 1250 8131032 8131051
    0x61302091302031e0115260108030d060605030601020c04020904020d0e0a170f040608041103010507050a020606030a030203070f0602040306020403150b0f0307060509130f02041a090303040608090114 87
    0xa80c2490b440038804907120204e44003c5640c0d40b80104182c100510311802c0d0740c542803a0003900d203500c034030701c150384107000500141c0648140300c00070903042c501000030025222800001c04c0b010745e45600076a034a0204441280c0940c02180c00b1420304e0070aa0001c3c4000840200010300c1d0000b9080f2580c100c4005c00300d0440294019540b0a0811040034807586404a000e8a802d04101c1c499007084060702c507a00076a000c024816000c1401c008a140818039901d600a009021514007000300505030f40040c00c07040018480c400201d035443c2004a00e07a045142c141c0e0165242000347e8403140d007030703040d0040101c0b1426400c120010200da8148090300203544203618000c2203d90f060781c9041a920b002070f1030f82c85002d50884030b00ca15900090020122061420400c1c2ca60049400080c141c0b00303900380359252141004290701c00141030384c8c001c0c41a502c804010140700a9490381568684c01030004868141d84100400d10626014100d226031242c0700d0800841c0041d01c004140e404a80203a991210 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 8133532 1250 8132282 8132287
    0x90a120201080f060a0909050a02040c030c0e060f030411060c0a0503040501031a03060402010e130e06060a0f032a080f060402010905030c0607060c0306030b0906040614010e061302091302 82
    0x11903901940c0d01d42c0181d0756800c81503003130400c540012424000352264a54186d070f00c01902d01003000511144258940040c0108030f51034002c04050094032078100c0f0000021100c02e80c802c814a005010745510482c10f140d1141180e85547c2c607206640e00c4a601c0c154000000e1003451240b500030800383e801c41e80b0610142d615103207841e0000d81503c0384010740c014910764200b0990000d440015010327501640900c1e100300c1a000410105200002c4959102201403d121242000c02d04c00200340780200c0b0305071100480d403941c400041880441a010091a03480001e110809034446090301012842da0a5030100646688031825031414046254600c80e540181d001c00055681213105440248815005800e0211500c4006801841403000c0209155a90b400b001001c0e4800e90001e005181d2010b4200341320705062030044d540c1d40003203a00b11407003420230294605401d4a005181d0403104401c0e40900e10307403141300802c040c0d114008070300600d855013407001c911181c0d10390001d00e0305041906401603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 8134782 1250 8133532 8133569
    0xc010b1207090b0a0303020c040f020906070804080c01020f060a0b01020c060d0c020717250e04030c060c0c020d08030612070902070302070806040503040e1009060b0a030c210903020102090a 83
    0x24160b81d5038203c550f1184107410010400f080d0045243c0020500c1224006203401500c02184024000d620440703400120110b030000c100854880103000b925002e07030071200c003044c000c07004a941d084030410380800c0390402004603e035501a90801d00038450140151001090300d00b022030200d8000868808026072588014146290180900000317800e59100d8a00c8843c082aa2241d81d41c0d8015020095a032517500301000380f414004410300903244201d0320922604080c14000e0441409200039540c0c1403801c0d00141c4964090b0100c0321160b90301400d1040c0c1456140c460211a80004103d40c0c2c102c20303000300141e0007401c180710717040240a45c81001612030b5030310304000b4901031883c5c0099607a03034003400602c00411400400d48007140d88108504803995104201c1c0100d6050943c0b0003003142d410304001042c050094409848480039541e4100000c0c21011011515008040601c00e0401409102c002c0605000c1c0c02010825029000252070f0450036004a05051041d034404440d5004205004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 8136032 1250 8134782 8134799
    0x30705030103230d050a0e0409060b03060a02040807172407020c030609060f0c0408030301080106060e03010b0f0910030f0b09010501060906050313060603050a0b0406050901020403170c010b1207 85
    0x200f040c80710308030400d40c81e5000d504803141d41c0c5000804100c280803004c20101c40541c400c560000041101500900211000303181c581e01410a0720b561510900900340040da0100c50f0344240c4044642000c01080350030b1401c124446001c031038501e01c0d49240903820b062281c0b2603c00c41c021086200c5c0034071300b8043c1c2c60b006200074100120b58041c180710390014002d201c510b68002402c0c03600306840c090840e00e9500d031003d10102034070580d440184070380404000003450610651100048520b1a03c6080c0032003171180406080710f140400d0180d01c00303203159100d9424201280350b264170120107240c0752680750300d80e11510300c010b03a2444112140c00d0440c0410111010a01429004001900b09030189030305224000d0403a000c0140f000710b01040c19201d00f418070841e508400d008640080581c0c2d00c0390b200c4d0a01c042e81610440b019294103040002091b0303200414401c880444e60408980300c2176100c540583d00c010b03403181060f580c0d5503480700842d121320b5550401448840780c940c0001c0c44010f00e40b01c0c41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 8137282 1250 8136032 8136053
    0x504090e0f0601080d080402040b031504030302180d080304030807050c0f070302040b010c2d150902010e06041a0304060f0c050a02010c0212030403050a0201110c010b120109030e060304030212030705030103 90
    0x42c8001d1700401072040d400c0c0e41220116810640c111000f058586200002c24589442d0012200e150340c600000c5c003040c15010303070051600d09041d00b01110140b140c401800f030302c245120380050598074104009400709114203600c64120020b480c000d4a041c1c8036170700e0303103140c2b00fa90050411950842c400410440c0b03818410702411100a0030544401d01e200c0d280c80051081d080351206402c080c42d040425544030040311030350500d80c04864454540042c2007450000c00620b070080b4003060071051000c189280045c20b403000c0b03d241010700d0381680c2541d2604a07644d000038000300c0300a034580043c1040460316020b681d4140c00e040d034481d80c5400a600d40203080d9440e1000403030035904090303101c240e041d140b041141c0d406501410f09683c1c0d078020074400c03401884004620b40130b201e404074240324091410740045240d0141162001d03030209500102500b00ca08212004000ca51a0041e00c00d0604002e405142d0150080c01526200684004610f0315544210b41c16400148000018410031000f40b84 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 8138532 1250 8137282 8137289
    0x519050406050d02060406050c0f0d0804141612020604050402180a09020c0a2009010b0d060b040b030411030f0a0f1203140a0b120715020613150203070504090e0f0601 73
    0x400c00d0f010304854011600521440c09035404000c400100082540340170050083c0900c100001c443e045000031800510041061303c040391440c001c010580070018001514402c05502c05415502051808001200c1c0c2c0c111502c0c1240c110900b0310000070380f65580c1c40074002003c1c50081700b00310894000100701030503c00f9000382031070034410720655225040001c2c1e8220090b90280040290762480301c00c501103c1610354800d5440b4220000200e90490b01c400500715080c51014123010b260307200c4407040d40c0c6026500500e85104400d1000501040e0305d041000014200034050743c0301071030100c3c280340c00c11306080f01c03e54000b0641104401000390a02070050942c40500d801c0040d0401c581350028281405007403a0401500c40c425419140d80e442c50300d041032281001220140342c1e580210f41c009100b00c060078000740c011140060100b0042e4800c403258580d01c0f0107101400303c4c0050701ca00083d04050100380410006200216a280191003090340d5002071000a00440168103a00d43c0341400582 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 8139782 1250 8138532 8138539
    0x1170114100c030c11010c0b0a0f0b0a03050604021005040308030a050601020d090b030f090f010f05041a070504031502040e07020a05011113090509011b09080607020304060c030503070306051905040605 88
    0x10b4501012950042c644207516038000400300d0051010310040f0348030000100040c00c09000e981c1488154100c95201034200404688140086c0501da010004900c519100c0074003550041000035005181011148030b205801d424107908160301c0e500c1c0e80600b500200e9050241c25620002c2c0101c96030104640e070030b42d040625101103201d04040c0d035240c00c0c0c000540380088524a007004194a01030a10006640000a0000300710004001d0a083d000e01020b64094602000181e503d506072a42c2c0910944a81c1a9403601ca140514640d505010001302c1c04560009a078280000318164040d184880c4c09210f0550041035a074a25061860850740d1140100c6080c203c10400c8101002c038010007a011501e0b4000d00140a641c0e038400c40380503241da4202d00c1c0c1c19540c0c080c0c520300301c01e0f00000000c042d03030003140446500350b40e8150141da50740728600a10b00841c0c198406540002e200da8019680007a50f03107004103456580c1c07000300760a8103401412420601c003001c0144000d00b400c1c460a002020101d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 8141032 1250 8139782 8139797
    0x80609010612050901110a05180306011d041a0c0306030105150a060309080403022701090501080606040504020d0b0f0712110702060705030403080c010504110402070507140117011410 80
    0x78030141003400c0030202d066080e078490300010070441081d44541c0c0000c0b20050541d50b2032130000300040c031a60000701205840a44c00c203904440d07081c0041c506041c0d805200205240300c0743e20181c1d1a000c10b008004607042140400c00140184c07500c01c0d150b010f181000a95501e0341030801c10542034038001807441403000700c882d0031622240d030764449040488140342000500b95200341041807883c071542d00044e400401304105003818600d0201c002d014030390a610a01410f0b42c03106c0044c0f007554000e01c80d8144952015020503200e14003588140d0700b02d4801080c0d1a03c501d115034a01540440031500b004003075001d0020003181d160416070080c083c1e141c4440400080c0c40000d0709420900405038042c3c000c6a001c50604c003000010411034025640003800c0603282c522080340c00d030107040112400c5440040c52079045030641410b00a540903981c0c0070024180340d600301310505144041122070f031410018843d0055166a600c07411490181c5581d01a1500a0030a0407e1144c0c80c4a400b95140402c01c45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 8142282 1250 8141032 8141039
    0x4020901080c0904200307030c020d0e0613030605071709010603020901090e0102040b0706060311040209180402010e12010219020601050d08030c070c061e031107020607080705030301060c0308060901 87
    0xc1001c0980c0059007040058403410002c000c40d000b012000385180802410000c0a110035110070b001c0d5100f43c08035502800400903c0e0310481e150a111072180004c1140202010f01915080010f00140200803504d400c1040e07590702c50300240d03002034a00c8004102d0380410091602e0580d40d0243e44008008000c0c80f009103141c0c0828030902c0305200320440c00da941c656142e400e000a4040318010950410510340310301190074590000e10340c0748022501041e15407911112070525000b5619030b1180101800e0005036214141031003c1c8004000728100062007481c441560f03030308071800b00e520010b1000140c0343e04000500003c610721254001c000d5500040c0100156030f14103142c0c22407154130001403500ca03101c0611100260040040c01803000401c460046045039102102c0c036500c3d108503d203000c181c000f01c0f0041d0b089414040300102d0406040009070302604180006041841c4200d407617500d020f05a440d1141960070a8011600150080d10b85209141d80040f506030449411200d10314917514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 8143532 1250 8142282 8142287
    0x110f0307050706201213050d26060109030210020111030c0408070504020306101b0507030312150605190207030602040305010209090108010216060908090a0906060f050403080a21020412020f04020901 87
    0x1807044040e0801744c0b0301d00052248503d11841d101990ba0200888410140068010f08480f405880c00c0b004030003104501024451240c40050044406071100c081d66801e40e001d12448a5200c01d81c1c00a6648615044071407604c0d4400071403241169400464855051481c001d040003070075408a1710603801441400a035135a04500525044d6090404191a400540e07084003101c60790174014000d8042c9080010074190485505a40001c01c840200040054900030841c0481e05d40180c500041c02441103186000354142e5802000003140111380e64507550340d0345c1d20117907442078000300d0b501d0750045082080d41c102840703041d02511514009500b031610305c0d2910601e0b00300d4120b01a0409840e403066106011540007100c0b00810064460441180c840d1140702c050b0046118070710010340ca1440801c2064030030410384050300da200700414540f1030080c0f41121a068151205a80c40303551003038042c0e01012a100070401407805000d9000c0c07444203401000003428924084c140154010072401425030ba = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 8144782 1250 8143532 8143537
    0x50102030c06070804051903080a0501061107050103020d110f04050301060f03030e0907120c02010c0206011a030c0d0e070602070509010501051801030507180303030902090703060305060a110f030705070620 90
    0x520514002c007240c0d41e642001464040303901c80c5400192003842031f031801e0550020000c1c0c030914103030901344042d99844030300300e50b10f0400e01c4600c811074000c0b000a108a6129400405041e000756501081100e0120300c0e08070694041c9a011003207600000d4104040c1c1805c1c01444010080312000e11803051960300c01902500c0c0e86500750784554110300006035058081d025051950804020800c400310490001034000c1c0b02d80760300c640152080742d00014000b90010307202c1d010403d41020b8107041d9103807020304c00d10580280503000c3c0300540751006d0000c03e000c2004030100505565005102451501c0f0601105a006802150401c0020000076403440e04841c8202c109410030301e0000345582c2c519400311030302c1c41016034072501400d0f0b4990000a02da80340d040001000d008540b8159162103411003501100c0c1c1503c4000c1136030b0400d00000304c3c000500d90100d0481085084a03900e03010310205001d6441e070044968038007041d0081454000d1208601c2940c11813501442d1032810950003084d16846030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 8146032 1250 8144782 8144791
    0xc090c1e121109041406030a0308130f05030703080108010b010504170106030b1f080307030906140906070c080f0708060112020a05030a140d02060f0112030309050d02070906050102030c06 82
    0xd0032495103080000384108030314000741d03428000c2001103621048400c011544035480003485241003440c0701c00c00b40803c0204600030500280105a1003146550a031074420b80102720790a0804900c4c61800400c1802c100108514441c0000e11742e1040e60f03140180c04420706801111440e03140180d20509640c22100b00d409030380e5502454900e1030400521540076014503040282100d1641090100e024220320a001030740d64000324081609803550006035030703401070741d0014000451000e003c000c1c807030040404541c03141d80016031a181c406002e012031031607444884101c0d014910403000b04068102442035941d55880c2d039020b818611701e464180b41d51381078180540326009020400d0002103684120704100140b00c00341c00e070362064000e4101002d010184520190031402006c1c00121050704c0440c2c064494594003000402c50b0b403c00c44601400c1d00450021014180d0382e49003c0c02290081080c0303c191000b030b41c02000b001e424801d00c90180c1d001030b07019505550040c02100c64404004c01d015900 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 8147282 1250 8146032 8146067
    0x30509030702040f240f0605070b040b06030304230109060c03140c0705040f0f14040b010308090103020903060a150902070512030402030705060c0a020f09221407120c090c 75
    0x84104d0400c9402c010414841005001066603500d0305518840a504a0890b5642165100302070f0342c0e801c0985031442000070007000701c007086001500040c007000c1d07055040303c03000d011242415110002c81d040c0e80d502103040c41c420000c52400140c1076900c8020440602050b03c3d01e01020317090f80d030700503019081800b007004040c140410070800da1a8200f00c018000c0078010424022040304071901d0008004041c8440c0d1500d04110000f00e030912a98903807401558812404201a1b207540c8442c0308581059041d181010b800f0010344d126941d0401c000c82c001c4c450f81000140c1040c09a1404c0f03126102540710749940c0740140101008581e002c1160180310a42104265a076512480004c0c2004500d03002154410408034100b00196000501404190b101303035075002d08000c8a50410503034100c03c4900e82c036100310b6281030014190203d01d5480c50244a5407162107407280280700700b810100150400d0000f26000c00030b004c00d110340b0000c07210083c2440702e820003283c1d100c62001000320300c184488464 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 8148532 1250 8147282 8147291
    0x15060307030507030b03030a1707030e030a030f0b06071104050109051618050307061107060203070f060209040e030a020a0b10150c03050705030a030203160801060207050d11030d0507030f03050903070204 89
    0x4144c003940014650307810040540e075a501072558007510807002008000031301f003203140000300d02034001d00c106440c4980c102c0040d4102a04c00008401030b011400d164480151603a28205441d1902030191142500c0b508070008129190342c207120031207805130704c04e03d4803505001c00e21901020307405400441c4a00742c64502c2822031100d004044181c030980c01a03801d03202c0c106000464a40c40800c0000100922090f00c90040d40e0300812030783c0780924000034000b071800845007400103016034001c190780e0a0180001c141000300b170400740c4c01d5802200b181340140c1c00080d251010060f40c001d100c0d5000e02ca20310000d1003142031000040408007a0300500c0c082c0014105003d0030301d4011410b80c0c4060b540402100e90700c1104e084010042d400c19240800d20030324145480428502950865050391200d60052071072901d800208059003000074800d8500d941465542891620148010000821240c4826564554500d401003400c9101d601c020100b520700381c1800704101001c070403a00d005804460105 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 8149782 1250 8148532 8148541
    0x105091506040302090405010902120c030304060305070309050d0f02010b01260601020a060905010b0a0602031c020d02090306010f1a0a020c010f050904140f0106030608070b0703020307050d030f05150603070305 92
    0x7100340c41160006035001801d00100820014150003c28035540300380d071016000c45001d01142d41d50400481502c0c1c0c0364106100c05d01065210b580307c41d911240c00e01d404038490080d0f0310b585061520300101c8c4000620942c1c01185826024001d13100718034020f2030055030880103607441c03240c3c0e003810250001400002d400800c102da84208410503095030002c104001d1000c103031400d2402800030303613107041c052b0003d000002141400401a1076901592410011141542c2c4a40070020740c000c12a4621540d800e00c80aa19038908120b00c0d03001c0c2211408000207641080c08c24480001c8803148524030041c00c109401c1c40c00d0340403aa07051005002c3c00d00d4815600019016038141c041d0411060b0480c2c074202000f00d42c4400458014019556130300368100d0b5907200e00e8124140c401e180500100c2c0c1c1d0140d28108800398100300241032181c003d1051f40d0900f06243e64882c200390740c00001c2000261101c4e48cd5103100c41911800d90841c14a43d180e0380c904a00c3d102242c0540002000320050554031700004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 8151032 1250 8149782 8149789
    0x30807020d02030a1703090c0409050c09060a0f08010509010509030a0c030302090406090f0b120607020703030e0307080601060c060609050103020d030e120709020d060e060105070206030a060e01060507030305090601050915 97
    0x2482a680440c03e40701480c4c040c1700b4a40c85402c02c5031144c80074440c034180880c2c0c07804c00303104282c00541c000003d01001034217501030144030007007d0303d110742242c8035042c006040f0300592041009041d91000105860a041d00081e09403003010708110b403150420040000351325041034100145984c1400c1c05a2548001c0001500510032030388640c90707140c1007404440c15040140d05c5185140812902d001c000003070301d50066502c00c0100c0d0404050307448030200b440400e0050f00c007254500c0d030040848400030389a01006041c402d00307074800800f1610014402040001d50300800000e40354003241007105625680000380324801581016007800902200d020054444504d51480c0100800866200725a10010340307009611031100d240b85245461000304614924101450003404140c0d0ad40e030038500940c080141580c4041e040d40203055813030100207007042c1c200300964000e02c100e03221503455080c641006030a581004200304260b40106005200391340e14000c07074a401140c41721071a54034200030f5012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 8152282 1250 8151032 8151043
    0x3031b0a080712020607032c1e01050f0c030405030a0807030b0907090512060907090e070e01030812010b0307080c090310020d020304020411040e060405060f0607030201060303030501050a030807020d0203 89
    0x98000000042c219062180c0024803032400d5a03580e08403585a91200c9080301103c600003603c9024602008a0366161507880000a412200680640c0c1c080501d018100d1811070251094007090b944503401c00034000e03610702250390311100c0030208030b1640c41c240d5216a140e1040c80d8616041c4540d1b0700205070300358400d5110a04402c0080e040d5003850404440142621103a407141510075041504a01180c00d000300340e0034011303904003005082450800b00b0350000740000f58112405c51040311800504401840e15090095024003035855441e104280b070008440700503000300328a0380d0304200740002e80e45d2105100361f01000b400011034407010f14000103410b00c24200c0c2c96681c8503002240e49041d40b0f01c80d500039030213240b00326400c1018907912134508030f15000d588a00080070300503500044003800c01c3d17040254441d00013001e10f8000c43e2500001402d6030001682900142e5507641d0510815415114150151008071200c2030b1039171442ea149a280d203c0c01400a007d018612001011910b08010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 8153532 1250 8152282 8152303
    0x240608070c02090f0603010b010f080109050c0702150a0f0c030806010c14070807080706030501030302100e0102090406032001020613060213050306090a03020105060405060f0f150307050901090f0503031b 89
    0x180c2411424401842c540309802170310500e11a5181c07510905c281c1d80100a900903419094456040e07583c6801000d400a140042500d01e0340c110800403900141c0e034142c1000102c162100040d078688180b070341d00a15100b1000307454010701115600500c0400e030003002c010341c048401d01c6c0c00c20003410546050002d10442c1a54003400e4403c420b00071803490000b0901c0016145c040084401c419500d00707044003030790421b10000d00540c01103a44010240050b4000032908148240050301e4207000d4400306d4103c0d02c66510076101450510b0b40200300a00102c0c43d40c4e40c107002440101b0f001d0a000e10903136610513140a00404a5a001990b1036501c41002d500400801e030050664806240005d103190711220f040c50200c0040d480c10000569619007807048078090f920244c0000c0808590101b0700200c2452682d03c0b07a8440d103c00303c02051418100b0046118603000c0c2e0f1010303201c40d6048005803040c1940e40241c03d15100303107003051006840000030b5a250983c80101c0a500020400300707503060208069 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 8154782 1250 8153532 8153539
    0x20c060409061a030403090608040c080601060e09130213020c0a02040c0906020708030a020c0402091210021b01050906060607020a080601030f1203020310030803060301060b031801240608070c02 85
    0x100000e000c0442d03030140e42200c4076018100300042102010340e00901c01101c0007408140d01807010700040741310b8910280d0091140b00004407241e12800e28510304942648014001003946c0c80b40000c50a02019441d0020344802c284000825250300207100004400c1d28008281c0d4049290a0030110820040b41e4043d001b42040100c081092001400d04031a40035090140c440c0d03801c001011030001040704c59518043e8080c11382115810704120203948007503811603010020110140c440c0c0348c1800100350300c1948040069450860303000c0500c400d001c040b02e031500d07a45410100280c0c00404524198070940c201e562540ea07030f038188005504020079801000c3da501c41c00d4008802c020320011841d000901905d0b0114296540c0d8404400360b00c011244201c3c070609029081001494103406560002d40c01400801c2e42a155805180b860300201d501d00703038076500300799503120380d010a100b00b08000480e03681031015030203080b0a90180c05154031524080150200015140d1171181d441c04400b00e034001e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 8156032 1250 8154782 8154787
    0x3091802071403040302090709030f0206130b03070c0311010b01050f070206120403080f0f040503070b0702010f0f0b0a05090105060403080309071205060f15030a031101020706090302030307080112080403060c020c06 94
    0x202402c3e03503a03000750104134010038070310300894400c1d40130340443c038101e951184107041814850350900610b900100c00d0900e0300c21754480081410103584010394810406603890301118012414010a40d08560f003110350b0030792601c61a4001030f680001100d4500320f0820451b03541d4640ba00c0071a00702d1081400501c2e1100c004802e2004155000202c00d0260b000b00c07400e61515210729021544895007602c4c001d000e0340c41041081e0001c0d64884d00d03640d0011443c0000550745842101c0c002c180c07281745000342026030740c1e2070041d8507514043d00001d01600003034960f80240d6061102244040c851400702405140780800054440c00040100801510395404074660301d034420301d0040e5440c40251000d548403c02c010020708802002041c00418540041c005c1625010648082d5006550070306a0b40e4695000c002550204c3c00034050081e07040c0c800c0e03000710740e00d00d032100c0e00900c60001a00300f8075258295280b40c1e0080307421442942c041c1c0f40c00800000306142189002c0e8500240c03406202d030080b402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 8157282 1250 8156032 8156063
    0x8010501030b070809010507050306120a02040c0507030201050108010203060a030f0f050d0504150e0303090d0c0f0806100801110703050a03020d050c041401020c0603130201140309011505010203070309180207 91
    0x42e52116030088180b515560302da5240d984449080e07802c02c0300c034500007a0007400003a87c40e240410075100510100c07010b480c0460159000326054810101d8610040751001600e00c003050b909108242c0104080c400071400c5081980001e144144248806880507110903008410320011941014050782d111045581001e880300c0054800d0f0028030400150080000312400880e000305001c84010384010003031490511500308100030041002000e813000b10b00b41502003142c80020180c0000341c06044010000340c070f8040515050021103030408030302079043c224424814580b50782658202076050900d00d0302e9446030300088000b4050100c400103034504080c00c0c840001414801071080d83c5000d00c010088102c9403005981e169a007541e0990407010400000d03002141c941c5040350307420300c14903156120309641c1080c2c003416001628100c50360396551540c5d001400c510490340300101402e0001c0e6081001c9528017800c00c8001d4450700c12040d00600e00c44095481070b44c100c4e4480e83c1e004071003040d007404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 8158532 1250 8157282 8157293
    0x15070801060306050907080109050c0714011401050a08070303030c1b030903031101110304110a05280609030305071101050409020d09020310060f06030b03030706060306050910051512070801050103 86
    0x20a2296001003880c040c008225810982501441100a40c40e2161070b646840310b02001010002c0030030f4000e1030f05100c940005013850401c2c2c1d0003400c124002140490700c02100d1401d400040e4841445050005400c00c000c01c004124481181d03010b04000a801800100c195825010381406448229030307039000c2003c26401103445001e40780240d0310b042a403000c1c0b90200e42200c2c0480c1665107814818800200044c42c20083e8a48014001c0c2c43d100141d51389101164101c50440e141c4040c0940705143c1460072405401004000c140a00d0005030007451500c01400078458004003a1000c58910261481a4020011280200801d0708115550720400070440d0051101c00e9007244240140c42c0c88035486405030103000240c17201d40e00e9000301e152504030260024040200815014001400641c022814a1082c00019405030311f01281502c1c0007104e09041030312040c2c4400d20541303810148030810743c0c224050307200c3c00d00c103840700121b00070850640c9162000e01c2d84402c06941c20400040200300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 8159782 1250 8158532 8158547
    0x1082a0901060809010c020619090203010609051801141303050c0109020a0803070c09051e0405070302060714060708040c120206040b0a1814060d02180301060303030b011d03070e04051507 82
    0xd42d1300002c101300e03506104101e031628000d68008440b90544c55036840181d19030381c0184041d6100400024190b5510740f0a075003070b10001ca031021a0140c8640704068082e40a0052030501c020040407c1e400d850300c0c4082001001103540044c003007010204050b10082825400050030755001401041030503078034100c4560f280d220f240c0c00c5450755180400092001100c2c000c1c40e000e0003030908101045150806d160540e000001c20680c1c1e503200740c500000158480000900b80e40b07009140d1981e00100c0d8001040c5800c4c1c000d40190b0400400d0400c010104a0342007a04050350180c2c0140000c991503400000c2d002e002e19008030081a80000318041020740090380b8151043c142c000c5400b0880d55803106d1031000e42c0d003000381170b08902c0400c4098082d40580e1b006000c12450a40400c241c001c04c0004070b803c6642580085021940c0c4e03100d1040903682000c0605c14034455915400d9913a80c40401090b11100140b140035607a034055801316007005010702640c2d1410924541d1003040d031408890003400003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 8161032 1250 8159782 8159791
    0xa03021f1404050c040f05010e010603050403021f06061b020a05061b120307020606060c031c06031202060403030b04110f07030e060a0801050108010b04060203160201030608010f090b0901020301082a09010608 91
    0xc07031034221824528441409258109c0d00c0ba0075404240780e00e041d10940141600400450071801a01702c0d1440030b904e086030700d464040c1070300000a1203500b0000301501050a50b0324520301084d00e20030b480300603602ea110b00c10030786406076449a101c0d0054540c0545e04003a1014034806405804076070401110f014010b5407096a0503130858140c2d48840080c01454401c044140700280c00400281400c0c1440c0d0540c00000e4228a20006403699284c0350094104c1c0355046280058101c001403009043d4140114202035804843c00c2007000c40c0e82003419040c1c0305400d03000001c4100030a80b10103050044101d00c5c02800098600c0390b485080ca030000b80301120900541d0b02146051002050003000c8406481c103072142a0010740c540700c0307901c07036030300c14030303032690400c0b4100345c1c4441c004100c400003801a0449400301d40004144031081e850080f061701c20080260340d09030300c1440100004840000e854a2000080d60444c25030940c03840d02500301c1854406080d000a041e01c00083c0071580107407040c1c4034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 8162282 1250 8161032 8161039
    0x2040308091804050a0807020f0d060f060504020307050405010305060402040302040905070f08030307051605210901030f020a0801051509040903050c010b010c0b180717060105030f0a03021f1404050c 87
    0x1002e030720580708a15000d49002e40240d002c00e10360700008091170014101d690004015031508a0180005030300318144039011a09580c551031451030b030000741d0084074041d02c4d08507415800e600c4c2c00301e401000341c0120300c0f0301e504254460340803c4aa483d241d048070040d40e0098428046030710b0310b0505d203580702200d100d4031143c100c102030002046600801502d019a003035540341460988201179091b080800707014191058020030411078221140c000c11090000d03522000d441e103c0101900240c11111003002c8201e40d98010080d1420060b8010300e150f05451080b00c5000c50b00140d8aa502d110707001b0041c40d180c020b80303800c0c040428190480080c0480102c014001d04c140c0d503c150045408a90000c0d004101c101e100011500c10902c1c0480005181c50313070011030304850390750031400040840d184100c0c601ca4211a005000608013408504040c82c0028001e100f15900e65030000d68400003440c803114400140c0703600c0818004580c020101400e000c0c80100c08904007400d02e151070f13011310ba241520 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 8163532 1250 8162282 8162299
    0x80a0308011203050403080f0d150f05030f060a050711011802040506011d0105030601110105010f050f0102030c030301090b060405030d0210050112050a020402030402121504020405010b0f0d1d010204030809 90
    0xb101d400d001a403180882e45550740c2d80c1003518540d2a02d182d42c01200c07558002080511449200800d00c0c0306491440c48a0003003414501c0ca85840c070081420290410b50094014400340318005400040d400e80003c08600001443e594120085503c02c840c0220000503508003282d401e0440ca582c2c0000c81698000c84040140c0c0d2101401903840e405110703081c82800b210710700940401d60203a000340d540480103040210520128030301c0142164000d81004003401b080c1c076800d2140341841a90580e0084083c00254075050350740d5051035503800140700d00054246c0f218038480f25510741100b65002040081c2c104c90400010740b030041d40321190780788120065807602d0000075495284812403401c294003c40500b2040381c2070b80a20000e580001e006a130400907100120740710355410004100e005012400450a030309281c81004240c3c6c3c0c069100380c0c14540288442c00f100b140c1001145c841c03d10303442c00000c100c05100310603003c195040c18104401d520200e400411300004100508001e4000c803100071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 8164782 1250 8163532 8163539
    0x106030c0801140d1202010b06070b010305010b01050903070317040905161805060a05031005100206090c06030708060d021201020c03040306150303170c04030203010207110f010c021f030204080304080a030801 91
    0xc400740c1c810482c2036130100c400c0c801c0402041c10003042c855450701034800423908030252004200903070702010048840c85405001002482400c1c400d07480f07541000d10700b0300c1c40c101c030890000ba6601c91500014080d0f81540d0141422240504221401404000024050f501d0f100c04651072107000240f60704089015006400b60618030f00031040c0941c2c0c0d00034241810141100c804a505400082c90749490069488010071503960f42c0c400a45c0a00e101c2d070081c40185440307504c1c5820484052240c0e80203001c20300500214680000002d6800320b42510700451140c41800041c440c0c550b05c3c20706941d294400980c2c0180514080028001d40303010340400e2140d14900c1c030b6140b0040f80c041c44003a00040d10900e0300c103502e1241003691604100c44400003400d29480e90002400caa10005045030100807a8003081490b043c440d08181c1000c8e42401c00145c440c085070085403901030342c4116035680512200c0c0e80e02120f400ba41c152005812540700300c0b600e5580b83c0404c142d407402041420781c0400c06110000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 8166032 1250 8164782 8164799
    0x10506010806060f0a090b04030b0103031b020f0603040f06050a05090c0a0e060d020102030c0f01020a090902030403080604020306030304031b0509241302070813050909010207030c020f01170106030c0801 89
    0x680c01030b40b002d020989800400342e8071001030307004101004200110001c0c0000c80c08511340180000c3d5006981c2c4030040d51441c94040c00d51044043d0325188803610342c00c00c42c096a560103003501d03007203406e45015607603690320314000b0380708402101b005100610b0030080c072110034626402a88940115030458107551490020040104400d02c1941484200c210012f10b49003070208448108620600460781001d810000441c102003c07420702241503903004c1560f07030381c25900160540081c811850114507506103510300401c41c0d0740040c01203015640000100c1c41c00e8404004940c000c68210441074501c1d0b45110b600c00d4226094410603210352134000c00711f014100112001c80c9441901c0c015041152221414441803120806004000503400e008200200d844c4000808444404a0198601500300003c00c8030050f0040d03d01405607105001c40c000094210005001142d012500102d0310b040050040350710f1000388000d0345010841400001d80541c06410840d603030000c0303842d48042031fa00c8004a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 8167282 1250 8166032 8166047
    0x30204020304120906140711010207051302120a020403020303030610050f04080307060c11061501020a080a03022205180402040209032a0405061003090c0b03070e0306011406030133050702010201050601 88
    0x9080300e13081b003008000d00113081001c403942849410300640d182d007961200003c600000f40c0300129035164001441c0140540e003040075a038450824102103040c01d0954010954074080103040c2801500700c40d007808001ca0207841a0b030300d50000c000346240d070307251595402a1a0380003840c0840d00c5070f09041c40b80800750b0060750800a0000301c203004205d141c0d290301d45a2196002c200c090381c158011140181e001c40e00e24030003420303c00040d8a01603540c2c01d482407107290400130409034034a12000004103000a0351403051404a000102c003200810391168000500244118002103502d40f04a240c8078035020659906070308007440b0f450f44000c0c00030000d4140800d650f4101c4a599000f09150700703450313980d8080c2e4043e150046c007884134121800d8807182d001d55503901c161808004280c1c4014100300b50300d0108840c034058000d03020f419440e0707a048804541140410b01480b8030f480000004450340e5116100c00d5006030054445020040d03020040140055101040980c019401d21001403440d5018940 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 8168532 1250 8167282 8167307
    0x406090605032e020409140601080411060906190e09160801050904140609210405150a020a061415010804020d1211030706050108010c020703051002070309030204020304120906 77
    0xe030004182900961505040c402040400782c0701030f105500340c020a9201a102800c002080081d00e05040565850782c524010035142c100011602044000f503905c65040c3d01c598070569000381c0f500c004500042c51805a0f0000240c59058140e036103484c2ca17031200ba5074644000a450141c0d50340c5403151980c00f644445254400402c03107081c0100418145400216446801018040b0703403c005014a181810300a54400e1020740c0700c003019508102c40341042071305442284081e18075051600700400c4101203500301c91240c3c2c800120341c86c80864004d10418160b580e106000b080340300605107000b010114180c41044026440040000c0c980d40150f110600a94008140c01c0c030210003a036a00b00202071181c1c1e61000c216200303010a12900c410801343c0100c5d0700c02c040104256040c46001c6085400380e081082c00c6601a002c01c0004c14000301d00904030301303580400503035507198a04041c1c07036080131644025080f5100000704001c2c01728210795441c040e800c03582c5000c08990741d10403c947c07030040da00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 8169782 1250 8168532 8168539
    0x9040614010602031912140f0412030605030c090c040e0702030c0106050904020d11030c0303070503030613060b070303050405010b060d0b010206060312040905130b090709051f170106170307020406090605 89
    0x8003001021400388200380751945c8515400301f120703811503001e440300840c00c0c0c0f403a06854140109003c10041d000780b0010b90b1307400c24a0100a110b20b040000782e82c1d80b00984445005642ca0f1022036803130b2184004640103041100c0d541003c0d0b0900f0301c5c00a41d41d0348009a854603a51a021001c50365242941020b030099400078501307441000c0c0e64840c0c0c05102d1108000c2e603854402c0880704159920144054100c241c01480a540c0324501541401234840710510400c40952600724140004009a0142d440c4580c05203000980390313a5914059004080202c2c0b0194007803008115100200380c03641004074110020f81c01c0d244540c440c4814155101b864440807a48074005010a1042d82d001d90b00c2150300c24403082c2581c101041c01e0b141c1e281c0300c02c02030360b4031149034001c090140000384083c00743e03e17008518548a00306030110f00d880743c8500303c42070080201c0380141c4510400900700c250402c9018004c0c1d00b40e40c0643e840d40b100200c0c1d9a5000400c102d0085007000000101000c81c2e00c66070044a1740a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 8171032 1250 8169782 8169817
    0x14040507050405060c0109060c020a0201030e010606080c0703030221010501180f060e0402090402040902030906010605031608061f051b01050408090105070507171b040b0a0306050c0403020904061401060203 90
    0x3c0c040050782d411050003180d0640d6a10f5901d0082501030294401d0803801d50090064100f0600005041d0f030f0580940c105030761304000302007041c0c40e030044040d5840b03502905603940f0f8484030b02c0d0032001381c0300707500b150311145e1740848441000f100d04280d4107040300c0c000d80b24008a10214000070404594034032915403008003176001002380c2400f696020f08040070042c8010314182445000500300d070003540001c259903a01000304811b20038104505400340c5085d051075805d40c030b4101490381c030490507009000c040110510120342c1d140c030b4010f00103c100003001301c05564821a8a4018500e0300410098001c401628401c0102d1a0b41849068001ca4100040f103260a441070019141036000c84000c55051045100020300c10850482d200203048640d00504641d00003600c00c5041070b41c400001d02d00c1a803901c8203449656580328070800840760301680114085c0d403800e069141c24042c552029421409040c00c0008100701d507405a4500400c040030000d050740c841804a80d2230292540034007400590 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 8172282 1250 8171032 8171039
    0x1090b040b0d140a0b010e01060e010908060103030e0607050a050604050c01030606020a02040507050c06100905070806010e0f1c05070f0b090307060503101a0a0f050c10020304060e0a0b01140405070504 88
    0x2081d02c5074107032031043c3c0b0465100300440e695816a05109a010094500c0f1440041c00f000e03074801c06130b008644c0300b4070b0201c8009060052803902d4020600c001401d004103030407204610348030304040d500d507140c11005032007601c003041c200144c541c403040b03804459038000e061207400658000d102d204207803052036009000c24440c1c2d41c01e200080401826142c02c1c400188005880d10700e08010351440348044841e140d44083c5006582c0081c4ca8014220005201c0600100a05079910000f40b90035a4002c807641003c28400d140400c2418060003000103000d080702000343c007444000034070032048030f0040d06013100d19039403204849004e000b044a0654907421000301004031902c0703000616044986600401d0900344d617006040720170075440301d80001c401d4002c03540d00d0030302c0c1c0c000c0c10050032500d8908040e440c21000d560919103880780346078522102c0b580070000c00d051025690001ea10444944203c41d000d01135410052400002440f81407002040102070390510305040c0140c4c1d01581e640e440d550b047ca400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 8173532 1250 8172282 8172293
    0xf0a05070203070509090d0212122a0f040509010f0312050d060e01090608010506030a050c010320040306360303050403021f0209030c01090b03070302030402010c0c0e01090b040b0d 79
    0x365105030381c144158203021585588801000d80a03000200040400b4403250002070308040344178444e0004071000f0302c402000700f00c0858405602c00e60700114080203003010039038034140304ca4020302041180710104414940c40041d43c01001034940447d004141603986040300036511000d03000c02070105103080402d9240034010f2010701102c3c8402d00012400319218810100710b48400d81c080742c80c1903203500d410400e040080c8035403900408243d0207004841442d4460302c0d5600b00c0e000c2c03c0360415030340d4098420180c84820b0b0f0200c0c04d03c13100d40380690312035403401d1900c0a091440e041100c0c0c25494840000c0c0f02001c1000c550340074601e04036a498203540e035281500203083c014030682c00e40c05210040040e03c0c507500c0e848603000000c03480058960f80d0038014035140141c982c1d20a4140603038464144001502032090b254071407460700d005a581d41d120710048441e142c0741e00009054801500380441c0f8410f4080c00c15040c2c81e508001000b04940d107404220580d0745511803640c21208044080300448c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 8174782 1250 8173532 8173537
    0x5150910180807080d0c02010506041a030606010807021207120201050c0307080f04111305070305100602070b1b030a0c05060a051e0403050c10050118020c07090b0a0504020304050a170f0a05 83
    0x90244440900300400702c0149030071b8a1a031602140140d64880800c107292500744540252040345031340c515002400300c0b001c00c0e66003030090116030521240400245159208100000030100c01d070310b18a0300c1c0e400a1034500542801580010013550800c0d00103650880d40806807803007204d02d42da588110343ca465400d01403c0c14090400d981607010300c1d00044058550490091203102d038400b0010380d038504000000d00300c501c00351410b030611000d11800c00045500040e4007090712180740400b83d071100f5213001400e5407550300000622600011440c10040c0b500803125080070341c01201034807100da0300e00b146241214421a07200020310180c0740c4414212404a440c9a807191190030302d01c1c6000b0f4001221458100d90070354224910b503c55005126071501000704001e5200301c4a0158101480d90b54040e4507403409014032a9100d6565404100302d5030b800032018014032014000710b40e20708050420940f1510b000c0b00a8a200003d0080d903404908128100c850008007001c09074200340844034202c0f040d0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 8176032 1250 8174782 8174797
    0x1050903041e0e040807020f0301020406050a0e04090f0f05010c020c010c08091504090614030c03030405150403020607030302030603011d06220203010c030c0f05030103030905010807020a051509101808 88
    0x1000d03103071003c00e030001d4024100b402a070181010a071181c1841c4104008030012100c1e09000c0c0c2d00600040042640200c01d4501200c494204002a4403c0342c000c030300280900840a4404401540d040040c046402440c4012034000c034002c0c03000700c0f07600320142d980e109640003030390000d460342e240c040215980501034880f00000030f003686514810035a040c3c440b03030025000607030500d40d00c3c2820400203400702c010f0104200250301908004250400083d00e81c0140d10505002c1d84410240a40c0308085c41d00312006154004d20541c2c0720368413410028000c0d081113501070300940c600b026403481c2051000ea40203807011194018840c55030342101c1c41c01c6045500000701c1c0c1243c1d03400d9403d00103030740a0046e01500f07002950006a8402c0c3c14600426401500303c121051003010070060011070750010078441a21000e003441c0c3e51070b40b15a50101c1c5808030b2884061310500070360b0041c4160104a5880500411030681240c0903040c50711441c8040700c80d0200c0f40b0340600a203002e0040007070168005050107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 8177282 1250 8176032 8176079
    0x5040302150c0405010e010215150d0b0403030f050106050306090414010b030106031109010512070504021809071e1d0f01020312011202011d090417041a030609090105090304 76
    0x51000d1450005840901900e040303042d01c0e8046020702080d644030175025500b01c000d2000f8203d007695089090519100a070903104514422000d00489484803030000c520658080c1d09400c951509080080003041c110025220550034200000351980c483c0080c0c1f4091000142100d885c0e403515070340d015800d80003002c6084995215110545680d40a220350402503004002980d510691a0100b00c0d21140503000540718030b4443c2525507001d100001c106081e504156401030380c490031007601c071100f0701039010040d511003040002c0044103030340584034a003105094003076802e0702c000800c0d0940303084045440c00c0010800796881c00109240c4048951055181070050342e00e0242020311040c0ca8080036004088032140061641c011542e110343c000d10190070610181d18650000f20001c1c146003400b83c03000d0071440c04140303050319141858040f140203181500c00020740e81c18010700f00b15290021160ba034841d102020000d0500e40040c0902d0380309030303200300165240c142071603003100440034040e005044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 8178532 1250 8177282 8177293
    0x60806011b020f0d0305030405070501050304080706090201050f07060b010201110c03090d11040504031106060301020f0702010c0201031103010f05130501080703030c05070b0409020d0c1107050d050f0604030302030f090c0a0905040302 102
    0x603580c032110814113201d0300070b83c1d0f02e80c0d81e8a00341c2000d81ca04070903544803a040040420400c80414440b400391040a6801a008121544039000403078103805450240200b42c82c0000d09503042000940c030001034a0000c2c1c0081c40b00741c1d0703c11204249401030004000d000d4104210000300c1d80b50854070f07045614070a0310941c8184d40c0b4640840e040b0b4004803030407030100c1c103d4040e48061440800c040760380004110000d501d00001d80a90b0f076014051400000d0601c440010001c00b168041d0304248218009402040c0e16980d5410940121803024403a0b10300500703100c080601807003102e000b29416121400000c00010303182d07940072500b00ca40d4075000c3d241801100d00108400e00c540008100602940d140941c40350b501001e02030460700c58031900010b03c055030402029103880400c07440d081750f0f800c69801054800c14100603040404407400942280912001c110415816038003440c02080400440c0000e65620030442e941c1d0341000101c1a0b100e13801078010401c035407064000ba036001d44a48140e40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 8179782 1250 8178532 8178559
    0x1020705030a030b01110706050706050705090316090b010804050303011202030a080301030b04020a06021b040510080111070c1d010902030709170c040c09051e0d0c0303080f01060806011b02 83
    0x142180c000400c0b01000a807507481015003581d0286c4151254442c00000c0c1c0003403840c0c031030068040e102d6144020001da032503034009281d49000c2c005440d82c845015050355000400b2907072b20003050460b030140310000791401e4520f9401c0c0d482a01000c1c4916030000040d46582d09004e0b000103043d000368030413030b851700c1910040340c001040200514020f51054483d42510309007031040040c0c05038540c1086003150b00849000c1152400a1040c078400c4c80280c3d400159034030f0b110030700c100120182c2c010805a40c2001e01c4014012104801030103100e000300c1940a405449030140500c280c0d4095140510310700c0e0100500c9854159801150010b826080c4906895505d1031590300300251400000b01e182c000e09848003481c102805848c80140481ca0005042c50800000640f0348601100a6440888070a81ca900300e0f2502c110042400c0d0b04038400c01441a90ba01d070041000301c0440c1c6500e0b030117600c100006001401103084074001c0c40c0586500840f4511000c2d61440c50402007020f9034001d410b03030a442d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 8181032 1250 8179782 8179793
    0x6030109020d060209100804050303070c0822050a08010b030601030b1e07020109060c0305060307030314040305160602010e0c0d0605061306060c02030c090103050d080702030c07091406030c060d0c02010207 90
    0x25140c90344560310240c0c50b4405031080084c02c401080464050207e00010040016008000c03280d1000107424031040303058960810102600540501d0f042c20701e000405400c810700000410320031a241191804a017a07102c450709401d942c051010311303426030702510052000411000140780e10842000480030030510b440740200c4641d07800e4a030348026075950901282442054041e01b400308408c2d00b07050146003021000300b41e40b0207040c4006130800c466003001c00615481c04048034000c0d42c2000880b507506c1e40c65441c944000c0d00c0381c0700300d401561030100c0f520300190011032110100031008200003840c055a07200c030070140800500c1c1c0c0307504c0a4508840c81c100303a614810302004c0c3c115035503214520329152041c14030345822020418415029040100001440041e01c0e0100c0c62642c0740c89400c42e01d507541c00b42d00d14000c9100c0354001e07003d500c1c2d01141c1034a16038817014842c08840c0e07858040381c070345505254480758020070154015a040000d002000721a07006188101110f2000600e08039042c0c550 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 8182282 1250 8181032 8181049
    0x4030807030f0203091306081005150111010f0504030e030607020a03050301050603070c0204050a0506040609050f0a020f1e03040303050703021801030209190e1005010801060f030c030608100504050d0e06040e0603010902 96
    0x440e624903a51f004240890001004402c0300030380307001e00400c000c3c103211802c080e5041848038424100b100200250400d10420342240c410700b68007034800d0080d030a003880d01a04409142d04214007911411001805162000616240745c03034141d00d0f62032840e428007080c44034a41c8014400020700035441d40902c016105c610469100300220b20300000c550421030100401d0380d9a0750300410b03040d410001444009914002626008100c8203401a1760b41040d01d01000c42c0e000b400c0411512002c2940701390700707105088005602c00d0307110b40d40070400c17555100c400341c0480c00b5010034a02680145804020b05501a500800801900901e0011580011a80c6800d800190380050030f00d4600101070120314045218004060103007400e1140166042070401803488c00c004000504054417882d6051019009503c2000904078200607640a09442c0c02402c0240070b0540d4200c40520a010581035664800c010004100d48001c2c43c00e0f1070280790036000300c2d1949000d0080c5525542c4c4581c04030040e07483d442c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 8183532 1250 8182282 8182309
    0x908090d030206070206060f06040b131802040501020c060a02060619090c0201060810140c03040c0e0408030601080105010e030a060e1603050f070501090e010510031b050403050105060604030807030f020309 90
    0x1440f991405020090400001902c0d80d40203609008544003941c0d2468207403000e544a42e081552a5245501d20030340c021000e60000000b0580000010050015500100184c1e0310a8007110111080c032010301025100e01c48007400146c00000c0400c0d00c0b032501c04000d0340049042e036841004a80c64143c01c41c11107082d810054050b0703559440c200240042841801b04908980d0020094800300b0b8542050520b801050340e0504800040060b041142d2442072402904480d0301c4850203140a00d84010075510580d0307454080f40c51031000241e158442c4910328250080a030241c201c80b03c091341c4240142c105c850b00c009590251000196480d010641290000e5004000808004601c890070f54248006600450704110780880c080c41007441c03106500d0704480042d0342846118680d154100c000782030b0300490403000c041401001d203080703030b005000d00f046d68040c03002080f042d111802041103603c5a0f100c0246070100070301c5141c01207406403140005c1d119990068030300c0d01b2400e00004403c54032448 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 8184782 1250 8183532 8183537
    0xb060c07030312021216090803070605040311010e0c0d1a0c0415030501060c080a02010b0a060801051503090a1101140d02030411010201050402010c08090105040b030108060105040e0604030c0201030908090d03 91
    0x40100305241d0f00c4100041c0000650030214503054800e5900c0c8404040103007900c9424804071021002c0c5840f4110807001800b9610980385c4503a41c52404c0c00103064240d0b4194001078039000100c0d0404010f100d030104842d000303401003080340c500c40300780062200000020340702c000c02100c40e0340e000030301031400610412000c804555114140700c00c4050486461004004161400c1d0062214540000818001641004596844900521003240902072000429801010203840011416005082e03035041c4c3d10222454070001c03030701000b0740c000343c0070880b2040300960000d0304000101d0065110440820010f16102d0120740d081c0e40e101400b940300760364882c061540081003209124004040d03004000091000784134030300b0903400003880500444000ba000103400a414041607014401715401012050340302512580e55582d0385413103150920800c0c0c001c3c2d007800f000c00790309140890014415949070701d610301c3e20740d400e400440003001c0394401107422810810043c8403507558040002222803203903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 8186032 1250 8184782 8184793
    0x50a0b1807080f06060c1b0102070602030a0e091302030304080f07050d08120a060504090609060b2205040c0308030405160501090602150a0605040219030c1409010f02010b060c 77
    0x2a4184040c9008403036440c040c1000440c1441000d5902042c400d410002c160102105a00ca007000100c180c4600503008180e48211903001003001c000c200720100d9a2000d03026a4207140d80e4120a0b6200c3c41003900c81000600141c10305101464000c032201d82000f0070a0040030750a86079408070786560700940110156520800c1d1000b2800003c20041e0702400003543c004001d60380680c2c80184500801da003aa0241544400181e4001c03140d6000030002d02c4005c10034480b09409007401401828540e00607103030035041140c091064140301a07603489003a0700c00d10710b07208540303c404000004c000103001150300c106050b00000106c2d4080780590700482c0181c020300942d107442184020072000540c0820305020182c0400c200c01d0b41c0210711345084080a000c91b035900d40d141c070001002001685c00c202e03405440494070480340d24504612011070f0169031020032a94811220540300001015000c1c03007440400c00070182e0652040c0c51079022801c071400086641094440050581d41040003a40d146d60300a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 8187282 1250 8186032 8186051
    0xc060f070c0b0a0807110a021504081005011401120207081803010507030c1b050a020d03030e100504020a0603020d02130312030b01030207020607060b060d060303081014010c060c0306050301050a 85
    0x5072441e94024a511103201d8902210b4200c00780201074014450340920206400e80f44a46e14180840000c0c260700404c03d03285114805100a00ca41103406034854600c9425458010410b00b48581c80c103841400d0030034109a0410070045031850440284280f400c0e409108000025200e04094881e0001c1400c0400c61003068a00341421128001c14040c2094203220011036580d4102c801c1c506840c0b20b0780d03071008404400341401460b014440324020f40000c10f25464006240c0d069200c0900c10224800b40e07101c0101018091042e0781e01550040d60020302c5c988200105070003607000780f5400070314044c00b6040013507070034024080ea00ca030303070061341d10030340d146101401070350306201384a040d00c03090a0450500304190041a07160060400040c651513660001a080f07503030304000e41e80c2c241540031051001c66101c1c503006203409001d6444903070040c81441e0114110400c0b148a0100c07003c1a5140c080104d01e42c2c8072040a03100c04070a41c01415910040456107490a0041a100320f19202020660001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 8188532 1250 8187282 8187293
    0x4060e030a020f040e01060512030c010507080f06090415090c030b0601050f030112020103090f05010605030d050a0f0e0f06070b010e0705030c04030303090516060305150306010b0405120c060f07 85
    0x2825500980309800a85540340141c0e034090325204408010380d000070701ca180d0b04500340c0c0105000e170405039026507000e00304910f040001005104030044c00c2d00902c226122440d0a0b29500c8069908414107504240060202e003801c5880315800ba00a400920107817240d14034031021030340140010341d507070740c07403640306000b4440081c04460f0070010078a00b030761415200d4007000d02540418029290b80c01462680a01903a00c607411840b00f003900074040721040966442c10500805582c45854000d002e86003081098902030800d45040050544848400e143c00120488100c01917110b01503000c2c48903c5005400d40320f640241814521030b00d41000b55505113820790007003c800510702c4007049820010082c0090000c0d0a48044070f500d810045102201c40c584541003501d904500034134480c1e110000550903030300d0307005540a0b5a0104000e05c50781e00040070316840e58024040c69113510f80810080240f4181804000c0e56a4010425103122084100c00030b00154006003100c80700700301c0851545d0a000c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 8189782 1250 8188532 8188547
    0x503010605091f021606020609100e01090b011205060106030b01080604050405010905100c090b07080406050a0201060306020f030f090604020913020604030605010305030a090603091a0a0b0a030c0611010207051216080f0406 97
    0x2400100300600e858021503507526801c0e001c035542c1a2f02c1d48041c0881d000250011070503140d01c802c07900c10942e1a881d40b103440140f120b070251424820320700002074590080c8540d10140750107030365031071017542d4100900010f400c001e001100c0c103650701c140400118405000c042d1990301c004402084044110070014081c00d910b81013080c541e801004240c000418220482d4100d400c3e9090064690084010513801001ca5900c0a0070346070000420f0240080d01c000118402c00c0c4102d10101a621809042960781c203040358001c0d0010107030004109800300300c003051001c00d403000307008038609034032079507020162030f401c4c0d00454580e4004940008603a8020700c801014000f503160400048805880f1903844801e00031a03c075004102001056480e14250030042c0006009002900203990301d15088000e034505200c1d800014401c0c07003079820740200c180211407040d5041002003504084580c0420900d5010300305a1000350514124480050150340c050961481050042521585041e1300034000b107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 8191032 1250 8189782 8189789
    0x203100b0a1a07020d030212030103030507020a06021f0519020f03071403040b041b0801020703091503020f040e250c0302060c0408030d09080f0d05010906090902010503010605091f0216 81
    0x2000d62210b4201c4948861094a0409030100d502401c688102d0030207034100a1442c18001d240c01c0b0001c00403050681140003000d58600c2594181003181d503076134089031100c0c0642508c40b61440c0c9480014040201c54001c540c018074030302203101d41656215081ea08036440385500a24880001c010080010782201101d2101c40392741801c02d18500c0c0c295100f1140d03040040c0000c2c26100d04a06042d441a03040b0f030960050a080c5008540e00d2210b03050180c00d0b110544644c00c071503403442256a50541c800d0081e903ca02c44100b1003d4109801d0100c0c241d01500003c0c22030300d902030007640a4900c02034103000c003480e12005884940d603048940c10020b04100e0300a0601c1c803040c204100400509a000040f201788100140000844042d18035058181e03201c0e012000e4110040400c0f00706c0d00c0003140c1d12031412101e00c03140803c2400d1390382c010082510081200640400d40500040048a0160004101005004106a644c9042c8101c401d502d200808501001684142166031201d1581500c1002a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 8192282 1250 8191032 8191049
    0x80a0b0f01050a12110408010f06050415030f060b1804050d05070201090501030e0f0d0e01031802030a0201230409091a09120c03070506070804020109150c0204180203100b0a 76
    0x1540208000a4142e03c58101d620302085000c4a4086404480307070700c58240e030450000790302d41d80c61303031400d140340a004501007402006250100001e401d00d03140c842d00760b6096480840469181c41c6442c1c2c1c4c0c100400c1d800054406a40b030b440e40740740d2661424582d41903c8107608502c902c82c1032031706029103400c2d18030b05400c0c00d010f4204041000760b0b0304200550200c400c03d18010440398940321215040c0f82181c0c00701d00e824410700484024454104100c000205002e03a005c00075220555045e050000142030040d4050f0848240c0d500903500c69450501171441000b802da014107042210091141c0c800d41c816500c2e5980e41060300104030400346000300c2a03110005c5003056081a03050f503a1149415a9880703031400c000182c58411040900c141c0d461950040190790151904d008080c07d100400c40b8100e0020703119a0000c100d08404e0203000000c1c4045940e0f030b10060725640c0c03d004c010b007007a440040000500c42c40780380060b0790070020400c50f0f80074400701086030f00b0745034240801454039401400c503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 8193532 1250 8192282 8192299
    0x90b0109090b04090f0302031b0c060d0b0102031306020a1101030207050c060d090b01080106080706020f0303070f0c02030a06240803030c0304030e1503090d0806030c010309060e0d080a0b 82
    0x4580e4455110340070340c0c0c01c484000504402d81e1001070002c0050f82401000b2a10018000e014990080060800d4007820340307080300401020114140c5980c60b407100c480d4401d605121582c00c15402d50b0007824800c5041c0102c0703140c6060710b1481c4122031460307801000140d12a146c20000c0180c40c1c00b000e0340911013070a040d405d00201c1e41d00d098580a8908a603801030030301180c11098101182c00c280800c50f0481035051040d42c582d03105a021304a14014112140310320480000c0062001640c24a0300d420800a58215100e5810441d0401d03824080c1701c04102c549131081002da50188414103402d0f106410001c3d9050203c003140c5100640c0c66400d0f0a0225251010080c0030070210840b0303440700304680c040da940d5844e464142c4002009401c15070308444501c07550002500c0600040d4060001c100898000c46469002111450001c0341d025400d0303004001d500d10f081d4001e811410340c0d103100c0e120206911f080f04282c00c0c5001c0080c41850005405041405030120043c4680e110380542031301c0c42c54 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 8194782 1250 8193532 8193551
    0x7030b01091b05070210030f0f050a1107150b011205070e090105030309010207061b0602040602030406020f0c0a0501201c17100b0f090411070501050f0702070603020d02090a03060606080109 83
    0x4010340220071340607002e0032481132035070400c502c00c0d408481c400c401000f0402a502030380310000c00402d41221030300003991900484604181c0441e050b9000c26500c1000038201041c0c00f01040d01034001a880c05060001c88000d1088144c0207004507441a03a0640d16450030710410b40c1005400c46040e88202c0c0290402c0241a800d0799020444070241c0c1c40c03c0c00c020300d0f00c1c0c54002000303282c411110405040244089400708440707034040020710488040754200c52442c4c210082481e11502c50007070485c0d000307000100801040d40070703141c3c03140d03106c51014030130407080d06042029040c060155034004003946008206084160454040012205051014025440c010080c551000f44a0041007100c00c0040786442c02079044030120b607001100500107100c2716041504500c029005420b007100d140d401e040000304642101504c0030301c140115402090002d103441ca081c3d0007075203d40ba510400940803c403140741c54807500c003a400254071550001581a151a100806d404010380040c0101c2d0b0400c0c4480c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 8196032 1250 8194782 8194787
    0x816080a05070210080f0106050f040503030c0322050f01030b03030d0608010605100302040b0f07020d080f04030b0f040c0315020405040905030702011413051e030105070e1302040605030a05060102010e07030b01091b 94
    0x1030550382300b41499555140042c0c100100c034000d80e80101c3d41803000041a12145801102808524542c190f5000c42014191014414003240303000b06078204450040d8407243c1e42c42500809080d00010f002d5070f04d440e070312044000545125806c420500c2c0c0d1101d00c02c101c541002d18100380750795054035003141040d0a00e80c000c440c0384141d401c01f6000c4040410f617030b4255030703c1e00240210164003844c03a9545a141d00c58604e0290800e10090f0f0302c0aa40340c000070f801550b075002c040d03c507541c4850b07140c110500303550746c0c104644548030024101980c284808141da0316144180c0318114020700c010f6499264520006201c401e07102010843c8182c03d1155040d002c25003a030540076070360225640c44450343d154a5081c2c0d420b40525076030394151708103014020165005030360540d40c000b01366005640c82c00181030316000e0b80703e14480d590008908000040403050540d100365007084051001080b840d840c150210324080140c0c0054900082401c01000034090704c1c4112484941c00c076002c244010500c4001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 8197282 1250 8196032 8196061
    0xd0b1504020f0904230103050c030615030606130608010f0204030b060103060602190302030f040b090a0504060b070204090503040b030403110607030501050d03080a06050907020c03061506070816080a0507021008 92
    0x41a0140b45c80e10f00d804600c0c08083c50500d07041494003039040096950b0700340f140d590070800d80880c2c0a40035038004a0140403031949030044a11000d0002d2205458110900400b443c1303080c942c12646641e98000b1039121340a000c0d01e009038403240c001607259404e500b82800300e040701806403410b0502d08141003040c20340203c2c0e040781e0240e01d030241c184946000c1c10f01368118820b111040140c0c07240080c003ca40094440060300e85400b0aa403030104c0107032a0014002224458010006852414050b07800103142c03903008070303031160320440a803406e01d0750f03400c204c0c0444c0c0c009079003c070082420f014860b02d50b41030411400b030b4007181e10300d42801294940400701d4440303445904043e08100c00d4070000f46110100d07800c040001c00010b0060315181c5031290000752120074400c2914480d004a20100d440c04e8112040f6005a0030010003080c9840e40c0d690340e03189a0f9010400c0d140c3c0a41030040c00c0f8001c85e0401001e400c00d0412a00c0345d913510209481001408000b4014001c2406201c030b00384502505000b85 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 8198532 1250 8197282 8197297
    0xc120f07030b06042304050417071104060e010e160f050a020c0907020303011511060a200403030801050909030315061e04080d0201060503030f090108150d0b1504020f 73
    0x10000480d11014411005058080c2d605900407800040024549641c1040001d036010081c5003108007400c6a0104401e82e20240c0707019040c4010340642c8010095003500030601e1501c1038130308040c00380052000c05d00361000e9510055200b07640900400440d0080d044c06580300d00c0c1c4254038000e54032071400280552a4042e001d00c1040008140980058000c11983d1203110004000006c6890302400081d40ca038401d00600c1401e40e03100d43c006000340d0140c0301c003290350700700c01015003016916a02e6035001089180109500c204809410400d023045840c001c0001d14040c1e82c5101e019810401400f480e00c0c4060040d83d06940208100b18000d0826106040c0c0400102c3c0e0a03139842c01e44c080c0005000c0345080c02150846800140020b01d45000209150020040e800a02595a8800c00c05031a405860301244120303204011452242d8440d03004a81d100d02d0409114200c030b003100010550b04003024008680c0f1030030070402d1226602e01085c0104503c6030484040d468820b60218001c2c0a000307040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 8199782 1250 8198532 8198551
    0xd09090203060120070501020c0402040305070509040302150106020a0501060b04030209040204050402030120030a06051503010902070302100507180b03130204110d0e0a060b0102030301030c0312020a020307090606080c12 96
    0x4040b4586030b200741c00c0c02800c400c601c0d20304400012841100c41e00c0d0f21352881541d0142c885c071a005c40480c105030003941c0c122a041400307051103a03d440144003005900600882c114040c54021319540f0074100b0fa018060450340d4000e00a900c000e02e8880e007120050340241030110401d000c00c00060b50744080d1281c0c006e40c1520080b43c151030360720121780900b00031418402c0109141c05000d64649003000512f1040d82848000d00c8025910014442d0203841006c1c000c4103003608000500000c001d5030004c207290340c0b0902c11a10b040c4814040d0314100c03142901c030000022905c070610f49c4141440d076000405000918005450350038100002c003010330510350000e01860715a10f206640345072680a03160300321200c8a0a03c4990081000d1607200c0c070a841048911502d00030340103656520000a80703046c4c1c0d5105406c0d800690840d1078030b100c0140c01d51414011842402032040060703d06001c0c981c024540c050010a50300c2c11b14002415030718000f00358a41c07001041c4145042050487d2807e604141d041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 8201032 1250 8199782 8199787
    0x70c0315050f130c09061d1302010c031d0a0e01090f0605010210150e010902042102060304030804060e12030907091a01030e030f03100906090c0c030e120105090303090706020d090902 80
    0x900d8411904140d60340440440c41ca4110002254100071f503800003203040041602e04036550704400b1003104003034020045d001130213980312200086c0c0070b4180030742414034009440c4088622000003d00240440d00a0154107060310300400c0941c119001da801580c020750030501482c0e0400700001e5903074030b079814a11281900d40c02080840c00380f050755003014040b2222121440e60312240110065413080c0326044054000070b8092100070150b030b41e81c2e180c040c0d00601072465a100d60302c3c210b8101d003001d04143d89880d900c112504407880204082d900d001004c2082d10b071240307802e203040b506180b1030380d00502c60182070000c2c0040e03051038949000d46030802405e00041810011a08a2850260078a8030340407141c00000d003c04d07460041090130499000101c01d20a00313403580304910a9502c3c0307a101a010508200d580400640666000f44090308050322200310466841c000c58255030003520b40313900e036400000074010810303000e0186602070a0903000400706007445c07100c01411060a40f02c0c030710105a01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 8202282 1250 8201032 8201071
    0x2011101022d0705100e070f06050f0d0204080604050c010305010603090209040605040602090901030303020c010c09140d080d090804030506010b070201090b09040b150307030501090506150306030a08070c0315050f 93
    0x50b20280d401081c0c01c88111007030745041541420007809058040751491042c00c00008101400c898241e0a460590342c07014100b11604a401d4902d800040224910603024800865220001c0000c1071107140a000140701410f0004005401c640c4103130414820107003070400007030150720b446a0303480c1c1099208400188580c1d481c1007000c0240100f50a0a0b8000c8030345000005050340b41c2c01510030141400020826411100c00c01d44458005115036020258003d405125901e4110f00b02030070035000c0d00301149800d048030701d48402c0f2152001c1c2100c114074040350034418410b040141c140509a51011207140c02d080340c00180240c52a4800c0c80d64080c400216084103440d5a00240080b01d0b020340700d10100a4203000909090300b003102c44100081c5040e000240d009982e0058a000780c0e80940070130064546196005840d6000909007a01880b49480010010707085c1001000e03d54024691100c4840c118a40050303040d492a14012149080c4024032800346181c94002d90420302144414801020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 8203532 1250 8202282 8202367
    0x509071511100e0d0201150f03060902010306050303030109020705010e070614070c030803041a0a06030305090f0303070b0c04030b0702030a1b02030a05070609080c1c060c09080102070602070201110102 88
    0x4004103050080340c24620700c840e40c8030f00090f071010ba0020b290002d200c0107850030304910b11030302144134820112607045000c20106480c0d074440050b0600601d404145d1944a00109103554006e81c01840d001c1c3d4005029070602000f8401c5500c0f24000d00050b0403107030701c0c02400525821032a81da04881400000303804c02000040200c6d0710045034810011500d82c030307160802d100d0482c48490b00b050804410000184000c03198400e900540e0f515403240750070461004240030103500010301c03550301880204013507008121040401807184180070481c1340c4d12401e5142800701054054101811765005101840e01035410078401031500c0110040c8046084013400001d16013103200e400a407e5004001000c130f15203600c07544240c15600704004443c02103030160140803842241d226102a00164800309000050079078212985050302072810004e0700f80c5440c041802c90380a201704640c4c840e400940c070021540c0040c0014656003021000310b051440039003500b000c600703008114454883c01d05001c9100c1c600e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 8204782 1250 8203532 8203543
    0x103110d050706030209100f0f03020307050913020703030b031504110a0518060108070e03060f0703021b010504031704080712021c0201090203070e160503070c020607060f0509071511 80
    0x503080800c40e0b241c643d440c41c1c060001c0d84150781250042c24005400c2d80c8203802001000e081c4522907880301070b1011840750032030003074002500340000c00c1001c00c81c2090507540e01500c04406800c42d000103980e10170524024044038000280c1d03074080c0d040804462140c090210403035910941010000350640d645000040d14007405c1d8014640c4659503d40481400103000030300c51096400b030322030703210310386500740143c40362040c041d002d6074994006c500040ca90017034030f0102a0081c0c0b29050240c28500f0804001000034500f00034000541e54500403c4280b40e030009075040c3c031420210320303000300d810591100481441107600281200d040c80f091011028420080c26011651882224500c0c40303142030005e02a0440c0e8201303a11900c1003140100d1150340564540380680954032a00c0b40d5100c50500684044c0c1004105070280103000b020340300942c440c41d0041004038410140024440700f001c0240b0101d40005d0101c092960200b4020f01150f01c210710555032104c1c10341001d000c9101e044900b85e2600 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 8206032 1250 8204782 8204809
    0x90204020909040f050c0405090a03030b0a0302060a0507120519030207050a0c090605030c030d050a08040302030903060f18010c0e0409060b040204080a03080903090102060106050705011b0e040b0414010311 90
    0x801c00b0030441803001004070401400c0c807880c1902c86150405041006464040d44e036515503070000c0390403c1c0041e0003588610400c4d07001402c0000c405517650001201500324800913804a10001411010442c40c3c428110b50610380c0d061075400c0c21440180c07412001c003801c040e1014594002080024490300304100f140c19680511105a056268290740c0050820351050b01c1c000d10071040381c1c18a5203004941140040381a59669042c00101c3c03200700c68101c070251003901035010400240700517490a110710340c825511700300200d50034108020030220a01c140c1402039200c0e423410500780482d03a40700c404000d500004407004034440d80c003402c00200400c92200c81d241c0c071502c0041d00140c111004112400c103075020ba10b518100780e4030010015100c2c4281c00c14140180c00c00381c01445500e004074058a07a9902400001034422100d00790300c0303482042c04207014042242e4102030b51003403600340984800c482007030310140020079140c5054054100306000061252080c0d84110009850705800720264 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 8207282 1250 8206032 8206039
    0x150f0305060103020607031b0c060f0503010e0412170703020307090b03060102060406020a0306080109050601060905010512060d060b030a05060108070603060e0a110708040e01031e02011d12070b0301080105010e010503030307030902040209 104
    0x516080e450b127035048000c0f5100d00350200d00c03581801c00d0a503010340c0a4034100c82650081841c80d40d02c2d60382c2d00d04500c40401d4400180222034600030b20b01180180c800d481250075480040c3e807414189006401131a140d44030b2a070300f000803c00c00c410341c5d9010400f1504140d12207000b40c2c9400c030044042d809040c8540045034950b20340070000c000e000001840034100c5d8540d403180b0441c076440d0001141d403481130400d602030750b0b11450003146050600340c540c1c0704654050b0383e00059007100d1100290402d100090103035400c1e802403005000304002400108010704890800300080341c80d02d04060300801d401400c440c82d0079a54070120810107200400c903051254002402f5030381d03d86400d00742400c00000c2c00151140d4100c107072402103840e01c01c09603031040c41e0141c4501c0c41c064140d41604a9a0400c0803440c1c0d0010b6003400050750300e050800c00517018100410280380c996040031041030840c0c005921500c03180554400401031920301000301c1c0d03007007051844c004c14090f0300e80c004038019100d07220200d0b41 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 8208532 1250 8207282 8207327
    0x1b09010e0918340302061603090302130c02010509011a01080c070f03080a05060402070b010509061503010602070306050c130b0c1204121214030105040f06030602070303150f030506010302060703 85
    0x1c2c3c090b20079031003d480300000c480700310003070601c408a600c840d05030000a410038420420000d6804152465003c142d102c0d00d04060502e4603a80868a178030301840c09100e80c5900da44213148042d80a010301035011a0220003000000071145512010301c60605516060100702008140e004480004641d48141c00c03402040c012006460014680d07203040303880011203440c00c03021480b2440e0038002c4031400358000c0341c8a14683d083c101048241c0c08003411440d41321046c2c007858100881c90602540c020042d540147c4416071640c00c090085e103c00074500c0810704000c003c0001c0703030a200c00075803081d101c0e24030b501c586403070242c01c456140410511840c58000302c04100051a00f883c03e0b800c0080d01e10400c101c1190ac0d004420550b0717105010410304083c00c406000610075410290700840313071581b00c0b03900880c41565030b4031445d0880e40000e4040c1d00190300e80110030401d45903100302c100209640781800a05034616102d6948410060000070700c602c0e0b0000e80e4005140c030548180341e003481d81c0103180e203 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 8209782 1250 8208532 8208553
    0x30204150504030b0907030506180c1305011e03020319021306080a0212030a080a0203070201090b0a09020a0509090a03030b1305070905010201050702010209130903050c0303010902031b09010e0918 86
    0x60071a085032104880654002e8001900070341d0118001c070842c1d60020040002e500c0b01030030442d68114051880d103892048100b4140e55540f41064404600c401c2c0000080031750514a15460070303a480d0b03000c111242c005a10400042e00e00003102203a143c1d0020b000b100081462000816000440602603101814048085000d42e004a0061000e0344200d4002071a510315030001c585a0140313103030600104070b024000451544c00d40d00203543c03240c128400052100819a114070104c14251050320303606554968000850405a107000050107042b0307542c039154600540003640e0350f4040040101010b480790f0b05030b44039895004012203c20300580050010f171404450040c814000c620402c0e0041d03081c20b0125010301c0c0188211000154083c00280c041003076080010050038072550b0440800c40100000440703540280046c6002c3c1a41c0708025a807800d14002c42c0b1002031b003507854601e01040402074071090340c0c0c1000b2180d05500054614007410354072030160329190172101c1d4654280d40902d0084d00b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 8211032 1250 8209782 8209787
    0x20c060306031e0c03010c1b06050c1902030405030105010605090a031506030204020406030b130e070b03040c03060212010611011103011e0515070204060905010303050703050705120d0906050702010c080c090103020415 95
    0x420428080e0000c02407c030f0035020468070140d11035851024152000c0421000c16480c1c6c002e980e000c182090030300e28040703141c0340c404607602000c150b07900160808602808140b6082c080c440c0100b00c130386031036030500d210200003440c6e2a04512004010211071310b04074405c2c0c0c0054104c0740046400070b104540f102d40d00e190203809032034048082841400c094a01031b00106c400d00ca04510f0f04007800041c42614203040d8141125030004d4420b94800c0b1072154000300003500350009041000d4144012103107549030078000b60556035400015000369040180341940710341c900050301d04580b082c2c44014661695416005600b0b50160021a0061540068544258844d0009006041c400d0318100302c01c55490300d49404440742808011300141081040c0d201282c4201e0182901c24040c10944e10b00c0020000710320710070b43c0302114040850f44c548010708244101307441035035840401c03400240034041a0420007050380c1c100a1060a40c0340c8040340fa0040ea074460b9058401030000c010b8102022a00000d02 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 8212282 1250 8211032 8211043
    0x20f150403200c0d03051308010c0215010e070804020f0a0305030315040603080702060306010909060602070905090303090a140703020a09020c06090304030803040209340f030b01020c060306031e 85
    0x50700410901d8a00341485606116068071100d402406040000005400c10101258060081e070030401c0034410f81001d0b2220340c904000400800000050300140904c0190900c2a1200c491580c0140311004008400001c220307250300c000f6034a41540103a856200103146055140c03001038100016080c04000c2080c00001517010344400100c04000c295100d00301300c141d881c1070000a0141009002490050518601441c5c019105041c8900e2880d100e2041d070089441c1c542c01603005038840041048548020300c24690000c040c039014500e58500090740c0755440c2000301000342800d007548000c4100007024402e0720b01540e4001d081c06a104c0d6103c000001070b41002503400d1f8180140d0022038468540001250201c036849912a4115a1580c08020407036030000c244003040340b1408032a0800b240c0700890007044030800311601c521960351080080141c900d0464000c141403030801c640000baa000500c0e4410160200d59a0f566580c498002c20f040454040340d00164030140c01c101042c1d404040780 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 8213532 1250 8212282 8212291
    0x10c060510090e03090a09020703030617030706050a06030317070908030a08041109010302030a1502070204050a090303050601020c01050d0515120a03030507030c0e09040f0210030903080907150807020f15 89
    0x30248003c909680c80d20751644141d040c0c140d44111251010449814250050952a03009040008800b5544e03025171035008a440b0700351115400000d0200c040003884d00c20f0503004100804108902815507034060700c04004021032030b82d40d00700c2c28005480944a029010301074034502c8192601c0e00c0400e0000b0307001010990b41103c0f00515655060a5030400c544914100e0303400a0050040c000c1e030742c82e410032807100c01d20003103010f9400700000c0025844502880b40641d9081c00d002907071a0803403d0003400c461002d0049030440d00440100c0750300340e90120960350b1000c1030b14030000e066110540c12003965a038542019401c5840c039104c2c002440b01c0403411001d4503000340c4050040340c3d42c0003400c50442d0780303900c201c0c40480d0703005581d2070240c20700c0100c242d485842051550b40070a40340d00021201901c2050030342c0080e88880c03541701010380c000d03d42078212103010001c2030054208084503207425407080040e410070080c000001c008502c01c112a03181e004010b001d8410041007074003106003050040703d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 8214782 1250 8213532 8213549
    0xe03060105100509060304080c0a0b010504050f010302010914010302091905010908070501020303040f03020f06010e060a0b070503030a150b0a020601091b02070509100308040e07020d0c0803060d02010c060510 91
    0x800020355420601080b0341050040e07601c241c500300c0d10b00200011070700040c00030394100d070050107001000c55080148103003050107045500e115624003c208010340d440144040c0360982250300410061b43c00261136001e50719200312030450310542c040100c000f8080c0001041e4021501899480891501c1c500300007511805ea0300e80c401d551b103400e50b240c2e8407010384c85403a005034010400100030552070890716402910031320644003403040310f5140703c3c58420282c01510341e1240500500c450b40c5040030f4014001d06c80f4015050030154192245612400014101c1c002c041c0c40d184440c0b46074049410b4100a0030789600e100d5155000c1c1580255185402d003c0c08807001d00e401110640c6e196901042140c4044030340c0106040c2d402c2c4024490022005802000c03500b0030040007100040443c0046e101602c55501c8550b0980313420300000f0b1821941c4802403050155201180011984000880342d2014017914886d00020092004a44110140001401c20340c0707084144038810130000310420844c5c8040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 8216032 1250 8214782 8214793
    0x112031407050a0206031b0a08060301060f03020321090306041202100b0f010c050102130815060105040609030807050a0f0305190807020a110a0902071518020a030605061f0e03 77
    0xc45140191041c818042c00d56407001c4030400041ca420360065910109041c1c1c40d0200f8815034060100c0c40e080005440e001c12105010403429042c248a400f009100c000c000300c500078656008203132540c21051b030f000c603120004001d45021020480c22a00102006022a00c2d24501802c005d42d03025038418038240140180d0b4518a5000c1c424001c01e41d4011000340050b4515001c003005560001e8002000c442c10b54090011804041e035a40b081e030001d00c22400a44024030355660003c0c1d5991000301118140803080c4003d102d841c1d406540081900d13481480c81c1d540310003a0900a250500b000c86c014070f21804c41055004056119002d02400402102c00900d0300c01004000c4d101d10300308484240040c5e0044a0390000305104070608001361501920000c103190301c529042d016a40100070541e85160b142100108201c4d580c412100f61740780c51803003141c24110300d80c00944103d8641c403000d44415200e8000c50020b94844400d440c034000d401d0061010f804070b180002c3c0c843d040a10382c40f1b10a0262 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 8217282 1250 8216032 8216057
    0x5010b030f060103090201020c120a0b01080d090303050c0304090606030e0f0a0203060604090311030304030c0b010b031003030c0602090909070602010606050f0a0809030f0a020c131a09060607060203011203 90
    0x1100156800780381400d003080c07803030340c0c503000110018941000140d045100340428a182a00d90b810040c102021320303000780a0008080c1030010300b40a06a0085082e83c2c454410742107455440364100301a242e040c90301981e20400550640d20b140103a030048059203291100019102d07815900c00e4580701040f200390f07048802d078004419110034180c140a07405812003c001901031800b98001e83d41d5034800d003003445892192841e2145190000c541c100c0200d84148440350909c40e00407001d03401000001d554602d5444c1840d070005040c2054480182841000d9280703404011403038041d60311031640500b09561070314098080d0742d56080c20b841841c015529200f0080303000e600c54000c0798843c0c5484503a052402d0b102c0c80c012900c1c042e000788100743c1400709100c40b1300b0480031007005202071740e61a801044074160b02c03c00c10103d03947d0007000c410740600c1e00c5008621810f0250080e4007080d42102e0800542c1d5500010a46606c00d11100402c55440000049607006011450300e01c06406942d500136690704 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 8218532 1250 8217282 8217299
    0x3160b04140301021305040b0402040305100506090907060f0c0c0b030717010f050607080f090d0503090108011203080f07110d05120f01050603040b04081c0b0316060e010516020307060804060501 85
    0x210142c2c0c0c1c1c400c04008200f07200d02c7c20a41c1100c0d9940c1c078003420052a0959903105e9606055180e118001a40e13290404c0c030015241031448190040000313405080340520300716000d80141502041d0609000c0c960342020b0500000528100042c402c590540fa075070725001a00400c2d0742003000c4d48884440303842d000454681c016800352000c0d1a4040c160038034050882d101d80c1c03255003040c8541344211808212030700c2146c50782e0f4416801c01e441800110344800e181c60000d807290b203058000d034150702800c10203100865808501d5603000a416000d000d5640c65001084664a0450a00f410f103449281d0084800990000041c11a000a40d44032681915172040c9050071030428428107a02c41c00a00c04580440c0000a910740c000c1d20aa0299262400000c8020300c0303c610036107a24401541c40c003002907942800c2c848880e00004454401419904102010f40040741881c243c50400c1408144003050b042012400f0002e150014100e5000c82d075100e00082001c2c000f02d408891003400e00000040c0143d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 8219782 1250 8218532 8218537
    0x60a0e06010f0e041b08090d02010b150306190609030605160207050105180d08030403020c04110316110102070501050108101808160b070809010e0606030a0b0603160b0414030102 78
    0x84160345601c1c94515955080312034518003c000780c0d0243e61501c007070031012a0002d070304241c00c501e0344030401140307020708505091040030702028095904010071580300307903100f0b450000c0d0744008580c4540c498441d5070124002c40110b006c950314100440c04d0210b65907030490101c1089901c00c2a05000c16035401e02c030001d880d12401440c01c0075174011801800290300071382c06043c88006d2812130603860004680001c00789044d00c4000d6810750800401e10090507411300240e0358103030f01500c0030f10002100101c07150359803000414100102071700150b00e400e06d0744210040e00394482024001e5440741090308005008010a1184103018401d4801048000d112030284d1030303d0030410200d92601242c1d44d210692190300001030504040c0d200c1e031070000061040501e541c065407480e0307681d150307501d0302c1452a403c4610100c22880e0a0740510100082c1d0780c1c000850a2019500242c4078821381c0b114800720b441c00e000c004000300d0001c41d256011607003100d000c01070421100000c0307651240114001c00d150817403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 8221032 1250 8219782 8219791
    0x150301110306240301030c06030e011802040c0c050102070b01140919020a030e030a02060a15050603010513020c0d02010515040504050c0d020f040204260f070e0c04030209010e060a0e 80
    0x440e400d100048240c0f8000b0000019503015070900010900701d01c1e201a90b9a00036002150540c803044001e2007101c0d071604c0f5401c10030802400801c0b80c014003240701c00c0352100a4000034804ca03120081611b92520900c80811501e81c8200251b4030741419240c02c61070300e902406551b41c01412400c4c0c0880c0341c50841aa10301420942c090b448080415500342c40103513001e0f6031050103140e00c0f5120440050390400c01408083e949a000c0c0100c1e0814812080584412820128001070f030400b06101507500c0008807811034a04448202400200618110182c010102c041186000d5901d140b001183c0642080b0700c94a40c0910410b5002c0b218000c0204a07070055132301402550007200c0c1000c160034411850308c2c2280c0000c084890f80c005502c0003405036402030b080407240701c40b0b50310405000c44080341c1901240c203101740500000c0b20740440d20766940400303114250000381c403031004c81ca4a007103200444024540140c6040019038560385041841ca9080d1100783c0503000e0a800000c440b041540400e004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 8222282 1250 8221032 8221061
    0x9030a08040305010e0a1707020d0f0f0302010506040b0a0501051309050907060801080610060305040f14010204091a0105030c030c0403020303030c0c0d09030507060c0615060305041202030304020a03020411130e150301 95
    0x40400c21f60b03c05071038101040c101d07045501200b0f44008100b01e0030404403514071465031480600c0c11468020700b9181c0c090400c0780203505140c0c60f00d040d030750b50700180e9054440a1a110b6228042d21007100869680d980c46034441c64908001e20007404004241072080d18041d0b260085103076a914007043d80c0b80d0088074000c60001c070014040c810148280c01450f041800350030030180c441030b80d440315041d01e00790401c1c004160f036000800f044410b000d8051034030084040a50a1b85090810700040c107248801010b460580200200081120754001c0030390780070390b030040c1c11651070785030201460308160f000000100c0b2034464a111409154032035801c160035240e000000c2e113a02807a10070152000d00c00742c40202c0790583c07070b1140c06c1c581610414110004240656022555041074280080c40c0c0605800e00300441d00100100800760320385151440860360b040d81c0c00034500400d00008030090144c141c003038150b01d103409030008208410b581e90030300500d00049504140100c1d00c080500326080030702149074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 8223532 1250 8222282 8222303
    0x10b0604031a0c040e1501030902090f0714070803070e12011109010905060c0703030e01110f0705010905010503090606061b0604030c020f060a0804061d0706050a02070f0e04020d02010509030a08040305010e0a 91
    0x148070905106c000e000003410f0402007107000c1243d00041003103000700ca1104090303500300d08002c049a40a01880289402001098a003a605880302040c0344030003003c500a100c1c0c05800c1d0040e90311106070700b810b02c0c1a414000c018080d4859007142d50740d4000707486240090104107002c5428545101102c81081c00c04006044c1c8515559003034600135284c103526410700c503501035140c2809406010340300c103030003248020b003d44604120014100420300e8024604008044c010494001d03000107a45400243c02c459a6850b80682d081002000c0d0f8811107501c001d01903401804200364100019580683c401c03151180100400014086107006569014001606003070101d000300b1250385c04946540102c005048041d801d6403085450021240d1010300000c0e00080c8041e000750f41801590064000c054451103043d05d058030144070400c0240020344034a550400c18021a030040003210080d540c098242c803907504035070500001d00c0c1c1040c0f100361159402c1003d01038401c000841d1241d4003550207054150b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 8224782 1250 8223532 8223541
    0xc070204090602090a0e04021002010b090a05090304050604031a010902181908010203010e0114040b09040311010f06090207061103010605220305010203043906050c010b0604031a0c040e 81
    0x503150100d800d0b41c00d03035800c0103050301584a44900754050104103510208900f032520600c5174441d41c0e000c5120840e49030401030f071003070b6403803160040d08201c0241e808901307601c90040582c110b100d0750340102c0d403150001800004102a01410121510301c0e4000705d06640e9803001a07030243c2c490203008a401c01e00d55541c50010746403141c640c1403000c54481c60002c850317403101241350032a4020381004030610070203001007044a1503c00410907036502a903013406028440c5010440580d0090401800e00c0031b10b4818807943c040c25400120145a550300500190b981d03014090004d5010002c01d41d0500d0038010480e41240460b030440717040710590380d516458401e02d145100004104043c0c01846080c1a08000021907400d00155009600560f20f205040e003a0b052140207500c20340001c0200b501000028070607581c10680c0340750807a0303d0350920683d200c5a1b01d51180c010300d80340614551043d0045400700c00d002010492140900d610286a0301c40c1c1c480c5441c05d03200d40154417441d140164007a0014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 8226032 1250 8224782 8224789
    0x306010315020a0207080a080301051c05070902070f0b0708100605040e06100207030b0903040e0a14010b0d020d09080c1219030c03090210081f050d0b090f070305030a0807080c0702 79
    0x51003035001600c15154480d0311b6401050070145205419118500007200602c2140313001c052710701c4d46080101c03e002c10740304995500b6440340e025115680310540c3c0818500140003035030003600300595001c1c0e924407842c54600006000150155114200c02c000200e020070302c14010301c01c480940c0d9191112511030f80d07541040180c3e44035018080c03411806203060010000d20910b080320f00601e4a02d02658603541442192500103200030701c8040a142040e490003100c0c1c0302e4020702c9041d20302c007007203e640d04c0d1071500c0d51001a1181c2d29080f288245070118000070300c13070174134041c1270450001d6058510a05110a060303840380070ba4104521484d02ca20404552039000e0384c070170011300450b8103011441c1905600002c00b918600c041010220714000c0170043e030100540303280300c2202202c000010b0f4403410300703002c2400c413000e150005104a154201045003600d040100c05c61081c481400c5130301c046d4580c58015100e4010301421130100b00700d40003081c01a80039800700703480750125200b00ca040c540c054081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 8227282 1250 8226032 8226037
    0x501080c0906090603070b040605090f1005070605060109080d02060108010b0103151512060e06011101060b160204020409060305030c0601050a0302180a0b0901120b0c04030b1f0b0d0903020c030601031502 89
    0x55041c032803040002100a00440030f40020006074a0300c94413120f1a41c14440201da120333442d10300c00d9041000169900b5004026070b4032640d0071040c0010707640d58000058450302d04035000740100f440340e82c07541540103074001030f0181030f5406140240f01030303544980190b00361607429038401d02d8408a54402d1040c410b581080c04034064240c0380101d0b80c4140c0e003038441e048941540184c005400c5502c100310382035070015800c0840048000080243d289090025030041c0201c8000400d00e0000d4920300c401d42da110740586000c0c03c0750ba0700800c480e958070718059070f40c2d50102a4014203409800000581d920313044505100322500600144e03851803030204940a1003000814001c111030341e6914983c10303522056a118041d003020640c5088074043c90800d4600a01d004003400340c4807101300010b02c001150b0740402c1350081d03044804004288141c0c461030000d070303400381c00c1192200307030102c2c2084400c40075401510619000e07401f030b240c8812a07001850340745d503424003000d8040032180304810f649181ca03500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 8228532 1250 8227282 8227291
    0x603040f081206010e01080c0f0703110d021f050103050607080403031404080306040608030f07020114040306050c040504060501030209030c0f010309020603010806070305090703031706010504090e01050405010501080c090609 98
    0x42030808408960328040907800003914011150900010882c5650304003203000c3d444042400c240c8041d21705104401004d02c41c40c800903240e03040215950382094003036090600024401400e6a00c1c0f1070541400a6a401508030600c481d09245081c02505291038030aa9040c0d039040070261001e540c450341c00350780b41d4201520480030140c1d90420803600143c82c1900a0040b44552107456881c1055000c210940e000c5400040d0140c10070001815103c9644085481480e828202918040320903032941100740690703031010f1724003410242001a0041c0210040065950440701000b890742c9483c01107007240281461039030158013230000c0a0403440c0501c40d030030b08008145000b042e039450a601080c1150000ea00140c1164023034000e105507243c1502a07240d00490030401000d00c1031441d10018a1400255286201c2e48800c00104550381d1082040b6009002d2a071401d011040001139100d00070481110260f865500c3d200001c1403401d07002c5418a818a4020490111a111501000544d480160 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 8229782 1250 8228532 8228543
    0x50702040c09080a03030f230103021908060f190902030d030e160303020a0507081f020309010204090c020c01021506010c020f04021603020708120304080a0f0c2418050303010302060304 81
    0x21000143e6140c10060356000c035209507004901d0008400341e000c1541c005040d00c2d20a0906010b02d89880740541d008141126011240c812024582c0000980b07601040c3d004103209000c0c2c0000c05c003403030f0242a03000d805898100fa42c020440240c82c034802c21500c00d108000e50582101d030448441c140700c0c0c0c0003452051078600c113403030343c8414101d00d480500002c3d6204401581040d1054001d001050012000802c2d01c0d1020700111100000314410b8084d0140c40502101c0d030110105e8a504025810703600500214407082205078098880a581d0f8002c90007042d0051080c03206110b011500300e240316014410684481d1500c07031f0740d5800c0080350030503d542640c0240c2e003070003003604d5000c1801c003840806000340c0207480c1407410400078078144410101c2d42e200c2c0c4c001c10000e00c000200a83c084842e03403105490901d030b18031842c05044503a043d5110014000015810080603000845c4151824148142e801001078040720740c010b0398800c017803500c054410782040c40100050702f1b04a000310b80c01407049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 8231032 1250 8229782 8229797
    0x602030f0a2115030308011d0105010c0c08070b04080d020d08011202010e030a0b090d02010e0606060702010e0a0b0301090b04050606070f0c17070603060e0907061116080609061303050702040c 84
    0x380400b03084444801e401c44031948103d008006040d0010326081c0500800b5040813050860428021086007042c441c0303504003c2240744d074800344420cd2080c040a000c518045e140421b50310300320546107400030b0003482914000c000c0d101c151540001080040355900b5191007846a20780314602c49d403851228000e81c1030040c809808a0389990500c007600750a0701c206240380c001d05068441074682200d0441c03101c2560314004460b000031340300241150380403000315041945d6228510040314140700c145411500201c8c50200071540292800165041c3d91003000c0812500003c038080009039001910401e80201c0d0400240d404a01d10b0300381c24104a01581c01941c602d548c60500e01090780c04918082d00641280c80c090041561601921000344182e48503003126007000040c071900e41c0045c0c842d00781400f00c2800030800c80d020a0180035201ca1104011700b550359036035070034251286021141c030b1056001e2000003400120501c41e082401c5505541c4440c10040e89030700780b20050074180503980c284100d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 8232282 1250 8231032 8231087
    0x6050d0f020d06060f08010e0c0304020d14010c081b0702060d02130b18010c020120010b04091406070504060f08060301020405060705010903090605030105060702010302180402030115090602030f0a 86
    0xe5000502030a8418280025079604d0321078010241060090200100010480100980c40e0b5a0806640215008420300d43c0e81e151413000038105015044024001980c0c805400322401d01948034001c1c0c0002a00c55640399a188240c200c0d030001480207600710381000703200c0350001d8148800a4100d005216000500c0d0151600450380384481d160321040c66030358001a1032094840b4440d4000d4955428244281c6043c01d43d80007801c800503072200d50801e1640010b20081c07046007500603220001000d002080920203904142240c5810010120014400c200206100d41d1240040380e0031a0324a6503101c00e81022104112441040509940c0d030540d007d000120301691402c000f081c5c42e901c50700002519000c21724001d0a00d12260380b1500034000c2c14001001251549030445d00c0300c036824600181da0b862940062440c1f850414110ba4110f4808000400c0821010400302e05800041e220050140e41c0e40c0403c1380e80e4810300107000c010050601182c0019402002c00305c0c500b034034044207180345950 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 8233532 1250 8232282 8232311
    0xc0f06020904090b070908030a05030105010e0109091a091b030f040507030b0a1a03010509070501030906060f08010603020112020a0c020f03030c060c04170a0506010302010503040305040305150105130905060106050d 94
    0x795168181c030390015803005c1c0b103d002e800036405401803042c07002660804c8001e95024256000500c600e505000b0000d010320075a80c031803246500a03203051181000200f059034180810903200101d540d000b104088082080d900b14211403a10000003142d0340c6246a54030501080d030007030098412a454882c08d280032000400942100d803081d19085400269911780c90f00020707500140124060007a403403e0140401188045031079130603100c0030700700031030080107514005005003400e0348401c0610020301e00118440c801034200d1000c8a000740d84c0c90b02c031710110000600032445a03059060200c0c2000b040340c0018100070070b050b106c00c0c000800792800e0181303441c002800c10100325018008040b001034107115090f01d8009416020300c840004007c0242e140e42c0d0b035076442c0c90600010b03050140100006080521503421180655807182c10b480044c240c80b203817540e40c96820b01515100d60700100f096071010b0018030980d02c2c150380110007802ca9919190b8240c0f6a58000d80501c0b012688941c40c2480302d030b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 8234782 1250 8233532 8233541
    0xd05070806190507080f150303130906080327010309020d0312050106020708030711030a080a03090209060409020d12021006060c0203060702030a02100507030b0a08060402040501080705010c0f06020904 88
    0x125240c058072482c503041c441281d034102c07440200d00c18a8074260900482c01ea0003190658030071001d0350091401c0d1074941100c1c4d9100d00c220001585403000094018100c80d078410145e0498141713202c1030001c1912a803ea40d141d024000401c5d01a1009034994a40301107c5840d82c409aa41818000b40d41c18031a004030351100c9042c40240c3c0840e107409414000000907115484c014800c52024220f150306242c101500c86c8501c210182000140490204041c0d40900400c13400e0366102820581c2c030307100c20074003030080c14180100340c2c032a4902000249484c1001d0180780a62503009009040d01085540c0311442d40c102032002c50b0852042ca0310444004a0707501c142405066252140140342c0001c1c0304140c4bc0c040020100c0c4110b400034000317821519000161500d2203146560301240710351f1011002c0703009103503940b8002c1c1d01051a140010300c40901142c05406940280e0301400580c0c4c98600c415900e8001c2c0c4120350015100b2024000132422415040404510888015161418084c006011384 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 8236032 1250 8234782 8234789
    0x20d0203060306010b0a0c0f05010b100909050c07030509060c0a080313021311090d08070501091203150305030a0309060204050a0b0c100c02060408090111120d0b040605030d05090d0507 81
    0x55400000c0c04110700d4204503050040140c04a100d02e0301e420075200500400c011007004005440003400b050820200703400c80f2001d0980600121a0a001c05100a003d50554402c448400d864640819000000c040c103c5440036059211240740807100001d1082c290320a00040c240d5001d51003049000891a100450244800b0041001920315500410800c005004807182c0c1461420740c0c0080500c1002c0292091020101d413803085440c031030305001d64284141e160080481d440c2110a40401c0701c20a4280c06081c2c155900b0010b500301800d05007101c4d286804090500d03132092003800c1090f40303c1d8001d65002031040a016003442d50350400b2400707c103c190000c4408641c00701c1d61404001040090603044005050107104403051180041e40f1540d01401c00303080c000d400910401242d00561b0f0061103000480200d5885240003540f00342c064001e00c030000d0400e400c00c85081128035040c040c41c015160000c0242151803c60b00040d58181c1c040282241c109286600a1340440c0092181e01d008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 8237282 1250 8236032 8236057
    0x1030302030c010c0c0b0a09080c010e010203041109060904060b0307120501020c060708010e04030305040206160c0303110703080d150b0d020301031106041203080613060f0513060608040807020d020402 88
    0x4403502d6400c03503801d643c9002100400c000c0400c01c0031001c96004011150032403100f4000241801160170402c04510985075031901710760074080d0850121005500a51207540119042700d058034210342004440001500d480e40c0c0695200049408a00c1503070103003010180007000c59055035542d402203041c500340800f0645040e54046400312000005009483d40101280780074480e0798144800c600c540310020b03101030300b0135030b9544c0060215101c0350100d17100b441142107804000319192900340b01c40340e00c0d400b0031800900c2a021040f1420710004180e010b60b940150303103a042c0254091540010120010041444180200c000410001313510080840902150002d0396941c1141028a0480d1810301401d002d040f003003104001c0c841c0c0d60300c05242d06a9040c50100400e4485000003164880d2001c0d50146003841c1140c00074005c1030540c9100f0482e0740c1901c082d50000c15412008089a549201c1d9902003005030000a00180e0000002d00065200810441d0b041440d5004941240c0280c80301801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 8238532 1250 8237282 8237287
    0x708040c050d200319050618061303140409050c130602120a0c0c05090f0a11070c03060f06090e0109020405060f09130305070c0e01030302011a01051c09050307080a080a06060f050a0e0301050103030203 88
    0x40003007232055058030f0301c0949004190900b0240c04030f806090388401c3c05020047c4c68a8440d07441d1001c44100d5006280d82c1000348080d0610490b0003180d54044440c05400c1c101c9942c0010780305002181c030074501248000000d00b803c50620741510080242202140c440d07034000300204245da50300d000740307028940c14442c055491410300d10380021a1034000c40a0702c5003500b442504000f032801800305c402d881c0e0003000410f0744e003001c00404010300302940202403001c0c103004415812910552090888034004c80d01840191950801d0000511800c6c41c543d80049142c0300007030307000d07800e80e9400006501c82e1900ca40f400c5150345401c1c2000b80f050f00140c1002d0340c000d00400501d0303424080c440c0349150741c02c10204500e10540010f015441789481c0c2035059030031414008540d00e915072100c1c03106500034084d030342e0721310961610516650003000703082c01081000001c00c0c0e5240041c860603080d92401d881d4130070720341c20040307080e01c01e0f4100340030b80410403500e8001662540c07400c1c00b805000314420740040d0b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 8239782 1250 8238532 8238541
    0x14031501030e0a0b090607020a05030f09010e04060602010f0c05040503060105040c050c010203041209150215060109030804030803060103060b0a02070509060406081504170a020309060c03040b030708040c050d2003190506 96
    0x1e00309003007e09130ba000c40d401180c01101107003000c8122200d21801e196225a616104401a62400448550340c2e0380580b41210005c1c0441c0c040d040b40d440520403410403c01560720400c02d90b4140503a00403540c0641c804d00047c4483c0c1401d40c0091802e41403070518904100340065006c0c260791003110225041c07030724001d80031081d07034001140b98090491024009405002c0340c5c0000d5481e58032005920300c143c440008907080f80d0107103061001030354002c0b01c0103554a480c1d081c64403d5500a8460900181c600080024030040b070030281c590320030b5658050804546050208000050302170400d641c05941c80344c001400700010040314054203c0511501c1592401d8200061010001000192130724403c00c20901000e901108a030b078074040890700d19071100b0315580340d03034a50b00a42d04412071140c030000034000c2a9801c0018144682c0c0318803884110a80c80d6011b020b101801020010080e600450320346040764101170b800e01144a000c1c0840b2401c0c62401000280d03480207100941d40e42c0c20210500 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 8241032 1250 8239782 8239801
    0x190f02010309080324060306030a030e0a0f03030201020414010203090a0306050601030f05040f020103111602011209120810080a0b0103021c020a090207110301050906060d0501021204030f0e0114031501030e0a0b 92
    0x85c0c6002e00c040301d10307034250b1422401083e11801000307801420090b064185000c6a5242c2e115a40503006106561251984a280c003034001d5200340944010f25003c28100c280e958800012241484e9024004560300303032450340c40101030200a84454145912100d18ac40682001d21503a4031481c000e0075442c0c00c0f242140005030032565131482a8040c94010481300781c002d0340c0140004541a828600480410b40e240c0d8807400501080100601d0600b2188112182d540c1c0650f0b0580640c0202d080c00c412140da4038400381d17035609822401001110b01500410140c6080042e80101040100f40510507800e10381c00510465420b401030507045501051440038008040008101010154003c100b01c2c1081003403155036801c010001481400920202d00401c44290142c0d2148090090829810f080500c0c014001040342210100002e44030074070740781c582d84a03115600d1019230011540d8a580c9650410b40c1c1c0d024200c50006040c1902d032a50f91011050422844503298003603161100182400c1010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 8242282 1250 8241032 8241091
    0x9040b0108090d050c0c090a060608010e01030308070e030c040509010501140402160605100e090d030507170402010509040b0306040804080f030406050307030203060a08060a0504110102190f020103090803 89
    0x2800d04200d041020890300c42c200092000b48000d0900304070341c5403100004d4052401c1c902140c141c2c4c2050400c1e040c800c004440703801c100192130558840b0350301f6030380300d40350078802410901c00a00010404d0002c9504240204a6007000d500050b044d80d8481c5290b0001c40d0544409544841013695240010010044014002c085082c41100c0c29440c00f11408007500340044d01e00d00290015030b86902003070a00028005420042000350310201c0140350103106e0b540c0f507003151495000800d05000008038914411401400201010308410610780c03119001100e098105004050308565121102d040c0303981e08000852080d885210295031307440c2800a0036082081041a0764402e40c800c0c030050100d6070700602948c0c1e200900b49801a1aa030b0781000007030802c40942d1084000c0c9c0202ca05014400c806500b02910850050b080c60281c20b81c0302004a0355005203680440c04d4040300070466001414410700c01022500500d0041140720300c545a40210343d205030380c60f00031400802e55044882412854 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 8243532 1250 8242282 8242301
    0x3040b011502010902061c06030f050109050c010f080f0604020408011104051503010807030b04051f020a02070f0605040501120e031603020d020304060e040b0112020a050405190501090e18010c050904 87
    0xa01044c2d2640e4045496401160040c00030003400d00010f902c038240d5540800d000b141c0000b4401c03059404c40c1006070081095030f07070542c1d083c000c00309a1802d0f54020b441e40c81140b6160b540350341240d61070410141010f000136200c82e40c481d0b020040094206030901070344040c1852030b43e88650300c038500010005811009010b00038106811f1004100d6071070081116801c0b43e41101c0c61039000d50311840d0103400c24501416500000610765003101502c5090b90162030014640e408440b134158a52010144a41d0709216030b10004804000038090b0b03510422100d460401b4504002c200d40032129417060641d088915001c070f44080e400d0300c41c41030590421000742c03613402c140051351803d42041c10041109a08080c02c1d400fa036121580892580d1060300148941c01c907a540c11921040340b002d00a040e40e0251051900c101c0d400c001809070804168586130403180161242400c0e98540f51014040010040110185803901826800122001e024440c1d10420303030780e035665441c1c14000c01c11044422055 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 8244782 1250 8243532 8243537
    0xe010806030609030910030207020a0e0105040b03070302030d0507060b031b010801170601090903050715060504060503010b0d0f020d14060f0702030a0905010e03030403020a030b0f0609090307030311070803040b0115 94
    0x43c408210404011030300040320949141c462610841400d6019205266009402011011000030480500500e060580344d003100d06214245861041655500300381c0400303540740c0c0000300c1c2200c25a001d40010b05029109400c041030900781e080c0061304108040196550316441110b180e6170641c0d0016a00d0702404800c40b07004c0d140c42203000d6240d503840050013107a101b40e98074130348041458020010f0b681441d52000d508202540142e00001c01350550f84a2180100d01b000f0700410145010f011b4408111340290810110f20056124000003805010050b80c000f186a401000460580a402c404c41600c1d08010907a81c02c0c890218040040700602c0b48085400078081c001d051170784010201c04454003481c0640b006540e00000030b0443c0308981c07000354003040c1e1000c000108000825110b100e01207030940503510fa52030b0800d02040c1c9808a444140039002044990006402130b4006982465403062003401d2030095611030200354400e50b01511481100001006840401e021400d42030300c252 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 8246032 1250 8244782 8244793
    0x80609010b0604080d0c080f03130311030f090609040212090a030909051501030c0e030304090e01050a0204210c1703090301050601090b0f090310110a021002040f0603020d09050d0e01080603 83
    0x1d0556245c0386000048010404680850024000100d06860310b4410017644640e81c1d00306042030f8044d01d4107100007203000c580c1102c00e102c0c889001105540c40c0e80a0154920700c1c4c08042c1040181c50344c80a20400d41c030075400c0c005c5859100e203010050384500c0340c00c0014204940709080290503050325034085041c4506100801405003440c07040c0961072035081c00e0215001c000184141ca03010149007009806200102c0d00059811560f04144210003001b03008010702c3d01d4041c076110580c860340c02104003002d99550020b82c402c400400d01c4024078000c41c44009080d4482c0c541507030040a503040100541c0c0041070710803562400384521b039003000307003400c04c02030751032078021190a00d000d402d003120f644070703c04a500c407074688042c4440138014551010030482c44034030f42c000c40700340d4200005520040c42200f450304464480742c422101541c20720701003c91110314000c000c81c069481011028203030794075410035800040b4100070400389a40c054464001c8000c501c400113002c4180148200d10a9000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 8247282 1250 8246032 8246039
    0x70b07020601090b0d120302030402040902300106062a060f0204051009060e060702030717070315020705030405040b03031b0c030d0302031302010c020a032907020a05060a1d0601080609010b0604 85
    0x10710443c8501e07581f8180540c03a0341d5180001002001030a601a4220300526080031800071340004440e021620300c141c0340385442c4000782c3e0a01721901401040042401c2800205e8500316922410710120f00d80e5481c41060a0140d44000c151451046450301440c0c0104040c01145068220380480d0392451401d44800703807404100400d01c070200c21209026080000ba03210540d2000c0c4000c0c009070603403403503803082d9212084119a4070420341c84240e0301e103110110004501c0302c2c20300840e21217a401c900150b0815080008102c000c10051400d5a458402000001080071400c200d2000784e41d00304000d849158510002d2604105811805400700745c410410406102c1410703108050a03902842c0043c03129000f480424680b540c1d175000908031540c2c50009118a0344440d480b4208400544000d00ca01e440e12902681c2c0d9500b0310b00028100d070848000038030301c03410305d40c00000a2864219523001c0d0b007201d0b098643c148042a04068281e030491420441030100900403400c1d18902a00c8291500d0b00c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 8248532 1250 8247282 8247293
    0x30c07061e1106070503090c120a03030501050312030403030c0e130c020d0c03050d0203060102010204050603040803090c010c120e03100f0902030c0d0812070315080d0212040b120c070b07020601090b0d 88
    0xc00802d03004c207000010000c1a1042d90400043c000010042c1020345074261001e1032664038024888100c1c0000d003070000200d5241030104061000c0e0f200880da003410745e02d480c1e80507000341c600281002c00304002c0c020742002035a9031020f44c010010800000084060382c01c50000d04080594008405212000d041b0310b000036805002c40b6150940b0940041c1c80351500340040380680310b42e0b441590f02840101c107102c00d0084940c0218041c604450403100301902d40c41c0190ba008410b00d102500783e802d1603000014107401100b0454607400010103561400b00100740c664200c41c4038005070075a9955030102ca2003142410026000c02d0007040f110381a09450075030300c60f41c0901c21505171054802080300841c0c2414000d80102d10504154040001c1d2140c0764910070b551b807003002c5801360051203210a2885800e08000c01c0b101500e80c040c203141c0ca0186d0100248103080005010fa440100e0b04000440101d50303003014036401000143e01070202d551500c2da07580b0651f60390686542c41150642441d400044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 8249782 1250 8248532 8248543
    0xe16050906071e0203010204062001050601050a08070201060b03010f0e01090b030c010c030903300804020108060d020d02040507020609070b0f040e0a020903060a24030b010501080603030c07061e11 86
    0x3e901c0b1240c0604004000044414810f9404009415600110380444d031a03030416210344007030300d209040401c9451003070105030903101c040e42e0181c0440c0c1d08200e41d9240d548a413408a50000c0d1a0002051191f43c0b543d1441c9582d10980c004200d10724000e40c180288050804018010a1040d1085c04210302507800680c64510030028141030101d00c00707a0108160140c4205c20003560460f42405504055801e1070107001c0340f00c500070b0120742044a404088901405503a0300807a01a074409115540e54420310400600b4480103a9015090f074820800590b1b51303006030752260440d58060200350525000c0d192410b941c64000d4014554180502c182ca14801c00590741160003000204140b62100c0b04001e00034401c407050070360540550000c01910400581004150350218402890581c4440021b000860b0740f0340801000c120401e0010800c0d90302c1a50590313000800102a24604100c0030700c3d09241c200c080e4850004074040b0300b00c0d04144040d00da04001c007400c0c1410440b58215a2041517a240c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 8251032 1250 8249782 8249797
    0xf0c18050402070c0e04060209041404030c08030903120c0703080907030503030c130b13060206010909020a0b03090c030703030c0c0501031e0903050c01090302070504060b09030a081c060e16050906 86
    0x10742e80424040c082c054010070701d00040c00f103203404103040c1c1001c0c10110060741c00009418080c0741032020b0b48149504050030740d48603036007564414080b07603410381e40e005003035101034907401d041e102c00e010b5030b444080101d04082c000c1c00c040c00307400d684205c00d150150010000403d0000150000d0a041004c01c1002c4200c80c0d201c0702030f050441d41c0b10044880440010000e80041501d40b9000c1040071603401514003550517105c070b580850301142e0b0380728242415141c056900a40180e41c100b0100240700d4004083e5401000c61800c1d14180d02943c4086441c1480940c0141c0c0042c07410b0f0200310502c0b291483c41e002410003031800344285854030308503c007003105080040e201c036960342c1c4400d014180311740151840061420020f0000300c17007a090003562000c89000d20f0303208a15104000408414400481d5030042019019000d06000c644481c0740319049440450100b03892131030404100043c5200b0407016000310040580d40b414048460042c61118081f8481404010808005213940d03102c00d65440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 8252282 1250 8251032 8251039
    0x4060e0403180b04080307110a12110d08210105010c030f0e030a02060d0e0105090304150818010203040b0a0e060402031b010309080409020301030318060507020f0609030d02010f0c1805 81
    0xe00300c000c0d5580c41075040d940d016200f40600800c001c107125001100405ca9507000760218919450180e0400c01407400601c0341d466108a00c07040c0350001400462226226440108004002c0e0216200c00305660300201c003041c01035140d4810003d0002e40c0d441c01502422080c0b904007600c400350360380034120303880084007078050003102c12110405a070300300891020b00b940a400e07103807240003161541c0b010700044242a6019400c0800003108018000180c43c125540d80b004004c81070300014054403000000380c4083c4d030319007440315158641d4000b40010750286225641012132490315080c0901101c2048007010300ca0381100c02440003595000030502040d6946108280c4100085001a40280680c20004201c030001080004420280c1e901843c1203a0003901c17032078200481000c1c0090341d03941e81d01914002ca001800030350054207207181c68085c02140984003524250007480003074078115032002d103800180c0d16032400c40d0b00d6207014007480283c0c601038107040c0064412070710081184902401032900 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 8253532 1250 8252282 8252297
    0x1903020f1209010b0409060f110705070b1303061b030b06070c180902030105040b011406030702060c070204062301030b04060303050d0c030b09090d0f05030105030c1918060801050604060e0403 84
    0x400460a6102507810744c0002c100700000310a5207000720103808921500c8204a2030884141c1400c1c101400700d80860754000058007006060a42d0a9640c3c0c110007070b1f580720b01800240200000e6424810f00e40c2c401140b85c0140c00040c404c0340d0080032389000205960003034209001070310000340801d40c414103803102e004c100034420422480540003040a01303006941503082000b84403d01c4203080c41941a240086000011603041c3c8003808041c0c80281c81400040e44214009004848204041d00c107840c4010000b040242d580c00d4000d2040100c1010000000040400782c05a0741c1c144c41015030030706040d50203103d46444c0d03407405407550260b07000302c0741010748482d1071041d210311035800b243c251903004010559500303200940d15914002c00f8500b10205001500c2c1641e0b2601070070541e412500000c0003800034404007001d203c1d900d080e0605550400502c00381c041401c180c510151881e0a804201c00105145820700c6282955000b03800340d80510319201080c80898180515194000d405003001103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 8254782 1250 8253532 8253541
    0x906030206120714130503010b090903071101090302040f02190905030a03030504021906050304060b0a030f0813090c0c0c0f030b01060c0503040503010c0c05010b0f03030d0c110303010801021903020f12 88
    0x2c0b081c1066134075144100c04000b520240d8005611300c110245c40d0300358000c208102048c0180715000d41c0c1510702c01c0a580c0b00744106400a81d0b50045800d01c20010300d003280210755070b980424151800e24101d004c825801049a030660a0200d0b207150354452a454602c4e0304500d1301011036122400890302030304040e15040054195180d40c070481ca030303104880e0700080010383d54807001802070700166811500f0a081004079144d0f4509164540e0680750490001845e44070940c0e030b10491644925500f105050b0159400a10095203200c1d01040c1059611408030f020150301e000200c50130070380c101c0c5100f20800081400841c00141d00d203415070340306040143c0c41e4503d40c140b40b440c6000c6d950010b07034150f0034078061500e0598803035400c0740002d200344024002420104104000e0841c2c00030307901c0c1c15034000d0004a298868a030440c502158050400e454001e120310331841c20b5034001d81040d24640c1d0002250320005400a1200301044a20302d02141801d4910b16202028860050032048102520b004038 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 8256032 1250 8254782 8254787
    0x80a0f020405060c03070c0b04030b0601050a030e0604061b0201020310060509060f0a0201060e06040b0d02010e010302041214120f0403020d0809040c0801031101050a0e210609100609060302061207 86
    0x20307800b400c4003c10b50390712810000802e5036245d1080404651040ca0340e4000a074000c0c4810544d8183c3c0e0b40110181442d43d0f40000460380d582014035000201034031000025041d150511000340541d015410115103a400b02016404400c01f800d480000c6a10401c00c0156040451141300143e442c2c520b4a02d544580f07100000b20103000b0919000900d0310000f0b02c03820395039015031100302100c0151901d03103101d85d183c408000440d084080e030140c00000b10900d200040d0300c108240d01000005040041c2080e03220000c1c0740c1c190622440888480044030140c40c3d0031032081100030b05500d0ba052030300b481c2c000d2003884c03c003c600070b07480000d0045100c0740c140010040b0010681d0034400c40540200030046010340c004040348020300c802d0b180e001d0389002070546da52258040b9125030140d034030786050803600304050080e5108902d0950307254131041d1050246003041441481e0007105050b009002c40000d5001300001c955681d8480c0d080245000401c000586901c400e03508591804d61102c6010b41e51b08100f0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 8257282 1250 8256032 8256037
    0x904020117010803090114040303320711030f06100b090d14160e010b040e090a05070602030d060e0f0a0e0708030c07030b0a020f04150201090203010c0c110f01080a0f02 74
    0x449001e007038500004101e0a400002801900100740c0c0d0312019803000318020340e142e04c102c4c00060b0010315800c0c00102c40503800d04980e0540a0205203800b008a00c112407520140c0052508403145610181400440d190810030504158924000341102c0d080218100011950703170322031041e941101180000301992400020441e05420403400400f05c10600302c0c3c4c5031070307600c500c06480100075140310103d584a12800642e040e41d8503d203105203400d00740500d0840c42c210050055045100d00b998990014405100700002000c443e0001c6484200c50105181512801c1d000004d110402e10200003980c0c0c1094500c540106c000440001d004421405490a211407034002c00b1041c4000500007910000004d000f4003264001e40a01c11140c661000f07040603841001c820303501260b41880700f4031860108902c0c850302c201c0c2030b000002e031b14502540820709441d8010265030109c2d1081e46404284810124480303403002d801c40b88152070800c4000060700d40c1202a141a01481d07507800d2242058085904 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 8258532 1250 8257282 8257307
    0xd030302070219050102060901140604020d090609080304020a0803070302030a0f02030706050103051011040b07030522030606090501080c010f1803050601030f030f0903030c0803060a0e0a0902030715020303010509040201 96
    0x52031948070700c2d030b90400c240c00f000e204050040c800c40f00069641071062213201d8a1201e030034803201044d2620401c01010303402001c100641207a81e80c2d41324000540c18819510712500c9250401d840303207802e004200c441c03601540061040d4004110040000350301108864641183e403d095403101105c0404038075500800344010400340c641400401402000203480d0407040d00c02c803007400090204c160414140c0114840c0310301c1c81e00c0c00d000d5100081d0252001c0c0000319a16010034980401e40e10003248205265803041d924566240c0d024040c2c0341880c00f400707014103140b100402043c404030000a219200c1c1113007076400c029014a030b00b03001c034005828130f038021078000003110465616401c3c4283c000701081c030201c01148404006c40d280c0d60081e00c010742200d0b050380302d402c4c0c0c408503915042c100741d00040903503500c9140540c0111300040304030104c9020342d8103200c00060407003852040c9460b00b1400e402c0120ba20003403040801d2003680c0041100d06441054424500686035880160b03128501847e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 8259782 1250 8258532 8258539
    0xd080904020a0c1401090c05090c1207030c030b0105030108150a06050d08120f012103050412030e0406060302030c09060c07050301140405010c0c030903081308030a020c01170f060d0303020702 84
    0x140b454050b9a0002003200caa80c05416221640c400c4611000d00b01c0e114561300400240004404000d18980880b22583c4040580c0301030b0315200f4522021880a5011140940466030380d1000004895161083e0445060b003800c1c107030711303550400da009565425481d50380300c8058581000220008145d8102d0030041c08040c252141100c020301c1c01c8490384e080f0800c2c1d000e0818546001800421091903464100d92107001029004015917012220075651383c0025410320608003c001128a0b03c101440c4c1c00754002c0e641d0740c80c40445e0104110070b441095000030101030051062184a22824089170144a003c850f901e65175080080c00b181820320a0f0310082d07041d40713001001024512491400c41c1b203107105030000c0048143c0c1c064250303503d4103d030401070001005407505200003911900100071405840303003240d42d4166203500403840e507444198844c005030024101c55031907582188540e4051003640c102290380d460400c2500f1080180100002c0c46107050721035400500d4020b0741140c8040741c014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 8261032 1250 8259782 8259787
    0x50712022109030913090201091205010e070308040e1806070e010c080424030905060402100c0f0305130501050910030203130b250206070c030305060303040512160b0a0801050d08090402 81
    0x1c0000c2903d075045104410702951010f06030100b0004030f4817491191550513140c00d0040c3d4203100c0e00f094041900841100c040d0f42e00c4928035405503082109200862107000e14569403810000f4001da900c8014201920911a05900040505010441680c015102d1034684620b07000c3e240101c5850388050006802003a0010740404d0b503265401c6482c40070001c42c100c2c907a0200f01003a04500303c844000d40a491900701102040041c5031501c04034042a115181501030203c05846601c103044000d41c04a01003000003481c21807103002046204000c00013420a80d06002001d40490f441804001c103810030154000009410b0681c1288100c00307064224007803019074030f01003401811000c2804a00303680d540801890050311440011a5449009107a0310312000094550307082d4058500503000f650705010511010440d5260760f8079030a00700fa007100050000202c6010303105c03404120354001c501c0151b82084022540d91b003110819044400503600c1c80e141d400d56084c0810240101c0d8030880d80207000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 8262282 1250 8261032 8261041
    0x1021011070201020d1106010306021602040c080403020105060a030c12080408070b070507050d111e120102030a1803080f06040b060705010b0406090605030706110f010504051c030507120221 83
    0x800c001d080c40341d200703030211080c04209600c1500d045600701c1c581c016541c4200c00500005800e90050441ca41800c06002d011075055800030b4241e40f070102e520400255450100300070706609001e0700e03400140542d0070005281c2940c40c1c80c503c100e01d600031034000040360640c00f02081024001c0f90300410300c02080e28001601d070301400310154000b1105880511440c0400325007458990707201c0c0c0c40d850344141c425500314141c4090044002c4503041ca8140940343c05603001c915281c803886ca040020100c0700045e924a8174007000c408a0304100c040f0812241d0045038180002d42105400d600120105950556a690800000d015002622855401000c0170404404204054021045d8000119014030115403540c0c00300f0205c072101c4c07240307a5056210315810089240107003c9411080d40c41c0054540d00700e425404076083d1881950100e030240d009106200060080341c48030b2800000c42d00d0140002d00308100002c040401c3e9024030108954002001c1952076002d03110201010420300800200380350 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 8263532 1250 8262282 8262311
    0x30501090b04060509060f041b0302060d0906051506071407080319110f120702010e060c0c0a060806010206011406070c0e071407020306010e060607080409020301060f030216020609010210 82
    0x2034500b15410350a003c0070178089500450901c0c130418009004c4580c40d0b40701e8450b0300c03a40c0211400c0c0e0031400b10b90440070000d40c4800000b002d04203040328020410b081149000c0088450041840d99450000907000040b55910800c0701d01483e0005140c0b00c401a88050540c00e00b4102d500441c0300340f00008090141d0040108422610307007d076150602d0500c0c40556441d2a9900b50a1451254100203c80c0f045280a60042c052040c010325281001d6103d01c008101d00307a0100030812441e074400a15442c0e0344c600344070b0401c05070110307140c42181424148000703566020103002c1e074a501503031055480c00c1c680707a200980f541c2c80d4000040c10b21007943d452560f107090038241c440c0000100142850f00d081144c69040303410060b070240007070000d42c1c41d241404013201405030001d503225508114010200f06480c01810152500603401a502d503d001c00180041824008482c149030050081104401e005404940c11940546200d69500b240c100102d08115003000d40134841c1d80707800c4000d2002c04 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 8264782 1250 8263532 8263553
    0x10612030e0904050c2709010212070c170a0302070206030709080d050408061503011e020a030b0a140d0318030605150402040f120c05040501120c0f060203070602030c0403050109 78
    0x18001d859102034550208140000c032041180d000d040b43d03111200010203410100503012243c2c2e900c0036507140000441880402d180d2050342c512005039000302d000381085400740301035504024241040c01a01c0f20950b61030759440d4540c0d4004503411804605082c1242c007a80456a40640c01400d050323403840c01d00c0003e0443e46e154098014240b044036500c59a160007907085400740c41e03101d002040142c0e20300d2b45c0440500c158000003a00355413103940154011502d500c03010650401120090703291513a030030008040b1803191041c0c0c0d10800202c20108650107071080c102c005000181c0b0708081030340c0c003400c041d50302209020080c49000050180001070088950186000707481c039641005608089000300001ea0203a40511006010010003c024165800707401081281c0300305200050b40303984000003021210243c0c40038030050041e1071180208280044408068040c0110000d0621700380000290f0313a005c0e842c8000c284a0380040420400481c4038251001035521000a000910b40c926001d400369 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 8266032 1250 8264782 8264819
    0x5010603091401060501021b0f06160605090307020d030309060b0a0b0405011e090e1305030403060204060e040608070909020f0a03030e010f03020306010807210c091401020708030301050609120106 86
    0xe41e07410b18035640c0603060180e02c0489038140c2c001c0c91600384660501084001c1c0c0401036500031516485509183c0b2078501410a08204d0000602c7d68040740c201a0b00b605c20042a9100680003080040300503540d0024140c00d02e5018a0001842250f503d4403038001c004c14040c1f15480301030840f000428115a10082055a1080c1c0e941c47c80c0da000c89580c4d50720310380071b1550400411007025040c0140c0814003405648039806c100300c088840000d480d01802d50f4455002034074030710380000d03090054580144050000c00825601045124038009110f6100c0344540103000303034503445880400540d03954100c21910154010081409950740f49809007410740e1007240c96012424441403085807a00900c2174074451001030311015172560b51700c0c00440303d8407840c15010420740600617488031300071f00500c10700c41d007000d06403200902e9606103110040ca0f19001c518240c1154080c00061000f4a00031090302e04559060b941d05488064581c00144084400038111745258a40040000c65116581c000d0285 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 8267282 1250 8266032 8266043
    0x501032102060c09040b0616080307090b03060a030311010605041103010e010506040b18040e0a03110f0a080904020315030d050a090b03130b06010306051c060606030c0c060b0a05040501060309 84
    0xc8904261090b40c0318001210302048030441400000d41c5410300c2d40001541d9000209002d2a10000d00f020030b50317501c07200806a13a0340d40040b0411041d20703040b0f210310002e030420884250131450060009508090700d8080201046480800c1c150084001d4100001814004005008011424810818540091244291700c030240ca00014150074483c0c01c940c140e402c080b00c168940250340080c00b50010100804580140d513444090030701130030a003d800300701031181c0c2d01c911010003840400d030325102032000c40d0802c40c0c005402d03070310000f00c29004a421105064034007680ba580c5550044554480050f841034160182901004040d0303841001441e00c010716403a00d43c0c0054803000c40302400c0c0002c0340c03001c2d0f81ea44ca51038040b01041c0005900d0343d02801c1490302140560710b6001180c2d035280b0f90b81c08000b40034901204442003248a0240d407001c4d0601b49070402600c00b0f640302c001c01c00884885c0103001181d5440c104041600c50749080005000044e1051045581d148801801855402003d450 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 8268532 1250 8267282 8267333
    0xf070b0106050901021e070b04031103060708090a0b0603070308040b03012301050f03040c090e011e021206010f0306150e040f05040201051c060906030506091006060219050f01050103 80
    0x10918040c00c00daa01d103c4042c0c0c001d240510a008134a0300080e103000500890307100300f040010340d040401d002030010b18826001680529000e506043c54010060300050a1152321000c2104c1100c000030b03220009908412070507021780f1960b0200c0d04150103a04007902c08000050040b5130ba582400082d41200c6ca040040c0f904400d070044445c0309010a010540c3c0000e004020800004424602450b00603000d101d064080325954201c3c00d00715801030208143c2a515000070540000010400000c0364014100962410307020180301c1c20190300042031581400480004001c00900ca42d11000c01785c055606400d0528040500103406014a005580d1103a07052841d0001c1c000030900400d07008a81c1038541905004503075103030800d80e01908807807080d91541c0781c100040840040c0076141c0214082c6000c0c1c1002e0801c0ca2030142842c941c04006160641813120400280351b00091840710a0703032482e441d40b40000c4624001d8103106182d00402410741c00c010001c001e220009601081c4500030b92440b54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 8269782 1250 8268532 8268539
    0x607030b1c0302070e0a020c1609060b04140103020703050d0204080601050f030d02070506030603010e0601090b01080f01060503010306020d06030f0b010510030c02030403020d020d02030a0c080105060d0803060d060b060f070b01 99
    0x40103101c49220080040c0c201c0c5000300000c610ba28022a00300c072003260094148403008030340619090500c04560310f0807a09100802010034640b1961003c1e0000d14040d901d4103050074440d41150021200c00c0e07040650001e44003007414400c01c180c1d07500440a81c01555200c0c1d1f0340111603500c1600b0b0003002d00c1000407a04000140c94005190890185141c000d07024003881c00b01088900e400080040c2c2e0103540f2000074544c0c8010030312115010380b03244030f000078484c60b82c54001011094001c0c071510100310100700501c03043c0d805c101a01e0441e42c2c0004050b90ba503281c01040800303801e003a0301c002d02c440a480d0f00201044039100441c0d051b0381050fa4024104001407a0490569160549940c05030300100001c6c0b0160034890010100180040c0c100406c041c8203501003840d0001024058030700c0808035006000002d428058075810020031955614040c049450350f101c0d03840301400c006d11540c0e659102d681003183c290000009074100600303440e154101c283e01040d05074401c00d42162200c90410010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 8271032 1250 8269782 8269819
    0xd090501030b13090507080a030810050a0305060c030c0d0603080318030405150c010204030c0605031005011d120703020915010305010504182607030504030201030b03010c120b060c0607030b 83
    0x180042d0400414a1183e00350041e40f1100602101000f41c995004546000c41c581804001e0840207034429500c00e03050f440d10340f0954088104582009104001c003090400208800040c0d16030030940425490742d803074682400c2c82001d4070036100030100c41400c01d0000018011000042c41c411601c0703603440802040e180f04040e0300e901c518000c41d0781c401c64544201001c1a0750f007025204945589000610301912a00d5100b41c01c0695230000c000900b0003c01c002e180701c0360000e814014102070030310b5031421034069600184400603024150140d03880380c00c840380d010410003400008540140050500303040c82c201d4841d12020308070417079021030700f080c00009580c1064450318005c0f4800210a26190750740e5503500c070a1112500154010300c032403001c031030341e6004044002d1540c14480d07186c1c15600c5140d0b100240503500800300084c401d902d0b103000c20581542040203a0302140c0207010000d0303082d5050780018028010124444454440e86081010154056200805102084035048010060001030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 8272282 1250 8271032 8271041
    0x50606040e030307030b0f0603090c100201090305250c08011a03060c030105060304050a12050325020d03020a03060b070605010503120712080703140403080a0506010f1706010318050d09050103 84
    0x407107101d60302c03c000248045100b54042010440e008040c08002c500035000201260419a0345810075000042c8140d014508a00020580c5546000038850016a500c01030424003d01c60400041d8106140c040d0841014000c0d442ea0541e00456001540391150100c90007460505044d0302042c0090a191015140010b2201c0c442c2c0325085c070646c0b4623030920041c409560000f4104560611406110303000007484044401c03c02c58030b50b45c032562646040f00404070b075a254810303500f80d04491705481070006a07000c200710340c030340000d801c01680d10014070314128020100756004840c00d100c007084680c1048900d03040241202c42c00c030b044030583c40d0281d2080b8068814280010207400d44400007054460140c4103296000000c0c1c00c0000c0c0007151580101c8150100b1a021400034100a04001c2c041b00705101d21608000c0070302c1c051030741000ca0003018000b003140032040318101201000040d440c0e88203403c0004018102401381881c031880d46881a0b440c8913100401e03010452642c000303d02075203e4407a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 8273388 1106 8272282 8272301
    0x30c010b1c030e12030d111b0304052202190c0203060106020c0d0209041110090303030e01050402010804060e0a020303160605090a050a0308100317030405060604 71
    0x801000445038807211068104014101c8080703640100f04071040d080559450f40d00c0203ca20000d071440c0100c14684081d5801d1100c100d80401e020300140c284010280146012646c174500b0f419124015405410b4005c90311564501203058844070300c1c0c100740c44a032001841c0900030540001c0720724258040708081200c003200502181400c00c501d90040c40355201900c4020151000280c9680c01200d000c0d02c207111032400f040a0005c034801004151000070040c800c00424003001811030b90b154801940401e00e49600e0020f20301044c01000c0c89294141d55203503141e0741e9662440024806c0000c81c003640d118250b043c10058904000500900403900381c1403024501a26200054550091103844140c0144000c0780003e140002c0d003506455040c1001d22640d41c940c1e190101006155001405010810178640c51210760303100290700882c050410b6401a55070042440259000f205 = true := by decide +kernel

theorem cover : BRFrame.Cov 8093532 8273388 := by
  have h0 := BRFrame.cov_init 8093532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8093532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8093532 ≤ n) (h2 : n < 8273388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
