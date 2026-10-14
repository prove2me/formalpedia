-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1884
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:01:39.869631+00:00
-- url     : https://prove2.me/submissions/f0721dc8-461c-4fa6-bf76-7df871e5e0d5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 338669064 ≤ n < 338848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 338670314 1250 338669064 338669083
    0x14040204060e040e10180b0f0912030603030702090103050c010207080705031002090f0a031b050402070b0c070c0e01090e06010b040303050f071a0a29010e010f05070204061d09 77
    0x441c40c60007400700c80e4a01039015010081d125400d1340c12060315010354000300c0d06c15100c8144400310070090007041c4215031044580c08400d00701c00702c1250606040940d550194280b403400c813034900100142c050380b0140305803040107602030440c81443d40c403403a0503a2180c00d198141030040c0b10b8030710f0029040000250070012a800500509541c0c03266400000280d8042d06050f904040069107418a5403111000c260003180603064108080103403c05000219040d42d011903c180e00501604020550413215150840b0140ba0042da6408a40c605080303a011640c0c0007146c0340707001100006207001c00d900411100c1e030209054035010ba0300e0b0b04992446000c0e9000140c0050b03030501603800090b400c1c0008090031401440e0f402c000c4001082c00310380c0c1c0c1d1011540707201c044c1e0f19804803080300c4400e030840c1941d01c1201c020000314034004000081c44d061045188038100001241b1041d044d50140c000c403024031703030080d0090111940b02e80000100d1521008034000c01150540012110500030800300e26 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 338671564 1250 338670314 338670317
    0x5040b01080103031e0201150e06010215091f0e10050a060f1206020703210912021b22090803010f0b0705120a0909140105150403020310020a05221404020406 69
    0x40c680e620014441c4445c90b550203410540d9614059a400310f1801d80100006080351341c0c9140e003504e0020002410102e1200707081020301281e00900503003200103d0904040521801c2c0d6501c85d80c40d00e0030000150910200c0055030740500b0340c80c40c4500b043c540150303103c2c020010042c400c0580e507801d0500100e80c02d10606c6205c0081c0c094040000e0f48a800820310903000385030003c2c02c82511308200849003440c201c80480c0c20b40d252032020402103138141188805a60380050440800c5020f0002c0c1c10007071401880f071142c03101e90407080c0b8008405508a241e111504400c0103140f00514140d82103038802c1c000c902c680301000b0303030006010100004490302554003401400800341043c1c03070b000058208440d03c00c14002c01c1c0601103400e00581c824013106244101d9a46c2441d4034102c24000360310161500810314101c108018805030701d0000c1c40450340183e100c00140e880400071403c031858003621030b603c0031000e48030700300305460046c3e100c0301c0c000c0c1c039600c0404481c04c070f81c100200700c01c0307100b984103010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 338672814 1250 338671564 338671577
    0x3070c1b031a0c19020a05011a060912030c070b1209061605161a041401050105062232030a0308280203071d030a08070f0303090206120105040b0108010303 68
    0x41140440ca0086402043c051041404e01001d40d03903000c1c100034002455001a40f180d410780f01804800d001c0c11640c0700c0b144500102480108002c11360320f10030307841d881d400f6030307040c2a0081c1044010822292042881010b0711072254a52a0b042016070014010014914040c00460200b090115000d80070f00003980122141d5500c0082c1903070241c02c43e101c0100721241081d90700c3c2c0419810510706076505040f101c8156940b9151a00e0711103400e040d0603100c2c40d80c0c586030050005403240001c494000b140000e9a103030061a40f54148018240e45e041105082101c0f01418000300d04070040d041110701065490401014150a25a0382c1040d0003000e00002c03071410106041c1c1450b107003a03462002000e2000b130070840301500585d06980c03095400d0350001b081250ba0307601003c5d01780190030040c001240540b07039046950b200c845103401507507009002c0a00f4410b079081018000c0c0d00c40c4156580c058034060f11886000801d0861031006d100d503900403401d10408da0050342c803c1c0d0040e81680c2d45511000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 338674064 1250 338672814 338672843
    0x209010921030c14030d09060f0506030c1908120703110307020a090203060f1e01140f0304062c01090210210e0f190c061d13060b03070c1b03 62
    0x22120300c0b0300030700f040c0c42c5090030040c44445a0000c1c001805240c8409001040c051340a240110489405113041c2ca000b40c50001446610755002c42d405007441c8007200c41100d80513000000d01c0160806601c2210070f4171a500d46080c80741d2219000c1c0203c580252a02060f0b08003070b1400c291a0321503214000d5100146ca41c0a11401000760301450b0081000392842203180f11030000305449a070814503210f814a1820004100c03076a00c0342030151024034a910581c10400311895507216404007170802001c468a42c01c00c0e0564905404075042c4a01403d2860b104100e054840c0724000c01c95184168010075010020950190213504402c90740784c03041c0c81c5410001d00d00b1a108000301072039402c1403500d001c1d000784001010f101f008159071013080040300311100d25403460701003242c4615901c0801401803400300c400c8101c108824040a4100c16901d038040e4000400c40700c2d00410058101c101c010300080240b1086070385c440f08010a261058004c0d071100b840e000440301c4801000e00c8018087c21242400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 338675314 1250 338674064 338674067
    0x60702120910050702040f0509010b01090305120c01150e10060305070c110a0504111213050714060706060618060201020414061b01060602030c01180b1302010c06020d020901092103 79
    0x315649080034a04a13080c500142e00003025030701341000140007562a042400351410003031280f402c840800f406c04005451a42d5a880d480d440c0c10302914146010106401a08a400f90001e811510600044a421603200d146440200c0425a01c0208100c51640080b83c41c90203803040a000c1c89258a036042100c40503a01e000c03100704901802a045110340b4030014894490b40070f02100701c8a00c2c504a03031600e03d0380d200800d22040003426580a41c1104e407419002c03480c04514001514905001c03020a40f0094011901d0380c032404000030105071600e4070000381998080546001c810303801141c02c003a203507a420102c0c280d0040380680c0c01810180804180c175843d110004154031000c03803401c5100580e00113106400c503000c5903c8074000d44c10002e04c0d00403028080c40342d800707201e440b020700b1131001c00c5580711101c2800c1c0040000c50394140d410320b404103680c001c0000c074900b654884800e65942e51029185400380d00440c001c103000c90b9200c1e00200d41242d8a413480722091680c001c0b0340c081003815480 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 338676564 1250 338675314 338675329
    0x3051506090d170c0703140303100b070602070b070c0203061302150a0908030a030b1804050a02040203060d0c0f1503060b0f07020607060204080a140102090102071505040914090607021209 82
    0xc0b609890786070780f545035104003032000e0100022800e001e40702c500e20354105501902010003040c0910b8000300f04000e08074051003110019202072181460b01e034245450400300900c01d5690141c031450243c000c000209600007103000e00c213482070b0300f61030340c0b40c0710107000d80d00b102902c0750029806000076501043d6041548080c20341141c07c0c0c5030140b20255503464990555102480c0780002a4803850380366841d00b003c00020040340c03406d42e401405482c150321959100c484540c8000e1155400001140c1c1c41d9035180703108424185c2146840041076035541110105800a2007980e111100070100403510f94000c0c07050504546416015038600345401c14080c40342c2e4031408080382c0c00102480072501080340d5101410142030558020429500a1b040608510114494112003a8010002d0040c141d82c08180355080303c43d050515810220014400c0d00e40d03008036003105032040d1401100407052210030710094000c440b024180c4825440d80748c4100d031900500241c108845004000901003402c0203103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 338677814 1250 338676564 338676589
    0xa08060f180c0901030b07030e0d0905010e15210901020705100c140f030105040f060b09150c120d0b06090a0b0a051c0b18070c03030e0304030206190305150609 70
    0x1020390b034021503003200180b0f00b01c00a8100356140c5100c001049840b50309441440c82030350a8a0040810440042c0e0080141509000380b40c1001074600841c0c1d0319486082007000d609089040b80c82c3c0b84d0003c40c023030b42540c44c140c00b0f0f440d404007408000b080c100b5a040c400c5403151601300c005042562090030070701c80905030381042d8070108001100c800f56031059010251028030000d0300940d6895250608000641d280c201c04003130550719040082291310021340845651000a640c480840c280500c001c1c40c0c540030f0403082c0c2c90176000b40700000c0c64440d025002411000c4d040300080010141032401c1c450a03000300e1480542001ca610400d0181c20b90550203014014046d182c100c1c5000c00f1100008848540800341311601501da0950780b41c00d15101c40081d5000300c0c10042d07400540740800c2c1c0200280700b04600603007855540e0182040b030420a10803280070f50380107031020fa5078291220440d03a100f1102d003824400a881d00380480c0081d1050110414400340003880d15003029403030f004004040d407401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 338679064 1250 338677814 338677861
    0x12170f04030602090d05151503061e07140a020a3503090a1a0115080c190c02040e060711150a02030705070f030f090605090303030c0f0409050c030103020a08060f 71
    0x5c0c0720000501c1c00c0003d1450b19090810b000514144030311340100d0760030101820340c401e801c6402000111318a10072810703102e441101400f922070311107580548050940500d03001b10b42c2c02c00a01c0940c0746130006036980e66580702300c031603a641074880f8203481403442c07004040302c03c500c0c809a41903041a142101544e0010000400d498030b041c2c0c19a41c0d902000e902c075500018940500c80100420403030742409200000407403c024000d894400c0c1507030214400c000c80407032100a40070450349010b02c24513220400a81c050f0080144104400d207042c0d4594040750420000380010b0381212a0100c00306410400f1031030b02240f04c00300c1e10388944610182d04010141c80810106001010200b0561560744405a0003900e030845451002c40e0000c1281c0300c1c540040013407080400000c2015100003044950000c2c0c0c101003180c454500000301222171040781c4c0f18011440c00e1a0501401c6a444402541260310031501d403104203a5a5084603120a003c03943c100d40075228500056106145808482e21007480 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 338680314 1250 338679064 338679079
    0x30210050f07061a0108130611090303030108010b120a0b040809130c122318010905030d0e100615030b0a0f060305040b0601020708030304240612170f0403060209 71
    0x480c66512841d0b00301c2c04055404580711194403044150010495200401c28600b43c10700f4a01400031015444d1180c9000b00703402d6480e52039034041c820080c280c40c285500101175a0752541d442003180d010b44028614540308803003a0a46802001d00029403010f20b6a0103107407032400e0f036140d0321080840c1d0000180c4540041300d000c0c10009034080b51080e004940741c180c40c0c2d898140303d032040c248100c0b003c0f011100041030000c01d01d03c4003003c242d00c0b030991001e000ca18a91440031003d1466014101142e0000c100b0301c800700340c50f0850301d0b041c0c02c0041010a100201c03404408840b580d081a01c842d40b05480c2c46103803600350b1035040da100b03411080d0301c0766001c0d10140c11147c0e25601c6400c0604c07260300080c00a6070354414002041001072040d50421001d1004015036806d084403036440c0c4c0f01c054001071030040340724142c60054107080c99803009502225410405184c0e076107100c14901c1c2405104580c0d10010442108081401600740c5202c8080c1d01d07401c5051030304642d01c44e4020b50000004540c001034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 338681564 1250 338680314 338680327
    0xf0807032a0503070f05180409080f04080607080606120601180e0115030b18070c05010b04110a02060711060c0f071203140a05060310090f0209040b0114030c060403021005 75
    0xc0d0318000111551140d8545a80340340c4403500030205210b02c030345c44d401c0210410030480710100d4203810702440d61044074002000361651600480320b11918440c815501d5004c10006900c0002090f038501c01d0300340341c54038103141c1c1d1680e0402c11103100e5000403220740d054010116946500c1500e00729624400c29050040441e103507103510041c490241c0c01200074440b021030004009601d8000c0c00520034040d6100104403031f02c54040154140010206030402a8200221052002c00d410140640c2e001034002c01104006010f140100e90089400c01d000d48a082c000c681c58500c074003c03c40115040344040c100350703226020b11145640c400d1610b0502448203229550128440049180004029440000c1d4501d00846c003580c0c195401083c41c009945810100a010f4402140c02c1d1070a43e400749001074500400d181c0300460200c011c8029411000ca07004020400424040c2c0b24140c82c0400c0e00800038414400c100b580d52042e0080305030700003409020410060a2420030b4210f1094541050360400700e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 338682814 1250 338681564 338681621
    0x317090d2111040602010f020c06040204150b03010f141215060a0b0c01020d110301060909051009090b060909010606020712050c1c0b01050d1113180302010504060c0f080703 76
    0x1c0d01c90010b403422410005041103030302d409100b00c0e59203006600c001e40c14410000034280d01c80d500100302038021615410040b46900180c4160800382c90f808200d140c80703503122038400c50a00310500a00e05482503903c4200b0039498280790149900c4500d00050400707403903910301085401e501800c025080741c025000442c40b009038601400394950310394001a16400226001c0064900e0032088080140d4200010f01150740d0088042081c1d0f40c1c0e4075008100b54644c400c5644080c0391b00e0740f100043c540341520207420031140c500018043c20302221849456100c404015003240e4184c855403015070312082042000556899000b007840b4082c00540e000e91050300702182c08104204000103001c0f01e220001420040c103220f1160240c01d06903141912030f81541c2d00c85022040003907200e80300f00c9029580820850082d0044c41c044946250301c4070031000f086c5800382c0600400d560448195003860384640c0d003103200d00648c00d241c4450f03940301989070702c8515068000b085143c1d00920781d254241840000344d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 338684064 1250 338682814 338682821
    0x50105090a0f020f0c0604051912083c101220120a0c0f05102304121511070201050304050109020a1706180c010513050406120317090d21 60
    0x2044085d0103000c0340d191078a0800d04049402c441d0002107001e0240700b0001c1010303001c0d501020781007402e0520082c1c8801480c1480c009004c1511950b205084c071300d800808034820745017074001b1401034078000141c50301500c2c0007044030680a14005600d01c1c45034400444c04500c140d40d404040e0407041807a01c4140d901068441d44c1b4140200d0072607000d645030360300300700100e000c0b503004002403084509080e041c10b002031554000076961100300141042480b01066002013204030300d030300c0c2a00c0d0070b41e01d40d500c000300303010200c11f0344043d90b06400e1030302a0141074009004010002e921500c130245000318941c0156000d8001410a40d003565940040f18010f03224080c603c0c024104102441000c400d8500110349410001014001d9017074156640c4040c00034002038088034a0f0003424115144c1c0107641005002c2281c591200c0d610500340710000400c080318400e581e48040c000d50782e84c8604201301d48881800c2c401039a03d501c0d1030780000502442180305145d42c20441c102c11800034107808650340c0503000d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 338685314 1250 338684064 338684077
    0x6021c050714030c1207050d050307170f06010e030a080906030c0c010f1b180501051c0516030b15030a090807060f05010e060a0506030a050a020c0727050105090a0f020f 74
    0xd6400010010f200002c1040065400d034020f568071850015550f4820b03855a03000d188e040e0a2240200206892a0260480d0740c00207210306958034003407403c4400d0034018482550940c0c0850111041e585c2176080116521f10541d4000d030003107140518000034400140e00041268420f4041804125070007c02801103617180f14001d040440c0d4a6040214020301224044004080c0318042081c07030010a01181d0200880c1e8007400c0080d201c450205440348500c00300031001c042c440c60503080000d29110b0150180306421903a0b41002590801e50600803060400032008403800c4060001540b01d04040c1c005402e454490640319090043c0d40d5074a00c2a83c494400541c031881d00c660052024030b10103001c8990284080381c104070b030305140902041a511007d06040030309074031440021003042c150740499a0303501c010b03400c0325142c0e5900c100c1c0a4902c0700c03039001c80e80c0c00c1700b90005c4658401b030503008803410784200500d01e04083e03c134040c4c0d02c40201083c0c4038610b119502400712011030b00042010300b61 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 338686564 1250 338685314 338685353
    0x816050d080a0b01080f0406020415090e01090b130b1903080714060613051005060f0c01150317090109090f020c0709020c0303011e0905010b190906021c0507 69
    0xd412654410280150300c0c001d040d01c100c14907004100e240c513170b40070031000d80008421001080684481c1000c402900c01c2e504130344e492040000b00c034151668081091406c440800070f200c0040e07622031040d501a1904030f0003441d80103001d010003080702c41680d40045d038400700c010b1509007008514003943d4568481c1c2da100380c8002d540400c189090040e03c0344000034428240700070307040504d4032800255045e00141c4034055490b075200c00003038580d090039546002503c1e00801090305d610004123020026407000111070190350802004030b04140c20580c440066a0707001c0b80c0400341c0e000f481c12413440d54001403c07a40c1001044d42c0000f07203c0c0311a10424080307103041400540c1c2c1e0138508407160324105150340b01101c0b651040000c1d400e64907010069905444922410418404044040702030104154001c03000180c5804000940303800d44070010189205c21b82200c0c182c00d9159041581e95138203511425000da00301039440120340301c9032003d284000180f82005410910b403a01c13000209491040f4140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 338687814 1250 338686564 338686573
    0x15020712080f011202030106050a03061b02010510030204020a0201021911160f0306020705240f070503090d0f0210090803010306111e0a1e2325081605 66
    0x5204103145811003031580c034180406181002e21030404000014450000822602d1182104540c0c00b900080028200145540c0015072a4200800103200d1030180001d24184104668032050042c040c203407062000200c42600b10b4515020700001e50f0049042c2d0b01155420480b0342c0001d00481d080c100403820550700d04030142011449a4905a0b5400c1818016401408100402d60107104101c041c2c9912060140c3c66280b03a203092454803a640001d022001482131641c01d9031400d10034413074410440740f07403070303c815132030710300c0241e4a510054401f0302240d000104110f440358022120f400f1000070510441c1c44428121340450100c1d080341c0c80446440900000410501407280a08510300a5100c020303803800c0d8015010f188103c070b895500150b50340e00030500c00821401807540216000d45042d2111022041c01c43c0200807500346010081c45503106d40c400c03002c141c5e0860596913014524903004e91404a48035500c105500403003021240d612040141c01008000b12441188181c803550040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 338689064 1250 338687814 338687827
    0xd08040212150702300a110307060510060503010305191721010905010815070c02120a1419170712090e060102150a5013140a1502 57
    0x381450000025040c4049a242c3c80c0e400450340d09215045001c5c000722095580c000d91101903c248402c5c0000700c84a010206c5d0740400c1c0906138218520034035a1250f207440542e02c07031005845902080c00003401590000044610441821401e83d02d440d009103083d007202040e0210009071644007403088030600e40c4d103001e98440080000c02a03400362910070424400e07076040420103a905c4440040101030000b1240200741c8041c02082224801900500801207060b2821645a941c001c1e10310225404010380c040e0328518032000c0307204500340f0314a544202003551103856103c00241c044108059a2400708000d00020360380d20891a441c0e0b10503141d10ba4050b03e0425804070354280284228150b40043e03112242c40b4043c0c1e43c03070700e40c0408103400009038444031011544060010144594506901b40c10207110104003224101810b03549401310340324900211241e0740510f0043c0c85e40c0e595a1032030161180014940340c981202e80404100300d901014080d1948815044007044980035039030f002460 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 338690314 1250 338689064 338689067
    0x2040e1e01060e090604080a05090904081810200c04020a0206010501142d130905060a29070314031e010b0a0207050f06090603040503091c03020d080402121507 70
    0x40b80000d0400b20f004502502d40740c0301150300d030140240700074165a000598485024003500c1520000c0002130138105952400d03280c5a00c0b80e82c8003440c68410445035a8541e004c0c1d140591582c04008426502c428500c54511030f80840c4c00940170381042e90f4004d0030f51004440d00c461000d8250002254000d18031075150400150000061100080120508020740380e840304200c0c0400c007042082d1150506d2001a001c554440340c090307414185641001c82900162501440c0c00c494000c20088889030451952604d034003c0030f030010300f00c40305006100031071648141c05000241030194020305043c140310f84c80c09003801d0076a000300d94900c07521a55900c0c1284150048031018090000b030400130b0306d443c10604010b981c4019601c40c080c410980303000401d01a441d4035040d05ca080002401c450380382e041528005840c1e070030800c03640703000f8107080e5042e145180c1000301394151507415402030158040303c05000c80e00100014010303a0807007644a001c0300700900401c580c10016400320308842150821010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 338691564 1250 338690314 338690321
    0x90503180f150a0e010c1506180c020a08030705130e01030501110307020a0b06031606031e020405060a030515150702041401060212070213020a080417030f040f02040e1e01 75
    0x30294003440740e280b0141c1142603502c1c1214600031031424240c01e0042150012221400c0307003100208286260152070326014039980214064500c0c10300c2c020000c404481500c0b04885840d0301c0140181c2c4501d60440124546400035a041401440c0680c900601e0400d11092255554804803c0701c8105c0e004200b8400b00b0300c00d07009444c5050310002d00d142000c5200a694030440000904055408404110156000c010001d113003030300c2d4800d14051507070b41e413405001800e0b50740440192484c0c0c0c5002d42d07110031891085400f82c8000038150340c2800c800c600201c000308001092100c3c19400e091124200d541e8481d00d03540b1060387c1e03040342c13650380c0c0040c4180015905e0415950f1100e40d0080014440c481c0c0128500d00303142000956140c9079885800040d216594400c25014428400640001c41c9030340030003c6807203507001d090803c0183d0070414600f00d141c8000c96a6460790003026020030006a081d4030b62080d4103000038000f08101303070507941d41428410100f201030704070f2046000c0c24a50900a01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 338692814 1250 338691564 338691589
    0x2c030a051507050a05120603010f0c0203070b010e010305031914070c03031805100302160209091e06090607080603010e100222030206030406020c0703170403060e01020c1f09050318 79
    0x103410790820304c0340307000070708103000741d0343d488001c0380c04400002c0d2641c400358440000c00c00350400c18840b0341c1c0800000394481c0e01445042c1c03030440955002243d0740200d90304042c101c0703909c40011480e11540000c1c02000c1410180c0d4402002401c0036098185910360000d030020b14060b01001f06000d15524020f080b5609514100d0844000c02c041080141d445c06c0f000103030010740d401d02580c0e03003400e030100c144943c105c108000d42c49241d000900c080f03c4400030300001440e9a90354146140d80c25000d41568a500445482105500110020340518810b02e02c45130881c0010700049007100700e008205003400c15525005400710f0340424407400101c80d402e44c1c40e2421481292240000f030564000c00c82c01c0c4030051002c0c10440c7c0001d46540743c624100112401550007000406281c041540a503055610500c01039550740d0130007000645210040c400c4401c4090058010201c201030110307401102200128001c0c0301a0340c036010103010410a1000300110100320201c00741503810761041141d0441241c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 338694064 1250 338692814 338692817
    0x111222080604030906081506130e09060c090d020f090405011e0e060c071a0f0106030f020405010807120608031210270e0a02040e01020d05070f2c030a051507 69
    0x2070140804a07401025400584d421480c1c040307025900c84040b4048181c2480f40c0c0c3e604180d000603841d0b0344c044070910302d100f66683c12006040340d80301c140385140c1e105001e8514100d02e0004100c280980e1030100f440d90907040c40a4585c0318081c9101c2c0006900180881d81030f41d03180d458404940300c01c0f0001040308101142030004210108240740f40381e9640500501c8220781080010700700c024445404881c05040c0c80c1aa41c0d0700c40ca203400103140c548050700303202e4400800d06100ba9420084a6030007a03c0c203440f01a51484101d60711085c0c21160b03c0100e040d03c0c4982596401e001c00c00310020b01c0140114044204903200704d050140480b1503528241e8030040c0c1020044080728490960003000304205c1d0b010a9001c200c10b80d4002915080000c43c0c0e4009500620f00003917400328041c1034020f4640c0c00c40c5d042040180c1d07039584c0305c04d81da030f116007146c1c14001508405040f1000148005079900b143d0407107000380c2005042c1c04c086031800440c0c072030035178095003c0f01005c00d810203a030407141e5100307045 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 338695314 1250 338694064 338694073
    0x21c020d020d0810080a03090f0614030f04030e0a0620030a051b010e16180507050406180807060c120306050a030204020d1b0801050f01110a0311122208 67
    0x119500252200d941c01015403c000b42c1c2c001103a080f011118400014042c4e00003030ba0340700c00491030007030130032415403003540f04a074a425030000d0700034041c1c41c00050407080c507121079107160b5800d8038034403680000802c100e05004180b10304248503100e154a00000c0c048586561721580c0241c6000f000c103550380700c80748206510400c800c1500340d6125040c0c40744422062010516032203000c0503030380900500c02d00a4028030552401034803250840d00a0011a02c1030303541e21f9800410406404117441f011034a2801281d410441005800e110700d07102c00707880c2007070411000016100e83c04503041000701da0140b4001144400d058080c04200034024144211034101007290034500301c041149040140b002034451980482c000304c0e00d518541019402080c00b212114044402c40005440180c00f0b000d124041d24903a101e0484c15401549508241007580000300500030382c6580c11140d020707004483d01c5950290030301980e5030b201c1e081c01600c284c0b0080c3e00c42008040b074024266001c2411a409410307554403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 338696564 1250 338695314 338695333
    0xf08091509030d11120c010f0522031b020d060207110a0311060f0706050a15090c050f070f020d140d081312020102090303040f0906050405040c150201060312021c02 72
    0x1000100c0c0d0742402c1c654104000d00400100080f0b01741240300000b1410a8000a040c02c2004819802042c200070189020041525180d681510b0650303a00c440707191080702d015255000c070b4051000443c02d0b135000c0100f9400f030309299020441d480c5008000b07c0f68245c0204099081001070400000c81c00802d840b4055510b1664444920610313584101c0c0e03000f007070b001450640d8203c0c2041250303810394000300701784500d00f0840d020074020080280a8515241d03007001c00f0550032203502034030b400c0541c00d941d10303400c0c01a0301d5800c242c10750003180120782c0c507481d0700486030050302c5104401d0040b900a41010391244c1041c10100e007071800c031b0b494680401c4004010403000d85021501110a0f580098013a00c140d0203598041e070091140d141421391510010a0014241c252003095100f99007540e1021b001c1d0a98510074041a0381090300d00a14288234000140304406213081980301d00c0856100104016580e510f03151800d44448036440010b0700812083c01044211403882204a140d500c0200307943c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 338697814 1250 338696564 338696569
    0x4050315010e0622020901020c040c0206040c05060a0f03051003060e060a051b0406050309150c0901030f15050616020a0b090f030715031d060907080d0201090c03030c0206070f08091509 81
    0x44c043c4001d40d215503400f00f000000c0303074800c00c080003a41d0310140040220050444001e5500c601c01c4900301c400c41411040400d4500700b48007034507424190350711460f1000313040301c505401424006000c0d101d1652480d80c00008110305010b00e540c2c1c0c02e40c520240895040106c104c0c070035a40000e022034400c0c7c0281601a41085030b0384100c07400c503541464201d032240c0310b010b400d80c2004680d4091101041240051014900c8004001c150094090300c04010b00802905401c0c25a03c0e1031090080c0c42c60610010007060405900514550042900f4072003100c405500082c1e40c5c3c6880d4001130054440498200000d0416208501f80014120000d00100745482c0100c25401108006c1100700354039000354881101423401d03a08014444031059400b2880c0c14400c1554070341c0e0070703c2641031a2040e000707107948850061080d034a070144c00210000b222030450328159000300040c0c0049800c00001c01c041e4021622070491194843c0c4036030201940c804021042001c1e595100c50300c81e04440c4200803180c07156 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 338699064 1250 338697814 338697859
    0x4030605180a0f030509120709050a3b0a05061003060c0e0901210b040f051606080f0709261c0c0f060e0d050d050f060d110604050315010e06 62
    0x51340362524036074450410012034845101c00814903501d10441401103451082c94111600ca11f05080c42009001103200a444005051078580d105991080800d004515071608c030310480130340b0300e004035180184141d03140b81c07419104803200d1036591802039050040089500561200721000d01d40090801d000000107000c540c018410f14600c44c0300540d00c40401d61400010644030b58000c802c4101928003814407003c080b0700c03424215880e028080c1e0300342c6c205086001882c182c6e0721076a00c14403141e42e010f414540008019002200b03202e06c0f4100060349140703424541c0b10050f0300c1400690440220340d6042c0c0ba00751311034404041128080001540141d009031541c802c00d81014400380326041780d0174290014603200108005074015110000841c50300003004002c0c03202c0d046c0d000c110030360766035413050103221040c1d40c541c4d0b01201e180c03400070100740240b92000d5002e0b40204442c0c5400e6944000901e011b822009421044001c44010040841c10000c6198130400907106c135541e01d420010700c8942c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 338700314 1250 338699064 338699093
    0x6051305070e09070318030e09100807032a1404061403190611210705030403270512070807120c0506030a06030206040e0a200313021504030605180a 65
    0x50240c08000f810180c170035040700d40050314980c840040034215040c02006100d601c5a064000c1440c0c00108a00040905501045541e89006000000c1c11948c50031078811111000704656214080d04c1c03078081c240040c0700001004000441c64124004078280020368150340c2c01440c29440c500218420b0f40c8010800c54003290340c101100d90070160780c0c1b0b0102c0c002e01c010310442516890200f0700b01101040f1103049800345002c0c00d5a85459600e0400032101c43c4812140100040c560529102c203031040b200016040c445074a010034409600c03480810703441c120824546070103601145c0d04010814041c00240043c00b00c0000c54081221183c85024007a03840703100301c03401680d0000c0000c140e541715600c2800510b50040c88265117a07560003003080009420354410305010f2402d038007080250240070300382050800e9004414103554500551400101380510240d030499440c448180200c179403d0003c00240d88103140c002203504000990306605d480c40d40d100d010036440109100003040200303110408 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 338701564 1250 338700314 338700319
    0x30403030e0a021018090f050601110a050a0f0503070609060209011b0218100906090212010e130b0702150406090b0f07020601140f10090501020c06090604050405070c08070606051305070e 82
    0x480c1541c0250f400d0017003609a00c69800c01d4074042d05080002481d80100340580001d0307039864210658400810f440f0300207441c0c0109181d00201244000880400c0340031030903401601602e041030031035240c03201074458120046448545c009588201d5607000220350100f6403003102c0c00b42a085055010030700719002c031084040140314120015250f5075515031158040c010440b0103015181d41c030b0291002a400040c100004064003800210320701c9425804c2d0752103440c9140012580318030707588520407043c0001c0c00c0034045004020401c0401d40d40b01e021a03000700d104860000700d007c5103041080c1049006816544140441024890314940c00122070341543e82180080c040d0039905000210082c401c500e0315600070414028894205402500e040200d81080e000e6400000c1042d0402c07456128030062654410010b1005010034185640701c9130740300a09081031020315180751074440464110702e204131242d0761140024011414050810400600b01410070300c49420314403030143c01410307050580c0d030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 338702814 1250 338701564 338701577
    0x307020d02040b120a03140f0318031e03011d010302060d0f1b02010e0d02061902030907051c050c0402090901060f02150106090807051509100e0405010b030403030e0a0210 75
    0x38150760b241d40c0880c00b50103004007904415900b0601040c2c0710880a0700590210303c030400000c9140c3c10402c22a0410007100240c281f55543d0400d0551410455210102c4544420f0101c0c01050304c180c0501c00754480c003c810b5030f49940c94140d8100182101d180151895010b0b40010001a11b42c1015659080320094021500b440c041c03035a440180038a03041d02d00030503022101000b04130380645c094860751a034902501d50000340c105080e81e0b1400d042d20b511920401c4c4c4036041c0110f00203907000d55013000031001610b06c2c4e40c1d6142d0010340000c9010801403500e4075506d00000401c80c0410445905100c20360f825030904100000003520018140325141c28840a090b1500b1040e00c2804040b910031080a03115076196101d200c01802526240100030707840c0714008001c110b51034a021205100451074010901c1d0000c01402e00c04042c0c0343c80c40d4501400940c08080455079034601405010f800245e941d291a440c20b410020b0582c0c40108000c3c0d103642012104d0030150301e400e07a100c24048018104074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 338704064 1250 338702814 338702839
    0xb0c101802090414120412120806130207030306090203340507020f061c1b020604081b0a050d03090308070503061e150d0e120a0906141204050a020a090608030702 71
    0x16041485d0000012500100004d0100b0790039111a480510203010303c04101400710641c80c1074611b400280c1e040c0c0e03031004c5c60088441c42c1c041c850b00140402c3c0d01c01d00e4046001c0390b0302c4d03404200340c0e007064030f401403083d511401c42c0b0030300c0b05500300c42c04142d141c002c500da52813001e0a401501c2c43c440e034980a8000e13202c06990f55801d0325020120303510310070981100d4a0407021401305c41d0040a400243d13000f80852030941502451000400c40e009641103040c2a189c40c0da11140144004041c26600034603000c2c4013030850100f2002d0190890706c207043c0c1c40110368541c140c60001e003c0c0f000204600c0901400f441400441e0715001803541c50b50359101281c0c0c0c28100000002104100c610032700041915000890032003210881d04102c0340814580100c0351042585903900f1032a01910f02884000713051b000d801c110048c840c044418a0b80e46000030240341803c00c101c2450303840011902601c0942c0040030030421410304009010003004404820000315040a04080d100d100703ca8010788201e03041c080d00f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 338705314 1250 338704064 338704103
    0x1507020d1416021c0b09060108210a020c03060c0d050705040311040b1504080106170c1008041e051501090c0c020108040206120108150a05010515130b0c1018020904 72
    0x80c00746104103013191020718001da1804001000f42115108680c0c010310000041000002070300402c007441070781e400400007901540c40402c5807c181c8003807007140f00b00c14101400391400c1c8102e5000f0b482c000f075010341d10042c00c0740c0d88040d09d20240013102001340030881007010800350b024100c0364280c1120301244100c02d00c0e00241103a00025509d03000c1140000e40001c0303800d0305600400840b000e10301c9565090f010b00b840e040d00c2d100400040f0360810301001054207124458a2099402403050024a10500103611462032800400340b04079956401009110f910b02110044c41d40141081d02b018040225031110080440040b441c00071b051000c0b40303001c281150350311402d56064041d0030160380c889680d50350041b565840c051400380c02100b030320780216402032500c0c014203042e150040d005100c654054009000f243d80090264903140780c0358040452103000ca00010b002048200f4020718030100e040e01d401c021222208000340c1d5201328650701a00584507500400d91040e000258880b00441c000c0c032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 338706564 1250 338705314 338705329
    0x1c17091e0a0308010e07080631141305120f04090c050a261803070f060b0307080f0601090207081605010903030605030c03060a0c030207051507020d141602 68
    0x1204140140c40c1146681080c10000d0505610741c040d984040340b90342d840c400c1080000094039808009003c803000a803c908181d445101e94201e5004900400d40003c00221003601084035010401a181d400c008103a035580f03100303540c1001d140c5540c4c0051814680c2c030a665000182e280320740341040811420000210502030350018a40c000d010700c60450810b4000b0500c1d40140c0d002c1011412a4412800c5081543c45080100d207421001140d03d80380c80d1680c00a80107512110f841900c4200501400030b582c42c80350b5550385105800105060072101c0070141818020b4200c0116a404107800c411920f00010310a8111500c0510040e82d03101c0c9401d000500c0d214200400f403084107042c9078601080015408403079502e000e581d04100c1182c40d00700f00754664002200d41a4154466070104c2c031043c94642c0040e0f00780c0d01c14100103180000755070703449080140390401c16101c8807a103801c12005640501c080350a01c2400e00d8461000c1c0c2545003441c0d014000c112400500610100e00802191144071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 338707814 1250 338706564 338706583
    0xd06180f06050106091a0a0e0402040b0c01151401090302120a020315060f0a030f0b150307030614070806031b01090306020f0c0d050918040204090605181c1709 70
    0x4403503000e000c41030800c0e1010700401c0c070071200000d502480000b000c3e602c0608503c414000c0021903407500500341e000f2510300807041101035025500f00800501441403100922110501400104042202d42034800b01822036600c105246406142d440e0460ba030b2090085040e242d04036240035060000d2000d0710b10306014100300075014850019861807149500348030318070803d01201d1040c907081c024828403124200600c03004007a02c0d8030b40c04940c0001e45159500b9480a5541c00341d2a00d0103000d0700092400c0c1c0740d0317030040c0c0e603c95403042d403102c0c0f0803500d020090340320041b0b0030150342506041011a030780d110110004580f40940480104540e881084c0ca0f800441c3c000c50295143c02400343d1140c407507448800321301024450080304030740c1a4050b000350380c00300500819040d1144c0e82d04070340b080e6100001344100ea000384d03a040c103030000603921f00c0740ca400f6100200210b0207600624000c185441007030b00e9034a8002843c1c0c1a52a5100d900504028960101851003607440d1551411545420b0211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 338709064 1250 338707814 338707823
    0x12100f270804031e0507080a030801150e03030f040e0f16050c0f031902060f0405060105010c1707081308010b0603040201270e070f090f1202010207090623010206060d0618 75
    0x162988072580c056001020540360050046d1000070b656040101e9440700328003170080205481d0700041040b8485003001c00e04003591303405c2c5010110302c0000040c0c2580e00010608400d018017141c1444070080704001141c0c402154042c00c982400e01039000d100c020b400e260710300200000041c04101d0081c007486042c8000400100b2a44c40b040f202c1c031031748400c1d602462100018456400000d003a6000c6c1038506002c1da0300f000180c0083c2c2d081000464241c0c045640640d4400c440b00c3c41c00d460b0507c90001403c5081c09500b046444100d001215101c001203030348100d229070f040c080e104225a88140881e034201e54242040503000d47d1005807000c4e9070703a0841e08000c0c04440c0b00e800068500c0b155003d0b070b11a241c90b81d40c00c2c062101720344007954200401e009400441c640e6100c24420300c123154048400c518014011079034065a2001c6103404d039003c07074005003103c0c8201c0346804804402e528042e10014070900141c501445c0850105a440c1032085024100c5500d640036079040b080908071416905800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 338710314 1250 338709064 338709083
    0x4030615120c090e0109020a05100513030813050a03080a0e010c02030313090506060a080402060904022a0d030903020a0201080a020408010f02030f070809030d0509010b12100f27080403 81
    0x905010b04000100d11604509508026040c01300301018072802c43c1c202e82c01091a01c4036400c00052105000714008a401800010070802280d0701030003034031400442c410034895a4561016400354071a2403141e11aa006610001e02403000a000c4000e9500606082c6098180d0704054030040310060300181c1c1c0a505400002210242081035403903d10540c0c0c48888103000740e0f214030080c82200d124840c200e000080d05680800c00515101c802000b0312000200090f040c038050011101c0b82003c0c0b407800b400180000000d030909080103000d044007506507030034100321056550318040c1d00d03680000c50080c100320380d410000e141034a0b6a815240949032072402003040310071309201e0800a40c000d41c0c4025201c5030b400e0029002c02d01c1030040702e00c580319010103103003005408007400c0e01a06001d4412103c654031403802602d01d485103048203660301140f10080030201100406001100c4811142880490820320313801c410117402d8040c0c0f9a680c00d01d0030750580c500c0c400d09051350300380100d41005111088 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 338711564 1250 338710314 338710349
    0xe07120c080405010510120204020f0f03010806012405040e090106031205071110050a0804050a0f0819080106081302011101050403111b090c0322050303191104030615 73
    0x40c4001c0c0d65201e40d104000030002511070b48504403412440317108110102110010080c018100b0b034001d40303008140e8140180c00c2c80500c08800019030026007059155601c01001088080b5442481e8615000d1101140d07a01c1a081c0301c0c014118444d80c081c420400041c04003081601c0d209511613001160060116541b13020304000003000c2d548001d00558085103c8142003400d880c00f25880107044195458161420900c00800d444078403000704180d415002c0c98000502180d03180144810052003541d00f640d80d84080d10340740707211080e41001c280030402500010300015410805040e042640006103911402c8544012175019030202801484c40d401d00c014001010f40029a49155000c00c40540303050303400c101e203401c42e80c40004070003e5105100a02144003256924011a0400c4aa04a0200c108070b6030320180006d9024500c201c030964400030030052501d110052020042c030756400e090100b079402c400c40503400d006034003010380301950f52040d9058166413a984d080052404050390b80c207004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 338712814 1250 338711564 338711567
    0x501020a12060513180507060c02010f1706010e1212030103060b0d0c05131107030c03020d020c090105040c0509030d0509030c151e1b010f060803070308010e07120c 72
    0x104201181804180501d4107071414001d01d0107880b0945001502441d4030144030749110001d080c5491084c641000032580c2c5c2400f01d42c1c1400380b080501596240c00b4500085840014001c2c2c075884022410031178071800714014042860070164101000346002d162030444000011a200c0200b060240d05100e0059812151840038010318101c0c1e0182c2e904101980344a02130101420300014010480081d03002c0600080c038000d48810403008490f100080c90004040001145034006403040e80403030703440c85812040650411100c0194826032001e0603003100d010010800110741802000d00c1a1340b100b0f44070036210b100b481610241c0c4402401c07611310140011015066501c02c043c910300034001c1454211180c02c0100da40ea0040140035002d501c0c0c0111000c42c203c888103442900f10598200308640e05504866242044500c100200000b407902c5568090208842c02c0c4c4d8000c403c190024049c04000c240c0003031840c2d0440e100095105c0080c0e445d58070441d07945c1098403451035982e252204005155 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 338714064 1250 338712814 338712817
    0x102070f14131e14010803120109051b070615090b030304260a0f03020d02031204120c020301150e0a06060219050f030f0307080a060305030d090804090e030903070626060d05060103050102 82
    0x1002100301813026601e9041ca66101d125500b091103051492000400c0000450307400943d020446156202c120b0f20098070740c0c1030590100000b620340ca92a604410a008480324444000702200d143c204110350306000421780b20302540c4500e051043c0c100901c61410810003090201d500c40302c0003900c41e0240146802003a6051203641540144282100c00440e00c2c0000115004207452241400c00d035510b964414004000d0000781c0c1c0c1c20081c04801900060710309014510b1110442e04640c90720500b0028414010b9034002c1408081c0344c10540100f02964001c514884a000082c0316041060002d0612515107002074054240521000445010b00c88a0002a40c02132400b62b88003007142d241c90310300400362080380c000a00907800030490704101207a01d40c40368228511130b0742080d05240d95224124119100750100e104590000034080d101840c1c144a8030b0701418039408d01281e82624840d6900c1c080c0404000005030f09654008180e180d07580e136002d01680307540001221171540e101d18000e8041e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 338715314 1250 338714064 338714081
    0x501031a030d091a0c1b060c061014030c06030103020103050c120103030c111002060115030e1b0a06080708041506080a050f010612030c12050c0a110102070f14131e 72
    0x441c2d0701551070780100c0c4c001c404580707030040e0160040800200400000e02c4a5035540041c40e031202081100300920b00b000e12005104035640b00040032040d00d07003400d0011540503181a039200381c2100b0315141060745d400f400d503419a40c081c6000561581c031040344204d288140c5180704c64400c1050000400c0562200c0f16001d4030b442501d5040d40f2400318014000c141c40e201004801607080703d8018000d11a18028007940c0c2515440c0201d011010b10b594241011041c50003c001040c0d0341c203205a81b814503080f41c030001d0080349464007041c074010900030a883c0c4050801450902410514210030415400941c06800d291003512680503013403030850750b0f68002003021b400319401c00100091500c948804d4090b11501610b9417400000c0381e55951604030300070005a001d1101c20b20820402110412101d1403441c4104a141c3d0800c40c190006490100140c0c040200c078940107105200780c608050042c1c41c0c4140664000180342c106c1903004e0050030000c101c2881c40001e0400540c5825080e4000703034103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 338716564 1250 338715314 338715329
    0x1091502040f24320702040e0606010210020f0906180a090b0d0308041704120c0e0103150504050c131a0603100e0c07021305190b0a0501031a030d09 65
    0x100e1607aa44011081e181c100d043c41008a1041c0381da00035554098640780100c400d044001c0340d410660485414240410720b10103042480005c9682401c500b0984141050b00b51090f0041c0020710b0f100e40000d40e01c0d003090341101c02540d00491020044c400240949141c014018031803501ca0350380c2c240032001080169051840b5194035130001419155504c11090215400f402070706032181d00761000ea505c0b10000c0c0c0121003042002106d1a81118800c02405c0039105020014054509a0a00307141c2001250030040c1c4094116004000091100e02c10030070310030040c54080303000d58450410500b800c200141907900554404203d01d030250940e4400c05100c0801d0401c1202060b50005102007400202c17030310002c64128034402c1c131128a58611b401d6202800c0300c40c252030420103902266a883c2d1481c1d403130307846070340b01c82c2801154003906a40c1e1400400c916010081100400c0020b03903006c5e440c0c81602d060658a002108120441101907190700d000a07007200c82840b4110b03402001a11244640745 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 338717814 1250 338716564 338716589
    0x80a050c010f05060a060e0a0e090a031d06030103060515030a050706030e0a0b270118030f0f02060a0b060904060312030605011b060b0d02090f10080111030f0402030109150204 77
    0x2c030811500d01c5464011040503012180e61801c040b820340b0030b084252016584030301c2c9042e0000d180e0031403411140c803d121210180052200901d40601041014511090241a01d2079024050388450701624116900070101040c40c0c0ca88545101a8400d18400243c0600506548606014000842c1c804580642d5001c101c40b810100c00c250310381e010400000d00c0c805452001c5600700c800c401d1498070506140b0030086032061094a254210760545500c9161012100502c1c400d040e0004200a102d8415003408002212200c100079201c043c018100c1c52a01e580b0038101840e621005c01362485a04082c2040299644030700302003104200346140103000a0030036001140315441a05207101262240c0c829210b581150b5903801d019260100d401c0750046d20300c00c1d20b40050785d50b84698900600c0c821003504c800341001c02c03410520003046d807c4080c00780e0602c812180e500c0c55003402c603580603e0010000c1d800392117074400a405070154600103025444480c00090180701141d00500481d400c0c0340d08032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 338719064 1250 338717814 338717831
    0x17040c0f08210a02030c070e06031002191d1215060f0a03060e0a0c030f0c060f0c0b0c042c0a09030f0302090427051504020306010b1303080a050c01 65
    0x503aa80ca100e01400b52030481409280104604004058101c040803070069905140d00c901002c7d2900d11a40d1020584038600e0003800b81d10b080921541c0c82c00c0030410303015480d05600310141c0c0403124050480301c0800882501440300c4611030082d421410b0001805134580700d0020100030340c3c401e40c0060750074201000201203155464200345684008401500f241007482c40e40d01e4810042191700d900001c2070040c0306200001411800189020314401c61544ca1031000c1414820000d24950b000741050000c544c0742424016000a0a00c044c1036000701c0d0400700b0381d20752082074250b0145501c1204401c000102c450302e1401d07da6040e0305603800b0b41408100329680c0c0d4075001d00391450800d01401103900d040800602c03501c2900246180100944003003400c4607841a21a00e84906140860511980e10402d03c2000fa05021460784c1c245c441d00d070046681400d03000203850380e43c1840740c200c4014002078183d2907500e0240c0c848005540011078a601c811100c600030b07060f07502c100c800695552800900 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 338720314 1250 338719064 338719079
    0x60a2903070303120b2101050901110d02130503010c0c0201021507080a0c031d010f061a0a0503091510180207051203060f030624030303090a0206090117040c0f 70
    0x48482418004004281c050300d10349003038604402c0800e0a81d4201d80300e154110090320380c0d5007000310392240f4044503044101407050440c00c448015107800740343d03414861000c03401018001551954010701074010b0b50303041a001004400c0340d46520240d059420548601340304cc2d0003400742c4208078000e0b020768041091410700c0480390481103441038081030034800400e0740383c41c4a40c420010800c4a05002450144066003102c45856600010000781e445103030401c1c03d00124003514004004010700750003050301075024003c00b80140c0c2c01c904200280800010074040c800c01404810041610b500c00761401c00e10072650002100d4001d002c4156501c1480c240c503400fa9100300c50b04280c00c40054589541501030380c1e90b441d80b010f000d25522400340404c04189607024412a80640b034141c00e550321540c2156898015202a9607002d41b00c0e420a0042060300c05011030a1004c096045840e41d0742da01d80302c0016a84981c051012040c01c403801d0040004015001c010324056500a01082c58400da481c0d01 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 338721564 1250 338720314 338720381
    0x1306080702030f03222d050307080702040902120303040c1202010509041e06090b0a09060f060305070c06050106110f010c0c0305030a0212130309090504081c0905060a 73
    0x4a400042e8000c0140d60361400080014541040d08032103910184681da1034403000441207114190f420141801003e5000c03103109461510061590384e0381d6042c840140c031516182d004240c4043c1050320001000700440d030340c0340d0080f00d00a038000d040c40005008211060b990390011103044440c000d010a000c1886501e86504131039241d8160343c1d00c0d190108800034030018001244007049200c0d580e61a1900c4102d00d4004e03280500700a4030700041074070240b1304000120449034002040b180c40e12809020400d840e2410070145e40c054107000c80d881e00e07201e00865041c2d514000103452a8071700400031903443d6000c581e603920b4030364010840b80325414110b1024200c1c0c8c8a0440000482c3d68400004002400303103010319404101034000600700240c2e00c841d01001c0c1012507641c501984610520b90070140c0189481c0044c220a0f0310401061070142d4455440b40310743c2a8856203011101c030768268070305843d00700101d0325903c48184c8000342001d0744004003501048003101c22002122042122041c07850301d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 338722814 1250 338721564 338721571
    0x302070f050a0306091103060c0c0105010e04080307200a030c060c08090c121c020c01080c13300606050a1a03040303020c1c05040e160207091104090f02130608 70
    0x10000d4542500d1076854031300030709404104443c0082c003003140d060b4035681800800d105a501c5040b8a644006c2e9440303990031035205070880041010301100381700c0807521005c04c1d243c1c00039090a003846101460054034030180c105074400315040c0b0902d1008410103030b1040701c0c420218440c3c001030000c01d9910000707460480341180e0504269102d010100e01c00c0c9030034074030111815403490555984581a94102180001c503036100805a03101501490881d40e01a611325407103100440740300e042c518904451200b81000f4400e409100c0461441d00b0003007055480090001c402d82d484d6680761125138030f081c002030250392003914804d00084400003070b40001450201444030031341c1c01d028959915a0313001e4000750401680d000c4203104170b5001c00c201d00031b41140302894a070359031540750300c072454500303143c00380b81000f0510000c05221890502c0079a03000680701e001d5644a00703010030000400c01025009008503803106c214a030402c00c1c03070100140300f6801040c2041141c4450308000782c640780c090300c4843d400d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 338724064 1250 338722814 338722819
    0x30a0306050108160f140d02070c0e07080a05071403040507090609020708270303030a0204260d0e01030219110c0d0201050304030309080d0203070f0915020a06050907050405090a0302070f05 83
    0x90620b07072401d00c00c00081020103a80c0c10400e6a560206c4202007950700702640385015281c2c002404810f1000d4030840c130780200500d920b840014581014014052140500b8108945841d070b00850b4815024401d191100140200c3c440c0c2c0b03c1c81c180c100165601118481c944d20a8036201020520751028000c4035040340d00099814580460464808182402003402c000380381040610110195030a10046000c3c04140381c0c051384175801d03c069400900c459000d14960746c0390001078801d41c2c240101302c5018012950801484140c400c10041e0042e2050b04c40d14400c100100f00740c5910f658210012090f1541741030111042d02008a050200d0b11081100c081e01044060000800081c842e411260926102d50f585034105050051038905a0300240c8882d0701003592480b203021035a6101070580b00901c02d02c6c0d19081040704109010351a188500000b40103652100005441c1e0b290402c42c0711300400c0d029108200a191095110780c03a03070341d4400c0480041c000d00000040c4d00a80c038940d84142d4800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 338725314 1250 338724064 338724091
    0x111060106021f0e03070503042d170a0210030c1e1e032919030c090b040e0a0516080705012a05070609090e0109051c021509030a0306050108 62
    0xa982003c1e0f11040f02090200d2183d131a89249800301405102a00e1240d100d04001e41c2c45038141100c0000c80045442e503803008020500500ca0020103004d010011100880c203441c5d90109145a03aa0801213002c00181d080300241c8280ca40b007a0789548140f6110540e592490a039010004041e208040d920b2210300000790a9101142c00030f81a503c60034840f00f40303080001d002003180400c42c0000755843c81c001c0d4005042c40520150342030a0000c204100300d19120f1004117401c44c1d0b138416002c0001d0080400081d9070382000802a11141c1c083c00b00d48000100b1108016841d2411644c2c0310b041c1c0070503100419038a880080c0142e0009440b0b025680d0507100c0904180884c49aa20481c0100d450301003d01c011182040105a092000c0b8000c0c0c001d9603981c1d04a60f0821301c25409940c2e03808504102a0724082d00c402c041280032a035060148140100820100800d80003286800030b10800c400c039600e074a1040c407400c484000014407414000c0d803001c2c80380558400041d9141e900448007056011003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 338726564 1250 338725314 338725333
    0x10180b0307060e011107150f0203090d080a05090d050c12210703090b280203040305030304200a0b0322020f300c03010609020a120c0c12030b011106010602 68
    0x6143c400080c5003042c90010041503a0421492402e1017560003800d1000c640c08584190075031000c90b0710340040107400110b20b014440c20204400c0f030700001005d02a9140803c4102020b44100111a04d1503001003411500c240c0c0345c28440d484040000d9100d11400741060400215000423440c120702c28a8070240f14800c0d5414151a4580d5201d46070480821200700300c00f08101e0720000241081d081c43c4c0c2e1074401141c50001c205e9984007100c000303000556005100400c00110008100c903801580b1840c0c1c0086504280e102000c8a240094650780c422000d40d0302245103c002c1002c3d40c412000c0c802e0326140c204000741246010034403018084c0d040b0788030a5030030226091444580220110010042c4101d00c1e0240441044004400d02c1e500c00d80c10509083c0018a024002c0c0c030040c1c0781082d400c45c50001d102d44054040044112001d01d01c1d6144d600e600ba800d4081c803403480c1459081510b8541d45034041d50010010051050460f010030104880074181100000c1c1d168140d445580040c1700081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 338727814 1250 338726564 338726567
    0xc080d11120f04030906052a0f06010803130e0c0702040c0c1b08060a020c0304290a030204090e060601080c090a0503070e1608091e0c040510180b030706 67
    0x5860351510050050030401580110100040607200d0303611400c1030b00480c00e26150007809903419034014410400b0a1011800a560b140e1140121400700007042a0171a003504981e400c00c0c10004001400f40265400010a10000b000500f882004c0506661581e03440700c03416159544181c4410001500a104200050070654406406d2204504228000c81202d503034025240b400900088209030703500c1000c10410790108040d40d0441684041907081001003a43c4c1c1d43d8900942c4189900751400e40412091402d8a018016501d50300c20442552211600c0010b4003951007486940c20035498014035061304030b4003150481c0190b20503564034400752100f0220041940001038803070744c411a010b1780040c0640d030400000d40282010206c1b80742614091902c20403040780e2411060a0168030000c1040c0424007107080646103d0741e1042040d400c1d04000c040c0d04d8807521500c0f0302d4200303142034148100c2c0b481e81c104a02c100c40401918800049288200400b5100e01900c901e405a01c004c2050028a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 338729064 1250 338727814 338727821
    0x1060f1e051b071401050318030c060103150b010f080c090a031103060106140301030308190c0c060501120308010b0304110d080702040b06040b030a050901022a0606010c080d 76
    0x1150340342003030310300c0c0144550944008000c1040808540c0c0029241c2a40034801d095100000410b000303000303441e1a1016906203101c0100300681042400800540302501ca4240703204510000011203840368561200d15a172144203000075600e80301a2005071103601c00034051080303081011395681c0c0d142261044203641c08803000d0901d07080303040280441007903038440710003000c01580200c01e00c80382e000050f024107040c100181c002104014056600c0c070b440800c1202141e04503a4980f4000300c2c1566071640040c00581c002880007001d90601f4280144030307038824083c80d030726405402c00f0000c59036600c0c2d103090300c0c00740302d0401000f06010304010069403080d030018542c03044c001c004207600808408001440c18601c503800302c03460f1350081217400541c10715106d10400c03104181c8170945042e04003040c1424500000f81071b00e90f07d42d141c0300050700c2564290180c5d09540700316840c1059a4045101c495108100c0c001000c03640d12940303000070003562051410301c1181d80c000000c02d180508002c45107000c1d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 338730314 1250 338729064 338729087
    0x90702010e0307061a0405092e0603030807020f0601080703030c02060702190807050a05010509060a091e03051504030525020a12030f020111030a0e1011090114040b030106 75
    0x95540c0c419008001c40e10901c01000b405101e42e0f03000910083c59007222400f003507465080c0c1d005e245402d00704440f8050000b810254940100414140c8001c0f640791101aa003c01c40041d80281c106031000040540140b0340c2400740b1083d80170341c1e01c900d00c000c058079590352003445801d0f290761041404002080c020340400080b1400a405503241240b1500803c0d07055034181e00141000d40e10780c00070840c242050103040054441240c9070580681b510000170464010b40b404144215030000300e02072114010700300240200080c0d00030000000e242e640203a050f04040c4400d03030b00350040f40700b48242c02da84004c42500c91549612403904118903a00e8164a801c4100d0021042002c101044005a59010758a50091003144040584803a007840d00038012250f074158181035a0600100005641c109800d60781e116016003c00100b04030000b000c2c0e880c0c485210310300d025103482c04c0e09000c0280d01c544004e180c241c3c000c3e2075400011003032641a0106102d2440f45003500c0e0340502c01405034603c140c2c5ea90f100d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 338731564 1250 338730314 338730317
    0x501140411120a1b230d1401020c0703200114030103080a02120c0d110a02010c0b060a03150f060e010b040e1816030b0604142208030f040c0905090c0907 67
    0x11400340d8950240c1c0b80c3c250568010a0301d844c0b000c20240620031032000f030b41000f041110700040609008101a080c140200929425003024046a20700d0258140c1341c40541d2079040315111941e82c1400050020b2078841c4080d454598080c2c3c85241d40540c90b0481c00340c000304035007440c3da031a41c2c4030900d003a0045412501140214080b016135000f00c840900b40c8071000704060704070410454400307002000191110701e001d8210728800c40160780c00454118400c0e0f00030b0055112030f130f00c00002810302545500020700e4601d51030341d07010031914640c6c41140d0b500300488003000090344901c2d489801c040c0901c03541c1842081048144000321504109030b40225094103481c04101d0806a0030342007910b080c100444041c038036a820001e010515280d50340204042d1000c020040304032914a640c442c0081032110b40101c400c28bd91900710007500b8a40180303030854045516818070b03003548443e401e015507080c0d540061200300882c0c9182c0a10440303004041500081400c02400c405005107080020111030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 338732814 1250 338731564 338731573
    0x1090e090114070206012c0601120f0f0b030c0f0306040f170a170a1a01031a060c030409060914040b060a030c0b0919030b060d0819030207050114041112 67
    0x54070950080c03002400f0344080c0d00035001c00c1d818200c031401048410400040042110100100307440c4886206641000080c038180c60401801c81415026160740c80581e01c030315140141da02100702c0943d0026810681c21000da400340e85203030081102d8880201442d943c190800e4001c200005c44200805168502c101c0c030140090b00c040e50914070799040360046002090307050444d240d01d01c0c50429020747c850142042040b50400712000200d075807802000640c140340c7c2d02c0c5490056004070140c200c40a04006090030b6035408131850341a01c80d000b0707200d000415030a04101241c01e62071402440c080300440c020100131a500d903120100e5465000c2c12094106440e250040041040403091a01401902c0720650707550156005111403c803030852078800d00c524100045c000114210081904040101c0c1c007031142031854108151070f4882d8141072030045922400c2201110b4141d0040c2440f01d01800003000307800c14041d0701341c555003805c850040a103884d0490b518100e2620011031200c0046060864 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 338734064 1250 338732814 338732831
    0x509091e0f03070b04051903090605070314042601020405060d02090609040e010209010207080a0c0330090315090b010501082d010e01080d1b020d05010c171501090e0901 74
    0x860840c1d104030004d4540040c01400c0006201d02004210000f4010107441000001c1c640c800170b1000446010b20410080e001034018140f40c0301c2c008059106200012503a0703900d43d82c0758104240500402c0040503840c900361003450451040c8252011104090718043c03070315401a08043c020b510114000d03501c0700301800250301d55140c52150f200c02c0c002000005950f401440006890140d00c0d6025280543c401081100090041000501202e90100354002141d05200d0199000040d9240358004580e0180324000c840d5804040d1710100c03030148010b54a0261060385030fa0544004050183c0404003040042105503c217415480d0f000354040060105001c8220103102e15040e560074203c02c0c43c20810042c00036a00c4140706034014844c9000809020780b4054003c0c00b00014411194800c01d40c01c400a025900c404074030807100b0313500100030130601200200c0130340402c502c1c001070160381c01e055000542c1460b580403405075001d4161528802c251034510041c0c400308004007a0034040d52140700c070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 338735314 1250 338734064 338734093
    0x80c190806040c1e1409150d05070608010b030103080712020316080403060c020118030e03210307091e050904060e0a030903050609010902090402060706200c070509091e 74
    0x110b8000d6104150f4800141e00c1d01d40302e0b003291040ca5600c0d03105010041030421201c48440700070280c0102c03c0e201d00c0340c1c9668004041c0e85540c2c040404503001200040040f0400c40e01140d130809441031900c9564450f6251481070403540802d01008001420030010100401d14510750102d50080901c100c03864444490f03850701000048640c212489200400d00340108030150207286010000c52000300505c1c83d2102243d140540c800c000a01400217042c5d00b081c25807814031042d1440b4001e8003003903010b68070340000007402c0d034000c8460340000b0f00390280c0429141007a0020509809401079011450340c18001000b00701c28002d88102d903800d540e60311907030750540240000c0d10054001d8039400301c01460b6080c07090601c00300034400100c607413428a031980160349111203141c1007034041d600e40307840f0f0070b441c030307101d03001b000081050450103a034047c5070b0460807000c0d0b00500c030280340d100550701c0140d55030090004075a415034000100d81c0104221049444040102c4030000b102ca40440d102c59041158 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 338736564 1250 338735314 338735323
    0x311010501141e0307080106090e03090f2704150b12120f0715020901021603020a0902071506081f09050316020a030605040302010c09081603020105220e0610020304080c1908 76
    0x119800e945aa42c10001c8040302cac480c80340e80d42c15a00284d4a440700c45000280107041c14180700d40f16404401094030030103440818044144514000440e050900d410001d0004040303403908184a0304050002d07481e424003c0e0f020101031201c400910894200002e5807400340c10544461094000a01500003c10204107000e0300b4100704000040e075448010000a040c60000e01001c0c41d62204504100016264210000200c1d000c500005868100e80c3c071703101074000c419080c0192040d050400100c1e000d107000c42e100e03110000301c180d040460034404010300c081da071a0340000740250b0428400c24001c070804030003940350700d8402020f040009490396100380c202d42084e101640145e554030900c951540c1c000c548140507208040080980703101e00c2d19220055101c50000a04004000c20040f4805a03650514401d001c1741d5100c0e24291900d941200d1002c3e0300444146124580e0605062013240c004400c60b01542d000702c001e031005184000c14040e41501020a00e0481845041c000500c01c80901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 338737814 1250 338736564 338736569
    0x3120b22050717190b15040b07110916090501030903020703110d0803010605030a1d030a0c0201030b0303120906072a051509010c0e031c141908040311010501141e0307 73
    0x34844088221a0901002201e2294403458046c0c0190343c039102c0b1380f08038007080c2c070111800b0b040c64a42eaa801c1e880c00b4a5003074503140e4201e8120194009010058040712148200f0440903500c0940b0155100011001d0f503184160180158102c40303410700100b000c812a10556140150605400074925682c4415552090f0300900010720301000b1300460780003d019004081d88409400d103001860014400c1d245e220b600048e50a201802403040c0031640650081010810010203503520354107003480b09405100c040310401480d00036034000526a80c012000c0d1080000c905a0407040c0c038460b00390031282e032a84074100340c1d02c6d8410150307440354540341c04110501c107448803000800d0f44242100050600a0749500840c0301c3e800000718580d0701d04003942c1d6112007042d640341c1800c40c81c0c00c0d41c808180b10b01c5220511a80d81074001558400c0c503810080300c3e4040c41c0b10f40c3d50b07450101d0aa1740c0d01400ca0b9001e0003007041e05400c17420b59900c140703400612100c0300c101d03103144012040c0c10140080d18003003599 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 338739064 1250 338737814 338737831
    0xc081605030f0a0207080c01140a0c02030d0e0102160807060804060b04150302030c0a03080f090402040b0309030a110304030b01092a110f0303010f05040c050c0a03120b22050717 78
    0x9110f404050b414031500004001c42c0c1c1c0140201c0c0e002c50006419941010180d6050900210740f0102191150110003015600a0280ca0000d011030f072004280b040090303540d42c0035202c2e62504100003000405850100da40a202812806051030303021242c030b4030098019a1215110269106e041da1070380725800c1303007102000041c1000351035441403504094903892070502c00e0240803020408550706030121003c600540b00010354440503140000d000740030f50b410407001d600d0044204010050000001c0070b06102c591280041c8100071032415030342c0d1141d40001041e42210000402020741541c0004114404c801d07840f910002015046010701d400c1102034a000805a02511b100c1c18014011100c0500034007001d50702e10360404040081c00b100318410b4502a03969000f0000c1d100d41f258080c0c407042c2c80c00c0c0c01a6084055075040040c4001c0107052046c007018a0070020400d9882c0400285403025051007400c3c030760601d0341818500901e00104108284802d0031841000340c030014000754480c0021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 338740314 1250 338739064 338739067
    0x80601140408060709080d0804060c020f0f0f011113140406031a0703290f0d12030b010210060e040b092d0d0c0c180f0204060e130203070c081605030f 66
    0x13130700082402d4816800518603070406114840300b1507100c4007650b03009802010104021960a030103d181450310407a400b8140a020705408040001195211a07010840000d1080c2c828112000301c15201d1284c0c081d107001e0143c0c10030411005c4441da214002d110003800010450741d07079140c42d1107964951001100ba032403200c2c01c0040c1603801d4406c150756240c540726407961154080c017106c9081a00b008442d4452880952008969a5200c03c05141c10f030b440915144c90551800e00940a07106440750300340940580403918080d40b0880c0704110840e152038003c0069a10341d500d8101150710050400d5015005141d131000120082003410301d08000c01c01501c550381c1282c5840395050058507145401004041008140072818050740101a6050095821000c04001000c1d00042114034003568885002240025103107802c00d0107000f508105480b4003000a0200c00d8a00032480f084646a011600c015011404101520007621419445a0420181850310b0b19202e186070040c04079000103140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 338741564 1250 338740314 338740321
    0x304030f2001020a0305070302031e0c070203030c150f0c030f06120303150f1014030c040e040f02030d0315060302090f06160c060804150504110a06050a0e060403110108060114040806 80
    0x14175101e000d6119a6900e4114210705084d150140709540c03d4030303080302a640b1140412101d2003a4021188490350050850781e41d030180502094070380e0301d8003000054401d241c0001409a034410402c00d4414501080e4841c80c40c0d5840c600e5810f0814017900241d003083d000c9010344c0039120100000e40c06211082c07112900c880b094401c00c00026440002c1500039012000c40c0301559802909644584503084ca00075165961220210800c1c050395220084000c08007062109110f0303d1010310b00d40d140254162452026454802c0d011303618004c40825048589001c1009800d10a502501c0a104020040041c554095000800c6a00100842161000703084000d900b0042c260511900400381400c182d0b03150724081d100d80350002c1d0001782001c035030b54903000014200040d402e550041d00100a0001c1100713503d80707a005140750080498280803481e200000701e0f207031410f0341c00d46e41142c0e0320110110959641074011100000301820140c10700041c0c00c90075a48451302000b40c000b030314107000100182d25 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 338742814 1250 338741564 338741567
    0xf041110090f0902120601052107050306010813020f190b04150e0d08040504021303051c11071a07030e06220605040e1f0515210c0304030f2001020a 65
    0x1c082d501c42d8880721320400c032010300f02d002c0040e65036000000b402d095403903001c000030400809801c240d04c0c000ca4060b540401c4080340d0450051406020280d8415000d6500d0341480803031040080302c040c0d0311010201443e11645821020111f0034100d90005286099440a000b0300e1500706400514504000c50f8403c402140d0016002d01c8120040b030f206228429240c54000c96441140a102c0c052900029050351103200400c1900055500c00c00700d030799103083c9103180c0d00c00d10100d41c504c50001d2180040e0040c03102d000602e1006403040413420b0708071302103101010211988039840890901600030039800c50341da510800307810740d8001007040254030b02d100b0f80c00b129150301c2c1c1e4000205009040c4010310403010300c2c0100c0c0e6404020001610728400388a02d408034007640d42d5111503880072403810002002e510400c00342c54541c40800070192540c8116628201c0340d1012508020207040a100040100e4401d000003e100304080c02c00d55181c1c0c4550740101c030018000440c102c45690000b0b00c45140c135 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 338744064 1250 338742814 338742839
    0x1003050615070b071d100206040c15140310150507150c080103112b0212010c0e190f060c1202070819030215011e1502060f04111009 58
    0x100081410900e010b54a0391140d2084070090686801c100791030305c1d4090144e1003201900403586008007110414030001000940d00c8c0421201106c1326900d8410000d0242c0301d600903100903200d1070300e0342d0440c0c45819080179031940005041c0c0b58190b1501074000307040c501c0b00031503014043d00d96a44641e58803050410b1011551011104d94019192940c00420b15074498940c0e419a54014061001c5103d094005000400c1800040c4007045c1070700c3d44c0303c04030071000260a42e054403e4500680b44990385416900300e9645040260206003024403040251500203540703042025042c403480d410b55102d001c12003080c000b0750803510101d42c0e0320a003030045c0110419443c0705070030315200400185042a201544540110f464804c007100c0000d82d20f400c1500a01c04c00c15600e000d280d40246541e500c24151000350b642e4080b198144044000104182840121041c0700900d03940040c1001c0d180e058451f452480000c20641c1d2540c561801000030f50384055190001340d400c4d07035880d401c603030134050880c082 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 338745314 1250 338744064 338744089
    0x5090402070c0f06180303020a110103092f030a0206040e040c080109030e130b010f05030c0f0c0d1710120c030209270a1a0705190f030605010c0b06150910030506 71
    0x70040300c05c01000000d50000b51448115030065500d0b05007890400141e014041c5c5401c001c0c08803a001034140c0c0742d8040325248010388903c0e119034020007000c1c5003e15480b0b14409da40030350020b07020001401080c20340c02400f50442e2003000c40104099884a01d90300b15440014101d00185800084403034a1614a007003242c100c00b82c5008118440082002910b0980c10725144010302101200059034542e204042da1107079071005d01a50740d80c0aa81c1190358503903c03000e102401041498072902270644050050501c600038402199484604000c59404d0501c42e502007212400000d410103c01070311204c244034002c04100b420941c2c080300424250000c0d83c0d0461a8440c1640210540c00201c0c031034200c83c40902640c44006c4002d03441f03105088a2500c40c0311018200c0056216804841030b80c0980740101e0300d50b49580030804951074400440354140720b06800703000070201001040311460034401684600c0d03607203c16a4603101e00c56001c03400e0160b100c40300d4008284e80701b04004090901191070083e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 338746564 1250 338745314 338745347
    0x1b0a0305010e0c040b0d0504050f010c0215100506071103070f18060b0a0c02061602030d0c1202070312050a12052706040308160210060308030105012c0105090402070c0f06 75
    0xc02d400c0c42e03081c6146004942d4106c10705619100130406005062000b01c5562551100030f220240c0740904c081e5840181c5040301000c45894030000340d181da0f480100c00d00f91074000f04000d24059098880c1c12190100300f0410340d060081e404000341c11001035000b03100420300007030000b1143e0700350b020440456005904c10b41180000f0041101c1043c1d20048811175903604079600c1da00c807400b07084100d01361443e0003c000e403d0301c0340360345805249800151094866118108117840044061001c0740c8031802840300174140c3e010409414221409040504441e850910341041d106130704007190400e4500c16102d1100f090f034801d951440300e6480080c2814200640b81c01407030141890fa030028440720b40244811109070302c40c6581541584240226145200b207400c01f4841e441c1c0320300b4552502e510078410a40803c00458600c18a0702030100800000002c41ca020800141002e00541d80c1d0760045001d264000d6081061200240003100140007825240030010300007401c0002c094200694054143c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 338747814 1250 338746564 338746567
    0x60c020c010210110d0f0905060109060e070f050d1505040606020313050418141e2d030706060b0a030c09081b060c03030405061006090605030a051b0a0305010e0c 71
    0x103141d0300003540105000c02c0140c000f070036225a103141031107801103000c0c2800984c10a25000c0d0003103040c1d00680d03015805003040d00c031580d0360307500004115a418420503408041d072a001030281400b4541001101c010750900078a8185d034140908111040d0801c2c0d10081a000c02e010b021504141c8203600c0601183d0000b589050f1110710982c60f000a180b2426218070b485080214040721079417036403100542d00216200d400285d1030580c940300e43e0111001d03001c0655602e00ba80f41c00c280020707980ca604040001c0600740c0c100f20400241e09130264100d418040c442080000d000070101e2042800814903109481e85500441600505440d000507590003081000310050207510b00109000c00702c0c40c00c58001c81c4501104602255180c014502c450605000c044100828880c0100d800c501c07030080340b00461b442ca5220a010303551003c0a000340c40000d0800d00010b60300c200d01c1d5020b19000700140d405907213958003031754011110b031f40084c0c0c2040c0040e440340c00400021411070400c1d600503203855a01ea = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 338749064 1250 338747814 338747833
    0x1c0b0109060b04050d050a1a0a0b01090509070315080307061a030303010510050702040f0905012f07030c1721010506070b06060d0b03060106050405013c030e010612060c02 75
    0x2c0c29900580c090b4a10580d05a41103000b004030420076000300507840300310b221081006095100e004001140c0b0603808909002d0742200c81d6105415800680b00010a0310740651185003003207004200c241c0207140c1111181d10013149002082014000c003912070100403501056903680d10340800c141c109420f00940c0180014005547c0e040b001c0107102c09113103816621002d00f400050b028009136160744071407501d828003c0701801010740004a000c80b8030310500c0995001c2002240c008070820303a807900300c080c080c061031000901c516180704181e4000d00c0d0300c50240e00c06400304400c40d441949911360032081003c48030051007601103214010a000c482c1175080c2030442e244c0181c2c001004001c14030030000001ca00301d004117150300040e020900507084422943c0c64170400b038190740c8140a41d501244d10700c50750b142403103043d00c081c00240c0d181d4a50f52000400340040704091101f000190302c00e05440722002c80e03684500740b190f80018044090a641104000c1c00c0500489440e0104074045400c0050312 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 338750314 1250 338749064 338749079
    0x180406060c12030609020d0f15050112090804050907050901090e0106020601140d0f030e1e0d1113090506060a0e070207151206030f171804020304030309021c0b010906 73
    0x844421600b10021000c8036640860880040005030001d0200a02c0032070298881210323940310140810080f601003200c04407034103081c3c510040e28811b443c0001c1401030714501020381c40d00201c1c0c900c0d1180b0a4036040940300c4000400301d40040b01c501e070000c3d034081484400c40d0b80c0410508024a60b1404506140d410654001d4640e0014002d000c0426550040031006403503590540e032482e5007120395002003c1461a004001c140b88024040c031564060f01840c40f001d402004103041c11000401c5843d1081700780d40c0701e5411880c20101c450b8440d502c0d4100202290890044040c00c61152001e03015500e0f00750200481801c1c05e800c01c00b03110098404102c1c01c9900010607001361a00f0101982c004452940200e5210300094001c0200c40e0400000208000d84c500a00000c04c3c0304100c000c19400c1401d243c1c0b034081c040c490078815000c040038804055030800b42d00841d000f42c004e140c0402c1143c0c080d004900541c1c41200c684140d0300d1009110030030b001c6200841409810040824041c040c0362060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 338751564 1250 338750314 338750327
    0x6020a0308060f10110c030c0310050a090b09010e011112060904020303040503100501080c01050a0f0804020616030e01020d0e010903080d09170a2a060f09140318040606 74
    0x1009051050300400700d40326984604102031220f0004244000304c44001000816403c00c220650f98240302d02401070700f2031f2502103282000f10360050001d184560028000801503c40584654a03c682d0741d689140814681840f4511403551580045040c141c40e40e0100c1c21124802c094030703c1034034180015908650042d1842c1d82000d01160032010f2604c450000034103500c555400b1035414071911414110351180381e04100e0403916007106840d02c03203400c800103442c00d218041c41c40000410303d04101e8403e0703001e003120a8102d8000703000b1a013003082c0b10620003012171450100780d0110309a210b00c20865070341002040f01280302c82c40e1960358016450b002170241000380c04010115000414091020300d055848040c669400100c07126980341c10701015a8254818040f104c0058140902c441803080070810704010700c0308030000604850b010762610801410010b101d03100e5280c690003400701040d00340324068030500040c4081e40e40d94103003000c60b40040407100d5030307a4056810b10100b0400c0b07980200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 338752814 1250 338751564 338751583
    0x3060603040b04170d1406060c2a0a0f210b06040c0203122d010807050d1a0c090f09090d0c080c070f0e0f0906070f020c090f0f060a0602 60
    0x7540207420380c407140b400100010104400c1c104002c0c0129140c01c003005542c11040d14046072035511485501d5050500089100300403640e00a4ad21420a0f00c1c1d040d02c1d480a010520382d130a9450161000d03080c4000f550040d005c4e03001e42c1e11080428810b10a414800840e18801c403443d40d0343c1c862007007266543d10b070100301c01800240b01d1981e40e0700010f40140244100ca000c0c2c0110100503143c2d29025555882030208000000c5021081c0b03002030341c501c103a032107400d8107943c40d410080c88002d1030142084000e503809401111800701d82060854250a038a240c2402458550411034a80007080d052041c3c50303110042c070134400e503400020300000703060110380400f14060600e005400f0380341c5818038681606c02d00c0540311162040b040e00140038071052440c0800c0da03c400304080d05039241d01c840c02c000c448095070140c51541040000c100c1c07103401085403e03540c3d42e440c0140e5031040c0801d00000d030400b00440d030ba4400302703585004010807441c0822801c1c0c0e1024080b00e101803500d04001000f9034030b1100c038 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 338754064 1250 338752814 338752823
    0x90c0903060203060a0902161101111b010c050d0e031009080304110609060c0f1902030c010804020112020c240705030f06040b0d080a020f0f1f140103030f0e0102030306060304 77
    0x40403580300d880d255410b802800c0603190555444403080d61445588e89809429505c1c24a40102061550f120700f00c0d855072014000000e000c40c8181e070341045100c01e0aa1788641c1840440a0002c000a105114000f01e54207643c4178500f00700483d406060a001ca000c500086080c40c0c08000300020707805500b9290010380050070341000208100200d0300310301c1003500f20b03070f845500440ca40800e40400101c4400d82002c0301301b662281c809030700450f00c0e0107003540002503050300f000c803201c1005c1d446121f85580c403c1c0149084e07001800000140001c0f03030301900c2d00c420705c1d80026030b030004c80640302200320b1252020140000d001d80b42c88400244280006840d901d140300d1208017240859942d50018010300307070300070101d005080c101e14140c2441d40c0300d01520fa01500a1244000341c171140803901c29589070175000031300001c150002000c11030740c03000c5181d601865034880c005449031440b250310303501961007511070318111440c084028042c0c030f24141c180340c1103601c1041003041548611081da500180e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 338755314 1250 338754064 338754067
    0xf09060d080f160b091011191e020a031b0309051203070c0608010501030f111605010e160e0f0c04090209010c06051005040b030f0a0b25021006090c09030602 69
    0x50000030300d0034400d401c114582064202c0243c0b007404150345a160145011030304440c00c07114052069401e0f134603180c801c00050002480191000c1403e0051854104002c1c580943c00c1303001c04d10160800940303d001440117a10802000e01016000014204400d1034200c851f08902442d41d0000c22520250159a000325001ca48004076103004009540c0459400505090015240c002c0104401001d11510b40003c2c1007940541910000d84101e8000e850110340d0386e460000c0344407004815041a02d800c890b80e660b1103080c6c0980d560180101200400b801ca8590591460440c481902042c05441c0c5031000009006100201c501c0e00121800c90720041d00150f116604140140c548240a00014140908102c2003000c50b1448524200c01e5032011103040201000b98014035a0311440c0d0102500f41d68007448001c07000c9881c4203020769200138284180c400d01d2541011105414041c80c41840140e88910303807054080f40c0034040c810160100280c20407010440700c10007081605244005040d0765030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 338756564 1250 338755314 338755327
    0xf290301020f1b1603150c0e0d120c0b040501020a0f1b0f0c08060a15080304050607060e0f0d0503070314040203060a0c090f03050307050d05040e160215040605060f09060d08 76
    0xc0c4520110500e1190360038040036035a04080804c081b9505110f112140f500a81d00c4105005401060300c4080c040c0000d549007000d5540d540c500200025404140100300001e00c0014400c625510300c1648100005615481030000c050240b640841080040c408048082e80304055154040705403150407201d40304010b9007505000036020700d1a000745146000d420b040103194100e80d0008400c080c100100d000d0030550301c120594882c002c900032554011001c011071004250140c2005251407e4041a00d900460301c8049502c1d0034000d152100109801100300071840381c1620407119600d00b080c1c030b0f0080c10319065001a0703c031840140140c0500380e403507103032006d900c1c4964811009005100094013000341c5a013007080e9260005a41111984541c003030420113075114a043c0c40c1240c40c5102c42d00a941c60f03010491070300d0095610b64101314841c00b00c41c9200c104c2c10a99450003a030042100040d9801d005050000074040c0546407805032100c8824040e15458080740114080e030451a0300b0b8075840b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 338757814 1250 338756564 338756617
    0x902062502090a0509070b040803091909020a082202010f1b05010501080309130c020a12020c09040803180c030c010507030306050307080105090f0a0f0b04060f290301020f 75
    0x1020014060b4101d159502000b201101035840180108061011a00300c0350340c8001c1c410141c0300700e02520100d40c0003880450705a003803415000c140400303007400b01032a20703484404100c12030f00005414000170340820180a688448a1006200e042144000c401110f14a0300040d100307020720f41f90001006015980024140038100003220aa03030300000a00455035661051941c030b4101340482c0348900c444400e90140303c0803502c200d041d40d0074180c01400d00003030b0076190006240e0f581c08182040d0700484a0000c9603948178000c96101e54803965511361681000d90210000d0b506102c542d01c010f5210035440c60b596600011599684042443c0071951020145400c9014110f1030340156007610462501182800d010b4010f144129080c004540404903d980d9050f540d41d00d00300c1c0a0540001d0b5403030319001c03880c203045641e0310901440300400c250300c6002443d41140e03a005c40c2148420600200b0080341c012272409020000780440c02541041000c4e04008501c0c424071880c01d0f204822146900c1401c1d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 338759064 1250 338757814 338757877
    0x15030a1506030c0e01180608060d060606050d0b10020a02190b03040503070203010b0109150309080c06100503070b040303090506030702120c0319320c070b041503090206 74
    0x50300081188455180d071594003a010380244010310b80451035030425200c85500c01ca040351a039081e11415040604c0c501502610340707003c003030709264100e01c1380c2025101003030b154011100184465500c20703030f48086031140303801220400c0034100d228071803c1884c51032041d40080c05522683c2c048600080464050120448ac60050b034440c82540300702100b04428080048060a101070096000b07018000d607003401107550240b03601a03207950650603c2c600603014429070180c5070440c0300d6170500d8a05041ea82c125071504078115002c12206000000600582c10305224400007402c4070255030741494210364018181040c140607140c00751201000042d03209101b00000c14500d001c11594568903291103015980725440310b0740184801400c0c601807210700384a40c9074203007801c2c1c0780c454007040c540c181c0c03401c40c4806001d011090647d01060000ba480100b05200307c0c07005100618486540b24604800d042d9010014414102810b1034407810030056141c48045800311204070589401c440300000c2c0e52042c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 338760314 1250 338759064 338759081
    0x6260a0b120703060b0402030103050304170a02090f1602011e020c01091b2115020c010603080408030d15030503161707061e090c0501030b0a0b0304050c0909010b15030a 74
    0x200e4031064440001d404041511003d81e030049200740585c4002d80140010b9100a01c0010801d52003040100202a482420382103001e00744800c0e5580713a0519000107030000c4040c4d41b4001c0e07641228080c00341045000080a084101c180000c1c4030503d010030404501d0b9069400d1811015000220300f6241242035200c4a00c5a51090507090009441c80309d082415030a8020ce060740000450141089040e15440c856001c0c5c1c0500c4400d481c2916202010182d0402c0c048560550340741d040120004154002a002905406000310b803601c49481e1203d050300c41c40f0341c4454040010f8107092001c00c101008940d581c03d03031000045910300c040c1c9003040184d0403488010303081001c003007000b00c100f000f56007000204500c42230040d40002c00c610440d00840c9c1105500401c05050381c1020002c2d94082c0d00240b048060041c1b5002242c4d0765041500c00980c0111000c035036a801008a805041c41c01d0104d81c0e8110720040020408034004002091400c1004400860860350201c00140c0300603950304203420 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 338761564 1250 338760314 338760319
    0xb0703090819231b1305010b0306040c030b0d03050c03130b070c05030129042007050607081b1c020a020606031207020d0f0212190c06260a0b 62
    0xa104041c0285903802d01403000840303455056000030000500500c600704a226050b40182030800f20348000c6401c44a00300081c140c05c8554140e070203922a400d0700c00c02e402800d0545400d5903034a005c20030402156507001580d014146040c02c410840e8880c903410a962541c2b50910329038440c0f0f030b40c11041c5180162001655030302480d0701f000c03030308091002c050031031984121401c400543c0c13100d04240c00c1c0c0700149502030b040c000180c18141c95840943c4940c42c03000000c6e000054506000c0b9142452800040030030a51801c00122503040040400102e94444102d1409002c1410100441c590791181d551810454607008100004450f032212100d404859911804642d00d101026001c2d445200c00c071f44581c0b09000d0b050709000741120503403c40f031803d940200380e0303120b0f903e01740e440c04020419102c0c00e07a0420035070801002859400c00c4104500c007501e10001c1d8040503c1e20301102c4010b0950404010810900d40440c81c28948030700c0780f9003824126801d01305980d1405502002018102241076 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 338762814 1250 338761564 338761573
    0xf04050307121206091404060f0b10180501080c0a0804030306120f1110021002070602090d0b090c0f090103030e010c150e01050c0406050f0708160b0f060414010b07030908 75
    0xc0041d00aa0300b0248600030f0407050003200e0f45d40c07107251700300c0300381c581646500d0317440000090004a0540c0a00c181c0030040900080c6c1004000219203804610b09a110218201c40d06150342d00d000c01c0001ca00514092030310b55507518124115030418099080e040040c4a60207011804160003608188081c0c0b46210b800030885003182031010032800890740940c0c90010300000c03083e903420802c202e0000b0b03100c250024082c0d41888012800203601820042d82c241b0ba09001803c82d035640d07c000c078111940900103030031080c10220f5840382170103031042917036104119240c614240b6807034910483d4116500b41c2000d140301080040141e40d0b2410400e40184060341c03111087d0780380d6203294420640410507400800556844d801c40e10094401c0c0d000d994046041070012900444403640101041c038410407507a4203150555192003420120f5030800c071020451081040000881d03aa4110390107101102d083c0f018100b401e188001c01c0506000740780d911800002d442091501031a0340000401c1000101d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 338764064 1250 338762814 338762843
    0x50a030509041a0303040b07060b0405100f081b0405040303140702060703140c0304110111100605130b21030c030d050117160504150801020a0207030c120b0f04050307 73
    0x140310340e101c03800c2248034038039103c04042100301420b50040300940260085182c1811b1540c02800d98114001c00c4400307a40301d5002d01c032503132180d0198a02420702201c5810715941000c0207403002d580d10b5042020164010700090f1070418102d11a078203000425140082d0503246d50408402400b281441141078100e404240200140e0000703400740b0038152a501000000303d41c201d0f03035040b0407094420118a00003880800c01246555007a0207000c94141881e03400c142e02c08400340e0400e00103840c407903015aa500f004000a0800c80c807036011300f8031185010080c04443c02c0024071041d9081e040703120103010744031800080c408100b00300c8280418400440351210075100c0400040c0400b40101d1003c0c555100c08445022000610744c00c009481d00e020f2000142040309100060800049074900c5800f0b0400009032001c082c03008044e0b01c4001d50181050a08504226078100c100e0b510004082c000a2a042e01042e108214550000304550700104070741c5460900500d0360145c80c501500b2186640d454 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 338765314 1250 338764064 338764067
    0xf0d081b0403150605180a0507050c0a0209091609090308070c080a0c0503090d060e011a090115090909060506240409020d09050102130801140f011502012409110c03090d0f050a03 78
    0x8034403905103087c0c20700c129035607440c0848950040d0403403c2202d6104001d070324014030380414100c0d0f02034003500440c1c00486401c260348030002403651060307400d42c1e6070340700c0c407024194040b10050f80861181082e60000655a4805c62036202d0a01160204800203401108014060040b627032000d40c010800b030540601418104001c0180b850314180542ca007402903286030082c1003a450980300000c202d0708107a880c10000b204402c4a45200c1010401a8940131031210074901c984500b1038014000010946000c1d070a0141002c031304d40b43c800250442c5040804411000401c035003c2d80e40c0c0c41c802580f281108094a00036241c80480105030354000f05000c0c210005000c0040101c03030307812000b40807051000301146028942030342d1034160494008014000552400c0000c503442c1450310002416264160031300705502410100b00c40001060b01d0104000d407442c0c02011040004460118a440402840301c0d036244202c8a1060140b10b81124002c10300110903880010320f40c200d81590000015443d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 338766564 1250 338765314 338765359
    0x905010c1713060305060d110d140307141b0307151412100b03060a03020411070f0c0609050102010203090d030b0303040e0405010906180b010303030e030c0f0d081b0403150605 77
    0x5203d0000740741030001140b9240c80307403c884403242c0240326005c2c0003080d08203000005020510a84492341b0300c243c50f1080400410003007000c54051900e0b0f0003045d910020050030000140896103a02c4299006880a9a00810703604101d03644c0040c0d030fa07801c40c0c41c058146c1c1c104665815031103250700c01041010103102e8500d502c0c3d10410301903200d8500c1586904211059020a0f209190480701913001800182010340c0603030000080d204541d400e14211740c2d10b00200c62559141202c0c42c000b800400c00140b5000307848a00504002d00095085150000005603103c0b0503d01c00020980c40c0d10782d11150703403410320458001d480107201c01909031a007420b015010744104c6004580d010b290101000c41c08a40c0c5c1c60743e01d00305a102000c04c24a07480d54808034007409902c0700f182c11070302040100071541c3c002000039508429004002d40800c003103580c0007515491008001001d9071481d98070482c2101c40382c3e0112410b032503101c030700040d1170a02c80c0e0b49031005000581040d03401004801c80c08246504540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 338767814 1250 338766564 338766569
    0x30c010c02070f06020a02011b0b090c040506060f18150c0729121f03030e040507030608120d0f0f0207111e1309050106170d0f0905010c1713 62
    0x4007150440c80d40c1d07024101980f2103503c01c10b80140c01440780e4500540c4140c051000c82044905809040d100c0b40c0c566000052040d218080168443c14800e0000e0415000e15640014101c0e1002d09005003043d1040843c4030301c0310710094074a900341c2e407003600e40d96022170002e0101074100c0ca142c45c1c01c0b9101009276506018000d0020500c2035901c00300e0094003a4a9112007505000d018905200b208010449450805003401c041e85010012040c0200030f110001c000441c0269a01c1600040e00010b100441304060b00100806043ca9010f00c07080c240020103402d02c0b14441c518a40c1c42c501400100024815280e00c00c800e1400c2c8410341000c44480e40141400c41d000354a9a43c92126040c100a00f200c040902070020501080c0400308524010f40c0c20b46014407484070101c0c440e20740d030b0341e81401c40d1600e400040c20210302d440b0b000c0704220308104030484601a41002162280040005003001c90640b08560400402444c03210400c10300101501048a07441041a114031013210000013403580ca0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 338769064 1250 338767814 338767817
    0x50c0c0a05250f0e060a1502010c03061a07020607150507030e060601080403020606040213051302070b010b0a050301051201020c012a02010b06030406020717220b07111c05030c010c 79
    0x884106980b0411684000890300440000c2050620341480c043c00424010080d9a0142c5000d100048100c1c1446468220407150782c0000fa210312040e80280441e03003e500440b40300d10b0581f00d1400200c04003004c0301c0ba030a0301181c159441c2c02040c640103000f0050980003080c21403c2c0320a015030650950010210791120109030b801b1f654420004549a86084901600503480f90002ca0344a04150740100020605486034000b000e407034601203100324003920f4188070032b283e00180f00c409110301003c04038091f02a0722010303490480507a0004040740030601650741304505d8840740d090403020950486e81031244480080c480d00c443c2070400c404c01043c2a1000c0d0034583d02100c485115841031149010240005000d141141c50f503445440003904000d90881c0c2c8555071006c100c5880c032600006d8083d10f81c0007030102800b030b02904a030004045d440d0f48050f0310306906008460008089040c40d404a0109a55040c480d054090000080c4815001d001e130460100260050f9610419003100042400b43d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 338770314 1250 338769064 338769103
    0xc0803071e0302070306050903091e010305060307030f1203060305100902040e0f1c170a050601031107030507170d0903050d060e040807060c03060510030c1404060c0204050c0c0a05 79
    0xe0040c480284071a610040c0103802000301440010341d1540180c0e00301c0e00380300c1203a050442000100c0c00304480d000c0944105984403080c00025030741801502d0388804203a01500c1541d15603518944402040040100b594078aa02c040440d54401d9118100854100301100c400d610301c1000107005004000003a40501c1c113040c072102101c14005101c080a0440e20002c104061081290b6140d500c51041c130b0001b00640c04448050075003d841a940c025003248138000b801d81443e0340054122000c402940b1402d8030103000d40c0e03020030380240555440740d0b00030300d860140c03c42c0034800100c607208000508c4005894000c5500030b151b03112000d0114040e10f001e08026180d22030341e0700b0442940444000f170040d5410808200050601d80020002141d98140801c00e551980002151504680c2080000943d5111052010741d841155461607141900401d0310745420000001c0055202036800780c0144e84800120310f4581400048603096800360080d240c1419040c9002520f5035070314511049100603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 338771564 1250 338770314 338770343
    0x7060609200f1e16230706140903070e15040e070b0313110a0e090d09080709150b070308010317030f1302030a05060a1512080a0302160c080307 63
    0x40001155580b0001e401c001c3e04080d1900b000910314410921841c000b80c00030b0010020b65071880e000a400d0a104481003000d004000383c0151050001407203e015503031000408210700781d00146400c260440c01c110045e03450101e000468504000c2e5808507403d059950b08028010035a03460044020004803401d03c40c8158000c41599244298050310100110030404503801031441d1140f00359075031003020103c441c4812000051001d403a558800c81541804804000c4218024800341b4510062810b19044090500380d603103175910303c13030f010302003c50b5502c0e18900840c206440340c42c0010000c59441d0760369004185801000c40700284000c5501c00c0c4c0710a105582c000c0304001b0f803481481203801444455855401d07104910700414410f9806004103007524011a070103001d110f00c103540c001c801003034501201c40310203d0600d0503071001026800f8198050000f03001002126441600b070310307000d0388500c1d1841820310351245c515402001c131080ba8400050040020024103002030040060044081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 338772814 1250 338771564 338771621
    0x70605090f0f1507050109022b14010f061202010e0a060f0804021c060516090f030206030c0f04080705090c09060306040e07092306010c02010f031107060609 69
    0x14000100d51040c8006011201410070b05042d00101d400103010401d0500707504000440c50380296070131713070f0b999444418190560a111b0030140c15518580c00034114408900011340b10f02049050042003210440350b19154601e0940044181200c3d01800304801a0340e014401c896201886049010440601c0312404600d02203a5000440f0099220780e1005a040c4608480308507004100f280e00440300d840208039000d10503400d400440c4103610005007807c08000000c0307041c5402a580381009580038052180d101c1d0f11400300210303581661910b80320703110340b4014800c81c01090322194000d28086400034808000081520881d1400c1d02c0c0e04206480e13418640140b403080310803207030700240d04001050a5007015400b1011081c10001640c0140c0d0b190044d02c000c0c0e0b012400010101c6240030107000d074201e07215000e650000300900b0141e4096000744e0010346103980d003401503000e165807001c25648100b2000221600780345c0c0300408101b0592a032a82c00001d101401d80780e47c118140b012800c4094 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 338774064 1250 338772814 338772817
    0x19020f131406030a170f0708160b010b0c070618090509030301230607230619050114030616270e0702010b031b0310020301140108130305040e07050909011403070605 72
    0x1581110b0007011005442801c5c0d001070703012004100000d04104044800300701c1c840003912507905a4518840c410000d410400d004c40c0d01a002054081d0f0104008802c002000401c04112046400d04040c45904200341001a803920391212990500700400c10180140101c001d50507100030300004003128501050652200d43c4061400f50020010810180814120002ca03000c03441040d003146100d0354402c42007810b01009440c0f04a00c240c0c11944d0950146050054501400968011800030018500040d5a0316405050074007004200403d8030b152034411050750045120412490341000c80c81140109118900d20400c494620381c0c1e000b080d041803042c083c1c10412440140180b80f903102d2241c000701403c4810f0440383d41440355014488850b2aa400a2350090200d03000d074104d803480703000000d0401c1000902d90344da02d00701c5203403400c0041d8111095905603901c40c031804205981d2000700707a505226a50070182e02c0805e0200024040c00c0c03240c41ca200e2110306400b52000b0656400c0d054619 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 338775314 1250 338774064 338774083
    0x1101020f27010f05220602060114091605070213020a18060e090105060a1b0503070201020706051c020918090c030c0d080336030a020114010819020f13140603 69
    0x2d081c000e500c450962054014020605c00f6442038201c0712a100f40001c45241194440030158200c413004014403640c124421130604020b13604c89034030349414401c0820a40c00520a48140600440e0380c41c2507460702404a00d07074168401045541d03a018260140c002d4810710324089240501110104c0c9217842600110903c11020b0102030f00e503400c10702004003070740228210400700074481c2c10001c0c040c23843d0007a81d007519000780059030b81c5203d5400024103005d41038001005101040044d00c441601001c6600c1130030054010041e281d10b00100000d000303407103120240c0d100070403540600030768600110724441c070070034110200c80c00300101d03009201c00c2116030000544000c4052000411080c1c0314494000403901050010051107048404520325000021005010f9031003c559031002c10313024820350428214061045145600d40005c2661b102d806064000603550429030450854585840c42401d07084000d080da0030b401c0409104c0c1c4014010781d235084254540607070105400b8240861030540 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 338776564 1250 338775314 338775317
    0x60f040e0a0201030b03010e16090c02030c100f02090402030a02090f2202160203070b030106030b0103180f0219140f0f18090c06030403031406010f08161101020f2701 73
    0x2150302e0700150020420003941a40654880c04581303030711041800414685030485803200c01081c14480140d044407503000700d14041d0341c02040b2100030240c0000e07560000340b031488004600c52121007070500c0a4082c00d08915002070005c03050003513801a94002d80301c011029101d04c00f241003c802004402c407640d00c003045207401ca1040f110203032031842d0010031020b0807c3c8240c06d400351035640481e20b049020b50101710483da010005100341c80c0d050188100c1e05809180600107003d40302c1207008080300150006042070311400c0c0c2c460071901c81e4901c3d88a80002d024a401d095561403004810800c1c98104281c07240609440c41d501a20b4040c516810016010300600c548000c41030040c0f41e03408018181a50f10b21a00300d8642c4181d80d45001148114420340e404550701c1150004003403a000c02401241c140003c2c1100315804035440004554010242c17180c1140030718080c01e045e540b079103a200b13428841e5400001d01e005000900001840809614a0240d003110006d9400b415500c250082c030301d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 338777814 1250 338776564 338776573
    0x405040201080703110f0315011b030e132004060201061e05040c1106041b060c05060411010e0406030f03141903050403030b0d06050609060d0308010e040c1508060f040e 74
    0x20f0545200760701c4804c00d450340b00034a51030821200840d80b420303001120901e6100b0358070100b0000650f4001032a000701c1641d888090b10243c150303134014046452481c078050051480c40c103401440f05050300480c1c0d01c0c041e20045003154007a24200840c0316406409040050340c07c201c4c002411800008180b62181100303525070818605100800018040081c40c000400100c0c2c041071144003010f0218130302a600c95519803c030b401200440344c81c917140340d5000c0020f20081001900214001088050f8003a5000050040c0e0000410041e204440c400e44015009442e0000200800211f022040c91180c00ba48880e0700d2500350f240085185d104203550300c03001c0011003202d001014000c1d009903422070310a042c082200f5204c0d0001c03502a0703844010a0340d4098581090001c0703414003601c01a0801d106541c105c032007480c15103000c1c05021043c1b10389080944018002006e2143e40392022028003d01586200e0036681514020040001070360160f110f5400036000c901140303000d08c6a54010401c240142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 338779064 1250 338777814 338777821
    0x623030a11040e130c1203051801111f06051c0303051306020715110c03091903050d0f02070602030a080105130e010f020c010e010c1407060e031602040b040504020108 73
    0x2030000d003101c59500c40702040c090001142000e05040d07070758480c3c000c5000584448801d4103055240c00255030018030380c5468072040c2808298001c04440190180c40c060420b214050b00048600425a40c10013201d4000c08400c600303242d5001c0c81c1142ea200f00007500780009925201040120710510101100302c04149511000181c0030307030003040e400b8800c501e0502c000070313558641c1e101b03984c49602c0440b9403020302109160800d00174030600c00c5103003107903010508080115050716524820055014072401502141c1010001000198009154044203841410040c0c50000d03040c02c0740c4101304000340c050381c0404504988000180c44400795641d1703a811541e4a8841402404020503501a0106072100c8400505c403509001f1101d041044030b07001a40c40350340e0000142143c01d0715009030745990410b10b00094181e800350f0001060580000903954805007864850014040403465a00c240004106100c030000c2d900c50809602d8000c0e81c1c2881002d20394010482250001c0f20f00034003240c0d4000c00b1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 338780314 1250 338779064 338779081
    0xb0301150608041b03030c02040e0d1209080f07050631030806060702210c040515100c060c080105010906081b033312060403050706050c0d15062303 65
    0x2c0980080c0282c0d040380a0ba890189070400c1501950410b40100700d0390782030310046003800c0c40790324104000003020b00703460510020000c2c0440076440303c04200c0c1d6110cc60311402d01c01d281089582914000c0c1203a035581c01545040c5488440131909440000240c0050b0207005c0ca000706c41c0f40829814600100b8000080d60b42540d0545029240b1900000140710750401a100c0312000300804041241c0b0110402072521400d10b0080843e004a004a09210a001d82d080a201e180010380340c0c00c84104c401203c003924212100410440060700b0b00d0701f030075103991005420101441c16030b00c0030f0707954840850311050161010803060b14580d5001081402c50920a0845c8002d16000049888649100208410710304e030000b80c0e01240141c01000403a241301e085c501400444500411301c40503018a25041d10003600704e01580724050301e080d4580c80092245c4c0800300c1210160001500704018041c038592095035448500c0c0036450208020020142c810f00000626205a03a080d4590300c2ca1039480059 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 338781564 1250 338780314 338780327
    0x503070e040b0c480f0309100302220f0617072709020301090b03071805040614040302030a02060a0b0f0f030a060c0c030e0109051503040512030106020a060b03011506 73
    0x42c80401c000d1085100c0040e1141c841c803841d10003160741d03440d07240c0b41d00480c1c03a01c4d042155031002e003110f074002a081c10002802105941c13551404494122004100c26801c0d00a0f11810303942110f103851240d40821a540740301884026265000c6102010ba07803100d0781581d08480e24107200841c2520440061f00361072180c094074036843d240705400e0041da484045200118413958101030b6507145c0201c0103004084a92260301500c0c00218010310388145000303c2402e020076a03420210340305440710001340c10710005401500a0001045110b0041c1c509400c000303440382c00020f0508014000c200200d10120b00d0382c0902001c24400034402080741c031058040040144402841c0e5415000c1c140010010501030300c58090504241d4480e041e2602c480e1070024610384001c4240e6040c0291501c0600040c1c4540404541d10f5030801c1c11a0b60b25100d50a01c40c1c9040c5002c1940c10f810200007001103070403640441c001d0020341c40723800c0510642510004160070380b01040559a1620b030800010004244241e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 338782814 1250 338781564 338781577
    0x17042301090605070c05120a270b0a0302040305061302060307030902040905010e07030c090606050d020a020a020d03050d1401050312031e040308181609020f0f03040b010503070e040b0c 81
    0x14076041a50349010030744604403440004982820700c1d031020706c801440301a961010701d000f4203103405c0d09800094030480d45131a1020f1054641c260140c0320140c682d81d03c0300134100968210b603c40d0007003c0001c000c0c0d8081e01040b2518010000480c10900d4071301300e2101902d0340101191305603921280214001d0070480000e076402a161503400300445c0003032041c05074004883c0094400e8605500b040c0d8001015503110507921f40c40c241080200d140e00c10b003501e400000840d005682d03442115412464a805d0170006075015807110385e00001c0503084030050048102c00407003480700d40d440c040041070101d03091040c95010380054001220001a100007554171201c28803028440303140e80d00e05c140c003421042350304502240b1180c0a2060304445c80c0c1e180303202c00c0d640000501c9500c00d400c51101e10140544280130780907401103250070042c0c1c14a030603188489103003a041a124602414002c403421028820305000e401601400b0600c04c1c1c018403414480e03900007070031b0040740d20b03040000131a541c000c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 338784064 1250 338782814 338782883
    0x102090d060e01060e010f0305010606140315010c080d0c02060106021911190314060c07050c0120011e0e010204030c0b0d09020409030e030607020d020706110f0d0f1704 74
    0x28400882c2000342c85c800503019040209804040d00e0441c40c10500f125507a4001d80c040c0a024520f01950624000c02c07258170210181640d004152800e0041e04d86142c02c200080c03241001184041161a00c0e40c4040a80600c59003222141c1e40da500c000d0b81c941c0003114161203260202c95542c8081503617007a0302c075480d030005004042c401c541d071900744a10380e1013a0400c5801020342404a10078074420040b103500070458102661a0816564803156035021904040381408a60b602c03010310101c5003011140d422040d14028806a0307152005107401510714a01002020f1404868000b0704030f051003500c040e25400300200340600c0c02e0043c0c4640c0f03604a80c8074030440c0c84d20b450751100180c03114020f5448040c400d4807440380c07800c41a0f007098102000108400119030100f041d94202560000f060000c031107090030030f40340030100b141406060110103608100d561007a0b00000100550280800c541c1000c1d40c0e450702c0208107901914210808103a80280c25282107084040620404840644540020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 338785314 1250 338784064 338784071
    0x3040e06130e1606090e0a180c142e05130306060b0a0e0d0309050d060b041815060b030a23041b060302040e15180a0f0e0102090d060e01 60
    0xc140c40300058541114800b8101c1d004040c00d1070f0300010182403000039040300c1c208003040741d003400c400d9164074000402d0b14540d642c85503c901308010240302000f803031341d4012002200d00e50300d0302d4005410201007400580144c3c1101c001440640d01c00500742c82e410320100403c2e440f00540c140032655504001c81c3c1240518091b00c0000004070740e0700c2010f000345000d8107031541b41c038078907400500032001517000395005440b046529800641d01035610002e50703408407807488001006082800c020315640340f409130018078000e18038140c0414049140c0605100d084090704580c1c01c45850410b0700c00501c41c6031840801840810f01011260300009000c654504450080e4040245100b2141000383c60503112400130302c05181140e039006813841c01034041c0381800c2d0300e444d2070851944458000140b640420031058904502c00e60740c0e10b68955112a04044001d0680c20410110b40050070400080ca803805e1038941c4002e441c0d1018002d580d0503043c000c00c0007100c2403030768a0f0280988421000c44900f03558 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 338786564 1250 338785314 338785339
    0x7020103051015030506210703081608070b061002071d06150a031506030c0e060c0c060304060e10230910020c030c01060801060b0316021212040308061203040e06 71
    0x303d401040041071502d980115031420320300c0a2040700003001402d0019010b07007040d06003104000040080c200e940c096805680d0b48502a4103100d25042e0300001000800005054030602080707071042405100304541b04200325001070000c0c3d035030307100e240300308084450002284c506280311002c1d901d80c051405400c1c01c40c90504050700100c2544114490b03004280d45580d1159400c40410020001d0072081c1010000289107080103090040700c84c04080c400e00700055a8a900c400600041003000c401901e030540341e0920785442ca01409060448052a104641d020400702009009603604800041342051840c0700d4204001084503005100f10f220788903000030030320340c0b900342c0c030003003000340c140038040c5803150640d00416094801551000605038100340c01030010020940c120b81cac0180c111000081c4846007042c05034140303104401c40f03420144000c2050344160041c1c118052003503209589096030b564500c0100010041741c40080710080c0d2051105000540e01030034456080740008000040055 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 338787814 1250 338786564 338786579
    0x71d04031b02040f1b02280501140f180111180a03120e09010f0b040501051309150e061e060a030e1c1407032109020d050c24070201030510 61
    0x1045034080380020740e6212403000c1709491807480c0808040051001c4c0404813175054000c074140c40c202849460300148407983c40b04000095016a40d00c0440c66046e016034a042c03c2c07514100d0b24100d9504c80c2a0b41c100f00301000700300301131280c001c010011030100d504001c66680d4005000882c42050750700880d0b25003021011500c040400580d84a89642e014042d0340031406001b450300b4181d110201c460782c2158148035800f9448152f40585100f840c0007500c821203015411415141640801d82e0a0700e450100002d20b0305002290080d244201d4250046d601c4030020310400903071281e4040d03241609a40861080e1911800404a020b801d140c0072642c80f001044072030804181d01e200e80e1669a0001100e4445900005000c1400b102035103c142440100d8901403d408074070684020408112a9240c08141107980700604240d005042200039500e2031601954880c101001d89105071001442d0300c207076400307003801403154880c01c4115904008840d40194081c1501030301102620b00703003820104008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 338789064 1250 338787814 338787821
    0x6010f0b270307030b162303070512070518091902180603090303070207210305030a021605010603020f030c01090302120a0209091b0d02010807120605100809071d04031b0204 76
    0x70360140350303019083d0911070b18806c80048044070140c03d1001000700c1318200c1400c2c0034441d804450401c4950b031b170380d44d5061088680c0c3c410038005501c003030360710703802e00c070040c0c1c1e100f0090100c42541d41e55500303c001c051001c0101180d0708a07458003007100c0c00401503120f03260540282c000c01203140c81b1401403800d0000054001d81040341c21f0082540040204030306942c0c10406500203007a4407041e07104000744103c4c034040900c690300029003401400408641c070442240d040351010209190701031400d0341c4a02e0941d0180030148070591143c000c0c4101c0e1255132402161000f181036050f15580790103482e50b4240030b00450440303e1880c4a005016910025869508d506441405172401608511700c60a007184000503070b00c0c01c450700400c602181040145d821802c401c0d00300c1424186984040d42001c011030181c074198002c0b942240c00071228102e210b41025820380140c00c8402a102c4181c1c84001c10a001101c000c2505580c0c0d202c50081800300380a58094100800b011b2801c20080020341c01240c241e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 338790314 1250 338789064 338789069
    0x91302041a030406050c070503031302130c0e030d02030a1b0501020d0c08040c140d0b3c010e0402031c0302220815160e0a0503010c0e0306010f0b270307 67
    0xa07441c000208000c2240920419611100700f00c0d1490a10041da00c8940c0d032030000920503070615000b0f03500d00c0207550741e902c4c0f00e00030021040021f11408840c04030040c60720300340c041c000d4002d1007818502200503001005441c00400903071f8400f0580310031741e0030b804068040420141c1c1d080d5402c010110081e05140121150031400d41c503980c007075003030514140302c518145500400e0f115240300030108090340d41e5480d5008031a080b12542c00580c49403800000c030804482c04404100ca4042401075110f83d036125100014902c0b181c01c10060780c0d80365185030110100b1140250325410110251040d25000211805001c03224070300141010b0601880c0075030542c4a84050070908043d03641040640c004004402e01444d00e01000300003814500d4612034540b0940340c00c0c50038802c070660b40040030b440d8080500014a0300030700a10800c42c0c8000c0c00b608401120040902a0044030000b042a141c4451078204464160280300e15200c100100c070200072a5029950300000316100203030300c65a0301000140b01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 338791564 1250 338790314 338790359
    0x112140708060619150e150304080a052217071e06050307050f03040c090c030b0d060e0c090a051b0c0d050d060801020c0606010306230603060301090b0a0509190809130204 75
    0x902c6c58102007045042206031081943e000410401c0000166070301c401e82e0f0078007825050686c1c8601c00c500c0c0b00140d6042c401c00b034600d80b001400e4005081c504140c149542281c101c41a0350b103041d216101100c0580a14240103002042404108090303131117107005643c00703031191030f0090408480342e072214101d6109540c01e1b60015684041030003048110700c100300c5908164201001904508804104504030404000d880142d85c1c04800c200e0250500c140400c5c044010541c0a107482c001503003078010300042e00d5600110300c2d0382040301c100d41ca030318044500e007a042100404845c03980c0b4004440c4c40e406000c0140342545c0300c2000140420090000e401e10b01d1a1001820302407a140c0d00050894884e40c0c00110b41503850340c055001d910b50381303681c101001c5003641d0155495441002081c050190940c004041034031510810000070f445600240c01154410103540074100c14542038412801c61f011b003e02044010081d0701c46034038004240105004019070b0150600b40c0c0c801c4a480d50340d02084400c913 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 338792814 1250 338791564 338791577
    0x2040e0c03070801090209091501030b03070603051608070c110f09010603020d0b0103060605250b04051c08061f090305100f18051f0e06011214070806061915 69
    0x14050f0f8110302014094152400c00310b0514440b00d00241200c500501003201c107807104411a11264400d400c2442c008030041c00710b604040d51154018014403049507498007140c0c01c400541800e070b1244802c00d014980c0c5a43d595410200c544070626400860700000794804030030982200a5111642100e000b4030954400607150041c2d95070000c280d03a81c80380070504251800701c0a211030ba800034180c40658103030a000362852507540391100d081d15141400580a03092000810003044400540c8030020f44d115030618002061001c1c040d202c04d0070a452441d4850105c1d0352204208044500d0010a0782161600704841641c0c0d8170f80a0400c08102070382e521964940400c1c80c00d42c24a0f00035024013151071003003400141d0041d10b41c15150158100c4020b80d6001c0070052820210058002481d034030382038426200c40c0e50f52101121603200d1912411610740c2c19192203c1c101000119142c2d00302c5a0020140003103076105010090604001c5030849003c036054200030503c20b000c10f00000c100407140c2c542c00e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 338794064 1250 338792814 338792821
    0x705090118021c022107202b02070614030412051b061f0302060a05090a17010603020f010c0b010b09150c010b0306091204150c150b0a0b0a020613030302040e0c03 71
    0x2c2550048603114540b44118000f405850741e48911901c0c0014071107200ca41c7c0104a80c2616230400951201c4070f1168000c02c00030101d105500340b004640c202007602100d4607141e85950540b07619604540700c10a010003800000d0114035a428041540302d240e10307150f80f503c0704500718a10503018a02c10345603658406402c02114102c004001c0d900c1100c031508200d07001c2e2031680040c001e4402e070703407080e41041008918000306840c1c12242e90090030072100015240140e0a1500d4020034461000340c1c840c030a140d003c4c1403d54000c2c0d91000b1081d400c648443e803560b00b400c0020040c0d511018805170072111010002400c05041c0c07025103001551040041481031303042c41014504800600101c040c0e4102d8401003500d0b01200c003c95044a440c4c85d50f0840c1d80c00000d4042d2840000c0d10b6010b03150108000750114412400d510421048070b0450300c0c0400d50340c03911940100c1e40118078810001d0391264020486010015a0000e0054460720740549819150780820800318015030740720f1000500441032 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 338795314 1250 338794064 338794087
    0xc0f1c0603120306180b01030603020d060905010c050906070215090d200303030c070b060303073201020c0a08030406110a09080d0503060f010c0201030f0c0908010605030705090118021c02 82
    0x803500400c0b01e19007405002d05160103001d0143c01e200006564554400340300c2940c1e4080d4210000a5400400d074070002942810610050210810125440c0d442d0140c240049405082600c02d42c0c00701500d654240b0805500307120980c02a050103040c0c03010140f080f00a030b550780350660707031449101304011001e02034030a06003042000c0071021036110f0b42041c010018240d481e241503a00090f040f03900014140c480e01c01007411131188040c084d103109003801c08403480248c5003601c856610b41030344050300108510340c2405d0807409440440102074202c15810380c00705501002039034201d401003074002040318143e030022941d43d224450300804119220020040c2410a04c4103005002190908034652f29205d800a800c44a24010490622002142c0c013030a5910a030b0108140c00d400f03071001c000070244880c000d081c541c080c0c801d00110350700785079020403181004a9503004840e40034081c0030b890307400d200e412001c00440c2c1224250480d800e0120081a02c040340a1000340e104840d80184d441c40711142 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 338796564 1250 338795314 338795333
    0x10807020705130e0c0d020f09180a2a081b0f0303040e0609070801080613060212070206090c0301020403150c050f040b090a090b090a0b031009050c090106020d0203030c0f1c0603 78
    0x640e03807148180300701b0074003d030f121031b42c40c5088044101c4111006a40b041621a091000010101030a00c6440c18a104000182441c441c80804109a21685c640c0007030303545281030480d016107242c940204685108050588a40390b0b03542034010105010006980301003855500264002c0c414000c8031010b015246c1040310009420170303410b00c4c00c2240c81d810045c1c45a69680c0c042c0003000b08208680c0040700380600c541c151600100d00c84400081801e040000a5443c3d00680380b00751b41c0d0041100c01d241600d414401c0714200c96200c024441e400c5c15103051040140907080002d41449410400c2041001e508401080540300c842c500c1070300d40d0482c03000d00541901d9900008901403030251120541c0d69105030301684031445240200d003014400000c40d040c0344030031100c441600c1c2015003880810902043c41900c0381025a5880072580c0d0710081243d950180211a5025810400218641c207551400802a0094000c0d1051500c40191201400203e00782a00d195183d5a83d03014010403d110b407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 338797814 1250 338796564 338796583
    0x10209150c0705370f06051e0c0615030102090d1b0812030106020c12060615210402100203120117031b0d030c0306060905010509040f0501030b1509010f05010807020705130e 76
    0x2049032038480c00c00c50800340d00590350050031b050010110710b00d0310182c503212400c16844840d00c0b0103a00c0e44803020020703130340d04029920070f81103405501c802200c80c2014800d650350701308000c040e402c00e0a02500d4a00c0c00d40700105544011078910013000c6218030040041c090300e000b468110325965850880c0003418036040c1001da5114000411040706038600c00620960819000c40307500b13941000401c2220424410740c14503a075070f1035001100300c03541c040c1e0b03000081c800d50007a10300b40703080c4004050898407032040b000206502c01580006000802c040d201462031081c80da000c0340c2c40c29500c8034090f6500715580036007003a01e900c1406401c0384d0a9050042c070420044030305080c042da905080d009044400a801440c0c1004000701d0410006e03a1560403071100c07403050714004c1246503124142003003104012200c601d6846e40d40b400c8074840c1d06101d40a113049891100307040110b00c0c20a0011a41c0d81005000e610442c45080f601141c640c1e2201c3c8829004402e400c400198880c2c0d03050618105075040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 338799064 1250 338797814 338797909
    0x91e06032703030c0403120c0203010c030207030311090d0311102a0201050903030c0703021c0306030215041a070204141006090b1305280e18010209150c0705 69
    0x24400c4c0103500d50b5000540d010707258000d00414001c0e0070b5004c2182c15008501d03020313526600303207070032214001e4140e8003d04000b80a590305005024580c0c0702d00c1c0485c4145810107400c040f000e4104000700344180000000c0c80a07240c01da44203900e80c502c0c3e01061781d41d590721000b20b95860300c042c3c8158020f42c45190074030400500080c801403401c543c0b603507203d000040075a07200c0207001501c0c170300301032003400900301141091200003075401864200400a005d070340000c038003c011361030143c0002004041900c007190550302c5071a914403030b00e1141d0080754100200c1240c0054481d0b0310611402d014105e00d034491420460721300311540c40d10a00920701c000c1c076403240545e11000c0040d44110b000300781000080c0c540c240d0f140032441c062a002c011812404204a04112440183c0840c001900007503c6020f0902141d003400050316040b07502e4200d22560340b00302d50000c03541100042c0154803401070031030b50541c0015213940c2d6540c0d03c04102e2a141c0e4600321206100c101228030740c0200c240c5d11156888204 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 338800314 1250 338799064 338799067
    0xf1225030b09060f010e04020c070504050c1303120318030201140c0705060c03040507030510050601030c0e011706041d060604061203051c020d0c0c0204051b091e06032703 75
    0xc0c1d80104000000190029000308021101d991307469001e2004c900c40b550010307108645e0b9440c0030080d507131144068000c061003142400c01180714002000c00340d230032884daa21201150503195548081c03a1181e04003481e8103240d140e588428075401c402d0743d100c0d00540280c00100f00801800b421702c840c2c0c0001894107002400500680002c1003000801c0d503801928041c48035982e484a0803c285020b210341d0004009106500640703604480b10381005006100c00c0c1c81c2481100c00e198001c0d05d0524000203100c1c002120210040034880700c180400360000406003001a5240119409030654160541c84004d40d03032100c02803110908181c492003008100c26198118102c038070740d0b4014000e05c280c4c030030344580d44c01414624500c00402e60480b0b0303005c0c801d1a006c0013404003510300038110f000d182006031b00c180c2c0f40000203441c0e8111310340070116442c81107002a10300b2002c242000303000d94411a034144054034035a02003990f40c544c0c10045000d0080039144940740c076000c000d1620340c01604501036005400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 338801564 1250 338800314 338800331
    0x4030210060f230301091a01050907171306050a020703090f030b040803071107030c0806102405040e070c050d0504050f010c1b15090501050403050a080f122503 70
    0x1490b0080780c15680301c40180d4003901c0511203c2c500700420b40000961651078002c11328100034410241a401d504004440d5410b6079a0321700300144200308031100d00100300a2000e810f15407150400743c561045988013a0700450000d600d518084540803910b08140b95030000c0c1c207006060308142c03880002d1140320006a2502d0031961051058007014000030112000400488e260502070710a003c409407994003107504043c0e5134109074100c403845100e640c0d02c5002c1c00020a0140b4100c0e01b614085c1c1d10100c590310503c904201c980c4030b1070f403881c8901d8002c016050201003040e4400544250050603d5501c00646d002e10781003490502d8825120081800b508000c100402e8580c0032848503081e100b4280000b40c510b09081c049503861880d0a16040d2134074a41d008a011515039402d0700340003031582c1e1070701595a01e40005481610860001030040d9100071802e134005864180140410801d402042c1d05100084200e81c1d440002542c040c140e110000480c04407032030308290807103003008252a06110804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 338802814 1250 338801564 338801579
    0x6070207140303160212010f0903030c031b05090d06051f05090708040b06120a12020709060e060411040b192604060f0b060d05160c02130c090b040e0403021006 70
    0x100d544650344600e010303039000d5420b40da036621891b80b40405d1030b4001d2100264041d801d0000f460342c4902100444e1a0221050b24035100e481689500d00c81e0800c4a0f2610749005000d0310b00b40c2000000c0c6030b0100f0220309890000e0268082d440c0101284035002d108445030078604030988203140c11460103000c0031410420380c950301c034420980068100c1402c1d002a190800411140840300030b02c0c50041c07080c425070004102103801d600f003003115aa400d50791220740340c80500007903501c148600d070100884080400c202d89000e40c440800ca03000031003810300d059566506031015801c6a44c0408440169007402d4400c1d0b9001403004041214a84d0b8000c04200c1614980d103140c000600042d04c40f0b42c0e56118868102119402482c0a80c0014140ca4483c28416203081c00790000301c1d405296090885107054055000c1c1a151083c0303079004195400c0e845c01800074000411002c00050100841260700140c50031b605002040a41030311014200b032450603040c041d2500780020007206819103001004c00141c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 338804064 1250 338802814 338802817
    0x510030903090605030c070b01060e0a050906030a0201141b030d27150f0618060f0305120a0201060f060507110d0804050613030204051005010f0f020c120a0f030206070207140303 78
    0x39189400c0030b680b00c6d2100d500107441c600940000a0400000f00004502150031210032030304548201c40b0700100988403800e121001c0020b1ba80a501a4040c0040c60b0044d0300417880ac071880f2501417441d5040c0040c102d004814140c410458401d5a0000038105006a41c0b900071f06c01d0042040e035803a00320340001b814091a003018850003901504694246000d2030704c01d41c00c40101941214820b100058695004202118102d552440380901d494000200c02603210b04a8088a802001418215210f20040f0180b50310008496045560702c07a40890395580407001000034000ca5550151a20010b2401a105450b10035210344104c40c25080c140010700818205c0c0c0590b50103540a980310300005030480c0f401055500001d600074249001c02508408a0100e502165800d0b03035140383c40300d000d00c0705852400c50900c40e17200603001000314100e00d040901802e0300c4440048100c03a000203968407800f000221094040300103810060921494990400909002d44404500da5100d1190100000d641c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 338805314 1250 338804064 338804069
    0x9060c1303080a051201060807090e0103110f2209030e030c09010b0f0d051e06090c0d1107020415030b0c04060207031b150f030f020c0c090a0b1207051003090309 71
    0x220302c00000c103942c9551040d010f5554100c801e640303200c1c403542c4410000e043c1560450702040000c801d1640014034116400c04103041388d400c00700707040e00c003055042400740c54015070319940e03000720480f40c1605030303646210b188400d000060700c00040c1d206010b181c000c00682107030b0310441c460347c0f020404505036030f505154a811541044629945e4410001510040b400b616078407002091a000401c001085200f05160048880c0594040c0595803201000501e0b030342a14140b455480902c0308c0d01b02010658484100c0c0041103010383d0038220240d002034140d070f107862806220b81d1070b414810070421a8810fa42030b040001201c20508003814030034001e549001d5484041c001c003150f0001c00042584080804029101e1a030f004040740c40c0705000079020300780c01842e510000e0b240c100300030150740d214400e031150140741401400b00c0c03010000c100908040060a00001c0c40e54030070240c0500d0795520000c40704680b03200040c2154903d40001c00a10568032070454003450308203600c01c40065030000002d0305 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 338806564 1250 338805314 338805323
    0x60306090c020c2116030203011d060a110d02160c0506030c0f0702150c070e0709120204051504020315012304031709091e0603012702040212070809060c1303 69
    0x24106548031340300e0f030060301007007551140340208405c0310080300307200310010181c0e40268005e00c10501411150a006207aa1900c12005e40100300415070a00305a000b0024140300340c0380341800e200c9103031842d4040760300440b50b00f14070720840c180100070840c4500040c00201000ca92a03800d40c600180610000d109030102c500500340006100400c554800004100348194502c0543d03c400030a42d5103503961f00701c0c0c001c001c40c0724551000a4022441440401e082c1c48034000072a018011690901014050203054010151007100002c54251030314405148652040c0c40c018a62503003080001d005421040c140302034643c0044230480260382c40b00704403411030350301c0207080712500d07594001c0c1d045501136440326a52100049090050314201d04200c0040c0e0700510f14803c1c00c40d1600000c2500b00c0d000300308040d03503042c01d00200d1202c1101e0140c4404c0d4050020344003515080f07a03451109945801220004089803070701003401409442002040c3e0301c80c2880d600585004a160000c4070034840d180300003403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 338807814 1250 338806564 338806579
    0x306010c05030d050a02131403030901080702011d0d09080703080315011202030406060302040501050f2103040b0715050f09030f034c211103060709060306090c020c 72
    0x40007020002c0303c84030b400d642c03010071907814503280a0001c3e502c650701c00e0304d18901354540442e403a445058800702020006000714070301001c001c0159410030b8020b15000965580750790046a00d00103800c0d48148806880180c042081000f0340905044801d42160300c00b6070000200f8000240e054080300d8111500c0120300d06074180340e900403100c200c4200c1903003400e5800031042c00100f20064000d0403c2d00d100326005d010603070f283e200740041c2c1402c0d480159400242107800c8501401700314000c000152030307081544c0c030301a19070001c3c0740c01da4000b22040765002150042c0c240344d50151b124081e000a9246000074003414451202e40d541d015542d015218a9800404a54040443d00e0290700701840e00e041c1070307a106d190800c0394031186507040031025522003110710039032084070007005502500c08101b444010750044800e642521484907070102d403c6458011400c105540030024a40b00b1350b0305a888088080c1486001402d940c01580820788080c140f4800240c4240c020400944a800541f40300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 338809064 1250 338807814 338807837
    0x3071802040302032e02070206030a09020f0d030819020301030804030b0c04050901230102190308040f020a08030c16060c0210030b0a123c03091805090f06040206030601 74
    0x90000e1103150b00003549403050340300c55441503e1540100c45180d031000032000407140400e0501c001c0e80310361000203512290401c0081d42c00c00240c0d00c5103001500103059034464a04800125250640004066011a038804200320b000e40000300d60848640c1f900e03a0550071540340da40e603403040e401786000003840014024001040c0c81501801e5400400c0004c10401e4156900c185c00001b20b180c45c0306901da00f0b19584a8080700e9400080e0340f034100c501c240403520b12091642c0341124041006481124a00b1418205102598903241d418026094410156540e4001e1401c001d01d80424289102418074522600300080c1c2c0c0c02036104045590142c0b210040004401001c800410080040540c0514030a0020401100703030211250410b11800306203802c2e0340009c01d00c0903500f1492240d142030a000d4064416501034004c055041ca40c0f10342040a8004e4440300004801d203010b540703094441d6500c0d0108020448204412124000c0ca0409411241002d4000c00c0e20b6100c018095418428004081d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 338810314 1250 338809064 338809109
    0x7381e06090a14070903060b01090b0d0903030908071a07020706021b0303071703070e01090b03220c0e150613140a09050f01050a0e0f01090c0309050d0c0615050307 72
    0x140304420b110100f12182894580d030050300380e00d030500095030a140b40080c0100070303501070120801900c1540b12980e05208c4c540f0300c90f0b8040c00d0f46403c00c804041c7c550300150f00007500c1d203010300a80c911440310102c014041a00145021000130300c050210b52080303508015440d00814412428404412086400c02d40354020a295100b1807400600c0c0b08810428852460703003190213103014081664030700803c0c0018000440d00600f0074058800b00f0316040001c120a0030311400c48495440724960605015203060704c4034102a41c01d681f20b081078003140c004000d1610b65038110700d001d0400c103c6030f0a082002c449a00c20840f90b250180481e200e44090300d0124584d2010412001000e0317061080c071003442e2041407070740c00e0403080c480c09004583d2000081540600a070f00349108a0703400b181410300342e10303001c6a80040c007000620b44061550315415540854010720082c2d8010003282c994003400a5240b502904440e0080c041e22404070700d4000c18000351340c01040003070441d1307040c00c1100c028590030201d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 338811564 1250 338810314 338810321
    0xf0c0306010e0d050601060807030908090d050a1a010503010f1a01140f04140f01140703050703090f0306050f071805190b13061112030c07381e06090a 66
    0x35000e9003c1400740d075107802c010002031054180d4200b6074407e100e6445200b002d40a035295000001d0100e4001d01c48070f242828114519070006000350101d4514040c00d44400303502038480d003100c1448481540c018442410b00740070f80a014031201c1001c100d081c102050303400c1d015003a81d135014100003581c00e01103003811415064515400c1d0980c0f125a40f507a0b40d841604103080000ca0040c007a41c00401801c00541c015000318681d5002e1142403413a00c10103039402c0310a648000402c4090020790034000c9070030300c2ca5521490146214400001717603410042400b8840d004000e1040c0d0401154006d84040f00c01ca5045c040101d807010786625410f00618624120140310300d420001c0048008641c003d03c1448612a110498200f0b440c0c0c04100c0c144032016035250551014003003c81c440c01c2000c6041c0e542402c004203866402035001414000021f42c8801d1503a01d03c0000751140082800b4191354141c4080c203843d0002c52101010911000b00032140540c00001010f06103c2c000c440001070a50700542c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 338812814 1250 338811564 338811587
    0x11040507020c1005120f06060703080a0204080a0c0305100911060904090209040c0302130207080406140d0603050c010306240c0f050a05030d060803130915180506180f0c030601 77
    0x5004074220036120b10f00801c96088483c0070900a04024041a42c000044000d1401054003404040c50030450782c0781913602040260400c03181c103500b004001010704052107031034291403140301c1c0351010a1540c1400ca14004c02c1121000000d840c042c40c0d0703c002900c10034400d0619400340e0701e0316150034110300081d000380307000c21021750047c0f0888200300c1000b01c031100b00b01c15280b084415440c44803a0350a01c80c102d00030302c1002814020100300030f110391030003401e62245c06a00004000d01d015007070740c1042c003a100c195208441580c8002403c043c150b070075024141c0034110401240c1c0142420180c2c266806406003582c03014060311402034000c3c4864000081c110507080801c5590300d40c0c440c0341c500c1d0307264000c1100700191b91a00300c000c1511080441160003400402034003000d55420f1a40303d0004020b200020b1401c80d81b901000910341d1b60964440c44500c0700e1800014041c6404002c1c000b0711100036031614840e4100f0400c106112a12110013500a07141c20a01910f0b580c1d1030380142ea0045c98031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 338814064 1250 338812814 338812819
    0x1605030622060518060a06110703240f050106030b0f03071511150106120614010e12070909111005041202060d020408030304050d03050907090f1d0a030201050603030711040507020c 79
    0x2007511120344a104d201c5001e40c0c030a80c0e008820680e100801c5814401c0c0362001c03030b05074004590400201d210342900c4d200314400042e0141e030387c4c030300b42000700110380300d814030802d401d44c8a40040000b99003500c41c000f41c4a001303840a80600d2610300010381c48180070f0160b050b0902c070032440000c0d01480390702c2c22015120001c048802c01c010390031a11115410034811040040e00790302e60f80e0010300390350003100120342002107580c05000c035460040d1a210010b441107038001908100c1009185d100b00800802000d01d843c00103141c0c103540c10100008a10f1140310380c000c40c102c0c0800311aa581c001e04031341c225a805013010b414010148001040c9104101c00f03048600e0000c64045040180400158016403044080b100c401c500e00400303400b03940c0d0490341e00800e500103c1080010801d0350304954201c0c00814400990b60481703901d02800d00c861030102240690203a101d0b2810036030240700d41c80d0800c4044004600700030075030b604d150704451010701140c0165164008581c45d503000300310044552000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 338815314 1250 338814064 338814079
    0x90303110307050f03120601051303030815100c03020c0d0302030f030405030405101d030a0201120c031404030e030f0705060f070515070809071d061009030f03050316050306220605 79
    0x83c042100d503646c0125501c8400d410203000400c0f500d43c003e100f11188014040620b90181d855603c055078401d03070043c00c000110002038411a8240d560b44030106000a441e02c48003002e03400c0b824020700e000e841079801da018000d061451408245c001042d114030b42e0008003015a00d903110f280050a40c0107503800340350002c2042240b68000c41e00300c020100c0d1407004800c030306d407100c400c0310805030740e0480198068082040d4004202031400c0a800c600900d0380c031400c000c2801d880c03040b5010000b100880b015000a441e0101d00c1c0c03100c0c64280300b0023480701200d1000b080180c0c1417000080261241c07280320002840000f5400040000c1030108110040d050070401c0341ba403a0400018042610403144030300785000754140401c8e52030749080a2289920120b103109019920070080c000d5504040792202c060200c2460000001602c0014058000d4402c0d55065282d0078011205030312034204a050310107000d0103004012140e00e454000e96000d0b84509032140d408a00658014014421500140d401045 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 338816564 1250 338815314 338815333
    0x90308070309050112140613060b030109020a030506010206220f0b2410090e0408120a1a12030703120f0204081608060601120e030d0c0c06140709030311030705 70
    0x802c14403080c1129001e0300c070020301e02c8040e80035000f1200d00802c0c5481d500c680c1c001140050400c101c0700544105405400903603e074a0301d00000082e0400d83c4981c03819a00010041100c1381d042c000c441d044102800285414107150101c0b08065182282500548001210b50014040e0710804041c40e650401c0702a00c03141052928040381c01503451010051316050b08682401d824103003140c551400300c55844190303d900b4590010f0000001070801d603151075007800282d480c0d01c841d080650185900d004005200f100d2044805035401005118512a17102c54481034078455022080714201703545803410100036500148000e00400366000c018900078804100810b00700000038034407440d50b130000710105a5075501d006039652288202c4020740000d00c08406800089099049030b080380d402c5206803400c000e110300781d8504603080d081d41580012440c1420b07030b0070b11400348500d00010030742c8500c020f00d5107010302d0050300441813032100030108100c43e203007a542c0c06014815608030560250540b402c1ca603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 338817814 1250 338816564 338816567
    0xa08030f090607020f0714030a061b030e0105100b1b0f070f0b0f040b0708070f0812070215060f01020c030a05010c0f050703020c22050a15050d0b040b070903080703 72
    0x6a044850035094070a880200e80d0984c00040d0f48501c51030003034000d04506007014041d8001141164459030144210f420844c0058114001c014100000030075a005030190030310700070151400400e000401e0792411080c4040182840b401200380d490b4401c0c482d580e01e00c110749600c8501551100100e0360700881d002c0e040148000700300d403011101c0360b041c61303481c0e5521009441264030400740182c800c40c0c0100300800c008200d034005040d055004008242c00c0c00c9464940208a01015008507407a420009810b03802c0720f14903198540201040c801803885154140140841c1c0714042e1132148940343c0b00c101c440040c0e208000008003030b40f015080d00d008420382d1078024041e01c01e01a8682c01302d041c1d683c01100703507407107101502e0080d5015401041c0d41d072221f40030f021000c0c440302c00c18500140252820030000140740966805445500d20006403000c0040c20340940c24200d0300004c0c82007480340c0d1810302040104140341d401a80020746e01c1d020b500c40c2407069455012aa0004000c2c4801168110034076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 338819064 1250 338817814 338817841
    0x10e010f0e0309100827070303090b180f0a0305010f0e010b1002030d02071a1e0a02040302060301030803060a0e0705210405100f06120606050a1d0a0507020a0803 71
    0x420180034140464920090065203074020801400d070010540e520b108800c601c070704000340d0801441c180c1a002000c10b440044800008000d810609038003030b03e810000c06038413916490040c80c0400d0002d0403c003000070190608880412110b10620300644042070f10395a0002da40d0043d903001c0c0003000603901c9080700501500007000b030710b0442c0d4601004c41c115030400e0041d4a06500150303020b545001c110750394400082d04818001d60f8420300d60840302000402403048540103a5188450106407081514800064003000341070760039580c018441040107848000903241940e61061106850365105030104940c41d07969031140c1d808040c180148002250000012b1a1044901c01d141e140c0039003520000088481c01c2d1402082c9501c05600314407010360540c0700c940c41d0110300001081c80e47e980c6c01d0048c07071000b68040541e8090383da040704000c0d03880c10040240081c0420030900f11080681e0b446600d001600400c0001d1543d113802c00182560b00c02e115514403a03500c442496200d0410510000d201c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 338820314 1250 338819064 338819081
    0x10204150c0c050402030631091110030615031a06040b0c120421020a050307090c08010e07020c06070303090b0c09030f060421090f061112130501050318010e01 70
    0x4890100c0c002042e0f60074140201c03171003005c2c003800003925214020b00700180040791003900488666801150000754000e400b5440c00c16028010490907070034500100000d4908401d0744100341b51811004210b1400300d011052100d040c18240061000c64640300d06103120100344645600c014001400315006031420081c2010814001c1212910646c0880c03aa01c00c1c0706500079140c05904c251325050241c040152410704091000d0300d80101150f551000c20300d000036070f4110080c10b5403580480054a40d00407001e03401007c0710000000c02d400c142e403002e03407144180c28256004000000701d810525009030003a04281c2e0b84041686940e15005201e4003180c0c10203e503461190084c8a18504d0000c030010320180100d410940320740001d42001c103141310154540500509000c1e40420001e4a03001c903200000080c503d07900c0b0051107102c03148520f801c0181840140d21070240c10300c1407001141c020640501a2042800d2469403a2119841006482e003011050344041d820500b9440c031103101904a41c28 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 338821564 1250 338820314 338820323
    0x10c08040b03190b03030706090204021e0903100911012a050d170f0105040f090204050a0c090503030c0616051603170709030b0610030902060c150f010e0711010204150c 74
    0x3d440e00c031201203206564180043c194141c0c000d00c03e6001003042c580c03004919900c020401442c211210440195020b2088090381500e074011418610710b0400388551100500700c03600800681d0f90030303034410300c09509072580c4604111039004c80221003000072400720754049e5041d03a10011040a0320380f00d0b0352965007480c03a00c0083d4400100340c030340c10484002240101020244550b40342e0070f20782030100420309e61458030513030303515a40094090b032900d1240e07078000e650300704020460300c4c0d1040c1e024044040c00d5000c00d0095000300880c00c00c0801c0890b601e900061510001c40705c2148601c0222418061304484801c0c46200c00d500b00c04042d00898a881c031598403c24a1025a46055007a6692034107888007501e0b6040c3c400c0015100c0c604105011203c071040e040c00200c0c20001d80104445d41c00a048030704181d0303c0111110714403e0900a041d5003d50241c107001019818401004c26400c000790024007404003242c60507a0703500e0290140c1d0702418030300b6503200c3c1c9800760760740051455011910685 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 338822814 1250 338821564 338821591
    0x705130e070311090904110102030d020a0e041b050d020304030207171f0e030702060702031e06070e03060c07140c060c030406090f03020907080a0204090603080a120510060c02010c08040b03 83
    0xf40e6400400b0b040e1075078401c00402c55980c03030b43e90b510b890608084c441202411030008100310317800c12900b840584880c102d981c1d10b20694031030b0201840101c03500c400800011100c012580020341750701c00f040340c0c081403810034003503140e89481c030301070340ba08800d5007102c14114800a24640070180009650b40f5000341c50f80d64840004138682c0090071100040b024070400c1c2c004002d003d02509010000707021262014084695000702d01c444407030300724104c00c0102e6041d0014000e000c5082d6000c038615520007411800b42001c0c0c20641411401c1d0320034020002c00020214450300f036404418000007501c0302c4d01401050b034562001d08a81c1d120341c014000c03e004100490008640010001c0c15001580c1d809080c0c5038480d00e8240e0240c4201c04002c028000150302000085180d9085028180046221b6105a92113511020001d451000b44c0114800d816141108206240160103031050482d0703100c1c00c04d128500e0850004031307446050180064014200024001801d4030300c080211f104401c0b000409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 338824064 1250 338822814 338822831
    0x3060f041e15020306280504021e1b2112040f0b0a02031f1802160f0309050a061707050309120c0604020f01050a12020a090503060406060320010909050705130e0703 72
    0x1c90610b01c0038011b181111125609000d83d0805a00410306001040d5036005070070300c100d40a00c943d52100d0300280c6181d00306010304004280401c000c1a201c980c43c0c1003002a0440c29800920500074220500c1741400e1510128043c024280180b00c10550820203101691501c04510406541300b96004c007031022400030740c0c40c182c042e43c1041c04141e034140001c1000340d14000204e807000e901b0100d140f1070360328104003489000a444501c0b10030101c0c825110482c1b040c1c070b003a08000c01000164403040601c45800c05190f00c1310034a0b0101984080a1704110b40c407525400d41c164501346441300c41b1141e50200185490310407000003042403046108071848524a2000c0c001100e05001d07048210000c50007505d00c12203111b011b50054401d5041c1454800901c1d5612000a80780c03020a031801c0c0c402540c4d581060040c408820103d401e41501c40a852203400321000009200002d50710903d0315403070740c90011451661141040ba07051401c040d198111031511160306400581095544402007031074942c1c0c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 338825314 1250 338824064 338824099
    0xe01090b1911180a0b0a09030515040812190218120a0201050a1b060f0c030e070b160807050a0b01060e04050618040507031b06020c03060f041e15020306 67
    0x108240128a2118103040003c0700c02c031841e03c41e000e4005164042110000801c000000401030040611141d581d8481c1d140f86003815420082e4020002001c1216007003004003284410080744c038850b4940799234071440c5c0c0d030703400b034810700b01c0b82841440b14181d00004600c2808415100308850005040380c40c80c2d100c00400c184140d44100c1894000e01094060101001d0036025614034604807428030601a4095403a981d200e048511801901920a507203030240c01d90980e062080c414403001d4800101011410641858010f0103803242c0001c00c01c1812196004000045003550502c651180807150341002c50b00c5c00d0342981d0b070309000d1074000070411035224046181034080d683c012900507003075401918100c1c1410320b00c184010701c00e56040c03007010303c0000059484030365039402c4001d003842203180b1424460000c0c00e0411010310203100fa80f08030207000c4119001c1c03064a4005510100c810300d01107014001c500c0030410200b01070170114452540720325064450300110f120f404200c40483c00750201360032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 338826564 1250 338825314 338825321
    0xb04021614010e01050f16090e1603020d090b060310020f0405060f0903070f0f080619021c06091a0d0f29090a05060c0c10020a030e01090b19 62
    0x56840158030890310300c10210710303012401d20340040600008107500810080e601d0955600740c82014410a0074400c103c14640c89607142c40003144d4a181c0798080529009190321501009001440008006540a10141d02940c1101c0c1c0381c84d0030320010300041c00981032242c09510100d40850080c042d0240182c01c82165108840008080c201c0c5241414201001d0100a03081b00c2502c6110f050200040201039500304594030090074005017400c1814104910b0240051481d400000c159121201b80400201484d80e2440c0c42d07030b2617100040e161003c8181d140070106c0e20440c2c1503a124131301407001c10044002d800c0300c059070102e41007e100e18a008805c2c0851130111b2071010306083c40343e940c8a0005030035090041c20400369110b070429160824001c0d5414100140d03000e40145d03100c52440410040305022481d441511050005e06020200c1d10140d20b0741a030446e06e203c403a03400a01204414001d40c090b4201e040e03004000c000040306450b00d24007090b0f09403040040d0580303101b54105154002d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 338827814 1250 338826564 338826577
    0x4030306051f0c1104050f042001050702040c02120c0d02121206090403050d020f04050f0103020301052209080301080d030e0705060a030b03030405030a052a0d021002010605030601060c060b0402 85
    0x10103209000702d8801040710b103122640001c0342d8401204180072502d5865004650250b00d905c82100001c0c101807030040c0b0103805034415211100c01d016031404540e07803c9400c3d034000980541d00410740804c000380403410445920184207a413003000c40c03012140c040c00144046591125000c6890321420951030101030300881841c000e0415020000408904228001980051180c02c006003070482a10010007a0703084a00d10b0b031810740d8041410015450592100360207400203003021480c550508011030420200c1070148080701f0040341280019015039030000340d1041e0000e40c155125611500e4040e1140388016201000a003860089003503510b01041c0c002c00c45000a06c0540362040e1418168041c0c01000e010540c140001d000000c0c842c3c5052060546540c8541c02404070340e651b201070040100e400b840104500c3d401d40c20b15043d02d803100b002003140c0a4046804035a00626864101d0141c0601e800c030a415008440c0005281908241d0b40b4070090300c90070050100112543c140400c9000c1c20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 338829064 1250 338827814 338827849
    0xf070201061208030705090307090f0b010801120b0f07020f0d03050402182211060d02030612030405031b0d020d11030d0e0d060903050705060f16020f0607030f060314060403030605 79
    0x4c2012078a007a0054000b0300c5c0d6064094141c981d640e5440707490904441c00342118403071141d1034050385a56503034410401800f400c2110145100e41c8100c0d1900b00465100502006910080344081401075008001652407540760504079410344607058800ac0142205490490190f0b103210350030111440c896001c07c0c810140064606500d450000320120000121007007a10790b51290078282c07149031102001042255401100540d82c2e0070700380300b8000130044481d10580705801c10300050041e590701107041318560300d2800200d1914810080000c01400d24084029031241d03680d1031220400400f10803104102c4411030668002c000b480009030f41c038900400c400f83d40501c81c4440320780014450790141f40c48a000b49469410003070103a0301c1c5860f0000076183c2c402c0c00b03003100c020411030b40d203101e11411020700c15102900e444811060f0319992610b0241c03004c8103042d10381c400e554140200d030340030b0030003540c104540c10060b04c1e002c15000e40320107081d0360035000281404400705003130030083e07000c10344286034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 338830314 1250 338829064 338829067
    0x11010f080402240c030f040819080702040207080c2a030d020c150f0313020f0d080a031a030106090e0606090c0f0a020c04090302032d0f070206070206030f070201061208 74
    0x6400e40500420140f080e28080c1d9a0602859201480400140014100e0030502c83d903286d0a1400b210700c3c01000d81c5204003c2504295008001514003007920074043c0d0648015131a02d106207010308850003001c48452492107110065514048942080c7c600c0109450400d0138620728032040c5030b110054003810902517402403c8103081418400708400c9206038401d081c50a1001150140c005540166680008046490500000d601d4807840c3d4041c1201d040310580700c0b0310025030f00c00c500c0740901214003060581c0d4501010f4a05013a000c2035000d20b2004008100c001c0c5c07141018001810000341c1001c2500c104400980c0c50b05080302c02d00e00400c0303640082030500100c01c54070f2245601c18950307c2d00318080e203680c010141e200e50280c0302215200c1d8000c3d540743c22602010a00000c6622144d039814505568064483c3d0b1405045070b02810800301410f5845215002084440c0f1036010000c2d042000041000369000d030381548103000713421560017807112650358440480414580d80001e8001d010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 338831564 1250 338830314 338830339
    0x1915050d11070b040b011d06060a0311130e09010504030507080a030e06101e150309020301020903150405070b0301180207060e34080709090c1211010f080402 69
    0x4802404614104040204000082199141d915001031504580c651600c809201c00c0288504c406400350441c1000c13480c06108000078080b001001401c0180184400203043c00454440c0c1c00200c01d0741240180301c1d6480707404500b0804600c50328821403003c0d2107004082403180106000c0c081c065901a901c407428030022303807500b580d244c0c409a140c50505540c0c6800c02200082405460311880b44c0844c1d141c112807070718180321042d2180c2140340000c400944070501000c603098200d240c03400d42902c2c000491070716500c007117070092280c260401d500d441100700f20a980c100a49149109600c141c01351104c05680c0e807800002c40c0401e01034910010507503070005540d1111940034006050217003c0110b1803041e045009070402d012407005860320b0541d450887d01a0b0b105034941002c014106071040025031601c00040d80314032450060001d42612202d40d401070002c8001e00002a00144101003641c0381c052410400c6004c60503110f50100381c46920060005000310785c440c2c410354014115018010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 338832814 1250 338831564 338831567
    0x50c06150a030c0e0609070201090c03030e0103110d020414031204050906040204090515030616021009060e07090209090703020702010813172106060c100507140c06061915 75
    0x818204900d9004016610000041415440c01c2c8008028640360003159080500034400f040034011700d44400e5a04203800c58001412440c0d0f40d400700c0390180b900745140124240124064004080f50030301c0444042140d08908240d640180122030741030b0080700c4003039144401d150300e030742c0f0041200c00101400e000400841c1481c1301051f601c4280148014609922410a642125815a80c03d81031040c85030b00c801c0c481c00c080240300e812081d01d8504d98200025591b001350386043c1e00b4041020300b5118440402001300030341025102d10340010645001680f504442d0000350400b484040c4100c00680119500500074400c403441c8a8041c2e446101d01d0380d80805144058100c1d0381b00b00c590b18010200000102000406442030802001b842d444604d10744800901c0044040c111130b22030003040001141c070910020303c00c0740d150916040421150754660056038480000c10f801109140e00141c42c4c4000074001c00c03003510586003144c03010204454800640604c1000f400740909660b4140c0d00400c155 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 338834064 1250 338832814 338832841
    0x1060f020303190902120c04060905060a09020903100903082a0f0c070504020a0e04060e090a290c04060305160906051e0d150603090c0303080c070f0819050c06 70
    0x5001d0610040b902c511907030b01041a0003101b117000c0d4043d40000700505268503003401085c00601c80000140401d082072800503008000e01d1040001040d0700164040c280d403000e102440408100341c1c81004115450304001c0c0c60404215146a20307504503002e40c140c40380c6110b01010f007198502d40030780d04155510142c100309070300c40c261850980c0b244881c0025960703204c0c0001d01002c1c1c02542d540140c00f4035003090000b6100c842d00b040028501d02c03400c100d050000000c000c410070307401180c0211311750010f02a05d901c840b00482c408007480520350400c03107007503100d100030812211140c0c2c0804c01c40e686c00b100c80e006035844d42031000000c0d003000d2007000000d00ca80e025045280c2d03206003815030300080c102c800206601400e00500e0458442100c2d10640c030954181800034096802d0074040b000d501d5403140403001807400010203110381103005c034400e0034a01080d280c038990b000514075420742c1a0b06195040d81c002d60005403150400c0c001c013059951007003060380c001d004003030000d00103610b80c6003010940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 338835314 1250 338834064 338834101
    0xc0f060905060108010209030c01080910110c03030f0402090a090302060c2203060911030304060903021909020a0201330e06040b0607080301030302071409060d0302010216030e0901060f020303 84
    0x4864481000c140420014800300b4020304989000595801404c01450f083c5000046028144030016003005444880818406900000014005003c0c043d0580702c0100b4042c0115500c0d484c4804420000015084c0b101640100e000b01c03903802240d65250240e9090311807c980c020700580144004c143e0f42c4d03600314081c1a001c1000d16109c0043c04d1100045800701c1c0c0194015120941c940c0d5005045c02503c500b10700d2880000d401951415080034806881c1000324031009004816488c0d54003a001703041800030010340100001555a108603900083c0a0030301d030680040700350f01e1a5144805040600441d0300120b00420303216810925000d034041c010130b40100901d4029403602041c441d5940c2c0e02005100d024881e5505546075419400c00078580700c0c01d07421a0102c0000000700b103030302d07544c3d15800a521032012900c04280e0f80907031070128003901600703124015810100c002902003603000445030422220903500c101c4103030380c0c1d4002254050340c81500440941c10410108448102140640c80b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 338836564 1250 338835314 338835323
    0x5060f04120506310311030c0f0717030a0801030f0204060504050c0702040c03020a020a03030513050a051516090506032a0408100b0f240409020405120d020d0c0318030503030f090a030c0f 82
    0x9001029041d80c0c2010140b401505481c1c00a000920103007802fa007206128111060081d8148010350002400d03040d01030002400c99030040c02d03841c1c115a2540c001c07601030503002d807003400345081040d441c20715600b0041e001c138820390400e0100480c4610038801c2da43c6a6100d94010540912240c07003d40050901034610b420b02070440e21003038040350041100c0c11245100c0d0009003544d10b0880d0703000b4924140904100c1501071320003042c1c01007641c01102c55066a0040710040d9503034540e1b2620f00e10034075400c46e20394000c0d0180c00da20b424525400016000300e81300001560050188040350b03604558a100c14141d0148100400818034207240208000e08050700c400841c90039030050201c0c11036041944074103403c9400050511842c00d01c15440b806c00c82002e0300800d4298005e580180d141e80c8456001c0c02005000112003003414800c000e152190b0381070103c000c0c54151a030070000d86035401240c0c440c0d401318004001c0341c1c2030440055007412544c0c00d507441c0446100340f50343d182d580c1501d03001c0546 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 338837814 1250 338836564 338836567
    0x504020904060e1806090705060301030821070e13140a02070321090c06020d020d050a050d09060c02150114010503060f0405100608060604030305030105060f0412050631031103 77
    0x4900d5010222980101584800300050713240c0f0403035140c60480001e000a8490708104020015a2508019a4152540810310a403250b8810b80c10310300450340d65003080c01e0701c81c072141032000c40742c0c10284c5841c00000076078020f65410007030307041841600e00c05030300800782101440c00078941c99656400b4110203440b83c03800c10500300c00740c50011102d414988010303500303569642c6d841081101d00011140280102d001403d40403e0715100a515801c105810304240040000c020250a114000310340220080b00c40c200803000403401c0c043d0062005202d408090301c24940380c0720a1035442411541215020311a000c56800e40e00011245504050701e001d4111413141c005400c2603680d8090540320340c5a8240108a681c90224020303c5444050146805590204010700210750b000d070460703064410a8441903640c070700d110641c6080784115404814040d1000d44928200403000c60554022507100080c4d04685d4a42070392120940b6403110b0500c1c09007005c01c0300c130740000e0040c1c0c0300c2e181c80c0d6800400d4a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 338839064 1250 338837814 338837819
    0x70e030133083007060e0d14070b06041107140c03030c030a0c0c0f0b0c070b030c121005060c10050c0f09040902011403010f090f09030c020d080c030a090503010c0810050402090406 79
    0x950541c000e0141117600f50f0720382d80e0a1102000422040078815098645a840c0003040c0c000e4400502c10001d000d4101480600000d40544030368202080404807010356903503920007810308c0349202134040119451070042c403c2c0740c0c038a81340c004155410450000042e5286c88004030040d41c144142c044110344c8504401d00c00203c0306a04030141004100300752040780e4030b11004071072a05151054104001c280c00500c2449414ac0c40c640645000100c511030045060f141c8510708800501c080d1700065100c000002c1c006151240403d42002282072000c00303008644505482d80c540d070081c0220700c06032110600c804042c84ca45a0084428103006042024141850040003409503000341c01c0082d0131034014a08205104040c4901064050743c00c00410200d1880d80d0010308030380480700c010344a2901c0d041803100b40241e102c1142e10712010b603411641e49500c65003001c1e0032003041d482128030079403818010200702c070b020310000c6100d0403440c590b03004001e04060822009400ca080003980040c4d454402 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 338840314 1250 338839064 338839153
    0x1908160f050a0e09161d07080103030e0f0d0f03030921211b09050102070501052811010203070e0f030a03020c090901060911180d050601030209070e03013308 69
    0x1740005020b030400c0c406103044250040f4088540040c1c505000c00000070b00400c0800c0c0d102c2c1c2c3c10842140704542d07606000d1214800110181018180645007100b02921b140405805900c00100342c5e1041005014a603801c14502c814000301802d00008642d01c181c00d0258401e60440324192030030381450000c1c4601040d00d0301100190310745c000802140e021281408550380402601d80103220034a030481c80c251680000c954003144c80110141a140844c4c890001c55015451300701c41044480c0c001c540300e14144100810094803449114003ca00190b007010003410301040c1184000d42680092079601300e800c0600c04860001401c0a415550340c00f000b1554420038001d030544030514003110b54564070034480035038400d240364000e144192000c840e0000060008a9600d04494040769940511398682c001903885800b50788819515518210302050402c00c2c2c40100700c036000e454003400c03203808002d500b4a4460a002d008101403030344030708002109410414128442d00d15544201c50000812922 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 338841564 1250 338840314 338840353
    0x2030c19020a0b0a020615030307050a120201061a0405010909050618060105090a17010501061b08160602030c03090f010605010e060c2107140c0a030b061908160f050a0e09 75
    0x44c010b80044050040c00078101071580484d000407000345141c00601d640300340d5915103040b80200400c0b00151040d04040c000c0d4401c4e00141148088072600c406560b0401d0090383c0140202408510f41800100781805a441824800c20000c4e003013a500c200c030380084003d1607078000e0101d410010104641441c03a181d081d4200e0003000842d4045191a03013482c5018290b07007058104000300031540c1810390700340e07469800040065402c07141542d81c81c5480201d19030a1500842c000d0001c5000005000b410328000c0025803240740d5002c01c0d03075503402a00c041c8a007038035020710485000808055010300e551920f400102010291072046030044450054200d080091068279031400c4080031443c17100b44504d59806421544030000944001030480c00059496000c500024041e42c072000002100c986900041210340100c0c80000074207078ae81c0d0030203103680e00d00000b00400c40d4455040005038004101401c40c0a50b04c00900321080c440c20801c1c1c09010100041a01000c1c0c4034100301b03001d0940d190017 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 338842814 1250 338841564 338841577
    0xc021309020310061a1207080703150b18040b03063103020f0709060f060804032601090e0a050a08070206040306060806010608150f01030c030905100203040c050102030c19020a0b 78
    0x5020504601e8417075104403c4c9582000380c0e80d4040104800d1a40d204161001039000c2e5841c2800034140d02d5105d0100d00500550990049411000002080b0114641c0c0030b00250700c400107100e41c071550400b00f40801da415040c21a0b4069200704041340e0032006c0c0801070022001043c490f929217001c80107803124040344201c001c6c0c0168200000b10042000280256409091502d4051003000c1c81c01003204c00e001d00034404d1000b001120f00104003014031500c0119179a0f9400041e5200803d103030b004000000d4800e01c07c0302d5006281c007402d904c0299020070304c001032582003c00b03060405034946031507074242c0c031450b0200c2e0711600030000440000c41134031074400130b004a00000c140340c0d0f040c035401400c00c100c00760000050501061000c41c2a6440c2400015000420b1034013141a10801c04164080c01c0c0511000380b07580038980d41c0c2c201c40c0d0000d6024502c200d008004071801c00d0740d110016a00c0f88204101c000b00341e005164a20102840c00504909280c0702802a000059980545441c0ba80014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 338844064 1250 338842814 338842843
    0x6030605070809161e050607050c0a060c0b1f051002010209090a09050607320c0d140301061103070b01031a0105040e0c040e011815110301060c0213090203 68
    0x800034001c800d81c1c000c540e26070000c0a90014801c2002c540c6400e0900031203840b45400c014040e0b80c480f803400010040c201e00070700c8060551603c411903842c001f61a4400403401c42c3c0628520040051280d104402c80c4030865040b1003c400546c07a40c088040604040312615400c41c0300e1520005a140c49290708080c1c402c805900050320b44010101308280070b03e02811341030300d060410004202083c00480c078150409803909202c4007803108181142e0f08555018102a01c01003407604c1c070300c40003803c8001449120224401d49694800c0345106540317490100c60f5040841100f4801808036500a248410703401003920112403c141c00380c1d44d24030988100360012076500c14020900c0300c0c0003040f00310b00c41c0513100c111410303c07204000e0038042c2e603500c0100c00741d02d200f0747e2203400e0500a03860030360004003281d91850f01d0342d0081c002420007500001c20400c4164085241000304000c810740307041602e05031503490303891030b60220144e02007105503103450134920390f401d0b0395450440069804100905540480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 338845314 1250 338844064 338844071
    0x203070314030c0405010e041b0903022d01051e0f1215010503160903020307060c0213020901050a050d0f14090d020303090a060203100b0301030303060905010803090a1710060306 78
    0x628005010000614000e41c04120a000b400b030350303402c0780d0b0070364060318400c2c41e202d448107075548002401391400508104020219105c00710b1250303405403007282aa4000e444601c2580c00321180d5210207107489402c60003c1603243e9040045602c00c0e0010300300044611900302103142c030002580c04a0f4410b070390000b4035a070005142c04841c50450440d41c5c0c402c40e261400880c04d0b2100c130020b801ca200007003056045020320307800e00061728000c95940000c0c1d5000783c204d03800301d5100e100c050a48a41c51030181d208110301e1819810030800c600031590b210406039199410300401d040e0584641d0099804a041c003a00c42228802e089031a119011101c0f440c0f1803606428100782a00e01d00b00003c00c061541150030410400070808400504075605550000c40140d40c3e40d5149000c40100d22a60408800c1a80c0000000181641a0400780507584880010030290760b1301c005443c1e48c0d101c0c840c3c410b9000502c10038204052045d04600d85602e600c602c00382d0384110300c0014040115181604200d40300c9a8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 338846564 1250 338845314 338845327
    0x60318140c0f12100f060e041203050f010609030305030415020307120606020a050c0f0411070303020306031b0913080c03041707050109120803191806110313030e040b030d0203 77
    0x101000030307209040b0241d84810049180c414001e844241d40b060307040180303407107810b41038846650784c0c1711000401651040d031200b41001d240c2540d0051600210000090611001c01d80416510715070314100c40c102c1d141c0e000202d145540c182ea064100130000d0b1544084072a1845a200b82c0340011482841165030b4106a5003003004d1050807640d56800081c215400001a01c000407c0010900324102d000c503803c050718079107080000c0140c919648502e0640d2000f20742c0204058054010750b0042204800f500d1103248103542540300601e542c00020340c00b01c130f0100070500420440215406103402644064a441e90007018503107903500035889145050040040b850400d181400780001510003441c0c034405252401401521100c1c0c2e480000d01120380000103d51010343c00070b0003071046d9011401c00d20005002d0305010030742c4090000c003a5a0365040442e60f85244a600046030312480c42c0404070804400d094500701c4e401d50000007995009035849042c4038075a9000c0042044071040e550056682d04d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 338847814 1250 338846564 338846569
    0x5090309090a090c080304150305090f0d0c0308060f0d0201031a041107060e010c0f11190b0103050d02010b0303180a03151d0c0105040905070203070f050f0f060c04060318140c 77
    0x2d0745e8001c1c1100c1d08288410702c00020f2031203040598010900d0045000c2c0ca90203402401e00002240d001040d22a401d03516130001d07080020469154001c0d15000125a100403e2004000b402914035a10000c4400b1800041d80654010824114014030203150800f00a0102e011201e40c1c0a481c0c0d046100440c114041000502544d00180e0344100240104030740c00c44007908820860507214280001c1c040c03010800c81041200c1005100c40b80c5000100034514141210800360a0205840301d0044501c0508100c1c0140286030310758601038001d40c9004190a0070030380b5000546009980000c1d448070000100c1c404515a02e00c4400c40e400001e29083d07111b810810240c800c07030030b401450304108951861a070b004420703102200c582003800b0850369598282241140319004d0f0040c200f81104085c4000e03c0030010b040b00d107446a86084400001c03102c100741c0d03980c4104407605900c0f040200814030005119070404c0303049401c0c000c110491181550f0310051000e50001c21f107055940818040d04076071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 338848920 1106 338847814 338847833
    0xd0f0602030f01210c060e0d0b0c130e1605030a0222030c0b1213020f03030c0c100c021806060d02040b070c09060b0d05090309090a09 59
    0x30b01e844405100c1400c400e001e90b420002c14948101d100408141041100c10b800000d5010914540b21045510600100800e9000104070350740b48005000012003a009071203540308142c46080030802c041c02c3c42070365482001ca11910a06000d21a000500782c0081081c462034215503d82d11842d00d517001c0e02c21903d51080b43c4204101e000d2148034084065815207101d00c80060109503035103032142c0a030180350301c1e1207034802d40c8101043d425501d01c00c070128801e20191030f400c01310400f000000c1c00d43d0401c8010704000d802c90420100c0610700008807001489560400c900e045605401260b8008000c0c62803d0b04204100089019542c2c0c02040d00c9080120328015990b46888c0c00c0c20740038039004480106c8100e00c90490201e0050740500844007900c050806041c02c1a02049294014200160600709540810004d464040d00c03064001e5104a10305034011801181c90718008508 = true := by decide +kernel

theorem cover : BRFrame.Cov 338669064 338848920 := by
  have h0 := BRFrame.cov_init 338669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 338669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 338669064 ≤ n) (h2 : n < 338848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
