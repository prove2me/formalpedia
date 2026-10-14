-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2380
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:32:22.785016+00:00
-- url     : https://prove2.me/submissions/7122b10a-873f-4da9-bde3-1eaad2ed4690

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 427877697 ≤ n < 428057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 427878947 1250 427877697 427877741
    0x9120f0f0219110d020a0807050307090902030d03020307050c011506080a0212150109050402030a15080d020307021005120405060a0c020c031002072a0306140c0913060b040e0406 78
    0x1c01d031030101c4100c5005007180c02c3d5120403400c40e00c420301404c240ca41c0c0a0048041ca071f4444010558030381039803080303901c280f0640c2030100700f000850040c2d03508107134090028540d0000208041d0040e41005002c5401c0100074045010460341c24001c51b40919031a01d9089800d60420600a02c0010000e180804250041140440c00c04c42556084c0c1d1080d410194030040111007001200c02103100d41c8400d0384240040144020584c19500c42c40544141e814410305071551a0265500e900c400340034140036030410b014000260030800310a620a003040d150180ca007560b602c03208001d280081c0c509032565440b40d420411b034030740b1900c14403249512500041000c3e080070000aa983d2224458010300306802149410400560000c02070004a020810b10b01e0040e039801d8982c01e078240340c44242c41d110708001111f00384005050344503002e9045e102090340780025880500c054401c402c14202040d59990200003076a1410001a0000e01440c101703d049034201400c1c03880a076190310500c11b5540c0c1d03103880 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 427880197 1250 427878947 427878973
    0x30b010518070e0118091e051f14040228080c130b0c0a08283e1b03160602030328050a02220b030a0f09120f0f02 50
    0x20f240c10414003444c0554207080c103100c0190074003c0702c1d409039040c81d052680e402542140e62541100c0503000050400c5150380315040c4400b6808107040200c1400c400e10030030f000340e49100502603440300c07001d0009407a10740c4050000c184c0400010040c001a0364a12009090316401440250406107000c111414003034060b2545444892905c1081ca0303000c0002100500b4010910072580031b20b0704803130300c0c6450b1282040040140380b00d492440c94035031060140c54408a0050041d041c5000c0d451100020150400013503141c0b05a40b00804a040c552464103c403e00f030781009440d014143da6592502e241e561030007450b107072003a00288800c0e0100e0132501888801e80c00000d4a501502100e00100e040d903d1007042c5080c0e090990010219600b040c08000c00c04c005034004003160b4141038076622840c8030f20441c081d00c070f503118050300000c0101040403461401d45600302c21800c000b1444006003254103580c0b00790411102c82c0d09200441c855041c480745990f00200720247d0003266001501c5041c0710b00d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 427881447 1250 427880197 427880207
    0x30a0f020102011a1c03020114090d170108030307050d0207050f010c0e0d120e0d1a06090702060f0a0c210b15040e0718081509060a0b0d0b0a090c030b01051807 70
    0x2a140103841c07105d803075004149803003504041c089142d07414680c42207050107201682c452500a10700c9010905aa800c01d80740000c04800b04d040301d01420246045855014003140d03103600050505c564103400780072290106005104494000800c030300000380d2a441d180d40900001c6488031030714494460b0f81383e4500420108010300486003000d01c0c100200348100f600007180c120000c1c602901d0300e201c20040511492140e50391600078402190300b10482d42d1106800c85ea1200c0c115001882e100d040e0002c80ca0340c1415800101d101031142c18040f07041080040c1c41c1514104010080321040d88400004c82c050400304501000340081001007487c02d0f00f044480c809400c400f800b84020400204000700c4c840d294a034060300503110701004d07600040c4008604854141040e81c50004a000341c401240c1075003c2e61040301802100900620080c80350b0340c803600302c004001406040070a8a03051140000b03100c2100142c083c40c070440805940b5414070060200013a2580c204611090810050054898000b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 427882697 1250 427881447 427881469
    0x90c090e0705091503070c05030f0919060c11030304270b040b010906050f13060e0405180d0818070803070303050703021e0a0c05030d020c0c030309150d0b030a0f020102011a 76
    0x131415180c3e43d856840045070a60345055024087e400041801031801e00d83d14010501900300311031140040861030250080c4000070b2203914046841e105d00134000842944007815560300080540741807540d14102c0c082140800100c2d40005c500c40c0c00c10700325141c103a00c603001d0000010780381041800078000c006400025240203100a1100120b1041c5d031600f0780350110703410285a51030301031845940d038501801e242040f1024030710450622001401e0340801509106003110703981c004108061521005440415002d0144c070101140001900110341007081108000d00000008607620060b50800a04a030400b91030380c03003003500400111003200f000b4404000ba461a0560059541c482041c013035507aa0180d800c001c0141c04045601000c0312456405000c403000a0400d40e230f0300070308035820180c5034855015900c0d8000740410791241582c02c450701a101040c0540703000110a020341d40043d18259a50b00b04861218441c45950110b503828000c1b042c42d2842480c1d400010404503000031806000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 427883947 1250 427882697 427882729
    0x90603230c120a021f0e0f151815210106020601030201031a0301060b1806160308060a1802181905060307020304032117040f06090804090c090e070509 66
    0x72107040b00c072808140603a400705a4014052600200031840e401e40001090b5050b001142e9440381c0301e4080c0c00c080641180035840140070003940981c1c85040025500240e9003c4010074500e18a0318141e1105200e111940b01c0d03544400340c890300d601140c5514070711920f400c8108103a944004002450b000a202415258242004214050f10104801904111040350740c4d0541c2043c03000540107106074018402c40145a402d0b0380c41502c010213102451040080c41c5100300801005030303000c00c0c45001d0141e04281c005041d400b04992311400c0c0d0740040b8030705151800455000590b4040141c50400d04189444240d0380c1051005a010400da240c2c84d5034400d260152174008001030003d4424021070b0061548804c80c0310303c050444003e200d0100700710101001284030000448107182c02c001d0f00034840c690056130114002d02541c0c440002c0e0443c454201c500410070301002c40e5881143c066a400c00045a90740310320b851400450748500107002e818031041c041c080040104070f803102540b40d00c03001d00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 427885197 1250 427883947 427883959
    0x51f02060c030c0c03030709060306050d030503040b0c1b0c09061804020103090c0b0a091a03010b16170c010507082503021e07120201061e0e06010216090603230c 71
    0xe40c1e41c81d02903070f0f03124040c82c02c411804008100b200315030300201c2c0030003030340c00603a001c00c00903403200144614480b141d81c001c0c2c0450310a0000500141000051030f03070000d085581182000030f50300741e0720402d1422031aa1481c0390012640a5a41d040c042e4460b85d00038000c440c035400044007003003801c25148028102034109900c3d10801802d00c103080f245407000b00341312580f440e0b94800025000b841454903004110ba01c918404c0b01d06191007104007500d050310b0100512030310746403122440413003c0010380801c40d410540000e15224a05240028050241d50540042110f181c0742e480148200d2000304110b50b511945c2d4000a82089401a80d02d242c801e01d0500596892005c80c00e9542c010520a02182000b800940c110400403800d6a0106407111600240304a5480f1030103007044802124000d0f0001c14005810850360500040c2d0b2a009a4113005603042007036403c0c0c40e504100300640024120a0321400e00b081085201c0411070b2082e004014042000149040c45036100c2ca49081e54500c1030b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 427886447 1250 427885197 427885201
    0x4050a090504050c12030d0e0705091602071206060312030e0c010e010c1502041d090c040c0e090c030106201b2d0a0b07030e04020a0309020910051f02060c03 69
    0x8400c10600d10300c80070040c02c040314070415007181541c070387c080d08200380303820704200701200040c0340000c4903001c1d513100070000c1455603180b4565417102103803486000210b12801c940050f42924824010030002d00824020404e42d00710708207001e06000d0064140200752402071000151100443d03a1f044d21042440c0021000a00703000407a50303a09010000f4059533010513403003414050b1540240122400c200814000301d4a04003019000c0b4030413160003034aa0401a4020f9144c540b0b079021240b42a103a0402007441c1015901240c0710303d03001c8a400703036034240000050100c00e801a030140b0041c0c1d410228400e80542d0030030416250740034510512080c0005180e00c84007a581c1c0e44011081c03070b4211805501c4140d803004034102c209082080d80d40a103d40000200d00e100c2d00100f201c019035015112000224102c00070310000b507110080480805681e102c1020060381d8500d204d601581c2c44050b50300d0a50f06140030030079900d82c000c061103166000701c000b224225801144403030f800000e0403500303503c079 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 427887697 1250 427886447 427886453
    0x1206071206081009030801080a1e08041e03030e150f09030f030309011b050a210f0221010e130b15060406200f2505041407110304050a090504 62
    0x1600003908206000d019203e0180c2d04420290b2140d60194001c0e5100c01d05642d0319058a501d5103aa4900508600c3d54400001038041e5007480d8201c240d80b00f80344461909941d0040d207040504400c480c034402d9a9520003c00605500c600042e07032500e0100c030350042400c20507280e24458890108058810140425040d0195509100207408550f00109581d41e902d040319249008089480c5c588a582d10800c5200801610030710a880c020001c580390050246a1541040340d51300e240452440042e4492a80102560942c0003500c0c42c10400ca003071107400c48525040c0c141c0c1410507003100321050511001c0080541c021003c2c0301c40e4980140c04898603482e14020084040300c8825900d402440010340050255444030b42050403903401750003003018800105102c0c0e00d402e001017221503642d100c160618100c010796803041c03140214403c11048516034460114056503904101710825410711030812540d150881000325646894102641c41d060a060009414545501508035900d641b00009810 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 427888947 1250 427887697 427887701
    0x90102030d0b0607080f0310150503070c11060c03040608091b0d0501270b06040911040c180605130801020403030207180e060a021e091f05120a0b0f12060712 69
    0x1d450740103c0d00b90754901da05d92102c115030740f040d82d2880c01e542d01c4123000140768400e414045c0385080580d84091642d00d420f02c00301c466400c0900c041e00d000181c07002c44000c0e030355102c1c014094012960051500e540c41c0c400050719445000303041c0c0740306820080c8072114401a05d1140c48440c141105c030460600704500f04107005182c10782d182c00c510713064035410768014210b4200c04030089110300c02005050740c3c1c0c542880181c401104004117581003501d11540f25140642108500c03144524042c0f480c0c407405444045424110f0384a030001c01c034001010008254801c409001814880c40203502d803d14580d802565012176200e00300d040c420b0a040310306180301e540c001d1448004907904589880c00c14404560095010512101c121440300000c0800c06000c0b4060b1050100004c01240a2000c1d0070b6618001d480d000060f181001010031018400d4008041118003d0560010000301e145116040c41810041d26450a224440b0622000803001001407125032050262418054514209500c180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 427890197 1250 427888947 427888957
    0x3110f060a090b090109020906060306180a0f060803040f0315060305030d0606080a06270b1206060f0406180c020f07031b0e1e040c05090c07050d0302090102030d0b06 73
    0x110a0040030300788101c0d6039403500a100598010001d440036601c3d84d18040c2e01320341500000030f4208400200081c4649090400f440e8080000341005980110000c2802c8990004503140c41400340e40c2c60700e0310180201403040c2d8000d024182c00941ca401c3c200300010224140d144401032601c1c111802c1028880100d400c403d00555001c0300f100d403140d0034150080d001d4406801030b080041c1c8030030000ba2085440d40074040450303001101c0c0d842240307268442020411342140c0c103c034065448000102d540e4491603150342a502480003d0314160400d0001c000c111090a2a03140c444e0381051000d000c8001000ca03066040d03074801b00002100182c54005074186850b80f00260070070b0103900d00000034000c0740c010100310038a03041070b05145c050b02c407452000020810744194040c40104000961103e080540450300706011b0000140e0b6a07a44100103440050111900c140c0100c001c1418420448100071a84a00b503071801c066080c5100b20000035503d006921700c140d4a0340d1100303902a03040e00d034070003198 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 427891447 1250 427890197 427890223
    0x603070b0406050a030c030b0a060c0f023a030e0405090a06061710060602150403050c010603030306050f0d0201021902130f020a110a120c300216120311 67
    0x1525079a0b82c00300940660061302c00a000700703082400751510140719120319580420001c100221146c1003010031911002040c0e021550505209140310160780c500460101403665a0507403403065035101280115068041924401d03022094010000681c215400440d0050185e4001465a81e0554410b1030070710360500c0980303481d241c01c4000c41c014a000011004200703050044072030300d02c82036030220201c0320240300701001a040034641e86c0002891040c125000740c080e180241c10207030001040d03402c6444581c4114082581d0358130410643c00d0006400013505421a58600e035609680c00203511000e07210a910729012489561000710340c1c81101307002c4901444da0040103030600440d103100081d80602e08980c0413803a8414124100080013401040c066400764256030181c0610000741e0345000c20340e4048070300b10161869105440c0e461508002000c81c4274a02d1104619501c40103424014420010b060481f41c50406008040c080d00c0348643c0141d05241800c210b45030440611b00b0071801032096 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 427892697 1250 427891447 427891469
    0xb0f15090a05070e010e130506191202012d21290a1514070f050a060e010c052a0601061214011203030c02030c12070606050105070b0f060307 62
    0x1200c141c80055021034820781c030b1615004000c00e9940b0064440400d0350000541c00a01d401c080c0b40d003074000390415900b081c0013400100d0712103100000b0008900003608041d10b107a0050050302d080d50b07031101490b64402e59542c80c5100242ca8003801c140540101d81102e4280300100d07440e0022112281d001c00407002d000c140811404141c011110203041001d0505041e0000301240d40c0100d02c0e1803101a03048844050a500c3c071207009030001c1c0d0b182c2c0c0b0b104d45200b600e05801c5c80b103400483d0f0f01d00010800c0c1803140b4003400c51480d40745030003004c45000381151942d50307241c1b10f2408160f46c0c000707045444100d07642410701c1e0101c1e4101c03210b10815428066401d41c2d070141d00000644207411035030224100856070801e000307643c044c841649800c071003445240c00d485180c85001c400b090190f03111850301c40d05841a24a05040e85500f9481c1841803050101e800f800000c4180c20f0001c0c0d8484d140145c0380901c9d2052401d440d0340c44075042004050b01d4074101d05080e0000c18441d9a003085204014200c050171 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 427893947 1250 427892697 427892701
    0x230409022805040e03031014010516050607021204080706081909080307120b0904020105280c140c010c0206030901020409061805070309030813060209030304090606120501030b0f1509 80
    0x480000844500c20240140e05101d0381810f5101301005980c8108016489405290302e40100d040a0341e41181860341401403c200d1711281440b40c041d5600c520307008200401c1c0b241041d3700028a000d03aa0740071049001c00074002400710342c0340480c0c140d046401c2e030700d014107543e110f00c0a0b400054012614420005290400b0300e010003e000300070f184188941d0311181400440c060198090360100c47d1203560002d014000140190b005001034082c0306031040006d0340d04148061780403422005041542d0118040114010801c05100c80c84078641c649403010f0856003c540740041c02041101100920a2401000043c5141407d5060750010441c480303003400b16a6441100e2000b0040c0c12601034000c1e0b0900001403105402800b8140b00942d2665401b5000c0d1f0342c1c0203504441d805103d40455100d6020050701a10381e41c100040e0000d0302581c1070000c0c005240c0310010703211241d141e0218801c14205801040841c49481a0f83d038455074240c80d0340c0c05aa103d070a8102e91030400f1203010350100c00002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 427895197 1250 427893947 427894009
    0xa2304150303120207050a122007050a0503030c10050c0f04031208060f030a0602090307120b0108010c180b0a050903161703090d020d02030f060117010623040902 71
    0x3184001c0700d00070b44030042200c1450002605921034800054100e80c071182d05800098003e9a420820610a28000c0b8800d40c0c00c0c0b03008400000351045014603507000b11018000c603d00701c0308680003881c044000710f01c1d1007901031202d51904007690b150f041050740d03040000e01d42680da801f00c03000e0050100880303665a440346020200b0010b00241c600002e070700400051894207105044049542004000303000844c038a50301d040c0a54080c42c201030300350246850003d81c4503440440191410711410003100c40b076040580c3c0c5030840351843e001c1d1080011209a0728000f00c1c5400b520300c01c1d10102d0015907904d41407800c058a452080d00d48494052151511060001003403220b80d405840e4100d900d00c508507280320743c007640d0f4040c80740155072002c0e03198007940061078105401d510b21803020301a0707444c0c51007104a00f800e080090344031844100b480c4caa282c080700c0b820300c164070207892800219458803010f20344801010583d0880b01c2e024a9541d5900415551000364150301c2c4204000500c09003100d981d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 427896447 1250 427895197 427895231
    0x21030a030507020106064b020604171318060b03010e0402030114092a120a0b0708041707051002030a0213080a1e0f050114011707050a2304 61
    0x54606005510300310303000c98018420102007191f03652000072800d010318140200b18007020300202000403402103c0c0c0d0b01c04100315281001402c0c10481d0040d04030b5240505060902d651180340c0d011032050100007444110110390b4201c001d64000c08107600300c0c40741d503078111401403401350040d244212000c800000d0802180701014410380c425070086c810034100c507000d01c0703006506840c00c44458100444102e203d0620100030081508540d900d10308402d40c00f004140c02c02c41d615000d01c40c6800c08910301061210740c01d11107412044901e090000d910f41a161aa400301d00b001200c406524005060018403400300024240e00c000030a0465890401d1506200290301c242d04000d40c620007100005244200030035510009034200c0c0c0303101c06640e43d202413038411641e00c07000cc41342d00050607840340c00304500f4480c107100c503c96001712114550510a106017000c90708405000d043d44245020b00894503026546821a54080351006840c1e2030591000079400d6003041c100c0c4c000307140c24604075656101c8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 427897697 1250 427896447 427896451
    0x5031e190303092012070317070f0210083102010804080909090f10020f03061203040e07171303021c170a0c09050a03031b0303090b09010605040b010302071121030a0305 74
    0x320307a400076048015141c80c2c0c071b603100b07440702400c44c49440101c04c00c0c2071604401040392510481e090a036801c15540040c03040403412442e2400604601c00b00490301109068040c0d40b151307002c811050035914803605031011009804024108811040400c0c10440c01006440318500000d0540307902d40ba0040b81107580340c00c0907884241e06c0c130541c260361800c500144203d5400c490b00031034144c03640d9918401d011000303c1646c1c4c4603007503100401000035100a0024242d020b00d829648881c01510350403000350a124001c0d0201050031024000880000d40004584041e100c14017203003000c00449810a40e0040300c09103c90b0030782c41c4140104121018190302540c0e94107019142e0b036400503120014000f041170907020040c0070503840141410600201c6001c110704520034680030500144640d2651a000425124441c10382c0d169001032080e4a4039000303a1400b9502803a045081c41c0150701c820380701c00340385003100e4052030610700304c0e0820140c2a144030302d203c005102100da80d0104008010018042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 427898947 1250 427897697 427897699
    0xa0207020a260c0f030604022e02030301080d03230c0c031b0d030501060207060315180e150c040b13090c08041e02010504230a090605031e1903030920 66
    0x10f0200742c001c80d440c02c1504644100c82c042e0061200d540e075a42400b66440400c03100710113003c1004008504101c10f18421000f91010758060743c2c8a51401c0056880d010902450106260802d00840c0302b004103c01d40980e0210840803d41494803103c8101101d8810301c6d030f81003800e010024019414100c0c280d01c2461042d1100c080700c40c8180c40083c200d0495000f8020200140c0010a0402086110b0b40044a07882140500084001e68a41142921440095140e80c86684a404048032081e041c0810070312440c050340b0785c1540786082084c1101910403070244401c0d448020a5104444070395089880c0034112055040102d0f950203a006086014215800c0381c01300e003540c050910540110b41081324569040e15510305041c10103803410300081243c0034501a9603c000e5094030240d44480300704000b083c07201c2e0001942c0b810001810f0405c0c840c01c075020010049001c05112241c1d0005180d84044101c01d840381d890f11252404902034100d07a14041d054101990048119801201c100f030b00d0024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 427900197 1250 427898947 427898953
    0x60f1203090a05090705030106110309041d060901110f1308030a0c1407080a0b0a09020d14192112020f1309051504050910020705061611060a0207020a26 67
    0x166071410898114400c17201d20f00001c000b400100f21050080791311003c40066201500c0c00c1404190200f41221280d840640c520401c62409403240d400a0001d1900184001c009004804440003040514412440b4521000034002000300700024543d0703061028080c0941500d079100d40b501d40042100310780010540b40444000c0c0568070b05100001c07448101e524403c0a40201c06c3e4a4a44501c0e17108018014500c054884075098016a260501c40900e40d201da05210700c100d018102071032802310050940307044060112103c00118100e401d20b1204002e0415030345600d0803160a040f1602000b80d06120030329070010503009103580000d00a002c14441091402e9900d50369130401000352042a6150405410884d9810305507060036001143c1c4280c0e920102c0320031702444c0140004a9000c02020740d00c0341c00503000d00a503500103182440d8040042d152085035401614010fa032968400390082c1d81c42580010080115100c440d0480000c18050007440720203a01024422030303040c0248480c5181d80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 427901447 1250 427900197 427900199
    0x5090105160903030c03030504170712090f14330418051e07020f0d05030105040e030301050604061803020d20040e0a06050a0e2406030601031109060f1203090a 70
    0x80c0300b6040d42003140e4040c5e1340e04141860540303050300184805007003074445280c09103082d100c0d03600c01c0000740003440c0716245110300c01142400003030080580b074100501010360000200070100f44040c40004410003107079450000b00c500c0300f80b12546c1c4000c0c1555404002c0091002100c1407030f00e00604202c5920120348400c4020342400042110001c4030881c0c20a46003103400e20000070011003090380201d01d401261500c0080c00301e842e240a034910540b00004400200601050a00e4060340350383c1100980114195418100044c1c464015402890100103080550405090b45850110000c64010b094212170f40054282030582d074880b0314040854003001501d000c8982054070540000880302c00140c0b10100d11036940e90f0150601520303044940d07455a410b0301c1a840f040c06815284101018140308447c2c3c44036420818070780041c103032442a00f1100041010a1001c015224104400c5945c081d803a540c2c0030002c0d070081090030340e50780c2064052a46980c5030760300000911920390103c0301070440e5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 427902697 1250 427901447 427901491
    0x6060302090a0612090b131703060102190c0302060a0309110f06091002010b190302010206011d0f0408070b04060b03280204050606040902071208090f070e09010f05090105 75
    0x6403180c00c0c1d15a41080c03011804201e95442842289449041d101d80800c42200e152a002941c0d40c0c2a151581502c10200c0301d482000040703495002c020740d90201700c0f41517240c90b800103522441e16111880009850707001c02c504014004500b03101039a4002d06561f190611020010020159144c0031110007280800f2002c60740b51055003030f811844000d040f00e103440c501c0010f00020070311100d01e410666488000392521982c2d0b0441d04026928960f0b00c89807240d1442c00020b20f0140d06900c80d40c00040304208642080442180003070f0b0018003200740d2020b5441360315149000f0b00c180040640314003107502c00d00003000404d401844000408178111070001e80d00b844040e55068841c00c0d030380c0081050340c01031030060810b078200c90b500c100010a16400c00b50f4507110b000599000342001c80e0041c03500858607948580040388650000c2207140140092042c01052079035410780707400703a0482c0c50300802c00120329000075005813000c01444c00b0140424203203151401d010307040a445018904000c0e0403101d41c3e07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 427903947 1250 427902697 427902701
    0x11409060316060f0216090b040b0607030c020609010c02060d0e070b282307061415040b27041203140703021c050f0a060503010c021e160810060603 65
    0x10252021104080b41890071200b92025400c5031244025402884d00848800310303022a0440141580c2c48003140c0c86d10042d0400080700c107401d0b11548203c9040c890140440da11031805400c03c0d6054906907500c00c096401038440c030958082c000e5100d9000500703c0607041c0d0070b030401c807004030f81c890032190750544906050030309002e0441c2100322030550001060007904140c4500482c000c0da4206a403490130418141c020031101c40541d00710b0003000042a0701040704038480d030980b411000001d50800e04002c2503400034101007003888ae04c41d9856415125281d560000d80c18038010006440c1070304c2e08800070000751120300890b8181e942002c8008180c40582c0a80202e041c0f80307101e82620081941c03034030b81c180d0080d002030003503251102c0c41000184400849102e40c6010350b450355840311032490300760702c14000d403100ca070441c0d030081e4180448520074903000100c1c0c0100c04a070a030081040000e8005480c03070701440031b0140442d103441210010315020041001010400c0301d00003801081d4175500180d00f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 427905197 1250 427903947 427903963
    0x1308030a020d0e0a05060a020307030906020714010e04110c0106050f061303030804050a1703161e030c180b03040b07030b0108060603040807060e060a0b0406030f02010e03150114090603 81
    0x800750b000440d288079078034803482075440341c840000e00819085403500e000c1340d20382c0c000d098060050f81c4005001400c0c16000601c1e00000c003da44010041b050401c0c000e64030520b0b00303405950501480200e43d4100b40e807135170007503135139070404e41d0002c1e48400616003180d010301080c1c403a00740201ca8400e180305c520b052003421680c1c40480750180301095841d42c0d401700e400d403500900541c0e443c003d5a40400024a1481003c42e00303101d45021541c803820141c0c05030031821100c021410501511140142d40d0000100100582d0a0b00d4200010749440b81041918015905c3c9044a1040d90240001c0380c00e020300301c065401180240c0240025030b880e00810340841703410700403450104035035100003401482d00e0760080d58443d00c41c804082c14011255540c1c002d5442035203403000307680c01c42c02c10000e4480706841070890800702100d00740610391070341d120313003a00e4411200040e041040070500c0c542da83d1400c10400070140d00e044454000307981d41c0c21030343e401d2210506426100f4403803030000c18118900014512 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 427906447 1250 427905197 427905217
    0x4090606050f161a04050a060608030c06010b0c011e06030b060105070f0f02061207090305060c120112030e060310030c09020f180f2701241b0c0902130803 68
    0x103141410000301c1c03c2100029000c100e4070340102c0111684c4119030140c549014520600003001345820514007242614450f4010b207240d03a0060001300121180042c1e11030444045d40c8c4c101d0b65540c2c00c600c5032070151501304410941404c240807440004084d96100504490140c4103034106512448011112403080b540301801c503000d124101c1d001315020034a00c4c2003140c0b0090030b047c0382100c1c0010016004008950040c04100c8424081007848400d009195010880081c450301c0d00c0803103410f0892410041c0078401e01b0350008242c0a040602940703240002c00380090455407240341c08403c0042c0e000c5280801c484180c032584001a1028103030082d02c12a40c056200c003418a8440c4e01011440090080e1141e80640c500841d02c03003036141c54444a6054001540b4804002e58501c0d0f41a41483d06a015100c3c44003070003c840e031441e800c030151844000740fa1604a00b1b000b1003242c50580c3d642400d102070700d11140d0701070000e070146003135008046a81c002e402100c0d03895038441d5880d81700e02601d40c0132 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 427907697 1250 427906447 427906477
    0x509490519051005091f09050717071e0e010b180f06030105090423010605030114160f1e0f110606010e060f0c0706050307021507020d0f11120409060605 67
    0x240350f140c80f00350841c80d400409042110350700e8910b0b0a0001e51a00d01d00d80c8000300c40d940c0c1901c1800c0c8501880118098070750340c00b1200304035000c160542d6903914540702d80004110400302c00c503030b803901760f40750b0400600c40080c1e04500c5586030440014164084200d644801110341d5000f040c901b041e55207100b000c1c10017406981036030f28200a002c0f001c1d800500854031881503c0404c5402003c51624100c0b80381c451f000040e006041409042c02c452006043ca61403140040802c50310b0344040f40c10f905c682e0700c180781504100181044c1650300d00c82d4500801e0748000001e40916440c0e9101d52425036141c0316648a20202c100d4019450312250180c910b00e000640348481d0340c4940c100300d00145003400c01c40c01101d00d4800140e00c0d41d820004103400c9100000c81c00024070400c0713503040081a15080340100c11003d07509000c00301070354650803003500c6800d20a100100b05030042c01607100b0035040503501d055524582481d06125800d40c45805800d80040c540340380400c81342e118000351034515064481e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 427908947 1250 427907697 427907713
    0x30090a1a0601020a02030a030e0a05060c0a062a020604031b12030b01020f191a0c071509020415050103050c040b04120c05030a0b01030210050949051905 67
    0x98440250001424070b810340c070600c0c00c11001a1010048201228000c1d6124000c0c440c17200c0402c00411440d612480c42404240152414004c0210f8804429070b030000300000c00c80f0003254500711401c01c900480d01200303400e050b91950b0725004070b44113103d14460758030111182d0303022030a03203034050216402600c1c00305000c990002442c020307070000c11900302c1401203c41c00f0141c22465464603000c0900801a4001c4ca00340b403040140f002441800928a520b480801c0d18048080304680d000b00d00000d4604e0400c103501b1250031860342d1104244c00e402a0040c0204500c690740c000c101101c521845001a14010014285c4910101550295071280b0a16464580740400714002d59844000640707001c6941c0340001030a07541003140000740d9118001c0c40d0300039031460040011444020581009020b0f0420002583ea991a02c1040c0e84180d849100f035290b407454a207100c80034402e410300041118802210103450400d480c80b4800c03440c89074088551036000f480c107101c403c0e281c0030401032943d072000365 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 427910197 1250 427908947 427908983
    0x61314071d0d080405030f0c010c0305030a09060603081b0d0e1201060803030f100503010204030308070804060b04180203010e0118080706150f03050d0905060f070830090a 75
    0x94003111014803145a0354070350084000280b07800c80314140c110f9480d04001010002801c060003d222031041180140c41501007000018085580c0d108005042220010001d0000040ca42c0040c250540104040100030740302e15102016a0000f107003481e14202c40402401d60400025000101d450155200d115500c010301c2400b0000c0f0340074082c2d21482d505c5110204103c2401c101651294204840c07404c42d80c03c013800758000307816094008070f000341d0042105002194024404580260306460708a90603922410500000c007486019030340e03c2810050ba0b014503c0400c94010a03181c0200d000b000301c50f003100100c41c01c0b506101b036441010380e03094518030301041c0b07240302606545000b800045110b441070010741c2102552900980482c16000ca030500134480100801d003101065030030000451f500b444005011030180c500300c800c000000041c0d0404110498083d140c11001150041d0318188085100542903401e800a8482c20581c41000480751640001d03030441d00e03600320013041d0131003039500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 427911447 1250 427910197 427910207
    0x80901110307021309120201020a21091209050f04060f030201030b03030d32070806130b060f1905031302060904110a180906180b0109170606131407 65
    0x8038410406000034410007015840344c8410003001e8006940001703c0d040c803881d00b200210a104022000c580c41170007101072164001c11070900041e10460f0404c290103c0291010240510500080958a1101c1e500858075004074402d4182c9800b25000c000076820300040c401214140c2c030580b1700ca074501003020005540070313030320040e07200b41c014041d24034001ca0708080c201aa07115440d0100041d01c441c8484804110141441c80c5d504000e0103460343c1d078104548000c2c0362600c0035060368451100c881d1b01d00004421a07100b2403662002512154944080320104065504100802c41000098400034002184200300302e03071050702074044144a04e0745540a0240513000048200e4003e070341c85d448082d200030b07d04040c04015040d41d84e41c03c10040c0e80c481460010303c0070b6101c100c41c80d007440c8041c4900c00841c80780f040d6284849000007101c00d855001294903280c1d40d8002500c0749030b0a5242c1c062035102045481c859041607c40407803c240c6a080c803011100c4404c10100040c1295000c16045031041d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 427912697 1250 427911447 427911467
    0x15030406090f03020d080601110c0909070f09150905040201140306030106090207060504060617070302060c100510080f16090507020a12090305010b0907020703081b10141003080901 79
    0x4440004160341e03a6940c50034003840006056000d607200d0040f4540076503000444c1503101c0401c1c688036103003d110701c90f540e50303400411100511030b5202100103015013100b0001e074802441d40384c42039104540d1741c0302040024a240310410b0f900305124440422941d8403030091074052941a5240d020340800b1078100c0d0768a400140606a041d52115400110484c190001d421a00d00540000426007807078034100c000c0b0b8005a020003164000740c010806240000308a46045a40683c0c00c40c0d65906015100c13420b00c05040c00050210349401c0611800d52501040c071410f9650f2403044590240c9200042c0d503640e10703101039a040031030350008284412030154001c0c0e50440e00d2401100c1c80c010159517102c3c00d00104042e49000034006003030800030300401f40200782c141c0d88165400503440c1030075940291180100e0201800801c000220681c0b400111888006040d034480142c4e00d41458000503030025000310040101c49500c80d03000300b202c3c82900e07548031007100d600c00f044038039004031080152644459 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 427913947 1250 427912697 427912703
    0x8130308190b03060103230703080405010302070606030b0f0621060a0207020105090d060506040c0305040f02060a0207031205130611152707060f0206130f14030d1a030c150304 77
    0x4482c44218251410407455002e18841c545204140c00300d42c00641c024000004a480030354131400c0e0800108841d4400c41d41a01d02c20718026a0b262610305004000c0c0400d548020011050034003001514540b40c4031030390203001c1c12298802ea540140c0b14107080810582c0900c98550040c40102e10030f40146d500901c0d1052042c14038604040e20a400202e04989410003540c8068a80080240a02d014403c0321151585805c0070041c5040588824205a5410350003d01584000450480c40303402041000000c40d444106a5590300728141d004050350400d907050b0111100341c550214003140201940750003907104c900201035a0142c0c505050010324081c014141c0203140c100505400140c468208241c00072140080412514204009010f509a15104001c5412401c2801001a0a40349001c2c9071034103e0000040c11100b070800c3c1c03146503510310244500748800101c03034205035526001070a5048001c0c07600c1c203003655144281500c2d040c0f07214943d94490341d0409074070400c0c036004000d1a00140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 427915197 1250 427913947 427913951
    0x336020109031202010609111c09020406030804060e09011401020c190801020c1c08040b0a0504080405062823031504020a02060a061a0304080d0e010203160813030819 73
    0x982c03521440912000440d5030380050351204418800640140120722511941460540ca4008080d5000060030000c0d94400815901c40014101755603070303a0045d001454010715511b40d1199551005000944076a4025005040c01e60002441c42502c0030360014801040c0c0180a06000b00801c120020680001540e805045504003083d82c103c01d1001c0c0c00f010a04a0007410301d00e002104910035241ca80c807804d000c018250041000148181c0e0403150001c0d00704401050079200c91806001c180140e4201507080342c80440e680c26444000b0340360107420128000e50594400741c4200488100c003a0603100d0820740f0010107a404520710100095900007110807600081405120010741664014500840164004414400c040e5498030516009192a42010884003080851981c041c0001000642040c6021031710300d00003412074110210625007000215643d00d014410842952002c404100024034070b000010b10034030b0724204003428681c01d0b0311480c500e9980c014980500030411001d00e02c0980d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 427916447 1250 427915197 427915199
    0x1b01180b130606080c01080901061a16080d1a1509190803070309080d0503070c080c240108011410140111010e01020d0e031602330403030336020109 65
    0x3032891007000044c144120103800c25901080c0010a440c030b000c1d00c040556450031070100030b0150440030310907144490006840d1030308401030311a51081610311015111541c0040d4640c040481a07010803c0341501110501c1c2c2e01078070409011180c03524241148200204020f04003451a0103042446c406411802c0b107000315480d0300960342103800c0700104a011449a0720280132214003800b040344c1440c40c41c90640c0c11881c3c0800000d002021003a00074008420005005005c0c0406200700b8440304072501c00b440f07001400606100c43c1c03400c24400c0c41c0142d4600707101038659600c3c0341c0460b400313101e81c12965202542040707034401c1485a0801d500d8103020900407426038440081c01030041180d217050006031544441d41034042030710b180c100380e098540c004128150840c0c0d90340410058554042d100c20413440301201610309500d4104400c04646508030410b1130242880704c00400580b446a40c0c2400b40c0d1080f0100a20130400e40c4040c500e140402c0d030000218031017243c6250150b42e0052403c50001c0e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 427917697 1250 427916447 427916453
    0xa0c031b06060306052d1f0905090c0307060f080a050c04121202150c0a08060604120f1101141b33010f08030912011407051b01180b13 59
    0x31090741d80f003201d10f1500c0300c04001000c1d46d940c1140710440b51005442c1000300d00c60070b44220815005200c07a81001400d03840301c40b40c100400c0d445000d0074012008111606050310f04c55900c0c150410200d1180c856250040f45103849841e0b540365000240e1903401807074844038154405031070000c00a5403080d00a00000031a4083c820074840c1c000d001325403250030490380c2c0030000c0c141158504103540c07004031041400301c00300f001002c0f034044c00124a4016203c5d260200040c45c548125030100ca254040404007005200000d42d0829607907210320315103c2c25046101c01501d031401441c40c55007032000c042c049000f10880788104400c0041c030700c4e020703101c1145036004041d00c4a811414a011046140d070b554140030b4551503540c03409000f0f003a801011003450720040070783e80e218140d05140180c4170202003540703402094101c052501031600c15541940303800c0c42c0c01405070308000010700302c0b40300c1046030a10110041c840c4c5251203209009402d070200d0a501d400d50f020402910303401c031543c2c2d080598404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 427918947 1250 427917697 427917701
    0x301020f0714010f050f06040213050a08030414030604110108040c0302060304060902030c0d0503030a2c0303220c0308070213110c15061c0314030106051e0a0c031b06 73
    0x250078402c40041020300c1146401ca800c45912840d140c5800b031901c014481c40c40c0320a0705150384803008481c0966100110031045440b11142d621503604641402c074007003121003011015106945035000c10441c071180000c101913644d80262009004400f40182d141902d500c914900b6600502522420900654036400310f202c0d40c1c400c85040d90810b503502d100d5811441c06201c100c8140341d084408050100060701d805d51a4480030f41402c41e0150703503003d018800b0914000b485802003081410a20072014482c60b02d45039841241c00c03068840388400c0c452220360b5000d00c02c00303071980c0000c0c10600309819584c500b2943e07800054140e84c800e519040000381c4812034025039680241c62703032429884107540000c0b00d10b82844160f07a40c8451144600f0004a07864020070403403840d41220007480100d40301c3c2004d607129414030000c5600c03000004008188170380c10000a04000c409051100c1c0c0e003501c50301c10441c15004422403040012682500a00030038410301f421401400e6000307103880c0481e480c1e81c071801 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 427920197 1250 427918947 427918957
    0x326040f0606060302031e06040e100911030708030703081503030c0c090a02070503070b040f020306010306090b13050c040c2703020a0b13060f230913060f050f0301020f 74
    0x940810015480310420419015520007010207003415419820320b03414610641c83e0014654054405080c005034095559400c07504c1600c0700341d07055440d081503030741032400501204441a03590084c0c8448218890400041c240704aa40703e070095401d1030804e075812681400058401d14200f61507002c0c4c540180d509100500007859600003c14003c0341c02c1c7c0a00c81c10502c01861440e040348140800c2002c204084103d401007035010612180c1e590740d924000d41014940070019402d885494008400c000040d4404071002c0e003d8282c10115a84e80c20000c400360728041402451030304403c00d131002a0616810038844590142091100214041c52017032041c04202007820042e00c081c4820015400c1c07807d800c5011f00544200c01c0d05d0320f001c62440600c051224030807501040f007540b601c512030a01c40d402d208030b103600c102c01c0f40705881044240072440f60044540305200b400301603100003070500d06106920440701000c141c010224a0941042041e5114009107078040d5002c0000000004000009003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 427921447 1250 427920197 427920203
    0xa0510030b0903120726040c0e010b0307020708010207150515060a020c0f041a091905040c090b09150105210f01060f02030309060c07020f0406180b09060904032604 72
    0x55101d024201c030b92003602001402c220b040c49140e00c10040d1062048421b08910040c040700944182c9461030521502684c940c0032001c844000000410307101c000c2c400a60040980340d003100e140382d495421080c200c0c419842c008100301c1c00100e9484044c0c3c000d4100c0b991260b00b21160340f9140d860700d03011400a9024051210042c0c00102200c1c3d00380c80d0080304400303040001d58041042101a00e01e005d01c0401c1c1e090782e42e10039810354000030100720004400d02d00380590040144031034205031402d0003032800c00d405080788190400700419080d040c589820362103041070713150300c00702c0109020054030700f68424006410b8880c00009583d82c8a03915214460185550083c080001e40c9800b10007418032003040d1406045410030070510003420070004800340c101c45110b05071581c0d130240d880000e030544058591070303400c20700304500005c4061000d40d500c4401e840404003801507a19003020400307044400c41c0c0341d990208002021801013403094040300132032107111030000a0f0002254500d01d10340c800304c0d021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 427922697 1250 427921447 427921453
    0x30b03100c0306080606151b03070c141801031e0203060906060f0607120e0a0e07020703060b0d050307080d0608070f3002040b01120603080712050c060a0510030b09 72
    0x201400b03074540b103024000c0c14888064050360511030700190300e56009164001c040240403920400c4400500700c04601e81e60884201c036600c02152610303c071080450310070809281360a800280710340c14061441030b410026aa507500300e9a0030b5548115185402080c4c912810031520707000001a1010403285001d103440200402d51071070300f00e08103e001407051000724010034041c807048000601540340319140d4034481c01c2c10070910543e08042414440242d20200c2e0f103003030007820b0000440e00494044243ca011710002e0092a414a00740425150030020051141d801005030001113500302000d40082d074020440810f00d070f42d803942c4040c9040100c0d0819002c245100c0d60410060b0281041c01e101c1e0f401808241c030229810340e00f281400c0c051441d0190040b80c4900001000e42e11580b1960002d1120440800c0604e860f03007042055038100000484500c446903040c0c40042e4000d1060b64140d1180b4801071141c0d540d1800f004c00a40307006402c3c800c1060003514040001039546920500c070b10309240003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 427923947 1250 427922697 427922711
    0x501090c0c122f1b0a090e0c0603180f0111090103240b040e0601020c1c031709010e011d0d1809020f0a1704020a170f0a1b060f0c060903030b0310 64
    0x20250800d070104260041c00001d611412600e500c9140c031710b41c04c41c1c0c0c41c4d13031000501030f096080180c10003030241e454991100000040204544080940c0704021110f02c0844602518420006088400c101c040743c4000c4801c0c0300d840003540c80794201416480700e5a940d9004003007600d01c03000500d0000e82010060398004541403284031030050351180d104c0e4003440100102c6c0072000c0428490343d0501501003c11180101200525000c1c0c1e0400340040c403050311049903860000360490003002c4a0b9000451942030100c0c80f18090442400b10074103095510140c141051600815030340140005543d07400f41c4440f00700020140d40300c1c4003403c0103600308540250b641602d007800500b40c900d20030801000302d09980510015807181c2540e8400c0c2d0701c160858016100c080c0c41001d1810075038001d5034a451040300c03010401c1024650002400428036107642c6c01d102d1b10b806c0241c9100384114640300004016403104400b2441641200e801da5029080001d00030341c80c8804213013071180c0340b01903003801c41c1c0b2080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 427925197 1250 427923947 427924037
    0x206040f031a0c040306091b03030e0a080616080403181203031107052104030c14040c0206010e16030b0303031005400b0a0906090501090c0c12 63
    0x568403904103000c400702502d03803030842e48000780c6000741c0c0805480940e941041d00d0802038603e441444c4034036603038440038440ba5280340c02070455000001c0f0501603003c0d13060001310643c002815030301a10f50386418140a00703c42d0f00c02c03140820700074015420810301c00c03500101d00281d40e00000c041c24140b640341600310441d09000c2e0035620f4440d1001ea07031403020011100824004210403100103525040049080340685203c541406250405801015a9040041c4001e80c000034234004860507281400101e590a40590300d40009101e0560040c480c4400650400060300100c01d940d102802c0000e800d030070b1900032a145800440d000342e0242c900c0d01d414000c0c0d00d410082c05590420b45141c80c040300061301305c0d810400788101c4c01201c08040d00c2d170f0702d085068140d801804072004064040310550359a595032001a0545100b2a98a40d281c28008100c0d085240940418181191a148141c0c182640c5e01d00b2030007800030303021003044402e0104241c0c41030000010001e21602014500300c00d04000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 427926447 1250 427925197 427925213
    0x7121b15080601050405030a060911030d0806091e0c22140109150e091005030a03020d0f02061302221505030f070f0b0d020705010f0905060f0615090406030206040f03 73
    0x646030b01d041c403805000030050390381c0c0003c0780300100742c0c00800441d10152500e091201d452070280036942c5801443d10260140f503000e41f8a034884e1204540c041d179551100029510b44080c01c4040e055244481c00001c1e0000c5070341c40051000c10307051462101c0300e002c2e000402900442c280c004c80d0014200c0c0c0048212507078080f48010142000034550307821140000d80c0940170b04290201c1600403006071001400182d0042d4020000349405003ea40c1085400e140080d04c8208010120300030480c00700302a03c84a2000a010343f1803214100e840304034050070b40810500a8015042400485595446070600446070040d0340c40703c9101a01c1009260400040600304940340c00d10b4030071980030071400c00803803c800c10244121820322050f6030395105501d080d40041c1c80b400078050002c0d800e00044001e020368a038020310040c0c0c0540c0a030b03425030300c90098030401c0c03500540f003840c2d01c4020280c0f1600c80510200041081450080002480b6030f600d5012038415007041d80003400416140e181082400a48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 427927697 1250 427926447 427926451
    0x302090702010c08070e0a080d02010c080f040804090f0f110a03111303060c14210114091f03050f1e0a15050705071505010501020c030c0307121b1508 66
    0x9400280000109403d000303000380402442041049008100500706403511042e0388082c1422001f5100403241080c8007030f0117800c1d4a83c1c45400a030b82c40c03000800104081c2c012500460b404000c180c0740ca480c09074440c021f814a62640c42c030b22030742d5042503500c0a6284c82032303010364446180b4881c0c03110700515000e000c45a92004407a0340060804c02c0072000c40d5044050b038181c95001d030f4001802100b080f0202ea540da410300d9000100000024000402804a0140101304400c00c2201405a881d0700c1011001010000d03030035080070200c404192006050880d4900400d40801511011580c80c0c583d80c0c44d000017805480703040e070405644010341c9a00d040309130200c022420014040004150741c3d41c0040713140f0074810f540c500c1e900c1011505040c0320b007003141c19190b0400368002d0b003420009030300801042c4c00c0c42024054400c809000c1c0340ca0401003a49200804010060b10b0030707a15003031002c6801d43da140000c60342082e05aa80e03e00c1e2424038182c090140103111300e55000d442403d03502601101c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 427928947 1250 427927697 427927711
    0x1120b190f1a1018030b04051c030209040c09030f02010c05010e0709020c07080a08040608090717150f06010e090a11030c030411030303010b030c0d060b0a020a05070504060b09060f07020405010f030209 88
    0x2650442404c4601d09a5640883e0741c0480c0c1c100c1d0540c1c4a060042c20f180b11418094070898000da0511000c50381a0040e00540300202c07804c0050203d07031031058a00c0c444da40f00c001c0000d0b00307419403100550300038010103109500480c00030904140342902242003161640046400380c2d40418100d91007002000f01801600c980002808151110f890320007450080b48078950410904a00141d10b82c482806081d006120300941e02500b181c20b281035a8030303450560301c07075404440b0450003e6403002605051174000d89040e11003662011a080612030f030203000410349410740b0740b620301d10410302d806900114820781840200d02d4480c202031511494480c82a40a54444d51007270005005c05111715044903004800d0b41e5203140d9400c00c509502e0040e1103907a1250b41000408141580c1c0d850b00031400c810401d10450a0358040c4d503d0750100011120140140180c0768003d1161000c1e504100009110700da00b40c40c1000d080c06510780c001401d80300260091100c24441100820841c18911800c60300124 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 427930197 1250 427928947 427928957
    0x9150210150f05032e0209030a1a070e0f130e0a0308010e010f061422030b090705041a04020703020723090f0f151c060203060901120b190f1a10 63
    0xa00d900e00000f0b00007141e0514503240c10110810100d0740540d0403030750140707805405d40d485180c2750704001e409601c0054100c8040320240380080c0035103100d8070400035400d5000f00700b160f4043c1c012040c4200408140d08503440c4542d603c154a200031001c105006140344250364554072581002503119200006a114800d1400c03003420500801d5004143c1c01c540c10480c40d089a21014002403092600d103d0400d4101b003d41f49403004800d01c5880041603100781010303c1201d00565070b40080c0422203c0024200c0115500410609c402d0300d015002011501d02030720440c2c5102d5240d25241d2207561024001680350805000002103504011818a500010200480030b80d0f1800180902041c1c1000307241a1240ba9a2071442085649003150000e1000d14014400340d00a007a10700b040095000f81c0f100d920402c154400003500340d0301c1442c076043c0e43d0742c0400900105d440d204d03c081101c0700304140e8244070303503100c0c000c04201080c540b251074035406645032400714820410082c40200ca04568040c42004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 427931447 1250 427930197 427930213
    0x3140408030a0503040f020409050a11010e010905040c031122050406050d1202010e0f070f08030715020c0307060e0c0a0f210218010e15090709150210150f0503 70
    0x101001c800e645540380e07141011a43ca81c3c1d0b6140c2500004050030009511034031b0140701d58248200041d81084080c400d011070102c08038140010344503071811100d010b000485010042c82a400c0c40c5d008012401c0023418003107918003c80d4100e4900b0f070000117624502d10302101c5644004041c500c504c100a22060b101000b4140c10500401c04055070620007804001041c07040032100351007540820100c007141001c1e203065120b0650300c50780f50505885107400301c503087c83c2e0200d5011000720440300d882e58040c40100599104c002a40040e4100b00c40b004503c0c0400d00a0b0310104119004440300220180003824103000040b040000500c0c2641084405424000c018450303980d14050109040a150090340752030280c910014242c85203140f881c0026896100001a06000740586a8065905483e104800014810500c8508841116890000307200b150703040006250782541c0c994907010502c1600d45500d0800ea19400713541400c0d64550910746c0c134820420000b0f0000020401410048014114907 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 427932697 1250 427931447 427931459
    0x903021f0216030f180f0e0f1e041b1d0f011a070501020912010b0109080102160209130b0c0c16030203030f0f07150603030f02061e070302040b040b030103031404 71
    0x84682e03960003400c0c4600280d81510700360180c0a0f0344503180c610a103c20400c0c1e21203060014924603403040395101010180402c8002004840b543e209103000900c4410307500318000744050071f10300030380140c0c1d803507240c50a02c100580041ca510405810410101c055990414942c2c0c2c4000708002e2491400b0403030a0014000452010081d45101815601c40f944810305414039500902c1010045948000c286848410095041d0421407024400762030781031020341d503401524240d101c1c0030032103048109032044180062406d07031102a0880d0f0643c41c01e0901404580d40c0c501807a105461140241c1000720b1442c1c550300007040203007840141a11003106091569000c80c0c1d4a0140c00007820b03a01e40b003c660b005d041c280340350644281c00d400541040b60709001c48510780040507a404250000345142d4071807140b460000509901607007020f0a041410072841c01080d44042000d40403004141d000c0200080c5840c9000141003d80080b0009940e44d500d94030b0b024012800d170fa00c900a030094240700400030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 427933947 1250 427932697 427932727
    0x90c21022d010305071116080d02030313020907030b0306090703020a06050418020d150308071a04080d270302010b090108010608060a1a10021f0e03040501031e0903021f02 75
    0x189050030700f0046050f07103e08400365014021444c203010284914a5102002110441d911080741c034a6003e40340601d002c07103022603c0380320807103054007510142c680c5007005007414442154042d03070754079001408000d10000207080c01c5040d0751440d05c07179001000500075490310050440080800d803e04901c3e0034500030100803007600d5a80c0380c2c000c4503404501c5441c280c0d036503041101034840003500340c1e403915102c0c07070a002a9000400283c1b07800350303c801a06407081940c030301cee80e019035080101141046070380d1460501414481100817642031a0740d982002416505a0101105200c5d4002151445034030b418080b0001050b44800e6160707040103820460964041070981d08041040804924111055001c000d8401c28041907508540c0c0c00c010856103d5011981c0c40c4000b000303c4a8079410058902140140e481a0071030400c61780003004100300c1503020f03901c0101941940c0b0901e02407034218541c4002103403074200040c0d0140c1c00c86c3e88004002010040c15145001001d0b804500f03003682d00c846521 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 427935197 1250 427933947 427934029
    0x601270903030b0f0a1a07061d0d0201110405010e090a0609050c0901080a0212061c0c090c020118050d1b0803071707091208092d030c06041503090c2102 67
    0x180446c000a580014404550000024000b154081c4080c10b00c00185030b0343c0d00d000301c0d1100030042d440c042e0001c0300300c03084c41c084600301e03401690352046210080702000303030b00c5102504403618141e84540c00540141c0a010300d42c0305000f0003689644030302060b00050b0103442d0080c411801e0718810044510081d8201001641000040c1d80d18050080da11580d450f40845441e40074026200d010400140040d0755085000280f42a40c003e204004d26009881855000c0b005d009080350480039041c044144a6404400644890582c0821440307043c0c80381002644282c0d840400541c038400020044410004140c5c1c1001350340c030b44420f0183c903161040c60b021600c038000900d50540007980e5152036031242070440700003c000041f4015500301d03070903440035013245101c100d0182c0628907480c43c051421100351400c0b0390801c408021020340070f0078210020001c0980c11511340b1401c49000c0f4002601524102c881d800703e0101e64025142d60040191543c04080040d103843d00d614a28401d440214124003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 427936447 1250 427935197 427935239
    0x1081b01020111182206031e03020a03080603011814070f14010e1305101a0a05041505040b0c010f15050105160606080a0b040b09030c0601270903030b0f0a 68
    0x815001c101000550310000c03030b9540846110b403c401017505c0d80792940608126031003098224a40e00950000007101d00441c10081c003d80c006003490000329001c1c1c00080c1e8000c40040001429000610402c0008a10303110241d564000c403e0103200003000402041001d00038090090320840d2601c0207500003201690002410403010400062058640940e000401a1907100030300207854440031409480789244194084500c07040c64a40d124401c2c40700301c0d0100c50741c0e540d40c64540703030400c210a0401c4401c0f287c0c41081100800c00021141c54106c09003255805410000c103c3d03008095569003669000840e004040c80541801c000701ea801900700c03100215900c6142c803c01700b450801e0340041281d58004604da000e440035010410031440c255504c164859001c1040b0f40e11a1074002d9980d02400c00452035550200c001401442c80d0b00200c205801a018011074000e800556100c003038518001044021a4650300c03841c81c68a4452002a585503058030741511052400500129000810220ba = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 427937697 1250 427936447 427936477
    0x12060b090303040306200304060506210d030908071a0901050601090609060f09090e03070318050a0b03091c050405180f06040b030c04090b16020a050309100e030601081b01020111 78
    0x5000410802d00d03040d46d4010a5114540e1689090700b032401c06441c0c1101c00ca4490011241200500c40c1420541f81e10340780480000c0c800c0c80c000040643c020003c0c40400e540e0143c0a0100000107400d4030550a640c2502140c0b41e1101e091400f01740c1e080d22005000c16050181d502000d1200c5980311540d10115083da1800c0d80359440000c0050f244084540c2101902a080c910003041860b0000000c02d901c61007a0784941c01da030f004c07040d0307408001c0e81c1e402000c3d4441213444040200310440405150480640002d581d04107035140d5a500c4a0201418581c2c08203002080421041c40e020740849a8440c04c21664071203860581c0c800306040e0300060945109654550360340030103440401145c4c0180401420400800b640c82c100f03100c8140c3c00729010000c41c01040f42c4658440d02c081400c591080e40300000b18105200c00c010040949000b00b8007100300103a03036203030003400d030b50410030b4034001d014030006401c03890008100780080d50407001040d419a0304100c2c0c051000c10a540450ba0080094190 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 427938947 1250 427937697 427937711
    0x605040509220c0608011e03053a0807112103090c0303070606140307030818010c0519032c0d020f03030304080301090c080402060306191512060b090303040306 70
    0x114030075088141c080544180711818000c0b802d1358000d01054169a000c0c44504000300138014a111600c40c10702004119030040d24070900b000b0041c50100b105440503510b85031040c007030a5080700c0401c49510000000414030018170003401c0e0024841c107042050394025240c40c107503085040111262440980d0400000000040d4052005001000340000005c00307070b070760b5400c540c103200d0b0140406000c0c49000a0602e04640c0726460001a140c00700d17035000c1102410000081c8098208411000038141800302d20b4040c84006902402181619038925140004090550500810110749240040b0b0b079104020600e886103030250401d0808004101c1f9018068401440410813515408000c282c040c400407050104200d241d4010358140d884a03a000c1081c09480041200c01c10415140a50440010030100b03a0a043c02031580c03a03081c020072440304100c0e9071241117951003903102021030b000031047c0404402a80881c01050010421b5022443c02c2142d0400003907140e05c01d85c880240902e944542c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 427940197 1250 427938947 427938991
    0x610051f081f090b0405160c0803041106030a1d010204080a02060306040905070f03030f0c080d020d0902120a06050f0906160201061203051b0111040b071a04080903070605040509 78
    0x1c50b460000e10110300303a00240d41c0c15101014040710800d00d441141800300203442d2010700e101191001ca8035a4030512003064544824500f603201800c00d0301c10a01a001c265103544414000314002d07611042c00285190944d2144003c41500031034040d1582d0040004001c100d030000717030030804039404484403590303516103400107401002070a100512a00a070707100042c4102691102c801140d02030b80311010040100c580c01c5a07440380701d05004000c03070000d1040c208804025400f81900d1000080d00040310000c0b900040c01c5450300601400156010a425038200290f80c0980c41e0000d0301003d51b401142081403025444080c01401d0300c035510303505080910014400d4200300c000f0440e0b25056041c0c0c030218180107003144c0c13044686060813800710304400340303280301445880c00d040030042e486824a4200300140b507003075000001c1526140340d83d005550072255020800390040e4814415581e03144440c1d414141020b0b01c1e5444182486000e00c4108102d03101c0030300b09035000e22880410030812064031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 427941447 1250 427940197 427940221
    0x70f050c010614030d080c03010e040503070c27050609040201080408040f180e060603070515130b07110901080a06051e0405010f05010f05060405040902010509060c0610051f08 77
    0x1031540069070800c40009a00d040752200202c0c2503800b50151002266801c0040e1518041a55200c2d04e00c4400c1004221903405400d446400c10321540030f80b8a01246600c1d00ba00780d02894001118552410040040880038040e9018903528000814040f500d0040c0006000950040010381030051240000341005600c80807900034140c1d045035250f14544801ea0f078a02d41c45882c003c6000c03186040c24a0040490002d11148105c0c40100100080c60920b004d210b400c600c1c40911240442e4180110600c44091154a001500c5aa0402d80e204c81850401440380c0c40c4403d03c039401110403138010b11906001003091015950070110100c1d031034840403880c60000341144140d440e40200f64041c00704000043d0484040401200c1e400d01c02030345ca4840d80403210150b48070392540310fa4100b0007003000e410309400010709203005041075810042d480b004541680c0c07024510809940040341003040340524a5050005413a0641e60840304200030a4001c15241c44408890240800d40380080c402902c84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 427942697 1250 427941447 427941457
    0xd02070509060f12150f09190c180504020a0603020304031b050a120f020606310b0402210c130b0d110a050c12070f03110a0203120405010201050a14070f05 68
    0x10f002c1649130903550310442c2c0c6914100c1c000340e1007409410017060300d1b00d800c0e0101c1c1d0302850601003c0c041403618583e400341c100603698800c03151070720000c0d00007030700c004040d80c00c4042001d2280082882d103402c4c41041034099950f0814002c0c94810302c01d00c80403a40c007200300207060000b8100c0320048062424198504080303080000d0111032078002c8034288580c071100d00042810300c0e800702e03003041e100c900801010281c0c030020200ba03004002405250a41a0300221581a12400000602c00c83c48008101aa4021503843d4a460300c0c0c10301c181548034043d640180d00c698085806820410703504002d1204503158030806100c0040800d84140c00d0f440c0340d00002c90005008001c3e40e4801a00b179029150350402d601e0750703102d030040d40b45101c100303c00b090403189501d6009001c03620001450b40c040d00e61f003c2e1003030190341a1081105507401a1400c0060001c801500415603840300e24102c00203094400c014650b29107503040c00307843c4104910048090342c0204203800d000c540d203032215208603124010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 427943947 1250 427942697 427942699
    0x703020f070b1b060403021018050a030c0201021006051005071b090501140a0506070303020a21021c0c0f050c010b090408130b16241b0305090d02070509060f 69
    0x14501d00180302c200c028010032a0119041120000c1400703402074907160001210080c000d60032450325011414107903402800d554503100d07440b00d1503e80c80d032500c51411180800c118003181512403824159030701000600003d80f00070600703100e032070300b0305021644014000200200b07008010503001c0c10044142006543d0940b5040d40714003050395901024082c1c4000c3c403036003920b01346580d000d8600c1d00345401345401303480010f405a0b1402045580c114020350ac40c100304401c000c079601459005410504891040100ea5003001d42c031445801151901c8400e01903000205914002c8282c943c82d800556080f0b0302d804d90f0a100f6200c00c5107407885405442c040301e90347d43c8003102c0b0040008000d5510003801001d802420840030b0709450707c140381428850312117958022000300c0e00441c0042c5a555250040d01c2404000c00c1500132108900b070143c0b0040100344000103090381e1580d14140e0f1511400360301c103903100000c0440070f051240c06500d40c44280107c50103203140b900044d1642d1605194500701ca10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 427945197 1250 427943947 427943953
    0xb2e090806131202030c03030f0903190c05060a0c0f2d0903060e0604020d08070302030405060d020714210c01060515181e0603060103140a0e070b03040c06050703020f 73
    0x7808900340d82807008000000c40f480307a0900c5203220442d100100b80c8202c481200019407440c0c0712000051200400200000200d100810001c0c0903030403858003510080c655512031840d82d000c0c03172510320300b807404c001d2001440d03501e442d08070f00c1c149621034007102c407880b0f50741854001c8409003422440400004940281c00746482c00701060400d40c405d100070301300da014001c2006450350100700d442d01d5040907a00658804030781040d090205070444000c04010348030340100ea142c182e460012824540190112800b016400720f208130a00c90303150b0440d003045400c07401802c00030003011806090420754810354482124081451000b03464254898000760000906c0b0498a0b9074244001c1d1940d4452920f02d00104038000c00415181444403402e40241d20108204828042940c24010f0700d80004050a04160720750b01d00045c80f24840600c2c9005450440c0c01040e80a0100001d600c1e00302c5540c089268414108104000702d803013070b480901525520f141140e990007850400301d25103003d0958208442c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 427946447 1250 427945197 427945201
    0x40e0105100e0108060f0115120c0e040e0d05180f030f0a12030207030909090305090a08060105040c050c031213050124081515041401090509010b2e090806 68
    0xc4070055000c0c111804120340e80c006a89500d5645e88900c004e403403200c200744000340140921070f41000124945a42450456080321038050814152208800c6042c04585a007101d442681000d026000d0804a410b000701424031405000070100c0c4030324032401d059a41340fa0422170381540c03185001c9201040040898140e0301e80302842c90380b12032020a044811071600546000310341d00174000d9990311501500c84c1c14500b464084100702034030446808a00700002040142c0c2d540d81c50340414006404644c006150544c1401d090204981f00d1111000c2441b0041c00030311401c40f40081100c0800749014042042c9440b001400c1c0214211104000c00729401e001c0e00d0440c00b000f09000c00b171684000601c2c0000540c1c1c4521858032b542d0584056440800b440001a602d80f5120400d8000c906004c0c0c00041d500c00360008003080c1007001e0b0000480d043c0c07214180240072900b4052021403500403034213a0380b014400300300c00341e21610100a02100c003100484120f801e902502c040c2c002880300c14240c03481340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 427947697 1250 427946447 427946461
    0xf2a03050c03010b270c0409020a03060e01081906020a0e1509041d0d110c0d03020606030105070315060e0114070b07110111120612010905070e0f04020d0b06040e0105 73
    0x8040101c4224025840c210b5003011501d0594000c03040340c4030700d9512104001c00c0f603030045403130707000100088141d25081000050585840c4002c00d1112880d5800145040c2017082e40069000103a10165096201c5a04000d49000600d0a19840c0d94880c400580c1c3d684c059070181c03070060043d805254041c0b160b00034400d090820324000c20342030750115010400c0701d240200b4078103460303009204440141d1001054040c00d5005003d4901d109000c0e00c1110100350880000510b10f41d90b042044005822400034445282401d0080d15003044d418101407000c614407000a048000d03a0388554010403650030390b2030045d40d0040f4103083e40e02c43c0c204a01030b0380e20090305003030001c0c2c0010744880740060240080f80c0080750040c8144020801008015468030502143e80c6c0710600c8003508403648840e1580c001c00e007401d000d03c101c04078144030b070000c3c020162504c68400ea003040028445040c0d407540e042008010398481518000c5a0350203001d40c4c1c1141c0301c030b02c04036000340164070b404801e5618100c140020303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 427948947 1250 427947697 427947703
    0x5030c0d0218150d0b100f1b02190f0b07050a03122702091e0109230108060708070311090d08070210050301090b120a2303040f090e0a0f2a0305 63
    0x40c07001130050a100524411050000003c1c82c01440d0002809074441080d009204502050020090201c8204800403a400281481100402e1a0460302e010102040b501c1d0760b200c0c40e28010410030514904100d125106c00d0380700d90351725400600704407001c12540303400c0015611403050061001c00c030410030401c5046001250900c4070099124100340c100184010800d201c80310b4446c0c081d10b241c400f003a4a48481030b070103051151445a070004070380a41003960103500030424001c1012100401980c2402a0003500c1030030007401035000c041c01c1c0182c03c01a0704150701220241002640c0081c0712860904224182d4001c0c440001d60029800803502010746d409070145050707510700c01c4c080081e041c0c041c1c03c0106483c0710740c242035119003000c1c0b8644003041e0308003601c2c2d500c083c02030f80e50707001c56030048142400d55200307402c05c800c0d81d10103031014415103001d4401c2c2070ba81911540100013071641030700c1c0e00960204008009016039110848440701400300413036908518004100100e2150720307403402c903031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 427950197 1250 427948947 427948957
    0x13080d02070320010903060b06040503010f05100614030c0a0306031e02041112040204050a0b030601081c1416210203031503010501030201080a0209010c140a02090705030c0d021815 79
    0x50b10b006040f210300d80b89610303050781c0d180048143c40b00c0d00858615075550f405007a036400500e80c00075082c88001880c2e102800b0b00f9003204070701c0c18009194548800b6101c1e043d6800d420040c10410b04490380c616415a000480c0c1d001000840700c2503c41009600850280103590001400c1c00b43daa12040d42284080100c481c3c2c503807003110140450701043c8003444081c0030764010940d0001154012401500f060742c496504065041c802103010341182c40030a00c0d04900b82e10039081a4003100351701c03034040d00d10850f09100c0001481c0046045042500030700c40c60090111001c00c03802c90580f69420005040f4100c0c1404550010498203901c0016000e900d070740049980b5084140340280c4032980303160611495068a90503142e8081e50345440741c9440003034010b800c00074180290183d61001081101010b1803a042d00200106040038a500c103018003050b000d0141c2d800c0c0002402408880514041501c0c00c0340c2001e240181c07100c0041011103040455a40056003040310b1001c695100e40d58000241 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 427951447 1250 427950197 427950203
    0xb103c03050d110610050f28030c090203060a0312020a120f08010b0703270e040b0601020c040504170706020f0a08090d18030303050924060f0f0303040b13080d020703 73
    0x28154075203188005440313000c1111500c12900c1102800e01403442d00362803080f03503100050484500c0228501002c00c0c0240510651341003140210410020000185275480c082c0140c80320560a5041c42d00102d03091540340d00005140c0303078001015415083c0b0810810107030a8000d010484544014100501040c511124602c001030182d00081400700ca800c0884480d0344d8960741303801d0800200c46103908901c1d40205503170103501c100d0400103507a444181307406004501900309142e071801c1590019150203219007005008030f003030070100300204500580901e1035190910f6950b558104e64640b6500912554041c491074100c0410701b070b0000317070340194582d00c0342d450b04040320010101c1c00c1d02900c142d0341210003520101c480850a02c002480780d048030380c021007010700725944400540f0302c84000c56020440c440c0020b450004100c80340c9000c1c07a00740410f1b002036400c42030366107441d030220340c59202d1400b6401a8040000b25040d5610801c0c000f900280400e109455920742403400080d1140c13030510080e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 427952697 1250 427951447 427951457
    0x10e09070e091f0512030d0c0504080f100b01110a03120f02031014180a020a1b05010f0b060c030301170c0907020a060609020c0a02010f09050d0f0b103c03050d 70
    0x71070b082c00d001c1c54255815100c000291f061071145203000703000d840e91a24110800c8001d100010700000e04100018540703000b4005811070b0010200c038001121039900c102d0f4100b004006050704101c002150354902d03960545840c01c0c0c08004d11414102400588001c0890b4500c000100a0714a07105146402035079201d05030030b4030064005040051f100c602c1c0804401c440640c802080e80500264010044201d09042191034058000400302c0d0121040a09940d241d4440b100744141d40300728450135041c0c460403a035540c10003920703520040d500c2c0414041c400003048095145010040100401070903018020500f001910381880c0094940707603022801c4641b1401c10401040465250082d40c5450100070010041c900150700110f0741e00540440407002d00800e1b0300042207c0d1244003481c01000c0c06141005c442070341c1854a0131244034010700c100892003034040c00380030340c01500341c0030501c40100c10100c86645440c00d424082851003410412002c00d0224070000c1040b80110700b0b4a407542c0141c443c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 427953947 1250 427952697 427952699
    0x1b01020c0c030a05100515270a0e070e0606070803010b04080d0203040617060103090b01090c020f0102030106082719140105150d06020c0a050309090108010902010e09070e091f 77
    0x145a074510441600a080360040d900704101c5c05400d5204551089205009035000f00014010030b148000030700706400120034501c0e02c0503007410318035603c40c0c01159140702000304091070070040d43c03140c81c20b00405031116081c20200e401170390fa2809540076690011174240d5256551002102580c3c8a8072501001e80600c8090440a80c0003000b84c0341128840c0c0c5072220180f10700200c025150f0002408641410754900504012a11070500d141c040c00b920440001c2007160580b001c1d181415400d200b0420f680100010701096034040d1900341c210200c0604061000790311131203440200251850032915101d0b15600d809284021103401e03070700c0383c0554840303440301200721081400c2c0c0380c0880f0701c401c002d000000b81001b80d0030030103441e0045e9801550b0060820400c048424103080f03c090302500c60b80d0010a10ba070140ca010100e090051148500030016582264006030520000c0b602c000c0c42404402c0c002010386020300d101300070380e450040882425180c40810010340b000129002400c0c565203c00c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 427955197 1250 427953947 427953949
    0x30c060305010f05040b030f1501051c110111120f0406080a020702090c090d021203030618070801030602071109070c110d1a06030a02060307020a063903021b01020c0c 73
    0x1c10705040e070740b003800c0c001c01c09030034901400081c00500c0000d035014411182d61074143c05041c0300040048080301e20a5450394941000c0101d0343c0400b85024041c2144420050001742e40c0d803180300d08451003070a004c1542800032150605040524403014125500091441d42d001c00e640b000348280e803019141c030a01031f16640d103608100d004000d402900b001c40314011440c5424004080d194081c0700070000c0c00c811103e0f07408070b13216650840c84c2409990011082c0651403402070020703502c0d020b14034161b0056280c1000010001a018072014055643c0000c421080c03050080745800019409400011103003020b1000421800741c9400175107400340d580302c0100c040d00e082174910810580258202c02c100845002180c0c8072038001c0d000076858450ba60300000141c603004083d43c441c400d140c01508000655080410036902e0041040381852860271412000604240d40ca00010203084034290081503240b800b03900920422000c1000610320402e13060001c0030540051030180e8204054070040e45c5000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 427956447 1250 427955197 427955201
    0x10050a0b10080613060806060f01080601020a08091f0c0c050102061e06040204270b19030303020d0617010c1103031b0703020a1505011d090616020703020316030c0603 73
    0x1015081d48240d06520400d01e0707602c1100a0b0b900808001c11907040540c2440c44c4c10101d0310741e540300601ca86c01400c10880c16103040c00304100080750a081c52100c614101c00001d40710f0050520040100d003004c2590700c1240c4031241c10002c070070145002c01c1074200715810b0150904202d05000c90318002c0c510000f20b040d504c0424014060003640f2840401e51909881580100b88001c0105420036070074400000c007030048500d401084003106441783c50441030116a83e0136554950390b05800f0b2540c0800c0b4141506012600b04206c1e9003600d00142c56203051070409018102950180f80d041c80984040002c1d002c0c10760014215140c3c540317500d01c1959004d44e0040d224082251100030140c1da810708520720710402e1006242d0b0754400c1c4140e502d0720490346d80306044403d0031a01d0003855a034900c0144401074441d04655517030919694200c1c2e55250400b402a56080d008001c90010603000d007140904900820511000c0c5038000c090784c06085141c00622000e8005120545144001560020302a8024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 427957697 1250 427956447 427956461
    0x904090b010305160f150c050303010b031f03020303160302030c06070e0406140d02010c15061409013501143d210f121d09010504090c080f10050a 64
    0x401a1400c5d140b9281c60740201c0c2c820118000c050042c00c1741ca9500040051000b1406040c0d14074080707889082400c6042c214460034000b039075500703180030400d2015981c00010744034a8002103c80442d0f408161404034110b00030f082d800c51a0340f28040602c50700030f80151914034550003d0314100a40d035070703c01d0110030140e00400901d0708400341c00000000b40d481540800e42e410f000d0800c000e400000c1807290400c5900650100810036070807481d014040c41d150030004d00508001d0202c054802e00411440c91401c12001d460548104074004d051032404203400a03800c910f40d5100003040b03494050704444400c90a0342d03000c60000444c49190150140c404401c0351515184100d010310507040405228142c000f5110241a00aa0303483e144e0000300411941011188244610380251030f1007403001c2c0500415040010320f41200003010241611607030b5600d81110400c50700403407240b98905003004c401d40240c0042c042805010341c1d81c8607000700000c00201801d00d407001005135580d00181e1004403209 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 427958947 1250 427957697 427957709
    0x40606181a010e01200f031b12041d1801091b0609060915020c10050c0f031606050417070302030403050601050307060f1107080f0c030606060306031906020904090b01030516 76
    0x88681d50285e802e226108000150800d40103c5444803000000076186410580c84205802883c0034820310304407041c001291000b003014406030900382411014098588526000000149500005040d0030f0030310900c08009102c1000802480d070340c904156100204204101103500d2500300002880c502c030b4000c8500712545552200f0225041417503001c00c00340003050f52400c620448003901580e039034840c03e58204032541c2e1181070742e5410b01c000060030702a41400d90040e0b038000340b15207250407800b802860030340c9601c00c00005141e5242d01d003008183d5007003850985060404036003030041580020040056a01a200322103003681c0c1c0341e0400d9a100c1641c024900040c0307824089903101402007a0118003400b146081d1107240b13032900c02c090300e0a14030040d1000181c1c014541000d45013800c1c4400c5030032000564200d403a40c90120b021a5840d081900da20b03010000c21451401440b0080d4150342c40c1400040084c4a601c00740e05103212590020300042d2a00d00810f22480d007102c100d5500c913801c91f98 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 427960197 1250 427958947 427958957
    0x91303090806041a090307061407030f1b050903010f0603060b090f010312030b0f191518030f0f0f05100e0c03070e060f0301021b070b0a050f03040606181a010e01 71
    0x210401139070300c4080c0060060b54403844244901000103035180110390322203500d010b0b20320044c0380c003410013810307120110903842c442e81c580061094228a4451610805220b81c10010740c0c0c0e048000110b4010200042004115450a1008400c10120f0b400c142e41e42a022112149151034090b800343c400c480a102c000c104d00464040d20504901940201c1c108030f1000344000300880e1000003140b40c1040d00d04648035440d1640704140548551000110940d40b590314100b03185500c0c01d41721380710040f0940000750141d4046c80c40e1408101c150003030030740a2540302c1c0070140041c409103400307540c0360301c4843d00d0325442c3c1c2007003074450031144001402d004002e0028000c282e52464681e0000c2e0502000d0401500a2480c0d9010411610240001c000c1c815801d44c4240d400001560390a08200040d046011200010869109540d502a0943d0900c40d0451002581d80d04c852034984000c20346e981c0025680d0080f80e41c403080c1c00d40740d41d10120b500c00407545a01005240d0b040110b420b02542d01c00280402d0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 427961447 1250 427960197 427960223
    0x1701020912070803040504090f12020a1511030f181c0e010305040b0a1505060f070b01050d120e0102100603050303070f0302040f0303111e16060302030c09060706060509130309080604 80
    0x89060313003000c0c5003a8042e006c19126049c1e03544402d060502c02d400e80c18096848403c500e0100001c6d43c80c04005a1001101085503400707070080315a2620001d0b1170300030301640b40070106004000110130075030191044405c071542e00018101d0011034a0843d8410b40200e8a10100340d1095400ba0140500c140da100e40f810405680e8200290002c01e903034100e03a2100c004070140070980b48c4984008090100014007903a4442c1064601200300c600b0503044a409503110f0402c1400041c0d03500580c0041002600780008851035000040745040c00d080e9000c0c060a040110000502c00d0100046028146541d9524040c00c1040010b5090744275a10034030301d5010841c00c00b000402c0c401d84203002413510394416a0035842b0034803203c07030f0443c447d101d41080c00d4029098868800158028a100030085810f00b9421403a02040c032a0460040c00700041c0511000030f00039003007040c264001740107403400800d40e00d107074101b00611224103502802d044000c640440760200ea10000000c00d50b00c241d601a0803d5454 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 427962697 1250 427961447 427961449
    0xc0c05070e011a0c0f0321150d0b041e0c170604031b02060f0d050906091b12150a0605041a061e04120503030a0c1b03081017010209120708030405 64
    0x56000c4101070070203005c0d010110724010002c2c4014160021b0568030800719080e030200460855001900d2803441c02168941c030000c50701c4108041c650b454103c0300c0b8032001c0e5078500308001400d04009840740e192150011314810030080c0c002507401e442100c03130844005100840250703502d4809550150210340109290294034180d06141e41c0c00d0351001e02418204214450a07103d81d070800c07140007480725107410400241c000c04001711030b80708000900070040d42d03124600080100e021107105034040e04444400c0c00c690841000801702c9400807984204007032501a02e0880201a0782c06150b02c1a82014450141440c44403084202c00c940103003041e16104041426040ca1600c1c5071180b4141c0d4001e00001403911400031101546c1d070f0040010f141ea0b8134281ea00c00c1e080300e15508403031043c41055810030020420304c02c0100e1007a98903041006e038070303150030441d22030302501030340f1001002d15406d9210040f40c10640181c40b0703110081d68a0714580703a60068013900e80c2c58a0041a03520b038001c5c8400c20103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 427963947 1250 427962697 427962749
    0x2030403170403080c130e09010605040b030303281d0609060903070506190b031015050105040e041101030b0a09091b0b180d1203050f1008150405030d0c0c05070e01 72
    0x1600541441b03042e480b0799101021659890115200d514a9640d03040401c4182020700900164070401c40c00b440c60b600d090b001c42002095403825800510000303d5650300440495072000800a1b56120092480280303007610a9803607004503158002801488045032620a0000036a00c0c05907102026103940d030380b0400444041e41c0000287ca200e141c032005d8900d03040e00e040c0441100854051000300d01942c00c11500007005d00141e0001d41000800c000800c824010b44400c0d0360441d62003504518007100710340048010741894602c50b40c0c800c0311161b0024074000c2c0c44d840314010310320542054442c0d9090b01030340c440e09026032191500c2d1580400c0150f200c1c0d1003510000000c0d40009000c0e0780810940d441d80811051608048401b0035551000c0c0f01c43c0c0303036080b180d40d648201c08a501074000d9080821143d2078460314410441443c0c070b0113005c02c0400a051054681d03940c0010000c0000c14520000240290582c2e04203403003500540e030021030301100e11608541652112100304804103c403c01c80e82d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 427965197 1250 427963947 427963957
    0x708091810051f1d1f18030804050904260c0717060f090a0605010605180a0f060311040308030901020702090a05090c0607050a061d010e0105041205070f0c060302030403170403080c 79
    0x81e4a00901445100303944481001d0040300d02440c8468450f0107961000e071108040410421944046407807c0000a2903682181c1c15640162100d001030f40325407800040d000b007410103000b0f00002070314444c2e00f60303004840a41900e0310040c003291105903031180c508070401030305000c50025810510014000400702e490b09608050050201c400320410341d103e09044603000c1e040000081e100045440019100105401080c0700407901c0c2c4403143e14281e0107018510043c4280303824075455406100000407800142e4000f03507000b40c2019134a140c03a8820310300035445504104d00c205a5480891040c181e1403065a114046131801000e562003054100709083d080300354110380c98416403880400003030440c00f8124106940e40c20114034210940d01036800e55100d0150b0b11400c2e0314040801000c81c1c841c10038080340c1c400600f40145c0c0c42005050851070f090780100050b080c05850f0500050455040d4000e52185000303650b04450f04100c605181c86019050328003600041c2c04001042c1841740c2400209 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 427966447 1250 427965197 427965227
    0x3090109050109120224030c0a0807110604030305060303090a0806010801142a0903010c0906090b070503160804241b0b0a110d110d2a050708091810051f 67
    0x1800c441c50200c6c104001e40d000b00c2e4400120320001c03a000c1d0760035410602d040d400a81f541010412750000d10304466885900038400341c10941c542300400c00c1a201031080b1062480050208a1401d4a501e6140e03a102030a00c941c84880d0720340f5164602c0c52002c0c1005c136000e031851580701e0464050b042c00c100c501c107201960581c0e8102c410004805595030900c0703000810340154489407000f51405c100a031244809a101d42c0c4914020040800060000f104032010807400c1e0000c410701c00414200102c041c001d030341142c1000848032440030a444600320301c2d010140751964807521101c9442051105040040d14020080045100407070708071062500004802c042561409003842c404070450b80075606007503450a09140005a490302160a5004004c00a03e00e0b00070420303080c2c2c2c91444511200301004c0302c40c0c200100403500900b0400030001b03c034204400100195040c1c0140040d03002040703015034510744000142d00e0002080c3c2040c0c16a44541c1c2c2580014200000e0122025518088420001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 427967697 1250 427966447 427966489
    0x9060c1e091507050d030c110a0f08040302060301032607030e0105031e010f03030216050f10020a0b0c04090c11060106180308161a060d0f111002030901090501091202 73
    0x350300442d1110302424100d4061300042c15040c3c1140005003c403441c1500200800502a0344581c2d101c000081c60300d182a4440c0c2c42050303080c1c19083c0b41000d8011900004c2d40318900000010601000140b026004201206403401c0440c1418440c9924454440006e003c076090520068440d07004001960b4401c284054a0200030481c045444504800342c0200ca4400b9401c502801455030400c201e118440038031502800080c01c18001a910f003050211440c440c4002e0510380e032440f8400c0c0007c86600c0d51080100d4a2030400441022064016020382d0100c2c41c07400d0ac082e0038035071151150b4019900c403000075100603401c1400c00c4500c13420b0300321440719041c244100000010300309402003003034450f9400c1966104c1e00f1885c10120b460320307080104001501c0c1c0d1080c4021599880209134101c0c0e0b00504100c01e81c6180d1402000025040f00f81701d900410403100140040c1e008401000840c00c00d0780c619025a031a84015610a420750103a802c1039001320b411000141480c6611070144030040240b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 427968947 1250 427967697 427967719
    0x90b090a09180f03021b090903120c130e06090901090c0902031017030a08010803040b040603021b01140402010f0f1d1f271401080a150e09060c1e09 65
    0xb4440c0c0f0745803002e42100107902042c0f0300720442408603094400414122694801d5080240100e980d070b00810360034003000100b180c003046044503084201d4103e40809500c189041d6174034204c400f401d4004540c2c8901600c1c10b080042c5421358184603142e951540200480141424264102e00940000b880307548010780c80e41001c10b90141c107040c18500c10006200440d40d9140c4480000c201f198181c0c840c1c05035a10a210a0266041110954050f00e919160041e21803168421000885010a01107281c6510f044291203002d030390603401c144214001e8941c200410781c181002c40e1a05100c0c4480c00c0051070300540d401e00009400d6180c1880280240f007041548508034544e142014600703840004110703511140d010ba190180c604402030815581c003c01c04920342907080c045034180048060411502800140e00314265a10072041000c1140d0000f03150b43c0c9646021120075030a5668420300d01c1500c3c0020300d000c8031801107503003064044821050180c07410f84010741c87d40108141030b42c00a18122 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 427970197 1250 427968947 427968953
    0x50601020712051011130306090809090108031b03160803060a0f0f090f09030f180e150406090b211033052b0204020a0906090b090a0918 60
    0x80750b980350342c010000741000241c0d411402e021078029600a074a4244203020101802c1680381010040340d400c034601003185280c52030007624503c1016401e581c000c200c98004a0940e00001c094042103010f6442074a601c0d0300e0702182a030ba030103801c25030030301c0c2a2034200141c0041c3e03180000d180c0001005d0190040c068450200344004030482d0401502804218010400400180500c000d01e5882842c200801065600e0041c1120582c503501003d118030b03d0b1905940d03041e0046500f0040031002400c080504000f90409000c0380c0428100e0720460a06d00301003500fa8081c461000580402480051558111070800c40c922174020181c1265000b07c1e061480c1c0b00e5024010280e050a0780f2945900c10a45404154105005908150524a6425070501c0303951600e41500b80031000d0901140f024900c1c0f00303c510501c4035060402500070340042001d5076100d820031244000d41c0e01070746800d1103807a210105071000b4002d81088680c040342c1d502e410080c190203540581e50010354614504a1451551 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 427971447 1250 427970197 427970219
    0x201020c0604050f06070c030e060a0c06090b0709140303070605040f050a050c01030c08070905150d020417011d1c0e030319030501060c02010207090c03141311060702030a03030506010207 82
    0x44090783e07150440519000f0102041c0103d940c090b146040006490a554900030041e00c20b0b03202c03c0b40502c1e400120503107498003e05180030f40da170740b1040501543c51a03281071500c032079098480201080e0440700101b4800050449035080311700240007076003001515120200503000140043e04d0045c2ca14490b40d02242080c031680c4079032800b45c0e0007000b140d140d0100060440340e58011034010002c0e03003414040306541c001400001c4442c1101c1c407407140d080d84564000c8074403452450b404000c0c030000d00050549448188a1003a481c040001c0244800000300024020300714001d07412a600040b402c010607411180325a100c1c3c1ca03ea02d8030200303011050003c41d00c3d680c8040c0345201000d28120f14502c0c00d40c1c0c14007503640500780603d0088a80c46c06540041c0d40c038203490040c00d6509869044d0b840c6079030300c03d4cc08040c910211b01c400b944c40c0d0900f411044d075244d03403010307064071960b01d4040f9812082c00d021040b00c881590140081800700c20380d480440003404040c011034114040d88100180c117080403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 427972697 1250 427971447 427971451
    0xb0432030304030b1f1202090709181b08010e0a02031e07080f0603010b030c0d06020f130603050604020a0e13090803090102090a050d0804031b0b0d050a0c030e0d0c030201020c06 78
    0x200f606810031704203880401c599180b0300c0d03e2034640446005040c4401ca039402c1440b4141a030584840304039448000c4180d544050030f422071201441d019980c0040060f203508485032004182d0000c01c9507481c040f2084aa03050240102c660130581072011800b401c040e9802103600207072000d0329210407002c0d4801c1c48188003040d9010800954100148002c000d40c90700038542000048000300818074450300401d4641c1084c1c40558411031000c4134140600003a40c0444240440d004c004a40e5030302c040e5000c03800c800940c0174000001e4941000200780742050701c04c0700c0b103003034041c1c0701c44610741c00003010090440c0107200800ca4150700c50041c00c0014800710059401101140c00140c0c5450802d0144100001180c1c4801d11034a4a958500701142d0001c0844007038980100e40e0a00d0050581003030150745c1010b620207041c4160001e00c451382d03070207030307a016602032440c250f406d0003c1c8142c0d80d411425140500018003d070b0b00039640b101c45c05030003120b1340590076100340009801c215818400310b0070301c101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 427973947 1250 427972697 427972703
    0x1050a06090b09090c041509050421020c030606310204090c020c15091c120905040b0a0519120807021206070e0409170d0b03070b043203030403 63
    0xaa00301440480100e0180100d6a101518429210b18011021540c0e800001c0f0343c2da40a659107000740300b007104000d8032150260031a02c01c1030200741454038124010b41c440d040c403d82d07002e20b1001102101c030b1012a18103000000100140301326201c503000c0020f1148401401c10030f800c1d0141e040c02c40f07183c20708201040c1c5140c1030001a29146000c1481c0240c815080c1c1c41411900524440c0b105507580c1003c901d900b8190701c0c55103840b03540d0800420038000a0029a0b07a156949a48074420040492444400718526039600001c0a0360380c0140015a00c00001d2a40c0c8071608a070f0910241c201488109e6040410030034600203181c1d030303008902c000f100414040c1da4011002480d081541807510074500254003100040040d031900e0500180100703c0518030714825a03c070300c00407042c80170211502e110759295420f207075964240c40840c5c1c00181503070341e14507000c2c2c055a400000e258022100303450494065070340403204421b04c508026800607504102d6581c1a10002024111341c070104080c0c0b000d0740c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 427975197 1250 427973947 427973951
    0x60509060412031103010e1008030309101b0219031e02030c0f0c060412021f050c0c100909051026010501120f0f02130516120204060801150302090301050a 68
    0x2030500344a415201d94a0300c03101414280003601384201030034400c0300d0444180d6103142c1d5541c1c0341c0c03054003841d81d0a03e074095245448080b081c0221a2400300309090311083c2141e082212002103610407244040e03140c00c6002681080034141045c0501a00c291600c81c424a8003500200308901c04038400c0d030240001000592003c980003045600801126600d0364103d0b00400c03025035000d0000e5080d1050740510100030030308c05000320071074450358120b011300703034080003920054845100c0003809504025041052842a42680b0300182011510302c46228540d0342d03080030103800c100740e520240c100074200000300a900d2100003075842851258170766500140300c1d588030440340c6003030543c00c1d10300c10381100590706401c103070490001d283c0000107140103511000d081c4980c50140001001000e0b80d803840c1c0d5007941040100701264518604070342c1105c250f51504101c40c40c01d40c03e103000324061800b42201050b440c1c401884408030300c904d84900e200302443c0140c43d00040502103804c0d964140c48900800e5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 427976447 1250 427975197 427975201
    0xa0b0a0605070c0f2105010e0709050402040506040c0813030c0c0603020a0801080724121103160e0d02010315090f0f0c210506010c0803091506030f0715050706050906 73
    0xf040c8400d09000700390583d0a92403582c20583c644440140c0f0b51140304c1a1184612100704012081d0010a041201d0b9010ba8074840d60703a980ca94080c100865040703100750316010004640346841e00c14001a8a403981d540c02e001e55400300052031809001009a080c851064005400a840c1200ba07a0244c1499a405601c071007400401900c0302030706070000709060300001014042091b00345141d04040c4510280f207461010100c3d8181d4040600400f00f00700f032401c2007240480e83c034000008500590b000840380715200c1e81c1d039104580d00e00d8005030095200201007090805076200e40c000304103914803c0d010482d143e0307580e5452400c40f41001e842072a04e40d20f031450002010800d10401c01fa61210b400c184410890007216218145002a88200f640765110049819644a0101300280651003241c050f520f08006058550350940304c0e0070441050644d0f000a80d050901042228001c41c0c0c160042c00c215044c40c82c041010f801075508d070010030509100d40c00c049031850042c0341c0107000b0a000b030602c034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 427977697 1250 427976447 427976453
    0x1d070b0a08091912090b16051002041d07050405030d0f09050a12030f0e060d09051b1509040b0a17070803030c0901270b0a03050a0605060f030a0b0a060507 68
    0x8403200501c41c01c1160011143e1800552019560741032680d80b1071000d4840e1803031981c069030549082c0c0c01c01c131980c6401080c10314421216854603500140500c0488650600400700c0400388c2c481c500643c040ba90240c402e1116900850284503003045550519a05040c0c44802081c0f80240070040c61001600e00b5564820182e00004181c019003415115005c009040c0001c2c4540d420034090300078104070070214020505449003031910540c4600411017603891042c0d400c031501611859805039090700540e1540e110040b84d807103808070641c0d0060b10244425400014035502604407000b11a002038039001ca9170000da0b140000344020b0040c114000c40c001584a800c10314241c40f41c4c01c40c11141d0710400500a29205480c00d03207109501c00d01c2d01d214000c0d400c0ca08080300303820180d0840105502070502007000c45401d4081c2144503125a01006156240c44a4005580441c410b2941282c0c4c10800c07101c12404a60046520500410000c0f928034035820204000388203e502c40800504081102010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 427978947 1250 427977697 427977707
    0xc010e060c13050117070c0203070b0c07140402160b041106040b040806070e1e01020703020d030f020f0a08070602031f0e01081902030607110f06010b0403021003020712031d070b0a 79
    0x3c0c082c28a8200f10729050001298054507000d0300c1e41c400c1c4040518044110740c1c00300407080c0078018244a1a0b07c6005c003e44550340c1d110940503100160707040b500c1e0b07071465017828030030b03640e4a1049015010420030300342c6032000c1c0c0e020040c10075034160580c00b01320f540e03e80b00c050003440213040d01501980d42e14030b040a001c1c1006006003100081003076803061311480355a80c03280902d41210140c510042601010010f0307203030104540c0300079004100300700d0326010300d1f40210201d500c3c9896a001c0d248041c02c1c08501c2902c0d0412000000d14105050015a0218000e07601540d0301c040d10104818480a80761845051700040e98404c07100348220800610a0a0090003e410f04070002c00040c01000d4050380000c1d103c3c50000c000b4000c10111149a0024440400c09452002229001d881d10b40d41c6410318003c499005000981c054550340c8490004a40f0a10032221089d030040d2125452954410044000d031620402d1040341e20344007800d07826450001e204090080c499141000d555251103d00a45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 427980197 1250 427978947 427978949
    0x40903050c01060617091f0e030d090b040204140103030c030e0103090503120103381308070323070317060609120a0b0f0105010906080907090903080601031a0a05060c010e060c13 78
    0x41c1c50b070402039001c4107403003801201f0051300d850000702280a40344081110310718069031803201046030406585000740010354613a00d014600035102400b40381c0003000110141c074800c0c88010001a5420003040100b8480c04910b03404403030514000c1401d40047e111645190054400d451115001000410402801c1503079550448444910702400d41030000006541c40c0300651410100d0000f500010000d042c406003006c003103540461015110092414010041244004030111808002e00144120404507056030340c100e50543d038040814810450f40c44e02c125010b0312203500200140643c80e02c2d035030303001060700c81c00c146100102a80f170b01d0350620450540c80906026a01e40030f031070040c816641e0286400e010703030f1824103104001740c5403404024a010001d0307010200c0c492034042d40b102050b038070140c07403400b90200344da062020303520040e1011102d60f8108103040c0e010070a40c13030420041c242440039040450fa00000041c40c07a44502d48142800c02c212446203a03020009000e030f140780101c0607404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 427981447 1250 427980197 427980211
    0x22150506030d14070204140c0a09090902060412110306091516020303071b050a06020901030c0306081c0c2a09060e0408160203071401020c09040b0105040903050c01060617 75
    0x160740c11040b0040c182c88450300040300c0380b0100140c224250b454a800c40c030f20030f03516024166854903001c61300c48401c0d04203207541000205c440f0350000b0b1030540b0f4000c1d03584458008100c641360620380200c01c400325801510807980307089120444a1156008c0c00028811007085002d4450700d144041c018140c00b80092103180da03482810120b10680b640042620b0f4050f800e8100ac101070403841903100c810b0315568100420038850000000d0030000e50345c001c0c0842c041c0032f0300c6c01e0001c051410300903415200d0034040c103800781d44030901104101860018142d1030a51a062150b1500415200c0d02480d001c1c5400d84850044c2c01c03044850882da1078440e0100406852000300030b45070402c02e0241d40407001030000b400203003000c5920800072041c1c07044550071507801011070307416641d0341c03c200050001c080c604178054080c81c81c0c900014109044142c0c80b550784030300012007a80c00c0008001c0240280c140580070080d0500c08a200c1c030000b40704040c050405a21051003d45d0a1040c1141c40340b4005e01304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 427982697 1250 427981447 427981453
    0x504030b150102120703020304060e18040b060d0609140712080a050703050f1c1a0d0f0c0e090312013003050f070605160206040b07082215050603 64
    0x41010610008550350010051000000700c0840781004034070f4021044080c1024507000200d0100b0550000024030131903100d902c0d600300e036003806401c00031040c1e8101c0440c01c1e0700481c40e0018001031000c241944d80700348014001125104181c0743c400440d4001802103a01c40540b40080c41031034000c000c0c103030040c0180103011021910f03da036840003502803258240207001020600c00e04041c09901900c0105030240600303034544e120304c402042a0340e4800d0408101c0742c5405912000003200858240014401416028a80d01d5a50ba0244c40120744681910701c14904200812034410100056001d407440c1c400031a110341603000715613000c40c0180e100d4070401c00004135280d400030000d840400700c80b1000c841107120044a041c1921184241040b8107c6550009015410013001e41e10082c0a41c8000103400c407520403c0d081680d4034a0300381c401504050b84900020900d5200d0400d035036200e52107020f2244280c000f41d40c402001390b01044111000f804526164130036824600c40c19500c140d0403802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 427983947 1250 427982697 427982699
    0x1e0507050a0803191b291f0b0d02040b03040317090303010e34050d180f080309070306020d0902010e1905010f020c1c1505100e0603010917190504 64
    0x501c4901c00c6860303054113009800304280e038840040c0d9034011000360000c0d038801d00480415900da4645a89402c145580c021b2000414400c06038108003030349155400c40f464401c03500380740c0701c1e124a8104000c420015502004046140303c40300001c1c6010310322948601780b091942e04c40329011210700030401482580140010080740031203034943c5401c46136402d4003400148000d5500b0038032034040d8401a410350415403150303c18550050081c89010103042040280d0075000d400b60800700a441c801402000c2d00540c406c0c0414400030003076401180040c100d500d02e954a90303c0342c0036600000c0400200326aa51100815560080b051011809040300d5a42c2c41d40310a5000c0441c004903809250304000042c540042c444c1c0c020419240a0100145480800401681c560905c0b40f14588101c0e064090b50492140d841d40c1030066178056503aa842d06e661030707814500449010040289403651540d01d1f101c455001c075a01c00c0708440003620141c0441c0c1e580301c09404410940c901079980c5010020704000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 427985197 1250 427983947 427983967
    0x706050f0f070311010603050f1501031a09071e0905010e0601020604061d060f0a0c050c101a0d0b04060506031504060504020f10020106080606010f0f03091e0507050a0803 75
    0x1048034200d01c0c04205603512100e481c2012510310b28041c808040c036610702403002c03050100000c1d9070284002698125035481060078100100700c2428440103040102d41e4403101000320806400d103911281400803140015a25041042c40c00d0301d401000c4c2c000b4609020504c8601c1702409101d01408210740c600100f410a0b400007941c0f81402003000d4440740e80c03540e40385002c0d103108022410118805080300c07018184908031509044007070301c030001c0980c41c00903c90405405074060321039480d0200d016040c1d500081c0c0c0240050610140850030744a13841d41c80400303583d140418402500d01075100040145001e00d031042c1142d0380980a0742c0320340c3c043d00003220314559060b1081d5026611003004207040d2640c4c070101b807519000a4409034084001203810100640c15440760088801003012101240c40750f100558401903a1a00b0000080c0c0400b80041c03071070f010f278100c49034040c85160070a8003804920403402900200c250304a030300d03400a40b410442c0380360170071150014250340000f0b94600700c0000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 427986447 1250 427985197 427985227
    0x120c0c06070b150415060e211b030a06060905040201110f10020f0c0106061106060103150905180304060509010306091104180902130c030c180b2a0f070605 68
    0xc1440b03500c550711600e000742c0c3d9110380d00200b100c076030b1039003800d4056515004043c0000c4c0d11280000d028404942d2118001c926040c55600700400d00b07409000c024001040070505481c80300b100d42c3d05071054000c1c0c0c00000d1750034410000100501600004c860615200040080c140c142d080321981d404000b22400445000c125060803100d02c0c1801030342c03400380301e8460045020740d2400000315441c110380090100e0300100700e603024844900c240c2c1d146696060040d01140d0604500140310400480217005003855544507542105c1003200300d20a003015000b01d2483d56103d03410030000200c010402009a58060003040c000d0700007144240542000322440070098011880b89110303024170084135203051400d5500414800346c028264054051480c040f4001034804904041d000034608480318000300c1c45607440d04580c1d00400c804003000703458030740010f18a8003e2881151114001c2c0003c00101d03400c1d05100740d5420300754000e081a9800700030042e0070000a80c0c400e001b882820050502003600030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 427987697 1250 427986447 427986451
    0x30f010c09090e010b1c14010207030804110f0409141216030c0c090204030318051c06020901020c09090a0501270816060905060f0109090812040201020a05120c0c06070b 74
    0x100d000064610141d50158090710b00c00540c1c0b07400010580684400303c1505042e021032070b001c0e4040321030941c100e581c948d01300e1098807805000111800f010070001856402d00c0b0140000051100400e032000c400007504950080c2011541103020550341080c111060003c4480d001c460340341c560921405c410071509a806c90707007000b02000071402c02c0f8000c2148a0544802403c0c0700c02c07046450f2501d03490301901c2c1c0401031010501080040701c00082529100d85c004030f04c00700003c10407807015081d6403400065000313411000c0c194001c0b0141c07020b07151110052648100e804034018040a00c0c03c0c01d00301e0844a5072051000c425454a00d10440a82d0200c542c1c140160311402c019030710b402140c03900003900c80185000b0401e07428450a48280400002d015018292000200c0c0b0b040c0d0f61060380310100c400f40680105409010f000101c480751196606c15401401801580e50800b41603848904054698410107140400070034411100744040000301d0b1209803d861151401000b500d66850f29240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 427988947 1250 427987697 427987709
    0x30e0d020d0206220b151309030f0c11040e0318040b06070b1005090109090c050f15130b0f27130c032903060a1104030f08090d030905030f010c09 64
    0x404491310036031100c0380080181d19082040980c450400706400c29034808a0107580344a024407500103135000800344125a070040d41a200c0d038118851070081610210000d61040c0da186012170040d5074181c481e0301450400f10b030031030080c0d40d540ba200c16500d0042583d554090713025620b82204444d954941608030380c0c0d03681d0020320803400b5507150340304030f503015036581c10a5810000e08400080d429030b0a4200603440d0780b2540208440c035407100203000542894082082c0e000300f04422102c40309050300001d0400414444400925944921385214554002e0050481e441800144900310280044a81e800c0381c13602700041c1034010440000400200000700d056501c03c0d0b80d0704080300828043d9102000c40103141182907402c2850342c0030464400035203440eaa00a0007440b000030704440c0c003882440645280c01041c58101030468503901070040c8a288115440c010800c080c0701076948411407983c0941c8280c0c2c802d02c0c0181408c00785400c084e090202c400c4140e04101c845040650085e0341d00060380c2e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 427990197 1250 427988947 427988971
    0x30203010f0f0e0f21040812270604090b0307050d08030f0112020609040f0e0a1212060803070807020109030606081f090203060708070210050103060b03300702010c020907030e0d020d0206 82
    0x180da11925170789100d85e0740814114410260380080304078040d030240403441681907000084031556092181c24101416001d0780c060420441401242007507809124082c4024089407041c686a0000c51980c1ca111582a81e100b04088100310b001d51110807080d001d01040d240900c4060300340d5010898030b000e4252071500c00c64440148190100055210420041514040760f100d083c0500740140418200607090700001c001c8244414901142c1c06a10100d4207035000852078003006846072049508030b221304a0402c50122000808076016004c0c42e805051200040d00300210321050184000c2a00c88684070a0f50410710f103400980c1d008900c003903110802d41450b000c0b940d00c000040b81030900f400202e80405142c0780011041c40314952028082403020740071111800741c1d00342c031942e050218030020809100010914101441048050982c0ea0302c103050a07004a20640d001a2020000301ca0000c00240e41750803001c0268001c0050b010814010b0000d00b40d184043c802c02034440200603c1400e047d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 427991447 1250 427990197 427990243
    0x14010b0f011106130206070501020a0f030608121b01140a0b0406060e181506071109072f0316050a03020714030c15190810052209020307030203010f0f0e0f 68
    0x1446004c1200e00588d03010008643d9445441009400d412000b8080d4001a10300380c1c003c140100002500d06600c44a1182241082c0300492540c214400c1a200041c607952101d408408074002e403515240078008030704021901d440a5401d0000311841503102c02c04200501c8540032030754540c1740542c210a000000d407520b0594504c2d4180890000000c0890342006e00000d62605100080c440d000300c5d80740c00c484004007a1150741c811504451784600e00c00e0320181c1218080d402e406100c003614006203003041601e0920a8180c020317500c1000f03800050750240c1040684004140d8140201360140884580e4031031580c482c180442d070784400100808d40102c031110b2124038003444031400e0341c6071903401400ca035003c0302c605000103100d03036003d8818040c2e003c0041c0700442d032803420498144c0e004000c0990095400f00c4c0040f050040c0265941c160707098016540d010015850038064034000415075000810489104900402140ca030880b040c0c040c0d40002c090030645050200340d1301c2407000306105090300c1c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 427992697 1250 427991447 427991449
    0x103080a1821050c271006170a11030c0a121a13060905091c0804150504020607020d0b01180e060115171015050a020d1103040314010b0f0111061302 65
    0x481452940c2c0c0075201c00c0040782c1c8183c80c9103000500c422050682c49840d21140f8941b00042d503071b0300810010900c12585400c12602071000310760710071011800440c2030940411000590ba00039500080b034510b00051070b038502e64003c4c800005004865004110300701150f80b2034202d02103c5444640308481e42c450b09a400e0384950040005084105800c0041c1e0400c1c00e005955100c080301d04034a13000016100440c01c5016001080c8142d400c0a008480e800c0b910040e5001014020000c0740d00c60720034044400561281030855644070703c40d108407041340d410441c030012100303c1061507003070450074901c407010352200120b5064111803252507903c89032030300c005080d5409544510480411203080c010400b9000a400120044550750070702d0200c040007a210494880c403800050f1320250348400407000480e841428803049903045902500e007050707125915a000c1140d4902d012803180c5d1200740441d01864a803407812440e480900f40751010070300c0c03510a01c2d11000d008000413030364a5004540c80075 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 427993947 1250 427992697 427992703
    0x604110103020d0b030f0304030c0515030f06060c150402090c13030b0603071a04060306061e080702010e070611070806040c1401120e061f1a0f0c01050103080a182105 73
    0x40e41000f000e84001d200c2224030540c2c7d030f402c00d20064420b0001c0c28000107041c10000d0301903c0b02c80a481406185540b06115600c0018020f0b02441c2c1121040000280000e400d00419010304079140792924141041d0040041d400400340445951920801c00482244480900344085a40c004070032069559a0130009080040503440300c8454000404440016252800188103980003078a041003d84c0d102c07141146c4141c4071281d040e042582407040c0b81117550140c9106a84000b180c400800c045501040c21410180b2644c80000400e0600e10400d08150003400494060031192004181914098541c04000c00c05442451841c16210718001c6c0c3c583d11500e00090040e02500007400900003141d140b9546140480358a82c910554000c00d0300b0220440010f20101c131440c18410075001c800021020b115440500840e142101c00c1180d02070340d0100303014041c0294025414680c44044101002d800d00380400c00c0c3c406c18048455090014040000d4041840d05543c000c3c004000464604145 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 427995197 1250 427993947 427993961
    0xf09041a0405031309050c0901030e010b060d06030204140609071103072009090c010e06090f1e010f022b05120a060f0b07050601030821010902030a0e0604110103020d 73
    0x1858400201000140700380000280038140480600021145c4c2d40d820b1782c1c00f2100255040240c800040110305a17a61003500b06000d8060803200000b0a035115a0000754036510025481141d0750301c88504106500e40f0344034a00c10041ca071400500140391120000301c540e1001029981800002030f9103610240040041d2900c140e840341803000d600c086583c0004040d00c641c9089072040c0c11420000c0c19460021541400031401a1219907440c041d8008002c05900080000b0f03422034200e014083c07440d030b42c40c06000c0326501440300c0307c1d09500951000422942e2202c1c0d01340159442004542c102826006d001c0d803132020819030420003191003e0040b51144181c21040b0380d014030580a120102d01140e03c110121148001d180c0c058598682c0e40c10424002d0300d2003d046078101c2c4e4010008203000e40c00404508600317424420410782c081044800908081e04422586d96000c400c01c003400c41c4c0f901c1070f084602c40040041140303140940d500303a030001808c00303040c0c100b540200c1c0045030a1000d41000c0c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 427996447 1250 427995197 427995233
    0xd02160b090105060901060c23011e0b030c09010e0402040504240c1e080f0403090803130320061e090409150f180f020a1d0405010b06090f0904 63
    0xd026401e0414500b400791000340e8049100700e05440000807040e0258140c200111340c00300004442c04c902c520160320101010344c40310165525100143d440950740c00007102c0000030240c0c0000ca529610b1b06051a14005140143c004d80d005001400103002540c50326a005504540220792aa034925180b100919815248601c0318540000203100290035004460003052a907a12522010500c48081140c1c0c0448101b4005c1840d000200e5070700900d012145078014000d040c11000d09542e50312061950307104901e280226003006409000b08156040f46100b0f800e101b00030840024949400a99a8420314440e80750600500c40418039002d00e0b41c041c1d440915004100304940b020900300404d610501c9190746c0500382c03804000f200100f11074800c0d084440494080001d900115683e0303c076540f205540141e0784011074100001e1000d80c810381700c00c0200391b02c5044880e1810545441400d592840200601c030f2003003803011150a45503c6200980b00710121944010f43e00c81c0d003403900c921040303501d6007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 427997697 1250 427996447 427996463
    0xd110a300f020307230915040503070e160c110d03090302090109091103010c080601180e101e05030606060d0e030703030e0d090f0611030d05040c050a0501050f0d0216 73
    0x301c0040d9909501a51103080d580c1c950f050a04504c00e20b40d0001482c0f4644da4002c0304060080c800c07242400702c0000380000400d40803c0c40d158482000900c1c10149a00400c1880360304070402c001c0040780243e0100310781c02410802c8001d40907648882c2e078030a00300032484c0a4808902e51906040c0300d0012103000b0750f00908840d100703503191000c050103070203546005d0b50011001d100c0c00d000c40c18144201d20030b000b8199560022a00c656004594508400070008102d0100d0900402d60074a400d0595004600710f101200340c0340d10f4802401c040c905503000401e80342e041680d00300210f0310082103060340160200c40385556411031603200303001000a6440c0034010b11011401204154040d441200c82c1c103800412581c1d400e0030300341e044500b4800c40c00fa07010103042b442c0d41045202d002c1c004c6244005046801e80c0d0a0403012811441112022101591a8040c0d040108220b04141c0694409040c1c02c3c40c0840c0781615151482542e4030030b40315040780040e170015100c1c404551100308070305660381c8030307001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 427998947 1250 427997697 427997711
    0x15040501120f091713140603040204051306020310060f03020c1509010603050106090f0b1210020a030605180103060f020901021209011803030306030501050a050601020c12071503020d110a30 83
    0x4a6070440d0052a105185d507294000c0200740c00000c1c000c2c64061b00c1c0b004013502d185035155402c0c8006014050054901424a03000f00c0000980500155110302445032a0504880c41e01c400103014041c0b00da15102403510400c01d5003028200403418071201c0c3d0340815151500d171141c0ca800d60042103981c1c00074000e5480c12802080c04c00154000b03d14243c8402c2e810300254a0010420000044203100c01480e64851030039019100e41e1500a0310128442c0e00b00055240d40e130f0408190b01048980c07101c0c40c0c0100b00c400601c1048020310541881c60207402007103050011160010b90b5951034280c40800c60300340424442c18583c4160380c901000c3c841c0340c01c44145a56240f41c043d028003d00c0c0401c80d043d500309000120130514070710600e0b1007107005a008100d1910401e0500407807103207c103000440f5008074140842e09500c01c04d100792040341603030340c01a50f9030031a010190442d410802880d03105c130000c22420060030381c041070020040401c8c02403020a2310800343c20a425000502e070100304141812070b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 428000197 1250 427998947 427998983
    0x301020c03030f070e241204060f0e0303100501180b04060206040c080a0f150f1a120c0f190504060f0e07020c2107180b15040501120f09 60
    0x800b45015028580200300c168030f4004e419038101d070b1a80000c0d9000740d504040048460b1001d0160295003403000b110a241001c1922020f00000303040703c0c152666a00d8000d030369901d010a2103900c10817400ca001444c103506150020100030849845800d040060b0b11050b11039101e01519888002c107450600d0a80d10340c0d0351900070351a40b030115070581e14a0038010000685907401b04507002c0881c0c0c403618481030803400b07603140700181585090f66a0415034600c02c9083e031140b5441001001d924090340c5141da94249070400000304003440404000d50403a144240103900c6585a00a850104640810041c0040109441d039001039070b101c145e00c10b0400000080d48402400340e036054822903410b01606507500401682c0c0c50040815098000071282220a031103076100c0300710450201a8425143d41c190754070100318003c003201044449441e9141800c05451800d01c500e100e02c4a04c400b019401d083c41c01001810860a0100c890b1401e074468080700c2c1d03a400c0700e5200242090340503c0040c46031207260 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 428001447 1250 428000197 428000203
    0x20a020f0102121b070b0708090312010b0315150d09020d050d08060112020c07052b20030601060f0822030306030b010f0b25140105040213050405061308090301020c 72
    0x139501001104c1104445818203050004075000c03241c1290079990207494460045606076401820b2441a0009101d030f0503401582841e41d90081107210f4200b0b8803800d0540000340b044c49030660302c92082c0030750806104006011000c0d50070344442c9a40001d01c0c1d801c24008680c0d1005820001400383c06010018504a82c0000030140a82400e076a01d442c100054020b120481c864031945c10055444072408100910b4a00400410700b10042c20340011311040c01010620503810f42811108002d070014540000319030504026081b403000c400500d455450140c02410702000c13220740004019804000445c0111852800003010f001300441032100041400c001707004005c5400110fa160402c0000041c491110030546410341e034021140703d191441300d81c08503202d0030300d0000c141d4012070488240f0003c00c200c200340e42541d001c0c240020509280910400c001103400101d001515441c2c00c0500001c1500002e040d50701c52107a4400200c0d0100500341420300340501d02519905600000d54404208404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 428002697 1250 428001447 428001451
    0x806040b0f060405070e131b11010b01020102070201120f021c0b130b10111e03040305010f11190306080d0c050708030a020a120507120c02090a0b0a09020a020f010212 73
    0x20a42140c07207403501010001616400e5a061000a000b110724060720302c1c010807052503800c5100c0b80010b041040080400700c540b01c0b0040031011421750f010380500810280180812010244021841e250559001805071a580407040119556480b03415410238034650480301e00240e50203001943e81207004980000e400340507035140c025484008448034901060040000b106002400602172080300c070001c9801e03e0b40c0c006c0e450310354400e1714030740e9040c081644070401180314180061a660350550a1080c01d4800c03d5201c00d031254604141c0011284600c400c1c0d5503c400c00c0071030301e94000b544e14011000f40516420079480e6024400342000c205421920382500d942c8036200381c80d44035507907522407512409900400000343c0c000c8108200000c0a100d0044c20401d01d60400030f0816140c0e4552040003241d44042401050030205241c06500e860700403650f01c290304002c04d010264200d03011a405920f14428030303103032940100d401d0303170114020302c61010510b9140008640b5030300b26080d016004002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 428003947 1250 428002697 428002711
    0x60818061914040b1e09061f0509040812070509150c0307150e120304050d0c0f0804031505090a02030a02090a06050409080a030b190e220c06080601090303020606040c05040806040b 79
    0x101180080007101e02c2178581b01c0c041140c09071440c0d51340d9101d030340320650340c5070420003444001c0e800c0400c280c3d883c0102c580c003507805100c8807920740444c0021050b104202078600f2003408020b00c44d5000d5640d03080040d090402c1031918040d20380d02170180341da145001c2c5600040a00122110381480d05805d588224000280e035000c9030000004118551614032041e603015005030094013280724000d02030300b10308421620909035080c0001d495102d11245402a400884058054035000400e14225010302e98000803028054042c21a25500003a91515522002070003000c100e8000381c02c044140d4040c0c0014607001e0018415a90103180401c5d940d4003c0201402003450700c008000726043c050180804c0300b82c03074506810120b003072100312800b280b0024180a148021000e50500d0040c984a00b04503191040c00c802c4d908506101c0d0290408000800550402c6000382041010990000c1c1c9240c21032020b0f0f42c000343c03080036030004603000d205580240704940f0a62044c030080000d6403006912a401d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 428005197 1250 428003947 428003971
    0x50d2703092102210703030c02010905100f11032203020301060e07090e060d140c0103050919140a051c080a051b0c01091407060818061914040b 63
    0x611440c29030b484441203840e5035070030001d59500c080182000c42e40e003114103204640503030f001c0f01410081c0c1e01d400d42d160801c400050303034088514210350f080b03401200a03001c1203892240000540b1001818480c031850f81c03404004100c0054240c00e81e0520441e4841401010081c8047c0307020311001000e0300083c4806ca01941c40c0c640c0004d03400d41e132481d00780c0c0240f10070340e0354400f000d1078403040803404200a4846a480510046144001034880f03c40e14442e0075680041c102e41c0f02980700140031510028028500c1b60006075028004681040f4120a82980400e4503581c02c14582e80503840c0c03180c0941c00521510039400d6600703507241d0b42548036000b980c06a4500c2c40c180d450303402e158180c80d8192500104050229074400b400090000549a400006c07400080d0b101d03101c0c0c442c0c0ba42c2209544c60004c41d6000f2400500007964840c070641e511014550b4007030554010700150b0fa90700d45c001801c040d00e5403118117190b10449901c0c2c010f0044084551200346003400c003801c10340c81090041e034800750418 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 428006447 1250 428005197 428005199
    0x11e0c050d0e0a09050603060c0f1201090f0b03010b0102060a090515090f0f070506090f131e0b04050c03060d02130509010204151803060c050f1305040c110d050d270309 74
    0x7030031780079291080b04041d02808aa4650050105d0280c1219607a140040c000b4800800910004041c881c006c2c101e0080100e401851060044101c0320111035003400381c1d04005564030266000209980c0120345180005403091071414680d080007800038002483c08503900c20310943c401c00180207840401e112040e15549085500c84680d620054412560403500901400c485482c201513808120710028044014000f10200010220307021049805c40c0425585840c0180c800a440303001001441550b08000b01d081c00508800760380801404540310349070803c403841c11920381040210b501d00326900c050205041c46401207000c0c1d0014050112441506107000c0300d00d5100d0503030340088800c1542090102030540d140c0340003801c2c10b22802d8061100c1023202e200c40b41c0150000b444180003e048510390503007484108029120000507000c200015210300b01d082d40c4000c91000c0c920042d034100b0903900c540503100d00d00500001c50b04d042c130590409100150f054140080c2652240c4250341d50340b945 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 428007697 1250 428006447 428006459
    0x120b0a080307020924010f030e01020304030c11030c09040609060617010609201801180e0a0f060b0319270b0105060a020c060f040f06210902011e0c050d0e0a 69
    0x10105d03001203e07031242d034841a24540d0750042280c02001c04031490007180c011031081105099070310540e4110001201040c1900c14400200c001c0a42c400045014055400034040004e010107005007000d013903160b40f80009004c00a10354411030003072240c14511114900105a258021300c004d1189121480c2400c0c0c810250780c01c03c54001841655243e05507052404800c22035100e00c00c0c002c181414442403105614900900000f45030003001d01c407907002c2040c44c009049800b50396107000ea03202d6181c01c102d810f00441440b2015660b102001059400c400a2800031040240070180324110760b101082c804440848154809281d03100d01844511480ba603030754062024a00c035039012140140c2040280d0f86d89864100d005200203207a2010040c00d107610340c598203c50320030302c0e80690007003820346100041e080050b180601030840461400c0042c1c078030b00e030000b8088814901400385c442440c2c0c032440f100540110b8591844640042c2113500d00307141c0d1000646000140c00500344a4842030340c001601c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 428008947 1250 428007697 428007721
    0x121003120f0c060e0a02031903031505180c09090103060b0127210c0807180212060d080c010e011e061202090402011e0504050f09040b0106120b0a0803070209 69
    0xc807907540c0d49031205055240d050040088000c500038a01851442e0005a6410440c80000364040c580a440a4072103190103402c032542e02e580c940420b00c0e0301c40e08100780d030b03070310a11140d0b40240003240d129503644135080e1802c1d900c25030111070760100d103010000c1b051183c0b55120744c00700e0000f0b032101c8112000403204040410b940481800308801140c9051000805018450110810400d00c1c9440b18080740e0700c00100f02c41d581c01c1080968880402080300c1e00c0c00c445044400b0b00c1000c01149068000c1c1006a58104001e02e03240c001c0c00701118040421410600700e42c400d400c240020000a60107200a034060150300c96042400c0100d01d04e200010600707440307110100d03010343c1704074044440b05a007442007200340204140d05028100b40c400039600040845a51040202d60350700360380e2801d1a081280340c119609109024203c4034080000081043d003006056414905090101e414640211009440b0116600d50420f070030744000180c0700b400101601c0440d00c2115884219500c214210403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 428010197 1250 428008947 428008967
    0x13060c0c1e090e0c06030f07030506060c250b0c01060609140f040b04090206030709081507020309040f020d09060f0b0d05060109020319060303021011040b0f090612100312 75
    0x310980d0000c100c4140b07568001046514038505541d0b50300407130310004000341c008694079404a100074040004847c1d062164960111044031224104000b10b0400c0e41e0f240d401001a404203078400104074020311268441000410700c110605a80701d0483c0b140c2d601800f614440c10700883c040301008a0004811146000781510103003da5801c03206110030000a045180c40b0aa0855a00c000c0c0c40090b84450004511400c2d15440300d4004c54a0146032602e03094515440d441017920300c60600501070703408422100e0840c0c08032808648040680c1e00d150080c0301c0c41d0601c6d04c10516154505040108542002c521168040c10801c0a440201c06001d4180c2842c1401805030b081000188460341d020b501468201c55481c0c90000440b81000800d0115002e980054004da0b00a80940b40280e015000c2c404c02d080e80c80448a040a00d414801505405800d440c2035a181c000301c1d402d29140c88440c00e0710f0001c062401440749504084030715281e2605d090005542c2c8550518078140c005015082d0300d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 428011447 1250 428010197 428010239
    0xc0a091a101b0f06060806040302070602030906040302090916080d120c1b03140708030f2421070b0a0f02010b0102060606030604090c08010c1205130b040813060c0c 72
    0x31901c2c10100c0c034040d8070084003a08079200c112110881001c21854131801001c0c0004400038a11420941800f07032400d4100d41c012000c55100f00310901a5403200b0080c2e400300c0340d041d2040d903025240c0c020102d0500400c0e0f0b050540e48640303501d0020b1044000036910740c0c80700050b01d0380d452800c1c0c07266180c000d5038a540d8512001c11100400f001c0019509c2110f0081c5900900c1c0290600c03207190514219688041000e698a605c00301c24000000960301032a608040000150a00070500b180c88845151107035089600c5009125503a400e00745c5402100030368061480241e40c0140d803601d00100c0da6070000d950341c0001600784110320107103500503c5510b094080580047c03640380d45d02020004541c8c001803580d034100e500d440340c5400080f0440b8243c4043c103010340010071400b0300d09a00805e24208407400d111002e040c02d0500c007040c0041008484000d0708146114029515828000e00a1085c0c0c14208040c51000c20001111540b2402d5039414904ca9200b812040323030303251240c080c40c0007615000c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 428012697 1250 428011447 428011457
    0xc06090d03231b0c0a05010b09130210050f0705060115110313090c0302040801020d1a0a1211010507020a080d090b04150f030f0212010e07030203190507020c0a091a10 73
    0x8110407510078502c0e0144201e80490203480c0000d03c002c25410403951718001c9429079182e50241c0c02da4070f0884829584400a0000b0700035400e25a0000344076690601448000e003c8001007041c1c0242000003159400ca805c8802c50343c803565580244802c0700560013902e030015441c0f404140d41d40b90b010044a04002c004620140d07800e082c0000034000b070a00c0350308081450341c20440002c0300802800505144000845d0024424642c4075a0850320310901e94090300c9103400708002c0c00300310f030101203000c3c06540000c5140040b1003c00010b0b00c00f40300303806010303502907140c1000103820080064421742c070388250343d903815589645240d0000d49000e28004c0014900c1c803580c49209182c03060388aa0000c00140c078012403140004403a1200700e900c445204400810703028014841504840d0303025401c02c0350780c5421459440c0640f45a02c08803000403024102645030f00c04140904e10070030103003030a1403000300841b80090352210140002c20403d10040c4001c48500600e4a543c90480c1c0c03180b40c1c50105c3d40710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 428013947 1250 428012697 428012701
    0xe04020d1209170303100503010b01020d03150b03090703060e06040f0b040c170a0204150803041205070f09020d05061504270c090305061b160203030c06090d0323 71
    0x7100400310410041c40104903460a00003400400002d428140090002c051a0303241803040c88581c00d020503800070744c000c0c2c0c1000402d90032030b6800904151610030624001614540711010f040d040f01155001d00d0b0900310100a1207100e400c00b0070200c0840748501d070700304040b1500e40411a2110ba0480b0003401070b400c4480e44002180c10b41388182d90192003107000e0410700391541100d00d40c10400d1098101c13154005c80342d42d011414944551607101600c44030155009140c0b00a20b9502d00c214010001980303c0540b001e0100f01c001c00180024003031441040761030ba070b200d0714803100942041959076240c504060124415041c01c00c0c16140000c2c05124880c41d107401e00d10b2440602e981d0707034803004914007101c071200301100c0c3c40d22031a41a50003030b98400c1d404a285041c04c9242c401e000d04038403c1d010750421040a583c0492084500422155411031001065400040c0c15030103030104d1104640280d10401c050640d000c5046100303d150340d1030410242d460811000c84012005800755940405680 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 428015197 1250 428013947 428013953
    0xc0c090203060316060306150908070501110a0f0807030e100807030c11160e07020f07050d0f0f0b01050312090112021e30131202070b0417070e04020d 66
    0x8550008000c0d044503203103404c40d1110f080c80b0040c0c2c1d00c0039000980d01d003002e003e459076105140401d21240d00c2d102c4621410445001d0301d0f60a9807180c64107001d05094503e000d540288085283d4540040911040d101c0c00e00340354009900800044000900c00760301951140f03407241c3c40c219021100c2d074489645a460f52001ea0080031001d040c0d00074800000042d01c0105004c002c1804101c03a044400140c0e02d141a280d4001e000001e0030810543d0407542c00c0340104400090342104a41048500019056a40c104010402c819045c003901e0071050300140c000b484010205141242c60a030b0489408003500c0004c2c3e0f10303901900c10382130300042d840e21400c1e4911145070050491038910000c4a0300d0004030003c2445e690348000341c240c0d80e400500c0103442150340010803a05620400c0c4141c82024a0041142c513544280c3d02801440c01c145140d070a18254400c00c44035018040440349541e079207882d07100d0130080008211100c0c18600ca9044007103801c0c407080301018015540940440b17050360b050350b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 428016447 1250 428015197 428015201
    0x9131109091b0103061401140c0706020a060e070e0c09010306031a060a080613030e180708090d02010c050405010507050106080d1119030903150b03010513140604020108010b0f130e01150c0c09 84
    0x1440708c0151040074061511620300500461005020b03680040c00813017554600202902e0740087d4140f025005110100b0444000034201640008828560323542c0e11300d48801a4024a410340002e01007a842c8000c60745854000c40c2c050380101e0084600c81c005a640f22100b51303443c40210394460081c0c0c1c101c0d00000c00640100300010721010000d0400c0009008180030640540007161980002032001c4140310310440c7c1441400115142d91000340a5492030038800340c4030380300d00d21450f410800e001540a0a1240a50103103019050300310030350350044900c11000744820f0060503900704c1ca010f0440c0541c0c051040314440c113a0f00e9415262010304501d90348030075a00c5ca203041c05c000c140f2502c400311501c1c241c0d000c0c4a1039120703000c10b15440310f4410083c1045c0801d01c50392081d80341e00740c2c0140140070140c3c1e0031404990441d840300c117085a441104a000c84d03c0782c0035800e00402d02e00400ca00200780ca11034121028141d035811150300c08240600c1904803204502d1120143c0310b00140c100030701c02c802d400c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 428017697 1250 428016447 428016467
    0x10060e182b0e13021e03070804021302070218090f010204080607140c060103242901022418032502210703050706050909131109091b0103061401 63
    0x10704180300100b803600003040c1004020840500544c1e4000740609040c0c08000c0c48040b02c031030300140703681103103050030f0003030092100a40061f100e0342c181328044402001d25011103040303a50281254098450048094210758005e581401540c011030081c07030700c01d0720144282c41c200d0345c07603800900090303d40100c02c0e2a140f444621400500e0f00400c400c8000a800b004550300940c071400081642040144100301200b1500c401c0030545414560b480c01c3d8025098140308280d1804580b40c03031b01c04683e200503860920100e03400c000100000035014110800168203a04c20880700b1400e008042c20580b06540301c4c440e103860b0a0b025402a24000185031442902121a51020f0146a48034003503a160a114885001c0c05440e00ea01c919020f00c204081885103000034031050800e41e041030764140c005030807441e004242c155401e05601001041c400080d0f0002850f02010703184440c2c50400301d043c03a4840d030a00f40b0080c100c0d84089000d519030351003031103030804840b034102c880b40e85000c030540119044001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 428018947 1250 428017697 428017783
    0x90408031312050301060f080103030f0e0a150806030609010c0507260c0c0103060503010605150903070e100305070e060d060b0a030c061214090a020d0510060e18 71
    0x2402100c0700005003541d4201a070151282c881c641c803589045002803402a4040840007000000001040000c2d0010f0b59080004500d08000c00401800d0011407800740041d88000c501d9500213041220380e50708000500e001302c0c415000c6d41c0e640d03554614100c1c01c2c1c0c0c0802d828500021010001c40020a001c4080280d4100401118407100041c1407035a40316500107102125150304100c0400026680500c5640d0082c00103600a0100d90f1910001030b03008085404c82056040700016000f1659400384410350180040401d5503010342814107050f281300c0034500080720341d4460440049003e0a46600350361003810010f21031401d210b843d80d03550025090303c7d100984c012250200c08400911400c103480064001c5540d0810018039800100301911015118149445002401d0008002000c03c0d08844590103603281d0b409c0307104a1074582d00e05072000640010003450b0200200719245200d108500440b007076100f23201040b94540c0281c1e169003400d04414a50340120308041102c0d0240050f03450300180c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 428020197 1250 428018947 428018971
    0x3070f050405151c0e06130f06090f151b0507050109050703141504080f0a020a081305040b041803030510080105010b0309071203080402040207081902011e0b09040803 73
    0x5590004a0f01c80080c500e4100e02c0b544000c504c24000f8801d4461222212028510910003107140680039500c801c3d000e0034850031440741090703940c24021315000340911340b50701c11030420420712682800c1040c04a1380b42d0444042d40c10500d54030215032140200e24890718100503d00d101340d50048190b500c0d60200008681c19500c400c1030001242c414800e500045010745818003112030480041401d00b450385003040e80c048407000c01d000200700d0410540301182000b000003503480700c4400c0305a1178911701c00001060440300003082c41c1c1001d034009246040b14011303a414411248090200000d03250305584030300030131140040c0440801e102c2d070000703070f04040915521200181c0340d003407850a40340e0076009035480540020500c2032400081000e10000c0c40107400440c200a89030790b004083c9100500080d12585c0c0109010040c00790f070004903001c03441b0b5203c0500051a81d1107010340a4002807809081c1032014071040d00c0e180040c0c1c0603065078840001e255011540c0c90b0342e200e0440350006008020351607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 428021447 1250 428020197 428020199
    0xe1b030a090b090606010f03090816060b090403050a080a0c080a110c0a052518020c0304050402040312080a02030903070f060905010e1b031516270f08030403050303070f0504 76
    0xa4014850382e8000c00c0214007503c040e00d05030001408441560740020200340c82c00141201084182c41525040c81090701e199134101d0007400c01c84058400010300503484020142480209504800188040406601d03509525680c402450741107440c003140480102c2c007541c00103201455035501850002c0016085a8100820b00c0703c0c50749070554810080b102503000c8031303102e260140040301e014008034141c819203501038180490451980544c0702040120b035004940c41c2d85500702802a140a008058804c54a40d5564100742c0b11303124241c2d20301c0001c500d1302400b00305a07a20900803640300d400c1c0030005514080b1181d56a030100301810000b81d604170764803450503001030001c2c003a140080603043c004041c0078a61001003062810422200742c46544004046100c65016440c2607a00004c04203410380d464945810030b4881217045410503008000c095007002c4192035418694003920740180c104c0140588440c00c0982c1c0b0311403400043d0840c0d100b40009000c003881070043ea0f804c3d141928180303040c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 428022697 1250 428021447 428021453
    0xe04030318170702040b06091f09180c0f0807090b0708090a030f020135061801090213050a1a0a05040b030901020a0807020606010e1023090a0e1b030a09 67
    0x80c2c8400403005a84803030010b02c00b4203500d041d0040300364020003111400c0c6004803140010f0b44012840b0020a0800c800ca40000c1d90709019070070300030013085500400742c0c6400e8407030501c0e03005081900c105004078005e4180b4590840c41211107520408040c2c0303406a100341440717610503141e00300e0b400c2152204000c1180d0822a02d420341e07184011489001100ca05418520000d02180402205040958041c00d656074400d0031100409642003c5c82c1c550a1151b150000414280c4503811443e6a0514150000040c04600d070782c010071900c2e40c0f68a601260740d4459040007881c9030288291134114070002c0030021100c0f0000c004002080441c18810702d450340d40d04004485801c00c4642c2029650301082e0202d80e160001842035001c205403014055504d04000040c1180c1d1202d55400d000700389441d40d00c400c4038000d003c401c3e039106a150010042603000541808503030b21080c186402160841c0b000181c5994003100503015140080070701c1e0b218503024001541c0c50f0001000c40d00155100c1c6442004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 428023947 1250 428022697 428022713
    0x80f040b0409020a09050612010312030608060f0f070504030c15020309121f0608060f060103021317210406030b010c020d08030a0605030705130207060609050702030706150e04030318 80
    0x7402e00490168a40c54054400760001081307901041c01740d03008011070143d508000ca24541980d50005008820803080c2c80200d0040940c0c0d000101d8601c24031090100c900c04401070b240c8103d145d04003001040d640c0640441e5240194030004211f1100301000b031105066804480c2616440c61046a0410400d500001c11180c2c41c00310707a00b400d82010f180100550000b910b4201b00304100442071200382d1500341095075402000300605c00720035524005c222147e00c02c0c0c04445a4a001080c4541180c1e141c080c0c102030089546030400892040d0b030140400050402c243d2060309035001c0800c0d06042c03501c0340c203030050300d0010f60003810018428007038401a51140501d4040078020540940c40340340c00b552100c00c4071000e810662095200f28400c000b965141c2c0b80c0b220345109113074005a2108850701d000000f40c440ca403c4461158109000c00041c203030b002000d018074034040e1a040c40200000844804051224001c60103c542000c0018005c41d0003a0090200d071a841602c908030001242c41d1149 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 428025197 1250 428023947 428023949
    0x1b010e07031401060e13120c0b0a0c091505042102030a060b1c020a12150905031c051006050c150702070906050f061e07150902010f0309050604080f040b04 68
    0x154011440d050284010b800f40316880292081010341509418034400c14541420440c1d0000c2461090250005042e03104030f07803801d072541d8421010041410045d00e06405803811400507400143c40070310018411000340c0c1035999400d16500e40c1c3c2d10740341c01d21100000191048003000300c100090800c200058a080107041d00880c0600700000e90034683c0d40030480c1d039000c10202c4230546231508080a0140c0d0703c088950b000c5500584103110415640c0c5001c2c01114441040c1200803403402c140c0c0420710401000034003008070381d519161035179240010112308603001500c10040c0e02c91043c0c1d0a1040900440013401d15049290803205c02d042e0005c0751346040c410494a00005070040081045210b20354060302000e808100c410480240c44400401c4041c024a0040c278481482c8142411944900e04101d4004507000b80c03680e00c0c2e40034008403800c064100e07600c00302e000503d40030300c08410743e1080c800c600d11541d002c809840282c0343c0c0c0e01c0790322450b001881c000306020010800012202c1203900140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 428026447 1250 428025197 428025203
    0x50607290109060e04031d01030e0a06020903010501270c050c0a0609050609010212060609120601030c05010e090606161506030302150a0e030d020a12050f04120f02031b010e0703 78
    0x40020340c10b02c8810303000c3e115190b20110003640450144000250890503004104858007840514040c0c5d2800403000f0301225042244240282071810080c0003460300100481c0c401030b00248441e036071352045800c2024940e015104002d000703d0082104410303d802140d501071940c50094146005176013410f08044c18088101d0700c4560300c02010003000020310103581e118000a000310f0900034800f401401180740140114811000040e88641e6643d0318560503c00142d03200c1102c10a686901c0c180128450500030380340030a50041c8198280d20f49420040e10601010b0100d50030100c000001c03005804a20000311505004118080c1d000100ca1240b000214043d5000b03100600b01078580ad0000e0304050b000000450074948106040d84000045a0703208070078800069580e14a050201d40b540e403500c5e61110803505000a0040d07412507462418012401071102d03c100c0155142d0542e8480401e48076070026030410304c00c0c0f6481c2403001f5064a000394440d03002180388400b007081e070760611446410071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 428027697 1250 428026447 428026523
    0x70b0d090c060305070c021207091508010f1e090c031b140303090d150608010f0e010c080f0a0b0406030803090a03020706030509031902031201032613050607 69
    0x10405014107900e4a40042c002400c0801a5040210004180c0c486401003c2e000f00c80d03404800340c920344204500c80051600d00350070081805620f201081240880c03081304110f40c03c0140043c2481414413031800408420300c03d0512952112482c20003a245051081c0e9803c00300500000106869110412142980e80203108100e42002404948503041d07c1c8010b011358002e200000303090b124445081240c0e07070071040e2040403410410350702d40600030a80011410307500f888c200d0100400f1640000c0d004508150080c0301c180704140048907a103504591400070900d0301c80201d4001042640807172035408029001180362600c0c0c0d02c070003183e5841070303984001d41d91040d15098241607040c80038001500092a0a01c41030810b0020143e41c0c0c000c4460054040381c100c03c00586040c000c008a40700f090340000d03c0d881a603502d0a001d54819045814031007005912a01c2041804030380c0c00712805414071246030040035003002e06015071900701ca2401c8445c0003000d86145468180340069014044500b100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 428028947 1250 428027697 428027711
    0xb070c060c0206190e030301030602030405030c01020412151506030e010b04050c0901091703040303200f06060907020120090609060d0b0406050f0603071142070212070203070b0d 78
    0x56104e41520f546240e501c441d140100c07088a1100100c200d0341103a4000d600941c4a0701d40342012410b61091020541d019032000400180000342041d2400c002401026400c1030170810b4105041504d1003000b044408500400c0d080c084030740264441c00c080301100307000092071801603004c2400c85030140c500c10010b05020500d40c265691189070744c4060081c02e841c012542201d02103281d91b90003240001001d00003240240740d032030648850000443e00403803080390200c0f0454000151910300a4990368040c1601200180140d030050180d1303032440354413895411520400990114003904002011903024804000208050340e954010b0f040c1614141d0700024031003e02c000300011526241d00030f9008940f003000d40b004a988060031f49910501d907040c1300125401c0c0c0c0c3d594605010f8900343d20794480120308a4040500c0c0c0035419035203a00b0400b00d401600c04d40031100c000b1080821500080143c4c000d0b10843d076003085410103412450b03c040d046401980d100c64a4010030b0300410315002c41140d40740c2c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 428030197 1250 428028947 428028961
    0x100204030605090d0c02030a2a06051e0c0705012006091006140904320d0216030b0105060a230705060a0605060301140a0e0711070618030b070c060c0206 67
    0x40301d130100c90164108010f0419440e4017094682041d403c0103007403078800385240b904440403402402440d4510242522865450300b0001e001608040300b400c1c221f140c0030b40003030f0780c0c5103410040fa002880000000c0507483d16000044071a804c0007814544003901000c11412142003c1100c81d015000700c030041d148100c01400000d046030519440050052042000322109855071148503410a030030241e07c075060030482100c1e540000f191380e080a44800e8104d0401c04500d00070906440c100c0f420307800e4400d80540b08140c1200001c00d400040c0c201e11407540104082d1410320010100700400342810102040c10b55500041e400503010002c11024002585070100a804d100c7d02d548108200390801801d402d04021800ca40414021100064401c148c0c0c911036a0303802c11303404010306010341c4016292078581c000074808000072403120304030f21458038049652800340c0070902d0b528016031400032103c0c6c6542c840c4080700c50007500800c01e000e502551100441c0c00341c090001c03d04541d400810860070604 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 428031447 1250 428030197 428030203
    0x340602071508041106030901090f081b1f02071a010605130e090703060f0608031606050c19030b0a15021b0f010c06020901030b12010509010b0402090108060d0510020403060509 77
    0x24074401046242001c0200141103940f040d4424002610070544a80d11801081c0c010201400007828880c2912030000030458800010700d2078000c0e1510240780780c2400c262469941d466610307048000c4d0034040c040c0d0100300450340902140d43c0030300425010f030011588041b030200000c2e080385c400103c0000703992103030f402d4920862005121106001026241205485455220601004299030744030340452350a0803040e044840030300408415030f680d400072042c41c545984001c00040310404c0c2020002a0084c1501c0180c50400006d144a601c22880040040707000305002d10005502984031307080410007541b511002404408180c0013031a00042c3e001011201d04400001c191145c4060b2040110503684003820004480d032103440035880c5d09201c80142c001e8078031048078540000396040fa80744541d00c150010341c003c4403000001c01060241100b40401d82c8071f1015881c0c0401d8031a004900e16041180c029682e0328090350958000100d100d140c3c13410b0782e020b43c4c005c2e40c155481e9002d105140c4014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 428032697 1250 428031447 428031479
    0x9010603110a0311010e01050d020c0106050a060e010203031305070e040807021305060a030204090819091d0411130603120c030e10091e050402040303110d090834060207 74
    0x2241c002c03101c14070750b0340d5031103140c0b4104020754100582543c00c203800740d014409075150b0400c1c020055441d120003c40d060b0007007002d449800e10900c21908001032160258240d01c0c5483d606030b028501e580e480300c403180d9082c0c05041040b140b501c14001c00042d04a041c241c1507005520410100d41d440405004100e260741004d0745004105180c841402001e43d50b240b5a4801c0f82d41c1603c0108a645460404602e6030140c0707020f40304071410051048985a510141130425a010342280c0d0945c40c50039881a8520a009c0700c4c02403030141d92186115451401000180803032000c00004100140c99a407981c0c00e00307040c05c00f403001040d1000c0c2070400705600119050321008041e20100520241d0601c02051181030344560038030201c040030440d04001d19058040090100684190750381c56880c5801403e0150809030040240076042c5400c11403031240c2004011501034800030507061110441c00c0c0d030030b0314074041c50320740703480481488042c0da0580d0740450000b448260040c1082d2454028140103008107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 428033947 1250 428032697 428032699
    0x109050a1a010c03020c0409030903020312090d02130b100806100c050d110a0f0f032c01050c070f0b090f01050a0516020607020d06060503120c030715140901060311 72
    0x40404500c140410755505800075607091074140366500640c28180c3c10940c64846031500f050800c640d61041c5a000403c1708110ba00c00d404603060481e00304078801e098058845800e520012103000da8000d03240440102070454500c13480025121407203000180c01081240541001c5104401000360a00d808071240c0c0c400c10140c145a04904400ea84654a400e6132049450500070f03a448806c0451300e08201400744681e100c0d56800c880e24103404d010420440c65401100000e420b81c0c5a0010010100844441402c9000769131200da2202001514690007902c0d203030300d8038411414001003000d038004082000300149040c0030f03951b10000c030a1141c4256184811070510500300405210568050100d1711400f180c1c0c001911107900910000f04588136100c0040e5220f1404040c003014000c841c0d010710300703d0303c0803002c0710039201380300600000713034080d84802c9041a0401d00580d0003195980c2641081d51000203000541c01544900c089901a010345080c002a0b54440042c001c005001d5403001c04210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 428035197 1250 428033947 428033951
    0xe130302011a0102070509090a05070e270607211505150406053c0c06060f0a0314010209061306030b0409021c140d0e090c040e01060813050d080109050a 67
    0x1a2002c0043e55941c010702c1000d024404400000c0c8800a050100c0885a42e000040d28a102d40e0784a08401900c000c0e5000b5001d1292038403c002201807004c10502515580f2000d440a51394501c4c0a81e589511040011480d0710208001010103810303100d4002c02c114400d800300311660900c001e1210341000b5641c04004014100800e021590304142170f0341d9484000100c484c41d442c5690400032114084101c0ca061a00b20012a0305541000700c2c05407140d0440c12040b22100c3d560941001903d40050700100c0d003100e03044c0707000c0c0701184d0780840c1e50260184500001d45403c0b150b00215140340c1c081c01100554800c103507424001507905002d0384080920071142808114038075000200d18401e410408113015241c4011402000400c1082a072450202c0c0195165100c40f0000a846484403280e2903200d40710510004040c4000c03542610103030307007043c0c00c450305603824000c0030f68602030041e08200200c6070717130302c600f0340024020032011445208598a420155160010b042c007651005030100c8010340c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 428036447 1250 428035197 428035241
    0x100612020a020a020d0809191e270912020a0c06020106051003020d18060e0118081e070b010306020d0c0f0f080601030914010507170f0115090e13030201 67
    0x95800140f00010740d4048401103c07001c0700e0325051025100385070145030050740c118204010340141070720107000c0714103802c4d2403031070b030500c03580b03003001220480c05110301000c0740143e540003080c540030171920421032805000030a07031045d807200c80c48130110b002d2820040e07102488840c02c000382c84600500038040d0740001e011050410000070348542001c1d0000c0e003095408200c1c444070908941001642e0261a96100c83c41050303800c1c054080c004e107042e801101d60030981d008400340103503030740400303407a8100c4000307814502c0440001010402c84640b02008a105002d50380104113014480d90007107106040040c0d032120070714404d1040e40c00400c0302100f8801640f2244200c40d8010550051201c003a2078110380d642c1c0d5110050700240895200540b8900355079001d80c40c0350105602c41c0b40142d50684541d02c0003001620701070100c0e00c084030f600c0c803507801220041040d0340700b40d852000d0300c000a003014070b41c4070b442d0680d40003105000c480c510781c403007100e0358284103164082c814080290103014a0803520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 428037697 1250 428036447 428036467
    0x30304181d150f0c091009090501060c1505091213060816020312060109080a030201090b2d040609021f080a1b050304080906040b0406090e070c0201111510061202 71
    0x12100401d40c043e40030151000401c41d9882d401101e58001d4000c0502c4091022240300615000c7c02d4040c401c459441c0c00700105000c0e0180c0c400383c00880d800600301105031204110100a8540600814100d1080c00e1b5001c0203070342e000000c0c2001c10310f094001e204040c0341070001022014003603c000d0090210040c10705025502000312900300c0b0146045500d180c50700f80048078103182c15400380c0303111b000700340c800d108160307040d04900035850280200803a103031102c810640302c0303460060716003074120185801c0034581c00001c003002d58494000c0000240010068002c00d5010529818202162401e09005003000d034000060302e4200c400381c5d03410002001522020f410310844600c941c8280312012000600b000000d9044400c48000a041a925266114071202460b00305028407804903031301d2803000c02e2803601090814071079141e50350b80c5281c11200da001910b04840d40185003c01c2d00998825a04500d06148038a028070442c4800320161850103400a08119650714104c407514010801707102b00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 428038947 1250 428037697 428037733
    0x7050d08070606051503040b10050603070f09090c050415020a0c12060509011109151e0a080a020712031d01110c010e030412141c02010207110f100e030304181d 70
    0x121075030148c0884166110214280419042d55221a920942c0041007002c4682d0001090080c0d5801d07860f268903254807005103009480301401c0c0c40001640509c0100401280c19100800004443c01915000041525a0b584e0025160042c070640d903c15007034802007000038810a58030842c0b0780d00070403200380842030755441481110301c128490040d10807601c01c040130180440b00081800310726144202c01d007080e00c4545030081d0b00c0401c04140c1003800188000418000c4400700d82d8020710240c44503519070740a40c020030308000c041a01c014070b2054500d10020910030b00079001d451501c010f840380c3d03417100706a00b0354400400310b2042d40c100348000c010fa4245140d2840b14258481c5907041c41000845030305184c110008403201c02400b40740b4000060700e4040d40140099800f1720880030085819006001480a0300100513410013035244408405511844c0300d002c0c80c42008050741c1c07610b90b40d00d071f102c4059242000030341c4a20343c1d182114100802c0d0302001d4001602000050800b1031140001130007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 428040197 1250 428038947 428038951
    0xa06080f010504020901020708011a0102061e0a1e020714010c230a020316030804051606170a0b033403020d0b070201060905010e09011d0a0f0507050d08070606051503 73
    0x101490b00851751a040e41e00910250003e811508000c002484200c0701c42c8092000c0340303034814058064280410703000520210324032101034030341d00924130741c0c3c880c000920010700c102e400c09507000108004425010030540000c1c240d04d4001c5a24a1011030081d055508440944106509000504020880080301c0d0b132412200c41c050041c3d015140c031000b00b000e90451040c0c0390b2101c1180c0c807140c0020105508400030b940124024002c880003402c40380788882645c0304034002c18010030040344125010b40050a003c90348008907140100303d10503002d01091400c681e8004c1036074488082d6a41e0140f801660907a1410100503401010195286402048501c000d003e0082c08400d501c00001e41d00c54000d4104900a1588820810441d0394490802501800a496209055080c4841b06910306851001c00d4240081300d4090041c0c2c01c1140c0e54029801ca00032404c6401e13010300d0000240503600c41000c0c00040e80102800c60703a44071240b605004440e281e802c403610942800856504070300c10304d0240d070f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 428041447 1250 428040197 428040199
    0x60f01080d03051b0304080a1d0901120302070f090c0e0f0114030a0603080d0203070e0901030302121c05070c03180f1a07120201020d0608190206220605090a06080f0105 74
    0x68182c941581e450f10101c8004481444c94100200b4401000703544002000c401d072550303990382d940f010007202e12181a002c824804ea4000d5425005020310402c034003034180e030980702e0b0041380c0c030740759854054a0100999078010030038566568690304809411512000242c00115003031086620a40d0010b00102c04c04a0b4403c0942000320018180404a6201402443e0421000e503250315901c0c6110003e580210340c00c0d000a03c81c0c000da4036040c1048907a0b1b5059aa154010b0a450319108400d40c45a806c400d050741c1110b01c1021403403c8095061227950b018045a075201041007906040180040414071101d0b036000014103001c0020181040c00c034402c0e10018a17403204100032540060b003043c010920003a08080c0464500011181c0550003855085011481405203070b40d140f41e9243c80d0f40401414840c0f000a020521005203480f200138180e8100300100c80004490700358003101100c965800c14404030300d00040b031a416140984030280107084518007064186840e44024404440c184a01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 428042697 1250 428041447 428041451
    0x415060b090901060818030705031e1e0a030f09120212031b0706091b0303030b0a03020d080a02190c0302011205130233030a0501080a02030d12110a11060f01080d03 72
    0x3c1500d200c85620101600d4020306e00b2a030b264411070400030f40300c2c0e101d5040f00d040000d0010351030196080d80c1c01a40c50f8002c943c80100317a15600c45011100580c008410354081582e510410310342c00000c1d10541d80701c0d0340122140a440208407101178544400c2800120301c03180c090040012030750540d03600c050319400140103a912603140b071800c0c801400700414000c00c40d404a4a1041003050003681c2d25084900995041c0440c906100500a4440301404041d4108041454200200e010720000300f10320300c1c01e441107849013000700350300344154100520b0855003141100020010756078031400c8411a006031a504100509088041a8003400a42c400a010724041c00b2217980c51040c803c0310780181101c0082d00303403104a4001c441002903004a481180c010f00d058004501c104000841c000c045501400900d0042509402603032481d070f5060446200765120382079140000010380290139803030350a40b00d5080c40d84810200034101a8002e00c000e5001151600420407010005001a00c1548a00300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 428043947 1250 428042697 428042701
    0x402040e0a05010e0f1b0409020d0b030106170714120d050409150f03023c041104060e0910090912020d0206060307090c0e0603011205100204060c061d060415060b0909010608 76
    0x51b485800307541d0240b203074284041136041607072880340c00003508004120000c12506468102c2140900d20813404020360360300c48c44091210841c1c0030b45a61111000070081710201d4080382400d80b030020700005035400a24003190400c260100f07030103000c503102840fa90b03007000300e030070140403d2090105101c042d01c43c840c10303a40010418070701c3d007403414441400403a0055000000b04d045a0340000d030032960f8010340c5407aa2401e980000c00041e9019a091a66000580c2c2e25036400c05c00c0004010741041e924606007000001d560800c0d100340d0262030712564010403140400c005c040d0a00d0440030003c0d095401c40c001300b141541d07003ca1100240d81054100140860003210120380104509020503000b803000800070841c03019441b507a06281e0310440c2201c100144500a04040e4081c0748161b40120b01d60084a0740082c5440c0c111501040b10441c114140b001c425401c4c03803800740262816500c05040c0c0f0340c41003601ca054040d00c006001d02541152401c048403000c200c4c031341c4c03051056104001079840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 428045197 1250 428043947 428043991
    0xb0f09041e0506150301060e010515250b1f06030f0e06040f0501050903160f03030b0303030f0a0f090213270605070228020f030c0402040e0a05010e0f 66
    0x5003006031601140c11640107041c0c1c0c905155100000d941214502c1240d2407200024a414010141513448540d038884040c1d10740000e020b0303e08605040046003000600c03821013813516580703e11460208241001030340d0105402c144156410240480c20031000c1410b81071440002880d025080302c480746000209a65103545c001c00a01628100d0301c8107004450034003091000380f45080d0302d0705000380c00811032500c84140b502d6076840b5919540c0c030640808c500b620082107208010280260103410003060900c86180081c1c1580e108032203400d1048023480920049042d0341c4500360305100d60903020010780b80d1580010b0103410b21810980d407440d0f16500d6409d503021031440500704480c91580100152a0245000f10140908451010062041c007100b29108e0b1050300c3c0404d45584070080b075440a00854080c070010000f1a05081d4041c0b00d200e900d2165074450788024802070039210907014882c28849220b0041e1003041e4010040e4800324814007941d031940b281441c0c0c020408903916004040c11107 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 428046447 1250 428045197 428045213
    0xa110f0a030f391806030210080601032007030e01051608071a04050303040516060906120b0a0f0501037d0702060106030b150408030a02060a0b0f0904 66
    0x51000740c0556030681500340d80140e0f00d40510241c4855440c03146040000c030380d08208890903840f020758003c000c0024162404d01641781a0f400107010300d0085031b1210000840c000c0d40c0902d85030401c124400060550504d03912000740d05500000b440c0c013b20f00140c4400ca40045c04850902410043d8002503101c104406800744c41c03074018070452041c03918902420115169001103400750340c3c03400303102201c5d002c9c600e42054900c203841a03600c40129450402104076580c0058650085e145940c528000c9460782e103100f0110000d0000d10000c0211504040004003131b15909030040c0c040d000b8000000c84801da00a03800303140404041308000d0b0344142011b040803d002c89c20708003520f0603803040c02141d03208000c0040c040f012488645c030b04c034842071020010002c004100c0c4c0200051308080010b1081c10310941000384905402040114010503801c1d00d0702040d0301c503a0114105500c001007c0040030f8061210b00d51010003204c04000b01b0700c5032008260140d00088815104480c200009070400c6484 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 428047697 1250 428046447 428046503
    0x1022b02030c1009021201050103080d11090d0c051005040b2209110301031703061813150c020c0a0b0a030b04060909110306130201020a1209080a110f0a030f 69
    0xd048881405045000f840100202001640140c0039000b0490082c1c2050150504881d031243c01103142048007051600200035058064905d14820010328980d503a54204003100c860141c4a017400040c51305081080045882d1410014820107120401c84c40c50300c04c3c10b03207030041d00740e604d40384800505400d40132035030540e130b0003074640350b89440c02c0c811480440c5009141a28030541c6402e60150120701c0640603070100700c500c04e07481562024200000d880d01c042e40350b0031400d110241d410f44a03003940c440341c0c01d00c900fa05000e00150307116a080000c95040010700040901941c115614504090b5100320720f00c44c91106106060b00c2d1301003d4070383e480c0c0b0790007103000301544001080404024501524003002038040e103840380c416103010404800311815040700e0a6816001008030700540c4e951000d13648210800d05060240d0300400080705c4100b803112607045445a01c0c82844030510b4820480702500c00110300b4050303000182e0510006084510b1080300540107910b0a82c890580540e1155074120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 428048947 1250 428047697 428047717
    0x90c0706020403080a02070f0e130f06020405130b0f09010e0406050c090901060309031701050d150b1008090613080d201603030b04050405030a0f050d020703081501022b0203 76
    0x10003e0b0401703150342e0118107001651000000740000c0d5541c0ca845a1880c801540d040251100c84024580003c000e00c28240308070307100d01c0001d414a80c3c1c400001d011203810207101403809442e592040c0c071070700e00700480c0380700c010040320314001c0795042115503081020014030040c0720390340d500081011814161309880720300c20300810f109059a143d01c0d004000e06a001c4040707010804003810548a00d02111800d41a00c0000c0c001e00c04d4140103403136155151000c1c0c1528001d0b20360b82c0318411841d8840c5004981c10354160b403503026060602074a0301d8035081c0001e02c0c541000c00c21008450004000300c0c1200c290b84042c8001007403001d00301808410001d03180036100c0e13208030001103038550300741c40709501e41130240280c804002054000b4240b10644004413001841904200018400c10380a5481d19043d2821407400a00b4944802901c00032684581c4084e40442e48440c2003240e1002407160380d1848080c20b01c00303030199402c60b0346d5601100380010b503900204107a02200f195850701c20400e640321001c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 428050197 1250 428048947 428048963
    0xf0c0204060605040e1e070c1a0a060513090503070210021f0c110f1507051c0f0c020109020117090c04052e0e07120207061406041802090c0706020403 66
    0x9510040682984c1c441d108484034561a20300203112404101580e03040e00b8021281303030303038103a441100071290101d1200c4100d0b442008490744402d0b20144403d694415140040000351312400c0404211800300c00440c03000c40c1e9410880c0e1100015408003d0380c0d0490380c10303645500521000701c801d0b0b041c440f0503060150114804016001c0344040368010059100e180e4031110910842c1d110069203401103c0002c00b440e522000b0b040321040c10310040e041e444842883d1403418810141d0360140c001c0070380c600b481000c3d074031035809868062091280b520604a540020003a201541e40081e000704141c0300d1541c2c02101c076100041100c10144005580048014800c000a250001140c008025003074000807400c030709050000f0f0703051180100c000c140c801c40e07002c00c0c40a942d009022078182d40e840c0a00606aa0240500400201e41e800380c0400540c060304010060318141c0107000c1203034082c80c507401c0704844000d07105015071102207450f40c0100212042640d18800ea00f002000782c4120b600080c0501c0c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 428051447 1250 428050197 428050199
    0xe061204030c06050601020a020d0b0702011121060604051806040e01020c03031008120708090f15090103050f060604051302251209030b010b09011419080906070c02010f0c020406 78
    0x691003036090072203d200e20410400d5440f0300340120781d02d10381c8150080d0060010790065010070708503a00340e035004500384008900500300c410780484c00e811a5600c9599114900121807842c40d2102c01179500010949805040514200c001060180888403038040411250040b4502d40c956820070007900c25030100940d90b130548a41d42c2c50384d0303a00c21240c03084070514a41000c03c40e944007240f9000d00007035140586042c42e1445d01c4214041d840113003100d41c00404110b2101440c0c45409010302c11070100f14401c0c0e00c03030304a0310024091f18001010f00320480c494100304001039807a036059405440c010349201e01c0345254001908003e1144890110300c14400c8039000e0800d40048510409852081c4440c00460340b0020703054a0b00501404000c0000b0711440c01404050a4040a040c0d00310317051505054601c020510100c15502c90245001050401240c20085030740110600f41c1058031000285881d14008000034a071078200d0314000c1c100101c9820801005100f0300b404040c43c0e030020001c0102c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 428052697 1250 428051447 428051453
    0xc050a12140c0d0b060304050c1c02130603030305160f18050d08130e1504111201140f011e05090613180c0f02060408030a02130f170604030f0e061204 66
    0x240c2c0221440340f000300d080c40c2c407029240c1041342c160303030040358024020122004044204801a5503001c6408a120a144030503c050b80d106060320030071108040000a510b4254200101540c00080c20300c07124040100b5800d81460b8000400012075146142c0f00000030805840e0601075001540019401043c00019070f041c000c451b0014904140c01541090005a4503039000040e40d03021940c54000c02002240303a2002d003003503000108022103070042c1500e0206403090018a4101c20307089204403031000103450b1450b050940307010000e40700900704101e8501824404413000c03012880c1030001c11401042034440740d250380080e1488801a09100f900c9903403a1002c090281802c01e9138036016a0801c101044000d00a030340c40e92038215198090015071f9565140c00d119640050304203002c1030b900b0070001d6461458100c42101915070801f004001902e440503891800420703200b90700054100505010009400101e0b400e071101d002e00f0b086c00441941c0300020141e000d10401c01e002004054100010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 428053947 1250 428052697 428052721
    0xf0c0703050c01110a0308150f0306070809010501170729041d0f041a04020112020d1a031f091e03020a030311030c09011103040314031201090c050a1214 67
    0x4100001c0e0380b80070f041c210400c0143d64174814604003802040a003408500c0349408104401c2505030060201d00c0d404180c1301c040b915100046a0a40c002000d076014448440801e0151030700420030012884c00d196a01c03030840761290100d2040858806140e099041400c0c905a4111148103d103240c407900d0b81da84003000c104e01c000401d1030002c07079507400c40000d400c600d40c481d4103401150045001845c4051260580e2a48000070303205a0600c9000141d070541d00511380010020068038140110b0121201c040d0b2400b0005d110b10003c2c420b0304004040c4800c20b1400232000a00000b00d500810f1410445c103107080c4641010300708100d20300064920205050300010b80d9501c80344a95002c0143c0085460600d0440c0000d65028191101c10000e1000c503603c1050701008010186042d05c2c90706599035184419030288010000b855000410414105802c07145918010241d41c102804002e4001c100240584140441602408105450100100340c10707405050b81501101074018103040500c10203072 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 428055197 1250 428053947 428053963
    0xb040309061b1a060102070e0109060f14030c1c050d08072d030c030e0106060c02030f0708192f03011a0a0506160f1a06010c0308010b0f0c070305 64
    0x840c80070301d804804282240e882150700c581001c10b4854a144043d02d01000c070341c025101c00d04600c204d00340800e441c045595814020011204001021450003500c4144c055080e030003202c001c04038440e18802c5d520081614401250201c0b100d0007448000d0482469115102c0805440341c481c4260411255030010f07007190098400391a4000d03102e10390502c1f4030040c4003002032260141402100051a50300a4002d0480c101640c00d01251130400c2420050868005a11200004011290341e406504080c41313659100c51355200038001c41420945d01c00da0b901c40d5401c02c151030300b20700d20701c8406100e0060880c01d200000f20303e404643c030f0300d000f0303400d61502e5441044610075480c103a00300f4203042101c5110321b8124409001c024041d49400100041508600160621744451200c80e40000d10f6559440ca041031042c00c00c03915403035103000c0074190f807280144170038103008030310382c2400202e6008440c540c110354114000d50340c6d6140040030410b042c01481b20b0000c0c01c5c0f15800021041000c0840e04030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 428056447 1250 428055197 428055209
    0xe0f1815180c031f09050307050a0c0623090103020f0c160501111c0e120109030305010902070b15130c05041a0306060f090612070305090d02010b060d0f06030b040309 73
    0x2920340031081c001611080e00240d51541036201803a14911004400c3e800c520a0000300d000040d031031040c2e102d00741943d0081400300c4581d0481a440300811614040c5c1d41c006c1d203006d10b8412aa00d0592103400c102d40c1184043c3d0540b042d0100d0300404980c480d40448151078140742c0d10b5502c2c1e1490306c040f81d0340c4140c0365080b1504429281c4012405500c2402e80c40c02481c80d0710010400614440a60307000c2c000b50103030b05000c110041880fa2150744a000a00c3d00c8181c0700d03000054204410b086c001c00725801038002e6442c41d40100026004107084081c0c458100400c0d044804058900d20001111500942c040311015400c1c0b00c0c49103002e9030400302034800c07269040021011014070180d81d1640c1d110854405e6803100c01070011000500111000c0c10301c004019110034a00002e0074840d1724644000ca4103030380007e07151790401c2110741d001d100c2c14040444d42c1c0020b1000d07210010018074103008010010403181d9940000d084440e13840e4005600454004641c14514242410000d1002d0b05600076a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 428057553 1106 428056447 428056471
    0x20a0b22031106130b0601050a0e03010e0c090c040f26100c0f090509010b07020d150506180f06210106090614030105010e0f1815 57
    0x8031a03550107034803040601d40d04500d0b06403400d94000c00d0300384180095802040000c090031080342c3c0014003400c00d662240452102146c20b030100c5848280e00d50300b4007802141ca5038001c81c0ea8489007030150b80c1e0000e00c0d030750783c2000b00d61f6110710b1041c2c0c040c03182c1440c400c03c904082030940e00380b0301b007811503800b544408800300540340181445000fa841651131440321101c4d50820345101e485034060071b08a4089107050000340c41d600c0144106021900d0004080c0c0131503850703103c2e8640d556417017100e13010243c400784441c0340101400c80705e590140100381c061900411300001d00a20504034840c483c2d045654103400d000041004102c8604540704d0b800c41641070150a0003064090f2680c003d00288030340c0703001c45111106110000660003645007070300501c40040700f80c2c851a4400382490600e091034540303240c000d4540c00002504061400b50701c3d215400c20801610385070090221280b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 427877697 428057553 := by
  have h0 := BRFrame.cov_init 427877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 427877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 427877697 ≤ n) (h2 : n < 428057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
