-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4588
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:06:08.898975+00:00
-- url     : https://prove2.me/submissions/fedc2214-60a2-4479-a671-52df5dfeeac6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 825000000 ≤ n < 825179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 825001250 1250 825000000 825000019
    0x11270903090405090609010e0f0a080d0f0e0d0320041202010e190f0510050a110102040b0a080105011b05030a03090614010602030a08090303010510050a0507150f061d1302 75
    0x6560342c0f0f0095600448015000d0034160414888081c00e441004005200755482140b280b00310203000580407080d60340000005032110012800cd0020f05107c2c007003281c80c01e0a24000d0014058003041c14621002d20f0740b010030207004000020100d21103941c4002c0c20a544c144404c0064a045030022001544141b411600302e1010600081621200d2074124881e800c60316014402c0c4040d40700c03200c0180808450400702c41031401c0008045114500c644806c01a05883c0210118425016100034005000001d5100c01610300010040b80007441600c0c00680c1d44154000c45110440c1001152600b21000d186003030000e403400c2d4041c0c00c40e01002c413602c59480c401041c0314040f03440d0050180016601840d551940d46100074401400907200650540081004105594440002d02c2000307408e420107540703410b10040700350340501403008041c101b060028031343d161010555100b400d602003030b41c034100165034035854580302c12030701141c1c800c8840d0044000b2031081c0e034100007503554440c40104040354 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 825002500 1250 825001250 825001267
    0x31506040b0d060e0d020a021e0604030b01060216150e060f040302030609010e0607090602150a1e0c090f0605040e131e03030501060804030509040504030e060705070311270903 77
    0x600b0034650040d1401c50740d96000a41601e02449200c5404160344002c00d000951900002d21080d01d2120210010b440249a10b039161200400e4900464008420038180e41c0e54110107529a01c1200c071a500c21191041e0200b403140c41d80c000c2003d150f5039603071129108802002809207684c0110300c00a21701c1014080000166020005244100c040900209010448984803450644050800401d010b80b4071820b1000a40c0050100680c0c034014980b00201e03112864030100600401008058410500740d4040c0c9600e07280e0441030b008003540c0d451040007580c44030405110400c03401040c0024004100c00c00505a49042c0c1d5030700200d4041d802c0c1c104549543d00d01980011038403511501c201c090207141305054140c880c16004200707c0c1040c951514159a000740a48a01c0512038851603460001c075040c1449011320350139508024094554940c20341c1443d941e00c100314401100c65410039904101c650500710000b4107581f05540101640343c0e02c1c94004c1c0000c440042c80041c41d0301c0288070100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 825003750 1250 825002500 825002509
    0x7030e010216140105061503040816020a0306050601020c030d0905010e0303040b03131407151b240501081501050111010e070608060f030a0302060703090c0807080d0f030b031506040b 80
    0x60600d21481c0c0c14502c1500030000c180c00d588000305007e00c034a0322404486004240c22084a40c0300b90700c0002c042c1c0d00d03104200c1840c0080207122019401c8501c400000c000c00c46c2ea6030005000344026022183c00c641010b08165840e00c56003801800201d070380d8810406035024032081a800f510040940b23003042d460301d850681070780049901c0c50704680310a420b5018440700080464103a003030400038114842c00c1820300384045030b44440d4003081052415403441940401802e04071807c0c1c3c010188100c080030304001c04107205001c0e0fa2420070700e24200001552440c001100c04c036402600000328026803031301c40195a82032140304901895501c64410200c404024001e0201a200540300c4074039a08003501400351107a510a9a10301942c403080d03420010a030000b640d41d9101986250100e01078004e440c110103600c1043e80140054402e0701e502080194010840340c00403000350350360f00064038914800300d0607641094101600341d007003c0707544a0380034a001040340d03228001034804142e40d003d460216 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 825005000 1250 825003750 825003787
    0x30b0403050310080304030302030f03040f0b04052d0d0e01020307050106091e1401051c0611031f35030a020f0c0f0a0b0703020a080a0522060807030e0102 68
    0x11400030701c00008014508018203240000744c0740303400056042c0f5045540180d40c0e4843d032024401d180401200003010020740c040610300300765204400c6240342c00c10785811aa18404090391000815003284c84541c1002600440b801d000d07644001010105511310054400f58000562513045010402c20f0358007190090281d50002c0421f43e41c0001c0d007000241160502d40ca01c007039842e20780da051451004440c121303450464151001143e21111010101c100d076002101d1014004002600b0908418010004d40000c2c52003070003034885070340da0100f50301d6200700410451701401d0702202610b061881ca24a00c41d9121200080950304404900031150905185800c1204040c0c0141d02c80c0c1d181040300d480034070094040d4a0242c94441485046c0000030354944034a010300702d13599030041004014188200402e00c401504190000e5859820f410300034401c1e80300038050403040d10903400d02c0c0c920340c10500000c0e0483d60300d41c0d207060b00d54480e140c048020704210800c81f1240d41d002d0010b11078418405049 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 825006250 1250 825005000 825005003
    0xf0904020315100e01080709031208270604020f15040905090a0b181b01051605030f0703090e0c04060503070807090e0a1e09110910090518100507020322030b04 70
    0x211110403604c2d400041180c2d10051150080280c2d44c0070401c00030303414820714041110141000a05d940c0c071244100303c905411401d66110680740d001e401100000400c220340a18000d582e100c031b04041e10800e20126035130b68025000c00c400c0810040040c03011540c819a0443c12180503100d41405988820349140c80a540d511417041c0800980c0c801a1000c0200900250922100345615002140040c0060240c2c103901c43c60800101e46440c02c109051088911552843c200c1c40d0b01c80c8142e0070007e241404500568000d080c4140c046070309081820203960489240360388851640e6114441182d0150000c0c0c180310903c00e0160300420f1103070311110814483c0d40b00020010309807600202c50f1040610040b4909801d1785008610004038100306041c03c0d80342002e45000361a52103142090101030110fa1206076118500b405101500f41d02d180008219421102294140c0c050f0701c4883c02201c0d019a80b000160f8810800601d2020340c481c1002080c03c10750100c818030768ad50361034070b05441908940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 825007500 1250 825006250 825006257
    0x2130906090312050a0b09011202061216021b0904030309290618090304170708030409090308060118030213110c010f11031b1b150108060c0f090402031510 68
    0x8840f0701808052003040d520082c4c0751014004001c2c0320000c6643d0a0041c00341100d1541481144010340d280c0b54216030380100c190b644070142c1c0c17500203942115106e10041080050088174691416144100c10100c00c109000301103000903100d40d54103070024515900112000e025007107201a2280c1c400000c040312416141074a0280c0c074007041048074065008132049100c00000c020f020540700d0000968003614031045418600d0420b5030800d42c900070300e40e40100071500c8002004105c2d448203401c130b0030685120f600c80070040e4407081c00542c0e0360505581d0054222080a404001520704034900581d486d10700f00d00092030040b4802c030309000c0e0342b2090321070362540c0d118014031103000854400e942001e07400e400c0381c40c114280380503541815400b86c5000c002540c070202c0c11440c0b00005c1d50001d148185c2c0001100c4034000040f0f0890766411003441108000d004440008a6080b842c0c2c04079107614005105031407801201c0d104000081d04040c000381032803003801d0240e1000f0380b02c0010251200c1000e49 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 825008750 1250 825007500 825007517
    0x206070e01110d08040b13030c0615150c0201021c0f181d011e0b030705090f06220603050712090f021c050c010c02180402120d0906030e03090d021309060903 69
    0x10841b0039503001802d001a10740c1198210700c04240c1c091010108075a01070400304211020301c3c0449150601a0005005442d00030140300c0107540105043c40030394400c0e003c0d681c411140c0407440826010009020001c206084c65001209101d4034200403818a07911038406501d0321307143c505400c02e0010750f2680e22195268014400c0c0507001c8043c0d1126074500c4920a003403801c0c030840c1c103590f0201074024002d001c404a82d08181c0d80c0c5681c00440e8500703010b001c140e1034443c0c0400c000d400624800254140041e00c00010444500c00c1c01158424151612a9046105401c410200406281e5410382c0e10382140c2094000680d11001c101200c200301a58118408415051030f03401d120074110541c0c1480300940c0780c0030058941d540804075240907218001d006545900201d0b0380d05418001080c1103010340d1080c1c00503990003c001c081541d240340d600700092020784400f141e40303201300f1340b2456202c41e117100701c03000616202403140851408000e012600100d0307544c90b0b0051340d40782001107004c9620803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 825010000 1250 825008750 825008753
    0x50304080a0312020c0309010810030b04062a02060711150703060f06020a021f02190311070812040b0903031c05040b0f060d080c030f04030624060206070e01110d0804 73
    0x400001c0f001c440c0390086281024201c0c0e41d40d80d13071003030400880c184100c180000e003110511140d080001c5070040c1d01113010780b601d450110000e09040c4d43c9a494540101488c002d80d80034003040e4001868240c00810392525011015103100d81145a19051846081e10090091000100a43c0a1403641d200460043d0074003075002c44900b40c1e07401c100b0440d4810b040000160303540c028000100018540b032070041c00b80c0e82e11700b2814003655494a400c01010740c000d007820541c0c06002c0601540c40c20064a207095103460525440d034024a000c1045c1c003400307201c14444942010b0041c40642e0b001011a49051a091180f50100301000c00740d0031880d9a0b00204400d1003031448081d917100201c84400381851501d00005001100d12402c040c014000204046040d820200100d072090088508201d03107840d80e80ca8210040c1103404c01c58010030b1a030500300000910180c94140580303000b5005045280d90f0800c04980181079210aa410000446007504507100140b00c80b264400b000d41e07a0860b1071a06 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 825011250 1250 825010000 825010007
    0x1905010509150c0f040b3702030d0e011508010c0905060c031e04120c030212060603030a0e060d06091b0906020d0c0807020a0b0a020c0405040b041509050304080a03 72
    0x20503280003600110b16005038503404098807907100b10491001c98880704100c070412250700607504581000c1200180f000c80421500c4003507559050048030201e9041d5070b8000c0446a0800b400c90f0300090382c000c1c0300e500803e240380d030441c0c1c40040100c000041c4544104c494000d00f040f05a1040070503956800541c00103940c8800c092000d0300040c4c848920707002c003012410b9624864158114101401021110106122101294000d200b2103182d9091943c0034140088400341c2c2d440200d02c189920241d0059171000414414419900200550300340a1140e5056400000a00030a948080c0802c508901f51000e44101c0c40641004080018218980001c20189501701c511b003109100e62104100141e560000300000000e04c0361030308407140e682074034048180780074018009600801150010641e40e00c400040e05a2905903030071501400c041c80c1c2400202c030800d540240c5150194400075000c1601c0100281040300010000254040c042c1c0790241190041d030001940c58010141540506a0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 825012500 1250 825011250 825011261
    0x31e010c14070f11060f12090a0b220807060b01030e0f03031f1a0c070e0c0711010c0b011401270504111905040e09010903020a0b18190501 61
    0x3164100401000110400520140a6038100400010102c0c40f4001000321040562030320080c06408031340c0322100075204542c690485c244015482d42c14074000382c9440300008204203017036088440ca40d2a616026a2589945280703c0c007211076003c44041d60001a0180700100800c60042c040042c1c43c500d040f0006040c0ca8880582e07202651050315000101800841101d800130703540c0d80385510711280c014003203502c035605500c0600369071005030400b0004071148004001d0103450f038069030070703041e01c0345038018081d0360540340880003010a200324800245c21800300f980d001c905040100b122040d650715014000d200740c0201c844000000f500800d6540c0151407182500181a9421004031903503c04440b107006502c20184510344036801c100d100c12030314088541a0703034000c1c05218645041e90018019921620a0b100044202d4000400c40b4206114944040d41d155001d41003070380d8242c68541c030404004e0645c1d000955402045c40d104501041010940a000000c03050030f01000c0c24032a08445 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 825013750 1250 825012500 825012521
    0x9010506090d121d0f092e0e0403081f061d0d051c020a0f02040b0604050909010501080c010c0201080601080c041e150206100b030a02070b0f0a0c0905100815031e01 72
    0x1080c171001c02080e5403902c2a0681c04041612071a6036500e0310000e038800501e4030703c08141c004042040c0401e80800054080348528000c0d22083c0068441c000c0400e180d1400303610030441021710100610045205011011050804c00010b1940c40d2050000404042d181602290309038441c0136007251030f820394a1100140e900600203001c261a05490742200111808002481166a86902d0400d076070ba8500f0780e03010b414058040e190528021010724002d00b000e020f008003501c80c10800078202d40c070480480900b02d0341030f56041c1031900e5410055601c450090002c05110205210109454140000e241011078629120311556481c00b800319582d041e11089007002c54201901300502413001d0701a100840e8038995035155240c0d035100e4002e0081c01540001440c5501b15420300a0710380740317880c580f4016907601004100e000c2984508ad14180510311544d03401041003056842201d02034104154803210031407500c04d2400100c00002d0805404511100b020f00103031001c4080007000744101400744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 825015000 1250 825013750 825013759
    0x110a060c200d06111e07030801080a15020901120c0c02011710030f1713080d110705010e030f01140403110c01120504140f1c0e09010506090d121d 64
    0xc0e100705002c0790500a032030300060140398484007010184a080b50032541c4410580000c025100710410b8040c1069000030026400203a0600022440000200316a4041a4888030b120070071003000104c40040e41004812030305010014010304845400d5028442d15005184da40c020440c20070f20000d84a02820241c240b51034510004010703800e15640380704003e0366044000c1d0152040c0d00d00d080c102c0c1d41000340020340200d03c089a020ba0725440e8403003880556240c081511516284500c044031000040c2c928080140d2108000b08610b5002d60006542c2c1000602561620807800e0001400d5600c003d017a8a0304a04200400c03003031544c0040c5040c0f000c0c8011024003a42c00c130003400203180300030100c11440c4d207964400101d030410510340010b20400404905480341b14144128854440010100d440320a0003200ac451ba0041e11542120001d5640140030901703c1e420001070002903007100f020103400c0b02100c403441c1c0c00300e103281c20482c02c070204c2c9550300a142000c8545140c1a103d5020445025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 825016250 1250 825015000 825015053
    0x40f0f02102a050a02010503040524190c081501090b071208060a14150d090b16050702220204230a050a0e060d05010f0911180403020a0f110a060c 64
    0x1100403130040000c5409207809a220b480d02e04050341007580c0580e1420080c041904030320308a9241501180c4115089640c512a85041c58400026121880304a00c0015441d50008005030322000300c1e05480c0e20f040c58400512602c0740c5078184550300c1100142c8406000d0410a41d003180d0ac04c500f00c0c0e0200f0240c4905008070300c0c000614880d0b07030300c1c2005544950f1039481c080c101880d11100307590060b20040424800f00c950782c28040a602d40940d80941e0301d14010400d15003441c040c0e03003210b084941c06015224081da03045002644020301e10303c600d1200d81c003007000060314158000c00760583d40304203c0c0a00800c0d0a4807c00625401c5035002501074140d00701d0401c1540384400210341e0104c0e041d038039141c4503442880c1282c010110130b8a800502807511440006014903010b10810f1510203403132140c3c6818001d001c0c50322100007160000c0c0103034011312241c000256441c0000b40c646224403141600c68619400048004089811580c00510f06080420034406c80104540304001d805510824 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 825017500 1250 825016250 825016253
    0x1f03020112020c160915050a0506120c0903070e07110114060108042402040501120614060d020717032e1e030606031109070201060806040f0f02102a 65
    0x5540e02101d00c00c0441d941c08150480c0c00c1406100703542c00540000c81c00c011361500c5400c0c0d000140710300d141c2e0350181e50a40d880401d031410f02003640b01c15502d004040ea0305142040c12b4417100c526009080d010003600500500200d92000c00c80c0350080c0001d0799800b070841c600b18400802007641e5180080d01c0d81e0422000001d4503e1640080d5000202032070a81d0380c0b40e0b038a013800c187e58001460394100303a4170200c0074260b0f1010654064425101c09981d0303950140b0900d07042000390713130450190101a41005078801e0603450800024000940c800101506000303494407008009840e5080c0c040c5d81c035000000300312401008450180403601516102c80c1d05c0704415440000400d400e0003100062482e0404040c81014050550401503074040c209006042e01c81c40c00251541c40311001501604180b40414803050042c00340d08240c034487c000400c01580c3e07a46459082c04c900c050b080e10b10710002d00c0040003684a2009690f070021141c0c40301c1c2003614146450305610300403084a800622680040b520 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 825018750 1250 825017500 825017507
    0x1509050318241c110d1d0d0306151403310f0b07031401060813141b10051e07020d11030f0a02010c020405040812040c151b17211f030201 60
    0x468510395060b0004541400d8011b14640700340e2140c090a4610650303a00d07450603603044c0c1104054981c0072840d0448654064030584124980c100080900072081c000128040c113a91501281d10040c600060703c1441d000c040c030151041200004d80c3c041c40305442d99814031410705003068012980740303001c00c491352400d0501086040180201c80400c070028020030282504010201c0ca15a0000746103260103091283e0b4607074861340f03900514500c3c05604c02c582110700e804030760810f4250303483e1102d070314080b0300441c201d0364030032324a0a0042418040c049200940c5400ca6900000b0b4840c41089041c14004820549040e5200c00030b00101d51056140c0c20051740d000c0c05101c8519411780b0041002d88540c41c00208600034402080724058404003000b06202c80300d181c600413a510840c8200847c01c410000700c440c1d0b045000c2e841501e1005606030000908441c0441149150907410310381410b24440c10114980c2960041c0c42c100c0800c1d10520004c0c0b0a1000d040e40340848010700d9650051840d40080c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 825020000 1250 825018750 825018757
    0x203162a0503060f07121811040204180b0a031709040e061b07020f0409030206160201021201140a090c21090b0f040f0c121509050318241c11 62
    0x130180c0700c41c00e002103803202e80910038541048488440510a2403c3d06406002c240c1031203600b03035045a10800700031200d01b050310848003559001d0745e241604865180d0540007401d9070720540b58000c24112030010100d03007461443c403401103c0c50101ca590700158003c1000b510a07401808030160482c406111140310286001098102c810101c9501c907a010300004804190603140a5002814003100e40205a40411801d106043c50000c460f040098a10200c0c01c0b4051510110400500070005000c40700030007246819130140282034541c0e241d02d5404910580b200b0000003004589114038540c201a40e20314607100e0880c1201c010041ca05076911459030821014220398485605000490244020200007035212034000d40c1031031182d035440b0050304cd2940800010f50307011601c1403da841c0d03c1094042d81040540000056062401004840d245110313109032090344048400f00303444070245198901e05101c400d11040355103644000e40d07200714056428001804070717450503120102c0c0101079000d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 825021250 1250 825020000 825020011
    0x504030803010e011e210c0504060602070602062a0306061309050601030e0a0c0b1b0a0f0c05093c0103060e0f071802070f02060309060106020c150d0209010203162a050306 75
    0x10b11b10601003506052010700240c1d0009508907040c80c901040031500001d55104072180c2d43d08556040e0b680032416525000c2c2d0408201c5146204a0b20412584d0020044d40e000710008209030714120480186d101c0815003548100f4405d600c801c00c0100c03660300362049284152406000d08a040000d944149a0754100c0c0290115000301061004183d01a20144001c2c106100210f07a6140c0711410301d03140c0f00040798003c80d1440d54204020806081008040b40102c20b280d4000303180c4030482801c1c0841c0c40c40c408049920b04001d00319601c110320601c0046008500410b4009000c48100100750704224003500b031003145074400c02081003191041145403401c090100801a121410341c5000f90b61b504030000041d40c0140080144010b102010582904844046d000c44009090500a20448101c0d0f00c0351a6903d51003406240701071840307500100b180c0320052040e00d00d0481c481c00310000b1410482400c3e0380b10300f0700700e15501010001c1080321021002e6091a01403052030000002c0d500c1344d000300b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 825022500 1250 825021250 825021299
    0x30e0c04091703090a150b100e041b050c0d090b0703120b040c0302091011030d1d1f0507030b0d0312090b01091a090606070f030504030803010e011e 65
    0x1001c2800000310144840703a0721040015668201050030395551901004192400d00810380c1e945140c24161295612904014103032402c1a6000b500669900414103000c507001501d40e1a41c1048001810001124828984500d0786404070401c00c549840c1070040810140b110300c1809101c0c240449050341c3c10f140d450310b040d4410a000300c05070406004c0d01450399400c03034100202d030384440750142c01609402c00d003503800d4945e807140c05030220f07940250071403240681d0300704110a041180b201d822404110b10007944600c1d40022500d0341902d8240c0f95010321402d0070710814101107240907401540c2d000b000915083c08100d2010001a000c2c800c0c0410050500c03080c21326407882010b440c0c2042e0005504110030200c1581c0d10601d00c0e02403c050400306494035030741d082081007840c2070040d0501901c00a0300b00c03420a10103688842c90785030084025024084140400000141150001d5001c1d00501e00810229450f100c0010701002c0d03a07a6030503040141c0480240100304a2183c00c8504010500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 825023750 1250 825022500 825022511
    0xb06040b03060613020d052d0415020708070c030503120703060e070809011e1e0603080714100f0209010e220b0a0519081e10020711030d110607030e0c04 67
    0x8260300c1c020f2181072201d0686c0c0d13050104021400c0310f0409440420440015201e1030000501803907410041c08483c010003200c2c405901d880c03510400e82c0541703140d038032800445150002d940c80d581d148100b15807040b10607a000045000701e0110f0b101d6404d4100c080307407e003400001c5c00c1444d00741c1800302c01005001001005e400141c07030300000f508100078402180b950480110041c60070540a46a400300c240072031103d00020b0005042c481c4a03076012690410026410010f00782d82e0407594808160058000744520000700800c0c000a1150306c215071442100140e94503800b00002d1302014012103490f10503002e0324401c0007000307080c4d640101c1820301104000340c0701441c0c400042030f460460700b2403a0007120456051130340e602c24501100039281a2012a04800c5120496410304007640703203c140b02d90000e140742c02d0241c607150050202203102e10700c5410341c0342580c0007103864483e1600d0820700140d4001503d42006d0b6050017170540050f0b0754035003440074900c202d01c11a980c100b140d98860040da902e4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 825025000 1250 825023750 825023779
    0x90606071209082104121a07050720010e090702011b030f1104051003020c031b03030406060503030c0703031116060908012f03270304030b06040b030606 67
    0x8990321141e00044021070031124038401800040746000310001881010075043c8109803d090000c0c1305684101c0041c905400d010711034800b203192904c01c84400d01c4420781022044241400305210340e2595944a03112140e5050015400c41c5442d01f5000b401c082c0200740910b83d0340294548644035007510074030410f44600404a00502243e07055000398a00c0e020700d080b42d2075040c0c00c400340526600c0428054001100c8618410b446a4030806521807001905584c01d41c1c003c0e0041c1c41c10140301d5090300d0074028031128170100048220028005030f00004108403c2211034803400c4c1c00b07450309900643c00c1c015500816039843c1494000034040c00001d04071038251103010081e02e0f094400044141407030980c2c40700042c3c81c6030564001d1103c15400c09041c400d900480d09001700c43c5010880c055034840c3c414a2061082d0751015111407124048000b50080e01003802c00000f0251401c580199941c6203581400030180801070a07140c86182042c181740c0050f50005555904042c2c203c8040e00e02040c4d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 825026250 1250 825025000 825025009
    0x80d020106052b050c031902090f0601050712020304050306010f0314210d060302120f1b01090e07030e010c050a1205060312030c1224030105190c03022205121203060906 74
    0x541d258140d142c400e084004900820b4042c083c10001d10271b651582840d1191406010301c0f403011101c0c5d60002d807080c4410008100030507112a2441610300640f07140c1a03c0c0e1010906080d826044100041c207090300406c10444541803c192840c034050103014180c400203c014038807410070030300310407480c3c010a10828443c0d895008200543e4000e02c44113144040c032200720b459101c115031030409400303800c420319490f102d508805e04034114141d5904000a00300300200c00c0c940c201800440030075944000b4041862800d10904541d400c25454050b140c003043c20b0000c140504801c0820a618100002d1180e1901d00207014410540c2e40c504068807035075041210181c3e800744c030105100061842007031140498014410f482d604e1038030480075402c002440181400e8a400307451a040d04040a03c0301d40b210720f5030341c1c8196800c900d940b401620b8031240c0d41800030580f101c2000b40401104c00c880410007890610180c90741c0980705070180032082e5441c0c150fa03000d404010030b054000c98444001502c19a00d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 825027500 1250 825026250 825026263
    0x203060112150504091110020f301605070503010b01020316030c0c090207170313020409050c0d0302070806011403060708060f1302341b03050601080d020106052b05 72
    0x18042d0080007150080e00744090036818001d0603038010501c1c7c0d0908818113202040c856002c1a0172002408200c919130100c070058180501080c400b2403d03102080542511000242541280c0300842c26000d03900b42065401c1000c241c0c04103102780e16101d1161126600441030f00c1a4043d6505403440700001400d055404000107440100b00410090010030398180f01c1d405412218000d5410141c1d60000407480001c82c8003d40c4c05007494082c88180000501e0650030900302c91b4402e00c203403400748900b038003c600801700d00035045000d03070011007040c04290000c2044600400802039100d18030b40a0001080c0c4a0750040e141d00704100c010302c002070710b80c3c0314404041342060000d442821141d0325500010000e4011850052402609218604000c80e08540c002c190901c6c031815082e01989a5660042c21126078110840010b102040000440d8051106034000c0000c40c010740b9040c140d0000080c2181d555810951150011002d10000100c0c1d40c42c0c5180c4030f442d10008804c0d9000d0300d051903440e142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 825028750 1250 825027500 825027509
    0x20405030f07080c010206060a091e180203060f01060c03050307030e0a0b160c02090a0e0f011b140a0e102c13020f07121101151503020306011215 64
    0x1c07440000c0700c06a4000140b440c00c441d81d640c19a00b40800d01e07801282c541d8025559280e01004c0c68006000c090420b900c130030808445064402d089060341460705080e1900c401c3e04071426004030604405600b400d0040c1584500207d0000110b0340c1440d07400380c402c02c4210406010000003100081031603000f5809456030307400d05021103c04a0152801c0c0d00c0320704c404c0703600d0381440c201070108020050051001c010350702d900074024401a55850304100041900d2408074019200e40e0000411a0000303109a1051000485602d01980740520026109580c01082040e64110402010201d6039219240c1e240c04101152a48041c41050340112094021004001c2c184c0045c101c0400782d001c01c00030700402c959801e0343c5001400b0b030b20090040480c0111268820128800c100880018080c0145070403001d1032030619001c94403441701000e08580c100d0340d4411070024540401e00036603103262020491181549030a614528107200000e100c60481d84803894181e44403100c240001214000b42070151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 825030000 1250 825028750 825028753
    0x60b030f041b08060115020c1305090316050c03061b0922050f0106270510031409010504060b0609030a032d02011508010e150903070c0b07030e102102040503 69
    0x450712a03d0302e90726002c00380b0030070365548180a03901c646a400030808440c5141d0051191404070f0b074585c2144003800c0700a154100394081004841d0315008400903036405540110000c0003201304c2203052500d080c00240c44246820140303a915040b506241044510500701a1034440311030f0150740742040e410628024543d210b030b05103030800455a2800103d18100c0750241d8070880311094a0f03805107192040c81600c4001c00c8041c01050280e41860f081d8061000e195183c000f0341c03041252403208282200380d030010309507511001400240082800350013a04001100d800745400384840010387d81e172802c280b0003000e0101b28080409030a40c00c81501a2244800c0700c01c041103008108028020114200507a003030041d5240007040307441d81407040c031681c050030b50000c20310756030b640700f108407000360050494250b0300c420400d0000007900d003040d0301c4c010440c00030504e446a499103000717001c40720301c01e511501a12116450444880d44a9032035002c0c0d01ca03900c00c0346414441265480b011784265009503415 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 825031250 1250 825030000 825030053
    0x50d051504050f010f061404090e0303040302010f0605060d0c210c0809060c091c02100309200307090207050703020a0f0608070237061a0307050103060b030f04 70
    0x40814200d091503004840802095840c036110201c6210203000b101500200a003050000320300038520030780b4002c0f8a0001d142000d64640b03404050305c0800003201038a80010052100301602401180c512a480c0c68051214504107070100f1a41d008522a40c0c01c181e44640a05401030301600030045c1c0c0701440461010700305080b007025406485004c1e10040020396040000760340721004100140250f07401c60f0441d2410340c2880400c0026450788402c1c0d4500b49010a2500c0180c0e11408510340d05c0050f5100400c030310f0110b0400407040d803850b4244c842900782c4454401e000c0e030307000701d0343c0e0003075400c0d000d40140c0301c41413428120725041050b00004c0d0401d10300d142c04126600c03462401401c880701642c4142d100d940c0c0b40012600c40c1540c5910948140120341c04180c0341041860540b04d4502d5071001c9000d00c20030b919602d0641d02980f403c507070300e0408510000e803036040a010040c0904403e0a0502c00203103002200403c61000508600080c0981c0300400d04000750203c4581075407000782c140480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 825032500 1250 825031250 825031261
    0x2010509181006200a030c1a04030f030501120b070f1b0602090f01180501081b03131e0302120c030c07060806040b0405190c0302040b0c0c040e190f03050d05 69
    0x1000b5090241001103042889041c035010700c1005164280d2280002400710404a80d406843c2071501c2d403011120680c0c035a000801d09040f0014062007a4000ea07107010380341d400c90002034121041a04078805440d060088000450312a094442d0072007070b00d00c1e100240109900341143d1014000200401214022024409015003500505141c3c1412520584e140303e02100569400c00c54000c5012500a0032108100941c002c0641e298005084801d90080e54452010391100368001c403418440b01101010480600c03d20140344031424881c0c000c2d01e0382d04910b07901c0107503881600e22103520450b000054895001c10044c07007580c12a02c08031040f54801611070801514070201121054052441e0490b030010501c1c00d40151805045418044904940404c47e52000f07001e1010785c040a068007040006403e0308060010410b12032040c010f0708155112a08210030340d000040202e805511681503481da1103044058950080d9200100c50503800071407505607158010400b003030300e0b8035140c4401c200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 825033750 1250 825032500 825032521
    0xc0607030309020f01091211010e04060e040c080303090709020d0209090405150f040812100321080f0106142d0318070305030a0e0d02060304060e0708030708070201050918 75
    0x360b5442c42104d2003419100503c004549110143c4200c0c0d01d94454003414001083c041402034814000601d0f00201c42d102c84004201625100d51040b010500d201c01044144a1034003040b10142c80204040c61075401c00d1038100c0d540310640d02403207403000c0e400256103074404229411150550005403111007035180c0750a03c551511a4081d0320507281c0c100900252603199501c071002d202d640d0222729142400c1c038030940d03401484002060019074002214022004c40d0125100743c04c8a0740d00c8507005444204a40e0050043e0b070b0240481500715036001c01445a590000040c0b1070f402940e403261600c4241440c1c540b501c02200150f9140c1c43c0c60300c0201c1042410111000314410b034112000c0e084050358603601280c2c2c42c00b1a22000d082e6070014080700e80c081c0c1c82004403000b1720344000c081d04c05220341600010b2482d48141c5080700c203203036140000234191400340302080c001c1400402541c18002a615517080910980310000d041180004440a003940c405000310a009a0740240f2480e910f012900701 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 825035000 1250 825033750 825033761
    0x141906110a120f021e0604060b01180305060604180f17040f06122304060b15040b0c0607260c0c0d0e031c120207140d0906080106090e15030c06070303 66
    0x3c0d0050040c200045140240c1d800142c0304820308034014801d5603220389035000200f0b1b100c21424104180c0c0712540d481c2c040c146141d080618090b0b03001e0506820440c04000403035504413108a141c0340c13069031000100b940103c044056580040061300c3c40900022101e50b103200d5074100140000d1940004a00c0c0c81e400803a940e12130058000410140d854012560584440c0100046012034100001400911290800d180c41d400280540100600480d0b420450350411703000780d02a80404544002d61070b03802c00190390448103500300019a004403001740b94400420300c0340782c00440450000301d94005408401c54216880e0801a0b800c406000c240041a1951141245129100c1c072040d40840720146c540c907032a4020252940e8090200c0b40c00320782c019422902c1c050700c3c2d40d01c1d03030010000c0c00c0d082030009403d10300940e03039091403407800c0c100003405202060b001401001a40721003400f5411010521a4000480420381c10b22540e1a100082c50400c1e03010340c0d43e421100128080c020140c041c0c008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 825036250 1250 825035000 825035027
    0x1603030c020c2b0302030c030f07150c021513020d0b06010f0e010c020f130203041b06020a0816061b031512110108130813141906110a12 60
    0x340c40d02c45070141c007004030782d9a807281501c02e0207046800084888105180001c50248a0b006590401c0344a02029003580c1103500c00c00310b6004000381000800060240400c0e01c000c504004011680030120002e42e9003400c070000d2154840d03a01d002c9111640d041024031000e0768028030402907000185807044004a05940396400720701030040021401d0b0003036004288115040c0d50ba007060701803e07002c001e2201c46030501d840d044009803240e66417400d594001140b00364001e0019080940c50740c03001903200400b40d40501d0443d0410031501001520b0441240c0c0c1c03010283ea01d18505049078107040006080c2c01c1c007070584440d03d4041d4200d5554254000c51036041141d841c486d00390707549591b060803016001070020242180884120b00c5907024400795034208150810300c4e52501d0040d900c61440fa401605010051800504100300120585000442d80d06088e5580d08400b020104a1078240000d40941414080c44046080800008101c43d0b03a10380c3d004050340c440d20600e4513002c3c142e250910746 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 825037500 1250 825036250 825036253
    0x203042406080c0607060920130e0714130e010b0109171c0909020f04030b0a18140f1b0a050d0804090c050d0e07080115080705151603030c02 62
    0x341480806039229550407120b600018040c800951010808694043d60381196075550340c2d03000300c000c94139402c0344148601181c101200034a00c05002c100c20090900030b02941c260901103801d103e4a00417420b80116400c0110303100c4015041c5002517489a514a01d145201e40340c40807c400300401500058500c0d10280c0b10391001688070999a0041c0c80300c082c18883d554016280b00819203010030603480da4800c20701d051320280d078071908024180e038404030406190079404501030040c02030b00f413a0550058140282006480b0915140d04150042204003604800300c2c0c0c030b10111840c0e024401e83d15108103110580d2003e180c1c04061016150000300c0b440c0c05010151404252410300030003650000750022282810645072488400240c810b88204004100c001d00003090702c1c12031400f44603280501c1c1d40183c403c09050040341421940c0c804030042a02c680110101700b5040082400019201c040e1141414480c081c001284103200b0140b488040b0419513141b0010316601d0750000b08101116030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 825038750 1250 825037500 825037553
    0x30a0e01140f03280c0504031704150807180e131103011e05090a0503030a0b0301090f060e1b01051e070803130c0e06130b0f06031906120305070b040807020301020304 73
    0x4402411150b145c500500851020030040c40420601110003403d4070b410a942c51030203480e070b07200000e6650a0b400c00004038500d40184603009410840030181d20503000f40d400b4000d45415064002e0b070310003503d078000440e850301100090003144e03403590840031000380c000d111146e00030304400f00c0c3c6441482081c4665152a02003082000045801d81415803c02c00640c01c0d5111404003900030254018600e0f4559600c20554000034201c1c1b8a01419501a050006d5110f4080a40c3c2c0c3c20988080007240024500003000e84c0c56a810506480300c0c040740c040040c0e6402101d0032800030780d1180040140101c8808410444d000c840c039020000154070907070754046916a284225005001d0941b5150792016285101d09030500c200e0380183c4800307030002c2600520008001c082040b81c0d00c25150001c0c80040742140300349800b4980900401040050111002c20343c140e1801040385c012110018808201c0d00041010301c520502910320b030f00d40040c021903682c145441e100c08104100380c1d00107403424030302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 825040000 1250 825038750 825038821
    0x807090f060501020627010f0507180308162d030906050301050105070605091c1d01080405060c09060706020a0509010e0d0c0308090111010f05010e09030a0e01140f03 73
    0x24040d100445030b040c0c000301419207542c85290b405071645800b803459400c940620a2003060f090141103520280e0081c00290f80c14445001009074207100310540350303a50602c3d02007001a440c4401c40d11074080c0b5800c1845030150a1401e803440045801d0300305141081032010400d41e40c103002001c0c2c0654807036203c4900266503008195074602091059601240091000314040f0f180b64015030b17404030342101580d5003445070160102c100c3d81d103525a5400034445e4245a404a015070065030b140d070409003810748003440d01c7da8038103542c0c290003445030801ca0000f1540ca42e994aa823010ba5075003541c00f0b00705544a10144500401d907800520440380083c8a001281e04c040c101076403501203054018043d1690142180c0311400b05500c92286941044000c0c8403a03100707180d00b031048465201c034040c40452254900702d0f02000700c00003d81072209607003081141c0c0402903000200d00e042c40c002801c000e103030411141c02a212500032201034800c5a5000020000035520141a00e0740d56a02d65807a840c84600b078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 825041250 1250 825040000 825040031
    0x1140d2d112d04020904020c011e050106030b090c07030903120c0506061c1b090216020a0504023c0703080a0c020106300602040806150603070c021306030b01080709 72
    0xe404414003a150040b00c1e6662030409400510b11444007070000b524000100032111f0850360195a0b84c8400c412440c0c40180b18000c50042e40d0040045240601c14071780d07964001590104043c00203003407214001142d00030140122a00c40055410004a4500380d40000000e0b00c040020b010032203d030300400300011030a14000d034880000d2441e00020141c18411940e4103400380c916005c03420300d060b6025070000b81300400ea000600d80040082039003115146548103206040e40e050304200e10660040c455001040182c1e0808801c0020860b142c4441c60902180c074288070240f01c01c500500030000800405064118092502071303000c856040004882030fa00880c204d94542c01262040c603903201c0d5403554000324010000050400c012081002d494564602c42281c0c00740d4480c404c00c1d00700c42d0801496000c0050030311040141559007518615044034010801039019400a05c540100d4030100903904456000c031b07014680c0a0001d8045584070080c0c103039103030058440c124031582040c10244c08500c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 825042500 1250 825041250 825041299
    0xf0516030e060f06060c0c03030f0901020105060301020702012a1a04301116031101180b041206140106021c022a01020a05070308030105010801140d2d11 67
    0x160743c415010740d81c4500007081613982c41002c003060301c0c0c0310720712004103166000e0006222064200c14003e554504160001e400d454005003028404e92040c402500541d80004104040c0c04107540c2c0c9041d040030101540e07070581e002d4080a483c4900759141c0700b07000241003c0880c00381340514000341d00d0681c80c9000c440440b4440078030740e40c0301e0030498a00c00742c20301034000e01841c1e49410054582c0c103003010801d07842001c49940142d40c290303296003825015580080c1a4001700c0b0075480d18528903418880100d207a40718900c01d40e42841510030300c100c1404850307800914102824100d0444559555800a594655809028591035407001c0410002c5000007488032100601c1003d8113190080416409062030ba03110545066001c0d40c550240020014881e01020710312407104c20f902c0c2d5040c107000400c4541d05030089944206030790300481c03081d581d0440c80b214055102901c01d45404400d0403a85003c0380144612405004203008041003000ea0100544204400c3d54400031300d44060710702481501d0f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 825043750 1250 825042500 825042511
    0x7060212011710020c07030b0f0103030906020304060903150914060f010602030924040308030406060f090b1c0c080a050106080114040f1203110307050307091a1c0f0516030e06 77
    0x1401850f03e80711050450f00a0b01c00b840041c0107840c80c05e03a480d11860311032017044802d60985803d2400610800d5045030180000c1c200380d20086081030308011014010403607500025100d0460b034001081c9491154020011907940304660041e10150381d201582da4440030750f111240b0286c100004110244004190b40704040010108a02049049080022108801300720041088100804400704500700000c41c02284590b60005506251402a07526500150440006182441e0000106584140d181e0419886143c0700103000c400d40d1500c0c1c03081c7e01c070703d80c0000082d024110030034083c03000c194440001c90b8041c1d40203110b48481c00789000208032007182e000b88801c0d201034940012a21034150601e00c0d00c6542400924030701d0000c0e0b2552280c204464040005000008000001d54484c03100c100034404218004181120201c0b880c905000b0800004075854451800030740c0b001c440c0c0c019200149a407a004c003c0d074140000d040c0400f00030001d041c00403a04048110380c541380002021071244 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 825045000 1250 825043750 825043753
    0x20306010e1506030a11030c0711090403051206030a0611120a020403050d050d0e011d15010806061c024605010c030e04050f18060c0d0b030f03070602120117 69
    0x6030303034402c100101034202a200000c503da0310542d81a992180c070b03008600481031680c10301d81b0781e54145403c0b060f02d0804e200c0b1500174085203090000098102003034540ca0254071032030311907507511032020903d01400128086c04c2c05c0d08100c400e4001000c04001444880803c142c0600d46943d44880c40e4141e1042d4440186654041d0342d40b410614030503006011684954400444c0206c04501d180782900c16880c441c5181010811070850650004c01400d5294103003110a0b6941307600d44120242c880c20010407a5000e08400d48011410440d60004c0034800caa008008111441c1c0350580b06440d0360b880031200a000081c49003c00640601044100034800b1040e02c080c00e49085c50011110550b0b4454220240003000d01034401595a03406050701ca404403650000032858106a0115050840c0c100141690050803d00041c24071600c100d94900350b6444001c15803402680210303151401c00300302c548007400082000401c0001e542c005055035910001030303d006076201c45422042110820307854125 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 825046250 1250 825045000 825045031
    0xa050123030d0822050105060108090c09160c0602040b0a02072403020d0b060c011b031811061c060303030b0a0e041b23040f060e01170111040909020306010e 69
    0x9003441906400c0d031000890340102c0412005402d180b41401041d2130031101a51144108003143d41e20004065205808000400e00c4085690103d0044003025103144ca050b05044001c10f0424050300c2c0402079254031140031907455550b0148000540c001128410040c0645032001a40d5841b4502481184200c6850601d140320003500c16402540440898450307552118031440b83e0741e03200c2014040c4901d81c200085440c41034003a02c2042e0040607000e11050501d020842140c1d81c030760402e40c00c0000d50024011101d0044500090b036540545a0404c80c08100e20a802c904003103180c1080040300d10a8400703015000c0c0e101c08000d0fa2000b0b600400000034030a00c006404181c4036100c0d083c89031020559040b156840320112404200540c0000360103948c1900150003e00300783c8182a202500500d0410540e8102601032003003080611035a24400d2011542c144119000e5025130b1407000c000041c141e86039568402c1c07a028061882081e4428020000001041e480400b900340c4900009400c0048 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 825047500 1250 825046250 825046273
    0x5040506030f0a06091a0a0906151b06060f0305061608220506070509091f0501050706060906031118360d0c050601080d08040303020903150a05012303 66
    0x24807080080200301095214640040c0d821800d208a4040c07160b4511b01c045000b2181c0c0c140035852000c2e0303014103c142e01d0300008210744645291b06620400b914500700c058003e1080060881808980300909110b02d44000041c4151903035450008036449801130343c0160b5500d08150947ea0039262101307011540b40c500040041e2080c4520008040d80b074440d00c0c0011a05407076045c42c0202c00c880f0303040420b00000b1812034524001c5203650780070302d6040e544119802c1c41c8900442c0011a8410030b41131000c0400e0b884200040d58104138041e00e003281003006046c0d90790803c9071080111520f001d000d5900071010707002213075580791094403031120182d1400400028450380400c201d5003400c0000e04c0000314242540b00c4109008058000340290340318601c100003400c1c030505045c0180e2100c852640400c0b19162480d400050356a84180c03d801c005882e81005008a8208005078884002e0021040c0030001c40701890742c4018180d520080c0e030380f5007683c182129041500302c041700d0190f047c0d011300b01514 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 825048750 1250 825047500 825047521
    0x21030e0102030c07060203090a141005030711010c0903150b15030c1e0a0908150606090d021c11011803060507110613060b0114030f040c0b18040c0504050603 69
    0x2001080620449103802411509182820065000b4000503040081c0d0310440e4a003241c031103009804120342c80c08a03107440034006813104e61404080002d2100c080f000070040b41c001e05090364204d030707008000c0c042001c035014001e101820b28081281c5031000b441c01d03554201c00a10441014800117800d03004404210982101c2c290002002c400e0314650412142042258217106600e074444040901502e940c80148013801c034203090380040300158040d0140300440c14443c60082c0e04448103490455031000c0c0e100c085691040f09260207508004401c1c80941e100c0c00d403c03103180c2d89900510820710200b610b440110364802c5584c142100301d00130f600060012903501e07481203400940500b80004084920040f0704e08010b030072203c0641050000ca8180144592030240342e074940003d107001d00004881400c0b10b0501d0001920440c05190b03094005001c001941c410720014000c542c503c1c80d10382d02500d5100740350901e5401c219000e5030403c03110070407080c0610140c40c10313144010031081c19aa5810034a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 825050000 1250 825048750 825048767
    0x2061602040b130605120307080a0e03152707080a110d020406031511090904080c07031506051512040803091f020316020d200705120114012103 63
    0x981c0e01a0742c0382d041182030790300e41d00700e4039100048203c0840d0300c0786010100480c4404503a1005143d40007045104005a0f50318110358201c0e800d400d215054404020109180114022a80c01541d52074000d115070145040d0309840d40c80910300650703601c985d1216109465800e240b1401000754001164200001c54600c207001300840d01a05014441c9260b80004040c2c032403640c4107a50811460194800080301da0245002d0401e40081591420360005c0104003802e4000304044c0c010900455030f501d44503001d0102c2001942c02207034070401c84c0c090640c0980200010300c5018401c2428100710201c681d4210305071684160701019100480d6036913128020682e2009104003405d000300c15138551050400080c100d050641c000005031a0328001c40d200b51100c000316100b1040d0760101c0041002c081c2d0041c181c068001c80900c4085500600b60720161814003e50031250f40006114070b40f00d00807505600440311420344116040440c1d9840648000c2000c00440c0c0286c0d181c000002000030078003a5584 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 825051250 1250 825050000 825050003
    0x5100f0210090f02090c19020601060c081c0e030d0b15161a0702100609090210030f0e010912090614250f050c01020d05040f091505130c030f0207020616 67
    0x1a10303d80c00754000703402c00c201111720014515002c40c54142c83e40c0c1d5949041d862440d54001490b01d0f506005019042581d28a0000d0928200140e0160350300900d10340c1e091001344000b801e000290704140000d03141d0700000e02101c0d01c0e51610301003400c20702c9c0c090000c41c1c825481e250340b41d14016074080040c20001c20311500b55083d003031b48680c000c82d10305c0d0b440d1840e2080b02c8641c042d0417203c102c400c95030262951030b07000740000d070700f0712915802503234940c258444e551509040c0060b110040100c1d00c40078002c0c0000030503031303946000ba07001c003440310403440b01d1005034070307070741e5210401c0e0300d420040e1610342200c004811810010f10940e61100480c600404c3d0600d11121071400c000010742d10743c1409800c26a00300c1d020f4002c60000c0b20301d035130100641000350890341045410681030240ca200d0541d1144070f00c001c1c4d591501080108042242c2e034480c0545006080c01807003121364544000941040000071001034603041224800c80d585109450b810390b13004240d42d00c0c00d07448261000450101850 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 825052500 1250 825051250 825051263
    0x11e03140a02340c03030c111f032a080906250c05070b0403261603030f0b120d17130206070203011d1b0301021602092a0405100f021009 60
    0x90f140c040b40080c043c2200452080c0e4401c01000f05514042c41c2018544010900501c020940b0424028210b60304030032000641c540082c00b0764080c49091074140c40324940c88002400c030780b81c243c030b45a400103806100300f0842c02100d0082d1525414009800d01c0395442480040313007107007448403180c170402c1c103809224000c000f1200b00760384440030040540d101d6801201c0240d000b1900ca00c0c1c500c5200c2281115815602480d03040c16004084507008013103030300c40201050398440c050140941107a00c02e80304c2c6507000d05100050741a12203031981d5184440d5544002c00c6221400010010f04e290200380701e141600d0b0f40604403030860b403c3c051140c1051400300da055480340c0745159410306d06002100c205042e03900901203c1500c080724030080c2140f280301c82c040d9004000c030340c80001e14101441c08050341529410450394401090561912521485140c5254010520355203a10f41c0c03000340c41a180d04899200081c02409810780b8010a14011a00903810550224203008417590006652030300600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 825053750 1250 825052500 825052597
    0xa08030c1306030902010f0f051b100c050909010e0108070b03070e120313050108041e030c080f0730050c010921170408090609011e03140a02 62
    0x40d814000701102d40103000026a944452419076034071544054103100b443c20b00d00c000800c10840200300c1d119191110401011421045d0351032007040094004800c80e0803c02c0005401e4881e000b840b503031003103400510511001002040c20352000d5032060480c4c90f06402464024600905940b440e04018a644184070100021040d19121180b40e42e20305082400510750702d5640742c040d10b501320764030742180781004408810030001900e4220302104254142150000f8015586011100030103040d42c0101540400b0274841c1445a8000107000c0d03162040c0710700c1006440c12001060703600c11143c00508800504103040d92684d00490041130040506800446d50a038aa01c405486800708112898208040f000c1030701902e6004019851000100d145101d1504141e02c0704103090088401c042d10030340000910703420301d0b8064100d04c2da00300b01030b040e0b01507030038510000580100110b503031100300e83d850f54001800d4002070340300310b17200d210790301da441200c0c490450312280d034941d00d055451a0342403988 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 825055000 1250 825053750 825053767
    0x40206040905160306080f12130503030708270616020a050d0f0b0906010b1804020706110a021b0109060c0c03050f0d1101020415030b01180801020703200a08030c 71
    0x2402454410503014a0309a81d22030540e40013401c03188154010400307600641030500700b0110120b044030200300f03808005070705c032400b056480031403205613400710b52315220010b000300400a09401170000800d00c078800084104800c00b00310000154255225072002041100c0004c03005280811201540003800302c908117525030001c600040d2440d01d055581103030b900c00d10070404c2000c20909601030441e00203008076500d0010340414602542c580800b4800400c007044000d91101da05980301c42d07030003c006000fa80c7c0300c1d80303124426901c6000c03144014020800c8550204448155840181c03034180d40e4003903903070b151200803560284242d0303084510324100c40000001c903004100b04040c004071213010700000a1242c00c00741c03d08a610340300c0303089a401804100004144c80e844031601e9411800c0c045103050300c4400480d0480e50144a54294612119000c140c01030154054040d003442030700c4444000c42d800340280141e008401002c4003681c1b0086118002400c02d401850b080140c09405506100c00c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 825056250 1250 825055000 825055019
    0x5190608101508070b0c100c0302090316061d0102011407080930030a0207140619090c1205031303030f0f031506080702070e0114040501171504020604 66
    0x1950140119501c441460040e11409200700c03010600d00c090070740035440ca010743c503507240d0169105040403d440403038140101e603000e0090084201180c10100407280d94608094025040b041440b800307031042c1005e18424400384180c24059403803688440e84203510540e100d03540c0ea82482e01590455403130b41d501c8010100f134060303011f0059503607441f4140035107000d24000e0f10b0448808a2021100305122000c01041118030032406039008070380659a81c1e40c1d036411294045d10484500420207803507200c10784041840440c43c00e002d031000700700d0200642100480d40003600d00e05840545542c0013080200b100040f000c40c0d1141c2c4922030816641010382c46101021129116401540401c0e040c1460100c1c10f40e010b5400100603019050810034002c040340001000c081e1402114103012058012400c0c036802040319000800b614041c410707087d03855a140000d002071800300180a43d0604002080c1d0b03076482c1c0280c138406681140144410320340d0720500b06003c0409442170360045020030001c11303132004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 825057500 1250 825056250 825056261
    0xc1101020706061409190207030306080604030206270718091b05041d0a26271816030b150714072601020c160617010b0d0519 55
    0x580d40082d0b800d1510300751004c0c54021203080d13403060110310b040000ba5079000d80a0b08184144900c01030b00c986151500750010500794105900601c1820304001c00c15500003200b0748180d038014072004540400c0c1c141a4500e10301e600c1e2b20b21b15900105400d10080c2c030862645009529282e401045092030fa469504600310240c1007031300c0f603075440744060005081074080d0700f00141909003d1a4100114440319845d24030b000743c0203060b03481100081c0041c442c403603400701c00c00d000340e5052580c45042000a10a88000000307109840e0b280713038408a01c0740741001ca400c00140c658070224a1660366003502c000100c04a03e9004241503507a0b80400c0c0235114400f2110502454a001da5a110003605005902080c0d1040441840d0301010043c007400342c030640c1c07804a100ca0148bd0195100202911074068040c50f801e015162050f4040700c0300b114256082c9000300e90240d02d4442804900c0300203442040d009000d108945801040420403895040c0c0c40741b50b0000c05000b442b4412107102c43c12105a54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 825058750 1250 825057500 825057503
    0x1101180317010806070c060c03060801050907090612050d051c0617100908180103021c0902090906070806010c0203030904060b0a121a010e031510030b07021f0c11010207 74
    0x8040d0415495101e11200c0710324003608000b0010500ca182415009000761045100145680d403158804001180240c0000c0080c15000c402480b01c4d1904485c00c507a00c40940c0b19500040d4200900060851420701000d504503420101a16001481560682d83ca038403c21000f108e0304518000c403802121584121000f0f02012170840c6648034160740304514144410440034a40c1e894070112100003500c0740100d4030400000040c00140d8070000300160020701844407202d01030071100712414050001a031110030807510803241c4c1d4041e0b80303540c03003210b6031002c0803180f0700c01050ba44c002240007980141c0081440700d20050840e464269403c0200d01030700c09650080207020800710b44c0100090700311014010100314041b041215081a5007100034904040328a207061241140c80750480d61818022500c0c29080c0701e01c00e18540c100242404441d07105071100b41d4040000b00c1c0860b8a092000c150120003601210b01612000120404040240600c040d48024020341d860000079000e800e00151000070b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 825060000 1250 825058750 825058757
    0xb04080714100e01110a020904050a021008040b0a2018090a0e120310030503070c061704030c02010f051c02070c09051014030c0619090f0807050111011803 68
    0x118500314503426100200c4446601c50034040c860ba22406a000861a040190910b4171040d06034040f0b02e41410284d0b680e0010b50003101d00030030003042c440005001401c0900c2a684c0d200701d2030b8000821242d00d201954000c0110a02030003048003031449030041003200907600121010400301c1e403250112036002c03552240f0620135141100c2207914201e0f48442e0b00501e15502408502c0c0141016922a45c6d0108040400c840101c0455011700340500082e02440d07201c0100e9540310f400342042c45c00c0d0a4a841040e0000d1034071020181f840224842d01405654541c8078030450540380da0040d50050104803603007003007150030720550b1420b4a0700390049201c2c03015030000595907071450070001002c0300c99800241c207050402041c8000420404e10b00b00468401d8407810000001685c000703810b010384039140640c04103000c51060008001c80c00400542a02d50300c03030440701c9665514044504a02d4480e8560581000c102040740f54010368031256251481d0300000703142014001c3e52001104203000a4001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 825061250 1250 825060000 825060013
    0x9070509041a0702030306061e070602041205010b0a050d03050c2803090b0c070b0f0f0a030506090a050105031209040f05180d1b030c030e04050f1b0f0d05060a0b0408 73
    0x2c441065000e4010007684040d620718a0204d000c82c4a610a01d01681041000c5c0c00d00d142882d1505400c0c0c0304160f038005020341d50349540d8001715208034001d4005581070f510700803d010161034441050b50440e031000c0e0212000c08140c1d18183c4041d040300c04e01b07106a0040484420070541012051243c0c00d038482880c9000915505006100d00441d0b080112104410819107125490000e180d40c01c843c0b0200003959280c1202400e12414010401f00074641b01003c1070f60b03101d054040c0c100ea40b003600103031004c0001b80d90790103c0c481915002e12440e6010340100b50235118141922008280c0803101400110715220a1003031681254800c8a0107920780f040c0818021500d42c05008003800780c80c0768a40140d000d41c3d100411400402c03040c2c0000c2c10700061055201c00c160040314a07000209c8001e01c10009480c040350050509031080f142c1400ea2090400d5071170050110b4070554030151100300780d20703080c06103010001c402880c0c0a040d1a0340060080c03800074021880d280280080e11604003d0480e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 825062500 1250 825061250 825061283
    0x2040e061803030c070b060a080321060402130e180a11030c090f0609070c050f0601060219030804060207050109080412030f0f0206071d060d1d240907050904 69
    0x41c9801072107000d190400c1040c0040120104162445d07a03410100ca05441d85610000611450442e807100d8218000071a40606e0108904207950f40d840245d41c1070041990f074002003104912819840701003040122005009101c0c0d0080d001d503100145200194000640341802498480080c0c0c04803410065400c00340260b06051044110201d4180e03081540750804650744494040d0041c03505024204030300004034540d1103661260035150704002039592402010318800d865080034040c00b40948191814a08800014201200c1090301941d03111229240c0d0f503a214007039403101c08107485947d00e0b41e00d0714001c01c8404000b80300501000441034410580e5180c043c040090500f249014812516510b020711034002c150194031260a191038410511007031214592204100c6160360010070114414001d5580365000300c0810101c4402005480c2c1804100355135089803006089500720011100203050f030740c00c1c0354030b50400703000c1c000e9485440e101d0700854118102118103544e050522840c00782c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 825063750 1250 825062500 825062521
    0x3206010f0b070f0f0203011506020c0a05060a09090905160803040e10030b0a0b0307031b0e0a2c030d02030c040314070e071d06030405150109020a021504030c02040e06 73
    0x2001070405265040c00c245440d110344084501d400800703002c03106091600821943e0a500401282d40440c0443c84030a8075800c00a550701360004a16004000241c00460b56103407880640310036103629070364075240909004d40d80c00901001241101d0070b20903100407100c908031071841d00001c1d0100200540d00c90789000111580311601038143c0208820f51182400428103c0d1209984104a0308020850310b201a020924000e800d0348094401c10f03152020410f2034a071700300d000040340c019111902e020f4640d484444e046581211541c0d0491a5a400d140c038504010f00d038010201400c130081d20f00f41004099584103a9004480c2c1d0200480002000d0040041c2c0912120312845a0f9000b8058282882c12040021401902c44000c0c810003412415020b044c100031030740d010714040e1440c0c2d124245850141d9a030300080d0160540b03000c00c90008900b404052082d20b01140d00d990040141c840c643d02040c07003407107000c2c20a5040002c0040d103207002d40c507240140030300d4a0010004004901d00a40c126 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 825065000 1250 825063750 825063779
    0x5012111030f0106032f0d0e010c120e060610051e040510020c130b03030714010b040e0d0503060405040c0b0a0c0c0807060507020910120507090c050a0c320601 70
    0x10107041c91b00e103204091941c0c42c40550416241111000316200c0500440d00701070050b035000f04403a60401319504500708064104100e042c250303480c0c100603a400c0c03003000402d950b245190004907901010024009150142071400d140c0c00d01e0034818500140c14613000904540700c401c5220300540000d04221600f451843c0c01410031051010b41010001600014008025103561601c425110006100c0ca59000e000711401c0543c00070440d041169141481c03406089644000c0d17215500c0d0164004910b8000b00710103200c005140d413101c0c03640e940c40381003100170040607000380c0d1424800900072070359078038a8000340400c5040b520703111000307031491030a003440d010540c0042003949c004c003400300440d9401805480c80240d04640c90651079481c1c00407002514015840010700800f10501c200030b022001c100740060301e850740d105022840c0290302c182d8051059540c00c1c0300160b2810346a41c0480d030702c418202c805486e85020a50105249440c00c0c000c030101c110061000d82120004204284103403108 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 825066250 1250 825065000 825065009
    0xf180613091110020f070303021e0705100f17010b1b01020a0e0f150720040504020609040f0e1606080a0b06190903080315040c0e090105012111030f01 66
    0x80c00003400c00c0d610512514244602c003030150300c4071849210443d000f8414031403c01131030300031075040951b42d0a00950300c8400480d9903c025101c00000c0c8100040410017605a86010300b201c070400c00c0c1d00d074040b00da5200c1c2038121000c01100554400c544132619199600030440c01c007820351118030010400c1c01c1c0400b9540510080e0307104004080450b80c00a0382c151521030115203844046d50300e240030601444800d041d8001480300000c140082110f003000503007001c0c003c241411309000f11603080c0301c200c41381501c010f548200184085845c40c9000d8000d042303046030240000c54681c0417400d24610b800800c0d07840c2c400408401c4c000348110303681300d001103602043d0600c0c14841e000036000458258440d0014401004000076141141039002d00341110042d5031085e450b594070715089c1e0250783d6a0f41201c0340144901d00b440c1980b580980f10b20840180480024111001ca910b401c0054480070480c00c144000d006240c5d29240301c041c81841140020b00391003003036a41e6860a50180050810140c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 825067500 1250 825066250 825066289
    0x210411030604021c150c03060611030a080606070f0210051804060e36010b040e0a02010801140f04050a0b0123040b0307091502010615030b030c0f0f1806 67
    0x400025964007544403400d400c1c0c44034041c3c1036880340d0070700c0000070b505d4480c0c403041981407202041c0e81940c107070320030000c4540325a2840700f40001b1200307098881c03103034008010009403000e020482c1850900c00034a8290721036100769081c072600e580490304050324440030501059003c1030040d148500310b03c3c020310a000841e010000b5a061a52507621840081d20405440364110217100d2643e000030680c07100564490311120662010401d00c60280c084859045d000358101002ca00d030140780060401c003030b958142c450103030766820030701d440195140381c01080354030504014609050303844900c0b4180c02000349000129581d0002d50000d800c6600680514418088200ca000301e03420b03910080da002d5038080103405680740c0f207001c030440b604030098002459040c00d4102d004406c5030150b02c642c1c1140c01d40c004881c40c43ca0744050540440d403200e000b10f0342542081609000340c1c50314100581c8625001416050b00d6034051010174201081d5040d419040c864407424411a864840c3c083c40c40300e2207a40d0b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 825068750 1250 825067500 825067513
    0x60601080417030a090f0c260601030f0c0f0b0c392b1b0e0c0304030c080c010c0201050c0c030403030806152a0c060d05090a080a09140a1409040821041103 68
    0x3001c0c540c0d14181444040e100e0cd0481e2804820040c040690800908091844a0010ba11000035400310b91002403031988604c43d40c1c00c0d0101203030407442e03a00300c010741d2001c2c4441d03081e60400c944801c0e201503071602c9a20120880c100c00c840017000000d40d031240c010040340711076010b1600d0094540448502d20200449064004001402c800d95a1540c444616041c3c5500c0351180c1c43c1c00c1c0d40200004038010000380020511143c80d440541c00450400044d6000b07100c151583d101c0004548560443d184468004020600110303000d01302c110b4003c40080e08500170041107510303030b8000350007181000880b00306480f407015003a11003c60381c0c03c00054a4003d0002e0745280d5002418a10507000c4c10f80b2010b07107443c00110045000e1188805841e04054407079030381c405150f030040031942e5134010403645012151061a840c24010040d20548a040d003001186500100810201d00d000070001c803601841007013001184960b40e602e105007200c02892581540c1420700d05900c1c20800c80001c1800780d8081d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 825070000 1250 825068750 825068819
    0x10020705150c0f1e030c090f04050c0409020f04080f0c01021b060702120c04090809040c1106040611040b040f030c0603140604050705071b08060601080417030a090f0c 73
    0x1003c460048641c5590a0750361240c00c5a0440d004019481e6070210711404820844a030383c0310402002c114074102c502410000d881010041198030964001c1c00224003807005104c078002680c020941c00c03102d1225242050f6175540350f5403901c0040026642c4035040a00701ea005542c0401612078002d422510b1a0500c010010205516008000e0040e20450046421110758001803102d40010b0b80301600a0200c14154107007150a235020303d0466018904d840e65040c0800d01c6010a451038121520181025860703a496a1010f06101c109003050320b0700c10031001619000350f100402c02445611301e00c1201d1b610b0360030a0050001e10382d001344141800c2c009210140d0302e00704c400c558440c00071600061203032035103c822a000e00030494010081d0901440e032041d0700005e42d0201c400c40b061441152800d60311100111071710f0380c0940340204034184641120052104040156030310401c0d50000051f001c3e04c03500c51110702e915414095031124651042405401f200498a40191900c03060100044924 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 825071250 1250 825070000 825070021
    0x91a070516081305100e0f06093304090e150c07023006090c060c194107060c0f0c09050c190f0e0907020f1002070515 52
    0x84140051006800041603095500e80e46101d81c0a01000b07800d400035040001e1029007440071011186c1e101d094002e801d01001c1c0b0700340080755408140603207225038464103010054104002541c0e07640c3e1030700440ca412440c1481303500c05040102000b920225003004451000c0c0e040c03402e00802d03800b1001051040000103103000040300d03c51a810343c0e20045606030000e2800141c0203403620302c1003c00565031a4410b00e01d001031100d00941c001c0e03040d61400b80c1403008010442c03007138041000301a0031904240320061350362461050786c43d0103512000c3c001100071540f24001e4a41242210038461080e003c0045c440c1100381500900802100400c0c5e001d003407020141501c0001d8100812901029001c4005c02450321406001000e9595080c4028140141e0902e01d580020a80d402900082410a2240c0e4443d904566603000325803212408508500c06100080000800701c00a51048408200b481c4a081080200b640f844c00b20040c2ca4528514101d41001480b6640b45210410142030010800c078 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 825072500 1250 825071250 825071287
    0x8100e070c030f020c04050a0618051005060d020904020307080103035007050c0127090209030c030607030e0d170a09031103040e07030501081506040b1201091a0705 72
    0x4140c140f03900403a0280b1030880c40c0100c080c145a800908100c28010301c0c990300c2d041001500c0048152030104001146181c0403a071044070021103d0355015010805030819400400c1040b40e50000540b03071280740302c04101640d00c1610b0740700c00a05520010070506500003426404d8000010003501442d211501c0c6028510361240240800d0004a9046103904400c84160018941d0700c0c407101d4403402c40e070400305c3d1580503400c8040c0c0032465105588205071107030722514401c0080e02e28080c00d40c0d81000c42c03640094101c1da46d502d41502c07407100a201940d800308007103032242d00c043c0e4001c00c440b101c000215081c0380265180c601888015820400d070300950318901603120101140000b00030000f402d003180c10715000314001169004c001000314900901d840c030b0340c1c07255031191024885666202d5200d540d070b16422504007003885c06400802c945240580181800d60b070001c10414150142c24003440c216001d03008220340904007000d11007402c1110b445000d5010300c050800e10305101c1700140134001d601 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 825073750 1250 825072500 825072503
    0x20100206150d0c080312130503071707060e01050a06050613090c090b04030302060f070e0d0308040c090608060402041b0206161419140f0912010908070308100e070c 72
    0x48001c01c44010649510360300c24030003a0050301d00c620b50b682d0342600b50303141d9202400210380b0408000002d50010461102c24210940c894021454a00c183d10323441d4030382860000891040c1e20800c1a40c01148942c0038210342820640000126410b00c4d000c0c20045400d9075102c1030048000380701305502c04594030940c500311607642001103420a02d00c0c000329841c0303110b0340110112000100300801807640c00208540300c2d9034181080e500540b01c940c401c2c0e4403041621074070365210106a010b100001c0c0300704040ca800c01c0c814240d03030445a844140e075106882140d0007070800380e4040c1c4104010f610381401080a140240e4001141c0b03034801c40f10007920f40e98028007642d60030b480d070300c0300704074103842414403280030f07000d075001c150701c41c18a09a100c01c400100a40e1500203010140c008101024030811205280f15080301a807411510b00e0030301160206011103c4501c1d584c80c0c40c03072030206190400400c07110380300f03030303a5010f00f440c22003803102d0f044007103402014000d0303910700c01c006803141c000e45000c1005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 825075000 1250 825073750 825073771
    0x40605010e1c05030c0610080106050a03021e03010605100f030b0d0c06050a050f070b07080906010e070c0804030501060e010f0f0b04090b0d120e040e0c060706020f041220100206 78
    0x11102c0381800c918500c5801d8174000c5612940080007000f40d810741011096401d104024881a44d84a0030481d115045010281d40140a00c48502e0032440503400d48105000180c0089842d0742c1e0707400000c2504050303075104008501c1182103640b400350b1501c00c0e22980c0808036000000d104140d00d8101502d00b041c01a05d051003000a80d6005c0907000b031040d42d1049200035605a5540c40d00d14000e10101c41c16500f03000803440fa00c0215046280c0072440c107050701d2840300450441e69801004a80440340e03188256040c220811011010640a000701c80107050842040c0115524240701a451500c46501504080855003000d001e0301c0b11000485d411102665004540c0c05041c100080c10106100c00c0100101440e0354051a05078000003860000c0a048070200003140d5010081c50729003400c02052580004100035a0380015007560141c00750260020740c45080c151a0042581148201c1a054a2842412034040300d100702c40e115406031203205886000d0050300341140070359070300405020310001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 825076250 1250 825075000 825075049
    0x3140d03050103080405061608162001020604200d0602190504210c081903030b010504030203070323120304060b060f1e0c0102040603021c060e160302120114040605010e 74
    0x248144a4640c3c0140781d0089100c030740c2c03a01e4016886901500c0b450040300c00c00d5030503c218070f40b1103511041e91802f1700182c000d0041540d480d921802591441151844104014010f0410f240c030b03140343c822402e030f03c200301c01a03071031041042030440c007040621281c0401c0720030002400340e29a0201d142e903142090040110540c0002c2c5040d4549185030380042c0007500c035400712804603500800c103000000f40240c40c108152000301004444600c00d501011307400d640309601c10000101c0c00c001c44c2d94210a10f8090022980040340c42505080b9a840c1d5a0542d450101c02e00040c08000d01c503607000e41710219401490000c90541d020000d00400f030ba03d20000b00e501d8040042c2004980454441c6040c0d003008641c1c2d1740e140c41001e4025000700788030156407903c0904110000445200302c0d0103070f1350600c4090800f5070341c00803c5460005943ca500b410540c0900510711310460b0001d03400e01a1080e02a1915004078000510040b540e060348524100640c4015000440d29018a0003000c046815401400b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 825077500 1250 825076250 825076267
    0x9030c0d0c3005150a0b1012090506162d0e01140313110d02010c1709040501060504061106010b270616140304081c170103140d0305010308040506 64
    0x110060640d00c642c11048006056003c0290100344114040402c503060320640d1540c80e800340031a1072091a00790040500c01146074440d00450b1031050510b4050008500c2c805681c0c1c1c4c50303051000a4603e00484c2c8010100782144581000100580010502e22202190034030450810400412400c50082c80008040c600199106043c900c0c20340440b0038455980b402c02d42f42d80059180307000020384010784103900940003031800314400101690169600340101000d52146044a032310426000d1130110104002c2103035031540d00609000308000c0d12007685442c1351050152451824207400b558a400000044c04005050800d85001980405100c081000c0650081d4540031800d40705640c0030501148003944294400d04112507940304041c005094251144110740c1ca00440c0690310079170300715401c04102c1207450810b02600600d540380c088410008040076400c000740a801c00e80f1a0001e181c0c059100020070001c5102031812440d040040c4d40c550b840d418024000d03409400c0c0305450000d45000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 825078750 1250 825077500 825077549
    0x44106030a0b0117040b0106020705061206011b0c09050a0513020a1a0c1c0306081b010c2409020f031612060b0a080c030d05030f1f120809030c0d0c 65
    0x1c5100300d04040c4c18aa0308042c148a00c40010074880d10005109000d00440c450410109071203c2e03c910b0a6000d403075032640801541d503600c2030700d00203220040d1a07840901080744a20908010316006c036000501d0704110701d0400907200000e01071041c03140c01c00d030b0400050b183ea4000c402242d0940e07913407505041e103c110480c91383c41400b81c80e0030765100340c50708228040a0742900001d03c02d0b1544080001e15541c20600303450348039240da0100c42ca4646600c0c80c600354002e07003090441c2c1d4030500040c407003a5a0401c120035a192202c5c00c0030008d0765150034980440c2450061a912424110010041198024100501c441e401d00401d802481001190780c200301c2250030003000307200010068416280c4034544140d454071a141032520a00c15814a54042e034000c000301e174000ca42403d42c200042d99160581402c0440540301c101280c0c040440001d80c400000303840c62440c6204a024503905c82c401403c0514055001004d5841103010f1502e800006142d100b0f4031040320304200207030540325600304510 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 825080000 1250 825078750 825078767
    0x703020f0406180608091c0201091e0213050636011e09060b0327120c010b0402040e19090203030a08011503111608044106030a0b01 58
    0x111500c09010501154a40d04070303614840c01a9040030440c0800c3e580c03901110400790030b941c071264503042400b4002030301c290011460307100c8a560002081c80030455070341c00c1c01c425200c040c80500285035000d0404500d00170a2400140004480034080c5043c540d00182401c403045040c2000902481c1704070122801000c00440c090320b2102e10700c00c2643e550002003400c2040c494080202c220030b0040852018140d120301c10550b110300c00c401e421542d81320078103802c01c1720203035040c1c819031102029540100000c120f13841600c40001c8000da10341c152a0b40c8582920412441c1da80705d940140400c1c00802e42048401c1d9000700280b8a122003044030904e480c00038003900e030300a9018000003c444410701e4100184904a94074401c0382c0d409141095000c8080301c001000303001241d601040300d94141000c2d0085400f403a8014000c5600c3e140e070340e211140055030748159044403e420b4248444d542c007900380c0d01c41034050580c41020b5a4940c0c0c2000200c1070310004260b140020390341e40241803607134400c0d03a12 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 825081250 1250 825080000 825080017
    0x1a0622080601030212070305060606030405011508010606110106080c0108190e010903171018060f0914060607150c17040b220203121e0a120b01081e070302 68
    0x108a5540394a4490340700d030400d01091380030740e800c03401c000355080d000a81c0104898004000c1c00d082d0b10381c54100030a1303620181c0305031010b41d2540320003c80200103039446001805408000954a4540389000c0c0071030b480d000428000d07034580401040317800d20124002018207001d01e0710988a5490400149000c4000c80004400c0c1c1c0c90114500b041c00815440016002e0282d21201c401d00702d001410414240d045075601803046c1010341c02c00c1510400c04012042c04000f410220301d60f86c460540b000c030f140742a030140104544030403000e4080880303e042c0c1074004e682a501c651801c47c041e256410810711000c000f1803403959840d220380340b03d80315400c0b0603089494603c400d407081c2014140300350142c0040e06c54204510051010b8680300d488195030b200c4081e4017038040e2000b454030f00b1031076006130003100c04c9000c8803100180d030490034044580100800705d06c0391a40c90500c042010380608071940028000d042c000ba00d401e10011615a00d1041ea007200402c6107048640e40748182100a4024100c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 825082500 1250 825081250 825081307
    0x2090a27030516290705160201050c0a0c0f0803090307170309181602030a0c020409110307080f0c010504030c21060e0102090f09060a031202030913050114041a06 71
    0x42400030000751079000485218412943e480c1d4012113004006480c0313041d20600c0106408000400907014860341503890300c1d0050500304e046c00134070443d4a051401029044a2405012000b40065603144240720090310a41004604000d0414080703940c5055900522080002c1910011038450041040303901142d0090001001c40141080c054400401600d520300d010319041c8425016034400070584240400d5903079094100d040755000d000090030005800c1d100501400c0ca100500e41b01000b403200244491002400340d1080c2c03100700ea0070101010311203030401c81c01f00010808500602441419559144000d40c4020f403c0080c60740500c031b050100402d03113410000440388441d010b5014080d1103106a54100103804010708010690800b1100b0540c4074885210a00108150320f40640c080481c6004981c80c1c44941400605403c04103551182c00a4a5030014440400d450701c2c0798a1115003554240442c1803204c1e403800036200550f0f122401840082040e440c60b0400c4902c43e9607000b003560 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 825083750 1250 825082500 825082537
    0x201141005012118060f0b010813020607050105090625210e0a03020d03060b071518060906051b280e04060e0403030518100b040e150402090a270305 65
    0xe00304ea84560914a040d00e00301c0c6002d0403400f800c0e64600807103480ca8016520846c0a5603281c0b042034120301200300c140c0e005007080c010100000d00c00d11549014001100040100c0d1034210000318038185d000549880c090481807554010b140c101d07110500c81540f5501802400c000d0000300e50042012003030b1860740d0f11940340d4407400d1640102d07031090025202e0754180721550301c8103200031591240180c020421111841382044030000b5038000b0300260184e01c02992216030b40e072265015038403c40c005481d000d039118140311742103422118040f040c950726819541040c44070800c0242c03d15801400c1c82e81803945c030104402e520b1080c20800c02e00e09008004201c902d4540100c10f0710414102d800718007183c50300b4080b409082644100c040c8240f01075000380240307485010800007910286441c00c2e0000e8a4030b0440c54001014890b0302d01c821408612541c25141c00e0040140400b8040c00c40b20106242516083c101c18104020000e0301040540143d64003046140c102c801e40300f11200340c1e4080803180d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 825085000 1250 825083750 825083771
    0x2010e041b03050106090e06060c21190f08070e150a0309050105090304030507091107140607020c01031802090c0702030604080d06140a180e030f0a02011410050121 72
    0x40310702a40c0c19039155001c000d16a2290801c0e2100c9116020b142807190040e40015840d141080083c010b409280303040d5100000c40c40c120041c5070850b08422448a01c000c6107030f0b4540c41801c9100998800c3c145403c0c9401500b85030081c10b80ca6002e0001020054415061103c0d5101d8003074113400a50410745c0aa51078080c400020300801084804517069420480403400760840002541c0035a60810040e0800c1442c00c20904000c3c00c0d00e109140ea010700601030900810b588a10354550340c000c0030094000fa00c1d080100a04110341200c0300303814117140845980b1554400003e10140c40d9040d64543c013241c90b488284038050040d000300950511600c0c003040100a17014000e044000d0829005120046e11410b90700c8582001820b2203800000e0382008016481d403249840e070120018050000c0c146c00f003129081e00350707400781203100840c500005008610b683c1c24855500c00010354040718180d41406401619000c440e88901410007299a40b101040e000c80e483d0429443e00c0500200540c5824 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 825086250 1250 825085000 825085031
    0x723030a020a020106050a1a03040c24080702011122031e200d060f0207020406091a01030515040b1f0305100b0711270406091106070803010501080402010e04 69
    0xb440d100040d4280f00e00080c0ba0700f040c0c00c00400f80c9217038540d1940c40c5044034840049541006006a82c00180e4000c00208c4428149010b0a40d00341e00c096041014005070303029201078006010300d4210b80c9070161281503012030406503400c26411030341c20b60500303c0601d0748898105c026007000d4815000c9003283e0440301c880c2c0c06440f80581c8a1901c681000c8003214920f10150300f03098250303401114051340b802c0050001d40c400d007010342c8060f60050074103079035402003421547d66030440d07100b89658a500d440d02c1550340c46060400c0c2c5003460148018504070090b50700780c1c80b400e8240781c000c03501d40b0014541a903844400c40f6800110b014400665084600000c0117420140d40141001c043c0660201e000c0e0f41440840d42c855400c1340562000c2c8002e40244290801d02c0c00200444411000f64407403254820201140514001c62011861803070504110154807076550400d40300d9541008207100241e1f20b142540c2c111402400c0030b030f4103941e4034001a10f00c81e06e440f1032030341d1261624806945503003a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 825087500 1250 825086250 825086257
    0x111010518061b03062422051c1e15020409140c2a0f030421050d050904060b03010801090b0c0a0c1b0b041712040308030723030a02 58
    0x8482101c2c0c882c1c4a000852103003050204803c680c0d624104002101420700e0140b003105d51514503983c90814041c0307118800c29402600f408a022141d4442c910454000000e50303c0140c58200e0b4690b2801d01841c0e080d40d8030390542d55005000c000c2c0340a0801050b030190481d002c8041c3c0041c0129175941d540319101c80258031600030b06400d646000d42c401d81807800400040c0c450000c0e0b140f031510300883c9020b0808081004e00c0046c41d645030f10500100710410910542030203292000c0119112400c083c40742041100706100c104009266100240108100040141c5589007504000ea600d466140200703020f03160355008006025400000002c50420541c04090070074007441c00c0a1094035074080341001482040c149030006001c080214010402d0f61b0700300050042c90408507600581d4542c8500320341e82040c3d02c003100ca0900e500090302603200a20808144002c0303500d0007850035096948808950001400c034004000002c0321000114204141c00c5603001c501103401c94807850100c0c08400a50b2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 825088750 1250 825087500 825087541
    0x303030501080106141e1215090d0c03180518010801050703060e0a0e0102090a030f030f0906050d020a0c05070b1809090703060b031504050a020405180c060901110105 73
    0x3440c0c0320000030301d0390040c03080d00c0641d4034100744108001c043c1401c028103115100141d5608491b81900707000c1701e50300c50044082c4800d1a00150141d03628550b0500031043c13008201c500300c2e4000401c41d07141541d111601514045d8035040003003031f40b40740090045881c41240c2101c7c1d00459180880300155108060842c12500040001e0000e980e0300e034000c5090316014032130000d8003041c80010800074421600001c824080d1007000504080342c201c0000c004940641c0141d80c0d0750f01020404041c541c1c003481e0040d0801150400804461070814001c4c0f843c800d015407104003660114151030b03030a06c1840700d0788100350444121810300c0d490b0010211301d41e001c130600e04001403030010740f0f00c0c0c5820050552807041c503d000207040c80c0c91460b1560b0303001e0300d40800b00030f902d8010302c3e50540e1802001c290580c01203002e180101000c1c6018410b1104403903015081e03882810384401000d0a040740040e4220820000340c1d0b100c0e0300c4098081c01a1014003240e5a072110550900c0704100c9040300e58145540d03c807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 825090000 1250 825088750 825088757
    0x20c072d060e01170c091c14160320060a11070f0537061d010c050606011112040e0a0f0506150306031219080f01081e030d0903090303 59
    0x200d6450701d064520128006800c0d0201e00d2007090240d226105a00e00c40e844a101007030340745000d01180c005180e07140202c2c0c0078103040c2440050300051140e40c0d07004203800c110010003061b1104840b00210310070059440f009080c09209400d40b01544c031700064000b07074003101402141e1248524000a018211303c40b940701c0d0940f29103100007550b00c81e076000c18412100081c14242140131a0b0708018100c018403031440010200c00f0049601104a581c9070304001d00c2c140e900c4544c1102401604450200b28990f100c0c1007006084607040441c401084c03031a04981d090030a0140c4c40c0e0913031422420945d00341c0002c5d070380340c40c04580012400c28001c50b2511402480fa010081d180b03210010364201c403010348038550440c1c510b040034494400000c00449d080740d0010215041d607400900e20700019400440301490312041281661103142d0484a2160041d5480c14031f501d4540c14480c1841c1d07030f4101c09030388582040c0040eaa009582130b007401180e840d030084c50820b0128456070304000c0c0400c5401c3c03001304c001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 825091250 1250 825090000 825090089
    0xb0d0e0610050d0b1005030a0b0a0c170114031507021605060301060e060a09050a06030c030b03120901120612350702040c02030c2a150a03020c07 64
    0xd08010708000701030360790040c10052010029200c09128103802490f00c80041328210340072485940c1004041c0c429449100000c1d10342c90040703031030f03019901c1000641062268119824900800e0151801c6c15540b5040303040c01181c1c40e6000003440d02e0450050501021400810f212600754041000030040c0504003150200d136588a080c4038113803009200b00000580c03034606114031f070300e4078000400300c1103401e207081d103601c0c1d44800006039101099400b0a010a640780c0207454029098010b801084800310043c011760149a03188000c039215400d8560304100c07421001000100c12030703210304060800316503285091922850440903048200b4491351076100b01d1a101150445803d4030754803107a403e415468201800c0303134244030241c0000302e945020340c0418003e4504900d801c0002c0410f80c0902341002803103181640b90112030000c01082036000741c80690401c030716401c5034022550b030503000e860016034841c0e9100c440c50070840990084507080c4801d00c0d0a51200c0100c0c400f009030311792140341002030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 825092500 1250 825091250 825091261
    0xe100501020c0f01030506031c090501031a0904060f0f0905060717250c1b090f0e28080a08060306100621060f06051315050f07020103060b0d0e06 64
    0x380c070100e10400329400f5460b0b1550504035442600a242c104402030116002c4010003040c031101c041c819844600010340c1c40e8401c0082d50b03418010f1030f00c8407412400c4031601050040119600c180c0c0100041c20f515106c2070040156052507210500803401c843c1c003001100035070328210341c58a4007030380c0d80b03400180e05014200c180440d07500b40078002d070500420047c046000112088040545040368410f114403003c682021886034802000c0001c0c540540c60106418122410100c8525250002000c0d25212882e0b05100b000566800c0050340611002c0001410b0140b0401c1c008802100900300d2101040304110103400c0100280610310840980398940c0e140111807005040f2403103039500055425410f241c4c92200c2c2aa40c0000202c148400300b5042d49540580030031a00303d610400004000281020300c40c000074069802400c81d101c1114aa840c00f9100100207004504065a1003c1e0000d0801c0c11a8000d41c0322030001c000812009480e6103584480070020550702445101c1c03401148001007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 825093750 1250 825092500 825092503
    0x1215030b0f0907030f06090b011217040609050103050603010b030d17010b1614010e0d0507021206010b040312180e010302090604091203180219031a010b1818010e10050102 75
    0x384940710ba2002010750b04d1464503036068090049105951340e03582d0340840302c0450b4113610a24043c0621207482e030081803842c50322244905c21000d503004203103014441400019408203045080360002d107008281034440078002801486900903441d410303c07800300f200c1e1b0100c0d0482200050f8588440708100160399032104100d09104100c9002440ca00c000c842c8400145181030922040b116100005100d000c241c1c000c03803401090404480c0820f40104a480461078018400e040240d0544040d01081d45440720034a1f1070b00039030100401c0750280080072400e1905c03030f40408034107454008402105075aa1215101244020b0006900440d00640003900f50f04103801000c0c00d4940c0402650308540d2072200c218010920007140d500f4410001c0c0454002d42e81d00840b914804501440d0b1902407450f614103082d4601c00c0c260000110941c0c8001048545c5190f010340d0f8044202c40c00c20000654004001015210082c002460450600c400403550303a0741008043c0c4280f038021480000c1e02d85900069 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 825095000 1250 825093750 825093781
    0x1902031c020f0307030f0839070c06020601050f040212070f051e09120c010e010e041103010834090504080c0102031303030c020102091c0809030d020c0a0b04051e011215030b 76
    0x610101018900340226508c00f084003101800c07210358014142807281c1c0c0d0704440c00d621540000016482480140304600d00684040e0079008100c604503c0e0442464200034550030090aa5045c000000d0480007058007030400c860600d0b8410b075145074143c503031240100b11600001c0b641402200a1901c10941d0f00d40003903c0d02d40c41d14140c4940c101d9401c03010044441e0796840b4440e980280d101c509036201407035002c0103940a044400007904c440c0801410651886801003000d440b10503005805c45110804a8180020b07602940d00103d60380c0c2d11810008540d03c40c103080d00140d507200208100d00300342c5251221150303c1c0311340d4040c00b40110303000e0b00324281d0149010069000300144c1ca010146400421004c2c0010300c50140c00341484200d60020b82440800e03107000c40560420415001c080c50b16801403030203030000020243c10b0900384004104417180c2944480c0364008880c0100344181e004451949200040c0c54041c030001c1e07448069018070040718481280c00b0202000483c100c2052425103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 825096250 1250 825095000 825095041
    0x60108010605121f03050a0b10030312020c031204050a0c150e0103180f0b04120804033608150a020403030c020d0606050d060e1902031c020f0307030f08 67
    0x142820031000f000284044900030f8010a0f9180180c25558076040340d00310f0800046000f200681070403d46400c01c12a4020f00400083c0e403802401400e100080d0024150008400d0503040180c50b103080d441c02c24694850181d4206010b580f0500f00810020700203000341e0390f24498002c181c0070320b5640c044400b0708600a030b909004990503100c0f17003000754807a40c000c0c94642c2c070382006140f4401807034480d41d40d6001000030039503590740001c0420042c031149000940c000816450700504900c3d181c0c03801080d01ca03050100440d4a08402c03200c2081c075007110781041b0350803000b901c0c4414041d036a207036282d51001b0101440609002810020350041c4952003590100c03a010784485003104010341c20480d6140309208101c4045035070365408100c07622007862180a85120342c0d0300050004071404600c1c07404503400e20211203100482c42400040e140800e081080541f08000201c40c4410a10141c0c1400c0c00d400c03030322074207100100d903d0040c9a0b111201c00003141e8a500ea0300784580795211403014041182c00d2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 825097500 1250 825096250 825096257
    0x10b0c10091e0510020c010c170403020c010c11100305090d03050c0d05040c0e0c09121f0c05090d0501060614030106170705160c050306060f030714010314040b07080601080106 77
    0x480e891524140c41e02c0003a040c810402c0d04c640903441d200000882e0040961100e0360703955000e00c0400107420942448001d102c50640ca1080d20b85540c0c0256504d02d10141e050401c45640b480c8001c001e0b14481040400b04003c1c29600d20000015000b0010304003100d44140602c10500c0c1e4000c0940640b0a0501410f2920384240c0780c40000c0847d8005480b0150007200c0c50036a2400010360051022016409800c41c18000c583e1501503d0420542c0002c0540c0e10215801000b000d007030304020800841500506800f0215401e4242c2206580f07a02840000d9504025000c040c5010402c3c10350010040c1d801e2911420540781030b11880000c0e60001b4022000840c3ca6510302d1a10002100d05040c3d21050a01d45540384c9285100c03a451400c03400c1030104c4054104050038000c61805000142d4070590a031100301d8090380c0c03000003e55821481c851800100034003100780304980d01caa080f1801311000c8174811040c80c00c3ca071074904019142103034004006450480410807940c401c05110b812245a980c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 825098750 1250 825097500 825097523
    0xc01090f06120e03041e0e0f06030607140f070308011805040206220f090e060c090f06180d0f1a060604050415051203090109050402040609230306010b0c1009 69
    0x2900803000303102d43e007580907403071105110005000030303c1e02c080422608484044651680b9060307032641c91030005030000d003d08054008110482d1000180369901030b40610700319045030300486050481d841221003074103481030001040c0040c503412620f00e50489104005820030384010f600d042e0100c81e0240c0d4020f40c010420005200200ea01d00f449401c0e000d5800b034032001041c2e8850034001001c4c1640d200f9200c09444101032180c032041032042540c415005510743e49400301c0500000c0302007240540040c49941e0200c2c0c000840c04000c5090f0240f5036029144440c0e9096a007044d00b440940340d0310440d4444900203202e801c20440d11002409490090f00c0c41c2e0505040030704101c042e120182d4401d036004003803c40003c10f03540d00070248081e460010003840d96003107640700042003107140b40c0116004500400082003220340c0070840c0e03000c5642e08181c020320182c03030406d807070741c07450951020b00c0d414801c0e1400070454044500c014400580e0520440d06003213820800c440949840c640c014110001e0303038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 825100000 1250 825098750 825098777
    0x911030318060304060f0513050c0114041203030612080c06011e14030102070611040518010e0412020f010f02040f121a1806040c05190b0409021309020a020c01090f06 73
    0x240c0559005031241c1d10200c0c0601c046c104035402c460341100c41c82d041d100069400814404148884d4031070704170a1810001c009042100090281301d24030426803540312014101781031620a40c0304001500300d6070a1200000024203181640340c1112070001c2103400f030307071000143d4600c0d1505131060000300e4609182c06a03241500d402e50094003060000e405540070404000001c00340e105034801810b241006a4650f4105414454482c0c0010914084841d00710f0062009607802003000b9401a8840341041b1403d1001900700e091084800100155600784511010207100580103007023078550084005c000c1654444d0100c41e510500701c00900310320080c0c6410390b42d040c901b10305035600c0350080b8403111004120b10101c500d805000c0764141d1f5481038540081c0131070b04c1c01c507251584112100c10f45002240c207240103003805d8802c0d4444c2c03c1c44180c1c0000d44000f0f4912000c01000100f200503011504c4142c2001d021391120780c020140c41c0000d101220114080111341d603003005554850f81c8050140a06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 825101250 1250 825100000 825100009
    0x5210c0d0f050c240106050405030a0b040204060317040303080703180201180512030408060615180312030405010e07081605150d021308100b10080402010c05030d0911030318 76
    0xa010240801c1000c00c5003412440040103116201082c1d010080c0801d0081300e001110b85106802480401030104410415503900003a00440a504001000280e88552000034018805644010540c804d0700018646810080003e030003100d01035141c80c501a507905008a00b21240c00c40c074100c1804040403140055445480c00103030410104a80e080c8154403100080e04944414a841c400350f40005401e2140b564248941a041035090b1218050000001c032016a40d024503050740ea0745c000c6d40810488507640401246205000000b0030b0303030350303401c190034944d0180c0020500e181c0503120711440045c10761400540650314212500000440a05100402070510300320350005400a00c144561030404521344001c1002c400000304403000d051a00f07241c2070805489202120b60b80e8500802e0f030907030341c94110820b0410304051030441d19550b00c0380b00580b802c40301c4400c05031061101040040d90042235034440c0f50f00c0b5001c2d642c01002442110101952032081c5c2a4030581d00c0304019106400b800c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 825102500 1250 825101250 825101267
    0x15070e0105042903010b0714030901051c060b070803220203031c020d0612120302031302010e01120c030e100504110111070312021b0405041a18070305210c0d 69
    0x41010100d420103443d810750b03600b181c100f0307040310241c000b0000b1460200210718942e0f6000c060440007540c2800714507000644180111494540300e1a0399228941c0494859030000c000380401100560700c81441e81002e40e401d0700300300ca031140380201040e9a990447c13603c1c0c0306e07000e41950080055140c44400c28165400c412801c030b90403101c980a110b5225405194003d40c80945043c0c58098a15401810300100b201e06010f1070300103040c810401d100618600510f084400c0d5021300740b0595080e400c40c0100c0712064425420407200e03250007024107034258980c000081003a0078400300d030300f009042d8403101d00311031054400034854000381c1d208440550103412501c6040d1000c1d429120a2030390380d2114030135001c4d03220f418001038110001e140d80c21311100c0c2250300991402c1d00e00b0411440c0694a940ca0300c0048540c0c0603406003280001240c10440106000c0c505240205440e460744d42c03450802d50b12480241c00d01d0131034091208103018060000d0035a08200540b40082001140c1000280c803a00d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 825103750 1250 825102500 825102539
    0xc06061403062d04050105250e010c03050d1b0210180b0705090a18050c0c0a11040f0c0c0605060316032414091c0203090f0609030d0215070e010504 65
    0x40c0e9602d0100301c165296a030310f201310b000340004552490032250b0301000856940c80d000406040052000301d070b035446030300b0000054080c00c0030300c190205420103480c0b034080c058940c2da0140c1080b8940640b0b2103900341002c141121602244d90b115060300c400010b0302e101d14a02200c8291144118020802008110703030080910f00300540740040d404081541450644c0201e03191515161400d10851030364443d655004480c81788460a00e103000000c40e03120010500064005840062407000c0383d91684d009502ca02c0100108005003002e4840140034241c05843c00c2c0c030201d2510002455904020450120140003074080d651024255680c000b000faa0440342c0b09080300500c0d9045980745142d20440854441030100031445113091034000745048400000c03000b106016031350310743c54a40c0001c280ca50703050b021500c4400c3c414100c00401c1182c0200c140c51545071050320801040d039a00070624400c02e4034103610005003541c1d500780030748118001100407800550304000401442c40c03880840000e52 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 825105000 1250 825103750 825103801
    0x204050d06021309110c0c030a030f050d06090c09062c01110123060f0409200d051915020c03031305010b0d14071d0a02070813060c0606140306 63
    0xc0303072103201404c22184030403901c800c0c00000040e009850b1108004071a84894101c004150f0940d0a40e001086141206840020b02c4030104903055006125000f00d005850010300c204002c40460000410440070b42c03203900013143c032242c0c1d42c400e6010803100e140100c030308411807081c0c01030b0000300445883d0544503100d40b06550b20101030b19565419810740756007880b41d000c84415400d00c0301c20492a5a8036040d4507106a1402c0f1124000403c49038501c00a5500b03000d11584100340a0040340c2092100c0c0300040040c0500e400341d5132100b0390803000e4020107002c0e000c18802c4c03070720301d207032850403441074074401c1100364414170024103080c04401544000070700c54400401c00304502c0300403820f01140d0705401c031880e220040d42107603182c104003d4000244002c01e070040070145c030400b04501e00c00000d80300f0b03e1465000201c28042c4040141107800e610f01601d001a0a40e6032200300820360000200100e6095003404400200d61040c140c1c202903262004010f803030355031a02c856076480e4101c51640c1c840b40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 825106250 1250 825105000 825105037
    0x507050105070309121a0604090b01210c08060a0b0a030807060c0c08070b091c0c08090d0b01171006030803180c0a0b1b0f03160309150e0906040204050d0602 69
    0x40361840980302e10700c00d100c3c03c3e106004240e041400c9540e06d50003004603000b1440d1042d0300010480b98a21281140d4403291804140c1f41c000c0810035481030b18400142102d13081075000554090700080c4075118400c028001c00c41411807904200c5504801d01c0041c0c8250800c1c05401c3c0030640340d600c4541c4d100c00314108440c0030001c65590072802d03000104107440d4540300004100740c4a0741809442503c4600020f803a240180d82400541040f2101c1c00141c02c0d503401003121030b219140c4044544110340c0041020041b581d40d4241071195180101c88020340f8001c0c400e138050303508444d0041d2400ea80d405001541503586070243c0500c95200a92034865038031070082c2030001350302c0c0c0703804240180120300c0c00617540b240140d112800c09034042e21010307001d501007908200c0160700842a110340c151004084075005405083c00c0380c0006560704610601c015060f000842c0d107400c08540c0004800680c3d480009540b5402080100d000d50701c00c45401c0032580c465100041ea03140c1c02001540d0030f60120242 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 825107500 1250 825106250 825106259
    0xa0303050a1e020d0305010b1c0f090503070b01140d110f030106050415061409010203120c09030610061805090105010e03120304141504030c0b0403110a0b0a06060306030507050105070309 82
    0x280350000041000350308070200c0340304c5660781030050502425803400074a161094040341d500300c020b14011110b0003295034401d08071401c1002c3d00304808094014040b251113420740e061200d10341d403080c4504092789607001c0708281c040c02d0040306800380642140e400d0040f14640411301c050300304501040c40d4955078036180482d0b650f69500c2103000da180d060703804110103403e150000e024420f003030240c0711140d01d0501c01c002c1aaa40001151844981440784600d40c0c0c0383c3d8035070a144da0056689140e418000c1070100403031188000840703402c444882d92500200d00315501004a449001d008a98012409100500c1030354064520b00c001c00310040c0440d001c10a089076a07488903001a03c0448007a00c201d021860030517410020301031170881010344160a802c2503a000360906103003140080c0440311b844001410316019a001161002000041d196440300610301180c1180c411034040b41068070308400401e078180f0074030806065951000041400c541010015111508002022070030469410000300e07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 825108750 1250 825107500 825107537
    0x30e130c020c04060f030503040515070b01090b1302090120030d05010e0a0c05030108210d0216060e0a0201020606040e030f0c0736050a0e1509010c0e0a0303050a 71
    0x149030209035806004280c8030201000141c0380c056201c520014a9180c0600c0032580c00310031a421284211158500c020014480118a02401d80301900c0034911100000702c076412034021744000d03c001c0368170340405089100d4003022400748003010384c00925100384102d005907110700440c024030720980403642423043c85032000054513801d030045c1030356030326034800d0241030001800340c4100c64085003072150540d8182074696a030b640d2008101c841120f51400100b0258554204881d0311080d40e04096646801d0001c031101040381043d000c4800e60b180410181403a00c0c0860300d00c2e0102d90513405080e8548a02b8104400b41c01c4029060b95140010401c5520718800400200341c100c51080c040c061061414407281d44150708540101daaa041044110000c0000d69900304440c0c07200c0440010b03681c0b03901c180b0400811924101648034071405c060b40129042e0300702c03060303c40d005500c0203000b07028035100122050035085292540004d003002040c0000b070b0091002e045034110034940000d518880000c0300c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 825110000 1250 825108750 825108761
    0x20711040515031b0310020f120c070b040b0f1602190503220315021303030f1e0c020a0503070302030a12030e0303071d090c090f0117270109020d030e13 67
    0x4c10031651203c1c1c1040707007400d20600310409202c02e411402c0204064124183e8030410511300826904ca000180e4440c501d503040e03540a42d00b00c1c0c41d0000d1443d01d0f15062951400540d1081c2240c034682cae00090a10741101048090f902142d405003500d0841443c90070401400c00104440d00c1c001481840c41c4c175440c80480c0020014107a02185001d865400c245d05802c002c40380f012011401040f00700c1c468403104036800200c4c7d80c545001c0d00e4100b16020101d5520003001d26011044140c441c03a42e8980d64000b6060607402e000b15051602c80380c1d1202059a0b60415100094040c0c00c00380e0008040341c0c0c1c2095141140311203090100e607100c030308460941103600c00c54011022481c44200c8901641103880030345a02d2070251115182c0b4144102c1c80c00440c040c0c2401b0340d100f4107c3c4070110040e80d01c1000f10540710b00b04421005074130b007840b001103035290402118940d000342c1c15080400750b00c07805006610700305030060400b13400703108a80c03400ca0b003003601022040c1e0040c400f1032444004400300d2054 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 825111250 1250 825110000 825110023
    0x101809030309061103011d090c100c170417070503070b07020a0e0f07030b0409020a091104090f0b03010b01020d0c0609080f13030611091f022103040b0a02071104051503 74
    0x100b03540398109014590030304400c10b18039200c403540300b0230040240b1000508000c1603400301c440340700e03c42908200311a801c808110040480c004102102d5a80f000e0001030016036038443c00c080d80030001400c07015540c0d403181c81050342c9580665010000da5001b00d000b0301285001401c55503580c0e4441c0303030000c0389050545003c0070a0400c1c404020328240c1c14807464078446011201400800c20340d80001d4407102c00b030300503a045156030389440c88114440000300e8008080040c02404050b9400150400420014035030901a500349143c4168640c80481c449000b8480d07600c410305051300d00d8a610006043e4004111102078042022840c10030a050103443e02e0310701c0c7c4081c511418114030f041400c2d80c00ca0340c1d82c8540c440701070028440c030740d9442d200074940c03180e452005400803001c02d1049280c104031005a600b501000e1301100e100344c4100c00118495030141c4071004140d110000c1005c200e2041204c094800c0c50f0420074800383e4901a00722541240b00500728150912020b40042e091941000d403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 825112500 1250 825111250 825111281
    0x60a0b042d0302100806030705030a0f020301110306010504030f020a0e1305010c09061b0c170708010e0318090601090b030a0207030e0f01050301060c0305130b040e10180903030906 79
    0x90304042003468500c10180281c54259000740c0703902d5a800300c2c400d5081821500184820800025900d032400c00c0460020000202222400c000302d040c03420710009080d105901035401c0c0240b05090030482c1044900507041a51031034903092a54031107a400580950080742d10542004c4001825030040440e14001d00641d410f91000392068544903084480d124280000d10521100401a03a034119100c84c035580c44181040103206c001e440e00b003440c01084d8010385d900c070705015001e140c103102c00151a0156030707429000308001141d2041c819030300e001d60403d140d0462030000443c5014280a120a40c0140d018100b00380c1058840302411701541089a810f6102580490180241a0321221181c41114140e50000621064400080051105029a109102c0d21407440401c05100344104c503c1c42d03a003034000b41080c80d05c0346180c0c0c1c00356104c0d1040311018174505c070204902c40b050340080001c0fa41c6802c4540448140a00c092028001034901502810361707400c02440401c400c0d008568941a8191 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 825113750 1250 825112500 825112529
    0x8070f03113403050409020f160812011a0301090e1e1b1c0807051c0e010e03031201030b07030e07090509061b030a0b04110c0f0d1403010b03060a0b04 66
    0x718081500140d22010580300340782e08505401003500300381210199049401c002d40d81e01146100340490b4410404d5010806050065007002c0c07180c0c1002510b00c00d2180586900d640c2d80e540201010b42101d514a03000105d01000100f11004a0768004404078408000b034800e10b901d40108201c6404070b5a01814550700028410340381c1500d0100c040c41212800c807002035000f203111030300070a18110100000c04440c00040c01c031080c040d08000669245919181140c111a103c40c070040021000303180040c0032808040010702185004401c0c1c540f180c0d03030035402d1806030b80380d41c880c103050000140c001414980d43d050250600b07041170007401e0107000c4803a00428a07092220300d05240c0340c1d0051103011040d05d060b606c5c0040454450071680c204103410f2000c01c040d604000000c1c0148007040c280040001c000030045d03014103011a40001c400c60800139030718a00e110000a42d5a01000480107a0110f4200300602c0290040c07006180c1041000c0d0901c055584c07205071412031940943c00441c442c05980 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 825115000 1250 825113750 825113797
    0x105040f060e1003230a110d02100c0507090902030303070309110a080a140c010c03031505060c06060112020f120c04120b09010b0303070c0b36030c030a0308070f0311 73
    0x180703000d031740314a820480c13508406141e003501501e48215040042460b00011006481555030004400c0884e4004014042c06408071343c01800c00350009201b122030b400740d0b010025400c4140d11030105410f1f0083c010303500d1542c03260800c900038202d1200c200c42c1d44420701084c2d0314a03150444010040e00c906402000d2002e81d904042c070202d01d410702552110b52002d40141d000c0c0c0d038000c1c1503005880c0d250070003141540125100240703841c1a40c020580051011440d010154000112a13002c0c00342a2582040411081c41000c207078070400328100d050f04010010a042202e41103007803035201100c1107907181001c0c2c07200c0d0342c04242c28000c3e8040eaa003900700700038070002d20003e00c40c2481041c001c900031442d0444070364440d0140b05091081d8448048003127140100c012107030103a4220408501c0d80c9800243c4001080da608010340c04000780603206031404001079007000218900c105416841e04003066842d80d10456840084000c1c00c4201030300c83d014031030050104000b8002503041f4105586480000703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 825116250 1250 825115000 825115013
    0x106030e01050f04020d12030e0d051207020601050105040b0d060305060c0a0f0e1806010c24060905040503090d080c01050f0708060915090702011806050106170f0105040f060e1003 79
    0x5850750082e11210f200780401695050b0720444100e5202c0283c02e03500f0800c000a500410001800c00d155014107a9070741080da52201c0200102c403150103030380b11141c03249201242e807104240201170105104000c103104ea141100301070007495104c00c030301242494480d1f5503a07080a00940c0c90003800200403d51504054200c404a0004020b51400b01007011064000031080403c0c070089080e804201004150340781d00c1080080e041c0d039040300100d04000c0075070503281000210050800d00782880c1203000705140000b4013505020320b4012004606100700c0c64204020034911107011106510104114803000c075081c042c0d40d209100508189500380340100d4081e1407104018101c1c0d100e16404000c0050b00d03000d0100c4d550300002c0941d0401c03116038403441d043c2d005114002030ba50982d20500c010004010952f00001e0684004e03581d501b80760031402c0c450200310756040e1210544868060014881c13401c044e801202d504800071008a41d055440c0b00010400c0000c2d030700301014940356001801403050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 825117500 1250 825116250 825116261
    0x30602040f0503190f03111917090f060f040f0806041a09060a0b19170c0109080613020609040e0a110307061d0a030605010602161e03030e040f050106030e01 69
    0x50540140100344820400f41e5144011411300411094070008901d082c10301c01c09160103172806e41000c490031184549403404210400d00303412641010748085410819800c20240d410707112003d011114013006907030030081c4640240c0c0010700d031076105100c000344070302041900e00d00821030100034040e9800d20b41010004d18545006101da0280480c0a02000001c0020150b9000b0044000001c00040c90320015022140382c82e030400c040e8100440c0414040e0203542c1003410020182c003241c0c1c10506013001074922401610400060390882400108280390001c404440070b480200000d240250f034000050441d0040f444087c2e850f40641485001c2101008201f4a000070440007000400d141100c01096402195060100740080e101002c2c56070729a03211072006980e200d0720600156840703038402984c0d24115400030034042d24400d40050003980c005030501d41c1903490601c41c1d18290031038600f61455181c144021ba002075035000100d4145510b40314480c0a025150f4001c6004950000003071b00707607074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 825118750 1250 825117500 825117509
    0x612230a230313090c11030a020f0601050d030f080a06090c0509132711030105090a0308011d010b0705031209011a04290a1a0a08010801020a020d0509041104030602040f 74
    0x34010000380300010143c641990480d08038840214918600d014112040750754519840190b11001c10b21218954002c2844016a00c1030421903216070b90320000c1254402288402401080e89903802c3e40d1190701c61b48256500c40718501001c1441c42e660280700c1e080300c0b20100920002080030907a00e08038500b54074000b0816502803000c2c03002241402084c1c59941424003203107400c0208d81080c0e0f080001d00c0100700d8849800030002c200614042e420941c03160f01c50300c000c60010b2110000425813005841e2440c0e400c102c00030100391541e08001d20010958041e00d400d44480c8000d1100b007c1c0902042d1149108558810001c1041040c03003000724614075000c5107440c862800d00d81004003100d07075508410201840d00c401054400b19401c013054a50016070000002d070707503103013101c5043e000c0c0c600e0007001e056000384d40d0310f45a6a60350382c0403801c130301941c1c1c0c1505c0188c11000d640d450303d5101d00041c180d00034000340002014800141071140540c00740d80112580741d0003060801c0180f016030100300081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 825120000 1250 825118750 825118753
    0x9050904020312091305010b07170f0412150207060f0c050f032706010b030603190b1501050409060801051b0301060215040501090b01060503090c0102010612230a23 72
    0x10305140d400070b0f880749180300d890120600c0201d40000c0542d50300100180003100d8000421840d41c440340c081c0e0322075010140640b1344041d40f00c005403a50980504a900300000d144485051904041007100c2c461001d003010f850751414085140d45081462004150760b500c9060005082e646081d45041074486014004080c0f14082c0030005184142c10205d0307038443d0071002d0000140201c0004280e10210200d0951428491180040388500e0f0540085000700c00031012541c590070602e01003c42c2254145000700205501008204010b440c001500c03a0305005044c09030810381c8070f241c008201e66030713513004c4d1040717070344520621035500c0359501001060004125520318641c1881c0002c0c0d52440241070b41107038000b20000180a115003913200303036869a44142c400b00296502c00b8028001d410a0700c84160034081ca2034012480d41c014811342040301c04129201d04441803070380799000c141c00d2030b44c42d050824010017800c101c0c1c1401446405503280c407a03940740e1108840200b603010013224500d6540702a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 825121250 1250 825120000 825120019
    0x506010530070e0d060e0106083304020a0608091e010b121b0d1b090c033605070509040b01030b07050414041e0c0905030d1b02010e120304030501020a0905 68
    0x568030f40c01c020804c03103504684042041c0040d200b50b9801028582d00c041180e000391aa034011f0f1400700c0000c01420844000f000700342504481d4644500c04055030000d40c04000d01c4030402480340141d080640c068241c0c03060b00c1150382080191a08034688060158459555801142c0c403840e0003c0d0200c640c440ca100102207040c20743d0142e21a00409400c0c1522a0b00303c50800d00c04c1002100789809030914240c0c0d0451070a648a00316030240261842c210b000c641010291041001c40000f0700308001d11902031041101c464207044078400c10b16040a803014003403d0004281601c0d0f80f230100d03004e103104a5454400d503145d4242400125400341c4104100141008200140003110034681540e0508403000603115120204144040308203460b0a981c0030300f0048400c40c0d07181c004c0d8284007150020360a484440800c2001100c95201810001034180386501078507025500c0364608100c4840054000e0881c14040e00396036185402c180d05c21200d0340e40010300c0381425a80001428028203040e26603010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 825122500 1250 825121250 825121277
    0xf0510080603060f1b0705030306010807020307020a180908041712040f05150d0e0c0f27100b07050c101b1b12060f05010602030a0909050601053007 65
    0xc5680c006050040f40842890104055000001c5080d80340050075410355906d44440c90010f0326508200c46507804524404005550a800803084a0001307500070110301d034060410452241e460b284803a0004d0f221760f034080d007800184c84e42000300040c05408140b5004010742081c141c2c0340000b180740110a46c0014071041001e254040124001e0f03c1003201c948591030402d2102d100240035010b118902036040c180080e40d00b40c4042a2600b0020050300e00700030041600042c08a41030308a0034813894084c26000500c000d02c10041c030290458170b0080440062981c1d041206a5900011400d44954114280000d843e10300350018803e449034900780039844c0c001140c41415550200ca402401c40d5061503200c0c1d50781401c010710a409812018460b215030b24550801000804446c0c5440420a240c0400850300340e00000c02d840703a5030500c6e03890800c114205110348000e0039019284c14103002003030251010f410502c40303072803036039010100260000b40c000003109102103001401c20000c1c01a41e0b2030090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 825123750 1250 825122500 825122503
    0xa0606180311041415130516030504080706060b130f030c030b0402010c05010c020f06011d041b0b04090b030d030903141602100305100e0601020d12150f0510080603 72
    0x10840360030000b1158850340300400f25002e490005000104800c0e640200031490050300c415145030807041c2c0c0e010b003601015900c5981201c07801d07103001c62941811100501c80310300ca80c00059000744500c2c901d9042c02e035255948002d42e0507540000410050115498224202c3c0524650081c07a01003804c107480351460b220b607248842c10f4003010b46003110010001d002d59014111100b08191f0010080010f0400742400945900403130b0030740020703406034000000302410111a400400044640080303096210b541d01d00402c0c020021100800300100040043c0b41c2003030201820040100396008182e958038a02050b040c900d6002e81c00051514142c0584c021a60065012880c040d901940c0c6589102004882d01c0c10034100c800294009600c0700d8800020b541a0800c2d4020000d43d41e16001803034503001c0b00d083c8042c08481d03481c0103a10040301c9030401c5128401014070780303800000014100140b240350014002e4190400f01c4100342c001c80400070341c28410310005150700f032840c20b07881c10304105000a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 825125000 1250 825123750 825123797
    0x3010f0611010b13091b3218060a0b040e04020a0501020f0c01050309010216051e060712020319090303091101090e0606030402180906040605070504030320011b080a0606 74
    0xc0c8030040d517034075220040005d4640d1a0910060001b030354409140d0307403017003003900080e148411141c100d444034280202c1c0900403501080e070300c0b006285182114500301c422041c0c030401402d065101c107100ca80026485c0e810790040000d412503414000040c0b030b2038010701041510561090341194070025115140d20408a81c03c0c2c011582480c096a5070707229514960301900800456101d529030008080080110015a10801d0300e0703100360b081981420126042c2d01c849d0115800300101d0480201010034003101e50045600c410000c0304003010259400300d1030221f518200b811004207a80300c0100d800d100c2408a40f01103405d00740791080320380741003001c0c4485c1c40783d000d0000d5019150100204085580e10f0704c81100c0e94035515a0040b0510740042040d995602c2901e00340d400030314140c04107840b6407103a0100da0540740c16403140540c1840c103005056815560010301e6907695607a44800c90900001038018581107100d41d0303018001d041c02e81d0503008949041d84110103000000001ca03850f40705603d00c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 825126250 1250 825125000 825125029
    0x60a080106020d080c0a111213090501050307081207051603290c0d09050f2a030706050a200303070507110904020d0f0f0c09021c0b0901120309030803010f0611010b 72
    0x80030741035001c003452032400c001c0030006580b88c20701080821190714074000140c11038801c40000e00460360b0700e60030f0640b02c440c070b8000c1e20130740d800c0100416030000a0100601000d40701d8021144541d0101c041c0c0400b284440c6c004076901c00440c1000b00c080035180c071011602080e071070300340000c50802001900051140d9122400340341d45504803103003844000c0c04090740311020325082d034544240d0f160702c00243e0101091001d40c0c505440c17583d0152801c000413120b0030344000707407500c5140030308a41003a1041002480b42e81049640000d0140d80b0304c0e01840554000d8207070752111038841030380386880c281014212000c0b500410207c410000035a843c0c1004511040c0c0181d01001c070301c0c8803810004801c40d0a03100103451200d000e500060704900503401494050f4400d58104d021503500c0b402e45098495040c0d0140d40203001600500900241c3c00b41125082e04c40d007010140c966495607000c1c03864009911039001c0c002102c00810050350002155010450480020001056240f00045045802402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 825127500 1250 825126250 825126257
    0x90405072c0607061505030706020c090f1f032916180e01061806030b0d060c020a02030a0c06090b0f180f040e0a0501060909150b040b060a080106020d080c0a 69
    0x4070255202c0000f25581c064100c0c409010048042c404100300304420320845020348219500010003a102141880162400800300301e4252908014417514a0300904540c0e095403c00500da5191441c01000d070009521030103011008441008481100c182508941d002004005040240400084000307004010340e50418980407000702c00c0781c0c0040502500044003043c4424000710700c990b04411004183c0072040000c6605c00e403076030350481c103903016040c50680280104040400040307080d003003030701c15607010710446480070802e400080c85c0165003c000c1e220307682e1080b420701207036500c0003100000d8101004c541e443c01483c00b00040a0388182d541d13045060380005620340c0d05a440104d80803220500070802d000500c00c2121030350b2580301d4032004907065032070707c0c2e000603103a00e19005030560301d41c0080241c024000c103801740e9030142107031070340350742d44140d41c0c044030724103a0380b8031000d030100500596962001d5810027901920b050580394039241031007a540304002a5409400032a03800c1801443e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 825128750 1250 825127500 825127577
    0x6181906021e010902121c0f0516050c060d0e1005060d03030509070510030c110601120b04081308060703051b07020415182a2a060c030209040507 64
    0xc2c0168014582d07103000a50280800030031104090000504428012000ca9220461200020f05441c5082014916404a0300502c20841124544a0b001001d24065420f503402c2d03541c06400034030281d208880d110001e95039569070455615003081814001042d0600802179030518500082085c19014401001c050320b400008400b01024054a0001c100240ca8188600318264014014000c00c3c8a64000140b2040c841580c50300c002600038100c9070704034a0700c0041303903d60315030340300a02e13000340181c0d8682802c2040c210f15444c2002038000034481100500481c1c20541c000509540d0040c200610014210310b030440180114000c03282820350440d4001744a00507050b184240c82c02503803040c1c204038004803d484104507260441ca41c1180d01d85000036000d03840741041c1040454404107a40018107801020940024020100b0301c40c10a8295030008900d031070703031400b0640740c0d80343c1c0c0031000940102c0ea004680c1850b014007a00603031607062251801c990315980e800b1041c40e40716000d468000700c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 825130000 1250 825128750 825128803
    0x280e12030a09050712110109031115130b0705190201142a010225080406030b010507050d0918051612021204050c0f09010b0a030b0406050618190602 65
    0x1d9000c009078a80c00403d032610f0075520440c07070345c15007880002940c040006280007a96503118030312003400e0b00d81c00440c13840c20101c201d050049920b94054402101704003081802110002d1102c03880081141c00032403a41d82b842441c0943c00d0024030b508503202011140403880060380c21800120303186800418080e1a0705d4261001644040704c00c0c0785070b5200c0c01c0708904031240f41064008082c1400588801c4490b00c0486030040103440140300007502418040c0030a203c400c1c07098000c030b0088081403501506112007510b41904200300001480c001c911904810010480340068100c044200d620003040145045c942c100200320304a0000400c2012400425240001e583d043d141c00e45c841c88000032451400d85070041d03945820f0300d8041e02c540000c0a44410074904400802c2c143d03420b0103580760600c1c2042c00e00354060a103019500e640142c540d1000b0406484680141030701c01d156a01580c015451803041c0703c40001821148100c002c00c141c82030090741d4000480308028452190005002800e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 825131250 1250 825130000 825130021
    0x112b0e04090317060109140f032d0714060a0e190806180f0d210e01020d060504020a0f0c062406080c0304030c02060d1103280e1203 58
    0x6005095403107890580c0010515500c06118902208040300601084d154032005448603e510300c194042d100e95038410003070310304205040700540c140181c00c8034012807403108201c071980802618000826000e6024580c45c25080001030020700c0c0d2020141c10380c0b020400410501d200b08110708050090307950788111161648a410881582c5041c102800c964990f0f070030a46a0005940c4a0310200e4217980610401901007240e040c6200320b034000b01507400e80d840050b40e0400301203000011000c1e803031103064884810750080e04403000d00c52000607594078007581c2860440d0a280c1005000342c2c1305000b40f0b10242d0b0001a003480303212060800014504051800d00c0c003800000003c69116004c01d031003034003a00050300900c810303205a40c03158411a41c0c0c80c88802002e000440e005000210303a01210750160070603400900c0030001d90032010502013003004066449900070303900040f00001d24000c1400c03085069107400f00d0600203d4062001ca82a8542c15079034009460b401c1c4600c1c00000040b4a01412 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 825132500 1250 825131250 825131267
    0x1e0103080a2105010b0c010b04051312020102071a09010c080f0a0e0721031d1e01050c151005180c2a010501060e0913110102101b112b 59
    0x401c01d42c24042507841d140d801c1e00035001010001000c0d030810310152414039060084c1c611400380b620fa0466024031945642d14171888000c0444255542000f401011610161002c8c9404200000c0c0c582c036400c1c544c42603400c41c2c4a05800c0d0042140383c100740038034202c0310b02002d41c00174040100030410042c00c00c02e2a0410300c040e44040c550810008080502500312085007002c24040d4451110031040c04203001c00807241d0b0384010fa0301c2030032483e0380503159100b65104804280185270407401c180e26022018a840800d9803081e00c83e144035805c000715000460b084402070242a10700f526000d0780d103480c003041c5a80140c1007600000c00443c1e145024116000040720119000d6859026a04c140b41c020b03000b03180a006070800249010000c0f08181080003400d03020324050581c00c01d82812580f1412411680040e5440c1180990200c0301c0170307481d01c0c0c02810b1404105600c01e0750205c00211000e080d22110824258094002e04010180310301b00c130300d00c28803004481000304035004d42041d00711801d60 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 825133750 1250 825132500 825132557
    0x6170c03040218090c1f0f090f12080f030405100605030102090a12110a23010f0f030504260d0e0c0a12030c0803192d321e0103080a 58
    0x9000102098034000c003843c06d503607081681350304028815100080312141d040f030080702500603980e0010803040002c1101c44016038003407455141001d1003c500d4002c01d61095605482c1584181840c01c114009031103510003d149c114000c42c504142d02000c900500381c10303c101d0000c1884075000f0401d100030310038001180100100f080000946031082c0c080c13010200c03c00701c1c000714401c05a1854a500a05070700f90588403640311007411070070503a0f044014103c000e000301c0d0004000c1010414115909910340e0585d092000c0040e180d10300901d13804101c071904a0380759030541c0199860340c220313207840c00d450060728030000f4100e0520910703003801d4580268104004260501c0002041060342240341000e0208003420014448403641e12518001c1240c1d8622048a41103203841c00c403940e104c0c1754840d100030543da070954280a141104003503018140034001e4589510a542000450b0590030360a41444034004c0d5010915411510b51107520b001d944c05500901035180354401c555003040d9031414940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 825135000 1250 825133750 825133759
    0x40c14030411061c06120c0b1b010f0b131a1e0d0f030e0d050c060a14030a0902090f041a04050a02030a2114090114120106170c03040218090c 62
    0x40e29500703010324519180c0380f4410410740c50f0001c04107900090841741003201f50403c0158040c2d07403c0070392000b002e83c0400180400c581750185050f10312542030050f1243e4401140707000840f404a80248000740c0b4070350101500c05407408141e0740d0030a4180c1113441c2154025581100c204128034000818681d10b88a0a584600800c84200401101780248004288269070f880c0d0300c441c41c00140034000c0e5003420300812781d0300107001e0f48880f400d010002e440d01101b40e280c860780480700800140026401910604441521000444254100141c545410440700503401100d4038250321914080340e40b0b41030248070b090102d00400d040c0b0004010a01c841c0f90001c0556a580e049840c25540420500e04020b154002000f101e440403402214070459001866030b0244c40d040c880001140d1751056680c10b40681c1d0414800110107507000d40c001d41c00b8024a451b0480140c4401c21a500d0f01c1500030000c0c00c0f044801c204000040e00c54070f00e5031444d040c52030150300080c0c40e03105005040c550f00c01c8407203401 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 825136250 1250 825135000 825135007
    0xb06130504051b12060411030304050405010f06090815040303231005100e0102060c03090a2a0b04080d03050604061502031b0607170403050d0e010b010806040c1403041106 75
    0x9200012500202c1c441c800f01d81c0c116031140301824040c003020f124681d0b800a13000740f40001d01240c000b40601090000040070b0302e25250300c440000701110001e07045000800e46160f42881759036041400100a065200018106000a00f10a0302c101d84000c000804040c0c80701c0d020107041526610b80c50015540c0a900b0f031551070880c460543d205058803500d4460700c00c00601a202500440041075403440690140210780d441e104e04801e140c1c009021014a8420160441e02048403102a402ca540f0b072422034020441d0005a18059003280e17800c41c00c58500d04100030041000005980c00e90f20b03040b07040216070356944100080040803c2d6020003031f001140501c07082000e502000901d000312000b134100020070602081c0c10b503214421560040481d40105010313810014041c81550322611034501540380c4401c1061100555a07200d0202403980c0d1292403021941da001204194042c05c2501c0c00c00c034007028a0402001907000780889142d90300000042010f014261649445d42d07000075208655 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 825137500 1250 825136250 825136253
    0x60602010e25050906030c060a02060403080601092d0f080c12150105150c0d0903050d08090309100302040506040b0306150705060c160b070216061b0b06130504 70
    0x1070510854865454050103000c076003500007101440685020440611200d50306101c1070090002c1c02409080d4903100d0403400d101965110130043c400b5400c03560203400380741001d280241108502500485c10300c902c03014240401ea19150401c8158070524a440980f45095040303020b20304200d030400c04101c1294400031070700042c0014008900c1801741c1d0100480d400b8a20219190204c50304d81032102503031100104903500e043d003050365101c1c0c86550312928100b04412114541220741c00103c000c40c0d451042002440028061080040240e06200708140b800b400b44945038071900a030103103d64403000341240c0d21840380e03050780c02800001d0b10305680d0b2070b1140c2c210b401941048403d240f040140503400c10b034024582090366841c60303001000781074503122000c6549003600079541c00b00c058900c8440a201207144125414000c00c00e940240041e04030401d480600c10092350007402c180704014a0380f10900d8400420794100c0354000e40c1441e130076110180042c0341d06074030508680744681020203000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 825138750 1250 825137500 825137503
    0x30305180607081506090f0f01090801060620030a142d0712020a0b0106050739090608030f2101032409030c06051503030a0c050c1507060b0303070204060602 69
    0x14040e001884d00401800c9200081204602c611108107800a220b4000003a40b0b042c610144a403501c014181340a500381c035403c10380d01f16a541c2d0701440004007052403006200320304a44100b1198000e2003e10714165640e08051702600041100122000d80094002c1050716607480048481081c5c1089802e0520080103200c02608001c00944900300342c14a807100e01400040c141200130b9004030358025607881e01c2c0c0d040e0b800390041d03031040e100071800b03401c0c1c102101c82e0001c00700c0f1714040510b40002d81c004004040001c41119030406200c09242000912400b81c00000b43e0b50710203140f00d009a900c00c8030580740c0c0e2914610544420315103003010004403c105480d40c8000d0586c1c14131a64009006180001509072138581001901198011079401c1c0440c107142c01140d4409030b07154441044141e007002003455944a541d14400042c241c0702c0c2c2108000c1c00b408804041501124140b8010518410042d114883d0740c4c00145400e94034425601a92418001c0c2d80e25a40c000380100030207680c07150042d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 825140000 1250 825138750 825138767
    0xd0f02010e0709060e01052d0307030807030507110f0d0204020c070e070f020d0509100c020312161e080f030a0605060f0c0607020619020f040e100501080906040f030305180607 77
    0x15011174020300c00800d407400c0055642540c1c424600e0040b02800110364011005145c0d19040d94150007a41004004243e150700104a2240b10307666a0b0380c1c0300e1050410718948031184805510500354042503c00c030750b444c41c81c120340c682e804440c0140c0d20342c0c501c07601911f0002d46911400300188020100300c440b0350420079100f007800058090f20031102d541e00c000c80e0300f4858040003a9008004580300340c1424130079405d0300d1205101030b040321203001402d01e920032560040420a07103043c419185085c00c02c121040c81c004a120600612101050503030398104080c01840c02c401c911510100000d0030034085a08403800800b0060300c0107035a88a200d02da0325190b40100e4141486100360b00100c0d103151303c000b4181d481802c140d003540d1113030002c2110350b070003a50015001404000302804040b40c034000c1020503038000c55191450b00c005529050000d4007010f00109450300c150070000030480400da43c4c00c86092411307071604c1d00140503580d01010b149000c090b203082000034422141040754498000200c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 825141250 1250 825140000 825140009
    0x90105190504051906022b11070c060c0f080309060403031a0d021e130204031202280c0b181207081f090203100c0815030d0f02010e070906 61
    0x18010000035501010140c69082c0c900401c41d5002071040024024a14201c00441e80315100141c60020a00d1f08407015185038620000c49200300c030b84e03001c00702c01c00d031180c9034101540c2502d40d81420b000c0c1e01c4201c00b000e49446180280050b1000550420400326217940c05c82c0ea200b007003036071241080c0f0f04090f5100b2040f2021400f281c5010722070320b41c0703042d500210190b0103801022040d040c00142d0900c925900e240058083c0c001c0d01090007007069482d00d402032010305e090200161141e155003009404d02e11150100e009540011305540c7c00d4501c0905401c000071226800d8404540b01441c0100d460a1243d0040643c40008541c0360340301da513000300e80d00040e00210781c55a000c5100741038946d1210840c1c80380c2381050740410920740351040031440c0c1c2a184100a04009040c11440d00424103212060001410301c580e00c06184001c2ca4100000c03a401c8950348a00c01113000c282c002181d40c1700c020319850020b004810f84c0f100b2800b8402d4020100054804c0c007610380302951040c0f0180035103000c0c0103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 825142500 1250 825141250 825141271
    0x209040501141c140111090406150c061e06090f06090e0312130507032316030201110c0a15021c09032a0b1206030a080414040212090105 60
    0x49140380041034006204004001003060f030889040c00c0c440d44000d070400c03611031a22414400340ca0100b841204111100100c2155407041014108812180d8070b030400480c040081414045082d8060307856454250b1004c00000e03200d0000c42d420120491955292030390905050300450140c01a07003200d0b010041c80d140901040c0d440d0900d1900303607000c10302c4200b22075006001c0c4c902180030406210ba0440c2d240750388094412041d4903003d0410520390415184111405241c40881d260219420060201d40c8054404240300c205a1601ea24041c030003c0e04100d0f41142c06c0c20310450900c54200107040003002801250740c1c4991150300142c0400307000000d40503080422420403445035030b01c0c1d070020007503981c901c01b03e003140c0d5400c034030385421804904419181c0000000900c01421864003410070119800d480340c581d44000741c40d0000081001d40690080c0080e24000b4a10409a5003550400b5141d00541c90307a51011400900075800e0b14103280000405200401d00194040c0e80103285414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 825143750 1250 825142500 825142511
    0x40e130201110718020d09080a1e03050105011209060e0a1103070b0304110907050408240702240a111602030606060309190f081902071a0405040e010e060901020904 72
    0x2120503846004610902c03200c54401ca6644c80d81e00d075164010100e1504040001889500d80c0d203070024941c1050040e00085516525072500310503c00030448208005440c0034051503048c100004d015048100d205082c1648600e078642c1044019000000b012010f80200c4da240d603000e01380030440c2c121410080f0f0290040c10404110314550700d0843c1e106035080001d02182400b100244031410100520900820030103000c0815401f8040c09014024501c80d80ca060000078240d244400318500074181800b594403254403013800d99076003080c201c090861102d0200b8a680e89401140181c210710f00c5519400400041488040040a9948140f2402541120b40950b07812003400018801550310502c0ba034000c85a103500e110103c403e0200f920312504401101c5159540c803000307533811451040c8602c040c4081c18550b81da5042040800524101892040510303c0c44c0a07000203200d940916400340c0c1c2c0310003462010450035041404102d8900c82140c9580c9030200e002ea00039000a000309206600f840c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 825145000 1250 825143750 825143777
    0x20c0d020d0f022802040905070b18010f0e0f22060905010905040f1e0f06020c010b060901170c1315030b10050a1d041104090b060403050a08030c040e130201 69
    0x80d030b0001000010314010b682114007002004400c04c61400b00e80c030a0b2210710290000b8030505c505d40c01018014091a203440843c0745441c0400180d0a90504103d01c0c20000081c456000042483d8a1401d98941c40c6298903100855100b405202c890b040e510019500c4101c600341d0751340880112660140c00b04800c1e40c0f900c0d201016602c0c151006814005494001c03404184007003003180b03904d6110384014011010a99490101008a00c0e0951b00541e020400701800f040070b0181c0c206070070044814900e4080c10100181800448030100c1e4100f40c2000000f1303940c4403140d070413184880c91041302007140a542d08504480d0581d10001040001d080003041d100c0e80c00c141c501c0d41c8143d1056101c0c0350400e884035004503601903004150344c8031480511114001900e9610809803507040740b0012540e1281009941d10036955840401409a00b040200b000030820105100c420030f984104040e6594443d8484940c032400790741c211681c2c00e504030003071100c0c45001004018545100b82c03030350041c11000c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 825146250 1250 825145000 825145003
    0x1110706020c1002010b030601090b0f0a060801120f0b040b100f030c0306020c190c06022407140c0d021c02061014030114090109060b1207060f03020c0d020d0f02 71
    0x124851400503a0251a019442c1d20304591114490200c134800007407102c1c1003100003490014207a020440e490341d0b60b10450002e003000b0010310340596055a2000d40d603440c0c00f0004120344414851a800350340c0f8000d9120800580b6500046e01035001001300400782018200540c00320820345202c4906200d4060018982c82500346010031a900101e0041d603403461615442d02950001d41c0d0b440940c09650951146900c6401609801034051241010140e04003c0c02130f191035840144081e0410b03c10303004480e04002c00d01000e902c038505217049400030860081c5e0140074003890308140900c2c050000506a15540060303404c10310800c6181c3e91440c44400002070762200b0040c1c9041e404011200c030140000499020b50596650f409800001d8424140d041f04d004444180c40c3c0403031a03512068034070305010542c0100600076804960501003030040c441310325603584852149a0600500f1412152214002d82c152849a50318105480d514290040c000303407650f0b1000d0208000c035070405000c0c03c100b0710 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 825147500 1250 825146250 825146263
    0x102030411040b18070309060603050a05070f050607020a05060d02040b0c0d021203060f12070b280509090115090b04080c01121518110a020715080f0705030a0902090c07020111 77
    0x41040e40c1c0d2104174003140038040c03047e0240e8034140c80d1000040020000c001900805000380041d11007542407561a81588550382d200c28806c030400c2c0b00310809613603000c1c0343e407040b920308a9000360f560101885103c0070b400b03154410000c14202140803000b001e00410b204501c41815802d442c1e81501d411054856404207a9809400414a0740050140d0500340c0184001d8001e4104440c00244d48000230340d45503024a070100400001302040d04518001602013440d16020f90420b1070800c241c40001c5002c0720700511880c4c501c0b50a040311994801d001d40c0600d0041c0c140100045d0355107480720b001b16680c600d4140c4460000741e40f641c80300c480711031702d1007081e040c0c5070620703469480c0714030f440a44c1d010801c0300c240c0490910780e40c0d41d00340002040d140c001c200307021941c1c01600c940d40c0b80550480082007240100f006000d100070801c5403203400320620650090403070400d0b580381d80b140c3ca41e82009102e0050001d40100001050150b0b4444400144c4403040c0301b6031ba214150740d8038001e0350740c82d0305 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 825148750 1250 825147500 825147529
    0x70501020d080a0b130f15050a0b03071206031709100c051b0f03010203010806090d09031e03030b03010507180503070326160305030414010507021f09050102030411040b 74
    0x102c0c002c01098540da00c6401141302440d005140303080801c5640b2001c0211020842d042011030ba80307181e503054010720004034400401c0300721a0010082d10306040e00100b40706c0240034404018100307001a45070601c0360311010146401c140b040d024408085160b86c860b41c000c40540d803180b41c084c2e030860781030b5111b00c00640030291320102400a100303070386010768420341c00c070360045503c0380c2d80c184c00081e141c0303092019600802c4504000c2c4400e085c5003290302e0909001d04c2c080c400f0000b542c001400824a090501c00c810f0003c0281036840c0302003414110014141809455070550a10b002c4c4102d81d60b0243c40800b0403045e0700b842c032000c00e81c1e4604150355070810b031100074158180550a4194002e80203d005411000b11034118600201c61012002c1c1d468a03850403004200d0201c00c0c4401e220300b22041c001c0c1200606d000b0000c501300f809000c0d687c0c0c02041c0c1c4400070158103c40c0b08480c0d0b5100c1e0064115075038007400a54480c1094604000d981900b44c1b0968002c5151480d00b141920344010140d8502c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 825150000 1250 825148750 825148757
    0x1506170709020c070302040f05040b01150507020108040212010c081005100804230f0f060a0204030f141f2a05040605032809060b040b15031b0a090305070501020d 71
    0x892412074007030041e40114095034628055010000050707203035401420f07280c00c00e00c00001040d1800d0329080e5444901a000108180016015100503581241c00c0310410380c0c0900307189945903907920009140b1403518045030b40c2d80d424209021062508005070501900c041d02030343d180c0f82d07124010312a1b00c07560b91440c039000813140004940821159203402142c140d020800c000e8a040317000c00145046c0a441d4031041c50703401080307103c3c8084800d0150316004540c00350b0a504d0302e4030b99121f4200d15a035001000c0c0c1403810f010302450b8003041c10000c0900042c1610029100100005a80d80051000d0541f20085400c1107203c40d210410031a1503a030781039425110070307090a051150449464100030315252540440d03a1000d010b051050210210b41d03d2202c0c004924603c04d031812a0655040da220903024504013265069581c0d10400c106444030a2121025182d80d07a944000c1a050f13074074000c203610541d00148040f500caa110144030140d80c080c80849281c1e41c2d1f10801240d8030980c040d01c00000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 825151250 1250 825150000 825150013
    0xb1e070909020f0906040803180f18060f09100302010e0a06140a210614030c010203030105041e090b100e0f0103080f070c0b09180c030403050a14030103150617 70
    0x361645a806040a0034140e4103d904005002000c5a0769600541208906070b0012070380c0c01001403802c1c80d000100d031041e00c520318408280d6000c11040d00950f02e001c000c2441c00300024105444e01c0d1f084240c0c1c150010f20401850400481c030b10620321050000781d0000b11109000c0c0c2990501210000480d00181d4510000030310103150b00c44d66070405014074037007001e8003201d19454075541c8241c00c0c1840c91501d000a0403490405004805000141005d0103038002d01581010343c1e8020090740e0448034103903400319220000500c032509070a420306081803400c1c5401c20800500110307402c03280c418060301003448012904c4408402c845e0008484007101030002000600014911f500038003428070030103944c41e0034102e2039a40c0850120458200c90225070b0082031120007440e0058401000d046080030001e0b80d418055503010341480000c00103001e1107400035107800c03440d2090120a00802051b100c49407a5612442c0011100036420720400c225410050040380f000c84d5000c11303144604060004164 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 825152500 1250 825151250 825151259
    0x807170405040f270c0b07030314180a0201030209150d0605121c140415110106150e0405040f050609010f060e0f041202070911120a0501050d080f0d02070b1e0709 71
    0x180e1810700d01308983c00380b4000740000b0149400c01c003910032507109880c00b00d007038a00b19071541902c102c000e14296602e43d11580124403202c0c0800c07080300c107940a190142e50303001c0c6280071900d07080700d007000c1560094000881d100c680031168090340c242c41c0c0413211910f8580d40d1005180d624454a0001c0781554540350040404a0040118a18000c50b010f081820b2994400111103a62618010080880c0e0402084c85116000303209010180c4004603922094581d80381000344004080d0001700d01660351034010030140f1000e0039207500281d81c00b1084680c0303444c1000240f4080d100c0000b12102241c1085004900400402003407403048824543c03c1502c1c1c0d55607194100314882d040e40b014154000e01c107012803020544d0045d001601c940d400c046507105012089002c03c00c6c40103145004440c60714006003d1b45c0c1d91080c400c81819001140d503510780c4000c542f80419486010b24590a0390320020310740381000441100c862081e0030050447c403040c0c080000240c0c0110b0300301c0325000000c1d00140c0902 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 825153750 1250 825152500 825152561
    0xc05041a0d1104062f0d110a06051608010b040605070f11040e0304171b061803070609050316052d060409020c0d020708190807170405040f 61
    0xc6895208000032808041c24034000302c1c1a40329421100000355605480c1608540c810b00303102c0012056081001041c142610755500c8050010215040284185120b103a040c001c01c0411085604000100001d0070f004091301000b080818022010030100800000d0701c21901003075900300c5515031100b03485c00301690796150a010000000b2a6520413981c041203903511107101d200c1c540c03035844004683e5182802400300b0521a000d45000c19584907802d803804101c0b401b4210b08021108bc1c0c0d030a030329142c2c61001c40c40c0400803004203e415115914000880f1607028a600003166002d1701540d00d0b00f440d40d220850552600d004079030b0000c40358034030002d00364229545550000220840202c100c105280091000d0f8080e82c008003c064020890113412501882807288240356800102080c07850700e00100d494000c003600707582d991005610b0700c00a0000300c00840311155440144030307103441d03d0303403108003c0d6411902403240030314030304440300603908103c2c4030b420044c140240140d030340d543d802e039902c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 825155000 1250 825153750 825153757
    0x1012060b190609080c0a031208040c08060708391e0304150e0625090506310308040e060f031f0b0a050619020f070602100c05041a 57
    0x9070010301805101480708030040401000d4030043d80c55260061800792110720345030a056105101310f0301c002d010000600c1000c1103c51170308007030501a19503503603410a00740d00415507008103e44d004540400000c15804819148101c1a20346260365507540c80d511400346d2000b448594001e502c29001040003202c0d180040c2c00807043c400c0707804d2080c4100c00c3d1120519041510103c40110043e03d650318400c08a0042c0c3c61003080c40d400a00300361519000340d00040003a85031400200c0c0c81c1444070070300c10703200e185040017404000d4149503a40b4144040c1c0c1040c1da82c80c015900316100700c1002d00c3e9a1050861074841141e40003c0303410704041c00c00c20000200d80d0040e1446a009070440d60b81007060b10b0511500c81c01e5215418080341c2a001000c1c9081a684900003207403040d00154007c1c08030b61381c0c42060b1a00c42c249140e407481100041c1a05915043ca2035a1071071a5125032000015181d90001d40c8074141401044284100a0040c10503103085c013a03030081003d41004603291156036400113001c2d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 825156250 1250 825155000 825155021
    0x20703050d0515040e0105040b0c19030203060d1403030f100501140919030b09070828020d141612030f1211070b01050306090a0804050d020a080d020102030f101206 72
    0x241c0081c0700d07007030005085641885c0c10700000e175110410071040c050640c102981c44504c41001c1d61030714420013007812444040309080000d01d90b0100c00b00c1c7e166203034001c00b44103260b8082d0a4242103828601029940d1f0411503280b8030f00034000002aa4000d0070003181c604680040e100d200813070803407118100b82ca40003036a241d0780084443c190700c91720441603500c9000550040703080c1142410300802e124100300c1582c20906035039200192000700805500d4601521520032440d40262607550710019115080c403000280514990b020384007074520020603600000890b0703151802641d0350382c1d401251180d04001d0054003060551202d940c2c0c036405070313075041e2908400b8040080c900c1c1d40701004010035004208181c814200341d034010b1000c1e00382080352541180c681c1005001341030a40d510590755100d540611030182800d81000000c640711160300300f020308090380a642035041c460000030700039082207440d400045654404100f50300101c21809094030a1031b800d0051141c00d980b264805009030000d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 825157500 1250 825156250 825156271
    0x81b0a1404020c1009050d1707080c120103320304050603090f070b0703080f1504021e0c0604033b151803070519030f08091e0310020703050d05 63
    0x42c082107020f084c840740d000c40c10720000005285141d820414030f440c80211180d010702091001c40303020460070503491607021019107490201c5595020b0b2081e5a4040c000d04928107254a40000c010091140e954150468440004c05107034440c0f07098040b1910080b1a200c080ca420800c0140418140f1000450303100c0d80c903408842c0310414030b22501d03140030b2655201514420020880e0780c105640328561030340094080341103d40da07062803241050420130410320300d846a94001084020314200c00704460211105d080d88548078202508040d444000c2104d0460000f01d5031582c20315440003000d585140d256418140302c00040540300e20780e030350043c1a046180d00000c40c501303070445108800d0050807002e0344001c503e0070014145050510340350058010a1140320148581d9034254501900c217403c60760001300110b00c01c035060424000500c03403509a5a0003078090207100040c402004600001030001f40c04507441303402d5081c8110106c0c064070a004000030320070001c888051031903810850300726031001d0303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 825158750 1250 825157500 825157507
    0x306230a060f0b2503080a0515031f0b040f0b030708030c150406140103080a170601050a030203060f0405130309080340090c020c0a050117070e0405070306081b0a140402 74
    0x495010300c131800301801c40014164034100900c04109000e2550880340188007800702c4460304c0c00003601c41c580c4d1144002e08190800300203801445580009001e180d020b88100903d046094106018001d908036060103442004000502510000300b00c4000e80004800750052100011084414010207401034030019280c0394001c1d07007120b85415150095104090071607440c80d00000142c44061002d40403407510f8000020410141d8100d421100c8400c09403030700590720340c0c1741c40c0055504020560303066042403400081261180d4540e012800290090300c0f042030841d40c0300d03011942da204034a500c81007802250581c9040c8203000a030f101d42ca400c070940146183e031180340e880e000c41509502c00d2042c0d070780b00e880f404070498041c019001c1d5800c003a40c60700500c4e820280081c140c080c6c0318900341d5500c2d0031500010101403203022448441030f4010428001c03070800040040151074180070344c1206000d1001c0c0f211100154416500d0344c0c1c20041c1249140d42c0c81d04049455460901c240550001d4080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 825160000 1250 825158750 825158797
    0xe0a0803011a043308071407140708010c17061c020315070f090b040503060f0903040909030e0a05010c1104021c02070623040302061b040306230a060f0b 67
    0x243c040b003100544c501c220446802c1301d0481d0440d1081c5840d000c24404400144001907900c02002c540e000c3c1c02404c01c6030703039441c0c5141c000c510301800c0301010158010542d000c22200c0c01908102d40110103981d400b00ba01c907201d840c1211618064861940c0a44640350054400100310701c00a01c1900040c15030328241d0210f580c1d128018812a070900c006842c0038007100c0c0440d0000e4200000e000104032791800c150405020071740d00c000141c071668071034004500041c18040100301715000b4010904061044280c82c0ca0082c0c981c1c1194101c107407180c40002000700d45540720781e20b090035080d04004590301c0c0307498800600c0f0080d030220042480d400035511071800080428001003240d18420300b000646c03415240001c440d00d484203107403a031250395007005102c0841d90009030550446c0808444032001d20910409443d248296030008110f10704194904040c40c00c3d10340b4024040d00309114208091b610120101c089901f40d0060f107181a41041003840300d1589080502202620800b42000c40c0700007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 825161250 1250 825160000 825160019
    0x30902010e090406150602010b1516050d020a0605250807140c06010e15030a240504080306090105040c05070807080918160504050a03112101090201030e0a0803011a04 73
    0x40f2015928141c4800e4040d80b15000c454903080249001d10003041802284c00010f220441c503200104c00742c0c00b0109000d5144440c0310003d81a160f030040465007400c0303500c900a501c1e089204026580d17903150a0018995600d00e9428a00406507000a10802104480305481071140a00080c0400c4000e152100050120348020701205001e40018001c640c94030016a602800040c01e0f8031801030b500c0c180f400141c50001d203a0718440d41c081f007500e172401600c00c9518180d48501c400242030508007418002070003004401540100026602081180e88070401d010a40e0306208440000410800520340843d0003a000707404124461079160b0320b02001840026490000f29521680f986049024405d5588040c6400b800d43c0c3c8080c01c1c5141414070780800034168210740c0c40051314095581002e01c03040e03030b51070300c40200702841c0b0310b012000300c0008640c45000702150310040b408280b401d99a003000c0e00000442c040701651080c0c14501d103a01b0044402002022803502d01d258607001d0001203581d1071f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 825162500 1250 825161250 825161269
    0x1180803041404050a020a0c021c050a03030906180b0c1303020301090c0f1703190201020721020f01050c031305030f0d0225121407020a0f09050c0316030902010e 71
    0x2001400300080400320410803040741d4005d800c42203011300c10010000116001204d00380c8250f011a001d41c0c044410154002030f0410b582e50007400341c002c5540000801d40c1650108207101d0003840c041041c40c0782ea540c0344c1072210b56040064021900c2c04002055a010311005040a6040d1040c13440241d41d290b021a0039100d148400710344034440d01c00203201c5a618203a40000628100500314000c1100145590b240d201740420f040e00d11a0030203440060034001d40445c0c08880c1d0000c1d040f080d2800409000c06100c40d0b40b0b400300014001c15050014080c070502603240140040004a031854465441458074144900800c40702c0d0701013405410004083c6d400070740904240603001680ea80b8030403c860406155120342b00445a039802c41300c1c0c000c2a10020344030044c019030b0401488400c004289294103005140d0000d40c8000c02c1d04000c1138a0400000010440d80400828443ca4650f901c1c2c10ba4540030803101121201040d000d1f460b01a0710a4200310b006078010f050803016841c0403404a520041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 825163750 1250 825162500 825162509
    0x1506100219050307111512040201030b0607060c030b181503070e0c04140402040602030d0f0f020c0c03060a02040e0c0a0909050a05040c0501030507020a060207020f09040f050705090103110118080304 87
    0x7080071451009001d03d9030350b05c0d2452201110b111102c5c080c5003441e805980079210300c0c1d200a1040d48001400c41e4006d500c4002c02c000c0091a01340c44021900d82800075100ea242c40800184c00d101c8241c415051049040550800340c10041c50299121821011102c0c0c154140580c984246500083c148140100250054851010541e92282007034410b800700340e10303103a01301d0143d841000104602507001c02952064070f0659404900c896400e80c8040281075140d0b42c100c0514400600403044c103500040d916480d035016020744440d6620450103004a01840c8212007402e281a000500f00e010703904c000b04a11b90050500514a03a210800401160811640c50307c0107690b81d41400f061099410761000240350904c1c040c0300902c0c5c1204001e444004251005007041d40200d000340444d0b4822108003100c00c000341083c40b1600e450f041a2016000e10001a1060300810314049018100752075428140d0707411a840c00000c001400045400015032440b0180359503003883e01082c02c107005d200420050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 825165000 1250 825163750 825163753
    0x909130302010e0610260d020a021c020d021212041215200f1c1d0d050406080916031103280f08040803040902030a0608150610021905 59
    0x110628640070782161003004011110743d0041007042040180100c0032000d64002da601c12001c03a07100700c0803082d040aa840281c3c000d0040f51504095540c1c0000c1c0035034a64000ca90100482011b45074a4044035154403000e0b412402d5a2540c0d0094140b00081211b055048021144050300d000900c1421350000e41040c000002c10780010402d200003056a40d88046c83d1941c10068a42011121007811083e200c03458030318580841c0d40342d825840f00d415920054a001c2000e09065041040800100000308201880c00c520812958030203000103400485030517541c80d03052406080440585001c500281801114030800340450001c0c0d00d10f0039120011b40c811201001701400c194101403c0401c030006180320100d04210340302030003004240310141070340c10200e0318a0b5a0b00c14240044107104541100e0a288000900041c1416041e40114801e40301d0000400c006078039448070b06e8440a400703403211101814100030461500c0c01c0c00c0f4880e40700241e401101c000102d085007964510700ba01310309440740d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 825166250 1250 825165000 825165031
    0x14070605040516090c020c0f2701050901060f08060904290403080a23070302040305120406020706030b0102060a0e1e0a05070801060e070c06111801110d0507080d020909 74
    0x7905620307801400500484c03041480400e440d028000d55400240144c14403924010172490426250401104000b070039401e0240600c0700c130070018000d200000e11800d405452007000000d000341c0310303803aa1440b0007880d945d41c0546450f40b0041004414000e00b082d903c13560341c0ca96403a904040c0b00ca21604a1048070766400e40c070b18203810083d00241c402081c0780e0459003840082075040130f18074028010510511031003110341e203400c0c800314024051034000070b0042c0b00301940c03030112224070300151048070301c0d590860b052541c880a040301518503981034113000d60b112030081000346859030001c0c803a250b805011610b00c1020070044900c0034541660354038564001042d08810b00005105480290560f50001c0c88107030304d070005608240d07100901200400606100100403c412608516002d03d0701c5c40b00c46455102c42c03000a0726104a07a0080f50114a4220750304440130804a0301d03c0f600180707912031900b0440c1d5510340c00203e600225084428540c20401c1803080c1d91032558240c0200e8801517004003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 825167500 1250 825166250 825166273
    0x280507090608060d151401080f120f0f1c020a031a1002060103031805040624020708030a1103040504180510020f03041101021608030c0c010e03070303140706050405 72
    0x1a140c203400c20740810a0040c100303d80e5444802a0100d541d40c0005010f0300d00c032883d10750900500c01852403081380c0320400300004845100054083c0c14010340015182e12540c2c00364515520311030100c403242a0901071002d41d41a04090002d4418242c804441600340e9115442c0c01c1c0803a403124000c42e0100b540c54804103941414904111541141594140d03512281000040e40e102d005200090810800010520b40b011100b00440c1c01804082c10034132810361200e00040b03c0040b1480410180484980c54440c42880026440c0c2190302d410040e5181203085101192481d09801995200f8070040200003140d0710b81d8410300c0042110344690004880031458079900345280308005001c0346005110040100d4544c104a907002948203c1340fa01070707401d190060b414104403e45140c1c803940c850b500025482804002080d03040354010544118074510700c01541c1603c08401480e416521046040c00042c5c016940107655401c0042000d0a00d0030030768071031068400c122022034090304040241c5a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 825168750 1250 825167500 825167507
    0xe01090b0102010614040b0105040906061205130308070e150309030301031a01180203060d14010e060703200a03022b050105010503071209240501030521040905280507 73
    0x402203401d10080c05050b00c1c1c0042c03036900f03020115009108a6891020407a141e005070700300c030018040d0a0081c40700a99424000d00707105608541c00d10428180b0000a92030001d20790601e541d107038036444d003881075141c20808a41480042445a1300103031034440d1420030005e160b02a51164160000655680d070440c6840e06007040036240310944c1c81100001809004121174601000808070000180c0f2680c503000011100380c034507030001d0201710340b03001d583c0d0412006400940f40d1400710b03411035a05072a81d1000b1401c036440a00c00a404001d00c060109054901c07100504d03000c2d45625002d03080941d02006001002d20100c1c0b980101c9958112414401d0041c0c010140105401d0a041e800c5182080c1d001d010200b0700d00c21165101d940d401003404000f15085840755801003d0a02c0103140301d40f00400c00100002c5c003065035644620444211034490103071500103640100e20090703090521780900f240290601900100300d04601c144045809281800302c00341d43d40e224000480e050502c9103015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 825170000 1250 825168750 825168761
    0x306090c080f0601060c030207030b0901020304200f06130e0f07020d03060605040b09040e10021209030304030e09041703160e0a0b041206151401080c071e1a010e0109 73
    0xd0707226030005003020b0280b040106075141180c1031401c180c0607180b1281307012820301ca06070700300500f41d6a0300001e0003a03c000550186100c0ca11941000251050201d092607046100c1240c25502200c0c40c0259205401d00300007400701e0706005842240542d8907000c81440000342110500e402503072040410a00e02d904110f44400500301d07040c00c00c0710b2401c1490003080c611440c000c1c011041000030b81810244c41b15806407400d03140c20350590303035802105400c1c1310280d032141030f840c1560000d1038089844080d010007220300030b40e8103441d02200c0400c0c02061010070f0000910a9803011220002e2004c006220001188200001e500c82c80c0d0300c030101d06c3c002e8030301d410410009004030303c18242031012082c6081250191800c4030100019100d07286822400703800c030303182005803801e01d1481c00603100b664800c014041000980350b4003107641c3d800d5040802c80c028020050714580c0001410042c0003800c1010314003160245140c8454030028902c01d94000c40d083c0e022000e91200ba03001000448094803c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 825171250 1250 825170000 825170009
    0xf03020613020307030b0601051908160810090e0a05030307030c1707091a090d08091219020609010e0d030c03020d0c0803240a060f030609141801150306090c 69
    0x7400c0d55109034001c01e81c0c442842c0801080710703c0d940c0104050380c0c06842a80c40b8851040e0f980b500358034502e90f0040154109481500c1c501e002d9a1400440d40c0c058182144030784180c0e002c140c0b482c0d2410703c05070081e0001f2a04070407240a0031300010f010600610085125035003d1308c0200c0d03a0b82d0034410082c800250b942c0200d0b40a03941200341300e07540b94070107002c00860340d40b1481034051a00340301c00b004a61003049030040d88082c42c201c4000c00c000c0c8040107007000c500105c440d03100314108007802544030700001c07a44980583c440ca00c9a4011b20300a0003034028004107241507401200c801000c59030800e408081a00400c144403c1c9a04043e8108100200c0400700e280052071140641d0300e0315054017003e0720081c803a9150750000c07001415142040844000e00074000142150766110280600c40307020303042d2000074107260010030328500902680302091024558480556560103203807080c2a058041704d110765403503403480d40c50340510588000256020b81d0740014540b1303a900c0c2080000c001c2e90312 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 825172500 1250 825171250 825171271
    0x2030c102a020a151206060f0c0201030e070f05040525031104090606031b0509130b041b0507030206150a030b0901091b06030e0c0604030b040317100504200901030c09120f030206 78
    0x500380f00d203230b900c21107500014500d400e040030391795524801680585900409a0701c039110300d2600049a40a004692007211001d030b0b006c2110340c40308081050700b0520140180c1502e070f5009201e821080c82a404000601c4510089504041d140d0b20250291503070355200d400060380350000c44400002d640d40103014030741070b410541d14218051000c140390700c40000400c02015500c51104a00d134595800c00c8841c180b0074030a0114016055201a02a40000d10f042c1c00520400000425a0018401043c007846000f01241da070a49547d03030325815104010070081032035481d00c41c0c10380051058003040c0c500d00c58000d600c03900b07a414504010220342d0403400100065100b4648252551a503404550540b030704800020032998941c14141e41d141643d01c00d00d1441c0c0910300420109450006082d07040e078000b11030500c421801c50f119120741500804a9604561080203004460342c001e40c0100c0b40b1040700d00701410305030f607111001d0800d001c50703000548842c0c0c2000101c0c800c15074103210344e03907110f5001c99 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 825173750 1250 825172500 825172511
    0x210219030806060c070306020f0a0f09060804240603140c011b020906010c14030306010305150306071805060d02030906010f0308030c0d0b06130302030c102a020a1512 73
    0x4400911a12002d0302c214000c02001500500a8205101c024040d6030010015980c03640c81030042c1d80307240c0c061240000000c054940e00014244160112402c981e05030380c0314000707601c480d1980034812040c1c003800c0304407164816011f514160680070b0640103500030b606900380c040d0100e0140307091140d02950303e81006441d41d0108000301620040c40c28158054501c0b2842c0d607a0080181c615031403c00003d015206008808544500008003c41c4102e0081e03805110076203481c0102e0786e0200905482075415004100028a01841340d1103071007030781580c01020052a50303a040811010b5001c200301041d40c5800008000040324100700300c0740108001c80658015620b50786031032205000190404000400010300306902c1d41c01500410306052000b4651982c0e101c00c20b5441c0304a91403444124000c3c000c0e044075540c40d1510100388120080e10f505c55004851744d840301d2401c20620b00c0c110540000d004d03041800540c40d0703464000c001e401d00322900a00c40e00c10000181908a50120740043c0f0b50508 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 825175000 1250 825173750 825173753
    0x1e270c121603060c02030909010e011e061b0c15050301030501050606070201021207020126090114070c02040b060403081306020f03070807031b050105150f03030a021513210219 77
    0x74a422640c03c000700040300e04510100f01c0c1107100d84440c40340e01442102c0041070b036880429900e4101c685210040c00343d2952104c1103501e2100520500000c5600c20301c2101c0f85074480c07040c008400d032141520b00780f13050702c401c19441061341c0524610001603001c0018010000244a06600004101d0705103083c554580e00007961159160b0703a0a08a54010072200116402030088865a03802605081c510340d00440c0244004a003c0b901c03110b0315820803c1900c0c90404401c0224098421551003024bd005144c007480080c12864003c40e13080b5030208400004594603201504100c0c0c00b440c0116241031070301d03000030f10b00360503140d001c0740e2a002000007100083d078440864419682c142003045d0101c0c03002c2d10b00b1a4441d0004d002920b1542001c1c100300b215854054007152950003124501000003401e014544c0d06d0041003240030240e4407203151170104480c83c556031a4031a0031002c60003102c80c00d07039894206d45180180401241c402085080242ea0b0301800240d40c4240003070154040114503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 825176250 1250 825175000 825175033
    0x7050307030c1502010e010c0f030b1e040b0109240f020606100e01030f0c020d170c0315150c0703021305091e16031b0b031e270c12 58
    0x54880c4141580000403c0300003e4002e40180384014168002000101c04910001c1c044000c0c1152010000b89018500a154540038008003507840a004121500303007481d9042c40000c10b0008942c5041c005940307030029401d05407508002c614441240c2c054210b400a20002d040044105080410b5400c024104071440e191040203c243c40354520f804c091216400340168014000392000086070760409039002da0b081d0b0000354030101c1620030340d103035815016240c5107842070140a0780d103206500002c0020403956107a030055590502c8000300036107041042c00a034602254032218011140303070051030040040d8035180d860905d420719104400d0000c0d18001ea01d850b104d004801078076081216a00c41200c4182081004400210543c945008030a40740c0c10400084800008001e00195a18802080080440d400d80740110344e40708600c81100d203002104407100300020603c0207180600c0c0302e41c104030204a5290700b04030681c28003401080e40040148040041041115029684115444ca04209a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 825177500 1250 825176250 825176273
    0x2503021209210a0308010902090f09071403010f03020a0e090c0d03051b0c0f04060509040303050c07320d0e09040c0e090618060403090e040f080d0902030705030703 72
    0x9606503501d503500d19660008a511482ca04401e920402ca10494407200388002580b01c01c443c040d4440380e8543c1e98420700c503002e030700c280c161407500043e94550400060401e000703540d4000c8003900700000b10400300440c41509400c00d034003102c041700c1c03810020030a6040142e810070203020000c0ca03801c0c091074002c48040d503610440c101303940102d800d2007140c420b043c80385007900e078040e0412042210000c0f10040f901c3e50341862102080c81040408484040da1500e44100130803208045c29601d550368403510309400401c40140204d891500c01c010141c0083c0c084002e0502460081e40c60b0011001c41084120050401100c503540540c469003007618801d03005800410f201804441040140c1c4d074920300160400b8040c0e00c1805d48001100600c9003951000c11200e218281c0390080c40b9648458807545991620300361005070109070078040500c403100c0e840d40d015600900844200390105400d5449840d164040310382c1400d050303900c5003104210301c0c0a21200004080c01c500801c041e50854450904445 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 825178750 1250 825177500 825177523
    0x10120510240c0506070e0411030f070f0203250b061e15191e0c0c0e18100605040f0213060c1b0b09040509060f010501030b01051e250302 60
    0x1d80c11641415454424000a203030668824155281e50814000203050000c401e0700c010322036405d1400e51848041b604040e03922552905180c000c6035240c0d68020342d40a84804143c0c41140400c01c02c00c50842000c45509504030302e0b0711a209000441820018034107503002d07080510030740b6004240d1170080b0900b482e11009039000c45000c403c204402c0c00781c582c6445032030000c99100180701e0104104c1d90b002900c0b040d5115038204c1d2074404021212045808105020004000d0528108103114550741a2840e99202c844070140203d4203000c00c580e00d00d0b20704040841480140c54900500603820b2600413140c00d075412035010b40c1030515000201c401900140078100c2000000c000e203034103200058013401e010594404035490340d240c03914258281c643c00608000e004d1800c0130049005a6000215039204070600c441c2c8502c0769003060011000341040c81c80c81d0381003100038408115940170050b4001c150004824000b9960900b8018602c00f11000700306082c020840c6c440242c0109802060307228101c0f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 825179856 1106 825178750 825178799
    0x60906060e0108160f090302030f06010503010c050405010c06050a0b090c03060405071d010c05010e160f0b0c0a110a170d091707030303150510120510 66
    0x1030790140e8100840d0300c0d0351180318494500c00c2c0941d003004e2005e072800b10800360307036138000914007140c500d0100c685402c030000410045c03800b440b5030418076132541000303810140b40c1000a45690b107000301c003800705a03c40c0d0005901e01c181d0740c402d49110500920610080c01c010f5545030841c0c00031141c080c02185000041444a03018944000038a454514500c40c2c0c407003182c00458200101e0801201c40e0340d240c01d401e05042c641881180305c1036445002030301c000c615002c03445000804a80c01080409402c01c0b1020001001081c40c04280da00544c4540f1190500d1011030080b4031151700400d0262602501000c41c0040895000382c40c0045503200c050180c2c81d41350074605406650b01031b00195006000c1040000c0c00f0381c008031103460096003180304065541020401c03132109440c8840025017100a603060319602d91042c0d81d005000c08103003402240c14460902d6840003a50000881b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 825000000 825179856 := by
  have h0 := BRFrame.cov_init 825000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 825000000 ≤ n) (h2 : n < 825179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
