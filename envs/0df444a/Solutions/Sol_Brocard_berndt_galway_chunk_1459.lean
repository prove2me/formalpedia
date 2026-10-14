-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1459
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:05:24.265005+00:00
-- url     : https://prove2.me/submissions/24757e20-c619-43f1-a8ef-da51148afcef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 262230215 ≤ n < 262410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 262231465 1250 262230215 262230251
    0x100e07052d1b0106080c2727010603080702062a01060611060f0f22030206101401120f0b0d060e070f08030403081e0c060702061315090204 61
    0x20302078080c402039a075038100354a00a4840480c1126071240d01d0100104459000410741d1407012801300c80200d10010460401c81044081e440d0001400c03032640c04200c107800740418450040540c080d1804c200f03070b50403803805080e590b0500004114901c05c0c4403150060900e840a40030510360a183c40403008070724260074400314007084c0e55441503912040104080c80c0c10540c8841100340010103004d4900d0007031a41e02103004042e0854080000c4e10b4002000d5444400c107082500011000243c6c1e60051820001d42d1040143c482800c44a0f000d6400910038501d10f000042102040c4c4401c84000c041000700310003068030714080d0b032070345480b091000580c4d40c41201c92642c051041c0c1d030000303010002000c2c0c149402c110707812040041c81443d000380a418000000e031000c40354401c80440e6100912030703a8280c6031031240f900e0b0302e040318007083c840c2c004e480100b08107100da80302d40d084444503505d2000382e0b21000115840078065071300202c40c1ca41c030804607405c010300f5a4005000802c20390a107103140c400d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 262232715 1250 262231465 262231537
    0x40608010516080114061b0106120f021507030f08152806030905031602011701030501090b0f130b25081906051c030e0307090b010206100e0705 63
    0x4480b1528041241a035000620360340940105c0700e00206051510740400c03440e10400b0381c040712014482c00c050840803404d40100000d002c8110340744446034000d15044164a01000c030481c13103005800700260340c0e4030044003510900780d050307034840344030744401b01090f940c01402600450b43e140c510002041030381c66180c6040a00700d48110349800380300c140c041414641140c2d4103d08205330400d6a01c402140c7c0c000141c1d80c1c6140c01200300b050382d0416100507a40303007802c0504186640350590000052220644c1308000c1d6074083d00142c10a40d030ba594100c1c1c89041c5c200c0715000100d805082d10404150a0791601c2c3c2e00503409040d0900e100090903015500b1020012540c000984100800c04400080c0c01c40403418500400c050000905103000100c0c000750083d444090303880010381590906100307540354400311030049d05603901942c413500e4550113002c03002151030143c07181d00d0100e00703894256142681210f141d10350741380a0f40c440c0c1001310b4040d80a07448038600c071401c50598894400807400c00b43c403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 262233965 1250 262232715 262232731
    0xb03060a0305030c0309180106020705090c1911010b03060609011205031b0c010908031204150b18100506070f12050706020307020703120f02100b01090b030c0301031b0812090406080105 81
    0x6c0c8070440b000801a0113143c030b88125082000c503030010403031a9000503080c030903034000f00d516a240c2e68480340c0504084c000c1c40110703260349088a1048140341e400c140084d4501e81c10341c00a102d818160000c4c0369490f01c081c1e5005400c201d510f00104a40c0000c1c0540c035000a216600380c80c0340c41501c004400d00e0b10111102c8030030a80020b1060039403981c2048003100240043c01c042e6043c255441040d2010a000800181c111000c01c2e00d26001c0d4035117580051600b0f80020818003000000141285490b40111042030301640c091001084030700e04034040d0388016500c81c240301412006a0303034481038044d2624800043c0502448084000740c1d090010310f00c0303181d00b9030003420081d03e5428422010400102d44005000c4440c4106802e180c4c04103001080034215200400c3c1c02d0388032001203480d44441e500c522003580d804000c1c01a41300704080110704072070007840c0460741110700204201c0c190702d20b0300c200072041d4031540c00000c0301c08500020704084c000003800000d0040e92607111a0a50b003003124510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 262235215 1250 262233965 262233967
    0xd24060f030209150c2e0b0d0b040c0303030506010309020609060f071406040b070f080a0e0f030703081807061e120f09150c090314160e071106060a0b03060a0305030c03 74
    0x6a003103400c005d041070a060350700700605443d030092428800006e1103026900700907151403462440b0748903241c0b004550303503210080d21114a440d0400703491581448c042180041d04241c042041c641c401e01542c01d0480c2c000b09207034074040540302000001c0d4000394404501d40302c1031103508081487c02d400e044500700070801074800c628007803a19660a1300020400d109100c055216a8200b0b03500814860b80454041000a4402078410720740d46011805041180030384000149141019031040f030a90003954008403400140690706c0e0100d803500001d0207154001035080301d049c2d18042140900103108800c1e82001070101c006c4042180c00d0300d5500110300f001d0307a29041054204008005001c0c0407000e0140100841000500004e100303c1c010f00c4090010341c120310400fa0201418016800c84c1c2d02d10a0b504d211560341c0d40751a0075043e8044440e4030200d8507014445007280b601184a03486000005d01c207081e05828610510600d400251040b5040744c07a0f03410100000f24104001c10520007000c3c011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 262236465 1250 262235215 262235227
    0x109080a020c01090308030a0e0c130903030b1c030807051303060c0f0c1214091c0506070206090c06071103060a023a020a0516080d24060f03020915 65
    0x41c0c9044800304102d4100600c1200402c0820485401c0c0c0b80c0203003142c8030103d00d007000c080f981440d0024040341e072680a034001010701642c01c4203030310800401d4825201449008051010460301a01e40101c40020110401210740003d2040142952084107410068140b640c0070034100000c501c941c01c11190951384403000d0a0042d08005000c4030002d040c600700030940500e549055a004208a941041c004143c04c200801c5842000b03450318660060580140c901c1d2102c441040e034a50044140d0f25409007501040b0b80394808510280b007081000b0050400903049000c0c0300042d4804403040e030b540ca20750000c0501e42c0e80c083c0312080c092280040c000d0b85038201030210241c0c10740c88083d0340206608220000d802000c8036412a40c00d80813408005844900f60941a074091040203c1c07264400f800b0703140d010821140d60042d040e9140c1c000410040f241110154105245004001d00a8040890004c22890340b240c0c0781401c40e003090380740c050300b803529540c040b548221002002e007064020200311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 262237715 1250 262236465 262236467
    0x30a020f0d05030d060906290c280b01080f0601032003010c03061703130909031b08120a06051f031d06041401020f030a090606150c03030e1f0e010e0109080a 69
    0x80c803010b23142102403124440100340d41048a040d0032800c01c0184940403c400000030414003960030b0f0780107240c003082480c0d9142e407080c402d0464152412582440d07620000300f403402c0c00194400c90032083c20000c1c0016425500c1c0c03070039816002d88482d0682d2503246009600743c0c40078010810b40045a80b00800c0d0b8506101c0300111a441c80c414440306648180032008041c82ca84190f14215150741c417001640103c6420200d640410461803403c6c1050080501020044550010500b11450440e072034226141e0b1180d81d01514201d00c1196480442c071034080c040d048418141161680c818140025141c40080380240c1c56044a08071074a21f82144040009105c1994203150105600c60021403810310010360a118600001d0300c09056542e60300440020002e1940c051070180000c0d441650038180d03003000044c0442c203107080c1100001d0a01d80060600381002030344003404c19001203400801c941d04034900300240b40501e0300307400b95903c0d080c20040e14031080c0300f1040803c1c0a803a05076503503885010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 262238965 1250 262237715 262237721
    0xc0306020903100227031906020c0109050706050403062003060913050f0c031621050109080f0901120e06010603020d1404080c0609060106051602060d0614130902030a020f0d05030d0609 81
    0x301c46c01b9401030184401200300c0d901c150030145601910060300e4000f205031440c0142168100180380d803040d6035000c0f80e0190000040c10071207102d28824089644440510001d038056456505000882400400c445103040e8105541c070010b0700d405007a442207103464251400170303a00c421002d143c2007860054010304007400803020420700b8154046581d490031909076895203101d0703401441c1c00e000386480001c104013908041031058000c800315843e0410800032211b660311807600c05002c201e4031040740c1014403284c000c509003020703281c0260915030b10f070510071307800703540180080d0701074a5070b5050079040f603941c000000e03001c1e5018040302c81d201c1c0d0074144028503010b400740031a501588044010082160300c0421140804200b0651702030040b01440881c100c0e02030380e040d100466007402c0c401b00d81482d036001400443c40003110a410400b000380c00101c112221000044d405070800034146c005401c0201c6010200c2a01500c4030b111071300d164480b181160826800c400119880c1d0f00100041c1c4100c0c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 262240215 1250 262238965 262239037
    0x3180b10091d0304210501020309060f01050103090b0a0c050702030a080901020105060924040608060a1a04090f140c0604030b0f07080114011d040c0302070b0f01030c03060209031002 80
    0x101e0380c140040440e4625070782c1c0200c0c4940c5541003d0468445003285c1421104c0c59182e80c000004c0d902c0341000c0e00b146880c2c0100310f50f00f54980c982100001101d603c00d0062100c01c1d500200b1181080e00d80d22020009066a981c00300180b0408002140050324200300010b8040c0c0241c052030781341d4182c18002429602d010b01101c0c0b05032540010302201c081089901942c940441940c200c00381c1400000c0b4014000c0d230b030322010160042c01c040101304000754200c5201c8078480003003010f00c1010241000125041014050a01c154074101000003070031f00000e0514407102d407412181d0a0f0001000540d02d9030083d0000c8540c80d04400030312190461010145130004150f0800c141e46604120491051f000d05000103170400001c03016844c03190905107444076459001400510501c03085140149c041d5014030000c903400200c40b800980c00c0400603000a041c1c9038040d1324090900c2c07441d01c500020b50090240f8940c10f0040b04010301800361180b000b007000722000e008d0070024260032061020001248 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 262241465 1250 262240215 262240241
    0x6152105060a02090a0b0901020c0607030e0a0920130e04030c150c080402040b0d0b010b0a090906050307170c03071d060109060f1107050a092c070603180b1009 70
    0x43c04800101e45c0c480010380c00b92008103154684071060400103c1c5001c660b50562038029900044e40004d00d41d201014a440400580d030100c10160381e181000d0403601d524a040309603110041403011144c801070300508951281e041e40c0d032000740d200d601c0700c6001c41c130a84003180407440188191041004803900c00c0113a04d039010003000102580706000d0461040103000900c640d07902d00d09004d0030754596200b504001c1d0002c18200e40f960311540440b26a60007203614a002c20f85280000454000ac0d00a82d002c0da54090040c1101d50b10b0010450a60214520b607c071460103000f0f41810f068030304001c0c50000344001409004803c2d181c45010001c4680900118100002440c0c10f00425400401c03d182c40c260601d4121010080d00c00c031182071030079682166a12a654440000b16240f094000c90180c8283c0c4000088244103908403240010800d1600070007034001e01c2d810400503019902c0a1032121024184041002c095620b141d8800c0b0100c42c0c0341500043c07010f050298503494417421050b030304a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 262242715 1250 262241465 262241467
    0xf0b0c06070503040201050c0d02010b010e06160f140f16050603070207060503060604030b011403010c020d1407081606060f08010911041808032410080406152105060a02 74
    0x240a018a4880500a001030148034000004c2021039102d502240d4603020100140c65031a02c034000000e01074020130303000e140001e030603800c031004914280040310803003c0640c1c00034401c3c01456a40c8400e0707550300c11041c2e55551111081c014510018004580c200440202800729142c8101c4600b0008a1603040903002d200103000f0017030710540004241c3c09484036800c0040d2280d43c0c02001404900c520f4200402410590f0000240107604801149502d4800c500a02c4508006401281d50710100300d5a40001415180c0c0c038040f1205070001085018090f2009a1600c1040154482e40a01d0740030120b500303d584044c10026179201580002c06481000000e00503a9416180c01c0780701e4009819040c401c65407080c07007800000c1508100030704298007411180c2c403490090140d05061507801c41510310889000798500d030f0341c80d0241c500d4840c2480394036015140d40351510f80e24014426419980d1400315907101c045030300f1511007201034980075040c209690b04105071420318244080540f90480d0030380 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 262243965 1250 262242715 262242727
    0xb0a09050601090b041511070b040b070b0c0f0d0b130c0809070f080d0e04091e050607050a08040312111c0f020c07030312140a0b01030e0a05030d151e0f0b 68
    0x1404440c450010f80c81f444c10000c0782c0300049240d81054a40d90203081540720010300001c06000ca2000707043d845008440c400c0746036032841001662403046a0071500c040c5410800c0e10304680c400c0d400103207a29409004041d408068031128811605500c040101080048040014070b1204114070005880740740120342c4168641000e10740c5d00c0a00d28080780a020b1020021301030bd446a13480003071450380040b1810340100d104c10614019120303500f000d888500075400080d2499004504030703640c1e11190b80c0c4442560390f854600b10f5001c4001d80500444503125821100c00201e00d03005012001e4001c6010148841c1c0210740e0000c848142c00d861207618011320007204401004904401120303010301f0800300b895010100b40e4010985032034200711241d006d0050002d1046561300118042d034081c6c80c04c1011005841c210b50351014800802099079004000241c40500c443c0c110b10030540c1035142168503e5224041c15071902000340c0c0c1040114194501007080d1034000003401c005041c0d50128502d001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 262245215 1250 262243965 262243979
    0x10e090105010f050c060f04120f020604150902030f0c010306120209130302070f080a030e19090b0d020405040506041209080304091517070312030b030a06050601030b0a09050601090b04 81
    0x804144580750500030b650081a040c03d020b4070031910150b0090741524901c1c0780410b0781c4000d41a041d03500b59800a0f241002541b49401800300c050199000e400802460761103568400c1c210300c4208000d00c80300d40718500d410058508022480c0b02034201c2014000445c5490001012104154840300404105082c2440561122040703690011110540031980c60b4040c1002c2c0d141007450b6010200c0615170310800214403070041a00204a4400e07070b1812401030300c94080107020300e012504000800f01c0d0310780800c4915250740c0700401801c80504030841c20815500010225001124155013580010040104201440d0301c0300e60b400c2a00e083c000c003103908060205030b030380c01280110701100d03544018048940c4d0016900d200101203182441d922041007440150310707910b941c802101c3c01000c5030f2500c02420b000e07011b01003040c240034000b000303407484503146d07038001d04005071a10b4145955180f94030300540b0707040a07160203891804404112418241c00052441032194800c0700c0c0540180700038030401c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 262246465 1250 262245215 262245229
    0x307060c06020c0715050307142505010f02040b04080c060708030a0203060103060b040801020c010b33070f0804030302121204030c0c0519050108060a03020d0201050a030e010501060306030b06010e 86
    0x34036044840141c8941e01196864603001d207031782001c540c0582c0c0100417079400340c0c4070000f18410111540c62203000210400041c166001e802200b84008800c500032450f441131103900c401d19240524004961600d52003808402c99020780c0001d59003080000d41400300040401220074803c1d01a180240303000c605469101c0103000c060490b0904580003c0454941d07131280d08030402402c0b500748640d56942c1d465621a00075480075071010101d5007045a42800c0e450141e48103000d403003850310042003010304900007028004200c0742d6802600c000f0b0102801103507902030001c2d9414410031100c4ea50b5411810080d10302044d21515031503210080004403810028414000d4004c1d0341820140c001102030b283c44500c4071041e40050790040301c80320014200908104000c0226039086c3c81d040c0e000e0f01c82100b4003103d46002c1c000a0f42217801041824010352040009103400707601817a00064a40d2940c3d18542512001e9201c44006600c1d02d60501c02d00c610307400c1c01a0060001d0130b00c1141007052401207824 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 262247715 1250 262246465 262246487
    0x10207080a08030601120e03030a0c110a150e030d06060f0801120f020d030c0b040605180303131b08031603120203060a0b0a022416081902030a0b030613030e030706 72
    0x104107034418506d00803422900043c1403000b207501034a40700c0c40e010403070100601c0c4240e000c00c002800d14918403414680407603001d03030041e0004044240c10b111400000054041c0043c03510b01c0d031100300704038804012240300d0709004c0c1840781d54040070b03040c028070000c004c40810b0700300703d01c840400c48060002444e03c4103240600d80c0d0503649546201c1c11401c0540324040d5201028000c00000400c0108200450740142d00c510049200f0300300d0303040c4010850b03660340000c68403800050718200048021507500b4810454600d10403007909000c6450710341860654100201c100c0400302da8900140406070000d81c22015100707a25011419072824200040e60000d180c130a401000200141a8180520a010309001c0c0840741e0341c000c24a90b0500703440c100c43e0000b200c0000c44024001c0c251050715203d00c0046028000d034092040e4030f4116011030394002e500181085980568401c21440d25440a100440c882c0f042c001443e104560181000b824140c0d24011191190f000030700d09001654001c00c070090 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 262248965 1250 262247715 262247717
    0x1302040608030d050c0c0d2604060603230619060f030311330c040902070503091302070803040b1012110406050a051c1a0108060a15031a040f0818010207080a08030601 73
    0xc04606411207079501005240100502e2402d200400c070910803c5c0d00020102c3c0d1245011637460b0410035950100a070b403420031888507400000100d81e10510064202141d101076003070001c0d1480c0c4d66a07181d582054590b004802042110083c4081042c05104001d082000d40100701a001b500b8840003070301000180d03000c2980c170103103c0855581d0b9880015100a0044100210366a031050304005540e9000411030a20881c00d442a0800110050090341e01c540e9100d0207a9046840701d60310100700c91001800d8090b40292210300181c000f5040c0300e80581c0901407402480c403081c0260600c803d440550304414094003100f0002c01c2140c4032a1a8040610b40e4464101141a010b02c2d040e000054440780180300d080504c0000f1480042c0803411501031310000204202580640305804c01c0003016100151140d440c10781d0709909460790700201e40d0301c54403694600600b0b4520b6980c1714040d41041a855041c01c080d0f601284e030359601000f454015080b02c500414082500d6503c0c204140701c0100158 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 262250215 1250 262248965 262248977
    0x52106130b060d0c1509140406060c020d14030a110d08040201020709020c0f1203060a0e04080307031a0307090c0908060108030301091d0706170f040b010b031302040608030d050c0c0d 80
    0x1409102001c0c11000141030a0051804412078003034004058801b14040d0b01200c00340c0100c2c0341440e180034498001120f0086e25103100e00700e582c4d0204210741003500802c7e01e8411150428914400041c4001d02c0d581e050760300c0d003100d990000c41419250041003c9400c0501185000784000f40c0c0c2c000403040c00310340546602607503400325100000c0c2010585008514035110344c1c0615036003000c0c1c2002a51140c481070b62b6034414a5500c0b203101c080e40c0000d580103441540c0030004100e82c4c0f07200b41c2241001e03490708031501e2191030800c40400d25011070b65110f45042d0351740b00e04003642c99a1110a0800814480c40181303a10f50501ca4026103e100c10b01c41c0c98202550344803040c16026240c108003198038402e0081c0c03000342c0d54900c4003401600100c002d4007500b80180340040c0000110414241c000d581140d80b61a09078202030380189154809002c049558800080890059035180240705c045c00c44c03800950f0301c8211141c60042610800b9011070303402e440600c1650b501c40c0c00060481044040c40c42d0803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 262251465 1250 262250215 262250239
    0xd06060f0e040e0114090607030506010203031b030a0b06070b0402120142080d0305070c05060619211b051c0201050d0e1f020301051005030a06052106130b06 69
    0x5401403040b441820b170300b42019801c001c418000800c0741841903e240c2c405010a90b14480120384a20046445580c0c41e00b0722050f441a03a1014000381da40718030a26400251180340c100081c06903008410201c640250701810401103003025144c4c01203505094000f030043d03511035951400d40310002c0c5400759590b4054140810103100a181040c100c2d0b407040343c1c2e50011501c42d105680c40707008800b1344001090420b804a1683c07031040c0488040260800301412882c4c0792407081048070b40c2e5a2240f030440d0003803208049060110342203c00e880202042c500024043c40d03283c520410401039441d2039032011000c4003000b1985401149034008924a4880c624051641c401a00c0368000c00802c0ca98803403801008040c680800114030b2101d040c0b8150160550203514081c10592000340181c1e500703d0701800715203000750300807009540c0080c4d10400100d5410b84546c00300f0340b002c03140c0d109070b03060703410501080b5a801c60a012464100241140e050103c4803152142104028094000f03070113000c0035805 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 262252715 1250 262251465 262251491
    0x203101e090804090507020d090501140304060c02160b040f1d220b0703090b0a05011401030b0102010207050d09051c05030708180d03020c0307140d02190312050d06060f0e04 76
    0x2103c0142019a60070003540c101078800a640d07024420030040801d00240d0082001c0d0300070450100400d02132041c00b440c6594681d40d901c080d020310403414056224501109051400081c095405010960181a00c42d441c2610f059003448060f403104440c1048020810450200b10b9031590340000c90750750100e54005a1140034800c4849a54040c2049550505014000d030307140d040841c01c1401003030074a055850715688a002c680707082c0701c0c24100107101c04a180c0154065000104c02075414000103090420f980c0310a4100000084054001200200f05010074a40804a82d03034001c00c44480301c01041950b52456941d100da090040c21111001c13600c00f00b1000703603130528001050b015100a000c480c1a02e40a581d0b19035100c42d2501c01d0140047c0802c00642d02c1c00407030300c0f14000030a15400010140c0901c00c0120550080324000c002c540c0010011030649820314800c0640c0ea074588d50f840d614452130130100c41c2280c100c00104510b03204004092940051140c808001c100e400041103064454 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 262253965 1250 262252715 262252717
    0x40306090c12052a090a0e150103060f0e07031e020f04020c060609090c01090311032109030c060a170c0c01060e06042307180f0306090203101e0908 65
    0x3004074038900460202500f0068085100f62076180c1e41c9010428200c249042c10201c001181c2c107054001c0800000a5020529500314100c060311003030075500e444036402400c500d070003c03d800903a000c4d6210030360b90344003446500c6400501110303003001c2c1030300c40c1c119621410f0f0100046039054581003410350361415503840302c020402c000c4000f401190341e0310082c200a51210004c551075840740e10a20001100c41c0d00126044002c6203050351081130440c155520301d06649025030240f5090301c01c204a0301ca02408012455000741d105541050322450b00e10f0030185007135402030b0198052181800031060b410b401001c1d000500d21814026a216620005203003c103024202d4034081544c20104002030f09003000e45031038002c01e030546040c440440d200401815031401001002004607820b0001002c2c90310608402c480c04000c041101122030b07075141050140c1005420540740595070303a031080e04601c0c04004029016075040300901050a0040f102050180400d00d1044080e48802d000340c1080310041c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 262255215 1250 262253965 262253969
    0x6120a0b250804050c04060503030904110f0c0601030b0a020a1407030309061e060503060f01061101060e0f40110907080f01120b0c0a020a0b09030d0c1103040306090c 73
    0x40480c0c0c407a2220304034010505881902e05131240d0003442562440750405024000030f50780050300843c5041101414080100745034a10760180010074407400144945107801440d042d91084000e107025411030030040070050010300307500c41075032040022440c06038000f03058800c000101d11020b6110501400c059016006071080201600e00c0c0921025120401003160f151002c4e00d8482000815264001d040d5101c0c0709032075014250580e00010041d60344a82c68225032072140000200301c05903a00d4503140b051100341c0f041c4209034403040802c2803c20808415902e0444003803011901d80030024890904081c05009180d02c2c4012010307240c0910410054001c02d030340010300406010320b49610000c2c51844169040c92024901d00c000240e44c29640340002406a085030001a0075100c8000b01c1500b0750100700c040041d07015024440020410108940307205000c01c80c040c6994043e1003d4000407610350703100f000107101c12400102d0114030700000351407e43e9480000040c0b48441e504041100910741c1d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 262256465 1250 262255215 262255261
    0x9140a1a090f01060f0c0506011e090e0304090507050a09030209061503010906050a0e1e040c17060406060609031e0503270103060609060516030e0d0305090906120a0b 73
    0x25001d01106180d0300902c20b0403280030b50b0702d0121a001c684030071540003402c20406000c0d5400a001030140d9042c0b0030381208d00503410905210107546d2464044181c9a041c030684c4c0c015040824100200c0f080303406000e07801075480c0303000c52400300c1d41c3c040500ad030309144c0800390044001c20001001900d41640c0b01c6124608090300c543ca944c0e4410380c903c003520060107094010307100c6060005521001d00f001901030080201112440640c082d5035264580d40144156410442d1100004411101c1059504410094006402c0e07518043c01c04105075603142d402081000384543e0100049403240d281546229584040440506404e0a125166014022a0740b0110002c14802c0d80340481100d04808c115200380ca041c0541ca43d1040306848807444c502c542c41c04920b041106c80340d084100c00104e50454400d062038001c6110740c2010031840301c0d079840e088000c04d00010360800245005581c4540c4520304581100ca5003006001560702c403c03000700020070588075280820348440b4081c0817282c01d1100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 262257715 1250 262256465 262256479
    0x30209040609022b38010525030c0212060f061203040b0f0c010606080417192d030902120c010c0b1b0d021b010605060405060703020309040e03031009140a1a 69
    0x106205000c1e096a410851005c0d084ca01c07405101c103501420596080c01d04030031a020440c020030f222881c00d840000c0c07046003000001d101a40c0142e95500414030076103850f200502e858584041e07003810010001e840c2c14414403021010802d1039000004550944041040142d102e106a000e1a02d09000d021942d1101e5420b0070004608568081c45841c4100c0c001d00303510300e034100b800c42c0c4080c451090000d000040d1001c0b084020200e4011025802580203c85103840d01100100d0b40469400140c060200001e03142d4a03008158036181e0701c0c801c0c0604889001d0501040e0302000600000074154008103200901c60001c1c0e43e6000300780b480c551800c0b036102104c0d034590b4808015802540075880c2d0300040e541840340010924414440c042c242c40c0d0107004070b031806042c40208400b680049100701d00f14402000301103519140c5000b040d020003640c3c40259141c0c02d04034600001d8241c1038206a84151030009007409600c110140282c02c00384201d400220301449038203000103201c01c45015504980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 262258965 1250 262257715 262257761
    0xe0a08070306050405060a27030c0b072708030919030506070804030906020d120e07120f11010c080301090209010c051c0e0609130c020c030d030209040609022b 70
    0x2100f6040300e03200e43d11840903a0700550311040003108a81551b60070a90031a07000030a001e08071034250304411010302a045c40800050155607516080c4c1b0200d0b0103200083c0d00070f801c1104a50b00148004014100c00d0310302140c1800d2400080c9e803402183d80e01c030f11449101d00c5503010b0388214540b510103190030205844891034003410140002c4015102280020081980010003a10204540040000d079540307070080c0c00c54074100314020b0b25a110b40070b5002d025416000a0310b5100c0030611085a120300d465151b91500d9040503c41c0c28608070640b8103002605c0c00358000600702004481c15504000340068a900f07048004903074101110000500d01c0c406e200307080000c43c1900c00307018901c1c4e0056030340c0395404401c1000e2103c20300030070049503044040121b80812118840d000403001e600c8a204031000140b60000007450000d05913132071070203e640007a104286091900800c0060030700034005500c1c00c9048840ba0910700c3c4c0500c030042d00c8044181e422080480a500702800215100c105aa00c240b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 262260215 1250 262258965 262258973
    0x20f0d0603021804110405090c331c020c03070215130501020f0a080c011416020f011a0607020321091f080f0405030c030d060512010605100e0a080703 66
    0x8450000b070340b1420200f4800c00c800c080c070100540c421a4004042808080e00c3d0b014000a0600980904017034003480c0d4186c0c0b460348070b0007106007034070000c211661845440c0c00d10030501100c0319010b00420707140801144030000200840c50041607041c0400603654695003c046086004800000b9440000c0e15020001030100401500c1c010b0b242c0405644080c0c5d40b03030010780c0d40f00c5161100740c0750b640203606c02c5000b2548501c007270005020003034000f04400003811744d41600b44108a0f1540381501c45100503107445581000703400c07402c2e40c1d0807000300078454540d15883c0c0d039242c68001c035a1040000150050864509000140d00880c5580c1520080410620a4680c9400c10b0300707518000d00c035400b903100c82210a800b112003860f02c1c940303c665641c2c031500007869a1071002003094034a88420420f4900801c400c00040c9104002d651000443c44c2c144401c0140058080749060016810b003101807040e55502100001c01c403c20741814041d487c001c001040d8142030302da01200c1580240d00001040c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 262261465 1250 262260215 262260221
    0x20d0f0f061d1605030c010e0604121202060a05060303120c090d030e1201052214100b0a062c0a120b060a0b031e04020f0d03090501120207030e0d06020f0d 68
    0x51450252808400b402d10341181c09903c1d4400c551341a800000840040d50081c8032600408201908040c54540c1300c0c43c41102d20400c424080713495980c0c40c01c10100c59581480560b400ca600a2800d000b6801c2040010303687e80210400241103900c4400401d48902c29041203628100c0c1c013a08031503080940c1d043c040c2c103030050055458000c0c544803900d00710800062042510a02c032a0349244102c03040750703803c92000500c04100b01e0b480030f141504900b0713025041014240680c10300001140480d840020301c04640d006510201c1400307156122030311028200c0c0c00041c0d02e41d00c64510080f003a1410303000145240c2c110380c0310310111144401c0b05028040543c1030684140c1d415280c203008207030f0780c01c0240340d68801110010404000c04811248403c901c2e492641c10a000422151000c41060000382408651120441c04070320901000c20403560460310950002c40344000440c10b002c629200580328022074401d0703034400c05102d003940d0100078031581a50542030711645880c0d11a900c226002000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 262262715 1250 262261465 262261511
    0x12050609122802010608030d05090d050406020a020f0a0506070503040f061103040b130f14010201060501050307021504140a0c1404150902070f0516140d020d0f0f06 72
    0x160041c0500c0071504503038402203442200000806400905203100c00c40d64488040340381c40219500c5a000280c2c14000b00090038041355800c0d40021f031030900c0d400311440d12101e0000c00041c01400c2c8000c101260300480d45086c016010744e0381481c11848040055207051180d04030a034440c4001c1200c000348807000000d0000e07507010100400e51a0340301c0c002a90304039400c07030301d10032550300410044c0440c1100901600306400340310441c0b040241c0780c0301e55112180d0305400a40e0f41010804d0988215a42400f072000240000e0800f01c0c99030900c00c0c002516064520b200c0d9454010400101c0c0400200c049040c4d014040601070b5800b541e000e180502105082d48583d1076410304000e02c100d11850b1a124041002c04008507117500c032460211600044c2d0000039041e9130013450142c210010910510605104141d52148586164148140710300f81b200070381805401030090400c44401a12a024240e40e02a0855001192001140f40c040074600030b42c40000d0240b420b0948100243c0320300041960 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 262263965 1250 262262715 262262731
    0x207030909150302010f03110403080a030b090114270a2f180f0d0501060515040803070b06150a020a02100f0e04050a0b0406080c0f06070c03020f010306120506 70
    0xc510395440c0d00400079610520702001d1040c001190030001503005d281004855020703424045800350b0000a1820160416407060b100c10380700060070034640c1d6040c41180d80c0074104441882055040aa50101690000b21854020490041d00c00d10b08031114504861030955003488030003a180025204003c0c5c52103e03861001d081480c22485100c0d140400c01e00c2031071407801d244030b0412121102190b134001c003078054681c0202c148003120303125440d0011350308150782c0034200100d15640341000703020381601c2ca01d007503500070300d42484103004444001c42118103030341d00b03ca110046030311a800044c1c0c5074950181d4030b000b8800700203903c02800d0b03004664032030128000c07690084000140030042e100454130311103500008589280d6905c3d11f20303055000e2904501400780014610001c42d0200c1c0441e005a00720168907403100680690780d00d80201c83c4c10704034102784d4a0f0b0307082c0309107652210451145800002e00c59500640c0d400c07640c1c1d120ba0300c00c1c4000c0040c160ba0300791165032414010348948095075030320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 262265215 1250 262263965 262263977
    0x2040e010506270d05030304060606020d0207050619031415030601060e010f08180a05010b041a06160602070602030703050403020c040b011710080105071d01080f0601031a040f020703 80
    0x11646081000c0c0c9a1000f00d0603103202c0101a091400702d51180b00c003c2880d40008400707003c8020590400c0a184940e100303920000784103003801d1000c0d140114503401750381154483c04e01030100d034a4040036100021601840318880484005040c0e02421070b0043c19076010820340c00300a0005000b001c00c0f03942074425026214181d81790341c4102c46030401c8150f4140424509201240090b00c0b0380c0180780d10110303030348241c44404c0300040c0481c20902d100c581074076542e440d15150720407880e09114103030300c105040910020356885180400c20501901a000900f110098801810b2000320780481d01c54640c402403c55407460101405401803005640540c0184111100d5110900342032045070400c400c141c64222003088445c9040c0003840b03000f040b0b6000d00080c0c102c00078030f64409001e101e002e501c483d11211003803600d40300c440300807504828840e4100060721082c41002d401000308030342c100c5802e03e408654213030f00a00084030303a003882c940c194101c1e207401317003c001c03c207915400b510120380311396070b01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 262266465 1250 262265215 262265219
    0x90227010504060503060d0321020a02010515030a0b070201060801090b04060c030501050303180105090a06030c0230070602092812082208061006080a050f0a0c02010e06010902040e01 80
    0x46880c2d0055004120101d0020404180d00d403516a540021452103880d100c82e1645007445850045522403680051094010514030303406902802807940c006c0447c5800309004a50100090386c840e2100300240c41461040007087d81c0c40e01c00e41014001c0c084403c024001034016241540011104407401c0da0180e14001f08100054407902030306048901c0140110304050100d440004410410ba043c1414480c0800c40034000e41c50f0942150700401d101d440001e0101040500070341030848004000c008411010700c41310303c1d1800b06496690340c0011100c81c9031540140d1802c40000d00c900760b900d07580090010000745404000503ca000118101e041e8022410b6485840d580000c1ca90940104220b405000b1611007649400a4000c0d41940c1e4440e0f1484980c0c4140e51810700700e00351011004400b185101b40b04103030b0000421038112648441c104194602144100c064050140c02058035540b00d1202200907031003504074544404820094554550359008180000e52140c80f40d04513030010300d400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 262267715 1250 262266465 262266467
    0x40b0c03100509070309060f060302040e061e060d2f010518091f0803030618011215150f090e1906020c03041815080708070b07080409022701 62
    0x15280501c00c441008161542007900308012000c0041c10042007682e600515404243c039800385085001041e54002045401e5006000c1074654030010040715a000c50140b10002c4410944003010709025036035900b01d41c071000005211450100405040460301c091213400c2d0030240c40200c2103100d1200300c8980d2030001040103440500034000b0000307545941e6103c019050030222012035101c4082551b1155000303003201d18000c3d896a0b5081a585030f40702000300191418541c0101c401c0c61004203c103060703036142000c00d131076400c51110000d01c03d0740c002c14030320800d1000d50010300d44038007400026000585c40d40714401d512086840341703030681c9081c00c0441c0c120324000b084004010308101c06040c00808a902c0d07010196008191201140c4010000014810410304100c4000b2101081c041401c1c5d103181c05d140040d25540d000049a41c201610800110800040980445804d007011544943ea9410034820602507075014107180360001581888c2c0e956442640041c181165508042042c0d017400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 262268965 1250 262267715 262267717
    0xd06020a1806050406030b0a17151e06010c0201021c0201090b010b040e2a0414310f0b030d020a03091d06010c050307050d030204051003110f03180d0206040b0c 70
    0x8a1640840c3c1d003040103002040c807a4100d10b5000101619401e5526035074028149181020303801002980c204054410340c0407100b02c04650841d03400311446016081c8012031140100d806482a8103000d1b0122080f41164000c2c80f001d06195841d8120807020340301900080e018000031641191007445500000c6141c80109007590240c60000c840d013801c41c1e8601c0c0d002609903002078640d100300e44440c10302c5503c1c5210b10004002410400075041c00c000c86910900000300141e20104080b00003210f810154201010200b407404600c0110100d145144001a030000304155111260503018602c002d9408640000b0401182c602c203950701d81d50a0758540740350030310030f01c0070050900a45900c00070620340c0d84246c0721a823420b409582902d01c0c2100941c2c030540b4008032002001e000c6a00032404000354a8049504c2ea02e50042c0d08040c400308080610544481c0310b11510b00e0800f90010010800100741d2240310040040410101c0c0d030103002000002e595000100c40403541909040001058950498 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 262270215 1250 262268965 262268969
    0x20327030702011b06060311040f020c0a02091009151a07030801030210090b0a110d030b090123060d0207050c0a06020d1101020f0703050705010b0103020f12040c050d06020a18 77
    0x210246081c45010b40c0111808900310000c1519648034000d5800441c101c1d1140c0320045114059040882c20504240415103c0340240d040e14a0b105200c245900c52001c96000e00da581d0481c0c800d04207a07521801011a56015000b000e215850020300c3c42d002c45880d1340c041d058030000c150122448000086040e428402d182e401000120385500400040c1001514130b100f07801035003003c80c1d00689602c82151300e1317040020218009840394403400d4211200382312030754004080d440d09000f0b90107003a01281280704188280c40d02d03088003030f0008095102c0c1129190f45070a0041170b0f259a400c8038003000002e50000700e002d4800d40201000c058143c42d00e881ca400c1124545c1d0017504103030114401c191107400300010340c003405540800040507400700710401007011a00c20303190300da00e401260620380d007152881000c1070305141c41004109010900b0b64199881090b03411490350365955079207401082c480c100d5011980004140008008204450300901000703082c3c0e3307903150040e4610032800c2211910074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 262271465 1250 262270215 262270291
    0x9020306060a08150415050403031b0f021902040209030601180f0516080601020f01064e050c130501150c12030e16080604121412280203 60
    0x1c030062290398645481c03160f801030080400c4101c0070601550070b030989404650889c0001c2c0c0e03c0b80d410050700303000190f104041d180c61030b21030440500c011000c1d540c0d502c100703408012800080e0b140c000f155203e404a804080001e0292042541e4607091003003440c03e01d00c0512405410701d5508034045c000303446440c0c400c07041503400240c00003c002096800381c802428a90450145019440c0700100c05d00444005100f01c40541d0442098050030503102800c0580d000d07010162404050b00404031800c26400300900403004507800d04092810603e840c0c00c800303110b130b0840740649217181411081d5116030b04981085120313900d00304110a044845020042000780500361880d01c0c1d1107054829442035a00741441c10840703000ca072000741c0d40307400d10307113140c0c41a001c81e88420100400c00001c0c0388441143c5104e42080c820000d40f1f60381050042c00b59500407900c0c2d52443c40003680d0070410000b41c60100032581801800380f01b110b440180650f20032600c3c1c81910710b072000039420901007103028442c10101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 262272715 1250 262271465 262271473
    0x61c050f0115052d0108070e0d111503060904020105090316091d0109022103070204021903150f151b06090606080328090503060f010807120503030f09100f09020306060a08 75
    0x2880040d00c1c1c500300071f0800c0f800c201208a400701c0303a4441c0e001010303115000d1200c15480d101b1510030408000140d40c002d141c0c4040a00622000b501c034601070356002a0b0909182e920b40907400c0109250600000f0100841409081d0010b0b03008616130011400341155180940e8031485110524260b4108004c000d400ca07a122601100e10000e41d400e080c0102010030076a840c0141c540c00041c2a0381044072020046001c200002482d660184940c80b01541320107803c03a81503203041c0a81444600904c07590b4090140000c000d05c1940c4a12446040034607206c60500380d00f915401c08600030080341030304440562a10301d000c900070300000151a01c48102041c2042030005825440c09503100041e144014000d04103008181c0b55010702c6001c0c41100505022441907141c4461f0619003c1d255000c211200c40c200c40c0400410b00c0401226440340c4d120003e80b22a459102080740343c41e104540f40002c1c24130b4041080c4030456160080c605c201d0085040b10308945809003081081503a80c4102c5582c0d0740 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 262273965 1250 262272715 262272799
    0x50d05100e01020c0d0503011d101a090409080706200409020702030304090c05030f010905010317070309080303090a050606030102030c04031e0c0308030601110105061c050f011505 79
    0x140e0300508038a1039001d001605000c0200100740ca45007080801c0408244081300500800d0301c420a022104c1880908050352428840c03607606c0d20720014000c07880c0642091086a400c130345c0e240c0445d44458005402040800402c4c2044c4161782c010000c220f440d0390402c8014103903a4421003104031501c10410b03802d4505490051058001d500800040380c040c0018000005d022440d40b01e642410401d54485c0d5590746400340d100000c03110160040e0180514050041c130105403001101001600714a40c8107030f4500750303402d094982082c5a40302e51120301c000403c1100040c1d0228025064a204100b15070341c0d0340b229420103090b030100f01c8c0d01d5622802c0901080000c1081c4002c03010000550590548843c032140e212401004201d81054503440000800d1050719644158110000050b000080009050141c00a900d07103501100c540b0100700000480001c0c4141489101003085000008200c1050800b419030581035042c403c2c01c0c41451014180c108003100c0c42c0c42222201c1e52a02e040b60800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 262275215 1250 262273965 262273993
    0x60807031416110102040e040c0605130504022104140d080f1614040807030b06030c0a05040b0103020c030c0c040606050f0403080a0903060c09090c0e090609060301023001050d05 78
    0xb151408441040051540240e03018800c1c80180080e00c038402c1044024038150030241510b0700309a001c0350070810300300a40c44480000a9002c3c0981e001141e01507510a101000076a055080c2442607810b20303544400e02040095101c0c81c541090a03600980c0d648140041d01900d1031407045a20a04803d044130004044c0a41c283c1c0c03092441d8650b05041415440701c0c512803d05e07402030340003c0b0312a40110024004d000b6a6004e003580901d045000741036509981c008906116407e2040a010300d4a40d205100c050b8000d4040d11140100c0e042140c5d140e44441038800c1c1e883c1d442c43d50a9000318a07248020a00034030030740490340740142c4411074618051450b5a551502d40c000081d5900700000070b040440012498091412100da00d640d6030000700341440c00031005c5031040fa64100034020140c0401c03d2503100c450500381c0c8081c0454680281d5980e103c0070901901c0703201d103443c141403102c00c50103078440d001011080c0040b0408007229032983e251420302443c001036a002070305542c02410005071031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 262276465 1250 262275215 262275241
    0x309090f0a021201060c0b3106240e130308070f020c15120a020301060c030c0816080a1b08040302100e030708030d1506080f0c160b010608070314 64
    0x307041c41000524241d41a801c24141400c20b80000000901102e00207003880b4050001d01e40218154030540e0b803661b400c2c10152012401200c183c07184404070120141844402e0340b200b850140c0c181c9000d418890502c07000e5aa4850900034541000703045400305e000c8400304500d05080b0356160326050400d4440500079a503121510380c0400c110720529210310140e032504240000d028248241d65a1a407070500c20344001001d00406800c4441d10510040095560043d5024525a00b60a100c10450a5420291302c00d1041c0c0c01140e49103622034061800b004103101c0101000c03007999075286108100000c0482d14440c0308031002d0002d4409000034005883c02059404190700b45060410482e01c07103001090805420350300c00b40c1a9003020503e00400802402560909030340711503020304990600c40007401c40c07280581041e4040c0c001200195000080404850341a210381e201c2e8520550703a40790800e06c0c01800d014001c00034214001084c1601e002c2d02450304030b50303240c06500b0318669a8405030000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 262277715 1250 262276465 262276471
    0x4030f050c070308040303050901020c0d23070b031006020f0105061509042306100c0c06030b0d1401230603060c030a090804080c120d02060a0b0406030b13030306080309090f 76
    0x81c02a4840000084c120300014001588a0b40b10280c039607461500290a02e444680f01c1f5004030044401240064080078000200703001d25811800e0402a0b5030002e03242060315005403074240b40000601444220440c0a80202c6d00b82c2d600b240c419001103a41542666020796905070440341000343c0d080880c00b2000941010a4091300c0050081a211038001e03030b074021f0b003983c441500542c50920a0a0074480c4d01d849080e44903082c4044064601d40d103010280c20b991141c44209a03549241c2030103503403051072140381c587d00b10301003a1800e404800c078240201464041940081e0101c03180170349485034250a68850500203018118030b03a20750200b01030a0348024a64840650781e1108007002440c2000a03002511107280146184100207042c00344010340c42d0321800c40365010322a86550305500144095020403114000b00725000c0072804203021b440c00e0b0708000c002c407142d181080990f648207040b201406001c0c2c0c0d4141706031f80da9410040d80305d100e00c00d140d54010000a0000d070715601d2840d441a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 262278965 1250 262277715 262277737
    0x1008061015031812030905010b100215180a0c08010513021806010905120c10020648130b1801030510120b041103150117072411010504030f05 62
    0x3c200d69a42d5524801c01c000c81c006040480e80e280002e04c148030092085240c0030000b5031790302d1540840800042d41e80d0480a8034481008901302c0000e410740e0103907030081d145204080c00c07600b0140c400e240805640304075000b03130a180e42c40c001c00590f00201d03880749164115000742202d03212090a604c0c2001c502070049c8180d06201d064040010b0b55200c001040395000b414001508040102e40308101c40e52103001d51600071075000d0380921540c1a0310b42e102000da20f21000c107184030b04106040d0145403c00c903000d40c0031031980069501d42582c5071040140300c42064038082c9458551180c80088842c000c465013a0341c0e440d40907400d14410f5000364419a08011041404084190b40f12801c86030441ca916088030400344100511080015006260104c4d0a0440150100f00205c040102c4c003210144190706001020748482003680b14248144005440070800b4a20780c8018481201140702500c1c0c0c0300c40009090031035072482c442c0b061007220300899240d0358410b0004206202103915411481c0841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 262280215 1250 262278965 262279001
    0x20c010c0b012d0f0302041104240c022e0816050a0203130f0e0106080c03061e10020618060103050c150412060c030b04020316080a06050306100806101503 68
    0x50144010300450000416a440400a641c5d096205110a881507031290070403219051005028455403404201c8025254001c0038404540610080b60052254540a5044403041c4e18980c60400280340b8801c9040000361111418003020500f20740030031007200e02010440006a4008040d445640244807600aa204072410b10002903c02100592164013241041200400810230030f2140b940c8240103098034100016039142103843d2148038480146010701c1080301080d038030405001c82ea0206600b010242c0180407480c0c0b40880650307903590076201c6c0c0440a1145445044c1c00f000080d40c24184c07644000540002000c1400344400640c6121210080103400e00001c502c140a07044c100d4417150281d5804100c400440c1005002c0303032105040e1a0080380108200140200d60301c4519100b420140307000d200a0359038250728401003005420083d81400b552060105605d61903c0c5507090f10741c4101514001c2c0c0f9980119294a00c542c8071341c5100c19102c440c1800e07030340d000e940700c91b0740c0d10600301920b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 262281465 1250 262280215 262280279
    0xa031d010c21030b060f04030201030f14040b0402030705040b18130b100e01060914090415060e090c04020c07060806040f0e010f0608070f1202030a05030304030c03020c010c0b01 78
    0x71210b26400350901c0300d0085000c422201460385030007083c060301d1042c1c4925141010303001041c11148107034040a0b050644411914100145c0d13544a45e0040502001c45035240c1424941441103440542e8141d1082c030502801080d60f203410b00c940300b0b64500c01010160001d1046e0340403004000c00030503081a00d080452a000843e1287c44803601c55801d07420a022501d051109003045504181c00c880e0801c5480c5100b8421041105040c51000c1e0084403008a15511440c0c80340c0941a140c14050100381045000038440b9607180149021303e1300c1206541898244009200403806601250302465005420400c4114025101c107500094007400100782403552800b40c4082c0d0b0b400c0394080316140c0d9500c04000f801c5100d0320038400a050f030360303014000c95850a003280c07100701464091030b83c2c08094180e4801c1103540400ca840c2100d40e2201c19a5102e14060130040c0642c1d48104040d00903014000381801d440d885408101c40340c6170300000d100c0c19030742041110065103580c201c02c91540301d590b981c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 262282715 1250 262281465 262281473
    0xc0904020a0c1704050a061b1e020a0e060d030c0303180b070e010c0510020c03040f08070518010f03060e0102071b1806051e031c05030a050105030a031d010c 69
    0x301001d207901d8896011181d001d1a00008070050140420032552043c00b0620040c2d64101045048404130302d0105500d0041507a03040640c221004002c05058503900c001401005803a1464902c038021a03910220658510085203443d00c00c03280b00b0b0340804510480c0300024051441c4444050103850000381c3c0102000b410580200c0c0880e0035144020700c0c1c010020842d6002119400d2290207103008000c1040c0b44e0b03552035440041603020003030160049510b480010f030810550700280040c580e0110355542c1c402030513840d91004d0180c0350003900700301404200400c0e09040c0b141220480541003248500d5a11110000c00041880c101d041d5001c1014001003010700c1d00490804a11041101c01240303807440b014801200300f00d40400c0c5038103016081200c0c1d610700c03401d0106001c0c15802c1e40b4064103140c0000b4101020103504100200c00030f40400c44032a4000040c1d0301c030380d00504041080d40d88a204241e078540c0e070010010000b5190b45450010f41c011400b04050b01174040c10030b5018480a503803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 262283965 1250 262282715 262282717
    0x30e0a141e03120604090507090c0c0507030602030709051516030507050d1d0a050f090601050403140601030314070f110316060c05070e060d060c09171f0b180c090402 73
    0x4260030a60010441c0503095503070f000c0081d0002c40c125010001501d066a41d03e40f145418032410039400d80c0c91000185950003154445c00c89580074068645680d00c0f454400c000790400d039a0500081c42c80c0d400460303141003009060449103402c082032410040881d00280210300341710400c42c05c100e01480341c900060404c00802d200e0800a4903404010b00403030142c0040c0c180100703450351250320788010070066900c40034001508400142c480e00308a6032440b0040e50036115a910090031f0101d0b1503240918800d0100e0483e050b80d2181e61200900f01c10111070b000b0600964074042c010410760100380002640d21500419004006415a0403002c0c0401c51106405481d40c000008030b410017025030304005060240c500608190010400380f4200340021aa000b00c10f240d0080415564000205140e401245501b00510010f190807201a505070f500d181c070b175400500100354500840000f2041407501e402000c8032040701a008a01c407001d040042f03041c1000c060701d00241300c00c2c00c00c075040090300c03940 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 262285215 1250 262283965 262284013
    0xb070503120703110a0c0809100c1a0709050103050a15120b09030c1c0201020706061d100e07050f04050d060203010305150601080a050603011401091506030e0a14 71
    0x102454807045020480d881c1c041c00184042c0c10140342044408181301403505548151042c0e140c001e460020380e15001c0454480c01440540c02850301000c1d01c0c85640c0026005815417051100c2c2c0c469018090300140c0508003176500c2000b01d00841c50a200d994802c1d804298400c3e0003600204140000b8000e1500d0500103400c4083c591404080c0a420701c0703040804e00385c00c0494000114904162481459212104982401540705850590740c201900c00d4054603c0c81e50410700402c2450f81e0390000b0034038822101d43ea01c04c26010400054039440c000c0c0b1201e0100c5c2c400049414259882460490712540041d4001321241c1040c000442e040d103c5a1820f1103451140b90b0050b0740754150b0070143e1a114520614840d01e042d00310030080541d03889032407650010044030340400c0a446010000340544000008400074190711000006c00340c03042d410201c503c0440446200c0c48585130041101698026214078000358005c8111800155040340043c101c000a0070586915190b11110350203118082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 262286465 1250 262285215 262285223
    0x50919050c0a0605211009050a0b040c080708180304170a05010e0607050412060912030f0513050c060a020c1302040905060109060c06091e0c090e06010e04060b0a0b07 73
    0x128031031140c504103110a040500f0f41400c2560a1035508010030401100b220104010480c412000ca4500d103018401c2402400c020b1000313005c0d9113050440a001010002d1405100303500300f1642ea070945000c3c0701e0560081c010303a030b1041459500d4407442c254408110483c80c10341c1c403080100013201c1d032500d07203d18018075040f00604002c0c1d449007000c60958800541e06221904054140a010f0390010204d504a41800f4807200a041c40d50408000a01a540025110784070b2024803841e6554186d0100d5807040b8031100070080e58071162803202545250450042c400c0d8020f903011440c0b840d01901500c600507091044503030914071600802c40401c0900040001c00e40c0100f4180f007014500d0040d1644a5820f00e4039045051400400030551004c0050261030307160b0301da4408041c00041102e2007074260300129110061071240c540004007440138400c1449651030030702074507840d04001c58601e049510000310a0650f441e29103540000b00312509010360302c101250000a0350450000207400c2107801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 262287715 1250 262286465 262286473
    0x9060703200a031701060203030c16030201060e070302030f0f090c0d0c050d0c0609060206070509011101061a07060501090b010e010f021603061a03010603050d050913110301031a090a0605091905 85
    0x74140c0c850304c0b490310603041042035400c24070401c40c000d40700b4401d4410005500c40018003c400c1c50a05900402642e0054510700d02028100000543c040d001140200c40715071507c3c009913144d500120344a0300c29140150181c00990044609182000301400d80b18012120011050750701c030001000c2040b0390f00215880003501104000041d01b002d881c0300101fa4900103040503207042034008090b032040d2134507036040c041082030303450a10400350f000002a150124141002034604603102c00c050b000400c0032164203042100224003820140500b90b600141a15045641d1280e07000648614115400301c100f10b2281c0040500301600b40900d042c0214000c10300020007441120361044142e160a04490090381000c2d0100002030000074030040c480d0b42850040d850750346c8400011070908a140c00c01a42e20b051a442c20151003820006504882c4a2115446a83d45943c0000b254050849900ca107a405c102002c00200703001b600542d5000c0c00760015140045504080340c2d8840b403c0c81030584940c1c6c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 262288965 1250 262287715 262287737
    0x40b0306010f2103090314010920100306080606010c0813060f0f030504030905060c030d1b1b0c0b0306061213051e100b0415091b0509060703200a03 65
    0x846410000e0320b45001e42201003400783c940d140a404070aa45c44005c00049100051800e02c040a510035480154440034071000040310980000300705400b081028428400d5450320325189000e44919000c84a0301c10250030075a442e42c00544e01a482c00d501234483c04000c0060094002c0281442009020303540c444840001414000402450f0056149401d1620300824030010170b03040003404040b0b40044030441d6840c24190340d02411402601d00d0100c0007030030700c4180b4921051100070040c41800030381e00c0d011100440407000760150009e990190002102d900288080d80781e0700029030388108050700c5549080705504803451442d0044800140d0718623095800d80410000741722051021140b0b01601840581007603107641c80362305c20591a8812541c0d03280941031911140c0010440f001000503082c902d1780c1d02c00920001d40400c07054540d1a04503001d40141043c0180c05642901c5c402a00c4c50341800c070603580c255030031902d10700550f03550023802c0110201c2e21000c01100d03e15034826a580b0140305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 262290215 1250 262288965 262288979
    0x423030a0510140c0702010c0204090201090801090c0509100b0708090109270b03010b011b060e160906090213030b0601020c060310060806060901020c010c030e04050a0209031e06010b0702040b0306010f 88
    0x100001e48859820131040100e070002d41c0c0d12410140f002d030340403200054074943c44e10050301c600100d0b50283c4c00075400c0612400912512650f101c0803114152110800c0c0d41d15882d282e440e4a07070500035001448018410000454407940141450950604100040310313102c1c084005164000c50190001e9110143d400e941c40f40c4030b0241582c0884154000c3c049280758800182014a1010580105085c1030040100380125070700844842194a0f06032200105152544140e0091601030403c1b464202000081c4140b441c1c400c0700c00304052070305020300c410700390f0766030082190f0b024085c54114403841450b940705a549000660103000c500c5a620340c22032034104007403d00c01006200c0c9203d03200501982000c0d0b600440c005450b2002441d04600002003454140d0701c020346404c010350013619190402403503005503401800020301c12811100900340c034a006000b07100f0303168040c410790380202e0010004a102c0201a16407503100410206140701a003002c06d182550036072010300441481142003141e8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 262291465 1250 262290215 262290251
    0x80406060e0c07110d230a0206040314070e010b040b0a11010c122910050c0d02010c031b020d050a030b0d0521041a0f1b060106090b0423030a0510 64
    0x42c042d10006501c4031952659081440700043c452400340300b107250b40ca0705806c103120300044c40d580281901e44480d140d080601c45240b034032120344094407648402085490754036018a040341c20103404cc034a07150a1403070310542600003074654410f0000580b0003030103000d001e0107405001c0720155a03c104070803081070a001179034009a02041c1801651348060f207480c1c400d03440010b07055403d80325648000d11704641103c0134031070703030160450600820401b041180da040d0410742440c1026075040c044401c240500c0e10070140c0250400c4050390102c1c45e1180124000c030050705070301a40e4200020044a00404209200c50714542100e00350081400d143c0d44d81d1442291790041d04cc401d1801d8180303030401c400b04d00502001d0380e070134002071f00209407542c01002e104111950b00c0c4a8800d17a5000411f054440742d5160030a00625001c2603034070b080440c84806000c20740d400c0b07580e10b90b003402e460920b01300303141500b0210070201c0e6054040c030216100810130422580b9813842d00b203980000c1c64243d60300240301c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 262292715 1250 262291465 262291493
    0x1091a01060e0109050f1c030518090606090f0406120506010e010902070512070f020a0803090f040209010207030209040f14100501050612012d0801020901021615080406060e0c07 78
    0x51002c1241841007990f445580182a40c006131045c0d6100180d0314001052549507118904041c14001d4040d02050303803002c0a030240c82100b0998201018000c0204644d4240407901039030000b034144000c024500d001d2080c440c80d0071014200188542d1140e610a0819050b80700c1a42c0320350050b40100000300c4030b01c01180c014440710004504040850384c07010344420380c01e101c210380304c8000300f1000f007800b1102c8603040341160700801c0311004698440311140c59400c4451158424a10000303114400d0405000302d8000341c1c4140d0162020904513401c020941301c029005981200d0501d1141c80000c00c040c440c1d25401a021000300b148903800c0140c0d50a4a6050b00a28040c0d80c003401075110b51080402e860703054803601050284059424408203400b903c204103042030700c0a901d2000504940194010040303002c007a426500e030150080c80d02022a004c2c0e208100c03c059460a804d603416100b040a0783d001441003c01188140c0d54100000725000152070741c12102400055090030040454000d0750 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 262293965 1250 262292715 262292717
    0x301270603020d021e060a1710060e0d060905010527072306090a0902040617010e1b0c030315010807021b040218030709020405040509060108030f0901030e01091a0106 73
    0x1200d0341c296070118004000e8000028003d41c0320b03100406052800074100c40301301e2000b070b01d0191a00340412004100541860100441c056044003040c1240d00e42c840080950f801c903280c480c0c208003080c040c00b060703041c0b600003a03921650b80c12040000650038000c450080e15100c40348500c04c0d03940014881c0030b5601d01c400e620150b0010104006c1001d805070045002072410352104048032024000c035a080c8101e0300f400341d1001da4800041183d0540d903018006036046551119104028511001080003013130040c103a409071403400082003150300c00c1b1900d5103801c40900355800d1480c3e0303400b400d103903410980340c40c022507802282d4495a0350b884640c1903442103091005008402d20b0004030400c0310178a071280b500868000071100c04011840f40081c407160009406c4565107603869840100070b4015002d0a4401d9050030b0208a8000d80016800c1c16120340c0e0300a58541460004a0f01142d0310134690907041c5901d804a104444c0f000f071148076200c038055041456040c100d154a1540030720142c110b04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 262295215 1250 262293965 262293971
    0xd0e0708070608070c020a0512060109050601090f0b0f12011503050a0504080a0e0312040806090c0609010203032a070f02040c0518090a0603170a030b040504120320030127 75
    0x220700780c2e214214a4100c0c004c3d007020340c485103180c00807901070a0103801c6141c0100240c43c100c9541c000018860b8100c0d1441501000030741c407600c4c011913190a15200d12554100302d1481440160460001080003001e22450b03e45041901c0aa00d501c1c610b01740d00141d2602e850341001c14074181c240c000d0560095011808001501c1d055942c03c0b4140588404a01006040035150702c4985080000d00069260501d0107511581c3d550140d80e07642c442140c1c2070406025100580b0498100681501e640501c140c002c1d500350354546020860b0158202113011032400c1d02036070343c10000c070716400420156005414030642e403070007801030009441c5a0364480040000410500040800300740e0710012030304c01103c0400d001d858a40c0c5010180c05150000341100004c03049145266030418000c0c505002682c5003409600e4401d001c10040790030894010741804480011101d125200740d210b4030008140200480c2059425419003011342c0090300032200304001c2074110107410102003004101401412014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 262296465 1250 262295215 262295219
    0x206010f030807022202090a1205120c030d0606050901020c09011811070204020a0e09090a051c02190804050f06040807030201210e100c030c0c030e030709020d0e070807 74
    0xc600010511001e8400c05002c24460215500c0107401d0000c076051940c0e0004412000301518020750048140a12852000d500041c3d4a43e8000c42052580d412a024040c6481c00044104044d4441d072003102c0c55000c00c11281420580510035007000d0945542e4a50f00e940582001914003490001142c1c03080e41300300d0042190a461100740e00d216584144003140340c040070320801c2420701901600952040c004581d07449401c3d031020550303030124000c0741e00c444651903481841d40c4840b405080502180c11003e151014144031045a140e6403540d44101c89045100e4000f1958009800e0b50440d00f000d00001e00700030f1031502d88141150140c0813110a450a8501041d041e900e00c01440003d0600190942c0400f42802054081101500c43e00040c40044a40c020440e1511024030f08405420724114500500038460300c505d440c0859540c44000c2c401c40346403800d075000010074a8030381e8503108461000c907a0407603a0010b00f9070006181d80109194503110f14041c240030b4a13401c003920581c441107007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 262297715 1250 262296465 262296479
    0xa0606030e100b0103060b04031101090b0313121e0201060f090c09050d17070b091027240f14070503040f060b0603040506040c0801110f03100806131101020601 70
    0x64850300b80c1034200010504501801600a000c2c1da03071042c500f1540201d000424404442c3d03401144603001d9890300209510781c4031410890000b954080b10030400310190000007220710740120041155410f140281c15080e01d010200110340482400040c0d442d100c00b002003001c3c0b450980d010b400301380300600000002c10002040804544200c41c850f142540541e024403052900429a2a094405455480d401401c16040c0c3c03c0042d620b0080c140b1480b100c0388680c0c017144c440e20103d09081445019031041e801ca80f08400c01c4c40b140b0583c0c0c0c1c074000100c11043c900b0f0040424a030101e90200c046600d011081100040362501071a041c06440d061041140c0c003035010302140d41c465403003210030f100c0505a0420780003d0180e810840d401140004c10321050110008120b4400c078401c0c02d541c01a10f4407081d5560999030381c94001c5c0c404000510591102c016220007660307101412144246003103036114072061508805071601c0c3c0c500e451b0b01100c501030040000d005c0729151020b00040115500d4010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 262298965 1250 262297715 262297723
    0xc0f0114130801020406090e0f010f06030203090111031e160806060a11030a031e0c0912021305130201080a0605060708070204090c060e030d0c021804031b0b0a0606030e 74
    0x1a000500c4400140500a4940d4621080c05007100760000c5444944906000e0022080f50003042034a800600c002010300f18544405416114010003141500b49400c2003900603402c040d04529055484202201c0c014070030001a6104005036808195040148502d00100741000b07403440800d54001035800c04103642040b001c5812481c251100d6694a01e0503004503144614040090080e000000f072092034154150001401400d603108002c3d8400ea02100d040300303c490602180b80414620b034402c00002481142c0901c0650002d4040c60f0f41002000c00c103c11034604031100b03001808948070306402c5d9640041540c0d400020711004000140c1007100003400341c00f13440002481e40a000401390b00b151980e401130003405600c000d80e0003941e43c135098050403000112200c0c5012f845400000f9040c14840c0c1d200203402600541180360510082184d61706c4078000610580500200426000110302100f03100f09406004003a00075450030b1401c100c06c25200c1e0341e807220082608000c504450030700049 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 262300215 1250 262298965 262298987
    0x50f04060804140a120905100e0906060c0312041e050c100302120a0603031211040306090203010209030d050702011704080a0309051e010b150403170903011b0c02030c0f01 75
    0x81062000ea50b40e074a8110307441001009065094010f88064804014020b80c0e03260614601d6199800000c0e2a4000e20008000c080a80030006101e410071500c1f6080c10703820183c01040c00303003665207015403500c84245103034412201d18442d244031038100414040c045d00c00354040754429002401c1100180c171400d0781c070f2071b1f20507602c3d200c0c200600c21030440f14000d0341200e8281180c86e02d2030f4100c1c40c14512403030040c100351101341c000c0f0340c04ca002d030f00f00e80d101c5200b000c51500c003001000e814075007103849000c0107110aa100b20780640d400c02043c900341d41c0c10004502901d0b801e903501d82d0741e00f2951000400343c000c42034486409031910310a100020300c0700c005840888440d40f81c0082c1e02400380c00c09910745251403e0302d00600ba02c403660b00c20400410f401031280e291041d1552140c0642815000b101442644406020098048481000e030842036008046030180200040b030070404480ca90110b001e40031034400e0103d21607101400c04c41c201488100c2010004907680c10b156007010001800c2c0f19004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 262301465 1250 262300215 262300217
    0x50108070e0c0d140906010509010b16050f07080307030e0316051903060c0203120c0f161511091c0b060d050106180213090203071b0201032a0f050f0406 67
    0x181e4000744607040e00c00140d66850101010a021003210f0240450350210b013510402c025006890000c6900e09140c140e03075048070f0906440a02c3c0c0302a4622100384603140380022034082c01802920b07072111004000039070142c19414080d55590107107190290100d00e004c0c0840b4041d0700443c00c020181c0e00500704550880d031342603e00c05a10700b5800c2000102c031100c2c3d00000c010500d0800540041d5034004044d10007400e0450f603111840d16041c01c45102e500405030810311300d075410840b0150208008001d400f14038810091b10704844100c0c0500c00c01c0e0380d4142c40408586801180012030381c50305144c0001010f2910142c01e010340c505440780d40354220000c0626020300c1c464544001042070941c4154003e00d45072035901001000038040c01e0203548050000461950301c02400f203a19607051003281d0048845407900f0504201403842c82c42100d40500d0180d041c541d503081c00c518221000302c00758007403403946e94810103d540b03940b03000740580d04120032070802c03c42c0c00e0103118100d0040204030b40541e483d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 262302715 1250 262301465 262301489
    0x309100906120b152a0102030a0c0e0a06051b030a020a230604020118120f0b1006050304020405070908030a0906110102070c29070303021e210601091505030103060f05010807 76
    0x416440d40e00c2804500084176000112000040f1000c0c0c0103501440c01515802014444861003500032280441c609640d61b6120300042d0040000d80e00980c000e040342170140006c1c2c50400c2c56024418110f40064014a000d60020000d90040140324501c41c5602e140e0126010507454410070400da8403a80184028140030b0b0b0408584d0070281084041e90007088801d2241841d00324031724000c0711031202c4c00811107405460700085134040c081642e0300000d46410341d54050461385c0301e80800c400b50101501007414400c3d62032000c102c0c001b051008242462103900c617140428034203d0024030b214500c0503540c000c3d0348144036200024038415144001c0b99071600140360800d04080c04041064419030031000a0b140c00500d850405425801800c111b403000c1d1032040036054005018071903440f0704c0351540c981c0700d81c0c0c240603c120010000c4041e00a0303410701d000c0c00030782d44440d02211140070382500500402e00100c0108108006030103403e034544068041440154505541241c0d150507500901c070010314 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 262303965 1250 262302715 262302727
    0x519030c031506030f060e040b0c030a091208060a0801020f0a110102040b0a11010507080103020d030f1403070207080c1005040e07021006030b0114041b110309100906120b15 76
    0x11003a00540c1d0b4071080d101d031a0a4881d80c490f809401050302c14110a0510308110f000605190345850952103580c104000358410b5640754000000c1da03000070480c000c0140d540c0480c001080340081a44007558131511a069141010000c001b0420b18a07071001c0310301c0c0e0040018000400e045010380f001c112080c2401e24828202d0100d55002e8040d079002641890008920321418503032280348000e1030034070303000200203507150480b086420620900020750400007502898002a100310707184c000c2515580703005240a0444110071109910a45240005910440c81402001020701407110420301c101c0fa05040000a0394018096004034807600c03100784154070014044a000340000e1058003c00002040016202d1519031001c8000703006010b1445043d12000d1000c2c1420b00c2200349080803045504506000c0035403c0b921000c048809590a000600c2188482e03294000c440c011f0300d040340c07511104141049002000410841115002035041225132101515040380070380d120101c608403582e441c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 262305215 1250 262303965 262303967
    0x90414041e030311160210050a08060d0602070f030203090315010531061d060d020a14010c14060412080c180103020403140703050601050d0203060a05061206040c08060105010519030c 80
    0x803401d81388411400300006040f0042d1035501c0000c0041500c2190b08200100c1c3d80b14003100c490007841c001030003050000011420314502a150034000c6407144001500e0000780d507590360040f00c21414210056440800c0785141403400b48903000350780c40810350f00011580b4000000d01c03003044141002c104015500070904201e905100e12807a81690000103114496032405940c0c601c1d06a120003240e1a0001000b0684520344032410303501203078008215100190a203c07a1a0a41d9001d040b40d50501114040f0200040e41c40c034034043c0700441c000c024010310725107814400d1020b24204a070104219212040043d4800f1303034000d03285100c0d0080701700a00c1e1001240142c0c000d05c03942d0409048051070301d0315440c2c1c0140c0040e2080550b4412400c0d2100f907640c941c2800083c040381b080003507144e0000000100d0150313141e0300c680c2d4008402001020305c00504000f181c03e201040c0c50541e00384a010b5028001501d0030048180140000c0c070b042c5160051005100d914505120070f9039003090307242c0711b54284032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 262306465 1250 262305215 262305221
    0x20c091302030604050307060f3312030c0b130218070c080c03070c06090b09041a0406030b090c06070c0501110709060f05031603020105040e071101060b090414041e0303 74
    0x8241d020b01240c4035404c082c14080d036a0380103a2400c540f6203050043c2c2c842d03840d125010341900002440340010750326860303042242080b440064094001405144000b4295140982c009455406601c9880f42091141010050301000030b040560b0144032800000043c5c03910707103699040384105c011401d140c2d00d4110003100c0c01c1c0302c00f08000d0210304001c6882201003001000508515201e1540113408954900f0b007551180050320681c200e9681c1401522894141900100e0308020741c80100c891100040c030002d801c0ba2450703001520301d070b0742c00c00c00c0260b20030081000c0107007044115052801c0c14010707036900e40f585501d4010241082080c42c50400450403c10104000d81a880020700403103440d0fa0000d00f1024091203514440e100d5100540703114150041442c0960384c040e941c051809003080d408a031000d8000c1c01c80c4040080391030310440600b0003840380c8000303088907426981d642d40e047c03801c20040e42c00c805440851010102c0c107020004802041140324210386000c1e04100103103601b015401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 262307715 1250 262306465 262306501
    0x5070f080409020909060a0f06031109130b03060106030b060d020d140c0310050109080a17040f03030e1816030b060f07050a02030f030f0306130603061407031b020c09 73
    0x4000008100420041c540307070003504010809945c1c00c40960f403140100240c2c11168420300e0107802c82d01800340003051207904010400140c0e1000d8030314284100740803504240000c0d062240c955a150403000b007a10301400020b0040c00c2d80d00d400e101c191f4019000417040d02c41e40e400351b0100c40d400100580000120b4010301242594180801e805151075070b00c3c0c612a40c422a0392116840d0305032004601580507030b20300740c00d840c110801002d6003403081d601e54074071746000403e95100c000c0c28000001c03441c40500f4800080c43c4640d40b120103604500040c046200801c8074007145a5401c5070402480b20b00c03100741d11841041510b4045904108803012501c40d220b02d155840c0125000140c074400d001c1c00040040216100b9011201d17114a00340300d00c1d841c0d0180380325040f000581007010498500e0582260f00a115003443c0c001640e036a03990b00c500440d0f808a134080907080c40001000400c0f0b405204e0104c09440c890844001c169012000070b4941c00e1081c0402e04c60902030010841c080855130b10304c1d0f5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 262308965 1250 262307715 262307723
    0xc0105070c031e0203010e010204030b060904060603080d0e1209101d0d05030c06090c130b0a1205150601030213091a09070c110307030b011710152303070605070f 71
    0x8030008081010f1030500b00c0d5540e069000c2e41c20003444507400e550501c201d804a0381c01000da8052a220201040018000903006860a541342e483c0400424400d10060110051040001078241c00707040e401400c0880032509040c0c4803d0901c00240b6644946100ca602c800c440e10f032000441a101450782405409260120f40100c20080103008100c0e000000b04000c40e000e600311042944d40b0001d042e5a280d000c1c0b1520313000f5204101c0000a40501e400c00007510b0f40007040b07840c41940302e014100c00c2c2c45510b41d059071503078051582a040c450780c001450703400c504286015407416101c040c40c0e845480c11445069030340c039900c3c003410343c44c0d07110b103244400003134001450707054070707040c1444c00625828099405417460400303042e1480c628580001d400040700c1e408644016607a1030b04026603609a1420618403050050307184442c80c5030000d10880c0010010850720050070380c02d02040403a803804520384282007a501c03881160060354001480f0f030403600145051541c0d20f03076524040240f0000c00d14020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 262310215 1250 262308965 262308983
    0x39120207060e031605100207030c02120f060f150111031e0f0d021c02041d0c0d05100612090b01090c0c0f0602270f0402090604051807020d0f020c0105070c03 69
    0x2600c50b1890440040543e4080d07012200e041e921b41380710f0341c202d100b881c0c80100403070090b41d0084010701f03100030459101e1440e5002c3d82d110f505c0b01c140190800008480d202880c450741d00c20840010501100c0b60030304c640078646640703030102e500d003465540c3c8200342c0c070804c3d41071131503d8144c4110410001c403204185040d050540b16007802007032901035080542200500075080324402d08211003442564211112070441c28414004402002c92401021b800c401c0c1c0184104140c8102c140c181c01035a0040e51800c204400407032400b0743c0103141e0800b43c1648c901403410490b00d2404540e681d40c040741540e40081d0000b030035100b203a40669810301c80b500c000300304581c051028024402aa4040c100d801c1010315109058501d0010242582d4907814500740d000e013404081c1d05140c1070a80c080c0818040203803e103842e0544440028640060383c140c000c0203c25001d003003240e0030b90705000400801c2110306004001c80c91008000e501c81c0303100070341c07281002000b04020381440020301044004540010f41c41c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 262311465 1250 262310215 262310227
    0x12010608042d05100501090e0a0f030507020a050d11040c14070b070c0f05070801060603020a0210053612030121020315010b0304060c020303070f0c06020d39120207060e03 75
    0x200018150901c0f031000254a801c040c0c02c485e8001003032790790b062507001c0c00290315440e49030380230382c0c1d50b800280c82a40c128216443c0410203443d5142031071034403030103100e02c1d41d0f14001400402007902d4040c1c0c0b120042190400410f42002030040594840c9a8003884002c0d25640303884040b01e0b106075106000d00181d400f1417008080c03050209003030055900301d8009105036a103482c400e500780d1090110301801a1b101c80c00d41d80888a40364003c94024580a90303940400d030b5800c0c414181400540d49903070800100105c50348041c1000c0052980c42d81d00c0c81c070410704541c940b402071800c2108158643c44801420b0400404540d018840704070322040d0320118a2082d61102001c0441c1e4008503402c03140c851800609250a90000059034882c90745e95448168180018000f1501440801c03011100150280f000d00e082400b14090410003008030f1041080c10160490102c0c0b0504414000070305000104200c212460341c440c0e52480b0743d0b8004032001d680c03011a45011030090412006070030080c00040780f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 262312715 1250 262311465 262311493
    0x2030a080c01062c070e1e041401140607060b060720010305010e010515070c080309011403010302030c0d020105070203071e170601090c0c0b01090212010608042d05 72
    0x203040001c0d0048000c0221075242c601103012490301e4144140d0b00503061410820758404100fa0b40e6006410786004845c800340000441c030300d00c8194144090744c0c843c03024806801e0405108400392017240a400c207060307500d48a03000314204500380c400d5009020004c0c2003400c0c0714a50b0485601301c2405042280c0e14480c50a160300b46910780740c84480c1c00c038241183e105d81036104c0d00406050b220b2500010309207920705420021902c50880c0140d80d100e02c2840f44070040b803603244524000344104405169611031980006202c072030740c0f0700f81c500c0f0748006000520151300c0000700a401214155000001e0300300c640010f0f2100d000700c40d0025418400c201010549070042000c3c0b200d0700300540a44101c6980324031040d110f45160216002c1280c1c00000100000070b40c0e03400a80004049080a41044d01580c0ba42c140e5501e0980088201d0f6400007280c00b50001ca03280200d00401c81440e0602c1541000d5841591408001a20f1b0800d0b02c0c4040c0c0d21303001c460192540180903a800310440e904040c210310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 262313965 1250 262312715 262312717
    0xf0a05060a021608030a030b03030a09050f010903020a090e010e070f060507021309060b0907030c0215040804030b090309010e04060302011d0a17010b12010c020d0309230a052a040e0a02030a08 84
    0x51b03181c0001d06040842c1285d003000404e40341240c4d40c03a01d80b089050f04150a020a096000310094100107404a001002d62507010030100a8500c0d0100480c54884c00300c0918250b0b500480608005e60101038200412005c000210080d51194504942e451856000180607000d61000c3c0c848220302d400040e00800050394403014850005440380b0300e895179880c40660442d10303000020030141c0c203d10055002c15441c1c61085511038490481c050501d5180e13251000c40080c01c076010003166000182013025582c0040c0e03007507103012040f00c040c0200350030b41d4002003c0404c003980b80d00356807444111040b05d1303a0b00c154440001d0018003e10300f0103484810b5055000e0489208024003031011522a0038040c0c00601440c041c0840b10340081991840c0c400b02140104940403040d10045003015000c1c003031300c09280310140c050758040000c280b10102801c5c21802c1080d00403c0c1404009001124004071a0a100d910422602206c0018415a007040913605080c69882c00035418001da5000c50204180c1c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 262315215 1250 262313965 262313977
    0x518090a08130302060c010c08010605040f14041404051b030604080d020d09050102030703060501080c030601020d260f071e080c090301150905091002040605090f030c030d120b0f0a05060a02160803 86
    0x192700d03152266a541400d44d0244105d002c0c84035061002001032008000c0c001052100e0309020707100145480410a0b0750481c82c1d0305031021a45a003005208482d982040141285003001c22000ba00017820299110303101307442440361001f110b540108400240c0e800c542e10246000350041c0080d552840d04820080061040380100c90220b002e10005c9030940c01c08034162031082c0c0041c2c0003014003400c0741200b69040326100a130a4400c010050507084044101e04000303005d40100740304c2c8602e81c10140c201500141950395416000c2ea0310880d840c0305a036001e9050758102840c80b11031981e07140b210001c80c2c05442c8803002c18030843c44008000582540d075901403881030101c401542c80b9441e00707200c4003042e486607100e50303000640c2c20302a4814074946100c0410300b088001b400c440d0341c0c06202012a040c50348460009010030702400301c1440300010742c01744039000813084175000c4038004000d002070f42c0f001d40c1d800303070500500c8049806144035000b040003141607880b44110081c065035640b542d40e5240d0201d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 262316465 1250 262315215 262315217
    0x70b0c01060f030f0807020d3201051b0912070b0a11060403020303040b190f0504020112091e05030c0a0c0501180e0402041a0402130518090a08130302060c010c 70
    0x41000041d0185a002d0141c055951203d10b518100c0b00302c0e1110303000da1b000b00d402079034840e68021a02d030020300b44008501d480d1161440080d0020403100003c400102c0340c0c84844604e9040101300041c00502c00e08030030040c00305420303250304c0d040c2c0ba2005c12404031141c20081c0e5030b48030302c84001c100c07500804041d1408200c9980c4403403a5000c40d244c215240c6006a0300200035074414008100065203084440e940a000002c40c19451900c80e00d051060303c80071881300c5109039403034003400259680560840b4606450081c1480303000700030380e180b0700303031080d40c0005d0f0101e0b88204482e542001000c1c0100c1d00c9882c043d00840c0d060080302c1c2000e0421103031034894039000c5680c1c00302680c12031840240641c11610603040c0015540e99a03024403024000c0107107050200001030501c05e074642da640c030280c690345a0301c024101d1100d00700f00501551801d0078500044005e107290811014103400107003131010a0303104084139241d6a5414601510025542000b54800b001081030f80c007892055020820500007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 262317715 1250 262316465 262316471
    0x313080c010203190c0807060501091d01330801060b0a02011401150513080d030b090c0705030a05130e0f2703040b1c020d050402030706030e0601060804030c05070b0c01 74
    0x864010b994030710800300c03001411442032010b040143c1c01400c0c6820380500421354585000c1c0e00c1d80c0e4110844109801440450b9507030b00c0302d0703071105002a54014803242828001c1140b030300040a014003204010003800001e8200000d10011844000381d081c000348038000007442020b444c1c000d610b02c15000840580c0040d0b2130064607502c444921995a0f04951000d00c2e059170a12000c0c80c100c5a42e0300c040684048103212120000d00c0c503804000081a05503e80d5001807050280380c104039210714060500c2845940511950f004910040b044032526405804c0195130703408110003046240380303694481c0c00419441410400103103202103480d40308400e84881c4101c2c40701030343d80c1c45605007418188101c07680d0080c001130003d0010b40004148208940118041811552b06014141d0740000f0711444555103400c14481107050800140c0c01400d154181403188860b480c411075500c4105205c0e2104010201000c0f40606000701c1c01401466001000c0e2580b294581900151b41d601c2030080030020b40c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 262318965 1250 262317715 262317733
    0x5010f05090703151701090b01180b03030304020a171905031801170f0915040501020a02070501090b03040b070306050303070f0506060f090a02220e0a060f030f150e031308 75
    0x4820701c11084d031400700c1c40000041d141017200c000d10902001001c486550350394008031010515805000c2e0080260300781042c152040082c0d0401698000408140070394070038818000143c2d00c0c06200340907a0034082e1041842c901410840e4a0070410001002913aa220000d03042030080104c01040e100903030f41c0d402041c4c60304034401180c8012103d18104109070690b000308100066400e042500642050100c0300d01c06032030301d1508825001954215201da500003010b4441e148c040c40750000a110900340141e01500c0e041820400c1e00c4000c00c000e003010440760000303010b64040c0e4056005000040c04030703900c56501d031825000c603105001c03040c1d07403500c141c1002030041e1502a400c540e958102400b8515a0f848a0320303408041d4120400d058020050b0012023540c110401c1c0182c0028010603542c1401d50400161034001c4030981d42140c9101d190024080c0041140c00e211b52094640c4107584e01502217800b119000107024810709012903020000b0340e04208800d05201074261448002039844002d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 262320215 1250 262318965 262318967
    0x30c03030503060109120302061b041e0503100203060a120f0f08030f09010e0a14010902090705070c0614120403031103130606080c0108070809030409020a110607110616090905010f050907 82
    0x6c000c2c820050043e4454000200c48001c004444032000321b5144c4c100e804e05498a00701903010b41e43d40031090110300107020800c0079280820200c210805041021031450402102103078100d00b56015600204464000c004e08200700100e1240d40e080c0c00c9416800c0210052500c0c820366807003501c0301e07064210190003140c00400103200e05401078181000914440f04d05d0390b1000b020006a00007c4103a5503a40d2054000d41c548066062240c20360f552a0b5a68428903d040c810301c04080c0c010500700f260406015581140b610121b540108a032100112950340d40d02e412005404140f800106208001c8140080c00d507805d82030303520280c813501003840a0b40c0c03a03101d8666114a200091400112b4003004526140e00980c5030540241645007600c0c9000c1e2500e0b4143c0580c1e010a90303e80000d90001610032050000b03100075504450a0f1031718002082d580003440381d4960000e06030481f8030030541c940300e4205000c2d52840e03005055001050180e0340c0d407080c80c5031074640182306041c084c03560100020469 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 262321465 1250 262320215 262320239
    0x10207051e03030c010e37080c190302070906050402070c3c0509011d0103230708010218180a05062b0c060c0b0609060a030c03030503060109 62
    0x61140034000910001c005651440c540403800c10040d0140810484103121030801e0003048003003030341e500082c01c405005501000c60921050400d40c20300b201d0414040d002c0300b90342c180e0a1161740141011f03031208007800c0b00301c1c02d20841e5100900c0318212001d40404058011032404212071020904002d050ba031203045c4016807055000c018600f04d1500c50038400c0b019143c031100710041e00e041c005284403202426545804003a03070030b440f020b00d007500010401c5290403003185014240904015a81c00d054141010200c4010b010040c03000040351303014143e80d200d035005844101c91420031107400954400f1500e000350f000b030480c02202d03107011451001d54100f990480e00d682c1100c2d1210090f42d03464800543c001c103406403509a1242403a800d60007816040c10b65043c810001880c2104180220b161511419002d60310040030320010405000c0400c0000407566803180c1d084d41c0080c03048c1e540f400041c0010003243c000509403017104a0200034154004003451081e9401c0e20b8a0310015111800c47c442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 262322715 1250 262321465 262321469
    0x20406050d0c11070b070c1d0a0e16120c0602120d052d07080a110a08060a0306050106051209010b15090a030233030402030606060703020708010f0506030c010207 71
    0x816010488496596080e60000c01d6508040c50040c0250f0520103405091041e42d0340030700c18100003c1298801e21003442d001030018182400144010182444141003154004040d00441c0d51784074003080d0300d1001840b107864903d910354801c4205a072501e01d07a8480c16507400054412020000b00802c4e01ca00010f032140c0151106c01c40e803801c1083c0407d03c00040d02009218030113003e082d1000d100722401c00e40340c4540151441074800309034a0540001803c04030000c003d491224103298031854482140801c640c910316583c603208030940d542d14086043c0181646c001884c40745417038000201d0036800000380c0408496416896115214140058241c60039a083c40f64000c0940c0220542ca030407007002030207002c0002d84083eaa0a50b2900044c0c00350900c006010301c003014040790240c2e4808c0c03c0710a0320041401c000c5c450300354141500400c2e510320703008140038003d404c001443c4013031500030018070303000740324100007440341c6070481391828090441070394600c5c000c1c807680710041c0300e540c008280c00b01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 262323965 1250 262322715 262322717
    0x616060501081f0b0f090a0e030a1707030902060d0216080706020705060f10170c0406060909150b0f0a18060f1e141c050906060a0b1e0a0504091e050901020406 70
    0x4002c1290801b0045240c5010f805d081045903610300e100c4c0c0c403c1c003e001620890a640c0c4a032140301e6107601c41840c4502004202c1d104052816007404010b954030002d650003a40c0c0d034007006888000841d000c0340d40902e07844020340320071800b10b090400c001c1c0035001030030f405d803040054031019210824070b0401c1010a480581e4070201200080c844001c43c1c2074494000608001280c1d140d49099000c03030126600c0d40c12080c000b40b40506c0034080380d00f05001d00076003264036460f018011480e1860366a8103005044c1d00c241f9000c00000d0208485118850b21084080c10100760b00302980d442070042d207070f89103449000340410a044072212140608500c006c0310600b20ba1615099003284080c040405d600440c00540442d10f451078005984803984259881407075014002c00c00d50800204021882040f43c0c000035901004100c02c6040c0070040c4017400b00c82a80800300c0f0340316604501d050341c0c01e00440c1c1001390703410301d032441084440b4180b400003102400b00c68001c11098848101c0c01f4242c5c412401031038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 262325215 1250 262323965 262323979
    0x30e0d0206130f0e0f0c1e070b091b0307090c0311031603050c0909061002030d0911030105010f06050406123207020105010609030803091018030e0d0b060616060501081f0b 75
    0xa0394608100d0082c000c480b00a08268841c7c2d1009050381c6050700003100564030312280108110241c0c804104c06642c03042c50b0030a15042ca04030100190303035080903000d00d141c2203450f0b1030660398813402038001c94030083c962400b00e5242e1400d2645821242d900da101400040d003458085250b2240240440c1d4280d98050300900003941c0f143c040c8940305095182660440c4410804000000050312645401601c100d04170032442c41c280b001c05084d00d01c103070403000100034010400c20885070448112001c6402ca401c2c1040130022080108004101459071030480303084118220a00c2d9415500f8003c82d10146040b42801d52680c0300300700d00b250b00c00d025220110b085054140003152703000740a1a440000001218000136284003518256148100280d018850040d0070380304246d00071440c00c100d20000e8030b20b0741c40030120f516001100c400151aa03070040000164005005980c0200c040c40213411280510141d40e650700d150fa520101c1100b0908220100400c0810741c003581c0c000c000c04034600500076 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 262326465 1250 262325215 262325221
    0xb030f0a0510051c02040b03030a052208160302010f230c030c0106080708060a020f0909180d02030a03060f030f060506030f0a080406111504030e0d0206130f0e0f 71
    0x18401410701400c0e101210054082c0061107680d80c0840d030151580320303000003809000398814407094a00802c2000c0c840c0e0410b00110021960100c29254286885106504200580401c1101c610500c1d00003440d0f5004400107000145200002e1500b145c0c401c1c0da0344500408800310803280e5000d00414058164484004002080c641c3c1000e001c44102d4507084e685071040b625046421140e43d5441031220343c004001c02c002188080c44240e5202200440940c41d00800f041141054804d8410003403181d08503802003001d51040b1900c0c0d0541d00a01421100d070f1031060900030b035a030b8022000040000307045c0400071400b0075007041c00c00100e075800300e5144688841641c8810140000401490305803045122a0512030020000702c1032207401400d0081e0303283d0030540001d00c0303401607401426041d402520703c1c10117000d81c489299403040c1c05141c080c0c01080750301c000035400945264043c0d80624086104460220201000411217078101800300c070b115030359100c02241c1a01280c80412800c510000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 262327715 1250 262326465 262326481
    0x415030e07030b09012901030e12040e10150905191202090604090c030303050a051e0f04030210020a03060f080f031c0908030a0e060a110904020f0c0607180b030f 71
    0x40c42c4c0200c03105001003a464000c40c8000700102c202500210a916074086524655803d480340d101381a42c0e0602911101013154200c46180c407451143d415805210000591021149642913000d0941c48414508595200c44000d020202502030a0b1007865001c00c1c070360000c51200195800c0302c00c1403007090380c1910243c0030042c40010091800c2d8201d0388585010f00001d030b068200c10082c6109803400141070404c2c4491108544008090100e1031045112540604000007041d5510401d800c500c42c015a945180807400c162104c07110b00e9420f4001710b0b500a011341c15400810a90f242140e08500055581c0142d0b550b0340316000034070119070002c001c00a26440038600e40000003480840108145080d50b0b42c2422661040341c070340e241140c0d02e802c0c542d0300403018032003140c0010701d128090020394022480c5a1043c03280306820740c4220350000d12a010500306500703441a00c203a034415110b103807800e1f07031025018100c01c0c1c40c010034880c40b0071401300303030400f03030200341ea006500d0341500c92915a0743c285 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 262328965 1250 262327715 262327733
    0x9020d090c06020a050106270b130213031103010c231201060309061514040903030b12150f070e0105090f03070314010f02190c1a0406020415030e0703 66
    0x4105000591100426008540c1c2101844010301196004041e0109903060040c21940e1941113040000181c1c95051a400755103510000700340d10b50840000c0c69100c2c2d40c001442107402c8400541e001e400802d01d10504424a0001c03001c90380a5103c2c00c14180368401014200c45280c1298008200c042000303c1000804203042840484021522403800f01150900109400241d2003000060b0f1170382402010030079503004405002d840e502c2e5144600e4140070003580100450006940200d6840b4036182c203062080e040160030580c040c0c090542e0011001c505902c81c800040303542c901e06005800700300302100d40001180b1a0020341ea403410008104001110300740d1103100403581c0400c15104000c0d06580512500f001940700b050300051000c2140ac0031825241c80c81400380d0502d03c140701400d50b020241c1380c0d51054811501e400c170702002c43ca191280018102e0b451100d128003c10080108110042e802841611410328400c3d07001440000218150b0b01c2d40b00d001c40d01608030780010400203840b11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 262330215 1250 262328965 262328977
    0x5061b250c03051002030601030c05090102060a051e090c191212050c031206130b010801090e01020415080405011506050d0c020304050d0515010803030103200f09040f060b01180902 79
    0x4108501c0060780d9880345490008040308103074020781d0020074040d2668051007424030444071820f1080c21700c003400001035160b0074010034514101c0d0302ca03400111480805070700e4001c00f5603100c0b4000010704010030181d43e1528051003541c041c2c601040351a9050700e2420394407007140d102e2084020034a040d95121216054003014007400e02405100031003105109002030080314031280c074203050510708130040040440b000c020618100f4508030f00440f00340d90000d031150540b2a1404c01140d035a403004501ea00a02c1103070300003055002c42c4500e062080303a0200d441405680604000d01c000c0d1804030a210381003141d88108030200300b04104402c825162900030142000240c01540e041c150744802240010303040a8089800350018018541420312003803409026119841c01581158119070b80c1d09862140c03032440031214049100c00d240c5903075845c0600315036640080e01c810440d0415140000382c00c0129501118003d042c003065113400d520414002000e00441d1a600d540b151800300c0d6074000b54015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 262331465 1250 262330215 262330223
    0xe070e06070b0a1e050c1b070b040312120c0503070f0c0512040807090b030a031101020c150402100e03060c0a030b0a171504020f010e0409020a0305061b25 68
    0x38030090000c10b42070740080f03109101a0b003010400751007803611008070b0301c01501c0e100441440d16040c8104a0014400c1d5220f5621104152076a2555010007901d450840d61106400e5540007502100b00202c007c0c01c041c1130425900c40040c070107411072880050b110016001c4000070001e00c0000d51061081501601d0743c80c0504214000710231644481d41003220140c1c4900b19a10009410050040c040081000406610360700b004804c0d520000243c40344094000501044151105079030480000e60450361a92a07040455080c422049603681130701c2403c0300e040c1c0c030810310b034440061207a004011200c2c24100c02000707030038540c2d1040040c4000d50001c0303003c00c0c105691414462542d17198000417801400d80200429141c110035982c062038400c40d903200c400c01114100c180001038440d0503030600d9921003400c1c612214060000403400400308104041c2d03010140079000400c1c428041406801407c00074044040010680c4400700e031880b544954078220010082c01c10780044a01502ca02c203d441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 262332715 1250 262331465 262331467
    0xa09080c0904031218140f0f0d0507032109060b0402070b04150608010504080306030601080708100f111914090a0512120d06050405010e06220618021905040e070e06 72
    0xf41c609010000642180103d030403c6c946420072118a80c100240d80e00f0048003401800240301c500d80d490f1b180e000b461007400900801141c01c0c401c05009000c42c0106102000c00d40c03000300741c451500c1c1c010305800c030001d0340c24500e0011105140d00b4107000b00c50f038107074200c0c2c2003183c1e540302c581e075645c1c1121140982c12032050342c41c440814201d200303000d150701450260341c0840c0c507818140101030501c401a44101808d6025081c1007001e9035000c1100c602c90001d58a002541c0b000d4148034002508285184207100c4000098584440850a000100902130359681700c3d0740c9401c1d00480c0d5000e1284403509503100c41c001c0c4c4204840d2a0559606a801a00c4410764607403240303200304a40d8507040861014000c2e51144000c2c8403d0421380b09031401030004041180d9141002004105c0700c03c07581008880048440040c2040589507400c810f0080102d5a81403500400001c1240000d412245d01c210b4012000503080364903612038001e407400d0303c0796000000b08903100c0c20070070b4403a0800c440c56a500104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 262333965 1250 262332715 262332731
    0xd0618050121061b080a05150306010e0c04030212030a0210050601020709020c07030524060f10110c060f180d050d0c060f020d020c0c04050411040b150f0a09080c09040312 75
    0x40c05a00c1035075181565184c0704078909000221b081030b600020100e012019800c200940305540028010341103aa8011505000f41c035503605ea100188183c3e04065081004421000e80c00c020000080600b0344099080d08c5013412080d2585040d91802c0c0c54441c0140d0100100f4400c1042c02e5009141c000c40400c12a0300706996552541e00b00070140c204150790740c052507007942200c0c4e00e51812541c0b0640440d007160f0003101c1580020214100002140304201c4410b4a0542d81a81048500703910030340201450740300c5800e004000f4203607111081c484881501c07847c84041908040d845c0c0380c00660f00c41c0203082e9200c009501102c0600000e002640c0e4140c80340b420601c1d0304603601c018402d8544030040542c0c1e500603a000c0c10b14042e4030301019030007245824100001f042c100358101c16100c204590102e582c420180000350401321400072407081034400a0a600420b00040044c11418556195000e48959690849856007000907105d83c100c010303c800180020310440706103506a00000c0c000815031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 262335215 1250 262333965 262333991
    0x5010b090421210903090e0f0c090d0c03081812070519210b0903090a030204020309010917070308010501020a0b0c091c0c080705041802040c030e030d061805012106 72
    0x20b8011240c5480f100e0313944130a0424940d01c41070180103400c080d45000042d0503d4258850700c0080100b031003081e2400460016160340e00d0b180f21155050b001980d003460b0540b03030304200d0f6056000209084181d080d121005019042005a1072070580a4101a0040328503060038841ba00510740076005031030901800100c0d0000301103451803400301115400410302000c91804281c02c0c3c034084c1481002d40d000f8402c00c105a5181d4902100341c03070781644c001d600c070340719a0526409450315800003807981c0148990104c640d0500d10107000329034040e96a0482d9647c1c2d40006a840c1c404003400034002030140000965686041d40c01803550680103810350341c4080c485103d40700380030648030044a07074140c020703000c00c403130041081204042c0100712070801c04c2c1c00c0070034909200d10450b200003e008940f19694214640e0203944003d03012105041903035980d00c240e82c40140184902d009860040007090b48014482440d0b1041d80d050b9550201400d403d4484401042c0d190201208101c1d030306c0c0c0e00c940d40c040c006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 262336465 1250 262335215 262335257
    0x1090b010908060f0403080705090913020105090a06030207150c0f03050421021c0206070c0605040602070602041203080108010203103501020d05060d170721050705010b090421 77
    0x140c0804d100348038140c2090f15000f00140300140242c400c20400f842010960b640303005140390001a5072140c0148240301d44010307034060140b06603103940403803544800209030b50150001d1804620840c20350706461540411201240c10128541000070403000c1140c00e607600982c422900503025008440d1408030400401170840207001068005070404d010421207a4002c01004488903a5030001e01860315103440e000b031084040450161502c2e40303400205003803100f030345d04a8250580280d030540d6182d485031000d14000d8000d0b0030840c0043d4502c400000c85d4101842a41d010300c503e0080c0000007454421154590b41c1101c08081d000f60031040700400b000c02c203000e06040344419200140e183c0801c0c00600040b0741004242030b0041c64002880000a80801104000720862420440d140d420301e0910313030341c08150f44080c1c404201580d41c0d5034a10341d410001420200d80724400a010103c200e81c21300c4900c3d00c055800408043c0074522140b03189110381c01504209102d840c1c415540c81d0704603903820360 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 262337715 1250 262336465 262336471
    0x712081608090907020d1b06061208090102150f0a022505010617120307140c0d050904060b071226010e0103030801060513140105071b0608100302060301090b01090806 73
    0x81d9080000d01c80070075052006400c4d80c011040e001405400c1d5000e18041c0c041900e41226074141c00c0c000c0340e66002c10005501880c0640f4842410140c4400a844d2004451340403001031805441200011800e24000140e03003480b40080d241c003403c15851300500000650807410b40e81400520020711a554071590910080c4031901410020501d20b2401d0301030103802164036019015900301c0442c4501d01d444d481e00b1240c11040501d403104482119a907820858020340070500241d016580640030410b40c4800038044030702040b1020044075a03501aa1005031080707800c01468020511020803c0d01d00884451814003500308840d91000e8042229148200d0240c200504100c034000040c01803680c4450514054201c90800c3c0380381c100c00550b00c0180030000d10805000240c1c2059094072640b041e400da4104c01e5203c0c00c504140d000345607451020301c0440c01400002541e410000e182c1e102070210410440340c01a0440380780d40d0030038480c41701418103741e82c681070000d5008001050704040040d944 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 262338965 1250 262337715 262337723
    0x904020c03070317010b04051f03180308071803111504120609120503060105220306060608060f061c021b0307030801180504170304020409050708100f0e07120816 71
    0x85011403071076111150444c1a00100c140340401d1105000588aa28204000442c00484c0c1d0b2a83c5122034021005407940d1415031803502d100ca4244010903400c981030602508480d00c8800c8542e42a001003c40c96280d8480648a400b00810203101801c02090000c81214500c81d41c510346922003a8095480b243c60104894103030741d90407002c2c24400041c550203030300c451500e042403840c140500000c10500500282014814008003800e4000d00400400402903521660a00c660b5654000c0507004220841e03800d070058603444040005460300c241141e244a450b8468000c00721443d9520200942004004140c030205210140a140c00d04002030aa21440b0740c0d5110344c5581400d600c0007034084829002d0080c58184428400000e03101c1c404e0b1300c02900a00300c026241e54503800007801808100602601c1ea00507d00c000c10303800d40104220340320441d0004103000d00c203908101c40003101d44011010510360003420061054405420130b10080501441d07080b030070103400380544115101510300440e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 262340215 1250 262338965 262338977
    0x80a120e15060603060a03150e010f0c030b09040804171905011b03020301050d03053006030f0a050c090408040308030c040e0609061003050702071a0c06090f070b0904020c030703 78
    0x1030318588011203031030741c8000140c81d0f66040d41000d601081c0022050301005004100d0340016007175070303172142d8800c3c0510b2010034005e0154642400c80031005011691344000000c0c1082880416801d02080d0640100c2e0702030300a910345480c182070498800d08494454220303000710f0f080f0903880c3d0003481e510b00020340507000000d4070007485111808490511035122041c1030051004001d2641c800a40c41c0c005601420020743d1030180d0054074101c07071510325038611408840d00622201a0000d5581c51107444181c0403258540f1100220701d41c1c810304402c2c010b015a00082040c0701605108848580040c86440b0981c149900c0c6d80c4c41c11801d420440c3c40c0800d660703000c0313402c0115420710121030b9008213064809840da070414002060f110075041d40a10103245d11400030903491442001850010000380c19180f8014a0701c0f000901d481d0303c1480c0e80c440e68404e000205507010404201c10f5800d03040364000f8a011841d040190506070021184c2940c842c1d8244890100c6070002d00080091520a46d02c0d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 262341465 1250 262340215 262340233
    0x1006020d1e270807050d08040603020913050406060e090a050618070b0a02060a0609020a050d0b0609120604140d1b05210c0d05040b0901110f07032103090807080a120e 73
    0xb503450710265902040c4035141c101c2c162001f10b030141e803c071810b80d5014900541e44400c02030100710030f50009021359100f64034000402c800e0000c5030b40402c080e243d00220050140c2c40f0310b04203d5035040c1004002e40346800034004aa00210158481103c40c4002c1c010b6034000c9a555031000465040705c5d681c500903802c0b400c100700c0710110300d109100c09004010b000714203224500c20010550300030041c280043c1641c85142c00d01961764a01540da141c0401807424070104139411469450b5a0701303484c02c55a01c030401ea01c00640d00408240c68001c00a940c0c0c074480704d50054107080c0158101803c0c10b907818050210001c1d022088102e00c0e41d1104119581f0b41d65660390400b0180c980810310500d0410864180414801501207104449124200346070401140c0794500c0c0341410306d0368060f800320040c0302e5580000100680d40c0c0260b903a41400389049052075000c2c004c15801c1e0b803610301008000700020055903000403000e8018003030580d454980150002c26905c2144210340001284209a81c410014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 262342715 1250 262341465 262341479
    0x12010b090f071103031006030e0f03160506150d0308070e06182d0409020f0306090114100e060d051005010e18030c061b0f0d051006020d1e27 62
    0x5160400d0f468000840c61440c0c06600341c94020300602482c0209502c07004a903e02040801c141c1041c00c1c2120203481d51401c0c2095581001c080c5014225424041d810000c1ca518218140303908170785c00003130005500380381d0556040300c960400810035414000458034500c1c5640782d6030060142c00025484903075020f6039640804c440702440c450078240000d110301c200e00e448185a40441d01001040c1e034042181e044901c0015401c15554030780c160544a0101004900401500180303100140c0700da50454688591007043c010500c5d900849812551340004034205081500a040389107010b141500c1c1252003212404003035030002c0c0d000034207204440c82802250984c042c81d8214154907000110310f41810080c415480e800010000c104d0b074422071030355a4440113820111100c08480c103001654805410003640e000b0041550140c4036486802e5002c68102d000150480c10501c0d26212014140c583c6070707545968144c40c0d04000100018500003200c159900e000649010301c8003980c0300022820451 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 262343965 1250 262342715 262342727
    0x1e0303041a040e06120705010e01020c03151005030a0c050d080408060406091101050c121b030c030705070e09060a0e010213032315010b03041b030f02031605060912010b090f07 77
    0x4110351160710001485c0324803980c009810030850717a0a0803d1902070b1103c0c40182c2c10084008181501742c0a680e19820f155803840b401c0030300c00e41240010181c60360305c4506140d9990010040180b20360f0408806000c0d610b03140d01c034140e010303204124040c42c103600e9500d054200103054808031040c5450f5048001004520406020005d00078a0300c0e604080900e07045507a91050600100700308500080c40da400e8010440b2002c83c10b480c00e5046907510b05014006595a07840350390140c80c0b07400b03022800301e540480d03d0401390085490000422158850b42ca00708011f14146240c0707101366600708620000c6101042892000714000d010b803900404000744403105221329a2480ea205400008542d8058011950305a05491088040035200d5407240b0f0194041084c800d9684038440200d0b0001040107019024808170358802c0d8141c8c0d425100c801c0c0d04c43c011404034050f00f940800240310103ca5070500109418150702800c00209054681c1004903d80c0182074039280c0d11076111204005415030000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 262345215 1250 262343965 262343971
    0x50310090c080708011e091a04020a1e0f120510030501050108011e0b0604030b131709010f0f0504090213030f03030b03070602030f0a0503130b010e150f1e0303041a040e 74
    0x14000703140c50304c942030900c80d086d02d07580204031206030340341181c143d41c284c00c0803080ea8024002e0701c1156a2610b400300509200c90706140d203168031212100943d0024421510310811030030301c2d1034071540d00d84111000009071070010080d202420044100101241003401142d0003006220000900c0b15880c01600c20060980b44052500c182407050542c080c2d16844121400c40c0d0f00156a044a61039140090000114113040a4031810188500c2c050680008009120041d0240c890201c10321840d402917854200101030800800d50500041200808a4004080c03205c40e40b25441d031000d42313a66070341601074050101540000d50310300200386075050030040c5078081d142e240021400c0454009a0311401e2045e552503008014004c40030641c40703c03506048005065100d40b88811a6071601c0222808040031600c980442070421001d0380c0740e040c101000c4440e07120180082045040001c010b81c00d15112515107030301403204020000700780c0d4092400d2840e50017044031250303941e40780564114000c4806 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 262346465 1250 262345215 262345229
    0x15070906090b180103020304031b0c170c0a03080903010e01021803012405010c080d020a0804060605010f0c020d052b030c030501050d020d050123090f03040b0307050310090c08070801 80
    0x10080c0e1280e0518008804600f050240f8025a80f40e48030b20f0115034910038845002241903078039a0f40001c001401c503504060740d624007041203800080b40285992030305218820b641000d090313802400807420100040c9600c25000e0300201e44401c0c00c3c03c0d0305089a00a01035424000465598a04285070a008422550300c220541c9603c0c045444001c80b02c1d0101d80c07007914144007108942801700301c010070a48690030001041151504d034540d002500300039040341e045540074900403002c1947d60146e440c140d0f08021566840c5d140034919800d2140314003912105452034480c40040402e000d0305040c00c038001d125504090b0b004c104101c43e000c0c00740c601b0b0703501710814103040800610060302d80da02c110306001e4044030704c5100300c03045080607801455900c0060340b8a0360f50303a440e030000c07020320080c0030301904600c41241d4160b04d41880140d164062801208880c4400700045403810b403103400916002501543d148601a56440c40181110060954140464400c03010000c020f6080340d44070b8018891 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 262347715 1250 262346465 262346467
    0x60408070e1608070804030c08040b070b06040e0c060d1b170f010501080604200d14060604120818130e06060f010f110a020d240e0c0d0515070906090b 66
    0x111402c0600260402490141041403000019045c5442812a00960354000e6240d03540d40ba220106041c0e650f0150070160b990081140101d600c03410030344201058038041300b004d041c0102c8800204003a90740070a6580201070744403003c07406008200c058030022103405464403142c03c403048000782c41c80c5a004000501712420700d070041095036044900254007880444001655100d2059209a072110000319034528010200e00411280850340c0440d13408840c1011681056a0742c504102c410312840c01380d40c000d081040080d8000072002c4c406486840101e0743c5031180c08401601007002e059134000f1131000282c0b504c410346a902403e10220f40c000b00103864a000c880d19600018000620300c01a8408020017030f14081c02c445000d01c0141103240c0c1c01054034000d09100d00740031603075181849625810082d004d483c042c50560783d115400e02c0030b003071101800f4411456810020360446003e001d036018018440300c1298062600140c621600c41c5e501d50760030782c40c1000c00042a011b901d4010500c501c80c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 262348965 1250 262347715 262347751
    0x9030b070e03060c0d0f060e100f14090c040b1602040605010309050d050f040801060305030c070806040b160c0506130b010518010311041d071809081603030b060408070e 74
    0x1d0100d0035552204001d15031320b64840410804800514600c400d41d90944d14041c00484c106500280050040611002c1c1b248095154441f0704a04801c0c0d200d100c076103c0350f014070003c107418070100c0d10368800007414000741800c3d5100b6041c0302c0c039840041a0041e000040d0120303411841c00d131141e580544000e103002c110840c605c0e96415a00d08018441d681440700114145509250710f0702190082d00501c002405265680e28100d50790350040c4040c00c000340100c01000c14030f048001391903441103030000451021900e0b1195280c07540f042155130102045120502c0c0c0c00800d0081004a0240b80d040c20611419205410061043d410682103c0e220f41041c02406408400b801c07195819a50040502049000400c000a0080ca82150105249020040e50900d070303d00102d1032800712451400d148104928503112082100c3e503051004002070b5003441100b01011881c40d4401400d4441d0600190307480a05c80064466002940070080300e9204810500c9010810845940c10500c4528400d12400f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 262350215 1250 262348965 262348969
    0x91a01182009041a030a031817071217070803040606080303190e010b03070b0d1803120504030921020a081c0f0207030b040303050a0b1f030f0b0a0609030b070e 70
    0x8820742d0509880349071641e072141c078680e00300401d001202d240101159100e43c65440d019108a41c121602c912100d080c40000949100321168402000c3d81c00f8060302501d81003030b0800100101ca00403d880507110b503038000414250f010014400309000d812191b850303113040e207003071010303540300b6000007100390424001c2c40402002c41071000c10b064001100420220041c10034a0300529001c04041c0e4184120800018440403010080c174481203400010300c1480c0400860202950880030010009801503403000ca80500c258869500980710780703048844141d4480a4041028101459003052124884004114540070190a00404c140009408801010f0f041c2c00e5201e103c0d0726590044c05400b03440791070007034400c0c0907110146078403402d15415414a400d0050044c40121040d6003828685201c0680da40381c0010702c01403036401b032a00790703005440c0200d04a000e081d139080401e010f075403102001c1c8150340c3c410742c10601400c55907581c2e9111703d1650510060540d4040e04140078001102c09030403c50b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 262351465 1250 262350215 262350217
    0x7030c060507060209100804021906020604030807051c0b040f180f050709020a0306090c08090d0f1b0609020f06030c07080304030519020a0b061210091a011820 70
    0x540090030065110b6450b07003850703000b0340b0407140300300da00a018888100d4102d411018981c0564000e50b80000c1c502d600040d000c14401c070390301030b6a0150340300400140011b0300c0303004559800300c901d1901a0030400c1c60020030303142121004111a0366606c94103401c0c82418039100d0440c010100344428000e000700c1460300f5800c00f0304444042d01c080e482110390402d00c4000c00c05080244220802103585d120034100050080c00180034645115042c1901400050700c07604103140070b1503d49000e0710f908240f03032000b6110050080012400e02c0f581c4510388102c0c004115407050203902900010a96503214410015451011000240b064500740280003100641c403042d0f800c007541c030003801c6680303450f80c0c01c040c1c405024004a5075198807804208004096010441108480c41441c124601e07859810420090094504034007000e0f52000c465003001250036040003a0b481d002c0c207401c5e80c14480c4102550056103090300802c0244802642c5280b00001501c00c98007290f2480e440703c004121400c0701c031201 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 262352715 1250 262351465 262351469
    0x2040504121103091c020a120606090605010306060f0f1b05060f0a060617040201021f0b0f06161112030c16090908040510110607030c030f0e0a080a0302070b15040c0207030c 76
    0x311031140341440045440d8140851f019020107190303145444180d290880140200f8040d20b04554140700e00050194080c0c000c400681c0c000340c4609030b85000e161011901c07500818046020003071070b500442c0d0002040c003501a0307110301801c0500380c00d03d002e448001c2c90403c007070500000e00d86045010001f4a44c4094910340400a208100750700da142c03400100d00d04410801c403120400909002154041860303482014282d00944920700c1c4c200048003001545e005401180ca03d840101c07501d2750020312248032020064200501c003e458006103682c0030f1940c0c11150300100a907000da540c00044c40f41120400000305414941485000c2007a07031649180d01a074440c240c025001d0710750429001c1d006810b104c0000200c00c0c212880c3e4600040000e01034000540808003180c509019024600d00750f014004112290000501080000d580e17000f800e6404a800312041590030300c90440091001050ec13800f40c2d1900d0f015001c2c601c40642013000b1a205c09100300d055503c90f00c2c0c10000a001d941c90902 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 262353965 1250 262352715 262352749
    0x21b01020319050c030a1d040506010e040209010302040801021908090703030215090c0d03030b040b190e07270509010e1513060807090f050f04050304140d0204050412110309 76
    0x41e01d1028910b058566001d50300b0340000078000070460000c1a503003c035940ba24000045406501d40300c0030414081116000d88840b800a891108103030034909160300100200c000c189401440c05a843c0350302800c91300309142c03080885480c910308078100c542c48480d0541146a94025100380c0d4511b981c065075555001c460a01104209400511250014480030300c601d98040c14001c88a44d2074980240103040207171406104605c1c040d032a000354142001c45140301e104003420160482d0801104001c02c0780000d1911040107003601b5031a035085010305481c0e0000c410344211180c551300341001c205140c181604040f000c011100208a400854140900c1540006481940490380d045009034081c0005070002c0c00c1520a141c00010351882c1548041c9041c921450200425142d101c00380160034801d640c0a0702d2940300340018090300246034002c4840c5c00c0c0c0288101c1d8520b9141d404039040d506d080740c00b07407042e140f50b0520004403500101004040080300e00594607000e071020020b098140703001c3c4202 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 262355215 1250 262353965 262353997
    0x50a0612090201090b0a18060903050304050d05070302060c160923151207140103140a0209040b13020324011b060603060e16080c060304080c070302060d0903021b010203 74
    0x1d690242c1180c4002e04001da40581d0f0b06c2d248440080d20102d042d40f49422024500400022000e10034062142500d84c020061841c061030941004404e424a640c2a03130140100e90b40000166284001400c5541142c0041c021510580342c805141042a41c08030003602d0a1040440c80441100c0250584a0b0540082c2c1c0041e100e01031118501d00c228180941c1055041c80c0d04480c0500004800782114030340300100507800a40c0004600742c0c1d20400c1030203030340d0b081140860200d1409402400b100800038200261000074500015040d8002009c58042d00c0e50010178440c0031f803c1402c04034a8800302d0140f0450707042c00400000c114107a40e0015004041c000c1c1e050310200031441d000f120047d504030000b4041041d440107065226049190103d01e1810b170300c800002c1c07a080200c0d0102409038001c0c00710b802c3d0b07503442d03c2d481042d5101d2a20310901d4010030740c1c048010ba4500300501110a100003000901810514000e46440c2003c261031072800c80302e22480350b05aa0010448100c840244802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 262356465 1250 262355215 262355231
    0x807140301260d03201624090807030216140f0d050f0d091502070905060607060908090414090705060a17090d08181e0705042301050a0612 61
    0x61072000b9038a0501d45000e0140c03c504000455040d08941c01d10100212001201e44d4204a81e540714804c42c5040411a968904903c02140351042001000301c501403c544004500711070a030211f41c8007010881c0c1c60000490b102c81816030400c28106030107818450303c1d83c06410a41011a200c011035040d500c00c8002090034505901c54944010b280c503403140484011846c4000030750b40310500d52500f02e0014040200004080049140a04041c510ba8000d00701f25401d2045010141034003c0c036940d00098100280d500049845c8504001e40340500b195079243c3c0880c030100b10648000c28282c0710044070100c03d00070342204c003081010840b481110065500d074140030381074500c64005142448601c50082c01c05c40d10701d201107964502682142d6855200d503031500f01401110740c1c5002103017469072000446054030b8070341141c003414a01500c0e00f1113034455a110001415100204209800241000c61202407146c600b03604c2405440102c501c1e0318068281000100080c9a80c0183c08010f6115901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 262357715 1250 262356465 262356509
    0xf0b0702030d091406071b06050c0f0a030b010e01020109020a0e0403091211010311250203011b030605030712031713081909140a09090c09090507060807140301 70
    0x1c5a0b541901c59905001c00d81c03180c100051010751090032810503014a00010303040e284a80215102040c00c5c0040c80b140408940342c4400829004140c540d0b024020041e05200e20202c2000d82902c807601d03540402e051540100040682401d111000d065a042c001c0400050755125401026130701d10b0101c0d1805035886003400c540702300c204d41c0040001c103526a02c1c0014006000340c00381d0401400c0c0c809100094140f00300310107500c2800e01c0d030201da0108a0100145000010a010340d00b400140049910500300c40c03002c5090804260706d00100e035680070200510304092210000612000d541c031183c201040d10060000e0b40b101421802d400c4141000408900c4d240c2013106200d82c100c1c4030a500c80c0b000c1e21821108540c44040741020a40b10403000904125000050b9061040079200100c05450012501c0261490080c11910a404020f01003410000361180e24003982c001c00050a5440c94518060950716010340031408105007619108000c2c9101e10880e41120500d41002c483c55980042e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 262358965 1250 262357715 262357717
    0x1080a0b0a09080a020a050106050a0308071104151205120f09060a17101e06020d03110c120307090b0c12070f0203120d0b040b090f040c2d0e040f0b070203 68
    0x100040c190030f00411902d410701c0d07002403810301c5030388a01d008014494803842089184d010f50322004110403030030000c5800054070740c4440640424041c2c408501101385101c000c0c8242c010360440b014024603003420324141311003009244a80f0070618002d030715092103425854036500c518040140608400034030203945a00c034281000494042c40c4444169081c50116105a82e03064850381b9030300c0725845040c6004a82c2c100066085071003e40052072030709110300c01075000d000f01d9504134025030414130040078030342000d2040c1607400640703541003035481c5441c0801074200022078110f80c00d100e00901c0002000117000521f0745d001601e26000703a4a82002c0d140c2061050a100402901400349440003511841c0000c06007103102d004040500c24140700209210498440c0255140e02051210200d103403108d091000c50342050040180c01c902039107564603440c2004030004d50713112600d00c00000601c0d0132004062140039000d12945201365003440d4a845940071000c10010707081120303490108011a00801c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 262360215 1250 262358965 262358981
    0xc1e0a121401090501023a0b1306030503070204050c03041e0602070816061a010507260406050901020d1b0213020405030706020a0b162304030b0c0316050301080a0b0a 73
    0x70000f441600ea0702d240c40c80c080e40120b00c0d004865000340582c182c0004403420030b00c14480012150182e403086001e44c0d1400341500b80300082d04000344510050140c02d0390f014413009540140011503880b1180d105102c1100c03402401c2920800081c001c1c040007511011103250350078410410180907020a0074088001d2043d49002032103002c0005003944081c550520660b0854001c3c0170030007002c012850500f00e007009000c01c1034005a000c1001600080000016101902660f04100558010140d008420707a000740c101c0d038082003011a4070b2810f50781c10800c10409a41c1c5240c0007000d10552015040350343c240320340003481001d070355580c40412043d603410b54004007001400c840e041d0b6511600070b074407001080300c29101503030884009510200c1114103a05002c050340c0d0349007400c00207550070000d80190344252a1035081c04100c0080443c14507048140030380c0f108502541d4a040880e601c507445030359a410a41440340520040006090100c1c200490302c2d0003000d40c400683d1054114002450300c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 262361465 1250 262360215 262360253
    0x101202100c05100504061505241602100504090b04141501030b1f02070806131704030209040c1502010603020609060c0c0a0905040c12110411090d050c1e0a12 69
    0x11104205c148405900301c540660321001e402e140aa8070350007808894940e2010300040c03500344824090501c000440100143c2300920228800c1c0307074656001406c113400003200c200000300041070a03c0b030f000d598800c19a002804860030441e47e0000c940c04201c10100600c001542e522060000d00396034082e030007100d00c00e04001c1540401105111514175030821010840e07005100742d690100301e20500241c00d81c020704e400c0511003100d4445175541c4c403c11066010462442e00f06100020041e1584491140030768415009606c03581d0070705c01c0c1c0c0c0312f022600b101050700b1a07050503410000760b100c1c0ca080741c4611005542d01c0d9a1a41e400034110f14050b21403080a4001d00000d400240b9220950703c100d00584c8222180030500390785c1c110303484c41d06483d1003001c1c000801000ca000b0341c40c60194400840d0100001c04542041e503100c00003160740b03c500c40f094070290050210b02029240c2294004070062401c02c0a00901c0c240d84081142044c10780a206401030382c3d03c10345003d0102250042c00c0003494 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 262362715 1250 262361465 262361471
    0xf1c0b01060305011a09031504020a170109030f0806010e060f210402011107080304051905030619200d02071a04050c09060f0603150609040606020105101202100c0510 73
    0x14410000b8003e003004d1041d540c0b00e200c14119803040c400c290088400d41d6600500800e03920406444c02422004041c1c0300b2039100305420400900308140c0810348241c2c0164000003d62001c0905018101000d0416500100541030042100507a0480224041c00300e0964009448200022000703c0b00d209900e4520380c04c41d0325611404001e102c42450b503106034801e07030360080c01910006410355170300440e000e204e200b60002d00c000c1c082c0e41444010100c900c43e0300186111040e6848012030b09001d070903504050070b0785d21101048150303402809503c106a01e0341c107151065003d0000c1c0e056007070081758803007007901740c000800100b403010000207142100e1100c04008440d0415181181c2d88048207060395004103c8900002e90a107860022519074050281000340742d40e89041104410788044121140d218505200c82d014545817407041c40c01034003040e000024181000c00c05401c4442c16940711500000700402070b41e00503102c54a064184140d60b0901c460350305260300d03000d0b0600c90715408452181345 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 262363965 1250 262362715 262362719
    0xa0504110402040f0911041d0702011d06040b010803030c0a0c0f02030d0518030604150207023c031c1103040306090b0402180c090f030f01060b040f140f1c0b01 70
    0x124182c1c038031045034070f481d0080040c5090f0006e5060607008a00c07914034000100e021512400a000070b042c0e500030300300d10001510041050381e24001d056814040300303860303000d50100410007142c03016443c09410b1400082d4150b1614080340101485840e50344001c211403038038442c08208004d18030340b8000e42d00a064440c81d5800710001031450b0040140940303080c8240707082d1f540601b4003040082c081e981120342070428864600e0120003a60107042c0c1243c20250061504080006000402c030b041d11803088030700800200264075044003511880c0040c483c0d0443e0007410348907491103804040e4202681086041442e44000841c1075001e00d50000d41924141100841046903004060307120b18400c82e0800007904040c5c140b401030440440d9a126150300403c1800200c0c40c08980c1070904100040c02c803040050f104c0744c41405e5450b0355101034036078140031405024901168030030070054001d20401202400c080c0c4005410480d058000d18002e0f003032083c2ea0030390741911005441090b9080781410080303507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 262365215 1250 262363965 262363979
    0x7030501021b070902070309091d010504050c0f0f0f010f17100317210a06080a0606060306050d08030f060609031b0301150308040e0601050c1c020c090702060a050411040204 76
    0xb5440c00140c0180600d810114901c0400d1083da01d900790076640c5c240b00c890170180c08600812000810000b050240308210040d44000d008143c0320764030030800b0340782c9004400c062004907031580076810311400400c4100d075580c0d15062214035008500b440c0c0045002c14106068900c070407480384103d0a40200c030f04110110500b40015412248030f282a232540b01c28041101440d4080c03a400001c6445031050f0706000645600c041c0d07504160b4240000410507596a81c4528003500200c049408986031341041102c503402d403040c100200000c2d10100c16010340750307640c049507100041451094030054000310300691614000e40740d0b41400034013145d00601e003210b81c1300100070000010510070360034922030802c8150b01c150a070046981c4008414141414641a408801002003003103040003418000f4080c50304041010b800060070350f2a44000a800b0f000c00241031402407607080340110a29400c0c040c80c00e500040040d8028004000001c240c6c40d14034100f203070b088009280c02c0d4040c1c000b19010500c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 262366465 1250 262365215 262365247
    0x40c0f0308190e0f0d060609060314010c08090a0803040501060e0406090c05010f210f1410080d050301260f100608070302090403080c0c010501030807110409051e0703050102 76
    0x31140354600c44400c8900b003001107030081045680c40341c111305040d540d01c041d401c00a00140400d03118600224010761114054811a801e55000707498500d17040c144003102d003100b84250151110344c0d14120906107405600a036440210030801458418000002403c2c40820740c86a0007400d10900c489a1030700303090602e030000d0006108191148114445d002410751701440003450000200d44034020101082008810202c00510b101da1009407a0700030a41d10741740e148504458010f588100e084681004000340d803081b003068000c03003800e0384501800c4000503000300603241110082201d250314010408071002d401e10030071018015034428100d400a000c3c00c0070400c10303030314440301104009680d81c0e0900b80e0366a40b240d22000c0d4002a02001040101c0d02c81c1407940d500c403001009152400c2c46031000542114026881a03643c0708000c101e0008000d55114031145580c411281845403210a884180c1c8440c01c189844803a80d034021800c420341d8009204c0c020055410500840d11004885034035400c1b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 262367715 1250 262366465 262366477
    0x12010b09040b030606030607050f0c0303070215090c0d0b0403020a02040c0806032404060203090a121e11070b3411030703050c060915070303061806030506040209040c0f0308 76
    0x1050381406240b80203030400080e41403003403e0040080c120303178940110540300d590202d800540c030500c3c03c014660028134104000d41c011107071540140103a0041c0f031007000516201034825261a001080141a956590158804010b400c003180b4266500c03075140c140d00e000064000207400a0602e8403419486e90000d0845101d03081c00e40a1740c01c00540c0290b0040d48001c9114000c640c00d14000106d0f020414541c0990307801038100e002c03904170b400b00b5284d07040132241c82e45002000407608442101440c00107a0258002d042c1170802800c28100d050301070b91140e5140c011a402040b0200f580c80f2040c0300c000e003900341454060040c00d10303105800308120711340142800c140c818030798038600d825aa080000c0c11a044a410030003402c5601030310020000c456203d040b007141c1c001049032803c0030303c949a100a00700b8511944002601030f2504948201401c0400c03600d001071403a2100800209001281040d44164102c0da280000d641c0d43c03404801c000c60a8001c04541c20000301e0204c1000943c0004000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 262368965 1250 262367715 262367719
    0x91302040605010201090305220b040905040507210312020d0f0204260d031a12010c0806030d09060315030503120f0a0504030e2202030a02090f041a120312010b09 71
    0x101d666101d8005900382c4424000040000b0360030010300c1089103c030328500b802d520030782d140c140005a41e4000722581e03401c241c121041c1a540e54051004000017040b40800030072190030154041c00d540380c1c0c008900c0201d07a001405200701c01c0d034254004c403c907074111003040c2081602044040503085012001703402a00a024031140c1000445981101e5071912091a4035640010018000000d0003207000e08039002680c4443d01d942c0300754400316038402e0801e9141042040c000070b840560b49030014080340002d0715042c000c0d00490580385086074003911174010303244103080204422220f40c1244803030030f540c2c1e400a4100c1c00045245d0f90aa85407180690003802030011598854852000307030000c8880079500100440c08401c0d0403903003420184450b00f0b05000c0c00171442200e40c0900c00540c04da0f0b1013168000030640e400144d0202034039000c406a2a00801036800f0070010f40d001050200164909105a120f400400c0c20300c0f952100800c202c0e0700c0c1060300c000740c0303500d540d6400500b0307403d8001058040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 262370215 1250 262368965 262368971
    0x30f11090f03120304140f1009060b0a03020a0b090102100e06010e0109020c03030103120c0609060b01021203010f0909020a08033603060703020f120408041703030108030702040c05040509130204 85
    0x101c0d5180000310900c1d040501040782d840c0d62500c4e80e422600c07041400c0d0b18071050161010401741d800040c400001d14064030a4041404d0000e840d0540c200d40c015588c243c0b003100300040520140c0c44444102c1e050307454030303000d80750b03180003000040c0e05e031030200b80c9240200ca003007043c03c0b0808400401d106040719201d6258120690301d0740c800c0d10581c026299000300e640e0060004001080180000c896004481d0030651415442500d403142503803c6c0803c140d80c129110340811546503410403043c000000300e01c134001d04650600c102c0c240080700341e104407081103031034041030401d41d9a000030841c02800c0f94800c0780d54407060308495209031a90303d582484610741a682035022102c0a007200b4a48440c028003405a55441c01c605034025080355451010600d02413040e1600d1094410120740101e0080e0310954803a40f80c50310100340c1d6078a510100d6083d030030034401080305410000a503100b95030b046402144480010b03004440601503940040c2e0b020340c00d081449902000a4031101c40c2500a0340e0074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 262371465 1250 262370215 262370239
    0x90a090c08030403151a120a051903020a062007121b080a0c0804080706020106080c012619140702010e0106060903080c010f0509030a09061d0907030f1109 68
    0x1980e01e0b801144000392174030903c4d0001e400034054982c8a504120000c08400344040b81e004081400b480b180d00d10000160700c840342c3d0f0010701c40c1c100b15425000b0080c0d071450301680321a940023515001e00b031400800094131201d10380c82c0d14028170f14080e9240c00342c10140b40c0340c002504100f00302c0c00002801d000407600c2401c8286040441488040130246c114044074a08041c481c2d0840ea90544076809540820040c0404a0106030601c5040010202d5a0000c900e20381072141c40b03402d0a0f200001a41400110a02070000d8090380031401e04142010048d03512039074030040c00d07000c0c110603040030070041807030f01340401c82201100b02032a004d0711031607008000e40816544018200c0d5440e000740c1d000f1400c0a030040000030310900045ca810401500041161110090345030180c0d601079601818a030000b150981d403056000b18000001c10b02c3d45421013194650f440c0c459000c1029903202406684500300044000c0d01a0b01b0034411388030308030b104000031542e801107605560001803810780b041d1190100303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 262372715 1250 262371465 262371479
    0x10807050618030a020a08031804020711010f02101d160e06042018120604110103180210090602070608010510110f03120a050105031c050c010b090a090c 67
    0x60009844001c0c11082c9840e0b040d800c0051821003044249905100741e4a000d00140c0f61110301c54010518980210b8503500250030640e00c00d9044141d0314021481440141c0114086144c08036104a00b820014100185900124102a0348841c2c8418841c00e10301c0350b03034941d00f20206004e194854034041c2c90004003140c00391039126209124a14813886000003044207882d00b40d00078102500203110b031401c0069000400031050b0812403911120122414124415050010317401114424010240c1103c2c900303640d40100c0e004004200504044d60342002841c130100d09001c098209400034002101140c000c28010024500e034012130700140100c0e840050304034020302150f4183c8a0062440300310200c485800c849404020700707211114811001e41900da03000501c001c007403018014421060a107018480c100c20f0701c406038080350181c7c0c0488000a445040c1d0b008500f0390001c18903101c0e81c0c40e041610414050452003100a500c428440140030301030300d03194071145240d0b00c10640c1e801110390f5000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 262373965 1250 262372715 262372723
    0x2040b04021207030509070e09030a09060f08011e12060f0f09020f060f270a0f030b0f06120d120b100804060f021b0c03010f020306011403100504090506040303050108 73
    0x80440c0840c840070b004900024003903040b0942c05109982201c9040d99500140000f02101f82c4801490f034100060000d08507500041d0719010702017900f4000141c070341900000f40306840510600801c0100000454164804400c1380300041100403840c0d04c8000c114207050b070080c02e80a40400c0958035041402a200c151801a05000e6800410040401c2511407d105166011118105071075104001074200c6207402e555a1400112503801f41d42c13030341c40001c1070200c9404103070401806155a18000c03c0000e41140744580d0101030014510529200c04011602c42d002c1d052485049002d820a000b0003594041400e0024164a01e028048000943d0031301c00d116144540c0100080d2100000801040c2c0799040640000d000c0c503030051501e20b0790408190707141083c2ca0192880d4000b020204414507090188441c1c0001401085255042400010305241030404c0500758001000c80020b03885090098102c0c01404060002c0c091004680b60590315044112411000f0a140c01e0000c070b200b6030001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 262375215 1250 262373965 262373977
    0x501140f0d020312041721040b070c0b041404050f10060f0c021c05060a0b060a0f05040803070605040c06090803090906031906051812160515040b0402040b0402 70
    0x26014100d400d00c0c02040c0301010001140030b903010b1051480b0600d00c686180000e100800e05844188585c2c100c28080e1030800201409041040b0f4441c40780b4200b00d5059030480d0211600300343d100d55030702c0742c0b0303e0b0501015079940d202c01d04071800030400040c0035020000308094080225010400ca40c0c400001740c000c440283e9000c1001482c201d0103014141c050943c4c401c00b02d000b820310a181c40180c2e400a88461251036914070b050608041d4001002030410035540c0002404205014810606001c10500e010301400b01d81001840007040e00b08074064401c40d0050314491007903980c1c0701c6150410b20003510094800300d41106171414000307000c1e0b03c42c611080640c0c1081c03000e1484e01500c0300800c140740802600303441e8180181400b004010745000181d6a400c0e00c50480801c8600e08030317048504100070b003011559540c00c58007803080f645950314100e4079100341400355602c3c5070105090003450035044a8010401446841c280814095555402440f45108507010b00215403410280300a0f0b01641c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 262376465 1250 262375215 262375219
    0x9030c0f0a05060f04031106190f0902012111040905100e071b02060f0307030e0712020612040302011103040c031707022d1011070f0509010e0a111c050114 68
    0x107801080400341c1c800907064000b4001d24225601f14008101035040280554200c001042040740004140c010380c0500c200d0110040020050f45000d0f0700080d22200ca290a000c21400d8200c001440c42e016a6000d10100d109400145440d40c3d01c92001d03000420040d41c481d140e04244090028200088042c1180b0a0095689200e158030144be040b100c1942c0403542260302110620400264404946c080c40c481e425035640442c2070000800c1c6039081c58400c1d0440804000018003007800360302e8a404459000311121038030381d01d0380d850b400e00300c2c0105040d1813160407900c400001c1c8001d12892080000a4070300a41d40305034050100300d1070708810704c21034000079003025000c070640c640101f202c0600051040e484202c0350000f006a40087c1d00000700c00703d4280490b405000d58100110100f08020140190041c080c02c00c608280004091740340520503000b4106000002a0007120b41f60000f6071080c0b81011819251000401010400d9640e42c501240d20ba00c0e1400000c0c0031a03641001c1d00c610040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 262377715 1250 262376465 262376473
    0x6180703050318060f07061a0301061d06040e01050f0708070207180209030f160e06060301030203030f070c050d060501240e01050a0c08030115090803071505070c050609030c0f0a05 79
    0x1aa0680d040f000800d0b8007403551045042c0f0500000c030b150600140f501c0361007140c0000d035060b1a00d2240740c3c0010002600c602aa02d403200500140c0006140c1810044280c1e244032101c0e55001e0000e03001d4640c0400300701c255405d0030705000d01d29100610190003010a525030f00c495541e0600100e0740c5001610460040031903100c580340341c1207070300e80c0241031250000c1c007641e181c403080004081c60003285d01101c0621660f8040c0400450303c40c010820b400800c100c03450751565240d81c001a94030300400c5030902c502000028480304200646034060b008041c0603020f1089a0312900300b203001000c09128501c02a160040d0510760a80805e45101c000310803501d90f0020f441121004480503006900c1940038840340c2d0355560082120200910f0091012200e030a02498402c403004103422004d9000410b241e1080c004034000541d03100a0744c030700e00c41c0504001074907624010110f45440421002508501411080c0185020301100811115001c58100c609404400e03000640c3c1e03404240c00075190b508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 262378965 1250 262377715 262377727
    0x402220302031e1b03010e0615150702060901200d080f060301051306020a030b0406030507210308010302090c1c0905160f180b060c010c120509030a030e160602061807030503 76
    0x1101c41c1345080c404001d00001528001d854120340707001029600700288101c0071651000629082c107140e01d0035224041d1942c1003117050303408600d00d4001d21250714140003100f880740c02502c6008485a50311980c50701281c10b40500c00401034030030081510b801c1444c001d03440028403e4101402241d0089206203461400b242d950f40300c12000350009200d2400b090b0711040304d1590b6a51f43d005110140d0f000380041c6c0f280741d1070002d441c0c104004591650000f1054814021301098114a2460460385c040e10844229030b90818100040c1c41880b004c002032541c41c607480783c003c1c2295403000c048188564104c0f10100300c03500c8214884c800d00c2c81543c6402404d100d0a1100304403040581390b80c04039200c0040f03410b031900000255640c001c44109541c0383e640e5420108142c0c1c0c040192500a102500100668107282c26225104e1058041740300c10b0503140d9a070440020b0b0f00304203500c82c20b004005541c21580d01e03400001d4503140b05441c007030461183c064520200d40d07404680c0c182225481401146002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 262380215 1250 262378965 262378993
    0xb01090e01050f2206030b090d110706050d06030f08090301050c0f0d0b03150f070e0613030224130602100e030415090b0a0503090607021203060105090402220302031e 73
    0x151800c0d20403030711041301e0340300c90740d005519009640155101e8101148039240c607240480c0780110910024041040c079810703c80c0041030120302d400554550303140c0070765550071203a030007400f8141d10341c0b0003818008000548014049040c1c050200d4440460092040303071030780c881c00907050249181081e42100c0c1000310080d810034030b500000c03649001a09580242903000c01c2a410a01c0840d4542c80d0070100f6020030100a51014852000510454a0a05114400d01c1a610101c51400001e0046d00c1c8161005015101081c1160801400c844043da542003884503810700e0311054800d0030090700c19550410701c078900b00d00411488280385802581401e20300088812044817909100080c4480044086003520001c0014000304140c0d803203c0381d803070502108043c90080300800740c10441d0000300d80c01940442c81c608498002c5000d182042c3c0740c0e00d640e00010001d22442c4100010b8082c00d0500031241d440007075151f0203c4c5d000b1400e4801138104200007500507049003082440c40d03001103200714924 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 262381465 1250 262380215 262380229
    0x50c0d090602061f030f03360e150d0309140a1a0a05040801150311181614040305060105041d100515060c0f061605030c070501090c090b01090e01050f 66
    0x6400704c113484000c51641c985660442d26849041070b00040d000b19819644100c0c00707880791020341120018000484202147e816824090f406810b00041000005c5500ba1814034002d60604400418055405d95945005030984015208210910708400001041441d1001200d0b04881016003a8042a018040080c0c1141d00c503505030390134004c0038040031404800034410400e1a9180b6481e404805096051903a80050918040c52140700c01d05402c5005aa01c4070303600d50005c9881b54514a890f400c1c1e00d05413120030038101140f4a6000c041000814440e00040d214100c80041d0380801040f1440c1484101e40390344000b80301050780c0040b50080c50082940d02861b80300344403400c1d65410307a80d40b0b00020b000358841c40d102507c69112080311103000c84184213440e008030301f03a02107488d010701207000580540401070101440701c4000c200901440800e422840310700782d202291850b150388a0b0143e81c020100b050900d40003415400c0e000c260a04040100d0303050f200000c0030f4100d090050410800a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 262382715 1250 262381465 262381501
    0xe01170720010e0717011811090c030c0d0c030b030f01091a060d03080a0906020417070519030b040c0909200a03150c110f030d0b03060720070305030a050c0d09060206 73
    0x5c10340d650108503a8001e0104001f0343d00038481c2ea0900c4001c40b55104118090038090620034151208105000250000740210b031418078103d1804150b010010005400403c860b01000d03405000e0060740106011041d400304010510a4a5040101d000300301101e55615084031002d80102d5511040302c0440c0c01200d200e0b83c000900c00300031885c2107507540d501050343c105034415180100c60080000010b40103002100141000759034403959155510700c440b00600081c0f00103080e2850100206042c840d45000702805041c9030041808400451301c0d040350540010042c03484c1c402c0e100d02a0301c0d8646440300c900006c0f81d0b00702058082e01c4400c0c01440c0000d00c5010700740c4050000b43c0008034011032041c07108218080c803010140d40c0f030304240026001070701e1035500180e100e900070708200301007680c100c440c280c14000300194121110020a20041c81d00701150005001e52002084118030640e02000800c030b91003181d001c0e2084011444401d5604035110702580002d030b080100001d2200911403511345d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 262383965 1250 262382715 262382759
    0xc13140f0a0f0603060e010c140301140607061103041e030f081302101809050103151e0501080a020a060c0302100b0102010b090f0103030305010b07120e01170720010e07 74
    0x180c10502c41c2d02d801c111001580708440460b150044203451a0080c8101e5821000d113040011903062060b4140605200502401000340019558180991100d4080c0c50149500440802500911b0b5400808980040f0f070101c0d22101c040c0b07008504040780c8440181320300d616840d8514812881401a11404401002241d8100300d603560b4034090381d100720005440030b286465035072807070200900313071008091150800c10312241030100400004103600071501c0404024840041d00d40007003004c00000000418002c01601d050100103c0ca02d0800f04140c000030b8800c03166101425610101a1506030700b040014000d03030445414580804810b820820388424148000159035003e4800513144d88010703100c03000341a07204001801016014800c0300e0141045e10401ea042203c0d558500c10350460300112a001c00201010f80d8900345d0055820400020030a020042549018103006114414151492800740c4051085060540d818880e400d02c0c2c44030744000d0406242410380400d00403001c000003003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 262385215 1250 262383965 262383971
    0x3030a1706150a0c0507080d050702040b190b0306011211030411060d02070c0e0c070206070602210a020903101527050712060f0e060f120304080c13140f0a 68
    0x30680802c0700140000d08035912010029001130074958a400320a4003e43c0c040e501080d80120025005001c0d40c0c2c0032981100c3c00b103070008034074009c10201d00074034008140c80745c05040003007810211000a544200d00c00c1e80d440000c5901c1d9561442034070081c004076102c1e4102000850082500803807040512a00904140c2c03070f11000818441c2203900242c81540d150901c1c41c02803100202400505400c09030720b02c441801c240b0103800095040c40f40c030300001c2186500150802480110007d080010040790b44292094a8043e80200180d400f410415101e4000c494013002015050b1083c6c4003066007440309402d4003800c00703074020642d00d15095901905034400030b03040d07002142401040c0c07080c0540c3e580d50503600000c078000400c2d902590072860741001ca00f0030600c00301951204090303010a08650302e1190b4441000401c0c8081684982c50a590100280c04949030b0400203118280101c1600c03401507100c046580d2404807a50070b4103003090540c460021800e446850f4104640008100d4800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 262386465 1250 262385215 262385239
    0xd030b03071404090323180a03081c0e1006060f140301350a0209010b0307020c10030912050406110102091804050304090c0e180f04170904050f090c03030a1706 70
    0x40d80e25140e81400081240d000080c600d9481c491211100800d15055542010483c10342e0342b00043d0b400740521012045001c94543c800f01d94880c0c00032042c0b442d0f0407054504000841040740050f00260060502265811240c1a00c8034440c0d4080050810242c00e4581180d007484450440c01010760b842d048803020700320304000d103107801105400640406400170111160144180728108905a2048210403001e1080001103170f0041412041d4420850300040300118641c0c00390001d0a41d0000a4054000c24070740c1e0030841e030480c00074002d1345e00036280d6240981c400315240b03080c0d2045490054201650140205100f0b5080c2c8000342c109101d0400e50f41050784840c00399040342d64800300d441c00115074100d81c548506140e002100c072040700e10700e0941c00d403030645400900d039203002c0d00003081d80051036401202003050005803201040010010b01c15420f001c1c1c40010001000da9116003140540c040002040c43c0010484d010f03000d0360b48801a901220318032008051800404e2203801c00250004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 262387715 1250 262386465 262386497
    0xb0607020a081c1805100c08030405010b0406090605030c060912120706140106020c10090b040f080106090e1b0301020904020f1801020706020703080c011d0d030b030714040903 77
    0x12000140c074800b802002d5881840b05000c00d159032000540050083c402d00d00002104040e07006803c0e140190b8906242a40703d8100729014200c0707070000380c03602d4404000d0004000064026840c03448040750103000780b546860901c0100c071014410540e2590042494078140d041005c0a81146070300206a08002407084d41142d080500c0c00c1800154604002200000c1028030300c14440c1243d42041041c000d9810074401a58135111480360070302c101100034420f40b40f00d214a81800c0a0121100c4070740c1c9030765403141184a0512280502541035080c0701002c21000414458810034a440100a045215074003030071200072040003a00360b0305075400704982540c5840d2800101a6903003800e510310381e03a0402505070304450f44404000760464004200410080f82e000810702c003034a8002c502c3c44d58801e8803000950042660b039880315007030a00300002114941003c516840c060303005460500c02070307040704105512403009000c3d448594a4102c100401c504065100711015403080c100540c1c51607904403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 262388965 1250 262387715 262387729
    0xd060303050c061302061c110406031413050d05030403050403021804060e0c0108060411040302090103030c0302120f040b0a02030d0f0b031912030e07030f0f060606050910030b060702 80
    0xe4001c9100010903040d6101c04000c1d850707000720302e260401c00019807580050038510980c5a50702c0840e18103038007994198041c0c0d01075200c0405140f602c1c0c0c0d40300d6940034041e028207680c0c028040341440c0b100006244500d9828801e0034542e024000d40f1298550400503561030304003034000e6003000400d000201c010384960782c0303540100900800040d070515003450080169080d9038000c0105800040b902c0d211039820110907900a41c0494001c80c809284411100c41d5000f03030b91000c1c1d8070103d1040000245508410401c01c224002c0d42920303240508013141d401140702c0d00d0356891400e42c04210400084e00c5503009040140f0701072060302e10301264025642d080d1910110381c500d2081e03803820072807200c4c94200004071500c60400100b10040d0425140c0c03941c41074500a01c038086c1608e032000840c8990050185102a59102070094001c28841c2050340f44502c1c450021210076203000404510715004409131758403104001c10040402d51139203411400b8000340100d45800c42010301080c40142d80d009 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 262390215 1250 262388965 262388969
    0x2040c050d0c21020a080f0612031809100e040305030c040801152c01090f150e090105010e0f06010f02010209040606030b040605010c020d060e070504090807060e0c010909110d06 78
    0x5030700c04050040d8068241c01100001e1280300401d07104100a4170074039000600254401c100030540380b140e81d5080c001c9100714000d60642d08407070100140a0042000042e03107404881c0c4140da40c104c1e1a911800c013280054224003581c801c80c03010380c00060020384114001c55000c41040403690601d42d65100c07981c2907071003104400c401c1010406081c03052510441509075008101a40342c0c41161200080c00c0403810107004074088039403511100700c08490960000031641104d0240301c4a0f5543c1d42c0b8a4200b442c1080e20b0305410355003000c0c0001010940344060f1809254004281c1c006a11064015100910407010801c1955001c0c42010303080e0351540b040303000900c0035407808074210f034951080100310bc1c0160010781c180585001c15001585400c924281c1e083d0340b2120014481c44040c030080d103064800d43c40302303074071505014200003004040c5004d444807a20512041c0042c1003100710107912014030800d414001210804100609007140c0c00030301038041407808d094500340016080006072501a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 262391465 1250 262390215 262390217
    0x1e0c200303032e080f1626010b0a0f1806050609091906080a020307090204082802040203070c02101d040c0c2108090a03051603030b09040b010f0e0c0702040c050d0c 72
    0x951103c00c140c10070701c046c901089030308185040e00c40c14039110010419960340c090020143c41e0181d08003886007588440700e1854010310b040c0d900c1c0e41c0c2d0700500251031410b001d95044002c43c1211102c00105030702940c2c0c02d1b40c00090103c0d0500800e04180301d424507005001c2243d074440d003a850020400584211030280503103030083c09843d03400e03006042c03030072900b03500c0303954018810441040810b802140c50b034801d00c140103582c0011201000402e42034012041f02030741c01440001400a02500980302c0134203180309842d045a180040c000a450152000d0080048030070b0440481860b803409602004208083d401d0440d582455501d45401c6403075000c401130700418020007142503098100005a5016140c03200406081403296402031590203002c000c10340c88105c0002000400d4041d4100e5442140003802400581c9000c2c203100c4602c050038421542582403005010403c10780386036450388203441d410324007440d044d406e50030300004060358506070f000c1100a0011040050081c01000f00d85001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 262392715 1250 262391465 262391473
    0x30201033c0c0c1109062103071e11090c071502130f0f0b0304080d0510050909121602030114070207081603020108040308071e0c200303032e08 63
    0x9040007004907034690b020441400844618000000d8801c100525004000d40300140301c2d886800c04504071001e640150302150800c0e0104140442000016044040c040c1e02d48003a044020710400c50030080c07000b406804400101ea10440d941403041e0040d400000240d0b00e1854a110390f250f8801c040c1100d080e28110f83d1300064064003100300c1200c5103020b05003032607001c903441d45003104480e90020244103920040d00040005403c0c03110714404d6800100392401c051141e441d0100d0000144c00160041e14850200440403d0402d8030020780c4041d100851071032a89407190701d15007194100d6100380c003280d00d03640300c04000d000c88201041e280e01a915a40007803014505001d03549042c8030003040301c844100001c0740e04002503070b07100300b200d9001609400d0404180d1074520f0111101e0362909041102080b03460750f802d01142e071001040c080a40650f5124601d0000c1d003440c982c100440300c50040d45a4018004200d031032402026600c00d644442c3d69612560b00404013244070442c203a4071014503500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 262393965 1250 262392715 262392821
    0x2603070f09050d0503092b030e0406030b071809020c0703022b080c060f0610110703080a050408070b040843060305061f0c050f03070b01051e030703020103 68
    0x4064201c002c05000e0005580301d509090b5901f90031080c41403a0150030410340c08092501921254411000703550805800c3c0c00c0d5140040c000350201c090481d0b00541c560200f080001c03103060703034403d0341c80148844000d400c1040c5940c0801040e00c440b502540f101c00701484540640c01e0b4a440c0c1e0b19102e030310a1001c581c4620b0b4540c0c030181854002400340c00a500303040104041696001400e1500d1041d50511420200c00ca80785036140c81501c0d04004d0659000080d1441c1298004024108441c2c01c10100c443c91502c6680004079805944103600b01988003c60710b10034220f00c00350303a141c0c0c0c4400b03081200c59010317604068040ba04002010700044c00102e50140461540345c0100c5e54449020348211041180032075841004020054030007007040a09201601000401d026050070340500340708581d22049141007050f2200b00070300c685c52145a18142254600380c170746c490700c2c000400c005c01401c0418610707001980945070147c40380c00c481c0b110280b90012404e44080c51000380c08074440d03101e00c2d85 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 262395215 1250 262393965 262393969
    0x1080f060106020a060f02120108030903070512060c071403030a0f1116080d0f0515010e0d082d0705010507031802060412030e09132603070f09050d050309 68
    0x584111504401600800c00501180d42c0001d030328100c40da400100017554046820a41c0000d006038800c11109141040000a0303400c000000b90001040807010b44504954400c108440780040f1403a04405070007820000300f922030307403001401000d4041d8012100154000b08500d0859000300d4920313054596850001d000c2c001c90b0312901c8101d000c0c944a440c641101c10040f00c0c42143d00c0440100b0b084800180c051081000d500f003000200c0700284240158284000f040c0040740031456840c0c0025010f0600300e402c0e28103801c40c1c20b0301d55045407000d450503800d40518085c01c480b00c3c50400405288400a07044c4141200c01011464003580001500d42803502c3d0060617a0501c0c6c00420b281c040408014000d81d80d140d0480b02101c01c58400d603000380200385015a0f1030003841c00ca075a4005454401c000a40844882d554500d81c0701c1e84c2282c000b00304000c80c9041f034565900c00d90500c0b81c0c040c40080c1406010310040605558181002d10f08250760703000182d4000d05280d03003100c4c181c2001c15030005074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 262396465 1250 262395215 262395223
    0x60207060306051311090d15050f0402090a020a1803050a1421131e03050105011505070f03020a05011a0103050a060305060c0304060b0d060c020c040615050a1110050108 74
    0x603020924003404100d00e407500007034480b4841c040d565045130b500c021003440b404603502101d00030070002e4011584d840a82c1412075040c40541c0c2c14581250074a00060070021390f00d491540320302d900130404202c80c1c5480407550020b40056540c6424003110000c94403007624580e5901e401140315900526880300d052405034813485510940950540c0181300c07040313205081e20740da410103a100850840d180c11141c81d001041d1029076000d0100c104920003855083c1c0c500319100303015240180003c1c480342e647c90f40380031040300c0010b8a110014409100000004d19800358012541c1d029104030344070708159803511804c40314914400d22445031841541680c0c2d5070940985544020b072908100031040ca19203505443c0d0f00010001001160300000060800245074001440044098414403648090f0b00d00321009240c084400d00162044045842403482e06000346d405642c547c112121448081170f08c00d48082d08458405014005555044405910204022650a0706a803008100c270b515100b040d0f820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 262397715 1250 262396465 262396469
    0x5011e0c0c02130c050d02040306020a11030a090902091f0306090c110a1101090308070f0218090706030c020c030616110303100e062805040e031c090303140c0301060207 74
    0x81c0595409400c025039195109842801d100b49008120300700080300440c0e440c820754200e42ca107184041008018850309602400c0b003524a0703280ca80750050240101d956a000b500c1c20b91001900e6842d003400403440c1a0058808400050840203619801c980b13131451427204181c00350002543d4500400c00e40c2898040c0d180a03a009040c4441002641c0416540382c900d409000b40c42c2100130501c0000036442405510000e41d0810034690300e038072980c5004800a02c80d120164420f84449507101c50707030701c81424124003480c080c0c0010a6141c0c5492403d4015110801c160b100354000d281d41465551014403c80f4070505110301e804031080f9001c5006442d16000389182b4540d64800d00800592030f620404403019110031812000127a56120300055201010600c410741600e01200322403885041c0d403183c20195001214180000c102c05c1600350307683e015108101000c44009070f000800881c40d030740f2045840b8001c1c0f4010580341102e010600c1101810f541c0603035000b00003c01006015411312407400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 262398965 1250 262397715 262397717
    0xd0f0b1b07080a0207030503030103050a0b0f0c120907171005070309020105070605040206070204060e09070b0c03042106020313050c042d0f0c050c070b1317070305011e0c 75
    0x290500044050005405070881c0103208507400549a1005402001840b00441d03008080320b1340ca6131640307445900c410130300c5411908010724074017140c080c81c1c42d031010b20b1058000710540c0e81019107114901e2010701e80500f200016000d0000d0114a416100030100c0c000e0003880014a005541840c00d08110f4900810150405140c14070a00040c2c0e4401e04072074415400000100b100e07191800000c0840c812550002c1d070181c5050000560708821020151059075460291500c181d62600c0360480d6104651101903650800c020a01c481100070711041c40e00e006203010b003030307000300c43c3d07980c100481e40240da03900c2c03040d09a03552420801108002114401c00142c4d4248400c82c400e00d803032110340b1441c1046c001c046041c6941c81e0b290b810036034000d4a403011004002d10140e88003001c054080d070312406481200b404ce9800200d02c41030910102c0b4284120300810b540d400707107480b81100d005100d008812a440c05035810020100c0c2090180c82c85035504c258040c6800589144a141200c0d1803404c980 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 262400215 1250 262398965 262398991
    0x1a090c0a05040b061b01020903150106020c09010305030f0c10020d0212010b07050606120a02031510090504080d0c0903050a060507110f060a02090a170a02030d140306010507110d0f0b 80
    0x43c0032034880b0302c1034500300c0d00501401e200f04008041214003a0186100882d014072540c000b41c038031400d844040c603040390290b03002e40c0ca9106119080c469007440901001c0c0c05540100400c1010348000310041c080080c5000c02d17501c0103200b1800c10b6003641c0c06a50310120350742e000b00c0c54025048169480900500c0f940441c00e141001540d107550700d036900101894481c0c4004104a406e80e441407080200e080e07070003425114900952103040c64401c1090355200e01c0d12020400125030341c1c00354030a41e0300982d00520b55034240040f03510341c08054500b0511090801c225614001b00081d0208100b48041d407240340003090a2a2003000182440804204d5404680c0641c1c061071041070017007041900f00c3c01d034480150341e64082201244c0e226586900088007241804141d10903840301003000c1c11413a100310181c6240d5007036990304076900b104034000036440d40c1c401c0001c034030b07558011001846114422201a842071110000003543d014424030b007911030018494a4500304454581c070306903c04010301910b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 262401465 1250 262400215 262400231
    0x2a1c0501150b0a1e031413030e010f080a050403050c0f03030109050a0612030f03060f0b1206060a08011e090216051513060905010204030605090d0e0f0105161a090c0a0504 75
    0xb402e1341e40c2c144d00081c1d24850360201000c0c1030b11a401507903201c00030904400d80b6041141105030a9030041c00190300142c2c016003500d50342d40c4540741c041101c40007a07445040136110a0324620081c480601304400f407103010084000f00007014410b03420884200c074042e60300c941c901039201e82072340c02c010311031403005242950512104100c00c80044955401d807801d80304200c080c00043c2c1c010501c5420001102070302400c00140981140020b06041504000c50482511041c01340441805401c0c0800086a070b01001130045100802580358a81101500c80d16172565480c0c043c0e0803039000c9103400b51181c040100c00c80c1480720411107445040501c1035084500d00d01031065404400c1070001c01001c25446003032a10500c41d094043c0e4005c1d54020700104070314100303501c5403035a8614511a0101040d400c00b0000002d1405100703580c0c1600c0103071103003442c0641c44006942d80d464405c00446440b04501c082c0040785444007045403103401c7c982d00070706030b00c1c200030b00308254007030282d01c0144683d05090034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 262402715 1250 262401465 262401467
    0x10815060612100512010608010b06090d02090a0915050403110a0b060103020901020106170120031603020705011b0203040801060e1006050901230d0e2a1c0501150b0a 73
    0x121034101c1410303081c1c5400b9869504054284480e142e20156101c443c00c10440900780c0194451011261050000c1107140e0b101c0342400710b075020342594954404031180c82400035080640700036a104543d1240010700700456603c00035a81413180102403029600c4003080201030700310250110000400b00240003480d400e40d98101000c40083c40613040540204003409664000d420181c090641e89120344040342103131a201d80200b0f031600618021040007401c9010020000080f02d0083c02e40440541200c4a401c205802079481841d0482e101c1d9620070016010078444c0580c403009559682c003642c0e0b02c0349404103040c02d5400941084c440c58451a040c01146d440700d840900454242d410200d458071107440c01a6181001a10410340700b1441d00051030180d86c160000b0308511458100812480701d00394001690b40800e0888200d0560088181c9400c40d0130a956210081d803004101ca05003000c1e4058101c0b0501d000b80f42115903a4503a2009105000c0e40c005240240c800e0240180c1410345402c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 262403965 1250 262402715 262402717
    0x9090c050f030d1b05061503010c0f05090f060d050a0c0e0406050f190803030901060504060605120f0603100f1d0a0803071103090402040305030a08070305070905120c03150108150606 80
    0x4520f000c1c072107140314001504c00f858400003072075038002c0300380c410500e4a44040c000710a00340d102c00740b1a5207429418103146020303106034040160a07644840c18401c40d0b0040c068444810307814281d203e01c0038441e1f0040040c1a0241c5845090038441c0465080014003019010000f1009050b100e0383c1000030074803a584640507158002c0130122a500000070b021013103181d0402c0c07a90130262183c00300104000060702e0540220301251404d0f5400c10000c3d54030310040f00c6600550100d940e12200c0307203021074403204071000604d402940003419110040b0030044020111090741c050030f44002d8440d04000c0c0003108581a1012665180f8041e0040c007031240c2da071075a2888010690410302200d0000d540010f002001500c1081c50003600071540c4a4990038443e6a9401151072100003840030b80018419501c24001d071405001541c1b500303003046040400700031202440100d030b00302d5445501020b0039503540030003035080d1410840250209a5050801003030400c000542001c1c0202d01d540288102c03610785130 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 262405215 1250 262403965 262403983
    0x20c1204050303070609150504050f2a10030605120a030306170606091e0c04090518030406030207170313050601080f0606010c02040b0306040501020c071e0303050c1002030109090c050f03 82
    0x28100180d046000c2c5061011203541487c0589040c0c80d1004210030060000350700504e2402c0306089134020014080c00310ba281d24500070003c0101c038100051489070410740100c8101d800c1e07904010030050f440d10086468060401c1580b4441c1c0d0004120006041c2c042c801c56004d01000030b180042d080c0700300341481e40e8010103007502c1d010341c030f880000469000000f00448201016441c4900325810412245102030304140242c0503080c1c500400318440b1a41011001042e007034250203035040a103801e40640c02904044400d0b83c240c0540d0150105109403030000718400c081404d00b280108c4041d082052400320160403010f0240d000780d00d07104100c90700145155224a091800719410121440810060003011845d140c05100c0c94050208003e819000f034450b1446d03210807905000d5032820030010300d900c0200740c01109282c003582400400d21030001010f034403442034200c486800903000140200c1c1c0c003d9218680c51580c2d41503100403c1041044107008280850f00e03007142d01c4c103040c0080e84805043c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 262406465 1250 262405215 262405223
    0x50105131104150c06050109020703080c13061b080c010c0f02160324090506090607140919080712060606080403120b03070911090a0b070308010e06011b0303020c120405030307 77
    0xf503264214503500c258105070405030700c0076092026503582e0b020311029401003801100404c04c100c1c0000d0101d4101c1c0250342031600c0030743c0c4035400189040301c280d40c00140f000c241c451400c0000b2030307280407a15080041034440200340c0001403c008450340100390700da150784034104540204000c00b941120143d4444241d80c0c012101c4803804003500f00d908020644409007555071804d21880700e090180200b00341d40320740c880700140c800c26940c41074111420301020008240d2081e0600002855003001c4c03212042050b01003c070820125161060b01d032800c0b803268400b400543c074009203c1c0400c4001d002d000010031960500c09068146990301800884402551000969139181c0024890740c01f00034002c01016542c004008624035a840340d441507001c643c0c96405050345000c002030606100c41218841034041d581d58040b81d08044000c1c0c91504007418050412820301210401001d046109001031403190320016554403180010b94103021011341c041121440512040002d5207001c422101c1c2a580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 262407715 1250 262406465 262406489
    0x30c1f0603081801020a0606060203070c1403030d1109032d060c030402010f0c08030703090c050a080312040c0b030f070f2d020a060203090703170a121815050105131104 74
    0x1080d0040b8071b4440754200c05842d903414000001042c80d0080005c080c2035001d070102400c0140c0700c1c0300102258000302001e640591041188580825055110114580d031803002a8508000100000e2610f0748908031100c6001c00c80d0b04503c2c0e280280120034000750040f0700980850314000d0300d007981c0e90000400c0a0f05114480c80d00c2203409201361070310602c059011101c50b4607410031060080040441c401c040761450961180403440e85800e10055048900d1440210b240c8145a5801d2419040c094011034a6980c10040401c010104c080a1403003041c0d45d10b188801440e095000500360710700703100e039441880184c503c003510b4070303c540043c04801e03d01ea9207004108a200c2904038500200c10030f002e00041c0c4040306203c070f0800003041c5041140c0c051035114041c4940e400303d2a00d548a200220000300c1c02d6100508202c1c8400e4218040c0c8401207008411a00d80c1d58030780040c0030f80b040021034042591140140018602a00b03403480405521200308044200c40d00412258410b50181e05092a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 262408965 1250 262407715 262407757
    0x7061409150606090102013e07020a260105070806011e2709020c0a0314041809020d02280807030c090b040204050a060309110117070e040e030c1f060308 67
    0x4002d40001d600031504001c940703001844c1c10344000128102e040701315410b0a04c0c4155051400c14030041d9510275800812000346941751a80d072010b5101508900300f201c8a500c0b10000c030402d0280b00d141c1c85503102c4d440b0385c000e07490011300060a410501000700703005030504ea0040d240c254401001018845410345003407011311032012039400040d5070b6001e080c842e80002004c41d210030000c1031a8101600c00c1c1c8482040346408912580c643c0120f002e05030441d080280c0300b0b020104243c0084a0881c000b80c9210717a0400d9940120302c400c0324488100d0350f91038036070092102d1090a280303130390000c001d05e074080c01c80325045503100041d280c0203115500d103494440d4070304000d035940c960403038008000044c40b003006182c0c0c91401501409a900083d140ca08070034200d0382c4254000e00c04084c1d61030020a100300351740d90b11482603d4505c0107210b2182c0083e0369001904000d1030400040c007126040500800f9618031f05c2e60106582c04000c1d0b4070341c101604041041002a0084041c1d840303010228080c507408003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 262410071 1106 262408965 262408967
    0x6060906080a030c03171e0c0414040e192609010c0b07030f0e010b0906030c01020a020904030e15030114010905010516020f06070614091506060901 65
    0x82c101d8600940040d10544100018601c00e08100c130f05845400500400b80c10225500600d0b4914a00d0603e817035042440c196600c01941251149400d042c0075281d005401d000400d07500440e10391944100003c01804400d041801804600b508c01d00340d0304040d0b0300100800c1c4003e0940d80c9002c0c0d0010700301c040c98101c612942c010703121800103112540d1010f040050060460003010341c3e41c80411740400840c011009200c0e0908000700729600d400040050004000d04158400d512079010302003241d8010852003c06501150b071500140d0700d500302910034580c240c100b030f64082200721010607c54092009503050710880786001c9100d0402c0c00056030141e81b540103240c0811000e00c0805440d48022500403030301803000d09018191107095000c01c0d816001032804030303103481e10340c400c0c800d0842d03c03c88425031216000000340011150003608021703c40c005401d0038041d50001910815503 = true := by decide +kernel

theorem cover : BRFrame.Cov 262230215 262410071 := by
  have h0 := BRFrame.cov_init 262230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 262230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 262230215 ≤ n) (h2 : n < 262410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
