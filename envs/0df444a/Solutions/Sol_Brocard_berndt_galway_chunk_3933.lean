-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3933
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:05:58.233729+00:00
-- url     : https://prove2.me/submissions/2c6c5c05-4f01-45df-91be-909bdc738677

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 707194244 ≤ n < 707374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 707195494 1250 707194244 707194259
    0x2070f0e060916020a0b1005180c071212020304060e0c0a0b09040c03150e04051603151a0a1502010b04050423070308040e06090702010c020a060c0c0503030a14061207 73
    0x41030000b900210310503145c400c0040344182074590701900b24011030340f125606000512806846030440f80c00f54000090401600922000c10f07191320aa011003480000c129258088520f141c442c840d40003004d100100744400c100b910780c0100c4c02a0030342c00640746820a0a010000ca00e0201d1160500b10101002404090b16047c4e000c10044a00380c00d0004160842c103024001d904410341141000707007010018031050040030030030709076510246d031000a4058216524038000e124400750040d689520351510701410462070b4500e0034003000c0038122008a5a0f160284046041006850f0340035518100c4200607504060040c284500e8010441c00d031002e01c1e02000090181300c1004216141c012103601100150400c07004000406007141e0300b1006050020402c00102000b612032019a890425a03091258010418094090300300d1000540b00003031030825256000c0c0c0d840000c00754000003041040d640015030000309208020444a40d0f15034806003480007080031030781d14070001d9010884c1040b652 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 707196744 1250 707195494 707195521
    0x206010306050a1401170613110402030c040b0a02010b090a090305221502030c0c09010e0f0a0204120b0412050412150f090506040224040b0f090d0302070f0e0609 71
    0x416040c030001103440003103646504e100c500380c100050400b070b138401a00d040c00c001c00600707400078403410450445120360f54822078803580d00c000715402150080b00113070841f500c40081d60000d01c946002c0c00d9030b079100070340000c0c020500e80c0b0b50a41302e8030300100441c400b461144a04208658075032261403406c141034034002400e0350006001c070070b098061080405c03000140c600d21500000190000d50b16048141300301c0d82000d41440f003080c081c911401c0100001030403000683e810542c0f1020158054840c0007801001c3e04c5240c01c0b174198891882841000c100c10755400c40e00c200c0c00369105c4036903c90640800c544501c940c2c800c911840000c544280c1c0855180100c1c2c0f20840d140803000100d038461207025100f0307a0036500d0140c0b030a4012030b04102c15030620218060f103c1d400c0b07006200420010483d01c0117203000700d0003030200540c00443c00003800700030a02154500d100043c414090715605180003075032180c0303034003030400300c41c22480c000101d0054281c80e03a03004603801040041c0356954a08201d081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 707197994 1250 707196744 707196751
    0x515061c0e011e1820010e03030f0c07090e070608090a0f08090103231501110708060108070909050703060504020609040c201b090619060c1e03020601030605 69
    0x50a603074045008a03050240b060200303100344100c00d802120b007000382c1c603c03c84040300c000d1003800e5405400c1d41e00103501c1300000c031081d506103904008558001d5004843c511807a1031400d40500c400215244501ca07640c0c09401c02d0100d00084503151900ca40810f02071311400e0381a0030540d8020794040c0042ea0049241a40c4600c107032080ba2403601319138030b480ea000385030030348180c1d10040001240c40940d6410301400c401c91021001031038181c215502100383c101d02c0100481c6138117081c9900361080d03a20401c082010840307140200c81c889610341180d00d444203003c3c030549030303140b00b0705500003207075501401503094454011024005481c9591501c101070240244100d9010300e0801103040c2030f51701c1e807141076003c1000f0b69030f6540102051001c0039401d40200c1c02d800c40c0c0e0f40450385461584c0d5109001d0541000c0507200741101782c036a00e010074034000c0c408450460100181c200419616070103080d82130807501130014110340d42c5490038442c00c000600300000d00160400130043c4042a61900510741 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 707199244 1250 707197994 707198047
    0x50706030203060a050a0e07210203040f0c0b18061308030c071d01030503041806180e10061802250f110105030106020d1107050a0e0f0901021204110a09060b090103051506 75
    0x18407d004404105e2f442258100d0ba1b0381c0b025110740090007804403c51002d41141c10b40e1078a0b00caa03151085182c10014400c05100384800a505020210f901e1607010007052220200d80e180c80d40c641c10740b51150a5402007141803105901000b089445015025040325006030180d840c02e0b00341485008145040480080c2541d1502000901408500302155501d54621800144a0b800c1043c4074104410101c0c550052401c0050521000c40c44030b0070f01040045924005940f4030050304500c001580040c070400100311820280340911013038242c20043c4500c625100c2003400c601200645070350000f0701070f01006a110014451640b8060404180480303400310440ea825540c40000900d041c0341908030032300380d8040b04144009401102c89030360300858200025410700c59968210f4808620007440a04158600d074400c603500e484485050000d0407084038144201529003422121035404036490a00207481c00b40041c01d400079580c0040d0f840c0030010450f134503250340c02d0881c94905400c21503400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 707200494 1250 707199244 707199287
    0x1204091406100c1b0602061e01180902040f050108030c0601050306100e090703170913020c2d01060905010303020606030f060601050f0d02030f01150f05090418050706030203060a050a0e07 82
    0x80310b104c1108141c4009045543c01042d85181917076100c240407070040e45000c0020304900c010300c01c0800c51110303008503403200a4005018100c60000401600d41180ca094110f4500f90022501d210040000c140d04240501200c2040e40d0712802e041e0f0f6035108130343e800380000403820180440314541c0c000ea80c00003002000c4403549070b20ba440c1c80000c034800754141102120001400380081c20003801864600c0e90010046081ca1003030124252280900810030007001d01100540c44421340c03482866811040000082020360746589a840061100380803da001d4410381c40043c00518000410046032a105030240c4a1602d03480c00540b029040300415403003566041c00740b0000c42442c1e01c06035106005100c94001154900110403400c0c20344001910700300003079001c0d4100315503002011240c0386441554009000f8006c5404c4c40807000424000500314090342e007000070072543c90b030040e50041d5001c0b1003410702c07141c0d42c0082203510b4119104280e49184500005503141c2e0107881a8580090301d0101f14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 707201744 1250 707200494 707200523
    0xe0412051b030405040606140a030c11070602100b04091505061c2a0b030606030406020405120a0c0f0e0a0b0609091e07050306130905030c1204091406100c 68
    0x2241c0d03100d614501003590320104040149207000d004100082000b82090030000c1c204140e00f410511581c40c2c2181499254500310b0780c0b603032080300c010b038140c00ca8006442d005030721500000d40381d041b400c42c02c0d60041c4c2026480744051809104640c1c01c00c5d8054103c02044c44e2144d407240c06090010308a40e03011440940d207040041c0540c051046241c441d1031000890400300c100c1001410a07501d41c4559185001ea06003c400b100e80c04680c1c015000316100ca4507942c40d071803c040a07105980103260409d80a6000b55501c2e90000ba10010301481810b03403812450b11041c1d40c01d910541e912aa9008041c40c070080340035640350381c1c0003600c64840070f041e0f549003092000210303058107015140c88850040543c2e02c01d99000001d03e90b0b0303411180c2c4e460a1031460510200261640b83c41c15440b04403250b403501c0d0034040000401c00c849400c00048241d548a40c046081090141c009200314001c440c1000450340b03010004c080200d10481d8010311003082c50713204610441d40b02c100313040121b8060a180250 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 707202994 1250 707201744 707201767
    0x5220b063f040308012d06020606040f0b150f071b0806150a031103150106120e0105060102120706021c0911120619060e01080d09060503010e041205 65
    0x540498104928000452107440c0d88000660140c0c0d006400d48038000c0a1200003640030541030704441c405402821400d682c1c0c03c241c01d40201e064054440705008640010300c854010441da4800c3d01d0440b800c0181c41d078250404030607142d50305101980143caa00b0f000781007446500182280c000b001f00072a042c00059520890035400d4034500d06c0300300d0001c2c1001c00101008000ca5548410038812442c0d02107040004030304444140e01000b40740b2a9086d24168913624200815844805101d05005503540c0d54203019010320010340d0100a49401c040500d0b0300c00708140280f41c041d10040c0e000f040ca51075410a050081e80049400320392454003004100540071651b0312142121280c007400280400051a100c01d62408001403c0c3c01a030a400005c6c104980106850703a00c04895417079043c080903d410944001d100d290400c000f90512007002040410000810286554450700c0d10307928113496400540721404248111240c40070303c034000400107601480182d03800c04041c1059030410040741e01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 707204244 1250 707202994 707203027
    0x1d091603272d0f0326070306080c090411090c1c0507110c1509040b0a080a03020f030408030904020a051207030e010c0f0203070602131a03010f05220b06 67
    0x3600d15010a00a00d021030603030039100701548102e4481055554041d81d03494a000348010300107418014014041003004603984032803024440541030000040c0f40010010b0010241400303a482c2c54403591807086218100030380a64042c5422040300302c02d010750348080203401a0700500c1116581018804980c19001c80080810407041120340824549450300009094070917482d0360558561051040c9002610741ca8046000c100780c602e000e0b6583c04515000c9000791941c0d034810bd810036046000001c1c1303042c0124011240c01c0c465800c4d110740c203220700342240d07480c051406000c0d81c50308100305580580c81d190b0300034071014103035040050a0200300e05881000c20303000c6030141c1c0400e0700c400068244640a100b0000307809003506106400c000726601c02513490140f000000c06071b1b6030008403400a04040c4c204034000b819560040d400442e131a0726072200390340081c80340b8185a101014003054625104004070214218150400340c80c00317131a50607001500050844a0f000a03042001c19640714481d103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 707205494 1250 707204244 707204321
    0x50403050d02030c1002040302100c0318290406270e010909060b04060602030d0e15040f0b0127050a0e060106090f2112030b09071d091603 61
    0x10042c1d81c480242d00d180174202542411034403942c034410441840180d0b035981d40c0869030090381c645440c20102c0ca00d02500d01d4104002d40049000503e40c00150340304021800c0d980c0034012110907110a01c000d15000c1690045004280109801179000305110b400155000d0f041004c40301c002c146a50758003490010000c0a0700420b44164682c1200340034050b480c042c240c4201e5003528100030213454024020744034050301031070b4456503031034034203000781c02e001040320b0030608036001c0c0d040d949400c1a152040320403d61400446500c0b4004000040c0803940e4030980c152070000403406404980355012400080800074607070700c24196101001d12204504000c0c0d81c0c0640354a4903020780a505001115400703101da41c0c08601d070001c61104145001c0c8900c44220038140d4030488495000440c0d8005030068140c2018060304488140104400b1503480080c42800440e00403013071090101c10003c1c005906012640003100300c079a0840107800034442d41c0241a09101c00c0c1c0130b100d0b10040649449400c030ba598 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 707206744 1250 707205494 707205497
    0x3060603041b1d160807030b010306030c260105100306050910050108030d061a04030210050408031c05070203070b0f060f0a090c0906021b0d03090504090c080d051810050403050d 78
    0x103103888503018a1007039005402200845101030b801d06100380082420400030f11b00c00c20551600b2552016034042c0e00250007855012540d102140d8582954400c0c80071920070b21420100081c0020000c2003043c81414040c1414a060043e0242113407030f40001341070b000d04082094420100704550101d124031400780601100303005140da480c81804840c0c1030354002d401030f5405540180c2c2c441c040030710f02411502229415914190b0034000c0d04020b403114000c1d81d00001040c080024401a002080743c2014031781d80e61200c080040d511018800ca0f52800790a9004008105040206805648100c0031030703032140000705080c03100c03442c200c04180100c0041c2c1c80104102d455070051228960131444a40c050a098130051200c601c183c1c1c1546400a00f46c481c3e10301031500c14401400b8140319410201c003514000d401841048130502d054810036455109005840c0100c40300c4c03000f00341c8100c048031080009a0401c1e0309468080041045034207000d50b0741411300c02c003000f0000000700140041d0034107400c1b0303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 707207994 1250 707206744 707206769
    0x509070806031015170304030b0f0a0c0c020d03081005030d0305040c080a171c020a0e040b0301020a050403020f041d0610060c03080c341704030803060603041b 70
    0x5410306141c28141d404003ca00f40c1080a0310751070901d800c01840444007041481703004c110000440c86e055128907007002e84400c00400410070703030010035030245001d4982038504000440c420300c800c44001005c0c40f0020743c0303c1c4468a242010034442c1464a42001c660f910700c1030425568030000f481c00803000400310100c0d80781d00401061050952580b0002c0c042c0a002c0e0101100380c0e0745d0003050321003407142c140b008800400c100c403078040e80242004290350355070011035494010a0000d02104100c0814074400c1d410011400302600307060080d5650388160f6150141400d0031607080014010240c0500c40d0000d550f90302910350607100d0303040c0c41141003c0c0d0700500414209025095a000c8483d0841e100f8004000d24100021b94440701007035210340011921074840e170011031028030300c03644031809035098409103c114000502c110a1008554407a44040d450111034441c0000d0a0245110290804100740b00144141c20000000e59006100d001c4030711000f42481c00c00540b0b80700c00c2e003140075420740 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 707209244 1250 707207994 707208001
    0x1a0a050f2403010507020a2f1c020a0605040510030b061b101802130506031c030b100302040611060c120709090e06010e07082502030f0708090f010504060c120905090708 74
    0x2901c81c0b840d0010002e01c0100300c2311846440d882c00750030f410b06880500400300020500c2c42c2c81c1104003e06075166009061112050703a80303e0042054200340100303032150500111007010b55000344195000761002500180c28007047c4a100c1d10b0003101141c10410314054998441d040e04905e00c5043c210611038183c40d000480d4900501900895281204c64540e1401050000c69500040c09002c10b29045460404070058004220041c101005c8616000354440460b84c0e80701d501600503000352003855450240020342002100d556a4082e034070b1006ea102c0c208480f00d500c4ca80710890070741c000546d0909105090b81e88010000320b0381c12000d00c105641250006110030200c1a00650700306074246003581c45804c00010881030b14011441851111142c110804a510300130300070340390188158035640e40c0b42c1c80d00e41403801d05540b101e07400a00c10340044000c0c0880e03601480c00da4082e600c281c0e58003061004a83c0e1520b40032619400d00c103040c851004c0740000c0694508100340d00c14202c40c0c0d1013610605 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 707210494 1250 707209244 707209253
    0x507060f1b0206040f110a09140f2202040f110408280b1611030d0b03011104180c0c02041a0102070b091c1506031a0a050f2403010507020a 61
    0x150760021020442d0032071024000072403109000c0d40c0c0b942d500b00811411141784038000415a04d101d40c4241e201c2e50030300300c140c10380c0a141003e0910401b00c010030104a9586c00404444c000c0b401041e20300c4d50035008041d08003500301079110318111a281100020340341e4144904407004d821542c001486584903500f110710f806d581c004040190b441c6c80c4c004029100d9039030b0725000040c3e401130900182401c43c07240951030340e10410144c01810134050541c0d039204414810400a49000b01005000c0c2d824606520b250700e0801e0200d0f01110011200c0450201301880c0c800041e02044903220204414544a10090381e40c1d40b081c4c2c044640c0300940c0744441380c460300c0068204bd02ca40c0c001860311105008032505501e6101c40101c80c081c00345007a684504107490040c20010328003004540003490403c02208000309074034070a2115455081c010010741e110010041981c40413618600087e41c05800300300c89a80e00705e102c01c500d211080350700078209001c2c000300713003103603400c549120060f40f00078040014030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 707211744 1250 707210494 707210531
    0x903251503020313030c0501060b030a14060d020d120e031515090907120501110c06010609121203050618040308010f05030328050403060f020a0809030711010f0507060f 74
    0x8403054201941546011a810002d9188808003e0140090340c1c81e10302c10050203600003000380040029190700e03424401e010100030701501c5100c5c1d40c425892404108980303800c19459501070b6005200c0d00d40c007a81a5030700c4042c40100c02d440d00500c07000c003000d0101c5503001e01100600942602c05032034941f40042040c0d49080c501070229010f41c00d08814801c00c50000304d112002d84016001200007078015141031401403510300c0e00d80380300d0a000310b21180303803001c007003465412914265100603400f030321005550001e1010401c024042c0315051002240c1a01a801c00c1b45d21504c0140880e50b007218404c601004440e0403503040303000400d040018000d40000c1032140b00600700660046007004094112032100d64501d18188100810307282e43c4400701c600c41e104403406175134450130501048010b0710550340650040c100b01404190707071000183c074850b40041030300c4580790003000741020810b8050040d600c0c4921110f01e01c080140c01c201600c0401c40078081c00d516240c003404000341d40e205107038454504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 707212994 1250 707211744 707211779
    0x110a150c0f03051015051303050106060905090c0d0c03090807030c0201020f070810020c0307021503060907110a11031e07031406040c06080c0d2d05011a090325 70
    0xc0c1490502030006003c1d001c40a013064408140c03000c00f540307607241d1301610513004010300314201c50000d00c000300421806400440844600e91242a2030301c2c3c035042040300d04081103075100441d6005004039084801d89412012010030182000214002540c40708141e84d4083c0400b03074082042240d180085590400034104218241c02c050008241400640703a00d03080e1801c40e00c035407160080741e1015002010320032250619801051500c044141e90300c4c90885400844111b1311030300030080015050750244030742034403490400b0081c0171150040c0d41d80750022003070890358542621034000c1088440d020380f400030034407041c800010720800d4590319104d80d841000007002c0070960400010b0100150b45404d480c0103803400d40c18505101e5883c1e414000342801501c1810990300d04010035841861000d24a1505d180f0030700c4e440307141c1d10301c80500320301c25140b080c842d018210800c4121003942240b0100542060304004068603a81411078a039840801084c844911400c50702d00c404200992901c0304007a00b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 707214244 1250 707212994 707212997
    0x50309100c020d0e120a0b01090b0d03050702011b06020d09060f020726070c090b090618060f0402041a221202012d0203040602070b03090303010501110a150c0f 70
    0x1201c07080c0c4002034031011603980c6081400b90002440240d640c590a201390014820021180703415017609055103a47c10030300c01d0003400c91034544034000c21b007010602d0305103044e05a181c4074500a502d07801158413100002450348904c0640502c0c900041040c00202000440308a0200e200a0541030510481d1071b1140c00055841c07040000f64000341081004414210442d81112065105400e00214501ca0b02030000d00a40800c0d002280c030010b203074841d5174140b0007030300d44201ca0fa90380b034284054200e81c00801074401c40b1010014081d0314040002141d0120054005402c2039a42d0000410641c4003c405006960300070692440d607d4458080d040c54100310008800c1c12407400c0c5071144480c4030078001074100a034441100d814a5401806521400c0c5040a00349507400d42401c02501e94019016860043c042c03124005075681d8031070140e9003c0c5c0100c4003c0e601d075901c0c0c10010b6800c3c014000408842d03014410a000100700d00e11a40400007401c1e0b4000700c0e0140e1015002002995484040700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 707215494 1250 707214244 707214251
    0xe0708060f01170717030a090b09010c08090301091b1409040f030c030309050a0f0209060604080c0609010917010f061d0a0b01110d120f2f070f0305030910 68
    0x7a0440401c1c079640c111035035200d000a1030107203150501c3c03c103d61038000d1010703070200100035600d00b03c0c000002c0480c181c84c1c0d40d1340315a454032648000168880c240d00d0b540001c16055103a004203803040300800903454000c000107408003440c0d40c2d0610081a490590f200b0f100c200f0000c00c41000e465840540d190000c0340c420a907403134659903a9000d07102c2c0302c0002d0200646943e034101050b00980c400a02c0c1e9810000329003100000385406c928408503401d04138020b010744004903003507007031003003d0700c0541340400064110358100c0c40902210f504600d010034108941e0f1013000951403070f000580720042402c032001240d54a4030404600c12f03603010380c5c00381c28440015040c103180c3d40403950a403500b00420400c08036000c400800103e40050707600202c031004d80240c0c55181880703604421400d010f0440c00c0e800b408030024a0340c00408943e10151540d1507500c0d10303088040d04455400c1c81006040c0d0655030305040441a0320345110700e0703651f10003c8021075000414401d80e00020002c541041c4841041031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 707216744 1250 707215494 707215501
    0x3210203040f15090b010311030c0319021509041d01061d07050a200f1501061b050a0c09050a1803020c060904060b0d05160e060304030f02010b030607030e070806 71
    0x3000d00090048003d0a603584260710108602c000d40c10901c580e5410414581995840c4c2c00c114812025150015100744680320240c401d5081c041481800b10360364210540c080101a02803004890b010501001140420000e14102b41c0ea9031050031011401c4c4d40b8000d84190f502450a0f0868440703800c00801c2d65071203003210b84015400c020302503000045107803403900d55590b100c00742c500c0719000085240b080003803080c0b08802080013858048801d901e208440f504064003010f40126079080c0100c40c00070717001c28034110030b05032105d00c1d14140c54071800807504900300c503071110404000721341c005e2903070b01e9100d42c21701c00079003418001e58a2441c103c842513440c6000ca9a00a0764508409101c14000c034004603410341036036590f034000070040a2502d08280c0da4400581c00400520084459140c1c1422000c0d50032403041c0f01d2010550f10301c030081d00c41c2d403454940d40c4080d100c3d5461403607514110b41d240c91140130140c4080c40034a00400144e203000c1500c0d080a50f85038145240758005102a50014041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 707217994 1250 707216744 707216753
    0x10c021203060a2610050910020c0c01030b12060a06030b09010c0f0305060a0f0308071b06090b0d0204030f0c030c081209210303132102030d0c030e0a0321020304 71
    0xa000c1244c40700c4107084603440e4010526841c120124820820394010030880e202c1d085207980280b803080c9540780682e840100c100c00d18504a008600c45a03d080d0b200094880880d4007903444200d080070010300346021000100009454030300200d81c40008940c46a03010000c000a048125800c04102c000900005120940c01000803403601d210030101610740000c01c1107130b03d0301c3c3c503170a000c5e0070900e820418007601ca00742041aa0700c401001c94031070480d4107900c01c070b843e503a2500741e0a507a06655811030140c50044011099000a0b1445007a65403c21002002407212560364424070702c2040b0041c4e842d461070038043d07560740c0365602c40c10301034219021a418050f100030859254000c21104580ca410210030080444c1d0309080460b2030078030001043c0651010b007440811180c501c25401e6000c00b10000c460310304060300400c110800350344140440c5000c08244e40003502035031010728001840f0320300030113100d00d412100401600032449480308201107110220560012a000780c1c415851400c2c590748 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 707219244 1250 707217994 707218009
    0x61d010203031f090213150c050303040f06180f030e09100e090f0f211603031d1902030f0111070311150a0606111b0607060b03010905010c02120306 65
    0x90300f910352500904100d9000b5844010406800f07440c90440d200c0c9040600d4106406807801246003c104a841246643d44142e02c1401c10701c0d4020003841c103540710b03a81c41580d81128001c0840700c0c20b07118828000f480c5c210342c02c0e508986008031034040700b85810f070402910300c1e001054018002c4101d0400c00121303200c4c05526004071b46d050003064040341d840d015600e0078800540000503e501800c0d0100c100d00b02d001440c01c041c80e5010f026180705c0004000c1420192040c003011002c07000200a5507030109000ba442402c0e5070a4040d10501c0c215562843c0d076081500110300007894449a1a1000c25401c0400500360341c118410005c00c00001410305000841c0030b400e00003000c00800c0c15202d00c0b030714070a00441040d50045600c1c440d40c2e041003002c03c00030303028030300820380003618001d9812000703040051040d0b40b040240511b54425181102802001d40c80100155551901c0d021846120b45003440f8101e005402107000141c500031210b070080c104000000086809a03086c070501c4100d80d225417 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 707220494 1250 707219244 707219251
    0x405100302060a0f03020d0c11190308060d02040f0501031b0f0e0c0306010516050303160302031501030f14010e01140102030a02150406060506070b0f01060c030c080a0203071407061d01020303 84
    0x90080c01001d041108801034440d0303480c4400ca40b8103008e20100303616000500c14074604042000e94401290800780c0f09114020014082c000481c00c0707001c40e0103070820500d003070302e4940040d00c040f81252924201d0010b07540281e208485a802e000755020081c3c0b052007444011341111041c8145003890f001c3d1500c031440c40074200500c810740010100b6003c3c1c0c016002c5699040c410a9400c0c28010281401601c0b40c02c110369150b60300707054504024200303200b4400c4900c1101c04017482d016440103c0011001860012040e0081c1da5031a008454034075260340070103001340b42d0310280e0099981401e070000b0100c0c1c02040c00b00c0c10740d4800c5c800c125004ea008035402440d036007504000c0718981e80340d040050180520741d010541280000600c042441542c059261090041074041c280703690303881000700c804c1d08504c68042d001492640c06800060220350040904c406584100e0303050401d280c442484140058148041035406050100720703c50300420101c101e5041c01c0314018040d0744880020352030b1f00c0000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 707221744 1250 707220494 707220497
    0x91608071217120c0c0c0607030f0f020127060f1104031e0204110c0c010f0507031101150611010e0106270f0c090509060904030f122301050405100302060a 68
    0x106910380c002440c2c080c2c07079020340c00080c5444036040c2a0110348490b40004140f0050740a0b40048030b00c6403c2a070308940e0500e07450b69842128880480341201c00c0e5641024950455484281400c1045011501c115031881901c1d90316040c10b210b031810340304440489074803a001071704140c4440c078056049000d850442c0c0e0450040c00410300791a130b041c02c41d0760011000941c424178014184003040702c11005030081103003400c2220440760743d10f8019220f407043c00d9960030021358100114000030380726480302c1c910020700c074002092079404a5541100c1c1070681c2c0101002070710fa40035070700f1a00400d0242d565810201f038002c0200c181046500710910503141c00c440900c00102e0380941058100c2d41c0003204c540d6149008100c2d062104600429034801341c45040d00c80c0d00c1c4403000c00c01624100310614011580360710f840820314201d28060741d0400d1002e15600c3c08640d215071030000286803d0300416950222010140158140b034104070489201501da02c4690620744028801030315144112000d94105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 707222994 1250 707221744 707221763
    0x91302060c01140f1b0c0a060c050d140402030613020d050f0303090d0503130f050f060a0b191206150e011e091802010e030c040f050106080702030f0d1a04050916080712 74
    0x1b4400d0b490325094064038018440c51034995210800f683c4a0003030450804120002d010249040d51039030500c40d0160780184d410341180c00824052a01c0c40d45a4018510161501c0c6400501d61a8030b801c001c80741c071b0800b415400020030450141c03801d1180042158850800b64194240203d4181c050541554001c05010b5400c1c90181401400c000c044d205480390021241c1d985002070704c3c0703c081c055004030b0900498041104000303041d01c03240d0100a8a00300c030010405541161100741c050b204cc2d21050307003070140b1203101280e000480d0582d0b601a01300e500444601580000400520504a9000314416880d000318603407111f0000c07041440c00c030740918004000086c02000242011078400b00d0640c0645040c0e8040401000b0340c03c528102c1d603560300c0d1004036a450f4041a80c50b4030412000c01005a810001c140c00185541e0020008880945a000c0c40b034411802240481b8000e862030038055005400072040b00e0a4803043d0805040f4402c043d120442c50001d03050122546c000c07000700a400d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 707224244 1250 707222994 707223007
    0x30406080736270c05040e130c03120e091501050913110406020a1704270902100503160e030d03020d020904060303051e031302091302060c01140f1b 65
    0x100b420012028010741080c0360199038201c41c3d20040c0700c02000140078018200031104d0720f0785008074192011070308801c0c00e0010558420140e03c00350600c42c00d08454a03c000d0030040081134a01c0600018145151a0146038140500400c00f24000007000c104551030b19104074501640e008098880101e000e807000200f800f102c030ba0b1b480c00341000301d01510082501290006a160340022a81d51060203a41c0007491400080180d246611441c02020712444142c10102087c1e0741c203c4261181c156040700004009000c0e90016450741d21401071003000603400710030f03c507a2441515021640f51410305103030181c142d455020a80300e12900d484242171542c0030980760b0310a03180c0e804440c3d544134000d00070030619899140292081c3c1291400300e0003c0140c5491041c0c92840b41b040b41e004000840240302100026400c004010f50300910700c0c03c0020040c84040c2c0180c541c00040c100510b8204008101401e0000e001500200000c0030042c00072001000e00c542d00003001102204001c103190210355804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 707225494 1250 707224244 707224337
    0x309050d0c17100e0d140a0c12080105120c0f0d060e07080109030f261905010801021c110904090f08040801060501080915010918080c0304060807 64
    0x2441d40c1c040a49111071075207112030040c0224200407041d402400c10405200958921580c80000c1030413140415180d0700700803d400001e01c084e0116075120310300108183d01998407a5072440800c00c1c1c410104064000500c614904402c50304a8900104002c041210400000480b0184003e00150082c2c1c035001214050260542121400d1244241120502c0341d1b0351507203500910314080240c000504035045503500c80d11a462601c1d043c104c105485d080035070109052011401c0203008016210385d0b501c1c10300740e25000c40c02100d00030214100010307100c90102000388a60011001003646c5640f500340412000140a01a210080c00640b40010404040c1c40c049003c401e03104000f801500c40410002815041500154107807070003a41c0d01c540c1501d5840c0001d564180b00b07460300e20500408001808000450380c806900e4014401c221501d480d0151610b082580c810603282d0400d030000601403103a40c1e0030140c4507800c40352529020b140c240c011f20403c04003411001a8540116007409008900c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 707226744 1250 707225494 707225513
    0x170c0a090905150912071a090601030302121309050a061a0708030109050403050c0f06011e12141905070306110306030a1713120512130e0a060b03040b0a0510030309050d 74
    0x1590100c2da40d9104c2a504002c0d1107c00c000140a00d00804074000410362200421401d040b00e91507001030075140040380f4089015040403202105003c12610000b85950660003001d0150303c001e000003c9860402c20141e60b000281684000001c00402c4141c001034021800c9070b0469500b42c5002032162181e140407200c0c0e2099030398565071445010744580c40600007261150490f00322103032220400590803548101e1004910506031340364131222101c00402e00d804052900181c0074019916590900c640301c904c03403001010169040d52101205008000c82c2d4428900c0c424a500162425840c00c040080d0740c80400050003044500303c5400d0880c09000002501d410361854640b050545455a500c00040c03140c0070416034591041c103500d040d601102004665083c6030445c5005613882c2020409565050f01400d14007200d955103500180245184002e1801107115521424003030802000d2101074030405480c1054440140f20100000307a040a16903044910503500304014807100c1c00c119840 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 707227994 1250 707226744 707226763
    0x19090b0f090d0605180d02070303122307120b061e0a0207090f0507200309010c02030c0303040305010b03120a0206041217040c051903121404170c0a0909051509 70
    0x3c241131100784030420141c0404558200e8002c000c8030012001440104d03a40c101c1c1d07200150200706501598200c5100c0c9403c01003c0f07801282000c08078100c0240e08a00d42001180e40780000b40078002d05480980550160310101d03c41100d48504208819a400020014030b40220f180c0c5000000c14900e0b2500a0001f04010400400100302c1e2201d01c01582d00549000c45980c40050007040030f01e60380369a03003030180401d004400010f40c100110600150384403440388000740c0c0d06120350907105000f0303030b010001000034512a20001c50351584100906180c2a00c94151a1040f4814001c06000d00d80c0050207690007500020304d040d982c250403000ba9582d91440020280c103c0d00300c0d00700411301428590820455109841c00c03c40c0c100c92050300b1000c02c046000041c2511454480b45890510a0070041002260300c1400c2d4030f49a82c1e2225036840720a1601c0b100c1c0242c01c030a104042c145414a444001003008207403d21054005035a05a10b0380c1111400180c0f0704a040c3c040f601d502d2080020111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 707229244 1250 707227994 707228003
    0x90610030518030d0903120504150209061204060c03060503070303081b0d02070c050a0b120c0c0c030f06061302040e07140c070801050103150b06160f0c060519090b0f090d 75
    0x60301e204d104140c9001d041106410340214620b402c03a5030032400c0a1003120301c82c1313401600034105404079400520195000d0110a50f007c441423050103950005150b0f00c5000740d2158a0011b039807100740d003016040d01d035071341e20280c4260403005082010940003451107034000e0007072070b82c0301411907040100340d56030043c043c0409400c1d01c046280e4040000003683c0c1c50681d4000c560032a60940d071408030400d00e01c0b82100d110340c890014000b14071403484210181046103086019101b00150b1100404d00c0e08992510002d11540510244415400d00c6140c40c5090002c0c54001d618060500d04000c420b010080c140f5001c000c1074000841110003120140c40c0b18000c2c007000d8428196413200a107018040038001038a460203260300845c00c01d0328a1086080351203010302064100841103850328070400e01002d0030b482c0b0307040c08401480000c04030b0131004040c04142e128036407503002c03191405002c2d0031a1000c0f04244030203110184450301e692001d83d1030322480b808185135030314001400310704000700d5044000c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 707230494 1250 707229244 707229247
    0x100305041704150801050301060503031e0403020d1b0812160201140f0a0912020306010302010f03020910030204031e05190501020c0106152d0c0602070c090c0e09061003051803 77
    0x10301030700307800301403030f4900c00e039075414140380d07256002c06080380d91502c2a035515500c01c0103901c03000c1d49041c0701e00303125411040d00142040d0390381d004030b50301d1008583c044628600300980e9040c80c41d00c50301104c01911040004200040010003d858540f1481c0d0303100035512091020002168400d2001030b040c2e04442e240f01d81c94800b06600c0020ba50003c200100103c3c0d281540801e100c41009000e4000c181c004000700426440c5800541d503041c04544010201602001192a50344485c2c2d040454a1150b40d80165590f10f141401140c400200b900e0800080050108101080c1c001925039400b140c3c1c00c43d0303645100070500e0b15a0080c13103442d0611009500b0100e0000d0140203201030303045c00c1d07039031601c400c15440f0185003403414030f43d003114200c05400c01084404508138801c0428054440c451000140b6140458441080442c01580a0100651221501302c0c0c030076072055040300e4080060b20303400c0d0141010000075000b03144984016003007640d202c001681143c03454164503c00c440080649 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 707231744 1250 707230494 707230499
    0x3030d140601030c0516111302070503030708060904050703060b1309060b0a0608010f12141c120204080a0b07020114010e04050610080a110a05030111090406060e100305041704 77
    0x282494004403407050100380b514402c640030601450841d05082110b04030382d801d0364915900c3c010517010051920b5004603e584e140f10034a62144010145107015200450312882c3c48440100032010081900c0d01070310100d018000024000a500419079503c45000f01320091020080790352814048001c00c2d6003030403c3c400030280301c0207601091042400740c614032405a101d04040e07980140a1146811000620004100f200040c1d5030503401e0520a103880190f280c01c00b140d41c0e25200a140c1d404031510344d46aa00100650040c00820010780081010b50806203000c0d81c075619180b900c0e038090a60784400000811a501c00c0d800060088480c1400300d81e51b50b1a00031007516a14102d4044400c1c2c4035041c0400e1310496460301c41407ca885a100801e032301206a501e991504174200295900215000c1c40800c4599080c0a4504010b000500081d200c9101c0c0c1c0400080e1038080d80013405114202003460110f44414420070b8107500d06080c08600e54450746001c60601014103259600c034400030402 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 707232994 1250 707231744 707231771
    0x9110a1203030f110d06030b06030303090304090b011407031701060e0d02040510080a140111130b0c011d1f0c050702010810093e04150203090a031110030504030c02060903030d 77
    0x46c000b500e015404581c80b968400007803550728402036a4805003548144000c22100c1707910f42002c0504101854822400220b08401000c10f400c05a422070100d0702c00c20540614852100790140140030504d04468422070403804140406121800039000da41c503240000c00b505400e15100c0f0081080d4400c859039103499080c121054002c5c2641940707a5420702c40c203800740340540c0c41a110750034035243c0c0005c103071840d264400407540e100041d002110b54a41054011200c62420181000d20084000d410020b060031100d10701d07190f40b03100c0c40014a2600c51282e480715840000c0d00d005030b9085c208488aa12035656240181e10680c0c04080042c0c00c0441e407107a030460000c1d480c000c82c0f600103001c00702c00021400090380c1420030302c04034440c0001400700f000000841c406101c0c0d101c10600680340b03007000250114541d0385140e0030175626284120360001850520b0740444110034079a140070451030a15070340081003d01e0002e8041e125520200f06c0d624166428000c0701e61074401702e2410015046104d45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 707234244 1250 707232994 707233001
    0x20c030a1713030210050301061d0901170f0706080709050108091203040f0f0602120a09030c020f06040512070602120a020c040b040b030a0f020405010501051206060705070f060309110a1203030f110d 87
    0x9d000009401c22a491034683c49091007002c000c0e0b005180804680c01e0010383c4011013540d013401d12880c0f040100740f1481c3c4e0810322a05016203520342d5409507601d00640041c03c0d100f8550701c45810001d80900b04844044081112406009503824031079594031941000405000f8450000e000031a404080b541002410b6009100e0600f000e205a00f490350390361045022071f0241e50022300825100c03000200145050740381c07480401c50080c503440c2407a0700e440110f0003499002c41282030b076a105034024003100d501000b0044161070a0b0300d2035458070001c440025261201c02510500803038a07003241c4611a0381e10340003400c071290042c00710380b0000c0090414100c2c0b010303001000d07405146403400200d1745512038021600030b400c6035041e450081d200d800900610b9800403900b85d030140100200400c8200d80f0a03003100c000c050744d582c00300c0c80521509001c40080d4000c030110313200d694100810000c1403000c0c400c042105415041c0021b020800750315000240032455480c0c069044000ba840703440c084281d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 707235494 1250 707234244 707234249
    0x3060405091f06082a01080604060b041202031608150709031505040c0e09030405090a0e0f0f07050405012d1701230f0408030702070513020901020c030a1713030210050301 75
    0x4080b107809582c84010404403c415645490000b08401005d0415500074a000d582000303015100203403e40ea5254007005980180d00f00d842902d1540c1b03075110a51400b0880c605100d0040d01001c00c45a141032070055031a5200300d00c0607540b2020000003056140200750b141d00454111850000d0022800c1d003040c000d08007150700b1075503480c4010002c190748003456100c80c8110540d400071403609003800100441440024262041551651040d04000c40c09010303603011048130100800b280c51200c0d005904000150704500d006900d000010020520035a03a030000c0c00c00454480c108407400c481c4212402c400310f400424030b40c91607034010507603a80305510454485507040c0b040300d520714182182d106070040503a00d00d80b0b00321290000c140070450800045420180e05d004859807182d540300442c400004400000303440581c086542003055805010324022074100300c026040300e11850340e6941c420700100c0d000c07a15a4002240c541d0300060400411409503800410111843d980642d00034413562090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 707236744 1250 707235494 707235509
    0x305090301020703171e18030f0d050601090b0906040504020c030d0c09090f0b150a12050103030503100b0703080c0c0109080c0f0f1f0b131d2103060405091f06 70
    0x2000154221406112070080303c00c0e0580c6d04000b41c0c0341c5540c40c3c0703a01c502494444003507000401c6001c082c41c4c04d1000808101c80c07688000b04072483e040002406240c5184e01488010740d0030010641240d58185c100c0303003036803011200143c60b451150300d09880c40c0a9000100e003090303d84960034103003d400409100890f40120028008020440f0310f0409880303042c54043d4205c0c40c10020003000880340405080702c0000344c03502d0342c04000740201071307015105c083c1e00c1540401c1000040c06901e000904dc40406000804041450002141c0d001040078500619038034040c0e4011540070120442900b046a0542e00b1400203a00c2e05811502d05445812040c02c098452040b0104c1a40d26803010441640500d0583e410143c4d061503460100c1c050400900c4240d0310030b00d02505800e0410b803d200e1441c1d40c0c0142441000e0740d019404013030307103030513030500d1112a100c403000e0010014902d000d080300d034402c40039580444d080d01c442048520703200c4152048511402903d044041e0521240d203c0d13022070384038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 707237994 1250 707236744 707236787
    0x25060b040522080706151503060f0501050306091f180509010c0212250807020108010605090d1103010212070c0b07051306110c03160305011a0a0509040305090301020703 74
    0x340301004010b514004011003901d028410382502040000019051203800360f040818489031030408000d160010713400044096a01749804510f00f80e052040b24003418198600c00209400d040010307110340002440944079141401c00074004001c0c04030701c0600d140700c1c800714240f120703168800b05144480c0904004c40c3c6a1500380004c0b802c0c40140500808074001342c010f0507648002c1800b10105500ca00c25200310354150285016503855611150f0383d5860146810684540d0907100042c11020180d10900800c2030501c26041c00e640c0c3c0d011111007450b0700030721501004c0c5105010902902030220040c185150110401c000190001c3c0b248038806e10648000160f959407007000d807070703038000c4201f0a081181c1101c1c040c40f41030302071f01c140182041c411040b9424071030b0707440011340303050441103294200000c500d004100300f0509018000d80c0c40805941281101404030216412102070721825115504403070214040c14090400c41c2d04151014009569030725190901820320703596a07100410807200c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 707239244 1250 707237994 707238001
    0xd06110702130203010f1e0302310605011b2a050a06050703020307140a1b15020703050c0402030606040905040c0302090601030c270506070b061207030c0302010525060b0405 76
    0xb2403007164165240565400482c0d0b052119400800110443c051501440840c020000d640d680d03d1047c980d040f045241160b03414151002c1101080c180410003015081070018820b60b82c0012a0f904117000810341d1035043c011a017414804506005042020241c1c883c0e1004291032034581d0f0042a1041903d0444070642d0302c0e0021265803180100180060300184035060008010600c0c0c4906002010f00701c0701c0400503130f190502102c02e084034012824101050030044030079031100380d071516107840c0080c184551451302d07460b4032000c071110301c148a42c0d400030014941c2d5a88006541c090705c80407604100d2031801e4a0305c44d100403d01e00040e403007021164001102340d8424017520210074526a1076403100408040074040165009080000c0000f2604c00030801e5101c032009400c1b068091903042c0c8045c10300d4030620030424003040074011207402c114020b002003201cac0d41280c2c2c00c61b44c0c2031a007030307540e82d603440c4400460524841c06070002d00038180c01038090040d650400c19854000711010840d0380c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 707240494 1250 707239244 707239279
    0x4090c02030f07020607080c010c1e0e090c0a200a050633040605040f0b0a120302070e060a2301080609060d0f050f0d09081507080c090d06110702 64
    0x10300b1280e190300304040100300010305002000d010814411601d6904064404130900e00751041d82000c040004e815040600181000c3c40005a1250b40c40c10002d180b0700d03102010407080200142011700c80341d400038800b0a00c03441441040c90315040b40070304441845034006940e46940c08800d05a54600c0b510001c134039001c0701c030581c107a044101141010402038094148007090389003018001d03486990b8080004440c0c80d540180c103481401c3d0302d03002070100780d91010882c4c51045600440080d403164540000060380024482d81aa480d035140403080f0342c0d9500014008560742d0b003000c1c00302d201801c504031411300c482d00d4418a001090300d60044690740e0509002102904841095201c0030042030f00d00811918000301d00468010029241d44000d0070041174580600c42040c0400145614800c0051400074840c5541c4841200301000d41801e0103900105071000c0580101519580052078040c1c80d982c0c104410515644a0802e0009d1810b241000348103401c0390714241c1c010101030102c0724480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 707241744 1250 707240494 707240497
    0x160b07170c0a120b06040b0c10020901052215030f18081e0409050103050303010e010801051608130203060a062306031314010203090607030e030a0e090a0212090304090c0203 76
    0x40040704066420701509280445004a074000d09510403039a600300c81d03420f92a40c0c40100301600c0e660700d4a43e6102e5455040502e0000703400c2807060700714814041c5210301d03170740417085401c42410500d54031030501500019130001c080e550700030b5944d911500f510034a1503802d5040100c0c90000c0010800c102c0321403038040d005840900e000100702ca42c04001200038440d550901211841040d24000c0c01c141d2200d00c0310013112800c1c1c100b50b03125031000c0700410200202c90030050240408a001344600c1c180850146078030b0036070b101d06900f40301c0301f500020307003903074404001b40341180d0028101d81c0d0070b003010040580240341074042c200c4d0f6410600c51054603000081629040d0303d00c003810710b07403840c1e94015a41c0064281e0010031150000c01880e40c04003540240040c500604410002c1c050a060202d009001c440281e030714104560801d00482d400c45400c140549074007802a600d041c81d03544d03046800d000a10810850427002a044d4082c002211400000b4109031040101d0403c150150050300341d949 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 707242994 1250 707241744 707241751
    0x608340e0d0c1502190503040806090d0c08030402011e0806091f090209030309130f061d1b1902011a030a0b07030209030c090702060a061e0b070206160b0717 69
    0x2c904910000308028180c40850481d40116032040c2c80e00ea00c11140c21505201c140d01c420303113080e403000c1402e004d25401440101d401c4000ca1004010a003e02c0d1000b030281029a8405081050702200140a5900844810081c1d05900030703e0514208007400180171400103070703800760150741c1e07031301c00580c02e0021041110204d20009160488241c50048000c001e0342c170800160303405000078021019191900341c0c1031071510a035000c0200e880d00d01c04189408845181c2d103c4080440040c0f445088040300c07520b22504035800c0900d01010001d4490703081c002b4410344444880c0c072580140440859903040d8411416400380e80e820300544055003040540d01c400080c00500540c1550000c10754a43c0170758001c0a210f20040c06030707035100400c5000104000002c031040005030708014204161444c4901c116070185c640c824845d48447e031382d0044086500c02501889518110025042096540d00401d4030142056201c5800c1e03c08000e00c3d046400510540d01d10002c10f900440170343c520300946251b02d20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 707244244 1250 707242994 707243003
    0x10030e07092c0109080c060103140a0c06050d0b1215060f011715030a06050601030c0309112701030f050d2307150507030204060e0117010608340e0d 65
    0x441034181108012004803902c44420365840c40d45000290f0000e0140881c0c842030006800c003980b4504200303054212000da824940d0704184042030000f004074155000f80c880c1464400d403100750303042d0040024004800c4403603200c1702d80e503607044800200040418000400d03900804c0c1c15141c410500401d142d608044501081941c4031501c240c40707909103141d5000c280c1c0c50b61800401030b00343c046818008500000c0d104551104204542942c260240785841c211a180800014805444816606a806d0b9140f889585401d400e514000c1441e4185a0b80304041d04d0150300300d5a6030b10b8828010162030070b00722550b00450905205546c0500744000303200d41071150814074010344020140055010041c12602c1585408009140f264030f03106441c80b07945503450050b82c1d28100075005d009138501441c15410020010100516269409011811607507541490381c415150b100d40700743d4411000072501c0c1a501203140c441200240312291601c40002a203c100c1c03580e078000b062040380501020041d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 707245494 1250 707244244 707244281
    0x60a1e111330080d02030c190e04050c0306150333011404030803040f1a04060b0a0b0c03120c09121f090218093a030b100c03090510030e0709 62
    0x2102401c051700250f600c20000464140383c203c1c208050a003810f880c1c0300420000d02c1600300c0004505161041d03a4104043d44c0c040360071454900000340d030002948100310340d40700010012680714420309141c3d140c060502038407061341e0086da00002031030700045c0b0211400518100c00c2c112546003464200c6041c0d03a00010010b103555a00d40701d607180035562046c11180c08607400540f000b8078004900c1a400740e40315441c0171a40900c4c403420000c03004000e030008030042d00200045100309030000100d6103481c00c508011402e039070351021542c90341e011b462142c1c3c2c0c124659803410055500003250401d83c0da59042c6501c04906107043e403c80880d000d071413000b074100b102c5001038041c20740280282980000003208850b4000c00f40d40f515800d038285544600c10303c06048460b122400000421104c000210740b40802c6428000d4000038401450001c4010600034500c1282007030501c100d410001600028100714620390300e1000c010020040900610124082d400c000b040b211898041c0080c140315941c03511 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 707246744 1250 707245494 707245507
    0x1110408100c0e0a0b07290a0e0102031905060a05060a390b1021020301050c030403020d0507210804050c04090309090f02070506130203060a1e11133008 67
    0x10105580710000a6404c007c140101d42c41baaa1003d14072604540e41180340817040c10400340150686500d100200201c1c1d00500c00c11401560684a45820700031040c001709258a40300c022078a03d41180d001035803c103130001071070094146c0000d00811451a410960303250000b04501901f1a8802c0c100e6000c0445a40001c21000c6402c014450340c00c2100245580145580c500b213a802c01324511034440e4003140340b01590019072070207201c3c3c230f0b038044284240300e8598a410b1f0350094444409401c044240f050100b800c4040c080700b03100c425200c14140207080254a840400500000d000316002c440701e21840346403031001d0a246c010f5105d0304e1740c90340705c40d8140707410b0655810152032941100701300c166090140e500800c104001c1640034582104440180308a54014503007082d10081081c8489414071002072903040702200070f44c1900708001000246468503015103010713482010f00d040041c40310070402141c079210400071000c407070001610421520410081c0002d1071520701078003500c501000d0114 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 707247994 1250 707246744 707246759
    0x703020a06111c0e0a1701180203030714122703010e07050603060118181b050d09030c240c0f09090903140a0c050d03050c09011101110408100c0e0a 65
    0x6840d160f41e550030030040480350100840e5849040d9800141d440c0466101c0342d071401001c0c41076400200c5e0b4115102d841c220f080c0c002c241d4911520f08020b28103103034400000819081404818209a810880c041e540c1484c0b0107828020805018011942c1c07a600d10b020310b2504e0144500140103403900c0107441c4503407420b000c11100e5000140b0050500074000801a40e20784224541e6015040340300301400da500c03e4408407411101c0490411120a00340803000040c150440700344d40146000000108859000f86412a1220070303858004040d042a00022400700c1140d042e1184510403000c02004105002c079000c946410348101c4480c04501124000c0c01000c00540107031101500030300f01044401d00c0800d044030680d0140c030b0031200107160208e44208004040c000307030300110401e1034103001030f04014000312460301c600c0071118140a42d41210150040e000c0d000020b401102a0340780743c4540c0d03210880303912040240c1015089624240c040c11900d40959000700c1d54000c0030f814112136030300f000d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 707249244 1250 707247994 707248033
    0xc01030b01200c04020a080f10030807060f0b130b03011b090608090a05060f0a06050108070806240406020a0203071208030105060703140a0519020607140f1b0703020a0611 75
    0x5030030b50103020f68031481c940301d40c0000d00220030650381d000054034100d101d41e004454007502408040889840030004558034500781c810861300140005940240c06808400030950381c00d050303402c68021251070305180740b564007000d130000301031f030080c1706c2c0c0f1484520f500c0b8840c0ea0300c4074020200c0c068050501056118141c5c507540682e054084031206902a142c1510f00a012120648400c0309401004803800a0740192801800d082c00c0c43c10890400c03000107407103120001c1c9814091008132202e20380204076a40c040c40407141550ba01607035280c582500035110000c0c41000c1c0c2c040d1244200000b030180e01c1003100508960821005400c50342800104407040d805500290100a228124000c000310302100030a00f0f4621511440e0780d4441684034504920262400b03c401d54214008000c2d080c1d400c00f240711180612252903a40d24941000090454011555888084523000b001d204031390030002400f03c2030f01d0080781d01c1c12120795510300460320900702441e5140980c1124196502005201c3d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 707250494 1250 707249244 707249297
    0x22a0301241701271403030f0a09080714030924030109110417030703080108150a020a11070308120f0c070b060a0b0324010203040308041e18020901020c01030b01 71
    0x10010030211003110614902040130055079000c449100c080204000d100e5010030350000801006e5411444c0ca17400a55076042e000b41103100035511411924100200f050486101550203084c40c6003a060400351603650b42c1040d55001d0155440411000c07000101807024800c8016040145141d40c0c203003481203028100800c1140490901400b0200b0302c0c0d0000100e984d070540401000315255183c40c100140b5141c4e0603440f000c902e401c06650155090309448090341c1c800c11150016a5401581d00115040b4215507490300240c002c101c800320401c10303c0300003030003c3c0041002110701070700da142000005001c10384550191a9042100e43c000070012005140c0c0410005c0c5020f400c00e940303103c07801d5680d000329906c081503c40c005a003841d100812041450b81e480a100460905055030b4a00125115134018548404020a87c1400c20f0b9200e03082100604a4118884a031382d000142500203504052412409809640300e1048907510904c120450200b0503034401c2c2c030010540212012150810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 707251744 1250 707250494 707250539
    0xe1506030c06180f060c01140c0405030c0d0302031c020304200603010603091a19140910020c010f1b02060a0b130c02010e0d020d1403071707022a030124 67
    0x201c41d81350342d95552014040c00444400003090803100c031102d8000500c03000301019441102840244440d480001d06141c03031280645664840e248d041c1000e030304d9806503190310645503480c460a8200552a0740280d4000d621608000c1402401e00809990071440c4d0914150040d50078401002014480c3e0483d1003402c0c05444299804102c404031107440400403542e4a003e1512910b880003029802c2c4900b1910000c0980f003000c0b0b504100301029150741032401e824460640207d02c2000e44c140079842150b0341446041e04000b80307821a1204804401e20a5101c3c01502030240040c104504901401c0403c0c003000740340c0000b0707807410304150009180b600d80f000115907031031810000c2d0b468108440e0307803a524250000c20414482da1b400030302c98400500710410310803003407090283c000d400403403000c407070000e040c2103052645d2400b034201e00e04400c8120090f2210340d500342d20000c42807000c0307101c0743c0100300380c00030f1143c17080101030b0148100c8015891940780e06550020002848803090307180084209 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 707252994 1250 707251744 707251759
    0x30c1112220b040b070201110a030e010e130501140a1401020604020411070c060e1309080307050304021f08150d031d010905040e030c07080a030203091507060e1506030c0618 76
    0x1c9200d16442a04aa0000302448130001400002e40d1b801c07040c44550b1078040001040d2441c5165801040f61a8400c1011b0501001040e181d1403992800e15403c02e0421050080109694810842000040601810f400b608811340d0110b284403804086200c03221041e0002e21050719541d00b8880203050042503c0a0001d06001c5d12001825500400000741016a596071400c00654104520300701c0d10541c920216182c0030359180040e11140a0b642d100781181801602d0351380314004030b052403d0181d002852102010008a00b8a80084102d0300465000c9041041c0f0030680c400c2c800c0c40890040302801040b07040340021560400c0c43e030f65070040701c018901900400e0307980d0085020348804811049050f0004075000582d6203003003049900070b0521000614074001d10b524080d4891144c2e0740d20710302a039000360b8104190210481243c0340c06510000c2000032105418010341c40d1041c0200194403a074419000c81c80c640f42c0000d9003460411300030125807403c40c0260048605402c0104460b410000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 707254244 1250 707252994 707252999
    0x3020613020a1d0601021c020c06131d1509040b040f11040c11061e0c0d0b28051f030506030a060c020a050c060f03010e1e0106030c111222 61
    0x114461211983d507001c000d90a0303506240c0006824040020402040c000c028207144507410b80c0001c2c0c030101410103980c8540c3c1d504501c0c4100a05620540101d10760034012410440040c08a038040d40c0304260182080c2001c500c00b07020443d0513003080c0c8020f031a804c9444003050100700707411991001144519a00105042d564010801740e07405001000041400415182c004003000d006c0140d016a0144404440c640c142900c0301c1c0f40c0c940541000b4034140007061401000340075900010138800024a00d00180c800c86d8640f61000610150f864400803c090b800102403c28003681c15804c00c1d0792640d4001c01c1c1c80c541045008090040400c0d5051099481c2c0c0c07070104941e031044240002d119400760641400c0c5040070b030b03d00005580231901a600400050030400c00d988282d905491440100f4407203503d40000108c00350140140a10382842e00340000500346426910100400b5100d23140c060816100c03450560301d62110b1658000008800c0103c480350812a007206400c00344610141e040c080d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 707255494 1250 707254244 707254259
    0xf04020d0e120a03050f0106200a0204020d0204170c130902180708010e150d02010f05121005010e04091a090328091e0b0f22050f0d03020613020a 64
    0x1e40154a2a441020000d0440e80055250045c2030b402080030202948651600b44024100060381688100001c1d00441ca4522004140030304545c0980041c41951154400d0124100030360007441602415a15410b643c101d161000c148030620600044c002000d590034030034040301605100004992204004010f42c0e1a01c0d040d00c00341d8055141d50340d844902c3e605001c1d0000541c640030345109511058001d42202d666180c0402c003442f2542803801d00c05a408040d01560030b4000c070b050f148090b07a041b0080159441d03003000080d00319403090342c56843c903d48120038030044904004014060105480409032418030140c80742d40c0108080381204d00d00002c2030f5070740400d8034011500031704000441003c03412140d0301ca43c458018190f083c80540316000700481030b81c0c5215181c03103034840488012541d0304541a032601501d603e820004140494407211280c0078081140a00419204032101a0b18803510b09200034460b8940d680f5400502c110b464050740c0a034007103e001c030100c0c0d228480b15130104103032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 707256744 1250 707255494 707255503
    0x1706031509161404060501111c2f07060306240e1207090506010801050d11031c031512050312040f140105060a0611071e0b07030f1106060f04020d0e 65
    0xc03e0300840281d032049001d81000f05592281e44001e04026101d404040c3e051000300e58184051310390950202405804030041e80c00c0b490100d542c8480010740016050344220f031101003551740d04080140d9030f50700d4403014254121041401802500b0b000c051034802015002d528603501961242841800114003600051000284d0002801d11303410a4000304140a840d01416402c9102404c08103102e40c1444040782c0034001c00040501651799004404030142c50500c01700a0310050480c41c030030034a004103070241c050030301900e0000035400041d100181d481602074443c8460b540c4400a54608072640d0380c030b400a028082c1050f100c80d16141c103071b030700060004401009081440720010401e89403000c104034240120783d00020a009248500b801f100c9000f141e0481510030010a01c4c0000c00029003200c0f1800040d0010070044000040305810b040e00501604c001b0b2545a80755190801094500c545400d02aa034494000c401c44038404400c0c503168000d0026121418000640e07808140b00d2640340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 707257994 1250 707256744 707256749
    0x907030f020a47030606031308030709031704050d021306091b081623070b04080c0f07120818041419020c1b0d12050a170603150916 58
    0x2c0041c00e00d08002c032840300c0b8441d1055283e540e0381e80368400e8902c0100c0c0070f903480024041e80c810b210000000318460a06503004411517080001540c07030f8505440c0103040702d14980000e40f00f0141401c00007600305801c1c8102c0d0280c9a02a044400b10f10740e07942407140e90303e00d044045178139544600c1d011030030010502c900c200f58926503240360b4070310301840b601411841d0040e0540390f15800c50400044100d41280007044030021011013411042640c0c121400c0d24021a04010f001c0d01c64101404240180500a0480000e00b0000d50383c446908441c455078035541441806902c200c08030b4000042b03001d01c0007421030120f00844110358481c00034002804c8031098416814402d110718180442da081562020700d0020600c82d04516080c80504080d41c0d43d0f003403000f004401007080700d0072a080e8403078110580d84242c2c0605400409581d04d04041c0c1240c0101c40010000340ba5144198210f0400d0030380680190300c042d01801e911030f00d2210b00c00360080002e040546500c601c030121065080c0402c4070800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 707259244 1250 707257994 707258039
    0x1e080a08071101032c07120804030b010e07020d141605070e01050a050d0f0203031908090d0c120e040e0d030501030c05220b0102070e04030203070b09060907030f020a 73
    0x55507005864150150044805018109850200004990100e62801c0100c0400417803980184006010340149806030540101003d1403200485100b000b000501a2094900c541003604076a0f880d2581640f4a090448071000140d00c101c240c5503080e40100e840a6240c048502c0061030071151007800c02180020081c01c0352180e0001004200d140004074500380540802c40740801070368078200000b900384036185005068a41107107080000c641d410800c440740741641c81c2440324400700710400a021110211803103041c50103001b50300d0a20300c0c8285440540c243d4043c25504071896400030465181d00b282d002243c026550f40c02e0301056000410001c655005c02c0d54020445605528240183d580075a02030742c002c0c401000061034600010032903a4824250040006021a40e280101e15120f00b660004d03081c07000e13100038802850f0340440204025401150b84109580f56104401d030b44400c12100c4d01d02030f820044c1d0903c0064108070841180600040110040ca500c510031a41500c03100d5640c0c0c030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 707260494 1250 707259244 707259247
    0xf030d1205042907030c0206060607020f03010f180b07022a0a0b0316021e0307020d081318051807060e12010510050112020405060a050c010e0a03020102131a041e080a08 74
    0x44c03c1d40c1c14000c08810544910160055041c11000310b00b0b0f80c0295803000348554040541030989031000d600012008a2560302800403840c20b031000240b00c92181d00545181080e5000a061940009496001c4e484102507109000480b407452201405099250035484404a28005050010140914003c0120154034401c844d0f0800d006846c203c0030350242100810000308600300800048152140f058055440b843c40b00b01c542380181d0b0034801c10b440c90912205d80310b00811089030b00d802a9900c2409030008100300c4e02e030109250301c58503a03010b40c1c1c0d1b080c0e407061000b0b20045208981340c98100c1c4002d05900c810490700e051240c00d548040320ba45540104007101002150f83c0402c0c0c0d0017040c2c0c0958003c510300760810340461610b01c28450380e8014040b001825508503042503102c94260b22855040e524214141e24000303002c0e500a440354941d02c0c1d900c050100e004078880701c1c280d04a0310504001c1e894146032403802601d0710340c100080320b00b40032444400503c00006004864a4520842d4003a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 707261744 1250 707260494 707260501
    0x90d0309050111120f0f0f04030f03090611120a030905060a0516090b0d0b01090e160e030706090909020d0b070c0219142b080301050f030d12050429 65
    0x1003c00584072882074060b800910406501d4000f001203980410030407501e540e40742c10002d81c000503840b0b410440e00c00038000240000c02d001c003003512000d0003482540c5050701035540d1641242e50031035400c200340d01500a004c0280e8003480c070b1001030408841c0e070b09012550400039111300303003424401c0700d0f602091502c510400c01e58035500d0b281d66840c070a050038010f603418100340001110340201d011800200d1b40e44e03c0c82c428960f000c1e510902c0140b984082a65981c64080d4500b111020301d1040400803804100f200c80d1549000301e10042030343e1035580c0d0b0080440c54001c07104050400e00100780c2c0c000840150010110f00400350f0703503109510030748903038030001850b00c18050829006000c0e41e8000410030700900c045c40d44100d02000c2c00c2001c4440030001040344001c101178401b0f009040c4c944030075032001d00313040002c4600a14100d55080f1809091440300c0e500b49601c460101301002c0000c3c02818050074241e130150301c080e0304940541e03841d005412098509510400030300c0e02109040307540c007082 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 707262994 1250 707261744 707261747
    0x2b020c0a0c06050304080301120201141c06050625110433121401140a0906060506030903030103140309040f1e0b10030c02010f05070e030601080606090417090d03090501 74
    0x100060000d0f10301149549090f841d20030040c0418007031160340c194104c00c1c04003503a100d81040307000c4420030103030309075600951140401140706040e01514014180343c07000441c0c0c035250045d2081500310303001061812a2000d00d0881042207500c080720b80b44100a40240d007600d81e482041107810010002040104a0410302546550404000c400030740322040c0a00054040345206c2d040c1540c00b420304c99034a612020620301411a032060000540d41040800c22800700781e80103030312800d0150030200b005545450030b00c260380c40201c602510320f038803c0004100140103142e800c02036142c6882030340d04040e10300000909440e090f904000c03c450701c0700c800d140c18804180750811060144070080110015003408110401c03001c1803038000307159407041d00c514000e0003900b01e140d101e014842c040115241120018211485415206000e4032443c0004285c0400026006008400c004c0001c103a5940700c2d640c60340d130415071480c000803a00c024040020340d42c94004400c0802403180c1c03038559119052200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 707264244 1250 707262994 707263013
    0x230a03060e01060f240f201c0302070809010e150f18060a020c09070513170d11100c110303100306230c03060a08060406020d1b052b020c0a 61
    0x1100c4030001c8594207030900f003180304605c501240440d0a00100601351000c0590794188410b00c40d0b007503241a505c646410380030111312105100f401c1002146884800340c2c00720100d02451000030301c0b06600f04941c01c81c66000f8450454070000007031031008034400800c8003101031b801c00d40d4141701c0d041c0046039030784524445d02001c0c2070b075640544045041540403200203581d460390f10040381c040d0b4078103000726a4992080c0100c520540c80e03042e0040c00c0e99541c940c1c000807d1000f0000e40140d001d211218260300b8811501b0441006000c402050400c265030301c180700030031404a2000500001c50a40381052205002452051078940c015420301c501d5420801e0540d006940307010203030080c5540c8513003241040c03600c203a0440d500188907a00e81c3d40c0d0f140800e541c09565040010584600310402c4200211034000703200301702c500542030158036685015003918041c5810b01c0e0010175000c0c0f00040c20124003445001d00440c0075100240702c60001d0362500c0c03c990100381000c0ea1500400c3e5500c0c144220020b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 707265494 1250 707264244 707264249
    0xf010c03021c05060406090614100912030f02031b0109020109080f0d0309060f1d100501030c150e0a06020705010305130c03020d2d060e0601230a03060e01060f 70
    0x101540342550805154009949042c85010281d0ba50350200342c084e2074952002002d098094020403003191030303400080320003005007110f9100300c1315200000380032417049039000e08071011101d45aa046045a809a650119030040a81184424091078220310320200c0f1031403204403400c0002424050b1400018800d45e003d0300032150ba40c1c0b1940221030001800a0030707140008003440c000410541340e2902001a00000160034059414100303c028018082c50142e480c400180b41220201404000180241d070000d03c8068041c403040c02c000c02c60004169600d0b85400080d10300200d800000038002040e0404a070000d03001070348030050902440d40c051040c0364001000d2582c0f0382503029540e407120100710351400003e00507101a041081004000046104e8490346020300c19541016401c212032803078413565082d5034540c1007000f0300307619001c0130401034141d03040e8204140309600b18441420808090000f403e4004001300d000001182d082d1180c03541415138200017250087c0380c484414000c00007034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 707266744 1250 707265494 707265497
    0x9080609010905030306100207080a082107090b091c150609020405240c03030c030402151602010302130b0d0903030501080d2127030818060f040c03050f0f010c 70
    0x2d02001c504001305403507015808482c0f04200d1440d001c800c070b041c844a948504498886c0102d103104201090300a03112820002a901965810120504c00035560503610180898911035051080c104117038001d19602c0300280c12110300b250001c0720f02120401c000020741320302240500680203040746016940003008415410b500b0181030000103101001350034520114242201415600c03000ca4805440710011500b0603207480386803038000d034250b40e80203c0e030032849110010543d100f990b903080700303546111250800000720001c01c1e03030040d0300940c0032518009094040c001c0001c0c100240d14014400101c0303900011400c805646400781c10b50310b041e0822152604009150048690b10881e00400c2100291b0f090b00101c0714224164000d05071803500c1c2c003050f000c03807a0300c100501020202c140224800c3c0d640c1d45640d5615090204d8096079621030141c10340005010409405540e0743d8223030440d000e1003a169409507a030751013510303000d00b200e28405642c100d03036210300740d21100384500c0100c46d032503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 707267994 1250 707266744 707266751
    0x501021014011502070312050310050a03054c0b0301060e13060f1d121e0904020f07030c0c060e151810090302040501050402130314010e010207030908060901 69
    0x1c80038401605041402a01e6034000f00c0000041018030801c090401180c0100c00d090718410b0741a0300401076402113a2144401d110014002840d061006646084030340000142800669000c2c1e00301c0c006540a110a00760b0542c011a550a2001c9a500301021084901829240c696464580080e61168118176100b030740341c0f036801c1041e481041005548444440d460404841c07031841c023203000b042800c101c117070481e14020386c1064170340542c800c540c04044da1204035000d50030840803420a03449403030f1150241a4015003414240100d8901030420800014009414596421403405070380d000190280d0000d041c21090708180304018591802800103480d140703520136140c1010650b0b507148080d20015844001803581480003070100425420710b40204011110f1000704402080400d03140801d070300c1585804000a464a0181308580a2210f12a4111161440c50300c4102540c20003140b400c415548506414442134402e1000b400d00341e100391510a51141006c10b131300e150443c000d20250440c0c1c134 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 707269244 1250 707267994 707268011
    0x6050a0e040209090f040606030b040c0302210c01050c190f021207061e020a0b010e0717100509130b10030b0106050c0a06110f120a05070c11010509060f031005010210 73
    0x3134400d051580480003e0301040c082d00c4d14601103000702030302d51015060940007020b010812004038000c1044074000c65218402d0f03655000701e02595080c981c0402410380c0b003846035207041d502482c00303840751210001c01d4600c098810a5070164411405c0002c481c4803520030405e00462a028000f5805100841d00030319004d420b201020b480340d0a41841c16403407034007142868007464070801c01d0b102c1c0c0745e5102c420003166503522500262158410b40e00311003c00c0000c40e01640d50805503c006106562081400041ea8506814400c0c071000c082d1260402001c6401c0503400715454090f118000c448000c01090700c6440e41c140075284034010b13044481008810070034842141000540900f40c0760700030750700040e448440a02d000300c070320a00c003024604103404201c2150464140a4042c071524950398140103e54a504040350300c100214401804a40051b82030076881d440740d8040c054549010300f006282c00601c4400c80310640080300c03080f040c6000c64034284115641440131000724985007806002108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 707270494 1250 707269244 707269249
    0xc082103010e060f0d0203010c030e07060c0302120a090b1b074112010609061e0603050a090c0b070201140c030a0e0f06121f0b270a06050a0e040209 65
    0xd4090000c03031091482c001c0c0300700940e44040c120840e07140d001f00200548061441c02801a00044a01380218080c1c0b50303000401d5406803054000c00fa034181c0c05008640310340b503801055a04031480074001c01159031404558520440002c1c20440c1e040c0d06808821040c1c00907580c60000c90b60003030340e20b0002c5801c4034102c6803201c02c04040e1420740000d80100920900210103111060360340d105030300001040380c2c610040410340c001300c03d07a00d02e12414048180c0b684043d01071400128201a80c40c99100f40030443c0d07074880e9101541040070018042080398941e15502041c212507004000300182c000380040440d0780207040207100c0c0024011049c105603500106c42d40340c1c00b07200a0314080c0014101604a15a201174401c420b024008103102d868481740c91800130042d004031a000c14452207441c414080b0b2003010b1010301181c0c01c000c222440d1900440ca015069965110555000703c002c6c5090103070740c1d940c1203862024203840d503100c903242d00045500800043c94640301c240500e00c10083e540d0320780c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 707271744 1250 707270494 707270519
    0x71112041202040e011b091d01121401091703090f0d0e040209030705040501080102030613051302040b030c04050901020d0c0c080304030305070c1b061205060109210c08210301 77
    0x1c0340c0455000440d50b80340c4003440d0240c00b09840c080e400000c44c08801074190340020000065995003040c981c0c148038400f1104443e00340c2030080c030500213945c561240000f80364458060a02c0721074000440e03010b055607103903100e110040d5205d00341c140001c010421107140410620900c0c82402c00100501e100180d800707085400c0807000113000301d40003c1c0a6a031034030704005460040070041c1c4100483c0d81c0d40c0c0b859a00035041a5911849001e124480301e2407900c480c00761030302906d2140b808019125450342080000e19684449a8041c0100c0480c1a0280c6da14400e09108841003800566540443c541321011581044281014042c2e8002d110000c5112003041d81d03841b40d414240055103444001069030701490000c4002c2c40c6040c02a181c0003690402e44210046911644402540221040d59242a234408580290001d0102602001007620b050b040e030500290007800c441d490542074135810360750320590304a03007280c1c1e1141d165000710741070104814100c01d003580341580c199414241d4482a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 707272994 1250 707271744 707271779
    0x1e031b06101e08060903071b3014060601030c111f0b0a0b0c060a02030f0a09020120062a0f0306031002030415060506030702070509150907111204 64
    0x2c6600d9410400c240c10742889000094840c81046031514038002d03240e15a0f03a40894000c4031010f02c0d00d204007080d4003c06650f04107460b03505800c801c20b203041c403074030080031106080c0281e60320307056110050102d603800c849454840e1310400070300100d190803c005002e591160b0984020403004c0408459a41c1d03000c1202100300f0b0460f2050401c0d6423094080c2b0b4064a8400e420750780c0207010b00e030001102c189640003421b141c1495400c1d1441d80d59804510022030004031900c2852032004800200b25440f85d0740100e02c1702c1d10505100702d602a0260300c42c0c802c1d0481c0e44540364594884028050301ba081207a15024400025601011800c00c010040c0c00758042c00c0780c000782500f00400800c0f000e9034141b05000c901102c4600440d243d103003604000c0c00404003250321811042c1b60100119030303030030004101c91103025a41c00500040d0700d8030040c0308203140010107901d682c4010640600c950ba994a04240c09208255240040c1064407440107040ca00184060003c1490401040001c507818010070f541 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 707274244 1250 707272994 707273009
    0xe150109121b0b04080a1518062d020406031a03032b0212070809010e070b1b06040804170106031112030d0507080a140f0c0c1e031b0610 60
    0x80708070042e400740c50122616001120b0221001c02d000c24111030001e407220480d03008190800940e41d85e59040401c0700d03081c00158a80b24200c80b6400042034442d000b548024008904200c2a0410036225107070040c10041500000d81c1c0000d420403007180d25008100c0d502030300032490b4581d040007100282e0740344144c8010790301c090300e05002036245000c0d0601514000102c0641595152614407403400300c0c08045894501145070403000c2091200b0500c200c100306141c0384010500e180c02c04900805a401401c001240038604820041340d210301031010300d00580c858402247c4030342c2805038040e0710914041d4442c016a141403000c1020803084140600b80000c1611585030054412031401c1c10345c0702d0f04c50101c0c0c18030308000a0210160788480d6091103071200e0b64080020640c840701c1c40504400c1a40c140c14111001000324014004500040404030007240440705e80c070481e40e0581019109203541922260004110700c500515000e180070030406001d00031f00454548440460490250b43c00b5001c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 707275494 1250 707274244 707274263
    0x40c0e041b031a130c170c04150c0210081b0d02030a0b1c0201050306040b191a0406091401020a17030a0b180a0509070906082b0918020d05010e15010912 67
    0x880c44c1c0c0102800c4512451640c1c00006c0c0e0720340141d02e0049a4014410700c85030403000000640700b00d03c03403501c820480da402010000d00429140c81194a84030141031000c00540300105d141c6c0c5124948000e100700c2241510240e124541000d084c0215400445614041d071001019100110504410b030144c0d640d090800c203840340c8641c00480c00800d1200312480d000030310100740060071620b09002008550304103000b10601c4a14655404440c0120720454001c1340007480d00740443c206030a49115401018411280b482403551a00128580c803030708111039484000042c00001802c9000301940b18000340c48450f8510b506010040001c02c1c0117000007100c5a5841c00f03d000e04000703000c10001030402c9001404510b80707602134641c503032409050083e0805401c2d80761420303002460f07140c2d03042c0903815101e42240c00e01d0602000c0b10525845400003d0640c20024888007103814400c80e4044c1c80f00c04100b01c0145001816135429501000516050000303450042000c07601200f48034800c5588903103801c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 707276744 1250 707275494 707275511
    0xf080f0307380108030304140d0e0d052d010606030614010f1101020d0606110708210712050c010b040e031608071401092f040c0e041b031a13 62
    0x103481c0380b10b000c801c0c80000c120800061360030740c00405540201d00035034403a000c007104c5202e03590742c0d219502c48140116409031030b0502c0504e4040f1610b10f00c940100261494480c04010101c0810407044000354106c1c0c0809403d0202c5000348a034078040d000b14281045407908007600804602d0b1901581d44c10419101c02d800710041c41002d441800c9500c580082d52211140121000906064042c040014020b0510b10640500c005100f40854403680042c000480c0c441402c004260000c100c0c4c0604c0300e00810090000510400240705800840d964158030b641086d54501d00b0341e040414514806c50402000d6041e5000110442d88804000b000c028082c02440c90180c41034021004003814151002003c00716560703040d0003c0b810a842414480740d4598400c6880108444007101c884032110382c00000f2903030727042991021fa0705480c182440b5140790076203800113003519010007281a24400000c0b00e0050f0039014043d00c6008000c07508a440103190181c0800c149400c000c1441c0480e503100d0341c0c41c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 707277994 1250 707276744 707276813
    0x1204060915051c0209010210140c0f071e0c060309210201060302030102030c0912070f0e07090509041b0b04060806060d022116081603050901060f0f080f0307 69
    0x111241580d440d68450520580e0b03c021400039003003440703e41c1c007600a02404010b06140c2c0e21071150761242c105c5201c581c1e0348540c040c0c010150407850840784820001c2010101249111f8042503d0824038414204000258030f02944110040d601200c10305040c05000c80020b85000d401101c0c148030504005850f150340300c4200e01400e459413010750194800000d1144500c546402000c804006407003180140901090941c4c0d50401c5101d1000c007400c0c00031047c8016903a03611040c0d0000c40501e0500320060f140c07400260410b00503a8101d45501010704008030080030700421000401011100508081c98203101070f0501000070481071194a0019000141c0c40f0143c1c151022018200703a1000511841c403071401d071100059400c0510000c11001000c12644112505ca20400d1900350702d000014481c3e01c2a000341802034003c03a5117540303941c000300701025180d501e100101307440000030329440e24046200c0e0814540b40740c40845500104207040100380c80c107156000312180c4480c040101103080f0701 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 707279244 1250 707277994 707277997
    0x308131704031b050102030918151201090b15031b060f12010801060e04020607020418080d2313230105040c0311010f0801091a040203100305120406091505 68
    0x84009181602060110038003220f1100c01044520303080c6141040b640b075100590fa039015906146a008500c04640e00c034a43c04040b80a4001c450112000c440c540301e44005407040d8070607440080981e40d684c06000030b0101c081041500301d101c10500e1451075640c46c001c240c440344803003043ca45445400c1a40410b94848504983d22800d048103026199117600b42d1031080c2000c20302c2059415828940c000c140b0700200d01100d4040c590017492189050115402e21000d401856070300443d0604006440000c034043c400201032861058800023284400d5120741c09011007119111002f025a1008001c062005004c0d51100c040d0421042e400e001100d8042d10030451001e050303520039508140501042020450144050307a00c41e44981029162480044400c01a24540b07480060034a0004024945c42c0768840d03d130000b89a041d805c072200f440c1000c10140da2040e1104201c00140d0401003051007000c0c000e00b0354141128104600e054a8140024203603d1140984001c020440710b580c0c110b140580e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 707280494 1250 707279244 707279273
    0xf041a0901060f121b14090a090213081203040204090c15080f07031418030c0a0b090601080f0a020907030b0d03110115120605150a080d0306060804030813 68
    0x244224015a1660401031040400c0c003d08808258003102c04200410180111805102080014090307010040d208807410700281810380300c00d210420804041d929212116400740030801c60160342d0b1701681c8604031010704154008100b80c0c100003003225840555004480d0401c1d01120007182e0312505050440d4600c0a60b400070031300c69081d0850300441600840454400c4421030500d450300e41d075410099096030100e00c2007401d4580400e00140000c0b41c60300300d04070f00c00952000c4030f08042c500301b40e8500d003040c4144203881c07030b01c17050b010822100c10412601d4054407014010300500c00004c4c544a9990b286040000d214910b51000902c00078825445100c24080c0104000d6071040a07040142550a1003101d8550950810700c1411104940d611460221001110b40341c040b8401522a00020600584900b000380e030207a45020b401c0d55045030140140ca0345c00064203035001200c1010703044842d07540c84401032203006001c00001c03981094425505c0144041c545202e8011460014144c00d01c20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 707281744 1250 707280494 707280499
    0x1050f0f01080415110d0c140c0d080a0609020c030c07080f070b0702040216080c0d0f0903030c080903060907082401051201060e090c030111030103052d0102040303030203071d0f041a 80
    0x85052072011209801c2543c1041f090b840300800401030700c201030440e2140403001c2c0c4141d48035854984807544550300642d880b06804ca8000b585d6511524000160390220042100300d520215210340d0841c1d00b4410031000380312003c000c054040c1d108603ca622100a4072503446154000308880e020b5403500c0e011200e612040e49000036503503000d450015000e8221850380b40d920721940480803001401a44400c84003407403030300d490085a2842d81c0403a0300404001040350501c8082c404100c40340c0301081894041c40d20000078061075420000b20618280d1000e010001c900181460007071090550702c0c06906450055545074a502c2d8003200c40340c007400c8250301004e404421202005404000031031200a482c108030700078820800c0c01c4001d001c1500080c00040c03c0d94220340303104921404440002101181084502041056082840350880c2c010350b1094020a03000070410140c1075011182407003c1861304502d0349240203401c04950861022842c09000b40c2e0391380444500341c1446e0541940c200b400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 707282994 1250 707281744 707281747
    0x1704061b12050604090201140702030106080a11010f0e0d12021c0509040e07031e02030a0b0c030a060801051003030e060d020d0207051c020d0f12050403020601050f0f0108041511 78
    0xda4008003141042204000007525003800700d0441d20f81405408040d64050303568024000302400c0640382a4000d4008980c19036880500048011050200610b514040d0b0b80541c43c650445001521140e0140f04070400c0045001074640d241d541c1000c818a50f507040026070b054000d40c140c00364641940e82c0d68003010710600081d68031150344d0200040295042c16070381404001081c1c0d650a6890119000c01420f0744036400300180e440400c107914501031070004048510a010603195902c2e20340c2d0580712024403e40c00820000d1030507060203100010003a000007080149840141c0c00070610321400010100031032a00380101503502ca50640e950307680a00f030304560b25501d8070000c80013948030f01401c840038000c42c007001c020500b1405c04004c1e640c186402828003244001c40869003864509034403c240424a05103213890041d51043c03601c80c1e4403d80003004194100002c01418070080c43c00903110706a165030094040c4d038000099600560f0100180780300003092086040902076100c0d01c200c56480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 707284244 1250 707282994 707283041
    0xc18020c0610080706090308091e06030112030807082a04050301060f14030c1e010201060329060f0a1a040302040e030307030501060503010515030405150a0c0908030307170406 77
    0x10340c60290441c3e203000b003107803205580d038407080c2c89205451201402e001003c2c4010105400c0c0603126280800e11821016a0004842c0010f00240c0003038000c0e4412019005d016420103800c440c1698025110341403601980c5007450b640d041001e10b6420740c944103000c40007800c000209000940c1c02805009000b8040d09440d1445142e515485220b500c00d8040c0384860f02a10703080102e09001e0141d40a07040c034400b43e0710102d4404010390751101ca607045660760000040031605051002c036004074416000388a1a6206520760803054025210074455100c0c0c44c4a40d08594441802c54100d07500d5a0501c0030300e00c881002207074180241e42c400394005090111500301604007100641c4a00c0882d24100800e988600088541d80424001c094115500b40b01d108c0300705098030302543c0d11504c0b0700101d58000d000702c84c030802c0c4404162003144003a91140c000c000c0c2550040301e0b03800a041d03640e004504500e410140203010b4095074140600c40310004021400b4002150060509a08513158500c03d410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 707285494 1250 707284244 707284261
    0x8070c210b0a0c08060111030909190509010c080711071d040c151409040f091121100b150a05040f08010c020c061b0625050301030c18020c06 62
    0x80a00e0012603401c4104000035080e90102c0c40b550a000c0d40594918038580e440c00010350301d2140002c108041c40c4018031905c0010703a1004182c1d803007000310680044084801b40c007450107172140900741d000d1590410400c00962035001001039800b0007a8503180409070f000c100c0441c140740140c0c2100302098107100c1080c00303410350ad41a8034002d0f0b10035540480300c1c0d0703568400300303000041e0b122401c00043c01d41070340c1e00ca005104074042c09070214001c1000640040700a00b40084401145c0d048601c0c0c2c140b8154040c461800d1858203030050000b841d5120700310158180303a0745400c441301010042d26526800e6861a44402180b04501400c02407035680c0c455100c0e102400582140c0300e0381c20750754081c02c03000c24650018010194180031940040030b0000d00c03c003c000c82d0380c00188414043d0f0001101e0001c24034000c100c8107005400d40c81015082003580c40d0454441380002c1003100070b10204000400028004082010491321700380b12522135a2040c51100c0040e11600804100e6803060006110580d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 707286744 1250 707285494 707285549
    0x5151306050c07051c02030f0d0605060c010b12010b010e100c0219080105070c02010c110105091905090609040c09090204110720040c1b0204020f0715050a050408040308070c 76
    0xc1c0c4c0100111000c4018410040d81301d000303541401c4005030414001d0b111003942c0e250107060421483c10b07011501503100c401041c0240c01042003050300b82e44074110ba06070350400610f10417042195100903c0001007141c0040c2c10919540d040a0103000c4180180100c1c51080c240030f98644c1d4010310725100540c8200403000050f0340340c0070f40c201d65440c000c0444c0d900b030700540c1d61030401030781a1580c0035540100d4464101c881c0c1d4458085050120801c549211031b41e4266810b00006414400c03405218186018040d141e0b400802d500d000311207200a00c070204210300100c50441c1c2a00d200420165180d2020801a011900b048001440301048160030000c0754059001100d031000180c042d000c4160007000162201407540101080300c020645802030100004540c40030300140c001342c0750440c5500d02001d16441040196014110907a0558020307005003e259000740380c1e00c80522082c2015101e0049612070741c80001c1c0a01000218041008041003510006080e2140000340401d001c44040241 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 707287994 1250 707286744 707286757
    0x90316060902041806181e1a01060c0606082410050603040c081506010e010c080c03031015020a03140d0b0a091a03030414090702151f1205151306050c 66
    0x900d04001c030645a030003076181006d411a41000d0007400808081d020041c010140c1e0905803003203120400c02811071052940044e00078602c40d0798050b2001003d09044084031000d810041d20764000b04940f1010007100040c107110418944405000342d19001c1c0800c030154820350145402410120402040c40080300d8000222100381c01030319455610103000c004602411a5400d01061142044000b1544100684004148201c40c01c0d4584160340090900d581c004880121000c04520310520000705000c02031160451180010030129249541c050100c81003940000c0802c60302103100221200d0035002040007c20182842a900751101c19400140a0100c080c209015080c0140f0500742000001c550854802c0008029510101001c1140200010304110704603c503009445005400485106010f0940015001e51403200e15a560050115a60203a000c8409121404002c00c20214160341a081c000c41042c1566a9003111b10120036440701d07001d40391501c3c04d0200f010980c0070380c000b41035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 707289244 1250 707287994 707288003
    0xc020d031116060b12010f0209180f07230d090605010614031909150b19240519020109020a0b03010305030a03050603100c050d0507080903160609020418 67
    0x701e10900400801c24800c81031001c0e0040a45030400380810b05690092244002c000c00f02160000d00003002800e4a1170030080240c601e50000301c0340280d145c13448d00950400725543c9400701520300b0300319081d4441801421071042c008509404860302c00310160300d48080101201180e181d40041086000501450004650881c030300320010030494010010000748441072000d15141d80e0302c4002d18007200d14410382c811920780d194640300c00002c040f5003140001100d0035000140c4c107401001003140100b0000190481096510b01c20b000c0e0f0445421540309880000103148416104034904a806106041700010442090500d42c510f40754107410a00301079000f01c4500011136152030070600548028440100581d0080190b0440140683c01c05a88800010152200c1250341d050803c1550305000c071901c0000d00000e4960a01801ca20071682c2062107032900c070340c580ca01100341655071b1148c40e01c0003640c038401c44076080820640b0380000d07401c160301030b000f800384082e41e280814807034041c40c00844 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 707290494 1250 707289244 707289251
    0x30d050709140409110a0312140f04140d02030d030b012a030c0c15030e0d0305101806080f030918040c300525050906010f09090c020d03 60
    0x39441032198103031200366a16200c002500b014084200f10080205050468030f20100440310038190350f500007031100940c007540c55843d045040c64001082e03040c511101c50040c03c0280f1a01c01042011020b8605455800c1e024481c4540d84a0005240d01040d0b80d00950520032001440c1209600d80c00440c0f07240000c0e01c4808400d1500201c045100622000c1003c11105100e401c9010900c5080c10501c0503001c1c0440494050701c58501040e40c9040100300d102081d160246207082180c104888200740500c1e140401c40c0d4100f078030000951041d180301c0c0c400c0ca500034512804500c0c0680d4065001020700c0d004a6176019101a405500d80e008508000e10807043c5c2c0a540c4038611074003a21a11580c6e00108020300e060074a01030102c1c50258000d001e01c0b10341e01235008044454503900c90804280180d0007024035120907440d80f0040c0d620490213040281250f441000310362900012030360449824244500b060040f848100c030329403060303441104801c0c10302a80c3d0343c0c1142c0204007602c035a9210b40e400e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 707291744 1250 707290494 707290501
    0x91002011d07150e011202040306090209130c050f01033e04030b060913020603070810050f0609040f0b1c020a240e12010c09081504031d0a0302060c030d05 68
    0x30790712440540300700040d00d4a200d940d840240d10612080007070040505001c0c031945036103090181240c200d03030011525980d0310401802541ba0040c8110707403054200c40e10b030994500784d54401814521610a0501a00600e0020061a030107500402000780119685550580c2280000d10300100000129844000300c4403190805a2040048805598002852100301d8659409000c00050300800b5100d507000c00118840050b6034a100031030150f256a076400c2d995081032089000600031a5000c0c0348580109460944541c03030781001e55000c0c0900b1600000c3c000d40c01151080900b40400c081680521b031460301011864082d00000007a500035146000407507164a05c4800c40d0a541ca030710726080e5201252110b80c1449017880d1586060003810450340f050016508034255202c000500307001c00c0340030406000e04c10b02009194a03c403100d1808850074141900e01405c00d402c81003032100c41c80b550703205116250726034554200c000c40d405440c5d40c0e034807112646c1103900e0341c06c00c041c0840c07150b007001c012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 707292994 1250 707291744 707291801
    0x1109091e01150e060603130f060c0f03060621051f03030c1407030b0118060b0a03020408160f05060309030705060f0f1501050328050117060703020f0304020906030309100201 76
    0xa10313100340806428036256071200c42e5540702900009404940c180105c000000008056004001d8250100d88401c254100b00c06800740580e01190047d0307040044945121510403950035402c011114002c1d030004030b07a218440c040a1201510740c40304050010303100004101a840488109028040d001d41c0c1c0d95000000b00080e01c4e04001d00c000303031600f16004018000c040099010520034071700d002001071510380d201c07030f01ea4140d0024001031010070350100f000c05c0508402d000d84800d030300810000b002c081c0d007003150007803e00740380303000d03143c0244004000144010b408004884586402008030340f200d241c40d103548031154108130b0305516034011003808134511400017290f40817908016101c11f0b0541d60f0701e0040c1c213508408441401650b03003e58100c090003403024820203010f4005240810140c5541382c0b03c2c10324051004e00183d081500c100010088143d2510540380c000d54129050030041d202c01002a296003d101c40c000d9010182c0c052a80d03590b60154000102207844422031002d0100d0b5250 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 707294244 1250 707292994 707293019
    0x509010c051c181d0601051b0d020c0a0b0d022203050102040603140f04120e1e0102060f100b130902120a0b100516050114090d18031109091e0115 64
    0x15000800c4e0740c48007800601000320100301c0c0d10040600d0028141a082c2a600e015001c078550005020b4100352036051a15038180722101e0404015212000c9803440c220241015200310008001060b9001c47c02030032400c4078642c245080114050401206516414118004d610074800c08003ca86408460212080189445440b0300f1402508003c145d456803611603c4100c4009900c003000f100c90781c24520766464404000300d50b00072101c0704100d001d40c00c0029103011005030028603014a54010441c0d40307100700100806481070740413880d0300c8d01704200801e41050b469070000c180550002c00d403824581858001170388942c2d002102804058248024070071113582290414000400410109011508031107640005070300c100c00003e41c1036690f41040240d43c00c01d403118007162b0095094006e00d6584a01515840c03081300340d0b602c0e415451070b84d500c5402542c001d1490301030208000041ea42203024400440341b806117000702c0c0b1054402158190013007582091009001c0b40b06803000c00c04440070342 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 707295494 1250 707294244 707294249
    0x15020c061305031905030d05071e080a1409060c070303060b04090b0a0501080c07020618030f0616090605091306230411040b090d14030d0f0c0f0207060509010c051c18 73
    0xa0361820307948580761006880009c2046080c0f14116501c0c80c01302c0312854100305484015500c0700ca00c2c0c103020b44c28005031410303010b5000e0302840f6002030100c00103010030040e4101c00d0281c1c1140e640c403803600d8264041c2c0001c2d0b1012201100100d000101103000b070708030320b0590004541010f900350f11741c4015900e00d01c058510741000030081c040c0328014104080140380040c0600800d480c1a100cc03400a450030050b09050102500030340244070204142c8031180640030000d0400b035030071909003140180039000300c100c090b01c0780311840042c00d80f0f106654805e4000c4c15019548080c000424009002c0080000603003500071071030501041464000f41b010780c1c00303540f100c071001403a005c5d40c501003020281b0300075816642c4100c02d244900390010200000c08038565004004a10141420303441d0049846012001c0305226440c0b803840415617000c41c010382682c0403400d00384d80710a500700c0101c0350001f1800c0001c056100b20b515800e207010164003200d41c43c110540c1c0750110101b40ca001e404005000c0e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 707296744 1250 707295494 707295503
    0x9010f140d03080115030905030429071716170a110f03031609090f052401020d080a0605190312020a03021b041127030a030915020c0613050319 63
    0x4005200045144c1e900660700c545070300e40420381f8881621442d00710381c0305920842c1003001044030310151080071000308003420312840d41281042c06a403218402c0000c0400305412252001824005010300400d8038030304181c0003d260b400045110030240740d154070684101c1c003c2089400450703509800042c03210007685d003903409541551a60308210404440950030442444680000807a0f841100e01c00c0c01041d020949001c105400c0c02d4805424219041d10034031864081e94400d42940e0b40c00184260a8843c2890f0204582d42c41d040c02d031000b4801c41d0400c13a4015021484030611181c120340a4065900821551000750b02e041001d03039444c0e80c0c040c0c00801580249401d6020840300241e10604000d000d800800d608080003d000c211f039008405202d10b070400e030b0a4a441070120020700e6101d024040e401006941c695842c00b4190050074840d42c10704005080c00c00c40410b2091000040101d0f001d40700986034001004007a40d980050f00417075000748508103114248a005000500215812 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 707297994 1250 707296744 707296757
    0x105040c1a13030f17030705190507110f0f0411071b0815041109040602070b010f1a030a090209070f020f1614010201091502040f05122a09010f140d03 66
    0x11991505040304d4250000c0c1c861702001d03803840900f402010300841c0325203001e5a400da55103c040e45c0c1d541100354550741302c1003000401d01048000804400200000368000c0343c6450a624254000841540303224020b035170000c0c10401c040180045070005050041c1c407642114007680001e5421a00c100c485101b1000250301400031400d4005100580b190170600a00003000c60fa144100890186001650200c0e1400e034000f03000010b200e101b09190307026010101c466810306140420b000c0010008a1059140260000101e128215503602c10001c00e50301600142107842e145101800e0341c0d04450b1b0b40030150141240d0181d1041e00850b604d030340c3d40c1c1c0c1850103540701e90501c040283c1090700501654103541d0703205148000304070354000e80028050303034190150359035003890610f983d1280ca9602140c016000c51119104056002c900c40001c42c6080c4104624120103100d160099507007940f02940220011b0000f150610440391041d050720200c065807a0b51003414030a02001e1501020090000b866 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 707299244 1250 707297994 707297999
    0x20307080c0c0406030312140c040501030f20121003030203030f04050f2b030b1309150204080c01030c0206060a15020307060617120a02120901050c0105040c1a13 71
    0x58009001210210021a40402c1c0080045000c03600640c1041e03002c251074100302c4038044400c7c000c2c40c10450500410790b0460504448401c4580114011241455210344007140c03d01d00a620a80c00780c00d0440e0250a040320035400c0308040e81c05820429601d10441c0c4c002040681c035681044d040b2913150f401103245983d28220964182c2c0098000c4407503004401e12581c1d0840208148a00001c1c5917085180148402d61422181d100041c03580051505101c400320445d035544d803030342c0c400700c2c482c41c40800d90751788529190799051003070100100e10b05e20104011403210702c0095802803010303003a2000c011b50005040d040ea51504102c2d0800d5100340700301002d000d032307081d54014040c41c3c1c0b0040c0100c0307042440580d244000d884050704203100c83d548603c0054410402003000040e4620410340f0341b850103514240094441c501102c05542c1c91074005255450760340f00750115900051004000c20581c14186804203003404c440c410118443d880801280448400034111404c4d00000c40524003002d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 707300494 1250 707299244 707299253
    0x30815010215240102190f3f090e0402040c020c09070207030b06040b09060f042903060606030702150907030609060b15040b091314160f0203040b1803120d0603030801050907020307 79
    0x2200c0220440b84000a8110502c14007050f2120388e0b81480e10300154564040041200203200c10302c1410030007040400351042200c000340d6400c4503045a0180c03004180b80f6031415081e880c000c0c40c019803503000705000b0100819181d003ca84103054078424847c040181c1c0b540350800007503802156241d030740032210b40f0104110380b402c81c0159442d00405030000c20030308074006250340f0318201d48590340d10442c0d002c4450b070024a070500c65143c1c80981121240d02394145464000d5403241410a1001c0da00c0c2d000d0089648500700b041034200641c3c1c0004140440070345450a000500511440c1a001c0c40c007424400c4481d1030080151016241c181280350704215035042045804000c13940348004480e030301c40c034a0300880c44039a40203204d1b00c12413004c0b11244500f50401044500d4040710a404c42d0400d0005201d0030807090101e8802e62443c00048a070f4028007000070717081115004904103150b0000803c0c0c1e4400c0c00039007211040300d00036210002c0300e0b0b90300c006201c407680c000c42d02c060058000700b100e040000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 707301744 1250 707300494 707300513
    0x312030219030c0c0c18051b09060714071211040603150b012303040212010213030609150510140f061e070c0f051003020703081501021524010219 64
    0x3843d0ba242900e8519040c1d220000e038030305941c0264550641d0300d143c580c0400c43d640601500a00e580c0010091096580c0e292030320340c044e80e161503214001c00103201c0d00f030040c806042000300c16110195008907a41e01c212a00882c0c01580072151101c81d00e40315503c81c40c0501ca01411241c10102d2040c0039110b84018100400021080c07a05004c0020589908004460601006020341e01c00146e542e086c180104000341c10390b048804c3c1c00d6801003004c480244a8080040202ca601031000300d00c48480b07180290840c284003141d04100c600d800d040000915000c07420b00100c48500b05405801b12204090050813408180c060790414420130000021400440741000007240c04039209080c0903617691500c50f821500e5002072740d00c002c801c0007803201e03141c1214440c0720902182801c51400c84556009032149000034450301c4007046500f1080e449034028090841c1c848168600c44203140b41c6480c0d84040c42d05410b00340d03c114162020202900c0d400000c1c4084544448648400c000c00b0a94488141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 707302994 1250 707301744 707301761
    0xc0801060f11160501092102040c09081b1f021b06090d030207060f08040f140f03040e09120418090305130b090f0901060e130e070f031203021903 64
    0x1045035814411803844010312a15443c0c03001101400c800d0380ca820001004d010b482d0308000d504203041c14070ba8007006018003980710072982c15540400d02c90004c032000c1c2c82c0101640d21200740c03030245680300e9405e8482d20740b0100c982c80086444d48903100340800207042140d2168259005603119401d0340c04080baa6158469290f4030060540349465607100c041000d2404d0385000b140583d0102c40705101490b0440e140008076415850440c0b00c5141070b8130b402d001d02c05400406005641502c0509a100a040c01040f00031800d00d411650341d560b81e2240480842005c5911503c2c500941c030320110416407850888003201d080d441400c5001070190f009034018090144100d080c4030b810466016812040600b11008203034031612651982512010301140c0e660715010a81301b600c00788018000c0e10b420031101e854892044d60030030b43d040108015400208080200010385116110b000100381e00d1991504098900c10030600003403041c011000c2e8141d0007004801011883d00032055001a4400e603c941007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 707304244 1250 707302994 707302997
    0x70320070f061a0d111203040608090705040506100302031506040f080c0d1208070c0204090308010806090d050d020d0605120703021f02070b0918180c0603090606010507020d080406020a150c0801060f 87
    0x406550406c6458039680c483e030b1024003c684030400300014206c1c2408000b0082c5401e8805000620300340303000030f40070004501c11005056011000c20380011011401c030744200009480d0301e680b1510f8032440104122a40309542031171282019510050404e003440940041c0e020300e0b0202c40d158240e40503200810300828090400841c410400b0143e9654000c21031003500a0b140e0580701d50400c0621403e243c0011300701d00c0c03940d0108184c1c1d07010381d034030504a903440b00c0203c6005841d0f01321031040d0720140032240d001940c03081091084070006440800c0d00030881e482191403040100011800039a20003410240e0400750700704030000c0104c8280f1a0081c1280305008241d03071840901c400048408070802d031a0b20007000d20092a040c60003008101050010004030350a074110310700060381540d00d0350010101810000c1c01b00b0040d003151544503030242115030261845841d55107401d0000e60307403003918a041d103940b8400308030000000c94074030a521203480c00d03030b440401c10380c01c00c9025101c81007038504c0d150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 707305494 1250 707304244 707304259
    0x201090b01213f081902040906080d0e0901030b0c0a0c0b270102121504020405031b190803071103032203020a0b0301060206070320070f061a0d11 64
    0x900068040403035a00215209a0100f614280810103203500751101d00803d1200c201c01c3c580801540e000301000b0350105000203806851040f40f81c010001c3c0c0070f0303a0f10880025007003600124942002080802000c1c0103541e42d0a000d1004400b0810801700170720018103c0c90807500402c81d000d02000c0103000c80706a03400c0079040400e0580d50b001070b44c2d2040710314a0104607800103101124085c50410b07c0013002c81802540ac0030382a048406031800c0207059078451600d000080c440c41d440b95010f40c0d00410008060324080c840f01c90390005090f2683c1a030500c600320039034040000503541c2c000394080e510103c0096042c12000e9444010007a01441040e034148014410540c0c88614a44600c1e21200302d0061590348500e54418409000095001408050021f01c0107004d11980040d819130302804915010404041e600c4071103080d8403102488244032140040d0950500c4405a403026400d88220402c06ca0110203a140d11004035100d4681c0380d1101c4107800c01c00c00700da0018400e001c441001085003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 707306744 1250 707305494 707305559
    0x2030112080310030c1203030b030d1d0d05070b040e060d0b070804031817060f1b03181203190608030f0d0b0301020a030c020f0a0b010e0406020c0109050705100201090b01 75
    0x1801124580c00000d07420546046c150400d0750600550071711070010b500911102c10314280203802030201c1030040c03a0000096110042d03c3e40c8202c00400740310303005410758210b1600e54803009a40e0b80b103800383e90038001c0300740040349aa003020822401081d4004081c0d00b841d480e80c18089601c2140071b001901089155030764280c0c00b15015114200074030540c0300d100d9060015102460808034010710943c08903000c80104410f20b0907440d010703d20186159102541c0c0c1d40c0d040c4600f40b06001080c0c4229051045a110304a60840350b03009502814030742e454000c3c2e400b040c050329415100240103000311a00305124110700c0414490103880b1010510074040b604681c42c00200e803c9802000d90394000035125141101c02c560144030f811401d01c0e061018010030f00903074a90942400040c801c4913196a20368000030b040c440c80d030703041d10b0201410781e0081c014102c46007082640c444050060620a0241d5078220702d8003070051040307105507944004d10003401d03072074202a00c40f02118810b07112502004200c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 707307994 1250 707306744 707306753
    0x506071104020712211505101202030406090b010801050405102c0105060108100f061409031507180f0b0a020a0807290c0d0e1905030c0c040203011208031003 69
    0x114242a030903540e41603640310ba4000c90354807070fa4581d09082c1824501214500507000101a1034141c40d0b0030365a8100d2340c82c0b580c0c0c04450f558100b1450742d00092000c001e0104000581e00240c032501d02964035000c40d0390f02e5648441c2203d01c155001030a60380301e900035054032410303078010f46800d40d0305250003848005100c4450425500315055a04140d5403502001815038222110a8201c6000308044083d00d08150084107911090b01540042c40003601d8110a000c1505045030b40005010b0f095811400d0540100d1510700802c1d1000e0000c0740d24030a0100c080c40710b6408200841d40540c4120210928000c07082e2500d0b03200c80c8140c41140124040705000c18150030041c03100500c607086000d11205c504880c0011140300e030500c01a031007904020b000c0d500305008103039040daa407841d00008162080d0140e107440d10403080014064410081c0b030503414050044081c108840c0c2703000c11f503a14002c05c0c0c01080b041344004d00440c0b040001d580302c0140861003000c041c540c07200a0240080c2d0a41d16038030f8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 707309244 1250 707307994 707308013
    0x4031209050c03010c0c1e0c05121c0e010f050c0106030506010b041a0702010801170a06180c090c32070804061d1c06060509130210080105060711040207 67
    0xd040d94103501c59554400c00741400d1040200c404042e10300803030a10902d589000885540380c03400d0301982c101502c144c040c4121113079090011700b0300038202007e01e201c11081d180c840d0260000359680c854848460300030b40380203550903005d07200160b45a00048040100507035040d00b0500e41414559a07420020000a50402005e0f010b032400d5162a41c403589841010758030801d0180c10704683d448140304940c0141d8011444505407641104004116103400d00740b1b40c40c001540c400584030310704001c41200011806202140c101c2c0c0542400c03821991a1044881591940b000380310000d001e1a85404043c0441d03c030940c02e68131943d00b40b0203503080d41180b802e15504000c00a030303800400000c041280315042108803c065081d10000f036042c03010303040000d4044c51400510001d00d0280c0b425281000b043ea400907003d043c1c010b056503c42d08015040c0c2d5601d11113210100e0203000e840c50010181c0e40100c000d01e0403140014205d40c548500d5645159540844a04081e04107400f4414400000e8110f00d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 707310494 1250 707309244 707309261
    0x607110307030b0f070306030b180115060909110405031203100801090b010e090105070e0103020a05160f1a04200406030203100f0f02090102030714150901050906060103140609040312 80
    0xb001c98043d42032020303685002c071001400c4041894034100d0100001200b45420a07440034206000300c0c88a942c440620b4058070003505400d100700140240800c140e50050342d8001075903200203080003054440c41440303016210314000c8a83c15440342d070440a815954000031513005079038242000c0c007030b680d600c40c250a440d80ca800480b0010030000050110040b1000c0c4690f000c00810024025802e20341e0019109000d410032190415400140520344e19024504586c00f04001c1c080b540610501030510300584005100115000102c04541001d6414100e500c5c6000300d4101c4d201506542c0a211000aa007580400841d00300b80c4030b000c0080945d4080c05008039410a10030085141e03406540c000c0110346107000d4000781d8500c140800b1b810707079074000159841c555005400d1821003600410b1180351903682d00b005540000c0381010840400c4043d0042c0307003e00c0b0384104591042d100c1800540558a00c4c03e81c500d58111440009061403400c2c11059400c2400b90500e400c02e21310001c0740c03405071900300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 707311744 1250 707310494 707310503
    0x3090106031104061508370b1f05130308040b0a020f070f090203040c08030f130501021908073008060f180c13030b1501031109060711030703 62
    0x1054200144002d0625161503070604403020030003035050a40841c0364251000c4000b04002051000603400001e50103003042c000c540341d031628094045041c8a10b00540300c4045d4040090400e100b01c425400c00380940c046440c90700701c03401c1194a040d03034100c2d003c1d00076501400f80303140c03606400004155124000c002030184c0c0411103a0b111940c1002a01d0554900e802034201d500080080102c095150000d0095a107c0c00c005070b45c076211400c1c613541c24015900228441e010008031b01110020200041c074003c0d18022094401c2c0d035492005907240d8058103407554011140d502c140300001c880380d004010b00d510680303036000407210403e048071200d1441d400100c10411548011080d43d40c21254040c2d01080885040c0042e542820106d040071211124010078408280301180744820b115082d2100301104428036514190340e130a1801009a0030b80d8440d090000e0f0b40d6580c4040d501c0b90080c191244100f207845480c0900300402c1c40100c1d4807815040d941d4a46684142c4500c0c1e50078400c2000441c0035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 707312994 1250 707311744 707311751
    0x406031a0f0103030e06090612011203021203070203030a0e100504230105010b220315060614030402030c1905130c02190f11300d1407021003060308030901 68
    0x2452008040d0901600d040307510180c031001003001950003803290784141010f440307003500c1d0f01c8104040303001406054421a4002e592070000f1580580d68011030100b540039500f1180d1200c070040c01c3e09003034842550303c0740050300200b00041d601415034121041c004580c0c411904921941c1074910204d4406031000c0700c21410011101018010264801448a417244002c01c00d0794034007030b4042d00601c00c0c403540c2c07220f10000c1681c068001d07501d50000c400071500620801d00c40c48901451200403e124007980004c0741c84010b5100729000d00030241d900c1103901800910700c0340c0150041000010087d0008928680c42040c081419203a4012181504801210100c4ca400d000c00000c2e040101d14900c140000300280214404500d218102d02c0760b1680220f4070003601480360002c52079040c2001440140c07040c13420200c10401e0401000d1603000102142907030120404c122088900c682241e050001100062140501601d0010b2446848800d0313400c00240340c1d5540e81d115035450300200c8518855035175 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 707314244 1250 707312994 707313023
    0x7050702121005101a18030c120312150d03120f0f0603050d0e0d1721070f11030d0203060d0c12060605041e0c11060a0c1121070c05040603 61
    0x1040500b0b074028048040c2c48000128540548211a0040d42000170342d06c5070017030910a01d82c60903c03c0018110002e01850b03280444d42001e01c0c0d0b01d0b072100d4202112a07904000003014a848070b003c0a820b2200101030002c401e0043d1421510b55080f1316500040c50340da508c801f0090b811a100d20700300c42c46403c02c00710311603145090103070420b81d42d006e0141c14400f00b01e1960301c080d510741400141866008c0d0208906c0241464208042d0049008085d052242001c04003403038240d0b000141c0c0708803d1640c40da0940e40320b04204031042c91542c075070035119038800d000c0030060744842d40203554050f03805004528280c04035180c1b035080d104503611103041410b51606103c1400035602136000a0304003900d040c80310510084894103101c250002c0180a5545c0d03040c524100341c402e00d5907104c40d0241c8070440e503c0e402d04642c010024076001080c0d60214084034000007240f00c0205401c400544c0c906011281c6802d544100c0031540e1081d002283e240f81203c41c045450b545074800d80c8060360003503141d81018030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 707315494 1250 707314244 707314261
    0x80f0a0506090319050a0e09010303120b1005161a040308070f0e01020705040b0123040f05040e1b03030f0f0409050106020f0c0f04020913050f060d0b07050702121005 73
    0xd034082d1100032190400c000e00c48108a01080c0010318010070b2404d1030343c41c0002c00c0d040304e12150b03c0c54a02c4d400003a000001050540c41051221520303401c5d403007003121800342000c20072130844114000c0d022175410300c00c0740c440d48100380c044603540780101c40205454442c8a4207140f1030408940840c041050181885170140c0c6c00a404401c1d00301508114501d2080d030000030355501003d10500e40300381d1319a0301802d0244d106c1e01c0c044034914000d42008100c904c2c101c041c9c06094105005840c110725550703000140b2842d0078043c100c01e50724280003420410000c080044404240f0392407203501488100910400c03000d80400800b100000c0c0d40035540c8450401c44034030191401a408201103500001400b1038003100419824040c2d0310071180d141c3d6040d01c2402080180c02101d0a80354400f00b00401c0d203552078056000644190148a0304422035a5003034100b14103a00084400750410011a0028011070301940052030340c01e00081c545402078514030f400a00d0f10601104006005450f24188481503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 707316744 1250 707315494 707315503
    0x20031e090703050a0b04030e030a06140903040609030b0a0e06070c0507170d11010f060f050906041b08040305091f0801060306140d0c1d100f0f0303030510080f0a05 72
    0x1420031809441001c0c503640390966130300140b01d800f5181103030000200d004c050240b23625860001d0042d0030740f07840010904001e00180100703807407052003000500c0021424040842103400381d03000360310ba044019055480d54605208000c2c07815030340c42e0b619105a01d0541080100c584a04540daa50321009801f038508075040c541c559009094110100900885594001c00c9015001089203005d114100d80c8043e03d501420b07240415103d014903180010501c8044511042c2c20340d00141d64148458a8080902c000c841d000c014412044542d80c50621090344200b00690300a4020318103181009406230004180d1101d030f1103165605040b489a401140317400401880c010700d4035040800110385001460312803d0b021a51a46c031941c0e405002d0700400c01c4038009a005050000d116a200402c2280d404100c1001501c503039485010303100000460340324800ca44425129403e981c8080549169416405450050a00b03104100c2444010500500c104003009031004403000803d005170036030a003103081 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 707317994 1250 707316744 707316751
    0xf0803040c081209011d0120010c14030709150512100305212d040f06080112080405040518060702011b0207030f030c0320010515010f0f0320031e 64
    0x21143c1804092000d030307089032441c43c0d41000103a4604800d0008001226850038213460b029030a01811040c0044010541c0005801800b80e1603202d100041104820b90070f000c2100c0c0d00001650031107003840380802c400141800e034412410064109480d102c0000c8080f1401c641c0c0501040c1c00280400070320100300305c1c50700f540300841160045034015001c204028031405c0f14104048110556900c1645100d400100740464890f1086403106d8030342c00280000c070b20901c10a070000303014000214502c0c101081020b981c0d030b40f01511078a003520301001e00000c0e080080c01e00311102d105250071701c10141e040c48114890445940001075041401c0100c0803403040c50381c4084210341c48040705100241a4819140d0342540604211449584030300c1c0441d1540400d110510b0250408081c940707104105410183c051002c056a4080354a680001141d00074980b031040fa00246904440d06811400b907841741442c8044204182e080c43c12800f500742c0c2d2940291102e45c01202c8054003580f80c9810648540e40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 707319244 1250 707317994 707318023
    0x6181a070b070e01320d0e0f0708060103030f09051002010905010f0b06030103061d0304150f03020f09041508070608060f040e0d080705161b0e071b0f0803040c08 71
    0x100a142480020000101c142d405046120725100c417003145244401c0d00d49400c040501c079240c0e030318110600300002d0010a101407029108001d02c0c01c2c41e100d004140d01040e941104014001a86181c40031540605981c03449020b00c041311001103519260703208410003061598001041b5000a40f602c00d0031035128201000d07141e441d11440080740d0341c5401c101c2341181c0c0c0050010481c0c41104a18401c91300742d81405241c503105c000703000074030401d0b50380c0c0d0710024604603211001400c00c4100241c090303106200b80b50441c042c04201071100e41c941036001120500e002d5044001c02c0d03807101407192070300b0881e0f0020404100c804003044403500c2c0c4010501c100e41c000f618240005c01c501000740d03a4801060307952070184010140068000d610410598905200e00c03202d410300c2405608000107900d035040d24a0340c0306100d200000c24800705440305180524480c1c0d0b140700b0b10150307641c0d40f882d115850880440d040b502c4000c1000200b10042c0185020ba070141e99041045881c11121511b06140c2035280301c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 707320494 1250 707319244 707319257
    0x105030705070813050613080f0c0d141011091201060b07020904110405040b0105030118050618010e011103181b04021602040f2301050a06181a070b07 66
    0x303945510005940460b54402546622040000c290a01d681403d4002c16001000810032060f120740200382001240c001106403260b207469090200d4480818800c0c0a40110310800e500e03001801008011041007840340c160780602d180e142c00f41e025594600d2804202e0f11000c60100c100b440c200b001482402d80d4080200301403880c00d2003409507400b41c040042d00c6441c000d4001018004010b03940c255003240107000300107600c0c0c9440c1040e0ae0010078003a03a8020b40ca41040e06114142c1040d90b103006c90b400c4401041980e44a41101680c914003a00c5c1d40b545540f500344681c04180c0134010740d403d00410305141500c81c0b8002c40d0b00c00c1c2d660004400d010341030740182d01e042c0e4101d01004c80c01a000300145d0740583d507044800001000803802501c0290024513201400983c01c141c2c0d404400140006050385110240d858407040d80703020300b07019040d03200d0310f4148100819800358480e00319908031500c10b10342c400e40ea9a13102000e000e152041e82d13000702001840070100280c14840e20b60001280c02d200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 707321744 1250 707320494 707320501
    0x20a0f021903081906030b0103060f020315040c0c08040e07081308271305040215120a050a090b070c0302060a020c0a113d0306030201050a030c0c08030c0711010503 72
    0xa1030a0760340e480014090001000c080703840500481c1c052a1241c052610901c501e03079a03490049000102484282e88035460b00210518411a074022240a915130301c2c036240004403120104402001e4551360030080c481189901400078049001920040100d80000e00c01c40c03078004130103488907000504120154a42c1180c1e0340004001c201550b05287d2980e1206141442000f6003010b2020009640c0780e0002d00300900000c00c0d01e450b0401c80c410b2b4070964100c40d11520100200503e402881b03400b070b403c01c0170302c400240320800a62129900940d00e601c0441d0b01d030040e03155082941c000343c8412000810030b0640805240d010002690032840c0c00404516240d0090312054030b40c840080010114a4160144080c0d6070b00c5d1400088815407a041d0220b102e50200350087c403208012200c4205020745416280382c03075001c0e1084500f182e0701a199103140050310403089000b0042d1403200003c0c40311845080003c1050304000d984220414a2481d0355250b03d07003081618441d240310140d04010042040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 707322994 1250 707321744 707321773
    0x504120201020c1c0e060309061f05010912080403120507060506092215020a03061404020309060103080d06030b01090933090302030903030706060501170709050f040e06070201020a0f02 81
    0x10f131300e000c0314901c00310141c400003c134046414401141100781e11003408401d2000000011810500903504004441607a007086401c03030768524214400c01c0d0124034405c0d030801480010a5011000a2050400750b1a01f0f071607640d48444580550010340008101080e0b1104000040c421660410303403c884403126482c10740f4140589640c40c030a1032880d500d41085000400400341c0008143c03001d10201035440310503040c002801000d281c80b40190100ba003018178400e604081c401c03a8002c65014000d40844c1e829500c900555901c41d801070707107146030f0301d240010210345024481400707010341410100700e449450508102c180501e04000b0f2201108082c01413070341031500043d480d003441405000c98058203d0030103a08501a1121441c0c16004c005104420130590b039100c40143e4070300341c0f2a40440300c81ca002e61545802c045403214040b40741011f062041d803618400461551900500110b248030b0442e901900b46641a41d545025039000700391a0842500180007101c1c000b2148010404034050060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 707324244 1250 707322994 707323003
    0x3020c15061c05010f0c0201050907050d0503030703051b070b0a230103110109080a0f35160f03110d020a15200c071a0711090601210504120201020c 65
    0x4504101254903914500b0003d0a404c02d0b0500709488500b0018031750210f0010b4042c00e0120782c0c44c201030068100c040345510300900c03c83d000e20b400000440c110b50310000700b5802824058081100b5044999490300140c02d001d00800c04148200c40d4105503040c90000ca8040d07030741c01e010030040310785141034110416584135110340c11a900690f15140c8030740c10100580f10503c981d0040d61440c040d1100b04420b0041160280b800c5c039210301000340c400b01c1c00d0001002c1e010001ca47d0220024108510380421001c0007001d86000101c948000b5007507003003036417210922868400214080740008402071105070090000710031101c85d5001425a0030000e039610003000ca02c6600a940c43d9a40d40d600e1881c4510342c20101c100302071f4000c0340f15622450b5100c40f03035468190384103481c810501c01012119500c942410344d411994018644440703101c0c04810400d0310000200500e041080c40d0300498070001065110400c1080031810000341410b0a0a20350031282e12030a020307042da07004005944c00b07800d0004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 707325494 1250 707324244 707324269
    0x180a0609060519140705060612070e0c0a1709010b031216020904081b1c0f050405010804051609090b0604050403090317073f0203040612060305030a03020c1506 70
    0x600d1a1038a1803030001c0e240c0c0c1441d208824281d113000301d140810008006003460240380c3c100c0b040c100b040764007a5825591504d07400b07040d1040c42c070480810308488055000d80150320842c102002c545608910340e2441201c00c0b1000b0050740c0d143c110708802410107000f0b00040340c594135030f690f2604a1090301a030254424000090142401c079002609014000301039813126a442994603100040d0755085ea079a84880c00c4445940c81000808641c1c000e019203214651403501c3c0c0c641500b403600d000015540001c0087c0b06031210f018510182140588000c1c0e0040640315071b410001c0c80d200d450615200102009117081d004034030784020b000c08079401440d0641100d601c00035001500c103240b85425a1b07400303400c40c010304107401000da440c041109095070300c1038841076803011220b1005c0d509110350440c4050070420b0240e0400c02007070101500c5003504600c15111050042001a520b5490f5841c0d1f40c4813007044000603078003003000094400140020184000301e07080301c50b040c1c00c0c1040020405070015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 707326744 1250 707325494 707325517
    0x80a0515010e03070e04111c03020604020d020102010207051e071d061512100e06010203120c03090708030c030d05181015050607060e280b07090b180a06090605 70
    0x11805903000f0340c0c0c2001803401800707129034102c1003030419241c00448400030074542403044002c0c50100202e0442c207400c0c0d000c415010350007041c0036140c0350203010302e107201644c007641195020400710001c1102080300310000a540e01c46e0001c503501d04500c075400d10006402c400d034914014400d11250817031070003540307400510480c0c1d003c00d807a00c01d906920b130501c00c4c0d84544542c001e0740000c1003d0034a914005008403006905e0201e03c035a0341900481c0c50748100b031811000ca0094038003080d00c600c582000b4541c00881e08007110503140d121002e40d8516040000c0a00c0140d02c00129011318012900072140c00c0300c0e42c01c00c103072090b0f0003403544561142c10b0503542403080b542e54414081909440752604c001048068401c56951015080200151101c02c000d1003551045072038511884688110b00c1c41a114906241c158010403070307171604c000046c0988103a080049101c00400c86076155801003041c400c0011507000598080c5050080103070856003c0c00900c01c030358a08118451b0000c003190748001d901d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 707327994 1250 707326744 707326757
    0x2309061006020c0f04060f0b0711010809151b0f031005011404090f0617011b0212040b07060b030d0f02070501050304020a0306150f0b1c06051c05010f090c06080a051501 74
    0x135200030a0080c0055400301c0c8654584180004541403184001c0003c00d02805480c040f100ba104c00560b0880003e07a45900717290710110301d1354841002000140d400040100c01c2c07018a5040040508040d00001d030040031001d000824801200d0f0745a4020000342000e00301000e640051842d048002c0c091441808205520740200822600703455201c1000750244140011550381e4190065008222441040502404001419802500008604c1140380d01850ba4516060801c00d070102503400c6004100c83d440d0301c0e41d1005603281d40c103114000b4954011f42e030748408007050100080c42c200055102c0c6041c4081082413002685a020284054a81041d0086942003640380600020f140542c01000069881c11002c10b00d034000c0f6000f0400780126401c4616100761410543c0c08882052080541c4075118034100b10000c0748100600d800f05016100001d1800c50f4425480150741030b05800b141e103102c3c002003c0c0a00b60308068140e80000044a0402c61440c01020024840250b454168140820f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 707329244 1250 707327994 707328019
    0x503070f022b02012004140301111b070f030b0a05090c09041b09050114090c13030803010f0905070c02041d0a0b011a0c03070201122309061006020c 65
    0x30001c401403030b480c2c500c090148128a00540494403151000c0c1030065007014189400300a1003690540084400d6034a0340ca0680741c07220745440420b5001d0301c40d8055403192030006503030107100701503c0d01c03a00283d0862050307000c4d102c0709402c00e4243e80005a03d07802c1d00c2028408198040b0860340d01c1600e8510004194441c07801280c640b0700b02d00f5095030700421000800080180750002002406110400001210780354170044090b21424061a481c040804101801600d001c05280d078101c0d2500e03c1141c601900c00000e140300d9004c039041682c3c0e2260020041240d1038607040c426005140c20107040125003400100101110f0551001034800c0361610402c108080da9480c2100d20007801c0070403501e1a0b0040d145c21110f03030300c00344114880421503c1013081e2000044045070078200136030340610b180646540c015070356007001d6070300150318950710320500034109601c0709284840c901428082c003040c03501d03110883c0b81007402880c00110914501007000030a80000d4442c0035403908627660020481d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 707330494 1250 707329244 707329247
    0x20313091104050607122a12050909040c14041107170d0e0106080f060112030f020309041404020a140f091509040c0609080160090b010503070f 63
    0x701d42106502c0180000c983c4108000e004111b40300b81041d40b24070380d080c042c0e0700040142d00d48520f001c83d14400c030845508002040680660800210760901d1804c250501300400c61500080b501140c848440003400d2080d00303420140c44170300b084115000d009512088688150340d0081c40401000ca00f4218180300300c1d1801c0344d0540342c005402c9041001081000b080d800e028001c40d118944c500d0255050324400c041c1b0100e401c0b4140c4242c16800c03040d006c0a6a01100d000e40410020000c50009107d44a52982c0354010700f4180c6000c416a81c002d810b00b03004000700a005070b442400085101100100d941d11200c248000422040b10845e038241e6a500a4030040d000d001d01c01c0354003403018020081003180c01c20800c025a42c09036618101d45072152140d234203c4000c40b1010045a10001400101c0c2c2c5c0b18100107291008284000c0a50080000c0304010003401c0b0080d15070041e1603611601c00c1184540e010500405c0b0200d0140f20001400b000031b002c40c400546002c0800c030760f000c1d80c454201d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 707331744 1250 707330494 707330497
    0x50106140c210405120d021513080a1e080403140c1608010212010b0f090904050f011119021c3903080c03091b04230114010203130911 59
    0x9112010302030b00d8180c8a40d0307140d807a60040c01120303c038050344522002480390024400c0e0094100e6002400313101c041f88030704031700e859004001030582c0c9400b12107000044e485001800480b0a191110040310309511240020b0f404c001e10300c64208040ca0041202085c2d1010308c1403a082c00c0c95500659800d5000a26410090311030047d54a103a50102c001424100540c0188940020095880c246036203c2601141920610340100100107060082c3e44aa140040700182c000e0b01c00d1003203a00340c1844010203030a40311280d0f080320b803161012400769208043d2103506800200144041d00401042109040a024a541000041002c0004c154040340c145100540d00c085140f14080000b400e4400c50044000310345a088002694960204e01c1140111060700d000d41e1004c0c0c00740c40703031030701a4101440103031400203030b41e9129449080741002503c4c40c80344d01c4041803254142041d158108101700a04405403880541158410819000511424407a036002c0d151400c401044962400742c40e55582d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 707332994 1250 707331744 707331763
    0x8011e03081b030304140c031b06130e040c03020108090d0c12140408030a14070f02090705161a01051503011211041b0315140f2808010e01050106140c 66
    0x2d9200000c1408140224094102c6454041c50210741c5040f0b810000c2c9a164400481402480414101c2d03ca8003880e00d107001c2c1404401c40c0d14402106680c80640448540b002da80607158a4894241413080d0f503400300440d0b40c00b020110003000800304a440080500316240e1018148021110782c0d400380301e1081400c40d030000007050b0b0741503d44d511200030343e0322030f0b120b404207002181c004450b0070b00814051050f96103044d000f105d85402003145401313200c0c0e940001013184003042400c0202e85c804c181e0511000c41c0060054260b142d981210030300c0c0c806175280c103800a0340309000003c4103a4a0304d1a8100712415107005401c20b01e0241c07464038103040c0d0665241a0a60f0040c02c0040c81e440010b00c503568100d0750203941c0c0c0c00b486801c016000f090300030000d81c003801043c50b6411400c284c071810242d900b000032101c0900072200f4452901c8a0407581d41c2c0408001c01d1400c0481007c106010090040104100340000204115450110701410150500304e0040a0003404250201c45a2050001c85c22 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 707334244 1250 707332994 707333047
    0x409020306010303080703150506160c052701050303181905090a0507080604092d0203011b170709031103031c1b0903020f0603041518020108011e0308 66
    0x51070b503101d140251140038200c0d861400686003030343c1e100d91082e0040e0803004944002d0481ca1804020f50058020400061070503601c0c108806800582919035400b48481074241284d0004c039010712043c20000c084040e40080e01c254001c0c0711524814110007507105400030b0031aa008410881021503540c40704ca80da1141d0340c0000c9100810061540c103400c041d200d0606030f41d940c40c0d180d40b04010407003200e1060b18007904161100d9105a20301041000b1245100b0b8403000743e0f86602c0003540001e00f07450310004401f0101c4001c0c403030949029041103610491660400c00d032449031518400040c0090801e210150201c101c1c03030503070170b4039890074011100101e111182c2c05031558040f50030761001c1c04c05c0c20329050305490fa0050301d0766030f64860355240c02545d500800c45131820380351004100c0b9541000d0029102d1510712040105246060b1040941c0c8101841440004200780e000241c058a01680503184104035403e0300c03824500c4c016540010b0700e60040d81303161a01c0c94072001181c0e2440c10081c40c07c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 707335494 1250 707334244 707334253
    0x8040e22030905042a03021815130b12060907031b080601091509140126010e10030f020d060612030e0a09020406021b03120a050d0f02041d0604090203 66
    0x2024160321104600c140c2d4000d4400f4001110b4400d2100342d481d204917244c0680c03240001c001041c2d42e10075001000705045031000600c0500303055000803034000c54075200640c03407500090800c14290141c1c00e190010500c0c0f4041c281481e40c000c13045055000000c280038468601c110008000ca40640d00c0902c0d500c82c0300f5914a0000200385001d040c406040c1c41c524082058807800080085802c1145200700c0c0b819a030b0300800c43e1030008020140311075000600d042c4a00704042c44030320300e0551801d0b40100b00c24450000154540074147c1d28034000600000f07a121100c1c8014008100b214030701c1500140d05841c5800c1e00c040e81e0400100402058200e074240308502d514080505034130036059040c0f0007041760b944581e00c1d81c0750b0700d070300891246200b188056040f00080c4008200751814000202038080c0540d4003181c5407401d5070129034095413242003c5100820b5682c0c540040c2d10460150a440710000c40c41c01e418607540d50a03001c04040111050702ca08000101e864945c0e41103440d035698098100c9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 707336744 1250 707335494 707335561
    0xe04150308070312050c25080703080109050603162c0a1d0102090d170f0a0822050606130908070b06090a05010b031816090b040b06030408040e 63
    0xc14594482e603020b4001400400c0c110a00100c94414640128480d00d00c4a181001c113030400d256250b1a80d070031412034620040030b8404160440300401c2c1d0035209903204001981004c0d000d33812180060b040c1c1d40070f640255a03440444459a0f502800d488030f501c0083c064070315008400c09111070158040c91280c00c90424402c00003e19004200342094014050307041c6004a80c810b4201d02441c041194054038855003800440c81303c14261550303124a084a5150a521141000e04c95101d44e418000095111003005040b45440981661412180c0001003917001d16444541e036514014061034800c81e0040c42c3c541010a560344030180459201a50341d4889032a0708000101e45800c40c3c00718000c070741150000310404682e01c2580d050784e4840d1100303415a01c030099100d84403c2c100c2019681d910031100390030740000c6440100c030004c080021010501113084420b1000b030704c800c1002d07103018007000d006000000e0100b1040d2029142a82d0a103415940c1c2d1880f00301228011040350a4003143c40b1421 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 707337994 1250 707336744 707336753
    0x13091103010609150302060a050c01061203170f0a020d0b030f03070b161e0e0315060a0f0803030105060703050403121e05030c0702091b0c0a0b07020c0d030e041503 72
    0x6140095004030300070040241ea0310059802d80e82e81620240c60010290014030040c5000c20203889407410354900a401c1c1a000c11940d800c561440e0448805040107035400800c05030310940d0a400440b050364400300130f00780154412880300001d09074a080b19004980c080080800382c0c03042c6e83c0480020221900841d00e41c140a450b58030000060302e001e102e00f400101d10104440d0345168900a5039510310b40d0101c1840004581d0321003000c4e200801010f40200900c9540402c10307010202045406004182440010031903100b6807036001c0c1280707007101c03503041081140203c203603070460384160f03005030f80c44840380750413a5548281d4200402d00800306100e5040d4a80c0460072600400c42145200d200841107a4290380d58042190f00b00b019484c05c1126800600b0460308072a04078a03511800d0810f50210100c0741c9980d08000d084031016403007550b1103014400c1c03503006240c00084500281c5222000707280803d0444203620000380c240103007220040300541f07943d0300141441038040d549480140e101e260 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 707339244 1250 707337994 707338013
    0xb0a051504021b01050610020d0f0e040501030602180f0d0201051e0c16050f0d082206050c0613021f091802040e0f0f130311060c09010f0503090303040803061309 71
    0x640f40020b6203400c0004480e420160000d198440894000f00061a9a00030844141000c01d101404011075010004416100c5006041c0a1417050101580b16007142c41443c1a80340d02c1c00803144982810001c0d0702441e00c9410a10020540a1a00715601d00307260154100007040e0300b1000406c000d0004098080b98401f041c07500c0c003500104605c1000c6580c1714108460b44c03980c40c200561080554803620005601840188083d0f520800485450b03c450741c128050b0b139500e94000f801003117000440d0768501c00700740300c01580040c0020189949007a0341e00469022485248180c0290030006038107144640210180c3c1d004041c810402c0b15495080002032019410910414440c0710090006c075021081901f05540308846954140c1825a0b81403850500d01f48081e1044e001d0202403440396600390024000284240d00305400340390b0f1015004001031400c1c0402d1071850400c84180144a1281004001c42e60480d0f085000b07507440742c580e1400611b404816083c140c051070300d09402ca904110300ca18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 707340494 1250 707339244 707339287
    0x260a05061201022b140702011d0f0d1431060f020a030e0f040204030b01080c03060103030f0825020f07050d0201140c0102090a0326070b0a05150402 65
    0x88000a5503221030714200e00f82c0c000d4131807a080850040c10700114010340000089414014000045000700301d00d2850514500c1c15101c180040c1d4480c0204000c0c6102c039450304920341c0c40e400045c0802508403c98940b10000d804104003084421040c04510903407940c19103140d8040661078100010100d01842013200c44450103040039045414000f5a550142c0b00c0d92260a009030050090b420b240d81c3c0481d103862803008450392160102c8009810b6445a1025202946c41400c920341e503035041c041c40c20300d4144202c841d24426032002c0014000240d110100100c4a03c1174142601c4a803201c18407001e0720b00070540e2000400015030b03807040b0704590004030b407220000d8103020741d800107883d041400550b411444021340800d000d900c0610144144c00002d22070680044001410518100c00003001e030b00c003d80c01550f500c40d50001c1c100102d2002298860360210420480785880b195a46034062104010450a42c013540c520018000a000754100c0d126800300034801c41d50361804c4080302c4c0b907112246 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 707341744 1250 707340494 707340499
    0x1020909070c11131d010203180c0310050402060403150c090504060609050d051c020f0609030304020f040209010909020316080f06060708130305070f03110114030106260a0506 77
    0x1a00407502690180b140039a1443e04003d085080005080078050741c0e84200b040d490119a45210901021040781809001c044014002503500d08181030300110190302940110030940001040000c203580c002003656400c124583e01050300d40d03032400050814010342d4000b4091030f40e50121a1400d000941c0a51002d5155440d4400c04a0307c2d0024030085441c140221030208050020900c41c51070540c501b1000c251050044a440341c1c02d208618213515400302c0b003180540d000c1c0a081c0280c3d0f100744078459011108200031415403400f900044c00131400d64101c280160307400034058050740d101c0c00581c0040c0c548190150b540b801c2085101e44088001034114001405090205100c146499001c1e401040e004001c10700380092922005241e9002058000080000d081b000002071400c1c044100209116040c2e180040e2660900c0c4080b64400307000b6504004a0078041a11281034100780da041d60801e141500034040c5080d9130000103014002c080462841e21804c0148080b041e80100d8441d0100307 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 707342994 1250 707341744 707341759
    0xa05070b0a120b0109180608010c020a030f05030c071119030c051c0f1e1202010c0e0f03150703091b060e030a050318060403020d050c241e1209010209 66
    0x1900c1242c1d080340d01034580c160006a90443c01c1000041408039010809600a400a40310780c1e200030890858104908003400368100d1007000c0c0c20302d908815020310100c4d01d82051403552a00503401e42c04da00c5070700c0300100309402902c1c0703030146a00c0d818001d109009481c1d4100e1003aa4581c10110a007022034420310348201e645001c4c91080d0a036060050900b40c5d0f01000c0351782d07083c00070b0f41c07041c00e03001580b024822548503c0004002255140b40071101c012925000010140b8071444003e0265000001c0c5600a911032907403201c007618000741441d03218140c4c801c1e45030f00d42c6034048101c000d000e8000005e061140c0250300c02c4500d400d4014203000311071080e140c4c0b800c1e8400e1002455140d5100181c0a8560341050080680148040040386401d5100922580c50591280e0000310105011481941c00d41d0003030703600664070706000b0140040010001012080500b07804510040e6108521a080e03250300422500002000c00106894101d00343c98070002181c60030550090003900010f0156110313010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 707344244 1250 707342994 707343017
    0xe07140f0c0a12030e19080c10090c1403100f0b060d021207081003080a0201061d0a0509030c070306020f0903011404050c010c080d0903110d0c0b060a0f05120a05070b0a 74
    0x2920800c04039051071800346c07440c65060003080340882403114003625985020044d020340480309001c40300c00e03411095000900b8900900b0106413080341d540080908640307200c10100181c0c0c0c0010113007010060603001241c1d05284400c0c40c4090520ba1070780c550405404103c0d08214641c85e0050880c01100b1450380d000c668682c6000c480b500000e5a03006a4180000c40038800324407580002c00300040180000320702140d4544580d0000341038201e1407000c0380e100320180440c41c03886000300f50300200c0750f000a509200039196915100c10340b620000b026140d00054600860b50300c80d040d1482618002c000f0801601301c4080e000441e502203070100d03000d0090b5104c00d0349540c0640e240071907640c0c0142500741403260180200001b0300c10410182c05009101400300201c1c00c1c00c0024001d004020b42d03075a60072203040d15000d05501e1003d4150392141d180e110080c040c01c1c2c2d0045070b0702e0803500c0440d60551981d03030311400f003424131072a4440501b960284100204240001e00b00500401c14107179076184201c0c0c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 707345494 1250 707344244 707344247
    0x30f03030603170706110306091602011103150915010206130309051507050d0518370f0504050f1f08030406051207020a030c02150d021602190e07140f0c0a12 69
    0x72023111050380c841101004594950203603034841070402020300000450a00007401d0004580044942407a00603407039401d5840c0341002421181c120825141c2a400c0b4148200082c0d00d03901e0003000319032600385140c1d41c1d0040c140300720020303401003601424515050602c8030307142240e40d2040205940a10130f848071500304900c2541254000d1081540e10301d0f208455108010300c007179825035422812000d8640007403180c8140000e90204505502613540c0c814079001c401e41034006140e0017603106618040801401e1340202c5c407456800610380300101d12b0f0b41d0075030364000418003003030b0040c80c030714880414041204d82c1c004009094402d605d18503400a43d07500e2074202d80d030300c0d400c080040018030005818070060409541c1001c0c0f060811300c0c85410581002c8a00b130403a0454602161444c0784601002c0c10340c10001080c402005c8000e00e0351210340e08202d07207028010700142481c1c0800c102c100c9000794080c0101c043c0d8410620000015a0754001c1003102640d17105004025103410308010100c0c118503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 707346744 1250 707345494 707345497
    0x708010e0601080711010c020a030305160c060f06081006051f120c090513050f2208070206070f110f04021e0c070801020406020d0e0f0a030f0303060317070611 70
    0xc4144410820460760780400440d5002809000300e010b2080780001c07050003907002e00540b01c440c0040e60051246400c03d080003000e07114054400000707188003140514449074003a205100035074001c1c00214940303528851000042c100c03580320520a002d810700d015034100310364110700b0440700200c6613581c407000c9010200c483c000c170310594000800c10350129100c1d12042500517204101081c207045000315035800c08139000c990130b02141c1112070369510400c01d1083c1803d02007070b004400418880701d08081c05903c9880701960380c0000d80000030110b0807500b15640c2204946110f9403162030880e0810041c030780304020034204004244039907410320801c12241414820340d4007542e000d910750907a0500503911008241d00038040030010b401100804140010240014002450258024101042000d40060604c0088580b503885041c1e501425031155841901c441c5c01d403a0800e0701101201000d1905500420403940002c028901400c015600b400100010300003444c02100c06000468420003a204070307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 707347994 1250 707346744 707346749
    0x1513181a010f12060b0d090303050901090c061103160602040518040503190c0506180607050c03031501030b0306180d05030405340902071101230d060b0c030c06070801 73
    0x800a1400149043c4641c01c51400c00b403144034002500c0e601e914096001e03600c803030b4104007407070b0310b030800d0108050b41482060ba000542030000c200341c000a039508109102c0c90300c10101008080078a00c0002c2400b80200c2c3c0700041c0c0360038851265407451030170324040d401511450f8070401000d4247c0352a10000d80c07009100d0395100002c1c520380780c6048a40307070b40c07a0700c0c480301c100030041d035592141c00048003000202e01698050b00000c0d091128510b0551600c2c8004104404100090140319110280041583d810808006600107840e4124004034000c1014a00d0a5818843e6105003d02d4041440044011102010598190300390464007903a641c1300548004101394414a8500f02101c05601c0c1126940201001a5140c50070700e42c082c0710b00d0310150001041582d0008002007000380000e520100070100b82040008070075816041c01a6600c941b64410808000045c4040c4215103584543c001e00303910080d050b1210403117604141d40c4e8100d660484000d00c500404070f104240140f8400b0304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 707349244 1250 707347994 707347997
    0x301031449080f2701091b0e0408030601030b03010c030507020712053406170a0606050d0c030e030c06060a14060d0e0a02150919050f1513181a01 64
    0x210340c490028a165010f0001d180755000b400c03000d030080c4140718980c501943c82c1015000801c102106084c003006a00813081001c00801c000c403020003044400e040215849504000c00640329034440c030040c2d01404040750710070380c10751a080d1070104251301a40098091070580c0e08032008561201000f01842c070750050090469440300500000c14450075080f0500c2e20500c5122041124490200070311281c06508400c02054180541000c1d201550a1080e03110500328001c1c86010310b421006000c501c107260758816502c4c0c9500f03251410720301035040040700160300c0c1d08682d61800076001064030350304151589446a800034600051010403d425082400b4005010074640700c0759515500c002c11380640507251901505180401580d030704c040000034000130b042e52980c0e0340308202c10056400f4000302070f00c140e00840c0505000c140c0752104400f0342901d0030740b1000c1c0c40f0000d206a4010b24040c440b1200c1d510b82c3e00180c00301c3e05000c0506060b1241c0c40c2484c05101540a0900301002e10011842050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 707350494 1250 707349244 707349257
    0x1060c03270b09040204051210140f0403031d0709060906080a03091e05040603080901020c030622141605011403070e09040609150b030706030e030301031449 69
    0x4800d42030040108020640104018501035580010994034885000c0700c8a09800100c4514081c0c103003130040360001c120240702b003809480c00400302d0b141c030039014102a04065a550842442100100000d201d01d5003000465496660700d01c000700103080a03001c1c0c603001c1030403e8400142410000b5881002580c5521401809030828850101000b100f2105910b100e08800c0d0026160300e0724810680030318021200e0750391b90034050002914080801ca4118060b40c0b10b6400c10905914100e2480b19071320102140c1e0070a9611418146803c080b0801901e84a000e911410a0004001048001100e2013030700c50140c02060002d5800e02800111260004500714482c0d03403040c3d00d492090b043c1d2152090000103000c0c0059180c0ba1403081e6203101c151032131562800807401c103140400004000f84214903003070007a00c1c500b0b0010758881c00f0600c0300400d0080b81d1002010080030901000402c00003c21600300c691090800c0f00c0c0d03003180680f100d060001400180110200d211060000d5901116200c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 707351744 1250 707350494 707350499
    0xf072a1b030f05011406060c0c01050901020a0605090a2303040501030b04021204060c030608070305100203090f06040503040f060809031603140d0b0901150215040c0e01060c0327 78
    0x1921445211032480419200d008400030b0642c040580d01c90340600000a00c03190310071080c100d80b28018003c207100303d6090180b044000c00c0010140049a001c3c60400c0e00c4603180001030b0720301190064000c4c403e03400d000030006050300016036014420300030081d684480322020601c840307104440910000d560400c2005000d1540650002030354a00007074401482e01030040380c905038462003924220f030400d0701d51241001007941401424080c5c420b1101804c1702524641e03e1541e2a03143c0c04054400c00c5d004000904040414400c04c4000030442096800c42d00d45442d1050302c0c1d600c02d00031034401184006010a85920a0415500c1801d0800c000d5140105144000b00c0040d4482c90850402c0902964580b810300398002402c40880d11510100700308007a0f10821403c0c00c0160813030301a4980c406a00c2030304603400140d9404074150201c591040f0b44440c100b204060403e60007600f80d401c0303404000288540e0000c00d500143e070180d596490b41d1411084801d200c00d0031854030b1030280400c1c1006 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 707352994 1250 707351744 707351753
    0x9130c05030115020a0803040b0f071d1903020603040302100f0b0a0e0a1d030a03060909020d0219120b0402040e01140615041502010603050f010603031b060b04050f072a 74
    0x810701003070f0a801100c007401d5450342c0c0e050882c0c2c0100c42c05c541403200c03482800310003c1001c401076040441400c0c14058040d0301d80c21190f011207007031001485424601050b603003920420340024043c0d41c01602085d031f2458141130180d500c04070302450551140c036084003810b44034501c1c458007100c510018064031019140c05000c1c0812034010b85010201c2d50303100000610613456401002025000401071503c42400203070107021606d69503c0503510301d05103801000117030340e00d00041700d281e981150b034014111070301c4080450120494000c2000b03224410010ba05006003100701c00d219034400c031410320400380c1c0c4418560903503141d441e507521403901c4000461002e2421b0b0102c102000d103642d44090905640d0905c0f44208015079081e4400f5035510501030052007000d1003040350544c10302000703100c0189140c0c2c0050003140704810544111100002c0d42c002c0015540050140e00c0000308284400d05001c080c560080c88152500d201180030035154107010000440d00c1d086031003d00b1002d041503100c6494 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 707354244 1250 707352994 707353019
    0xa170a030c0218010608100503120412150c0201060f051207090c02010b03071203140307080103030513030f060e0d090305030706020705150c0c1002191404051509130c050301 76
    0x1d00b20380c40390420320352400241081c400503008012583e9100070300c3c10200c11001d403210b07041e08010700030f4118075241c03c060b410a0042750300702c840a0f09545d88141e13450610303158100040c450460789506241003c1c102c40e505410107010380c0d54020462420513610310800118000100c41c01c0e0040d04000e03800c2007040c05a51014295805500012507407883d42c500283c14800181c000341d0340c00b10300c03412503024950300007140f40640920400b42c500d50700b082400685140d46c144001801c1003000554000350400903020403004582c03000c5034008203c8203103001d03000750015088822007031241c0a0a02030b0340f8425032841303040300e400a0241d4500100703038460001035404254140d03900c0c459542e0245901e90310f140c0c0144202140c084650b01c900f5109242414208aa83c046a8550052060030b1070140c4c02054224126200c1c200013000c0c0003206500604c50146520040e4002c038a801080082e4074010028031804404840f58080c0e412020b501000b1101c0d030802e500c00003101072005000000c9603d5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 707355494 1250 707354244 707354267
    0x5010903030f0831051921020313090c030b090606090f121f0b0f090609040311010e0c090109180b0a0908070809040b030d02100b04020f0c0106050a170a03 68
    0x401c0304100d14403201c4c0c05025516024070840041c540c0308000003440380902140121241311083c0b810016115100c1680216840c0a080480c00780301c444001c103140200110fa245c00880490320364201c1d0345030b03603080c02400c0740240d41e0003081c2032080c035050504e410b91174148180c000800e42401c01e078400050201d840090220b094003c1507140401824120030400c11181602e034180341c50003800342d5105041650400c036200b9010b8912401903160540e29500d04541c080310640e14001070ba62039050407191560400b540103900d500c2d003d910051944003091701c9020002c00c1e226407030145d990340700b00011074401071841d80040f8032400000c070000b0210b042854203d4042000800d5169013038661000f90f034001e00003101d20700d400003501030890415004078154914110060b2200b503003030b030101a489240203164901b960340da0b1005d46000b03544030b906450440085560707180d16840034000710740c000d00c034502031280308400394071001541c040d81d244514501c4004201924400186541c10f440b0001201d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 707356744 1250 707355494 707355511
    0x112080708030c070c210312150807051801050a06030c050f030a06030606061d0433080613200d06090605040b090f0a110a15030204090605010903030f08 67
    0x100100c402240d000e0002d18007071045078003280e5841c5120300e480740582c00c40d0f42c403d444107240180309404201080c0c10410110341c060030061443da4135a00c03140024400c0c9038003036800001079880482c428100060701ea064600980742644042501c3c154960001c00901c10b655000d10b0301d9005111980c401c0d048840380d00306505000d82021648042184240c204840300d045180d55003404009100403402550300920142c202030540083c451103100b400380a07810350714004c5441c0c00c0e44100700d910544649005100e803c00c40403200038a550054035043d03403031003020203a00c6564040b0f02411450045080007981c000000e5420404101c10380d0b241c1c91103400203503070100400130000c0100b00e06006610a0074810940019030b46010f10707080f0b0403213402414040340350384901340030030380f0003000200710000c01d400601c04a00c055080001032000f18031500300c4404042c084150000841e010b4004d081500c001100c10301005031501c004451f5502a840041c00084021102d007010300e000d42d0042c4d070002d510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 707357994 1250 707356744 707356747
    0x1050424090b270904081b030f0d0902030c040e1f02090916080c210406090f081305180106030f150816051f050307020319110d0c03020303011208 64
    0xe402a02c0301c9500002802081d00ea003050302031001418441c28007000b400200c90f40c00302401d10b522000708a00400b040c1010190412540d808848000c00613035140701e181000c49651201c00000e4000034280c0040100e00900c24106115000d14050207030040440c401c200416500a01c409450300700d00103d0038042c0443c0d030030840075085807640c0c5104c034072403800008107201401c900c904c010b001d10802842540800802c0c48900300e0184c00b0004281e08414100e16064142c50b079081120042c80c2e0740b03c0c000d00c40c90100312050100110100600201d45400a00c0400c07540e075141845074000d410090b4914550000d0014072150380241e010081008000c0c80c0040c9080c601008003400d0380c0150040b40d126880804c0340c00400c3c0c01c0b001d410016060540e0700001c1c200700e54040d10a01806044554284880480000c0000e0301c00c00075200350040e210503c00c244140750101401c0005182d0483c2d601d40580b07909981014040d41103c000c45600d940150701c0d5a1134a480741102000c0c43c58100c0d4280c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 707359244 1250 707357994 707357999
    0xb01052b0903090303270b0c0304091409100501050f0607030323011e1226040e0117010b0109050f010203040b0f03060108090f071217030709140105042409 68
    0x1414815039452510a8843c5034955040d404c014205010148400c0c040843d50311490a12001c501604800c072000002c2094944001740c458a0070742c080c41c5c00c484107507481c200e01c01140400300d10b0018020000f54040d14071000c0380c03602c04e00c140e510900405070005c0d0006001092401c208004201b102d020789000141c2c140540e07103001911160300401740700e0038102c1c40140500c40396000c01040200c120350b20f14825500c1c0110300400003d641e41302614200b2a03a0684400042174a590151511251030b00759072103490b00c1054500281c20b01504084407019841d0440082e014402c2008a0318161621500180b9190401c03c08282307010f034141c1180000c3c000050842c0500015050096000110302c0d180d08d01880010801000104450b0007540003088a20800001140401c01d80d07002c10707844028032416041103940034901120010152900004001d0302c03643c010301107819100d00d500748403c034070b039020011500ca00403030180c1240482c8000b0010b14191852464801c4200d0504082d001543e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 707360494 1250 707359244 707359327
    0xc140a03030f0c09050901051e1c0b0c04120b06040f0c050702030d0206040803042618090601080907061101110a11060702120a08060109081b04050a0b0105 68
    0x2005904501207a00c900d41142d0360720003405000490081031601440451410b0006440c030007062140701d0040e001381182e00d2641e40b200e0821120900043e10820b1030310101c1001c1c20011038a0f0105484038081e003000710307564402010460f01154026115550700754103d480e10301d15034002070300540d80240d440401c03000794000c0d8000c40c68011a1900d400351101c602d4014107081c0810400c0150842d08807200700400106500c0680340c0040d000b080c40d1240e41104120300680a42040040044040100340100031001d186030703440006005a5041003e80c56400056480b0b030301c00d80d643d005d942c000d0b0a0501c101c503c24a03480803071215040002c0f80b450745032681e02c4942c0c3c7c82110300000144901c1d4030840008010001a5013040d540d00c0100307035602032607800011038002d451000c8108a002c40c08580e290b84290b0459000d0036800d010313100500501c10390407410740e022201a034000c1e420a0700003281f0003601e04c107440c4090f81c11b8407110300d0500a091a58007100ca001443d942581002802c818000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707361744 1250 707360494 707360503
    0x10e010e0103081b160518130b130203060f090114220602070602040306060302100e0616050f06010b0c01150f050d0206070b0114011103130e06030a150f0606090303020d0c14 76
    0x3040300002c6441e149040c40c040c484a2001001c5050640c0701d060203000c02d60f2001020048d60301c1e002001160380342c580d48000c0b402500203c10117075051007420207010011051900f5680990701950003080364049171410141010011034040390628015445034100c0c800c10030900d0115440340c400145080415921f43d42260800e42040e20207569698091045080c0500b20100070f0000307092280000000c140080d44610a4201c85a0071802c110f10f40c0b400c02c0720401050482026180030b4885072f68603045000407541002d90941215800c084070350806030351000e085c50945011500c0c044080b800d107014000c0b11004040e0481e00301b40200000000b041180c02c4a9019241c3c15241c6903007072002400040ca1964440b0783c402294008000015000308a102e4400c200c540d400c0c0100020b6503900c0c00a03052016500e000741554185002241d4000300584c0031000e81401d800c01041450303203810045842c0009070100401590045103113108550080c41c1200c2498451880c64007502d04960101d401c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 707362994 1250 707361744 707361763
    0xf1203060b040b340204091e050a02010f05090604210f14010c0302042306092701060908060a020d09060c0c0b090c030d031a09040f0b010e010e0103081b 67
    0xc4040407071030142d144004c52902e803883c0d401c0ca90641100500e59110703120904401402882580e803002c444040024100b46501089103503450301d03104000c0c0f418207070340ba0460004100d00051300402210f4803903000d030040d14514031000c0c0403282003900300900b290408242241c44411b6030840c4580d040003820020400090a210b01c101446030f180780181903080d1014030b1912428580103200520004002021300d40d000c101502608501c01040000300d1f04502c110310140c0e421803145800d4034441e048030b891130209010810f2141516a903501000c4400200600449906030042c2d40412003948058000c0e140310380c85080c000038444216074480303040b5810ba048039804280d100e000ca2040c0482210702c6513100306e291000d004c0710450100040d40712034600003048103040c3c1d11450315101e848a0001d000f2501d002030040026810941050642d45c5003400e000c444011880d4008501320b0481c91a15048441d40e02c4c40d00002d03401c0d0b5030740420301e8000d40e00340d800c00300005070300303844040c01003010380300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 707364244 1250 707362994 707363009
    0x120408030a030b010306150315030c090e1009122109030f08071719090602030c070b0a0c020a02060a05070615081b0307090b060403060203250c0f1203060b04 69
    0x180da2018550103000c3e5449000218103151030b003141049108440d44030704d6a002503610300003c4181c614100d5148461040d000035108130b03e550004a0030005c241d0189074a00b035010100c03020508041510002e9a1480100074003004140204881450059239078001c0b04141041801010440200c95011203c41320030a8001504800401ea40d1941100c44d60ba000101c600d401900304044091181041e00b003d0609482c0d101941d41390302c0500700640c4000803480e44040155681d040050740c8841c20741084400340d0b00e100408002c50341205484c442e40c1681c09054000d003031410107680800a00e6004a60b411341840340810401340011424804c0900080004000103007171424400c2c034500d000901c4405001059401c0200d100f1603800140e2882140d541c2d210125103540d902c40400c200b0302640d40010045c1d8000300c03d1040300c0b140d50003101113504100c03e0802c106075850400b1603d159601601801a030040c0907200d01007808110429903100040c100490619a103c52207003284c1c2c0a60711604 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 707365494 1250 707364244 707364247
    0x40b030f0403111c11030d090f02040b01050c1203061804120905151207090510052d0a110717030d1b021b3f03040605070b0912040803 59
    0x820141c0001c2110500c0f6441c100030540d240801e1011006201006015011712030369a2807000340d10400c00031a072517a178501109019241a51503c1404c2c1260a00d00700d100318140211200154071070300580e80641c1e8461f005180e0000c0380e000100d060380c0080c1105810804040c51044100081e100381405207205040311544003801e0b40c2d00408065041d00503c6c0f1a207040c0c03007240c2202a92200f641e41035940300500074a81d4071401e4090300c030380901341d10441d00010590b61040407541c00c2009000311107440701c0000040e2000e48001c00c160b55854044110904040c072444403001c1c400c0328848000c07070400e01200c140daa21500c5082004d01c0c1d0410100590740006030601d0680742a00810740d00c01000c001d464561101c004000c1d40f5841500c080d440000c0000030340e28010f0341c6440d003662400d40c13500203001070406c59298840d001e8003da1290b01400008003a220b59020300001164200e50b80d07683c41e181020002e40e0362900f0490083c11703481c5684201e004824103240500010801031400b00c0045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 707366744 1250 707365494 707365501
    0x609110a09140a030320060c0a020706030b0604092d0b15090f06030403020106030605010b0403030f020c03060a180602041d090a0201120e030c07060216120c1208040b030f 75
    0x41c26401d450304845407203000850b0454141c1c49070600c680540340d00d030900d400c01c00e41342400b070503144500c007031800803a1041e5002d119a0341120802000e41003415402d4071205901e07590240d00b95162401e0064001c9006c000402c540721142d44040c0030b6500301c60441c40c07018412000344041513903200b250b81c04c0c10b0703032001010341900c1e01846491200000405842c00c000c003600004207480320800c013281c0140f000100140415200394003010285600407000c000307a584a8080442c0f035045070008401040b010440e40608500000d084400d00f1802030042440340e03a946800300280c00411031200391b500b0b81545150000b14140043c00181050400107160382002e89802c60820001416903003035030700000085000341c0d03400946002c100d01e120902145000340c49011030300d14803030400b58038100e0223468404951161701144650000c0d00d00041d100b0030549a0034960310300490518000e255014003101003221000700e00c48204034a01803d40c4500700360740d8800e000000d91084503190070340385685040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 707367994 1250 707366744 707366747
    0x1e16050f0304140d0f02090c22051003050f071409181510020c1e0d0c060305150f040c110601060512010e09060619051002010e010b0603091b03010609110a 68
    0x480c440303588101d4400256000179250a20258044403000c0c0c02100154001840d001031641103c0072200f6440000d4080245002c000c0e080030705500615106201d03e81580c81000d21078001c03a0300641d120b1a05c60050380b5a45400c0e2445105c035204030041c0c42c1c5c06c0c0202c41740b6a90b6100a481800d06242102c0c002e441d03c0c42044050141d0b5210245c414489500e40e100ca242e400543d40c041c0c1107040d202c5900c0b1490201c0d41c0c4011f4400003c0c0c141d0701448401400c03042062108000007158a51344003400580c0340e86c442c1c001051301c1c48928580101c4200d01145051070541c01952003854141031203140e0300e500042070b0f81803ea007600240041440000c80390480780c80440680d00418002000142605090700081d0f214440540620310401956010038101c2414856400c000c00000b400d0003071041c0e21884c0179002e0b284081228000e03519000303103d01c41e4101203049900c1a1051005800314a1440201c0344c01d03450340441c11501513517502c2d030101d2910414828010f00c0c1c0c00f44004180ca40140110 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 707369244 1250 707367994 707368019
    0x1a130e010608030a12050604090209070f0e01030b0f010806040e010204080a0507150912050115140909010c0206012907032a0809060c030f0f07050607051e16050f0304 73
    0x4142d1060f8000c03c10592078030f6001070210100c003100140030503a62144000600a000d582d5400f9600444000c2880140390304030440c2e82c6040b81780d80b00c0303240711010000154112071001002d260402d010840c002c0281d0301c10180c8660180d002800058402c035280c07030311400c90700250020362040c3d01c141004802d002080006000801804640498008032440004d015040511480f040c02c2c02c034901c3c0e002088400e4000d034815010b808842c11282d5540e070b0b5941501c28900d690706014086080201302181d10601540003007001680080005901c1c2005503020b02d100701d0041000780105517008042d400551000b0b081340c41c000e5654409220406000714011500d213141d00504240c0b044800b0005513a4034252400f00304212003c036180c400e02c0321000e0441c4212801c103181400d0014821008280542c0580701c40d40c0120101c4055560703032482564036100d405960354000c082c070303000011480800f900500c0340b95262000201c0d14400340d40d9891506203845100441e50f00080340a02006c41c8446 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 707370494 1250 707369244 707369249
    0x71e0b19150e041113020307351e010338042d080c070b0301080c040c0912150c051e03040305040f08160608040503030601031a130e0106 60
    0xc8041000c00e5a400340c2032602080c500c68407941550352000182440b202c07601c60300c2901c4015003404000c207240c0b01c04500a5004480020114010300a03059588101d070085500008445030200912607001412030300e8910010400c0002182d01c2c1015000c8207802504a40214810980d08414041030502c400d180c0203025074080c0750030320904080409400030400b46400c144c03c40c0c100c118105240c10f00c1044030300075407002619a5850221f840070400c14000400c003002c90704068802e0903459141102d1688000c0c03041ea10241e0045009001320710705a4000304a45406040905030940e5458446100b08108102910540000741003101c12000d2400b030422035480d20300c1d11515102d15141020013900c017048811a0340307034003c00098101070180c0304075400740c2035000e00c0306a00c5944504e600d5441304096180d480c115111540000d909000307003a824040c5901c81c0245045640d40c0d00118002c20442c001070b11640300e1300a500d89103444d240c05a91005821840c04151602c0324483d050a495856 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 707371744 1250 707370494 707370541
    0x6020c01020c12150402130e03071a060a0303030203061c030e03060603060c0403080c070e160e06090901090b030109171806090d230d09080607090f0b071e0b 69
    0x42d08107407a40b20010032804c0c401e103281042d00c01a030701c660001c40e4007806845000269107142042007a001d00000025000e014801c80e840b40c1107250740c48403c0c0710464161803150300881d04c40c0c001d0001034002d4002c0c541c02403014040105602503104440d4040e4201c0d1016000320313510303041e009414101030200c0c540c050004d50050081c2c0c00e00300e010072854822480050300c0420045074516841c2c000340001d0340100b03a82600c0e4200c0342004031101e0a500180004203010804000f55140341e81000016582d10100c001c4c09428241e06c0c04009801038202d071100d9940c1550f8482c0468005007418510a0701d200300c1460b07068482915075800d5003d407404104071b920481091085407402d540f001140b0490300d500141030851800d607890340c00d6228280d501d17807c159005400880d025242c0c480340d010101c4038401e08440803034645100540741c40300c050103060b10403041c401060000a003064010b0113081c0c46103681c0713044005100c84500306405149000c031100c91902c1c091003003540d0152031120b00345030036 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 707372994 1250 707371744 707371759
    0x1903110106050603071103040312022b050403060902060c011505150301152609100f0531020604080d03060e130b180312060a090902010c0209060a050a06020c01020c 72
    0x74000001c4142c00f005201c213080052240100340c1c6503031b05009840065600111400c01240c00a41c007a40395850398400c0c03000d130003002d481c0d130464591030204281d0225990300d03030515003411600d0300c0014203540f08050b80c216004220f040030504092080d0008240000d1103a0f0504d4140401c00070390700020b00c41c0302c070440b02c10300040c0311440c110242c405501c00d960514498400075500c01652100c452984000707510221020014200008038000d4012908103504100c0c030550078060008a650948040f11246034031204104880d2203039541c426440304046104c1c448014540c0011071f2644a0b07001809507400006038800b0950b018060078019005241c2c280e4154503040406c400f0b074502540d000f0300318140701c0001c80d0302c119521000d07000100604d02560b595860140b0207403140c1c10140d61080c0500449800001d083c00c00b4840c68100b10f038141d444101a20310f5070200310104101501d00355111485000001d940d540d450609070050034150040c01d840d403c18800682040340c0c15402c40d025621 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 707374100 1106 707372994 707372999
    0x20c04050901090228060804050a061e02042706241e1106060f130f0b060403050f01140411010c060905010515030c06040b0901080a020c1903110106 65
    0x940317119800081d034030182103c00762011100613189401902c04c1500043d101d40090303074164a1841404210f121008240c1c0c101d0340640d02030307603400c40b60256082840c1000d104008000d00081800c0220701d00d441c400c0502007210b403109034242d110703408160415134020076425070400c10340e81c0d00e07071241c48182d4400380132240d10301c28085c00c51003004005030040c5040204000c0350a0043d100e01180e0030035194940c003410110301084261034881c980c500301901c402004e0700045001e00024483c014031402d002e4211181094650f41c1c04d84c02c0401c21000c114000d00140e01d9020070302e0000c0301d061007800c0000090080c540b0080865081205122105500020051655000301c0540c0c140402d91001c00946100b01d20900d1114502801091340560190300340c0d0740d00221031840035140001c0110103a050008c0c85961001d81100780f43c0c01d806040d804119070803898108002040040e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 707194244 707374100 := by
  have h0 := BRFrame.cov_init 707194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 707194244 ≤ n) (h2 : n < 707374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
