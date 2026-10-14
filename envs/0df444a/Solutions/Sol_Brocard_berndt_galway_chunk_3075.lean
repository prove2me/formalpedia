-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:35:05.517745+00:00
-- url     : https://prove2.me/submissions/4101a8cb-00ac-4c03-8427-12727f6edef4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 552877697 ≤ n < 553057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 552878947 1250 552877697 552877727
    0xe0c010f020a030c08041d0103020a0e13060c14180405070f020c1c1e1101080609010506030604140c1b0303010506120a060b0708071a010303050316051b030901 70
    0x20300069000d05580000c070420650740524002e08481d02d03516001c5040d01c0b680d03001c0e9600b040421840c62070926014240740c12030b4070842d035078031115540e0108940c41c1c001c00c60f0740c4041d035051104131302c02040c5643c10040e0040d038149000f82101c030208202a0403030700f20101110780740e4a0600e81c28400d05240c030030640c010101e400e11501e100681c02c8000e555114810400d401b501c1540090402c1880c5e00c403801014540c0a058900801c025600190480601c0341e81540c113203504102884c00f550160840c070780541405001c95403540e00740014405254009022190400e40d00d00040003190500450540510198040669905d23400c0519000944074a640c8200310b8000b00300400c26942d403081115078280c448070034841641d48000303401c001095a079100e211184000a0118104048040208030540c07054103c4004007120b03d400c0c0aa04000340001804030b80e08002048140e4207603103810411380f400746017403454885c11251a61859500540c100142c0e400866000d406603003005c40a41d800306 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 552880197 1250 552878947 552878957
    0xb210a17070b070206010b041a0c0708030a090b040e0f0c0712030c2714011209030807120504050d031d150414060f0105060906120711010501080a02060f0307021e010e0c01 75
    0x1040800b071002c2482350780b046c0700044c40c03020101141d208140c0203540c83c0052070810b4822080d0354010042d22684004031404c00185902c00129a40d0183d605841c240d44400c00c4910325940c8409000400400103013008aa88a017440480c1c00110b2520218621180d45d982c046141001944013405200c030007800c0c050150100a25030a1020001c241c0700b088400d00f2010507a110f006a0050b54030140c0b00b00f01405c03c0d400e1861b405c05041d0400f011031301135459076403040100d2040d06503500817a04140c0d002046a00205240c10000e03101e50001d0078400700050303421204940d41042c0510b000034480c0c0c4450b0f18200041000140000c5000070803820303803521301420341403400c0d000c50144132805004161250102141c50182500c41d40140d500c059040d150001c1241410030000d000c176403d100c1c4541e01c030341c2008004030702820f011840c05079240d400b0386558180880103400f84401d8000520350400c520580c065a10038a00c41d02d10004612000340000900e161050300b040c0c140b9940040a5042c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 552881447 1250 552880197 552880199
    0x51e16051b04090b04170702030318010f0c120e0a0906090501030b0a0504021012020409021c0b060936041524120314030907080106090b210a17070b07020601 69
    0x1400510080d510586c0400b00404401221003071042034091080003039050321000c02d404a51403d03555000902d00c5098030f816480003100c240440d0420f400800080c220400c400780a040301d40610010171007800b00816680010341c5178401c01040340d04690000d9034454441c80100309101c0801001a08100104c0041c0503c5c50203070045421742d0880d0800104001d001070f200e1101e00701d0b9505407005400102c80540d0f551150001e403401042003001c007195103d20b888c4c02c80a4518000c000c45119a4019150400000e0344103815619661240714200d0405e00d0f0429011107070410784072252245110f903c1c455195040e03140403808940b10701016004100a0800351100100140340000855901107802c800200107494115802c42c1c1c40b2020155400010041c803960307081c0072078000240c03a200e40082081540e50f2200c80d055030a504402604203460644c1d480b42d003041d1088160038039800000f1148a12929035036822010742c0c00302e00007440b00010560034100710440f0800b0741c00007035a01c0108015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 552882697 1250 552881447 552881453
    0xb0c0c1e1912031232090607120b040e01060602250302060304231f0c1d061315030b04050115080c0d150f090b010503010303051e16051b0409 62
    0x2554190001d803e00030307401e064100d8001035402c0041109407030901030710805d5000b10001c0b440d061455a95040304840c900060040800144144c481c02181d9111000300d9038810216004110a524140d0840e40324014890005024000c1c0750040c002a03000341107008282c150007811a03141c908101c10000a141b080000d07a41d01b01c2a03e070040e80150718015081c1c107645141d40d55403201c2154100d80c4c000c1100e00000050200d2511042201000e010f01000c00180000c07554400a0009402d118214500c284001d040480c0a446000400444a80d041e501d50140c10301201d407a00c0d0103000a034035010180901e04090140500400c501c800204444014a40140500340010b2480011984c0410b985000e41d84542244484039141c1c0c4600e05466160341da101c07801c01c40c0e03001c1d04da21942407440054665228400f12412a9010341d83c07103090884280c000c503124907284100010188082c0001180c2190310749030302c0c000a200b54020441d9200c000c200540c03034091105068442c603d8500802c0c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 552883947 1250 552882697 552882719
    0x6070507110108060402090415080c010302072004111303120813021e060a050702040b030604080d090c051e03010c02060114062817100f0b0c0c1e19 65
    0x54140c090030140d02035030b65180170400034052010b0f5250711905140d2a02c9005404581080c1903806080c16151050702007801034090f0300c9984001064400da8040c80d1454142102c0c0755000600f0080020030081141100410346801c43c4815090310304561400b0400c11400c00340c03072070590b0301d1400c005000d40b030412204510b8025441000e402040c0420030744030004107001011807401c400400c51519010000c0009040d9048000c040380514a040c070020811b03c0c000440c1c0d8400c40d0300c9100c0340c0c40c164603801c2010280148103001c5800c903421030b5000c28140d642030341d5007412256010071410504003842c01c060a6454071125502903403c128010b0000e404140c000380d414203803d451003035940e40b5000e141041c0d1003c000600d00308403c1c40800440340c41d48240d000c43c0a981040e44446a0303252500f0201034401e00348107000340001e20450410201584034060400ea000000944500d0000d41c0c010500203010302c0080780f509a28a070038441c4625214070080000504034100095841c1400c000182c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 552885197 1250 552883947 552883973
    0x41b05030d0f051c0608100b0609060a0c03050d09080702040c0e03070506090f090f09100501120609020d02030604060e07080c150306031e0d030e0d0816111e06070507 73
    0xc2000070004184138102410850a0640a100401008455628190117032203a24801c0b0b000f41d1503060109020142c80d000c0251600e410f001003909192180c2c003402a5801404003008609020040c00401e03140c48441c814900c1d007501881000340c1c0c0c0e886c1c600c100f0003140c00300c2d0003600a1014500c0c48411a8500240380d50a9450130744201d50341d814404001030220143d1303e1030940c4032054104000c41d05a170450741d01d00414144044030b180c0f2107aa041035040d03400034021041541d1020030200302184440d000f03e4542800907000d40e80101c2c0d19008641007440464040c1c900580315142030342d21140c00c00900009180030700140012070718020000300100011000002d500341c02001050803554240007421a60807590911107100315490302d900c0e251004417940c180460325103454500307525000301c1c189a80d000d0300c0d0f4541d011680c40d16032044e05200e80701caa1000b04010300031840652041040303801d1005424a210700c2081d004200954501b050007020ba6041000178450500005d068072800f00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 552886447 1250 552885197 552885227
    0x709050f070e19090524010504080a0803130b040605090c0f0a15030b13060503010c080105060d0507110313080601290c24060f06181e09041b05030d 65
    0x4a60300a5401c0750540480c8640013040302903c1d001c2446048010910454500112480c0c0c2030144c06c0c07458015036a501540c4901c0700c040d04002c1110000032502c0340199440341800f8121040c000c1251a1044980703822102220641d40da41b0500070a050104045404c0355404c80e1400c0d144928000480ca030040300780300d80725604003d401145044d0303000390820032000c0b00c041c00c16180d030035007540f451014294074410b580c02546840040c0c44041e22400701076050b11400740040e880c0c014420440070041200a1a071000c008500e0541a500d1005000505c43c088201f103100100c3c0d810b000c00302d8185001a0b2041003503518560140300c8000300d12060000350001030243c0c44d140d01c011044182010205120b0100595103494002c400ca103120b41c40c00d002d528169103046800b0208400c0c00124480e55511102114518900800c80e02d801c080781c0c0540a1940c407102d04056441001c20000326050b507040721495000c000300401b14010700001c81c010103040f4001c0003100748040015268102000d541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 552887697 1250 552886447 552886459
    0x11030f040303030b06070506100611010b01050301030f0c0305060114030705040504050a0206031b040b19020703020f0d030327050f061608040f050f0c120f030901030209011b03020709050f070e 84
    0x2040145c0c4e03442003503503c1c0700e03084829a0f50a280140180010b1000e80c050f83c004100700c0b04540ca0710030701c140301e82411488180c56981c5140d013940c031007040440580360110744403140010040001801400301500a0031030140b08084008804109401c00e102900f0503405540f0b05010040030030000900300f5907003074040c0c4010360341e0f40356401c4400c2110000d030b0411444d00340000e00050030303642310fa0040508042c00e0001c150b201c140030340100d84035081031002960000d400c001c003140d5850300440052101d40300341400900404c1c1c8580007451480c40a040c3c180c034468805d4407405200050007400c4048039004050942440d007040c0074070406440390108000c0150b52400141040b031048004000b290b0003a0032281c408007130440c03050740c600110350298040d18107900c0380b011a4600203200030b007040c1c1c0714000c1c0d07040100c01001103000303400049519040240442c0e00f0f0801130700034140e0f01d01d810301980c0a030820078104003082050b12806000315401f100c507802007202c483d1348a0402021014100c0344 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 552888947 1250 552887697 552887711
    0x61206040c1e08030f0d0c1107051905030f1c26041713140a06090b0c012a02150103020f090406020f0a0e0a0b03010308030a1107080708090111030f04030303 69
    0x2098880041078004001a00c400a0445c41d5007550320060540190840000d02000d0148041180c084000e08644c3d015680b0540e0203100d2841d01d00302da01d000c0c08802c006040e9195440c8002031802d131040d8072550700380e000811001c00001a410070340011031680c2c10500d03407462107081c0aa800c034821000000c0380050f041c01150800220440741c10403030400c84031190701c4003462042c1003000411480b4006200c1144042503255041601e900310031907440d5240c03c0e268170700e05138200295502c00d200c0812103550f6443c104140c82d640c01800108000c4142d05000c441c8180b40000c0d1404001c3c0c2040f02072402901c00400050395264020f420740d1a060310404030a03201d43c90243c001c1d0040d08030100705410040b9440201a40c000340d51000d0034402c4610b00c0d40c1c0303a42ca994021042c8401e001c0600000390800015030b1201c119082404030a50040380c0602e01900c1d17131140d00c100d4102d0041210900300c000b0f231030019581d000d0440144d20365000b0185141000c1c0e4102c510041c8214400107042c10f481c1c4c7c2c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 552890197 1250 552888947 552888989
    0xa030e0c27160813110a0e1503061302012a0c03150b0f0609040f180309210b04050709090614070e03060a0c030b130e0f0601050a0324060905061206040c 67
    0x1050b90f00c13103c0180664046e00c1e01ca80410b0703008041103400154a0150a07210f803503500d000609039018000d19187d081100c004c03900111000090f203d961407071141e01502d4110350b1207488071012a00360046681000150451a2200703c00c225140c600280a0400f400114a82c0d10710120403052902118404d80d603141140109000d0700011818101d09490000155410940703a011303481c510344030740d079555401ca41b211850b14103201d404840701284880c3c043c030480002c3c007010305030740c02c28010170441e0081e07541e844894084d43d0200000303e072903a4403018015100c41d5611410340e046003050803d829444210400300b56280303002050b0460454640d518440024000d500c6010300103005400401d201d10481c411601904900d0415030081c0304110381e0740c0540703d0100b40d00c1d051b40c100604d5400c10610316120280360030000d5070011190103a022a42c4000601171080c4402041e52180c08906881c3c0403040080005180e018400039401c0b010401c00012010441282030700c14209030547c0c0c2c1c4030500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 552891447 1250 552890197 552890213
    0x12030a020702131a1e03060a020d060b0f0d090311060910051806070f090f03060c140301031106030c090301090b010e0601110c040c0e0a061211070201050a030e0c27160813 75
    0x4210707246c00d40100028090403031180d400428280b84580340a01c040703661803281ea81c40e445692400f08000f8414060920f405006800c50901c0b10300924000020301d0711101d4007410100161a088807907806071030b9801011250b809100d038094039405119006034164000d0075200d04c00141080c04004002203000405401002c03810044c100a100300e5146c1d41c2c9900e0004003c3c40840d200b42d0205d0441c0c0d041075801840001200d041e250310030258807403060110705100694002804404c070200c1e00788504101d0780c809128401c100c034083e00c2a403803d03514001120002100c050312050411030350714202c401310754000404160164050790000b40c4140e100c401102c1da5400440e5407175001e0180040040d43c00c1c0d02c016201c4461550305410000d00b20040c10140300c0744200c060013800305d00240041c00341c0364081e034001e44c1181d407000309030b507482d44040001035500c00b03511051a108510104003041100c110902055000c498074589003441c1c00d02000292682034002d08202c0001c0304006180d04000840c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 552892697 1250 552891447 552891499
    0x7050d080403090b12100f0f0909020607080d0203060f0103020a0512130507080607030b01020309090609070e04050108010221040f080c01090b07110c0a0f140312030a020702131a 78
    0x4044c61611058070788042003c0600070f1355000c0d680490504045524442c2040542c100d507035104514442610306a4441c001d0801010f080ea80f001e414081c0b0400b00703101c0801072252a2003c900140d481c40e1900030010010100164030b410140f05100420070381c2c1d049070481d07090b43c4100248050303590b64100c010728036885403800140300d4000e40c6400140c3e01c0c0001401d90203603583e501c00703000710030b003d200481e6a03000b0400000d51044140000c550b040c01c281c030b0725a41080851900d540c2c6c5d078822202140c1900c0007a4050081ca80d800208a021000d44c0660051141882031070b00312142807e4841040000e1038400c05410503000182e0389240c24030940c030190b0070a6000348418400d1400600c00360000d80d10101c0050305008590303400b0800e01d417000650040e07851200040c185941808500d00e00e0710038048a172509440f60102100c0c0b0751400d80081c5100e2901a00b025a60707052070301c140708a01d5448202d4003559030034114120301001c140c1481010302d09003a281c00780045a0388050710b440c2e800b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 552893947 1250 552892697 552892709
    0x80c070f05010c0305100b0316031e1b0e010e0607170d0c20160b03060414010b071406010308120c07021009030b01150507020d020f0604061806030207050d08040309 72
    0x1910080c010044e4140d007100c2d100791011101c0307003c61a5180d01040300d600c02100c0e02803c140301c01c51036441c081e001c2e5015102035a458288054844d800102500403101001284540701e1000524058042e41c8980707081c0b00c501c801e1070b203104070b0480480850020700501c40d000b07240e000ca18210364461145001540d5052140c03e906000c00307401d84c2c034040c2c420504820740003001c0d405005101c150722000510035101d9030102c0841da001b50f00c1c1030b10308050b0380c1001d4001580039488015400144818944d43c0380a000207000999450180349081c4101d0410421010500d8010f0ba00410201d0680b10642e03202c1c215040d021a102c0d61402c6000d211071090340c9000f03522000c40900e008605511882c1c0b00c0641b07109651540d920790b00c0310241c152520000c041e041c00980204070030f00040c10030900c1065031900c0a000060751450807000209540c20541086001035080700c240e40c10007101d4017104000f044075060461501081d80c0303510307844078589a655070500041074040780c1018801c3d0f10f008010702d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 552895197 1250 552893947 552893951
    0x106140d060b030c090c03090601050d1a04211707090803030103030e0d140c030d052703030d050711011a0f010509030c1302180906010c030804060b030d030902040e070501080c070f0501 81
    0x60551020704103904148c66402c0c0b18440c08002040d242400c0d0015042c4603044020018019020719110a10080042003240c68540021151a25060a1030f22404005564072060710001d51060301351a0400020202800c0150b101c0041056001c080304a0341943d030135280c00000750841d00d0200d40240b00082c030080041c0124130a002d00c460b40840c0d060340035041141601c8841ca0308940854040c0142404110001140011a90400e00c464460088200b01801752818548ea00502c00b0441c1c10840720040450700307150390030008020a220b50b0f40d0b0780310101c0014594a000801203403604c0a80310400d418804001280c4107240e8080002c0c0140d07040050543c200441c000306290042d4105903410405031020203c803100d07901d04031061500c50601a50f41c01034000e15030701c0031103400c40054001d403500d6a0b16014147c940e1014084500710b01166203000c50600c00301c7c4140021168070344c0621029412030481800b49a078004076603600310240a007d15103400c0c5508100900925011004241c5d40c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 552896447 1250 552895197 552895201
    0x706390c0804090222050603060d02030f250602030f120619140a0911090108041a13020a0e0601020a03111002070c0e01060f050a030914100e0106140d060b030c09 71
    0x924640060505036401100300045c4007101c1d07030240307203d0b509002c2d60303030722840c140001011070a014613007400751030005040701d6503403030703005031040c18905200c000141d069020b103c00c1c1070907400110800d005006030320085d0701d0a000000401c0003402a0040302c85080b4004000c65011f03511009120103120252880c111103da540c0e4031001102d8201c000103004140381400003d1182e2148a29140c00005c100d03400d291001190045a0485005004403042d03240e5507001a40c0320000c031000c0703201e10070f44d400a0b85030b014a40100840c2c0f4079594450211504003804020301a607004c0740643c280c5034582008102990703420341c410b05010089540d43c507914401304141d4180300c910340d00502103c61010541281c1c2c1d88901c001c8400d040302c0305001c0c02240c01040f800164038441ea011400031405034503030502c000c80e500c01721418141c0d035070400303007142d5128418103600d01801c1c82298020300fa00c042502800d007200740800d8a0b441ca443d00034001c5541d5103a501909d807000e12000c0ca410070001c00707030241c40c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 552897697 1250 552896447 552896459
    0xe040326070e190b030604061802030f161b260301090c0827070f0801020a03060f0501021e030f0a050a0801060f08010b090109090e030706390c0804 65
    0x204503000c000049044011004500344050fa010312000740b8024410028100090104a0313032018120541181d560030f00002d07954401e135a580080150f20341c001da581e0800700340203101c060028044043c00894280521411a00450780c0c150440025844190081a50400104944003d0340300054143c40c1d80c0b0303000501481c1c00c02036050701c84100080000115502044400800460303c407090b611030301006000c480b105555210b04004208129504203031103414a4010714019404407081d03a401141005109815006007406011050b242080c06071405000070341d604101c800203001c0428140d2001c0303008000b80100d803884907100da80a5903d071000c007030080080e4400c14040707000883c0d03540045110b512a84900c40e090000b641c1d100302c0341e400d00d00088416801070074075606200c10756a00140b0b00c0140d020348500b552102007d50340754031071800c20f00d0941da00322900402c0701303d00910b5201140c6906d500c0744e44103101180c2055110306a018140c46408012134040c2039800c02117800100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 552898947 1250 552897697 552897767
    0x30c120204081f0c05250501320610030213031e03080a020a050d0f09120305011d131e05030d02181c0308060301060905130203060708100e0403 63
    0x300009070790701052a10451082d00490301304d1654074000810401c222245442815052214444194400d1803018420354409085841b00000c0d40c4014455410340c8a607010118021846100840400c450328900140001c90302c000d0260078200385039010942d001d144070800703030030390243d94400d18503030007403000488051041c0300c200750450015100c00c002404880702e174003c0d5000c01880c0c1d1511424464403021500260070760540b0040e105507241440c802088180e40c403c2c0e00b582840d200015030b94109a046000d03004507241c248604400c240c03d00c848001e1409180343c002d50014007401710b281c0b0140c10982d100b000c00b00007034114032020a14524807080c42e03008100c0384804000a0b90082c841c1c80600801c20b0400c8514000206404010307804a8040c4030802d0380604010000600d80b502c03205000101c40d03058032115844040301d00c41c0e0b0214201001100d410501c00e0401002514148071102640291802444a203c801c2c84c042020180071b845200400421180e04507140700c030400740406 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 552900197 1250 552898947 552898963
    0x30f0203010b1c03080a0e1506120d140705010b12100c0801060c150b060a0207051203040f181103040506040b061210180c0e070905150a030c12020408 66
    0x4440d510742542c420552900452180c03290114620901903444251016180480001d042e207000035190300403518100400e10149426640801ca62040d070b003044014040d007480d44428502c010340c040d03020140c400c2d40051720361040c11544034845945d0b911a14040f03003d060b00640f9503130003004406403011048000305041200c4101e01c0030401c44039024140444200c40c0070700c16100032803009410000482c2d0400e0120083d40802e410104042e5081c2c5d02040150f4055805e940041c0c02c03d0700300b80500d00c1c00900d02c14104244000441c1418144a40701e002d420f801d10482c5060b8a030280308121000319070304554100003003040c10395168075190a20700d486000842d0704981d041e00ca400014450301d04604d80c254100070b00002880c00913030603c0083c000f412a82c6800c0b503110820040400041e040b0390384400503100c803203071420207814040760190401c10aa000144a01001d41040c4280d80301c1070180c4075400c0e010302c1c02003070f280ca0307031102a940d00380400302100c001c50002038040703680c00001801c11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 552901447 1250 552900197 552900199
    0x13180204080102490b0f0a0f0f0f060f110a020a0f08060a05010305060703020c16060c1202030304050307030c060f0501090605011d31141008010c080109050c07020406030f02 76
    0x503041414159810740342e9204180c805804d02d50100035458000b041c2e0b0701c882c0207018040c06000c65041440005000a0342c0340d40180020500341c44103000f0401c05004480c000d0941e101d100140b1424444050700380301c0b0380c0308000700f040b4413021b0014013054104034004003070303030040d0000318259200d1414070986c0800d8001c461940c0700d0310012a400c2c8000b48281c03812250800c000d00a681c607040070481c084c0d0b0001e02400001c0c455805181e41d910a0f82c0303101c00c001c0031641c0300c0d4400c07000b0700e1030201251030501e04400c0540d001401003001080c40841241c0c1c035558145044a03140305a450450000c1c9080c001001d0b000d854071001064852481d801401918000d0320f48050303040340c03510301400b40030031800d07216040903000000142c03480040d01200141d100f02d04001d01c000c0d030101d02c000d007225107005540451038450021302c001d01003c0020107000d4040c0c1300080c014030201d40b2014284400610414551554032000108a80303d480c09480b000380e03009009000d620782d242048200100980c8007a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 552902697 1250 552901447 552901507
    0x1230112020c03131410051b2d0601060507060c120e0106030b0606091c030306030f0332220512010b0306010e1623120405060c13180204080102 63
    0x1142c5c02012020781802c4204c010702590704104800e0742120144c01001a0240d20360fa40c203814101d1080a2080c5014030611101301562502c80d0600e81014611003003d12039150031103c01404096880f0003100d4140e17800550100f040040d0240454440b049030400300030807444e180c3c03440e40a050641002c802c40f800b400c005aa5611004c04002040c4108002c5d26805220000c40011810030094012510b50007800d000a4146c0d40351101840c210050404400049421200b40308401c2c0072032a2900100e1240601c1441c105240c5200c140c03072081141036001071440d0b074078201090700302c88072910103420003a010300800b0740304007240b82c00307070070064180d40c424081d040000c240604004110342c0b25000500d00b603903151864000c01d4608081c2402000d01d07899481c1020404030441c800200451010007641c0c860610b85400c01030300307040300a4401c48051504015409040036041b443d5800c0c0c42041508103448001c404c807800007445140d0241e08a07500101d100c1c004c0c4521044a4626400c0088070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 552903947 1250 552902697 552902699
    0x409140906010f1206090204090209041a0a02070f060e0c120d031a060f0a091d040203100e0304090c05070501060b04060f0f0807050a0e15040501030b040501230112020c0313 76
    0xd0f8483c0c40465000741401101462003c03000f0940fa038003c0b080441c0050030020b140003103a004140e0211040300e09840340c06852210f51540100c03005402d0784610100d40450401c881c560f00e400c0c44110f40080503206036101c1000c803000c0138007806200700409006115a80010180786e00940302c9211200010100e40751810030014403071021801060380c1d1000344208d24250b8810074010031600024800b03010412990404600c080d840c0012406074901d00c0c003401d10910b8240b0406150411400500d030f121424549910300c4900c0010945054031410b90010860702c0084208898030700135030402500710360030003400145002d1801c1c014001d560559503080c0319040c1c104d07420f030781c91509141405c0010b103103034000500032840b44010385642941e51900c55030f1500500f00150118040042000b42100002020041582c252260032400c007001ea40c148095031428100b40c25107040703805040048540942016043da02c0f450459102c0a4442c01c210340714115040c0c0b0a03500d400c8002c054401e5103000320 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 552905197 1250 552903947 552903959
    0x9130507020106080705060a0c1406010803090a050f0d02040c0311070b0a1113210807151808030604090311060925080d12020417030d0b040902130506010203040914090601 75
    0x501a098074401f4280c1403414480b40300c1141c40601502003522110074500b0340d0b41c2c400c1070610200e4028540e000066032640ca005042200e42403040e889940328403d0400a070013151100c6051002103034040b60000307140d508045050f8068503485029980141001a11b002000b0207d22402e00400e81200c041000d0400710303030b50181d54400e00034100a0b0411a007030070001300c2014800008210a0407000b6000118260340300401900007003001c448403591007400c107440100238852405030004d0744050205004907912494818800508014042c68651402e8401e150042007042c2c0c51070100000c4499078645580200e440e0409022000c800b03454400000d031504c010300d8076020903280700c00050f2003078071a8200c05031100007042940d03681054082c400003a01074030700c0c050240c0c000c4002002e150b030780c10140f040b5800c4a0154401600c602d1a1070300b4040542c440740080c40a445020308001659120f0900607171a60180c0d5004411150511304c02c1000440035a5400d4000c2d00c0b9001214902d9032114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 552906447 1250 552905197 552905203
    0x80f06010305090a0f0f02060309150c04121b0e1015080c1b0c120d0e060f0403030f110d0e040b010801061e0c120e10080f0402060309030913050702010608 68
    0x74500455a52203103a07480d001c40d41c5d013200f1851452150362400d011080a50202d941c075002201c43c03600c41e4104224a41000740c07001c40301c2c2da00c0b5520815092a040c1802490200c0072004140907269504558913064185d1140e40d0b90400b5040621940c226807030012000d0451040c0c0d809012480451250844c90941c041c00140707004582d100c04803400e10b80b07000c2c5060301e44803001c40381980034850901d1805807515803044480e10300700010081d040d071020804014000c884031014440c090030040001202e145e04e4013050302c0941e41e26203010101400901c070219542070806401c0100b078010403400f80d15194000e00c41c0d141010301502e09000c010411001581c0345d003000d1203210080ba4455002c0c062250346200624143d8680d41060a035590094590003520810f0810171004034415006100309490001000c182c030b5003952030050144d103010910742402ca203010b070009000300400700110340c00c01e0052040e84d1001e5009030100000c0400102d515000d80800c2e180e40300035501c4c01c500890842404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 552907697 1250 552906447 552906451
    0x1a0705071401391b05180a0e0703080a0302090901050607050a120201020f0d06080f0f0c0f0103090b19050105030a0b0609180f0304180606020c040f06080d080f06010305 74
    0x16150954149014001080110610f84518a43c1c01003030b03200709800d02e0801007903100c550050641c0d01c60944040082c0801d05419007103680719540004203081800d403925600c5920810150011030514003540003c1d141c141d003908010217410000c00c1c550f68003503140d40036000d0300d034080b1281e129a1b640c90080c05814480d540014000342c0141c12204081403103400710361340008091000510b401040030349400c50703070040e030140100c031a101ea40030000c0c0c1e0710401c4460404400752000e4030310405101e408941d5146c0720360590740503240d400921992680654810040c06070004100c2180e40340680304c0c4040110191207541e41545001300128680c1400103c0150880c3c1c448200340035030700d0710000c0064440e00100729444902d00a01c0c1d00c03441c00c03814000558000500802940c40f0780c00e1024050740740600940d5204e9017480d0a0081008650026102030b4500b41600c0020f141042d2125000103041c054000011a00c202c02d290000b07164070034034441c482c0c083c6951001e40360316404011070a072001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 552908947 1250 552907697 552907699
    0x907020307021e04061710052e0f332c060c0a1707030f0c06270201090f0614130f030605070f02120d090c1a07050714 52
    0x1041c401e140050404030b41449041107038a00b88804081d02000180964001d40c2200d440d0300151890886003040400020050000b000070901c110710f440401d402240c0341c5604081c1d032030020aa00c00a002819500c40406064a07816000c8010b88640340226076044d0590038109040f200200517015128140042e5079a440b40c2d501c424a890840d900382000c3c91282d90f41e02803200340b032202a0016542d20009214601c081c0024080e03001e82402d1102400f00c429000b004040c0c4100810000240d1000700001c06001d43e00780810020010708008000340980c15420010042d1041d40d032840802c0d0400e2140124401d03a0340034000ca0321440c0e5a141d440541c85040c0c0455507158000c250b01304480090402c0081420668212513a00c2d0403101e080b5045510a1b114956200309200e4001d511400000200c0c41c14001400718583e4001e400019100e11402c0c5046540c1e540150020001120308007001000c0a000b4450f2500780e540c11000583d02401080b01e1a00c189080004c01c4509500311198540c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 552910197 1250 552908947 552908953
    0x3090819050d180b1204121d06030703093302041802070f0803010605040e060603040b0f0c0405031b09250509010306050d03090810021606020a020a02030715020c090702 74
    0x2500150a94600c42946500ca03d8803912420204840c880040502520301c40081e90351010304003402c0c40080368070050708210820540c02c0360741c03400c0c500c032060300417107000103980c500d55998403a83c0440040c41207050061020b48040f1700007011228035004514510100791208402212281d0300e24120b02c528030500040401c3c400754880c8440440d40034000260141034042c046102c1503844c81d0705940240c001c070021500100d014400b0f0322400060b00d62003103003030741d216242d8140b03030700c642c1e694038030080072180841600350005140d580000300795002420007504450701c07040005200490700c07c003062102c0c0107013558000900004403255114072110340f081c8020030018a0420115280e42c40b107042d03d13041c50b44480c070000d078507101c2c040e40380b000d280650795580c0c1090901d90002d0070012407850544145005001c04850310300a0361208007690380c4a840141e40f02c04c6400145d061000303d880c040c0d418040c01d140010108450003088001c00c40c80d034260b88140308600308020303149005440d010010783c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 552911447 1250 552910197 552910213
    0x1090c0513290f030901060f081507030608030d140a0605090403110a080c010902100908070e1b03010b0309010f09080702061e0a17060a06080f100509040309081905 72
    0x400c0b0054401c10a001d03002e1105055010705031400c103954000609500064400020007400d01c0003880f444000e401a62120309240345003006076030303990b04031a65030958012020041200103009500000007880004240e03500e4004004800004010b003000c01020b81c0d40750030004001424622a50341030315030040448880b6200d9441c22607c03203070ba81907002d136140304c1d180071003011074828400742030501019070010031034110030710501a290010415610901811582c14020400085440001e5a809190007503407540e58111035000e005806940000301c501c0000045020f910703a0307006600c0b8000e2403009100a500081e1400d0840301034040203413400c0014084100145000d80c000d00c1e024401d02000890f2001199419480703501000b00c0d20302040c41d2280d142d14500e0324907940d035441141250032650a520b030127406041d1050080152203040e1101d800562403440d09d141c510050040500300302094540380c500a8007509140c080e0800500c5a000050030301a40010394154207a40040034082c20 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 552912697 1250 552911447 552911459
    0x3020a090e0312070e0316060f18090207020103090f060525120914060106080601091d0402040c05071a04020f03061608130821010b0a090501210504060501090c0513 72
    0x3030000034000c0c4c8201301e04007146192075503003000341d003201002c04001d8150082c603140c0301900c4c556564111005104210710038907000044035480c50704071024000050303956102e51004900404614000a0840410900300824482c540e03001e54800e29411800b40380224600700d00403902c01d82c146281001440c410910000c8074030b142c1000c000c0c01c0c4110b091b0891001c01c21407450609000360400c00c005080303001004146d681c441c80c240300401c1d04280d090b6070648004540952940010001380c001d680307402c0101180381c0305400b266801d40d00021000b03880700c4088140041440c042d10242e10406d418010810203241c0410294000d00f40380c1162810140c014000341e804490040ca4507800c040c402500341c01142030303980100a113140005007140803130100c1c1c544903a020b406030851584044140040114160000c1c451010b4075802d0030301c1c00702c9502c0300700c6101c030301100700080403401400e120a10040054541185041c0c0c0c07598901030141d0402010201d6860240d08001c9003115511002040b030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 552913947 1250 552912697 552912727
    0x30c060103060c090e07020a0302011113121b080a060f0204080318040f06090b190f030807080f04170706050f0d0b0f03120a08090703080d0b010e040e030403020a090e03 74
    0x41103500c1c100741508540e0f4160101c1700a80c1225a140541c20a410f0041015420b05c10310103c00c000e01109818840794442044404c40d450042002141c0c55441d214240400802e0704140700c4555003010202e5070301c40701000d4a42600950803a26903061030000d591170307111802581c0039a00d070a40214100328a122201c65054182443c0750b800540e103072080a21072031540035001c0a844e03000400308031075000704103000303003c4c002c00a000c00944242005010f9502050102012070740c20080480d1103086e01d0070900d0041c803c200c4504100c440000b4005518044941c01d019130007489821b8600245c2d44603403d64040c400e828034206142e400300001e501d800e8855008403801b48016214000052010b00460300e400c00c0b41c00c0c4d074030280c0340c0816200c2015902003641940f22048c000602040ca145580b065000d006118002013401e8844500003e1640304404009003400c3c000e00078055001500659502c81d4000d00040c0d0050440100110341c1c000039003d071041c1c0356103c1004500d800b0300c1c1d2483d484 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 552915197 1250 552913947 552913961
    0x32206111308060a02035109061002030307110c0414090607020111030610020f01052502010603210e0901180c0c08070b19090803070f083102030303160908030c06010306 74
    0x800090400c1040c01507450204071201102c003a4141f803030070f200c20007007180600d80100400d01c211803c0a208a1450740403040c1d0740c111040342003004100b074441f2409030800c1c2d03540b10480e070081e00d4404850420483c5000c8039014006010a4501d10740301c0340c0d0708900f610724407885290003140410103e10b00c0d00b400030340c10301003802c4d51055400d0380c450541803500707444c0240d407442e0b1855076452006589a10340c0d030418108030441d00080007903a10f95591661300128516000030402d030342e6110006401c3c01818040107070000284500559a1180003070741c0d00041da4124042643d01d840304143c00d2a000715050803480da00b040d00071342842144d98907181d020fa00140340110301c040d2203410b0040c0070b0560084560341480340d03500545a02c0d0186000380b114015150400800010000b80080c0300030100d04290700800c0d40d0401c1e4556000069109264525014000d406102c00000c2080341154018588803081c0d550740c072480455520b000440e81d80c0a5070010f98040c2c0c005400400025030580d0041c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 552916447 1250 552915197 552915271
    0x1110328020a0b01090207122307020f120f0606191e05030a030c02010f1b060905010605060a09030203012d0b0d020a0e100b032206111308060a0203 65
    0x10600d8455030f48030f80788281c003030f40400c4e00305802103440700410900d0303080542c030741c0c2d403603d42914860b05c0400104150205070404040060001981c0001d42d255032191840001000d001205040d9603041003c0d60b81d00d1000c81503000c1d008005c003107007807031a0083d4a4011000c00d001518441b03410f10301010403039920713a00c8001240c4154500060305440a000d000c82d55070007a19081000710450001601115074451564204044405624801545110b4250307005400c0440040c1c2c992061034100e00500840d0040d5903c15008504e11560715840074440055a10aa0080c49102500c40b08403982002e01941c1c0810003250304c2101c840d8142d2075001a4a0140c01028070310a0340e03036600401e0304200700e500641c81c1c90041c030042111490310745240500512420092a2441c50300702101280c05800440e5890100e95080c000740c02c1c03203001d03003010310300c58080e10b20706039201c904c0d038200d00303422090348a5002140990800200488401d200341d0303208401c16490305030031b220074203000540140e00801c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 552917697 1250 552916447 552916453
    0x3090a02060c010f05090a050607020102120c0a0c02030304090e0c0603011d0709030b0408030420060a0c0203070306020f091503040b060f01111e07050d020a0522050906060111032802 80
    0x40561301070b036020742c0c1e00403040100601364502140c100f050420000407c904207580c0108400381800340040d010950210030310342d140b5103030a03424500700c1d41003078000000b03036040c0b0000c180407400384141d6000720404030071182142c0c80204160244003042c00240f140c4904401654000566030980211742a8842c0c2185441c4102d01d881c1c0d40c40d244002d4043c0c5040c0e89445d000b000300010044081840128101c03980c0845896030b10f8640080c88621039003000801308602c01101c0e01c21074804105640140d6441201903454883c090900c2240d5040307020480d00c82e4030301004030a80d40f4800030840e070140b50800c00c1304909582d40d0050003940c04180a00700e04000404804503000d680070710502191490303008440600d94200050a442e0202c2034008604c12613045a11000580c0e6000429045860a80312607511840b03a08001c3c0281010003c1c00385580d0905042080314400820428400c4109803074401c261240c0c0441e41c0d42d20700170301c0304042002900b00200c0440150104090003600014411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 552918947 1250 552917697 552917711
    0x5060304061e021908090115031b080f0c03010c0513030602130302190302040e030901080411061306020303090d14032a0c0105090d0503091203100b0a0f08010b03090a02060c01 77
    0x42c901c1280c1c0903a00107482e0313403401000e008580b68402492500075540c00000c0c0300c1c503078040c0b240c020460288e1000a000501d484807506c40807058101d9140108508002c0d00c0d40c1040d88840c3c2da813100180301d1481d109520301074010340c295014030181c64440c40040441c200ca00d082d80d0f200802944251030522800c403550304000300503940e1030280c007030903048088168032180c03442c8140300548440c80e50043c02a0001d000079403580e40d2100f00070780d00c0341d009101544221040c8000c108a44100e07041069042206140466159000801140254800c0c0201c603000d1a00e0007007150303104102a00d01c511803808001007131507011443c0c2041058031040c400c0e0180c1d030068080102d5903901c0740080c00c1641e5111000c00c92004e005000b030f26200700303103400c0051031032425954441c0c03903200310b2244c01340c50304010020880e034500b02c0d07052390301400200c0c0c02c0c10f0b940c003144080a0041070321001d07020700043e6120000b01f41018041c050300e000303555800041898106581c01c010851f00704400c40500c0750b50b00e030b0b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 552920197 1250 552918947 552919001
    0xb131703072415120303050402120607110705040605060d0209040b0a121109070206010302120f0346120b030d0903230a02010503070c06110a020f070506030406 70
    0x3196800c8480039400d200001c142c240030702a11081e008202d5214000d643c200f00c0e80c110100c940380031991516001a00f0303030b91480061070468242006981611492003000501c40d003015074000e08650550885030050760350300800c030079500c860141c02d810203014089441e404429401070280c0c0d440081002c2400c1c0c00030750109552525a60210b907000020038100c1050084461402e001060301780c0e491001860101030180da90b90042c03100078040c07040002c1d481d4035514203000100c2c044800509032030b41c898010146200c01d2440e07036140a03e110362640540c580300488074911030060400300548100101d103410907a440d900d2080e06421554490110303980c03a07501844035803001c00403500c80c04034250a505002c444070403240c6418621a8001056400780003001440821840e030910b0300d6650b90740c52001c12100400c804800401c1c00f402c14450f250f801003850060001d01810713a0842d9040c102d01a0102e1381c500b058459036800440070400716001c100541c00070300301316100039015000721503102c17 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 552921447 1250 552920197 552920213
    0xc0504260a060204170105012103020f03120a050c0a1e050d0905070303030b06120604022104050f0c010309080f0702010c0f0c03170306010516110a120c0b13170307 72
    0xa5421982c46074006018032105100310b1481440030344c0c00000300015070400d051036909424914580f160035000e4003c06080503c20030a50110340e02c4402500d441d00c4034000c3d03035105907106031200e0030b00314200800129012514025102080d9641d5604002038401c40112803010403103880e42c10410508200c240d481c001341380250304009100c1c1340200070b02861420014110f5028206040c480c120411128003c140f80b211443d070800b404680040c0d654500001c001c86d4400c49280d034050124003036040005110001c00c420074004410300603509001e4104004500f00c64504000410811061108200480d0b14030f0160800a2060401e00701c10015502e0703003c0344000c1d0400c102c5d440040d0b03030020300800604034110032003800300c03681050550a0280020303289005104c0e040d911109861581400d1140031b0302a00fa0300300c0090440c0051a07100e051142d1550400c3c2c0b800d03508a0303040e050024580c95118102e13160a085990000281400c1980e01c50700c044412041c008248014009000401c0f119 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 552922697 1250 552921447 552921463
    0xf030705030d1103160e030304120f03080703050c0714030909010b043201030f110309010218030d080c13091401050f040614040207050106171f0c050426 67
    0x244011926030b40d200322031005031051405000d145180c24001c0c0720285409284813154020207040c003080309503e000104c3e166000d981d125032403225811100d1418080100340c0d901c603850195440b0f85840d41c03880c60070341c19180181d545400480e0100140c0300400c4408104490343d8010f00e050b20310f0081104002035440c102078101854140001a041088004818800640e10f111040074074140d2000c0348038410606100500905042d120f8180c0c0050383c2c515031142500210f1070150035143c0c2401c3c01d2a81c000d401c48803414542d005991030007083c5160000b504401d8480b143e4485106a403010708004254200509515548409041c0440d680200303010700000d18550a04103800b9600d00000c00a202801102540c0251701d000c80a2080201034400580c038000b00b41c81c05030b03481020f0301c2e0031030041000d40d000c12600145600441c01800f4049000314403681038040f00760f142e00c050b040010417940382d114000081042003100f000314280d00c46a041e8410300c001200e1580c9118100140e00340340b19 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 552923947 1250 552922697 552922703
    0x3091202150f070203040e0604090210050a1805090112080c060a0b0a17060a020c0f070801052e091e0c12060807050102100209220212070503040b0f090f0307 69
    0x31808515020340e03808050309520242d92440321903242001d10020b520382c4200e0081004090780580001d8168649401c003400060b4041d00c948018250881c00030004e800078944400050404114482e18015248042003603c000030310440b6030783d281064040611242e86404c44101740b040c451640000000d0003002d110700b00742800031a451020408003c0c045409401802d50903c080715102070710307600000c5080e40105000e00060f92007030038101c512b00d4224200b151910704c2c41041c0002c10b0100d0190070050151000f602c00d1228448200789800b4501d1040000c2c251340c002400d002c2044c02e2507074101d40810039070488007100307510302c45c0171103010f5806a80005020170307414151007440b006281700d48030041c03401c4000382900310304103030000b521446268207441b50950082002c02d0160745e00030010390a280048136a400b6100404040c102a403c1131a0303500128a0510000300305a02441c00c49215686c00030403240b080d80ca00c44014101003029010003003a00c101c0c260601142402c0005004140c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 552925197 1250 552923947 552923953
    0x204090b150a121a150604260c0306130201091517071b08070c0b12010810060f0b070f140f060a0b030d050706021e0a0f0c02091603091202 61
    0xe03040060100c2518198001d00a00f84466034a40200710300740d00c00c0400440d00d00e50360100343c90300085280308011000c01c00b40d002c0e20015001414280014a5114039040000450700942110408680300d007040400580c258003d07400103018100034500100e10948141080003506480d92054003000c001680c0450101d02c00c004802d04002c8007040156021205150842c40050b003aa500c01400c03142442c010142d6070301241c0c110403c0b140b891080040c05242d400350b5110302c03240700881071000d4288510b0289025440b40c040c00402c0c03900944c015a00e1034400c103184135162281800ba1507009200c180d1f4a40c0249252000149401e141407007040e0543c80103004075000790180c0d905180014182840c1145454096180c988000c10410b4074462681001e40d01e40ca15802d1201c040c1c841c484200401d0085001c1500c10600707c81b0107824a8441035483c0b945840c901c00702038030700040f0624080d40c00300700da20004002000350a003070900081a440c0114000f1007540e41d44803230304c100441501c0560 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 552926447 1250 552925197 552925231
    0x409020a1116051f05120f10120c05151306020c010e120a03050304020d141c0e0f04240e1b0a0c0b06011e020114060a06090902070204090b 61
    0x10004000d80d1003060b416a03403180a881ca01030010b43c24001c01010300451440e41c409900e8103070300940c03e94500c0e10314000c211400340f46c200010300b031910040f91a107014052480c1c0c003040da080d48404912a02d580309928155040c02c000400c00d02d280c10403005d00c00071070304100306880c202c03202031080c00400341a0000c04501c0c0d01400050034a100440d50a03001c5c4d100790300660004480064410082d50301800d0a642da03465500103d1030601c80c1c244d0281203450900081d0400030700008034141da9008150302000700307009041048411a009076003140c3c4c0030022000500e614234055001d61712082c0e81c0d03040800d140032a0000503000c0ca105034058100a800c41003080510402d48668200d0003002214003071500c005214054030240c4172680140402003150006a5039901070000e41c1c80f500c00d0140160b6a209002400901070150280c090300c0185074a400707d4514140141000192075a54468030100c42c00d0001c100c0c02900300d01d8050fa07000d901c944960010801d000300242c051b0020b444503075090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 552927697 1250 552926447 552926477
    0xa091a040606030e1f0b030304081b120a1407080f0f0c04092003031b0f010e0601080d1d060403030906020d021207201302040e090307030915050409020a 67
    0x49116501000505091140135102c841d00802d84c100031a0b04401003c1218030840f000600070044440e104d07401d440006000f0913690000200b4111b001d01d11303100c101d0014203c0302446400454142d1030b0030726500c000c8090002888010b50003001e40c40c81d4084a060f00d503180440d80c80d00c4c5003100c0d04281d54100c041552114072003071000e48449002600e05004416140d038554489508407900440e0904107200142c05030f07a400c0c0100c880d04048501c0d41c000840f01340000716201d4240c00d016081562030441c52554020740440e81d14129a100b801803c4681800701c0141d0b48071040c030000c040c00018014a020040e540d480180c4080e50007640c1d661061030400c200a807070b244560a100381598080d002c141c642050100803500c140b540460780303010380c0310514030026060403c00381050780501c0044054201600540c0500100c80401d032800032207440303000840740c40344101c0350301a0009480590a000410f68890048a202c00c18a03050b86401c2d516480041260400841080002c000050002c01c1d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 552928947 1250 552927697 552927701
    0x30b010e090f0127050103200f090601050901030207060507020f060c18060702030c0a031b0f0503030909042105070309080303270a06022208030a0f0e0a091a04 70
    0xd004000e644201031410100201d01c1403010500c0307004054002440180201e2043d182c4282811020043c14000703540c480c0b40c0003c500c0381c1c103003801c03040e41c13215065204185031070030f01c103040c0d110003802c400883e44440c00119050343c0024a03aa0615808010a100180c002d01c00e0612170b840a5010b001d40c456140800c6041030405480001400c0d818002800d641c0100a41c0e0941e030101100c0060350359609102003030038942031a0307000381d00c4108070070b001050080c6d030a03100c1e02030308040822891311901c8a00306c004181c0340d4010a5090741c0f00740a60216030400098080c0c01c207010b00c001030142215206500141e0f402411075000085c8080b43c45410113422007480c80c0502240000b560441c0b40018044407059541d40c03340201c45e0103500303088001ea00c03d024000340d69800403025540c82100c020240700d0b014119440401c0b404005800064006000c020750f81c40510564810244c060038200c2150150040c1d50456440a18400001060041403150300004841c00d0301148561801500b0001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 552930197 1250 552928947 552928967
    0xa081204031208040c0b030406062102010905011106061215040501020901090906120f1b080a05121303080a0504151e0509180907030f1a0a0b060d0b030f0d030b01 71
    0x700f40f10102050100242003034103c041a0303101041000d49030355807400c0c1080034100c0740e400400014040ea5944908c1403400750303c1d0b03201c58001c2c3c88054a4640d02d400444d1789100081c01050310b0b030024000b09a40345009039942e2107100d903410803908100594160000165010380d8204c2e442da6000802084650304644d0701002020211000c01c131543c41c00c1c080c894242c4d41c0800051680405081e6030041110000401201c04681c50608444030707220561a0355859616070240c41d10b204540c515003070701003507100700c0d090403a50b0a24101290b2655075020324640000303c0a40c280b0100740000705800e48204c00e100300f103211640c0d5084440708143d513420400c90190807107400b00041040312140945580741468110020303401008010b64032008418207080d031542004151000002c516400e211017003001910b44103480040c100300761500e6240000720f130300304a00e0540252041c0500b14100340b2650100301100c5010301500c10b100c034020019030601801a2810002c41e5440503000076a50340905039035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 552931447 1250 552930197 552930233
    0x90a240e06060f0f0c2e0e070f060f0201020705031c0b01080411100915090f06020307050c090c090d06020c0f012c03190905010e01020a0314090a08120403 68
    0x929110b206031042500348a107a078498004440000c585044c2031003000071949445114406c50f83c1c10b107801c039210002a02440c1c0802c41c450a203402c0805100c0c021405000b1104400040c4814900c0c0c000c00361881d18100340c4103400d5550a00c08400414400e00050540d01060003403851504142e0003940101d41d040e0507514100580c2904010004044420940032036030708403240c25154948040031107043c2d4054011046c003e050032070354548650054100d00540b0701e4540001d894945a8104981c2c030f010300390001d8125840484d00c42541e0400da80038540260804840c2880c0a090a011558100181104a8050b0b0307000401c03200c0c44905000c001c0f20041c04100134450108003a8110380301c0801c001440010401620400710010401c000300c6003038040b1003942c0c1801c016000c0025291811030302c81d0741e0100300403103146540d035840030500c01910350b41619115020500704581c01d6540d0024811550090400c20020038180403c02101c92400040d010465886096180c0ba00828070518000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 552932697 1250 552931447 552931459
    0x6080106030f1404020418060603050102071419030804110301051305160f050907031812020d08040201320c0102210f13020f06160c061d090a240e06 65
    0x200c5503451010f41d00541043e011500400c0300300c400d140800c00d1144001c5e004000c8d514010000080140640290000703500a8502400914004032515161408410614001c8502109501c00a80039000f03907a009401251f140e150202100b0209084810544032403262440c4000c0110030040204003403030300100450001595030380f0f00342403032070303420194010790703219100740340014459034420f0b407004010720814810084680075904000d503c06801c4902803006002d00810300302d0703090144104e00d001e00d40c181d4480c2d03000200c900c14001c03c0d004104900c000c40c0507100d24842103420031400340c020a0190000140d85000100100f179111001c8182c8009400006041100442e102e852843d0300c12142d0001c000000c01e1440001c16010b0700610030361b804000400c51102d4901c1401c4e0094005209161805040e502c9007425607c4a20040300e0003111198541c13440342e03c2c00c0612040d41c210064400120320105900000c44081c803440910505c101c000240c00c002e400d504440c1c040e0004810b07500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 552933947 1250 552932697 552932711
    0xc090925050c0304091a04021b1203060607080901110619060f03020a05090408280305130c090e030904090b190c080408161a31030e130606080106030f 66
    0x6668881c0142e00c5490740311790b9120300120030305030b00c4441e13000d180400600855942c1e4503800800b200c20100ca102c0e0100d442a1415030641e440005e04883c094007000700898100340d000c0d66030b05d80710380c419210a410800d40c880320156408042005c5805429506550048002c004480c0c1c4121980c40d44040c444080c0c0f984200003585540080505445c0b00340c45851865076103041c054a1441224040d10075002c9410a2034142542104501c0104405582c00e201540340c080e2038248081151401800300411643c00300140107503580001030b00b50703060040c0d074100340c48040000c0441e05107070010340d28100c907402000601e4402c450000403031501c01404000034221214000c143d40030007040108880d03000140000b061040c40032007048180e114842c0d151295507100e0101046c00c06480c104038043c15504c0300307141280380b1800030203514010b0007614000c00c0340d03460484002210341c070b205800c0107400c076200c05203011500500c00500101e86880f00c06500d003250003400c40b40429402e28250f0320740381c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 552935197 1250 552933947 552933967
    0x40803060324070f050408070b0a030b0337061b110601080a03051303020402210a06030f110117160e0a15030b03010b060a0c0b0606030106050301030602030c09092505 73
    0x40b950010614038148071403040260080c2d4161103250002d00d200d210300a40000d01d401c4180040041400581c3c0c1030200140480500da80e031040201100c401b0401807400100344030500000101e545100e400d03d0020840507200c2c6c80468160250151481d100d0038098030005411201403448203011034010b1038035603d01480180c80d8404080c00034100103001940100303803480d041388100a183c00910441d920b160368044816140140318a00116800c1000003274003591951054500b1a600411583c5000c03a403039580b04c01050b81190004d061108910409101007403600320540b10701004c200300c07451400d441002400c041d6041c0c900301d20905452009104e03440c0320b09040da2442c04135041c0412010341080c0024094034044132140d405c107401248a006080d400000904901d0050480b003209407201e42c1403001c588024024503010a408000400c0026481d9000f545e001c0100d80c5810b0402200c40d00241241000382c0c9c0007a011815401c07255810f00c810110410103201c5414a1494485188 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 552936447 1250 552935197 552935263
    0x1508060c040e0a0b030705120307060c03020a12020f12011203110105040809010c02031e0102090a0f12080d020409052e0e15010216090c120b06070611070b0408030603 73
    0x381000891030300c4d00c01108031078600300007000142c0b100170100e1000c1100e40031801d40d01d4120003015141103042c2040805140d010b4422100c503082c1603aa40501501240d103800b020390301001c05001c8405040010083d480640014540038108a00c0d0340c0d0342054040c01d00401c0014260041c0300130342d1418040c04005011281243e8072041c082c00c0c03440ca82031080c0000703800c11201c2d50102c002ca1307841500c45041001c040d40140300ca6042220343c44c0025481b480403001e194540d01a040110024901d0403000c02c1c28000900840c1610740c2c400f501c8d144c2c0b9030305514140d80c3c0590380c4500c108100980004808844104c5800410442401c142d1213440d12100d5944c80c800680034010000061509180070f034424480383c504008110345501d00907590b28a02d000420301d502c02480000c08121542c0c0101c440d9000740c121100c001030005007080c5c05a1103940041000280681401c4e008100c2c482c009200c1c01c4901d0b1255000e1110140c030791a11000b41402c105e180103810024418189035080030704001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 552937697 1250 552936447 552936451
    0x801060504121e0b0a0c0819020903030c0d08010e150d03120b1f0f1806030216140601090612081801052206170903030403140405041508060c040e 64
    0x8000c400e00361042c64200410200d8882c01c5003140341403019405824001a05600381c0034200200003040500d00c1e100040310902c00c140d9010107601e80035500c01e051014207401a00c034480005085ea0b282002c540245072400140a83d040f0210700c0340c200400c59044191341c00c0b40d10401da40f100e81d01000000d40020016840d114004052060040c0d54400c1e07403402d03502003035a810b000307401c00840c0168110440340ca03d0560740c1c240001610b807404031b144107110382c82452180c81c0380d2401040031030412006502a4104401e00b02c88000c0e0051540c000c6036401228048000b1080054685941002d54810a48145403c99548188403201c1d00d40001d1030f402c100d45200c064008200e03a02c10f680d8004990620030f603006054400d241d0180c43c14031819591090044a440c0d45520085001850120b40c10440880b01c0c2c1c2c086070070a00001d00801c0c0074103100c2081071600d0720b0b17092030503445600040031a0140720802002c0d2806c000e042c054603000f000025081080d641c2c055040920745004400c5070000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 552938947 1250 552937697 552937709
    0xf010b0712210b100f0807080c0d050c0309330c0c060f01090507030c0e0607061103100906050a030f0212030c03120601022509020a021207110108070801060504 70
    0x40c40c0740d180201c501c5502410164a4070a1001d41c8400c1071440001c0601614800144180580d41c1c0000080340140b2104204c0b201c0e80c0c44003040740d9105481034980c1c02c4000d0103484036000070060407180076250320a851155098103159500c0c1d04112104c3d07880c000904a0380d11160006180c4030300d0540501d004815280a0a00f100072a907465600c2707001d007030044030b0f0031201c544202c4060210720810114003174180d40e03185ea000c00c120354030100704038256045c12070240041804d800c04070115040c440010300505002d610003140d040358165004c0d0140c1c2c41110003005102c0d0351081031018003114003d00e8018042200c08424207425615004400140454020321400c2c4010010200d103500340305690511000e0000c0c1c030307180c0e5241015903060040441e0394600600600407000104402201012400e500c070303220b002081818201e0100007903002c034076000194801c010f40e1034100c0035030340c00030007800d403045920000e104654000034013060307000340000040c4202c1c80014441598443d05990445003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 552940197 1250 552938947 552938963
    0x80a06020a0f1112090d020409060507081e0112110d060b310b03070806070207180c0c021005070b0103050c1009121e08070b010e0109020708120a06050310050702060f010b07 76
    0x301000106080c6c50008000c1d0031508060481c800c0c08402c0d844140f06034419203610490b40d50704100200c1540e8075140100c0003a04220040c003c20940345440503406200300000100030050400240740c080501504a03025078813114071b15600e0410030720301c3e01520841300010001220002d40044002c1c41401030703520a039510481004940d40c1040750600a00d54801654903504241c00003e4070b239907260103200312084842c00070f02c0c0007807101d1140f01800c8c0025502c0f03604252040e0308222800e4150069502086000d21100340490400341c14603000b0b41c824401020403401040500c40d0428101c0403041c14460180010003100c15070b14082c04182d0741c01030350940446a58001160030440809021b0030014000c2040e40400a420054038180c80c4006c03204001617070783c2ca030040141c0c80380d480001d14843c003e006110040c5000354045411241c690008203a440c5c4500109140c4075803500d610030050b88440a12501540511082c1d82169a10b040c01d10030398140b203082039481c0310318040100040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 552941447 1250 552940197 552940207
    0x9071d060f0d080c0f010b0604050907081f0e01140405071b0c0315090c0f080304050d020301020405101d030606011704111507063b0304080a06020a0f1112 68
    0x350320aa1410000d0b94807003101520b402214050550751844040002515031031f14001c4021490030f0b60642c1e04941c401492580e4035980c9030400c4502e80400b034007603602c10010940230b0402d010760001c43c40c081c00000450058540c545a110181104000c000c14011413130b100500c4940b56000c11040414401b203084020001751500d00400c2074140c1d036001814128910405141c1c0001ca900303c4106039002c2c19265281e55282c218150f41c0340e01c00d10070082560704c1004204241d040ca4009440b025000500050401c3e648002250528680799602c00000d400443e0440c400720f810b0429500c00001940100442c0c1303000800600902031000d15020f00e041d98100040400c152007800700c001240c003401c286910000c0003920081d0f1703005640221111800c21455035110304000746551303d1120214145030780018000d04400c8032409008406501d400204400714a000e020002032450600c82e800040c1d983c103002c0e4000745845080c00001080200c2c5c040c000c518003c0c0000d090380d0205000c10390b5170740d031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 552942697 1250 552941447 552941449
    0x240f020a050703111305092109030f1e0a02010203040603020c010e0d090602070b030c1605070b040f1d060f01033215060c0a110612090609071d060f 65
    0x1204854010030510070502d01104100504142240003113054448016042c5e198800b02c0a80d241280c41d072200d03911203111071641400143d40b59061200155040e0b1410490602003424451052450740255208102c2d021484030805002c24107880a4009070088442c140d000035104c0c400d034403402c010146c004c601c031064500f082d84804001c0c4100d40844580d406446805031441d5001e204172800b5004e40c1c0c9002484210300d0084a00c120495620340307117401000d40114103008613002065800740305840001ca0020039800081000c3d002032800c90052600e40780454074800d040301e40c884000c0c5511800d01c5240c1d25a0309900e41004400d081c00714130103100c51074109090403294039204040141c4481c23000590304042c0450f010f007151240d001926040307071050002922600303920b40100d90010b582c4801140d04504031500c03800c0001c00e03480c500400421215100d0400351032042c00313500300c80103000c0700038410000e02006102c0d1065804100003e12000149500c0041140d4000d502c400e40c82001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 552943947 1250 552942697 552942703
    0x2102040b03030706050103140d0206131416140d031d0f040c05071509020307060f05120403020d080708060a0b0c010e0610030b07140a030c1206180501240f02 69
    0x105003005400c40b07072148594100031000e480c00f8030041e1a61600051071041911002c90301c095030040d160024412030702c524848580000c02c010040d00c5e44030b25040403865461060242d40400e005030008420301c4c5080000c02c910300c4622050440c0328484d1101c4403030020303030482c0180942d030309003184606c0c0e9400ca00c40400d4a80860b405955485072030501c036000c0294020000d0040756000d144a410100f003030700100c10844010303c8000c1e5140d48500e4080215900c9400c1c2a80075000c0da00c0c1c00e904008040300c0c50780c004401035500301c005d80c0048801140099001120a512114a180601c128107020000c00e041c45d596004035120076600041c18071b0300c41d909401011481121004407110b514004010031000364807400b04841030310060340030411840c401c0181ca080c18440c80401c03031900c1070404044d4000d0044010080c14010f91510080c1500400d11a0200030468a4031096280810308005012038005800451005080350b0950a6808a08240008501440c1461020500140c0703003649 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 552945197 1250 552943947 552943961
    0x3040309051309021f0809010506031504030207030b010f03021206010620030408070f03021509012f0703061b02010501030c0b07051614010305240103050c0d060902090f0a210204 78
    0x50017a143d00e61600d545005c0b201404400c080a9075104000d03101d82403898203031141601c0480d4544d00000c10071840d8900c07a00350b550407510a004540c0340170783d25515900e001c14240e02080381170000074001c1080d401c000a000303412840081c0034204039814142c01602c3c21301c0c540c03031001c4108007180320b40760b1020701007040710003400042c8100e0b4601c542d11a9450650402400101d010b803001d02101c01c0c01070007180030341e038207054140c480c0004035042a145c201100c0c46c003110911200403010384091038800c03e1055001450040c407020410b030880f5098002d46081042390581160b241070010030200300000c411100b03031600000b0f4150740c1c48803414080d1601c01e0040310340c0f4401c4203005002420540d488441d40c44800e0a890030b002ca55102469581c100c414500b0305000000303284c040b0030301c035032082d800300d51300844110f0090300303049a02e1415012101c041d002443c5242d400246d042c210f240c03044401000e01001c56008240c207060100224540040604200000000201d000c08543c1c5640040c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 552946447 1250 552945197 552945199
    0x5070b090a180c14070804030f06270303060f0302030c040507170a0207060b011d0d230313050d050a150207080f03060a3005010b0301140106080106050304030905130902 74
    0x8400d0190342c5900c0b80041041031407450206041030107490804415034140c400480d0400c0e03600d42803910355141c00c0c00c04e0340310240442d0b80300d03034405040e2855030250381320300241e90f20301220301c0f400c40072490054101c6500360020722507680c418104000695000907540c803890300c103880110b0241c44105065611001341e00c0d8a0502282c20800c00911142c19800781c1900360041c0010312040d003080c00195001101441c40c06101d9100c0301040c0700b81e090004c0080141072251118045407480c03c03004d800c1d00f4082c00280300702c6800000f44848116002003510000c1c26003103c802c040710a0a80d0395a5a41c80034030f400400844001c0f44c180440d181990544400c1a08240300c02d9886084800710748042d4000c40300144508041d140104140c0c4051090b803640101180c02d82e5403882410806c2441c0f9551944101d03259900c1c4c0380406125102030085141500700f20345a40c40340d50402d1806485803005030040010800103208010200368004044800c444065070500c050034801c010810290080c2840a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 552947697 1250 552946447 552946469
    0x40c0b0c0c060d090209040533070f0c060f02071103030a020c1002070e04060f15050307140301150815160512190509030307021018030e0a03061a090f0405070b090a 72
    0x1100303005c0b01141002c841142e85180c404842c3c0105480c2c014802c01280100c0c0500d200d50002d1400c80c0034bc001e6050307052440c1040150911503569407000c0e100f0203410b07000100d4011448000308919150f80340345010342180954141903100c200217554070500402030340700c0c1407400c000c200054003c0c4085d1001e040b0610820300390f0710381804c01d0405802001c110f040350700c2c07402c507415100e03d115840740310a4800090181c08103500c0c0100840038010502200366042d547d0b18051400030b0074110000008010340000b07014140b184403004901500f00401c08005a4002545022959400001c40303440029052a9036401c2e1100004041e00808542c1c00d112003620b00000d105a124000015503c208040d41c21075021041011040040c0c8042c0d0902d4080d80303900300d00701800603010320100100550041c10028043d41c0d04c1c3c41e80011744000d4607081003510100084403009080c0b008015500060140c103081c000c0c2016960580c0c2d680c014403030300f0301115000c00d80c4000c9a45202516004001d03980c09 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 552948947 1250 552947697 552947701
    0x6150a0f0e07121503030f090e0414060601080c030a05150919060f0e010b1605190c0909081902010b0d032001050c120c1b0105040c0b0c0c060d090209 66
    0x12a84907510580314a404160030104150354900c507402407490b4184e425540c5a40146169819111761b4030210309a01480200000425801100306e90700340b05500031620061100811001c0d2402d050340986003a04000c1100104140c40c2d611008498004076111000900c80e80c400e80605500064181c00c0c030713841100c58050061000032140c05044503c4e101c1c004000c883d03511145040c5840103449038030441030f0401c1c010011086840003801c10780700e400c4040900c031800c90765842c0c20118419004181c5050411071942400a01025040640400c0340100710004807600d1340e0707040f80120850090300e034100880b1003400c0751007074010311241c00d4054940107880640b860040c2480b0000c200300ea180c80302003000c009640c60705000e058001c070481e0b480702d4948100004100b40620008029013201c8008000d407200b8002e05040e800001010800001903900b080c0ca450140c0c144280e2040c0d0000d10240030030701e050740c0701041d40300004c07a0840d00240d070361100d403160b20041d200c041030182d170084010341 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 552950197 1250 552948947 552948959
    0x1e01060c0f020d081b01111903020d090506040c1d220f080f0705060604090b0115090b0415020d0e0307090f150825060e0d0f06050a02090a0501030203060306150a0f 72
    0x8116084284080c020b00c47c020804a0780d01060091400101d14414014140d482081c0a41d0040c00180e1481001050520668540398a003103001e4504641c000001a004c1160881a99241051055103020700649080541403400301c407441c1c0c07500404030a0000c05040800864999a034080c81d808403100791900c2605a021041c3c0d04180800c0c0c903617008a000145091915100f2212760f00e0b44180909a00d909118075404072040031203048048c410071890104032445600302402c0141201002d0300c2c111300000381c4c0241080c02c194070f00001d111a04030000380c641e43c042400790940c0c102d484006080e40b2a000743e01c02800c0c0406a241c86550400004500c41e070f004622900345080003003044956011510800c1c40c101807900c5180d0000d03440d010361103003070301d00480e03948440c0d406520004100041a00e6150454100b034600b101e400e40d0000d103031401801c0080003040180030900b802c40c11413422801107615030b00024140400022440036192440c0d4039125100082c20503140780d600480d464030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 552951447 1250 552950197 552950227
    0x1e0d05030409060503064501051b03060d030f02010b19150c050309310506010e011d120712150f1802092203081e01060c0f020d08 57
    0x701840001030f04050000c141810700013034142c06a507003000460001c41c25220805250742c03401c010010803500b20350300242441f089001d020380171a40440009070905000355030a6084005000c01041006e0070300c2006640d585c0c01580700c10150b010b08005441e9850701c0070481c01086011407950b8400140e003074441c0302d103501401000a5030600742c00c3d0341006040d003100f600c0101c0341d000024030a920400007403c007420303e0050105584000020f001c5081c41c0c1001c244803044810505e2440213507071b4400c0050540e4000036100d0144400e0801d0344d00007040200041c1c40c8410f00d00000d0061848501445100c44c04001040045c1303c0c1d002c4644010516150211107020814114502c00b414906942100c0886228061119200d0b00c10131108000b56400c1c0002d800d0300038850480c100301c2800b203924110000107052071062095581c9152481c003205800c40084c4440c1e40810007c01200040c030903941c100d0601408560020040c2c2d0030b8a8891001401c0890b0207080200f00c0707074000c40d001d00c4000b012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 552952697 1250 552951447 552951449
    0x20705131a01210207030c0812190b0f0f0d05031309060503070b030f041406150301051f0b0d0e07150e03060402030d2a080702010912030c021e0d050304 67
    0x800700c0d07480051298001115152440812206540d4070700740b02c86003184083e8020300c801486402d00c0c0c071031048a9240c0c020b41e90024800015080c2c40141040141c1e00000310765100d106203000200461605a004103c11408020b00c00c0d000f840c0c42c9944595540e1030b1410101c9050b44102100c0e130710b103403180603510038031214401d0011140c1058004a082d01d008a0036500b40c501050400b403c0d9910182d01a910000150080e0f4520007200343c801000b40051102c030388101c2c284424060429a40024103003150001072002c080f1214040b070a880000e2a40854400c036065080340a03120411000b080000300b030000074000c0c1c0d52242010016440860788a2403100440c07645514904048d60024540c480204450003581600600400803400b4010070311204901501c0080900455100000e401080a42c45040e104490080780c060115a4081c03007a00140040117150000078241e55806811001c00b480024420728148641e017115410004400e9581d49000340801c1c100611030400740d4880e031007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 552953947 1250 552952697 552952721
    0x100201090f14070e01060507150f141009090b010302060702060d05011d010b0309070b031504141f030c15032a09060906021905030c06100e132102070513 67
    0x10f01c0400061504944e603045040303178501d403a40e0b0b01d0407040c0c3e501c02219110624032000701e03c1d1303540c1c0301300b811103554801d540c42c0c0c1a403200c00102c203017040c2d90b0082c480aa0b0b640110030040c100b520100000e214000c40c2c0d411070368150344550b1038502520000d00640109010200d01d940780c0b0340005070052103107020054070750b0b51170742020030b69803241d1210b10786102c1203c4669055004040c00c2101c81c49101c021940076001c00c85105032290382000081c2034540c40b00c42401c40e1500403050200410801860300401c080030100c10345903501e150b550413002c01f014481c400751a030001c094240c4a50080d04200d040e80034080c0d02c00100c004030301900d03c0040c25a0035100008681600c041030f0507004803044015a070041d0000c14000c00e440324490312a00817040211404d000c18002c0c3c0c000c0c50400c02c9540c1c010b851020b40c2c80f00380c1c0c0c20890602c1a80c80005c000f074002c6030b100d4400c8000f04101c4896881d440c0d0032402d03481050324000c6410f07403038580f26500481c0c1003074181142c5800d801c503640c0441d550140c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 552955197 1250 552953947 552953953
    0x3012018090c0702041a0f0918100209030115061202070213020406050c010e07060c0206070f060e070305120a17060d050f0d0206091b061804060605040e06010207030c05100201090f14 80
    0x540000e9031b043c850902c60b8a680c0042298120700344510348030b000c55500910070000611000113400d440d03801c00034004071002c111038011035400d00a103828002c26080c824080d8022283d1403400c0401015141e605052040c003e500113055010f64944030105411010313100019951a550742c00000c06607480807110070429441c01c42040103402c00800d09004035106070b0b5604840250a07000c00015a01c0144101d4056030007604090010705180500b01a0107003110280a1742e03895404c025040c809402d901e1030203402c0c20011400f6079a004040580074041c000c82c118860350710705001c180141e26200e03018101d4400c2d03d0580403100c50014240c10160380c1a404da07605911448080c0369512000303228400301c0003e4040c05d0704182401e4000d0280240c000461200b00101c1c000030804a44150b0084130000c2c20004043c01070716030302c4000c1c5810190a200500416140d52607a071003984e0940a1076129080101660341c00078800d41012650507002240640d445c21700386400c40c007415a031446952140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 552956447 1250 552955197 552955211
    0xf1807030f03180308180d050703060501171204090218090c03072607030c0207090e070510110705040e01110409020c010b01080702030d051b0a0306090b03012018090c070204 76
    0x505400d1000013220f80c441d82c21810803051078104521100460380c0b1640080d6452605804150108800c100950240c640040d4550510084204042c8154510040caa1081e01d80301d10559603c030803901110800c960040e00c400c0f042a41a100c006d00031310281c3c0c00300050041c01001e918080c000c60288640d915200e00a400d50541900c803091005506101d6070050400a058107010f074000008400191056400086e10385c000142141c0c082c2055112640c0001c2c0c045c026400c2050047d4016007060901c82d0066544048850307440342c0744d0150780c0c001c503290000c12002d602d00b50010084d035110441c03401d03229a207071a5a14000c3d08014000000c540c00c0c84018200c65028000560055156901070b40c82e010b04020740f000074107800b0b00140b00c501c41c820700c0c100a6140c4a00a054003074003d907408229186014009400d9516803d500d0f17100340d00d41107008a6120540c408513a40b91307401c00b06903440e416800d0f034901d03810011030796850300608448200402d10f20040010451944203ca00304045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 552957697 1250 552956447 552956477
    0x2030f0a0617101104031b1e050f1212041e060302030610050f04030c0b0a0815030a0b1b0c0a0b010801050103030e0d02130e0708010e12030f1807030f03 67
    0x1104001ca0074207240c1e04280d102c500c0003550f58201e0b01c1e03880115031602e40307019502e41c1c07204203064a09500501105a14201b4408807521a581d000d815800c01010444141894000781e100c0e641e03040c12912460f100600c525500c0750a02080350340d17000001e2020b8a5954a5040030303507922004071511004441c207440814000e0082c03003524060b00020300121103044030140280e505920044600744003080030b0000000150010b4020005009a00840c540355002040c0191117030401400c1d0140020200e40e00111503200043d40d451240d410602c902c4080c3c0b1200a541c01400b484110804c0001d0000b81c18020428001051100144119000003580c0e99603070850382210401c1c00014001500c801042c4440d242c050820201540010610340c1c101414142440c1141c5060f80f81d03000980049504203c03600082c4945000e0721070301000350920621a000c124614800248940045481600400d441c0c00d190035207500c02508160440389039944904141c0c1d44100480b00441c0024568901c184074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 552958947 1250 552957697 552957719
    0x6070c05060f070530150108180d0e0a05120303041208070903060209060d09060608010f06030218070c050a0602030a06081902041806060f060e1215041502030f0a06 72
    0xb15001135070b40d070380c148409400010804a90411059010322001e17044502908010050600503116009000c0c981030603940054401c00c0c00400a0060b1140d15840300303940708001c1088905e0f440b50389000101c001c1d100c80010100d044a8121980200b990640c18144400c004000d500507030041000154184621404a0780100103c0e40d890006505400400006103241c01034103030f01c0c9000300380c142003841520401085412943d0117075800c44e1608030402c400e0b00284200c0702c80c0d00c0c00c40420301040d410740c1c01003010002c0d1801308000c0784507210700149d5602e119030001d203860b40c0c0c4802075406180b5241400f5019403c141c1d89652650701d0060b0010712000001540c840e1469440c1c0400c0421500d0b408102c000d26401c807901000990291800703001400301c3c4250b002403e20103d110407910b08100340104845400117601d03001d1b0068158022841000150b041c07402c0140310b826031481e544a2400984100c0c0701481600340a00100c14040f2000314056914800c1031258000c120300c65907948100c030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 552960197 1250 552958947 552958951
    0x7170408012a051c1a0f010309031b050106120b07120e0a1b0503010204060512090102090105030f150607080703142a1204060203070302070e060a0e1806070c05060f 72
    0x108458100140001c001e00803030180c0b002030001e4015060b83d5144a01503001d035030f1005000f40300e070400901d411714103141214810a4006080ca020030080341255400340a80c00d2034210900030b240f07041074100820909401c91000b030070445681482c051043d107041708001c1800d4601d240420043c00e260702c4000002d10822070703404c1180c4020a040b100319100d03a441c4da03460000b00660322070101070100306520240010030003400c06589481d5207201c1d08800c01d40b9524060b15004850b401000756001686e40002602e400401c05041c100940d00e4400710280303122034101140b90030040114495003070001100c003507c0c03164080d031181c44a02270449000b03c002c0c840c10700190016011040c030444104000210b6401c81403550044607240c5c4461500c000658003c0ea000000584c00040c0e20020180d051208500612450580c101a410501d000404186907809500302081d500c5000600c100d581107844c8040220a805a400f14241410010300100480400f96068464840814440303500411028 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 552961447 1250 552960197 552960251
    0x80609040b040f020409140c01120209010804170d0501030606051801180221040b0108070b030103020312070201030b13020c0f0303040506010509060d080a230a0816050717040801 78
    0x80540d42e4941d2410040c1c0035400f000c1c0d0704203a031042e102001884140c80305040c09031100c010079602812800051000300b016050255090060200c201d440c0d800002c802c1d0003030350000d201640a489420f06ca902e84c0100914288403a04080c00003050110544c00613003039410580700195640d650704c800039803c0d40c0070f03c1003a540242d07550b03031072020f0f442c0c0303901070b00390000c1c2c048004c0c10003950320b4042000c056080c2c0f0240c1e1804403110040101c0d000c00c000c1900102540c00855041d5071640d00003d84413210480b2210b0316075000184141168480e5220402d0340c00000c08401e48803182d11481d000039044040a91502d1040350300031240745c2c400100352803086a100004000980c2030406111a83c1c4025004c26084420807095000142c2040060040c542c81c42d611000c209582c10a8800a07058200d82030641e0001080103100c1181d00c000220781c0031091401c001c450007980e1508036032034807460708c0140002580020000c4001541c400070310450341903034001d112002440c1c003e10b0100011100d21 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 552962697 1250 552961447 552961463
    0x190503090607050f090303040311040c020a0f030305250c050c0a0f121e0b0901051302010c14100e01051009110417120d0e070923180f030a08060904 65
    0xa54060710410052100011113a0341034104403403600840c0c51904150401c581070b81100d024580030b814203100e03405200071184000c040f84662030711a00000c2c50b1301d404c0642019110790003d6400c01440b0030b4607081c80184121a408081e00c1c020003811700c00075200c01c84442c09058508403651034010820001c3da9074882c0302d044080c1c40d2901480303000d07848005c1124207641c0b528030591541240c442c64020300b8001c8854003202d150021a55003100c10061040b40c0340383d0040c00c081c0142c1d0380280c046044c0f80d03104c140c4080d807000514280d4034158450b040074044600340b42c100c05100f81e0641002e800b540d002d02d241100311b5254120001a2001d141e05100e10741c070305020800505000c100101600800c13402a075154035044540c828461340042c80c1140c0e05520b400c00100319800401981e00203000c03e40d0b04010000540036044d40203c00c10180b00303034103e0f160300030550440811171000c82520165080712000750b0350714180c0392250410f00c005000f00314003100051050401c03020b4503116036804424 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 552963947 1250 552962697 552962701
    0x20303040201113d092d1203021b0304080703060b0306062209080301030804140f10030e0c03070f060906030204030b2412030c0c0117060105030702031309021905030906 74
    0x1454030203140d00e010749030551040205000b24061903205000c0d100b8020500900d074038600702001242c146029490188080c00c280582006c54000140035400048234500542e0b6100040b15452030035150213003030780282c000040d0000d5480000170700a41100c0c810401030062801d48410140c660a048a901d42c02030010120214482c00905d442502d070002088002032451060b1a1000c3c103030404d0704100c1d90042c0c001000d015010300350103041d0421000701c2d031881c115082370340441c0540c60246a000281a101c0c42c013010301c0242031103105000a0042c040340c80850355841c0c4120200d200d880342801240c400c4001086151003402201c0c02d0b00d401c10071000480e11906084800360b4140c502c120050344180018840c15a6180f5010003a801c07084011074032902104171850401151003905414002510031035101100100501a40704000b42406034803959220380503411403140b01807c0c0d861088030b8801244840031075010702420345840f40b0f10b01e034290100c20181c440b0312060b07402400d02da0080c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 552965197 1250 552963947 552964003
    0x908060601030c1101050411090c03100b031315020310080f030304030e04020f0c1513020a140621040b0106030c0806040f02090a030b0a1a010f0e0103180302030304020111 75
    0x708200f106131408001e4030102003c2c0c642160010b8404441d10082c5041c840c4042c80c04402030b6030451640c28245165003420340d1030703140304035551240c0725092030081b001070790f0a02e2410300032018075080b11042283c1380c5c030180010b000350320880b407d1450390b041400205502400140034807520001d5002585152281d8806903081c11807480407031f41c40350f0200f110004581d4044041d040b01100b84000f40070904010818064900c0014600420408052810760245c0e40e200203400c21107058100281c410307404040841d01e503104400741c04452030340c011540102e800420890030312443c094401510183d880c1c070000c40a4130500c0150800045405000c41c500e882e050380303e031051041055005280c000103102240882c5056441074540c03085040801402c03500c42e018100c0301c2c294505582071541b0b032400001c0e10600706111101c041201c0103003000810390180e071040004c404000f0110901c1041442c0003956070744104d80403400034136200440180b0f070301c000620031640445080c2c8540c3c0c0c2d0301505 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 552966447 1250 552965197 552965201
    0x907060c05030708090f0d03030c030f0b0a061407020904050604030206090c060301030b0601110105070509030106051009120c091107060c0c02010906050a0203070611030405070f03020901050418140616090806060103 94
    0x1c0407580c1b00045d03038000d6040b03580315040c0600b0300e0b2203510081410304078800d0180490310b441d0281d02c1c555040c600e54403110394400400c5000c0d6109803c1120031822141d80000540c011000c0c025000a0311105000c14003800040041c42248a50700301c802c1543c946404c1500c603e40944080d030003210900050001880c40c0c0c0c002c9078032030740c10314114080d49100c081040c2034603415a800008908001807000043c2021f0145030090507080d40c0c0e010300d070300c0407000c0201200c2d031071310503041051091071030001001901d40e0b41ea0010300d41c100341413050400c85040c0710403560001c0d604840003468a03260142c020300802c000c4581513016111100c100345440030642c3c1030303840b040000c002c5000412107040000d80510031306a40400c0110910388919003480c0103464161140c0000e19540c84c7c110081006a4a105039541580c00c00d980205003940034440303140c141c0c111000000c21003000c502d29034803542e0303000405c24407516000c46a0001c02c0a000001d484521351400741a0761508180f0024210b94000c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 552967697 1250 552966447 552966457
    0x2090607080d0b131506450303050405180f0f130812010303091212030f0605031c0e04090b1f05120d0906030501060e010c0507120b0907060c05030708 66
    0x5a00d0100f40149980f0000e0002c1c0c0d4030000100a140e5126800c9144201059416006d8442401c1c4001820211208007945829441510303402e4170b03061083d05d4454401020750803075908102525580316032a4900a0003d4215006160040702010405880041c41d1341c6902c7c0583d207040310340030403900c41080b00c2140b104010861000c070700c00780909030005102d00d0010494a000c03041941c11a504510300144907a0f9290701c102030b43d902d9000401c011919121420000803c40c1c1000110510f15801100c060141395200c56418040c941100400c044610000b260000075607a4030b4900700c00090400c0100d0700520030284c44150718100090410804416052140e680d83c284002c009075a07038002aa844420210545540c1000c450390212640108141000c1c001c1d40c10144155814010010200c10820080a04124034054000c00340201031241e88040c01d0380f0340903491003240b9800c6c011007011081c0c82d581168440c1950000c1c610344100340c292a84c1e03910038091440d040e00d50300d44c6606a049 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 552968947 1250 552967697 552967717
    0x1b010f180f030804030209010806070801121104050403021c0f02030a030b040b0613061103040509040b060a09050c1b0c010504050105032203030506040f1b03240b09030706030209060708 81
    0x40000101e000220545241c00a5100300326050f07a560940c03041c00802c1c08180d00450346030b0301c130400380042140c002107803606444410740507002c1c0c0c1240d401d10348013100c400c1e801e068209140400303100c14903502180c0011001d02644510714180d1960000b10f41400d414001c02006800c140600f03800755109400500401c1002807021451040e44400900940c0c000f4800301b109080f0076804120440c0c120302c43c0080201040091360400e85444c002c5004000e009000070704411408002a916a45105100c0044c00351184d003000700d80ba10004640301d0b980f254242011600c0d00c510f900302511000192001f510320103969803070034146440019200e640000e440d00f14810102664107010101c02941ca2441c3c5000b0754020a0b507081c42070a0008444040c0f0031840f1b224141300e000c0741d0741d505222021fa006006440d00040f4072480307880100c8412015541062094000c42e800201040200003424400c8070840a842c0c1d205e90b9036000703800303d00c074105200782c1161050000501090288000d4402e51503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 552970197 1250 552968947 552968987
    0xe120d0f060b0d1b09030c0303030209060c07030309060210052403150a0903080c0c0604020f01090806100501030e0601060e150c1005180f100b030f1606021b010f 71
    0x1844901080940d0411090f0302400c41c1d50f000d48884500e40300040407040302030f0b402d20f070f40381604540783c81d03d413014240406000d01da000100010306484003030440301c10140c684247c40c2c003181c480c54014446d51a0344100001403154545104c03a002c12440391601800f02944181620001c08461400a902d40c0e1184d641c107000700b0212107801100d09000d184101340341c00001522100b41c0c9130140c03034581c018082849c5044103220307402d03140701d00040c03458000341c045410f80c0c00c40c3c25140040382c000086400408990140300141302d0040010b240250039504240c030309000b01010322000c203070384d110700b4866180003446d1511001344908003002a0348808002c8103030203161410240409140c840d000c1ca80c6582d8564883c00c00c0606001c016a0300024009540a00901c0c0c1580a07059078612a20314100c41455a6a107101d00698041202c40c298044c8402a00c000d240611706441d0301c2e013041c2c41400c016004d41503030800138002e10704041e000f41c02c050710381240f1028400300403114440303500800d6040b05 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 552971447 1250 552970197 552970199
    0x92a051c080a02160b0432130516050915030c0d0c0503070e0111030d02030c0909041b08060c0a0c050c030118060f0504020105040519050907120e120d0f06 68
    0x80e0240000b403940420b2900186000c203400080c403030700c0b52566400f812132442c0a002c18054580d5119068440114079940004103182c181340458010000004641e030000309020010141c2581d900824810b03007902440c2c1000090320101a1680c0c45080079041e44a000249442018403007c0301440c1c11106034450301341803001c0c40742d201d012111b4441069020510110030094895880100d8143d000320a2030610003101640d5421076990250000044440c0e0700800000c011080010503118201340041c54800b00e408d0504290010441c81070003480c19400504010500000009260380503460700c0c00000e02e030000e45076084407450310304003040340d03035005400c04020541c0d800d01408400a402c40c1681120308018170340f050442d503480e01601c404609000c00c11002d41c1c1c100d000d641c2115429104441c82407a04404800e081b00d0303641000350b0144039403007400401d642c000ca0412540c02e07102c1e070800280e403000c12000c0d41c07180030507003070741c01800200b008600c42c86543d045215900c12200c4081942 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 552972697 1250 552971447 552971453
    0x30c060714030d0b09090109080910031107030309020909011407030207080c0a05030c0f121b2107020406060309170a260f0f01030c03020d020d060f092a051c 69
    0x3640c03000e6482c8030004d441c0c4401c24028a04242030981103040c4130000c0007803a03030344d40c1c0d042414090480058400c0c400c1e07105c03075070650b030281e08401c5007517404041c0e0551381d814078540a0020054010301764014100752000919943d41481007520380155141c11a0403607440074403c9000c6c0d40640c1d01166103c006100c04c1254140030408141d007103100d80d02540d2124544c10384a4070b447c004000312842036010010a040c5051200203c40b450089140c9a0200707040c0d40c400035240203184055041410725003007901c0100d00190b4058421644210340501c040381d03503520202c05039418001c002d82003400c0031204920030001380004101c4007809040a441c0c00c210440110210008005c00304805060a030402106503d504241d552105418204102c154115280d00740e8070951804000d0081c03403140d24101c15996112405642190701410620034261028400d00160416a100f21000e25912801184040481c5280440b405120341a440d401e40b61404110030710441108246000f40740c00802008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 552973947 1250 552972697 552972703
    0x30204050f090c0307230d0b0703060302010e0108090c090a062105010608010c09120c12051005090607120b040b100504060905030a0c0306020310380702030c060714 72
    0x1180c041c0c03055120300c1c1c1c5084a192410b00c2c100c03510441c402c1d00914010b1100c080e020000e041074a25002042c045c0c2e000344404964503088840020f820ba64800c802c0040d4603038560403000546e80b003a0385803903071303200020700640781307800c0984a0000c0354000c00e038050001e040c44101290b11501401c804242140e4441c0144c403841000d48182a9046d6094540020b203c02402403100400140d0700800039002401e00c001c085c01914002c0b02880381c4944080c00038032000c80c03032520103840803d01202445c0050f241c426522a20b40240b981654100b1001401d05003020585510840942e15514021018221800010507a4004003a800361391040c0885071500e6010031200c510700c4607122540c0d59801c00201800c0342c10340e940018488c0d84110b03541c0c000a441e814004046961101000d40c89071252030388c408005206030000611003050601c0d030341c40f010344a19800d1072941c804000e5000323035209450201c018410010040d400d0b5000b50180c41e200d0400c1c0f0020105540240f03003c8064021022010341 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 552975197 1250 552973947 552973951
    0x4091703070e0a0b04030804050907020705030105010b030612010507050f070203150103060e0f03031b091c151a150a1206031104180f021009030501050a0f060602120904020a050403020405 82
    0xc0020003201e160341c0b440c2018140c41000e09032011000e4109071450351480c40f0b901ca940a8035025401c1d10700482d1a4500811118005e004002c00a0100d50384130381071101e00b41c01c100e83c03c600c0350481ea050f1080c032800620809001d03840c19074444d407410008406030806a0b000b420100d805108511201c0d07032550344002c1c0c1a02a502c1202d0100f0129a0031109910b05007442c1004c0e58940c00810600100403024140401e0460443c2103c917280d8000b400000ca00c00d41c0d9165005c14107603580020700401c1141c2c0700600421540c084100601c541c0482032144000710601160382000301031200f0b41c4004101c20250102e40e0880c9029501c07640720249901c2038401c1540115040808624100074500d091702030300c4050100c100c9100200c1074a070f03c030070203940b03111440039009182003804000d1081c070508802d00034541200c002d0042c1d00b0041c0f0494024901b10788490001440c001020a0991000c00e84e4404c014040f807840c3c0c1000884004c0100130740c040d4180c0780074080c3c01c100010050300c0c0d50040074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 552976447 1250 552975197 552975211
    0xa08030c03031e071d040e01021909080c09192007150c1d0a080a080301081618050c1306050a031d03070b09030705250501091404091703 60
    0x50301c1e4140401d03d290303441c0200304582c450803004000c02600e254007103455540301c16a9107142c007005403040041401001c1e1108824950b500004500001d10000010040305a8291b0345040081e0354031f15401e0389a008500707090303511442c1c40c00400c0c505d5118401d21804111010000601001c00f103070103511024105528180c0c03445c012984000b8845c6100701085904807440e4240048600e640000b069405050000a003641d0101e030b00c0b030b04c103449002c000c10241401c0000c035049403241c1d0074040707030300d4000348103104c410f00c04c01003e0403d10100c9027802049036018803041d1f407001001070854014000080414140d05010320180350080590300701c080c010020b82c1c035000e40e21442d100c0002c1c2a5660b01c981000c1e18079044000c42401c00d070000888039001e0700301e0380b20710180c0c6031602c840c2d00398441c04074080c1c054072034150f6030039a584d0003002050786c0c003001010a80165035540f0054032010594440ca490324044041caa2096040c070b90404004a8811061b52181c00d41ca500d80c4072003a0002e598032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 552977697 1250 552976447 552976453
    0x90f06100303030c0801050a180f1e060503030421030c08190f090311040c030f0f0e1c0203030403030911030f010614040e03040303051b0109120305060402070c140a08030c 75
    0x70414560144143d02d0444540d140c0303c0510343c1002c0c049910030b039035440785009480100910040c0c410181c0d10008500e640c104082c88a0400040412041c45a02c003200003040c0c6001c20005030ba00d000801c80301161000015641c03080a20f0ba00c00500000c80c501c281c041c043d1203d1508001218100100604552025081d50071040e8440040107104070403200320501c0540c0ca820b101040c919040bc0f0f06040c402c0b10045015000440110045c103641d03483c8204881c00d20345001542c0b90183c02c0a00c4540c90720084480131003180c11100751241d01c8a84010240e0810070100f00072a01c00d8000400b464052252010210502c0c0007182c03811240621003c8540d5681c40240b00c0e900d094030b6802d02520044500380001d5209000541e164030540c400107042c4900002e90f001681c0e80d40081150104c00351008119644050410410301d440a0b003107480000d10780b0001400d54980b920a4881144d0020440900c0b0b6080103628680ba0303c9480c401e90340410856000244070004100801d160625840a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 552978947 1250 552977697 552977699
    0x1020010c020a0c0909150c0e06030108100b060406080c03040303090b04060506030706050c0319031b080901050612060a0f18050a1e030f030f020d05150f03030c03070209090f0610 78
    0x8205841690382005020504020620000c40d000f52500c41711030114040018581001e500700765040c232240c8003241e0300700c0804000040c0881011980b5240c1011651080c001d41c2510340c07c00090b8804e5016030b20105400ca00454111404000a5a4010711038100010b01c40c0c50380e11074040f030ba102160100e5030103855004001c55030909011820040c192800c0050030b01c80b024000989a00500100c040c8144c8d0b050a0203400134031940180c034101085c541c0744101030380359400007480d2640440342040c11790b0803d008500c0c1c5003400440c002240c141c1c0301c054002c64540d2484c2a029241e541c1d12038050075120401c114524083c1000b80344401d204000500740d105062914890070b031580e03000c90281c0c10002c0c42c07641c0400c0d088102001d0361951803400007a40400c0f80ba00c00001d0164200280c403c0e4504420408003102610f400100354100312901030701e00d02d50b04c0401d0fa0700d124806000d05071360001d0290780018101655810b0700028080c05880303030108003030301240c0342004c111482d410740200e0a01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 552980197 1250 552978947 552978953
    0x301091a01050a020316020a0f08030c0105243d021b0d1b090c0f020c03120d181e0b0c0903070b070812071107141020010c020a 56
    0x415004550a0030b1842c100741e02400d019480340103100d004007000c601955003404642d82c6990220140c682e2100c0150b880c0e8032801c0c4503580350803000c5417610562804d004980e414229030100810380c03009403a0f0b6106c801e1500184139868840c1c0109524088103040811076840b5083c501000b200c48070070030200d072055403a8000f0300c1c1204c04070251a24000c0ca81070006180c858241c0c0481c90f035000001d0800c000000101e90300c22928550221100518046000c00d40c160300c0706003600321500ca0303801c60702d5000202c410035031101c0c2c84d0041c114420b10200468140c0342959001801c62040340301d030b43c83e03c4084070707102c01d48100c241d07184410743d601c0c0c440403c10821002400b804c1e0440c105007601410a021035011070f40d04e01260003000c000d56030200e0424200314056044070100d501028240d1102d00b000080500480e01c0c0000b0a0301c03500622a012948160130301c0c60030a40c0c04028403001000c01031180c10364000005580c0a00c100200d200341b204410b80034042c0140306001640140b00c54401d5003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 552981447 1250 552980197 552980231
    0x3090109050103050c1206010c05010905010b01090503060708150303070501020f070b0714030103030c021201021201030201090b1206040b0301020405030703110a0509060306401406070504090f020d02030109 90
    0x1400150500d4030380780602c00794507017044c00d40c0c01e13036911036011110781d0700c1d940d005075280344003500004e080d5800c0c0207000c2c00704a410b4001210601c8282c8a40158544038400c260303c1c0c41040303c1e010001610200000d00b0101d4522a40b40f5900c8003134142c91528802d03885070307030a90340640040395030840005040000c00405e00041540181d4514001206c5c0b07940c103070302c210035100603c8050200800c0c00c5268003503540e44119031440e8486000215640d5010350030721003100c0c00074401070b070101c1c11070507001803180180c41c1103c0c40449401c3c07521006560715010800104412440075808d913609000c08210b6480402080000e140100f1324800044008802c03c1903284568120230b010f00c00c540180072060320002a0305401c50012281c03541442d8019181240c0c00030f00303c2000c01043c1e4a20041007010400a8825081c04c7c01815164510b9891105242d5140005c0e520b4000045041008004001842e0700413015079051400143c0303444000c0c42c013241030340c100b80c00c0f6410144d6034001c0310445807524 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 552982697 1250 552981447 552981449
    0x8040c1505040e07090303230f1b0d0806061b03090303070b090105071d0603060d0c06052701020a0803090a17190206010b03010902180907080405191e0305120903090109 74
    0x540340c410f5100e801c582c0c6c018003610903440702840708c0004450740240d054a074015100d86a034240b14098403080343d07903240344900300d40e100640740328010b0726080c00016109030307a428030400c0050300141c5010784105541c05030051510800310709020920100f01e203603805200500e8a02e000d18060805030a0003031515007164005030440d01400115140d0110a5031000300032600d400303007199116182d540c5c0748080303000500503c070003c103882d482030400328a5a0300140540f90355904180c0c601010405071a0383c510300301030005158051780c070070000350340040c01170002194003030f0b2500250382031a05181e40305212100b00d07200c921520000416a20886603501d00040b8400006100400ca15490036021860600c0b060080c100080d0b0000360188001c03130064461440c610000d04800c0300d0340340c108002480b521007542e0403240741c001c40042c110004112180008420380011200b0517200307561914072100702600c5400c400384041404800d41c001d000824851040c0e102c940030b10f55a404a2000521400c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 552983947 1250 552982697 552982711
    0x20115060206060a09021c0c030c0e010503040812041e0c060e03060708070e0d020a0306061e18090f02030a0b0106080a1811010e03100f0507030501060f08040c1505040e 74
    0x401c0100f1555024410421074518040042e510304540c81c065110000008002002070f0a18100300d03601035041d40b24000e600c0440e40e0714201150250300440c2c0310710040c0c078003928521080c010221150000c04090fa001403064004407401c4114103002c200e010310000f030a440b8042003600030400140c0010300c620807508128050006440c2010700509201c20151000003000080e1001a09545840079a08000e68009000c00511036480c03502c04080e200c5802038a814812a400c1c0300c44055071802c000c0284c41501201c103542040581e40d1300010700d40c501042c5c0d49890003100c09005030b1401e0210348070481c056144012158101103000d0900400a844c5035215450080001c020031040144117452036440034030344000300c09900c0100c8220003100c0b81260301d0300524001065011266100c01c429085c681c0d0203001c4c541e0f91403419401c60310248500360204426030f00740c04046d40314000043e4000e00c5a4101d401c0300e0b441350f510f2081d0b28846091140420b07030010301800680b0030b203c1803a500c145 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 552985197 1250 552983947 552983953
    0x50d030b040207020112050919110f01020307020102030d090809090906040204050c0301060e190f08060103030201060e1003020919050a02070309080a02100f0210020711090a06061b0c080a030201150602 88
    0x12140e1300003400702c0603450513581840e654070080782101c80180010080903822216136004144c0c0350410701481110390541611410107080c25641c2540040141d614442e0143c0140d404c004450b40f400c4080c0aa101c41180d070300008000361605a81c0b102c0e0094007a2841000800403440c1910611044403c080c28480803078005000401203554000300360800070b01c0c192001843d208400c4010101040f50340c00c10020b0001408020812410000d0440d048a00030350084c08040d40d03c9041800c1d001007030303500442801907000180301500b03200035100c0d04207901505045151641c803179160200c031030a446000056400056580906a000007100301400c02c89000d0411302c02c0316400126402e1151004000344070380348044218550003032000c160600881d040c15035482ca0301d89400e1444440c0340500c40e01c14050f860210300f40580b28030070754041d200c0648405c0311558040405c8060483c3d02e070411551040e4280000c95803070030070702004422130300c29000801d19a00c1e01c250001c0000c1c81c0d4103d0700c2154 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 552986447 1250 552985197 552985207
    0x91110140a1d04020c0a150908040501050319050a020301060e1e01030b060c060408072a050f04090f08030603011103150904020406080a051f0c1425050d030b0402 71
    0x611000115801e8600c20b0510345a642180a010441c0c00c5191000c6580140301040c40314409401280c081a960710800c0030001c0c2c0c40600c119070040b201520ba01410030385081c401400799500650040d03070002c09058140c12901007003a000c400785c50003296540c0c00c0c150084010014550441d41d0f00e5107180b42110b00c08201407000120040113070030803085504141c1c0355403545442c0c1d00c0700c8040700d0700480840d041d40c0b07043c6801d080501d4540d002034411a01030009420041e4802b007409400020481c1074103d040685250408100b6030070301e0030041c1a80290f5403001c8030001504545c50703800c1244a40c0c0710a840c2d29190003011700b180e01c2d000000414034801c00401200414000c0110728500f0200ca031810035482d9400418003c1c54503400c642c44d03d128000c03c0381d0502c0400225524078050401c00240f1403090107802c8000c0d52410340f032840100c1c41040246140101d41c034041c00b48038245492a0000540190708035200400c080c0d0295020b40025000d081c15584c18001c500d134400043d00c0942c548 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 552987697 1250 552986447 552986477
    0x30f1a070207052d03070f0302030c0904030206040b0901021309051602030403120c110604171b13051503070605040e10050d021e131406100503071d04091110 69
    0xc08000f0001c0c1e450241801358000084030100f1440c1c1e000d000103000c64903c0fa4079000d803004024440d0000b03911078030440080408a140c1040380d184515455405003c103600c542d6213182d0400c901a0004410755024003034000d03d0041404907500034240c0050114045c01c1c0480103a00c80c0561902c904115081080240301160b8100c400191040851528085403186400d001d4034072050103042c50b41c402130006001694000414071840c0701650001682c409406d00b03401c800381148640351198105111090349050709072a684801d034802940040e40c11510b030900d000031305041c11900070707102140c0049403d002d00b100100810341d000e8150f00c61120418204000a1410708242200070301c074102c00c4080000200b80506035510810019140341e1101d0600c1400d40042c0019100101003190f07200006003603442c10441e50583c1e0405602c4813851070b1121002110958800440d5860903010b01c403041e502da031a00e20911000da806a003800404000c41010403d44001c44480f46041141c0740a440e00c1c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 552988947 1250 552987697 552987709
    0x9090e030f0310030503120103150b091b0c0106122d080904020d052e030f02041817030403030b011806110a060e01050f0606030c03070305060a030f1a07020705 70
    0x80c1601d0041482d120f9460500070030103005640c000800b503010200706030502c001d5450049060740d02c10a20064520005a0740c0b0003120300c858501d5900403141c20200b0840244a00d52090f400700e8034005502d840b001c240b6030342c255a01079020100c04601141d500091045144442c0740c180c1300d1140341000c9040303215031107440c80441840907201490005010004c3d03910381e070490b40000c0c4822002e000d9480c100a0860345092417000390000190255100341d035001c1d0000002041d41e501043c586801103858081c000100207d104600c8002007091003800800c10788828042c503c101c14030025580d00d09881c004040d0b882c0740345414140201400180048a00b0000000940b451072078010310070f00c05412420319004a0440c080c224600c1c0660449059406400507842042d54204240c0e89841e81424032a031840101d0715908110014008100711030b1198002d40d412000017410b0f00380d8141c49403a90701c01007a0240301200c0503060350302000180088501c2050b4403188a002034481d076898103010401d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 552990197 1250 552988947 552988957
    0xd1104240510094e060504021503010e062b060e10020d0e0d08070801030803040201090b030c090f0609131113030c060201060f0311010e030a120c0309090e03 69
    0x101c5842910741100c16644280f9191009000000701c50030b00d034849450251282002c00c0100500031140d1189103901c6201d00d0f0881d400c100f80702040d03040e4143d261100b50060801803c220b84c0403608032040202c0c1c82102001d14060481c0d1940c0c0c5805017040c100304207030709040300105601e152102c4003a501c0701e00e03017048061341c103504140041110b207070a40d58641800c06040400c11824404900c03102c1a144651040e019040108102c0e14020078840d404d6502441c12224080020350040044c0005642800510380161040c1000d8002a4481c1559001d40d00111070031400e004000c610300841d4945000810f2281600f602c0a901e031244003000310f684402d101e200000182d440d0220880355218070411603840c1c0080c4e4801c4010f507a12071903e40003c0d855072044200540c245040070400401c26212441100d5100e03201e0b402c81d23078200700151403500008084a43c54010a5a8000420888988183c103c030080c0e031811645c0080b4035015003c1e02064004070400d51070450004640c00001003112 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 552991447 1250 552990197 552990199
    0x5040c0e041103010606050a110708070317070203030a1d120d050702281d010b0a0e06090405090601050a060c0b0f09030f07050709050604090f02060d020403020d11042405 75
    0x44010354603420408000b480c0e107800290150302c3d000c80003400e294444040c02c01c000c6556a00250104811001542c4041c40d024143d0b01c0c0c0c011703110400000300800c07101d103070068101d01c0707403401c0010980009065412011031400400c9000741d1090000c08c032a80e4151100d20f040310268100d045401d04950b80346420341d800800d10600080354005e43d640d0044107454100b5151510f207114200c250608030f5904544a8a14124201c07156007421400809905059940040c115820903006d00001c03611240e003603a400b03822680410505044d51194000d06110b5800c1000130129540b6100900558007201c2d07010304100080001c0c0007001908180f180e54010200c0c15400010f911100d5150f801c42c07246840c9450705a50003d40c0c50b0070058045840f2084402034201000660f0750041840f068420081004045030300040f018801440c151001d4000300640400050601d03807a50302103030350369540c224191440340c111014680c1a203003d002d000c076a441c44c3c50b0100511801d180b80000c403039030540156 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 552992697 1250 552991447 552991469
    0x3070f0201180e0c070b0115141b06092b080c070501060506130306050105010504030203033c0d0f090b040f03030b100309030f030608030412080417100f05040c 70
    0x89400001a442c00000381c41400f108228604015900400350f030f0040b40204c45440003240001160710b01d50614a000c540300c0d4840480031401c03a2404401903000d41d104d110403040444c1e910400d00001c1101c18858420f0500810842c0304814580c2c04000b241d4014003055484c2149104109034410642c0d500002485001600d42c03245d813802c140940000d410903030b04146d020a280d4031401c241701201c400c032801201d0400090762101d00449451041e40006500741e4004c01010011784009103081500d00c3c00c681c12204c0d01184100c0742c0024498030220030001007804150b10b01211038034451011154810300c801c0200d04050f9641e00400240100b01802066000c00d4450605000341c002c096225801401c820f061800100d01078001d02d80d101701500044c5100085103c410b00a108080a075402c0c04020342c1000d00d00712002e10b183c201c41001300c420210600000400110191558032003510326009041940b45017050441254101c105c3da600e02401c00081c000861929108a000d8800c00454 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 552993947 1250 552992697 552992717
    0x90a0506090d09032d0b0a14010e0f04020a0513020c0c040b100c0602040905040803010608090a0804140109030c0308030610020a030e01032403060b0f04020316050c07080d08071103070f0201 83
    0x100701208260080d02094141c44803000108004880350500e10540c4104410084009a0523101030421424082e0340354a9010401141d150400e808150340d00c43d1004100104064036074000c038044818500c006089a900414044d001c40070a000c91001c030380307040e00c1c100315500c00c0c940010a485070820602c1c061080c0d0544a0040c0030300c54040b600640707107044041c01113040c28500600c1c250700902c160000036950b180444c0c10700d0b101151441c65190089001340c14141812149001c950951480d1410700246490000010301c1e0032100000031402001e00c541c513450504144811090020032280840d00a60268400079030024681c0074590428a070025855220300785900349040d41c880d81c0424498040c50000800000350030240540ea0148d4100008081e4007080c00280c1c041501e030340495510503c00600c400b1f10420140c90b61005450032260600e07070790300030582040b000100d8040000c10103003c0100f41a0440410225404004c004516101051f02c0b14619150201d100904200034005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 552995197 1250 552993947 552993983
    0x3090d0302070e0c0a030b060315040203060a030204180201080601020f030a0503130f050d020d0c0c0b09040213061d060a021b120f2506080a0c020a0b090a0506090d0903 74
    0x10600d0003400040140100301e040802c0c504d000758010401c0d141c000303410301601819a00f030800a0300c1c080c43c400c038403000000c440c2008110180d0002400c10303410a41c001c0c40040036032741c1d42c021501d07814001c24981c5a040b07a10b0000401c400300051100e410b5500c91244160f41c07060000884500035424600a03071031392030340600e40f61059502e003409011080145111400d10a0106402030840c0c0150201ca111604001c2c0982c0d83d003244000207000046406410400a14203030006e054200c0020001403034031a580050b9140c14500b0741081c40014207429132580409804d0402003030821080ba4403900300740d180300c4001d5440d40c0c5d07010006040200075240701e0841d11281c164908650382101610f0344108030048403580c1c0c4200d00750048690111800c044031042d1540031007401d4a46542d035004883d610101400050310440ac0a00e0451080c0f050385804107200c120329a010f03494202c00340c1140122802d00b68903064014188207425000308441e541d4407078000c41514222648005c1e01850300e50218 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 552996447 1250 552995197 552995203
    0xb151603170a0f0c020c0105160606051807020d1d10090305100b0a050d02090c0307090b03010e04142a0d06060b07120305040203071a070c081c08040503090d0302 71
    0x140c0c0d00d422030058020b0002d684a1500103400030b00034880c00f001051503001003260355034110065180840c00c10881d040718101c206588020780f0340210b6011900542e1040400d002010032803050790400c402d0003c0c8600e141e03044c8103600054600d460460107518552640d0007003402800b000701c0c4945103001e500203066006190450007507411005030354a0b000711724007580141401c46101841000c0c80c00c400b2505180c00094074490300e802500b40300c07850780d4030308209142e5030003c1c05680a2100045000500781c0ea000c00a60184c45032151300b51050070140f030001403117501c0d4132004d6981c0d004100c5038020003402443d41840c440c4840c1000400050083c00b15220007088000540002d08042001c51440c000d4802061603911500c0c1e26812508040030403070482d8070a80d00298036401605080041080303e080048070140c4030281c85103009801c1d900c581c00342c40c00360f000d0540e13030f04a00c06001c0c58040101e0703124005017aa040404441c40c00b951015140d00c0795000c1030b8400c800320185502814420 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 552997697 1250 552996447 552996467
    0x40201120e07080c190303030b0120030915182110060510080f060904061803080403030506060405010203041e030c0305072c130303021303030c0203010b151603 70
    0x100c0000c021405900154607128009030040c12558480c1040007503090408060380300f00300f40e1804890300c04908641c0c040b0040d01003002558104030080240d00f010088010b5001641c0149030002d59603070050038203100341151305011801c041001440b405083e24a901103001c0c00c03640884155510800790090900707140003161420005200c0d10841050070303079444d03000c0c00c1540c10442e4000800030322100112a42842102c40e483c0c230700070610200e007050401084040d0880e1080e040403990b01c40e0b285010109668a01003503002411000c20300007030503018820390340c2118082d1440b41c540380c18000041d5a9115a1003101030404180b01401d41c6a0f910b804e00101440d840f40312082901c1c0e0b40c0c00c2c0300d50b0b1601240a003002400328121b289050f11010b036001008114005032400e003c0d0384c8d25130504e10301682c55000354103054080080c080d4000c83c008501001d14440d84403464526454018036085076120014903015082030044541c80d0344888003034038404014540d5400f0409000d02d022030700b048034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 552998947 1250 552997697 552997727
    0x120a021306090e010e070504180f0302120c060601090503070b070206030a1517011b0c1211070609030314120c030c0d0f0f0e07030804050607031704141501050a0e040201 74
    0xd8064814003c03801904400c80145014003220302d143c3e150410802203c11105402c1c0b10041030941280002d19070720070200b08940a4016a200d2907035103160003d8070303440554880c1e01504507400304400c0d5138001005e040501000d0f8000d10300b1508050000d40d0510400b40040e100314070210005000710907581200c501c1c16042070249581c0c2d691071501e440c0d58280199202c100e9400c1a01c0d88402e601141d01d0b801018106545100300451603859041600c440b5028042c20401c900f9100360916400f044860014541542c404640714610b04008090303600c0c0210400c4c014000300818085100ca01c0d1116800200c0302201c06e030b981d180d0005151a40c031409040e032850744e0070061000c141170b5060b40000304103030040500780030041004045640364072640c0402401c1040038002840030781000c0002d8240700d442400d2601000031a44111b1601d200c00315801c8405c2d01d0745e001c51584044050064080c0621080e2400b10349506204c0010750a0b0120301565a40035001d0380098156071144c224048c104031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 553000197 1250 552998947 552998951
    0x3050a0602030f0109021903020f09181801060b090127030605220b041e0209090304060f14041211090f180304050306180c0a0f060905120a02130609 65
    0x1805180280180d0002c07103265049115200c00001c5650041c02261b03001c400283c550009021101d106070300a40102d0023203000407405100c800141e403120341c110585d0100092400300d991800c02e0a0340c034071403c0d81c0c0c43d0140c0e50341440b604210040002d42503891090307003401c00380f4038044c101c01200a440a81c80000601a400010010a000c0709605c0140030310110310380c402ca21100c80c21014580c00d44220700804034840c140028000c00e0544d940e0380c41c40c000b0142c41070404601078000440004003580c2c504043c1d00001020403580740c11615500003411181000409000112075200e2980164441e0000100018481508202810751003104401e80288041d11a00f030081c1c3e0f98884007030884401204d03481001000c5120500003013603804865004008103419a2902c50f80c10b140701355200038604901c6507045c501519682c882076040600704204420030000d00e0030800511050880d4001c500609046e00300c006164404a21444126016600b0540004001680700010301459005200880c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 553001447 1250 553000197 553000213
    0xa17071e0908060717040f060b031032040b040503040308040b03060f01081b07051504030f080a090201121a120a0302060604140103120507050a03082403030a0302090a0305 75
    0x50380001c0c1103415601c410040f034842d55920441681c00d40c44c940b00c403180c010010380001b8006503032a8540c804452240b000402c0b40501130000c00d14054011040c00d0700d080d04c0d190b06040c41540c14925880ca1141c1c0c030078010400c064900e5450100d1409080603011091500016080c408204101d0f001113a0010009649640d034040a030303aa508140d400f03d00c2601441d105006d9507106a4a490240280103a6218115050405e00506074411030040b6514051400705070646000f002046104074000d481d0340c6002c600c031260041c06c01ca4014800217a50745031165a40250b6030047c01c4504c5440c10480009005803000e6900035503120307068205520a0000b15419140c1e4000301c0c5140040d446a0215aa00d490721b10401098480402e2004684984007004001183e00c1c516014402121824418500140b07034803800d007010208841500811881420721040c0d41a004104000200c1a5030003400103a0800000707481c0c1c40f5013800070040680100e03403050a995010341c1c400c011603000040b40c1e458 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 553002697 1250 553001447 553001507
    0x30f02010221060f040c020606010c0201020106360204241b0302100c11060a0209060f030c13080f060a050601020f1603050f032503090b1201080c060a1707 68
    0x1e002c2c12108613004103c40101c4400c541803900030310b800095103401808040d0703500c03c011614030841c01002d0b81159250b52000480d58210b5007402101c0c5000319002d41340240c451700da001042e0341800b6840300584100030410100803400c1c80c840c90240224624480810f0b55070007102d80c00c224039001030b10b0b082c03504495000c254000525500c003185081051088090b41801643c00c580f90504408103900b0038000075504100d40d500510284100501c0789080207030703060b4951140e41080b0b441c044040c0f000500142102d901c040000c006212000052500548028031103450b00806010b8403501c0740c0355400300303400780c0c003c0c000190303184c0700c5a0032600031520111216516608920081d0390030f000e5002c82d115641e10100c00c0f240c0008003910800d01c03c1c0c0c41c00c20001c903030804d0040c0c01d07000c00c600c44001050000d28240105603014112144107125410450305509062099217402e03c200d00401413011203940110310220320100c81c180403000e59a42c00c2003510200080101c040480041000d19204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 553003947 1250 553002697 553002757
    0xe060a110f0c01020c0103060e0610030e060906100e010308120603071814070201060803030f040618030c1b1805151002070614040f0e090a4407030f020102 68
    0x82c28002d0f82103c1603055080c00540c1203580301c0c010101c030143c4900000f1a135052606850207641901d00d0b0006071010152081d03402e24409071058103c07038014009001112401900f500050485609070190651659940c1144d501c2081d80c00c03c00559082e000454980d4280105001010451500e5004001e120180402000290a0031004c08522400b0400540c814800c8034250340c0c1c2d44005529544501403161035028008100311445902c0e0385145c41c036021401d5043c1c440c41d11030740700e0310003038000b500d0080c41d40c841d0340d1400e21519000304070400030b40b08101000c45000001481c0084c0c070707403510f20040c03500e020b40301042c41d0440800008d130141240e0004d05041120f25503900c400c18180d00911615141c4142d01c20b44003090b5250f0030034412640c170003200a070000601400c984e4040d00513621321504203490a180c0380b4452015041040d03071080c40c2e40b0351300002000400701c00c02007012004030085009283c0082d0401444000700003150f03000b5070448014411844d4110403c0340030403410300b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 553005197 1250 553003947 553003963
    0x120409020a140304020d0b04110406060f031a2d090c040f080d0c1101110a060e0705010c0c1202211e01050610030b030a06050a06060f0c030e060a110f 66
    0x4540c8144042d5560304203090f84d004581c024403000b520b40c0c107138444158810015006a4120b4407a1540b0300040c1d885108510041000340c40f002d1140300509400740c22100035507050484a207a4886854180d034801c0004580441030070409455180101841c42c09144c45244090300701600e0b40900c015503000c600a1710448030170341910801d081c2c0300c0c04095190808400c080011401159500700050320b81c9010601207030301850014507210018115500d001c0c002e107010f40701e4030341c0c0380c0002045c0781c414441d61024080a0070b1003456240c1a594038118485d180c411344106a2a044c40d0608560310441c0301c99801c40c054010001880b0071072542d0761240410a41944052820300c2c61196000060082c240709000c002c00800402d6205a82900604688100240d042c003c04100c9400a0518442d450256204801c001041070a2100240402007000008030501000b002c9013000a50b20007010b01c0014010750302252640d80b00c060070f40341c0c0e4201c02c0e00c0c4807150007240c00c80c4180340e10000b000c103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 553006447 1250 553005197 553005217
    0x70b011806210201030b0f0d0f031209020a030818031213121e0804081603060b0a0e01180605060d0c08010b1303030c14240f07091712040902 62
    0xa416602d4007030501c03070780c00c10102e11002c03140c103501c002c09513000340d10007400408003a18021040d0101c0002600800d20300004030341d50702000055800340369100a100c481d5220008e0104615000c0da0009003542d03496203c02000034200066070320340440e605105140e182d4010302121400503080a000c11207400111401030380044100c00010000040c0380b109040542151358015a00188044d4440800c03038500180c0d5041070030000042c400a08001c2404004920241c0300d1a00d811890315800340ca05c0c40c14080d01c121150103060000704c02e0490050f0440d40d1480b070b2041d03020a8000070b00041c0c407031940300ca6070016020804564a255641001842c0c006940e2030b408a41e81380c0100c0b010318003502d1022100110301c02d0050001a016002c070002c0e150045807005141d50b0404801858a00c18080d08805403040c0802032071500c00912807242c120081003540341052400340030041a11000348601c43c59a409030380e800d00c00403028000309049000f40080e82d5941c94071800c444010798040c501d05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 553007697 1250 553006447 553006451
    0x804030606270b060702040b1503100f050d030512090109020d240c2007030b160206090a0506070813050714010e030c130c120c0f0f02160e0705070b0118 67
    0x100b01d80850620501d03400b00030041c502d40c106001a0240710003001c110070126006154100000145090b41c000b45100d000354070050118141800c2044814101c541d003e5400b42c5040d62019000940200a48002a00c204c801b007000381e8403800d035517004d422000c2c00650080820380503c0184000b44c0301d00f2040140313600076000301d034200622000480d1002010603000941c1d16026482c03045124156040b5807040e4404c4a0903903407a42c0b03e40c044c204007030320905c880308180f01071700c41c600b40c0500005502448082c054820510262111511504020505410000d1340000902c00ca506020510712840d0040125100c10b9182c0705100c2d0001c441e80e6465010901580d1401081d150004c0c2c618003901010702a50b0040e44000215030142860800e50410b000582c0c03200f2801a00790b10414490f1804d41d0744500800c1c170030041c058030003a4810310a0301150044882c110341540e1145020003142d6180307800c0c4070547c0d52103034111864050060001c15a80c814000091140702c403a002c1d1480034091001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 553008947 1250 553007697 553007759
    0x40204180b01030803100803040b0d0608031303080d060b0a080f0105030307170a0519120609050402061204080f070609020a08070608010b070203190501050414030a090902070804030606 81
    0xc06680ca041200e4001c086051a4006200140313420340a1500848001c030300c0300b00701d40c1741c0604c1c50a50700320b80c11030340e0b00c1503022403810340c000c805026801c0108403c1000e1807501c2881c800341c2e00820101e01000c0e00c2090f00082d40340611000f50321250041001640b6903445820710100184130070425200c0c40607521408001280c1d901d03020007118500c507070140c000c12082400007001000f68020b8907400040c01814480c1202050368541c02c803d14494540c1c51060303150801400004862064000c041c403607182c0010440181c60303c104907184291003a07000515982c403450400349a00c0b40070801d03801c19101141c0c40302002000d403c8100c0c0c3c00c2c8201c414170341040d211944641c3c0c0700710038890480000c2c4448010400c2e15140c2000741072a42c0041c05941303030040d094203000680900d080007140e05079910300402080c045840d03a600c002c06102c0024516020b0591001800c2c0240c500400142d42d5002038402c00b04002c040440b0000e6622800a22a035903440c488515040180d0000130303144110003032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 553010197 1250 553008947 553008971
    0xc0a0203190c02040f0b03010e07210f020d05100507261918030e1008070f0c1a01090c0c03020c0f0d05150601120501030b0c031f0807060e010e0a0b0f070c0608040204 73
    0xa05d0740141d403100bc0d00c4029810920109404410144000ba40d51448980512001d41c5510700a40340f000d000d2002400c0390803c0c00307005411031320024440010403200c6914084d4000e01c400c1083c4428581564001c02504e40c08610740e008040c1c01c0303000703428925010400c0c0c6040c0c41035210703103445406520b81c2d015541081c4140940030800204038400034200398001203002d4061540d111808903103140c01c0c075000741c0039980c0e6204100c2d4802d40d181c0d180860790040080e09014080e0001c4e002041c0742403010001e4030744d0040d59420b03403013100b1071043d5403c04690031191110340d1554545500001160041882c44201c18054581924840d00041c81c10a12101e903084902136141242e500141d95000303581c0b0381d804920700380c10107010202c41001c403581a0108940b40c1407008040c080701c5011b840018074211000c0e201a56060180c0d0500043c080e0b114080e540300c02001d001c60351920115561051b205541c20002e10a110006200848070384011502035070119215224a00c252000c003e205802a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 553011447 1250 553010197 553010203
    0x50c03190c050d15050702012913020a02010e100b09010e010f180f0c08060316080303061207050909061f2102010e031b03060c0a0203190c02040f0b03010e 68
    0x80040c24032114060100300a0a00f03c07a4042080e00695480d410560003040c0402650000c4e20b040c00181e440300750720030402034045007041e48450081241d0421303641220228100080e000c0010106540c041403104155000307401400c1c01c001600d003510542c02031101c07100d0080c00401200c03400340c0d42410020035004c94100250b8140c68203102d07504440391800c0320071100059145000c3c6011911001c070420226414003c402d02d5800684910321545068802d061418a5002c0140c8518062550030400400084126070b00304009541803c044051a81030a240c0f00c200d40c4810f800c03200600030000c4140c00071a155028120203101c200f41c0d445041180100b0001c14010341c1c00b1440c0e0804451220f030004680708800b1807040c100003000c054600002403d0160b200d103e4160a0156110404240750038088141d00003940c0007641d0034030b009408007d41d06e00820a194100e00c2e111856081d981c3e01402d0b4940032103070300a2062041101210030b40c4003034405905040c0c041e602f001c0c2d295580700008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 553012697 1250 553011447 553011493
    0x5160807081203100902091516120e06220510080109050c0406120c12110406080603070305060f04060213060507150b220f020403050a020a06140d02030c09030a050c03 73
    0x80807040021402c01c5d0307102c00258445e0701c1959004802502d01e0481220b5080a4171601e8070000b8288405152420060000310841c10038034108540034200740700d141e480381c007600d10502d0340d07070140c030580c641c5104080132940d003542120340e0080030b01840050b4160b0020806060300c030090f03814031280d210101c48a807580103600410001c141107e0f44046402c140750b2000445112a1503d81c8203000509c2d44403045400114050440404c0002c0c1480b083e07400007102d5800000c15802007184c03502e591100c545810000c3c02d4a808540214045401d01ca40340d0150303410b013540f41203155091603a80c0c0024041d640071101c22070706c54281d0f15003c0b280410710301c05c00ba5000005415445809a214000c1c00d0980c4407001c10391481da036548502c4044100d5101500246116600904605140c0c4c010800c1003a42644400100300c6011103160410b0016400d0702e145c0e02020b0000740e03e03501c442d9002072081c0500500c854040c8544000501800070004001002400940903500684008500d698442d602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 553013947 1250 553012697 553012711
    0xc0703170f040b060120010506010f0914060307140a020c010906171602070807031101090b07050a0f151b11010e0c100306080a0813050402030609040f05160807081203 73
    0x1800006400f0890008050794131520502d00755080048400d08203003001c1d03c00340d5204a030b0395100f0800c0035650f00020248640c05443c280390034124a070039000c94031418003d90280c00787e2004804196010b0040b540802a03a84140d00ca6807950809070000790345c0d4480ca210070303000a4002400080b03850055152451400c4041c1c0c4081e1642d894400f1060314500c0c00b44e40324114401c000e000200c580050000e20099440b925149142070000c4000526202c46a000400c00c00002c202010001d4400507018811030781c0000380003200401c0d4204140141492a00320740050b05107401e0310344294030b00c0c82003005003e40d61030b0900b001f101c0b404102d00322141c100c0f02c110030342d016111040903441c02e10380da0790301481d491801080d6141c03604621400c1090000c0102d07000c0304041052054400c40c1c0b0121006008140c42c118190314107000002e070b803c50050005800450801a05420310106200c113400c189598096200c80c1580c03030045650720125846012030500600020300c8108105c2006c803401205 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 553015197 1250 553013947 553013971
    0x111070b0f01210b0408090a030c181b03050c07020a060203030403020f0106150e0604150c210504030206030411090118050609040201051e0c01061409070f09120c0e0c070317 76
    0x9056544c020521902600039902c4178400e002c030401a586880440e03001d50312944401105514100d110800034a450300b440c0700b004d042c42d198090f814002c102c5088001d20f54600400c081d11100a0087e10b03200340000a504203402041c0070132690707000002940034520a50888a820003087ca0450032195a405402d0850031141c4245403000d1040b03070214441c8100400140c03500703944800c003c0e2004e14010070700c0e000c900c1d600c0078601400070030040c0b592031003440ba14014080c0d194010040240c0700d42c1c0002803107400040085401e220403810a4140aa8080c0c50001996110720050915020f11801080103500748000500300b41030002405025660684910b400c00259075200d4090100d040d4070b0194945080c0719040d1290b409002d600c00070b00b06128180100c0c001d200500c00c018000038101803e01c0703104007811400c252301c07a003080c04954076281d011400d4049440c000d204c0d000c1c5940503881c9002d502c4140303e040e103034050082c40041c0c4661190805105406d6a00041c100c046412a551403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 553016447 1250 553015197 553015259
    0x20301180b22110d14070801061407030318050c120111030a0902121f0609020a0c030f02010204050a0b130f080a06050a0e03070615050f0f040e0111070b0f01 69
    0x40a034244002c4090519a804140000254900c0031603401118002412588800c44042a50100c2d10203641001c20342c50400780540c10848042d05001e100c00d04004d13420760001e4175000b071500c00e9200c40711002d4682010540c00e8100d041c80c503947c040c0c081c203582c41040601d040c40d8182105100e64050130b194290514115620041c025008050f0703402d00b81e800404420042d9250a011300c0b00c3e0740404a450b8908110709080d003020821900140c106403034180c81001010758094202c032408040d01d50601e041041c0740301200c2d00f00d0184c0200e901c000d801810100000c01e081c00a42c01611460300300355000d441036555134854200c1c0c86064801c1c2c1c10142c001012010102c4c0541c0c020560200004d1804520182d40700b003d00c0c5941d200c15015201d840d070b00e100340e070304031107403900310800500040751414124281880080c014151900350103100b40e994495110782c01100b0340190142041c5045030741d031a20707118100003141c0001111560103408001c0008201c01110325030b42480c80c0c0402c00d04003020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 553017697 1250 553016447 553016479
    0x30a0e0904030306031401020d140403081f080d080411010207270605060403050313051014070501200d060506070b04080c070e07020f070b030136020d020301180b 71
    0x1038040500240c0425844540210105000c41c03140109105110700041c2e980f007102c14010304542c00340b50007101c48202401400003090340101000d03044034000706079002c10070500003a201c02101e2076200c500d55005030b4960008070741c2c0001c81d05101c0c5d402030b0400d01c400700700d100049032524803500442d540e1441c41c001201069a0001c440205e204540e800010080d44810004045410950044a096000045010803209421312641c02014207a4800f0204462081c01800aa001011003c1c50303520115012081c00801d41040c007090030f103003203122800c8921340040070705a4851409480154240b5900141a0600c603044562042c1c1040240d00240c49a603101d24295200300d40c6070140d4829804041074540c00309950300c1c0158003070b030010800340b085001054180700566100e080003d9041c40100002524200c074001e010131404003060020f0900300d4003002c1402e6113580d0303140f040d1000c0b5061506418581c000c6050300c074000036401300650060351120a031015840441d8220300b82c03510070051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 553018947 1250 553017697 553017709
    0x605120312130609051b010e030a0b0601050f0409050403080106081e04021c020907030e07170309061b0304090504030e0306041a06010207030602070f110111190807020d05160602030a0e 81
    0x41140301c3d1070b0108015400e40c0301d007890143c4114110751105800200c41c480c0b580c0000c0280d16040055001d0300c100609a210052015801050305061200004403048421000d00c00c80b00507041102080100d0308060500421400c000d002d070341f0100701746502261400b800e030f10328400c0003654551041101d580f140e081c80440e13005c5891490880e040c0704140d034016510846100c1c462519550002110001e01c15010328207150b503401120b000420f1021014000c00101c00c4440b41c4405071501039640440c1d5051010305807100d443e0001c140408200420303045c02d6500403d0040e0b00070b9944d901d188810504154030380d082901c000340754000d12050000e018000c4007103c1e078071000500688554607543c1d10344400f079038408002103130020340f1002d82104105402501811003074080c41c003000c0d85505204401d81e07610070001801c1f01c4203040501700e01004081d04c11240f02d1135020301803605090040c0740c45641d600040c0044450094081c1d0013081180c4008107a5000d4042c554526440121010078050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 553020197 1250 553018947 553018981
    0x3080f01140d02180906040213061a07050c0a060507020f0907051207020115080109140c090a020304050325020a150f2102040605031605031902030a1508010605120312 73
    0x21300000403500900b54400c0c2003060038840c0300780402519462820348100f01d10300340351740c900c0510745261040034094103060006a03401c81454400c8543e442000341802c5280001d2040c403c1e40c0803008603004200644d014010b004400d00c2540c00ca08042d4030b10042003240758049407000d0000c0c0c0c007405070710701028010b52a41e400071103074000095008906c0c0003071900d04005410200701d507034554545c5010000100c0c000e01d0b0a107903031800b82800000400c00a150800007400301d20300300e600032001c40d06000041c000c0f90410a00054401c404802204803911445100c2d90705a00c40c0c0111440000c044005219a0640c40002e83e00c00c056400501c1040c2c58403540c142c49400215020f03900c0d008590060720080c0050045a203c442d264a0491071940240e19010041c1081003011320a02000711b0000342c031100316403249840561603940d000d000a00800c05007044002142e420800014008019402780060701ca0940300310303114001c60515140d4a00c2509040b0012200310400100194283c0c0140c0e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 553021447 1250 553020197 553020199
    0x503060a03050f0d1103030c1615090b06090702071406180a090905070911040614070606182703031d03040e0601031a010c060c05070506010b0703080f01140d02 70
    0x10094540700e8a030340303140c06042401240640c0c4030740c030100c8090b03400c5200808100c522400447c079600e040004075040340105414034440d01100c0d6502003c20030541c600e14040b0310007180400c40c1a10710700b040e40f40441c040d41c0c401d000d00b41d04004281071502c08610707402600c0c0d219010760b4500c142002032108a901066111080321104000150260340d070103482c000421880c000450410814107202d4102880c07540014a942d16100382c0d40c540c41d10400581d4229600350620382c0c031700c44403017a03640ca40c1d10444c6001032802d85401c201041c58003600c10721540700c40c407080c03040100c10b4409500040c1c8000c854201407040729042a2000041d20a40000da050a4190a2207018408641501d459500150070500042080070204541c07540c2c14400c4071101d09911455001c540e44940000c0c004401019000e0729058a412100c00c1c1c0c14010000c5a0300258010216036066943c0da103100301c1e0750000d00c0d04900065929000c5041d44010b030040505a82d00407203004e280c104401c2c20041c824051170b00803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 553022697 1250 553021447 553021459
    0xa110108090109020402120f060a030309031502160311010f1a040509030c0f07060e0108040201051804020f0a02010f11120a020a020a080c301210090e070f0506040b0a050306 76
    0x800e0058a446c0050201c62030381340040c10395810310314140241448001c001d00d000d40c50a100801c0800e03444240d01007103035040151441154500701240d406842407091030701c90481240303541810103a2144075030341c035010b08200800a04403402000000e44035010403030032000030342200b001038918003a40001e070014010000c4034a814140304043d420010080186401c54000e04001c03c05142c00c48a00ca54880d000d10b0032003414540383c2d001803c540151004694080804040506240c0740c5504031502143d500d84010b03103550200d40001d0180c402d0842001d40d0600384000304c00c01d0168a025603107440d150700c20842d01580d407118814020b4220418640c03c5100300d007450000b02d002280204100c41e11840600f03104440101a48119200112500460300c22030705030400b002462400d503008002022800c07502c603120300ca108c1d001d2802c1d907082108111b140500c0303030300321143c000b8001d81210f451010207610300d03603038a04028860296200e5030744820380400c01c0c3c00c2d0140c407503070080d603001c4c0b0f0007001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 553023947 1250 553022697 553022711
    0xf090f090b01060c120318060b03070b1614010e03090d05030d0204032306060a1a070203030408010507090915090f090b040602031806090c0d020105040e070801050a05030a1101080901 80
    0x40d009501001c3e4003c1c0e01241c000c0b21814240059002040072000c1181401c0c400c12140707800841c20030001c00400380050b03684a401d0940703642d05000210060820800e02e03a1100107034142010206035803101100c5840c0400c5036894281c5040c0260640001c184001e9824820140140400805949402c0310140010042c0c0324500714144041e20285001c0e070804404102c0d003160a010032130034200608569031141041100d6030782c2d200703880c4080c3d030080310741d8580721003190318840c0c058042d000703000750306000208000c04c880105501c164824030305940c882c1091991610010f08888240203c0341c1c180c54100020b01030290160090002c41c2c500450004040803551180c0ca21000e081d00c04407981e64001060000702050202c844003034282100c080d04a900300300e200e26a032800c8001d00103004074408104a819603002c0e0003a2001811054403900700d5180041c070040c03941409004143c89200d15401c0400d103402d00045084a15911800c10380c901001880155140c0d44011700807401076483e012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 553025197 1250 553023947 553023953
    0x303071701080331080c100810032003060a02030604111207050307140a121d070329040c061209240b04020708030604050a0516030902130905150705040f090f09 70
    0xc0782c6001484568040d1031510399146c00c102075800384008620801155400740700e410341400003024122913101511070168021401400c142c81031074000142d05008000070410100310540095100d6042103500300300360f980c1d43c1d000f40c45c01d004800700e545802407800c002880b0315001e82d000b5500b2045074140071710396482d0400388444031b500402c0e0b503000040c6441d032100400c040c076000f003000c8900c100c1c5000baa8140786440c0d241e5a81603c2c0b0000d0812000c008a40703424020346400d88095200300b6502d05c14a2a0500b070400c43d050711440b40c04001800300c070761409040420f03c00d4581c41907200110906c520171009015080c2c0040104114001d40c0d0380244c04c500307a03694802489064428240346480c1d18007081004203d507030080c04452400d0600c0104001c100b5000e200044640490030000307480c180c00d00100300300c205284004c03d0f8880c507080c449804d000c800a0105000306100c0c00c01540c1e80d4912408032114002d03445850b40d1041b0001040c800c9100039044000c81c0303041107030b0010f18819961 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 553026447 1250 553025197 553025287
    0x304050c100c050c0604121e060204030c08120a050304060b120319020606060a090501140d060609080d02010b030613020d17041a0f25120203030717010803 68
    0x51600404181c02c8004541001010322495500400885503541002e2611a2030380d10f0700d4040c0e100520004001c2c0b24025105002e5104645c0c481d0000c0301151125280d140c0101845454040c41041d48038081803d990034201030111a00c4401c03540c2c1e024250b494655801c0c0c0030389070400c00c4036030001401c00703d01608241040940072079000c400e001003004481601c068280500508642d01440c3c7c00c00403912401e40040e00141192005e10304011100700c0018108014080c0034101c1004505100d000220943d1001000040d6030701c42058542c240061803082c1d0807600808480381c0c140d00544002038a40c1b01a944400b0600e00140481014102035501c070b08181c114080e02c2e44401402040902c8500c041c00040b50000c1103550182d0703c1c1c480301042181441c0500211050101e02c1001d9030842c02040480041843d1b6000102d0104140e00c071002175242c3d001102d00790001a80da4000d03442840c036040e00d0a041b1140714000c5d40c5483d4030320640c0c1307280301d8010306000100c61512049200742c2d5044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 553027697 1250 553026447 553026469
    0x2712080903011e0b150405030a230715080138090402071a10240509030d1706032107032a0501050a270507120c08060603060c0f0304050c 60
    0x1040000d00004e190381040340080080c03000d0005a1810300c82480346480016114aa56403c0401c100b030503034400061600c1c88a0030103031941c02d802102c10004811000d03004002d40072441c1e4070b80c0c40c040e80e242c0c4411541d8000d0210005013410821108a04181d0940c1442050f003031507403401480c14456101050503648940701c1110a00411981c1d08152111800c1454028014083c1880020300c2d10420042e05000b4210121141800402c5c100c1511300400403170350140b40103400e0b10001031180c0c02c06000c030180e40c40341c203071480007800004906142c0882c1e0341c125003003d840c007084006000750504105400c440c1e070440520140300b1013550740c0e10900c03074110058040c404002d224692580f4000742943e0024103484103940c01c00b040164007043c01040e1044421441d040315882040724100549003102684c040c910340303250b5001200500032041050350a4540002c1101d01c90b0310380105165642004480301e845800061200390030701201540190f81240c01481200d1103a010400000d1400d085 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 553028947 1250 553027697 553027751
    0xb0f131512140712050303160203040515030901060f0f0b0f0c030c0d020d03090b0c07020a090606050705070f05090105090a02070204110315100f111c271208090301 72
    0x4541c1e00100350040800c50540900b104d00c0e941c80341900680d0300c465a03400301031310465101d480c06205002d010300c200291070060600502c0d4090040c89001d030943c1941c02a50030074459420032001140d09070900c0c00c1002143c8061a406c208140351490320000b0b5000484003100c0e00d01b04104403829903004202402048801ba005007480c3c2138045000780c0303000b0014801d54103040c00c210220b00810301000c0100c0d80062804140b41d0358a40c28400503510344455004400d03a9858254045401c80c0c0c480040c062482c800c00413100c54940b0b900d0514100000c51250390b502803100700041c400c5040c00800305800c58500e14026040440b0b40c0d000905842c000440c0012480000c002c010021100900348858480b003500c11054403070020100034585080c9648079030074071a9a04e82d0850750b0b8410000602c484e0003072213004000ca503038404d00421142d2440c2034607414000003d80174501e01810911101150909130b0180c10200c441d0b52503071510341210b61559815503071840c0c0c0c03a8200082030701840b25089 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 553030197 1250 553028947 553028963
    0x7200337051b13050405030406030c02190506070e010215011a1605060403091d06060901021011070204050106171b1909050907020a050307060b04060b0a030c030b0f131512 75
    0x2030b500b01440b640c0340da01c41c9554011800c0c0414030020a1022048905841c49842e0101d10060b0022042e0f00c0d01d06a06a482c65040540f0b108100f808004180d9601902880ea900007050b4072003401282d460703103414a4240042c1070000104084426855200044010a540d460411400c4035031548207076030a0f201035801c0d420080c01c000400d6401b50860340a092441c400700884140703001c10316202d1000404e201d014000010382c512071070b8002c1002ea40200b6401100b4070001604000681c0c2c42d802c50b10003240114186000031030003d00445640704a1600301401d42000d982c1d408070346454407041d504003080300004001030819144514907121140b0b64580701d040080d40303058184030101c0002042681150050003252000460110885149940040c80845c102c1c501d04d00040080c81c555122102d202d0f4001058030710340385c06421400709440c0c5500d041100d41e50781d030b0600440000315205d035030b13000011403005101070506a01c181031004100c1303490011103032240101c01c4581d4149009132403d003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 553031447 1250 553030197 553030243
    0xa0302100c09080619020c030705010b0f0603060108070c06110406200c030c01120f02121609030b041407170714040c050f030a110720033705 62
    0x1034950056203404400c515014007014502049607841e8140500105522202c10341052a11541e54054540801c0c0a106603541e0f1411880c0840c000c00c1d0240d00940150a0780e00710340024034245058a00c00c1c141130312641c1c016070b110f810864034150803807000c0b5041c0781d40c2d8081c2c030f1001c041c0780f01804c0034080c01d40303070150050301103c05024a1002e1600000031a032064108606a480128501d0608038080c00c007107401c071100c0c02040c5d000c0d120b01510b0108080c40402e08001c00814514460301401d0444507000d08803561400c110350f8203045020140403004500d0100700000c48123100342c2103c1c5428800c1e00d040300e480f41c070030858003410b040040d1800c0d4018074080c844c05500e00d440410700c9508803801c008443d406030004d01903000b01d0f40040003084005c00007982c94480c0e5000300b070060400809003965551549440f450041d8104400460058400800009814000384541080964404d641171402d5000550f261850746800e2115846280380840000107404000a01044082c1d84040d41f00d8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 553032697 1250 553031447 553031473
    0x314130f03020127060f02031c1e11120a020d0903050306150c0703020105090d0c0308120c091509041409060a0e0a0c030602030406021c060302210303060415080a0302 73
    0x40000040024004c00803074a400d01400c0c0d20038292400c6800e0f0f81405800210210003d9056016503030100c107030b01c55440400303008824658031240c0d400b54581405004040c66003502ca003100c01d41a610b6141400c10001c8007608000d4002e02648100f035030802600d006401d00310182603030703100740003280030031004803d00400707113001d01d07039460882c0c4140c0d400360501d020343c80c155130b481c112840040c0c10700400045ca00280d07181d101020381c40b9908441d42d520100e9684c50102d40d2355000c01080c0800402c440081010b43c11144200c40941800400c524140300705828000c84540c029608031798016583c0c001c0241141e1841d2086125100d080060300d0186048540315045d2500e0450480c4c10750808140a400104072848000070303242c0102c1c0042c1c80350b0301c03858000001c2c410914425500250300c02144083e1460350059030659200351020400d004245258200840074030a16600580041c40010003600742603100480003072415104904030350780e941c0381c0ba04061141e5015001a0040b144140b24 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 553033947 1250 553032697 553032707
    0x12050d080603030a02070b0307020304080607050a030f020306102d0e040506090105180a110f0d2f0313120503090705030a1208070e0a060c05010f14040314130f030201 73
    0x4014000d80c0998540030700d5044c000d45942050080340341c10800840807544040c070820640d07003c2c091042c12185903082803180601290011000d03040084e040805100507180903000f03580c018840640042d802c082407080075505400b92080c2051030124100800200d030180340c05425848403d41c80d512440040300e021301081c0d4000601070307801400040d00401c46902d40381558203107512a41810049515145a010040d210381e11a082d40460b001c2800c0060112000082c0704001c049501007043c400151407044250400e8044000306501e0103810544811480c0b004680c003103826009110395034100c0e562211806100c0500d80300040b4080104240c0000c100440b401170102200207203030b08442d55452824410702c54010f0020000e00c9d1010034002400740f0a02113900781c0042400b40320903210031004000900911702658558201407901070900d241d44034458104440300080c0c06603903225241528500070700303454035649900030001c00070b26159401000000d080c003845183c10441c514000181 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 553035197 1250 553033947 553033951
    0x50c1e0304080306060a02031e120a061a1e34021309110a080120031608040503070b04060f06080118020f01050d06031101020f19170412050d08 63
    0x2406400400a01012480c80010389521800c102c1c0c40759503d03008000b040341903029041e420b000e4240c00010424003184114040d21150044048040c2d5640c0d07024040d5090b22007038821a0080200700d00c0385030180d0090401042c5509005001000701082406800c107075030b002c2004003c00c10003494254112041540407003202511882401c0603011441c1c00151040303050110304d18560365580f00341d074200040d04101c0604454001d12001d007071559071101038060302e002e1608202c00301c0410079a1400d20f03002410f5130b0150705e40c440b010304400318843c000e6400b00e102502c00e40f4184418402d140004a01400c8180308074425000481c05000f0010300c1070540d00950811354043c1d05005a081812503205600c86040360103c800c40004808240180c58a1203840070000185040c40008001c1c0301081d100c0c01c0d400c6c8000ea007101c0410000b10700c10362711605102c1500d0394500e5080b4800c40030455140408800050144a442c07a003951500701f950f420310f00c1081141c1a030800141c19458a41040b0225 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 553036447 1250 553035197 553035247
    0x160f03140f0303061306051324031109180f0c0a14010509211902090c03060a0e10180c02120313140f012307090303080f0a0f050c 57
    0x801c060201901d45a10ba00000300503070300910b4910310b001107030301140e0091001170030058034081ca5803e051a900020b810810076119901381609441000321200c00c8026040300e41118050300040c100004104415802400216829060500d500c0c00a40d0902410454007071040080c05026014001c0c0810303240250f1001145580030513080080e82d8100f800c88a0703002044642d819580c1a100325002062408441c0c200a0300c105041d55035800f0301080d43d040402d008031183c49540e84e0340290134040d80710458103140c02200c0744004010110803c1045134010514458134080075071152684030070920807100e65400715443d1410b0217607076901445202c0c4584e64031840e441ca189400581019400d14074400204034000c0c0b141402d0303034541c1c10301884110b1801c00000380402902c00990301c00d01c80100728202242c141d0f800104a215029114031002c0b81d605455084159840400c081c7c100382c4024202c62146445002588586605128051182954884554131412101912002510012861 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 553037697 1250 553036447 553036453
    0x903060f11030718150e090a0c050f070314030709060e03060424020d020408010615020c011b020f0901170c0a030c12030903060216060f021e0c160f0314 67
    0x40341d5400110002c0740c0d44400c1d41e041801c00d0710450600000d582c0010ba2101c5c805c0c04802001c001919405140051010001c83e40104292a03130f403d4041183d0600004c040411020401061481002005861954024100700c089001410380d401c213940d104403810710011789800014040a078001400a6000c3e02c00d5008104e030303140682d200340d45911840d081c1362000444410103660000b01c0e40440310380c3c0794071a00540d1255a2840c00c00c0c060041402041031100b020740e080d503107061000540c40b4003075005035100e1800e07908500380c0001e560700b00314040e41c0081c145c1e00088280d4039120b480d42d00901d40c840f0780000c0401032044581c14100c1540138584210040d010030808108207030968400c0e503145d1540c5440c0501d00b49800d580412055000401d650700105580340e409504c40f0507074201034014003050100480c14036095080303101d8082e06c1d0003140302c1c14045e100c02d100800090030104094000301d03419103420240301001c852446d0300603195054180702c144104050f070300d200c0264200c22401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 553038947 1250 553037697 553037711
    0x230d0207022b080d06090f0209010e03060403080a020a09050612060103050c0a0c080a05160501060e010605090d03030e3c072d0314010f150803040302010e0409120903060f 75
    0x440b071540d81550401428984010950140c1c07560103910007002000725190400048104030300000107034005030402800319070300e0043d02c0c506081c080b42c940d105952517a03840c502c5a03182c0700b8036402500182c040f0410802800c00114840e00c0f04401000384000f10a030701c521034a401000103050300d0001b44204001c070000d0000c0221a5002070a2001881c2e1041c00d041d240d00c0c1800301100c03180500450040303802c1410005078203000041d80088181e032261581007003140c0e00c480080d81c40d0701c1441030242d0082000c090340f0700424840e03403280c903030004414282d8a103a52400c01044528903a003445564480441042d090404070740e243d080e851340b80b8a000f51030b2491a241e1440a00c4448220400c010505002c10344042c10035488810007441e804031421039403400e04242c03940242060034800300054035054107041141c20310b2401c04112801030005601d45030555004599184000c40d800d90055181c0c0001c0c0d00280010500c514500303000c0d0382c2d00e10920301c0d504141c03007914005155a0b81d16803800e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 553040197 1250 553038947 553039009
    0x7051303060c20071d040f05061009050601050a050d020c150c13150e28030c0509060111070506070c150c02180105030a02090915090d090602011b230d020702 69
    0x10303500380c5c80320089948811039840d400c100703420308010301005082c1d005180400c48070343e0898010340240c405501c4d04011035034404c0b005507858880d206804002c110180442500a070058000309126039942045e200c0a60566440b10101802070740d81510701c6401180c0b076002d5110104454005201c00f942902145503400806002e142c0b00e658550300656080c0588024601c81424182e010300c88100c4400b0700c3c96490a00112048060040c10301c5401e409020880702d608c84c0545000a0201c0c0c00640120352800c020400c0c01d6021400c219141c00150000041900141e0a081402d00940d15200450001da02c1003100f180d09403d074040e81e0710380c104014085a100001d80034801030703040e901104d29407521100b2601d40700842e0703000744104110504105601c0320104c2d042e079480c3c0554540d50100c0d034440500b64240c038850b007405000e0500c10412424518854081000400c01262440289030301c00c999056450b802910900b4400f60005010411410300c0e44503801d2290b5403030700051400b81198 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 553041447 1250 553040197 553040219
    0x21806071e020109080d020c090c0c1e0a0c030501050115180b07080f130303080703020c0316031707030603031407020913020102030c150a051e07051303060c2007 71
    0x907078107001d020501c0000c8045900481300d0138094903100d0101c500e02048110700031b6490104e800000e000b0404c0740040794007a920300040c1d5680e01690310151590084d280e15110005049c0c00d4140d40505c02c10040031b01141c2890799113000741d80580c00201e615814009007810700303200301904200700301c1e43c482d510300e031000300031050710940e111200c00c1c590b9002c5a0414201d84e024001c1348981d00040014142010342003000c01c141143e100380c942d400c2e1070390340a6041d405c038002d1032a00c107a160020000c1286803410074040c0c00c8464445d02303003100c0c035a8000c0380c1e960300d01d03904465a03400300e56900c00c01d00906800a00c0c44403a11451140c40380340c08042e9000c0381904401800e42c489820b582200141103a0007802511001c0014004072003482107004101c2c1071000382580d8015001d80703844041100400151b000511200351051429501e4550140c22a01341d800070200c0180f00341c802c40e000c4005000b50180f0703811111550b8950300210808800c0c052448081c115008a562110b1002c0204821103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 553042697 1250 553041447 553041473
    0xb06041e120819090b0414040e0f0316171c15050a06031d1606080c040e0402060f120c21011404091403030c0c0706020c06070f05010b1302180607 64
    0x3102031580480690310f0a41c1d203500180c200041803107001c41c01040c10300001c0f07000b1400303180440f014800100c0464400780c80d5000300300003034000c1d003040001407804070000d5401e005243c0b290704040240f1000c0781174080c190304800509146541c0b105102220076149008209940640b06001610107103000300240d4050140d1040798240360711607507130105500710b1014070300c841010b00c2e0590382a080322014000000255010304c84c003281c041408a007034105968162410749410418403040c9444a40812103e80c100c4900c41031161002c201811078048403d92503405520355000e490b4407161050000c5443c8046404014011045a8010850060a071140040380041a20300103128042401e01c00464807401410a0144c0b00c00818030180c007000e10010600c800b02c0f24183e507420782d100c3c0c0c000c984507207016003890360003041030101c1004207800600c4200b04522500000440707820704030100d201c1d034041041c01c03c5a55404100b035205040050604550b20404441c601e01c0e00d046a40c99803c20414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 553043947 1250 553042697 553042717
    0x403050f16091a030d18091503060b060d140411030303151c08070c03030924030f091a160e0a09110906030c0304020310050603060403030e010b06041e1208 68
    0x30f4032036102102007002d210503208200942541c0e8880d01811020f040880c42a10707624030340c18002800a0358201d2442828642000f60030b00d0081e0500e0340e11944003402c004a43c83c6d510407020031a209914201c0e205900c3c225030844004c4c0c559242a007841c5e140719805805c0f0901030741080003001088800e030350b201c1c0c007116000c444c3d41c1000c0200c6003c036074041001d0f40000b0704005000404005100c40d003050743d02224400e5440030b031415211402c0b485810901182c039511300c29100200d16000303010303801c07544100625110000d202d0380c242e04c941c1d150300d2245011510548219007404044d0740c202c0103050030b03070400b0b080013920001d1407008151906014412071800030f65032510004d2010546017215134410008140d2922400c1c8061512050307441901c00304d02c01c3c426260560f070003a005016007482483d0080282c200350b512500c041e0007620001e01314000d29540c44401d00c0c0780c0c1c0d48800241000e4440b403192006036201810043c0d5040510b90444804c641c1c064103024002894441100d140c0c40c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 553045197 1250 553043947 553043951
    0xc1227040c120e100e01050a050601020a02031216020d030e040f0507020d050c16151e0c0602130803041205010f18020d0c080d030902040c090f050f010203090301020706020403050f1609 81
    0x60320b66242d0405204c00c01050080303080c176136841c42444054016a00540c48900204455202d9200580e40c416030720f0030085d01504008510a0306440c0000906a80040c0c100c8042d040001c59000030800140d1550450204012850791000c81c1810301c510108070204100070001ba00f071250780a0340d1101da914000080010009105609040901c180c0110784c00856008900070303152144100240120131480c1c00041e40861021103d2140b018000180081500e41c0d40130b82c0c240f81c4501c0044c0d40035044142000b40d48940010707089100b00014001020001c0c6041c640c0c0c0034034544a800c0d1560030440800b4542010781c0000b0041d08a068100c0c0b465040f01d00c0c07010740259181003e080c0109601465413402682c255042c521340640201c0d290610844080129440d0301c03005840b100c006000b0b00d40c030321020070b07024402030410100315010a80c05004881c14013086c000001d00366071002c03c0c02c441064002c603042013041020886103000001600190500390a0007804c04903000721885141c804075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 553046447 1250 553045197 553045211
    0x10c110619090203010608060117060103080f031302124603091205030d0c0f02060a020a02010204091a040608030a0f050706060b030a060e0a09080d020c1227040c12 72
    0x1d086580a40001603000c3d000b448859520700715075841d04400d08c01d2100004614002c141d0b604408a09541a60781c004030300c80c2002e00454041003075401c018499952603607034051850143e9034070544c4807030b0078a1440c003c1000058190384000700444440039a8408641c3e034030f0020761440a65203d59179440190b564805103112810100c80709511640006400c05000181000303000c000300041002d0120b81105201707025118604a0b0340390f000a03000d10040c3c0080020a00040103600100036003c80d80c800582030640f82c9412404451100418800c1e241c04a40c0c0160b030b5040600805009109400245041c80000040940b96070342891160b0b00b00f0074000b602000b00110b50b44404050404005183d880340ba155041070010030041c014911120702600c0081e429546601844240390b03407101e001070809000b8682c41c0041d4111100d0403078540500c4200e5a03500d01d494010307012075404164804640c0300402618071044c1c40e042e29076800f460919000c110032a0700150701f1500e14000b500009118 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 553047697 1250 553046447 553046491
    0xd1707060b12070311060a081503100f1a01050f0a080c120f040b1b0405011d09070f03060f030206030c0c101107110909120c0a060c030e010c1106 64
    0x148008201e480d071005440b5003840c0348220004400e01030703d00c55040b040c070701c0501c80d0802886000b40386c5203800043e04100003800c0c15142003010700220700c0107821644c514240c0e0b00b003201521501c25070820825030b200401c0004043e0b580c00c0f00f8250500382043c03440c0842a00c1481200e22030504000c040c49042c2c004100c41192260468494219005491040f4241002c1031344a00c4000c0d1401d9451324040350100e082c6100880c014088402485110ba180c039190500542e07401c1e0b540c0101000301ca5007000c60680e251102401c1c14400c00e03043d910700700c1224402c00d02a085805542040800d1540010103000507110642201d03001082003a0068440c901c11019903d000003ca8004d8500c0d8140402154000c8040d030213004002d108960303410303d20031040e0510000d03c03030842e014500c0da0b001d00e074508108554180140041c0441c5002d40300c04480a884134002e4a40000410002a6980440c0d0219540078807614058041c1c40c94213141c1080a00c00403642d51001501c07610700f64403641c10703030440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 553048947 1250 553047697 553047701
    0x5060703050c0706120b040b101b0204090b180606061b0316140c06551202090f01080a062402010e0d0906080c0903060a0c020c0d170706 60
    0x84120382c0030803284001d440341e1000388420702d00600c40b4071032420708441640d2841e1034090700c9046a8003400c40d00c03031000c1c800170480b0140c0d45080b8240c10500b554a60750050b0f251405001402400740710800c1035420007151040024201420303140d420381018080c040540d550030304079105480e0020100c440540390500311820341c4140c041800001e65501d50000c2080070b4065050b88000100d815100c0b041185070a1003414840d1811008851900c01c20004200141c100c2c0d1354810001202c171080450502c04000c0e000749010400b501d41901c03200c1c1a050362541c1704480740449140c8040542c1059145030105209400305110329050201600026201c1c07405d9a0110005002c0c00300303410074641d0f0f10f82442d044094802d107120015420708401460f080c0c1c00007048025a54140d0303e910b10507113802e43c22210003001030a0703803000c040100959005a0b0781003244a005104244000403030150040c000ba24014800720402d0042c1010a0708001049200c0703801c59000c105511004e80d41c110b02d2800d000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 553050197 1250 553048947 553048957
    0x4030f0e12010509011a0a030201020309040203040f14030d06060f05070201110f010f02090a0f05130f09020d0803070e0f032d0706120c0804021509030a140d12060f0506070305 77
    0x1000b580303400d040041030300e0150002d24602080300400d146820140b8280411400c840c000640540e00c20440c0c0240c5040a900456209000d100180b1048080703a8070312600e18549001e400300c42d400440c014001d5500d9206042c0200101c0c1040b204e000c05000029015008000b40a414045881c00e2049207800c00d02c4802c2c043c052807030007000400400c0401d440250855503003a4040c45c3e11880c0410910212004601510300092042c1180b85483c2860000b40c250311203030300c45040d100d012080058582e02036440e651442042d401d5100e142c4200300800d00ea0b200d400141c8130f10700814011601340c5001c118080340c9080300c544802030100c243d8140703000e841085818000d61080c0782c0c2c005a0b80c0e51203640e08078404544401405040c49258040700e09090585011b90b0107403d2443e44110000154001c18002c040a400d480024441c0d440f0150003503085000b042e04da400000601c8140e66100f032058a80f1004204100046d500785515801e0060990003414040d0400049200515004005035a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 553051447 1250 553050197 553050229
    0x1050d0b0910030b1f03120e100302030f0a09080f0c0a02030f010203100b0301080d0c02190b030711010e030d05040510020f180102010e0c010f050d0920010804030f0e 73
    0x141c503050802026241061900c01500c0300145107010950304160301d0004880c1d045c20442d1511a50300b551114541d1040c400004001d0001d00c000c14061502c406030940800c0680c0c1d2001620b9207081003c1c03000e888c1d002089401498a4460540300144000081d144110518032980fa104e8080d40c0400346840b40001d4041d515204207003090343c1c240c20540040d44540700095803840e145548040e0000980000e01941c2c0c007540085201307042d001d00c6540c0c1c0380c041d180020019105800348500e04075100205410410310030000004101c0040d81140f14440071140305c40007001005038100b501c1e03440c0e00510080300d0403551240c01107000c0c0001001407101485282c04215a070b44440150f4004685c003030105080c25580c4080344450560041c807401c050151404090043e644540340115003001d01c581c41c08007444014000401d541c9100c1c0316551046105100303d101c500c601e00e03880d800c1011000100c03410030046200f000002a8450318441c4100c034182051200000e020000640701c0001c04255 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 553052697 1250 553051447 553051459
    0x2001140705130e0903030a1401031104020708040e070f090b071a04021212030a05100b2a0f010e071a0a030b060912160503030322020d02060a050304140105060a0501050d0b 75
    0x403008007403012000791f008079020403080111181013224108e01035000d00c4080c010310800321a030304090419400400925100701e04503031416031540c1c16482d0680c07042d00c00d0400a501c0c007404528194000c1d0f4414050441c0800003402c1011a550f0002e140e070741200307200207107100707400400c0440d04d074038100c1c0c092a90001d0075503540d10031036496001c09800859442c00e400c0c1c1400c5c0070980141c510020744040c0c030b03181c00980d4548443c803a050680d02e545990f0740240c00100c010f44415448041c00101999520400086810ba0482800510b02a4150040b840d4038a0280c6445c1e5500007a204503080c1c00001e04000c20042d1040700028000e0250495080d0402d240101c140488840070404400000380d500c18642d45586407000c1c1560390104440025600300400150301e030510140f82d41180c2244018156070109186901144c00b5401515000001c1071000c418801044491b40c0032400c1030074044020052032400000003408a581d0b03100e0f15060040018046400c12a25005810000005814 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 553053947 1250 553052697 553052701
    0x9010e120d111210050a050d0323040603020c01290904030c0f060b180c04060e030f0d0e12120f07021207060f0f11061602031201062001140705130e 65
    0x140f21070410454500001407074010b008030307403460107801040c03d5480c083d0005808601c0303903034260b881080c60b8030251446002900341400c1000a40011700c060000c0382d40143c0c855040100c000d00b541d030342031a0721107101400c1416025104002c08100f2a600302220034030b0040e01c80307007030583c0c13468000305010b040c00c00c0c4007030a13070188040354015010384001138076850305420343e12002d0522501e0035501a01301d00000c21041200d03a215110000c01d100005055074003c03c00707890414039141c1c00501d160086260001040103d11303243e1a049825041400501050002e00d00307446001d102d05420340010329400b081031020340d242d541d01900078911041c103c9070695142c110142c1406801c1c0d00d00400186c441c1f030441c030207920803401c0000324842c8078002c200ac1c0d2200d9103caa03607469204649404c40c402402081100e01e0000c92031070080106031600180c0400c0c0c05407000b900259503807a140e19a060070140f124411007008a6a0300058a203485601e600d00b10400e581808420303400343d050642c503001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 553055197 1250 553053947 553053967
    0xc040c1b08040510030203100524070524011a16020616060612150b060f1204020307060305040b180705040603230a0f08130e150909010e120d11 63
    0x200800035540f0031140034090039407094084080c0d200c00c032140c0e52200c1c4088003c20440c00d14080200c0710001150380304101585119581895400119041e1f0300303644517421803c2000640c0300b01d10321115440340c6094603507050401e05404050b4400e40c8106060303000a08a1074640e20485c0c0329203c5500518291f6594052100515003000108060300c165103410030000c0c00011001004e02d216a1161341d0600ea00002c44005005101103032810360082c80800c1600c40d405920340c0280b2040000d000f00d0011414140145450074041d6007041051515060a1201061268510540c000412061b2504a800c81c00e24070342056a00c5c2e01103501315040040100420680c1d1481480c0e01041300d0a001c0d040381120ba8265581d024584040c2000808ac8003900110fa0100e0003000c000c0121207d000e8102d0fa01c11001c0c140718400c4400703040301200f0707054010361850300075000d60b00100c2e260002d000500c2e41400c4151202c42e003040300001410002590090440250089a032031352895020704e46a542d216 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 553056447 1250 553055197 553055213
    0x39030c03070e011d01080a0f1404060507390c09021210030b01061d0d0602070308370f05010801060303390204021306030b0f01110c040c1b 61
    0x168040c4085485854241c02c15445911300520076000b410540c010030049100640314242c02401c9007048540b600180b1300d2204d103074010088000200d9000005070702c4d090501d4012964094071103810003003044540c8181c1949080c6261282038012009204421703851130580400b0501203004080110300c050000351150f040e400342810030a0b040f10665150741d06281d20910080d02d01000f8007070480d240060003110310519078207805000d082080d5070003e0403034001451240785000b04a03070ba56000101e0000301070b0b11807107180d042011102003045050f440058010a41c440c1ca0030500c0c01e01c840701080e840000c0541144509030550702042145507101e0300cd09001c1c1034917010076070209203c0800320404d0101c146c0c0a001c07401c149010342198041c0c0181c0351403503d2000c0c4c020b90340301d42c00780510446100c04440c05402010300b500c0019800d03e0034010b01203a03c5003980c42606116103201e4098035050b010402c2e100000040318001212082c2d20819260078502521607015405001c00d0081005255 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 553057553 1106 553056447 553056451
    0x7050303311d04120e030a02090a0906090f050601060c0c090f020d15051201021204110a030c0315060b03060607061d19061439030c03 59
    0x580840400c2c941040c0420109840d104107000800c1800980191010480d003001c130303140c4c168000080d0321480b10607406400341010500050002003140e024005655021300d080001001a0510000340d078600d03003040f50940714823400400c3c46d84c065040b001c4081e0707010060088003810802e10001034500503140300c942503000e00004181428074011000c030070040712503800302d1914140401c04030045880803080c40717920400c07208921919828280e85e01c590441c42d96001240034402049032401680e0015068000c07519011041051b604600f42c074413600c90a040c008245c6602d604000b502c810b4070002d80c004020854800001c00c0c680000441080a01d072480020500d42007803400e103500034241c000080d401d14041020002903101e0000411a8a00078101e01c0c03500803148500790120000003107400b0032000282d02c07034031083d4144d041030280c241c00c0346d81c6a003400443c44441e5041 = true := by decide +kernel

theorem cover : BRFrame.Cov 552877697 553057553 := by
  have h0 := BRFrame.cov_init 552877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 552877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 552877697 ≤ n) (h2 : n < 553057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
