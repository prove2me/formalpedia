-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3483
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:46.802581+00:00
-- url     : https://prove2.me/submissions/763aeb86-8494-4d09-ae15-f1d747b2f840

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 626258992 ≤ n < 626438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 626260242 1250 626258992 626258999
    0x50c070c140f100906080408160309180209090117010f0c02280f140f011416030e07050d0f0209010f08300703180602060a0b120c01030216061e060603020a09 69
    0x31b00805034803070f00410841d42400380c801602401c681940364100c0c0018031440007401071002001ca100746410007140110700786010803010030300c81001802951050400c04442c0c0c00005801d400c4116699843c2c03005000d0b850b28148040e54038100248600c41c14804a80f03041c60541c4900d640c02c01541d0070241402e40c0b40740944580c0c03041180b408032001c8038020301300b00740120982401185101e0302d1252310045945041c0707401d03d442c080110401c03c00c16040074620540c80c0300001e0400b060303d104070350301c4526000c41e02c0d0040e03450481490094104102e0300000410008803400307402280c0c0c4107410707148818035810004500eaa502d40503c074294604c2e00c2a20400050300020300000c0340310f400c110100362000c0c0881296151035034405001030348810200841d18103103004a48600c441503480f2904141c1c48594182c0700e034180c40745170b03042540c0423a140e11520310800202d0600c0ea0090030400650b009140d00782d8890382c8022480000c18200f40d0006001071107482160504000c80da5a02400c904 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 626261492 1250 626260242 626260247
    0x51903090f03030b1203030c040f050d03090905150901090b090c03070c12111506040e0115030803150a0303090303080f070e090c270a080a15050c070c140f100906 71
    0x7084c3d07410358019040328107408000c0c0d420001180141c811440d1035880350300d80100c185103803074a500200d0141080d0b1021100103608840000c0c19102020b402151a030340e000c1100ca441500c000383e41d50b000115000014a00312140d00c40c1c6610001910980c80c248d8404003046c1044c8001c3c1c4181c000207513080ea15a004c54100303103006070b8039000c0c1d06d4805210640300880d1880c000020b035811410450b900301b80100c5240c144950020451031030000e008180d40740321003650a01e410302c00603100940001c001204100e003004a00c81c2204000c240807003035512401c00521081c600e00040340422440b80104100342050f800c0b0714440c4034503a1340c070410b41c600307441804403002c2c000e05030400366842405404541815040700c206041117500c2200c100143c0401081038a140caa8070101c5a0380040300164042038002c0c4030319002041d94940810583c441c0200d12120388900c90000e400f01500c148045001c0411802d0781d180020111450f8841c40750725020004122101c044042c046208050300708141c60 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 626262742 1250 626261492 626261501
    0x1506010c1203181104050907082802030106150201050f151228020102150c040506070f020301090609031d01050a0f09080604141b010903020d02120d051903090f0303 72
    0x101c80c507000c1821403072900d80f942d46030740d40c0300d08032200346000000840a0410744103c6520a0000c801030641a103444a49511400703c82c0c0f0800e02c01b0840c010302801c0400c038201e08940c46034013030300800003a40d5a104075580c804078024400010350030180401c1d8100000c1002c280916030001c0c2d40c0da0b120001744100205652603405080090180038054485400304416000ea00ca6401000c1980000648002410700c03803070ba9250f0868590410038050ba580c02d0800341da05803001680c14030b560391000d040c18001c260304400001d50540c2400844010007049800006400384a40c880c07528ad206070740803005030003152030401070006a051045a00403882020000c1c3c2e1082c20b0300b070440000391900280f0b414040c1c125030965440a00300340050007101d0800c251102004050120319610f4a0a4002020100c45d48130183c810415599600103664406c0f107861204076250301150740b40c4018850141280d041101112104041042c0a162803402400f400d400b0580c84554098031103102e640680080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 626263992 1250 626262742 626262773
    0x1061106070c0c1701180606050f041e0e03070f1b0501030b2206051206073903090e0708040c06020c0913110d0803100f0311100e0616051506010c 64
    0x19902d40398041804400c46d94401c0b440d83c02420080307401800d280910a00240100459009a1030200f814921039007120078850032a45220001c510f0a1548101c64a5030040090180184850700220020480c241c103207480204035480740f6040f0360340c0c1e4400640456603240009a00503c005c0c01c0241ca4400c00c1c0041c030381c44d800ca040c3c00114291514085203460b4a01008000f0980c815800d00c4145070f0801030400c884009080d0021703105c009410225591469904d1804140615985580825005222075006001c520961451030b1400035070040c43c03490281c60590f0611210034000c84e4191000c11a4180c0e00400707040d45072207468002c0d07074040c0b6208020040d10036480001405d181d075176a14100d020002c3c015400540c80741416130705540901107560040d00402c0b04d81c0030400c0090b10443c40300e10030410890310420350300d055031404c0e2030f10449021050743c41030000031190345803102e40414004c081d004008440c8183e00c1003444d032210900a450141c00310701c07400040b4000078010b18400140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 626265242 1250 626263992 626264039
    0x12061501050d14090105010b2703150f060f011d0f060c07060c03300b0d0c180f150b07030c05120904050f041e170301061106070c0c 58
    0x100b00c0403103008011620b285640c482c0c01c040050a102c5905424040c00e405400042e03942031a1141c026907403a080b503840c0d1b0624204d442d04008007a800d9070184101066401e100d2101c10541c0790909000c0c0e030350f2508030b400034441c4840c42200109548244070001000075480b05543c01d28003440b04000441e4140340f5000c1d0300220410503080409814080c11004020584401c540c1c4000392502618206118950296501c2c01c0d21302000e03941012000c51040c40c00091001803000300c24000b0403001000382c2000b60400000020008014500039401a5841c454541c00c005c0080031040400030f03121801c4441c1030000c035915080c0100003000008201142c07290510f00205210755480034104100317980c4880f001c90012484900c01c0c101409032a52240202c104192186030a503141d85102d01c2040407006e54034890b0840b1800c21010107000e46051000304040c907120b681d12030000b0b02555954021070242c0c006c0201243d8058020484495000d078088505640f043c241800411400350328078001c3d05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 626266492 1250 626265242 626265247
    0x804080109080c0609031c02160b0c03010614030609010302010e011e03061d06130509030f0c0c0a0501090308040e0c0d020a0f02070522020f040308030709030b061206150105 76
    0x518100922031021940d10803203020352030345000d011980c00c0c00c600030200310260b001000b06d030700c900300b940c2c0741d00c24220440c140050b12501c0c003003060f03013982145400080c0110800300034424036900030070245040318290341c2e41c01d500c20300008014503a0b00058803207980040d0140010b03c015801350000e0020800123140812120000f0a0101d070b80c034030f00208071008250783d241c0074000e0303541600c500d4035200003220f0f0204c11401c210011032070280c02e00c1d45002c4400d03a12400f1510222050045848807004408195107401044114a840f800000a00c3e4807800540d1742c001029401030100004403a048011181007902e00f603d00511315500500c4418105810800c140f082c10312803001e010030726000c2e503c66016010b0f002011385066090f0300320b03502c41d42d102c1c4043e420a18402c50308210103000d460700075888411744120201640540e4100038860640031080141c66980854020f0449000e0700d440d102030745450041c40502040071001c0a0726420080000710f409100f180c0c500c03c48001854400d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 626267742 1250 626266492 626266499
    0x4110408101a0621061017090f070806010e010806040c030605150a081617030f180411130e04120503040314220503240a090f0c0302100c02090a090804 66
    0x2501603115840d8412448581099000005003403000d0721750040f0b003581d48001c40d42c0e0070403010b403070f01c0c0a41a405100360400c900003001c450052000542c4005100112404207896842e8251140024050044480d0821000080e4410000f0305140946c1c0c100071307100d585909548410000d03202c0181540100441c1610b0b040442c1c81d81b40900c8000d02c00d10000c1d004020400302464401c1c603441e8800e11242e03141c181107681c1d0032008011241c0022106000c6581e031442400402c2c2142c0f0080c4c0507030b0703000307140c902c04844d501d034a000140341070154010000a02900c8a01025003000245c5001e403164000a0316005c4a0380140300560f0441d000b8200400c00c60000445100c003a4810030b66003001c0c11152200102c0984580c05000c058001103000d4010405141c400c4d407584540455001c00c00303143e20303000c11078181207503111840207604500341c00d900300d0b01424000081c03012480202d01802d072000032409034522a40303804c05056030040000d13a958030341844000240095800c1528104010003000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 626268992 1250 626267742 626267749
    0x10061208180306130614162706050306030d0c0807020f03010228020118050d03410a0510090c122c0d0f03020f041203020c04110408101a 60
    0x3e842207912480303040e0307080341c01d1820b101900c00e0103980418119030030081c8001c4000e100c0a00c860341c0910b140481c4000400d0400c00b01850001c040072500c9410301001050807944000194400d00c001d030111020110111800c680f031030300d141800344c4840003d0040a00501c1c1c141034083c00b010004001604180307401c00d20001460048505d0180702c1d04840709205102e0302170180420a0803032180c000e00115258480759140c00c82c036000e01003016601c0140b02051b640c001d25000c4030001c0d4010303002099680d04400002625118001d0400f03820150005080c440c42d4045c851044000300d950118251500e000f040c040c00c880c411010512000392803000000034244214031413030b00604400301010b2507031400812000e260040a008a07004070f110a2000b54001c00e00c0ca034424440e14005988450505001d1810700407500030940b2814004005001d00d1785c0000c40441c03e01080f0741c10400d0a031801c445840c40e100318481c103280c40c2c01c8102840c45c41c20040d8440101d5201040700d034604a400074000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 626270242 1250 626268992 626269003
    0x151d030d06170c03030412050109050a030e041415040b0627100e061827090c040209030c0d0c030605040f060501091e1d0706050c100612081803 63
    0x103100000e40e039000c2044003981180b40d42a2407203000d0040c0c8019200b560102e5200d11690040d5070200c0030f0f0341c22400070041c09600401150350003500355201030b4503528004112174042c0800c41e100b641000c0ca4103542100c0c0b081458001e101d104c0300942030301c1c0c5000610000d8061504000d9005005111a4900c510b0401140721941c1e802c019070380148040c0e00030002070f091018002c4040000c0016078407495102d900071110b0081015914025915414000442c600d003039802000c0d80400c0c3d048039010002024135514041c00586007510304080109050004900510304003076450740c4440708145a5080410350354070300700d0142c0074001d84251a910341c01d0035580161421245604902c2905080c04032910966002d818408030521a203e00411100118100121a910460307550402d112996050040c001c50a140240c192810340e0f903070f008003828a40041401c10304078010303450240c8000d040c40c4500030a96000600c100e20035240b54591600c203400c1042c40c03030b082d0090680c01100695003040b2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 626271492 1250 626270242 626270257
    0x80d02010b01030f0204030209040305070606050a0b0a0e010f0806010f0909061203080109050417090112050a02030a0605011b06050615040906062604021e0406170c03030403151d03 79
    0x21803000e010200040444070040000740e40c132032040c04240016a85c03044100c0c0c100307805151054a03001f0504140c1300a03c001d5200d5940483c00702ca000900307800c8103029003914543c0380c9030f0010881c1c0301801516003d10040c0020001854038000500660041d40b1038560b442d65840c217580030305e84682c44c400450b074043e00080340c40c0c283d0b030b52030008142d40030400b82d01400d40404140580e0401d81e41d0204c4403100c2c1c000d800070b902004540c001040e4400d040740c0c40d8803e2481d805008900341180c1c41d0000b58403c0d2246000e140c10a4008101c40d4018070600c501008040304030300f0703040541d803294001020060b00c419800303c403080c1c00c045e4210080300a0005050342900006101d80b9011003c1c0503480211014210701d0140c01910a8400d051146c03603901503016519441080061a1141010140d200400c1c1e4405d24210001c42c0000c1c1885809a404c03641e00104c031800007611040541c1ca0060707100c020b114040c8a030600d0903010064002a2505002c0c0000050814003070b038030207042d90000c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 626272742 1250 626271492 626271497
    0x60405071a040e19061a0f07030c0816020306090d170402030c030616030606030c050702010e0f04020c01062c011208090901030510061e030b34080705160b040507080d 73
    0x2ca40d2050b050311882040d0040034040ca0981c00700b40515049506d5018403e0300740c4a549010480d80c0a040c0140f00d522682503000c250903a454595030150842c1c140054410ba010b03124900c0014061400000e02211000441d00c0d11144042244003411403c10010004c0740c05014040d07052403a903d04004e5a4001c0201540e40c1d100280584002012a40144d21007410076040055042c0c000f070300070b003c0344c030010f03028609403018012040224080c4292409044c1e001880002c00d080304a9040d4482010f0301c0301000d05a81070b40d020303480301c06c007440000205a0010000401040704405007249005558800c65205042c40343c594001014a04240d1081d9141c0d0044404500d424106103c1d00c0098480140040745800c40100501640b0781c0d01d010091000e00c1d4040400c0d5100b0180d101155400052110740104942c041043e1241c103d0543ca00404964041e01150303026000707a050f18140d1500e0b800003240c4c2a1180c5031f040c0282e40140c03080d1b465020308030703000c140d10606110400d411000383c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 626273992 1250 626272742 626272771
    0x4020a0c0302010b090103021f230703030f02090a050d03090317041d09060c1b030409200403120c11030d0918020309031e0c0a1a09060405071a040e 65
    0x242000ba0955091952803071192100000510044c0d803580629003068220148420800007420300544107a40003460281030403003100781076400340c880000202815807095800740a00501d403103448c0143e01030540802c2d400783c50301d8000e00990501046889255020380f80145055070380e51150320340760400c00a10048450001024840f000707107203a20309820400e06112900c140703803400d40381d600c401c0003400e8001103202c0040c0c0e1459444584040c001544e4429050b242d031581d171110018001c003900380b414105150081100906101c95000740c4088a41186209503000749000085070b15403d85502104d003040020703040314090b1420002d240c40c2241c251110002c00c2e0810642c00002c1969180b10b40d420313401002048078010300401901c02e051010901d4180c1460308001030741042c010403510528612880c100c8200b0711090300510f40c14010140404185522410050781cac44500840c0c0180c0745510112003080030282d00004407900c440c3d00580f46007426120045200003035425500c80c08015081c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 626275242 1250 626273992 626274017
    0x1b030b011502060a150509190509060c0a0813060e10110702030a060b010207030503210a06050603060904020402160c0e0f0601080f0601090e01080d02010608030301080a08071104020a 80
    0x20019602424044400840d100000303207000356103000042c045001e0980340d582d2110b90f081c4001e4000043c1c580240407070402c1c5029000f1594000c039400c000703100142043e000c075142c59000300300b0900620703803444d52915080c000d40e0190f8000701c010703220091849602c0d41e1480826854821240420308403406410900d1000038a001074800b005c41401030f84804100c03a030300696000960b800181e602c10001b003280f20610300140d08000d803950025115010004200711340e00015800080002c0010f2042071880e101c200003902252054000c45411030420404140c4501e422000c0a9105100800251070000455100700350703c0d040d850100c41044000e08103101901410546a40c085e036410400c1d0300c0b0f8030344840020700322400a0031400341080860082a82070348551000c0c0d02500041480d4446541d40300b11240e90f038045500ca0300015460040c02042c28000030080f0780c100c079001c0000f4030051200b0b890350303452a402500e0803950703c0180c845e1f5594988560000c0e00c8002c0781602d450b240c01c0c10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 626276492 1250 626275242 626275253
    0x309170307020102010e0c180603070e04140601080c01050d020310050a09090c091803140f03040f140d020c01030f0b03010f05040311031903020f1e041a1201060c0206071b03 76
    0x4071084104007e40040e020908143c0325180007440c0303201d0110358000039485038070200b424a0080d40020032030451520030041445035541444c10414050030840d00241c0e0788203407480e200d03404141c1c11070004008100002c021404c5401035500452040d032060a155603071000078044e00d2040d840b1210710354030b501101c400e000032081c05400402d4505d800780000b00940d070907121000548800142803140040317400011010120030349641c0f00ba041950307aaa405c1504090401441040080381c200c43d50b603048002404021030a20064860340c6c0080040006c42801134014000304800388103070317960320440c1d4007c543e4240520341c101c2d0780c2d011001440e81858200103040d055500c2005103258020400c9101a441c4c402d20100e005040b868010384410f2003080003052841168100c0009806134501c101d110000e00d0014070440d060704480094150180e40e4007090350203007552080f6241a00d200400c4260f00916108010030b04c000c1042d03151400c1399507500c820b01070310514901510300c062020f004220 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 626277742 1250 626276492 626276501
    0x509120a020a2a030312060b0306061207090902040e1503241503011103090d0513090911100e01030506030706080c0a051309020304060b0d020d150e030408030706200304030c030917030702010201 85
    0x12154248c1440e61030030768040303511440707841c191140b024503001c0080c00c0c240c410300214000c0e00031850150355881c2d4a0303124036142d01c0241e4541c41d15016080441819141c000744450300500315031140c0c03103a00015801240c00c21002425101840c003c0703c80c20304190380a01c9540e440ca000030940035182e050003000385140c8070b03c0040d00e0062240801000c905448074002c0a0102c030104070010845140303500d006070414080da41c90075007114101e0801c652460308141310007900030082e60100043da40d281c08050b0303900001d11859010803100b07000301d003810150000501c80743c0e045082c540c0c50301298041810310440341c0d42c00400305640c00310500003081854005d100841408449588140314282c00140d8800c2d18100014060013030070390403900400e016005440e50210210a80b5202c940d2040d0041d125408944200d8416181107410324a548010400d0000030213020035243c20f6548075034050381c1c0100406400e60511207043c000042c01a11000950600600c44e000b440c0c4070a0280300281c20b45 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 626278992 1250 626277742 626277749
    0x60305010b06070b040b150409060209090a0204120605150306070206150307031703060f1324030c05061606050c042303030d0f0605040f0509120a020a2a03031206 71
    0x90b1010060302c000329504a0409400503041035120120b80c4501940542514003d58450740050030130001c0000d000403640580094982954044526511054030100328420340c06000040c4d0743c95003210000c03410584c03103c1d500520f401c1c0b0340c4080c1c110050000345094070480d26200103901c04802c0288070000c0c2014603080b1441a0024201141160303249540e111901c10000c4841801100041b410f9a031b0000c080c02d45000031703050313420b404a8840080c014012080c681d00c8095948104402103004046145003200d400c062030f090801d044c0300070803c00741d110464045007580c2d90920203012030942d224041c0034980c00d2103025540d81c949081c46c07540b48800d484d90300811130300b034134412102d0f1004401c0394024090302c907000034180e540c05c400314000c154942006401925208000b60604041d07803009000d000700070110384545045c00001c060324814103040c000182c1221900c2c41c000b0f00b00001080b0000b0b007080389803141c029122140305101e0a10752080d00020405041000a1510703446114040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 626280242 1250 626278992 626278999
    0xc0806071103070f0b0415050c04060e1e01080c040807060c0209150d0b090f03040801060512030310030f14060f0a0c030603080712140309030c010c1d10050f0c01060305010b 76
    0x403e0700d541c030f551107800d88140018058441040001b010040448140401e080402004001c0d604000851268a8001b4000c54020030410384100c6420724244200340b0304801800041803c22405400454403a10b01800d03d4100c030a0030710001c50440e0007884400c006e0110740d6907804829186004000740030001400900d05a400d460540e02c1a07103c682d5a40b0002e9040301d0b07007080c9521070011883c034000c8107444481c00390001040205440301e064002c202204e10840751100c1c41415101c42c90340724403040c0c8403039a0f03004070080108001821003141a4015000307400d0600c901040fa5041428090111166442d002e04c840800c826800140319000d50300a130391900308842800c1d43c0d00c0320f06074456010050402c00308005c0400c0740e248120191940b42e049800c2c034540701d0914540c1c0542da03800a421912095003800d08100c401342c4601c1843c102c1e1203c190641208414070001c5c080442000524002081020040d001c01031814034020310b58403401800002d0801e02c1c604155007120b6884c02110b10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 626281492 1250 626280242 626280247
    0x1120b0a153f0b13080c011a100305010e01060c0213050a2003010b18131107060c03020a0e0d110a0b07021203040302030a14010e151906030201050406050a020a0c0806071103 76
    0x40780440000643c0031044031030590b4182400d04010940c1d00907100410710a60818036070701c02c80e0310a892030001500d015949e000803445075050640079210700740034000203001c2a900400c589481034540907010390018000020a001c01c00342c000c280c605c212800846651140180c0703070045105010411701c40c000d45809810f41d410002051054460300c00c90082061705c01e501c1c0344507a40e4860707041c0c640c0c080c10302d810409660702031004221034100c03203400e07100c26250000440100703000f4000c46425403241d0b41e41c0f07015650000100242c0143c000e00a50744071b1240320035194036448103580e10020344070071900c0381d442da0407901c100964070301c06044881040e0010b200410040e02c1c0090a5130034164007020304502c0600c01c0100c14010702500d01241003d114006400e144041003200c1c4d5400750b41801c6070750003c3e0546000c000c003515401d02c00280001c40800041000501c42e0018294901040c030603941e6402d415151030203425043d411603030164100d1024841c40300d800c496503030000d4003400302450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 626282742 1250 626281492 626281619
    0x30c0102160b0a031107111c110d06021e0c010608160b091903030f030f050f010504020d0b12070e130c05090c041d070801120b0a15 58
    0x1412180da84104a08640c0203c2e4a96965003e600003004a131410311103a9107a04843c2425050030559000040c0140076203590800380000034200001c03d030b5001290f004500403030070240700c214580c800f01601c03450303802e000c01000d102800d030841900c03031801c082c0e031034075000040201400c40f81190700c0400d903540454041c3c4000c149404540048800400c2c41540f2007144501164082c00c0702d00000d0849038015002008154000044045018240c0d40401c85805604000c10403144103035605480d0110341c40c010009480c0c25002080050790855010a2141221010451035218015852810307007080409015840101c90340300d0340601d105200b5042045251101941c20f840c9005407400f0311aa64000fa0164401070101c03002000c0199511150085803061900c03400c500b070301d01200240c600000000c165115107140d41501d9040459401d0750340781c0320142401084a0311800c0b0741c07441c90300e10002c0c0a10384c07416041050060010807000c0b0300a2500c0718581c5412822980c0d402058404460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 626283992 1250 626282742 626282773
    0x201020703090b0705030915040614040b1905091005120703060b0d02070606050a03030c06060512030d021e0a020d0806010305160e18010f030303060905070203070222050403050405030c0102 83
    0x1004407180f0783c40c12555689641011030441c451541610342210215042e030344800501e0005000b01c403234680e51102401c2580108c88028070981c82000410302c410b0000780c08888415501060207411402c2a603d00342000010560b5071001018035808620049480741101308801e010b2540702d1901c0c03804200060418013014698012040460178982d804a0b0134010000b030f551045014000040c402d88400e81e4920b0700404006003c401141d0950078680c0006d00c070308050080002c2811040d005d107080214003940400203420450313400d8610303203981e41503145000c01d102c01018800e140e035000d404010ba02e600f000e804500003170102c90415140c00100008e070418031800840741725052500d074040c0d04d03940b00004c0c2c400503403400f0081300d081d00d040009640407040e4104ca040340d200b034409200780c40d42c42100b0f608031001140c4800140e0020050440140703000c4030a082e400c0e0304d410302598484003441c00d41c0211a01200c00300d004c40d000080900242c5810410410b03450030901c01404400307000d1952 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 626285242 1250 626283992 626284007
    0xc0e0a0e0c03090307050313030614010303020c010c1b060f0906020a02030303060108071101051503190f080304020604170606120a03020709020d09050f03180a031709010314160e010201020703 84
    0x1200e4100c0c1c0407010905a00043c421030300d2064000040b80c0d2600000d20310054903c80078401106c4541c5400320391200c540c0c0700180c0074100c035007580203007e4091801e801510f401440302c2c02100d80819403d10000300d0100c950700003003d081c242d82d4112072145200c40103400b03007803240c00001c20755011f49400307c0140e40c00000c6070341c001000e18200e19180c840d240d0580b01401252081c044c55420002001400c8074134081000e80c2d140c0840464408076102c08180c00842030122000e801c0040d00480400415424002140c0092000c1c200c140fa0950b40d240307010b0f0303008004203650400d810600c04c1c40143c0c0380103130200550443c840041c010602e03182d0307400782d581c0340780744100011940c0114460480e0030160703204002403504401540e011000c0d076200a0b482c0d40c440c001c80001c109403c03258402c28288840c104081d20760021609100c001d01204214254200e0f40e2203a04140c2c54886030380480c06407558040c058085501c8251059035074000150071000e1140790141160710510840010aa00001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 626286492 1250 626285242 626285251
    0x30a110f0607120c060609091407150212090f0607141006050603040204051b0706050f100b0d15380a1209080702060a021c031e1d100c0e0a0e 62
    0x10320031010366070745c80e194014001c150303c041400e41c0382c090400180842014468a40544141551101500c0e806858080360800e4041801680b0102c201060400000b00502d50402c00030844c0caa031003240b1002800d00d6021034400c0300d41200c0c080c054107040008000444400301c0784c000912000d03040901080c4a0b000040019200d5500d51021408000020384411207401c42d040300559a07040131f041510203482c050f1042a1b143d202c0301d00003207aa0300508182400c2d80c15285500341b81000d120030310805401c600c2d04c0440700b4000d68000042160b00c03145031201520200c00c8500c0d04281640c05224080703030107600240c1e43d00040002e54a400d0348200c41c403024620611001030504458103000c50503000c0c0300300081d0400c50014007248031640003d41d01c3c148644c00c0e008544003406840742102034402c41c1850b20801c10001c5203d084800458110240580c4034003030500c7c98000404159180c130710f89415900460799200b6004445a51000001d034581a0517070300c0894042c94406181c245250060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 626287742 1250 626286492 626286497
    0x3050c091314011409011203021f060b130311012d050702100903121b060c02010b0d060f0f2901020a0503030108011401380702030a110f060712 63
    0x214080c411140d41d030146000481e00d6082c42010742e10740c48401e90701550b9880992150103108000104402018007810382c0c564180d003e42003941440342a04041006a009402200d4903018082010030105000d0204425600c07c1d003101a461400c18190a0034a180c500e4100001c0094248869a911946001e50000c00310220104124024201e4042c0030703e0400951200d40c0c00c212500d402d8dc0f0080c1c20f0203030b85c00341181100002c00c8820640d180700d0710410303da80002180f600790010038036961043e64078500302d00001c61034190303402c00560191fa5220741200d209039200d000d400680205d1141227030b0149210410040d038140e00000e07151024501610900310f038124550000d80340d2088c01442203191740a42125202e5840701035540c081c0ca800d10b00c01ca19104240c000080312400e100101d0313100117100803000b800701d26500c601c1c04200444407840141540810140300180c03400c00139034040ba0300442500c1c1d81035158108000e00c180c21034500506c034000500020f0007040c485000610340e0612070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 626288992 1250 626287742 626287759
    0x90513031d030601150210020706020c0727021803030c010e061305100f0b12100c0e1e0319030519090513090f080703021b011107060507060609020408030a0f03050c09 73
    0x224022447c00d2540302d11300f003201e400815400108070040d0060501c1840c05001d0300c000343d407103407c008006054003c0300030002d82c2800ca41e414444d5594000c000c4041fa5210101c030000002010900d140d000c070440440980d5126038466031a03000f802100c0d0060429241400d080c1c860b82c503525540c040100249550540c1d80d101c2035403100090f8406042d00c0b030007030f1111400001c42441a0313100d982200e0218003c50501642d203813068803c27903100010110040c580102030030700d08042000003900d208030942502c42c40081d8100c234031540c1e44005400c0e10079654295910036042e1041042004403003020240050b05e1410b214903034400c0c1c150201441882c3c4009407401c01810320f08a5100c8150001d00504000900003062541c003180040ca40b00040c4600c00701052200c0044801035403250380742400f0b070007200c410b220040c802c10080c15101d0103041c0201703006440703100803412039200350310080c1681c0c8002000c405040e08a00e1800b8101d16034103041116103010076820358144034001401e8402c0309603 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 626290242 1250 626288992 626289029
    0x6040605060c06090f061308212e0501090b03040606090e01020a0311070b3903040308151e1504290a0f0305040201120c08011409040f06090507090513031d030601 71
    0x4182c3c05200040704ea804013440f508001c2b9858a48042c6a050313041015416182e82c15034a80d000500c00840d4070695a83c00550b103010b201c051540c0006d80210b80c003d8403500c000402e411940590707086500c5c0103000694034500c002000c0c0845803880c20340f0302c1442080c407a50000c0f642c0d00c841c0651019580001c0300540400c2010f00d0110344298504c011150044a40705885201c0100a0761160380b0039222600e00d80c0703840d5283d11200d0484000e03980c2c001e0846980c81554144100d8500d0340c0300020b8500d1018022422000c034407a00700340c10440751490074010319002d08941800218146848220040c504141d910009000000080200c0c084c591240c000c141164803c001c80c00c0b000004050800102c2c090073fa0050030800c003807180e4025500c0092489803245072100801c0c0c022540281d000384400025030b500c00260981c01c0d002c0e10329004250000030000810300440748034800303442c40f80ca0062601e00e40941303a80e05003085060801c0140c0655900c0b42c5001600d18150780f0481891850300c940d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 626291492 1250 626290242 626290267
    0x1180c02120408070e01060206090c0402160206030c0a0f0c0305070303090c180e01050915040b040f080c010f15030221070803280302030601050d0506040605060c06090f061308 77
    0x1101800075003184000200043c0124001c10508150307148200842060b03662a00103e0f550130003583d03940303543e4000c07420381251803130700c0d500524044481c024a5840c0e01010340003e200360b002114510b03144c0c5400680310000b56401403100d01e001145080c2880c050711503840080560003075850003024140d9820405090240e444c400e44014900c052007800246108440d29000d094011041c00e150341c2003201145440401144000861240035003201c40750f42c480d03c0b48003108030090415929105da02d5501d0300821900001055071034603480012030071200b15140c50381202c49128bc1400070306407400013800141e030741e408480710b00701e02c04100420882007584128100102680710412500c00020414401e2282a08052803141640c11030640d40507807103402d80583c80112522400604100094811600c031a48560303000328029200081c00d40e16940410402e6020406840700c1d03910280c10041c1c3c6850800487c4040210364010300340d14103149580151006032450010302803000420000300d07d20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 626292742 1250 626291492 626291503
    0x702060f24130c08091207170f071b0f030206030109021b190203060f01060f0f030912030b1c020306150f0405010b0a140a020a1719080604060501020601180c02 70
    0x190024154160030b0940c0001c1e00041c1481009807001c69100c8002512a480c0810b41e4580340ea140c04104d4500300940d500c50504884450b100c4081c100240082c05501010001818020f031180c0f1140300d0404941d902008581429071140c1c104035404641800141c840c6000d490450b0051a00580c07501d01c0752055407030044840141640070b00ca0302e01e2500b5030103450003400d00b10030b009605450300d6885012840c400041d09000341c01c0880e000440d281000c0d0302c81c0d0f040c0400310039186030000d056a181d03698100349034105580315001980f114440340d03440c83c20a0105a03520341125610602c5e90f1540d0100703483e01801403407401c604030140b81c1c0900d151180310381e1381c00f6250300910810442da164410f0003820781046d005030300011106e0860b0306940f007004080b582d500390190010b20070314040fa03480c08050b0f4040112444400e10a01620024100100c05c0c00d00380c04c00c1c2c2d103d008503032810406100481e100b40e40001c2c110f40c840c200410103064000d5001e2110f640c0a80d000c50b44440d848801c2e45001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 626293992 1250 626292742 626292811
    0x71b0f2405401a0702030307121202070b0a0b0f0f10050d06030b070201150806010b030a02120f0403030f0606080a150b1909051002031603020c0d15050702060f 70
    0x5111040101c000069a040d007005886035070400c1500552180d03483c038414043c450000307400d580204101d00c0032812400344802c0d6903026140c8600103213030254400007681c1000070b00f290750000410921107007141300d000321940038805131940c07028207185100242e440d07404910050f005080d075005108074948038a0031918550012182480082d0345c900e8490554203044030301030019480c00038041c101c402e21030704100c01c55440c0c9009000340e0742041c6000c41154006415119400d80c2004810416600d01c8007452294000c100000094601030801500342c5450042c074001071841c115040c0411070b00464130340d40100c1082d50014007800c403d4102401889507030804907401d4800303c1c49000d05544a24025030340981965610151650391041c400242d182401d00b00140e00140b00035400185441c05076a01240030f44129404003030a0004544450f1306418140d500f01c0030b0a200b02c1000c084c03401031a80101151000340100d28000601403c0080003505111080001c80b9140101c141c00500e1815074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 626295242 1250 626293992 626294077
    0x32a0604060504050a090e060f0c1603080702100c051b07081501090b0406140f010315080706033605030c030f0438071b0f2405 56
    0x3100c0d1900c6002c0d0030b5800c6481800e10450104401041904a83c081d171000058540010601600c0d9220780010050004000f0004403205000c0d15101c011042d85030308006000e521001c0d000e00301803a000341890200e54044ca1010b00b03010700301031017070351010403200d0754050350010348001060240d51600340852a40508982d00c501840040741d0743c86032032554102c40ba100000c21482c1041024270080c0d0302c1c1445910810107002d0340f44a020300b03000040f4065818145000140c484101020b10405140f581081d4110790124000b8488030b609803084c61a0511034184124078038214000c43ca089503001c084030b80d0400000ea075403104003c4200107440100c88580d050b01e444903094400b092a60700180325443d044605024018081c41684d205002540600c2c00d180b0100d400ca602e0000c0301c1d61006004441d0140d10442441c94075060100341409081c2d500d101c810130524140c8061701150a1424a040360003041000d41c246640004c1120348035141020f6404044403c1c1c503255240900e40c501d81a070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 626296492 1250 626295242 626295247
    0x4090507050d24061d040f23010b011d0f1302031302180402090106030e030906030a0209030705120607121415040c02031812010e0f030706050c09032a06 67
    0x400100b2040d46030154081c10f181d01c2554007003001e480c00d94003203108281186504076038104000c0d0882040e5507115004080d48000f06049030b8070703500c0078660b9281071300a08a0041419507440303001e0103000c5404c403007440c040c0c03079540311a058880b8000c0400855440780400103075003d40c51b11000f41c180020742c0143d000310340b20300e0000c86c440080d80c440c43e012486080144032701d4a0712014940084d00603600501400040e0f82020f100703800501007401703103100c0361106000f0107940350f03152002548500d21981000d43c80d488180d050603d018025040399204020340d45215a914030005a802d03400201d520300015003400a44a2400511480401e003109032010800c009a4581c11a114203c0c804d080c1d90400c00443c0c00d5008907207074000c904003042119160049070f10545042ca044003d0700c06200c000180c1c0104505c665880e00c88851480c1c005a0400b07d0603105000b1540f040e9940042d00c0c0c80000d04e48402d20300069100c42500c01c006c00d40110002c4217034a0114009403210311040040c0000d036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 626297742 1250 626296492 626296519
    0x1b0c0b060126180615030c01210b030f070807180903120203040204090b01140102150108072d230303030f07050a0e030d050c0f010b06040312050f04030c08100e0304050409050705 78
    0x326085c20201186000748284000b01c007255114a908030200c00c100b105015020101901003c0545020b8081035450320401144d040303001c4051048400810104c4001c00f080c6e4039000c21780796041810306800ea0b40c0b0b4030b009903000c0801d400c0b8480340b20b004112140103a5a64407440058000c0c4810540a013800b411040003040c3c0e85002d2400c0040e03181d09800b11452110700000365400c5400074020210140c020000411820540800132404c12001a2a0400000000440e80404181580b0a0042c14400d1103411942100f0440c40c001002080c0c0107903186203441e0381181161000580084200100002c04424440c07044100800c40308005065841003c14404001e113980c00a2401180a0107801c1d46203840440500c1603003504200031b130039a4105480d6884542008100300006001e1010401c003413011400224001c101444c46041000c0d15141000783e000c0c64441d2840c020704615203001010300c01d80b5400415a0220b80080710041042c0010f0701c1d040e07082085651010f83c00122540c000c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 626298992 1250 626297742 626297761
    0x1030f1b05070614041a0901151e1a040f06020705211e0c01030e0a0f06020a05120103050d14130519031a07030b0603010e07121b0c0b0601261806 64
    0x100d101102d030000e0803506d607e4807a2200d080f1082420b08034006032040b03074100588940c0302480048034172007480503026555500103aa43d2031203074049003498900001028002410f81c0303820403001d000c40c3d1004202d101c5c00c100c086a01140c1e04144c60705114000c80e03845070765403001c10030108030b000c101d101c0f51048a11107512542c2c401d00c102079140881e050114044188000240407120290001040504400d494440c000254081c800210411408102c544201c04080038a18021440b8000410f90000740603001808241c60103102c01e2481002c2044004910900101206540c81200c0c81c50048150440c0381280c1811540b0007405928048101030318141200c2180e403040406403000c0c8106a200f00400c10b06210900a1176480d010803400b28070b00b61301c60040c0e22002c100304800050101000b070108201210301e20110310005424003511410884280d10f21a040384082c01c05084041c80000c1003501d08243c0301345083d41000c200c0025107503039815030800d2090f11045058803064180220320 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 626300242 1250 626298992 626299013
    0x606070f050a2f0402030c0903190201120c0804030e0609150405040c0e09180a0c030b07090501030509030f031b070b010e06090f150d02030d020c01030f1b0507061404 73
    0x141c851403c0750010801c1e460440549111000700e000c0364854221050701040000d400c00380c100c0c410400d05105031281a24100101c0072a00e041e00000360154545100060803420180c8441c102e160506e0440c102c2203411903811900709a250900e80d02c00ea0540006c00c095000305c00c1e5965010620b205141a240e55040007001683c00a850074003c04160b07000655603c05013610241d04030050070700180c0200648101922011040341c1030701c8441c020740d21101c610807065001511203a90a009015805400c0f43c0100e00511080c2800d0000f1700e0144070f8a03840340a009402400924004001146086124019080c2d00c003000c80302c540b5444d4600700101e10510900400403c0741c1d045000c28914540622241c0c41000c00d80c085040541e00c1400301500040700d604405e4010000000140050350103000303246840d0f106070b0050544032203020005040d180302b0004c01074000d2030055021905100203030120800500b41c20a0f0703545000364a810402840d20303940e80c8001c0d6002d98103000821046001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 626301492 1250 626300242 626300263
    0xd02131104060e090f0402061303020a03060209010e030706080a020a02120301030c080609010213090903032c0c060306060d0c0908010612022e0f0c020a030c030201080c0f0d050606070f05 82
    0x2141c1483c1001102401040350017959240c50303811005001030010300c0c0400092a6021004107914001a66540850f28217441500700f1904541c010601e54615680003550f8485050100c0050800c2441e004014102c01e80140200c1d00360348e0001101d854040c0200001c444100060344c00d20b6496949080c02c0320902107d01030500c00d801240c1c045030a013181402543c8000c250141141c5400c1e2074080e202c401051104404c500b81511501307c4c005035000c00300e00303a16503200604c040304a0026005418102084094114850a010300c18040d65807100800d4452100d1001c0000440b002c074044152045c2081d41d00846d0b00c1d40c03c0000105099040400a0890600c2503c0c800b0301c1690200f400b65003c40800d0b00e40c2c0320760408004188400b131142c184d030404080b56080184260740c107038010440403040c0d50000c0d0341d105a692030403c210b580c0141041d41c040c0c02010814105450340050504921905990034010350711540415650b80c1d45070200e4042c1c0d91301200c1071410b4442450401d480e00b8841c0d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 626302742 1250 626301492 626301497
    0x3020d0c0906080f0309060d06080a140111070f06180f05160e07021510320301050c0a110c040e0c01030b0103021801050708040b04080307120203040303080103020d0213110406 77
    0x200000f0703a4480000d48a0220072007034010b5414501a4020302580703401034652450201c0d140e280004900400b4814000124062005542c00310301459041d425180c0c01c04030601c42420400142002c41e40c6039460030441d41d84000d02084256100b0106044010301400241010070a80c0b604000c02400082999125900f000441a40c55488843c0c030504036040350345201603044054440107d0404d201e82ca0b5020140c0d180d034003c4544ca81540c1d15000c4012099050180070380142082d1103040e09051840710601140280020324120070203144501a408065051100d103050a100e094810300460100c2c03007000d441001840f80d20b2400ca0368a60a142c105404a441c2c07519011065110303000311140204100c0d01c5682110810b401124191301c840c0b02600d4071002440301190940382000200020624a0010f6448c1c045504202c04541091060a4150b5001304000c100007604100309a044035011a60383d0180d110394000304243c081c800030a0052546042e407400e00344440c400140090300c4655 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 626303992 1250 626302742 626302751
    0x90711060f06210106210605011505070b0403272405030c1e040605071209030b04140a05061006090608012904090c0903351303020d0c09 60
    0xc944001001e500303642c200d401055000039000001c54805000e0800c40311040000b400640d0f40030300c1100c0300e080000040c004090a604001400344c5030003440d0150410180f0402d011200e1940603203648200e00d0010440344680b4002401d045c0100391013482c0d01a070842e0307807003901c01c1c03920010b015465500401341c000700745070050300d10f10240c400d201303400c424191910341ca141c40d4401d0440f82c2d5003141090400613410070b451541d110150401410091800c2e480e41626038030145088403520164281950400060660130800b140d685058a03421a0300302c0748980c140041c8071100c5040c1502a83d01818034482c000900c040508504000e40c111540b40d51141113440d1207003401c5441d00403e1040304122508403080b212007803540c0d4050031085801002c9585030966941c0d501059841a409880106841190400a0150345840e040c155905a0004420528252540c58a00d0076814221040b0780d00401d0700f0500c81d4803080001d0103180c0013001c2c0409001e175460410320b10500e5000b43c925240c2803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 626305242 1250 626303992 626304001
    0x150e100e130209150a120501020a030501050d050c220203040f03090602010b0109031119180c032a0306050d0b041202072105011b03020a0e092202040b09071106 70
    0x80c0800c0601c601e80c01068504107071124030000c1d03d0400b402000703c0d0310030a150310002c1d070300d50480c0400c1201d034407960025842c0e068486020301221016880640284030144001000039008554241c48060454080707403c0035114401402c6140d00170462229944000203000612207000c42181e10b861203030344c2e24041c280d15214101c0c01d0f20b10403c40940810b202441c280000342a9000d0180c040e02e000c0d000c3c1407083e51203010090040702e15440021081d9444140c5056000b0300d000b070400e80c010b81d00717081c002281c10201e144001603844049003d0070244000000c03041d4402e401120003010002c1c4400040040d0f800c1c80c030303200da00c02e03507003182c010700c507481084a104c1c000703d00c520455147da100000302c1c0c00315a44245841e55240b108441c95580c0d400d0080402100e11014603404540399001a103c01801c01c0190410309000181c6c0c1c42442c9203810062030039140324a41c2841c0240d028003a1058150b440894080d204013890254000102d41c00c000c81141c1c40040c40540c0010f240c00c9480355101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 626306492 1250 626305242 626305261
    0x90209061005091314190e0a0209010b090a09021903060504050c0306101b030c03020d08010806010504020a09080109050a170a0e0d0203030706060305030a0f05040810150e100e 77
    0x740050400c0401c0c810311202c4240d103400c410309050507650100100701e46070301e0300c512041c0c441c0c12079601c9a4035114080302c00300c14125110b2400e00d420350800615160342c0680002c0c3c80f01c1c905100d1450001000210f100c0e041c5c40361031928000301500c44055458460403045035824904002986002a2820200003410300d0309000d100d008084a5520a103141c40c0e8200b0301801c0f00081c1e524405000c0c41810801448101d094601d540900965843d130050b0a5480c000341090440244041080884d000600000c1300120701745e4119601200c00590f5400b05d55020f4070103840550001040394030f0702c2580c0c4103014020590241861044c104031014112010446486010707a1a0400004004c0e036030080f000d00f0030392540c01180d8001170440303003000c006681d00010344140390030440c2c154201040543c40e480d00f003c130031101c210302c90400c64105824180415921600912158121603c4444a54460441d452910007400202d0034501c840d1400031502052000244111100804201c00040c42c1c0c20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 626307742 1250 626306492 626306509
    0x305161428080d0219111c0c08010207140606091f081209010f051315170907080c010905011409180702060103150c1d040f090b04050609010506030a06020a2109020906 73
    0x5600c54405901106541c080c001807c483c016400f50700c544010381c200c089841d000d03007000141752280015944110f589019112484900103440d81030344101c0521046541d03c60460ba480f807840c400c1b04401002013440b44241102a600c826001d014449452085910600007440c911b24281c0b139030180003c1c091400c0b503040c41280002e81c88031400d0f00c818015a0030003940c14600b000d003441c102c140424840c101c0c2084201c00d0751002c10623800031108120108080c070812034840d4003420881e001e41c5c40d14001070315a40a00d500c0d084518070020390200183c1d500558a02c8030032014078070f1605440c0c001806503460301c082c00156455035040001401175403039400380115a024035500e0f004a005007010b030441092038035001079441911603186080c2c20b01c02d4480e82d6150760182029008500741070034440d0404501800c80040c0740d0400c810030803103450020b40300e84055030002c0d00607500c600e910021a17a0100b055014100d0301c1e02c0070068200810783d80c0150112a0086070400350307686070b5604111045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 626308992 1250 626307742 626307793
    0xe0105060a020a060209010e2d120d0c021503130c1e060e0307080303100f05030304050a060c08090a3b0a0f140a05010305161428080d02 60
    0x50f48500005000184190041c00140606041984a0203903010000d400c40f5030901103000c0581c40e0070b0b000000380031268003e0506074030a64038441c80004c1c1c20165a00c45449848243c10f02400d60090011500d03140e5064840104090381103031030f424202c92065041c0c0143c082a540c190a8010110305c0c8e52500107400750980b5000b91308000c09160103400d450f1a20400d402c0e503418000c1b480001500482480154071441c108010341a207203082441c030b900c0080042c1c1046000303a000740401d1140e5203400c042d10303080ea4402d04003000d1500d41464044810310401030346540100310401d0000d00e00584072000c10441845d4a8a801c00083d00c100b00c40c2c035021a50b614040c08103048012038540d807034651214080410500700032a04200d0b02c4140c4400300400c1e00c3e4480c0041d90383c0010000d110040c4080c05141400d400b4001d0307100d2801e4442c0035820a8201814840c6c0e00028001c410800700f40d0380001445c0c0030885100c3c0d11035407000e41c02c1d11000d401c1c01e40c80150088807414040300710f07202e1640554 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 626310242 1250 626308992 626308997
    0x1b01050702040b010c060e0102030a1109030604030825050319231b0f03070f02060405071404090f110102070503010b130e0312040f12030c05070605100b0705070e0105060a 75
    0x3066030503020080030300440c54100e414070040544c01c802040d0540100c000d5840e00c5000540e0360b0901c6480502210a00b10300030751215003c0c020123030b80b0369000c100c10350071541615100300c080c1c41d409800d0541c400c1d0800000e803121000800c1d21040394100011310300c1000703480280f01c00c03000f040e655281907607010460102c032551800101e00d240c83c101d019050308400c40c2401950032100001941c09254840820b15060400220400c594264000f007032040010706c40c4003401039820b0030340e035450740c0d06654010b141210141d000204c04944440e40101a51900700c02c0f64080c8000750700b00f842e40c0880000042c5e005015098000c1007034201400780c03400510303000d4008101e401104025500070807003941010300d180001c000307108031100070190050049000f2644005640c106280000c82e041d402100501410b0414032900f05550700101920f102c10b42052011030a681d9620607202d086200b40c00c60000c10038003003800c5040c000d0010302d480640d406010a00302590b00c52040228034007a12480000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 626311492 1250 626310242 626310247
    0x6091f03060b18040e0c1017070504081002030a1b05070c0510050904052d070206070207140d031218025401060305071e02071406040902070803091b0105 67
    0x80c0e07007016170101880c2d10051080d505940c0032040000c808102d030529800015187d40e10103c080010496681c2c0c003c0400c0c1405882c1529108500781c0310b802174402540310650110010b0814401500055401e14030700b8604c5601c0105550003400030340040c1410307128940c81c0c0360042000d007811840c0404041e0b05031105400c0c441c44ca41008058071004192400c5400625140140c46160380222102442203400700c03046844c20301d50003803814a0050801c001c547c800c01003002015102403030100034242c2600c210040038130900341600e20b0401e0681c1e00024901e0009003511100c00c12407048400b0307108486801498000f0360050110f0316510700012036100d040300141c1d20b810209080e501003070000700030b8118088032500742124120300c243c0c0b0040203e80c90f02c00f001000c03540324100c9000e001c45609260122249680d00950342c08003406090000040110240007a640d4807081d07078000c1c07580703402c15542d40400e0f2504030015002070303c4005603846006522030380c0003034418036200740d90702c10307540d450 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 626312742 1250 626311492 626311537
    0xc010c1119020a1e03021f090b0c03070506091c0c05030412260a0314040c061805040603060b0a05010807120203130203030712080705070503041406091f03060b 70
    0x1e00041440400c0380e000344407480004403200714000c44202c078240c0c101604d40c02c0f85140117020a280305902e48103400d00c0c98401640506400c8501c0c04165021340f58441d03102c1400c05849440c510540340068020f03c42d4004100081500081840d543c1110070b200c400c5125170100251000502c10800505a030001d100c10320114990311042013903903014034030941100a82d2011600104594808542e5000300010060346080c0c05015044404202c240d000200d45001e41f100e1200d98501d000d030300304202075840309900d40c001940c3d4001c09001c0040040200503600c2c5007010007441001040c50150782e108100141c6903009110700c03449a400c50b112598203040340803900c40203500c0200031016000c0700c2c00c00e040150b1070820207801207a11a02d408504c1e484c04007400380c1411401444a0304100080103031600082c000300a6604613004d10300005101150200090018000c103a02283c01c6040e54020340b500c0b09403082011a000e0b031030344013000416110391484c1800e2140c40001502001c1d0400c0c0d55 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 626313992 1250 626312742 626312773
    0x3060f3c200c0a08160308060f030c0f041506120f0509031e0f37350705030a051b2506051306140601022509020304080c010c11 56
    0x2032141c0c0b041d036030030344865004940c1c07a01d0b03850f0001003482904580c007000410030160445106a040700048400120a0301c03075500007a550410300c0041c60160262101450058546130040e2882c40f2000200890b0f00da115000102304a43d501100c50030349042c00300400c600c0d821489114019000000518a00103800c3c2954045041d4801009507048080101e0345030245202c020300a401e1001000c240351144420315800300c80d1801845541c00e9540d446a0441640c10144440f9075801140303210002020b51511000414058450304201c04807144c20880a0b0354804015442001d85003030402007a1a151440a1500b40078100750184030410451030440f4240f81030001850322074500040308a400580e01d400a88105498402d69034160b00d81e000d0402549014580600810324441c0c0c1a501e85000000d60b00d10400a804040114031984a10022030814840010780303a030b14400d664030306042c54100c19039806100d01240d1755103031074100207565102e01c5290112054510040550407000c6500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 626315242 1250 626313992 626313997
    0xc0e0f090f10081903030e010b0616050304090c0f023309030d0c090f08030711120f0312150603041208060f0a09050a0b010804050703060f3c20 63
    0x8808000a0315001079105802c002e088202c403081040c44c0d040218034500a0180c541320480c80d186641406144101903c03000180c0318104100342080c280c901640c1003440c1140300710341114030014102402c06961580048232007040400960071104100755200895004464600300c1c040f600d1950454440d02a03900350f600758202d1038004c107491038914444404011280717000d02030b0022542e4038004002e10041c424800000344200005540f03000843d58903141d040c000c03a02141d2080c2151410030242140412103040b00c0c28094040720781e200200c490700c0c4507000c02156024074030392083d101c4540a05004e800d0b24025503001c00d603d1a100c2c6d0201c004d441140b0003d11050300301101c1c0021107070942d2003000d201c0041008680c0041c060030a010042d003502d851a11280c113010343c171f070140800100b00080b914202c070340207040000ca841003e021003014112466407012649000c001700c20b00b40c5011000b485000004088200c40000410800c00581e510700c100311003450703100301010300c103905003e00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 626316492 1250 626315242 626315251
    0x409050703061e030506010b0414060c07030213090c050a15031d15160201110703031e0509010e010f15030b090a02091e0c090603070c0c05090a0c0e0f090f 68
    0x4001c01e02c41c0e150034003041289110180d003005a04204002c20034020305014682c090706014281500c2c4c0350074a0030041000075003401083c0180e100040c0c086403800c0c00e110700c40145a004024400b540c60088250000d03101e0309005941101710f91000080601d8020700176411295481c1d24000c0c00fa42c402ea040d8002d041d540b0f4141440940704212201c1d0f01c02c180130900c1d1041240c2c011000c40d00308104002280582d180c2e1700400c0d68034240d40b0f07140320440c1c002030300c003035507803514010480003000e1b04c415444540b114964403004d0f06201c10300c11280c41c113411150f440c00422000700300c000440000f0f0320944007250481c100601800300e052000c698007601156204450008a60b5580000e90201d184100203c0e003015100604566150f192140c48540ea030300403038401a12414440e40e0000030386144409014074091000e001c0400d0100005050520000e040060104010f4a44140e01d07201414120044100052480b1304500c140c0c58000c00210340408090800d0074113503141010302c560010041c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 626317742 1250 626316492 626316497
    0xd06020c100203090307030e040e2e0204030309080d081504020f040302150405030d080702030301150216060207052d06070516080d08010801021206091504060b091f020304090507 78
    0x1640720300030354039000441c0140d40c40c0c0d00a40e540c00c0c40b82801031601c540c0c014224030a5040040f00c0aa02c00009001d80c44161030300d01e2039014000c1507100180c40341040c0c3d200c2e55014000308001041c07581012007142110304001c2074442c2078000040c01c030b440c100101d07103481e40380d5030f0b0a0121405090aa01420002070208a501c0c0f0300f5441b07800248480210a560403e80c0c40c00140038040c50800b4064548031020b2405c10100e14100341001940701d01050180c21240340050b044000010b20070010b03c070807031000e2440542d13029140c1c9002900c640340d500a040c020000c20000c141c0700610b080caa4400b0200441d640d588600c0f154003040703600e030300070842501d15128030a800040b0110381100000281440402891850041d005c00340c0504030590040d51640d00c103000f0540c241c940007490382d80c4514201c0c2c000c2c5550b0758080310f40c076400c01d040500d160005d15026000c62540c5404c0c0040c180f40c60f04a0300303820302540c02c0d5143c04004482440d04801038009000030007139020310f500219007040d40da0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 626318992 1250 626317742 626317753
    0x1218060b0406120b060a21020904020d080d090627020f042408060f090613031404080303100b07020109090902060405060703031b020318061b1509011a0d06020c 70
    0x41c0103540ba101024407068130075140e16010b011180c03503e0100d01c0004d040c3c1c20081c0d0090003d0200040e0084079050300a80100040c0001904540e00c4110140d01c055210404903203402c20355400c40000c18050004880d4640f40c000302d041c040d10448800c1d1040440840000b480c01526800d11030f5031111130600c00c0c0c00c0b03522020250400052800c1488440d0440040c0307400035498528010b14003e00640f90380800400b01040c48443e11000c01d0b07256100140c402d00c178010740e04a19007190600051504d1a428040100e80424882d801000031409615084016100c89840d00350809042c072500038024085520108100400b6000d17400c004000c60004110300c0c20135a4410101d09668000b41c411000255218107031495038621041030004101c145c401103042070a205140440c0c6001c54095502c0b480d400700b500701524444030700407622034415405039042d07185402d031124208a0241c42405065081040c05014180164806481400e008200ca010000c1c580c844000941c0030f0b80507541940100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 626320242 1250 626318992 626318999
    0x506040e0c21120c070902040f05090711060c22121e02030316021009140d0f0804060305010608090105041a0a1808040513020915090619020d1218060b0406 68
    0x180f0004100c0e00e04002c245968131034003014542800d24a800480c3c51900c10303c0144940b4032a40801820b840c015203851900e901c0b90038007940c10199142c034a0040344501420058007000081c044c00f00900c00d00c5000c40304400800303126410981500601544604000b84200896075048000002da03614400000346103116402290540d403101c15080004081410400c0031420807840280400c42540f920229681c00c04c011007041c0c41e1303c00309088c802c2503206038803024012074041082450740d0005000d0b964650b183ea000d4041c00d0240b01d02d101181e50100010301c00081070188a100fa07500100d01c098540c2a071591900c9402e002c0c00c03512940c2e03590b180c000300c00440d04004040c028007a002c072035140c911381810009039103200c40b02015058018014082c9903150f40f2030288580d20014045600c0d41002c40100d0074501649003040b801042441d000c4030415008944400032560075950f002190610045000503221000e64545110410000e08008258594030030100050001d00c0455a03030358 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 626321492 1250 626320242 626320309
    0x7120807020a18050f06061603080a0f052403030a0804032d0809100903020c130e0a06060302040b060903060601120f021b07120201050403080c120d0203040201030506040e0c 76
    0xf101000a43c03039130340b424410400030b40e403d10f95014104540103407500c8885101000c4071070f0001402018003125002242041404e0340010b000c010100c0300400103480c050751641002482310b003403e001444d81180c41c6810303003404001c554000c0090307211104141c81c2e95804440d1002c920124034081e41e500808034034117000707040c15140020403540c0ea601050809d48074090400b0200c2e05820009460000100f0001e5004515031010040c1121103203202507403107e8100c0035010070200b081ca80e0143c40108020080f1030303130042c1c0507613009070f404010a26100041c04070394820010a6a81580310000141701c035880382c1100046120a0800452907024845c0c03660b00341c2c0c20140d00354a47c005032001c04900080d0030410a03008002910032801c0313440803900040d080740310350301024004810004c1e401840510410404c00301b14018420313696140420240740000390001d0790304a00007420500450054030b0a80540c41d2105a11000f500140300c10340100300b040a0500e00c22a0804003103d942c000240c0f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 626322742 1250 626321492 626321519
    0x30f03090b031321090b22030b070e0d080702040c020a050102031e060604062003130906051908060105011214070503010501090e070e01030b1309111207120807020a 72
    0x154240300c1e00301000060314018503104019010807030400514083c03004251703441104002101c0351940016901c07604a080c03680724851510380d00303002014800c00041005104120180724009a81d5803c00303062612040020050b2000c6015200c02021700840b00540f0701a881140c801d400c41c0100c92071410181d40355420381e041280d001058003003020b00d00c000481960ba43e0b0f13502203421203500b40340030300b0060003400e01c00340c008104448a90b40c940e1b0140301c4030704000300c0e0f0a200035040e02001040c0e4a040002c0907220714012180601c10213418051145072840500080d29164006401141c1c02d1000445031400641800f403003c0f5124045864818022001c050284e040b5560300c40d605c0d0b040034009030a4184550011600051003070070007202640c000082015906c0910313011230b40800045c00503109210044401200c00e190040034400c001a85010051034103003515180b0150800180554a410941c800e10a40b0b100201e440c20000741480d00500702d842c4028054410341e52624510726406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 626323992 1250 626322742 626322751
    0xd020c220b151908060306010e1810020a1b03390804090e0303040f0209040f15050a0606090f1202030715020105041e02130c0201020d0216020a090510030f03090b03 72
    0x2414001c2602c03143c01c1500b052819090030081405e00b40003081d52900305200d408609134485c0d001c03c0f1142e070809075807036402e4407600c12225110441078445000390702108103500420f2104202d16080843c1c035800e03c103240d8164480b40e00c550942c0c01e55102c1c1e40030303174200140512081008000c1240c800b00004a00d00d01401042c0c1d01c0b5800c1c00c1e1404100d480708105020a80e01c14410800081c0c181840c6404441e8156851092074a440c94156208400c0300c1f002000080c45003050108405264001841500c1d45031050040a565850583d222505400ba00e001008188400ccc8001e842001340074107030510103011142800d96615101c000c904240d1031040050b5142e5041c8011720880050b400200352042c02d0300c9842c000c09900154407200d042807500007603901c1d03042c0b000b6440d00032b506a5110000ea500c0030f541d16003d00306000c0f09581c0c0703900104c0c4200c200c0c0d00c020542003054850310b03114824040120103da811a1176044002001d00e03c21800c00c0054440400c08000550140d8001c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 626325242 1250 626323992 626324029
    0x6040608010e07050c030a0e010c020409240606020c1509090405030406030b0f0117060a0314160f050907050711031006090b0d03050d020c011803020d020d020c220b 72
    0x650421107082401c0502910300f0040203814015001c0c0090084121072501000c0e00b0128014500140142c5840c2c04801002c1e52107031402c1c601009001503940f44100d40b00818640e000300d03c1c44014800c0460301c8a008010040c5e1200d5503a0009050a200391a111000000d000b1300748111480041d81c40c4c602150708580540000c0b07010014a070300f40c000d6030840e007001c03925600b1100b0305000082c40140900c0034203001078140030125030551110071211026581045044000407089041103035074070205840d08000442d0454002400c0307041002e40c2007030f9140103040c00344e82c0e2a415800c680307540129500b51141000401c401301c4071355040080c41c1d440140c004000ca81742d854104100c6c00c80c0ca90680c40d90040074958511400039a002044800d15030f642ea40050b229401e07191903600408010340c0c2c8881182c1c0c460294014190000707000580303010543c0c2118402c214110040f615031502210f101e4005415103185801c011200d4144852170405420010381d8024000002c1c09090040036401013 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 626326492 1250 626325242 626325257
    0x1170403020c03060a0204120201030f1805031b06010f0e070203120702010507092403050a0b061b011d030f0a050f031302010306060e150a050c150f010e06010c11040605060406 77
    0x80d9803c060005030341c403009103035085007030030f1800d002d0071500b00440e007000b41010781d5105402000012a032006414101661101e01d100d0410300d41070f55a58048203032400000c090300c0d0034401d082000900d5a0503039132001715030428640b90640c0004140d901502010035408144000340200c2a841e40341d501c0b5a020754004601c9091054000d0403160441d040501c4603041d03078400180f642400a004448040149800500d44e07580340c01400c024400d85118a40c0b02100044881a00d8640c01c000c10003508948000c001020010000f0b04a600203042c9207501ca402c14404000c05035070040103016841d486040c81450a80c0c025000162a4030895014100c503054018090565070302d440390304e0140c0400d0400c0c140100c80c0100140310304400c401b803c600c114001550812140c030810503170b0116140d42e802c450b40c06400c203000034000d80b8202c1d4000c00d60404030b0000510403410010007802044180c440d40e4000751079440e0206415404c0d1a01500680c603080300184503182e0200802c01000c4075a81c0702c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 626327742 1250 626326492 626326513
    0xe030703180608040b150f0d06020d0b04020406140d15082505240904022b05070f050702030a170d060909120516150e06060306070e010e0117040302 65
    0x700c1007600800c0820001c0c03010000054509003d440c1c0044a00c0e00c68290700025400080b1468200121203400c048101d00d24000c10080e034000e0460314003000001e018404074a01030000b20b0042e03228800000d5000b60f110b02e4076004140042c03d2140c1440c4010070346015000b07682010b941c07076500a4125a105090710002c10105880e0b8240800c41c81164201c142c0c40c000001d00048c198101c0383c40c00c0c044003562301220250110072924804c0d00a0f2096441d41528a0030328511407820303e204007201036480514200d9000c03803060b1845104151184003241444920440d056007243c0b004a81500c6001751030400f04050b000a14203000d45494030360303078800c1000000c806640031a03014044250900c95040009071040443d45031918140c0f62094544514a407440ac17880c01c030400141c480820381070321341ea007082180c0281c000226450300301d500d00d8030743c58141a0b48100407982800007844611460b000d541c81125032490f94541454400c40c02500c1c0d146201c40400180d60031409a400301c1c041c2d5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 626328992 1250 626327742 626327777
    0x70b0a0f092303041a0702030d110a1e0203100209120f0c0919020f04030c051905060a0c060f150e160e04270c090603150209040e030703 60
    0x1004a0140c0d9034240400070107603480c590306581c0c1a0003603141814907100000044820401d41c3d00a160a1501404041038241c142c0c01541c000740041e4041d01400c0c44100c1a00d0050780304c0c200c0300200d003004041c541d101d610b6080e0070841a00c485042ea0301e90001080160760100010034280b80c603c0310050782e900d0328004210454129020f140090b03082150350b2420108046600ca0b9000016608080c0c1903550840e41e80014450401400703c0c50300c00b0a205e201101a036000e4010389100d04031206450b13869204200c03c90088480349104042140d4050129040201c090480e00c50f16041082d40003000d5550705e03041d1540d41c0a11468250313a100d044220300741043c0c12100134580441c1d404214103061a002c50340e50103020031001488a150b0041c1140d49031540415480ea0000c079036410020b17003024088a40307042e0fa1400323954201c803545000c6a0101076100f00c200f203e5000d005000104039000d049000383d0001110958001e941d58042d00c11400b05100030302020b4460380e04d103807420b002000c80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 626330242 1250 626328992 626329001
    0x30a090e090712020d03020a0b04030216060816030b010e030d0302120a060b070b0702150f070f02030c10090606030807080c01240e15060a0509030c030a020108010308030c090303070b0a 81
    0x7041066204500820031100c0d40d58904551a405407480700d0111494202a4a00494a8001002c0440401c03c01c020705501141a07221596941c1d9507107512580e030201107880446c00e6900a001c40c1e4000c000341c00d094001d030b06c0480c1058041c14558092a185800241440003a6504901103600043c251400d0409201c01c26445805007004004d06821300382d070800300340140440201111401404105110300811804c2c00c03184a44641d807405142080325048414025a403d0002c039070101c05003240c403170000c0b09a40307040d0354440040107a403040b401c3c0c13034010740310360702040e19001ea4606000c4046018040204681d038016480035646601d040303050341c211801c481003214104031140407806040c0b11424818110b48075031464001e44d868500034010016000352402d83d01c0300700018007032096900032000e003003145001ca0a58001c80150820b040e10340d8030909000b80003c0c0e2000043c80001c0810015680024003009030324200703105040460b18581c00301740300365859242c040800005a44a015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 626331492 1250 626330242 626330251
    0x10140c100605040204080607050711031c030e01052e050a0603230118050601210b010905010908060f0903071712010909170a020a0602070f0308130c060302070311030a090e 75
    0x1011442e02d07140c61b0b00c458407202c000c0c0c4004100b2034005414000d001001d500340301001801001d41d088000c4c0c04181d40d8010603c400c01402007824a40210110a01889500d00c2030085005c40d4003020b854401c56408402d034030f207600011010020780851503481d81c3c1940400f80c1103d890000d110b901080801e03511a03046c440901c1e9000500c4014018281684004441881900804204c1e511307100016a41030001d020540d4480d080c81c06034941003140c9130010000c400003070701c440c40500c2d25100119040c0906006040c00d075804500402c058065680d42190b1204000c000d40f4245081941c4800300000090458404800d001c282103012840c40645140181b00e0b00800f040081010342d941c401e03801c0000c1409400c070b040400c4d001c0c4824000e01106540c241e22020440d5600007a25040f0803041746450103134000390380d4100141c2d03082001c4124808454000030020100c0d8580381c400c034040d5002074400c5041140e0615020000c0c01c1c04c0028061100b002d4450f504d459007040101080140d0040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 626332742 1250 626331492 626331499
    0x612020127050114121e090c150a090b04030c03051204061b03200109060c0507020d060b030705100807080c1e220b04140103061410140c100605 63
    0xc0d501480c0000080d146080b41c07000c2c00c00042c3c0d03e2114114a8440c02140300d03210740c0e07603440d804200780c0a102140d0300c0c014a64011a494003170300c803000c03900d0b5240c0444e01c03a680c100c80c1a01041080c038500708064070b21710b03c0500d0700b40c0c0f226480342c901040d640c000d548100c5103030300000014410410b0521490140d4408443d526050a1400400034090883c0f01034680240300d800d025601450304c40c0078019450740310342d44180020511200c102c1d00a00303d04005481c42c920f4011900e01140c0304500321030510307400a0884506001940340e0380d0040420392140c6070305100310400020705464480d81ca440316022900d402800c1d1402c001301030000c120042c01d00e50041b82c104180658058640c542d103854408490100d51a00e40d41e50030114250045110040b41111034a800500007022031300410580c0d01071043d40b15928032000042d000c4d034a160203200f4030580c081551200c0b50030210100c8501e020149016800a07005201c120101e9100c0400204180c0100321514003030061801383c030300103004c2079 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 626333992 1250 626332742 626332787
    0x2100905030c0118031e05040312020f0f070306060e0106081602030c011505090601020a05060c090609060d02041a040e1603091203050618090d180308030f070306080d0c1401060906120201 82
    0x21b01c0d0051051046000050850b4110300002c2080c0d4420490007800e0052442107941c0c501d1000c983d10740c3c1e0f5074113201c00c41d806400c001010403426050101c880c100d41c00d5465018540e12005814944001a00321200441c402030114503411a401d000d121a03c3c0070106452403d00e00f801c0901ca405200200b0301410765204001600009000080b020b9000c81b607504150780f01d0b0101c2d030004249104240302c4a40c801000305100d40c115000d070780148202c580d424040080e03e04182000c40e054081c0d0f00c2122100302c5004002003984500036001e151510440c5000240340d5110768605c0382680b000c4181c4000030b030380c0314104070b05401c0000c01107011441814145c1c5071450039440300d641c0d0343c1c2740217503007030422415904009007a8000708150014640c020100d88e01da00d0304c540d0300801f0740e00c22a000c80c006810901c0014002c9000700b0561403000c081d41d86c0f04900e2480e41c41e01c50601c4100e08418240d03640e91000010244110711414024103822640b00d09200c0d4503000040151504001c0700141c660034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 626335242 1250 626333992 626334047
    0xf01030b1003050907050a082415060f04171c030207110d030903020307080312070f0210270302060402100203030907060c0317190c0206010602100905030c011803 71
    0x7801d410314801c0040e8640410660b549600c40c500703040d5607600036908440d21040204556101103072400140c0350624000b08200510780101c90240c100b0b840a0701c1c0290003012038501414200014207084607a85403551a180e40d0308000c020549035403200d8440340c0c100e81c2c0d07003214100e10012903034103240a52405500b020941d03150f0300762210f001c0100b5440740d190f0701169810075000d60f404c440210380060682d0406c80d80c0e0400315849a01c0034a18108610001c1d001401c101d00030070038071248903c0d66008207942d183d1400410014002c02a20125403060107008180c4c0c00003070740421102070310940c0600898201841444085005c020080c01590410302c1001101000090004102d07051880c016080800c2418240c9407018441102da0794a143d42d400c011036080e104802d040700503c4004104000d03050013030201d844000a015100040c1c000c10300f4605406129000360f480903008400fa079180020349456982160756480e8030030b419110040c0084103040e0021245401d01c0d120b8111102180d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 626336492 1250 626335242 626335249
    0x2060a080a151805091b0607050c0306040b090d170c09040e1b0301060b030c1e07150516030c090603020912010903020d081302060a0c0809090405061f0506090424030605060f01030b 79
    0x1400032440d000300c00110307903081404400c104480301170ac8003405603207241c10903040c04100c000d0100c41d1241300e031040e0344559414501c101c0510941600f0f59001c080d15480f116100b1003658850500d580c3e00640b103605c12288150203000c0094404076020303c0c00d041142003800d141c2074642c0d5500c240c0721400284100118034229008854003402031802e654620100803041295900644002912039043c0004214802039242e00c09030155030180251220607080e614128140c0310b0110b07001d030018554030020412036002c1c1d0068400d22500a0803400e215400005030707421a4180e0800303400685c0800402242207412016030f6810401c10404460820002d4009c642c00f8404d0202001c200710b40c42d0242c400340400141928100f480c003c0c08030a907414107041055a41b101650180c0342d10700d401d80300035021110070806034210342c0040d00075420301d40f1050821000301211001c1c001c901e6502d2000b1240e82034406000c1c000b85110b05000581810906c0a200d41e4484450290341858a80100c2592554 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 626337742 1250 626336492 626336533
    0x504080a0b04020102030708040e0a05010806090c0f0303092e0513060804060f0c0815010201060e010e0709032a0f120f14100905150402060a080a15180509 68
    0x7600551507445a440381d2004070318600c01c1c40ca0281406001003800308401da110040c41d4043c842c83e0100f4049644c850701d90030b0711041c1c01d6820708200d41c0072440404003801c00e071042000f01c6d0401001c2d02e09025281c400b1414445c0300703480c180c0000c009000304650204400148220504062030300ba0b0400030130040000141181d40140c80c1031000c64070015082280c4e80c0c020741d2102007140c0040c44200606940030304802d000380c3d4210f9042030303649496801540f051203004104c603c2c031012202ea03a407811044001c0d6000c090861010418482e10100c0132806a02d4600c850440020000b404030100c21440034403502d60340c0001110015105007007110743e0f907800c2c016042542000404a6121603460a08900245000c0421103406002200004019250300c0441c1c11400b4005070b46440030aa076400301c5104040b2002940244184185140244201706642e40540300d1000014070304081150420ba00d42c05501c00005140030a140010004582c003620b6007018001c0c0007800b0003420b0114200c1c400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 626338992 1250 626337742 626337763
    0x6150e01050f090a18140f090312040f020a06090f0e010b040b0d0914010b090f16080916030b04120207060813030c1a100b0a050901110c280501050408 66
    0x210102d0038031066038400707800780c009105107004804040e4901034950f0160510751b041194819104e4001014030f40540d00580c400c0014902541c07034000802c00ba4810007401920a440302040f00c458800140c40d0088040c010300442c0c0c84221030a4503000d41c2c2d4004015980000c810707034118078010440380401c031040d01c050b41c0c0000e141c0c40c2c640e00003e00000082402c11009441810b903041030001001040d440740000359400c1c1d0710b503403c69031810440d00110314141c0c0d1520783d8038200c500d019400c512504a0340e40003010030003034910000360041251420340c0990020b4880d11410400c0c441084250808558884000d00161141929041001d460810300030252004410000800e00405105010780c803078441e4801800188000003c49802070f1140031500884060400c1501160900c46031003920003100e420b5498614005140b001100c000f6000014450f00307203d0801c40141582d603500c401014410154910403040d510607040800c5540c1d103510180c140034041000748030071180440c1c91000f030b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 626340242 1250 626338992 626339017
    0x60703090b0f0705280207270507050c01290108040b04020f121905161404090213020c0d0813030c0b071e030f0546020a0306150e0105 59
    0x496807110829601c0b4071030212007813100e004900c060b1040280d044249171007103c441d030032a51710075125004030310391041e018800410400200e4012507c604180c200340d500440c00e141c06428814072103061801c0d00d5030b03147e400803c074050410400380d40d41d4241548642ca502440c1c81600c0e400c06444801b026280500060300036000409410b00315100d0f07480c100c039050040320031500c08203407404000f4072882d07030707050201c82c2405900700f05251420b102400e04141d480d402ca41030201c0c00c400c401c00c1300500d8280030480c0c00a0500701c200d07000000300d00c064a00500d501000d07150311440300e000100201c000034560a050b4100d9812400420750080107115002c3d8410050078031038a03090030030307508492164014200c188402801c40c1d00d82d50b15402804d15400001024020350703d030503500032040749002c04001c201c0e103044540001d0200c60611100780703604911816000d001c00e03200d620016644980b4030640403d8440804000040c0aa081c1c141d03a0000c174604000840e543c00002009071195003c030070344 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 626341492 1250 626340242 626340271
    0x5010b03060d082709061008160309080d02030406050c0f0f070c090c091707140f0f060f04170312131704030c080d0e10050c010213030c08060703090b 66
    0x20050040200e40b90400c013440c410034940300c0c9000c00741503154070281040c028080c0c0b501042c03040c00c10f0159082c82000076200d04140741d90701250100700d80000074812040540b629001008680d10070024074402cac20140026039a480c2c507040c41010350300098000b802268040245403a4841901d043d0f4100b91020180c1d81e41e124801d05004812081d03603004010101d00d85450190080c0d004082c050031a0594802c5030b08060680f0482a1512890300c1600c1d600c5a80c83c0c281c4605142c000d04641e042e000c0100740c80402c0a070f840c04105981c000e00300d41900e00ca40010144002d40042140110b580c401c800114a0640007040d0b0349009900908000c01c1003080440403000c11042c84440c05680c5c2001300410340356550703410845a110b0f0240310740106402240c00071081d144c07140c1ca564000101c060001d40b03000444010480b16640819101d909655090151007126a08100884000c602030351905510505000d181d13400d01e400600b146041c140744c00d5a0740000f4440c0003515902c092408607840c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 626342742 1250 626341492 626341519
    0x3050705010c060213080106030b0a0c2109120207141f050c0a2901060f02060105010815060d0c170f06060315030a06090512090303071203020705030c0303150405010b0306 75
    0x140a40500410603000f1301c5002d502246c80d900c1544500100c038000d40050703803141c8941c9182d00441e211008080000f50b0503400314000700381c022070b000070441d03001c040008004865803603401d800070450001100580000400300044030310804d81d850203003401c403100311190142401f01c40d80300c10803400b04c005218012a1202e0110b2083c0000101d81340c00407549500801442c8101894402d03035240c08402100600c00400d9003481080b0b011742c0848160000c0072182d091000544801d00c00a10701c0a52031018a4240702a882d90406001203554503100030441c0c2950280140a05070081d8441c40e20b0f804031010002d40145500d4500d400440564401d42d803921040b24001c04544070646180e018030034408080100702032075110884003400b48013a10803a031040510b0701c5251082c070350059416070040c00340c03c000c507101c0114074000002c1401d0040c501910341c1d60b01e41c2560044145260181c1020080028100c2002848080745208880402c0b0960603c0102d0001c1d01001e01484d01070300c51106403e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 626343992 1250 626342742 626342753
    0xa120c180608010623070212031312020325060e0418030507061401080a0204051e0103030503070809070b0d09052503060f11090d0f06060b0309010b0a03050705010c 72
    0x51003840805018500c9281c541801074010752081c840d070000120686080c0c1c0d20f03a080c03400d403201743c0b400c1020039601d0080c00e42c082084031400702203054242d0008010100981e0844864071005289111000d600c040d071030300400d82400210440c0043c407103101c03c0d65000001e07401ea0003105846c0c450801c490310191240100c1e0043c00ca007001e43c05040c00a00d04082496003010150031403d1007444240400c00b00c0d180041c1c1c000d0000c2c0f1900510f036014410351001480c00e9000300c1d40c4034152207016155280300d010714003c0c1ca40b003a88190003040c000410701ca98075501c0401154031980c060b00800c3e00e2440c068403984c041c4110a170f00f00085a88410141c108030060024040c1c02001c1c0c03045c0744190004801210780142c4a02c012941c6510b400e22500e1418080d004041d207940034142d001b420640b0900070701880d080d0f0100b0848a903040304240c0c00001e50184541c0e40501f404000b00c0e030700c80c6408800340b421520a0282c82d4803840e1801c07420070000310006000401d4520a103031001a00d101441c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 626345242 1250 626343992 626344007
    0x1050a050f041502190306170c06040603110d1a01080901060302010507020622031110140409021c050f1b0913110706112d0301091d06180607050a120c 66
    0x400b11401704c110404100c8607850f4000209940d9642d089804a00e801c41103185d031103800c402d090741c22150520080160500a0b44644080c151141c5800e00e80342d40c2d40d500c84c0c112010b000104000134480c0c03561042c1964041e00f49540914004000c00c500c90664001a00c1402407110003882840d0010b82d03007041c0e0704c2c43d80170340c0c107a51151801000601d890b442c040c240d8410005c04240610141607090302c8403445501c0070501011032060540c0b610b820081c0b00f10196000d2070070020600344140540a0482c01031044170700c5800110602000341c1070211000700c0d4030110342c440c03160072b6006001504044d9500c17110b421301c008a248000400c40b8070120107118601600d80d002c9c140900c0d1600035501c410320701000307109500c0d02200c002da0001c4844a0044082601c10030034040c1c900c18001400700d60119480020184604154040724007a503909040c41c04130103c41d586860b030300b152a00b40c04040f080040c69001801d6003003141c10501200d1001f0000d9807103602e10a000340d240c0c1100002540244403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 626346492 1250 626345242 626345257
    0x3060604080604030e030f07261f0203040b0601140306040c110f0f0c03071d1306050c13090507050a0e060c160e0c1204080d06050307150201050a050f041502 69
    0x1a2040c1d482d00c2d00b40500720345c1d000011603000b8040c00351174072011400440d01c10159544051800c0154041c104a00c8040038000c0724216144268001c00703000024800001194110300440541d80e407420f80f805040300203000c0d09032418408951200300c8011900c4007540d42c07025094600140001c0c0108040381d40e89000e14183c030036030040384001c840d06100440c1c4034217100c1501003154042c040810a140d552403481c8210700c0510a4490308003074003441042151740002c540c00c074605072403045481e0f5a040342c00c181e420640e4000c001403210028a0300b03110000041c021484d0030805c074685900098268030030700b0005000c1102d251001c4e5059982c0030103484110902c0c0007250304895070901500c05071805805050700007101c2c03d000030038130b55020084505641903860964886c0c0c0362030340c0b040c40c250000150300039aa41c449001042701d85040103800000e040d40d0a1103550803130010006421904090261a100c504101c200001d55a10881c00b9820680c4643e400000c03031075820b407950003030041d0354 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 626347742 1250 626346492 626346509
    0x110d05010b040e0a110306160c1406070c022d04111c0b0a08030415030f0f1104050f120a0b2701060501141e0a0c0615030c080d0507020603060604 64
    0x140401150f400140541024032901c0b000162095070010582d44e8242200c440344010000d9410300401d62180740b10100b028490000d10022041280400d424280d0440b0303c4800240402c20100a41c50455107540c184454445d020341d1100001c00e088022a040001c40390166842c4c040c40b0041640d01402c440821501100c0c601d0a0a0030b00140700151030f01c1807040c3c1c07140e0f0b10890003180c0060040101c90032208182c500c010036030303031181d0168094000c52078440c41c456078406542c50300341458001c40403d00d50583c0069522404c1408020040355108512800742803105080e82d80e01a0000f43d11240d00d0300400040d149503541201004109050700e980d00d442c80550b600c0382c01c0ca450540045094074400d881d0403078030790310b01c2d0019446806084d815590441c102807503036840c039402a0090001802d030385015001c1c2c210588a0303000740c8680c03035940082410746640402c05d0012981d8800b01400244000d0030940e0031000009049000b113031f03c0a07220b810004003040e07040d03585408880c024034884 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 626348992 1250 626347742 626347751
    0x1b03050111030a0b06250c15080a06090b0325030212030306040c030e1c09050312030f010f0e07030b01180806090c0616030e0a033c110d05010b04 64
    0x304290001d40041c0c480c400c0c510308226600000e8500f200560f07110b07040501c001d54980d00444180341c0005181902607c12211801021031720340b00002290b40e4070f5400d81c44510280c00c01c0d10203c030440740140d1184000ca45001c110450550b0089075940b4025008084618004450001581d0903c01c4d0350000b50f0200800b0102c040c001d40c04009940724803c00c85040103950308103402902952409000c00d000c075040400e40903038001d20701408040800b031514012030314680f00e0000c6840c080d101011000315690101c20006c0d52401121420b000d03000c84540c107001d1034503000301c04840c41000340107403050540b101c65a6105910880113940c91500040340c2c60030076566180c00c01d440d1001551140028015000e810580c3c0c1440b80403a05116030141e0011a801c14a4030300700c541d003013240c488586c0406844c070008045446000031021803072080c0403d40011045c1001e0980a54100b5169840340e0310510031840807c003000902c404900003503944042105061819600400a1046265019140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 626350242 1250 626348992 626349011
    0x2109010302030a1515020105010503150c0c0c090a0608120c030714190303020304020102011d120a021606020706020607080103030912050a020a06052205030c0d02060415050a030f02090d1b030501 85
    0x5c4d20b034104500c48640013084240d8a6005254071091003e0f400d04800c2c8480021400d0b404440c8010a29044040152002400504001910f00405450140e561900da40381417210f450f051150400d140452800c841c50401000503164a07801280c1025054140050250340741d80780500428100340e0307030300090348001c800380d02c2d0207802501f068800781d005629203220104500c20400440408242950090081c9040709114410341c0c0e00107451007003107000303500d0780b900407410300c034450409040d01e45c01400c0c51744d090440081c9441c400406030ba04200c0c102c00108003003908060281e058460a41070412002d400d41451442e04005100c02500840781d08000903030300764064068450624490342c0c0003418030801c0d03003207840e164031030050640c141c001603480c0d034040c907040c911054071620162200e0300b0155100952002c142100d114580030810004a5811150b0b1500c02c1c076105030a081400c6040c4518107011500c2140081401089981103000c41c481580000c900d4a004541c014002d0014002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 626351492 1250 626350242 626350259
    0xc120306090f0209030a02060c010b060705012313030e010c02030d0f030615050324060d05010501020d11150a1104170c0109080d14070b040605092109010302030a15 72
    0x40600c90500c440b8074160110403080014000c803110040700030020410302c0ca05d90200030640d80803040c1d1400e01d42d170b28090342c240e82d2160340251199500031400003030001d4440c0c4003810f03280748032255404904a000c003000391b4108204186889107406280c170441480100c1c005075008a50300c4000f81d4103100b043d141200280c0d200c03030344e491a0211a41c050022070342d07901c560803929038800840d001060f000c0c0001890710000e400c1440e02c4101d81c60070038850b501c0080c0801d07680d500145560341610740307800040c0500d58041205240b1900c1034079107403111001c400002611025108008078000c1d446002144c0c44d00300540055094040c6810300c1c80d40c90356242d503440c2410201004490150251401e41a420b600039529103003182d0317954002d8420300d440349200b1602e40404007481c4032501c074144681c0000c90444c2c0c0d001031103280302d901c00050314144010503a181402480d207051841c1800c11003100880c0148003625a14502800c1c05a101d48500c200c0c200604030060b1081c81400d07102400182410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 626352742 1250 626351492 626351501
    0x403080313020a1a0c0d025506150308030a090303090c0906030c080102040311060a02030c01060311040e07060e10030902041103010f170601030807060b0312041406070f0b070c1203 79
    0x4080085508886429005076168008001450080704200c00d8a00055021150320143d0300aa081c860f5154400740c0230040103450708018024800e001a075241c010400c0520a881d0304502200d0450909451955031b12501e10000701546025601c3d0901078080601a070028085030354071100f44400c1e5a19101d04a0040102d44404e03030307411086941c0001c0701c05043c4219070960b07400171026424500c40034244001c0361300000401046110821080030035600a100300310141d48607030300003125542000c08010a031100400d0240d2150018503080103129000070508082c0c450541e11040c0a5500f0703035003500204030790311029401c142404480b880c006004d000441c1a18480d10444c26615100c00e50f91031030f00c10822000900c0c0d800700c0c1c0180007146401000d444094440e00c008104903e964001c81d0030419001440b1030300460119062001e02c1c0c80c40106070310031505403401410700401d6202c001035224401c4004e04004038580100740410b10400c0c000d4529a0018030860b01185032100080091 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 626353992 1250 626352742 626352757
    0xd020a23030912100b04050f070c0203072c011e30050f0d08010623220503010c03020c060f06041103011e060813060c021c03020909010b0403080313020a1a 68
    0x4134a1718003c111185014030419000300e114600110980e682c1d40020b6030400d0910101f0b903810f10407900002207246001c4401080c0c072880d035400c10003070740c00024880c680c507206030840d000101c85403400311041a140e801c070100b191101d001041c1d40342c0d0303030342c0ba41e03584541178082d506055030122200a00740b103400554140c4c513001440850780c0c80d94100d401210300c0b040038082c04c0700142c1e000c032102c103c2c0b00d004501485808a140d50003890b182c04101c1d440c445c1d1601482452400c0a1060100143c2c5002c1c82141751040c11f80c1425803900d40703000c85403a1500c8000b0508907141345210085071094031907902040c41400c4040c4015929616211500600c2c140ba001042c2c44921181c0c0100e042407080c030707140b1702481000300d154012001690380c84005d032091b201d2600851144080102c1d8080004041c50600340c0d5a480050b80c41a9417001c0c816080016000298500d000b00001c00000d1820b00c00c0303941c0704168000c0950000000c0c070014200400a83c8024851640c03168145102d008000091801 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 626355242 1250 626353992 626354023
    0x30c1214161515030f0614071806021c030e01180f14010c05031302010234140a03120311040e06031c0f2007030c080d020a23030912 58
    0xa200c2152900c605441d10781d40018801e10060404000042c401c0d40503d14143c807036a00483c2441f0400200015100d0481d0014001414407608201c5450f500020340041d1010740302411503003451140f1401c8030100c14280784200340c0d030b0321980304041c2170a50029001103000813480640b1651401c08070389410f540c000c00c1d40e000712800301181e00048144a1030f4510203490700c070a810340d6121036091a10320b500d0310041c0e055005070090409817000c0c601c450809800d00c518140c2082c421a000010000e601e0340002c00403010111010f1601e507260360307002d0122540110103c0c04c2c0b40480008401030040200540039018001c2000b01c4c2491500c00c425101318020750407a4410010725421041c0100252a4000442c40c2c044101401520860110042401520710046c0141340041c00c00c0c641a144c3e03009807040002801c050115650034000540d00003513500c01444168010b458030585502d68405048591080301e200601c0041d00b0700588044030001415075140d0302c80104003a8035082400b4403001d6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 626356492 1250 626355242 626355263
    0x6010803120a09050a030305150d080a4d010f02211b0904020714010b1009060e010c14030c0703021f051602040e1c1704030c121416 58
    0xe82c032145203d29203036507820030000d001d10310154800354020302c009041e1903002800ca54407844161100c01011501c5442080010340d54503c00500410706640c0c0c0001d41407801d0754056007000e05031034542081e180c1c1c09140d80c403138a0301070310310811100a295a100c0309103942087d00c0889413000300d078081d05d904404a4a14041c0c823040b00c07203884204234116401590314606ca00e0380044100118040c084030700000c0c0006103400840d446854030408015010301d030740c4c0e440300c0c50344440f400c0021024011521320f06000c51230904144001d4000304041a071a03041003101070418040c041c8503062202108040c1007034030b503a070289204494464102e80030a901816240400d411682d81074048a005650795690301410300f00e041540203004c83e8445002d0381c2c0039480d000300c0c0c10440b03814441c1401e1030030740c00032016500c0c2e0300e228003030042100d860100b07060060810400c40420340001811071401c1c1d0010180441d550f0000094501c1011041300e5000000702007007107040b5044e01610b9500950058031580b1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 626357742 1250 626356492 626356501
    0x601031109090607030b060d091b05091306020304080405150318060907090b0f090f01081227031f0204030c081b01121404080a0f0c050723030601080312 67
    0xe0010010b850070340e000e41c014000107440500ca44c0c0b090703403a0f5400820075403908541c4800041698030000007510341e200681c0c1c101801e00c100c580300c940200710641e0240e09900d005852003818900003c4068000d40c0c00100003801c1003079036000c480103050001d084014500412030b103851183c2044501c075840c0c2c540c000a51043c0c0000180f240c0c810189040102007950030b04a00502a00044000035002100c0b0390030002c80e0303600e0102c0b4078440c2c1d0468500100d103603d0155224948680c03c0b40c0070460074410071030324022603610100c0c0c0a00c4440c140c40042d8440e03010340802d10705010315050345c60500e200301d4454200c0c0c055800802c1128040c03c034078011280c41d02d075040d48400540144100355007a40a00f8403079940181b031101e28501c074087c000900070500f1681300c2c80c452400c4a00f204c11107000155081c40d150400903c0c0c100d255546000101040a0750341c2c0c80da100005d0140c0d040f25024040172110014469000b032080b000050140d8050b9651481d0321a944d0300804d0180d6514400d980014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 626358992 1250 626357742 626357749
    0x280609021c030318021c0614070305040323071716060b1801140111030408031c110918132a05060a080c0d02190801050a050f060f1b0a030206010311 65
    0x4c101c1d00750000e080514244515907500c180360851082102e2007078075004451504000000580d2041085441c0840c861419141c01001c02a40031802016100060003600e0200d040c2420380c0c90055109208030307062a00c2843e1000e942c0699103100781c6a4016000c40400c1060a4002c010042d005483c6c2d4000c99680c110074503001902400303404c0e00d01100d071a04852540c0f0690600509035007500c2940d181a444103901410340d40809a00740c4580485051003d161106100e0035a40c2c0b03a80c1b030710316030400c041c103000510080c078071000c602044030318403011440c050b4040c0c80c4042000c2d0b000c260484031202581013042100300d0700c50700b4130070358a0420000a85043c003501308c4004008907a47c0316540d83e1298031108913604a0140b00007d61303420720107070203000584040c200d00030030130b40c4615400e50700d4031007003002c81d211903007003540180c0c070740321800309192a510709450020403840e03078058032a00c2c0e9400f01c08081603018850b0400d8407400920200741034011810b141628007a038160050b450034481407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 626360242 1250 626358992 626359031
    0x40f1b08030f03060406050a030b06090a0b0d030e0301060801020403030305160c02010215040f0b0106020f0f0c0a05040f09020a0e0103060606080c0301121403040f05030c03280609021c0303 83
    0x100d800c240c004204820003100640025039009400810000d88261140081002c17180f00e500704587c407944150500c041460700000c0b41c0e600c03a901c0c00050280c2c0003a8008200036418030a0700a080c0726813846140d1582e9420740001c0d0180904000843d12103545e070400034041d00060794110f204810b00384a040d900c40c80b0741c0e440801650181c0082807940101800241c52020040003a5005040e8030703001c40000700410310542c024031050b8007c180c9003001100442c10102a004030b4003107684074040e60381954840850301c004403842243d0024692810701d10341e0000d080344013402580409144404950700c0704491455050b04d00400c4d04000c5103489040550741c0342e0050743d100d454170106000400041d1250b2030381551042c880c48641c1a02e005d15400d5601e90380094000c0710350210700d080140014142003008110640007140200101c00e01001c4007406891405188018202e44030210014003121b6000804090f40c05462061800c1194042c0d04076284201011400241060041c09000410661 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 626361492 1250 626360242 626360249
    0xe09010614030a0e0d1205060f0a0b071401050c1209150a0507120e0309241902070f1217030f060418020402280c03050301090f02040b03040f1b 63
    0x11500c064006407080c0701101d03000144001110742d02c0d0005601d50841c240248440c040d940d480e04a0340020394545002682d20003044180103505080d0903900c0307941d464a08508592030003540a66440343e600303040941040800300c209184d820103050058001c10900103001040b88070740f00246a49030740004540703d400a103000c204101070600410707001d18082d40b044d0380000050508c0c80c40407620001c500113032101c0c922480d445800c0401d48641c1d03400d014410754944100c0400c043c50f86210b07a11445510b00030b07540035100c07481a15401e041840e00800003a03014000000040c403c05030360300703c031102d0b258407000704450b89100e240345003400e44e1014054034000c15648110300d03180d07076070801400010140490300700b500c018625014009601e039840100410710140000305100f0400300c100300400c030801c00290b0b040000040140001c29441070a9a06441c44000007064075014145941c0107401540c10001004000000707000812400c900d02c1070115120b040081c2c2051468000c080f0075495610 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 626362742 1250 626361492 626361497
    0x3070b0a02060c1305030a06090b0c04050d06180b01081c0e01050d1109040f05040507060512042915040b01020d0f030b0a030f050f0c1c08160605160e090106 69
    0xb01040c02c01040ca4041c0c40510980a82c0d6070030256036200091501003c01000e0300d03540d6403004801c0500c139031001c04a600190803010189018070b01b0003c07034100001480054030a81c0d0b503011020042c400d130075a0118403074101c50f200c011540c55010054a403000f1461000183d11901c140c0b0300e01d03a01400c00d0480c0480140c4409042c0f119144148026100854001700c0d0542c0c20854a101507135135200b26030000c0f01705000040d641c41c161400c60b00d80405c0c2d4001c84140070050011000c8001320746a4164070a40c003040807a698074285600818205070000540200e900c94001c000c41500c1c0000c2c03040010314121000c2c40f80d0b11005005a851300410056100051122004410070501036002280d241c00c001c2c0c01e8030f08469032601e641780c1084001004840c5a00f000c20a90607001040020500f4007500700e075034101000454410303281c0142c56800080840002050280c2d0031242002e14044041e0010f105001d1894032504480142880009690100d00104030076985405c01040c680d06840064 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 626363992 1250 626362742 626362753
    0x3080a03020a03061a09011106060a1a04050603070e0346020d0501020306012604021216090b01260c03040f1b090609050603060a050a061a030603070b0a02 68
    0x1080100e0295220141c00010315446140004815a42d00500c2480c1e00160340f680d07450720b4800c00010300c00183c5140e070007500d900a0702407201c15540c0203a0001243c900042c039502c48144441031803070a0080d6070005500c004040100600c503a0400c808048600088080c1ca80781060420300c1c1c0700d2940c02050030004179002c800d2040200e101c00c2c03403030008254110f10207111015654002520070800c107001b2600359402005105403540c01ca0328482e118031010007001e0040202420b035102c0b03c2c4d00104041e00c9507848440101c1c502c1c00511002601c540880c414185541c1c80e000c0c01d0b8040c101312481e15001503c0712050701294612441554003000401082500580301c0f061800070a40000c0c000380d071419250200200000c140c0c44082180b46072920150035150714140b0100212000795000ea002c00e402c0000304503c3d658080303443c0c1d80c40310312a034001541c0d4407058100001040290004c0f0030f01d40210920000c2c804040300a50b100c0e0800301c04403003009803908444482030040b04490303c09680003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 626365242 1250 626363992 626364007
    0x3061d090a03051e0712110703150c140c01060302010809030a0c0609081207120f1802040c0504081006050405090f0a0b040503401d060a0e090d02160308 67
    0x20310014004054001d60210038102502c50300a001c1d40008030446604900c8882e22403866000b00803800446247d00c040c142152031170700d580c0070b000c650a55000b2450b6603401445038040c0034a41d90550010300386a401e071039004482c0d5440c000d2074680000d03404a01d08000040d2030b07100010444000112507918980d070180c0d555100000b0341001c1030111046030040c4010414207030502d1001c1c0c4074401c2ca40c0c0340c0c0c1e0301e8404006114102c0701112643e001490401511b5415911155407084c0702e250305541c000750f12400386008540ea400b4542101620707010710100b103890352141c0e41080040d00d20498040105441e00c3c4030140e62000e001ca001c04144e0807000e898000704075140e60251340180a002900c1c03400103d42d20302480508501810401d0324210200c444060406290744000da044080070904610709180c00d034080041d1000070700300000403050008041c0d44440c005d080c01080300618100c1103044c540304060b00d503501016400b00511494030503905158880034100300700e80d040020549480300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 626366492 1250 626365242 626365247
    0x5180705060a2304030203010c440621010c08180d050711060d0c0e120c0d0203190503091302040e0402060706090c080c04060f0f1401021c03061d090a03 67
    0x2440a50b51070203c043c840080561030a02400501c1d02080e40e5414248200c4800c2511012200e0b0100503000c3c04215201c104130002010100b401c0440c1062661350b49c0d54100280e070baa40e080b1160440089102e180300c1c0d0702401504201c1d0040003a441c0e0a18564a9001a4000354001e26400e01d10b54400743c09a035805018000601c401d0b80a41588545803107035a001c200181d205070050560700341d564100412255100b403945106034002c4a41c1c8030a00c03107407003540d03503200c3c4940e04561013004100000021590200a0380700c0382c2070315403501c5014100504082e0303140e8206118081c0107050792458444214100d01c21a030030b0715003030844503d26465980034401103403c198012107920b0741d07800586020580348000305000303000003002410180c4009080c0020360704141e0203604041c5c41c000d4140048502003411b0400e446c0109032080d6070341e2105004030b02d070011690903500540003020700c4000850781500004196680e405600c1041c2b02503100440c04420206d0300b05216030010015940040e2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 626367742 1250 626366492 626366537
    0x3011d090a020d051216020103050108010e0d1b0f050303060108090a080a0c0f0f05010501031b0302031906021e03012c04150b040c05070203100e121c05180705060a 72
    0x5003c4c40885900e50002c0440128560060260f0161600c0040c00c071411503070301d40942809002c540707009100c900424084542d442c0750031a0940c0078800c0000b80305820030001c5a129000d950400c00140e035201c01824102d484c0da00984126000501200c0000c4d200900010950500c80c0e0090409142c02d8220108490840040904865000c0d0601102001c00c2000b004500b07014010350002a240d49145019400d1800050180903a52542c02080015a502080c4121824a03045256000c040c081c58400006e10079896141d41e00040c2d854898030690380c050186060741c00d00c1001e40800740c00c002c80700c2c4c42c2e81104512102900070241c000341c001340600038042c6402c00001130224007020010f00203410350790365000100c0000d0000c80c00c05d0641c034080000395080b4240700c030100b124500c80c00a80da00d5440064103010b07205000102420403da24018036803104004240030002d60900100001510100c40c0381600903101c1c20b60041550325001c81101c611500e030b605e4942110421711415007004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 626368992 1250 626367742 626367769
    0x80609030c10050c160302100f050c2a01020a110c01050f0a030b0a0e010603090215070b0c211003020916051602060403050d0804050d02070b070201110f0d0503011d090a02 75
    0x40c070905c0440800f60072031007031450301c0c0d00c00c0c0c001d8070000c2c080d4240c24007152048100305c0f104508050621500d004640100d8440ca00d81c11110100c5034001454020407030170032810301c01290320004004002a500c20740c0c120020f1b41820a0301c0c4401c000310011241405170104040610300c0804c5046034042c0658080d0600c14800b41000786c1d1507a03503550340c00b41460245d2044020a440e0390083c2c003186404410080520381c40f541f1079052003515240c0302c000c204000c1c1020001e1400050390b0070300e4425284030004080503113a40302c901c0e140c10036075820240760b20702c003c81c080c100c02000700304001c0080300500d4010400340c2d6554200f459610560151503684a8142d81107a1304200200100341c042c0300c0340c00d041c096038035030540904007841c0c40c03454024581b1310070086410032581402484000402c8030001902403918206414030b801140d030418205580c10b20443c4a0006440c13621504800070b1812501080800e40b8240e1f0100f008142e40c14045810710465080002d60800614202100e280789 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 626370242 1250 626368992 626369011
    0x8060102060628091a0307081005190612020111010c0c11040e06090115051021061502060a0c0306030f12020309280b04051806030309100504080609030c1005 69
    0x903c041c0406a41610341540000c00029242e2402c60b85c5185a401c401144003010350050403900c0c6401c003511303103840c1009503682c83d4540703c1002c1007090070748180c00c60405900c50740c03c01c94140d0f80d420890100c1350419040b40440e810405c01c544402040c411901070303100a44820030300d90703841d43d24035260f41c80c0b01191561140e81c510300014141c41c20003c440c490101d8000018100d40c500c86001c415414a6004074810b000c55101801585c1d0300072200160515024000416800009a20009460640c000e00350315101c5400ca06c04059001070440c1c05110402010414540011012030960b00039010240042d1000000240041c404010749041c4800b1032049c1c0c1d007402c4600d000101d170850242e20301190040e52120302c2ca00142441d0140c0700514004400700c2c0b40c18500b502140d91410720150407119244001c00240c160740301881110000080140390ba00308500d4600b0180c401c1d002070280c1e641da4414000080c540740703000421100703021200c800510110740400d4851300900802481e074000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 626371492 1250 626370242 626370289
    0x60f01050d06060e12070b1e040b0f09010305060301020f0714070e010807080601060e010e0f0301090204020a0c05060606041d04050708070906090e061b0a0201092907080601020606 79
    0x484001610600000c1c1403640c0d01d40600821307034010010901007041100c495500811401c0013818158000c60742c0c9070f038035019582c1d0000042c60908c0c1c424043d41d0b101ca01d07200c10003e080e01c11890114001c0003410000d8034100090388a81c000e242c00c034014105031220a550800a1101080650301c000c030071410320404955200380c5801100800040070f9001a81c3d5038042d900900c007100381400b0b140d0140280d0b10707210550380c1841000030086c8440d00300c2c03603001c3c1a903070300340003c0b64a00717403c00c40c401900a0419995000d414500404218140000b42ca490182d000854020718140c3d00301d90840b00c0081e2120800c0245280c40601d03002d01400446032441a030400048124083c08410000d1000d69000110319243c9040601540e40c00d005411554001c00c0412101100b202d59225031000702203021501c4449140c0c2c141c1c010040030302e025143c0391559203440000f804070411205414240300c0940e10940b260348042d9000b00041c0e4a041c0960002400101d03d41054001d00048010384219181c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 626372742 1250 626371492 626371507
    0x702010f15141c08040e0c0910080402011e1107170705061c09060911030d1718010504110126010e06010c0803070e09061c0605090f19170c0303060f0105 67
    0x410060303643ca04460b40c55001c601002980d45501c40182c3c0080b004814038905081c28000914030003800840c03409001d075545c00300701035900c900300810722400c0c0c1e185d004400041c0802c02601c0001d40030b0580343c040c490303920080b800c02c03150340c20b06c8901585040102441d9041108004e0b940d001020408403942051080301c0c0101a240500380c1424050fa1300007600d41c5031030400a03004014000030074020703072003568003c00701035011040402000c100180302d6410780300c146a000120100d1041d0300565030801050106021110402980c0c02c48240c803008540305c40e51a070300c114196123060455030030001d4801004403128a01040f41e0083c0140340c2500200da0039950f00100390801c0c6c0c0e040001803100e6074542d034075040404140f50442c108503144440c80510001f406200c040c5588005c1485407200b0200b0382600e0304011044400c8010070036900c6540880140880d81041640b00b5030b10503000349149040e1251980c111107248001002861850f80e0724414010a2103402205904204007081500c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 626373992 1250 626372742 626372779
    0x1e0a140403061a060405031926030a060608010f1802041a07060501060201110f0d2a0f0906120b0d021f02062212021002120702010f1514 60
    0x308040c500c6144009504511440c880d4410705080c651580500c108110034006981c0000d103d68800402c05e848024911040c649056016442040341c030102c00200c034200d1000d01010b01861040d14900020400140d8032841161080b10a2244c10507000310b00d44144250074001c10004541460a40c0251801e5607135101124072a00c8649140150303140492070008200f0f09004950044c80188000c3c04402402c4000d05c45510400c020985408000580e001c6041030703030741000071001c9079007240015000c0c41980400d0501121200b0701e0001d031a65545c500c08078000d51740c2c401034505695034880f2442c4850000401007145180e0140e0100320400d000d801a0b5400000400c8070b10204203050003150200c0000c0d1034000041c4c2940d40040c40c07000221400e0a0440f61702c0d4200d038000014500f622103001c400d0341800702c03200c66182c146000185917040f4100c0c01a00d50700940c4554000c01c80070385c48411200c1212140c0e28032890b0300c2190300c030070040f4450550381c178070b03034524010a49200c400d0301c100b84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 626375242 1250 626373992 626373997
    0x7030308040b130c12140a0c0635041a0c03040f080d0c05090112090f12090b0c0319020625020705030316050114010b0d0903140a030e121e0a14 63
    0x81c0c01c0481d105c80321041080f000b4689501d02c901d000000305035896140d642e174804c00b0000e004080400c2202503070a28100001c1c99211100d1007417039203812001c000e1204007000c0b070804407025124078210000041a210700310f01d100d48101c0741c12074000d007103481c1c41d80d4248940d15007070000d40c0c4d00b00b010321040c1c640b010544902d42c01440107464583e034442c54400054041c2c0c0000c04544d00350392520f0f24080208500c41040d840b0380d90f01001c070044e8600c4407082a900c0c0109508044181c04003c61019001c0e000000100000d500043c0840d07412524004200c0e5070b603104682001c3e800f5003d000034820b00c0320300725111440c980c503401541c07500c58899008c60300c0c0d500040c600c04560041c480448042c80428810845079041022142c4860b605000307240c101482420550801156509030a0081c1803007100249481d2181000f95961420400c4009015104c88034007030249001d0703c84d00303030070211162089450306100d0041e91818502242406155a0440d40340d076818005c20300071342504110070100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 626376492 1250 626375242 626375249
    0x90b040e060702070e0a0b06041802070b0c0909100506180406171006080102030408070b0403030209040204032001110c09040503040509040503190f09120201030906050a0f0e07030308040b130c 84
    0x50001031702d041c440612180740a41400c41841c80c01d030b16654191110011a002c1d50b03020303006600e0f0018100700c0c81d4000c4c070504030064a00029102800040000f0900416081000b10345400c020b890304040080d05d49264812154070110810034080345102600481800102c0148002030702503986822006130040b0b080003d405800010785103c0ea00719502c241c2010300041d800071821032a2a565000d1300d8404c81c140500405c0841c030002d81014401d030101c406201c1d0180c07080d07480d1a903a10303001844100107013080300108007000c1c010301c05511502d000500c9013988002480c3d40001c40040c003480c29006007007a1110b0004100c00304560f2036040c4594043c52051009541d43e8000c51294141c02a103d0009030811012900010000d0b50240c190010f03a042084002c40c48516407005030014004003500809007410042005030000059010700c1c01c0c2c1d0840941800181441c070545510f071111030000030085070111000c1000724021042140e804018008403004030840341e120082180426030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 626377742 1250 626376492 626376497
    0x406030b09161401020307030804171b0606010825050c0d0e0111150c1602030a08041505071205160b090105101e060f03020f120103030306080d09090b040e0607 70
    0x150004606001964000000d10325105040d030b40c3c1040c680003e4036031017642d9000d020407590101041c14041034641030001c1c0080c0f0401541c0e551101c082c1017400300d9800e84070306954020b51000414a500544d0f04a104561080c008110f0210f00e004007401081c084203503804001051019034420030040210b0300b0000c096441d8048401c540c08001894410440e00003411034100000d10074a481074100c003150045402c1d42017946441082880020909410401039814890007240c3e0090100c950001c00584040740000c0c460000b00c528140c03518420010014a0a83d00301c1040d10854881e0001d069407003a00c5641c3d8035049601c1d103441440d20000c6d200409c80741d5480d020700501c2103000c3c4c216401051004010210100c0a0303004003880e5009128080c02d11019581c000c2c1501d00c44c3d4115480e8040320172126860b046140501c3e40786a800f40011030110340391050114201c0c60000b07001104180303d5407420304c044e04190420003c0c0404424881d0004d8448041e26048081441424418452617 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 626378992 1250 626377742 626377753
    0x1206010516061d0c24161a160507030c0b041118090607030b030a020f1306080129030307030e0103150b280e01080c13060519050301050a030f020406030b09 68
    0x6086140c1004820041ea40c45400d017920041070070420b000d260044d58a40b0305c4031584403402c010501402105001004060700000c5856950300200522007501070501030801c241c2254000c81c1c262240e108140018000c80ea0104d0840001801e41102c0c3c0e61251280e00800204103011000c5004482c1d000480c20b10107130010200092032600b002601e500c00d100745000c0c0407071014500401d8550800940182c0180b030075110401c125241d8080055407861103600030400e00e0340d5019400c4c000c01940c0d5034640001485c0301c000c0b1803030700702c007039440c03107801c4010b0145240c202d056074140da4040780044980e041c50345070b480d004d40d4220b011150304000e103120352045d40e80f40380341c1a240c1c04040c9060745030600c40e055001074802640d03020074840c40960007030910703020a848030902d17840140980c210035901200101030220350540c0c00400741070f40000f1400c40841a443d0684103030b855000900030b682d0440940d03c030030404502e000d04400049800500b0000d04aa2241c90f4600a03000444180e291580030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 626380242 1250 626378992 626379041
    0x1021009060f0e0304150216090c020c1e090c03011511010e0703080a0f1e0c0204090f050c010f0c12081509040b1005040911041113032105120601051606 67
    0x12041b01c50380a16452015000701411252240030b40e50380741c00b5203140f05944940682130306000b00900340008400408541509840b5103814101d030f400c10240c140110b000c0c0c808500654640010f50781a00c010322080d01049507281300c202c841e130000209090585d0740307640020780c00d050248800c0d806180a03104440da5031021910241007a04032508140070072080d02c0940302d0010080f01c40c00f132200355074070307000e0140c3c4a1400020007900f50007070047c1400d119459100100100040c1ca16020282a04d0354894200d1702e050035507000801180c0501103181c5444412440c5104820540d4003401004c1d0310f196040f51080800d0486404403002c840943c0740c3c20a002d11220b031310402400500c802c07101800040d140f640c52003641c00003110014000c5442d5454401e54010034802c1e50340c0a80040d1109984d00e0381ca060095802100e11891480003240003041e402892103841100d80e1709060078003c4800e9100d0307000448056108038400411140b81c6041000014810300507103c01601d10700310380075078803407 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 626381492 1250 626380242 626380259
    0xa230c061e060d08090a0302220e280c03080327030403051002160510020a120b1012020f0406020705120619020f091315080c01021009060f0e0304 64
    0x4a1a21541e030a03020200700480c6544500c4228100d6500580241c1c5924041011400c1d038038454000942c08040070040440c10081420280803241701d0030800e01c5054814080c603a01d03950640d064201c440350601c518800e244030742c041303000c01d60310a00c038501c2e51030380d6521040829002600d50758244e40c03140c40b540481c403006001c0882801106800380d4a040d241d96900c0d6600c9600203498414240c010882d4404004c00600002d81d10b50420190b40c105d07140b074540303030000398000e249070342c0070481c00d45103000c0c0c00c0040c1c4100e001c03008001d0032000c2241400719040d80c018412030224550240c0801800502e10260000f41000f013600750001c01c1c1407400c1c1410000f809d14988084070055004000300000e8202803804030101d903001c090010303615203510800f80a242324148501c1d8201d41e40d003585a00d9802183e01400081e0903c0e0080c01a65407104007254955540004490041c1d0104411460242090703004140700707882072000081c1059940c0e420230550b01c041a560300f0039000818100007024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 626382742 1250 626381492 626381521
    0x703030c0810170f030f0d181205340209060303070b010e070504090606121b05030714040905090d020d0201060501020303070f020a0537080a230c06 65
    0x20558100007401c1d1400d40c1152150022600c11520740705143c460030b0b11980414000b00c00c040c80200140d070396400c00e81e51001c00ca58000d0004420440c54a0503003200401c01a06000005034865444540b6403e9520f0442e0590400785a540c6228400c3c07844c1c140321030300b00c1000360044844103503080c1610b5003401080001c200040c0f615001e0740040283c00006200c1010040c1520031582001040d0385a1070700445050180750000802140f911b80f0100d80f00740c000403032400519038880280000c5000d0320742e40e2010741c54001040701050091010030b4486010700100c205450b24040041e040540d81c050520565605803140103064100041e6413840950510541040c624240000c0c40398500d0080001d55038400102403004004900b828ac0c40703914400c2c8010010f0540050031519a82c480e1002081807520707400e055002d5134884d0001c00345c200c003e09a10a480c82e00b2000090078a0b940300410f9070002c03018450400941c0c1120780c20310108100f000500501500c0700c3c01410b15140c00d001c41c00d60f90 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 626383992 1250 626382742 626382761
    0x122503020f0322290a020909011a0c01022808041a040609150b040b0f03030708072f09060d0b1305010605101d100507080a02030f030705070303 63
    0x94010000382210710003207030889401102038042c610312070640701103c040c4580b010b41c1c003c080000c07078080701544081d00004101004006401291070740c6810744013000700d01c10f112585801c0747c2d01600401c0801400140c042402c100e008640d4035040482a8071422a403240000113030314180c0c00c01e040c0c641d1240d0359103410034086d0f0381000a0310781031076212449181d444804c00c00000c40701000140402506400c0001c00581c442550a01c5d00361501c08400500f0181d80b040c0d0180b0303c0c2c0480e9070103074a040441d40d0078258010300503600c2c01d800c9850b418400e03880301100b9030348000001c00d1400302405000b0015240e1020b0661420884c170907004200040c41f0140405200d00e20421400001c40e448900c21900143c00000d20701c0c0ba01040d00d011805004150311180e400812018081126504104690000b248075504110306843c00810003800c20305005201d40000c0c0700340403120000e24120000e1007100fa10380120390030319aa024001c10719500460f915000110003048000c00c064050140070000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 626385242 1250 626383992 626383997
    0x11107241e291327032303071704110907180e0c0a050c0c040617120a0504031209080709060302040f090503030a09031106010b041e24051225 62
    0x101054005031400c070080300d02d50600c2d60b41340c00d08801400803440c00c0035068000c0c081044000b0003800c01901036044800c00c4405118241c02c3c00c685c1b41c0b00d010440e8030aa03e00c0e1100540d005000300d40c04a0746000800c1203804030050003500c2c4066441e28001d0744200c800b9074035404400298201d0000703d0040341d001d007240c41c401d901401102e078804402e4800d1410989025a11010900500340c0b4003111025a01c0d00186815000b1503182d288103c0c420342c5940000845a01101c1216280041d01c40c00100e9400600c0a100a00c00156040e90054610800b46480003807140c0fa1441c031410b001503944001c00d0507a80d18010421400d05006825540010030002c101340850b90302d8043d140c0c480249030b080481d95900c0c01d00e0425000c0d400e20b000c0c07844080d0880782690384581224072294814001c01c0803002c260291110501d200c08110300986052030034101d1100c490705000000500e404102e8401d001d001d00070a451403000124161040421603c003403100c00408001d42800004840e80504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 626386492 1250 626385242 626385311
    0xc39080415050a020709050712050f01080d11070e090307140304090b06070f03080c04030f080706060509070e0409030e030a150f09030903110301180f0203011107241e 73
    0x240f15000f060352070813500d5603800426295134100b000c0307844c0d840d40204403012501d0071051102a0b409100c4850690b595030084400540410b40151341ca0b150030a0030b800c40e03074480e0200b07222042c1290010342d0071400c1e6204130b9041184070741d01c20310004003412007806203a001043c200054441e03401810182c001c1501c410f80f40161716284d9910f23107800c51802030306008420004c60300c10003070101268003e603046604641c01c08007600d0a56440d5220f800709890040c00c0c400c001c21a80b03030605d580c600440c00741d290a03000401c07900c10300000e8045410160140180400d00c001951014007084000324420f08000c4040103c105080b011900e0032001d04a1151810021000107030b00b020016080d2a081100d44100b101020002405040e10400e0048003440d4075000c032003008921110244220300c200d00a0001743e151040c8000390740200725014140c4030485e1400072105407000c0c11006080c04800000c1100c01020f14504843e09010034000341e029601e03d00c654040101c0101d011224455030600301 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 626387742 1250 626386492 626386507
    0xa05040e0d0c05031c06090b0301050603030316260f0108010501051309141504150b0d0b060109030804080f0f120a11160e01030311010c3908041505 65
    0x1562071003078814010034031560048001c10700c00100180c1e00740750b40480c08007441d001e1029070180607005502c51001c0340d03801c085000c45640b5041c0140d0b44910b1014005500710340e070304448009042c10084011080c8108035504200d0310711010031581c010130038860344580a0070135405005036204140d11003019a454000103100d161342d0011410100140c20b1000b06408806040201101a0140490b60144100c0071500851104103078518480e502440c0b2000d140200ca003015415585078600380d81d8807440d1786e0810703c00105c200070500d800c46410700d08416400d440c0e0b0b40c3c0c058541e00c2500103c0c81c80d40440c1074260400030810560b1103407002c0102415984122491850442c0a144404000c2c05054030346069842410800095250ad005961418003590790080448840b000c0c00158001180a0885078845105010781101c1001c284d54000404108445080b2104069001a00c1003086036107000d088000001410780c0070b50040209698035483c0c81010007146011844480a1010500110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 626388992 1250 626387742 626387771
    0x16060213082514030708030a0e181308070615060203190e030604020105031f0312090806040c0b032d070813030801090213150f0e010e060906071406150a0504 69
    0x150445101000e9030f280f5801000000f0b003400c049030451501c07407001044450300c141d444840200b44500a4590404110740c2c031410700074001040300e242012400505400c00065020710040c4411382c060301c400240b0381911500d80380480403551007440145c1c0040341c80c40a0196918030010309071803038203185c280015000d01294407010b0050001e418400044001000610704080d600c584001610b000030703940d904e919100070061522540702001420000300403d5038440011102c4c0115001200c02110511f0803108050170f0740300074503198011807c1720745d1204640c820340c441d0103d4690750001002c107141800c0002c045072401090040a24002142527001c00d03040440301c0e0564046a02c0941e0758100d940c981c0103081c02d55400200c10814030325084907042d07840340700c90503840099034039031500c090600011100307440e1245009502070b2041002581500e459001004254411301d43e043c051418101007038203040048421070701c1443d40301603010980ca4110354000103018103c504000b0500c6030080f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 626390242 1250 626388992 626389063
    0x1306090b10020c04052203050a14040506270a0902041a12040602030402031e010905010515180604090c030f0312140402100c060c030b040510050906061606021308 71
    0x1401580d40d1404101c088021460854000040c0d44421680942c54a4000c206510809c0303446d001a0826046484541221040b030b001c95100415484c02c122400a1446c8a0320062003208600c0325590322050b21501c3d600d03214001890403510050300e03280390003400700d510b0040050302100218100b28040071110b044514503041038204c40d00688030755071840406d1038180015000c0082500742a0508440c0310150007070b90302c2e984508000d004644882c0d110702c000e84140c00c4641c0d40100640407440520341c460816951010008002081e0481682c44480c1c0340c108642041d160790020b00e54030400e054002001c10003012540b00200b02013045c00081c6100e010000d08000d02c0ba04000106480c204c1c850f54500d000360b0703000141000b070803a040c01c1c09001803001001d0940200e052000280a005000e9000f404555001c0c0041e02e2903601c050402109a03c40803014181c1c403007401203800031400710b01c0504440854000540aa04c0c00d2084caa403a1207040c0ca0800ba044020b9021041c0300c840c505207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 626391492 1250 626390242 626390263
    0x50114040b130f02060304080304020f0405091e010b090c120f010f2c0c03090120250f0302010606030506061602090604020702130b09102d03021306090b1002 69
    0x6051075050140341004543c84500f4000c2c2d480030340481032001f4400c0400c0214001c0b482260b40811220640b01404243c61085910128a800c5089280045407001c1100400c20005000000c1e1a01c040341c00640100c40540d051403c040000c04c0c1080540d42006a940d007007141204007441d1503151050345040315049009018040b4404100ba0040301038042580660b0540f00074113085078509860f81002540046941d19500d60078021000700f0a103803100b5804801d00d104407072138035120036020708620210245036000c1f99089129070010101d01c0950400350114840c2c2d00108200b440c00b0070080c16070700040c0c4407912070a070030030140b03507510b00c45030701038280a9040e20640041c0d0f403103200040085c040c601c0e020750090328009154500014652102c60010340c1103462241507105c00904880c91000ca01801c400c220350317010301c84021525a800142021450b07103101184d15240e50103d002503401909030092176880311018000701d030060144c0d06401005844041d42606182402940e0340300303401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 626392742 1250 626391492 626391511
    0xb030705070c051309020901050d02010c2d0f0b070306050102030912071e15050a1d0a03020d0614160504030b04142d0a0f0206130f12050114040b 64
    0xe000402c000d07032152924010403000305103409010495001d03502a141c04041280308076120000803695282141c440c0600d030b601030b500c1100072000c981d2003a60041114517010b080c1c3e5409000e480f01310242c2c59505030f403c0c1c03140402d44182d40c114540104d46d0100039081d6402c1c507081007018015640c0c00000e59144071070498105812214036400c090920f40c168110303205426000340c40c0b00140103c43c090138100d5404d0b21039a548050702c0c0c0b208403518002c0105010026204540c1c813641141d0065103001100401081411019a40da0000b504101e60b0f40c4100d41c0c65460f00c00f4140410352035000180c0c46510a004e0814060054200904034843d84c0402461103001c4008141070200d28002c0e00403500044048440248040941c0400707c410310f44902c4000c8109800380884c0c41c4085058440154080c51002c00c1051990802002d604030400d012841e120340c503800030b02e09510242003c01040c2c150060384460760b03142421801d40700c074025880c000160403400d0000281c85c0d4180998001c4151b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 626393992 1250 626392742 626392747
    0x3050403031b0e0f09060612090c090406140f04030f18150801030203161404020a0324050a0807210c03050a06021213050703030e0a0905010b03011706010b030705 71
    0x91505900401c6004001c894807040b1908603004aa00500702051800c01141c0c42c40080d400032042013140d0404486468001405024150b809140d8907140ba130441d0900781136480d0040d040b004100031500c11902512103548800402d610003641e1580d0541016846404843ca0b250549001d440e0b04103d455000c1000031461182900c0d004151208016001e0120240044035940e0401000786400380004d0b4840d00503c09114101d60724074241c3e40c12103040807005000120311808000080d0000c0200d4030074540ca80c549004a0001141d00b04a860b6808075004c03580c6050400b8000b401031150024101940100000d00c545012800c110907450501e1400d465590407a00c2c1c0780f216002c05500081ca14458860140d00f0090260003030001c282d90141603c280340c2c0d90200364600c9001d11200644150408071062001c68423403e9907100a41d009803600c802c403076a51a04030100c6009901103d81141c0100040c0400340051903040c0104048000800e900c0d4184042e00c6282c2c40050b04420030300100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 626395242 1250 626393992 626394001
    0x143f09010806061803060c1e031005090705040902160b01080109080d0507270509070944030c19030f0e01090b0a02010b0301140c0d0207020d060617010b0906100305 72
    0x44c0e0030300150300070042e007518098103100261150582003200001c4451400012800c003050351102601e200c0c3c048640d8041603180b400047c48a41940542038a0400008100100300901d245c0010048604009a01c0c140c07144103041c114008801a005945241d0400a020380440d1036501603a082c03c0386210001100d8450380400d851130303044011200440741c0d88641d05030120941c409030104480d42929200200c0c0e0310141c1c102c9490401d4050002d0b040460005007221242002c8001203a00c4c02d040d0342c0a09541e040e40110050b003010003043c0c01030b07000186903504d68405021550400c1004804000150301d940d03405050400000800c80403c140071074071403001d0b8442d0250384000c2c0350600c07026507120011000240a4000d090030b00e0b00179820300411a804030b00e031100c0c040c450300140810506018140c0f458501a522060050343d121030308607200030110b0401c0c4500002402603100c50303101c0c0c40c515040c42e42503c60250030148228488020004540c0f11001d034131000c03a40b0362400140e1a9036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 626396492 1250 626395242 626395267
    0x71202031819170a08010603050604060b040801061e032118090c020f0a1707150e03030103170307020706030902060d0608101d0a143f0901080606 64
    0x304040100361045042601c0b86001418070788121501807549038500b03078521568038540303120301c489800c00141e12000402c02244a540020782091009002180417665035400d003004d900560485080c03030b59120740800606200c4004003038103200a413428010745140da00d0b0b0202c4a017000d89111170414055500c10051803151046044d400b040c11200c224064403580300d0b0b0000c15030000800094800e5200001d84c03000001000c1c4d00e10740d400090845a46a87c0d2142e2210b604440c20884041000c80ea802c40b46400c0340c020a00c120306480c000310748940c035508040c0c5802d0114100112621010024410380030b50100324101a10032908000c11205a1840415000e2054a404030f401529180c0041020309011075000c190f440400c8080c400300e15400f50160308100c0c040711405843c3d200e05004e0001500761040e0009101031681511504110f03074812113005254886140e050803110141e9604090003c01823454103005220028203019280001a24040014040500c5814085003540e400301c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 626397742 1250 626396492 626396521
    0x1a0405010509220906111911120417070621090807051c14180d140d0c020a0e011203030506060904060b0319090209011e0b04061205060103020307120203 67
    0xc00702254000740324061050400241480007080310000d0601e01b40505c020011000c0d0740c080118000c1d441c00c01008070100703961001981c13018489074098010038403400143c201c050401001c03188a8241801401404a030408110b0340041040c090500c2540c129881084d41040a0b1480d040000420003400e090813842c0e80034100c0001e007035103e8201217049515003d44295144505034580500b440701036017844940e4012124000fa001d04011503100803443c05401c2819a02d002d01c1d0741c00b0b6503949403c2c1140c2400c0d400041a40858111211001182000700c035000040c0301a801b40202d65041506084850a030240050101525980460300e00d5840c5400c46122981c01041008450750300c410102242d0800c940c11010202550995402000b640c081c42e00d034035500412102c0030740e0030020302d89041c1c100c0141c50500108602000301e4169407990081c0007604207500e0b1108000030a5109005a5000400042c105801841407000d1031781c0180071514246080c03e0050384036a07940d03141c00c0150 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 626398992 1250 626397742 626397769
    0xc140102120d0e060622020702180129031b07030909180212011802090a0608151f060504051e030627060c0d0b010c050f01151a0405010509 61
    0x290700040c2c50305018a00c3c1e404900c42c003420105560a964415003001a00c0001c5503024511442e0814040e540100302d5000303110702407005040383d591100c0755483d84944907003600b191051960f914900003100d000c442541e0906840f81038410302d903113043c085441000c1c0384a10903512403140452880d003014015140100507112450041000c00907548040d50411403460099008940e0001884000c0c003041c06007414410255000d42e407085266800d02c010018010945241280e440c000414412010b00140c000d200c0d64101000090520b070100c0100800c003045030000110313210600b080b400d50020195000c440c0110382800c0008a000c502403450951008c0e06503041c000d003410046800c01e00a00c002039002e10100351000a44240c141658a160a9030b20800c0d10710207000f00000b0b0540760300304010081062400303c0b45002d26544807840c10000000e01451039448642040f08840d4161641c0001e04040303581900b0440d01340741c0810940300d140141410450000b075800429201c403035070440780 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 626400242 1250 626398992 626399023
    0x13020409050d0905060717070f060f0b2b03230301080f0f030f0919090f0e0d181701020c070b0d0b040528110c01020c190c140102 57
    0x304451800544484080300310b103000c550002c601080700d08210041d00c41c40d96004440007068980740754485182c1e009650103c0c0d03c1c0c010800b40100090041c001e0001800c2001c0303010460521603802c0250301d04c2599002e0745550b00f40c09030720003507900702540c02031450b1301070915041c4000003090b1036000985081000ca0300440000000038004030004000c40115400c40581e022000e45807243c030b031a485140200c0c0503112040c003041485160580604150007055010388142e81d6a40c3d42240c265460781c58440159548c030705421103003a2050180d500549064a0b100481c08200c7e454080d4503c20750095241c450100106482151003d50440310444020000c40d51481d44d141c101001e00d92200d400740104a007022040c2d015414a4080c1d10300503a8a40c121060003950480c0b2454843c1444145002c00c03501d0301c0440c4281c0d900e40009006500500d400982e40308078056210b0300d0002d125248500e42e44d05000000c02090340c80d05084155948030350368910094840340100d107040061003051341d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 626401492 1250 626400242 626400251
    0x603140f15031c0206040b070203030c03160504090f020d0e0712080306030a05070f060306081606031806060b0d050f04020d080a09050a06110118030f0e0114030a05040c150c0b130204 80
    0x58980000b045d92285100d04140309065a43c240200d84900060300c0d0a4000300051011804030680900c50315030310106d0341351440c1407540d146641400e40d200d40394100c2a00b80d0026582e42d00580c50300900c40202c030000000c0400d03510302540a201561140c00181c8801c1004c00442e00d10b070750500042030404d40241c01c80710001d444010034405101c0358400d00d0701103450304600041e0071030302103500d091035403800b07a089040900d000c00c00d402600245070304c2c1c20885003074841e05001070031901c140e80c040e1454610301d80d01c5800200100e001c075407002c0c2c401c2041d1040702d010800140da4504039410259400740d80c0720b03280c454459003610101440d800040d48444a0040403501540c00010146000d41c0d4900030312982100310101076801c8014540540021501602c9178100b80c001c0641d42c0da05401807410116102d010b044903401500300352160805a40c4070f00074001442a80f02c4440050001c1d42c0d00800d881301803100141024110300f42c0144001c4000c2e00252421180c80d09543c40d8940191044c007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 626402742 1250 626401492 626401543
    0x307180e01060e0907030e0d0c03021609051501090b220807090506130902090109020c03040503071e1a0304021e0303030a0501061806080103060f23010603140f1503 72
    0xf802c1043d80400e5a0141c040a4000b03216107101c1e006160485400c14003801c508500010101d402e4041710340150294495020303074079490284440000000c0024032800105410b00c8020350a840700b0b00c0c070140d410400302e01e00078010060040d00301c448040c400010549049203521022098485d95032111905000b00310000800003c81d81010b8441d00040350b00c0351940480d0790208080301c0445038003a4205800b1001800004ac480c2c3c0209110000d070021242482e5403200041e1811100350002201072100d03602282c0702003c40c00030000030308078554810520803c0c1503070003007103404002c0019210f4465a40d4410240d840001d811141410182c240e82e642d203041e65000c00640000c1c0314410000e0740c0320303800b41c00c5070700090199802d50340316640b80040c42c1d00e9a15500041c01840b03040256840d521116403d048000c0c4005070700c8040e5884d00701d101580f508501400b110701421880560086e12030030000d01034500f0100130303400302c410f4443c2c034000c494150110b8a00b40e0740c400c0741090000d58030000c1c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 626403992 1250 626402742 626402747
    0x10b0a0303050322080306040e03090a060c150212130c090c0c170c03090f031915050a06031223030c0c0601090b03060f040314030a1b030e030307180e0106 68
    0x310b01c10b0800107500c4400d140013084209003410300041c0540000002c1c0007060452400b07410103203911001d10102d070308000c000c200182801070107500c20b90115441a14100403c00104210010000540c10441c204415808441c81203940141009101c0c80e100e5071807020428002c117044050644d0300e2080006050f440c0e8054908a00903205075010400b145008040c3c82010f02100e000f56036042c05103080003058410301442c8404080101d50600611407000405d05011407010785e8103020755102c005004403100c1c800d080b1a4041c221640c00c07801d140303040c0003080150b01150541843e501e04105030030b10074001d181050303041509400344000c001052088454904001d420f5540080b000c0d03a485998074030f81d403000c440c050f4407181e425420010024012046d00c190213075115009041144140c40100c403016482da004860407980255600f00100700071a800e4002c0011401508040103408005050b0654a010080ca6a030410002017000701740821281ca21000915003445d240e0304070358581c1c201 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 626405242 1250 626403992 626403997
    0x103080a0309051f0e0f071811070308040309120237090f0605040506090411060408030c06041205161104020403050102120702210904050601050c060a0b0901050102070608060f03010b0a030305 84
    0x1c1c054982010085c400d2204080790045a549060004104a034548076220b030780708001038004040c140c0d5800310540815948001051000d202e50350303440345e41c9828a00075250111075000840c5400c6000b42940040c0c80f95105440350038817084095000d0143c580e0403503529680c03458101850b818007680016a06019005508241c0ca812400d025864944003404211907040341d031241c0c00000c160100c0d0124412900440d800a00030f4411403030291200309052856115000680040d80306000304803e01138020002580000185003c520385454000701901501c410b0f00301401c0111503506440075507a80e07504907001164054002d54484614401c540c0344803078111514030250154501786c12130038007400b0140c0488000003002c0341c01c0070700140c00c0c071000308001072180313040c030104002c03102c0e00342000c000c2c191040380c4034840881c61f9100300c402e03c1100601a40101e040d03501c0424140034842d002200564003032000c0c1c0317205200d84030f1040081c0c0500001c5e003170190044104500802416840b800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 626406492 1250 626405242 626405293
    0x2031c140906090604111f0923031e070f060e210307030e030717100b0f01170402010e06160201091707060c050a02040903050a02061506030c03041704080a031101090b0103080a030905 80
    0x2885210300c0c0d641c2d40010700c42741042e401151705030416580700300b030411440488a0b00c2001e02007110b646540f15a0610400c000d15080a4086088000c580341c0700e150900701101d0146411200744d000c1e2076800c120607540c0c06540c10040c1070000650788040c2c592400c0100354010a40c0d1404040400c090070a115290000f064038102e9150501c02603410340c1c10100150000fa8006942d00001c0e40040b81c81d69030740b281d001c0e000324104480c2c0c1040c0840c90390340c040600550a1044000060340d111840058110b2909622011981c1a00c9030054004c8001140c400c084079070504040030100e010340750460501c252100000c3d0301500c1e048500c018568030030003074102085030741c08803540c589603880160f009100d240315660f80804100009800b000e940d1001d9604144900708680036011003038000d01c00e90308641c0003815240c0c0620b40c00382c203169001c9014903042c01c84030000c1005001588030305054950500014218250001c0e41801e503e2081d40b003500d5440d0407170161580850142c44038400701d8400341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 626407742 1250 626406492 626406509
    0x1e04020f220f030f050f010f020d0b030601060e0409030507080c0106050a24030c0c051c020d0306030503070206031b031e062e02031c140906090604111f09 68
    0xe514003030520a070510101903420240c000c040e00e914555541c5141407400608407118001e07140b20300441042401460b613112105c040158449011400c0b04c0111707049004040d05c01c6d404580100300003a004801c500e641c42c400c0d10003103089211810152018485c03841e004100300c5000030f04400d402c40647c80b0009540c002ca44660140c0e0b0354400f022550300c10940a44e41c5071250301d480b44131aa0082d4480d00c003085c21400c001d16080c040381c071181e003480e01d0340c030414050728040402c00000603030510000040900e1030a0030000141107072034803962401280c1001b401407400101250000000c807510a1415180c1c40f0480d680c2d00d400b6120440410307901e2419000307000640c010070000d16181c807001120418404490440421420b07104078003454103040102940010880345422181241e01d4001211800c20302080086515072918920000248054101c0c0c100c1d43c1440040f010100c3c0254100c1d070440c400d144021400b41c00515000c1110402000d0648a0303e06409030b0b0781c000c212441140c5401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 626408992 1250 626407742 626407777
    0x6041a030a0b01020d08220519030206090d021c02010b120a030801060e0904030e190603020c0d02030f0406050703051c050a36060e060f100b07030c021e04020f 70
    0x90b401660344854600415000c02e443c080060303030510140c1000701c1c4003818910303155841000c6469890130b000840840710000c121200406040c140c0420045421030040801081843d1240301c00035164260008240a402c2a4404c2d000c2c2c00c92003504000302541005089c20124800c4c4500325580d40c0e85400d0440224002c1c0c8000a0002d000d940081070300c803c05061080541d903140d83c112039510010540c660b0080141800d806c902c440d0000c20781c0900700e03a031001681c84614102891610144800000442d4000c1101c41d42c800c852500361001c40f442418800d4852070180307001e4075907010f05100008007414080d1030504242ca290409405955244020801c01d03070441c08400d2401081c48500383c026040000c0c000610044460048007140104400501d1000d45400c0e5401e004058404c0360b4008019014020341e00701c00907a0303400900030100040d19158050750040d051141444000c0d01c82c921102c41c0d0078801810895085142c48024002c5550b132040140f008043d402c0391456070841401d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 626410242 1250 626408992 626409011
    0x902041508090d170a0905030c01090b1803040e090c152d030c0d0b04020307020d0f03050702060a0207080c0601031211030301050a090c201f200906041a030a 69
    0x4070f910900049203036070b2484652840610610410400340c00260a00c3d6501070307036000316400713001408407106400004240d0549609001d51403000150401500011501c0d500790107010000c215002c6603031003007200c051559030746105030409074405042e40d0490542c070445000e002d20107000701540080c034049841080308800070b881c8000c5440307107030409540301080482c0500403000050079050748108400725000302d1060125060381c0003522405c0140e8014190101c01a42110440142101c01d1404006606c0c00e900001c2d603c85002d000c1c00c943c036038006800d0060101e1401101c603a10413203030480345a96960315003140402020901c020000712600c281c2c0085050100031203040b9040104025080340c02d001180f0014590540c0d81d10901c02400c1e00d403c28412500c0c04d8108911014003c0d010302c50710101c010b0130084641c8540c0050320324114000147da2000e1100c80d03a1b0540c01c616980d00c6041c0c080c08520b041c072464001d0301c00c0c1d054200140800f44029001540700b4180e0580903c130f000304c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 626411492 1250 626410242 626410261
    0x2105190c020f0112270209060d0c0515070218011a040509010905250f0e09011d280e1006120809030102040f1d070f0e06030a060902041508 61
    0xc0c4660082d40700d0490480c00c202036100e10720149180130001070000e80d410340d00880214060f484408400e0007609458000d06500d4001945684940c0680d40b40380c650103903540300b021407076050052501c00c106000100d42c1c404540000c0c1c6980ba0b901a041d0841a1001107101d07040450900c81c2d0300e05803070701000410f111110700041d1422540044e0042403543d007882001e0780906001041581ea2408500006482103501c00881c15281e21548520004040c6180000c01030040d10708040d00907440040100074810580010305090081c1a52980d100e0f103a01d06075001120780707140c0070994012000c112240703ca085a01001c81c070080501203d0f003902d400803052050350254030070b20660711206100900031600c2400200440340380280014505034646040c00c0c01501141c00c814450505241e01d0b0f00c001800d03110746078001040f81055500012916402020781d0f22000606004507800b10220f0380d80030f050341200001d030100b05015074072035485002400c062007580e0383c81400a040c010108070f420701c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 626412742 1250 626411492 626411507
    0x3091f020d0e06090312030712051303050d0b04050106030606120608070512070513050105040b0406080d0c02210c0a09380a03110a051807030504210519 67
    0x264640280034595101c000c280c842d03025a024250f0801c008102c03250341ca5809000d1040b503070010b0b140064032801c181500520030292000c0b030392410751400003802182850001012a03050349854004c1c0d58001d10300100c0080d000504030942c01605201c00070031041e406070050015107103141d07582038240448444c60001c0e607601e4440c071181c07a0000b1405102d07a041021040c07680450f104122010290340380049140341021020240d41c440e80c500050025182c01c0c010308003100001c64090000c03a00b064034141d1691803041c0c0610900114161480443d00e407080b580303902d50403021114015020310b80f60a41c5401c2d042c10098404c400070500461002424441e100c4800e03540905030981041410020703121310950017191440b5400d4140a0070590355948654019502c07500500401c204100c040c0040a541c94002510a1030509050800c1c0104088000c2e80102d1603d008600c54035941400c0c444448050340b80007000d071074121040421a0000000c18160407140c80c8041000090401140c1d2007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 626413992 1250 626412742 626412799
    0x2031b072003030408071401110d0f03050a060816081c0e15040902032719110a03050d051c06060215041113060311060a1223090309 58
    0x400c8000c0da100360245406280910700c0c04040c0840e0318250300d94204074a0302119900843e400c011181421000d544d00c45031220086070707030703100800c00300c002070b000601103503d2040302d0b40070960744400180d203000f4550440b800900311401501d41300703004030608520103c101e00481c40980310310300c007070413405490510031041d880242d503a085611340480104541c0c016440e00030741c0b09400c14000401c00c45090720055000d1120305040740c4402d10403a500340390b40e000d808085403a41d000303001c1c110710307a400c000e0b0280c1c09903610011061103074030000e0001e81d0a860640020385944500500c0004603030304000104040c09102d000319800910130032070002554140d00a0b200160071200010072460250749020345c10031f00c184071295035141400080398011442c00501c80c0c1680d140c16080013801003e0b009100c420b00709541c1d07945800c0610401a2210306274032094600c542c2d5403205c40c07201d010201204594141181020041420041020780e580e40200407071a00c1044c00e44510000c0035070344000407401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 626415242 1250 626413992 626414003
    0x711030f0a0e0901060e2202091309050d0302031b09040e1504060501080c0f04021812030904150f17070b040330120e07030b010801050f0903070f110414090102031b07 73
    0x4100c82d03000619400301c07030f01e1050007c0036003d2022040765582c1d00d40c111042d0101c1400010108840c1c1091840e2032002400c840915104105004202e000079240105c0410045580c2c1c1c0e540800c0c40204008103e0401c111740b081c002c0c00d00b00800c081d60708000700d004074021402030000f80d803503888294491081c83c41442c1d11001041029a50781010380241a100482c8009141e01a11060125110505002d0840c3c002e4000094040c228601449500301d60b80e8000d410f00c6129050a80d0b01c50212107500800c0c40d4040400589400d4000400000d07014107282c9814a07201daa0320b00d41088059042d51800b0400004290301d00f003003100382d40c1e2210b10014181d5400600000e10400000100000e030195145402101404404a203000d581e0710300801d02c11000003050f143c0119410300008003e022228560400c00c150381c041403d01c03030550302003500003141540c3c44e0f6460380090000d01226103001e40940180d82003120170503040d80507500c01c0000d5007000c400c24003142d451340384510078441c00408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 626416492 1250 626415242 626415259
    0x1121a03010c031d01023a1a0103140114060903120c0615030c0a06031503050f100b030d052a0604110901050f0d06090c0e0a02041a0901080711030f0a0e0901060e 71
    0x95080341c6e03c0101131f007002051512201078081c070040200755098000b0915030204503141201e100e5a0500c15009044000380c0079500700e505051540c040b6142101d0790074846d1901050691085c1c1d8207220242461040140803030b918030039001001c0e00c0d10700448070350040307180c1c02129130b1950601241000182400511640c4030364142401a401890381c00c08586c01d88051960100005d4010441440600c19490060411040e18001c01084d140d5810455000750050920f1114882e00401a40c010f9421400c22003035500c1004000030030040a90380520380c501c03404c4140001e03c100309c403040b0303244103040c0c50b01c41d110380c0c0704c4c0144501e0801845480d50001d1004c440741c030120701c0033341c06094010b100701820304101c2d940d504020340303402003904c030850b5060f80006e04015100300155180601c030b0103100c0350f60801c43d81d02c0019002d090020034140a00044010581c040c6006000b1912501d2181c8080c584541c0d0840d002001003100b0342415003d1001c0c3d00010556500680880c2c00c14240180907a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 626417742 1250 626416492 626416537
    0x9061c1e0204140405191806060f0f06030b270403020601090b0303040b0706200d05060d110103020a020c030601060f080a0603051c02120706020711040b01121a03010c031d0102 77
    0x10800144080d403201e0106010b06e000b007415000e44548aa1406a02e4070900a1414501d041b070b55242c0c400a80c0b800e9186040118083d0b840500b01220741c6801d001035404641c0380440c44682440b046405c03040041c1d500c5201102200c08003234028bd0295088503a16070300d0b44400811658081805581503005002c00c004c0cac00398030070003840c2c10f50ac21040412034030b032280e03a01c02e80040a82494410024046885601c1079a03d01c19198040710489072040104000c0c1c0f6204001202c1030307100350406800140d800141c5008001c1040289009411100310f50b80d141d1009041011814014002426050214060340c07682c1c0500400d41e608000900046402a11181d820741c4994020700107501807031810708800d0b1103c1e03010b0200980035060240c0c0d51007041c0740c00100350250b880b01c1482107142540302c074041d07640700c00d02e4a002500c140300040c0d00d48518030313001140c4503005142c0d5815800c025608101540c035030458590340c641c0c80b03c806100c684400c556420b0b03000301ea1316076002030527100820 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 626418992 1250 626417742 626417749
    0x105060a120501140f011503050c070233030a060f08191b0612050601050319050604091e02150712050f160b07080c0c1209061c1e020414 60
    0x851988180000628109040844c42c00c0032400c503140d0611040020042044002061038401c0f80c1c1c0b580e03c1e040007685000d4000b01c0042c051418042d0103100c2c540740c038258810032000c0030000340300d60300b8a00403500c00c00c0344142100d0703004031810181c41d41841d50000d040b0079060322440503500408003402d0b04150b1003c0c0c5120000030710341d00381c9040d028490800503186d441c000c4c0b5000741400d59648000d5031058580d0a0582d035014108a04001c0c040003004100000107803028580003000340e001c00c50b0340301c0800180141001807400b40414a201d01e4003442d0851b1004003c074014402d44460503149442c0c54081c0c610b0080e90009007403c03281401c8003102510030b200400302c809078028460305080003202d034103e00e03050343d8800310f80f103c02030014072904940210390158070103004c450940c54100b01d8454640c5501042d0360f00c2c01105404211201d00e0303030714041660310750390650207088004d11070044031402030404d0304405d03221229060003540c0c007401d0341d000b00c3d0150f44401b450300c003d0711003410a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 626420242 1250 626418992 626419019
    0xc0903020f010e15031b18130b04060b0702040e03030c0a1101110f030709080309100509151612020a030806010813020303131a04050d0f0f05030a09030506090105060a 73
    0xd2a0410122450f00c0400c0e90356180c0d2042888000d2250540ba03141c0b003100310b00300c0c400b40480c41350090018004800075000c0c0b080200107a51003991100d80d80c421550030a40a80490030000d54000c1c10000041001d00091010304a17040c000c50303082c8040d426840780141c5a110603102c611416000304170801019002e002c1c0d51140c4106140005002ca446505424a81d000600187d40d9800000280f0550641c400c2d10742001d0180c200145282041e200c0005034030700c8060303003540706010011910b0211569800708850700580e00c10000d61b9288101122600102c900c2882207a46500b5142c08921491001801c1d10010358541c46148041d21548010b40e82040020110401d50406625080060728180050201041076240100000b41884850194144001007c0106039000c0c4020840795a860306151412500403401e0a015039042c20b0402c10611910800b0b0014880026441003060384643c888007102d00550a9440d070b525408585c40c2a51810303251503600c018202c00a200340c2165401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 626421492 1250 626420242 626420269
    0x3040c0506160606030f030e10020316060f090501060602070902041404021c0f0c02071d0403030506030709021309050a090c06030b011106010f08060108030310060f090e090a060f0c090302 82
    0x1042c1002400c40da50b00303410740d40b03190011115003402d102c12004141c0c114007103d0010100700d44c803440310104080001e58a0003a0224811001d40e428a02030901403254003401150305061030a100504003420418081c1000d441910011705c5040300000f0941e40510950741520811060400d21030100c404000c06900000302ca6180c4513000324001c1c0c050002c3d480344d1700000040d54400f25010340180c6010341010583d40c440011094802c82c251034520502c07505941c00b551600300004d0030307103522005c0707490240950400d03020140300080c0c41010300d8070084003408403090b86030184559500c0406c0801901c8110500401090b000b1109000349406500104200003045c03400038200e180b2000e010740b0340902039020320b5400104942c14000c000d000c0c404107002d801c0c50001149076080512600036289454842c2c0d404204005d00711000d0b140c4174070040300c010500c2c01c98a550605061000c140c6490341a00105d5059183ca800ca4044107218012120600e1040c1c413011201c3c4e00e581c0034030010a0140c0d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 626422742 1250 626421492 626421517
    0x2109030f0d181112010c1403040f02090915071d090615040f051e0a1202061216030518070501050d020c010903081504141306060305010c020102071703040c0506 70
    0x61080350b20000c00c007407801540c000c04101c42d5001c010801e1081d582c07041e00c10101541d0501d401814507640204120841030801c031075a039035035078603810080324200101000039030010142003445500d2000040c600300290081c2002412510313022015070700c401d05100a0311004c40d40b001c00002d54030345401302c280d002c0405000d1001c03210410300c4905255000f40c12102c061584d441e014499403c003687c982d80f09880d160305240e082c2e03905000055000b000c903c0354840096aa5442d401151111001da9220000ca04c0513600f03141807405507916071200c45108940068648800941281c020b24240032401600c0b001070200c440c02d000044465600044d20303092019000c01003a58005424071030070030820b00a554003003090510b900110060b0500d0210180301d5070a100d51317048403001088820f43c0040c2402480201204a4942038010704443e40c0090155460100170104035601900146040392103524513000080404004480d1804256070250100c2200c0106101a080420040840d940c04d01d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 626423992 1250 626422742 626422751
    0x70e01090e0a0b090c0a03050105030303040f020d1115040302100804080d0216140f0d0309020f0f0d0f26070503040b0f0f04120c0e091f0e01112109030f0d 68
    0x4000300f008944c0540d01c8020101c800100320f15401d515205082c0944030407000f562850030240c03150320a25204941c042e20800c2040050f104004020904c580d545101130003015008402d0460b181c0d05c0e40191200380e00810f11840c0c501100d92061082c94412540084403a04046050b1200c2c002504080c00740380076000d48041c1d06012443c14410182e0303882c4050000c1408040d502c0c0325500b003d1010b4042000d1604195201005a42d4201401803c2d84141c0d03000402c00c41c10800500e92440b6660044c194a03045401201482405007807003100e040c2c00711605106512031101d4003861320415002038403e410500091101c035001c80018902100d0b084002c0d418801c04a41c4000198495404801c0300c42d00100c2613420449421804002001d8020618443d07242040312a915000726401d5104050020403034070403942190b50022091403d503000800001802196236119a03000760340d24010710f142c01c0c81401c1900c100016082c481d02821000e90304052190b010708641c0d802210360354403000d0303c5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 626425242 1250 626423992 626424011
    0x91e150a1e060503130b0c120406050609182a10121d0a061e0606020106210203070b07021809010f0c0e01050a12020403050a1406070e01090e0a 63
    0x100645403010303011944488020944000c0440d9030070400758400800d004003401000b10602c0600081c88925400141c602c4895441e03d103900c1c614407070310303e03201d03c5c01c182181403000b40580d584c490f500c18036094030010407039290102c070150500d038480010a459440150010749010761503506005003060034080340001c00030b8000007211049601003010000b2003c0f01e20b000d9480c460302079002c0b0722001148295065540c1000d15480303070f002d0704000c0c040070746400305481644514560f0300b01d04104c14000300450350303ca14001307020384060f1080303403507042d480c0d0340b4900c070205140e98044d442d41e402001844200c0c613000042c9555000b5500c140e17801411600800006001000224403072509100000340c100941914042103503102101a070402110150b40c00250340c00608491320500c49040200f525100881030300003a1042e5000180307140a040503000030804503400d26038140d0b2440341510301075a1010811501d080c0b9914501d800110040b00c00c1110640b41402581c2042c00309201007000e002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 626426492 1250 626425242 626425249
    0x1309020301051f06051606020c07150f0e0406050307030b07140703030e1903021216061406180903070303020705010b03010e070f17211201061805091e15 67
    0x400712100b01d440c0d20035041d51030f10140103901c0e00740549540d041803810801501400c1c40840405000140303c03e40c0081c5210010b40100880e41c02031440b103403c0d03801c1c108112001000705c1d40b4a48001c010070f40011204e102480c06008620541e04040c0050038054035544030101e41c2c0070301400d00002d0103044100781c642d07480110020481c1902a4402003040c49040200c60b1034119811082c4401e80d40034107144002a6010615803400090301c641d16480351645001e88168000e6800004d1a0f40c0c80c0c80448285046206036040c819007044544d501c2c154850060351025000c00c540b150f6039a082080450002402540901541030240b80000b40081c4520046821a0824180c1c401154802601008002ca0002c42c4401910308112440c80d10b40080321481e6403004c540f0001c2b4440350b140c2c1c4135020000310030307410f80e00c0e084d6540c64a003007256555280a002c18800d50000b8120782034061020071541410881e040c01800207544a080c90380c1802c2d03000042d46001340c00301000700b860018000950786c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 626427742 1250 626426492 626426501
    0x602431a01030606150305040308010302122a03120703020a0609030e03030c100b030309010206010e0702012003040201020106060c0809091504020d0b0405090d020a06090305090a08031c18021309020301 88
    0x610414001130000d00b4200c5035000704a080710500d00300f40c1401c0402002a0b0f009100741d0440c0c1d0306907109003115980d04500f5017042c0800c202d003650307800d8104100d194104483c54683c0c0010043e010307221800d210480a44107441442c1d005000f5900005201002880c2c44e030181c040140249048440444040000703825540954540d200503401110450703030104840c4114412020103c005500e00400240043c0d00c0c1d02051003809001c5514000150080303000707401002c42c1c4c07c0c044440221140e6031250704005a00181c4042c2c1c015071a000c004500e890149481000b000d170021101400c2081002c1008540c0c07070001c1509120701100c100201154075076002030880003840c0ca4010a10000d04000c0c003044480007403801040f6400ba205103140a80c0125000f0301241c3c001c0c0011581c0401d070f0030141c900348111000710b03400041e0181d0001d00303032102101800d80b1014403a288035074500404075020035912002840ca031041d51400d40900103180150701070035a001c0e54440841d14140d10b0b00000e0855 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 626428992 1250 626427742 626427749
    0x2010207080414030106050402031603050402062503020c0910230306010602100e0c010807050d0216080405040f0b0108070e0a12060615111b0103180602431a01 70
    0x250300e120f80700c03c0c185002e0248602821f001d0310114154602441c8058250701000f844509150792500480d055486803811150524220b10701c18081031005280c05403510925001a401401903c0c0024414a044070724039002e0001c081c0007004140c00c10307a02c00003902201041403100020400317400e406403401c0c02200d00170303c561b401500070305c00050110020b40b4014180d9508980003035070318005680c1c000b0009500704ca000c1c40d00700d4a941a035103410000780f24004c0300c255184074008180c0c0070426800c000f0401d0300d00c00d56060100300010400301c000e950701c114005011441c0000010344042c031a0700c1441003544000c2c4100d0b0b00540c0c0f4030802110000c00e810503103035103440740c40c20f0065070b51002c4607010407643c601e490f240401000500f01e883d00050038548210031840d60b5000d44980c801c1c0c0001526000001030b40fa40f441561a00718000d5025000300d980811020011a09502c0c018451030351009680f54049503203c03100b084008203004911003269a1a82c0501d0300c1a4516128009401b9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 626430242 1250 626428992 626429009
    0x109210b0115020d0c050604030f050f0c01020723060417040906090207030f0801182a030e010b010c0201120207030318080c010b0904021807020c031b0f012d020102070804 75
    0x10a030b680c04020706200102c0002028010380000d0303100061b100080c6c80760b100c0c1e01031400c1c1801040700e0b2003c031000d1141e130078210941c00c00400d100803943c40650041c403003d0300c580500c03080051021024520b5040d15949a80c182d00000009400b040048124210024140040e14546604c0c2c00072103085807120713004030310540d9010908000f00f5030400141d044120f003905000c88950f1410503803200c405101104140740355200c00350222901d46ca940702c603031090903950f1040030038445100700400810071881e108915600308200309220354040d140c142086501a552184041c015000041c080c0d80044030850406680300d0340d106010620000a00e0040d1191380c00da40d44081c9a0101429540d101e44818800c043daa001d0000590300c0d02d035940b251503035480340d0418a55030010183e0410015601854042c06100c2c80600c43c1b03100142c81c95810f401c1142c5055510000e400115000603942801d00e40b4044100c10007040039055000700e016524a610001d031410803039034bc038000c45030071070f900c41000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 626431492 1250 626430242 626430269
    0xb0c0c0d0207080c011403190207020a090b01090b03060d0f050717060703050106020304211a18010609050c03190902180108010b033004050607050303010302130203060109210b01 78
    0x40900b062203841e208040902c1d105850441c00d0b2100644c0c0c2c44042c040e08d22130300030b90450203600c03e800c0d01600c40090f001009048001c0d600e03c9510041c1282e0711380e4600045002c000440d40101500a50780260070180001c0c01243c403ea90302c9004908071a819030300b48c441e41c2c4000034a07511410050328801c05040280616013410b81d07000d41a100306030040000e54006100c1402081e81c0e600038145022070600103180c00f0411810f0060324490444004400f2030441d40070009215020207003503401e0580c2900070481182d40b10807140c120340b425a9502000c8100300081203085d00e020710b455030507440401c0002510030599001418104140390800030307016601c0010407500318280f00c0c036002c100040d80a80112402c000d8111684140d060707078a000307641481480d111844404003a9000350070041c0041d03070b031101981031040d42c039003003444100d120749007200c00403002064500a0328025601030311000d0105060540c0740d8980388201203410424109045030300c0209a040c10302500074031a0014504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 626432742 1250 626431492 626431499
    0x203040302031b090402010e0424050a090b090601081f06020c040c0f080a0213051203122406030402040f050708090c01091206021e040e060307050a030506040b0c0c0d0207 75
    0x50400750030044000d800328002c40d00d03c0c9a40c44011032550b0042d42403030a00304100756840000c0c0201001e40c0410306c18a4006031400440b511602d41106481c012034024603040c1d030300c24114055a002005d683c2d007010806011032051b5000780c210070f13081a08101c2050111000d54010309940042d80c0c032810050340510468481c1d41014425403c0100c40b41c680510462069100a081c0c03001c0501784211940d0b000440000c010788005180018220050948a42c644034861555917508003c03005414070745120b01080d01110241e0318410481e0140c1c40110403042e0480400c0308940006205a8010b82c54184144000400703104451081510f52240321940c246104110310f03205010b051981484405503084c030421110881c0d0050709a03004a0150f135500c610552038500406624050004034004580400d50040c00c407a040c1c40740c1400c1d03045079a5640d40d8010044048541e100140160700201c0c0401e0201d404034140c1a4428041040300c0c0c81c080400d410285042d030714018000050f0884101270 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 626433992 1250 626432742 626432749
    0xf0102030f130308150402090a2405030708040f03030b0402030408180103110d02130803070302070608060a0f030803060a1806050102010b030307110d05070e040c080609010c0f032a0203040302 84
    0x5400120a03000c41c982d0460540e4003824155000c1c0001c0944800108038000b29901d0b07804561400e03502600003445039948482c0c140c01c2030120140340c9118046081c1e8042154414019a44511166624103002d40c86075140c000303031001040003c4d0201034580d040c02c0d209460314002180124800c0e5071960355030280c40c4881d02d07418410b9036240c1c1090f040c020407006002c03800041e202c0c1c9071441080141e8450304555503013136600300342d030003015140400b140040c00e258011403070038101d4507992501031140c2c0e00d510030012651502c0c01100e000c201030b40700910101c0d0540d40a5030744040007409801043d0307219142003c80810424000401d15280d00061025503070a005500380c00300260000d50521480d55180f4481d00141c1e00824002e81115841d030007404020000f81d001010042e07076176002420681004502c650b4030380500442445108003150403000c0c14031a20401000b550b40e210340c102c3c0060000c602821510544100310300600105148041010071035042900d91034008640e9030f450351060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 626435242 1250 626433992 626434021
    0xd08150102070501090b0d180302060f100515030411120f010f0b15090a150c060c0c051b0a03020a0e150105040312030f02160f03120c051204020406080f010203 70
    0x24181150000c00c800c10030b42e600506a24240c8540310300407900c946022031000002c2403417a44103c1150000303241c00f810715070080341c907d01031100c0b01103e0250b680c40c00c923020700d40134182c03203044e41100b0041e0201960722485c80186030170030b214903002141c01c03413008001003008180c945252195040b0480d66040680309102c1e010f03019131001e106000049a07000001c6100c640c045c1519004240003030003040b203541c0d07511244090a02013100415510078100010040482c00c102125014941105d00c8400d13809024080210350f807000081c00c140200e84e800c00070441d0040d1030381d40c01c41d80c12040440103a4507034035442d000e0f1000a83c01211450102180d45001600c201c083e4103118007088103001041c8280e034043d40c44d2115040200344500b108110350028400c04c84511080c07059a0000c0b810400c440704085d203854003d9440c0e000181451740b90000721078081080c171340810701c1042840d01055811030503d51180c0018000a00315580700112824200f40c60205401654008200074400082124 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 626436492 1250 626435242 626435281
    0xb0d0b18010e030405041113030c030c0b180127030b09100209100c03020a0c080f0c04050c0403141903024615021c0f0c090312020a050d08 61
    0x284042c40c420360107680c0701d104500a441c020750311050141029010003044071070f4100030f801101003450f036904008a41010502048136400140c078000030f104a00e4406a4007902d00c1440601c135925041030041d1542480c448441d0070038801440d80d10700f0804000c522400942c06400041725901d401c0d120182412003142440c12500d00c14001d14809803180c40815074441000d0130b01c4548580b05080c02e134500501d407180100040301004c070110b9a90408503642007004c013400304482c0324072104c00412081c0c0da0211062400c903081400104082440500c1107144016800281c0d202d01c01101e0010180c2030140d28150056071080301d00c6025a404a807540c0d001201200e00b6085050390400c07803100301d05d100501400c40381c81000e014030a10580344820440a0401c100456407a16004404181000c1c041d1041d00b00b24508000142404c3d482d005000e4000300c0c1da51040307506811750f968a403071520b61140b12811807281c80e980600041d82005895151035094692684a01c5c1c81120380d44c00b040441c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 626437742 1250 626436492 626436541
    0x5190b0306070206041b1e051c021507030c0501050c1e030c04032012071505030105030607140c01090c1404020c0709020306030307020901090609180506070e01030b0d0b 74
    0x70204036034036502081c000d4000754441d200200c200c9655810f200054400e07005000486080380d80a02e42d00030110808085907019500810b030760200302032103000c0c0184c00c00040c2d08114400c00641c50413101800a2480500c2401d011b558000c05403503550071103504607424060044000b84500c50410001c2800a851907071a00c540d10f5807622a90b0700c141405580320040c090356050034000d2204c1c590404030321807030101030146c40349481020007855451840d8400d01040e6883c059104d5222445402203a0507600080e0042000d501d5804080f120a0090507070003008060078000107042e00800e0080300186405541900d0b0610f007090f100d03270080c643c0300448600c01c1d4130412441001660125484049480c2c490b00140c803035940700e0200742144540e903c0294020584000811040b030241c0c014415603600107420096035030081740485190408002c081c1c4941e0090001072482e510421840980c00c20625001c9114071204000c10001d176400d0208071101d01c00d207020018111490303841c000051200d02d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 626438848 1106 626437742 626437753
    0x170f010f0f030305160303060e15090f0405061506041517010603020f04030b1009020a36030206070215120a06050603040b070305150405190b03 63
    0x2402120800012060041103a51400c9072000680381d1540b034a07441c001c20b00741280d4180c8102c05c4102c0805454000c00b254035500b0461041c007401c914020980e140c00c1c000c08007c0220001000200c541c900d030f40405c008a00001840c540103004480132306800e8100c04040f82003881590440801610640d1000440603407200241029260003000942c15980318a000c034183d01c140408551603803420310003800030842e10003085801011403200c3c110100d5071080e000042c0d8002154140c0030904c0208074448500840e403541e095200d04801882d5040c4003c400014511400d010103801b8000c0481c1110071911280b10b100c07961101c90040c05d885604861400030b5039102120410425807c00c1000030b8907003060b000f5a8001c0d9844514044603980d042d5046000300001440d0560480d6164840240d0b40c450744110307030041c0c0c90b95500c100c151a1040000044c1c0c0c5801d0020382c003a5000 = true := by decide +kernel

theorem cover : BRFrame.Cov 626258992 626438848 := by
  have h0 := BRFrame.cov_init 626258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 626258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 626258992 ≤ n) (h2 : n < 626438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
