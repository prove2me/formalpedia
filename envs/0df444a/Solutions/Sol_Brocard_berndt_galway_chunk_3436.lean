-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3436
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:39:41.668545+00:00
-- url     : https://prove2.me/submissions/a28dc7e2-74a8-4ad7-a931-1c75a46e4f76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 617805755 ≤ n < 617985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 617807005 1250 617805755 617805803
    0x20304081005010e0103081303080703080612010903140a020a1a01060f0207080d03020a1407050106080c120303150609060309010b0a1224110a030e10020903070b0313 73
    0xc0348040314001c400307241800041610506041c0e4180c40014032159007980c44094081d081207020040300780203601d0100c0801e022034042d04400744696140249483c00100b80414034640104499050b030415030311200190308a01c090300c07075200003050f0585621400c0d600702d240911800001d01031690300c107080507510444101480c10b80d4100d44861420218a0380c0403170b0b4400040c481c0e4144c9403c00d644001c21203100b60000d10602c0407070301c0d1004803000e5124810746a41d021400480d8240e55510080060640c10f100070600000126000710700c0d5030070307052030700d4036803000902c600d0001924008503203035aa180300c207131601001c015241a40301d1070f015441600030124002c80a11608112500180c050103100340d4841190703101c044031036040359809008410b0081380b07911030b51903512500c400b0400510900604458246558080f42900342c07442c0c69070910302d1090301e10301924010071850b0210784001907840100c411500001da40e039642d0704668102c01c5daa8010052110040d45082c42d11854400f03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 617808255 1250 617807005 617807009
    0xd1a04020406110f0706090e0c09060c010905070501020d05040e0c161203110304021305060f040c0f0e0a05090103120507060f240e0a020a020c04020705070e10080604061d010507020304 81
    0x107401c940b108441300102940d90f2890f4420710340021001c1c43d09101400e007241d80c151700101c180010500b0303d0b02070800600142c10030945000d0360380d9507101e603400340401042050010082130002d4215003202d044000c105200714098903404180d07002c04541212812400c441c2055081d015203081c1000038605a0142e11010f5420000a030420300036072207280c4400100c0b070240e03030b00810b0340d440048800464005400010f003060b9000c180c4807003a10342615240203d0b101414180d03540709885c64603000140c030050450b03030250700a15a00388244881d882d4801c0d81d5040d240c0085a07074845094140d001c450701d11030044020070302c0d41010018465807440360001a1400680c00c032001101074000b0140340c01c10341074403030700d04c000c2d6100000c40e01513030059004001000681c4103413100402c07005c0104c0c3c240c2e0b0084001700c41c540e011610800c00010500301c01030b0401c0710540d07201c0c0c00c2482d001c1800d40d00c680190002d002190303103007005810103011030600c0c04514079440082c01180b4082e48042c1d1030303030004c4c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 617809505 1250 617808255 617808287
    0x806120c13021c050609040221060a020c0d020705150310120c150e0f010e01350702030c0d0f0c02300312041506030b090a05071a0d1a04020406 63
    0x300040c40500d40f42c60241e10320032074003e0207200c1255034940030003444006e2101240a035001c40004054203036024020300b880f400ba0030002507035403842000d440d45044180c0d802e0344115040b000043c0072656a0030f1800c54000c034501c0e081d90300d0f0348503942d212042180c1c81d40110303499000e8002c1a01040000308004049807004108041404c00c295400e4400e00c0914001992041401c02501890360140748010185201854108a8143c420503106512005c541407003407411590000420050382d01e54500e41d00c05801d01c0554109100102041d646100744442c0700244204098201a00703880f030444007854640082140400e8181400003030f0061040381d400e800f100f041c000648204d550000100c45244c8a05117402c0c0aa913265100c1100403058440c01c00d0200303490f008004040703400c071450131340503c45910240c2103540b101d240c071503d0441e07940d0109241d0b90384096000700780c01a070420f407141c1855510012803101130b0341900c00640c4014828150b8083d101240c01f02d000b07680130030115040000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 617810755 1250 617809505 617809537
    0xd0e0d0f08010b04181e1a040b120607051c06060e040b061611040e2a01080408030c0304060b040f0609200a1d221505010806120c1302 59
    0x3101e100400510581c020203091001140a07413100e1003d60b13004c440c4280800c9440940480c6c000e4241007a01c20b42c0764119408020700305610716034507051180000c144821620380646144c2c1206c0203840d814020303c1d220610201161800300f1860800e900200301448140410010345c2700d0901030706107020603495a0103185400c81009c210b007440e200301c0e03040d00020500d00c900c00720a0b82e9000c81281754a4885504591a02130120007030004001441405984449840c003070702c1512a42c032042c1c2c120b82041410000850184804030700c4202c1244c0e045200900c2c0c0e43d640341d8860600308068002588603a03042481c250030b02e0a2240f0591191054402011052062500d1408102c1d40c00220b5030b0395407032950781045040a0540115200715a00182201007401171105000184212540a408003144009a4a2840481c4003845800501800b000c180050142400002031239850b004109500803900e980e00090a420204000034a0040060107150041d402020082c041e41000322aa01c2d1000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 617812005 1250 617810755 617810759
    0x30a08121320060d09120210050601091502150a0f110906120712060b0414041a220e030403210c0305090d08030403020a030e040605010c080d0e0d0f0801 67
    0x50101c4100465903080401111550038001c2c000041c94058000503030f020324200b0112015541c3c5009600d403a50040c9404148450404400b03410f00590f00340601110745041c013002401c0c0e0304050300000340c2e1100281030302c0704101039000f64070f030081360001b09548102001c10400b088106400440e00300070103031000c1c40601a01e403400d54581c010120010f80c040410311074440c00ca00a284415403204445ca0050306d50042e55004004480d01500b0004000a00050a111140300300211124840c025501001107400741408943d020120540c417500c691400e80d4012202121030a400d104091041c0e410003103540f50340c851581c0c0b9400351004440ca052500f040000803c004a8520300300b0903141c40b200e401c034260383d03801c0b1280e50200210540c040712998149011980a8000d903100d10310070380041c003210400e803c010304819811804541714900700007081c46030742da201c3d1007001d00c87d903c030800c90388038bc0b92803c00c4da01508000c42d00446511850303580010240d4081c0d44071821190a40303421032207903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 617813255 1250 617812005 617812021
    0x4051606050703020303010b030a180f050c01090308030412050c01022a010903050a0809031209030901030b0405163f050115050702010c02010e0a06050d0f142202030a0812 75
    0x2002e901d00180c00341e00117000410244050718001c40e031101c000e0200143c45107500460f1204001c1ea14402c0e80e40c640d044250702d0402100b000680b000c0300003401c000c10260329594aa00b043d11001380300500712090403451507662070080c1c0a5800304103a2200a41d1a81c015034070301120300f031008080700802090301c1900b14140e5010b102e50068590166942490214001d406845804014042c03580a200030014240c2009016041d68000c0c04a000a90b80d030b81c411a00043c10f407103860900364452481c020a100288030300188030028014241024400120000390715803c41c00c2007090362a0300c00030201c022401c40541c480c81d00c080b01444d901040245d8031411400300b17204c00500b912011a07420011000991701448402c408584149003c01c440d040c0308010800800b810740c88400881c4c40032500018110440c0100b031051382007130404000700380e204c8003046111103004c2d040304040d0004001c4d190070700015007203c0301015009800c4800c0d8014611703000a0550090044c1c1d50017024050125000d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 617814505 1250 617813255 617813257
    0x20117040f0f0807021003020d05061e10050d0c0c0302060a090317042a050102070614070b09100e1b01030c020616090504061205010501050a0b030c030411090405160605 74
    0xc0350041410341401800b9610a0031581d030040080d581990144240001682c03080075102079002580d80140c1c80c0c4004c0000c0a00b502e1000d0f14035031060141500d0210340c0700503880c0024240c0001c4a0814070b02e05004030a5980340308014000883ca802c00241c01d00300c98000c0004901d0703a119a0132140c29940782540c070001c440405400a001620f1404111080f0349450b283d5038000e4050112215820441d007002c240d002c0c890400350104121a400030072596806000c90001440f407030a0082100c0454941d0322001d01c40e8500c000c0c0007248160204003481c008100041000f06580700400c500645a00a541d480706042040e2419205075440c02155510074098200300220300c1d0018119038a44109400c0403007a0310706c1c1c40040018502002680355683d01440b030040c81c1004034032034840d8884c10281e013501d005030001e90051a41100070004650340754112603108680d00c0c0044c5d1640c80c6c9103010541a00c4650031241e01c00d164005001c1800004600046c4860114816012540e0380e48000c0d0380d2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 617815755 1250 617814505 617814511
    0x4050c0a030b0a0b210105040b0105030f150406110706023a0c022e0501060e030a03050703030f1410150203090603091e03030f0c0405150a0c0816020117 67
    0x1e18080320301040c818620764003c482c0100c8010301d001281c08508a45c403076007891800c8512000d03174450003884103110100889501400044d8007401c1c02c0004006090796600b200c1007510400550600000d0074014158461b11400e0120b4a11680e0785129007400301c080d410180c21200000401010400240c0c40d81100650002c0700341000e8040c82002c200e01c07001040169002c5040d405500d40b1032242d0040e001c690401d07621900c1070721142d0b40300c4e0141e1504881c01604481e00380a54114a13100c141d070001201d00003294146050340ea03884043c0303000c0300039220310034149280c1e60130a40d41d41594141640001d2081400c2c070311303d542583d6100c25100c2c00c9400a8108005608108020399860400f280196441195074003117408040d40d13030320915098140582c0d0b07040d041e0000300601c0341c1c0c0c4842111041e04051a82d150328102400d0000240e0410b2038507895041c00180003540070692406909548070b103540104145454070000303045a040c024200c10200d0001c0c0c10b0584561924074000d030300c0341c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 617817005 1250 617815755 617815763
    0x10b22030c03020d14011506080c0901020c1018090c0e09060a050d080705070602010203100e0114060c010b0a0b1903020301140f0d050a050709141603020a0507060e010504050c0a03 79
    0x407035196400f80051a0001141a28030002c00451119800c00074001c5141104a03807910a202c145041d000030541c84000d082c10908003010070801c0d4440c0e030f000170720300c1c0c4061017201c0584265849280a07111801000000c42d039410b0004800900010342d039119001e9013045403501610340011f0010454098800c680c1503600080e950380030f00c480d09025603004c0c1043c2c42444c1851a25017075032242803400c00a0340c4081d00603900041000011210815004002e054601e00da070f01e02d50610020341d965500c1402968060320300440c0d0740413101025007080c4000200034280b410b500c0c0d25408848407913403140501d85034100c3c40c581a1506203200b0701c01c80b07040301c034010030802405d0528000c1150800400c202140d00801c0040c207031740821410700c4400585445030006004c800c1c9840040001d44000080e850b801c1400f038010009400008c1405001c0c0c44d255160069940105110030368a81c01050400381000d40750443d8004412415404140910300680c12500c155040d0410080c054209000083c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 617818255 1250 617817005 617817023
    0x160909140d0f03021b010501092307090603020702010516030e030105010f080705270a020d0c030204180f1805031c02090a0603051017030702090106020d1710050306010b2203 76
    0x141d0b19100c1d40c05410514582e425042515400e401402d0039500203030401c0b2221a0786070155007603580c88000c100c54031041840032108915101002900401c09482606c06043d00041c3c0300e01160b02c80d8049036915002894143c000c3c00040c10005c10550700080c0140c0a90f00e00800480d43c40107030b034054000c03124140c008010890500d0280190716400076580090b2460011541c03100d0512000c4075441400c50721001611100b1200000c000c0d2904c11841c81c0a06204000c18064103200ac001d0a01e0308240da600800c00302c0407180440018000022811211105540044100b01e4080300524000840e01d181c0c00d010003903880b9800481c459140c920b0340c0b060300350100b0482c250203070b0021607000640003075011400d60b840d00b005c1d408070321410521015030000900ca404515080301540d000d040c4e944002c1501441081e4050145c00b1003142e031426645c072240016501000d10415240542000b600703803001c070350b580e951a1401d40c01003a102c60a04a0001c80700052000709205442143d81003081c0d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 617819505 1250 617818255 617818277
    0x1805030d0510051e03010603050303091b061201140a0801240e0c030708090f06010f06030c031104140303091003050f01061e110a050706050901231b160909140d 70
    0x102c16241c4c940e0300e003d0340654899200001051050016511441c00c3c000648145c510001a1600340d0802440030f9105075000c0c45005030b00d400e01a4264151403042144100c095010300c0010b8868a440d030000040750300305603070341070070710603440d1391a08000e169021200415110b0f4103000600d0021240c540d5900401d01c00211414861002940c200d6440800e03550498074840145061050036000b0040581d4241d070100b1101c1c2c0c2c0b51281c1a89440070f4a4100800c030001c6000920f0b03032284d48280c0031000036002c01c0071140d0b030f824400c031003548000a0410140711040507001d40503040441d948000100c0a80000a0031400b03581030010b118007032f4410070f080041c4800161006030000204d00e07898400c010040f070000e5000c0089401602c8a038965540743da1347c44000615070030003001d9030b0200070400d4284189082d0b82c1002d90300682c5d165204c5000c2103080344981072410000101c550803007801d00d0301c0000c484802c0d0b80001c51881c000c0b201c4981307182010160960f01e11107a40381c0400510311042c0b0f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 617820755 1250 617819505 617819539
    0x3240603150203040f140a120e0a03032106140307290304030c1a0a060609060504150c021c060605222703110c1807080601031805030d051005 62
    0xe55002c0e11801e510a6517502039140c26035000700d065098241544840c4102007405069000c2c206200018a0071182480030403010842145551100030300384480d449074084100c41e00e5218421000550400708440b659607400c0d240c2d80c200c03c1c10070b10b0290050b8000803c0304480081c805100c6840e24600303e81400500d60988d80d80c0c0c0c00104103900700b01004840100040179000e1582d001c4080030300d1040c140c1400005c0d041203030b40316408201440042d03041001910707007182c103903001c40380e407100060094011248240c4203516201402588103a009030b090b407101c42980280702a0718006d02080210540f00c1041c0040480454141d8201c000810100f146d040f80a03005000d0501c40660400602c1050100351006558806000c80116824601c0c015140604000c00d4501100c1107a007005a0203c40c0303400100008003500d0181004070b010000344007640a900240c01d5803070848a10310181c1694100180c89800c0000411101d904140201e441e030705001040c103084e0f680c0280814076111550310 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 617822005 1250 617820755 617820757
    0x2131116140a080f0904180305031006081303030e01020c0105010b0a02060603030403030816020106150509150304031425240e0d0c1109130c090912140d06032406031502 74
    0xf2106034416200c03800007e03440c00d200081f5030780f1882611103d4503428400101118600325030469800c118808081110217a03007402d0100245425040006004000c00d50403070283c071501c6410802507082200000d1199103003c010200000141d0036600207459600806413a841944809400191803030045269501d625800e02c0f0540070360b0000103a1250b0303820102d00c650703000311a14000300d040840c0100c0726080000e03012035003a48541c006495403805030f6002c0c0540501103802689aa0003080c95071481e40c01c401220544407030070b517140060101c540f0b44240706801070b1105500d035402402824401140c50300450303c5500088014001020901e44220f62840c402c81d03065401032150440d0f100a91142c0142c0380c0940b9044a1141c40c480e081e0270551750340122540702100c072600d08000100865013071100391010b03641c05d19000351b0010401062110a020740c041ca0174100d0318111001007040905150110030a060020095a00e103426081008880c098480075195904100b124161341210798 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 617823255 1250 617822005 617822017
    0x191b050901020a050a0602031509010509040f0215030f0106090602010b03100c02010906020c03030708060d050601030204150b0d060806070302092407050a0308060103052202131116140a080f 83
    0x200c112056a01c1ca502e03180d1070005c0c070f100c050312035643c004103000320302608020703910080d0001d44000e00d895140401180a2050082001c0c281c0036540c1e015104540e81c407440d0f201074001d480641d0752242801d80d9612450300c0c081c403e4034042400583d00144079030040c020302a58401c01409041c80c4110601d6420161501c18408000c5560b5034070b682d8009842440507191000c1c412000b1600d9107031880000e4905000074100a200c3c0e10340504c0b4100084002808605403581500c0106504454254050b540394054201840846000c290603140030acaa0740f04200700c540850442d580e84d104c804095080784164000c1c1504040d0b1000840e030b002445520804002c2c0315600820310349282600d80c00e00f4000e10000440004101c1c200784001581e00d03002da80d400c50201d00d200c0200d0901c0794100c8202e4511441d0080c09012607482556801105034480c0c0490350b403400146950b050102c2c4031000040300d01200f20354500300041d030681c05510002d88a95400d03800001d80f4600040d034203404038660044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 617824505 1250 617823255 617823257
    0x3130801050907170309100302250b070e1f0c0807080309010605060a02030f0f090303300c04031112010e0109170a0509150705030f04031406040507060513090c08191b050901 76
    0xc1103880420803010300403e072b2811460345100c0303202c19245010141141c0107091a401c2042c0c010201e40c180e52502c00903401c0c03a10060640030080c025000580e1328600200000c4d0151401080c428140711101d03006610a20200008004042c0c4480800035240611070228006074030520116140780b01c00b00052130003920340109541006407220001e131943d403056401c0709035041d080d4003050141601c8104811036008bd001a20428a4000c4040c80740b13018620000d0040040c0104681c416110120850340c108110030080c0420103943c881d86000c2d040f0700700c0854180e484003124558503034500059035104205640d519141030300160070007048038000382070310f5060002000004006503081005001c0110054072240d00c03286141051040e4201c005114800c40d0085402c002c0060001304d070043c00e032a403a003400d0b46c99030180c2804c504010741c00d4021210b090314240c05615495002620316101e15101142a140c2002c00b6040c2c005a07600116514a00c4000c0540b00e21900e0160001c1e000b18081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 617825755 1250 617824505 617824507
    0x50702060a02090a080727020c120708090414060a0b070b06210303040c0f0503031602041d070807050906010f020c0f1f120b040b03190503130801050907170309100302 73
    0x58030980c1c0e041c15042d0340412801750071f464000000301c0111481071110f0403003c0c011404d220700340c8441d685440000c4400500314400140340030800090006071101014050002c1100c4c0c440b035031000f10710000039120315104454000000814402520840300c81715442842c034442903c459090101c81d40010140303402c1c141840e400d95408907002c001843c45207014489041c50a131800900d6040e82149400080c00380e0001c101c00d00030094600ca01e40c2856605880c00500d88000e00550401d20f40c951400407400e0141c200b000a0030080002e8007000e50300103d404229544039140151050750980c9008070150f007000e0b03490442450010600310510001a0405000d120b80b00d0382030f074145208030405404205159000f0f5116072040c403445403054000e81d0100000d0000c2030000c0c2d9205031801c103015401141c0f0f588401004024001e45822060102031292600e07159440b0b01e001e010b0444810b0035510a0369400a03600070a540003032039001c00b64020310700d40581c45080c84600341c02030f803101c414150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 617827005 1250 617825755 617825759
    0x120c05090d0f051506010f0c1a06040e010e0304050a2702090411041e0801020c071208091c031103120c07110907020a05011a0a06180e130605070201050702060a02090a 73
    0x48240a00c80e121440c44c1000c00d618a00074002400359410900400c04005000f912000002c1248d101c2019402000601041350364400300041c000e0b100f104c50300c00455003071500c1c2001074207000000d4000c0d1441221880703180c03600d4000c01411420080100700c4001180d038951040306840d40d00070112400c01a002041c40d8403081c20b8890f9950185e0f000265020303083d48207510f03e644001d48100a0207180c0002d52424698207000c0d42e80d40310358002d04031503803c0b1121130030800440108441d10300c40042c0a44405014070140240d0a090300380c0c003070300450b0300000300c00310403d004006c80f5400701807484500d0540c0c030359900d26041303900202011500d600d140364003002a9038601035120302c100c943e580240101c01051600c1804d40c1e8003070500d00441602c40f83c0c143c0540e52100c1505090704d1085c5495420b0014250416900101641c4103c17040ca580310300b440035912240040200060056009100300d81b03a0703440403400c8580445c0d0800060b0000c034080b48190401d0f400a2180c80320080044a00c99 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 617828255 1250 617827005 617827013
    0xb06010c0f140a0303050615070b09150103080d0c0f02030301050f0d1208090708120a0e010536060c07050f0a09020406020706090e1308030901090b0f04141902310c120c05090d0f 78
    0x2103b03030405c0c0c40350000451030821070042070050b010401e03400c1c030f01a21700c946000d030043c0d500d000600865110b21181a1002455101c02c03801e1000c9a80040304114210b50881018204d8981690ba86c003890051110100d19020006545840502d1500d111807402c1d009010440c0c128541c1d00107141007010422140011141ca2000c6406a0703c0c8000d64520005032554190310340c05104824500680f000d00241c1e44082d00490400c00711001030365407600288016000500103416a08030000b09440840d011980c2e03a4006001d07426940c094841c000210b4031184494454082103540ca046d800e405885000001c0c0c003080510f03000b09010001040032002c5d592078a500f804112510790a400c402c0341080f05001e0000402c3e41400d403c440a4032510300c0a00da0148070302400305000c1d0150703050320007a8030007000c40d0000fa002194840490650350101804c8800540117a5130020000781400704800308540c000d100f03d40201c1c03980d0715080d160414001c00d00c0303045200b052003030b2580c44884a00030041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 617829505 1250 617828255 617828293
    0xa0b0d020306221e0b06031b0c1501030309060908030d0e03040f030822030506070305061309051006081b0118050a0f0e01120b06010c0f140a0303050615070b09 70
    0x181412403c0400d61030351000004100e000504180603d25003084440d2905882c1d640c00c82e500060800340554600205426911041c820300c1c03022141071040501c140c0501c8030541d00c1c5030589229550303040c4240e60314281220320032030324003610b4925003040040031074500080c0d02c680100b62220069905041d991007540700592580d6106480741c0e000014490150141c480d0140c800c06c800c000f824110504540340c603581d03414010215024180c0e24804561142c3d10b8061441c0d5041d408030082c00442103d10f031513601d5240d035201c8000d015042074004101e001011501d1070041c038280d008602c1803c2000011070f40012803200340300341240160004196902c5c0c00717603a00c0c041c26208814603016840c003159147c0d00d140503809510000083d901817000220720f4001c44e07400c14000d01c0c08012468043c101080c641c080440002e100c081e54245000c03040c0000b04a4214240c040e450400683e6100c2043c8140b802c284400b0180c011401c0000c50b00080c105c82c2400d0b0407441e0301040b60420313584804000d000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 617830755 1250 617829505 617829559
    0x7050a030f020c1c1b060e040f09120f050d02030705071b3b01090b0a0b0703020307060911100305160305040c0302091b0d0902042d050c071506060305060a0b0d020306 73
    0x40c001c18401d1f0038a040c14014400e60703c4541c4002c20805403980c4a04505101081030703007082107088400d1a40c1c0b40e101d401030351803468103507800310f50340d044c1080050500d0788081000ca41500f6251509990701c1d2000c0700001c210388105010300802c8014407403914546003048100d88045001c82007501c140034545803214040d203590395001078041c0c140d004101c00800c6951207004014001c000404c00298044151004290701510210f14003e151078135213201c500c4c0110140e080360006420340c5029074590040c44c0a848003c000c05010a07003800c007101628801c840180400c0600d440070030041c00c4c02086141d010b1b0490a8000c40e90782c0c0c5040b2808039500100d1000203c90f11540c0d4002507160074402c50f1814070500d41d0410003403002c040261444a200c059160305c03107a8030320006200741040400c541240d507002803150007040c04400c0c031000500c0d190080744002450b000001d1480d04103004044151595030317100f5400c00c0300080f4000040d520003001a50010b5107003580318464107580900c151 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 617832005 1250 617830755 617830757
    0x314010302150c0a29012d05090709090506030d090b09041d070e0708070c030c080c0d030204090c0f050d090c03150f050f0c070201081b07050a030f020c1c1b06 70
    0x9201c500300d03044103c02485190000c40800d0308170004104407115082d62254000030031420103c8403c50b841c04001d808110f0b803010f6080900c5200700000141e1092070314003940c690620401075034450b007041c10760300c4200180c84004102c94003c2405540450f03c0900070703100009001182c0680c42000380c0c0c040e0b040050351300e6816807080714103000c0500c9803541d065101c0c1d903600c1d008500e0310f4107a0000302400c00c40c2d4800b905010794503001c103040c842c2d4001124601c0842c0300c01c1b10a030f8030074007100400a5100f8819079604a141180d1140854880c00300c040504140c2d955640c103002c0350582040c01041c0e2908100d90146040341d002001464203050000b210141c60400501c04095022180984000800c1c0100800c014010080c9014401d02950281502840c0c2001d07280d6500c40d00c105150004003150188180c0840c60f07404000b4006a0902107901c00d60720700d440c908804c0c0050b80e403500803880d078950240181401702980096a400070003c54011803a44210403424203013558018042c0d040a8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 617833255 1250 617832005 617832023
    0xc030c0a03080c0a080103030c0f0519021e030312090a020a03111002060702030a050d060b181005040e04120507150b120c0d0828030c030506010314010302150c0a 71
    0x60103058000000036401112902d10f645000010320004102440c14080142805400c041313a07414050302910f513000390760b80842251208441089a080d609005110807441111410220fa010b035500c416180c0c0f010398058021414826000b00904141e40020b084050521802e0318041c0542e403800a01e9008600403002015800091801e120b00e140904141c2000c0d5880042030080032540040bc80d0340070301841c0b0302a512007044d4440000a441c030fa60002e0b94140c4d001c5240c0301d245d50788568880440d201282c8000745600e4204054a850003140720350701c070500da0354001070041031000d00d03044041d41061030440c0c1740481594810341d400d0410002c0042141c6e0f11800e429480c00c0a030b0b004000742194000a2042c000d1110008200c03c0590b40010404ac0d0040381610308102584d1084140201c074a500b1030b4400c114410080c0180500c000c0d040020303050101250541d40640700b088040c0270740445010030f50b030131074003408100000d14000c2c07505040d04100303c803840c14043c001c0e101060703c121264 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 617834505 1250 617833255 617833273
    0x3160f1523070b0a02031e0717090d09080f0304051306050402030708010e072a110d061e180201140d020f13060e1e030a2001090819170c030c 62
    0x510680c110081c1501d103440d10410034464825902203c8200c510752030030001d41d075940c2c0c110b004c4a0a03009440049e02000041041c804000800f00c1c65a010607415501c9a0002d60345080c415a20ba20040b00b85419801c100300070b12044c2003a58030140b9810f0f0b1010302240d442d0348d55000c54100e80c0b04a40340c0d07000036004030043c803090004000c1c05070406c140d1b00c1e100b02c51508182030030003440da004c100900c142e06202140c0c8200081441a0310311860020314580d10202d07981440d002800d000c00c55025442c4004040180801c4540b04503081c0007050200071840c08802e500544503a0314410781c8021122091106100443c1c1c18001401d484089030303505501c0380303804800c001600d60a900079809121100320010080c0e107981407454181000e03103001c00506198000880c1c10030031140d130b000d8400388010400303d942011070300050b840c4010030b03690aa0019a140c1c0c94584a400b29072641d40640503000001000c542c01c08910704000c05c41800352881d240701e502079149158004079036600680c00500e04c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 617835755 1250 617834505 617834513
    0x10b0a18091a04030f081b0c0715080f062202071112031b01020405060304021c0f0305190f09060f14040602060906150a05040207141b03160f152307 65
    0x5441400c45907003419410350420018240c0403403940f1f020110398540214541102c03400802046000b8101103e60103521449610014401030007101e00d0000310501030b001c0b6846080840d00e0324590810190004554075021002c1c1000c0d5000d02e4090356001c15a0102881603070f9401241c508910030300004550303130105110f03881d40c001c0101d44201c0c0d00703034812f20080003592078000449038020317030440d81d0580b0f0040a9011a43c4095510005000c0f100b0700e46540c0d0405030480d0041c64042044020205441c04103c000c450322410008000c001072291003042100ca4003842070309078800d00030f0070b01d030843c590382001104c1d41ea00950f00040c0107a05c45414048840414004103402c001e0501041c6000c80203103000c0380c0700108a02c102801594001080403c2c04042c0d0305c0c6ca1810030400080da41103409041c068036000b8820002035120780640e0310760a2040488625800854480c8008907401c41e02d04000d64004821050400003400605030147e604401060005c0c501848120003da40300e0b102418 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 617837005 1250 617835755 617835767
    0xb040c0207061d03030d20040b09150901120c0306080609101d0307080f0702041802030601060c03120c02190804140d1e02190807080609010b0a18091a0403 68
    0x402c101040f0015640690548011080306c0284e0b00d4803201240c0030410100c0780082071076103032030310011481c00316000c500f042c911401043d41d00c0e000c039203500302e0791950b0252181501c90b140c44540454080c002c101310b100080e4102036a1445542400500d0035070354101d40d41018000c44c1c100140c0e401041c0c1064a03888103200c0c1d5200480581125400380c4161000c09550707210f001c2018092480210b211001081f020044441d00c0e5400f61040c420132006030a101d404400da080102c0c428016030002240c518402e40c0c445a5050305565514026880c01140740000d0907802c1c51a011406050126400c1d81d80308145420302078452202c00e035a852506424462020750703032291501c55411407a444011400c68001254001c1e0307054407a540c6041144001188a192109008038180620740c002805441c041203990855000c0e01c29a1015602c480c1e180d4205c680044607207600c518581024003400b80c100c0b00030b0b248030342e85c01c1002598034090323242c40101c50500d0907112030307000200c4200810998011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 617838255 1250 617837005 617837027
    0x307031d031e0609060106081801060909050109060606080606073206010317030105060a030203130501060b090a050a03050316151a01170709060f0e0910061e02030a080a0b040c020706 80
    0x4c01902d995418440000c04400c40540b030390400e65180180455101c0080d030104004203000312003040003144038039169010300054107003552058900340780002e85a004001075840307118000c10040c41c1c4202a0768201c0316060091041040d00c030110f208012811800c4280400f428101000703001030361651418030307014032003800c60032007040090004000c9501e42900344c86e100e0840341400340e140e40e100d00d80d008a06080000c0500950b003422000144550352100510010301c003610100e0565031038006100b03489005200080055004102c21050803a0541035039542034880d02f06a0007041e0002c1d11031003070320b4605039038070b09030194a2058802036801c000868442a000d0910455910300742c00090202c1040788108804c0c80b40001d001d81d4400d12490211500d880014203103000fa082c070701c0b4500030f03542c000d000e02c0b0b001c514540442817400001e001c0c0841400d099038021850482c48000441e40d0074400750620520688480c007a422541d0349005060045d4066402403502914006008002c08403407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 617839505 1250 617838255 617838271
    0x30519020906010302033607080f0d030e100e03092b020f0d0f080405040c0903150c110307060506030c01090305061807031208060a06050301080307031d031e06 70
    0x1440600041c1c4481060903841a03007401c0043c0c580c0e8640c2000e400100c501ca4407402003c1c1c22060780c2d202c824202c480140c034024800106ea014030f4640120580d1207046100b124030580c0103070140c0b2071082c0320350881d40703411003800c1c00c0d52644013420072903206690751007540300c50680021a05052030b040980d9484c801540c4600c8074003001e03110001306080304034426030280c001c004410012074030752240354150669542c40420b88024115904021a441e005805110700c15410000203124551260300c2020541c2d4101d0807203610850160314100040402101c03000c1440519110840805820f1000d4a0b007940a02d0340840e4600c0e10200f0181031080d500b008034144803040b04140003040300010010f0348242070708041d044484142100758900503059000401d1404840000e40407664490307052401041d003510200710b6503481d80d0307054800d40401d01440d0071a0b1300070f04c0000702282c8100001d0900c0c501c0c3d107d030340114100400119041641110f1054003520602c1c283c00580d400410801c1d520404c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 617840755 1250 617839505 617839543
    0xa030b0103050601230408030c101503020a090c02120409020a08010504050c07080f0f04080703140a080307080712050a0209130b010c120302040518060117160f18030803010305 77
    0x210001c0d00350326054800840a0f01d484840c2080e145c581402c45016292030000c90b1f48a001d80001c3d00d5892025458210160342000640350303801407810110001e8a900401c40d2406900b0501d2940080c43e40140e414114407a0040c000c0b10030f11608028805014041000350350b40007a18406012800182c0c801c50041d072800c4100000b0b4555001668105544580095500c000d0400025031500610040408041c80054001075840b8000f03503d00c21a81b013109614032a4200348280350b02c0d10010100079101060400c0066401c40c4102c9150340c0c41102420441f80000203540310504451007215081003165002070303841c0c100c3c0782000d030104000401d40401c2c4032000302c0c000001e064035903682c0002c24058009444613000340c002d8060305e0203814090030301c114086105101c0700c44540141c625a0104101e1004510494150340309144141c845000d0210410610a0b080362804203c00d42981008061003000c106644519000d038000c0d4040c1071803d07120f50440c1002424107113841841101109 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 617842005 1250 617840755 617840761
    0x209160201232403071a272e1b0501050f1f0503101d1c030b04151a0c1506030c060307120f0e06090a0c0501020d020c120c0909030a030b010305 63
    0x600080c001d820f80e10340c181203940c0d41130b031065a88240c4c0a4850003c2c4c080c044030003500c1c009038141f0568036546c14101c0b01c042c5c80568070022003040f0280c100318510148101020402d4a50080281841685555220341c80c2d02480b074a5003401c4031000e83e40240c6c0da00d41d4405004540030500e0807404404071446903001e40174500303000203075208c0e0340305032500d400c5442ea04035800074580e8581d14503c0d0065401070b42d041d28000c410020034481100f002501280c942a6580c140307007094030482d180920f140c1d24805c003031403e000c4200d40544c2c000d00c98198450042240c0000d4000c240070640d0602c410541d410064188a801c040c107000500e40d2007401103101f4001c100701143d0280c0e084064191101d8002200c405401110003e441e0000301c12a5610031502809098840003a000034100d0144a0f210761540c0c80c1c03401241c46450407210300303005034498000030916140c42031402c812003030f10303200700c0d1000480c61002c1440904116984003142d0404201c01287c175401d03028912034032809180403c9146 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 617843255 1250 617842005 617842009
    0x111090109031401090212010903030f060e0a0905012705061305070e10050a0311040b041a010e0a09050c03100602010b060703050a090f0b090a1202091602012324 71
    0x2403544405410303c811616043c079002c10a44c030861405801818081c0c1010010000034040c200d0300c00c044002900e40f0000f060414810300c218002d0343c0c0b48000000d01030711445202c03005080884400e07252956070341d1503043d9031061382ca840c10040c451041038280800050400da4203240d0028112914005400003440000383c012900c542036a001240200b81070302c94071f4070664040c1107508090b800c00c14014012083c08100d283d16075140804076403d101c00e201410030300c01070350107a4401001c2041d180c05820300741d6015100071031048001501c28105030756110858404d40340700f5548010712510000920560003021504280500040c0c0024030102c41050085016407140b85406000c000d030105050b120b40e403189240740010003402020482c45900c82c05403000c107606c09005544161000f41e40014210b048240c01515690001c05009851341c0d1104038080b042c43c1007010701c0441d561201368001052011119107580750502c0034980d040e15110140c04041d00011003415038003445203005140507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 617844505 1250 617843255 617843267
    0x90604050c0412170a170a11090d0206070609031e030212011a190e130e0d0810031208180c0d03050a030e030d0f0b060403111516060b010201110901 65
    0x203c41002100d1003c1c0201d08203210441c010300074004004200042c0c00f2800b5601c191400418000604040c0e03081c3c840c0403a21040340c904217581c20f810082401401001c0c6005a0300011321400541814a021083e6840070100e4500030412004900d036560805e4664541e00b00300c00021843e4141140f400700c900e000f01e01000014824185080c40416550300800240f0381510100000a04240c1c2000d841c18805009008040a6035016011403000c0800c4034100d80980400300d102e95024050305c88210f441107800c80700c0241f16485e140d6030b02c00c1c000002810b040d18880b00c204240d5034040d15051000881c0458080d00304400d020758032116612030a542d420304890105c1c1d40c10704045036120f0403000c0a0700680055803141426000115240f000c40c0300541001003102c4012130100441c2d040142041b0860040b030001074000045003802c6e21007070400c4200141c0d50701401e034407913090015400103c000e020b84180c0855a041c1c41703880b000c2a95809003e240701c4d640c2c004503a982484d5140c4002411 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 617845755 1250 617844505 617844509
    0x8210f03070c0f0605061014040b0a020f3403030516020109081203041506180b19060c05150108030909040611030f041b030809010f03062102090604050c04 68
    0x41840000210398441d00400d03404120541c41100c03003032941ca450a001c0b000340301c2121064012511410a2501c4a100ea00c0380408808034200642c1018240302021031150001c1e1b10186c154400c0070f264900e0702e00c0410031203003013610f03a1080140d81c2c103400d680711800220b0528000d04051102000b440000d8100c82a2500c1003580300130714443e41040d0004072240101c070341c013541150045880c6204407188500044d40b055004514418150740c051130050105c4200303200d00344840d10420102402c1c40e071590403003208050020001003100301c020f0a0b050440301c4070703800301c0041201504114104401800700005001c0200441e12080d03140060281d02d900c41e41e616188184110000201044141c1d40201001d000c803c07120f588030310340044450070051040c0c0d410346541c0e5074000445503442414500c482565401868142401070620040d6022400c1955074000d2688460000c03e950b038882250340c50380c8410151b04030480f1400e0050000134030703014080501840c10f2008103c290242101101d00b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 617847005 1250 617845755 617845777
    0xf0b0a1e030f0c0903060b1c080a050d020a050a030b040b01080a02160c0306020a18241e030204050111071a0903100e01020706051509010603050712020c0105010821 72
    0x1031605680d04400070980301041140d454078000b0303c00c102c1d0340d0000c3e058080e2480b07490200410032824081040510310000c00c000f03001500410100099200380c050a40d5001c40d080c100d040c28510b401d10f5050760030075080c410000d0b001060550400354503024042c0d04034400e0340d080115440100000348a00340090422110540001c2d100c1200c0161041c0c100d0060741001221041c9904c03881d00801070341c0120f8491002840d41086483c0c011281203511081307a4146c01c640d41c81d4810b0700b0081d40d01e00c1c42002203005002c1c40c569441d9680c010b00c100240c1d404880da80051b80e43d030400e4009003140d040c0d2a0400455030017001d0910480c0007058000884002c0b41e09034503150f01c0ca14000a1078840e200561040460418420302e03007240c0150060542c20b032244805026554800f88940f0900d554030a0300c03644040240300400005000b54403407501728000f80f4084840f19050030040040e07030b1103840c140185a40d28401000121014070120700504101d00e12006100d00307a02d0b82c900907000e1042418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 617848255 1250 617847005 617847047
    0x513270c1e02150a05060108010b040605160602090909070e070e0f040b060906070c050f0f0f0d030908070b12010506040f09050c040e01030f03030c0e1c0507050402130f0b0a 76
    0x1c1d031260081102680d5540044010810b03881c0031540d03100036010684649000c100c6480012a106401e44147e6080d5031060b40d4090800c0410b61000304200c0e024441690100c1e07007005107500b5621132000503803081c05040e0040082900c4c2c8500e444100c2c00c0141030000b00240c5613861f4140e40c0d01c1d8812040702c48411100801c444126000003403191044d000c01651200c0d0002c5c22204000307001100d030007224070490341444201225400d2044c1400c612044a030310100300041c2800d245007035004010320500a2915411103525001c0d294036000040d040101882400310384804104207078243d050150605441c078901f843e29080e6440d0b5070103014024404450345950006281c5000c10090701c00801c1410070400700c659590400d1031910020210a80000e4241100d620f0f00034091100c20000b100d000e44020542c4410b80842005404283c3c000c1b07415004020000800756910b001808480121801c1303108114544200c0e91500c04080c1d1240301c00b40401d0255010082d040000890326500304d205003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 617849505 1250 617848255 617848307
    0xd110106090c08040317040b010314011d01020c062202150f07030f02010e070b16030c050f1c02070608041502070c0f0602010b010908060c07030513270c 67
    0x4280940303015003000c0d0103203103004403004103540e02045607400b4902a072503209800c13174100b0160442c2901103d0103010020030700010000070310303030119280d05066008000075440f8001c06c1c0400014114010702030160f900400c00c0c1b0b6280b0000c0c811550405480751b802c082d5007c00560b1030507000da0841c80603106000b480e800e1041c0385a410f0481d81d008105055040c1c1c0c3d8070030703464054015210070005034015840d040340609100c000243c890141e0b03201d03449080c20f100049030301c048032000f01641202004200c0502900141003000503000001031071004d02180440b450380049164820280c500442d409500b013000001e400201342e07500076810002010704030002c1ca1019001c3c0c4180f44004080850203107000a01c151520091000d40b40b10b030b0300a00014134000c0046884040c24040d00501e90000e00104241140090082400c036210717040003414108120709000c1e00100e998003400460103080c400e507003071500605000c2140003100e60208482c00341010014848004a13881300f54480030703001e078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 617850755 1250 617849505 617849537
    0x90910020903070f0b0d05010603200d0e1209090c0a39050105010e01080c0f060d180c03050606060f03040b1f080709110403030203070605060a0302040e01020307200d 73
    0x107a400034015501800002d2541d070070b01740c84c841e40001c0405ca0443d28100000c10340320b01c00d008d01240041030252000002e107081c1c0303810f049036020301281e0000560790401541014401d1048254600440f50002c0c0c1343c0051000f0721420383c0008000a200c21010000d102d075950300503480c50485180004d00329080350b1118014128685401800d400b862240c0104030100603054001c9410303603214100081060744d90b40c4110390341e0003100d445140e10081100c204c400300d04000000e003d40c4a0a03940105102000c41c03080150200040c0e1700307940000f0202400e01c14018200300280c3c000c81c0c02d45140c0c0c03422801202c00900c6010142c00144520f40c0c400200300803440c005000c400c40c0c90300f86030740c0d038030256603070210f9544080e41d108060a003410156103152080d141d5080e00c0460b5015009036240c5041aa1480c00401e0028940350780f12003040d10110140e211440307260a50250718000507035a08003004050841c1d80725100b0a03030003002e84580103440403000f00d21020041c9150921202c0030401c485 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 617852005 1250 617850755 617850763
    0xc0303190c0c1d060316140909100504050a060510060806040b03070e0a020403030305060a0305031902070b16032709020c12031e07110d080405010207050d120b090910020903 76
    0x2c4420040f0302c00e490b0000110341408070081c0a040b00f10100e805102a0b00a0035220b0131a92113054818800d105000559007030540099900075404016140460b0200d10600111074055409850580c001000c0c241000f00d41e10400350083c03d24079596a02900d4044001d14154006015038081c9841e402c9219694600b0011036002e0601039200115070319050001e800290014401030340020f05005c0414203d0070903244130b005030781c0c00070003443c0360100003010200b540c40744050000c21440f0ba444000b44104d110700142006034045000600e400c0303194180244005040c01c00c05010031144083d5032441c045000b0190101e60b11410090380300d1a2201030241030a071010311740c000151000007042403424400c50344845000c1c0d0b0480a2050751902502215440e409406e94a0250701147c50880b1f01d030b016030a802e5026102d0000035203000c2040d900c550400c10b41c0344040c0302185110241c880306695902070742c070310180c080d00c0e0b84119107030404200c5e9480c0d03550303100c1200702070340003c1201c550384080c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 617853255 1250 617852005 617852009
    0xa140105010b371d01030902060702040213030b070513080123070c060e030409110f1614030a021608011416140406050a02100501050d020f010917010209030c0303190c0c 74
    0x900c0c0c0e040f2442c01c440900709814030400019483d00c1c001200e00107600a1185c60003064019001906004496003804029440000505450701d0b005000000003000340c101c551186426940300354039410002c00d100080841c507040601542d04102e2280c0441170440c0000a03050044040408580c50344101074603040050080680140e0600c0740c603038014030000000b0011282991020013135032220b41600340481c043c11107031000b0784408110420422404180f04003403640944004c904880d0603045a92550b03100040b12000342e00004a01c542011210040800519005000b404400c40c2460f019000941c024a201c4c00d2600d0700c0005c0344118031a03034103e0300c262050800103989548460020380b9070b40000d0b03803200051050000396042c001043c085e59040f1400a00801c050300c50541c20000051500094581085035103000001d000382c1d0002514a10603900c40016625200c1754149030811241c043c600303000394800c002c28050701c03d044904001008092500d000f03030111a10b05070f07450000039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 617854505 1250 617853255 617853337
    0x5100f081807120b090606060f0f0d1b1106070903080c030c0703050a06052202060703030902030133030b06010503090a2f03070303050d0207020f0901080a140105010b 73
    0x100020414103903500f42c40c0310290107066104020781c3ca1042031540c440e4105c03505900100240440c3c0d0350300d50904060038041c4150300c1101c1c206030001e0300c3e07101100c440c12501072050030849903052b8072a4001071450031451100b006000340c9d240c4908080c01c640c60902c00104034072000600340308081c1d018401d0703494080300c0360107881c20700343d580c1040c0340d99112a00066030b142d890440841c540525401e10514410600c2d855222507480940800815402140090b42132589590b411401a5400e205145001f1103001d0046410102c440e2040e0040389090004100002d030b5101c1032011507545045658044000d01e00306075682da603103010904024001600401c4901901c10200ea04400e2039072083d810f00402c3c58108000b464001016038801e000e210140c04214104100919805039800403e101030003c1d19007a4045000000b291035140309901a000c10740291214208200703142c50071003d2001800001c0c030075541003000c1c0e40900d1040110500c80030b011034002d5800d519081c21506c116031700f2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 617855755 1250 617854505 617854513
    0x9030f0f0510020306010e04022203150b03060408070f0302190b06010e0f090705130513020316080708011e030503030708060a06090b1b1c0201020d0605100f0818 71
    0x260345444404601030a408481e203002d111110b0305201403520079288100e005039120900090070009000003903105030b50300c80c601600c00406d1041000e4114403000250701c0f445801c40b094152411000072502010481d0303100ea0481c800340408203254400b0307030301120782060144210045030b15061f40f90402e114100c21080d1803a0003c0390900c400b030f11003240b01d1031007a2141c4031121001e504015802034550340c01544281203c011074032040c801c3c005000080c038200300d162139045d2100001121040300300ea01d0345001ea00003040002d101603803d8442e8130054a0304128905042c4031502416002e014003a0022070314850070003166114401403003400079a00841503940d0f0341081d00c4018450101124018051082e202c00090382520441c444000c46031418411802c0008114040e4910300d00080a100e0030303c1048400105009001d400c0201c0000d25000140e95024000300d03001514010390180c1e1141605c080219200785e040210145230b41c07501d140c41e040c16642c028840340703032084140c21149288a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 617857005 1250 617855755 617855783
    0x80103020f24040e060105030903071124070210091203050c0a0818010908121803010b03011103010e1006210f050712111e0d06030f110f041118010903 66
    0x1480c0000e005031216001341c400341d9600c18006403840d10096039900b0641c0d004101003008106080142401c411000b0805451024651030f40c0134004404030801050f501d0000714130b0110b180080f600c60042109080031501c81d80f51101c108004030800d84042c082c41030014803102c0c41c800601201c070000d54001340941e102d5002c000c0610b91100b1280c0b0460208046840201d002c0c01e00040c000e112103107410606140c9400740c5241542c04c0182c01c002c54040d0749880c40705460355400e024060400319032807001a225803600c0b0184021801c080e1151003100f240c15000d0006580c403082000313603041100202d0080b2491230100b0340041c00d0400074625001d00d001c0c01d000c42c00790b200364010362100131040c090101e254440c00325040c51207450b9440441664420000c9000344107030014144c0c2000c00d04000448942c1c0392940c441201362150b04403092108903000e0710b606d1500200c0181380000c01c0e941003007550b603200d01501182c4034039000910081c2c601300030100340760703c94140c8902456100c042154905 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 617858255 1250 617857005 617857069
    0x60e190506041833020406030b040509030a030b03191109150d0f0f020301050f0108011a0d0b09070906090207031103070c090f18080a0207051017310b16080103020f 72
    0x50464000c1c1c7c0002414039064001e585000d0142500031184080070718070301106035505030700500ea80011030782c25006a280045101500b2558559418041c0c400420044024420008051801401c051405030725400c8100c2c50746800c02c4a4178420781c4016000c40801490404254203488141e00a51560804081150000700494114101c40342c9a0082c01107940c0381442103c0c030740151101c41e40040c1f03980d422601007003400c0840e0b500142e198081d605020b41700c2c0c52841c00d46a20340c00c0901001d40004164040551045500039071411410203503040c40c4290303484112441140c407804040a464801c0125000301543c01100c000030f83c40c00c41c3d0f031400c00c207280c0802c40350000703c80030700940201319000a103420000004405900d150b80d409401031028001080298005401007003607607142c1c4c0c660980e0001c0307140c818107814400e1100100c03650f101e1401c01c0c442c14004084070303d2002e00c6402c000c40b00d070300300d48081c2c15a44c1c120f40d00140d0805041c0402c12401078841c0320080000003100e000340038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 617859505 1250 617858255 617858257
    0x60406030f140c060f031303050910022422030e12071406040614070501060e1f270e0c060a1107060302030103021f03060e19050604183302 61
    0x1242d0300005444007000e0300d0042103103900800094400f017840c01c00016001c8915407180ca46818400d050003810308914801260141d540803000e100581d0004082c0c2c07404880c41004e5240402c2e61007202090b6191881c0c0000d050511503020350011030f99644000c0c10540161442c0300d8000000d01031031400c4101c100344950700c1c41603110302d80b04136100140c0c52119003400000c0700d0541e1040d8841128080e0700c424807800d03651010780d060b20079560701c207c08581c07005601e4019000e10030103109910b442a9000358880401ca850303010741044001c0030307850f600410150300d4000010745205800100d094403600c141d030030b280c12140216440b0000180002140d41c01200c81c1400180040440d800340740c03559010b400700e1200f80070180d07110f6014900451140c07810303000300c2c252042d01c2c0303030100710f0301d948850710070310300800369400403104171150080c50b07a400c0207205495110404440920451030225030442448074011006849645c0c540303446034516400100d00c80d0004000b0080c10028210041c4420007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 617860755 1250 617859505 617859533
    0x50f01110a1404031a180d030515030703050c0f03030d020c0d0906031125140c0f090c0712110303010b0909010504150e060307030203060a050a0507080907060503060406030f 76
    0x100d00d241902d144a800e9940544080d268015060b501c0c60901c090742007040700004084042042041c0010114020180440c500c10304441d02c020440741051411800c64903c2c001d1401d0181d0310402040011600015a07484060410389540291643e4440440e045100d0310300b4010409000041011069070001502198008a56941d24501c1e480c1d505c00c0f0240c900b07049031a00301120500074015054100359242d515441c00c028684921541c0e80c0c0e840309010b04003069000c1c030390404149011035007080e12280124a50840b17001d40c81d89420f5108280d103000d40000602010500403415103903030300810b9507041c0480b004e0126500c3c2d40e9034940c4004aa84050f007014020850140001200d0625000b9507850381d41404104107410306040060b541c0303843c0200182e81c1440340740030000c0940c900b400708901071320801c64045100d2034a00c041900352003010b0044410401c0701e00401c4005c48001c00c4860a0360140d283c201d5681c0c032120b0000c0c01a04407508017812101824101000b013200300d03464a54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 617862005 1250 617860755 617860757
    0x70e030c0402070c060215040c05040c050405120115091503140106030506040c0305010c2f071d15030c0d0f11090c0703022b082205030705070b1602040504050f01110a 73
    0x68140e030030a021f040031407416903001341114515407080c0118541500305008802840c9086410240e44900203641c407090781050f40500d1f59107140c40e466020f0a0360489001c0d0104a1040c0451000e100103007491501e0f0380300c0940840c90500407043d2000b02908034800468114007120041e04150908031a1003400b880220b44075840e01c0725900768940140c5030503042e024040da51440c04540480c040c4101402d03004402d05501490001207060308400c4035000c0040c0740708030000514500f81409100360703590807607070b031784640e1001d11540d609540c0c40442e4515284d0000c00140c41200c3c1c0d1614000c00341c101c06413a0313030110901c01046010300501005d4070b0120702030360841304118007602940b116014600c01c010b004031400c028a40303902c2d000720341c1c00342c112890017841c07640030078940c5495004442500d000c80e000e400014614042c040c04000c003102501d01c817204140f03485480482c0101c405149000240101c1d120000070742481401d101c00c86000f145840280a8200600136070b801f6580182c5c03142d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 617863255 1250 617862005 617862013
    0x30b1003210f0e0d02091305102f0306061b0106060e030d110705040c0203090307151701061b020103091b051c0b070e0d050114042306070e030c0402070c0602 69
    0x2c0300c4940b00380082807610101070b01c1c4402c51007080e001d1152a02d00200002c85002c00143d0400004104018942c411981d40c400015645042da021503c022054580091011035001840111030084400c032504030070202d41d040da84120001c11700101e1035001e0131b9011254a858400200380b0340216000c401590101c2c00c0da0000c014040b82950b6020071044400910350040106010384e05096200210601c2d860044070304100107640043e00d0404540c02c0002c0e180d000c0314503140a41d81040b5a8014201c0403131a17a10950f0400c0d800a08100080c5080307480880981051415640650b000d085c0f800d070048500710310384145514070600000caa10540b0302451290300c44064103000c04644078542c40d442505a403040d10340006c100d445901d44d40c00c0e6540902000702c0c000c00140309204d1850300c2c5e10a2007140440d0310305403e000440c040d007801501b26140758101c03146107840b0f002c60442d920607050b05000b0203140010003c0391811081c8186c854000f07100007002002d1104140c850740803204150300312 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 617864505 1250 617863255 617863277
    0x50d060504021603110a1e0203010615050717071e050d020d27050604030507091109010c1401060b12010e06120304090b060706090b0912040f030b100321 67
    0x30000303d126004488088000c81c150602c00a442000e41d1100304649a04444102010b07031071b850020424003890380d644600c2d26101200b1410203005910040050329060090b500c2c0c0c0880c081c2c442c3c850604000c04500b102c0b60a800c2e1242c03088141c40c072250700820054100c4d6051948180c0007442484151000c0c410246542405440003558800e40030503580c4a4044d490fa100705840781d030301440070541c00d0030700b030400208003619107601500040d03016400400d1490726080c1084102c40c070410710901d05c040200481110360b60002e44940f00558425070f1112080300300f0000c6401001c45800283d6080300019000e80c0b002003445515040e9004072001035a40d0320340c1010450b81240b08a455071440d042840108a004503c1c1d1003085a5200685202d00c0c00955907290401c8401d0000300302c62469000b000e000c1041002c02ca1840c00903c40380700740b1f142c2800e02600a0054810b44001400b032502600051141c4103100e2401d001158404040207a00074403801d0002c0761070044c054200058106600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 617865755 1250 617864505 617864509
    0x1214070507200303041e0e240a030b0105060721020a03120b012703230c010c0b0c0d090501110c15010f03110609030d030c0905031f2703050d0605 64
    0x3414014100200218a064900743c940c5001b01082c0001000003507040000142c0703000c1e001ca17034030b00c913014030501c2a44049002841c40c01c190502510076020f62045002440052111140309066070701c100c443da616101245007a40f00d04080690080116170a1644a442c82e038001035066000d0b0f102ea10b8442001d8540c141c0e50080341c000010460004040b01303030041080001d80c42600b40b46843d5803180a0542d100d86a624450440c400d1140d200010f1701d1190103094828130084001380f40c24a03040305500c0080c0c40f1202800c0e005003c452000c140051b80b50b4400c0525032000d01c00343c1c1e0040082c020016030000140d503d4015803107490141c0540320b0b404064558010381c2c1c0303041c2e6200071102865981580c41e40100381e0507400c480c80c0c011104002d1003003d580c0800c201140040c1941d0042527240784818024083c3e8030940c0584d009174880080d10b002e640070155903141d40c042034000007402c0d881d51208205094001f000c501c0400134880450810315600400812107000d0803642441060340d40d2003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 617867005 1250 617865755 617865803
    0x10f0c02100f0b030606010c05030d05010b03100806070804120207180f0e0d0c06050601030908070c14010212120c07020d1a240120031201090c03050402010f1214070507 74
    0x1c0c2980d895040701e40054000e60082c8ca00540759405101101c1c03e03d40440e10705021076074280c024100c0380b0341c04000c00401c4a4046c2032900980800c801030041414002c4014003000070181004201c4240105800e00311352003004294020040c01a19030815108040824003c1c81040b085980b501d080241d00f45000500040c0c0c8540e00c42c145d44d5480c3d85009030b448200c01401c001e4502810151100c10b044046200300d070141a00724000c241c10b20100c1d02c0c024401340b0303400d8000c555a0640d0046031002c1d11075502d01055420a5041550340380c1c48e6a00c540c01c0b1845d501c00d4690080d400001040e68400340100200001c1030041f0040c2d03950304a4442171150221080f90060101c07120211402d00d644951040030075004501c0c110000c0c5400040c41c00c020750440e04412240384035a4501e00041041c03445a0141e03000c245c37050708041005040c40e40000b040b100d900c400d10030a0024007600c0c6220701c58154016101c04240c4640c5111071300701024020300551141205543c141030841d245011021258 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 617868255 1250 617867005 617867021
    0x20f0d050117060703050403020c0a060203090901090606092601090b0a060506070f060209010c020a27090c171204030f1103070b190309050d0c1a0601020607080603010f0c02100f 78
    0x42c018000760f03681c2c120441c00b5040045c400ca01314000c603001b640d19900c44e41c60450140003240c02541d01c40e045841405003d0074142c1c03200301c2860410f5070030407405802410b2803050b5001c050700440592000000461080c00c060303031000e440c3d0318145441042c0f1040d494014024180c0100c203000c5c13182d5840c01c1154500400708041d010341e41c5100550001425540101030006040c10407540000c100d40000f40500d545500c01345c10003504040b180146c00700940a581d60450002d82040f15843d191285025100a0f0044545400b244540c1303a0b004682000200905122100ca9564a07612303841e021854110242086a50806001d07000b0b40518000c100742c403da44035507044e0785c00c00099108106a0400344c00101e0140740d9203124003408110140020400172000b03880e03620002119203044203904e40c20710041d2039030b00c52020a10009a80c0450403c3c0c025030355103021742207515040c0c0005e0040c10803c48801b41249421101d0343c140d03801140c5c0e03450124100404220080c1151a4002030702c580d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 617869505 1250 617868255 617868299
    0xc0d1110020c0f040c0c020901170d14180d080310050f0303070f1b0308030126030406051602151602011103160b040f15150501090b0d0504110301020f0d0501 69
    0x1801408501381a8002d03c080700481c940380d0709146860b000b145407220700703810002043c1f1105c11680042c0b1400c0002054941c1d081c07500f0860409d05580700c200c4d5000b4021741109150384014030115694403030b007000c0c02c12504602250342e2400c18510500c0c4441e05442894001c0103183c0580c01c107480c0c0070081e10303045504610158103200d090f54130020502e0440202002440c01064048007150f28000a540a46400c0ea00c40d00113072160083d50541860500201210341c1c0200000e1002550283c2611210130460300e42c8050747e8000d100040014a2600510890420220f645030043c0314404258108500030703214040c0c212194030a0a03141d00c01d01440a01c41080005842c00040d2020200e690050040307049804901041e900c040d484075000c40c0308a402c985440c039100002140c070074101c0042509080ca034a209160a88180309401600e80502c05143d0b1303600014103201b100707442003508140080c02150b5884140020f05104d400846030710441c0d40c6898004030300c518411885a40001c60 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 617870755 1250 617869505 617869519
    0xb060907080f18030a03062103121121060108010902270d0623090109032106051507060f0c021f0e0d050301090f0501050f060c0c0d1110020c 62
    0x2d40c00380d001c600b0009030844003d0103911030700c00c0d08410107001924440303140c0d40c4d022811a2a02d0650150012400c5259400c00030116000c8002608440d0040030801b1000004c502c484190460320b15600419902b141e0b0f000c189032000903010241291184903074401d0302c5940490340c0300c481e128100d02071901c600064a02c4d1420b544460700c461502c0603260b01000302042c50004551b030b01c40003030b00d030803990701d402c505507025020140c000300303954440c3e114070080e000300585901c42d1001440a80e440c0d92039045182c000c40000601c09071900600050705016000041c3d0311106600402039900040054441c00d00d0180300d0140750039a4007407051010f440354000d01c0041c00c0f80003010031120030701e203007801101c1c4c2e600806885484c081c050040103010907160306403258074113003504065500d14100e4410141c9000c0045c44584e84104020b14140c0c025903800c0d403141e010b52461840c0000c070100301548000c00341c1d050005c0100340200b15096520036615211085402030060f40e40d550443c40141c0d00542c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 617872005 1250 617870755 617870761
    0x50c0412080417010204030b010605070f031d0d201e0418050a0503040603140714090a0f0807360f090b15100c0b1623070b06090708 58
    0x680311030350414055507165252640c0c4011002c942c41c05021200c80b070303035000705041050207841c14806004141c3c41c10310901d0186241ea5800700c2e0080054000c080c00460450125642502d0100b03501c5002e025140f6207101c2a039040518112448070305105080009054108440c141051031031541c0d80d808002c60000f0b5070b0342d000c10001d04081d0034000c040c4000070261101040d010403500d43d40302d0081000c2c540d1141809001000c0e64142c0c121107030300d41c0406042c441441e5100c44220251855505103d46807e42507002405400b840ea2041c41d80c41c841d1800800c142c0b8002c1401022100c554203644215801110158a035106446050304080c844441603204294160411081c40e90007000010380c0342aa60f88000b00040140d415018000520442e4000d46c20640c0b040c200c01f8555060903408a005581c4002a0500c010b0039041c0000583c080b0960a0303001d012203e01491a004818503c01d4551006094940180c4415a103416061300410340034200804451300440310359656440f40d036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 617873255 1250 617872005 617872019
    0x804060c05070c0b0a0e040e06070c050102131e0909120f0509090a09150608070302060f1303050a032a030507030e031608060906090a1202011803110f01050c04 70
    0x2051035215060000411000d4000391888107401c014040e100350540d01e0700b2603510010640e2072240503981c09180303012420300c02c04a00252042d481351032480d12152070003462900074003900503120b00c17072000c0240e504086990380c480300f6401d07615500001d10040691f5911040c41c00d44400c04805095244081403c0c148140b06080704085000642002480c1010302e00206800c2082110002d0440781c8d90f22031102000f60402e240c50085064041c01d12001d4100394080791034072510b1000074410034002840d0f24148084038261a040c4600d89c2820240302d6076410020f440f180000d10443c0010028005a01240d202066807225054070401c08402c080e00b9a034240d0b11540114000e034140f00240f00b2b0b0300302030386d020442c0e445820741d081e80c0100d40c2031500001529101c800742442031190840300030000c0003000003925401f003580180c032600311504070040580c01400b4020034906410800e0380240185500315403404c0c0d40ba5010f00031140e00103135088281c0d00b20381054a00e543c003001e00300700420082c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 617874505 1250 617873255 617873261
    0x120f111f08160c0210110d0807020606100801060315120602040503190b0106050703031b03020a0201061a030c0304020a0305060f0708090a05060f100e090f01060501090338040506060a050d03080406 86
    0x105841d080c0b1441d5001e020004601d407007e2000c407140080d00410800c0729850341440155080203040c0d4103200100301c030030307006800304005000d40c200f09940d42140c20420000c1250000090203200d040e06441c90b50350030008082d46c030a000d00d0740248100c03c060030303c0c071462030f14075485650000e04148244c3d080001c02c4441d580018400e800701911404004000180b143d807a45c1c02600d240c0b001680c0300720308200a0300b51107499100f015004d030b0781c200c0c2c01060b9101504803907100c007011a82c01e9990b655480098005c501d070303800c050100d1044000f04200d415080b400b030f60091000762034100241c1d9507029440d5a03034801c4080149903403c800701151107140310190043e000ba103010159001c0e10380f2036043c0d00e21524101c0340c1036102c1d0b00500c00120000b00a103c0d0342c0284c4400c1c03800c0a041c500315200c034890107885011462551814883c401c040050001014910704101c1c00200c1c9141403a0070541d80d602000d0710b08511850aa280c000f4007890080401303400319038982c58583d025952502e1300402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 617875755 1250 617874505 617874529
    0x50307080f0f190809030a0504090203060a08060a15050a0302010c03030e0327180f04110301062c22062c10050a0501120f111f08160c02 60
    0xd1500501590b108807000d00060403c490010b010070000c0d88031400d00808500000d024410242c00030018248202d40c0b080071541030361415040540e8a8070307460003048844080351f100c65914080c080c06d004800c130064001d901c08820b090070f00000b1940703610410000c0c0c1100c3c800207010032114090200000e001e604602d0100311042c003500d050402c07500081220f10b582c0110701e80c03002c11200c1030380c1c01c0d0b14007007001c00041c2408072146030451401182d032800b040c070f028102404100741c0c1048600640d809402803006418400c800318030101032007904034403502001c60418000910b41001460341412410303440c944d81603205e14503202e103c06481d00c0c4e00800d101004400d61418802d0039400b05044040022040c0c03e018009101031054103001c0740c12230b0005003c00c81c80398185001040f0801e9103d40480d0300d150001c0000e60b41c0c0c005850012044502550b00715080b00d0800c3d20350b22120765800c03010000031000e80b1441030f10744c2c905103a49190320f50039202e000841c0100b0a41c00141c244005418a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 617877005 1250 617875755 617875777
    0x6040501180b0f0a021207050a020108090a0501020f03010311010e0609041112011512050618090f01050a0605120a0807080f0d110403290f0601050405060c07050a1205030708 76
    0x8400b5121202220241d0008182681c0350f82c00182424002d58100b0a070603100707520640c0241414420303950903844c1d0420308030190401482d403000c500d81e07207024410940440d40c00300085564803261084410aa00300f44800d8604040080ea1441154000d60b100140030b60001d1215203007000300030802c401015160b0003600042c40601034883c2a08042030524081c01403090160000c43c0070300c400401c00741e0840801c0440c40d04010034805181c8503001c041c41107840403800341101c1d5a0381c1c1000303860203450021840056080c40140712349201241e000d8402e66400313442124407080c0d0301c00c40d55940c0303074201002040303420100515000704c0c86180151040c084044421440c00740c901d052003058600440e01001c85040c005420020007951403100d41e0f0402c8880c041001c10001c024840f5401d8800520168640d4820390024031541c0c8520126009008001c02141e00d41c001240810fa0790340881c0a00c5010301c2c8000401708100610845484809034044000e52034540559a81340f042c1d085041040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 617878255 1250 617877005 617877047
    0xb03090a0b010e04060615080105010f030e0d09030c0602010c0801050607020402090603040305030105040507170604090215070501150b0c12090f13050906070318060b060f040b0a0207050f06040501 86
    0x40005901c4a2640d4024006564000150700b46800c1c01c03401c135030319a4441c0703151500800c035142003141c1001e180340c11250242899003940700d6100083c0d016100f6000c0d00c0015000f0b480c60450480e4200ca200003e8a000d15a07140386292074003000d074201c41d045044000800d00080040003940307450320007452410310261015040100c1c19000c14619041a202240481d00110041c08103040601c0f460b944159640313041410603414241d0070603840b0014082da4059500d800c8102e05645544120503008000115800d503600000e0030300070b0090610a070091485e00420b6000902541c82000b582c0780010540d018001110882020484944c89111141d800c049803400c1030103195154400c5001d040b003d018045180c0c0b17410301c0801e00707100c4000c06401c00d01d881c2c00030f004207450b8403035480c0c151191b00a80001d82034000c0c0f0700080141c019805a03480300c1074001404501c0f248690080d118605443c0c0880b00385584400400c0826801401c41c240c100740240300421040d0f1141d4082c0b00810715108400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 617879505 1250 617878255 617878273
    0x180b0708010f031713170124030201050c0c100f09080f0c01050a03060b07121719020c100507230306063727080a030522090c11160b0309 60
    0x217160004440e802501202e100c0d0b00441042902800351004102003044d05d081454808840e0846280c900d010180c100040841c070380304400800c0012540c420401461580040c080544c001c00d0014041e20020008402d9a80020f0440307000441000c0d2400c1d52000d00b00c0a000280110340e00d400018028041689071a40003d02d01d40c4107008200990040c030203c3d00f100803942d4041e2035034140104050460769010304015010741c84207401010b840d1030f401c02596401d44100783c945460311f25064004400c5c681b105000b101c54021212000301c05407a001d01640d034840d503000b803105000807910f06401c001c0400030441c400000a06c040481d0404c1c2001401d60b100c0c202801210451564500c000300e5600c0100d11210354004074441e07a10f40740c250055181a080c03c0d006511800c0c01c141c018284280032540c003c01610004003c180c0483c880701c0e80c0c50301541c81c01d10780050400d907541304011920201f0040341e00710340400c01000c0b20801179160319032207190000b10440c87e440144003556a004081c86 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 617880755 1250 617879505 617879527
    0x7091e050103030206011a0310090c03060b120f18061306060b1201140307060e04110702090f01060e01080405030a0e0604090207060b030607051e0f0d180b0708010f0317 74
    0x315406107009500411903903040008080010400103481c03060703a0000d1040088040107100300c281607400300480070070480000c010070340c090405e60b0440c0d00c00031404203007a070703e0f5410600510300c51480402c50b06400c1c0c40742c4840d440e4101c00003029180325003084c0c0016889a107007404081c0303628840c460000300b907980d4204010030f41c1c101103000020a0f505100400c04960340c1808a03140c640210701401d00d0900e0315034040c0a0340940098071f40030b50744903181c00e20758884c03850684840d150064202401458050f11203090504240680c00c046688040003000c40d520900c0218400ca500c440198603003000301206030784503070101c1102e0350301c6102003201203908652070003e0305d40103114849c00301c2e52142041c109803c06070700528801c00c2000501540003800942211240e40c031141041055541e0502c141c1a002031103945495401c1c1400c200070500c5401e4103d41a8011500903103072521b094640c0780c402c0340d10b00002c7c45120700125000609102062503c00c20a84007160b20942520380444c041d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 617882005 1250 617880755 617880761
    0x2108010b070c0e012301180e0c0d06030c06110a0312021606020c150105150307081009091401050703050c09130209090906091504030815040e060103080a09090204050307091e 76
    0x1c1109500b1a204a0000b50710080300c00c0920200c00b42404072142c01160207c00300303524a4410740403c1d0695001150000d10f0f83d00c00c039001ca0a584805125468490401019209051280000107500e1041d5028040e80c0410300151143c1d040d0b0b42c42c000610b40f59400806500903400880001030168070f20000a501c0384014584000c2c02d8014120f81002c22038840c0c0c800c04164000ea0064251181c08801e120614045a82c8410a4240444140ca6045a2401a0361660040c0030740c80e2404440342c041c401c42c000008100b02c4400300078803d43ea19510102d060700e8094501e80811202071103e20400c0c85c02c4040ba90301c030301401c8001400c2c22084800962548020f0340c000c01c190704114203000703450742c0c107000040d0110f44166000b0b880e418183e8004140c2e130002400841954450420711f003865075690051070401146604035200c0d03503100d00303155100e94011080100440c410b0140081c074828a4025501140c0000300a048024602006d400140610048034040c050800e0440d841d03940c0684 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 617883255 1250 617882005 617882009
    0xb010b121611070324050f070f090e040515010506070f060f200901200a02360609070f09090b041506050703081e130312060b03042108010b070c0e01 65
    0x548132114001e1003c03151040c0b417800e4207007601a8288400c1080158040c4d011a8003c074880c641510050201300b030854800040d038100584044a060a010911000058a51143c0e04c8904003583c03076661001080094401c2c0b8100408400c031403418000412480da008000c048202c00000c218500c11103148a040149030008080c4081c0225524106582c8621250320800c1000c055191090b078104078182d59000c4042e0080c41214844030490080001428441c00700e0b801e405403c101ea000c40c146400e01d54412602c0e140a200b0340c600007111075100720315012030080e41d03480300f00b900c504145403403015000c01d100e003a4005403911240c4402d002140704620040c50655203583d00c0b00c1d4079280c0103008800140080c4000c2c0010a0044440d401c050f49150f0800020102801d950798140b5056071150300410340d1100f190b00d01800014030300b064038001c5201d01d100d403000008003590030030720403111a001f050030b0000804050041c41040550802026034a0046080f0b1902554a9001c040031040036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 617884505 1250 617883255 617883263
    0x3170106090806130c1a19030b06120a110307031a10050d020f19020604060b04020316120914150a06032102010b031c1d100c030c020d0b040b010b1216110703 69
    0x1011741c000c1c42c00c032401d000d00141f1072a0030700c010b82c09200000c080707008481100c40307006540d9011880071340c034641c040f0b48407800001c00d032a200d01c2d0003c005001824400e06806441c0001d01001410346021150f2222210844e1100c40c100180520040000c0d00302501e008251402008807000d2404545458100b601c044d40c0182600c2c0390602d44082034480406485006600500c24445c1c03140c0340f040202006516880d25111802240701c080001d030481a2010b4242d210818980c010100301246080b82004011249600b03601c0e10a4940c084410320b21002c0c00d115001d43d081200301403c1082014154054030010a43e00000310000c1c0c02c2038801200c0824182512042c245115000407581a840c40c043c5410b41408904401051440354414040420004c4024030300b000c043c02581d440d652250003410103041d0301c6007880c3c4800c0380103050702c096900001d50000080c207030303180314211242661071201106c0c01da21441107030317400c810035246001c06122400c480c0e0f08100801b007180320011406 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 617885755 1250 617884505 617884507
    0x17030103030207090e030702010f0507021f1b0b1302030304030c090b01090920030a021204050105041a01060903170421110d0308180a0803010303170106090806130c1a 73
    0x34516010f0b1030700703002d03a01c0b00d40c910b420300401d4003003100040b081d608003640a0130004250842140100d596208a04001358007074840d04d01c4144d918117412500464a8590701c0b00b000c0c9801100901c1980c001030b101c0103041e00a142d0001d0a40d83c28010286a5140b0107001c490429031240e032414005a41d64206250050765038030070f4815507034880b4840c0010000c0120402000001d07682180000b0814440d02092000000c0803880c2200340754121030404c40000d207031803a030f8103181c5007140c080c01055030182c6d2501b61441c640d10442841107103c0d4100e5103562a1142190718551310403900c100c02039541d202640c014080054142591202c2d0650400c004031384042d22900380c6094110b102400c406240100c43d0140702e400041d4014442c1a0400104004a001c006010040340d18280444d1002402010040000010550404504082d0b41d50504103441e0580c3c803410100c921800d6441106441d91224001c00c0c40c13014803210fa098030703500035031002007034948541d0300501840b0301e952600940c1d10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 617887005 1250 617885755 617885759
    0xf06020d0b0109050d0b2203051909081513022112031905090309100f08160f0807021e030d0e1903050a0201020c1e01050609061e010c170301 62
    0x21403003581801c15090800c0d403019070805020540c21a10000010619820780f40440c80040f1a403012420007006002044a9500701e0310b0001c0064019100700a00362041403c8044035a0088101c40148c4000d500101100e030015501180c010801504803a040180c00000f4000360321740b542c100e0520310021b5140b00a280640510b0781c90041d071a0208010400140b041c007124500341c4100c400c000c0d0304038602055a48070854964214454032024680c040000c01d0180b560542050b10822030280c25141c9100960360b03518074200d0703e82007248200000f044900d01c00480b5008002c01504000540704035458184050074011003045050310795001e640c400305200640000900480e248956504090611001242c5003400c0201480300000d0501c0808140c061403680300750b06a81d0716402d40401c98132100c031140e18541d081010b1100e612059424000010200d04024a07a0343c040c000250801b201289101e820307501030042505510304000d0000031110214000509280b141c20112a03c81e079654 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 617888255 1250 617887005 617887027
    0x4020f030f0702010e250f0602060601080c041a0d020702031203090c030a02150c0a05030327060403320f22030c09020706020405060c1e01020f04050f030a0f0602 71
    0x8071009080900b16810080c01c901e00b000302150852101451380c0f48052200c016072000800040250002c2e290704ca807a14000071001c0c0e00103005401788001381c030f40c540c3da9110418540700921885c007400e8480c144001134200000083c600130034080c030008600500f0158144d00280c201109904120441403001c8244481c08100380110131001104400420004401354045441c01c070166101131078088003c00c05032405001030000b244900c1cad2000540e9505c2c640342c1103540e090b1182900c4c03003d1415606504140780170002403000d0049406032152000c02d40f072000b10b0107204c0304070130f0b0920004d043e54001c40d5110b40070b43e02070005500b1401500f900c841e41d000c03040400d40060600c84643d0492080104041141c840820040e1035400d040580d0714905402c110700a44a10761001d030f000740e00002d0149507060b002c00c420202c61000301800081824900c0194240e00502c00c190303410b01400c02c0104814a0529414130705040c003c1c3c1078511381800341d00d8020304040701c081c01751f5000740c00003580c0c0822 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 617889505 1250 617888255 617888281
    0x141204030801140901050904020105093307080d0c0e0a121104020f0301030305030604060f24110c13090611040e061807030f152c010311061804020f03 66
    0x50200b1442d9001803c01c0b042c0015004941032003442c2c0180d00b6803012509592080c0100c0301d0030000500f013520310581d078002d840c106818140c090380c0b89425050000c90b4001615080b00c543c10340101c103080c2855142c00208000b015010b421400780400814001c001e0b4458080e001c00501d50f0034038140508540c0d003416041d220104002d00c0c403071481001141c07103100848040d40d0640e9050702d0810307120740d200c1c0c0120300100a9a08010054043c40e18006100707540b241100c034501214104509048022210640303070440c2031000c020090304046400d00c1c1900300254031f90b0500010031400320340ca2041d0b03261a012562100c00545450400060502c10b10312841400b940025040e110f880d202400c1700e41035a68000054918001c144d00c0d07100542c203203901da1300300442c0858003405850403655074155a140c5180c12850120340c41940b0110780c40d0a001400815040302c4c1c00003118003420507440c00f0810b25a2020521045500b0a0314080a060b140c61000e8104c0c030211700700c0316607282001e103084058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 617890755 1250 617889505 617889509
    0xf180e010c210603080d050702010c080402030c060f19050702011d010c080304020609220e0604050606270a06090608011509150902030a1506050316050a141204030801 73
    0x280c0e0704101641007810381c0202008030101c0081d022060300c641c10022040640065480580848804906980c1ca5080c030340c0072a008920301e400802c00e07217444400c1030f10a200121800b1398181c10000300c200442c00e110005200020801c0400c0f4540b4003c1d400f08030000c6030240b10720f00000c4003c5000c0f0110358101c0c3d0a0440d01c01030714030003d5800420000203204a4911400074003081e00031010401310340b07416040c1c074014903000b4000703920071844c459888140d050503071491b904e55007080b2200510000c0071a425020366001405001196074810900c04c401e8084041c8210007008030764506c0300c80c5400f01e11035002d113500aa01050841c64160780c1c4065800c907400030100799140003900c2c0341d00746003c002c420803107034003210100307840700a80074161b0345401c140d104115142c00081006690896a401014818000041000781945480d0304a070b5502007200c14500b42003040100301e02d443d0082000c1c0851000500d400c0003080382c203003412141900800050042c468180d401c0c4400c141c0c0204210b40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 617892005 1250 617890755 617890781
    0x3230406091b0b09100302090409030215150a0e070224040b1501231309090c0807030201050307030e0c0604080a031202031b090d02040219030614010c02190f18 70
    0xb0281440401d9002d442502403041c481c2c134842e00c2200a490217174054030351880008004001408107410082d48501101d05c003005440c203076000050311020720b0f0504c0c0512a00213016096000d0422241034500c4902520120652180500107600300076902090030080d4081c10700c01d8207a003000d1400c0d20007100054180c4080748040c007408070321a68044600307221032080e0700c40020740a40c2d40c88500c505115500610710394100410000c640c0c03600d13075002502414420141070000540d40c0070381d141c80e1045408001d00052041020a6940b44070f508140c0b20440d02c8030a4403c030a00d40000100254031a5100034916041100d1b100c06040d0052400d5080740b800d000194a10f1030034034080380c010300c00012540700d0040d02142854050b01e0705034141c419594050070071981d520404000c2101c0c98115454036000900304840400d01c00003d81400e8000541a120100b00c100590b0130040c00000070f41e003a5124034840c2500080030305480440b0300c0200111020314490340329400d4100c00341c0d920003185c0c903 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 617893255 1250 617892005 617892053
    0xa0807050405090613090b010602010902030712020a05090a06051e03010c020708030a0c03170702070302090901060f170c090c0d0e070b0703030b010908010c02010c1d0f010323040609 80
    0x11480d125000d401d60710150407158400d0150005c07110304020806080080c0a402030711b0700114101c0d40551014807442c2c021000c880469030f540b205510009501c150007034020442400400c26801e02403241600400d6003000401d06980b24400310f0b00e03d28650b24150b01011022009071311505080c418041e41c0d0303200d48090b161042c02e004000d65244194911401004031200b0a03006251040401c0324500d00000000038450400003402540c0c2c064600090303103d08621008200700490503c5010210340030020b48809691070706040404a4084402c1581c05000740d40c1d80440554a00207003078816907018480603115404401c466044513540ca6894040d58042402840302d01008070903203005a03031519011401901d00c2c40121060000d076030003201d0540c04c16070203841c1d481c0c040d00024030a450715660048580f03503029414015412088a080c0c1010b01c6a0017001a5440398112110001e0202409515140402800d400152007110103507916952000038030204141d070310617140450301404e859 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 617894505 1250 617893255 617893259
    0x1b0506030f041e02180a050f0106080115110a031205010803091e01140a0f03050c0913090606120f02152703100501091d0718090809040c050a08070504 66
    0xd150058000b92000d400091000140c010001d0703910400d4640d15400b174a41c0b842800c016070602c090b010140c03880e443c5907040c00009844c882c0e04104280c100c409039a52807406901c0c000703030ba10f00710440141c00c00070403c0021203d07002c03510422204000304d20a0361041e14000c40b9001d982c08680044e0020070440d0410009a46070b030782e81d0f8000740907101040005429034079507040140cbd11114812141c054200001c0380703044041e500580324035461100380d2420700c0541d03502c0c180348145110300305110b03900a52040c038071008190b0f1540200c2e0f00c540304010004071540c840c424800b500e4405c0d5021201440c0411205085003001c151b07071a006540c09030840e003840d441609803032855008034440005c101746040103c09903035080112820a030361030307030b4200071a5071203402c000054084050b8003400704105010702070f5015800181c040031103001c403106034980c8070030724242400b410031030f00c083d100c00000703104400c80c43d81c0d90700c2000840c040781d0f115a032f922421f142002d41419001800d03002032250a00003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 617895755 1250 617894505 617894521
    0x20d080a1b050304301416030210051003020a06030c140f131202091305210703030e15221203051e06060d0f090501060e09120408150402030304030f1b050603 69
    0x4460300284250030b0070480015201103051b07513801032000e03200c2d41e005641700345020b140e004101031609011b0000c0030700083c0e89e00c81480f0910061488020b400000b0302008004007440795011809034100392400b6510811616102d49094011003500213005000150002500e402c980300f40d4003d0240c0c42d220300300704120390001084044000c10203980020030302e8820040110901021150320640e0013035050500001080410300e801c00501100440e14101b40c044001800240305c11849185510952680e6074801201085895410302000000580304110001038a00208103c040c920355030002240e161080c00702490400e40c59451031174205002c284065921488111003040d101c180c80455801c9809136007400400722910060000d51a080d0080352804a07041042c0c0074400c1072085404e03021039040701810b144254800d02d280796100300c00540c0c0709001c04041d107078020b000a05032801c1c01e81e65110000d08911050088582c0c082608265034080024010400900400e40c0d01034118501104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 617897005 1250 617895755 617895833
    0x418050907270603030e0906060c0d0e030c0901151710030f11210f121803031c0506042a0806040b060f0414040903020d080a1b050304 59
    0x2601c00e081140010940c80484098041d0340c0c0054607003040041d0f9503079042c01008001c15841c080d12460071000881d00c103141c424150380800d61100c01904680d0500720007030300e1004c0070f000d069406000c0c1c00c4541c20301c0d60f20240030500918940c000001b940088100040c0241c0e24290745861003030038034040c4000310103070061307200640b584603050091201762401d120304041954400e0551050340c03848001e10900c0390300107024144603600101ea040b51325090541c1d07210070075000b01c3d1110150034401070402d003040652a1200d031801800b520b103000391015081490100354003031416070680321000c1c0034660405211300c40305140d110b08a6113100c07207003400d8036418642800c00716003005218801b041540d51240c6c055001004000c090645d01c000c3c5600710707681d0303400c40d119031030024030340703602c510a1820701c1d000e0500000d42c907a022306006030441c0000d640c1d0200c043c00d9151003690304c002e0503544d81030701131505210f0600c1c0c1e25242e850740b42c5490032000b00c418810409900c4480140300781001a4864 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 617898255 1250 617897005 617897009
    0x907020303180c1e090105101b060212070206100e13030f030b03100c020124030305070314182103030a0c030212010303080f0a0c0c0209090a170418050907 68
    0x5407400744480c0c1190031440c40c103048182d031181d009940680f6213402c101410301c0c440e160502510304804a0b030344d55041080356000403030388201250b1012400854440c140b4107254005220f4000141450070143c03105072054400c0700c280016034420000d01c9100000700c094607004044010000d1131f00e01e00400010540b0001d01d0005051042c01d805002816000f1340041c3d81c3c500c0c01604581c00011320f00520300142070b800882d070000d9440d2150000c03c0f020b640d141e86442182445d01c820748685169412506640804402d904000c1018140c3c26001ca02034001c0241d034000d0300421000500e050100301400704000101c612030300d403651a8007031102020040c0c0ea440300e0f6600c00010109940d08064000e44104000e5600c0c40c0c100b40c0c008020035400596541c00b449005051816581d90300228004803903e1954a50110354422030781801464034a9045611040410030354012007002d5580c660f9007030010807043e090200c081400e0100b140b170514640303a0044c40310300500c5a800d0103020303070b6140c044038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 617899505 1250 617898255 617898271
    0xb0114090c0c1b01020a050f0105270d0c1a240f0109030b19110c06010f0f140d06020307120e0106030c0308030403030623040b06030103110409151a0a050907020303 72
    0x3c0e8040358a1607000b40000c2c1c0416810a050320300145500020500038001280c3d0b003400300100300f582071008030b20041645140b0b0078210081860300722580b42980c0d104c4184a0455040c0e2041d406500003a2003040c1850081c54141219848030035490b0304134110810080286000f8015203840d0031040c0c0c3d0010000044076001000140d00c1d86a403403410b14000c8000124948150601c100c2a0f8203550520061000444c0300e003d80d2580d03600d41c10703403241140d01482182da0b0003071140401d200000c080d401101180e40010540c52071200f160b986d43c0281d0300101c51010200300e01c4901ca841ea805d01380982c600c2c40f48440020402103085a6601045a0283c040949000c401000007030416002e640b0110241041c50512854287e8031244540c4620601180b40e0040c0d092100d141c02c5402c1030420340f0705895000b100862043c46203420302005002e821001d484a810000105040d44914440c825400200c02c4d0b00052206101c02030000d03064050b44454010a0210104002c06502100340c2e40c00c01c0f80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 617900755 1250 617899505 617899543
    0xf06050405130b06030120030f01270e0106050a03150c180303030b1513140a03170309120f0a0905030a0f1202162c01080304060e030106030b0114090c0c 67
    0x142202207401454413504182c040d807003c01c071f286600304000d00503612403841501d8803500d030384e00d07400d078015000103003040b0942d00444084807404e61500d940000852030448070001a1140d52000007c2e00d0a2195209461a08110301031641e2140180209090300e206424140c058424280f0445d10421007448043c0c109961038400345113641d00c1c9042d0070143d0858040054a48002003110b80d2450464071030070f0701448003520b03c407280b0308060344020b007145e0700b00b05c002503d8440e2075071103c01940300a028040c103003c0c008841d0510b4018002401ca20b41065080d180c80cdc00b000c100103041030042790400340c03095000081000c001880b607100080750310f5001c104801c14091201b070030f9150001c803074080070814400315004500321001c00c0c0311600c0d9005490a020910130940e0003864070700421f00034448640c0040006000b080d0013031001d10b1100c90007900000d18070355680c48078074540304e081e001501801d40b501000020391410880c4185c002058011030b0346003034070400d25156076001035100308040b55a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 617902005 1250 617900755 617900761
    0x21210f0e0901080c0402131e29090409030c05010e030912030702030c150705150f06040b1e060c010e100e03160201080a020d051e0702240a021b010f06050405130b 71
    0x42081f51ba40020500518850222083c0d2410500c0e180703e14014201d4004600c40340a1460042c01402584285803c548600d4510754109010261091440075000d115044c650305000503401d124006860381c903e00515103a0509008000300000000c1c3c0d0154158010310103040035a4003c1091503950b4822100b40c9440c6030481c1a140480c0101c50307001d00039000d010001d4110b40d45030b081603072144801130b100b103100d03a444000b08022102c08295807500003100113003c6a04038000410354002c5c900080c43c45061005080d00325081d50641074640d82a50021608091080d8140c06860075010301900510704081001100080b90f00c052040a81000b2030382001c030304042c04a90464085240404040c030680c905181c41d12400b40300800b50500600b01e00d030002e082c0c54808160b210800780810360341007590343c464200000c40400505600720a5500b0030072070000c0c00070040541c05c022103250020030100e0b100003c1600322003480d40014000c1c0e0400c020400011051184070100c181e0212804250b91 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 617903255 1250 617902005 617902027
    0x3040501140903120703090312110c12010f0e07050f090106050f030c0f040b1809100b130801060315050f0f130309031e11040621210f0e0901080c0402 66
    0x140c0c0c0700714100e00311440054174000b4583d010841c1c1c001e883c000c051000c9280ca6080c812154100044603114098202440c400d01c54503014202100341211040003052181140d4805400c407801a240c21295038009441080710342070500c41c40d01c4001c01111042e00341d40c503100d006482c61082c02c0f0104a0300400000203140002d001c0152240044000d0105803580d445e100688000d034041c1640c4550b245c00710311358000c10700c0e1001c100d40c4a0000d003403c14202601d46031142103c1d41000e880420510f59072600411400024451040118041c0092412444811540c0c40c1140c01c00307030403410601c40c044104401e02405201150304241c4020064141000d14281161540c9407600b000b03003d401019507803441c0e0110354105124860194118100154030361003003200700c84e402d11504846080700d907d90740d940400c215460ba982030003034284040402c08503001c4100c1c00c11a17480c40b00426000401004416400311a1f0840440159040700d402e5042c9070700700d80e0351005148042c2c469034001130032800e52 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 617904505 1250 617903255 617903263
    0x40f020a20190b0919240603050d030605090a060302010f3c02010c0c0f08030910020a0203030f060d0309030209150a0909031e1d0a05030a030908010b0303040501140903 74
    0x10b40310a88100714403004914007600d18040543d0110958800d41326035900364000b048a0001c103640c05074489505602d0b040600100c4180c41088072110740d0b45500c0000412418044454030640c60356001550500304410800e2000002d07050b07548840c90080c051006036080203018842001c80d048c226a01007009202c4168104422600003c44200001c080440144400700c90200040c0d90002e001040c0d401d0f0702152400d039194005044244411103403c00f0130171801c01140c1088816054504004413410a0026a030080c040013005901c004100035402d00601d0360351b60019001c540201d4003421a48000b800c0040d14040a8495039000c808204600003051808919000203070038841216911001c000050000c5041039010510400780d482c09408001107003420034841c4d4a40030603130150902c56844041010b89001d400009031900440c850303070100590085903100769901300d4030605000c5c0745400c0d01d90692803580039070310a2109000c6a030700148581c00a96034040441e8440c1c403500002864 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 617905755 1250 617904505 617904523
    0x32505010c0306050a060f050301090230040309090c0f030e2815140112020102031c05180102040b18040b060f04080f1606030c0e091005040f020a20 65
    0x198606005452550b8141d000402204c10858010701703015036807601691078448121044c00041e07401c02c014450141d03240d0103020007504d101c0f10325650170350264600c0e0450f800540c245003103054000400c0304041d441000c0c0c42c041d0903001414072401c03480f100040c3c5004d20030040c6200b17041c0c513034140c104d000c0c804000c40f4000d944401a0901c0524184401c0c1014903a0070505460304a03210480c1138111009000c0c2800f060280e0602c00a168030b400e1340fa406021070b0520490460000700042d170720f4001d451000809900c6c7d0702400141504054140c000c41800034868880607034010b0000300005401c0e44195000d82050150610242050f20001402080d041c42d038652f02500200317aa03c114058034003c4d009541c40d28048443c03d01c02c82e0070840d52450f00000c0e1102d00c2241d0f080500c003041c46a0004422402d0031304201d030f0b203c0082c00004103442d0040b00d40519042c0c4014040003540b6181c01081110b0000240c11480d00e1481d0f0002002c5062a0b00c2000204500c1c240c6950070318000c000080c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 617907005 1250 617905755 617905763
    0x70c09061d15180a061809050a02010c05010f1406270613021c0509070e09070b0c010f09030e03070608060d0b04020105041205060f0c030f1801060f170706110325 71
    0x51503103810410304001708200d000d1b407114034600c0f40d880c3d02001210b01c12941005e400000400042449600440380c254650a0440d042c1d52961002540c041d280d0050070300414201007025028a05001800681c18804580d505615890b01040214040382902c250300300d10107071484450210003081802c06441500003009203189800c01000d80020142c2c4200d000340d2400003514942503603000d58a0420b202516003c00307a4001005c10009001d8003c002c0c40408120030000c6403070030341002c510f03044500d00d01c400c0d004110301088241040c40d0900400c00a41000d04112829042407000700746500d1f01214010483d42c2d00a001c10709580c022000c0c2c90042c0405c50300000c005c8a00c3c507040c1d8131080c05a41e00c1250fa03244101207044d001090003a60b119490090519149a50f0f80420542c1200f04d001d030078019569600000c030305032508080c120080c1c40780407400c01d103910813a849540340103210303400481041a0320620b0350340d5410100880b5000f64080f00c0291034400c183c0504c071209c0e02c0106c2c0040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 617908255 1250 617907005 617907049
    0x5040b010b0c070f090605190b0a2d0e100f020318060412030914060a1e18030b09061005030a240501120507150c1e0503070c09061d15 59
    0x1100009504910187d5000740c40040e40e4442e043d070380824015290240c003c40103018000710448034420b946142c0c03654010044000d0071100e60b040343c6841c4140146041c00104d06813401c02d141d003441c10180f242c0180900c1c00c090701d44203034a0000d4603401a842000c00421442e00e0007040b565400d4190341c083c001011401c5403150f01c500e4084c112a1152040310010111f501d42550185058829a140c1c0c0b8803a884d054452002904c0704595542010f100c0720600000b5045801c101600003040d1010714440d40c905000ca00f001e5145c02d1070100e005109a0310710116090a01041c0c90102d41145c6250f408207842650515049500400c0c2d015400010003c516110000841600c0544590082030050007903d80d44c640b50050755840c00621480400030941c04c1040200150340c00b0a010040808003404058030117840d039425066901c03041064581c0340e00480b00380b00b04041d0b482000010501c540566001256110038004600c000400004841c0e00d1324180c0403640e122610500240b040720650380c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 617909505 1250 617908255 617908259
    0x4020a170d0212130b093f0105070509090403050c0d0e0f032806090807050a0b0f0702100b061e030a0f09080403022403070306051305040b010b0c070f 66
    0x1558600711203020034018480c0030303804040c00c0c0d00c5008480b80a408126a22002400c0928250f00c03a03014403c1903800041c0c5211080b00301144501000900b0006042c4042000802044440c2000d0790703100d00046914101c140502640c0050441c1c10980065603031040303680d07690a0541e4540a40080300b00a0301400c481500c0d40c6a010b515400c4200702250420080320211050658503901024400c21101401143d1400510004050040940301d070b013010034a60a980e551107183e07081044102da256018405403010041c8a00406034400041d0303151864928166400130350340c00d003a007604c0c1100c941d1011117035416211070301100d95541a07c8009020100380002102050f8400c64001e100c0e1440c1145100d141412406030710412904400042d00789030843e0200f005c0100e58001003514525020342d5204284560405148101c0c0d141d10006086403800040c444910304140c400b0850703c1c503100400c4000340409103030318190750350044e1076078032842103050503440d1886039000742489184034540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 617910755 1250 617909505 617909549
    0xe0a2616030b10060201020c0703080f1e0c1e06070305040611070b0702010608010c1403130c0306291c1b030605060f040c05070b040201030b12030c010515030c0904020a 74
    0x20307400f81c1d48030845510401d035101401c03407c0f4060002656240d4202c40c1081001c075003a500640001d860000c0c015280151001d55140746108102c1c411205100200300c2c00081501401924401107024269080d50400c2c0c0b804030392240802001d40082c0340c0da42000c202801501ea210b613140d0599815402e13070300c048504007601d61400440341040151700301b48001c1074000040c080c212110543c0d440c1e0807a00e0003a0b0028840a820044c070202c1d02c40004951a80030545001000005501442000419100510f0512003112441340c0c48820307142c0580010300540c8800c2c0c13810402030302e444e40344054201c0c0741c0342c410203440900b05140308000380800c0200030b20102c0e6020500521301211340c0d0a80030030310401d0200341c8480d80300303203004180c081c04240f01240039402c7c0203500520502d400240840e02500080110126022035003441d80f010446c003854a000348070780e94101c812580188020024800081d030348858070070b40c4c28000c00071900030500b103441c0c00002d6409003641c50b10f81e5004020000d030b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 617912005 1250 617910755 617910773
    0x22080f03060301050106020712020111120307050415020105010b07060e0a0503030712140912180604030609050120040909060e0d030c140406020d210507030209010e0a261603 76
    0xd15602c0303035103098000a403c600000780c0400300e51100100400000c0250010b45a0002c0d40207070344114010302070312909a030000001188a5030950b01e485440d14108503180c640c00000311044e5055a15140c0140110030801050310403841e4801e00102d0540c114521150038182181d100611511001c400e1140141d000400d100705002030050401c40802c40d4080400701d55001c0c0c0e4009113540164140054a2000e0340040800d0400c0303811110222507100c1c086955680300f036105035490340e600e100410400c10203026850b010005c0f1404000100c0d1350a0420b03040c3e1089200394a00b0b10380e10f0103c4002c00450342c210460506116059070a4420840005000780608854400008031310741b40c0500719401d5130741900c080d00c0c050341c0102907034211040b013a6040020080d2000760340c440110080181e0800c4e01596109601a80c1d01507107400900c000901610182c407189881404400814800310070b07012030302c160755820b05040e16807000c81d800d1b500d42003070603030b0004128245000f02e0101c14020300207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 617913255 1250 617912005 617912011
    0xb15031209031c120e0604110d0c03290703093311070c050d1208070e120d080c0408030306090a0204050312091302090f011421090c010906020622080f03 67
    0x400a201001c030039010186c0b43c0c00708641c02405088001c02007409401c01c2c081d1464a03910409240d8441500c0e52078500b03010150505080580b031030070510210305044068003540150303480c01c09205100195aa4045003034408801001412000060b200758002066203c00c0c0d0250f1182c2c200080060408c26a08590103404282e905403210400010541040350b44940b000d50881c25900b004d048201d0f007125605800f41c5140300300495110074481c0350b80c9040c0300c0842c174842c2d40018644401002c901504404000700608668001072104022048004c02201e074407d5045480c0103450341c2c0d941000c0001d0003681c10176a05403207100044002402c0103002007001c1202110140c052000384a882400d0384140c0300d03403036048842600401100e5001f0a0100a140e02410289080800303c10466401c50710900c100c2c500b050882c07061004050092142a184c52420303c0d203100b1041c14410003943d1200d0182c25248840d41c04103528071012407002e14006111b038402c10744c40da200e28000d0001055002a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 617914505 1250 617913255 617913287
    0x40e150d11120c10020c12063106021606050609070207090b030304090c11010506060304020a03020607060f1a012006010b0a0c201c020102060c07050703020301050c03040b15031209031c 81
    0x550300c2c14064001c00141c0030b200e080341003901c5411111027915091030010028003e07004030384202520000a2160014100b0300c10f105031580820783c0f1b50309010b030030303603002910460088644800b030002c6241d003c40c0b05015a6001032000c1100e04000c000b00385107218690000c800300b0314003031114102c60350190980010031151802071143e034540104002c681e220945009602401c050302c108010304209014001890103039800003a1042c0031100c1409450948107000030000d29107008007510741c1c0141191200c01040411040312080d503500156403010306008035544800c0100f41e42c2c0c405032041c0ca00300c3c0e03416404941d26210b40814442c159100201c100f02c0d512541181c1d100b40c0d5480090030a03802d80e990140c2c0203100303580700c5034207808840d031100005807564003620300d000c000f6840034018070b800741d20880c110702d650386410709041000701070143c001851603082c2810300006540020b019243c103c0703950915030356204d2580010b441c0000c880f2006120801000341c00a14541200b5048140044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 617915755 1250 617914505 617914519
    0xc080f06070906020a0209151f030c08040b0406201c0e0f071406070c0e01051206070f050307110d0804060f09150917040e150d11120c10020c 62
    0x3000819640c02c241801004016030244034040094030341110b0713403500504040048007404458401103201c0c038180380304840d01c00c1e03080c074010406181d2503c41ea0141140c640f50006ea981855582d00040e494050000340c01280c490304003c070103908800d02c0c0040c14100c82c080c15540d080024500c105945000003522540380742120600410401241c42d0f50050158070140901c1d504240820a440b03200f141e03810b0300070000f40711880000d40c3e01e141c3d21003c0d228640030715903250702d454104510068200f003c0840e43d0001410301c075005030418040c3d094002e007404d000b9100d58960710b080b03840404600040d03420703101e010340c0c9084403034000e1100c07405540114400e00c44a418840c1340c500380e42c50070703500034030301038000031070015110b81540302000c442c0c030629501d500040c8105510019803c0303034010550711250003040c84158130500c0c1d80b070740440d541039601a1a01074652140320b40000a9180b80d8007400d0b1400700244039817414001c01c640b50310002c21128480d0003140b0000c0d80d501000c1d1900e801602 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 617917005 1250 617915755 617915761
    0x23601030b0c090102251e0509010b07080703230703081005091b0f090a0f09150302090622060f030b09011802010c0309050d08030f07140a0f0c0c080f06 67
    0x7072200c0488030243c40c1a00100041d84415040c0c0000504070700742e03040c0c012040300c00801d00c0008484060180200d41c0e075004011070518007007117521310040e48024420301080000c98000f910810580303103041c1d0542451030507804440c40c6902d2410009944000581e00002c1352020140c0128405004001d1003800c401016202e4080c8495034000341c4800103201d0003480700d034500215110003080e01044440019043c0311030840030408003807480d0005081d4200f800d00070f2080441510405a2503400918003a088900e07540200381d04a0000c1c115900a4103468800060101c1b00403006c5081d02c0070210400403180d40e8101402420703139500049804103021000f01d0001d11050040089441d11b0320809442c00c1e40d254015500d101541f0000c50902c8a421400515580d0300c0200344551401403994580e07900c2d081e060542c44440c010050414000507402040d40d0251980581e8120001e03801c0489080c0011501624100c0c80180001c0100300100307404122500d0220302c582100341048202c44040cac03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 617918255 1250 617917005 617917021
    0x106020114040c090e120301060e19140d110307030501060515340614180d0206010504022b090311070602030d0c2109020307120b04023601030b 63
    0x203030142d4000c0c0c0b010b4018201480003442c9580070350b6041c10001304485031a90804407000e01c94109070301c15004910802000740d01d6040007445100b03180441c0c450044018240114184400240c021990041d091400f08c3d0040050031004000250030081c12542d68644d0380c90070f20f0290480d4010301c3d0050381d114100c4142c5203c20002c0e10380784d01d25082c074900000040c9034203104402c800010101384441100200021a50b80d100b10306090144140b0b85809103480c840c10740080801e600c2c00450b950144182010041c1c0c080795243c1555030403280940c1e602c940340b4055080c18489400009900c401c110501e40c500c0075684000d561038400c0e180c09050000e614109610341350644a4000940c20400400f4030464145c0d0100d0110082402d207248142e0030054002c612890301c0c0141e080c85656a00e02c0415454200704400c02841c58440701c18480c03030a940d56003424500500000d00680e82c1d0004004070080312130b0021048040983c45c46c81c100f10300b0241c400484001c0c842a04c900c1e02010216001d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 617919505 1250 617918255 617918291
    0x216110406121203020702180403020d05180d0201020f0d0302090420030109050403020712050d020610050a030807080c03030f100803090114070c050a09060e0609060a050d0c09090b01060201 83
    0x641000c000c8502d03030a402d4540303aa460030500d840c00b040550030405800160394101c22081d1600d54110007504078038061a01030b18120704521403005012050141400b04c400711100c1240c02c582c1641c813600c0410700781c40140e1070403039880e0388074581d4090500790b5080a0303032603406040b0040f0300321003e00141071b07201c07205010042011900c1500800802c01440040419042181c10902c00d00c100e0f028595202c000d0200d106024504840341c0c0c101c0404030b5280b5070704104040d000b501c007180005034a0300d800f0010380400300c503120040c1400c401041c24014016000305513958522503c09880d601c1ca0902d03100c1448402c221280c5e88212002e0a001c45c4152000055856182e0103840e000c24100350310a07500c5143d088000203c550072a80c010119450b1941d00110000300460403001c40c9042c142610144c484000a14460141c10100108115640c03841100340c00c0703640070f03210b0301212161303402e0800048819420408429050854480800c440c10403c64100e03102540200b00d5401c00c1348411010b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 617920755 1250 617919505 617919509
    0x1032a1710030b0f1e0106050d050f091e030c060c0301061404031a0a0b10081819020d0c0905040302030418021806160203122d0d0b0a03060216110406 66
    0x80043e00c20006001c00034484011500b1807100079110508000c074120551010a00341c0000001a9001c10aa440c003100c50042030f41104500030f44142c146416040d46545025039400e404507100c800580708850001442120301440c5d500040e41c0b040c0c501a0b0304940607620070301c40e88000805000603081c64480c1c0b0001c2e2820b0740e034018001040201d0146442a1288000d005040d00c541e031140040d269940d040050054038407542c0b18403000e845c24400030180201004100c512980181d41d00403103208017540683c0070305904980c3d40341c0780070703090610101802054222568092400080c042459000800f60040742c005141205840a610000b201179018282150011900c010695016442d1800c081c1c03c0d0740c140b007000c0250889031900040d103011019055841d42203400106501c002ca0302c54010011800c008404120280c940b80707030b491051040510400035255504503422280d03072003250220003550044825516109112541000000d22803411184101c0d41c003600c40050505004040c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 617922005 1250 617920755 617920763
    0x1d090303040c05010e0114120a0b100905060d2726091203090d0f060e030a080f09150a05070314100303030b03030d090c15030b060901032a171003 64
    0x1842c2032800b401902c52216165689040c0640070181d1001580706401401480c2d5460345d10302c17120b0614000401c21103180d625003174003410b0100d611240b1160001611390031144159036043ea138110210180307004111581050729003d04100d8039200140e03812000d840114003400c001c840100811480341209807200b512103030984814840c000341480d0012070906440e0b00c0300c0030750345000091000035079144c5220504403040000350815801b03008c040d00c901c00081c540301008501d01150312a000e014250004c225280445d142030015440e014148180c40c20a0305a201d100100e04041c48000040c00044449400191a00d820865540140c0b04c5090280c0d224402441155046440c220b01419082125580500c01001124036070764051040440342406071381010940b90800004210030344041010310101401c040e6264166516202250007980c3c027400d00090414044c084120941c50085d00050301250500074602015080b94012032440070342c1c148410659170700141030410340700c14000070b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 617923255 1250 617922005 617922023
    0x7050408010c1704030e2803060f0203010807032306070f022103010611070806040c03050f1501150e120f010b0303030112080a020304121a0604020304050a0602030705070206041d09030304 82
    0x41c0100780100d800e820744100290200000c0081c5d0440c8400138104000030305034800407e031007003007449494030500c840d01000800951545d451b080d00f0f0f43d46d6041c0e81c00040e05001c84031840d5036050451656544228080b00180c0d2030504c1c5c500300240c5001f0080e4405400b40c0100407241450001d45522954112030070361507a825a420040c089542c50b981004407192481380a00c00700342000d08000451003140720300c3d074000e121810b52404900305001c16001b0541c0358040c112180070035508484842c15103c400341001c0c2d5018081c24101c3e401e0b07a000c014903400148071184003101d42c002003001c1c10b9040042e40240b241c151010289562480240700301d034802070f094102c06001541c03080080c10910281c0c81100c5c02c0644610254000e10640c01085a4070b505590715485002116079003182c0c00780c41142d0441c01c45ca021f46481d5141c00e0403100007000b5a0380000000c01c0d0078003071410790300f89540240c080b9460302e403100d0445049a58240c845402482d1103000181440b1001040340e00c100d80c070009034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 617924505 1250 617923255 617923261
    0x30604030f0309320f0c040c0e040510090b1002060a0203060135070801060f0e01020709020408060f060d05031806070b0a1e0b0117180607050408010c17 67
    0x112088668403001c002010349030700b02034010820500400d40c1c90601d03480101c1103190324000c4407991402042030404190803020680c2181900450002c4039104280c0f004101c4039030f040c0013111340f0b00c090482c042d401407515040c070481240c28600c0c0301c1130743d580c1c0070200914034110b02080107145000c6101c50050380300c980012210701d016006160080380c103040c14080151603000e91079460349006103401e41c65603081d810b00140c0030b0b203000031500200d00d81400ca0055050010090401494400460501c4844450f0f001c3d40e074030800c00c410090503070690031515039480f002102d41741d120a840300c2c540b0007803000201d400b81c0b40c010000f62040c1e42c804001c2d49040303840c140b80165040c0e080307000c5500c49414042c1e030707010403c0c080c00c0912403c02d1120014282c0300f5501d04c00e02c15581401c200340d103146082d0303095003540d130404003006280074860a0703000c07907603075500e0007800b075900c0030f1642d08242c011003041c80365254002024105840001c070081c0114203c4400888400c585a9804d605004a01c0d000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 617925755 1250 617924505 617924507
    0xd05031303050706090b0705070302060109091226010b0706050c0a1e0201231816180902030d02010203010e1308030708180604051c03140a0b1f02030913090203060403 73
    0x80515610414000c60b42c01c40b06c0e103e041202d075084410002050000075820205a41440714502400e403080003088904481d4503980400b2034891160700c280007007420380041078000c1d10340c1c0da40706207800010007001b580c40e0000401181c000400846041d4100350204001d40075810589086059a41d14407120000c41540001020040c04580055542e10940883c1d0001000b030440c02080c00b0399075001450500007003100304104108070003110303070300522104800c1442406512045814010942d0203081d1101c4020000304140203000754540b10701c65010305800c1d01034010b94100ca100b13400011140d540c0c100a5032425411000040a00c901080002d82e0607004049494109050015010307070744564440c540e2800c88181ca0a4611340e0044050400858298020701980891403034241f00b00360210b205101c51410182c500301029031110901c0c03842e0388480403004110486801c1d907800444804402070b440364400c1c0c0b2100d00030b1034908108a007155090064140c0580e0180080c00c40f41e030385841c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 617927005 1250 617925755 617925757
    0x90f01030207140a0b01051e01080f0604060e1f06020d02070b0d02091306080118030e0d11090f0a050a4811061f0315060b12090d0503130305 62
    0x2c421540c402041c0252903450f4410044602e43c1d61082c484560a07505140403c0720148000e154191000100019103010343d03806020f45030007120819a40ca503e880d5080003901910858010803030f0742c1d01120410064000050310010300d0040900024501501ca6404988a030b07400001c00003d68018882040400176000045c460401c500d0b500608202490000882800076500392410300c58903400d09010300d030700a00c41c0c110f8407a00c440c0d0035114442c075960080c240b0309180c60000d200b40042d4101d0804d01480101d107000b0b80760300a0602641e0325082c031040c00c582d4070584510f0300c0c26140000180d0740500910540c000e050b21607116405007224100d00c000003e04010241d03803244401480e0f01511301604044045421035603c81082040014040d5441c0030402004094200c0c007200342c0f0800c441c0c0002041054031740040050103190850045040a01034550101d82c40c11b1000402c2d4520014020704035008581607419500d490880c207100311468041613407407401c026031440a00c0700290140c8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 617928255 1250 617927005 617927017
    0xa080406020d0c0309050c0406060e0402090402040e040b04140a0807080d0603140c15071703130c06030501150c08090d2d14150109020d020c06070221090f010302 71
    0xd002616202620b180c1034155402c0036060000710352515070380810040305110284a40005403402c000c02440d0941c000c0002c880b094041d4041c5a001600480036240c42d012100580035011340b00049040a00c1d14002c003032800c40d001c0d10303c2055840c9900308104003003540152103070400991410229280c03512011540311184642c0d5095a030b000000020720101011404079a030240980308090b0400240b00c40e8950318000030a160001308601e81c00511040c071003800303511000ca101504c0740d445e81c0380e8080d48419110003500d02c1e03041a100140203075140d00500d0580385ca000700441203140d5104140c40070303000c1140007490101c080c00001c540c0d003406c103c4003141500404e09122044a83c0780d90100d2880c80e0780640620001508c4508140000c085080003000700b500b00501003600117501c0706584100600a40c9100786d000600c0c208100074a4040d02d2f18503140b075042d96120b0078040e00195481101d0150303c1c0440307080020101100208030107560441402030504c1c00c00380b1802004600940c465 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 617929505 1250 617928255 617928263
    0xc030412020f0708100b040b0303040618090504060b0109080303071d03070b0d02030f010602030703080604180503161e031b230a231905030405130207120806060a0804 73
    0x220507104501c1c04104074800080c2104805014444017000e03446054a0001c0e1419010301e080c1100c000080d140081110100c1d000c1345000d90034803d41090b80a0040d00c0e90703000c415130609100501c03023404207960044101c84002d03281c0640c2142d503007610a40b640803c0303031100c012036a8803104c003a40300c01692a01405000040a0b280c409031070f0b10000100e40c000001d402c0f00c4c15070120400c4000c0ea40760061901500050004504041c210355004100050013481d4600a58644070f6070703c46240d483d054120080d07808001e8a84a014008600310314000806007a18406100f03240151038200c01c4014102e100e80568408030703050b150300b030040c000888408084900200320034090001083c1740e02000c5100030b40001800e040b0040c0d0804041441200d502d00660001d8940c090100d020001200240a04801205088803c480c28030505600483d4020390708060464001d01d00f000e00c0d0750003003418511400c038040540011000840d040d00c2e0407600260806d20400c50180ca40d40076002455100b40305d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 617930755 1250 617929505 617929513
    0x60d02190b0a09051c02150c0c1216060305061c0f050115030b100612090c0b0a021e0d0801031502210a0e0609030a0c02120303010f15080c03041202 65
    0x75604251980d68007542c00348000400320740041c006441c00b0b00c5010190640d03943c0900c40410280c00083e00800c005007900813210000820491a0409000200040310300078071044003a80c4400440b525840580300d0b4807091149200b020a2850191081500412014140c03075100bd60000081200150440c4103407075200342e2b0701e0f014000032000d01920300c0741c0d406c0e01801c4100702d01d03614080d401c00c50041c01aa14410b1060014000564481e20903000e0140810010a01c500700c0c1c00c0540010001390411400741000040058000340c00041c000c001d110300001d0020500a9440c60036200c0000c04c1c60341b400208580010404281d00000b0001e9600c003a04d801450000400036040600d9801040b281c4a852103404020710bc40045c4540e0710000300d0314028003103c0c945100f080d0703140d206030522101840100e0044c402591241c00c4208000341d000412291791707503158500300600800910488040c40300d80c2055511162217215624002e0400320459410354459a903040504034504101c1c03401c600c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 617932005 1250 617930755 617930759
    0xc0305040314071b0b09011209050a11180f090706090b040e06011421070206061503070c14060114122d0307120216060c151e020c070608060d0219 64
    0x4203444c1640e0041410002c030350354a060f0030001500105040c000d400500d803a114000c000318101049084000b80d028030b244902c010407900040b80c001501d10f030100c81421110401441541412806003e0404001203c101c1540c903542200d6010082c003440c400381e0000d1108211001c0c5105129412640504103410150317500c0d117403040315400c00800d41a2106000700c06405442d41031400c03580001d131074130140142d8944200440c2d800d40705c2d05510605072100000041e400340c852058840355036402903050032143e076019a00d41d503070842070048003040610584982d20b41d1901d4003020381e884030303800c014101c0c101440c181c1c3c2d404441d211400c60070504400c008203a68401c184000d01205105025010849800c03030802454180c0380680f0f0300c01c0580642d0244460703600800399a0300d80d079020490b03a0522141c1491b12018007024420351100c125010100c03078008400360060824103401c00c0481700030981c0d45c40102c0d0748000c2070300e1240d084005000c030301000d41001a41c00940c0c202c0905002660380e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 617933255 1250 617932005 617932043
    0x6121c05071203090242090d060509060a0c0212030a061212031b020304090506060d09050706080c03160f0311040605070b060904120c1b090c030c030504031407 70
    0x64030001d101000035034407820001146418040c00340020000d842e06c41a00f8244190012649003914808903035200c1001c43e0f004a102c41700c01c0320407003e005044480b143c03002d031501402805059504841a00414000424181032440b40110f1180139900605201070328000e5400c6a0f44068258801d4a4560070085450a1a01401c14003d0b201c0d03550901c2c50400d13004010216042411101555200840002109075000080d02e090344c0021100003011b0300c0c0c4e00c0004055102d02071208a10358103025682d03040c400d002c204101211066120001c0d10395a0803180300c8544012508040c060826070808407500380300c3c00c1d098081c100340e41000120400e400c84101e20640240d8080b000003980041c41d074081200d00d80303000d5000001912030340c2c50b03030070a0795401304650980100b40d020441c8444480c0c061001a090400160401507150340019441d090080301a1024680c80700c0404c0c00c041d21f000c20745100b84203a512030713078050f0b4441060b80080030710200d0a0313201510079540c06c0d100c856898115 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 617934505 1250 617933255 617933273
    0x5070b07090b04031505090c030619020904110712020303091c0521090c0301060317130b07060b0f120601090c0905130e060c040b0301090903030905061e06121c0507 72
    0x1130f600641881c0d90a1804290711415560b00809880890b00000054055510001070040d003200f03030440325410402d071030f52100000780950b0041c0340d4046d042540364405003201000400c081d90150143e07290304403c1041c142d90b00c1c401942e80903040c0d8080c840700a104c02c83e11034401d000040e03510304036150030f81c10b650300c407020030703008000c0c60a10b8145014815008030070009040605400d0340240300241ca182c82e482c1c0d4003402d110105c0b2601e4000a545054480c0d8541144068016240143d031552918100303034000381200ca040a00030400070400d080185089034030550681624401010380ba0700703002400c030107049444101400d1041120703000c14281e030b6580d46402100b4441e031000480e41c81c0d405000c0c3c60326002030032140f420802080f0901c600007102c8116410f481401070049440450303464128024080800094050300400341407010401c80b04a85404000005807140619201c4000304940c00082c030400c944668400410f40c40c142002040d950310000960a010b401e0107001c4e00c0b082d182c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 617935755 1250 617934505 617934509
    0x5010f060e06030d0215060303041203020c0117010302090a09021c14301c020a2601080c12010e031201150c020f28080d08010803070305070b07090b04 66
    0x84903100d00091141c0e070100316403030b507202c1d80c110010040f80030207920180d1100090783d25014006181030000d121a14108101c0c0c0c020680d01045003203004003420000d440707442c8160f0316800500511340d024841c840c1c50424038180c980041080343c2c0c3c0d44410340040d00400003d0030881c0c0000c5140542d100342c8480740e04140600d4007643c0d83d004c00300c510411860501c0c001c056100004880c500740c0c032034408814000305801c164400078042e580c050280e070031740c16003004107450048140001480300450754495000c0d04280b80c003840c5101513040c004480f151511090143d2274840e80000d80880b0a071500c0d40d9291140d1103d6000041c40304000c0641d1801c580c000d428035007a20990b1001000b1ba00340031510607284200528040c1c020342041c0c2e00003010101c0320425584200c4101040c0c0c1042500c1098492907a0850080440e089964100035602c07030340017a400601240b040c0d000010740354008011904019415660545000f0710340e60760001c44100a0914010814001c8000c60030390451001440 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 617937005 1250 617935755 617935781
    0x2041e0c02060c030108190c181b0f121802030a030e091303050307030207031b03180509040c09051801150e0117060f06010e06120403180e06010c030c0501 68
    0x152403100400c040d14001c0064100c04455804000400044a0208580f11010907080c4241c003500b101d030400156548140d0845d10b01809018100c44000d01103520114542407861803da103a03003400b1005403003102054224101181c41c0b140304103051502d80d8403102074100c540d45070211010154020a1402c01201d6085010500410003401c0341d14003540015841060b0881250110081d654018028080544000c09050300400c00b50101400b41406088011408104902c107a03076038203000f42601041204490a000011310120711410444401842582c002c0001c4505900d4261494014400184030100750b107218401904082402e01504082840304d001081c40181032080da130391521810790141c1c04001c40c02c4a4013050b42c034042034107507010710382c0c04143e03803141d440c18010b94140400b01c0307409a02c101c0010342e81b446880340c4501d66004501071380d160b140e6803140082c103484101c258050485801d42181c0018031540c130a444012405100c0e2a04404800322075031050f00b960540c0d4a044 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 617938255 1250 617937005 617937011
    0x70e0a0b010809030310060c0c15080a050a02040509010510090b070b01080c01210510050a060206090d0801050310050604020702061206130c050d1104150f110111040501030902041e 79
    0x1100d0380d070748080060b811500c128059881c0d4141401e69072031141d000c1c803a0300180a0000a0784042c00301d43c40040d00180342c05405035846510300030000300070003801c075409aa5903141c0030200304001c090340300751015118058007410842e424401000508032100c12201308120803084045400204c51014241e25807041228610f25418241e032541010341c00a800c41c10001350110700484140c03468440c6240b0800ca18002510b5251500062820219900065084140b0340c0e00080c1056001030710030b21801c0181c05898406111542c202d03907010082c440c1d07035899031000303000c04074054031540001d40201c8004e000601d00342f80c41e808210303140c00c01504c441c1d00078501000c1140c90705000390740f11907150a4640801c080090640d0140050080070039140000765500034a45500c40f81d0700460307002e0268024200114100c5120050401d032900020a00142451a02d5107024005003c0d081d003039a14504940d0500e0300b070400440003080400003c0e6842030315491502100e9808084000b00c504e2406004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 617939505 1250 617938255 617938271
    0x1906140904020c2e0b010504030201030209040b0301020a050c01140c09100e041d010b180a020c0a080f0403020a0f0f03030302030603161401020c0a03170c0a0507081c030e0607030b03070e0a 83
    0x4402450113012400099041072946030702a80e000f41150156542400d005880e03295840205000740302d2026610740541c40041c50321111a0443c000e400e92030743c0c460003031102070300c0701151404125081d101005045008e000400305883e04480d409218501e40c5007802c1006076020000c0c0560345504940d60798000c181d624240500340038041d503004140c00741c03906464903440806c94080e00340010301c40f20081d540441d42420f0100d00340600c014140d04128041e4490b180300c080100c0700da115210807481020344501c00102c000541091104988452403816001c92858906501a51005118507494040d0141006034202c04031054400f520340ca05c0d02b80c00340440d060000e032030100100e08040c1f060242e16020000511000c1900c043c00e10030008040e140d0f80e40c2d582c11854070b51000c400602c0e07802032000109282000081615140c100390040c00c0c0c0394800c240d000d6080310a02c901c8544a0b41214002501c40390198000607550b11000c0c00b1030303040b955117201c450902c2c1800e43d6002e28480e120268 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 617940755 1250 617939505 617939563
    0xd150e010e13030e0409061a09060d0b0406020a0c050d020d08070201020405060d0c03060e01180c0e010e090403020c061314030316110f0a03030507021906140904020c 73
    0x80c0500031068148140b0308101d203100d03030b004007104401800c00100d06140909515070303400c40d0000d26070010003802030b5000d50006558294440302c2c400c3c020280e0100107980e600e4401d0008038455000070034114243c50310307160b1202a51003200350b2010b100a07a0f10410000b5010404030020a07804c0e80074140307110f9880f000a1808102502ca44116030045c0000c0c0150b903149401c540d080545100d0000310b02054040680203045039a010ba03180420724400019a10100a1030104420103c80204044901020181e43e9000d21803042c0740003d0350102d0f01c0381a42045032106070010701038012141d41417100d5002850301c2d0700c182100810325900020400242014281c0401035450440280d030515801290181d80d0307a034406000b601c40303050701218004903211600049510903003d8000004503032281005069548028022030140309041c0d04c11031440c466120f1401070b240103a49444c00c620134021581d80300d401101c44241d2195081000c00346001040000c0c41138000c1c14800308034083d404000f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 617942005 1250 617940755 617940779
    0x101503020d0615020309120111040f0914040c0308280e011b03022d0102040f05240d020c0114040515011a0904020c1908031b12010b0702060d15 63
    0x10001101046240f1407201558011080e140720107803c1c5d40c0c034042407600448550140c4559850440010303800103004c28080c2c481d00c51003080d601883d0b828001c2e0201c2120030103160804070340280a0701070121050000031038038402418503944003002c200c481030500c0061084000c071483d03132070080386c141d040d00d0489503040b1915040d0714980720350301107000e001c1d40c0b070280d02d07151306205122003036914811070700d5000240f00510701c0d055120340085480f69100c05011030301004038080e03144158041a4408170266424500d406500c0500c050203042c80101042403020350071458010f02ca65494406004140240c0f1089903c034038003d10080c00c2a52505d2900c0300a0401038204a40901005c01c07400089074103081110f4280780705480040e516842039030000c2c142140007c0b03050941c045801f020302800000d02c091030054110102540d990180c00c082c0c00f645100d42213021800c0640003004125840d041c4026140903400039001a1415a141c41007000300d0311095007941c0b400e0042c1ca400d00400503128 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 617943255 1250 617942005 617942009
    0x12610080d08150402072604091a180a0b040212100506030907060825020c0102060a060302030601231305150a27060b27090f0c03101503020d06 63
    0xc1001500b50409440c80b4111032a2208410b00454001500074100180d401118420900308a50031310803420681034a4020b5100e8882c082840d4106407130701e4801512560100b039110f2005042d1070901541d00556494800001c02050b40c40c0d40d100b10b8511389440741d00003480d0340c0b0960301034905149400d10780130354006080d400180c06400e041c4200304144a00040d40400c0d2500742c201300a265031030300004001030758860204040003210400f041002500041c3c4034102030707000d07020f07103c036541d4170482c0d1000c40300c0500c8007a60550000c0010003401c810440380303051400301c102da460180b004010201c0c100750b0b10741d900c1e515813994800030040602040300c5140807803001100d07888090703441c1400c03910b0000120040201280c0003201360007400c045650215004040d000f41d115203890000c2c20080000c0c000d1071180c042e00011503d20f02141c43d00d01c11407841144c11400010745911907010107142d42d003004111800d500f424190103e0ac0395400380061003052903556000d65035040070321100c0203840c41a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 617944505 1250 617943255 617943257
    0x4030212060403050301091808120f060306131b1e0602010c08010506090405130c0602010606020618150a0204180f1404020f04020d0b0a030c031b05060405012610080d 73
    0x2d020009074004122411100880404121086c030740003100154510000010200315000500c0107042c03808004851040540c0040c80383c032a59900c0c14180c41d1207041380c5284030100564010340000b4001c01e850001e030728401420241e66610b99480c420b180300091420340d94000307000002c04c007880e4240611040c000151600100300d524001c0811003600512056178804c5440f200003e01b290b01d5402070b040f44503002115261000c0d43c848001c0c2c02040140502340040c0561000030ba00304072904007032014429200000c3c480d00d011404a004544406400545070740e13020400095000d11800540000c042603a10001d0413121070342c03850702100c0204440d030240311014810440542d440e45004603a041050310003594684034409900d004014a5a40c1c5901000700076000c010310000780200001c0d648030355010414824660310b00d000c035402610400350310602c108814030480d44502070440104500f54036a1010824021441e40710140c101d41003e015040360404004149040101d00c00c1c545203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 617945755 1250 617944505 617944513
    0x12011203090e040317010314070b09030c040504020604080105190c0e0a050603070e030f03030f0709030c031104090503030901050402192d0e01140102010c030c020d0807030f020f04030212 82
    0x10a50300078061400038419101c0700e030309000000c1c0516029404203d400050038941c0b1a556840f45082401880c01e00702540390392042c0c1402054481e0308501b101c0c2445001001805413041880411025040c0200700b00c0e008002404000b41c988024024103008416102d012042440c510003800210b4000460680c01c105e00e04805598a45075102c4d204242c5e907064482e0340c0d03a9541c510f0140c8209861044645c0c01d845041400850312102102075409a00c0041006000d0b072110315003121099054000a800200d41400030000142c140c07e09040d03042000d440801d221503161500c0d4150381044490240760394450301004110710b01100b21011680b0890f102c036216606000c01c0b0100c0c1c0c0c44100010180d0040b00c2412080c2240b005a80802030511a1150142d50707101d08002d080c0d007426014140c050b41c00e0002459006019005140d406000c0c0d034020b080c04440c0d920100e40c80c141c00350181c401e059440eaa05006280c0e2400280386062260646550312851481805400000c21182070b41c00e802c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 617947005 1250 617945755 617945789
    0x21804140a06090515070512070e0310090210050405100806030a060504030206061504270209030f071d070f080711070b0901020f0d08011e090c03060503010f0e0303180715051201 78
    0x28100c0300b51110300c0d85231040120710381c0c1c45a4055500400c00304038541d00d8400c02503a904400080c1d00300e40c500328801d42e02600101c3c1105400d41e428041c0d4010103074031424a0001000c413600c80e4a0070750f4410343c001c040320030040058803001d00f103c50a40c1d003600103801940070072420b030030102000160b075144900158505440d064480b1010a03400340c2c45004046900081541654aa01500c10b40c1e28014240d03001600340385420340c3e4881d1a88500404d071500b806a0b00c20031000070798841e2040d03c181d00c59002e940d403800003c442c40b0000030110000d10034200000e00200c8400c00c408009030840c0148290f50f107807000000391428940100c02941070740325011100a099001d01c00c241100c030640381042550002c82c5010803007a6042c0c010844480c82c02c000b0490301d99250300042c040b01c405800030481c40038550040026140304059480103940300308086540020f060084003141e803101000c0c0c501c200e0312040741c01c40c42041814028009200460038402c0c40c00c64070b400a00600c0c0085d1408400d0b6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 617948255 1250 617947005 617947007
    0x120614040816020a0302090f060901060201060506180d0b0901061404020705190201110d0306090b0103090215180604080c041401120f0602091002070f060507021804140a0609051507 79
    0x110403a45520054418050300302c046440c1c0594404c003441d40140209500d02d818043c04840110441d4224468078503000001895030041c410802035900c040c251928288110b01d10f01c0041d9402031210390088050910140401c000c00c12140c01012110300100d907086c035051800f03208640c00440c6910031032041200f800001e80c0001c0c0c1160048250244010006441c0010b07600800c2a8115401c1400b40c00080540d403541540304105684500f14100b01004030b1200450448025840080d00305030f80d2900152048451405403030f00350704101c200d084100b4450081401030300698803286c030660001044101074545802919602045c005074050950300d007222000301e4248520002c0d1408400340d100500f03008158040f1040c4880113880c0402030034800c81c000390f039044607105501c8820046034000c902c4c24032820490701481c1c7c0040214074440c10724003000c800e650000d0803c440307001d041e0081d200c0362035040c88140c0f04140118400151b030200e40c2029400c040300510031078000003822040080309 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 617949505 1250 617948255 617948257
    0x130b0112021c11160b0105011e08070c141209090c160b0c0d09110a0b030106050a18030c12060b0418060506190b0a11070503030a0c03020102070c1206140408 69
    0x44180c8201081c0729801540d0041244944024180881c06440c4e00f001409000808141282c0f820399442c14003206011400c0740b81c0711070401200005107410045030725070f0b204007002c41005d4000c20080c01d030000200703000b52801580074001030f40d443d000701d5007920601d40300000350351081700814018580b140780d481e042040034280d0030041048140300701040c0744003114000d680544040e480c0c1000501d011f0305082d5004003050a58a00c13505101d680800c46d074400074103603412034625850b66030414004250aa0390444614031644080001c1140040424403c0d02c2020040101204100200b00b890038440d003035820f42d4200501840c10070203d401103138110b40d4040c0e8842c0d049840021075450b0400083c000103995100300c41c0180040001003045400c0070010a10515940c8078410045040c00d000c80c0c44102510481e641a04107000603101c580c007603c2c109480920a200041c03428a0603900c07180c0c0801c03240c11603050200d0301240e060821115200700981c0001d501802403d40c5010740d100115 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 617950755 1250 617949505 617949547
    0x21020604050904210c1110140a03020d020d1508030306010801030201050903010b04050103141908030c031b2205041a0f032109030105060108040803040818130b011202 73
    0x6480c52400281842040c0071942c2640c404d10b010368011600c4c602c0c0080085044410540308165502640c00f901d2400514800004045443e180e20081c2c0c2d03a800341035540c1103136040409164007000800c10724103d500c000c00e078000300707918002032042c002c0c40d01c00c02c0d100e03254225940b103500800074040141e81020510b81101e5091806a542c0c642110200c0d001d00a900300654000b41800000700030132050350201c00c203002001c030484408041c02e1400038054408008064501c110400124112003813080081d9132180425800c0300c3c10a041c6c0d0b54030341050348001d82d66000902c03a04d41d07c00e088101c0740b09890090200302e50600c43c0c8003850307000134005010041d1440c414011481072031000d88040c8035002d0300802d030301030021001e4260003204066600843c1200e20039440c000004101c0c0d8015840c140c011908101d00905580d01d0755100c01e441d0f446005848040300501003408655910404000c1003442c514101040014039840094009205410350013001401400302c3c0c031001001e4003019507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 617952005 1250 617950755 617950759
    0x20306240102060912031905130b091b060d150b030a050106030e4605010b010c030f030905070e091006050a081f06030c0803041406030705032a0c072102060405 70
    0x20746ca4a0b003d02c58000d40d10710302c40602600d07080038100000c1107004070003003041a0164007600c0a42c2d8625140d251100c00003815121880e4070310300c030040f0904000d00030b48902000900c000400034003102e00800046102d600c904401e0000104010714117140340141d038018001c2d42400d0001400b840c05c0681c4818440c4100b00d0300000441c5452150070506910b4941c610458503030395000c4443c1c800b0300c2e081e4103040380d00f40c59542c200800413419501c01c01c001400c40780c05542d0161010b009003070480c007904141000b5196807040d582c011416504c034000c12402001c620005091580c2000c010b617041c4e40503940200d21402400d8000c221109002c584c4003022800c45d54a0b0541d01c2c1c49016440040c0040e03040900b52030b9074840d0206050700004010000eaa14842a071030340700c0340d8901042010b00c4115440000600140f0100340710307454000b080d02d1740300c44008950039440e55281e0210200d81280800158070fa1142c0760410143c2000340c40e880c0c00c00400546010701c0d24154010071100d00c65481102c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 617953255 1250 617952005 617952007
    0x20a050105070f060509010c11120714010603151e0b061b070b0c0106050310090c03021c02030d08270a0b09070f0306140606091e0409020306240102060912 68
    0x1d001c001c03041c1d100c3c803146075114108205504195805a00038481441c1d10408682c2c0c0d045500d09000b0300103401010881c94200a0345002d817503903031b20a0070b04208031100d10590f40f0740c103000c0001064803c079040c0706c0010410004610b0101c0030001d021300a100d80000d411490001e4869068880030221504000c41011040704400001d068500d0311403154841d000f4007101055031003142206400c92030890b54120112041d4440d000050003c42c2d440090040c48400d01d52030800040c03c041a031508090560280810001c2094011070305000c841a503000004294500300120000402881d492081d01051009400342502e05a941d59500108014114011020028180d00020004000a0804a030300d102c8003c0c1d6a10700080034021a4860341041d80c441400500103040c00c4052f51240040149001081c403a460390006094031143c0308183c2190311116104056102006803600480104012401111400320482c0300b4410507102e060441d0000828480e4680e0002880c1e2440c442c545081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 617954505 1250 617953255 617953267
    0x506100801170c03070e181b04090201030e03120906070306060c0b150604090e12070f0f031b080d180f12050d1e110f0a08060a05220b060403020a050105 67
    0x402d02d0080f00b180707860341c940705802002c00c450000c08426806001e4a804884d04402060600c40d107801414100a078210b1440d5004015031601d03400200c2c540340181000908029400700361415640030f01442448100501c1c04e1141040040204d16809245460100070032030034a40c001303007820b0005201600f00200607010540c0e00c40030590341681c810004103c44c3c1e581e644e40c401000948203181030204940200211114072810318001c40740041c1e40071804003850b01c81907468a00000a0072800d40400c955071020090f028441c1034812155401419200e4407080b069112506840c141070316540c500200590803000124440e030144401688400d1a4150502204040303136107000e03e840340c10076a0f040913030307100c044124000403d01c0c4400c01c0303400384203142046002044600ca55041d1f400190010001e01070130600c61740c1c07000d0b00000000c281010721503481000442c05d64a070203420000d107012160300d1300b8407a03492290b2134a41c5420b030b648a003814655000240c0c040940c1c071070305040c07200004030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 617955755 1250 617954505 617954549
    0x10b12060a05120a0c060801050f221a120a080702060a03090816030314070504090e030d240603060b0405040b031c020c0f01030509030d18051b040506100801 69
    0x84440070708009885810791900440c3c10303903a148101c65003981c1100c110400030500b0fa00c0f80e1040c6050340d50240c0207848680200c01400003000e10302c0a202e12008850411080c454103a003e8048081000002d00030b1100c425020000482480c0c03440d240076500044911000802c880c2c151440150115001925200032420642c06400c9140000305885000180d8012240318484411060b40c001c0d03a00704820b015000200d40c1e010f01c2a6680e402041c0f06020401c110360403a0025030020102d14103407400c04048810130401d84012005030300071150360030b281c5044c031504501c0010040c2441d18042c8a101e29281000c4070600c00c0713004042c0215240c444003491903c040002c00c51101112141001c026030000c0025100d240c1003801c14850000c0383e03000c003490f42c407074040d860003a821200990f2500d0001400100141400c40410242c205840030b25400318006015420304d54030100380c000b00b0f000b1140104012074400034802ca1003002d4440e06c0e01c50303403030b400010b86042d900b07007074142d001e00001c00f19 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 617957005 1250 617955755 617955769
    0xc15180f0a031a160203031504020309011806060e060d3512012c0105040515060a090812120a0f0b030d03140906040215090a0b0301060f021005010b1206 67
    0xc050075800c4043ca07180540d01c20100403501c9060b51114041201c02c440604980b64402502c0d180f25405003854402d265140513401160000ca141000240d510310322101686071445400c0240c030079681c0c840003009626010000315078402c104940180c422961a42d810545154090341001404c22107a1440390b0340001940d6035000d0b00064601a0f11038405185e60b82700c00e8801d00984900c52484184200d55603c51040c40001030005920030380c03d07a00382000c1c4402071a000b408501074040324160304a241c0c65681c0142800103103a92034481080c2800100b5182c484501c40e002c088503c2000310719940c040507000d05402000b032106c0032a614001130401b2001c1c0415940c2c1903414007400010146c599015402440d4000740a980c99105680c1c0c0d4501c1a140c690883d0060f402c074802d810f10461070180c0b00001c02240d039005020b0100951102c019555a4109801070780c040740d0b01c0c0c00d8045110350100300300740d410184000e05101d030307604203210707424940209034000e0000c85255000c1801555251 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 617958255 1250 617957005 617957009
    0x1806011503062411070f2306070311070506091e01140a17010e091c050d05040f020118060f0516050a0602090a0f051813050703050c15180f0a 62
    0x98100d03415000c42c40d48560825191078001c0c01103029040320031130341d1001081e100221078000000010b0f04d0f00d0040755649031907240900300c28100d03c00601920341c4d61440c2c00b80c4a840d02035528801c950400151240c035003c015001503100d00e00138440c5d90b01ca0355400001140030000c04501d0628441d0070310042c2e580d80085400491411000304941403002d500c0b000111030f20002c011241c0459903554807401c00803100b9a441d500b545c1100548540d40d44c0200d4031015121310500d400c603d0b0110100c0711104481c0c0503a4101e4111141e100c041e07095607486450310104e1081d4003101151302d0f03d020f8000c0d000c4508035820906101010480f02114204120b0480d2200d4209082d110041c1583c0703000c40c000d60090444070b03c00c24a04e100820310b01c40365400b10090300ea028190f0b0a45020049130508a40c000034006480361065119100003d94103010341703001540309500070140410201c0c00c0190700c00c00480c00c1642d00790248810821140702d811248030711a0143d40400b12032803c10045050280c00e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 617959505 1250 617958255 617958269
    0x20313120c0b180c06180405130f0b1e060a2102180105010f020304080a0f0c09020d0b010806040b031207060e0303010609091a03060402040b031f14180601150306 71
    0xd004001000d08820301c0201c81c6615070056800e07000e130420801c41640640290900b10307400602140141d03080036400282c101e880c03010b0040c3d0408450790748015840c20300404845a2203010288406644040c22107412035048110100c6940b400c0070228214a6240c8101751109500302d202e0321280c94a050412407058018250704080d507508500400c80440a1080c07d0006499030b041140513131000c0140d0b0b0a940d41035020303101907007c9440e107072008019610292650640768400183e1211140b0042180f128a81c00200701c0140540001d004250004c042500035030403c0348032060703a580401c189140c8554102400d031180c1003030a01074020b0003400e00c0c81c5143d110000000c246e86400455070400c03644928402d0100400301008660404013559015404ed84040c007c20010b18264109103190788018040381c0d00080d070100080340aa04032a840c1c2c1000ba0f03a5503a42d10b4090030540d040f030f800364016030700400042c40820500d40d1903a0511910342110001000c02c10307200c1c0709800c04d20040c412 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 617960755 1250 617959505 617959523
    0xd2f1c0e0111041a0a0903121b21050f0904020f09100801030b0108011b030c03111306080105030a05060402010f090510080906180613020109030203010203041113020313120c 76
    0x2c0c81e0310b000d165125014802c602410003642c81c0003000440c00b00c90810381c40d50f44050380103165560ba10007202072600284144414540342c1140201d28848000c4e403180690704040c42c1c0d20503039000e60881480080c6140400c107007002a0b6400c84d421004581c424102650b006035501c0c4000009926801240ca40a610060420f00c030b20381307950700c40d40082c141c0b4014a81201b550340d8812416080300c4a65104002104203910680d00b503a01a0340289025100c0381408104e81e43c21046000150f400a2a0302400e065078107010b016480c0e0041c202030140c08158000d0801c0d403c01d0f00c40581c1e44c0700c01000281000003d20581794100c3c810a1800c00500000c3c00424230b40c220a10003811481007101e40c8816442500300003400f1408542903c50400c40d001c0192a0988803140b034001c0c428540030302a41806007401000005031400d2000750301c280d01078080c0100303402e2100108200307040380400c002d0800d070042c030900004041150400040765444550305502d0340f580320050f07a0791012003e028001002d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 617962005 1250 617960755 617960771
    0x504050102070c12230c03300f04090b180106020a021503070f0f051c050402030f0f030a08041a0f0601030c0903031b14030d2f1c0e01 59
    0x15005000e02d00d1141d1010781e64551500c0b54910314920305440035140460030b03030446081d43c200e130b410200281c4d01d550a9030007020340301d0042442c10b080d8094620480088182925440c26640641480b003060283c031a403508019070484042d90060307005407420540d6a1a500360b2687d40c00800006640181c04101429070392203001a490345058101640108412910904402d071010103d03440344506460300011403110030300446044040c0440d510a002e800c01a41188061060688800c0180348001240d03600d4580f05042c144801003040071074030b03808000b0030030a18a000c419a800c2115515125215a0f1107047c076803d250010300c4070b01c940401d04400c0c02112a096204c9602c00c0c1b00c00e80b010700c00120707895802c0f42c044110740b01c040c0020340b222902810079400d6024139400309008030070840c005007848450f0350841c2e021040702e0000e04d6490341c611407045120000d001c05030350001e00c02406880c00728108000e902c1660b01a00020000064190501c0390f16842000058220f50080001003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 617963255 1250 617962005 617962013
    0x905060a0f030303051f081e0c0a08011b020601061403070909050c030a112a100e0a03030c030501050d1b081b0a090204060c230d0f03051f1401050d0504 67
    0x80161028020070803115803076481b28444452031000c80e110500206228121426600d020381c0001c500c54a00e4010303403a0102a03a6119071001e0b0241480000009416041403180090f455880200500b0754001c0b000400a1940000b03030450380000c81501c480d43c81d80c600a0860703c1c03002c42c0d04240040c503c0c1c0300a100401440c0c201031807141d007560300104094106020b02e443e50f80291891555180101e210803050340b5008549100281500c80440311442c10005414054035100180040035500882c0b1040900d541401454148007480c201040594103090110b14940c9040102418691501880308181c040d1440103800800c80300055544003200078040000e40c2c1c05110f2042e00c921010a00030811444c10300c00c5030f08a961075202e4540552066441003c41d01c294054400c4213414007100008e14602448521600440e41d80c40c2201c82c088400041c0840d03c01034640101c00745d10040701441041085d14010a44813100b244501c940d03c1c410040340d16229002c01c4206150030101400208 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 617964505 1250 617963255 617963261
    0x3040b06011107050f041107081207260103030804020121020a1d06070b100b040b030601032306121911030c10120c0c080304030c05011505010203040905060a0f030303 73
    0x2420241e81d0180d12582d2103803150f50b60b101c01d002c0d081c0e01c46400d030b1040c6401d1403e07600a041351903e00c5182810441252240c1855400660b03441f04000440307020401340540c0f10898440340324010104801c61320100c0c0380c400544030140001400d0045030404101968000c0c0014010780310340c0c07000c01c64101110320880c00030350400c154420200d8841000c102c001612103151258412018149508054003601c41c0017140a000e0440d0b003908014440101e0f40c5180c0d0300041003c0c02034072521950381c0c103104c000101140d10380c169510048800170008001c1c2c000f1000480d4000d403044a410b11814414507140381894600c07020000d00003210706401082000c00340e444602820304806541c481d03c00142800014022182c140002a22a1030080c40b040013980c481460600e0703034071b0508000f040c15036840d11150b0080d1340036004038240c3d01a00c405c00a09004031030134a0103045820702014501070001c1d43c0c9001d5405002079440d01c680004910fa100c034140d0800510b81e5031503a0340d00668904001e001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 617965755 1250 617964505 617964511
    0x907170a020703080a09020a030b0405030301051302070f2301090f05100b01080a09030504180515040209060f160206040608100608010b04050103020c160801020d0b09060f2403040b 79
    0x8020518001180c0410510a5800d5242c00d503c0310f485030382d51601072600501150340e003280d200b0303901100803000c49d00c4c900d4101d21842c03146009540d607506010030030443c8100b5800111400340100000170001c1c2921204103000d0b9844180821803500c12092444084001c025280f5250329100c901814861080000010180110191101c81040500410946060440d541d004c5507920b80415080200307680111842406450501d060035110256900700800403603403540307602c0c4c03900c0501161598031000743c0d01c011006c40d0118a815001c1d030105030540140000d00b0400e1f600800c000308401003141c3d2164282e5802840c04da03449440f04000303004c524054807201030040c10190007041440c0108501c40c141d8884456150400d4680801140a580070900c541c07620700895030581420341c15040c400000c1c02d2424000350300c0d0a100720521040710382c4641c0c03141c032031800034060081c20303140c00121800c821030541c0c81c0104201d01070550310902c544041000f583d40b900008110500c0041c081c000c0c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 617967005 1250 617965755 617965787
    0x20d09061802041505090f040309031b061b0203070b0c0a08040e1f03030c06020703210218010e30060c0409050f040308071b050f030406030b0a150c110907 68
    0x40380072404d901c069000e840342e01440e500007031800c1c00b0489085220304450b034024480e14042014548030340d99005a43e000c000340070241c005e10350003440359075000110281e49585460000c41d40c80700300d4000070380d1940280301d1194148000039015a0219060100c1e150564121908981d203e80d51866048000000c4450070b000d06986100660810040800c07082100d8059a03a403001003400d481d014002d40c00490114180310910b62540510109011801c3c103c41050000684030700c215454003140450280b0f0701410030101c4201c4c4615503a0b0341160a9080b50341503681400c80c0b01d505e0b021074040c400803c109243c6c2c81980d00700218450030000502c06d1700c201c1d40c4280701303903124a072503c2c940303800a03900280032403c00400620090300c640e00300d107072011860034801800010f079192641030000305442074046400000d018041a60940078010303000300c003a0780f40403040d1310b0852805044000441030104200b02e01e110841400808840041c0d520350003000d80c0744a0618203000341000301d040c00040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 617968255 1250 617967005 617967011
    0x9031608040f050303070b0402060906071a06040614130e0a0c0b0408070b030408030609070e0a03080403051506011709070b0d0c02013e0c030a0206090f1f020d0906180204 75
    0x840c07642008801e1b41c001940c0a0341c085100d841da03600304150703074112401041d041182400720f02c001c0f0712010700e0905480005141c08255017004c1c001e020076286076800c4450206001400c40300507032aa0b050940e40064541e6000407400d60180301d0070704140102c0d0010702000c0003c8400324203111548000d204603035000e0200c07814140c5d1000c1b40b001e640001c407000790080740c060000a0043c144800c1060b840b41e140d01d8092501010280007481460b5103400550b580200401c0a100b08441000105105049600402c003281b40681c0000d02d9400e070305c4000ca030a4503086011680450003009150081c10351840c0040c1c907484012028002030a09408540040d07007006003c1121280d00501417000306101c58403500c800007080c00c1029103032000854140221800c101c5609080e6040c8040d01c82941d55501610340790401d0000146812004410350341540c00030320300c9540c450b8141045130100c0d4410300c005030b01c0c0c04108001c4801004155000303802e15080034500c0b0700b03400d0b20107100e21040740308403420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 617969505 1250 617968255 617968259
    0x1827010e0709090504020901060309020409080c0a0b090c03030306220f0f0c030902130902060903060411011e050d1a0307090b030106090212010e0c0c0106060e090115090603020309031608040f 84
    0x10f0f080d2213060350301941040b018001171044600c40d4000002050001d40302050b81891603461010326442520300031031035042407101c002086410030080350020110b000030308400a0080010b502ca10010781028401d00e4801c1d030034540515241d400e0075800d02d210008010306204030640740c019040300d4107081c07081464250b94100c00d0340a882142c1e035440d0050046440c20b0502059a001405140810380c0e00030014004125950703020803a803845944a030385946070403c03180300054922810307141030707940b00c03210300440ca840c0035404025104050700d50380c00460446441c1d0020001c05000d03404841c0c050103103400224000c00c1e0b5411159405c1001d0300204181e650782d11100d8128042c038900c800c02c410b0f95400400c20307900350300d0320650801d007030007940703441e2000381e04101d400c4030b46c2c80d88510003080351285105004c0c82c000c0089401402d0f040256054408000c8000b80b515550340100414140d02001280f12060100140ca06403440302c451480300d68150300301360a098009101d0515603074a01c90300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 617970755 1250 617969505 617969519
    0x103180506070c150519231e130b04080a210626070b0309150a050601031b05031b040b0f03011701060b041a0d0501030b1b1827010e0709 60
    0x1610710071404041111191166201801c0c050100361043d020403241203071651440c410681941f50280800e0588540f0425507102010156900100304401e0103001010440120b54400d0211f0340c4035078001d20041d500c01d003040003a00d0a6042d1080702c011807901c0e0040810841c0a0f511800c140c5102d280c5980021346114601480b2010104440540b604116810031410b12900051034101c942c5006980040ca0756030581d600320700007122495800c64507003060055650b007520400b0341180c0543d80085054000d40c80c09442131001a0011aa0740c0541c0e14500c43c906481d002d81d00501300c10441c0700d645050190442046420a005024940f44e03c9200042080014071410003110300c250311040c00c15140c482010140380c00701c10b120b04044020402d4800034680c600c00c07140079500c2003c50080504020032900c0400700070b041030300744402d0704000d0051222013002048558140c11070f03180c00c010300e04264401014000c40100c0714040662400030071840740c5084054819030556464540f004e6076508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 617972005 1250 617970755 617970761
    0x909061505030c0904060209300304031703130204050703023c0d0e100c020139020f0a030c14074403030619140103180506070c15 57
    0x40381c40e525a000000b034000d1410a07448031507110380200c0700142048031040c046010035084001c0e24070042149200c1e9003c01c2003404158030965a02801507003091b0450307407200c040500402c500382442c5004000510240f030740c3c42004c0d03150303036000c1c2051041e81021880680650006002982441c46081d80420680580d0b04620120302d400300d40031340581c0002e62229925404680352071030082c0c603024100348101c02005040601d50802d807000421400482c002030031105aa041d040e00303a40005031001602d210284011854445040c54803c4000586000d91600701c000d000e5164500928128405064000f074100380d009000e64900f4050441c0700000c0390b00c0e00c0c06400390100040e078551395200c0c45030f100380308840c016840c6c940001c0e030130303c210f242c842443c0002442750740b8030307807000007040840d081820f6100310544696840c1148a401c00c3c0b9466450040d10031058109640c0d07900a0030006440c0c1c269200a030f40010640d580340c00c120400403c2d0803140b21080d100d0149100c81c0349081c101502c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 617973255 1250 617972005 617972009
    0xd0b060a0602010b09061219050604060e0102070c0308090109330809190f0b090c121203040f060b120d080c0901020d0f03020c0313050a08011e05100f09090615 70
    0x10411760303207503030364408008240700e0040c40c07004a17219030b90768202403000001c110b012140c000c00080c001860549003290540b00c03610b5090301d180e401400400c002070008210b0100352644124540c1e1655100001214404901d031301c490884d1903850402d00c030b0550480741c450410541e49c020450003a00013001910f8421341a102105e03d41c0c0503401c10f81642030410081450b86200e8000030f004a445604ca0480c2404180c071088080d40140d02141c401780342c003080d20b010f030404083c05000e070307065900d5515401e4000104081e000d401c1d10301e140c204100303803030b07005074802da40050841903444034001503507075a900320403c010702080b5482c010038031010501058500d4020140d0040418414040f0304580400b014852013041c55020f00424480010030320240c805001c3c9003505188071494581080b80e00c0380c80760720016260b45401007400c1114040c0380018018401c3c2940465251070307000260140c5600c43e423211045601c10017020400c4101900b000c1c2c80207010b0343d4140700300c201c44042490441640c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 617974505 1250 617973255 617973259
    0x1b0115060c080c10020a020312010509060109060e0609030a080304050705041b110a02120f0601090504080a0f1101060b0702130b090a150503060906010329061e0d0b060a0602010b 78
    0x14620200000c80745001000030460041c155000f40c8200c1c4e941600b41e0f00701d0070300e031400740e000412030803822850000842e0051800f110699224102640007811041181c0a18010000e40074007001c01c83d204c00c2d044442c0e540004d1f003184c0f0340c8104c60038030005c0d0303400542e0100c130b01e4000e00038009510300e0700b40140c00504403408061802c003070450406840070b004541c4240418021041200090b940b440f03403450403104407002500b0700c41d021a100d04c3c20720700d050b001142070700d25003014000401c07541c40c00d403818613815040401c0c40707044c0f5140a545511848030a00740ca50f0804c3c501180f0b940000d409001b035584240d48010058030b0000300c00040d6042c41c052207070401485d100290200d91075420024480c1c1d204560302151648070404070303090503021140540f556000c00010410031118184040010301c081d4202c01882030b544483d4400d0380c2c0080e0885124000e511003546096104000100c0c200078003d01480302c0000a1900501b001c40c1210708a1041e580c20b000000d5460040c002c0020303ca0780 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 617975755 1250 617974505 617974517
    0xb010905190312021605060705010f11030a0c080c09090612070f0e2d061c0503071b030b060904060e030c010606110d0804140a051b04050a09150e121b011506 69
    0x6d000500500f50040001980d484d0340700c3c0c4203001c00f55294444c42d4030b50040201059543e16040946034152082c81c003002c0c04005942c010006140141000e071912410121146400c9860341c000107045280e02c02041007203401003440001d0300f20202240b110841c0c200d0000c2c40007075503441c022200e40000c0801d6107841000c00c41518044280031103203980c0e110800a080ca00d20300b0f1850203807540025280401c844a5100003843c50500606422a04244050590100d4207a00b195203504030803a000d0b11103800b4070f114401050801c40d030f6412010320710300d19100701c07600c9040c00f24415010b40401c3c40380c81c000c10143d5402d07184500c4081800c08501c40325484500301078480d0b0f5660041300b40409121201c40c011580c1050008600307000009010a00c2d080b0180d82c0749441e001c01044075405881b400040d85001e0b072040010b8802861844200c2e0040b9000640e4000013800d10705001c008402000000c8000480107181c02c01000d40ba44824140d000812500110908007110b28001d40602404140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 617977005 1250 617975755 617975759
    0x1207080a03050c04090216023f010209040504050a12050c2a09010b1b0106120303052e1e0f15050d0c0c1103010c120b0109051903120216 60
    0x802904083d811001c0f584186182c07a9850411000300e8000e80c80c81c4070300352007401d02d440035803800620003e42908502c450140759260510300c000c542c03044450032440c507811030464610603031080d819a401c0c0c40001d4010312051030300f480e016450f00103156080b100c0c080c40c01038100c041031150054842c00c2c042e04004141090196030f108080c8900700001c8107608a581c04074064a4544504050003481c40501e555118640c40850182400e00041100b0302d5a00d0204100b241171203000312001c03201e4042c00c00080c6c50316207401c81d080c4800110300c907002c08901d40c40d0780000c0600c500c942c1c0086840c0d1f0794407401480201c40b100c0107160003610807524551003003c001e1045901c20001d0704010b0301d031814007034a080320200142c1e065a1012400c003001c2505203a26609000e0003c00c280d01e903c20441c0200300301556110f000e0700b03014000c141c4000050f91a03500c16a240d008200400203014010250945408905820030680d0070034041224080d140c00c04010340507000199001c4000401c0200755a458 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 617978255 1250 617977005 617977007
    0x4020a1a090a0603050106020f0c030d08061305040803071d0306071419091a07020d110d08030a05160206090309010503191b260c030c0913020901021207080a 69
    0x10152a2a8104814040011034010340d80c1a4070b642c0144500e440c00b040359031401201034100800021200e281d90080ca20f502250b680c00b06414010498074206056903132241c00c007159151003501e031046a65441c0200307020a100c040000385100d54404ea07502d20484c104a1003511030f803120b4100e9540c255010402003407040d4001e064501c14009150b40c0103091514031000c400000d90500011000324001c86800d02c4070742201c83c000d02d030901685141c1468003110b5400304c1c91a014130400500b802d58900c05c07060f0540e803810702d20072000d030f0400800754a0b41041d00e00e98004050070b90b034070082d0b00000f0288009140c00072030803d104a0704013010f1400c02228100540e030540c00200700012071010510121a130760300c90f20030900b000f5250401141010340e01a005002803180c2a000d50101d00701107005c4042082c1150400ea0000341c0252090b10ba4640041c9016580034070b0000c184c1c80481c0d8541803080d040b1030f50242c00304400036802c64883c403140485140c03d41c494040080c0100d0410460b90340c2d00c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 617979505 1250 617978255 617978279
    0x210405031209010e190302010e04022b0f0212010e0609010f031506092f0c0706110f03070b0a060b030103120e121603051614090705070611120a0504020a 67
    0x42c031018104120b0220340c03000016140143c071841d10039205485e080920555900040c0d135210203409403411494440d04030b000d096600d102c0403451070402005c01e0b030708000d08003640080c041410141c102755266400d000d600d205c0e1100c01d0240b0000b00700c008000958034644100024102d456007078a400d030090031b5496041124a00e29240450170352144400906c54045204080e640324110010410f16140d038081001101001d0344110f500c0001032054950707003c00840c0c18800c0f69014100032a00c0c1c0b000c4400741c0d0a051b80d4628062040c0000319400052000100c002441040144002c001094403844040428082800041c0441803142010960326005108602400f0780041c4601c120b122030b18102444d04805080700a1181d004507c2001048020000024001c40074203041d1007a5003480ba0181a55512055940c4501003c2d4045001240a0030482e145aa0894000d200c050030702c2038001015880011400281c1010100003401e0b03020b02e03c43c40707024541c010504c20300685484815000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 617980755 1250 617979505 617979517
    0x1080103080d0b03060c04140a030309170a1b061205070c03110a05060103051014010503030307031e060b040608010608190c0504050405130314070c0b03070e122104050312 75
    0x441d40d9a81c42e80f200d541e01004424030038003561103819070381c606150403808240181c10809015039104003040c0b00094104201400b524042d5801d840146c500300040c502c3c006203031502030108140d00da10010343c0480810000103032080b940322031403a0703e000281e4108035a000c44071100040c400010401c0000d114056040d00e210f22a02281d81446081e15210300b480d0081e8006c4aa941c49000c00c9000c94000c0d004002d401d220301c02005184d0341c904004284c8078440100740404140c0c0d00c9284126040380c4e00c146040d45021032000300034640d2195486180c0d5845070040d100420030074000091403d129050031481501403e084500901c2d00c0b550703a02c0507001107407101c024418280310100341a01d0300e100e01481510001d00c0d0901c411000e00300900002803403144201d02c900c4c10401d240c046006919603208456820707000b543e0b03c0e17880603c102c503030341c010a0120364003000e06220070b20400d40020340344005c81c0f14070780c9426100d103200c0600401d5100300e101e0b1582540004400b86480b107411006003003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 617982005 1250 617980755 617980777
    0x16081b060408010c02011d0d050d0207020613060f093305041814011205190c0e090115230108130b010315050f06060301140d050f150c04050108010308 66
    0x10400342c80340811801e4650107035400c070040c0c0d510680341ca074450b11301550300c8950104801501003602c01e4400207041d031254200303c21105800064100c210346409048803541c98440094004541c2c0b10744004004045036103400000881264001c180360914120303080111000c050010700c2076180303584003406801c0c82d4089009002080c040000c6c4008400c208003c3c41c0741c1c10100046080040c3c02441e28102e068120440d8070f1995564400000c00000d40309403183c9891400311820403441c07404e1407240c3d5290b04081e0300844412f0031701c0018181500a809030b6441749c510500029125031108000e1850034506003460440001610035035402514116040f0310740c92181260540c0c661181d0000110030f0340112000c0068080d06d49111a4621800703070030680010010b18203003404400500c540c0010b0049100c0e10481140f0b0070911b5403246ca0310000103901c4000c1e02d04082c01180c103151501c1000602d4800c1c0100480054079900303002040b6026108140c4541d11580d09607218000250011a03104d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 617983255 1250 617982005 617982007
    0x9060f01050f150f0a110c060703050c010b060a0f0e150412050106080d11101a04020a050d15060e010203070b011401020f0109060c032304141216030216081b06 70
    0x3020f00d1190004151040d03905125554491003100f00803c3d0030000390030301c040ca0b0010f50280001c0e03a0307080104e80c2c115405103802601c440010400c5401040180001a400340d0b0001d03143e0310351604000e005100800300d4842034680090b007400d012407080c00b01d40184107258104014015a9200060400b0040c0039800011b006600c8880795881d10300d8261b99200824100d80d50114405002c0250480c0050100c00500511120500c88248810040c5645100d9900841c055500d94414400e54000000d84142400551396150070468030808601030f12001a511066030700c080d500001c11645296480702c0c500e101a032816504809046002e4040d50450280c486000e003010800d008840324503000b054001000200030134050115034000030301980810541090102c0161201c8aa075030040c1c00c4000041c000c08520740180c20240c2e9144844400344022680c01070650550607403420513807003a0201c4040407000c40c407409034052944541c83e01b541c0948002c0b505d50601c1e8004400307441c8040c06072 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 617984505 1250 617983255 617983279
    0x1060f021612020a0605121b092e0e0f04090c030503040b03091605030d0311040f08010b04050a05090714060706110c0c0402040b12060f0301050907080609060f01050f 73
    0x788004640e9680546141e08114542000f076182c940c82c90401070119040c458540203200442c10020701c0c0050072005141d82c0c8402c03c0c500c040071035088940c1980001e0034507003216040c00080f80c0206d113180d0b8410f0b0310301081600080042c080c0c0501c54541c0781c010504420641094104000780105040c11594091865000000034004002500282640c82e14941d00c91800700b00d8140740081c1c0400611040c803450b24100303d5501c000c43d00007191241860042030021042982c24051310966001854240b0004000038400758194030044449004403020301454442803040d03400e540d025502440340da0000da03020002280130101210103141c020300070505254440e142c12044030b5090700e046901c68800100400c1030300b000d104081040c0c90071281141802d04000541410b4080c51103080c0034400094080b5010b9030b64a9501070322114000c0080c001840d11101180c0c0700c80e464802c4029a11811004c0b900454003c155288030340154016080305a280100308042c0701d101d000013075001000342d000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 617985611 1106 617984505 617984533
    0xa0b060105071b0b0903120906090904240605032b121b030213060c08030c0a0302070b040308161103041205120301090c030f090b01060f02 61
    0xd0315802e1a00e040102c440704002c644501c0360a5910005200c440c041c028010001c094040d54004610500c5141c214001d0300c0c07582e580201e0a20000095041100318154054000e030a07144074500560000c00003a61104d80c840c030b410351a41c000344100e0400300100d400221015104401c0c014000c03c8054500c40042201c0c3d081003201d010b00d540ca2aa250000003444a100029840100340c0e02406030095002e00e0355030400740e101d4030740020700c20b005804403030510740c2080d03200e031443d41d4403036041409a0113881040f09256090010501180e0f01900c0075214a100b03172141081800c1041180100c440021800c500704030a824085070181d1011094800700c9488424028011103a403a01500b4810300000e119100e100200000070f2445294200d100500520b880421010007800308250035a0a6242d01400348031f9030340c0c010000d0301d114085590704001c4d1403041d59807000c80d01c81 = true := by decide +kernel

theorem cover : BRFrame.Cov 617805755 617985611 := by
  have h0 := BRFrame.cov_init 617805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 617805755 ≤ n) (h2 : n < 617985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
