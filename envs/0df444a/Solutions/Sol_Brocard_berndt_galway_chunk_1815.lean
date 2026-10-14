-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1815
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:46:44.487073+00:00
-- url     : https://prove2.me/submissions/18d5ad90-2895-450a-9982-dec921035afc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 326258992 ≤ n < 326438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 326260242 1250 326258992 326259023
    0x90a0801050a0b040e030403021807050d0f0e15040506010b1e2a03030c0301060c03051b010f0e010204080a1b030c0f05120f0d03150308031302091e0402060d09 70
    0x40c2e405880f1030801660b0174003044211070722160341c9200d2480000e400a47d5082a0321203441e914510940104c00b503d0140e03c0c1400c000515001e50b40480c4c0403015080d0b890040035000c0c8070800407482080d0740c0c0506d8a0341c0380380c1611420b4550f44c0c144035501c407100b4001040e80f0030009070040c1074101c48030903480702d03120083c4039a0035050310552810364900d0404030a4120100c400002920b102d0380080c154649503a09003202242c2c40c140048040f420b1110a000e19210008000c0c4000da482c4a10000007800350000d586a0301541d11030140181d60b039104000a214620002c609030010b250405541c10141c60740c4401000c500d01164409000f100046c040801d00b0f00c81c1c40d0781c01701118822140c5a080c126600703032940d00d03040c00c0d21440d0300580c000d1110000b460f00070340110200c6101c0782d4044030300c02e80e030361610252503000300e5602550b400740503c24011450b04403d2203801920500000174050103159115078428005000603100d0780b00420442d10b040b0881c0c00154125a0200e02c4605a01d036 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 326261492 1250 326260242 326260261
    0x90a0f060806060406060203030405100908071514010614031605040509010609030b0a0501080c0d0c09020f040317090a0306021608071a0f0709090203220c0609151202090a080105 78
    0x700f07503920b51041c0d08240c1c00180c002d100000ba039001d42d400c030018007040750361114064000e000c0000d04954240040c094000441d01c03100c00325115601d010b074080790700c1c4900342c0201140307903050b00108184102c2005198180c910a0252540044010318586010783c01e45015900ea0080364031032680145068004660341e9480110141200d124440219441d160f508040007560024041c024866000c0e000000c600e103403496008076664018801c0c2030304c0e02e031240641004c0c2d91007120189450b07040018108104801600c5c140400c3c03500c401d0942c2408800400114859a40d10024000380c1e004030318018010b40845602c116940d0000501d9500c00ca5031500c042802c4004280032000d940542c00201c4441103140c445e0f00ca200c0c00d5071100c0805040141040082d04007800030300c0e40d0745207070145414070010508820764541c02040c001c1d205c6841c1c00401005804181c1241c01b07017002444055880c150040c94049515006643c0561130380c04200c003081021800b607204210a60815051200140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 326262742 1250 326261492 326261503
    0x4032003030c12360723040c030e030d061e030308010501111501060c110a1406160606060809070902040b0301030f0201020f0a150c0c02030a0f0309030804060525030905090a0f0608 79
    0x1034010030f60b041c00b130391902840f041504d08046c001041061500010740c0e490319a1118440487c1800c0009000d20440c0f6040e107503402c0140562456607076610148801d4040c80070b0074a100e40c945c141502403904550300200348132018805d49040c44059401c0c100d00d041c090041e0002d00f0b00c8103882e114290b81d5090010300359000c007030f000c0d22901d03907030b03245000d443c00c001143e8402e403840d2040d41249881c084040c000f8603800348a4044c3c81e0b1074600c084030001540b1307010f098024039041e40d5100d4a030405401260501a85a1050b90311510400007080a00e030700c4015030341101d03008400b01201c44403900040c1d0900720010803081c41070051075960801c10031410300c0d44c0070b80102c4080400c04422003ea05680c1c51140c1c1e0f1010f5810303400541c003000001d010b040000100c0380700e460110059541d0b82c1c0d65444641090700904085040400c00c0e000c03e031009480002c92004000c04903021510685001e040d00e22903010b50780c020410b5074005900120f0325000040304c58590502004071565664a5a8860 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 326263992 1250 326262742 326262841
    0x1050609010501030b09071b05060109090203010510080a0209071e080709050612040b04050a02060a021005060f0609040e0f0d090e0618180703060504032003030c12 72
    0x5016000c004203072544039124401c0c1818024040c140306403a0344d01c0a03503510044520f41942950511101ca00161003800244d009001221002c12201190702c105401e440c0000d0180c1500c00401e4810440b02100140254066030181e03010318152300d03070000413144016258082050000c501060005407540035811600c6402c080e994401d81c140c580d82001864800d50144655070761417840424003140481202a410511400444540c045194040313520b0340c0040700ea54025811100c48040003c440e0700503641c0c0304404580000703105401a0001d4483e0103110481d6028561f02c43c6c0e80c810705c0c40e0400018002c040c50b44100c1e5617403400310078000e040c43c1d1744e8066400201040320100c1c40c030f070800b801c800e03100544a500d0034440f03903a00e148070b0b60000031801c1d42203003900c0f40c1607000010450074491203000d14060ba9034111050140a0b95000c81d8408800304002a801081001700070072045040d03c0103401c0c000814520303501d80f1056400a601c0c0611019100c11881c5015401080043c51a1b43e00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 326265242 1250 326263992 326263999
    0x90103300c03140f040915030b19051b030c070c08060112031403071407030909051e1501021b2704150911061615020c0c0910060c02060c0f010506 64
    0x5640001003040618021004c0616803044144024441000103401c64410036514030040301c049644c91b00c600b00d105405850481650b1020f400c1c07101b07003900e5030003a90790000002602032400c411101e00f440d134501c80104245451b1001107405400c002c0b07402110001081d00404481d140c0d41c603000494105c00100108a01280028015540074080641540e03c00c0c441601d401030641d40300b00680d0407031350128804508100118201162100241c41268040c4c024201101d400350704070314010000800141c5a490800320150380b0071696a400034025140204107255003840510001c04181ca00c0e10484010703502081503003c104050f02d070311a5903841103008a80c55621000000886002c9418224001d0103002ca46038009541c0d007800e03001494600c03151681c0b42c1d070420301912040c1200320418003a100c1c0c0c80e0005500800d00404100312031440b0000c03151555541001601c05614141e288112010f00c016810301d03c003555610340503550049010020b48641240c2c42d40410300a0008a440522 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 326266492 1250 326265242 326265257
    0x7020d12030c08010806070503190c030f1a0904080d020412050c210a03051c18050606010504050a12020301020403080c0d02240f0a110f03061509090103300c03 70
    0xd80c24441c03e10b6504a07000d81d00540f210f500d0f000800c5076280d0000300098040b00b60403103010350745005841002e4000da601da80c0002e450f414082c412054032203902c0842d003080d1541c40d1078521030760740c180469041070788000200d030b8801804a4042c080e00450340f00c0d82c00c0c85001710b1240203102002c1040011002c0460710101090003c0a040c1c1d045050340301101c1c0e5a5011046540c0020300440c0102120328140d002460b070b41d4000c034100820f03207542c40c5500f00b900e6880f02c0300320b04121040144640190782400e01c10304240c00c0c40040384041500348280b9075030f8246248501c066403029070468024581103100295981d814405060740d03030b2031b001d841c0c170300500c00e0344e030140020040100b1445120009000c1c1ca002a01c80048010b410300d40609100202035035420703014602c964107002015601c0704844615141e240a004104280512514521900d04100140100f03903660042c40d505481d8000341130042c2044040096600c0c81c0072200004104100c0c40221244542000c3c0e14942d0a00c240c1d40c401 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 326267742 1250 326266492 326266511
    0x1e02160c0905090312060613120201093008070503210a1b0302030402030c12010e0f0c031507140d0501090513030914030a020d0b1b0f09060f07020d1203 67
    0x40494030b0407103c40d602d0390410f010910002c1c1c0c481c5240c43d007252004144070300b401c607011f10003c2146250b130f00060030b003d8901140411560020b10326002469000c0300a94045c00c1a01d80c64680d007a074050840c10880000e48090800c001402507c07515a00501225206e00e8180700d09015024041960a80b100f0030200181c405005070080b0200b02c1da0809070701e80908101c03841680a900050812640350150041c0000203441e0440701d054a801c0e08800402d098100c080440e007032000f81c20080765070b130300100c00f152115100021401c94aa034090040036003543c56a1048480100c540c140c04900072002403043c4207003181d40c010710f060f505000420007054484c071000c108090014000140881d140c00f07801c1051408440005001400240541d400e0b070f40c00c0d50004140e008500300885445040300b0901005c00300e42c629560b099504000514580006803010b0380880c0038a800c45c0740b0800c3d002441c0d800c0441c2d0942590000f40d030147c01580f4500c0c0516141d07503540002d07e4298002441c6c0948031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 326268992 1250 326267742 326267759
    0xd0804020a0e0105060d0f0b04090b070f140a0c1a04120906050a080c0307051e041403030a02030d020a030207060c020d1202070b1302030f0a0302060403020606090f06041e02160c 78
    0x5904a0704000e1480b46803094005106d40034000c143c145001c01680c40c17200041d070751a1802161421031141c00034a06e5441d000d0f80c040e00801c0e000404008224031984c810320302041e58000c070380d440c40140c140f600105040b0b1030106250390706107a468458a840509200030845000e52130359043c1002e803140c1c101d8503100c910450b44c5001e0004d8520004003000d000c5040001020001c5411010070b2038400d14003290385011306841c4c070008422000c5200001010410400305941032904070100324082d6140c003003005402540c074014024078014096000500e2603845000340d040722181c5a210209100001d90101e000e501d518080f4200b201058005240681c155503d200f240d007043c2e481074000f0010344400306004403815803c04100c0e011b10400082d080e4108040040c000d40754440d50003800b003464203142c004c1c1440340240a180c05480500240310454000c0041c0d0f0380d00200070364002400390540340d82c0606c2c017841c5400c103405240c400500700c401042c074200034040340c0b40100d80101110756a42480d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 326270242 1250 326268992 326269019
    0x7060f02011d03090409140106060e12030c060403050c071212030605010e0d031211030c070c140f04050402030705060c2104050a05060d0f140105030d0e011409030f0d0804020a 77
    0x240c1d90b180c00420054080d4942603103c405618084c080052102040c00344c42030848141d0380005000c208454205001c0f40b82c00080c1200440b02e1502543c14003c961404d503580b0344010340700078240803003ca442c0c0a84038007001210000c001600c0ea0356484d0001c1d0504440d445107019000c00042d081000218555005000f02a021403000d0035030220000c0640f0101ea00600706d174581c0d83c0503a26854a4548501d0480165008410300000160384152610b01008000d101d544500d0311708041500704500c0e6550200307581d05031201614003117143d644070720000742082c41640004d41c1c080c802241028081d400040d032801c01f51201c141100320354050007502400e5000d14403416520138000c15013800307a03040c141c016200d2602c00c10404900340d06802c460505881d1200448944007001100400070b51808001e82d0341021024105a240e9010301d4000914080083c01e40c1c061080000908117510b8030b0401002c0e01e00403400c1e0688107100c0704c1c07080c001c00b1b03107409032410380c4105031701d10003c206241013110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 326271492 1250 326270242 326270291
    0xb06031e0a1e020705030c0d090608090c090a0e1507020606010323150307030c06080f07032c1f060e0601080712180f050a140114010b03040206070507060f0201 70
    0xc0c5518282c52480242001e540402c50854003400140f10103c4406010001070800e10b00d02e844030b42e4024203110b00145141da0091400c00c45900a0100d07520944031503140070341011640e4408100c1d2030036084500d107050066480c00302c6440c1084100203050703a02064043c02814266003e0100001c00030040600c8440350303410910b040981c10204403480c0142e62070100d04075002d001c1c1ca07480e5942e0745410700500c0304c44e0b200c540412000010421294024010558400c80303606040090685541c2402107006208100315124164004402c031304040c1081000c045110304484082c01240518500f00039010f244181c61203980358002190b0550300070361160340719042d00e40d9150180b51440450b0030180148584103c0c6042c8860600b20200305010b0b01a03009a028000a100c400c11600d44031942c0b40c40d10b0002c401d00c1e45400480e00e108004e0214543c11500710701e58168803074445000162451082d520001c0075480740719000188940c00c8410b4907a507500d01d4000304103030141c0c40001c46511403a8003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 326272742 1250 326271492 326271521
    0x1808030619030203030c010203160c1e150f0f0b040b0319380105010203092202040509240409020d02010c050f061f0801060e0106120b06031e0a 63
    0x4002001810600408400d0001d03503124003000903a6500468295071040c078030108547d40000401030b00e54804010080b000d22103180000b1a150740e034948100880040c1000f00101c0c1050000c0b81c14131007030250700c40380c080c420081006014845504c640003006100d03040c03e41c5a080030340041c000d280511a03d00716a00c054090302003c80d400451801201003404101d0303200b81c010b0b40500c80c02a40c0c01c15070f00c01c3d0300003a549540e52908040c0c000e0701058141d22490440d13100704030795060307a1150f902d444030042c0d03404401c2c070300700c1c0c4818400c401a000700c0c0c2006800400c80030801031818804100c502d11001480d52a00050f0108018001584c1036280045d40004c08000b4010065110722410400c3c140038505917042d007148103070704900b0818181d80e8803031130300c0d480f0944080b8003515040c00001851850b000304241850301644004503081480740c60248181e07040039200355038440c3c2065100030700c0213181c1a5a460b03c6c070003040903441c001c0d801c410444006030010342248060310810040c80b1209 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 326273992 1250 326272742 326272747
    0x605131e030f0c09180203061008100b03100c09061206030503091507060e0f07060504080c0919090602070b0105090615031302090108060603060c030106080a0207030e03030d050108011808 82
    0x5480d0302c01c4111420707104965030039003100d00040d02001c81c404d01c11006068001c00788203214a0040501d040c0d00605070b02000c00100000700302c2d250000410340d420b180540b8002c90b1050000c00042d0420090580c84041107007800d03000401603500413200c0c41920990380b6440080c100d403803010400c45d8802e010027071280d8020400071710540707004880a01000c0d40c44082910b0100196074410580d036048001c00980c2e03009802c9001e4180043c0314070806402c5504d8420f040c02e01c0c10300c2c0c03140c0d00c0d101850740d00e006140290210301d0301c0c0500120441049042e84c2c01384002c050924144000354440c0509540d141d0380748001007854904070309554000c0c0001080381000d20590702ca8181e156201078440c04c3c0162550155000585078031915a000341079600203040989002814142001030003030901800000400060190540043c0480c2d0080c012220050b02d50043d40b0302a5003030a40ba510250b8184000314521030700700d080360080c07070584545030001e00c2022803070b03d0642a0070b140c1c0d0b400106101c00a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 326275242 1250 326273992 326273999
    0xd1226070809060c090904022d010f0c020d020f03071a04050f060444070e07030903211e050603010c020102030c04050d170a0c0b0f060901060c06150605131e 69
    0x4510268100b07000801011802d4004142011086045201c1c0c4c109c0380420108420320350703040008000051910700700545018426030000d001607034443e60091094001300c880e01e0013901c040000070b01406001d000a5001004042e080b0403e800610030140f2650000396060102d0400d0801d4804542e2142c2030302460381c01c400c4040804141e40644850407108d881861300700c0c800c1417010700268444440290550034105030041c1c0c42c2c41c100422101c1851b05006554000a6000705141442605119490300824041e8817000182c944070b10260042003424400e00c5982040740d016901825048008028407035207031400342d00345d00044032084001d980034042004107083c40100500030324404e0840c40c828005a50010f040390b0440110703e40000c808074008000c010b0003211440e084030490010401c1e038505a0002900500140940000c000803d603c076010400741707802000c02255a00c40d9283c1c1c03141c40798401446500071980010784800100d400207546146100520002d40201e082803892504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 326276492 1250 326275242 326275249
    0x7240507080930010609110a0f0e040c200a0804050f010c02090f0105010908070e010902071407030503091009080309010c17030c07120e0d1226070809060c09 69
    0x390002d9000421070740585800c070304014043d003a0030588800700c0320000296800d107085403465046505120324250000c9404000030040c1c40d909506454003821000301441c00b21990740d49900100d0300309061940800200b5005a2040181451600081d040d00504010a55103c446e9080038101c4c40b8108401c2c01141440c1034582c0d445207040c149030750580d102d54040b41c5039020440c0c0c4d0204098503071006001642c3c0c001c6214004011050062840c241070004607903658506100c3c052406030300040b00390400407910401030820046409481d401c0e0340d02d0414039180e5000c050f10344e1041c00f00c826000c0c2d000f070091031194181ca01088c01503003004402d10054076a080b5a030741c01d03900400203400120092104030000c600c1000f607150300c40d485074003524015840c82402048001400185030410405480303203000075083c43e4100c60005028210340700e09889038816142401903c4a03c0c806040030086c08140150244800b82e903003118565501480b292900c0042d101d00c107a03c48104051803107440c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 326277742 1250 326276492 326276497
    0x70b060a12060c0806330c0a050f12040609050405040f020d060c0e0109080604170408060c04140105040b12101203020102090306130c09020a200c01020c01080613020f1207020724050708 81
    0x78001104078a45012403449600d0030000320800c1709d10364008015500404130a011400c1444140000242085e04061003d072000c41c1c4c80c0200360003690f469002a00f404050951078004039006058407012480d241408005405005500c1d8081614001e1483c4035501c90fa81c00c8040344d80712005007410f500c030b41da2000e07000c00540d544098060f0742407101103400c460a109460003032880d441d003070b5581c601d000c02e2800c1d030200d4402094140030051000f0081c2404500454890303030074940b80503032156035002ca00812201641c000740d242102a000b408101601540180709419089080315050303030701c80088110441c1035482c0207203081050780c01000648450303005850002154241250fa0842001e40b040c030341007580c0c0300329000f035108940302d01c21540c040c05900103110080c40d00c080b8030324040000c25600004403150882c815800550700b28545202019a021079501b0002d29000e070410f03000c002d6550081e80110b10003148225150003018002c41640502d541742610b80c1c80c1000703c2511031742050b8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 326278992 1250 326277742 326277829
    0x706020d0906050906010e0601170609040f05101e0207020d080d090209070c02100e010807050f090d030305010e0903031905090c0d1209050411070b060a12060c0806 72
    0x380d258808100040c00314000e10303210300e144074014111903141c019070f039001000c044e000c1414031400900010411440b4030100383e01020603103504e402c0b034a43e458000110054a60041c05600a036400c91080c0c0041d5003103654002c02500c0f41c500b1030851901c4050480c0304440b0300951103090441030b2800220710502521520751814800148850703150041168040c0c125003180005512412590841c500352100c031011400a00d800d02c02c08000d50000790840c076024200205110000c038103080000400c008603400d52002810025150149140180240c4401c0c05180307440345c016400138141850000949120b02c00303142c0014031038011040c41c00e0081c10094058a11800f44a60030140ba03242c3c940705004240c492128034910000d10380009000700e240c0d421642c0f240b4100003d0800e00740c0c84505441c4200d80040b200c843c1c90301e4a90018003c001d460b400042d1001c0000540cac4140035039507001035030074103058554408958034901040720702c3c10750402c03070b14075001801000d044002c80d100004184 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 326280242 1250 326278992 326279017
    0x90608190f1709150a0c03050d0608010f0209150c070308090f0907181703091017040303090606060801051f0516290c0a0f030f06080d081b070602 64
    0x41525881e450b110341c420a050103103145002071840c0d0b4506042148040360601e0311910381c20712030003100050051143c0200641040000714860002e402564040001010352a008116240c1c2d80d02c0d501e8043d4000e8071205115900c901480f0b000042c40034100d5907805904e134068140b05046945802c41e81d041609250b40050752060124429220012250b025294a488200044910885400c1407100c3c1e03410042102040c821103859020000040c0d40d005103040741d03e11645c070036000084910030f00030041400080885402e2109041c0c15500100340d0a00451041c8102ca0302c6000568042c2400e105413078000000c141a112000380311101c11442c810245040b40c031385141092014003130380b01307402c099640d400340c1d5240500a010031040c5040428419484983c14982a03000071032030300a002c0940c1c107101c800380c1030304040d0340300740c0c481d40844542003020018103486500456442c8030844604004c2018031002c50401d041121044500c400845281440c10302c550b40c0700000f81d00100418000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 326281492 1250 326280242 326280263
    0x6040815070905060d050a1a0d03030902040e01060f08060c0913090c030c061805090112020d0c0f2c091009170403051f0b090103020906031e060105010909060819 71
    0x19169030301002807400590a54000ca0982007d00300c41040300c1e005290600441d1410030003405a4032029020005c240d003500780090f07510164000314000cac254031108044039501c1d00c0e03800b28034880080c0f01c01c0b0079108050111511a034400e54100e00ca4402c0e041d0803a8081140b407410500d0b20455000712900610800c0160140340c2e17240d46901c0c40d5070f4a80c0016011a40b1001c60b10910f0b01d441114000a01007218020629454100e195454550414019000d80d100100c24010700c00908002402480711b044c2c011507240d980c1b94101c40380c1d50028015190b9a280c184803011031490250711a0048409001901180207903213104e00040407520411644050070074030104051200c200680010b50244002d4101800451301201c1c0d0307c3c0e04102d07803d81052611804203001c1e1500482281500d0781680c0741c0c20151112000240307800e480d03030760b15420301d40700e03108c00c1020750804629a412140e00f038841094040d01c0e1000a000d9500900881c1c0d501c2c1e004090b4201c80c1a000310412078100d0080c040c4a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 326282742 1250 326281492 326281499
    0x11404020f06130b1b0102130902092101051602150a050702070512010603060e12180111010f06090b0f0112021810080702071a0a0e1302041211060408150709 69
    0xb03c4103040e8440e907003c500201d01040c078148a800403543c01c0301da2100031443d003202002c001000030044d0081c061619404158108107848400f141780d440b500304820910081000e00c44540601400ca80c03d400c0604410b540c1c1041c1ca00001c0c40c0a2103901602c0221000e540742d006502c010300000346000110b11441000140c180c4940001c01c80c040e07210000410054150305101d8199008a00300c3d40a651100038030f4203028100c001503a508209806c0035040c100e54000040783d4510840c0c5d40c1203015480c001849060000361f40c8814100c1d0791701c1100348803078895401042101c0409803211404596000d01c11210701c0c03015801800c03e40e4049680c1708200348141e0125a106180d09914008600a80140641550100f000800074107003803c40116407a42c0d001c1c01c108500410b84002c05110461444060550b548183d641110010440454541d41d9440c00c00c00d401602c46400da440042c8524803502d1802c0c01c0c400c480640e40554010b0154021580c42c078029044010000020014403c1010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 326283992 1250 326282742 326282767
    0x120b0a0f20030603070f050604090f0209061c060b0405131d0706200106140d0c031401020d050f100521011a040e0c010e06070f020d050a0b09011404020f06 68
    0x1c1072400801e000c1070344901d4143c0c18075141c102c207900070040b6651592400c0041d40d0701c0100300d4061702e0b00d60074080f800c0104408180041c0c059000020391110f00071600c0d50354280d044401c4440d80711035040038080c0d40d5403035507000b0080c03040340105134100c05005e0300440c031a021504800300644030007031030b01c51845000d410f00781801a03d81001d0700103028540d60114104030f81030700c0340040803507100030441980303040c3d0410200d6101c4007805004500301107000080c800840e900600450f040503240034a8191100d4490007940250103100300c5c545000c0110341110066201c40d40b281d501c0f00c464040c01c604000402c1000300c2c1401c1d10491941440200e019000028082e41038520781d14103181d21032241600c200400d0b03803815000620983e100d00d80c60314080c0e80c071414800703c05400352081c6540301801d0400c0103041001c00e101075008540200c0178400c000001540ca02e842d07004001c0c201c0d050700e54050f03150036200d12003c01041014203001080152500351200206544010b0005242c00d0014400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 326285242 1250 326283992 326284031
    0xf0d05060c070311010605030a140309030601060203040f0803040509060d020303160602040501031a180c04050406081005100e070806220507020c0307030c1e0e0c0a09120b0a0f 77
    0x604078068001c035885080640001e0341e0380342c0300300140082c40030703504020100350788207281003018003440881e103030340d441054007442202d00100c800303000c0c1c070640d40c7c6440010b56a40d210348901601c011031407200050741200402501c00790781e40180404001e40720002009a0703922001001e81c0c0c140802c02800c2c0c0d00c00c00c5148185070442c81040096196403034031002400b11401103448001201905400d61078680c0e440c1602c00100f000180b40e07868649464010410038002c580089811510700781000c074190800088080c1d082d00315010a001a945030149940340d990785108441c1030f4010513003c5424240544000e43c0c1c400000351040491507078225140700710300f4940d207001e98881c0c2d9070002c0c820003541c14030581100403002c0c0d00070b10303415145940f1400840c1a0744070b10f2035002841110401191521b45d4200010030707060009141c2c0e070800c1074060000d540f21290745400300e5030071240012004541400581c0d01034225140305143e954130701c007000242482200b100340c66665901c0381418201000c61 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 326286492 1250 326285242 326285251
    0x60f0e190b1204051002040302030322050d050102031807030213020a050715050405010e06160c020a080d02030c0d2102030618161d0a0b0d0608070e070e04050609060f0d0506 76
    0x310b0041d581800e080103420b040a095511840038010002400075032000000c54861800111314210008520407480d1288151900001d610111f03a00c988000c0c00350540203113000c1c0320b503003800c0158000c6110b081070383c4d82c07054070009420100701c03409800000815806081c0c01101030920f10b19040c46950340d2000d1034074030000010615a40c0f0240010b10a0902c02d02e64041c1c405d40052a103824003184910f5000d0440743c600b0200a00e1310340910464803400c01d01001006114102c424071030251202079200e8000c0c07104801d851280c0d5000ea402d15215222240d4619455010b08100034002c403c4c060103584014081500141c0c510711280726410b0040384035110702d2703240050f02d1704c4208024004003100e6050140030501054111602940e80d01d40245000b00e40a81a00b41c2e960502501e00c0c0c80034000341d600c802443d005030f41c0000b80703540c140320303450348030300c445540e07100000c2c03040c1007000219002500c155801400302c02c00100a824500c2001d0b035441c0000b850724086e400c603551745525204d011107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 326287742 1250 326286492 326286517
    0xf0f0f040305060603150105040c020f1b010f0c15050a0905120301050a050406080309240c0607080106020d0f1d04020301080a0b0c030103081204020f090f0907060f0e190b 75
    0x1030100140003061012070342050f01103010782107070321200d100c0001030307a0180135003403040b0f555801301003405000704583c0d140c100710141a035076981c00203883c482c4c18a18000c00d080c003150400005c0c03004144114450018154046e1040d600844c0300009480106401810915551b59401050340801d03010801c040d200307440044d000b9629814401404a2280d4981c40540903900f420400d0049940220580b2010f03a000d80d10390b40090528113812450000c2401d000e2094040090500380141021454078441d40d210307200c0c211079980c1c0344030403650350016452080019001041c44010305100354014a40031045800244910070700d440058200e900c04ea00c1181164444c0511a04010705090002c1d40f180c0f00212079819585180c940140a2190b13910b2407180f40e5014000800f1580c401e01c180c56151000340075031107a0310b022440c160010b00e040c0c07440103841c03165190004a103071068020405d0395201d907448151002804003445a040283c2d54040ac1d482c1d5075200c041142d580184c003070140200c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 326288992 1250 326287742 326287747
    0xf0f060507020c190b0702010e060d02030106030501060503060319020a1a03010503011839030f02093d210606090501030b040f0c0305070b1c05040c05060f0f0f 70
    0x880a4070f861800c05480d03004807010682c0794554400284080304031030702e6082032503503950b01e80300480e03c5d40a801102a800b00d0045669600c802c2d141e4081c5050f80c8aa443c100a103980f551b01c191120f01003224010b50541c0a00c03584e481d002000d240b0058081c0c405800c410059446d0150601850303d44441000e164801000400141c5406d0141c907000000f00c60326143c81a403075448540c200c00001000c8829240144d8071913101c8906941c0308401c6203141900f00c01a0358403890014080526103006a11859a400c04900c00c10820300040f109003000a10350349840c101e64045001141c11011500c488844d414400a003002c01c150010038642200c0700900c071301c101680341c044210b9200e60070400c0d000707140c8801800040d10001c403003904160032060034031034007650b403402c5400640c980d00010010b002d460800150301c10500003030580500781548a0552685081d03403102243c00132034016203400f0414204112508144008020003150200a5447c18000300002130640e48804071590313800000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 326290242 1250 326288992 326289001
    0x2070302010b0a0312050a02210c0d0e0f01030b031002070b0403081b03060d05031e0d0b040b0d12270e010602010506030c120304090f0f0e06130602070f0f0605 70
    0x28424801c4250046070f0a640c1c071070440e03c922410510340c15425090000008a04000c0c50082054500d01010b0064413407000f8141514001640c01c03013a04a00d05104900c1c41c0d4142c81e026560000c50910080e20f1800e580c0c51010044010b002c100f012103406000e00006000340f4801c40c0014134a803070140b4812407090602d0300e0003e100e00401450303543d030030080e14013040440590f03004807600418220382482007942c0600301142180b2035560a040885501410340710aa0409000340c4150700801008119840608041c002581c8844c21070a070700451040ba01800a440e00000042009080c40c18010312480301c100041105d46040c000d002e1009810010001150481c00d802c0c05002c0c81d100900543c00c2802c040307a40d81040180107481501a11800ac051500030010307900204000c0d04140030700c424100d42c0d180105410000990900d0400340b00180c5001d00080490003040d5541983d038030b00a5980ba194025040341d2000c42d03541d184945203502041c824400098218022a80041c0b01c0c2003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 326291492 1250 326290242 326290247
    0x20f13060b0703080c120a05100b0c0601080709230a0204030b010603020c060a0e1506060d020a1805010c0309060804020607060c110105150a0e27100b060405090406020a1e03020703 79
    0x2400580501401c00040306409515141b403608100c0245020410b520750b03d1003001c04051a800c0300510b50720200304011000d0000a4490484d12504181c94005884040c904141e6504002411a210b1071075a07018502000c0c0c03821684c0041e41d402e005060503121340d2004081c0e002030b030000c00001c2d00480d0010008a0502580390041d0000d9010071043c1142d50030390351624620801c030b01c1d48041010000b0756940310300e400c83c2c100ba000c1ca202159203212014000d000320f0340b100000b60300c1000d070000c00f082650050a540010316015110714242c146880c008540c003280041080360025014002140001c20a0003030441c4601d4503111603240c0749070801101d08413a4011b0200700740740300c1805050301e180ca9000040c1e05a4407103040e9205242d56a44100d428005071076400707418401990901403d081c1e021500040b0b808a51100388903165401c010030406024901a9503401641d000c00706002401a600420420f03000b8248172030001c11441310301b440ba0440308442d0003c04d0b00000d00030101039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 326292742 1250 326291492 326291507
    0xc03030408100b19030b04020d1b0314030304080909130804090b0906030a03050a0311040f0602062d07050a111209030f01140601031d030403030504030b01050306070c020f13060b0703 80
    0x9034113480c602c540b20f00480d800181044244005003d00502c2408102591107440005000c40c5d00000d248924142040501505050070300c000c0c1c031401c1021000603a0346001100300e03401290006182410501204104212020003801c807a01107a000052040001c07900700c0944001c024845000910303030206014070404040081510784a5040803030824002500b00341503504c200340c0c5160021300906044000d4204d4403454200c1440c15182603030016861350b00055251080c440241180d20138082c4900258100e481003c1107a014940240081c07400e0b4852000b42410b44501d00e4034002c50945181c1301070800c4018510050034410018140d165030908010f24100500710350020401541100c6841303d0700e080241c0031504040e290301c0303460351040140d58901d85200040e02070700d41e1107541e45006030840d80b051208803440d26a00c000080c8074034010980d40d204030055103030a207003204154200101102100f205c190302801512060889622521480019101c400c0c3c02035624205d60401400a6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 326293992 1250 326292742 326292761
    0xc141f0c02060406020a111002030124021216140a05120903060612010b0a140901050f010e100201150605120f04031205100e1e010f0506070809030c0303040810 70
    0x981480304024180d58000b80d5180d21036000030005840707095800307003191446d41054000c540b52049a4030840d400042e03078000d50480e8000340d070600d28017501405025807566069190750141c0c01440080806800a500400e00645207010300b0035042a02d6903249840410050403101e10740c0070b0381e15802084000c11a00d500600d03103550b000d08040c3e10300d0000740d070750200414281c055242034030b0b1703403540c00c0094205141211f40203000915944d2206880491120b420904030711580c211800040ca030b0500d240d17004401141a564102210704074014481001c004202c945e0440d035990004a401014010b46a4064a010f544050b5944102c3c064007000d581c001d001860f011480c82d0a2000090300910350802540109601107000d984e5440c40070340300880c80d80315420116000041048100c0c2c0c1040040c10f001c5142d40e5031a950b600c1d15102003900d0218025660001c40401040d404110400d02074203403100c0042c1100c100c0d05200000c28210f4206902c244074652010080090403400c034000e40321312 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 326295242 1250 326293992 326294053
    0x20c010e06030c09040905030403210806090103030f03091a0108030d060f0602062d0103082101081e010e0a030201060e1501050a05070305070c03050d09060507020906010f0c14 77
    0x190f007012a00d0060910850000521403135440402c6410000c0610a840084d81c11118104509180c00c115403400140c1100c107100141c1d0361000140f0a1400d0407805040e241c01d503646c2c0d4440509403000f90024031034000159101c4007210f44101c82c500c2c18030381440c064081d1501940e1070b82c00001e00c0100341c4905801148001a41041c02e20600307900044041c1c0c07204206400a155540304251030302c00400c40c801c40f040003140c2e08004400e022203003005111303a858515981d1401d50300d040072a95a243c003030142454542020035121038280d400c26003000201da1040000502d07424040d221442c0c5400d206045001d41d440340e20070050b690300c00006540c021800c8041c0008900b664000802a204030f078040c030203014000c6685030500d0310500c1034614440e8010f20000d00704da10f9042c004ea4481c41d00240100180c0c4640000c10700d02e100f2003e80c0c9110380c1c0a8001c480c0b5440d540015600746030890501e0742000b500241c0300c1d01050501100c2c5502c00745000103412402c5040d40345c0b090b07458525204408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 326296492 1250 326295242 326295247
    0x18030e0103180f0206160602040801090c090b031b060c1902010e0d031407060608060a0b0a0510142b020a020c09071e0302270f040b0a03031209020a06020c010e06 71
    0x1260055031120aa554100c5c1c1c01540e5012204e0442280504600050a1107201190200b541001544505882405000c820320199992084902130b11450321031142c0640048901d00d2a0308074407000201c40c0540140742c0390030401a03035005460407102c032444500b51600b0140c41c00540d60021281741c10034205a407281c622045940f8003500d44950b003c1c000502a030005101c4040c80b10613803080e00503007180c40588030141498201c4c600030345450075030117206000c51320300081e6525020803000780150039916a001c21000041c2034060076000440e40d20a4074204120407490f030b114a0440f881c0b5403108000060b107440300d001d80203140c2811520700c18041d4480300d043c010f00e00c1c1c001000200549030700e480b803c0b0920264108401900405041e00300070428080c2501d500390a0f01ea0344e8800384025520001e181c01544100029100028005a0414510303d800d0011a01c1801d45001e0100343c20400301d6403040c0744d03002c118107100d603510034001600f0841401c1e80d81c1d07078450909c2503480c600300c42490 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 326297742 1250 326296492 326296541
    0xc030106140306030106260601080f070302040f020d1e060e061c0501090b010b040602120405060a0c1a0412030f0c0503070e0a09020408071809050601150318030e0103 73
    0x24441410310300c155026140200004805544c2504400702074031000300040030b5001e082c03041d40d510140414120040d4003c8000100304194001481101800c8200040540910f55020f00c401048506152072109408100e07100b05242c0c039004002005407600303020000d055081d400c0c00202c94043d080007081100b040244074007560788007c411240414070481c0ca04120041c940240140031140000705429401d000010f81003104001402c100c0c0d146400fa600304842481d40990700388554003440303901c0882030060b032155034403502d45140c896100780c2e420368400040c0ba455245401040b5001c0310040c00c49039034440740642c1401031203590442c0003420b0240d4503c1510107001400010110010410000f80c2081ea0740c0d2918644401840e00a034210341d0b6035140e4071170945403007803400703417001000c59083c0760644d40300c0320b02c28404000e070044003810a9900340004040c04650040001042640b130740003045504001990304000c881c8a40c40e4140c084162200150580707011840070100c4411151110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 326298992 1250 326297742 326297747
    0x60f0501261506190806030c0306130b0414070807050f012316021806010e030f0d030f020f0c1c1d0904051204090b0f040c0203090d03020c0d050102040e0c030106 71
    0x2542141810440410a0b10071502041043c0260b181440a80b902c18480007140d50708800e2603130203007034181c0540752200e40c524241951404251401040c4210300c0c400700001c12592500315400901c600c40b0003d2079159100303018030f8250725800280c0c02c2d4120260821051508494143e030030340080c2030024800140351000c00c0441d0b0043c20390103552200203849600701c1c020300c6c00080526801018220300c08100c80381e600b60340c40e0448880c1c1c00310340c100c0c0200d841c6160005101c00c0da010b05c04002c1c6003941c98035004802505440489071000e51b000d02c8210011000200030b01138815490009044c420544014481e8499007030394403000303100d07120782091180b582e1050324092001050b202003841d82c41d58a4414504440992400c5003d40c0220700442e02e40d506401000d11440d0845010a00c5202c0380200000c84002501403405a4030810000300c29040c030950046c03c01d4013a0055030503104e0400e0105004812080c0c00b11107a942c0002c041c0000c9002030a4590401c4100344a2825981402c401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 326300242 1250 326298992 326299067
    0xc0301080624010309021f0c02030c090402062203120201020c06070305090a060b0d0c03050d02010501050103111801020c10030b01081b0403170415031406090f0117030706060f0501 79
    0x810f04050321000442d041d91201c2142c010b07200c00c03003250401780030080c950080882401c140d00724440e0140b0b0b09a0102860f10301c8041307000e1500188030074502140355140d86108002c112007416610005580003010680c810b030704d503000081540001d80e03140c0d01c0034001410704800410200c240351801c2c0134801020030005911544540c82140051018070400000d03554400c0e90800800700407602601008000e00411000c40401c92030300203202e01d90320b07500154140c900b1050341c220041001d00461944c8114601071010300c04043c010744514602c03507070100d02803090740744a00c40030a8503003039418000e50b4880780142d400b102484019402c12024030000c20248a24480940b00c04070801d0404446000442120002c0195030480f1014004003100034001d000180340380c60042400b034000801c1c1e410b14406141c8588407610800c0380c581e080ca1000480c2c012106030050081c070085c051b2600140c50743c890b408c080c1c0079400f8422015840d04000405a00c1a842c3d0f400e0501030310f170100365501c2840580c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 326301492 1250 326300242 326300311
    0x11e03060908030a0b0a0f0504090507090e0f0f06070c0803060d02042414091b040b04030c030606050d05060106110c03031812030a08130206071509020112090305180307030b0c03010806 81
    0x8011644502b1424403601c0c280360b6820441e0301c0c91510301d0204030110300082c21494920840196420700c05040c1d016600c500301110000b0120389688004c2c000548d05a0080da07000e4001170940d4008015600814100c071880350400103c1407100e1010240b89070542290002000103200d0081e40c03121a00204803c52805841205048016640403074051180c00070b0341e020745240d03c202900d40755242892040c1000b14072041d01d07032500d805004145410b1522081c2e40030f81c3c00c5001400c0350391a180c0100c400c8600c2da10082694081e650b02d280050344c0c180010006034401c0303940300403050b00c80030401040d081c01071071144480c0e20030040d110a15404c03c080c02d6014100c96400c2084485900101e1344600c1b82080c02410504104050741100a8950102488174000c0e44c42003a42038100c1c18210403582920b1010b000b08500b408a118251817440340038502244c050103a0740311070703503c0d940c3c4c501e40e24060320a0111864040011710180e0b80411030268410701144000b4408409120b40c01c01e01c00d104503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 326302742 1250 326301492 326301499
    0x30b1c0b040519050a112b1506030f02010807020102160506040204110a0801060806010905040906140c040f050f150f031524030907030803070903020f100503011e03060908030a0b0a0f05 81
    0x1d5040300c00381d0b0744200c2c04d5040d0f101c1f001c3d04100f04005040038480c802241100700d484000c505160780c1c404d040740c4101e01c183e913400ba2060020030429001034480c54402401d101c1159002c03c01e0019526624032642d00c1c8902c28801002141004e10400058030304002950405041c04c0c00000c800715484a9454111041400c02403400d45809004171640c2c04990440c540090901010208002c000d5001003410b1160a0380c03020359032a94003070801a44501d200b40703502071820080601180c03070517001a140180000b020a03a5441e030044244034107801850030140b00c41b03404000c0004418448508404008040302c0700344040303507020281b43c1d56000940034146075010202c00a515000c0820846010350703046007601d40c030f0b4034002030010f00808290100300d000b07081c0744a100c0031505100b80403288a441c5511460b046a080c181c0d202e5448514681d02c8500b00b581c806e001010907043c6c854000d002d070149050907500e00d00500382c002901c1c0c0c8a07000d04e010703914030101044810141f14080060b240d088 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 326303992 1250 326302742 326302763
    0x71d01051806060d020706023126010603140106062003160201050c06161808061803040b19030501170d050a020f1204060924030b1c0b040519050a 64
    0xd03c602c0e0001c6c00741a0f0000c014910024081c2210b10003101c103d403007401c4a040703c1120803202520420403c003030344103042c002500a201600080e10400c54420485100000005e205a494889101a60b101d508500c0f40c0d955890040c00b6003540980105900c078904214035800313100214403e035807030ac1284020b00c4691101074800d0116807080c8100c495009103442124681c0c20440364002e41c01641041e4080480c0b2449440d00c0c4c01d0500d944540304550f840c9020704901d80c2d038400202c1908100706141c0d05e42c0e00082001054504104000d4003c20b0034107000d00e06198a04140035085a0041e000101c544c489150303020f907550000143d070200051289040e85c0c540715800740982c904452544000307824015500034400c1960140060805c41c0c10360b82c0c40307020700380d9a042d00c1c3d80045051040d210b80c0c40b031040c0001481900a40004281200241c03800740b005d146200c039051003050f000f03000c0303c080c090442803009000040026003440301c3c04240c003101641003036440070340d0f940100c1c10041035407449 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 326305242 1250 326303992 326304007
    0x903030c15020304061b0c020a0e09150a240e070c0201031508010207050d05090901031b090c02010504141617010e03070b041b060806010c0c08071d0105180606 70
    0x80c0d1000700300c10aa080155100e08080c9403d6018160300340c0e10030107014910028181c2c0c40d108000d014030032500902060704481c208190a48114002005c4904911500300d03100425103909194521030500c150000803101001000144080030b114030381d0059401e8118140305040d20101072a030044858184045101842c0c03005074040e280740e1a0040a5100c1031000040c2c540041d001070040ca44103401340c400801001d881603c4074000d4580242d0441951001440054440324903c02015001d409803001c050381c1d10074000c16103000a0030701d00180d44034000e01c070400c5040e00c6014034102402c07000c1c22401c0c9001c0002041c0d80607030300c141c50082c190103104521040003988411040041e81040e80e58450040c00c12003000442501c0c2110035014140c08200d240350000b4172801550350581e550252a00c42d1001150b146500e10001d6502d013902e1103001548000c1009060024004090b54000d00c2d0580f1411400314007059000b1401182000039005130041c00b6005940d000070121a415224101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 326306492 1250 326305242 326305253
    0x9070f0e030c040c09140607050a02010c03051216020610180c050d09030305011e0602100518010926030f06060c241012020306041509050a060212090d0903030c 70
    0xb4400300c140c2e0414644941d61031840d0344804500701b03803507011120640c070941c0c60007800228418604e014016400c4100b0400c0158450720b1301046e12402441c0860034100041c00b41278035840241c070200c00707040c03060240d80d00d0141c040c0000d0707030710000e0720482e00e40c83c03442c00300c1515080303440c60050400a50b6176450000000d000d04141c40200e007603404100030a00480c0340c0580100000e0060400d84c00884043d0b400308000340d2410011b40740558042c1590300304c0e0400c0b21002c0c200240c407917501d030306140e00c2c41040070400f4440c3d80d410600607844d0304e580803518900160070b03071481451a00b01c66410010007454410129a60b80c124a054a846544542e00801a41489030540941c00000703000c4141d000b0040f41d96920700c0c00745d80703218081c0100d6640c41c1c4e0340b5050700e43c103014000c0d0160000400900444d040e4842c50000100c402004100880c0d580d03111400c260490500716105507000c1041110404500700003a4415800d00c02000c452100c6140508003540f03034480242040b854940f550304000c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 326307742 1250 326306492 326306503
    0x10e21070b09070509010b040807060f05192106292205101b060906060807120b0702070b03040b0a021b0c090703050c090d02041103071d09070f0e03 65
    0x1504000001502d0801030710440d1548550f03c9558032964240c4008100c0c0c58540d4210f5007100c0825008048162030820240c0e40c080441c03290005001c4144104a200103d544051402c3c0d0421341e96000440000c030009038a0059a03121f01c10804c4c40c5c4a414020082030080e0b10031801555020441020012407002c1010b100e4000c5c006a042d4014000031101090102c420007510350803221002c0c8520300b5901180c442403940b0381d43c40c1d01d000000b036601c0803944a900c1a90224003c001c04602192105011854012507600c100f8031a51140c82c400c00744110340c81441d42000c510b02c09000b0061a0914034050f0740000f0300058030a030f0800700803418021856040390400b049258800281000c0318402c25203030000450f8060142c0081c0c0700217083e581c82403255500c03e056820446080c0007034801807100001401e0300c200d801c0395495011219007918000a14400d603000d07641d0401c070100c01c3c11030700c1000800c00c01850042c980034041c0101190271104600744030040f40380220082841d034000030704c0d21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 326308992 1250 326307742 326307757
    0x806030a060e0a050705150906070203120309032109030406140403020907090501110f0d050d140103081903020708030606301e010b0a0804080d0510031202010e21 71
    0xd10740b100c000411800031402c02c003e140a0400d4881850303407281400480062400640f07441441023005198502c0c1400c007910f82c21303001408458054a401c00c0c102d1003640706669203c4039502c04205140e140f00300302c0005c2c01c1d45443d4000a1003c1c106211095a05d00403030140034180300344000401c07120b03204881641d0046030002c5c0291101c0c10202c0c0c01804006050050310700055512030116040303040000c1d942000e404080060440516110080303515400800c452020141c6400c9a4464080341c5c54005000e140689811940d03200302901c000d10030342d91401d402c4c007494018480f13400421010819a58000b2041d12035607621b24401d03d46110051080d031050f468134a51403503141c80391180b244c200c0e02c104040c0801600c072640d80d03102402101400d10441c0c400354400c102d4101014461103055411512600b50541040502c40f034040a40e182110305034404e0000200820a20080b007001e144251190f00080040302d009a60041e01c50030701500c1e1000c0c140d003008541080200c502c0c00c0b11280c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 326310242 1250 326308992 326309003
    0x1905070807120f030b03030a021b12010e010209030106050102150f0411030f0d0207050a03021507170c030c010f020301060824040c0801090e0c0a030b0c04030f03030c0909020405100806030a 83
    0x58042c0c803400a0449001030021200003440e01ca00c11a0508000085890704101900180700b00300c1c00380c0c2c8200c49001d01c00c2c1140d400c4004e1024100c0c0e941024001c171000c41e894800056101e401c00e90905084600c00e0f4445030455102e016650081014042c049070054150422a110b5035250704090000380e6444100070380600c01c0c0464030440140201d40d4611411050b8240c0d06810380e40c80410417803841c07600000c3d51100b8801440c04101542e40010030b6000e20542d000003030444101900c00d0207030440448000d05400c00914121200000c4c4501810000c040004500b5541442402005514020320380350785100311611040c14420030701e07080c0c2d00c1140020b000b403003030f401e0a40740200800c40a00c5180007607070030041807a05422001c0b440700480c1c0301c090412180742f455600d6010071107401401280301c0610400020000c0740c003486030b15507001d00a1310046840d480409000300540d825504c80d83d0528070502003030000387d4406440ca10380e1403440c1b60569140c1c85240010b070418600300d200910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 326311492 1250 326310242 326310263
    0x1401020d2f031b130e0f0108061e0a061a03011701021216090e01060518030f03371115010f0501050717070507360e03070f0b01050f03031905070807 65
    0x5d1100920001d18458005101d19108990ba13a4032020b0340c504041d24980003d071200103a1140107030703c7d5001d1981c0040741d030b4000b103001640d0701a80d14944c0c136414104400d002000005106800d9903401d0301e03000f90741b107400840c80c00209500621460b040a0480103041c261212070034502c3d4450780742e80c80641034451030360800756035514015000d2b910068070f038043c0d00403500070b15074a4036010600d003d14200e080051443e00314071005504107c0c610622034010b022020710b401c801000c020044004608082c1c075483c1003100c05081c10741c5000c0102540b100101023850045c448101c480ca5414102c6400b0300308580c590981d481c01600000f040020442c0144000c01d02d41b042c001c0c001400022201482c02410710000e03d07440078010002060b0420744480300782600f07a07080100d1541f0844d2030781c42d8003003a01c0c100750056480307102611108000351804086c1d2001846139240c8030010611141d801c80c0154076129280d11038941d40305c541c4001e0b80a121003c10380e4424000b0400844013070075400501d401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 326312742 1250 326311492 326311499
    0xc0b1c050108030a030b01020f060408250807031b030e09070201020d05190501050105070c050910080604060e07080a03080c03180f1c0306030807020405041401020d2f031b13 76
    0x5641307400910180c03002174142803115000b9400812071240507450305000d440c80395982e03140c00d400c40d84144409600c0598050490701c085503000300c4414041d00c40c1d199141e840300281801003080380c0c02d140851590310803808070300001e604060b030f05601881c00e454568582da0707a414260b00a02444659000c2c450400c0c0400c000300c00703500c413a0302c1500ea003014100300c2d590302c4000440d000d00400c0741c01041007031850018021481c001c0700c0c2c19804105800000486500c0741c0e0014284003058804690031758450800e6845090b050119002034480c21004140d21070f010748000741098409007511000181c00000700c0e48004c4805180100000c4550890356000c2e41500380d50381d0b401c5003120f044541603040e0310300c82c3c1c8144a03014513000c130390f0401c0c50b640c00c0c580c1c11b80030003008020180c001c64000b82179440416145000b0f0000d49404928403000041d80b2410001c404402c65804c00481c0038090413a1200c0b9280007010305481d000402c1d40209001c403900d228804100c0e10506d40c440d080d1b51404071001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 326313992 1250 326312742 326312759
    0x9102706110f0f061801091203020903010507080601020a02090402030f0a0b180601050d08031f170622030f110304240c030207231e15070c0b1c0501 65
    0x348014900e490844040c01c0b50054050707251280c80b800101c0d50303040300000ca000700d81005c15410340c0c41000300000803500d03000eaa403034030030242d800c00180110340c010510b040300e49420320a565001c5840d0801c0d00003440e0143c0004c0d07e0721242800203100300da010b0003060a64030204020b00302e10350f01000f00c5444c0703000c42c141103040358021100800351800703425031601e8407440464014104d0310040c2080d0211120b82d9611010790f0030040010b00c4070300c8071901910710314400c07020700401000c1c509040000300c041e500210f41410002020488440300a5103041e258004010780c4c0311032a038040c90000c04071030307440320221136003e01031020036003070f01c130129001c101c5035000c3c951000040b25100410303101940b000029241c0303070704c106030250141e001003604200345044821004040002551003c040040745000180c401c1c583c2c6500c00b540c00322507018a07c0d5810301400d4030101d81d000e401d40a040c42e8059507825a400400d02982404d50004211581c010200385410300013140302c15014065507031268580d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 326315242 1250 326313992 326314007
    0x30402190b0a050c0114100f0509041a071b12030513120f0909020c0102120606181e060d0c080a0608031b0a020d0503130b09102706 58
    0x264403039103000c4450203900c0d54003a295000c036040e0780ca401c0d041102c00303401903039aa046480d280300555241c1c50340c0d60690300b44251091113014107031402c0c05082d04002980c4105555908a18001d1045505000c04110344032205ca00280059150a15a503503803102110041c0e01041800d02d410b40b03101d2081d040101c600c0c0800b1a070100e40d641000103980b9804054a0000b500030042d00400c125002d402c0090710401413071740615800e0a10490090342c4101c0401264800c55183c41d980e5404941c1440c0d2010400d070a5070000e404403202030900e1411391074103041610f803200da0381c0301e5400c1c40304a0003941030f19074a000304440b00500d10346d2212107040d00140a40342c4107419000051141c00011900f42d6144074607800d0300c1000d00250f091013000c4a850b42d417003003e8591040300c3e05c1030002010042e81e4800341c240e0720500c20406141c480b01e4030819036825852a4224035402c04044c864112152500060310410350101e1810403101d0180c40020b06000c01e2484022030010103030034000c03e040780c00901 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 326316492 1250 326315242 326315251
    0x7050a06020d051b033903010e0c0408120a0c140a050c041e0905031308071e181805010501080c1903050d111f0506040b010809072c040803 61
    0xa00340010b40c2d0340440c6a081442982e95004120000c5c804510fa6000c01c4443d901c0719090724161581054500c0100f0740242501c070b0444100c03901c0000144040c2c840741c2040c41e080700d00c181c0040e00b064288a022521040042c40342c4140d4000428440c422a110b20409902e86402c0854056050700d107030600d6403140b2029600741d9a41c030030f50003941c4050601e88903143c0340c20010381440e07070101001c041800217000100001e442e0340c0306c144807140000700340c80480001004c0500082c841e41e483c00220500d00e18031200034902d080243d81c0d0811240c0c4203c0002841300c100c89200182c000440d0704015011405d8080c0900158a04000071034040c86c00103002d103a80b42c00319842c0b203404d42920050040140e15000082443d0898244040b815015207072094010b405a4103842400c0e1420000005403018108170b903e4207a1560248005420315104d80e0404907403e10b4408401d1410110741952a80107100310300c581201801501c940000b2103004a000601d0044802901d041c2801d0800d01030b0029203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 326317742 1250 326316492 326316517
    0x30a020d050717011202150307020a0201091a0d020306060d1406010311040503100c1103130e090313061409030307060510080604031d130914120a0c02041107050a0602 73
    0xe0115040a019090503611181d1183d403440850782000a501422241e620089030000c0070510901c070a0007421004d1481045d49134024000021a800010314155150b440152031908a03480142036031040011914080c3c0c2d4001d000d641c0e5140c19010425522070351071842084c5250080a10011505191301409014266014461501e104070581c90500c151f201e003e03030540c0000c25002c07903400903400c4036126080c41d0516464001c6400d11090455000c01c00c40b080c4060742001c24040da1103003200458210450000950524500c0002011100070a0054000707009203c2480c0c8210040c00c0c049030082c00700079040d00d0f04c0780410b1401c900074100594182c010b802c2e1885e004114071800042c520711403a095520840c01e4400500b090704640113044426400996200440c03240c06101d0240b00c01582c4508406541d01c0f9440c503802d81080402034410389002020000c00c11001d90041e500220142c0441d4001100044000d031803c00d07115030030004205004840302e1405001031a80540002400507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 326318992 1250 326317742 326317751
    0x110f180412110c040f020f03040b011503050f060d0c0807031104050603010902030a08030a0605120a06050a02090f061621030606050405060703030f0906020c0a1a15060a14030a020d 79
    0x45000755401603000070000c07410b0f800910101c42900e03107508512520140380e0001854808201d420380c034a039200310760030784500d84020010400ba01d6041d110aa000d440741c6000c100d1400c01c1e854455020b88007400032480389a54856031420b0010064549008080600c00c42d00402d50324580f94103000a40d103120b5100d10320f01070001703625003010b0190543c190340c02006804400825a121005500b0241c108070b2010780d15480410351342c48408941c03021502c44030003069840a0f514006040c4c8000030305a440e21350060103001038584485002e460040822101d01d0b0f2604031028000036456004034029044020106020b000b602100423070800e5050156020300085444280644062107140f00b916081002080f50101081c4283d1081510f0300c16203070041415521519200185c1c0c01450b0380701095004441403000308209483e4011403020104042159458200106692484072004c0c181c010000001d86041c40c80c441d600300d542103040c0c0c004898880c2400c0d200c600017908049604000149003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 326320242 1250 326318992 326319023
    0x7081006172113080a140610050a050607080d050103060b10020706051206060705010608280510050c1905070605071803140a0503040b0d05010b0301080a110f1804 71
    0x814580da50040c0c40101000c4050b0041800007103901c803140c04240d84141200104e040e01c000d11403519410301580315510f48a40d604c03d0b039030400c0000780c209864884007403401c21450b22403a0703040c0c086520480b00076859003141c4c2480c038082d1199000150440e8030304000401001142d40c803849442034240ea904c603206040351002c1c0d1b078a80b180e00a40f004120207021005680c1c294500c07455010300050240f80c2054500e035141d509540d04c41d00100c0031508203120b1150958401004901e03100000311030400320702d0030f9480740c0345c4030b0410000881855031503170005030010003240100c80c1e00070100d05414081400702c0c80000c001e0380260004403107042c200004100602c2c800d444170504006580f0714840054a16a1680c0c2a020074080071010307401160002c41c00324400340003910060131700c00000380c0d5420b10b000f41c090449005800541c5620350500040c000d030b94002034190151944040d4800c1843c0d080400902010b8800e91640c0c1d004030407947da03041c64102c00b10020300652092816222880c00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 326321492 1250 326320242 326320289
    0x905151f05041d0a060615170a0b0105040519030b070804120e0112020412110306090a0314040e0106030b18072f01061e090207150203040507081006 65
    0x500203482106220400d0140a54901a48943c010101058058000080340c50b08070f4200380c880c10054a4596841c1010820680e426001e408200c0791f07442c0c2080302165111034003400c4400034241220455a800c4103044170790141040780c3c09888001d01e070b5241c00c40c2103040c02c02d0040e054041200c05903045030101d003a050241310046d00a5030700c98002031031500036101c02c680c0e00c51000819810814140c0e11141d10001510080000d86280311000c480080d03242440002800041e003581c3c007a0340454100300780301101088a084450f4185401d070b55061012034020724034040c64010041d6500403000000f01203070075600003010300074240c03030b0300c503660030301d40c501c47c0000c0800c0780e0703100c04a811003884244d004c0135211340590100103800b440d081419640c000608507203a9802c07110420104014420710700c05c0d04419000141602c3c1c50951500c40c0c10f903102c100314040b50707006d134241d00d80110228082001c02d12804001c0d2840390100c0706100062445000600114400c004c18140140c02d40c290002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 326322742 1250 326321492 326321521
    0x1060906140f030603100515030c030703030525020303030a050618040305031303020a140a140c1f360501090e06010c14060705030a06050913060b01020a06090515 71
    0xc0c2030000141422030450b042c9a0350ba1000b0005070380744c000e41050881a5009110703003401901c65070324a4102005140500d45022045034506200e50702c0044100000f0758400100da4030130610200e0032000e40c030310b081c10f041502600c0340000d41c51301001c0204586081e01b170313000320300c00e00040b18828883c5e400d049450b010038005403030190000e070f41040019070101507050f086070361500c6441142c01448068441070761500d445032104102d40c0000c6000720030300070041d124282c840075035006842c80e42c1c20340c1d0000d003070401c14180009012020001d0040024040c604145492544c0c3c0310756924224000b241603a4a003402e0b4040d00c40003e0401d0100d0307194440c90704a800e85850951048030f81e2100030042d503030784070860800c0b41c01c240b1400100404080c03c2c031583e03001d41415126a500c0b418200458000c1d1042500194041c0d081d0f00c081000843d014046d1150307480d08a0400180b0400c90310041f4100b0324080c00c0642900d08028070a401c0000004424007218030350365111140341c0302d281d20f0300b0160 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 326323992 1250 326322742 326322767
    0xe100b07030f0f090306090606030201020d020d1b021206090a12091202090402060f0f03060901140102060601030c050c0a081201120c030602030709032a0510050d05060f060c0601060906 81
    0x2070300d0750b0800d0054501601428000c18071504040d03c0d000d544e030340e80c68240c8440300400c60b201a1a20301c200110758040141501c0215540040c000244044c0c1c0011b05500c03440654400090b0049001c03425903d81150601040c1c3e410000d0341c189162281e0080c0d03590184101c11103110140b4442e00740054420000d1805a841848040300a44034a0b003c1110000c00500141d901800800c403d03418401000010010910480c040c3c80c0c4900d010701c10043d00240c143e00c0a04005071300640c0002c9030307a01240c150340c048002d0031b00040c00001c407181117a0394082c0100c0c001c07851040340d00988c00e001c1c1c29000b400c03203648101100311240c0e03210340945040106416008200e2521420140000360761600619403100c298602144040c0d80da84914044c85401101e2505580f00361828044900025031010041d000646031800010000500101345100310780e00d8140b0a640c86021550640d1101c0c101002c840d402441251143c140760740094880782c00b0301c11080410851140020030700d0041140702100c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 326325242 1250 326323992 326323997
    0x70804090507120608070e092506030f0204031e0c0504110d051819140607030506030606030a02010806100314011706070e0a05011119080d110c1023010e100b0703 71
    0x185004030080c001c1f0b0b03020f05695104d0142c0c9883c075618540d80020030a05018460154000c4d500d06070010381240e0340051088251801000309101040260300900300c1840003250742907500c882070170252202c80c1d1a8101541c09800e0804c203040c03920014024010365110b180c1e0030005030700c1c0c5241c41c01603942d000c00140d000750800340d0b002041f08402c01c180d0588070f002d000390700d031010021210b0b103081c86011680d00001c266204140b21a904042120703030750140040d40102441c680380d40001c0d041c0d40c00140800d10905884040070718581c0300f60000614038501411040e055611035101e50117501d260640c80000c1d1241c140015920740c810b20400c61501005009558120306100044640e60708464403240e0b1803007814071854002c504124841c1085000d00c1c10b040d110306030100d40e1070076120441440d213440171045c8000851041c010500f901401079480c0e00240c0d100301250b4909d020b0000380d214500c070407040c00001511650304a502d9100300e21804420052544a0b80705000c80d01808c0c101400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 326326492 1250 326325242 326325253
    0x6080a0f060b0309300c03070c06121d0703110f060708031e0f06040906060b0c0703150204240e030a03121104060215060316032405010b030c0f070804090507120608 72
    0xf49142540080818a4031042030b40e01d02001500c4220327969000f07a104c0000181c403000038010100e060302c40c001100d02c113282415044010b059540d6550001400090300c4c2040000c2444550368441540058401001c0c0085466070140e003400311301a00222a42c0d441d080082901d44000d4512043c828410603d00c168031429031121070901c002452000001c8415030307951400440c01540110280c100b60940c90000c0006505510704210302040034240300312400c5c0103200900c004202c0c8403c215040aa070b0050382250f04481c0d0044841140406170b81e505030051000034000d06600c4841f450101d195500107000720344220000030000c0c0b2540c801c407001a00100315682c284030841c09581c0e04120f0080484070291418903200d02c240040e40d0048441d51180541c051061000744480f251100440f241005150b151440001c901c0c40000c02c0c520a08100107225480c20b00c040c4103942141783c011018070f03143c0fa00c1d003009900500007650080302091816a5a5404040034020703002a58494806401c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 326327742 1250 326326492 326326573
    0x203160f1e18270905010902090405030c01140705090d0224041a0a050a03020c071e060e0d08070b0405011112180109080d0c120e010b0a08011506080a0f060b0309 71
    0xb0051038001350403601035480b6078410340540e50f80300c0203500890145010b15070303402c13000119030308540b580c00c0c2c0f01014804160810111a0704171060b10400384040e111103225201c41c1c0300240c6442c04221820300d440d0b5441100d560b0646e01c001c05803066501000d00f00880f6112442d0421080c081c07542e40f080040c00c20088d842c10396100e0380241c10b5000400c1c00311401305440780d1515000301809a094440a01d80b104100280b6a00076a084910201a220f001c20084141c846016501c0342c800c8c06000c088400b400300c4c040100941c00740104080e030410a540301c0f1401044444001416a05100078541c0190354840340d24062203003009055010541616100100302c40d0300281224040c40d03414801080c405602d4039016000c1c010001406100000d02e044a050400030a1a450340008400d68948003000f0502d442d081d142c141941d006040c04a03441e83e0301e00002c00a0018520241000b505107440000da10031210040d41c0544400c81c10345a4099038904140792500ca070340345520190b40e03100d5000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 326328992 1250 326327742 326327819
    0x2e090207020f0a0611070e0f04030f09080105130210020303190f02070503030a0e010e030c030d0f0b1c05010501051206010b0901020312042001030203160f1e18 70
    0x205522440982040c2200200b02c0000d814608542c0c0203001141d9004c0300ca03404041e041c0050b001a00c109100005130b400d004107400440c8000520003802d0114821111300380c14010742c081001000500c0c000d000034904080c40e1000c0240c1c10b0412405404034640d1941618000f1090303a10907504e14000e00b903900d9865149401406401130121287c86d400c10208002c2030080c0000d41c801c002c49103000c950196102211804c580c02c0a003080b01c0da800602c4220040100482210b00c01c400c00304010403a0072000131a20001d00c08949416401204040760042602c005014800c1c114020802000346a0303036032052280c0303140220740340307a01500180d0051040c48041c80140c0035500c0e0610450b406c0c40c86140c2e4000f21003000755429990340c03800d9420b030400c041c603664855415540a1805504600341403100198a1250307134264410300c00d4145402e11100e1080c1c2d0405401410b008034424100342e8103401912100a001c036442c48a2000000445c0510300302d8480400c48808401d02e5803c2c0c00400d008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 326330242 1250 326328992 326328997
    0xc150b061903020408031b0d0507150905340608101205190f0506070c02010c0b040f0c1502121305060304061b2c090c0d090c0b032e0902 60
    0x8041410740c04d2201080101041020b040920042c0051001401d01d5400c483e00c1c0c800c4004010f42084410030095001071282c2d030340d01c001c07100a000e000c04c1040745032400c0e0b4200301d400c0c0c030000076040d903458103585680e081806070042810131038940b0441d030740c40d010101d88a081c110707400342c400e40b88a0420071070110402076816009006d20213a076100c038030343c0c1803100400d080c1d0032041d00d99a8410400d0828850240031103a00f0080900381101107220b55400039042c03080d40c2d10064180c2c4043c81c000340030b02642c1140c0e2044968800d000580f81922440041004014559500700601c161040e00190030f000b0000c40e17103144010061034100e5860813040010319030005000300d03a1541c6441c681000c40012640f200a03010141d1030b2440c8040150050007098012081c115030700300d050040d84031164441d0711456400903000310055945155110440300034007e20a401014a200e00200184006081c40030b140900307455030381840750b036643c00c1480004180008400107442041c0d101004040f200e80d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 326331492 1250 326330242 326330287
    0x11805030717010b0307060c0209090d0905040e0102070b040804090b0a0e2a12072a03030e0a0b01030b01060206370f0203070801030605010506130e091c0c150b06 71
    0x444c500c2c06940210b0b0426890307a025a0102d610041721a0852912000c0d5561041707900000b0150185070a80003041c0721502e1050a000755a9203401e882c0b101c2b000c0d0111204075800240344003507410709160542603940070740b14500c1001d00c1d0212040d5685004100f440445110a050f814241c5504100031206c400c814001d80d85810100c01c8680b600391210003405940c491131078031030218501804040c00030001451a01e10954445004c89010090a0040d040958041c5400101121132286442ca81240d04e203020700000710690002042000c2100454160703003c640c01c0c0c51507611542006800807004525020070003070301d501c1420691060881c0390b002c44900b10000b14004084111400032079000f43c1c0c1d070a0005140b00010b0007030041c01e00502e0300400c1d098882901e0120203201c1c040b85030085001d00c001005c0390801054481c2000c20641501200100da0000850b400f1039015186206004048401100708100111280c42500c2010807000d4054800c0785030820003001044507800042 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 326332742 1250 326331492 326331539
    0xc02032103060f0f150d0b0429061b0a0507080a020607030c151407090609050a0b030a061a0c0607030506010c0f0c0e010f14030102090d02061308030a0e0118050307 72
    0xb001c401e01581c40c00d85d110002d045c0c040b00e05540740a1104e4020a84101044d854042ca051076204403500e249001c0c7c080525160039284c400000d0001700040c100e200340841034401c10155100103000440c086143e542d401c0c4a141100c40c0b99070768071042900c17010b900d00060b6000d44244081d40c0824010f03151522094801e92aa480b84041c0c2c0745404115a0499903403a0040e134400100308480c0c0c0c01545840242c11141040c0340c42c1c0d480d1100290300c00c8410f0080400361080840400c40010300e40e007052001c3d0045c01c5a1300c000e0007031001614080d03003009180b9961881a14089480c07039010340300340e41c0102010307524040b006116443d40c00a071311103074404552000c1e12100c00901c0641d8114039601038a0304d002c003440d403285061907102450400e10031321031181e4070400100c03c89946504074420132a80c155070340c1c0d4440c29216000c0035060055800500e590000064546500343d10024107089c84c0b00c00d8031421004a10342c0c0d800c0090b04c0140c025030b030700f56001c00014001203402d0641c94041600301c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 326333992 1250 326332742 326332759
    0xe060919050a020703170f0c0c0703060e150a0203040203280b180d0503010f05090601090801060311010305090105060f09060604031a01030c06050f0a030903140a0c02032103060f 78
    0x4000c481141c00031100d610b03510b90301040860400d80e200c202c598680300540402c2c2c05034200481200c01c0300320013521004080b40006a03809803100184103050080d5001881008803941201c0425129103110602d2030300c0e55101d400160100100340b003600c0c02590050300529402d0310350107507003a002c1700d070140e8228a92000d1450030002071120b02e100b4415242e00c0e034004a40702d0b18024983c6050441501801484428001405152000c54948080703450865001280d0b80300c4d1001038079000082d4201c41003e509180010040c00070000488480d0715081e42c04000d80c0c0e071723080542401c0742c034117403600307984442c070000710700a01d2405400c03c2d80c22003c0284201e180c6a41c0e40c0c0d40210151011a4000d0354a16010041040c071070240c8200c001000641030652621004504003045171190b00d0f514800d1554034100c902c141440303000c568080c6810229910f5a4a08402d0f000e491034101101c124417920902c0601c0200040c00464900c44c03102d2146141d09603101c034000c11181c0c0150600c4c00d034100d1201c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 326335242 1250 326333992 326334031
    0x10f09180216060603050c010c02061206011e0f1d220b0604080708102c0a0c1413020a1205090f01093504060c06061517060a0e0609 58
    0x5102008041c0b40c41400005429891480c2450905088883c030a051150720075000026880302c1c811a0300060b00008034080b03c0d900e1100680b20b808441d142916640100d585000e210754101d00014038400c603e41f19420014244c0c0c51000c032003841c0e2051280c02111250300e00d6490031015181c10030038200d040c408603110003000c1c04100c0540055108501c581d21400c0204550714007400741822030300c20410300b071041000c0034080c0e54002a080c00010f0705a1401d9441261280701440a503035001d5010362026102c1c0d03038070548041c07819108841c0e6486030640101320707840700c401031003120004101ca0311807801c2101c0202200307004000051001c071103802105030340c210303805080c841c403c0190711483e001c2d000d41e02d49286480c20b03072040d403040c2e80c2a14245490001e40c1a102820345040303c010b440c140581130780d203182c00340190525910041710420806c50b42920f681c0c0045595520342c4046a00d10840e64036032080009040080c861400f0606041000c54205c0c18088003443c2d001642180011855a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 326336492 1250 326335242 326335267
    0x3020a110f060d0f0902040c0c03031401080c060c0f0a0b0712090b070f02070e0901020a0801140625211d090106110a0b25050a17090c030307050601030b0105010f091802 74
    0x48103040c0000504644400c07270402d40c043c4140c20707090203810f80402c82c035070401c41d1056460f101042124429080443d890400d56001c0041008907410070702a1075400c81c0a10300269547e500743c80d0f420105942400550381d0b0744680c428080d2982d00b107594119640c0380e200090701c41800320510981103019100001c0380081e000c1031001c0c0035011840c001a520b8410300c000030040d001c186c0042e8800050011264099a200c00642e4810001610807848030501c104120010b02001c18004160042c00c5400c515108406a800c044440094480301c14841013540d00318040c0c07001e0440507074866002d0300140480c1348501c40060703002014504030303082c031003858070b84002d00d4030b08407058104a83c4002c0d8807a0011603048803440b006001d402d00d00d0421001c000003809130700301ca45032030846e0290400010300346281000700e0407002d00d0150650755143c045080640c0c44810901040d2203032a00540005850b510482e5020708200c03450352008900c1e81881640300241a06180f0303a1816502481004030280 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 326337742 1250 326336492 326336501
    0x3240f040e06010509070906091a160b060f040b0306040813030c09020d0b0d0506060d1104021206030d0c03270e0a0f060f061d1201050403020a110f060d0f090204 71
    0x540000610003513142404010424100070921000c10102080400000da049150755040c0c403c0c2d12100c03140c41c804524180614000c4130030920b00d4100301052102485154030487d0302640c0240c0e00400403000700c80500c401e550f003041b0b07055090740c44100041d012500d00400350020141d02c1c400030301030983e01d494040b00241560001036100703038001040d907407400d8148a00c403000b13101034036000980c0e007260701c85585404000f0001030140000d03c0c6000108400515001401c1030010000c40d01d50141440490b500d400840c1d03098041e200c2d40c090703c80b13202e0240c91040c2c10f660703066968a940322085080c16440d1460075102501e0264454404507404009100381403181c0d081102c00a10801c0804d207210a440c4207900c4002c08403880700091101c0c0307034064807101c052042008103071103000780ca00119100140700c161001702546003c0900c800c155002c0780050f012030080740303030100e581228800c202e4010300c0145100c0e44030008001440b5085074a400254010041d07142c00101d030007054004c54180c5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 326338992 1250 326337742 326337761
    0xa02091e010504110904020915030112060518070618050301050f370c05090402040e061206010b0d0b1c050d03060609080706080c0d090803060f0603240f04 68
    0xd4034060850300003008450429401020200c0c0c1c140b0a8091050740c0a000384a1507803140e02494001405070240c0e2924a0b0700150b146000001c11f035a5a52440c0c0380f0710032000e13000210340d5182801302040c02c0d2410080308418170090b0708050020642740400a4903200c801940141d41e04240c004005681e507000c0c8103c0d442038900710340504541c54080b01c0f51101c0c4a14070000b08042d00341c0e007812500c0400c104540c00c00c00072144070008408501003000d03540313070055600460340540000f0300071501c500040111405200150341056102210b24038068071f4680901a083e0460b20902860220b034005400c020f119603405451942c60342c0781c03100001c0d0100b01443e820340e401d600040ba9443c5460741031184400620075413074207070116411300d030340180c64148a2141100b040640e4020940c0c0c0d0480c1030888501d001b4544003041070600310300e0010b40b0391f0000c40c0c2d4203200c2c2041500b0104903040c28802c680c45034800382400c03003201022011026003911032021403a000344400e80c090f07080d0b80341d038400c44240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 326340242 1250 326338992 326339011
    0xd050f01050604110c0c01080a1415010207080316081b0a051507020c030307080706061e06090b040608061002120703030506040c09120b31030201060f050303040e04050a0209 76
    0x242d16008050009503040120213048a000030091034070340f40342c04500140d02c1e1400740703803200080d2036002c00f02003d0402c124160407003040c036905002e000303413900c8031070491510280c00381c8166036520450705803640202004448192003561024001a110b140140400b594000ca4a46000071080c906031403d058143c0c212201d5000f4070901d1858a004510683c0c4040340707200500c00c2c044064003185d124055204020700085000c00d042042244d40d80122000e454902440c642d5010b04e00b1101603503184601c00d09020840302100420f10707940369400c5406540300b503140d400403900e0b480c00b8007035088070356641d0408600560700000084000640241b100c10301a40c2c011900f400d00740c040104442e1004d07a0030082c0701c5104810041302c44034080c041000d1b604504510341c5980e44429008c60946100d400e4032070140e540d0300e00c0c010700c0c031524551001e0030b000c1e50003081070907240c4010300c10b81d9146003e00d990603030003800304001900f051480207a0040c8035030b0a80f80c080080d0742c040303441440c0a8520610 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 326341492 1250 326340242 326340251
    0x608060708060303030903120c071703190204050a0501050a090b0301091410030f2a0e010e28090204021b1e01090804030209071110270809060304020d050f01 69
    0xd9580101e409412020440c040c6140d8241a41314558074030440040209072a80c9600042c485007800c0e003540c4015070490310704400c04075900042481d0f6032086510a041e5040415050701d100341030720030b54060b100301400d031400290a00c0010742d0b840e0810081030b401c01c82517420100f06c00d01c40b08051802001e222001040b41204c80c5509880c1080c018a8025044203800080011420410300d00a02d55001403241041481000034524000b046554041801ca00304100154001c0c03010b440c1412181c071074900c2f58140c0c40b100c40c01c00b545040b200b569078a95100312800d40d141d10b074590103109540e100810041c41d080380380d00e0010f03c000403840c800c08990024100041c0700202c1c16452445004040020070404005035550038650156001c0603008060b620f0005040700e000f241001f455404803001c40310039001c040e1a10020704082e041c020085803100b1040e8031420414102a518294000207881c00c1255035401d0046d590002801664410704d01440307140810317014040718036410102400800d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 326342742 1250 326341492 326341501
    0x50a060e1b04020c0717150106180e100302010818010617010c0912061d0307050d02070501210b01050f0a02010b03071410120b0612060307060f08070c0213060806 71
    0x6004a07500c00d800c60246004110b40d03030714940d002c91031100b0780303041c0c030550b41d0b050b00300c0c0e083c940ca0b080c410b01000c5144e002c030070004201541c000110301101800c0440c0c094106c0e4403940190071403101964010112080c0a005100540c000c142241d070180c1040d00c114a0703ca0900c0074207007075071941d034000520a5480014040000c60038040c0c84c1001c4200e04216105a03d450f9a1040c0003291110213414641e0710002300031441c0c07070743d034417205084580302c104c0340c13600c00605205840302c80c140070b14005413040741000240ad502032660710345001c0c4c80405420311400f00c2c4000c1d5000c1d10760b0700c0f0b95604004040080100c5941030300060040002150b00005002840800303240c80e1200a42100302c14441180c003142050b074580303004483c48070440c50702e042d40100c1c3c980710780060140764260642c4040c2c0801c07030340c0703890807c01041c5114000407000c49007401d81c0c4030b106403840c0c4540c1c01036070700203002003000030740960041c1924002548090b00076880070b86201d401c0740480381203400400c4503810010610 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 326343992 1250 326342742 326342773
    0x306030607020118170702060304081809090c06071704080d081506090418020603090c01030f09030516050319031409160510030f0f1b0e0913050a060e 66
    0x100d40c0010075000811a80c0001098804811081d4400400062001882200004558050300c100300d0703000d0f040c65100c2c03c2c94a042c0e800c42d0030030715200c95120300903010580c03035141c88500039001e80a030b60007402200840c3c0080c040b1960118200352203000d421000a81e806240c40010f01c020541103000c0c20040300010802007070b000c0041c04040c0f040f014400d00400a41d0390320100d42c5100c0003141c00191000075000c214213070031000342d006903011401104000d82c107003010501c4218900300f641c08008000c8902d1801086500340c00b009400143d0034040c11001514405540c00c1032401031007242d09000e0300801a00744403100c90015800652078000d01840200d10860441c0c00100c07140160a1040c500d0100f19000039240c401e04e88941d0b03101040d05059400799008501544807150140050121200850b018000c152142e4045900025201c0c0420b03102d1030803512a900d000b40503810f1921032000c54450312005050688180c0a0300c2940f400069207072040b2090780490b60080c00441c40c524650 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 326345242 1250 326343992 326344003
    0x130b060f0f0906041e0801091205031f0306020c0d0201090b130816030509090c0c100b010311040e070206010e0f01090218040c0305091014011701060e100f0b043512030603 75
    0x51585032303051400a000140000d010420000c106161941d225a00c1420241402200313925031411000812400710520080fa0020101c404201007121414000e07504202e080321913402c2c015217200b0302800401c10b45114101651482402122201e060400800124442810100c800c502041c0001603408041c28a2102c0c0d075400f40f08505120309200704c0d00c3c0365a4542c29498100103076076076501c625103010307802940454848005410455262516511500e40100c41610210098032a80e000018a0241c6002d0f0074413860f0a82c01d80c084070791030403a000e4040e400c00090109280390040703804000e502d40e8850b1403400c4000d0b690104d280d040680310641810725403a120b803d1350307041c02c0410600418603100d03a0b04540004044c08078450703801c810540100746c950020f01004490205109444584002070341c181d43d030382d0310b42107030407a66030100c0e42c201e229078403441b450b4048246181400c2040b40c80500751214409001503000ca070005202818140c0c04105001040301c00300a009090408009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 326346492 1250 326345242 326345249
    0x7090e04200319150905100b1c0c08060f130b04020d0b04050a0c08030a0c030c0821100f06120207060f020a0908011103042103020d0507090302130b060f0f0906041e 72
    0x40400120306261542d030b0300c07101e900103180961600c85c03500d488c07552101e03592881210130f211860448138901e8500000d0700c11141c4140002ca00c101004201c1c4c100f00310042d00c5c014030700c502c450300c0101c00703540d140728101c64002c0082e070340003c8030304000b4003280d000680944540d00c25000361024074140e1a0a03c403e80d40f0f60402785040c0d2081c00091055078022406040b0250141440c00c0a000d01e0300d00003200c0c2c450310400c069401a00c640c2d0120b443ca40c100f0290284a08041d0f1035221501d5101c040e010440d240300d85800589048540c038081d2001e6030080141d1405540c0120f04006000104d44c1030340d100d011001e00040c85010304000049003803281c26407454404000380d00c1d6052603195868141e1041c0740c004400d005d280460400c581c02641140c4080700464401c1c0994a80510003502c000b0903480182d00482000b1104840c1020520829a036944002c0001c0e0030900c01d00c4012041d83c02120001d04481c00801500701c06564510252008001107111050f12270039816050003a88a20307807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 326347742 1250 326346492 326346533
    0x5090a240605090f03100903170903030402010206041e060908030604140105060f0c190308180307170a03060906080303010906080613110a0504050f0a0507090e04200319 74
    0x100e061107800da2250031a03541c1403040f100984034010380c0d40040d040808004000f5985031400051008140d0421004941c40740401200223041c0c2c4d030940c215440e817004540080c010703041200000c000400c4102c652061881c00341d135001740407519940d004211500d400081d106441e010040180c0351802d070180d09049007103480380d024954036142c0424600e02a2841207407184101040b4010941010410004044098481d80e0348070a16810003508241c0c0c1070f2646510b0f0707465201e0448002c40300004603100c403031340103230b40071a9440c40006031495038002c00d9252003050748440d400685800b40340070307a00142000402455480d4504003034a001c5503e81c0d4000109500601e0400240c10000100100c48681111585a4045c540780005000c1c2c0303aa90410340e442803415080c810b0f84404801e4840c4207064040c410055034460700e03000c1c0c0b244080341c850700702100c803403200017000914004080518102c0c100321818440000c1c40009040c03040103030345003000414454110342031041d00541490b000c1a0710 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 326348992 1250 326347742 326347811
    0x7030305090c0d0314090f150d06051503070c050304170106331404030803040b040212072706030503122418041104051f09050708040b04030905090a 65
    0x160750103018540c000d403201d0030b00f86006c1000141500d82c141090382009000b41900104809003040390300300d402c0b4000c0c030440249484c41c04561800d00341a040c0c0300c04184170341c0034119030381c0400889080903d03003011a05408140000201c501c3c0b13280c2c1805403030310740500110b181824509038000e00a105a40038803c0856183d03014015050030b640500303105120724220443e0440d0300c005400c94802c540c002030580a0000421050008020400e0300441c8201e56031002c2d00c5401e481c0c0c035507a1741140624090607070301d42c00e02031010403e01003000315030400e5130300400c419a0f02e032039441c05c0da00701200013551214020b08100d1340d0004200c80c54448000710b10381030700c4002580d012480211702002440340c0324988402142c103005c0c00c00c032030301c6071079000500c1400985030100314003503c180b01070f080c920a40043d44004c01c0745481c60151034032503400b0341e80d240401d5071580c54008074400058030a03000e00084a9022885071240c03a1520b02c035050b0007102003003058491001200d00340c0b8004d503065451549 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 326350242 1250 326348992 326349019
    0x18070201060614310302030a030305160e100c0302012c0d09080d0507021f02010c0e06030c030402150d0c1e0206101a09030a0b06030d02060f041509020607030305090c 73
    0x401c00c20050f081e00c01c0302406500c1c034407003807a11a84d801600060350520070301c1551000c2540c1900114030a50806603403108100582c00b0560f6621281d2200e254002c40c00707254100c220340f0442c50503591900920010a04c1680c1c0881e640003484550b01c40b07080c146508030394030040c0d2001c00a404003030344140703072440c3ca003864084610349a4014a4401081000014112041d0350755407070003601c10807030380300011203a8900c207002a00030301c40b800d410030100300800c4d60803442c2d140103000e513031245452008542c5560748907401c105000480e50b619002c4400d062151107050341e12071141d080d10b12406e4a9540a524441060181c0d002409903018115406002080700c0c600001c040a012212941410160941c5001584040c1e00680c07400b143c0500c692543e10041c0a0b5072a0181d000c0d4078150161043c14038000012a140e004c11184050606502c0f408240050078440441140b014503e1000525600c4d43c1e0000d85142d00442007039000940b20021301081c10014000e000c03e501c0204d82001300b068030b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 326351492 1250 326350242 326350267
    0x4050f01060b2104080d020309060a0c03060305120a03090506090a0201030f02030402031b060c030a1d010c02060f07151103060102010605010305090d1107121b080316020f18070201060614 82
    0x40c9000d803484030f01c21a00200701080740d84802e40e120300407030100654503803900c6180e560307441d80105c07501c40149081c405905c161178003034400d40781a2030b001405807465424500b02072289900c0705510b4401c050741c4224040209106008a500499254001d0000162a03000042c1900c08031207000c5491481001031200580d000a0340b400c0d0700800315104204014003800050f26802030404101181c0000910292a6603004044813002103001c0c2420b50030309441c4004498541f85090000e400003001c100058110302e400024211452081d04e407140c0403400b43c409541501d1114406000200000c8148486036030207014010203008280780400030b81c034010513400d64131030710500564180712004241443d40388051000e58054441d00c443c40c540f40710b0500c3c00c580040118a100c001c641c9a404011850312800301c00c0303440c2c6d100320f901880c580040a40030450031544403545035501800040340c042101e501d0441c0c0a2040f0581d40001451610342540507150000c0103000e058104030410a000b948075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 326352742 1250 326351492 326351527
    0x612010501110f03180a081b011b0c0e010e0f04080a14160b0601020f0d092310030518190b070c0b040b01031109040f0605060d0204020304050f01060b 66
    0x11000d20700461000c1c0d20040c4203040403c01d028030400d03404009000d6900c0e548521051480540c00e844070403103559500740c040c0c4c582010b0340d03609041e01a05d8040008079882007408151404102030708010035071180c0d95440311204258410446002650300400c1120b9482741020307030000c0450160750040c81d140e50792600034031070809038909010066002d801d1415908054448100228160180c3d00c0e0312801c1040e8031450403903e6034010b10400d600c000c1c400202080c40a0001d800b52514031b504e0f402d04c06094500c95131001c6094002c0580d0014a4040d51220307110200c4a820b902c001031541803070341e416503459003400b9040e1119030040703284813010722503c1c62782c040c001d80102070640365484560045034050013200e0090001c614050501084c03000c442d854504030b0f842180c0101550a855051060652040720080d000e0300c0d12a07840030202c0e2160304040d078003900003007504007000481e0380080c00700e0b081035409039a0755200c411080c0e4446800d00c1070002500b040031800e42050382240f8885c4802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 326353992 1250 326352742 326352749
    0xd050f0123130c0e0406080106031704080a121106070c0201020c010c0206040b0304080f041508010e0705070b0a2d060506032a09060708121b0a03021b0102040b0d0605061201 76
    0xd40d220000b04070f082c8605010b9007403100040083c45010390b60b0181e640070b8011400280c80c00b5194001f101411120030007103804907480341c4050840220f0ba51113030302491280006c0001032000c00c103520308291000b0b00425214410a841d071440c0d01032640002407410351502d6699040c050400703e200056500d101c19201180c8004c111a030387c1e40c3e41c1d071518141500a050302001888c80c00725010410148505c501903020790182da448007140ea0301c40c640c3d03034818003d0b119240400c40812050011916202d062648040d0320440403950020b10019250780040c078400310b0510f880c1c2050ba102140c800c9004580c0242000c96030f060840c100f400e006002c80d200f0700c1c010800300b80c1c440c4c020000d001d00c0c1c000741c4241f214010010342d124049410031012941c4003030240344804420b0b400040001502022680320030340d4560480b42400c0180806800a40c0710101c0d591040b8480c0c480010000c0c000d0000f480030f0101042c0c401d440d110718240d0360041c0c4140d604498410001440544442925540000d045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 326355242 1250 326353992 326354029
    0x30d050f071407030302030403110402120c07051e070612050919031b080c150405030f090a0b130315050106141602040501261207030807050d050f0123 66
    0x140d841c0d034644001d240c1007100200304103006040e000028144c010014000712405207000071010080b500400c0b04901c0781d10b074a4540c4116102c08500103403014400340c01c145100301c1c2140d620b805198215045407521906420496200800074042954414031240207040030300d0050049090a0317282c96100d12080f80140c1e0307001230070b8021000b49441820040c440c40c10f81039400d038000b42c0b54100702e5069405041100840d2040c200d0560300720341c3d1001120300c541d80040265050400d804e9500c5201c0d400745240755404070b0f4006000c039003004060010030110300c072694050303003003407542c40c00d04030300020340700362400c4580381c000100f10241d0004602c03001b140501a4041d602c0a816403041401c000b400c402a40062500002190380031644030f8000801109035585110f0142c0784801d035640d19170008100b070400c42c09005034030000307000d0650960000d865084ca2410400d0840d04a03003200c0d4100c801240120441c0010070640010134440076034402540b10241410540308080b55103034003c50300030900d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 326356492 1250 326355242 326355247
    0xd020607080f040b04150f08010509060301020d02030c07060513120c061b030f0605031207020415080d020303041a04051b0301020405060a03090203060105010509030d031e050f04030e030d050f 84
    0x20001c00c482261802c40035140309640302ca031207807018103d540040c01100040d02c6407212001085000340e20080018035039584020440c0c0c204028402c82a070040d080d0b07500740d90240320141035081c690015601c64031890400c0398484807079060240690708041c10014440f02c403034020002180070302e0740045090310141030807410350615203001001002c003040344503101d0207244503400a9a50540007031000072081c0006024103a1900c08264a0310110030803000030140c200041001802e150300701c00c0d0224500d0040d510940d5560394514200407504081e040140c200108200801ca50032901c0e160b50040543c0d13407078080c60b065803081c1e9161109000b0030300318003094168910b01c1c1c2c0e09404580250201802054031401c1e40e080c054003800748100220310900491002003100d512035010ba0b4601c0e0305c002d00500c04400e0a0307c0a500034150340040c42140034100c17401480342c1080b801240c2c0610745003401c5654914150600400308144034040e20310a030880a081031985602ca41560114100d0398101907 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 326357742 1250 326356492 326356507
    0x8010e030d061d2422060f0803160203032a06100e0604151a041d0411010c0c2102010201050a1401171f0605090a0213060e131a03011a0d0206 62
    0x1452001c130910880d9011082000908080c0304180300a80c40203d40d00c014090030392691031101c20322001e4083c89045500601075110001c807030710f482c226494000707403d9038501400b110000045507079a0601e00d0b643d84c01d00300e013041c80c05403c010780d1ba806425420303c06261410f202c0c142016034800b0f0302c0b951285484402000319a1800c2d0b011100038a020560602c0c644c0e058120503456030004d21450f1810b90140500103804503499010500c90760f4041464003820300f001005441042400da019a001103242c2808036a202603048110700c940070700c03024920343d004244002400d641c00102103203513550401d08400145100000c400303064500088818000031500c400c02e61920010b101c011005100d90031102100c42000d03409801070311010f03280d85509030345001c0d01206074420f45000d14a8800b00490802219106200e0f00303c0c40580140300d101000c4801e00c01c0001e41305076080800035050b240c505800c2d00c1c5004d1064401c0340c0380031503803101104190000106003040390701019001d108000b4004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 326358992 1250 326357742 326357791
    0x2120402010e030327270703200301080304050a051c14190b0f0f040807080913020d0c1d09190e0715090f080303130302030408010e030d061d 62
    0x17250800d406030000414030148125891401200c40310b8280681518504c030705500c01200d91001c0c0750358140d007020115881d090000c5004040c24448240710040c402808101007140720001c50080180d40001d41d101ca04182c10415071070381d960301041c8075401c540d0034203030302c1c4007505200c6944c0c94100e411001d88543e2801c07228284030380301071a86140d59030140e10700104080c8058803405884128141e480c1d6a8507403803032403440c45003624050701c500c0c0140300c03541c0003032060f40003048002d03c0a410740d000c2404241000040c2e0f00106500401e80e9250502c01004642c03125009650b06200f080c0c000c000200500812401c40c0007600a941c101c880407074042d9520351070707002080200017a0045400d441d5a030980e100613903035114625400100400400151000b548003004195508540907603c0d40c0c031a403a8010b400ca9401100f1015808240700000b0952400c3c455038540d51a00da0155a0340e0580000900c04c9900c541c001c00c1c07480c0031803071002c0c440c140350f840110341c0100c20300c080644490840050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 326360242 1250 326358992 326358997
    0x16110105041802030412020d12020c07050a080a061103010f09020d2007031e050405010804050f0304090606030e1c0804150c0c02090f09250308030c031902120402010e0303 75
    0x101501500720545101590310b10341c010751086000d4181c0e01b84904e90000c08a0b103e0000c801c44030006805901c10040031005030f80104000e100e9002103030480d0ba52080440c2c202006030340900c2c40e41d0440040001809403900500061030318070340c130307442c950b40c18401c400000d403550780035200910358049500402c03442503503c00007641b21610202002200180100e004951080404500040b048101c00140e618180a104400d1000b91a041d080c24200801100d508100410a4030140308641c2d084a06070000e000030030281031180c2c400314060f4203005024050301c03001404000142d03c03d000d03a083c840c10840d000550381589107001c02941d00c490804440c807036010344c2200d800340c0c0340c40d04002c0724075007161078020000e20a0316054255500d1409802d020031049920342019000710042c4003800c00074810400c020350510503460100b90b00c4c0d44a10030650400c6994040c154000070901c503120039401c000c405c541050004c25843c2c2091b000016203020307805040241403001e481c0050310b05a400303005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 326361492 1250 326360242 326360249
    0xf0804150c110f0d1e050f0c01330b030112030e030708030a0c030833060708070b040c08120a03020904020d020703021531020a051e13021611010504 65
    0x44503c0f00c400c86445030340304c402e411303150800305400340c00e05d4504040902078040b04012035100c1c581004149442201c25034406035400a1382d560312000e402e00e40302200d924401001040582980d4019030b1071800c00c00c8200707038018a80d40481800100300004564078494100360741850404039450180010910300381081d08501598040481c4074110030340c0c0560441c080c14003950340d05845403140b201c4180350600b800031220320381307101551100c1c0d0b508200c003d020380000003525862802c11152150040c5c0c1e04030040440700040b0040611080c04520f501c124060222403010388007195031000721940a03c1040b00c00d105250700803c3c0c06000e0755407a13041c0c0c0c00c83e1500c001c05558900451400030349980d03842d0881c0f01c0902c18400440c440e50031251103440c0c030300c0c01801d1203043c0081400205240044d15141203038055002e03900403031547c0320341070060110640e2040840700d01d520f203402c00800b5804180380305445441404400b031104200e08980500503088400c04070510150801250b0a208130382 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 326362742 1250 326361492 326361527
    0x303220e0106030911040920030304180b090114030a33050610140f031302030d08330d03020a0803191b082d040803070f0804150c 57
    0xd0001682940640054002d2442403007141c02440d2131313000300000c0360700511015151404028603000141072400017100444002801c981c185aa0360350703c8403900c42d24141941d0002c1d150b5000c0c0728241030030f00e55103000d06030821907220b07010a88800310759101404540034142802400343d940030b0348400028004140e240c0e04e41855448445050680a000e05a80c3c1c01d004000c2d40c000d018401c4e208080c6643d100031040e1005141130101e00440c4103640020304480300c082006c3c0d4804005a0b07080121030003141240e281c640a030b00d8802c0110060308a44091001d156a03814420a1046a000703450309405108540740082c640702030038200d25003886040c0007031054100109020407007800d00e290890302010184d05000c07502e1076400300c1840119490700381002c01c0001001c43d40c0441860920b241e9040c90340c4142543d00b07000c0c00d609644120507101a02c1500c0300106004100d540400080c562650f0381c1404e82003800d260743e800c1d82c290410b00021404660320302100980c2d034030030070303040c1041300c01c25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 326363992 1250 326362742 326362769
    0xa1a0301060b190e0d0b0601020c0d03080703020c0c100e011d060a050d0b13150b04030b01120f0803010e060901080114190204080a05100e07240504091e0b0f030322 72
    0x603c1c001c6c103050010341c0d40d54058030914449200e9880d0040c4184035156050761214001d4a84004c158065044103900400750301640b1800b00668941500c07100c204c440355540c214004103060000f5007102c69400e06002040000c4c6180308003600d1790b000300d82000d02c039460030170f07030b070711003010002c4014055202c040c0d5100c110310b45000c1d41820590000020441c40e0711100d5290740c0e4410448030b03203205038440184052402030040040000c9009482c0e00e441c010110200d81c3c024035a40d800c2c141d4030903004020403000303140c10f20003203040881459016003400c0c0d000b041017200d4a8081c1c5070600c8001c1c4288001d40c880124031910503110b0f016600141f03010800ca5840d0803440ca40240c40c2d1503640b000c440c240c0c1c54540f00c1207030700c140015603400711070a000f801c1c1800342060783c6e1480f0712811014000c0621000308000543d00c4518420070804585280c0410310440a83c004001610400444240f00756100803069880d0381c1e01000329000000207101461003200c0300c2075192505030195000b0710401715034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 326365242 1250 326363992 326364019
    0x2603070915050f1305040c03020a020705040504030c02090c0c07060309050a0f03051608040315050115121509020307021506010e041a06120a0e06010b0715140a1a0301060b190e 77
    0x5524100064039006c032024010b400b0b07004d00c11800ca0268039003180040e07100d0a020403450905611881c0c01a000b450300c0e5000207919000300b954000b045d01e01c00c02c007000000b2680d0300c1c10828483c24002c0d102a1a0510011035551134050f40d51a810002406c03440d1251030107000c060181c001c40d00c0025000810200e55030741814141000c1d0018442590115051503441004814500c1031505946da50480b002840040345c00842c1c124504d48000701c4003a40d038160010403000033041a41c02005400300242e0740e8a030501009040003000c01c04405074071086414464243e82011140307400c89000d4a00081407580c0c1c8200310448603403440015008100082c1c0c0b10384100d11003480c1441056040300c00d00c0543c0b040504250754400900c41d15500005c140040c0c400900c00f025050391300c034007901c0c0100d20f6404580302a0500340d001d4802403181382d52480c940b840000000c11440c640d42003103000304810f40c41c041100d2014800c070f80d52001c145a10b1203a0424060107101d0141000c40042d0554171601c03003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 326366492 1250 326365242 326365267
    0xc0f3c0c0b0a110703120b04050a061401030c09151403090106030b13021005030613060f0503010f0e070915080a030305010e01090b0f01080702070e042603070915050f 73
    0x1034800141c1c1c01940d0300c00025910505030160050450120f40d445240c0b50058800320b031442c9040f50825070051303c5540f001c0c22569940101ca02500d00c140f8001b50091400911031380c1d12080c0c25038503040c14100300b0383e50b00483d00403e10404984607804039414406100343d00b10740c4040d019a25003000308010080c0a503c5070154041801d6910550700112107072510845141c01d1184a2030003540300e10f03a0540f408070307148980095038200001501940000407000100c000741c070510f800408019046000410003403500740118180041c10100811029100102c89a212400e030300416078056110082c035075800c0740528060340280109016640206030a203030081c05054280b152407100d08541c000400e032840c43e4401c920032000010b20780304800940038019951800000c20550641c0921403001a49101c00e0440b030344201c0c031805a00c018082c1d07428810168010303000c04101018014020131072401d410410b05416a0703072402a03085464a503160032662842a64514503000c000403849201000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 326367742 1250 326366492 326366507
    0x801271d0105012904150c02040e06090a17090a2d0902090f09090a0209090316030c0210170135030705010b0306060f12101803030c0f3c 60
    0x410b00300070b02d03041300c15510075103003a0302440c01000f09103904098104801c078003803083d550516101400201d422918400200e09200f82101c0918040d08079000d000704000315110000700c09840c000b8201e08160703120f000300d01c00c00700074001c80d0607862841140c41b5800a0a600d01240c1c000d920b6483c40d0041d40722040c0901940003441201e009102071824981c1e94a003805099200e800007000070403800d40541c0806c10700c0c12001d01403201c1400104501e100e00c40903034110080c264000e4942885058080c0b06015140d03c10b0404581002100001e001444101e1040541121000e090402000d08455134103c242000c1c0028aa480440324607254a99032000c4054401d290259008115064404084c0b64540c14126a501d61041d9400103190303c92030701d00c00c4003444040601c112034070000d19541401c102c0d039900104020000c02d20002204060f494000e45480c050646016003806d400d0020140500701c40000d41040980c16010b000c00c01d91182480001c2c9600140d018143d038650214081c1210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 326368992 1250 326367742 326367779
    0x1208060105030c03160c06050a02071a09061b0c0118020102010515060d09080403080d05160201091e050c0a1e0f18051e04050309010801271d010501 65
    0x44004001608540c01502030742e00c61420100340d03510359070340c1030390103501541084108018003091140d22030106015110b001c0c1b00301c0400c40016070303d202c41d0500145000d0b490311510041c00890041110122000c83d035541c00c00c941e40d4181c008503082c080c0e600c11701d00880781c0000d00381d80781582e40d1001250041c0e42c450310600070b800800440c3c035025400c10300d070010711685903000b5030204514104083c11740e1200310007034007400206040c1038403036071100c1c503e41c4002910b651441d01c607030a109036110011616400c030b140303c1c00204803101080c0e545685c40011227001a008020382000001441410301c07810460080041c950366002c1d0b103410501c2025030040110b5105411140404103500f0a03c003200f400343e40d08e08150341c00400e48552844054180100603034446801c8401040d520741030024000e0103107203e50081c0d034548903200001420b21314160700c4203440c0a00110114084200804500740350316601201041c1030341400c980c40308042d04519640c0b2103610305000024500090442d40410 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 326370242 1250 326368992 326368997
    0x30c0d0f0618020a080105010521090102190206040b0604050c04031a040c08010e07030b1b0f0406020d0306030f020d03260103020a06080732040803220f030308090f030712 75
    0x100c452040000b402c03409001c1c1042c0c007003440600107025a602a201138200c440c150f10120b400403800c4403801c01809400d40e01c0d4680f603074000c40c000e03224107002046140508100e1006001c54581902c0b80c1d494504094110b034042ea6640c000308040713801d8001181d018580042d16200015910040d40483c0701d01218192a041281100414943d406000300e0480c044c0d03e20003032040a0464445014070800a0f26640381910001241c1c000c421200003d840f01c00d828202041e01d0320316000780a03040604103107403601052310f001d10602c0028250442c0d01200c0e5010346d80a400d1704410700c6e0903100000b62695000d0a101d090300c085003401c51100c4040e0503280300355030981c1c201d5074549017a20b8100c0166a0080840e040e038048c044151368500e1580c11481054021783c185a91498414081e0303801034100180ae60070010f000c291f0401000b02e0503040140c00320022000c1c9203800800740c10500300d400014100040714002c02c448803810010048400c00c4c1c40c1c2520303680c0d81c0620b49020740100a802c00d002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 326371492 1250 326370242 326370269
    0x100f030f0b040c020c01031d1f0207020301110706051f06050c0c130f0e010b09040206070501140106050406030b090402010e01050d02121f06080403020a02010c0f0c06020303010503010b0303040f0308030c0d0f06 92
    0x200219400d000310405408d860050100700c2c070007060064159060480841015800c0c49804e000d070b036017405418002c0c501d41d064990703100341d503041140554130010321403650b0b030303c0d1040b2240140a00c0d10746a4101c2c1c50038a01180c44025040c44241490144030a0a074014520003801226040507031020015808501c01009003100d03112030b140c00d07124a00803155111090000241c0981030003001041003920480000410125008940c45204020b03004200005c00c081f905119064141c03182ca00200300c100c07540d414500d05980000c00100003218170701e04000e0040b0760b54040d00d00c1901510100c90300d43c0d00c130082c40d2620040c81032100d108014108c1055101c0b02001494601030300416000d0398059019080140007a001520390840c2d00380102c80300c111080f003840110b06034001c203001030072301a405542e481d45005c0c10142555041001070744290020041009403415255001040700d030b04c0703a40340351240d40d46502c03101c9501031445444442401d101140f48900f106510410642c0c1c0c50b00894403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 326372742 1250 326371492 326371511
    0xc1413050c0a17130201050729040b0a090c1a0d060902131a0f0703090b032707061d0604080f010203040b07050405101d0406170c100f030f0b040c020c0103 68
    0x400440081d1342e10b0b2030b50300609008001551044c801482403a024285a45140e50100e41e251850b4000303030401500e00c03601c0c03030030322040280d444030b0103400c0400c4003030611008200381c40d40510802c8900c11313003005401502c1c10350f28007050301e009e07108003a03444a01000010b40c1c03401604065030041c004811048180200881c283c4080414602d024122180036810540003485444d01540504026414007445480c001113088504004500c1240c001450b03000604009080d02401a2403090003802508001014041160720910b0040031090340c1a00d0030300c218103e80131a507203215503003168020b8000c4401c2201c40610540080d409581701d01400c81c841c1c0c0e40c1010485550042e4003d09034801404c0c80f41a0b8018882c80307409022183c002600004c00c1e4a000014084070310544c88005010075488128280138000e2201c04642d14080d201207459000031080140400d15005001060684d0b03145080c0c801400d50f88011425400980100300c002c0304000c01030760b03451184040c3c40c00a4100050038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 326373992 1250 326372742 326372777
    0x50f0706121506081902090a0605091504060203161a0f2a16151a0301051302030601151427010c0b0c0a030e0303040b0916030c1413050c0a 61
    0xc40c103c44a82c4e1301c0c2c48080e20781c2910054124001816055103903000c0c000c1951564411510310020603540e25410fa03641480c0c0140101c416000c0040c81558009100412885401108417003146003021a1280d14048130b20f08044907412141e0a0fa07d8515481d0804c0711405411008500500e9607240084603056041c2c03e1108000074645420002a41800400180040001000e03a80c5104034510741100d00600e0001044440003200908004900001d031251402c0030300c151608101c1030600706005540f00d4000c40e681e4107040c0300c0c00100040102140004510802000200140b800511503950020500d203a0004842c0d012107600004400030242031980034800be086801d502518105680d91081c0b1580b81c903030840702142d014191120003100088030288001c600c0b40d0f100b640130300414109411114584035254050f070b001c03003100c0001030002c51441c00f03e4500b05ca950700c489100500b460001320380420304c1c116030080801c0c109000c0c801089181009041c2408c0c259440d2049100c1c1d136000c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 326375242 1250 326373992 326374031
    0xf0a150c1a161b02060702040c1b060b0f04201b03031e0f0613050702070f03060509071a030c070807020303071406090a110603090319020105010501031a011b050f070612 74
    0x2d45c00300d42001504010f04098200d684801218100190721030081d41c036100310289541e0007100c4c030b95501c1c031075950f00746000c200c01180c00c0d030140c27070402403190503140c203007022100011040840100803401d41c0d41c244650407026000103103031007566100c0c00c01410110146400d11501850041d04000040107188540c100e14860394004125020b15040c007001e080060002034406002c500502501041c01c40c5541ea40c01d0003140b0031b10001840e490283c01250409500350000c1d080030b0f15114000442120384e10030350ba044604590800c0d40c2304000c2c074200200c0c5c41000c000941600010a02c1420b010f03140700001d40380605030066510350b43d550480151500303003544000304851010300c00070405080c01c0b00030f10303803083d4140f0440c2c7c504014807003203c0e1803144808035080145e4403540180003e50740760184000c400b40400046421030003900004e00440074065541b401c0450a80511080c002c0410001c580c41c0f01c08015181e50b252212002800d003030540d00c014003014204a00e00c107106a00405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 326376492 1250 326375242 326375297
    0x40503070905130b1b0c0609070b030103021005030709170a02030d111b0a05040603050616090b03160311040f0303110a0203060f0901020408100603020f0a150c1a16 72
    0x43d10351080060f5521100e80c480d028101c00d4007007a0700358070301c04184800c0004000351400d0300028245032410b0a001450300344a0340012044020a01c01023006844140003420100800c1c1089620b0782e0721100d003101c101c0302c694025485001c03410280308250a0105505e440b0380c1c002d50990307901c000c112105540382c0c1300755070f040141b607801a5504010035800c80c603414030740c0070014109c400c1181d07500001015075007070b03030015903064000b10180011502d100c10360900c10207690420801c0302d4500348010744207000041141411741011288540d02d5440781d4010384520000c4080161110f4543c07000305d00c0e1150a002c203c000c9019050445041ca400140c030380803169008004055590f180c1121200480001c3d2000c1c13100e42d02400b0107d1445400e006a0020300050400010f80c0361942c0100f103512200750150601030460040144010550340c624083d81800e141480460680140780c68100c5c80c24241d44455411080018810000489030210310003000c5130341d40250384003211001280c015141c14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 326377742 1250 326376492 326376511
    0x1080117010f0c0e0321030411010c050a260301240c0501060603050717090c040b030c0d06020d0e0f15060a24020f070e0a0f020915040503070905 64
    0x1004008041032000c2440d14064250004103803104040d0140b010386540000880100351092954501801e0400241d9600444189200845c0c0d501980c1c44196200c0544040e040e008138202d203c41a034061100100401d501a04581c00d041440c2007000c1802080070f00c1000a1210041c1a10040e01410949059440400700307030b4030100c21110000354001181e848141800075001d800f1002c15000e20031103006041300e0f00d0104492909040c003c1680c400d107140d01d1640780360b100501070141000a0540305030030f0180c4e0001a213000d0300000a04d003031442c080159000301900d0000c000c001164000c0d0403510319070401407021071402c0303401a40307a01424420002c00e504ca4076010200d201114078094010340f0240c4000070040d1103084401c0d002940400000c0d402d00d0420080d445241e04201c10f05880a00d0340142c40510b040c07141e0100c0000c405000d20744003076158071540c0d12000e0598100c940142d40140b0f00070412100c00f0148240d50480d2280034481d0146180004200301c080c0200351041d0280c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 326378992 1250 326377742 326377757
    0x807030e030405040b010215100807060f050a0e0f130219020a080315041d0a020907030216110414190c05070c0314010608030301090e0106120c15030209030307110f090601 75
    0x40144070060245803400340c114841c42c404c0400c100c04145110b800f80343c0320b2541c0e000f02400c01107072b10b1038904d040c2c2c041400c202a4407404400c0952000070750742504090703e4995050b00e0b2000c0081c00c58007200c80c01540c400c42041d10380d08070503c01e43c010f19050031203002102d12200c83e550242e8481c103440002400095040001880407450500d5140102e0b40c010300025000d501c4841084800350468004c40b010780c04088050250306d03242c140aa1700405a18041d072510f444c0441032a95501d03003405c01047e0082d01440b42445540310780041007041c40403810307802e443c5410700000518810070404c52811602d03058083c20070314411000c441aaa80003403116140d1442c40c0d48214a195501240181d25503a0710400700e00707101c091000310b00030301c40c02601065943c0054015400c4800c07c2c2e01c40e8001c45001811781d0b0001e0f40d00120002103982c9018040e000394440c80003607001e8415000700d01e6043c04000307096410042c0f06c104030700749024107a03580c1e21001d4825040c4558aa81503400601260b0343d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 326380242 1250 326378992 326378999
    0x91504030f03020715020405131a0f030a0515160801060824030607020c0a05031f091a01060906140307090504240b040e10060507020105070303060b16030807030e0304 73
    0xe41c107207004151061078014a003071030540700e09036190501202c101c011900060100654039010707841c244049080d507020048908901e2640d0440c03400341c0003190162550f150b10b28515903060180301a0581c001090300c6c035605100100039005a01110403a8810020b005a0b105162180e40c101341a1758994132451002c3e140e131501007403245d03a501040c0700340026600f0311030540d4030700b40b0034a4011801d40e0000c25280340c1950420415100790b0300164040d5220001801d03190502c0c2200d2a400440c00000190001c1d80e0309160200184001c03803941040d469a00000720950f004080c42c045400b80d51304d503000d40a110140e1240d920050319110006500450184043c0c503240e4040e003c14404d000029003000b0300001c0306000c03079185510078012468085800c2001c407600484403075000101a000c01510350034000068114040c042010741000800b080ca0f0080500a41c004809024045d91050b2a500b00c40e914550314411170204030002000503000c525914003138025006489100030103542450304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 326381492 1250 326380242 326380247
    0x4031b080d0902150a020606030106270c11030c0c13050609041205041a0702030d080705030a0905150108010902040e0c06070201030f0f020c030a02061513021303050102030c040e09150403 82
    0x2c01801a0f81c890010a4103040300c80800008161505840d005441c8a241140401d402c5842952042c1100c1d010f0300741c06081e141d64044004a0b220401c0000110810640c0c1d044445044080403000c4521000078013400c4840000b0349584940802c80c0e04010f07030b004401c0c1c41c0e03043d10b205481854016811f0408107000a821014402652046203002030420344c1c0c40d54904001920300182c10070003000022400b080d410248403102c50701712641005283e0381041c3d40010042c2c0702c020714241c0e00960f10b80740701040037018418030f0380085102c2c1c0340803120b5031141082c40c000d102d05136040384268501600c201001740c0200d0460780301c1c00c00a003034038109555a00107401410400620311585540e41500a0b40c4041c0d41c4050468035803070600a580b0382010540103481c280018000981c020081d041d41811961004c0e1104010b102e40031016845440384d0810716502c1c041900010403950000c42045034144019000c1c00032104003450401c0e154891820b055224081e20004c25003090f004030000e0301290 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 326382742 1250 326381492 326381501
    0xc23010804020f0901090603020127061d09101806050604053a03020f01020408030405220501062708030304030e0a0e010602060a060e09070501030e010f110304031b080d 74
    0x3400607149031000424180000c84085091b00304100c443c2da40e240900a550344040030043d600d914004821501a40303c1e4415201000d512800040100c4040304540e0001441040d21302c03507001605650302c82c10070081e00c054260a82c002c0c06010032010404c96504202400380d1000c43c0c40144c0118a410f0502c1e081c812980100201c0c400e805141110315080c3da1320082d03401c10300e0f01130100350080818075481d009040035851f056828440c3e006000a03c45024003004440c1103490844e5803140e28680c1d4070514a030043c5a90b180c9040768a48030000403103d800c20110000b4034400480020249074805110000c8001c078043c02030311754014400100080d0040c0900300400c0350061032029078581e1074803000d210490036042400160014018008001100d01440c8041d00b401c0034030300843d29005224aa42c2c1d4014030426040548410720009901e02c00c1d0b1010b0003400c4c0801c010300c10707000400e60200782540240c40c02c43c00101c0301d01d00e00d40406007629000e0402c03644444400d2500400001002c040c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 326383992 1250 326382742 326382751
    0x6030509011e1107050a06020304020f0108010608010b07030c080a02010525050702040e1e2401060507230708010b090901060f030807080912010c0f02060108070603052e030c230108 79
    0xd03d0200206000f04e0300800c40300001d035100c0d040140e503030301e024414002c0a01c8485011414021640014000150084015815640800c000079100c0010b4101207a4030140c1e50000340818000180f022181ca9040d00441c0c45598009080c02606600c036020450420314510075400040040c0719650043ca89500121030003100038089030a804117200c01a10300c11600707090b080040c4c1c0403282c580b404008822041c800014403a800100e5989481030140c058450040010310b80c2403107404281001c50021100d00b03116658000711141c031920340305c409009009841c1d14a01c6001454005249102e0500428003506c0c1100c1c44909554030315619004190040b10088614150a002941c1e441c1c4840c1301c0041c00c03218580021811f00c140d158040c1280e03000314403d50454200c040148074625000401d00201c64842c80c000130700da520340401840d400600c1110000b00340c1002108110001514000820341e405548079000c240e44c1e030030700c0402640d40102120f20b00d129a028008081d03000394125070b0f00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 326385242 1250 326383992 326384021
    0x206010b0a050d0216020312030f0c03010311131427060928050a030c110a0302010522121a0a1b0807050d0608100e010e0601052403090706030509011e 66
    0x11750503181d0000b0300740466030340080c24902002c010040b800404c031030056040b44101c034280e403441d410343d2100d40c516181b541ca164015101b02000410380526944031030406401850b80c50f485080035031065141c0c01c4003024441c0c9900d2131310010966140302250450082c2411300080c801d003e100010f44404130b0b504102001100480303c00070380400c4090043c0e000d01403080d41d8405d2281e02d145059141c8228520103a8080d506800c0c0034001031341c10000701c68500c811318582003030074540c407c41d01d0002c08082d08009000c0d20710030041000c2104c0c42c00603280c0041d64680030b6400750345088150302180d05004c0c07400310b101c0c1640f0b80188400c8c041e503c40c6810500c2480c0c03040c074088540d5880c40564049030700086440c0e1008546e45454020b0740300303030b2001c46e100340000e200c00058204403d80d250018010b851280c07100c08507000740003046103100100501c0700320142c0d8681c030b0107000441d11040b00d40704100c0843c2c2840001f80c9525010720620a881c82a0b00341c251032410b0707841c0c00d0300003040706c1c503011f000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 326386492 1250 326385242 326385277
    0xe0403020a0501020a08040c0806041205091c120f021c21020a02070f0501020d1d030a02030d020a060c0503061f020f0307050106030c0e19020a05190f0206010b0a050d02 74
    0x1c41d600307000038000c00790031b61150540c1e400c00e440c001d11658a50341c45180369410400c05d0200080700c01c802c18a18400c1440e0040d11201c0f68400034424030341100e0786421582c8510210002c012a40400d946801443c0c0c4800501005d40942a80c9498070001d116145040d00750694104030701070b1000c6290801c10903c0482504107040b03040c0d0403070740100c1003140980c0c4440380030019590b01da18250040e040a10280c00a6400880c0250003408080807621103a0800409841c1d2500c0400c005010301d81c0090849001d40745002c8041e4940d90500b00c00d85020b41400000d1521a01400449004900141080c0a075104a41800d0324644401d08814118054982001040712040000d00846401240005011071551801c000700c0c6c1c103d5030142008007114809c00000340e04140000c0700c0f074909030380b0260361048404c0d821a0319210300036440323100c0c45009283d045402d510070b0010000d8078698089800690301d0307030b071205028019181c0c5000000c000300310300120302216070090441e48810070080070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 326387742 1250 326386492 326386513
    0x2030910090318060302130326030106171312030b241804050105010f0f0c1b180e0303180708030a0302120a0b180408090d0c1e08070e040302 62
    0x41696031125003039000903038410f20090708202c5242c05100804641c10708600c0e2003440045560881c00c0d42c8409007521445881d211a2407a80e0f88115184036101c1550594a40e1a40c00180c0007a00b03519501c1c4000d210400011644c1c0035400428070103581180000c4107441c032184040f0003030610040c1d66900480d50f180c0f001d021500c1d4001542c1d44005a504441c1c03551040c9003000c40c810007141c0c48030310550609004000da40d03001a00100c54505e540f4040a640081210503210909466001449400b490441005605c040050074080d196a24803188480c41404409030a55015504046641d04100085503201c1d0610740c241107480303490340940d40e0b03296840c552242550030041854000c02c0d00099842800480d440c161948000d84400400c0244d4101c004a0050303842400e2203448000384e071000c1400d21045100365105201c00402c6050854031900d4070510070708861050701c0101380a0018440e078011f10002d00801e843c03451004050451400390011400348026000380c0650091501e03c1c13 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 326388992 1250 326387742 326387773
    0xf1909120602030406140f07030b0f0901090c09120606030c0503010902150a09081b0f030303070c031d030109030c020102070902090d200607050a0309090207030e09090c1804021302070f06020309 85
    0x114404d441c6440e0307405d15031400e23682c040c054800300c0e40114440c050300c071400c0035565941404241581e03000c080029a02040720825101112150068610381c0d0f40115040204051a003248041e0b034420070f1510b0005070380703505050a031511404025845440da0080385140da011202801c1c42107098038020740941c1c3e6900d0b0341803c21900010b0383d81d101841422140590401040d25400b00c20181e00440c80c5150000b03004250710b100800040401c6111b11040900c4941e4076114482d10400400810060b040c5240c050300b00c02031601e00301d0241c0260800000e803080c0d0351003510306191028212010864844c1c2d40d40d4512215040759181d5088540240782c20380d214480641300c03481c403035030003001c013028541405807030a00381e5442008000e0042000d400001d90042420342c100038107850340d44a507251b14164500f444002d8101d207070401e400d248038004460412440034012402921440c0c00c0300da0080c05081130344a181c00c05051040111414400a4515401554002c04850580e0b80901c90100300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 326390242 1250 326388992 326389031
    0x80105220b041e0c020a0302060705070f080406020d0212030613051b19140a0507020d1a0901020d06050402070c03030f0302040e0f0403110714150f0f1909120602030406 74
    0x1c580180f51510100060740041e4854000c2d11201c81c00244100340c580d030b4009594000003050311041090204048042180784038126159030b9100902c2503c854880f003000b9614904000440d00510654008490a08900d01281c1c014440035080146906038801c0b2100a007002400300728000080b40340f8407a426680002400b1042101c03014502810201d01c3d0003004141c03201c00c04680c40b2020402150b28980090440d0003c50b415514a62283c47c0707420312a000302c0c9800d1602d05080c0e01030041100b442019401071180d0f40590008000040d1510140022070003640c1c80140302088118003400402d001e81d024418500203850094585a02c030044412a02e00588402d4241d11052062004041d08501000341001d82074008103911494112001c120480d00311080b809070000458111210b45040201c03440c604584200598500d0301450104682d8010001480c420320540750076030099100c1c02c0700328202c03007510031480300e8403202ea11507d00952000d40211040c995414903540205a100c13030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 326391492 1250 326390242 326390261
    0x2a0d1406012903130213020d0c0503071103040b04030b0924060a0504090f08090402220e010f03110f0604030f0308180102213112080105220b04 63
    0x5981c0c048101d04040748200050450103031082070418000c101050001c0a044013000f41c048911007050603201140500901c611700c1c12641081c00e004800d06c009800c800154041c0f0426500c03400403440716548152a80200d008605c0d0900c0c04101c1007002c80c00f4140d620360005210004d4400c1000316666090070f15040151000303154000c1820003019151807085034005020944082c0500c0010740e454030b0820741442002043e840c0d001c01c44074540d880c1c0341d0640742071240350442d0341c0c004105220043d242105034403a90803016030034800820014804400c046c200e0360302c07401c00f043c8400310f0002c01240c0c0e0208414141c1240301404004081a411245991050301a0302e40c40d01d80c0c01c0164482e01e622002d181c10061036070040025450741c601c24160100f4080d00c1a01044103500c4602c9046400709845c2e12540507000703819443d02000e00350b01e8011080c24442d401d603004c0200d94000644441100744141540003100039041d821101c0c2402c0803100c40045080c0000306a02c0f40400103045441010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 326392742 1250 326391492 326391509
    0x1509010e03031303061a030a15060b1c0e0f060f060612070512150607020d061d0f010507021b0d03030f0c11070e0f010b1b010612052a0d140601 63
    0x90400c14011700307200d0084040d501c0c0c600c60307120b03440400100b5070b1030642840c000c0820411250481380d8600c070f039005070040e0411040241d6070301c892046c054231003420144011945032906e145040314600c0003c2085c50101c1400143c20b2903540d02e03601102518009001680008c0108085100c4c41000c0382c115100342c4203a118991a02c0c0141d101916000004101e01040d0040c20340280312950707101c05849010741d040b1103040c000c000615165000e04008904c04009006c040d00a01d240c0c5404241321070a40c0b04100208540d54401000303da460220140a88030120000c110700d2050078043c20311503c0a00034200072681d400c49405103070456450202030710014240b03001003403070550140068402004022407554180c02c141081250b08a41845009180c0500059029051880940c2d9030907019030b030402008403da94103040c1d128200521000c50303041c0140c00d409100341701040c50340000316051010b002c0380100311500303001940800d03003400d950510500b448a5141c1104201ca00d0291240c0c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 326393992 1250 326392742 326392777
    0xc090901031e060c030c0f0c2a0306020406030204080d091a0a170f06030d03140606070213050108030702010306051c02100909110c16080a110a0902030403030b031b1509010e0303 78
    0x3070000300158000d2113020100848c001d031201c0400c5000c0c0d10301813500c0320b8070001d80c11500d00450307a040c0d440da1a4001000140040380c00100550580e01034001c0f80d860105450801541c42011148034082c1e001e26580145c86901100e215500540504003003003031f900708940114403950000c82e0844040300c020b0412180c3c04200145800e00b407140c0542c1200c0703802c0c103015107807800e0243d0001e05401082140a803402242580641d03840702850600e107070760b1906c1003295503100c0100e00d89a50000f90241c0c0440e0510b0303400142c1d400c0c107005400080d10050549820301c0c00b10307405c01c0000d6050030002c40c200803190780301041c038881910076000c0c0c004201d60199641d2042840903070500e40d0405201d4602e0103104010070000502085a81c04203504c6200340f00c0d8198013000184132800c80c0d401c03444680f0b1000c4100010543c041d44000180070044080f15000801c0224264041c1c5c000072841da00801041d400746030441003007002e0a980d0b4014101034502c6429180820310395081050400384941a0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 326395242 1250 326393992 326394011
    0xc170c010c120908030a0c0e090403080106021b091b0915180406270603060501092a050403030e0607080309100c0912080c010b04020307170c090901031e060c03 70
    0xb941040719401c40d031106000300d041ea5103a540c05808014100c648483d144c0c0601d9550307078803d040f000f0048100401c0c5012604007800d0081555009024400151103031240083d842848100f058180d010300500b011000d80e103103040191031141d10130456016030010300c0400310507503406a80c0403118040b4031103180c80b1032048131880040c1e00718043c918001c42c5010f805001c4080d01c151500e011110340200d115458000c481c03460010070041d440600942d152000100303025851b6007082030902c602d010340450b00071100c0950880800c91403000c5012030000c100400000740604c0e16200210070041010341003480f030352076003001d80d0300032100c640c0190800750301c161525850780300c1c0e40c460351161703e040e030191420f20032074000d24009000090701d080b0b4040340d60020007109400405204c0e0300a403084d912410b2103c2d003d05140c01e412081210001810002015669604d0544848200081c8001d000ea441c0d41c031607014003020300881c3c1c19148440441000454998001c03040000015500000c810750f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 326396492 1250 326395242 326395247
    0x603201902190b0103080a050c070609081c0219110d0c170c010210020d180809011d0a090908040b070308060901050102030a0f0e03010b130606080903070c060c170c010c 74
    0x39541e030908044464035601d1010030f050301516419a50700800255540c0c89088040c2e034a0b014401c0b10341030b2032141c0c1e03c0101d21a40d10401a00454004004481880004502c844100400c2801f0700c001641700969240c1900350f0040d2600b0403d00032503030080c54013010b50204030606a0b1035010b03a07858109220400c034446010125181031380000380a07110060b0a100000e4407440002000500243c01280020040c0010f60010b0704d0031210003144807220b13031140f801a00d80d4124000700c42c0814924160801c0c480c0a20070040840e42e402032a128000c2d0a000c1054010212200c043d12401c400744004561007110380c008245041c0691610102480c080041082c1c2100507013246045410a00418041a8001c490704e80d01d0544c40c02d0030b03944842d0600c0801e0041030615a05944080401c040c1c61a41101c0d03404501034403525520100d50b175445920842da00c0c03040e224000d101011145c0b0402440340b003840543c9410f445850202c681d5020801100070390380007d07082c264940d40da5071040d00d5494 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 326397742 1250 326396492 326396503
    0x1080303160203040815040c05060307080a05060409030c1e1a01030501060603090206091e0307060806040c030902090424020d0209010809013b0d021b0306060a0603201902 75
    0x34079520055103020b062021107902c421010b40240c6051064002080802a4500ca01c601a043c00741131799032603103030003030008004080545a450074245040081801400c1c58050740000e1509074442c1d07414a102c0d0755031760000260300c1c158a02070130442c020b40c00014021642941c81c000d1294404501035055040060840701103070f00400c00d1525041c2e00c0401070700e500094414010741180d0003029040000c029443c2403140b00d49841c0e0500400b04d0102c1d10f140c01c1014a40140303c261410040184810019812584140da002e980041f00d03030006000a0041448010000280c12414414030b07200b64400c5c00740d0704503016824a031500030404000b29648048115801a8000000d0184140110343c0d581390031141c0288850701c681f2800300ea0b07503440c46880360b441c600c0b107564103c50300c00b201e070300d4000e4503045104240690500140b10b550840d01d80040c00c24001e80c0000c0c500d00e0500d140034002d4000b412400c1d032a940343c42010f13920344010311000740502104043d031040010b8100304014004d0406 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 326398992 1250 326397742 326397781
    0xa0215160302060f090610060c050a050d050403030e040e03191701060816090b090f0a050901060e36180604051c02010e031803100e0307110d0f03030b06040e01080303 73
    0x1540420100200c0c201d01e0080c0100300c60031801c01d0302010106090041c14603e0300c5002413340d106945400f214a54490001d200701da02070703075501000d498800208020f540e843c020042ca19401404424043c5140b00040a140e860b1070620b200d0043c81c030a5a1444160240e0040004c00c41c0030041100c04040d40f00490030900c9540b1300045242e041040e42d402e10700545000380d0041440c1c0c3c1c1c581e8000d40b145201c010140000414000d025030303480100a121149014503980956580c07120140e2009891a000c0d41c1605882c2e0715001c600051123424000140040420108180c810610340d9070900034043d05025500484c042e10303011800310100459482d1a401c0c000846e8900342071031220103008000c0ea400400115030004400387d0103c0001e140c60354200420320110b14050304030030403510000050110038450b0004000100400c03040007071000a0740409008080c4225178140001d100b0390000710b0340b05006281c2401c2580341c89901e00b071148243c0040616610020510203407041d2901c3d0001d04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 326400242 1250 326398992 326399011
    0x30e0604080d02100c020a05060f0601050f0309070501030605010207080c04090f021c02010306081501030807110a140f04140a090213111b071503200a170609090a0215160302060f 78
    0x3009580d2321103503a914014003100440c0b0592011691580c41501141c580c0c44080a00948038140208190740f00c043c41d105681c086480e2110009044d400480d40b007080702c4415000d4070311403800030b052102030912074004940040d0880d041c100103a441c01c0440b01c9280c4059440c0c1c410318054400901141c1880d00f150049910210405180708001002113040da030f409103140743c5510007858030b8901e503c4042c500647c450001c04000c1646e0700480200c4072621411940301a41c0e58250301480100d81c903006207100221200c100060301c101ca541c0001c4c89040c0b0260441320030381c0710741401404540420003072000d00c00001800c1007404920000c2000740c0302440d00078085882c6000300800704a802c02c0b100d40103141e02c07000c1504120391960413829440400f4030071b20355500c1d0986002042e811142d0040203102030503a011415a040c00f141d401e224640c00390041c01d61015039000c00041124106005402880c00c0028244202d0015000300360584203400070101400d00060b458201080100003160 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 326401492 1250 326400242 326400253
    0x4020a0f05062b060303050d050106091412071815090e0a1211030f03011e0501051e0d020c030307090b03040206091203160507050a090b0d030e0604080d02100c02 71
    0x19a0b07451104032514010000b15060120810101c09000e025101e001e145409152481c0081072680001c001c0521852004040100b40e88070b140030380d1140010b001c1c0c40d00804034004848581d0401031150390707058044404480c072180c0d40b0040c58003a150601407680a550321744c60f0001201c200d541c042c502600b040007050215101c0c26a41540c2c03440000400340c40d141c18501c140d03200f18001d810303420b1a012250700703690761840385031001070b482d030320a1040e039560300015010078182c03441e2140001c00b5100142d560b10b25082500e034046150110280e04541c50400801651080c4226880148804000000610388900d13041801400b0500242d1004100900800030040103903101c03000c4484007041156819008840e81010328510f00650540c80003d82800520740b05204000420340101c440031039910560940300c10044060320b401481058000c682c0c80305800c000b81c0245100701100c2c0f401341803603041558850030107141c046541c1b41da00141e0460150702d40600074600464403085114001080e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 326402742 1250 326401492 326401499
    0x2703011b032913090f1703070801120f150204050a0305010b0a0f03030c0b070c0f05060a050c0a02070902090f10090608100510200f010516091a07050c040c030504020a0f 74
    0xc400c0340e684981610b040c4d903540c60030b80400001070f105c0c6081a410402c0c1808a0110040c1c1e00e2007a4815107508000c18802e800005d83d00720450b42207826a0b074484411100200c8030f0381c6840020208a10b03e504c05e0f6003c0c00042429100c4c9000c0d900154040c41c0040750a81a600078844041d0305508100c0103810300c80c0091010070342160528103426031061003081c0c66030303171040c00b100c180c4900f11000b01308c196808955014031500082071801001420300801403611107490300e00c211f1055401400160b00f08004c2080041426400f07481c034100301030b083d031b1a807049810000701c090103401092408180180f1f018072042c0d51210100350b0150b02c0102c1d00f44810b044c0030004840e002c00c0710702e070000c0041d966071141d00050800c024800758800038044440302e04662074010b010303120481342c070450003500608200e001031080907020100d41c1c00c20025185075101c0540d0800a43c00b5140c180c41078440c0f000106507644541c800c1c40550354140d075001409003464810001680015802251052010101030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 326403992 1250 326402742 326402749
    0x30405101e0c030201020910030e0f060105010c020415031e03020601060311040e0907030602030a141e0403110f070608060f0f0108130f0c0603021e2703011b0329 71
    0x200d4581c03000d080c000c1c0ca034034192408138003920a02400b1500010031440b41250b0540640205c042011007070140e43d403a0014001180e81ea0009119290015420310910400350501d60304c40c0c0c000141ea0418000744544070b44031884903100c40d00d1700008030444154500c00789541440007a0240ca8103140a101d44811690544154016805412000c443d402c021a59040081064000545d40000300303540728035011100700020a82d0b06100319041e007020000556681e100c00c0088100b44d201d04519a0a03100c3e82c8003210115100d003000c40c05803080624090b46001d080090030000d011590760b00c4081d10f802000c0c05041402c0d0f00365507001d80c0034454846a1030b038102d000580d10140341541d04076000c0c41e50408103940a228007010344a044200300c0441d41c198143c00400c06001c0442070007120221406010748544940c8481080c0740071403d45511034046903125544c11400c2c02800403d1514502c00303111001d142406446001c40e03903c88480d031100032400b082a82828200750500b00c92a03250010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 326405242 1250 326403992 326404037
    0x1060801080307080a1209030915030204180b01022a041a100e030c06040e04021c0b0105040f0e0d080114030f06010905040c120f0201090e150909010e0a0503040510 72
    0x42004c540441e074032244512400d5090b00b103461040c0240301c40b50321802c0180203d081c80c015241510032140c10303a01c0c4280280221740031282e20340c0100d0a04801500352000070050500c1c1e041c114080c03026220250071911902c2c500909003400903441000700181004100c503070306080e40e41f2900920072203130000e544128078a41c2040450609140c40060031000a0800c0d2180e580903034407a902260208000b10072800d02c62066109903110195958141d460150f0008403110041a0350302c41401170003642080e400803450120404800701e1001010b81c000350500010012a500054610004112000406256880000003a0051f1a50040c4015115215001401241c200c1525500402e04010f0260680d400412002c1c0e003034004040c031441c0c524500c1d0f58a94050340010071407070010034a00000c1314031600070f07803072840b0801d500400d841c2400201400144246255503a40300f1040480009200b907842c482e100c0c001455445040c40f080107178034003045500104000941c18210054a01c40b00d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 326406492 1250 326405242 326405257
    0x1080702031b010b0d06140f01030c17030708190e06030606070b040c0801062402071818140a1b05030d2d0903020123250b070512010608010803 63
    0x1056600c410b8014040c0d014110300100c3c960030071030341d90a880902c5800e41c01825403558201c0c3d58841603c0702c0c0314a056400d000e0201a202c11240b03d810482a00c10709070841c44140542c007580c0c1805580d0b2030304411034100c000e0f28541c180169503d12000c0e80c0c0440200c002c14412500c45041d81071041c04a4814013a08600801d84000d42010809006046102038001c225001c000d201140c0c80d20194500102d80044028001c00c240f451040001d001017450011f486111030003003200200e02911002410402040d03211101c4015205004108511200329400a0b55801044c10b0f1001d0301d00880031100e89200c04442ca1080380303052100c0d540c0426119203241003450300c0c41c0c2e414041060400041c00c040070080c915462030050003030281d041030301141164000d80f070780e05030b031400c0385420401c4c40c100030100600a001000110720400008490100c0103001081c0000310000590700c1b0400c0b00d909403207010205101040c60307a42d00c1c60302410607016200c41c0ca000712607545001d288958074025800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 326407742 1250 326406492 326406517
    0x8010e06040b13051302010f0519030f020c1204080d050705030328050403030c0905090f010603020f0702030f0c0405010807080703030f030e0d0e010207060f0e060c0a0b040803150108070203 83
    0x81003007010758a80403400c0c3c50b94040311041282e41404182445012203801c42240411003040a4201080c000c0c815514032403041c920103141001410f00403801081e0039412002425801e00043c15403810420034086c503036000707041007585c40717003820321032842e00c4c00401e50075080040c204419400900c020042d642c004c07030582226600010182190b08540340c03821100300c6800e00d810100006c1c158141c010800d00301c160f48a00c0307049616101401000901140e00e07082d070641c08401089014880e03401801403e000050303282c1441c85d15800070303003021480700c2d6500a991103030a00d00c4a03032500f803040d035004016540c02411b4a520f0502241e485640d01d10000c0e0a00ca904014600e5040c003a030800341e401c846140696110b10100007000c4e14550b038a9502c10700500c00c0c2980403c3c1e00c1d002e42c00e254401e00c02502c0300811901d0754070420245510208010100740501e0304100b0010320001d41141c055031140f00c00726164982006036a5001c50080c0c200c6041108403414400229004002c586c0d4220042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 326408992 1250 326407742 326407751
    0x10b090a140a0b0f03060a0e06010c1101090b04030b06090c070308040807020a0b0409020d0f0203061c020409080f03040501140114240d020d0b0d050d0c05010b0405070e09060108010e0604 82
    0x600010380c030b402040c0d11824035007030f0004d08140c05000101c010f41c8281002c4a0881f081500c507030401042000448191b03000c24400d80c0024045110000400c518180c145425004152110b1004200d60496401201c2103054034040c40030354a0711000e03607039015040d03080b15801e02003030361401055a24050400390034490000344540070354031448a42c2c030281040b9022103503110340c0d41e55040000d500421202d0307100e500d4400304102c19040750084038002c1c18000c0c070301d20903100500604003120b190030604a0b80140c0c0c0b600c1d0000040c41b03020107071031829029040c482e201d1a041c100242503907903600780d00c1c0003400b403580103111822150410300c003044019036140c1a90301c03031060024030143c11301031600400480811880c90b030b40000d80040014042440701400903c00b4142440301026441c90300901c01e81141000e444458030901e11140b01c503000d2400400c0ba443d264002c20204c4200f038442500103101150303030074401e041c10104140c000780e003072034032418940c5446070030425024060059071040b501d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 326410242 1250 326408992 326409029
    0x604080f03070c0515070f14090f0f0307060810060f0f0509030102070f0507091416050703021c0801092702150d140a1401030305090402131701050f010b090a 69
    0x43c0c3c6404060580c00012220f411300d4801116600310011150000041d1554034403660403480340700401a4400e200b00c2980c149114802008413000214102d9500a1808642607089690801c4900c0c002d080039201ea00040c149501c4c00816004550001818044c0702048492910b6016040504600e513503d41a500c0e02e24040000e03001e4411084043c045180385084142802004038100e022205916000c1083c403001d00c20407030846c40200d4240360b1409002600c40c00d001d000390010540d041c440d2050320300310622902d584010720300050708a80060300010061202414500c81e05c01082405100303007110340f2420050030f20001c19440700902940c900c1020200041d00081038949000c1001e405000a0202001400517904102c0301c0a42031800c001c00c0e043ca01e481d580056044e07a80507a60103203041e0701c1c9018080654002c0b12070152007944503a00080140440540d4204080004004a014242014031482000042c4c0155400f07420800c011501c079941c18220000f100c04024800346211003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 326411492 1250 326410242 326410247
    0xf0a080d271101030506010c021f1b05060106080606041410030e0d02010e01110403050d140f03150a05092208040b04031203050702030f0403080c0f0d0c02030f0604080f0307 76
    0x16010032820a09030981e19020829142d01182d200c51007a603003003103103a5444004640400301c46101942004920100485190040c12644030115280c203206190b0081903516040c070b802c89040c2134034150003c40061100541c013842080d004002195520304141c18030340395440c40c0000540c024072900c0c60383c861303500700b0f8007030341000000c1400074040da14086001500603000e80400304012940d54070f0000c80c0102a04010244c400703998202d401024004c40042c0705552080e5a008100c45004081c03204d2075100010300021b41c4500d5040d0400307032907010458140026041560891482660781d83c0800401020080764240b80f18801210130400d11040e041262862141c1c2d008207141000c00103000c0103200c80584000300d50311940c1d82c100925a903c181c101d03180d01a6a605445115042104001080010010f041c0b181c02a000b0b541c032035040c100c2c403240b0348882c5e015150b0100d00900c034200d055103401e02c2429a01303d1000050071340e5180580d54180c01c0c3c4500014845405404004216200d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 326412742 1250 326411492 326411531
    0x120210091a090c040e010914010c3c030903080a110a180e0f060a2106020a0e0406030605010819050c120a0b130c06031a13020d0f06080f0a080d 63
    0xc0084c204000c1040300a071850b0203803448410640b94540300759041425004144136400c0303104150380c1d605100708075003000c40000000034a0f4000e00440481d0342c440410604401c05400d61490341c40c0003070180e206180c058050074000300214001454800c83c40005080c80040b03e00e0040c103464107a10307660500610b0340b0000d20503004040c003003141004201c11041406000740c001c840403603110035100d40c2d41a004092815254080003035692943d0f0500c00515142c026014400c204e041601840f20b000000c603080b501c84d0f07801920a1500c8000421243c0010f00041800105900607141c80a92684801ea90f806480c81014018a900f00000c1c216a000b40814044564032003900e9485003841c0d42c00c0281350300c880c02e00b42c4907034284a500103a005e021348582549040300c00b014064144c080c00800050f00044110000220f800308401c0c01074401a208d200b8540091480000344c5a051034082c61511507101480b401c568401c0354404041900740099502c46241c100300406c560442260300e14504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 326413992 1250 326412742 326412763
    0xa03030503060a0815040501112506021909050a0506040b04050d17070807050d0908100905160303050403202206051302032e06110309030a120210091a09 67
    0x340241c0441e191714501226030700c0d00032800380c0c0003480140307000610340b045482542038901d0b48403204403450752a200c2803014044100d008550041c2031000180c080443c1c810400408000507060034001d01240c42c040b1500005444155815410a824000b402070039203d54004d141c0300360140c034030704401c00180c1108500b1401c2807200494851007a444d00d907400f50861082142e080c0111004030800070700c02c0000000325030303146005050b910300e00340100c00240140803080e10b450190046650711080c5000400004620990b200d23a510b5146050040100e812102581110300d00c89419400b16590085004020701851080c104900d0708800101c00400c4168442a08418107200d19002d03800c0d1580a10312404032001108a040c001d6000100c3c0b580c90403860702c0c00150182001d1026074842e04412500840d481c003100d01d004120000a85400c948038800c858010300c0604081c44684c0c1400341d40c80c400011401400306504955407451070038074200141d440003c0241c00103c03405410005c10810 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 326415242 1250 326413992 326414009
    0x170606070507030b15060f03061c021c05060c03330a0e04060f0e06150a0b0f07050f0a1e0501020d090615080a0206040e060a0305071d060f0a03030503060a 68
    0x441c0d5882c50080c0c1c803580d00302c0d03a03080100c6003a94070880c0740c01e1000440c7e2491441030b0000d403640d55503004100c1130f90f0303103000c0101200c034144603480010b80b210003c84413011000d00310810001c07058a8140d2801000a02c2801440d030244180041904081c5800d00a40400341d01d0500117280e03850385007902c5040110840d800200042c00098510005207018003c500500c8188010b00641c900c135015030f01e00c1da50380304081c0e0245000078204090a83d0038042024000c00005040703549d400f0840403900081028070400b48000740c80310400c601000180c801c01c242070301420490295032989103402c0708041e603150414003c20108000c001080d030480c2c0600e940c012080080030f440741843c1c4000e000c05c2e46645007000c07100502040030800040c2c41500a03500822a6241505219000c0211b600140c07446801c81100440407002804c14025000036005000e0b00d1000700700319004600b01d46002400d82e40c09541120050141c03500c1d0100e041040d25010b0070215071740d484070000301c1c9a4661035880f5411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 326416492 1250 326415242 326415253
    0x10e061b1207030209120102181504030602030411030d1805010f11010f0603050f0106050f060a030b0d0515010b0712110c2e08010b03012922080d1706060705 69
    0x20b10540660181803500c0094030f04011807085842c00500301d100d00301c0d000500f58a0140c044441d45820181e110b4012205080a420140c6d65510311080c1e030016038044820081348084004c031410304100b84a0401120301d0104607880e240c0440441048880c0265410417080f43d0070320f950b950040c1000c0100c11043c0008101301c42c0001c0692008102500003204c1078041d99220283c0d0040500448044d28001003000c0c200410007820070506034040207207803040c1600c840c4604015a25081048455404cd00180c44003103070000e0110074000c0c050700a8070176500c050004401048501030700c0091440541041ca055000d008241441c0c500c0d0b014140e40d00182819001c00842e04003130201301c10041c410084841d00c0409441542d0a4009000d1181484024801005000d0100c80c0000c1c440b0141d4040403180103c80030700442c40d41c00081045404000c00b002d031850002c891000f4001407000ca0041d001300d81c0c5011004000d840780e51003070010200e24102082440d50740d1021200700c164480c08586 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 326417742 1250 326416492 326416501
    0x203070b1303110c01020d030b0a030b071805040507080a0c09030503041509050901050d0f080d06170c010810150e03060a0e071202011e051e030117010e061b12 70
    0x3814006074050031400540a40284051000c0016003480d02e07450503000340030707441da500c1c06c110000e044c202c01c041d074004255400040890300303020909000e000d156551440030888100c094040048070fa101a000354507000801884941c801002d40d0010791410020031107400102e000c80e10400c550b0000f8006000005000030b103441354140031018140e15072550003801e9507440c10050480350900c80c45802a511801362000140042c035040c42d550302c00d5003104d040c0622440d02608030f2708542c01460f100458400302060313075001000000713415042440e01400d01e00e00404000c4001041c0e02c00d8580300e4020905246007030b8020200d4039140c22000d412120740d45041c00700000a031a200c80c070301c90719020f04a40810641c146681c41c06140d50181c42e540d4100e2220f2260b009405480b11000040007414040100c0210300d202815070300b001d000450350344950404090100c81d01c030880e407407043c6030701d0849854641d92020900c158400445d0101ca03400010601e40e00f130341e6102d1864440100c00604c070411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 326418992 1250 326417742 326417761
    0x307050d0912020c10020105010305100915020309070603060e2512020705060106080115050f0315060706061509030f080c030f0d05090606040c0219030504080f01021e07020a060f0203070b 82
    0x10818076804445840e040444003038242e088423401e00015009c2c1e00001040502c1e15420340183c52940d10031007040c0c0b10b40c46c190750100300f2600140ca100c1c140e030700150010400c6562600812014140440c1c040115013030100000e110381108400100242c4840004140003074024101850040c48030102556181d203103160150b111a02402a40c021030070700400030a5281d1003034041c040348041c940701c8520704454134420040c1c0d40c000407d00854040360045075241c5403100b20161055a108500109015090000d00c2030040c6040d4800b10030080c449004001113200c8074500c001d100e030010201c955400300040788604600c182d002c0f40d41035000000d40c0c250740c0b00745035222074400d000390800d80b41d640d00da1a0030401958160b8502c0d0300185d2281c40d1140e030110f1840c1460704068880d09180f45050354502e00c8908020035490190000d07540400c0c0300252121851038409a064240c04540c548403540e03000501f003040300d0003406c1c20007031030902d540d0800f4002c004640883e5085202001a8942030494 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 326420242 1250 326418992 326419003
    0x130f05040b0c04060804060b210f0c040e10020903070e0f150102010c1205060117010b0405010210110a050d020d36050c010e13020f04050a08030903030307050d091202 73
    0x100c40e50404070700010310340c00c0c145083d101074030b0312540c554813241c85a48a100140a001c0303074459002c0800601c1110b141c800d418042881c50302c1f40040d101821842083c5400c081140c0d035514066401d00126802c2601c01160841040e032500000688420018020030f01d4801c080e04213800490264042c031050b510407640c264421a103140340c4418800c0890012402d80d48660513100118520058004c0d8a80060300b15680c009010304d055064069071401c42200d10742d083e48060b06003140007406010550381071140003500c0c0a00c44040c0582a0b280c0d014900502c1000491800c100c1c0c0442d40341c20701e1445404a441180700410b051100d011230144c2c2400444031044070003074080314168800200c00a41c080ca500e007940207000b03406450311100040d01c08801030b01110b58031544180050b14400c81a04c0500f080707444480314030340c0703460820041c03068400d001d4002a800c1c2d0300038068405169000012640e02c1482480e0568940000b415020050a0b4081c00104080c00c11108609503030750000b40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 326421492 1250 326420242 326420251
    0x60b01032d1b110d03140a050a020705010504080c010c050301050a03120207030f0308100608041709131416020307201305090a020f0d020a1203050c070806040b150d030e130f05 77
    0x90704c01c0d000343c00200703078101c0f032000000108100402c40080c40501d040c0e4801684070345000d0000d03141c10301c1036a51030300b10b8804850031250000003040b411742280c030910a001c1291030390304009203994180000100416070f41d2100901e0703542807041c01010340f4403d110701402507a00404034400b06840c2e00d80079100c560200c880e2060341c9010718001800f18032600e0124002c0750807840c000011004680ca2842c5a40101c4070550400a010054145590746118060319900d00340c0900e0b04a0a012400c03400f400344032000b178000c40d40180907090204124003800a00b5030415542d0a804003401b0f0086034403042c1403110740d541d851900c42081045000403403151101c52017101c3c0d400c018030181c402c010001021401c065000809210b017030044000104240c500c1e180a4200305080c5140340e044280307001701c01c1e0400f50503500514280410400b0a101c000c1c1c0189102c00c00341030302c414800204400b004d2110001d0208107020144441c9034580d2a00d0542d400900782041c0b01c2611166031002c0980000d44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 326422742 1250 326421492 326421527
    0x1b030c1d0a090f0f06060b1215040203100e0417030f061203181522030302010b030601051008040c1a21040f14010f020313060b01032d1b 60
    0x3000980c50035468030034040810707840391040c0340364003503070b207514400d8106401d041303c80a90702c24001c2011002c44010b0000c01c035482c06011441d2610803408602000d61914050155005005100b002025603588009684004050f03240725075981c200070008211030540a00c100d00000140100b1000c4422480d01c80c603001c0d00c2d03c2c11521b04042c00e49559100e610b0101141e8505021004900c0c5040d0001d2003118003103400640c14034860014402008030094801100509103900130010142c0a01585140034000c8015140a61620323010580149541e140c61f810001d04400041c01c2103420700018000d04031000254507a0100302d11524880c3c3d100d1001e0706c0d6420328001c0300c1a00703200f509c8100d510903503200c411010b00142994803d150b4010650000d6070654884082905a0342a480603500c20b00c1910b09a0250f03c1c50b80c00c200045400d11226541094103141040461060707500041c80280380000400795107208004454000305800c080c0000518901920031442a501c100710708117124215 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 326423992 1250 326422742 326422799
    0x33c0b0402030115050a09020f09040e0c13060311090903070506010e07021203040c090e030d020d0c03050c0901020a02100c06060b04062c13091e060c1b1b030c 70
    0x41341e2682d110002c51203284e6000d68000d4090001e120250050248030003003050341410419008005415a0360101401c4080c0d4400c0d0010011071a01004000c00e0100c0500104486825901c0d22402903002c640403d014000c81d50201c0d481d5101001103903441c03a00141520040d503100c603a191074528041c0e9100d00148a0f0445091f01c1e0200603044a0003a640030704120040c0d03191051140241c03411032051001c0c1d01041c8003a8401d40c80500050524a00d110310020b02d00712054000b60407070f0340161460144071803d00007000c107a600001c1540f9030a40407190000703907400055044428030509500200840c4c1051070024a202040001d401582c945850381e0641a0000110740381c006002e01310741d441080404204011810031021350380229103810008102c5441d9078075203034189a402210a501d2100c1e0605420030f00c050743c400c0e000c174264149810b020310078901090b8266908451350180646500c9201120f0310031a1040744401107620252003100b0750f56840e0302e021000d40300c41c0030518a4064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 326425242 1250 326423992 326424011
    0x120a0501090b011b02030f030703180b04081b0a0b0711031b0108040f30020709021e0c2107030206280203070306090e0703031107033c0b04020301 64
    0xd005115540506a5407020003425118102c07813501062101030b41c00d0702503507243e9041c135030742417008100c80c40c080d0312001900c00c00d10030701c465101d800e54010b050512061009000340380c000300c1d00610608840451401c401581030009010940a61041d084800001203d40401001751062002c4c600304a003540c03034070900d41041c0c142c0001035844d864009035140c4001000107492080383e821181c041c1110f82c1c41c00110a4544014644c2503800c0d2204c8114071000703400181d410440c107005000703074410650a04507861413091002d035500d031040350b4010000c2500c0700400310800500c101d68251040000034051868290340e065407100c1c40c02d40c018021391002030000d058810020a05042c1682500512284009240c00a42000d00014105900c40400290141e40741c01544140c00031040580b40c620b15614000c1e080e5100c04608030095001400f00300007146580301c0e00080c2d180030000180e800120031080714514003c54402c01c004803000c8407034406002c0c40552441c80f8a00c2503008010039084d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 326426492 1250 326425242 326425259
    0x90501050d050a0f061404030e122b021002040e04021f1202070204090c1701150e01060f17131419080a02011806090c050a0807030f02011202120a0501 66
    0x840030409041c540c04400c3e49000250404031103280c0c1c1c0e0060304001406401d108804100d00c00c1940e013a40045c0950a543d1070a14040248202e41d5081c1401020312a030302000d645980710b108001d8805d0a114444245181c0b07000388070741d0722203c4440000319995070f1501c3e516120040f09540590250980040100713460f90000c110003c00703581c2d07890741104504610440d0000e0741c46107600f283c02c45c2c0c80d0f001100000d0075076140d000240c0501003042c0d0120b100c4403886030854030071044107150351881d090200103810040311140d06503103041c9404025040742010580d02d240419041c1211982c101d0100040002010300f46d941c0b240c0300d040c040c000a03200c2d0b55481d9541a030400740b0781481a441024000082c400d80050800080030300000c1888003003070a000d910401c10901c241e42c0c954580c01441c042180345421000a00710032640d06030300c6c40c242041c0304e41d1a4214003000341b816505201403815a03000341c501040e0f50031b58140555880300c2c01200148603c0060b1010300005091100100340b103003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 326427742 1250 326426492 326426509
    0x806010c0b0408090402120a0c0e0307050f060304020a180605031009080334080f0603060403050409110f030c0706050907051302030c1e071406040b0420060a030609050105 75
    0x1d81141118145807a01d0319001c46a078040940254050740c01c005200c2503108100c0014498801d03280006080320703c40d0700192410b18038078015072003500300500500c0b2941d5010221010f00c1829100e8640f60398803403012030500ca002d500010090740480c407013000345034034a801a00c04c1e2401035040c1d40001c107110b4000000e0f81d029090042c03503280144001030f140950b40d40007540343c85000c44822040a2866681211400e075010302da400600302004001080e903264508580004d0140c0060555141686004015000385e0244040294a910144542005040c00daa48460b8075420090396400c201d4401440d40d4895102140c625040000156041002040c0c0000300c90b405003119041400d0b4100c400000d40c0b000b885490844001d110150102540c101900402503410712226503519040c14048041e5084400580700713036100900700000070f50708045a6404c154080c000652600880321a05d01c0c03060b03c88281c0742c2011001c508068060f034907420034421500751034403c01491f600c1d60140800711 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 326428992 1250 326427742 326427767
    0x70617070801170703240513020102031b03070203120c060901060506090f120304060504030510050601020a1101110a030221070f0b04020d0b010e060f040c09050120070b0307080601 79
    0x4101d640100500704480391603003042c440078003c0e5001e480d166038640044031085046907500c050110703502c4240340410f1054a405c6180385030629000000b80d80000c1d524403c1e54040f40340c02c000d51f10b0b80e1880020410a44445550050030754a20000d07120407901140c00441160031503104c3ca50101c0c0e83c0b54810f124007425990301810b9285098000c41c00d104c03c500d40750511940000b050104071000100910140016044039514030340e546241d82411890000300c112107007c0103141005200660703800188400b4515442456a0800395601005951001c0c1c0c0095060039401103051080805501040c10f2045494941c00515000802114100d480c0210a001880e425598100c2800705e0b80c440b4030154064401030142840d00d205139640380700c00e0710a9000c1c000c600c0110307042c46000d142000003c0115902a1010031801840d4030004200c00e0107440741ea070504c820701c2c9145400044038890742206019840403292510354500a82120b9402210700c4c2001480c13803408943c1c50340c0300786164101c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 326430242 1250 326428992 326428997
    0xa020906010323090a050709050a0b0a120b060f09091c020f030f0c0c061603020714091303091215110a080a0507090f180f020c100506030309040e07061707 68
    0x1402d03c201d01c5203246241c007500096070307445680e0303010000a004000c0d00000e85000703007022499091400c1c08a0070303a01c0400d269841205030f81d01c103000b426100190204295041401480c03103840e0714002c10500a03408c0b00c0c0c82d4000300360700304000ba02400011a1054940d51440c000d88210218004980702c22203080e860103650070810900c114a0300c3e401c0541001d08400090b82d1010b40071400050f600d078424120420320194152842050640601000c2c0040c0030301c0c04070359030840c004000140090070080000200340808000034060510466105c8041c1c4611851582e03180c240d81020f462203003a5403000c0c1a00c9040c001d04a4030000d90fa02030301e407002c48503110b50440d51540d045c03c0e0081c000046c40041004a480f90000d00343c1004d100031030046c2012116040c0c007101c07901500040e2503940e040419034a00400c03900c2d40c00f08000444400c1c03160302c91000106501c03102d002904510514007074941c054113000880181d0310010442104844250722540c90450804001101c50310f01101d03142c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 326431492 1250 326430242 326430281
    0x1230a12020c0a03081005190305060f010f18090c0b0904060f060512151c060c21020a0c02040501140108070c02060304020904020d0f150c03020f0919030b0106020a0209060103 77
    0x45d0240910a810001c6001c040e000140c40701c0108000c044201000b0802c00d41e10001042072120500905070804004241c2c5801503051250f042c3e0314040c03501c42c0390700d00144010303102c4210080760b02c0240b46540c0100785042d1541d84403100c2c9016004406680e100324600701d40090708120400001013114090380710709051120b0700b030400f0b16908004003180140f030700360399090800d980c03040d15114619101c20b078030307aa103642a810b0040494824002ca90144003a5141846003e005440c1c0d4241c01008140d006d030b41c0f50103a0724200c503031050300f02d0000e41040c2881d00100310144a100c401103106800e0703a1380200c42c1c0d00ca0340100c03030085e0003c40194200d0800c001040c0942084d1545581c003e0024200d808000c42650f21000018180c142c255404c8003118015101c041e464019404650707881d103010b50804000111603c0580b24141026204610804c00c0c0b0000c0029031000f01d00540e000322640c0010741e51108043d440c0c1507114000c0381300340325420000724079600900c500d2000b40b00110039401c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 326432742 1250 326431492 326431513
    0x309060708040c090204230909060402060a111c11030304030503041101091206090507061419140408070504060504060e13080c0d020a0209060123070201230a12020c 72
    0x11840740000d00305640300320240001290920550000708020800d1668084074495216007500840342e003000e500380705a002d041802800040000d4180d009a01141c015070303543c44280382503a11444100c1d40030180d0041c0342ca1480a1010585419a207000726255202400c03100f55640752039100461340200803c100f800810081a03500d07071a02000841814402500ca445c0c9203100300850074000704a50041d1035179022001c00038248100401401d0354180701804042e1211041c629000d280d000e64161500d54109504444c030408075540b02c0298500219a81c1d600e510384142c851b2554003035a4040c5042ca034000403281402d00c958000c4520700214520183c41d0300a400020290b00e140648803c501030141d03200c0c0d110203104820310214117030000c00c007000c60b030710610003507010041c051814000c03c1072120700300f052441d1035404568002550299105010b1005980f00102c40c00c041400b903200b4070100c60356018180050901c44000c0c0c642c032480d112412410000c1e441110300c1201580c00040102 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 326433992 1250 326432742 326432747
    0x50a0f030b01021f0207110109060c081e040e1b0a0f08040302010603080c0c1e09010e0702070312080601081005060915040b0c0606120106030506060607080d15090c02010203090607 79
    0x1c00041c0d505106451200e611008039100c0c110a21030301451859000170a10308102e982915420752050030300742941101d150400240c1740700c0203054094081c1c000000e0300390303120038450020b940400b55228a95115503c854100c000c5030011103005410410810810071640b44e24419111180c03581c3c0e0720400b0034006a40220381605000e4004c41c1959220307003011000032801005032030418250740060024104007404c102d000581548003884440c12440c0d0f40c0c4c1c2584901d03010324192402c8060313940c1161100d407070032481c00020794005041c010340392031035416850703014440d540100030076070740c01000f6104c44080164a224500c240c43e4080001c001c3d414590030a030311a06450501e0308019401c01d80c3c0c4404006195100c0d4008000a402c24010131400707180c45401070480d00708030402000103a055540f000c2e65020040c103a64403c0310042050303020400f0034000ca4010109514090120b40110418a44e60300707268091022034030304000c25852840c6c814803c0d2031040c02000300401c12529452401d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 326435242 1250 326433992 326434001
    0x607061b0c05030904540f0605040314030c030103061a090106110c04061719080313080d090309150311040b070309030210051c0902130515040c09080d050a0f03 70
    0x19540d18402059040090b04c0c02954682005542240105c0c0350609001010040001b118000025a041c00380800042144111500c443e19448a80080c2c6030700d8608068698600801280030300200000070000030216981c051340c1240e1141d4024400e02c020140403004000c90304c69030301d8108003030300010450a48144022151082044203483c685441034000c141510403035004010085040b040c1a5a02070040100b0001556950300000010b0080d84c0c0f610303164030000c0e240b2424041c8025100c030506c0701c0d54040380c112451017401008010403915020b0100e2215124002c003e02c415401c0b002d203540a4010441c0904c4050b00091400b410f210070464580c2200c2001e40800200d8180440140c803800300e00740c01c0b202c00d51119901c0d41c1071890100074542c142a100104142000070310001a12052401020400344007800700345503031006005410744c0701c030070003881d0300a080510b07000c12a50040b0800090344e2101c0c1c242d40c0c840c4c034041d6041d00c240c41005079050008940300e4a241000e44650302 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 326436492 1250 326435242 326435261
    0xd0f030b0303070f1101030207030507030f0e1215071107030f08040801020c15010506070308010509130204181401060e0f0705132d150c02040204050607061b0c05030904 74
    0x14005669000c0d50003203895030300403040882e0326003096200344040c400c11203000346408400b480c06514014155038018503e000e400c500500b4801540078118a5500400301c0d28400701c009402950044024032101d60b80301c020104100040402001050125105030b0000f4180c50015005080880c0795035607038000d5080c01c080540780020144004514a58203000a0184041c00c600800c0841384141148080c0740c4181d102e0351150304104401000290801c0180381160b4080761042040d0392515456110701e520310720029442450a1045001034066486882000e03000b80b291060008140d281d403402c0724000e001e100c0c2800319180014500c7e074105110b241c0e00600c2c61801034180501c2101f1207290f42d40d0794001c200c010391080308200c0780002c40d1040c003503503464854a10010b680b03840191840144143c96200c1004202c03103040081d902c40b901114001c240c00b4025655450190501000030010050131144c015038102c5243c0c50503100352070300b0001c00e81101c0a54a09000b400801009014240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 326437742 1250 326436492 326436497
    0x5100b090d050114040b040309060e220f0c020d1d030a120c050a0c150503070806240706061a0717070309030203060f07140f160c0e070e0f040501080d0f 67
    0x340f0313071402c041003003902c180643d108203960000741c24103107009441280b0a810520401c10315020000300313956804851400440399142d28108007000501081c0a44001c00106040d28109440d004035654001078068054040b503450419514003c010502111002c195179945544030710921000700300e2004401300c0111690914280c41c1390155a100c0c140500c0d20720a40e0b1a14060200700304040701394940c1d082e400c013a031400501d903150001d000380041d20068210f80c0100900418500c0402d040750322002c1c4400c000d400c081e00e03a8180d24250000d0940b070700034411070048201400d62099903490954450907401000070790454040d401c00c15464100d400203070208540c1034000070150b1411310501c1d0240400341021a00d51501010250030072683c009140100c1070108451120340704a68181e60140c1c244444030270b1396403000d050901d4000b0071a00050440d00311103050101e0503030032602242d41c01d20103a032241c00072000c08040000701d401c248264035a50308103840460646115403090600101d150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 326438848 1106 326437742 326437751
    0x80a02090612060604051e0f0a03030f0c02040b06030108030306030607050406020703030c390e040807060b0307081906050912040501050f0c1f05100b090d0501 70
    0x1100d400d80d181c00d8980400e0701c613940d50013160010f110051408160300ba010420000a1403000302d101c0c070828400c110084181040302007803080b2501600c5600c002c1031255402d44200d4030105040764480d81d0b842288003166124406107001e820300360300868803498a2414140352980150295013484008e201c1008040d0b8002000d0082c7c1c2c1c1c0c9403a10507511411413611b24003480007400c0c0c0e000f04401449401100080151205d074002c4082035421460b19518241c09400900644000d4442e80e0204014404602a5041500c522801804a4980e03031b6075a80101d041100ca0804464217a00c00b120001c14800c19020b056004168000034009020110440c000c0310f100d90301c01c16041c45000b003400f01c030b480c0b5450705849481200005580b80c0c1c008611045c034204038000d0005059030b1400c00400c42414144600505560400c40f0940c42c00d0031a20070003100b14540c140803034140d92075 = true := by decide +kernel

theorem cover : BRFrame.Cov 326258992 326438848 := by
  have h0 := BRFrame.cov_init 326258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 326258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 326258992 ≤ n) (h2 : n < 326438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
