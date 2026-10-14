-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3263
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:53.661637+00:00
-- url     : https://prove2.me/submissions/34d8fdab-7274-4fa2-8c8a-f61f8d50a612

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 586690647 ≤ n < 586870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 586691897 1250 586690647 586690673
    0x1303060e150117070f1202030616091a09040603050d1d0f0402030a0207050a060b01180f0905100b0a0f0306060c151a0301140612030c120d091e 63
    0x40e80040945081d08980105510700c1405500303041d5058042002e00400c0800c001d00060074072020f100d081a031520420354036021a04400e9020f0f22450011403044903050400c03a8903c58030781c0d0385802d03c5042110b030041c01404045040c401c40d20601c00300c469940c80d4401c240040d4410401403d40d50440007018040c980022650f54641440034a004d15a4036070011045142108441c0180d484d954142400c00030f02582001520520a4081daa001c100a90780b00c00300001f07003600d13060703200151201b144801e41c0a50152012100619400300b00322030141d0042504094121a0007640a403500f100d45200d4100f82c524000043c0e03846000b000359509841802c1c05010f02e031030309000158064598110944480441c07500042c0c3d00c0d8407864240d0f0b5503498030032a04d0381c010000c0c040e5540603003c1e99501c071001d0741d405100f1160071101e804030441c00800c840098500340064426a4002000c140e240c4d00700c51400a0309944810b0b162001030b0f22076840c880003003007548112a00d03000d0360410500c1180302c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 586693147 1250 586691897 586691921
    0x913110a021e030307051c1e0e070b070b0a2307090f0302031c020c040f0f0b0105250302210d0f0b0d0620040807060e010509090408031b130306 63
    0x810210040700b00c0441103a41c80705082c03c3c481c1d0340300c90070882c1d01c403400c2483d4541c40c0c0092420400e01ca8241c00294056104003001005100540f85201e0498650303a0038071410404107010400800000e458000035903010482c0840051903041000d2208076044644420701c1d04003a00c0c00400803083d400508403030142c061451070401244c25035010030360700d1200094410100e8a50301052051910821013111242c001a201f8030042c542007044001810100410074112401d1504083d07065100d107054034202041100d0900a41a41c01c42420080c03e50765002e0382180600988454031909800300c442c0b0344084017402c02d40e17500840f1507075030480360350450781042d040c01d140e155552036941c12594000950890000521b004588454015024110007007190380c400c041000528044081850001c0352001c0d1142e81085520500440f9240b0844102a600581c4200401c0220340a2009180c0c440300b4000701000408410010020540118079401840070519205008012003809644c941580c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 586694397 1250 586693147 586693183
    0x90e0f0f0a08090909010605120109110d171b060709080609060103080406030b04020417060103050d03060810090311161a070503160201120203011e0b0a0e060913110a02 74
    0x11041d55030142c5441150074052141482c403002c25403c00f0b084d80040c00910005001030054540007a4a60103000c6032442540c008000580444107800c20a00da11901940300d046440b8144450222404a400001422004d0480ea005030108044108409230084155840d4407455614007404280703041c40060540009402042c01000020003000c03d5a06a894600300460343c452000041002805030383d0040460004500078109052404141141a00d00800958007524081142071302903404c1d61141c0b00c0c01c0c5c3e101c3e9140c0ca00d011015448105018032900d001401e250b002014180781c11118410504805001c0004100382c25503401d0619611b0300401d503a038205a19512030036124051501e101518030b0300801c05a0445e0b20a6850481c203400301c1c1000c54030703561118612072040f0726100117000a11041f600115420704540c00b5a00120f400d82e4600e110f8800000a0140981000b4409500410480701c0c031083c1c1d003042d0103982d444c2d030084855141c46405031180240b8002c1207010000d080c1f2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 586695647 1250 586694397 586694413
    0x1413150801180638030a020904060504031707051c060b070b0108060a0c270b0f0405101d010c1506120204050a140403181a03070906081e10090e0f0f 65
    0x4040c0078845201d224006240910844040480c0c2401b1405000031b44c0004a54100700030820103511040c0a903000781e0b01c1c40c10b07450081002c8081948213a842c900070a405002c8401d900c40801d200300a40400f8107030115007035642d62070800503600300e0f50084a00050000040c0942402084690b038080715154081c443e00801d941c024140e0000203030715801d690310500c94a42c1c2c0d000b440d105031000b40541042159103894111946403a81c010b40180303446603006100e00700015105426500702c4411028030300c2c0020080800650b40f0b4400004110f078100b1403101d404070411000d100700c100030701e001100c02c3c49a8000744104000c80c0c000034541c0c102d50303180c02c03405000d69070140c811941c420f80c9810032103011030280e05042002200c0368021b4940d0444a08440006884840918010308407070b106c1d080f8042c1c80c0c841c291900b131070840d18170322074075a070113001d600702011001503a40281c0020915280b03184c443c4030750010742d0202180014254491103800a240758100000304028a200c1e0180c10b00d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 586696897 1250 586695647 586695701
    0x70905160e01020106140904140d05041a030f07050a090317040906050d0b04080a050906213106060510030204031406070c06050a0e0604150614131508011806 69
    0x40041401b100340900c203000002030401c0b80c0c1c3d400010401398140d08468948603011001411a401030159420b001140045d00b43d07000300060030742c0d00544c4034807070842c541d03607404070115481e40100b42004c00f000424840080030502d2401b1001c9040006410550f80750b040440841c04d54107140d0041d4001c0c01c80c1d85a00000c40d0b2168050303600306d40e00c01032199480f0305100b421901c0e0300620f030389180d100c03900241c078124003c503022600402c101005940d00c1180e41758542040710104524410a165114041ca010280c102d0512800828410b1400042a54843c80032a1211444154000119038006028002c2c004008540440d07003010400030031040c5003c40c0b000f08800a274010040070f4646075008250124010707004802c3c0e07900000110b07907031841c01c0d041145a80349103202d010215854442d001c50b06500980310402e0500010303200c102c14500c0e00c14071800420108901c4500c8841000c000300d1890740a01901c2c04000213030015981070b50641c00d10004840400b24078400440d102e854003810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 586698147 1250 586696897 586696919
    0x1c0503011e030f020105090a031a061e01021b031207150e0d021b0a1806030b180c0f0103020f04060306081c080a0e2e06090e0a08030405070905160e01020106 69
    0x200313642860700a4449000c040803a501d0516070b0802442504011103c014000b054000382e44500d00803110015515100c030540458280120281401600301140341c030390609400500122890b400b07001c840c06203003040c03224a415003064a0844214070f6580440309068124020404511200c2c0d009d04485031504c54013940d503815411003240d465802d1001c80394a030741c1c0c4085640c014020894070300c0d038031441502090000c00b0385002c100e40545903540803507890000c0245c2c42c001c0003580300007000e5032180f038001c000901140b030b0b002070b041640801004407483c0c2c0c64070180004200b01e032408a040e6052240b082c0c2844d1000703002030000d00c4000c0100c5101d0f64404400c3c0d8016161480c001854410600054184400b1010b0518136240a88643c092440c9203542d81d1340c4610302a6040003081d0316910120181e5400d405c0390b4591703600c030071403403408288044025070300144940100c410f003a607641500000c0d0380c0e0494001c8200450520918401c54010301c403006007840c00d2000700080350620720f00c011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 586699397 1250 586698147 586698173
    0xc02150f101a0f0706091b050d03050f0906190e03010923010b1e0103050a090c06120e0610060f0206060a06050c01020f0d02090319021c03021c0503011e03 68
    0x51900100441651282140303084410300b143c54105160b9518150078504050f101d01041100c100050076140000109404034070710580f003000300300031171903950b0341c4007114950040100b1a18000082009400e0340d0754002c010a26425008407549041c17080303035400380c00545500455030003a41006410800900007100700200000c5034031210003800c0d200c851041c0100461800c1f0342d0813006a066281c010380d6980101200c43c9001d81e018455a511171054406a881208009058003114002801154016080d1a8418140440c00030300b0039034107600a483c1c03103000e0312100356907131b80c2c2c0e0024040d65501580c00c00c2440380c140018290b0741001d4020814000c02807180d40b04010380411480e8140c00d081d01140e00090b82281c0258131007060301c0d200c00007503019280c25032091003000c0340040100010085949039540090030300c000c031940e081c1052207951000340110b046008102c0c01d080300803141108400b8105c90380d601e19440350f0501000f41c0c901e03c610140500340d860315200c00c0002071322015202d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 586700647 1250 586699397 586699409
    0x1a0439020d200a0b060f060f0f030619090207061a010f2303010807060f0c05030a0c02040204050d05010903030609090213020706020c0f010f0506040603150515040c02150f10 76
    0x5580004034400d1201c944100303255064107805003da00500340085842d00301d002d1081255041e00b032031441010801984903000103200c60345c0302071140c8010074001c04091a070000c0003426901c1890484490f503421801c450300500c92081e40410340900f8495248151544030260006514407194032600290420300030342811070810041f132100c4445082c5030202c0c0342d80e000b4504509500d039611200d003103813a0342084c00307110009104005c2c20900103114188611495802c035000d1841e20030707000d00c1111000d138045016a00325408000c001400c2d02d4841c28209a28051000001c0e04c848524008007602c6141d4072480e91036013000721540150f40c1c0c0ea44481d55084a503c00165a40d00e246000000f0b40221003d8400c0381c041d000f0494111481074100600200c00c011040100e540ca02d810072088803000c1c00042e2a489031104074036801603050f0701c05500001c01c2c00e006143c880e0b20000040c291185111a2001a00840c101c0100ca883d6000c91540201055100701003520700100645103d0440e44298 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 586701897 1250 586700647 586700657
    0xb0f0606030c191e091a03040c120804030b130b150a06030e01060e01030b010602121c02090a0e070309020f040b010509130905071d060a0b04091a0439020d 68
    0x1083c111402255410780d101d003584050a01c0c01c0c180715004d09080854481c4200e103c00c85c244081040301c003602200c0c03080d54040f21480745035040c00f02550b42c0c0048000308448040c020403000c000f045203920038030702c2011803082d03564083c41c40d49403014905130041c1141c1140000d5010b40304680d0351349000c580c241c811511b0002080203241840034090003699201000c0040914004010301081e00e1005040e02c1d40c580031104104404445507065100c4c140c80703440301c02c405214100c6455040d800514140350020400d8462985403179919110310300c10740700030300460341e50003040e011404c0c00c00b4541b484000403113080001107100d4001a100780f10302611244500348944d0504805643c682c084440103421a04650140d0380341c82826413078105260b0850301a003007040000b45540b030141440300950313250b10101810b1a19004240c40178103e01148940c91461044034000340d5100c9105882e40080c3c0840c441080810402c00003880034103842c080c1e0301d2021018020f244558000681465141042c604 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 586703147 1250 586701897 586701937
    0xc02090c190f0207061b060207050106080d0503040b070f180807050a0e0c031314030c160503011b110c09100e0601090b19030609020307020a0302010b06070b0103080a02010b0d0b0f0606030c 83
    0x491158030702c1d1404010700d87d52010914609000c01503004002383e400b03510440340380c200400d4040d5242e000480e0b00520110304540000c075418458a906003548000d810083d0f10b80014542003a0110910307004240964010082081f80746008e511030741c01004140001084c40c07c01d40000c003250f101c002c000e01814104072041c5010030000b0300741d04011a0798001039946403450244040d0303c540070071503100703d10300002c68040b40614061140440c114051310011030325440c0c0310005c0e20002c0c581c5c9180003180c0038803400c840e40c03900c5e0711000500c48c4c440311076aa4680c900b081c5038001080380c05400c16040001990041c0f04010025003100d01501040d80c40904a620819045002d000c0d1600545801c900100501c00e41c1074002030501d0406100740c0003440041000701c04c3c040180154800642455241e0b401000426103d900805802410307100104a02e8011000b01d1150609454202d50110351700c800c0221001e58114015008101103504510b542440604001c80c2c0c051130080c03510740030307840d05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 586704397 1250 586703147 586703177
    0x80312060f030601060f17010e060d020109120b0a051506031b040909030c050f0606010f032316030f0603110405060a0e0903091c020108070f0c02090c190f020706 71
    0x34030441e0120003003c0711615a10b03100020484011080c4420100740585840045081722090f82c03030688000034040501655908100142d103821503106078184480c0540101c1c104030300f014180c16440c000d010326685418190500411244000c0410204c800300c1c01000850396a00c5d0f08880e004180b10046050955411481a81c80e1007280e0000e904989800202d1080503088145030b407071784d40500c080d6502240e000504a880354000c68002d800078151441904003240a0b81c482c0300c40d00e103882c0c0c1055034410500715207145148161000305000d086060340c4444207925010b56004051442000d00009141d070f9603080b054070130200141d210384d84038000595161901540c3d40002c06c100c0e5114481410b21039082500c0c1d81c0000398031800348446000c03c9900c003a4400d52407030f8281d41a940c0204c1999400400c407600510304161500704503141d008140540d540006042c02100c0d02404983c0c0d40c40e0580b51001024400d683c0c1c0c50a024109034005170360b035004102002250301c00c1c28442d248514402c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 586705647 1250 586704397 586704409
    0x6030d1407080f04060807031a150d091401020912150610120903030b040c05030f010e19091506051210051b0708030f0f011a0f0d230601030608031206 66
    0x394140110f030011030001011684114884d01410403500d0801ca1039141c80441e40380c2041c0d80800c1c0b82c005520303da0015901485000404403128524000214036074656501e0405900800034403441e40e40102c5c0c01c10f130b40c0c03920880180046280900900342503618191150700400010302c1d0390301c240004010080000e0080c500d54070070700e02000c0c00304075070065868098000c040c41a02280903034509110019a1070080c02180d0007880340041c005216813801d2420390b4105070040a500416014088074201d4848500652060a20514642d060600210102ca0413500140c0c800c620808000307032220104040829600621100961b011440d599111540703d0400a031070345601c072030140000c0040c240401600036500540000004034810f4907441009043c0d05020b004032101381c65071446070041e07500040010003912981c490b08608001000d0481000c5400114014412098900e4a03016070700c940f60f0100e030722100c2400d0800866003801c19283d600c0c011480440d20b030441e4007010034156500d135 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 586706897 1250 586705647 586705657
    0x20a0f02120627070612111e03010305060c03010b0304020409030311040f090c030501081f1512060608010e03040509090a02090106090e0901020901051c0b0307060f0806030d140708 79
    0x400c0c200d40d401d060018801690380950f10010708500c00070a420380002d1004034000b42228220b0f901e099071204921050700080040a0300b03001450b20800080090080c001034400c0b4044080590a890350b245050160400d40010010b0100c0b4200300014041843e09200307886c2c03c50f4064400091000b11480e06500801c9510380c0c03403501720004580019088400d520300001e451040100f4406086000e00503000e42c3c0081c0150705040d00003e4103010000f0700d0407240203410030510008038180c5c01c1c010705003d10584680114200001500001082c003a86004080090441000030040c5510140d03065449014600515104450450205040320020011300402d26002455401107595546c40074082d08402d00c190072200b8051000075541c01410720a9400305001070711800e1521a03074a601e03030380d40640030380740d040c00c1070780c88503035030610b85007045050003602251301c0b02c954507442500c0142003044002c07c014829406450308804c1d50b030340b0000e145100d519071307880d0030f468201b180780c405424061 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 586708147 1250 586706897 586706929
    0x807021009200a08031611090f04020d060b06030103120315230a1703090a0f0b0414061b0c0a09050c09010309152c0307031d03010b0303070609020916020a0f02 70
    0x10070000841c94244041e044101e100f256044642071400b030038040030400427902240c0e6000d031103000030301504044c00c010218600c2810000303031041340c1e4800505160420b820680307444050200350080241c0502c200003a90002c0c0208000e5107140400c00c1090007503200e40d0702c070500d14900300c0816549450105601814005c0c0a5881011203059141d66076040030301514401c03100045d000500003d12074080040d140a654014540360426418240d4401c0c40011140c212404000485040c107000320100303100842c2c00301401d0308101c2d94003008055407054203c3c848045c9008107006030820751500322403400b0400e003000301c0c03031229038103200c0d0111341e0004410841d40e0402400c00602e40044508002e50100c0a500074041d5660600840d07890282e81d0000700400c07242ea00f07400e55030001800d40e924280004001185440002001c24256040524121003858441c043e0000714034064003d0b5034002c8040114440001b201c1d00b00070340d50310025038082c0c803640c0b09000700c000b5034880748021024408 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 586709397 1250 586708147 586708153
    0x30314040e13060c0f0e0402091203030406091709011e020a0c030b01060f051c0b0a170106080c0301090b01140409300e0102070b1c06060807021009200a08 68
    0xb82440100d0031007001641d0486205141c401e5800200740a800a01a06515981d807100c58109a0303040c80001d6000248003540901c0d9a0040c0a0f940c00c10002984aa84503080110b4107411030f00c0c141c429222240c00c02c1c01081c409102900480c0d030b11020210980030441c00390034a02050b01e2003641003400c40b400c080c2483c100c840c0040706100d064600e0034103c0792250307503204400f15525030480341401114440d154902d44501c0340000003440d5001a071903103070003d00b0101410b994080304d807880c90300c9505601c1542d440703400800c1750907410700158850800c00c1e03001340004282a0742c0e240c50110140160303d11850f010768100d6142c0c542d07502148802d0b0307000313003800c0c1d42e0005803200000b0402c0f02c002e41801c0c0094001c1d20101103100b03540d140441c05040e00180480e904000c00d520040c0c00503007000b00e055110310204020251540140c034020321054640c0c80c01803d19a200909000208113241106810003444e040040c80f120100d9400d145080140540e06240c40d000620342c03d195408001644 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 586710647 1250 586709397 586709401
    0xd05150a0b12060406240207090c0f09150c171e090301050709030803010b09060c03031302090708071403060607120201050612010504020a090504020d0606060903060e0610030314040e 80
    0x8122400400802d0350040c0c110240b65640070030842500c8240c00750040da0f0750581c0080e40c001c907000c00c0070354890f40e5500643d0b22164403840d80701d0845030843c1c8941c000500c81c07011891003e401642d42c2c8e029002030800400c04107009a00a0804405035030000c003080030414442400048443c01d407903200c05405102c00315404405d000710000d401081c0c010784254640004148580d016000010880c1e51241c0540c0c01d580c608101c038100780c0c1101c104243c12400c01c102c2252803507420300080d48210100c0700b40c1c98503d80c070b03401404880003001b445c03141448180300038440929041400700d0f000c05207803c8590b690b641c5940c08601640107021005000d0821410118816501908044d02c1500c1c00d44000a500741d005080c0d500740c1d0015035010750000b030040014082900c0b070341c1080b035216002030300f98021401580d0700e0004551090b40b0800000d01d01e05018010000036000703013041420101c0003003609050603800c440c2200308510000b41402100a100541c4102080c182d4008107840250307641c0d40c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 586711897 1250 586710647 586710659
    0x61923040314010b030709050a06090504150612030905040510080a05060a0c02070f051e030703030c05060708150d150609020702031e030a0c080d060311040c02060c0d05150a 76
    0x690850300088907500c0c0b0554681c82c030a48148990365000c44028024940300d032030a00c84100401014000c00c0d0566204d030004240c00701c46020b018000c0d48101421241003540c0d40080040f1a00341e0040842c0e81e462044031008680d01106030400c1e11001c1318009060781710a0503132240c040b415880b000342da00890340c3c2c00080c80404a081031003021110703c1030202004044049803151090700581c4158a0703105c009000604011000501c228915258041403e4000d00024a0b08400364001c600045080011004001003408000c2d00303e8203d003044001d80c204403110820007880010b140307000c0d841c80c4502d01c0c01e00001c005028410080520100050b0381c98103c46e1001e940040d0069020744240c4200c4010b01c03c005680200440a10700a942441030740513041322048000a800d5a03082c20a0002200300c104c9807065900841c8030300d552018200703550f000c2c04260340d010348582065401c440104203034090800110faa42c0041c408000485654034580b81003010707001c0c1074003500048030074004503c4e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 586713147 1250 586711897 586711967
    0x8030604270606150906030f060909120f180b03090a060609060f150e0112020f040902030601120603050601120807051212160e130b040c0822020619 65
    0x160701d02a4000f80304841e201c01c55000850511040c6000250035000c00300700c0780b407007507100c0750000b0340d81d00d000714690b42c1c0c0d03030040c0040d1140782c0d009840350010002112855034016001e03480c504c9079401c0c0100800580d0440410100b1548103108040d013000000074031079507040c854409170030f40c8034108100b11900d801228006100500a070341c00c44020b4040840c089a650b0f00d40d10761074400d0340e14082504183c500444520440c0041000303c590244002c040b40003102d401342020b8001d02c4001610ba14000c0b00042120b4212810b80c20020328003030381403002c54004107500d030558000c440110559400c51400d807056208422002d8854011050803030b00d0950040c0061035051004101078940745c9036200313801c0b88658098050400710385c0c3c800080b02e01e8249000a48000403142c500040c03408100004582565000507101000441480070070441a030400c8158450b800944c66001002d03042d6404941240305401c1d43c021409900320000554512807001700c5601000047c04140700c000380a0b0380c2c01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 586714397 1250 586713147 586713221
    0x1e030709060c0b04021224060f013b04021317030301080a11040608030a0905120a0c050d1e0501020a0f080f040308040303060f03030c171608030604 65
    0xc0c100080061007501c14100c4162498204110481d41d44442e420072550741082101103101c1d0140003106d02c618107064182c015400b5640403005014a402e0080000b110319140c4110b050000341e07a18440440e44411880c2611081c4034880c100e5140000903003c04029074905603584130f4000145030b01c54800d1640400d08030b0314129081c1c0c0c2c001028807801c5440e80024010f800c082d9004010b00e0010500d8180b4501c0900700c050000201c0540380e108890865100c1030385640030542c24a810045418091040b48400c21890050302d148541944c0301d120351314a13413007041c4c0709440c071129030014804108020311880203205080b501010040c070f03089002c0c5d040015520b000c2449402039020980c080c200a603c0346488040d02c09807a604c0f5a000d956040e4090419400c0550714880400d00c1c5a50725858000756001e81c0300d41d03403070f1a5149000c61801141c4110f130542800240030100a960381f800d10540300590241d195a203e40c1d985002c140100600c8040400c0803900c2c03100c1e402081060100300d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 586715647 1250 586714397 586714411
    0x40209131b030e030a0f0c143405041509061e0506030103080912010623090a021207121401030317281802060703090609090902030d0804081e03 63
    0xc4014a008416011070701c0c1a82460f41507041040b2501005100e4000d04041d20604d050151031406c2c26110410300701100d0701d12001c00d0b071101c10404005801520380250f6103001e18603500070b59004268031040444d80f40709643c0505e4441066000c2c0d8800c00f00000040c004601003004002d554000c4500141c80e499907040401c801400302040504005003106d05807a00030344000d1034401038000344100c102c1800302c00b1509568503080452840512401e940820394001801d1215074a01000c2205400003e0516064988100410481a030902038400c0e030041d42030614000c140c00340312100000c0d000702c2641e100361041e12000401007642004441090182d2003114540c59903070b145100100600c2032501610f2602d40500d090303e001a03d401215002044003a40c1440c5655640403c0341c903081041c007103000c0303111814240305440d4400c440f240201035200c014840c051031a0042511146244040d008004034071001605021480084454548142c10051901e100410000d445600241e800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 586716897 1250 586715647 586715681
    0x17270304080d0e100509011b02010c06090b0a0e03070f02010f053c030907091d1005070e090c0319020412030306060201050105040c0512220602090117131104020913 72
    0x4200102d12500031b070384c0501c00c1a101ca20341c004200856034030101042008078104084003442d00006100c034001d15034200d110300707008102414880b110000b41c07040319052103410b50043c844003011403460310840034869021300f400d5500c59a1310a04607043d1003050480c0141504a0185164240484004821380603400a002485a010080790402c42c4000e0740d950340c0507030003070405001c1d0848aa01143c85040143e00480901080240d9541410800581908465541d030104030f101c0b5040041c00c1145a401c80301100c55141c05040900103010180c441c148580341401d014840000a03070440307000c0c000901e0403d02184032031400402030070b598042c1c1c5005500301000000c050404c2e0045280703e4805880e003504010110030344065400c80240b0718144003420420a48009440541041c0c3c018020500503a4074541c1000142c0685a0055152140075200d820420664085005c1e41c0792142d100c1d5602c481001c540b80054081d010306001c5c3c980c807002d44034607000652042d034802424808030000d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 586718147 1250 586716897 586716919
    0x609180c02030a080703061e0504050603010c0210020a030204030c18140105010c080702060405100c06060503030f0a03050702120c070305070806161115041217270304080d0e 76
    0x4010340d080808004050b03401404202d00f914001d0800c5503106485190000b5050394030040e4080154400604101c130341103940e0140320904003406219800b190550087c01900d40c181d500960b5250007699034824654049016085030384641c04560056410030710083c40951038905622032800000d007a19803151808820075425411128658101d410503101c1d0b403500241601c600156074031180b400c90380000300b0840071519545296441d44001907680e900140c2404e04e1504a0848416070841407007540b0510000c0042640401100c55540c4103140128840c1c0750100182d291a5a0728214110316802051001c1030140c0011200c04480c060011142204d9842640300c0d280c042c180e91012100c1120029411000c3c040c0404d10380329148001150880191400c54259040c0c00395003c440c207940c010001e221300d03540305506c000c46400c1e20f400081903080031482401d205d5003000c5604800e41e03609140c507102d100c062043c0d400422202d4191445910b800f48000d0818482007a07451080c00f800708 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 586719397 1250 586718147 586718189
    0x15170f1603091211160605070510090506010603022505010b181e0c1c0605152803021b01050f07090e010b0318010e0c1e0d0b06190609 59
    0xb54a851640080c11661000307031144003240e60305001100c0030690320801801441010054000400401d0310380d82d041c0d01e5080529203503040c411403c100180b50303824120341f00c000c2a4040359160441d03e41f4180148d666080039010700f024002c8040e6417030804a182040c0b8180181034001103442001150504c8201e400e00040000c80c41c420350b0b10b40c004030039607a81d050310307a076900039440d80284d0900611401e01e2940e5151541000d001d2481000003a1100340420042c10090008001c00c414110754904040d021920000c40c00c003100380c450400c1a0781400c0c0074403540258115032015070754510280ca155081001036020740410f50b09480740b2540320000890541c49040803406586000f240c000150346452650540342d000a007106207004203850100b401405e00740b2428100b42089001390041d4025941003200d5030b103200403081103011881083d11450343d83c6907040d01560b6844020340ca0162070b00c40c042200c18206600810459114607804107145410034443c0c02100c415004d02e8011624610b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 586720647 1250 586719397 586719401
    0x120c0f0506160b0406020c0d1e1b0624030609021806010f030207020415060201050f0705180927030c070b0a1704020d050102210a0c02060115170f1603 66
    0xe00342c000c18800c640c038103200144041e0080c94005000f40005820b028140150500b8078040c051901c021400914503545911180000c00050514605001c0300400208589000c8043d4810000703105580d2101981004070702c401d107035084daa10500c40c03800e440340c403441e14070000c08003920103a10030380082c0001c4c0344417482400c040e88144e6041e5030340040c80d044601c1c10780181d080000e00700d84c8941c460307a28070f8125140300d515000800e4907900205142c02d0a07000c001d00100301604d144204042044023070b00d19100507203800200081a5454205552902c131510589081d00d0600701050075220100c14020b10004003400e501800d00f000d4880380c5507209000841c900c503184102001c40d2404060038851741d82c60200540c00350000d0420711410046541d1f080c2240c0c410510170000341c0d03c01002d4540c0b140e044076600d80c4808044000c00801811190287d580c0f5014410307100307500f07405000700340c0e040d201d400003401440c0e8481e500b080030305001968400540c8119005089048600e40d003006682c030038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 586721897 1250 586720647 586720657
    0xd0606080307150b2b02090f0604180203060c130f0303200a03080a05090a0203060f070e0102071a0a02100f020307121407030f022701020610080606040b0a120c0f0506 73
    0x100b17400c014100084100413050014069840380c14154000c00d00503072141e9030054411001d990080007903240010400048441c0c5914003141c0c0356040d850700c00140c90010320a60041400c0350115141e03140f00303200b0000044140c0124007010091301c0000201904140c25220342c1c1a441001e100c406510282c1964481001d0000350004c0c275008003090102072243c0c8034a80002070002a680c2d0b981040d000f013490281c056810082408101080100c042c0d4040e2030a21a1002407000d08130440c40c2c501005842045e00c0c01c517100d140400101011a203000b0400e0482c006011901400004944c1031681e00a400031507900010504081e41000c0176a0b652003010749100c600c2ca0f402c44c482c1c030b618004030b000b864a050b80360b0090f40e08201d6000702c1140d003c0d2100b8010710185000614861042c00207050141c060100345000b0304404081c0701e0301101003540d035401141680c0006036165104009600e00400f548035403510200023480380c0a000c003480000081e01c03c41091855410f03541c90602004c0e1040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 586723147 1250 586721897 586721899
    0x20609030f0304030c11031911040c021b031e0109170a020a060c02120d061401021212040305040509010e061e0310021303060518010f1a0607020d0606080307150b 71
    0x704100103400640940c41296029004145280b0b10304030810110380b401841c050069803140c000f980b0881045070007040304d4150101503400f404040c4141c04041c0d41d507040c0c0c0e108404481400000301c0c03942e86041240d0701d951500d54050560106440f19014020500d00384161810300602d82c481ca1151840003c0300c3c80c2c0407040d03004280e51400d985509005140c091400310450103058a060081c00f002009002c26240c031410001c1d01c14074191400f100742c015900d0030340c10364010503202c0f454484c0002c00d44e242c048400b45200c40e44daa0b1450211414400d80d001a035000544200104070042d00040062080b001965801c542c140d010f0880d0100301c0e4100f00c4160303d50300020445208803100e8014140200a154420320b0140c0c50ba581c0d2001e0301e40032180c4940880900c840417801d01000d01940700d4054601c80c080080328084240e03503c0f425116090b060068400003252011510ba002d29825515085442002115128201c031b5480e0740c052a001e441903411200c1041d010088c9105203403900030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 586724397 1250 586723147 586723177
    0xb04050c040339051206060a0b1810090905090f030a050d1814100614040e0c12010e16081507051303111e0108070810050a140102060903 60
    0x71a40e51a24010314001c0c50703191003c0043c0720030203401903e80080c011002010101400ca0314208424414900d0110280300481e601c01024090a61140b5080006440000c4e160640d6a020030341040158156401039a42100f00201491a00e5034001e40f0801503ca0700c1307a01707100b030381c8400b018682d940140c880e031901150001c002080002d40568014034035038084c0f00c00412a400c02c3ca60f000c05407001d100041d212101281e041c0500198240819000212030440810855003401c400075a00359407600c0c1c0718090742d611110900c61100403c60b02105100040c02c0c1c81140070078848076800390071102040590351241001c075240d000614400c14080c3c649000c0101042c001c40160401c5c100c001400d11014041c04019492003030485403085400380d40507030800d8400382081d1b824800b01c0d0a050001d070b4800069040481da45a13071252030250232090a00d01642c0d1519000c90703440d410395280c0e00150f8000410440021720005004200d080500b0980994210780d039101905a164403504204900c0e4035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 586725647 1250 586724397 586724399
    0x70c0e070c2a0e0429011202060f0d0207050106052106130f080a02060702190b133f03060303230706060603050907050604060906110c0603190b04050c04 67
    0x80700c07119142194910380740121102a81c03041c1000c5500d80c10340b0b0544018261813001450000e4895200d80e0306140c1e8000c0554541c90f007e100c10600c03410080c000e104580018061b0116000072054801d0304200350700455883e4003a20f80a4000c0c44140b064900035004180c0c0d0810300c007171820034691885058000380c450b036035131062424000341c0b00b0001102d40c1101c400080700440d0740d400191406034895002403285080c102400381c544440181004501e084110100e40041d0010700c0320b5030011a800c1030303003585200516120313880d4501280301484405400d92a03001c014003009003d0040e803244c10400c0d00110305104c04030305070345d041c1c00060080f0308411407003800c0c80c008040300d41503c04a00d9516040400701c1c5d43c0c032000d5400d03a07400500000c0e00da034240015035506005080c0204021a11075207442c2c42c200c40030308661094070451050042c00c20b90703c00c958000f80910003041c1c0c0f0091000341c0d20f2612403520608201c074207500300111403408450031100c0c140340c0724160150241c11800e500709 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 586726897 1250 586725647 586725683
    0xd02090402060d02070c0306180305071e021f0e090c041a071a04050610030b150112060308070c080a0506042004060b311712070c0e070c 60
    0x94401c0342c0218042102241120481c400f0b041c80b00d01c124403854015140d400c001c8140c603000d961101a0f50012200200000d402130202c4060503401400306100180101b1001800070344e09030081c1d000f11702002c000e1000d00119200b201d1147c42174459a003010b0045040c0701d0a0380702125005102c401c01c000034006068192001640e003e00140390070b1410b1295902c91505407070412a007102c00305050280003c000040c4a0780f07901a48241050301541d00e15114414098409043d58182400e0b006400d0016441603020201c4110301c0c2c1002d1040310b030341e49031501c1381d68400f01040d2181122004045160718020406052003a0000b0040c80759032119280c04c40c3d40020802e10315900c0b0480c010f01c8540d038447d0300414008011201d001030312350000c2d00022881c0515011501000910003c0c901c203081d00802c401130a03200f0000303c030500070b01211780c5145400c02482901c810041c01240703100c10002c151441106407000c84403c0246e80d01d515005546607445100000d0210411400d10304030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 586728147 1250 586726897 586726909
    0x5060310110d1406011106060a0311010c022e090b191b05060103021507032001150e0601020d030c170604021e0306090f04052e020f0c060a0b0d02 64
    0x18040341140d1071528500c0115a011904540d81000c0c3c0c00d0002810825a581c00c112913000d0000b40320702038492403501078001100070701140802824843c0c402644a141e9102c5c200c41d01d02c55038003500b440c0d0140f200710190309130444c40364928299080582105030b4020722981d6208229100c003040d181c1403c41e44035803040000544040c0000b0404524050207040714440700341a110743c0143d0150a0f65411801802040381c150843c80704020010003003400000d0b4003881e401c141c003e070400b036905007862070401c041c05002c8000d084002c506c54032a0204031041d40c480101d000d020240c0803100d000001d41c4042e400d503000a400440460f290b50203003112902c280b0301540d032241000303000525040403e0840440e000d00345d212111011004020010030b41021031646401601ea801b4840c0303d46065a140f6580d1045810003011642c403850740251106225a4150302c01c209460043d900c1c0d844030000a04150001c6080450900c80c00010519465082c841c1051100c80a040004074030810f400f8404 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 586729397 1250 586728147 586728161
    0xb070b0106120f06090b011d2b1202060915070e0609011707020307030e15091908011b1709061302030703050328050a0507060902032b02070905060310 66
    0x5429214110f0800030316080c03241001403c0400c5000541420840c0010110200c0c2c01c007521410040d880205010340d80c3c403125641c20400c161102c40ea0010804850206900042e0300400070b046e540b07031408009070081a2948034030b0031101240c1d01c0c28408904e1000c091400c1e20044040350320100e030403900b400c14400602c001101810100140c040c02c400c80b079551a012030b407082c0182c00c045003030001c043e41300860814070b100844428600405009000000303200d0080d099200d003c1c8031402c0b041c0e511005102ca0003c190840c0204a02080c400394400ca03043c1d01107042d4009906eaa81610340401142c000f20300034880000209078507540c1c0030a182c50500c940b601a03a040c400c1900000004500700000d284c20942d120b003050b200030300640c1040d0f00500303468403402072000510208030155404400d90f100c00350050320102e5110b078503001103401c09120884001c1500601404c1c1400d002d102d181d2481c402415a0071149040d5448400400b00c4506031185c2e81d0642140c41102d03000403564120304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 586730647 1250 586729397 586729427
    0x2040504050c090c040f08010213091d010c020105010608060d0512131e031a16050306060706020711030c0a06090302040e1f091101080c030f040c051008040501060b070b0106 76
    0x10040041e010015400c03200840341345111050000301071004040341100c0d0001002c20800030360503c012551500d400e0002e6020f44640c207980c41c01000d00a0381051703002d0302d03c0d44801008104a60940d01c2c02400303004240180808146042d001c40d14074201214018150740e000790140c16000f0403001400003d60081c1d102500d801070015022030321290000c2450002c204002c00380e2042c5144d880c0c00c58804510590741d40300c1c2040a800c11449200524814200399150b2a107103581c3d544038000620301c0c1c060504050007040c030120390300b400c01c40c0d81e201140c0c803040114121003040c4821030410110029074052000042d1010804200604098204c4203030b113034030541602d00304d600e4518200c40c144111038030540c000d9101c035800d005112544000408492013807914886601d04032508003403900c8003801d441d04c004440030000707041c051520120360203004010f104841c0340034403010040c44c1c94004e48054986510b40140002c0d052a48011155032983c4180f07241e41c542e1800c0130549400b0b00588000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 586731897 1250 586730647 586730653
    0x13020402130914010b210a0f0e0a03110c0a0611030702152706040b070218180c1e0105070c0503060a14063c0603010b07210c0204050405 60
    0x6031011040610169019007580b400008042900348a118107043d4180d001ca001e0302d50810003110380500c040342e05416205401c0d141c0300c80c3d0302c42882501c001e0180b010787e860031519108044002d6603022803110f030079900940d00c441e0140006400b041e00c1e0020a00007541c828040c44003000520b00980441e84410281320a59040074030300c2c2c004c0b402c51103040400f00a48000003072200b18600d2a48005c0d0304225405424203108800c09011481d148198082c80800380008140b050842d0341e07500d00b00e401c441024200500e181020b0f000302e898220b080c0d01d9400700e401131003091300c3c076406c0c003004942c1400723008010969804032140041d50aa1710040041d603000c01c45480110b03260320100900c038021a0b080000107500c845800c4814050f02c0058040d5100d15501c1c400404a003200f814400b442000c20418904003c244007860520b9503030160007150045004400010095540300c060300c00a800380380300078a101c0e526401490000c0201c0e07118000702d0003542101d009400c00d0743c810350740b186c4a1411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 586733147 1250 586731897 586731907
    0x50d020a03060c0504030209130512030a09050f070801230619080f0d0306080607120c09050301050a020405011e052a1506011b150c090b0d090b0106140313020402 71
    0x103100d064656661005002c50313000101001141080300b02a80d014a8503d6070311031a40c100d5031030300d441d100032800e0f0004d01000440070840b22941507000400305075102c4119001ca401030381c0119214805031081c40800e51810340d8402c0c1554041e070709a00c1c01100391040c3c41e082e646070001c01c41c44042c58003181c4600c843c0c988011816070800c0141010700566607008120310b05490000405551194010802540103c02403100041d08401200381041c030820307021900f1514540304594221660744007a1380741d824241802005040740d40140140d400030f980b08044035aa1510708840307072014004140000d8000c0003220002e65016400802c00661409505010b0140c070510320b182940c1502102c2880b082c0001f402000c0d03800c40c40344014449a01000300742d032041501d0390040c00c0001c586a031801d5466032101c9030000e10404152024010070f00c8000e4480c44507240c6000140712005003250900d04000010603c035002c0c418003020000707064203062465444e550310350150440341d14101d8100d40c003440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 586734397 1250 586733147 586733153
    0x190b0703030e190c14010e010c0825050609010c090303050f041503140609010602031b0a050607081501090f06120b0405160318020102061f0305011a011116050d020a03 73
    0x460101c0b400f001840418100305402c0207050424560700030340d0718500441c41c40c003060740c0184041d21019800d003001d046030482d40c20810303240d1141d040c80540507007643e000210850000300505815501490441c0e402e40c0d9200d0010307003261030003401d84001c5104004100006071041008148265192100301d04060391104d602c0301da0501048148003207a1100c0c0c010410b520321500d01717980040c04890060f4154504040652130344200c080000e00100d1340c3e55462100780d420441c50b811550f008080300d4040c600038500401d001c400707071640a214941d0002c06400c3c1d42c031481e0003c054849090780e9030041d601d00b40080d03943c0d20141103192a80c544480240f405595a882a54410061010300483c00154400c0007412200c8002034565043c040c2440d075400360b40d000408a9120314801048134003020303c450501300203400c0d5480100b6039802e0a80e002c41000782400c01064004080e2034018210803100324841e21a070200700383d190702940d030b60802c1085282240281003094005071003022456240d403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 586735647 1250 586734397 586734403
    0xf0703090b0f01212604050907050a18030b011205150c0405010f02010612020d050312090d0e0f1e0409020a1e050d08030726040f11190b0703030e 64
    0x4500081a1103200010061301000044041003d5003e8103d50f422040550b40c907000600d101c84e2980d1200400c50040400d01401411100500b0b0300034005180c03490141001000c0364024842440001d0400c800400060350895100d81980c6c0e0000403109a60700f8107207074401c01c940580b0156114480d50041c01810743c40d500343e0601941b100c0e540306690b141403000144c811704901140d64216031400004000c40e0350040344043c1050340c121500720742d100300c9041a41c81c60060311407440c20000c20601380b1007070340c90000b65000c1c80180f980700c0e41030701c20910b020480d86e00074505c00d064000340034140300c0c1501d14a00051315100c5800500c002241103851b0040388880f00030b0340002c83e10040805290404501e000c1c904d100801040b1108c0d048010300d5629105180000b03440e080921a47c0d500c51220039040302521a0b0414000d5403c28551505051810040345080010745403891500001101d60074042c481800c4051121a0029210310300b4503492210760086106600300b43d0703544403800c280c1300c0178 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 586736897 1250 586735647 586735651
    0x3030e06190206070f110c0d0503131d0c0909060d0201110a0303050108070b0406141c0e0d080c0f04120c080303010608070906020318010c032307050f030703080f0703090b 75
    0x1075000f440145403c000150514242034100c10601009100000f6040310010b0044180c0505a41c00d4000008502d410f510318010040b1500c40380310000c8001c507840c55000c01c10151a020344140d00915100c00110078400d03c07407008029002001c4100181250610840d0300404030f1040c07410a00c0745001019076030510754134103001c9000940f2040100012102000720301c001d80300d560b042c43d19151910001500120502060800b0742c0b201090701000d00c10301802d0301c5555119041c0070b00c00703500000000b45c1ca8050185002d00458607510225400003480d909442150307852102d518941400e1240703000e0300071004c400c11200d4515044003c07451000900c0a1402850180c43e02c0702c050900c447c015240d280140c00c040115441031007550740c0505112007140c11400c00b800d10146142480c1000c840d807428502c0c040c2c4c01c480703d490711400c00c0b42002c8003d04e21075000d042510380204241502c141c6034032607904040c00080909021811120540d14159002010342c01c00154040c2d0300d54400c40c0b00b03c02 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 586738147 1250 586736897 586736947
    0x80403031e06230405010f12030e03071d1324021603080906151525051b0607050601051c0c03050615011e0e0a0b030c030109060b0f030103030e06 64
    0x184a2903900307002030544420b011031a080f0307014017842d81440c1c503456201406202d030601400050f0f141400349405200c1003111940d011701074a160301e484203038402180864010b01c00c1c40d48501d0001400706402480104c203a9540301005030101c0071025041c4c48100c0384134620305582c81c2d003004086d0024000f205100750702c40c82916415a1850000191401c00100400f450b41461082151507030598a80740041d542d135000c1038146848000304844c1a1500d4495221070900c1c101903600c01c030a201c00000c4d1003041d850b516404038a0b0340c49030414009103001c1c107000104039910800051281345000002d01c0305010006180002182d4551298030b21801a5802660540c204105100254003c001c07d40b01c0c0e00d400f802c08108612009070360100d06401c500d00c4008101c406c03a28400caa03078601703903c04000d000c106102034880c01c0882c8000981e44c400e201d62619140b51282c000341340d882038070698030454000303003c035030560307213992801e03140b40c1c502c100002c2d0300150810a0880861045080c9488010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 586739397 1250 586738147 586738169
    0xa05042304060b0703051617031e0106020307050712020613231203160312020c03030115180911070b01170d0503011a09060403050303010e040c0e040201080403031e06 73
    0x3200028003046880740d400103040324004101c0000480e81080403910340342648004154884001d003005503a560590401019201000080c041c00c5104007520212481c1d00400008590340d9a5400366680d100307454008000d81c1040e0410007011900030212595540046c100030315051079807114883d60141038000c800c118072035041c1d0310010207104980381c240c0c0400713480f801c0340040c0a003403585d942d02502408001c00070103a81d424041603c10303244a12000c8403d0015900d40306840ca40607201c0d0030901804a005c810002e2040c00300384162110101104040325940d2124100110f1b80054520101c0c0e403800094100400400540c1614000e4020400c0005e10754440404c2c4045a0521340e024129104001c4240018411044001c440081056448181e80c0d40c608610001c1520350055500107071441c0008000002c0b1180c80138100d41c41240b0a00c01422807a4860300340c80b50400c000e840281c00140c8036030001c8c00203400303584030301505000c2c400c80b612490726965005081d1074180d0029103104c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 586740647 1250 586739397 586739459
    0x270c09060207090c0e040e1c0c0212060106090e090f0d0309020913020f1002010f06060e09011d0f0402041404060f06090506240c01140115021b01050a0504 68
    0x581c18084580034084188003031200318082d02c0010314405044d60214400c0c0d5540140700500c1000b080104807100d41421019a0b04504120261540110b100264012000e8a0200140e000b002c03401c90b05071040d540b2150b40c000d0030f000c008003141c40010f086c050140b052091440b5041c200308100035120406a07404a07201c540da105200c1c0d12400a02040c10b1b5155007042ca0b00103a840d20400101400152960310f40da8244560490140c0f018002e8172100a00c3c120012a01c00e5002e400321600c0141961044031690340c844230050750003100c40e145044c0c411204082800c2000d207070700803038219000802c040756040304008081c0e014201601e044455941d20356444ca0810f5440c01400d00501004004003c986084d03000320b10082c40350f110f170940713590300318440f01e180f11802170698a070b001da040002c001c01000240e8160300c0d01020302901030201c00c00e10351001400d10000c0c54400f12000c0c0303180c880d0103510440054406800c03581100e010712000344000700c3d10104103500c141106051005440e201 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 586741897 1250 586740647 586740659
    0x50f1006050306060d06180213050105011e020c090c12070314060a0e01030204020a050c07292106130e0a0c0909030c410606010e0109270c09 62
    0x110032540c880c1e8003d82020701003040d6655410422900300760401000318604106000154135000203601c001c1d0300c060543c121040044035640704038141c0d042a205c46010400c50321400d080302c4005502040144d01106010300f41382014488030b90013241e40d4035600e040908031026910782000894a8400181d40d584044498107400b002e41d47e00000b06548510403d030a00c3c01c20628041d050201038080c41c1c000669082440c4203904641c0b070f018016060f280c00d140c8a2030881d080d01050304104411542d05c4290000f0407030640103d0392045480d03240400c0501c0040080141124001c2c14981e0281040a29805002440c090070752402c100d600940b28142847c64904070b200b0142e000880a6480c20200c03a00182d0481642480141c00010f078080c00c428607848a800e4200b035005c405030003c10111040d000c141d0402c00d0304401c01100e8142c0c0e07190340e1040011101c20304407030203041c00109c5400703007003010240d40007811500c120084040c0d002c001c0c2010060702982c810701c03012400100040010806 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 586743147 1250 586741897 586741901
    0x7021606090b0d020309070b0418050106090b03070305060f030609010c0801091b1103130909140f0d0c030905040c0c02030f0c100f1b06020c120f0f070c03050f10 71
    0x3500e00c40c104503858900302019210780d40520107a4455090b400408116808410800d0070001c0c5103007080199030b6a15540642943c82d4001581c0c0381d03a50425001069445c0190188019608100051411340c0e0300e11404402500014122640210000c0d15040154070f092180ea03101d80c5165001003250800030300000d041b00416488040010301e0004a94070701c1d1000c000320000032806291196919030740000007411031107403414810360003d5030880000c3c21003030b9420001e40700f4010b51b0000f0480025001c599100c9004070300c4410503030048030b600c016090082c080c2000541c02803030101b11036529000400c04507024880c5a80200f2425081305c021441c3c20440c6145c840c0c1100003800303d51964001207084130282c00341d44814003e100c42c0a80c81c0622584000e039150b210b03c10050710440d200d0926000035400790070b29540e1b900541101c03104090030340007160b00d103950300503000e490501403800001c440d0f046034104440c041c680c6980040401c0040260111540c910005403602d050003c0305041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 586744397 1250 586743147 586743149
    0x5270102120c061515070303050105010912030e10050c060103050309030d0c050c0f062a010606050c0601030204150302060d0e1b03061603060f06031508070b030a02070807020405070216 81
    0x38071040181c0c01c500b20010420076005009004440c001d103c0b41e2001480842c4c0d4406071000707100340442d500c410b05500d604144c0c1218020388401c0e20072034641c03108601c5100740240160210340304080380388040c2007401c4c104100503101d03e407060130181c500c2c0d11982481001e91003079130158004904010a441c1c24001d56284c18500e0801815500107a655284c031035916415040c4242100140c2d1015a00c600007200c0d02c90b44024628140b02d50f0b680c1207415402800c4000040030341c648040401d03d140a14101c4d2915a003141c024100b50386142d08000c050312056201e4138001410030b00010058036500040d00503050001c90101ea03415080000d03514100303c25410b0069210a401e52824584021602036000f50003c0c0610391003024042c000d4003e021a5030003078010b40001000081c2096141c1d000c99111400316840304141d80d41c0d00c1d84c49075a0204d500801c8560340b001c201003203002c5503a60003080081d100e11991404c042440e0000340444408981c030002680014004a02c4440d80e240030304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 586745647 1250 586744397 586744423
    0x50709050c04150309020607120c140d050f180604030b04060e010b0a03060510081e01051014100c0501090b0a050901051504020c0106120311070905041109040305270102 74
    0x160a0503d481e003a00000742072014520245680d4113800800c2d5151241181d00c041e030418615401c50458100042015550700401d5a200304010a94072802e18007040c070007552441e50b074680d410989807010b50a441d521552144022181d0715400849907120301e00a080254092501c00c8114030742410040e045c0c424025a900c2180d14100070400b036a9982c01d0b140d8203681c1c200c00d001845039103203021114024076a40110349148111000081518100b803c909006e03c1c809009200f1500d0311243d014044841e40a5490381d164a24003032030301d60030220000da034100308902d00092501440e85503142103611564003900e0350015a000c000c90303402c150190796004206000200460b140158094404441070a6014880c1e81c00040c18142c0500c00d400c40780c00f0b010f5801c400d403d5a1414076010703000340e614030104407042c043c851001611409901c2410301c9941c01011040b140c8580a04018800754018021824003c0c207100d50703030030b03440041c0c03009840c03080201c00b44e2003102102001a14000b030002c1c2074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 586746897 1250 586745647 586745671
    0x4030503031308071b1a03060a0e100b03010609060e06090d1106040504050a0207060b120309061c05100807120c030f081902010501090b0901050d2d05070905 69
    0x104001000002160307401042c290110140d04003e107011070b001d202e80d001c00ba000b1180005807504903807105101804407000102840c0382c1c10200700d008038160200b12a21540b01d51b035003104111420982d40300aa0140240743c0c59070ba000d480c7e600d580f100d82c00a03003014001541c108814018180c0180360100090b40484040c0c1c10131205c82c001800f250f00c0010001c2490b0203080389118142c4a01c1c040d500500001031080c801840c24190030002501b083c04103444403420480f10f270303010703050680d551820741031280043d41c070f0106000b050096513400031071014519105200d01c18841340c0c1a10815020710021204910481d261144492078044079030010368040015490100c00103596450070000c8039807000c00c61010304500d0900e4016030117210309201044042c070f40c41740030300e640c103502403170580740b44078002c015410440080c03203c074050034003511350021140b6004101082c02420341d60740c00f18015046080f06013140d54082c21210404808030380552040d0f50a10030088a4010030b0f82c0300a40c4810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 586748147 1250 586746897 586746899
    0x804170c030f3d1512062a0503012c070809010e010b0102030414060d06030f140a120c061b0201021c09030c080703020703020411030610030e0d0e0315011401090b04 72
    0x1d00d0444882e003001c4003400f81d0381c0740ea00c030071603a41061442e0010310304a00c24407814030041c1040310260500720307501010305410440d00100b9843c03000d0f1103008941550b850a0450b801c140c601c400c0b000705010080c038000208000410541440b0b24054450740c41a50350126608041d60b070642900c0104550100c03590600100c00c0c02a64004151003c4840c891111081200c048000c500c191041d01e031103110309410480084103002d21a54120309503407107450140c0c4c13040d00e0813102540740d249107000204291001411005614801c85105c84c10034040c0500041d092440c02d20041140c042c0140480540d4000c100d6469110003200545401c0c00030714001d0240d00342c99a03005000d441014401007007810042410402c1c10310800c4003134040c60b0f000d40100304822a0100b00101600201c075864451404603d840d41414424054100415030402c0104010b5244050994a0b10808000c180d0184a8880c007240203022001c0014000c0200000d402001412000014402c070200e40080141180c1040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 586749397 1250 586748147 586748233
    0x50708090607200d03150608070206040803090c030d111e03030105040c140307050702040605011809020903030c120903010b03030703090b03330f0406030804170c030f 73
    0x90769035101401d0324011500030000d5404544038000c0208030b0001c0d1042e01c5081d140759405034000d10340b401d8143e500680c49a0b81e54000c480150003200c1600c01030704100007040020340c07104003968000394054143c4050750000408a0301d82032021082c00c00085403180d100d206861300744200341d0b150701800030400040d2038540d00310b65a40b106200d414003aa13a15504000484d01c02d0703151400c07801e000504107030703071307007003010b0024425000a54185d00c114170708000000c50b9030040031002090101c41804401c05483c040701403000303400c0010700c4e076007600080014591720001848400303001140d850b480ba4443d46410f042c142120104d6000d40c0c0203500400c2110046070b080403d600c2100c1c0308131492540c4c0d65490040580b202502130002c0030b90024280d0070100d000b02d4480901d04040c0640301107a40310744142c100819230f0244d10012b803403444204014015402c041c031800b4107914044080301c1e03ca1000c07101003880c00a8a2400d102143c01103c0d00ba030360300b00700c2c0350b0441c10000310103007152180c54122 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 586750647 1250 586749397 586749403
    0x50622020f06030403090305060903090a060801141302091305180a021503040507030206030903030f070306060507110301020f040b0d060b13060f020f01020a030f05130803010e040309030f030c050105070809 90
    0x54000c1d4880c81d008000074041500c102c01002c0a940d1003001e0780c9182c1060b18280740e0302e030003014a00388581005da0022643d20300c11401d0038100d8000e006003250070080c80381071203182c100694034841195001c0212980e40c8d00c94024070740c0d20403881e0000040525018440300000c108880ca03805964010318603110240e0340300702e190f244c074508441c0000d0741c3e41c64604c0c1081c5440023640c0001c0d040b800100420160b1400880a944a110850440110f070382d40c40c1003c804554660090f400802c406001c81c00224140e0786505480c804042c4c00103241201074030302281c16801603030066602d03e00014150031015000d004030340042419400d02d0b070030020f400e40c4004d0f10b030034140030f800c2c00c000d00103036108403492007000455000c0c1c8240000b155180000440200500450380482e90300303074100381c049441c082070749140b641e4664200d65a1400d5908100709030030319600141042d000c0050710070010001c14113090215442c18031a8031401a4070701580350090039100c00901e20010b006030300e01044100c04003c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 586751897 1250 586750647 586750669
    0x171603120c050403080f0702041404030201230a0c0203040e040501090201020d0302123705060f060412060b01113c0a02010311160f11060403152705062202 68
    0x1005e00c46e02e9241415031014140101d010103076103d41050350041080c0608840203000d43e000758001e025030040e1401d414982200c44030905000c0e00d0f4100011009121988001c00d40d00140c41030342d1400e42e440850078490603099506584607591030540404642e010003241445d007425003010360070400d5408014403042401000c0c8456291407100e200c004120b07514006880c94440e9124000383d00d010740441d030040c0300450303900c0e00802c48070000c0001c52070042d003560122294207511242e42d03c0f0540d5481b010b070100e882854148280c0320754059440301c0c24403c0e0911019285040783d00f4a141c0041c0041000c0640c0f401c81d00c60140301ca02d036195003000314a100c10780d44c080c01c3c0443c0003e407003000000d2900c581d0a88902080d0800f080c802017200c458503500d1218060b040103a6070300001c00820000784100c0c40028a0704884034154164407a46e0b8024420a04151414803060300007450306000d44c071840c1e10300700c0d0a500030108100543e440e2150b0300406050f40848458480540c0c2e012072200240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 586753147 1250 586751897 586751903
    0x7031b0207060c031103070f021306080a06021b07061214070c12140d2a0f030509071503020c0d02070510030911040608032106010912171603120c050403 67
    0x1003000b00f101414020703001111140403540803a5551451400c1180b0f0448114104a10075862000250780040c100d008000903124610041c200241065494038000c0d0f003d041e00000e5050022061140343c00c09004a05c0144400e45903a020a582d10604800f184c4602071441d044000305414040900d5000b6202210550301400c0c0204907614080e082d20095403500a580500300001225110354025420003c0a1580c0c1d4800395180d0004000c1004c00900c00744031a4001251b00c0151080310f40700c4c0c0c00c0740d0740155074801501c28407615007805806200070402000003190700000c403a04804010000306483c0f120070304c00b4048040c200130004000d81d880070500e0307040545403032130901404411080701000c05070080c01000400d660b0403480c4d403a40c100c3c0f804046400032070004030f6491400c036402d480c0f0926059690130112401c3c441c41ca000004005020780300c00030444107102c0194480c4004002c01e221084144030004061b241c01052885490803909001c0e041c0008092000c0d0484259001c4c0e0394 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 586754397 1250 586753147 586753157
    0x4060c06050a15090f06050306010b09040522020d0614040303020c2104230a1e120203071517070e13020c030307050c1f0501030317040308010303320307031b020706 72
    0xb0022170340400342029800c10350341030103900b000040010010b4020711000301c05039001d210076902e0000c40040096108044100030304c002100c90018608000c1030042c1920549000428522503c042502c00720f00711000c0740802d90016450070740003030400c00b801d42160702d40d00600403002171803e0245a80140e01c01d81c0d100c911000d068150290b500c50040c54035032006440c124030640d0703a0460000c02d0901c1d80c064000f07004a004007040d40503122000549141e00600184000380c82c4c840850416070324590309000f0420800c11a0750784805d42030b810f6004191540d50300b4142c10018081250380e2803841c01450546104201c171140e2028080166588800641001602e505400c070b8468107004409240c1005041c903102000b09142e4240e02441c1a03034000d94401d160b0b80001481201e40c2d40d030643d4003030046070560004100007442450600b409101e0000010403160030f8034040194a64611001c00f540e45000c410002296414820680e00e0f124004035040c1a002d50f22020303445040c58040c58003080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 586755647 1250 586754397 586754411
    0x11203140d0e03030a021305060f0a05030622090506014a01080124050117041509150b01022d03070b0a0c1e022a0604060c06050a1509 59
    0x22490703840300312555914800e0f0381d9030749000d83d500c0c0000d43c424459481e00a10702c0310042402c0c02c1c02401d071070b54543c07240c1455103000a076800170399850304014405a07006c459048a641240000c6501503085c050062000c0b076280c0540c81d000c2d0501d90140c10000c0d10b400440b8500c0d10680ca0411500c41c4c1c80070400c1c24501202c4001c20b0b0034520386020054403440140b0034000103c00e441548101540303c10340c3d01c0c460503081307900310681c038025140c45044d000035051007080d00a4034940c0300309034105104403040380340c2c00941e100443c07d540d8818401d503900100d90500032480007ea004244204a003480a03222a9510700d100c202100d11801d90421044072900960041c400d04104a40a46030891485da11a01d001d094440103466021038100014a56064090701d022882004504a00e041d8008d08000000041440d0402e030104c08006d2043c6880e505441c1e10391200c00040000e040b483c0da80c032030140c1d103070704055041c4c44000d8000b4401503d8130000c00031041110350250700307445000034082904 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 586756897 1250 586755647 586755667
    0x1090512030f0a0507050d05030403080412030e0f0312061804030815061303260307030b060f071b1703030612010f1a040c0e1003090206040906090203010e01120314 72
    0x15001d0b1440c000c010b45000100281d0150700311000d045183d00c0740084410065442c0802c94040c0001e035030040100b0340304c0010800241441c02000d0ae2021580340014010038281e80f60352424030269401501c1d50030014040304035041031801c550740610155910450f00729516602010108000d00107401c00100d000441d240960400107151803403070080c9825200c80fa00400c0320b05400c4588000c0b01e01407490404282503c1103036407069403103800007203280d0440c0c1c3c03034603c107801406020058035442417081000c800b021000c04080d18685002d43c030400003d42c0d2144d01c06401745055044100041140080341d410350700c0000852340c1c0820280c8460700001800f04c5210302500344c00c1404003119082030100707103500e252143c0c1c032a40c89900312030074008921516400c0d11480b50070703484207030055503200815000c1802600b000802500c050440c3d8a0207a98001e010200c030f15a4000c06c072a650000010440440312201071405800c00768860314043d0300568004e0400c03070707100030f84110f14400842ca440b04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 586758147 1250 586756897 586756903
    0xd030b030313030602091003090b040b1e040c0504060f0f050f12060406050a05060402070c1a19020708010c0e1003050405010b06040e0907060e0907120b152701090512 73
    0x1c1c4040b00030751a05542d4a030b03e804006508000602805a08181559011a48039002d42100f05030480d4060b141922291520340401c03100a085450f00403148140c060150400d005540c45903018080c01c2031014101020001034400c2c541c41045c0313800011506000314500300000c00202e46040710b03241c907420300e20070100c0d00340c001c1100d0542035802110304010900c1481c0e005a882400030400421280ea0380d54200405c03802210b20241c44000c82107030500903407001404a0002261800885042c810000c00e40f02c4840c400814840041e0803c0004001a0a09004040c8103503854100301115600c080040f421080320700424404050711a4046814440d080d03010359078180c4041c00031695552030b0350750031001000948600000f8410824001041480f8030140b0b4403c000003403000b80f540e12a081c0440b0031a0f0340502500b80c01c0e40d20005824a582c8107d100c034981c4c00c08003070b1b07103495002c0b104069044040c03500320340c1152044491040241ea03888012000ad0720000c49208d0640038071070003007074a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 586759397 1250 586758147 586758157
    0x702030304062d1701210209062e110106031a1015050417120306090403170f0604140606090d05010b0a0609081b0609040c11060709061d030d030b0303 66
    0x1990003c80e00200300342540310765500d05444104080c0700107a40d85030000060350040082008a681813143d034600140b5080e400d80e42c0201e0001e0036402d505010301d89014032001c458140d010b25440f0603990304180c58005011800300c01d000c42c008c005031813442d20380215910f0ba1247d0007003200c201000280e072122003100000090078114052400042c40c200c40a013040d402400ac5429502410b603024080100005441c2030241524854a0135501c80c0ca00b44081258050006c40601c000c07611400524030820b802c86e803081411a038060040c0c1008130078802124100c070440300b9602070340c2c0100055901d07443c1c1143c04075007050b0303003040802e42d5508126004140d200d00086e030110154100244c0190300481f00d02c1030300c0240050368400d0300b81e104201200542080090780108007030010004503c1e09a001031410641030420744d001000e034004003810f1a4044400380c0200300d1004c130600070746034448c40915148400e21034140741c600f40b400c0020f503646403047c5500109500c0d07218141c0303184c6003401521 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 586760647 1250 586759397 586759457
    0x30f06040903050d0f02040f0503030903121e0a0f03050a05090601170a1e1109090d050d0204090905010e010f1503080f0910020a0201030f02092112210903070203030406 74
    0x101c0f0503180600171019601510501200409500e4003107603920300881187d2096138020001c1101c1d440c01e01c6603008603001807503c5402a002d9030400900c100c10440140703036800ea25640d090030146c1d800d01c00b5088903005004010b030703c0c8c5408100300034800000303001810360324000c56a400310810004040d19011710303808001c10310f40e400c600c403150b035441c0d04020f241c4040c03041b144942c00241010a001c0045011209400320750300607a00511814003540007841a10506600985090744554250b01034884140080350260f55420044114541c2807041d404000c41061051103100da10200840c0c1005d45c0380800380c003a100015031801c00303068090480d410800040d140b0301c000082c410000e51544921101a030210741440c0040c20084010310840700c031204010646070141c852004920032904480304600d042d44140440c2625800c40200a0261490142009000103000b48044030f003d40d4041c100541660080c0b20000050364044142c0e816110685400d0310040c82c49002004003080d0340d0911 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 586761897 1250 586760647 586760651
    0x90f040e01021201052404060807020a0b0f1b03060d020f1801030c0e0702070b070f0201110601170f07050612220c03030e120715020709060f0812030f06040903050d 72
    0xe021098034021449048840c201c17800d05501c40803a04950f46d0000000303208407512003c000074007170700c2d000754006a0801c4c19841141e00943d01907035400b00d100801d03502106642c0040b020040b400c2945054030442141e4140c1860950601c1408111103101c403010092085110b2100c43c072454581a0111549080c0c28078100110359480c00c04242a0400e40a04c0040314494000074040c07a000080400481d00740d00c03980c611b4402a40c5030100d0482d07822004a0400ca40c0301218000080204419030203070403011016420207101001c21441c1c011039640c030b80039540102c0010009540c46009940c5043c3e01c07803030740b25a6556800d0310310030b0020401c0040780807004041c025001b4001402100c0f003d482c403030b8469a20400b152800c01403500d20100c501c0c5543e500c200d00c1444041c1a40c001480b8079072060045407007950f112600f44082d070350b103a0410859507007890300400000604100751210902d50103645031079400c01c00c1c0710321000600140b80c14000e5494000040400d80b00d80100c0d48600c484640c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 586763147 1250 586761897 586761907
    0x10050702030616142119060b360420030c0a0e0306060a170304050a14010f0c0b0402060a0e091501020105160512150d08070501060b0f090f040e0102 65
    0x1100300000454024003002415481d143d020b003a10b44c008540b81d0124070200a0741c4110b40301c00300142c4d584010704c00610328422131802d807542695405400c0140a144200c50b03103e4000f038081d0b049420750034024107050700103800340c4012000a00182440c82030103480101d6801c1307a2070441c2000980e150030400803c9070000400080d0309015015021882199559100e400b011204050780c859041e101d06901882d140d108201e4035083c8412120b82a00500a880c1041d80e01c0c4009003d41074590b11500304151300d03581e400d40c1580c1c4819202c035050214142011800307401d40390a4081100180002d00504001410290f0240075540b0b503191142c00404000441ca0811003020310000e00442e043e0140d801c180100b0703086a000d5000c232500c80c015589a41c1001c82e5680d80080e1030b0000780000d1100038081000c06515140c8c00c0c2007010290248844582e550640e16000342150305039403144140100034410b8902402e4442c02b2980324000171507a0750007881e581d0300006d0003003802c002c2e0500c0710b41c80010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 586764397 1250 586763147 586763161
    0x206040311090a06081b0307051905151c0b0a15031e0b0f042a09060f08041106070c091a0901080f150c0403120e03060a1a100507020306 60
    0x454021001c4103440040d01c40d12614a01c506a074400e0143c0c1c0302641201a810405075940743e600b2210500080c121a00f031603485000c00c284001249690314240c4441000384040c6c105590028210b8402d292114030740b016502690240d034182c41c41c584202038503402c190715150b5405c0d10302c2014041d808502001c0b044031400241c02000003505003c0c0d09a0f61501008a01c11507100d0400401c4001e05000c0c002c0c1046000c100080000181b00c50940303082000d0660440c0300500807401e61007aa0322000d5500e0309100015000c4e2000500c840f040090342030800c400240140c10aa4141c0002c1e9489511918149002030240b9850b4106414041c5080c02c0e88504a00e1048100104041600d0380e460703c1e600c03800800e449814000440e0313210b40c0610051040c44161026055018255010380760800e6120b03a201e8a081c45038410070400640207454035079107803030180111074100c03000300c00c2002260b5201c501900c086201003c9280b054040c10010260640510110341b001039006081d0f07242d80c0f620354 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 586765647 1250 586764397 586764413
    0x9110910180e0708190903050a030f0e0307030201021201080706050a08070318030203090f0603010e040b0402181905070c0507031101020a080c100b06030c030f0a0f02280504061202070f02060403 85
    0x2602902122441280c40f03504144134441e05182c0ca815035540c03031900d27041c884140c1c00b4003030701e0041c01003556540810102060040c000740526a21a034005640d070302c0c45411070110f04006070440c00180d0464035041000b1034124044903814130450030000d156580e1000c06a0007806861116482c0240c0040400105940031004100c03800c0100c403c1c6040d241a081444142d0000f405101003c00e4800b000c070f8041004242c0a42d03101d84024a0030701501240b10038446290401e5840049a42c660045001e04899a019156111a240c43c00401811940c0c513165640c00c09440007820344244903400c005241d1080c01040c0055030000540f42d941c0c00204c050a55503682201e07104090fa2900046005038544281100d01400745c0c980104c1c10340e10340b0350a082c261a40602104161b03550784400c0800c410050000e000e04a6140c000c061003c0c0d0000d1400184e00340c607210070410464208800e100c0c1c1d9030011001c0f003091a035241c006840d84514540800c40c90f40c511406588200046400801c101c450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 586766897 1250 586765647 586765651
    0xa0302031e100b0901050409290103061103041a07091e150503331315212612010906050a0f0b2208030409110910180e0708 54
    0x10000700c0e9911a904605581100c0340c112500307130300c602403c0041043c2d1525412a2400e5802640c01300c400b5926940c1152004803262814103280307206c42d0041041c0072417440381000c12000c2181c52442c514050740c0740c2c200f80020264090301c980c10180890609807203802440c02810200040450780344080c0020283d0f9046841000c00c44610301e0380d00401e4a02c90010b40e4056589004001c803030005c03106d0a00002d034030000902c40c0e0090039004070110340d0b80308080b80309945140b001c0020300100500b041c4034940040c0d007140e10001400c0910700300e4070110300c020490681d000a000c030940340742016001e0f5840e0380742c00304002400012a24405092100324a641212400d1100b002200d90341c20520000603040c1c441c081003d03401400401000d8a114010310a40801811000004406651464041c1403d8006458a50010505000a814a1280300c02010b0742c14200c5040000307010005484100ca103a0384000c0220307925503642c0d001c81c03004104018101d0004410319600e0300b444010a00c40741 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 586768147 1250 586766897 586766953
    0x1a03100209040612021c1e120210050408030c0a0e091006110706020307170702030f03030a0b040e030306010f02030c0105070e0f0d0b15030c090a0b091602030a0309020a030203 77
    0x5010f100040c0350000921345014280d000e000740c814680f070100c03003050103c90000700396000041c024018581c03c2c02c03107240e03106052090314031000c0450134103002842c21a003540d80004d81c0c1d1070710b402c0c0408617100406486d80304821301c0310340d0394a20140f402140c1031843c60010981103028103040c021081c0d16201418203880345952020700281004034607598a031554400d01015030000c00014001c0361040d40600307260310304543e540d0701c0c0401b6a404645484140d039022010742c0c0001c000d020306002d0702e002d00c1c1100ca40444081c403800300c801c02d02940342d100241c505030501c0807141402004900074000d031007041c1c2031000204502c2c50401c0d00079000c10314400c080c911580100309009018505032100c000010340111504001e5500e401140030b8141000c1112a8184100d04080c5e0040d6101da68040c450340c640300d000700703e0368409014014200c80107814138091071400007a01000950002c01c1d02c03074007812480c0100c0d4540450000c2000001c903500701940600440e1041c8044000800a80f8030b4141 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 586769397 1250 586768147 586768151
    0x30807110108010e0a0504020a050909010905070602030f04050f0a0b030c0c151608090f1b0a0501090e041707060905010203061002070f03241812030612061a0310020904 74
    0x544840111001d20b400d000346411825280e0110f0030306003056015039407207440907002002039510f40000030001c80703003210909400d80d1102a52420400107021701c1c40101500d00096052103080340351301000c5d004500405015094008588000c4d550300c190b080003c149400c140ba03504c0c1800e4890b10031541c407402c58140e451040d07140d080340780f83c880c140551050b4042524050241c103521000c441440000e0a000f030548141100d6101a502c2800340d9105000165889c1c05001080c40c140007141d00c0d2039100701d0520007520302c00c000103200c240c5143d0307000b0760080c034081408604048044403801070400140c505490a80c000e0100081540158000c4404442c164591011028200d0742c4402900030b040300c2d0301610a0420000c0e82c2c07003000c04110b44042089061906604003074200312a03a5500d00301e900c88030292032909001704070a01c000740c0d1314903107810302c026400d1850b03120304407604101c0108180d5449032030030304c0d20900c002c802400e40070003826100c19101010028020350000803107035100314 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 586770647 1250 586769397 586769423
    0x302150603070f0905090718060801051b03070f0915080121050d2114040c240e040b1002030301180b0d020103110408010603150e1501030215070c030807 67
    0x110307000030380d00b049030040c0400c241002c1c00c2402d50400390074041d24541061041032808107a9410f550740c450400040940d00081e03240c50929000d003910703009808840b03640240300030700b5608070000c8200c82d404003c60a200e002d12000181c112140250f90b40700102110341210440319066001900364120340d1141c80b002e14100040c9805a00608000001081f41e404440c004801e40d0044001804440c40410b403440d00c22403191410701941e00e03014150b060320344800200820000007a01200c06820310320304e241e06130304e800180b03031641c800c107481818248140c00c4060440d07940d480e000300d5002c04001d800340d0801714284001035a40c0d00280542130001d10402200c000601f0544031300a4030000c0208460011618ae80043d00113041c00700100d04003423010000418140824040c460066220390669000d481e206541e410440d8994021100d40d508a40f440741c0000300c42183d06815650116206007107824034440c603900c0c0d80714110000380b1100742c041c000000c1c0400f18014020240c0204484043e407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 586771897 1250 586770647 586770649
    0x10305150105060c0c150d020c062d0f04140a120201184d0f01050a0c02010e01091a190201140103140a150c1211040611010b0d03021506 60
    0x613008a4202241c168844000e616440c5803083c080719694000100e0107141140000c0068160717030110010f1200c80d800f600c14131a1142d884070000310188900d80e440440c0c18400e250003481c1103c00340041c0c402c04036110200c0c0601041a42000e5440900c2040b5200182075240100b003900e041136400d4055460301e104220700740c00d100b0010b0302460340301c44003011605500c1c0349441c8a6003128044440300c00320140781098000c0300701400310140389240104030034100e070204000d441c1024440c01c41c10030400784116001a80c0200200c4101c590908250302c5020a22004030342c0c1103d254032810b2a600c5842c4a140c02007118402003c032203241e5810a9082c1c80001c034241e080e03d500100c403118981c04d030744c0108041b421486040c1c00e522280c42c2941c3c80a0328549076503540c2d202c6200351004560340e81c0c0340014020341040a115001201c60300030320030702c208400d40c5011405684201004d1003c00080c01e503503c40d0039449903d284000904d80720b0101c3d182c0c20025036405642c41d810f44040107401c0070402c0c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 586773147 1250 586771897 586771909
    0xf121e0304060207091e0e030301080c0613030b040f0803070908060a0c051e0c0102040b091c02032802031905070b03090d030902060d0501090e01060b0304020312130e010305150105 79
    0x3607a18940090002d1071505d9240001010900c0c0c1c1224854034600719101d4060b9540150182c44403070724021a160b5040c2010a410f002800d04131a01c80c42042041001402c0c00b00401c07401c980d000701000c4100c3c0c4e503509200c07440222142004241d135000100700265150029142801d0b0382060080300c00c1c0e9a10300f140042201c50703171040c00b00810390501900e40700320b40e805070510011214006544c20804107090707080c2641c0081d0044401440003081066460800660003c4680382e0042c141303030103035125000b090701c42c02e2400000c003c000160001d07003a10313000c2c040d80000056001e0704484030342031180c4006002108a000860b40c43c01459000076441c5420007d480c000c1880c000a88070020070010142d000340803060317040b600880c3c18000c403c400c240318030a07a03000706200807010810008140740b280c00c48c0e089400c200c144610510503c0056100000c00080b0011580700440d6508218180c07403030000c010b58008110344010340004400c219004c61404044000e8170428049640c80f10300b0814 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 586774397 1250 586773147 586773149
    0x3060602011109040b220b2719020403020a12060e030a14030a090501050a241802130b04080c10090608040f1b12110a03031d0f121e0304 60
    0xd0a54024000c2c54000d2405900c034040c601d038020075103c4601d1b500c10b801d54141058a00784410140e54240ca00c0c205d060003000c05231258000c01d0100c408020100d1141030799800504603c0d800d0b0350b030499048040110b94100c80155030014225290280d481c1c02c0f00d403242895142c12900c490800c0c0050b00b13403a40c00400da440030740c8a0384815101100a58040140e908014140d2040303c3e110007400001c21400c2c800c0700d00414104001052001c3d14150f03c0e10f80c12061442d031000d8481003802001540d185048203171019a11071400341c0c0d11120980c0c0040100016001525034440014001542003000140300c84100004d5650040c003c802c00c030240c85041040c4111004130303821100260016005460900060340705010440310702c0c610701000c0006505580103a02c2e1441503924a00502450304200e10020404a41a07a138a5040d80da0042c03003461851600b081000031004100315540d06d0131900c044582015003640b403400000e00c6401c2d5220100c1036420000764140111108011001c0200c1d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 586775647 1250 586774397 586774421
    0x40f020705160b040f0b031b18090c0414220c0c030e0303120f0a15060c0302060a020405030a031d19150201050708130f08030907030308072a0f0213020a0306060201 72
    0x5e04c031903e41220011990300c0180b160f18900b4000202d404022200e201900c80d005602c126038403c80c0e9168140045c0b68405000c0c10b111500a0004111841c014192014140c00a81d41e4203a1292011564001e8400f000408180344e4103003504220303980d42c0411001603403070107507450f4041246250181a12031160192440d44121104e00142c84003010411007034001f61031980014040148030109a0104410b40000001621584203074080c164100403071500504040b408604c1d00c1d2404002070359440f02c001c0c0043c2030182c0c480440c0b40695000c04110740d2203070702524481015882032941c00c9041c2d40ca000d51140d452082c6d4200054500c14441c1d94480c01c099250140a91601580001d1208003001c084660aa4690340ca40028000d04040e42c0242c69074001030010500318500500001e030010002401c00800013074040540712030001e001012104080c65000320b0242c1e0070920740c500d00030040030307400c282d5003901301100c080942d0040420014555040017aa500c03001c04900341d4030288082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 586776897 1250 586775647 586775669
    0x6080103061d0706020c01020c011d0907050d0e0c01110604030e060f0708040e1006020a0312110f0a0906081302060306042c151302010f0e040f020705160b04 69
    0x50000400a501160005001041e41c50070700106642e01c03403420b48580c000c80e0040e0000b414603620355804105401c00030000742000d8a078068543d402181c2c3d144c0c4002c90a00c190782c0d44011500703642c00380048403c1010050002d00c400108000c6c01542c480d02c0104860000d180c95400c11203a00c07001c02e0b0039002e1039050b561050210003000401080d60404445081004410001c040000d4544001403005201c44072000d0000d01d0305541540070b429643e0301403015900103003c6900043d07030003900b54012034001c0360300091100440034220341c14010500327003081031400001ea01c0d41e641d40140e04c0382c6c01c40d68581e503005010340d1034000306c15100c95419802034201105101050751031038240c0050044560300442d9015548031454010406510788000c0000c2c0c2d04802d03070303d46400c0e00389168180c2c80b074034100e82c3d003a84216540c0002d1054001090700010030031004500c01145c0d0700c0307070810500207041070b4055403030344a1810b180c0d032514040d11100c19002c521001c001011000c00d02034808944502c012 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 586778147 1250 586776897 586776899
    0x606020c090c040b07051e010e07150315080307020a15050706020c0a050703141002070803040609060e1c030b0a060203070f0317010e061806030c0f120a1a0a0204060801 74
    0x10700861003000742551640410a1002040311150040601146409000282442001103440464500820079404070590415001c400220000034020b8200c4401d00d00490304021300071011002061040116081080191000290030000002810125001702c8103028465514a2214501140e5009920121344203002100124000b03502400b076102020047d94507810250b594142442c00a800c11606141a000c010514501c200510751040710403050841c5080e03d0b40c1c40d07418090100500003403015842d54110380c200030264001c0722101f950340d8100c1d6400e2000ea903a01d849022007900d29000289803100c80c0103a45421035140040b18101d40140d40ba00220b03865000a141c0030303081c02e5083c031940b10542c5040c0705103584250f000b481000b00300c585034104401000101c44040b2001e100588085040c48041d0b078011880c1c6010780d4044403081d20354484000880c0c80b44448180114503805040c0c4954248080800091080c154880d1051540c1e81c40100b200200d000e0b078003a010009901c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 586779397 1250 586778147 586778149
    0x902040b01031406010e040e0111130f0b0301030f140a0503030915040b0c07140303070f090b070309090c110a05030a0801051c03030f020412060f180203060411010c0c0e010f090606020c 81
    0x46814051b60b40030b80049003012002c4903a0742982c14000604581f07090010744040d0905805200384060190002d908218510340b2120440900060201030302d8141540c1c01601000141c1c0e1100200d10540419505068020706005440760011107443e0414050254440c0c4aaa02c01c0e080700d1140d5800100070030725461750204041d10790400304086032000b083c040c16406480c801c1011350310480181d0344520a03030300c100d0780050843c0c1c11039001c443e03090800d000d0400001d03080754022060f6811a600040c020f080380030105c4000c1c081a002050364003403100c4060910601000420346280161224000c0382d90341c005004040c040340b02541c8200b015a00400d00103442600321481500c2d060700e0160801d071b01c1d100b00079400a00b02c441111182e41e51650f00e4004015809600858404201c80a101401c00d4003c0398580c0d600034002094001c01c840401d04a03805580004c105036000015414415110720b41011444070a02680040688001000412000300e000c0d00c010f490130365000c2c022456840b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 586780647 1250 586779397 586779407
    0x30c0b0a1706032a1e1c0602090a0603020403020a080a0b04110102070f0b0319051005040b04060909051005060f10030b0a1a0405130c0903080703120f0902040b0103140601 75
    0x180040e5071502401e041042d803244861130708550b0080d9020380303420385481402000350090301c9442e801d00d04070080c60020840c0e0344150321800c070031185d0050b09038416114507000c0000d104214506500403000300c3e012405940c154094000d5901c04d0300c0d003821413501c884055640324080c201c010132958025000400042200c1404000c094042c011503080702d07203902e200c0e0910a040e40014072940000302c204031a41020300c0034444016900341d010001c5091031003000b0801112409041e001d40d8581440d81d043c2d454a0340300d00c0041000c42400c1141994501e8404d0700e90515800c070003080d0781010086406071030001400c030300b0750100801c084410100b07058150b001d40701c0c0601c1c1503403040d40030400142ea41d000d84058808030394a0b4001587d070b142050208406072010f100703416106450b18051103c2a41c000074108162904208415203400c49882c0407103440301c071500500e14003402c100b003a44100c07490742c102c1c1c00d006108480c10300c40a481e00004400b03d4008001e480b180b01c0c0c82e040410400c2d4094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 586781897 1250 586780647 586780651
    0x19060b2a280c0f09091a01050f150f07110112110304060b060c0111040f08030f0403060203180703050d0f1704080927010815040302030a1404081501030c0b0a17 70
    0x742161040740e60348030001c003142c01080d40409404ca49440442d0b0030411003000c8010703100aa4010159294101008112120b0407240400d0280c54038401c0d04080a494006840300059480661641c603901c51400c810b14050524070b0a01058441c84c0c440035010710b41c02100c040102d1600528110b9aa584826014060240003a81c00042c100905107079814203006418080c3c0f0b640d103c996480d8039140d03417051001c0d090b0f800340c1c085400a0020f288200b000f01c0488081b260411405a141e495450b5094405440102d1140061045c400004200040880c803c101c52181d921030309a60102c482c0296100100e084088100003809000607000542078000703060401000b4144059164a00d854604480004030902050701c1d02240100f0000c00304101100c00108440104403641c03c03c0d0380c0c00395890154420990034400300f00103640e04031460f00141c2d401081c41c0000c0740c010a1b00b221284c2580c100a02080d40d031801c1014020511501180460700a107050380e42c2d45280c0b6500d00c51041c818480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 586783147 1250 586781897 586781903
    0x1b070602041805100b0c060408030414161a0304051f0f02070b06040c020c06030a1a06070809010e03030f0a1206050411250b19060b2a28 60
    0x4203000100b512000030403a9284120076002c001018200118501502c20b850307440000c0d80c11003008410f01c0c9180100f801c030b8010758001d0301c0070b8503610340e03141c00c41c00441d21964104841c45000c01d54000d07424041d01900c03c540707811051211002c90699010090305c821070700540305501410600212021880840c90310040c001400154000b060880c00280d0380101c40a6880848070411300c0310b0f510309032144030ba0404050000300811030029010483c1800000c00302100340c1e541720310940c020002c0e401c000400b000c00820040d0b1fa040c0e549441469500b100052a001541400c140061410008101c038074008403074005904200b00380c0c0d41200c26a102404018030583c0f0ba00d0300103440c0c0c94030300422160309035a01b01281c031485000311610320f00b0422503c0844070b03d405015080800c4002c01d256800004440b510401c8680c4208c19101811045d071025002d00000501c425049144640001d0102c4115003a40d02580300300d0004d550f5585444480031155452207080202c2110088400380c00500c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 586784397 1250 586783147 586783151
    0xe090702010b040f0b0a120f080f070206030a050106112d010608100b240712110d0f1112030109050907031a04020906040c080114010c06051501020d081b0706 69
    0x5040004030f0151095500410075a50710360821000503e804c414003c0035000d000000b640a10140d100c11703011003418100540110f500103608a60030300480c00301d5030b0150f0082c044548d02e0404d02c000c10018038092190400240302c94064020707038440850b0000328075211020f80c1441804220705155003045411402c60107640e01d0100140d010010301004c40d2501c40d0060004140c03c00405110940b220001c079410040c1d10851058143c245060984180c15041000004154000d03030080d508a220f51180c07003247c0c0329042c00c3e134446079072080407080d801c0c0003a9944e00310041000401560390042c0842c805000c00d0600040c00142410743c000c65004000100310b405907503680d1a01030f200101c2c3d0b94403003101100201088154100041c0b1560450b10540d01004440c81800d4003c00e03604040c02482084000150400f00c0350b0700c65980d88440035007240701002a401c1100c03130414440700c4202d031240540242d40900020780d00481016202c0c0303010b0032030030400c1e980070a8800401e5015100440710a6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 586785647 1250 586784397 586784411
    0xf0f0315070e010f02030414011718070b0906040302042307050c01150b2a030c03120c03010f060c0819080a27060b030102040302101e08070e09070201 66
    0x1a408000465100215041a540906020000405121110892905000c1048102d03c16190700004480440f050f00501c2c4804148050048610065640c1140e8001c40c2160500c041d2041800e6958a001000300440f594030796200000031080c01140304d4280c0c04402403008002600381600030007403a0031500708000800c1205000b20020304010355079000054000304a001403200b0034441c0000d440d094419a070445454900050707514440d60340c1094a400340c1d600502d801c83c038181e00040e0040c2032001640c3d00c0b1890645001c0d680d8100c0300b0310840a401d64004902c07428540d000300c80c10f0f144000b03841c44002e42007410540e00d405110000b19520a020010454040b100c1403055000c20040e03070714084a1b04000c3c00308000e441c2d0b0900d0b45142203145894100d601071804a0320144941d22000120710036400c240003e00a0107103034400381d04000c03042640c2131100d6102c44010002c030700100030720f10782444881e4101c601c2c0e00c0442c0c07800f000c12403582c03151b070301c80c03030300b0728495074000e00a05c0046800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 586786897 1250 586785647 586785649
    0x2040b030a080c0d0914130c03090206181e090609070e10030b0108090f06060f03071d0403110a0302150a150803040602012009012604032102070f020f0f 67
    0x95110a940f40e89a4101e2031220a44552003d000c80041c6404081d4000480f603c500180d00105040e0000701850707603a1100340d500c40d010385c1000f41c416800030401500d820b40c0300740160702c403640c0d000c21070310442030400010901800c01b2801074040d06d01801d2429569109410301c0006600506120140302e00c03852110303260368030f02c1e406801d0401d03541c2e0040345e115021030015028140c05804a01e00350010002c2e2084404001b0310b266100d0012101c02d4a00c1c546800407908019042d0031a9010000c0c110300c0c5002c200074070099034003540c440c0c0d07a00c1c414420440e400d641c542800b803d0040058001c0c0e40084244070000414035000300407030100007402d07a0100e01e008848840356200c24a50781011404101d11502803182d000d58000b0555100480c4080c514550114840c0125107414030000025179007006070041426500030440813207900990801c0d007005070032a601c0c03113071640c5040c0846140500b0181c084c001e95400c0b540c44031140c5c410240540c00c01918152062070a900011207925900c0c003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 586788147 1250 586786897 586786913
    0x9060e01021c0e03070b04141309020310110903070e01060f0f0c0b0604020d023114060a02031c06090f0615140d1103090d0207050d060207050102091e280302040b030a 73
    0x23401d90000c0791510744440403e0100d1405038040c410a00c6150080c85400742e10041035024004200c0c9400141e002d00003c1510f1140c010805450340610405001003080070500302040d050310394545481c00c80350300b0a00211207501000c8146030000724074032465000548a1426140c22800081025040c4a480c00482c2c040b60001c203540d504a5840c50410180310301d201612455014040c010400d90600380340d1110404e80441d4026070041100291041c0c0760b038828000c2c0d40c16490303040d507c900d090310205800300c0134020300c1c020403150520780142d1050718001d03403140408030303002d1719070500c60455200800d0340c0d0094504e5014070a098208001d6900b80c0381d500c14010485080c0d48903a84a040c401620b500e41003945a4400640d070016000344800e94a00021004d01d40c0d01c070001595070001481c110340640118041c5c6600540b9000800c0c0004aa80041041490301520328105021008529550030040d0601c2c03c82d5500b036055050015040640000b8191080a421105441495036840d44 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 586789397 1250 586788147 586788149
    0x307020a1a0a0518151905011212090e07050a02070503030c0102070b060604031e030c1e14061b071106070c0f141008090a0f0309060e01021c0e03070b04 67
    0x480d0440c0881004042e00e080d200f40740d0450660800400c24040500384250354240d62590186100c89840004044c241ca400b50001c00d5616003a05102d256507840b018588565091021501d90080d204919034013881504907408480140003650110f80300d00c401540c1540c48150450114014508d001c180303030300d0800081490304c080d1000182e903418541081c10000038003500007031103040204802c20218800304407809049a181901c10040070f220302d0309480110748010300410b0380c0c00704065009402040d8200a800c107000d0101ca04a4502003610551a40d100b16034007044202005840c6c84c1c00c0c100c40780900000c0384911851215541c410000521a80012404403803c0d000300c001400302280e40781c544002000c4044602103d4410030b00001e10910240d1020030070484c200380056400c410420912200c1d5402c400050301904d460705000740400514050310011422003480c01805500c006242c4041c1040c4420501100103030b0842142c0700322003049050fa141c4104200420078080000081c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 586790647 1250 586789397 586789433
    0x50126010614070b0708180703050703060525020604030e0f03070303080615040f03020301180f020d06060314011b090e0f040c1502010f0b0f310e010b1f0f050307020a 73
    0x1b151921418441c06015441c40c0d501098100580800c00100700290032400e403588040301141c5656910245410329101215802900c1000700b1008180e580214a05005900075a1042e442041e41d009004000b107900d044540c156204030810000b2900c24445c464000380010320041c07906641d000c0b51081500580c00400e0304016500307007041145401d201c0e5000c5030400f00b00b051b42410554881b944c180f01480d40203070046901c5190300b0104030b1180d101c0e1003d10f80c0003032919000707a0703009501380c000c0800c2d118292180300f10744d4080240c036000d00c103500300711002c0e012142c950b40c2d6120103042d030a00002d0710480b849400340e4404190044e502c858019450000d40c00020059426010082614401441107010b82000ca040e40c40e107890714101d540b1506444170000e0441811862240f6500d400110206400c030324040300b1034041fa0707040d0448030040390221801d1324144661405244000c000d180850701003200e001c00c1076075240c010405036904c030000340159141d01c2020f807500d80003842c02d04542 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 586791897 1250 586790647 586790657
    0xc0303021308150105030a030801090906092004060b0414060702030f0a080c06011e06030b010c0c120506010f06050910140d05071707090b070206090a030c050126010614070b07 77
    0xf041d030121000309840c014401207000300482d1081e03481c041c280c980706010b10301800391989201014805150002c43c11641e02c10710680400c25042c01d4250311445078035041d03100d2400c06d0300010b02c48110f8410382d01035403103d03100e580303440100740d081060070790022004903010f004200c0361649038001130054901c114040d0b43e03540c0d43d035498218254240700c0142c102c10081c10620a130b10b2020695031104000350340071420001a038003030950041c0d4040110440051a012144102040c0c8801200c00054028400d00441c1d1850b62201c00d0034222a10705d000e0000081c8081c09203924624280c0c0411041c110360781440c4100c001c00c104d0702da0043d80020180a900e9885005104075180e22142a100c4104a2030101e0642c1c20301c80c0004040c0d4156204110b0a5080420800f06542d1050201ca208141c01456600792541c1e03882d208400c0140e07842405e000c5100c03c594403c4542110481420700b042c28000301030503a00b8070701b05031600b581c0f0141d00c0b0700b01c24007840100001062424514010310107900c074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 586793147 1250 586791897 586791913
    0x40f0210020f190501141005030c0d0f02010c0f063909031b050301020c0106060201180c030f0f120309260f0315030d09030b06090906070c0303021308 66
    0x50104809000880340110750002c408464030100114503c4024082c0320807031610104a401c000380901480e5480c8028294850b06000c55150750b4020301d0200d0b05d09506403515210503e04200744008a84000740071240980a00401503205001c8040500c1c07040b0038120813103126880d540112800104e8001d2034940c8038104031804608002c14101303078442c070783e00540001202d940041107102c561000600b10310329901c1e0078a4401421410070041c04016000f10740303503d035511000c0c1c044d009520442015500e00001c0c18074070034030480252043c942010802402a00d107954407030115090f44c509a0b075507221f0300800c00c009110004891020302d00e503540400c2c594001d0a00b1592030a0040b249a6241d01004808070f00419007020340c0e540c115208045902d0307607200e503c0b0020700d0107005402503042c014004001d0105402a0400043c2c0e4001c0901040c07503946c45051143d1103405850a8901340d01140000309000e210f042500a00d41c400c0c50094149000903000848094541d084880607801040e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 586794397 1250 586793147 586793149
    0x6080f0609090d0c080415120c030b091602120a03020c0c120a030c0f0c060203030907120206180102010908030a0606080f060105091c0503030a0c1d090c0a030b0603040f02 75
    0x81a08100304403803107245414448442ea82d074216441c500320a2012038221241400f076140140d0b0000c20003a4104a44661601c00c01000c19241541c0380d40000e160640003020b0034400e00c12410341c800040c1c00c3d00100d440744c00c416200e40d140a0b4000d811846010340c08424042004013030102a21161405031702c488000311468181065210340c68000c0c680f110038200c40f124001307948480b407900342c1410302d01d00c1c2441c1420108a103001001805d0b48596020001c0c072145d00000944c40f0340300d038034262407489858003107410f10304240701340c06903119405000041c2180c0c190b25501003400c205000028201d0101c1c0c0d9140c0e615002100c074821495030301c4c5d00822000e03070800352169102400d061800c0342c505e04031001a01c1c0740074444006000320811070001000b503441c1d10045d418603400074101c0f45c0b02c0c90b00265a1010b8081c0c51400400524520480c084200c44840b04001d03c140040ca08005a6a2005d8188081e040b5201c20410107845666522032a11210025801580aa4011b04011200340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 586795647 1250 586794397 586794421
    0x9060f0215070e0f1806010207060e0102030301090519050a020d060e190902130911010f020309031506030a0c0f0602070509011202041a060a27080c0405090f070608 72
    0x5421401550044420000d91140c00c0c0c1d10a40e12200500b0701a11007038043c03012802501440291a40024442c100446116045056603200d20f100341e0884420300c0d101c5504483c4d400196010602503401403005100351130040d040300ba884200044000d590b21444241d0344203440054480c118010b5002600713150a1030a8011403020305502c2c28100040e0820320480c805d0b0882c50840c0324505d42d40c0c3e404040031903a6103a5000020384c402d140c04e2003400c159044c41860040b80a06a60200b510340d14814850703400801524451140203000c0c20b900c00d4803c071a4200903078001e015075414040d000307500001031034144400004d0007803149403080da075082903406407130580c031900218072038900d01c001001401074800c600c181565040e28082801058602c072001b4110101800d0b036840780c17000c103104218550107000000b102c00d50041c1c890050551280c00000b42d0014016921280c000000204942c200740c4c204542006148040715821000c000c0042d0502c0d04c1d90f001640000c40034420310900d00c50f99 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 586796897 1250 586795647 586795667
    0x80601153c050f03060f0109031a06180403210e0d23031b0c070e010308120c0f040603090807080c060106180f090c0e090c07020301050c0909071215060906 68
    0x1905280b840c0070701c0ca00307085001d4007004192034446d142500c4141c42903481707241044011035104040e981e004401c25078412000e00115003075400fa42800c00c50411021812240d40c0c095a055110095415008481558260003d1000782051a1030301c0240c082c003e4108503000030703003d096a40700c1d8000b4900f130003c41030f4a01480c091041240510500400130814403003041024950b05081e0341d650b812150b11410311070a07030b001c0130f80e00c80044000030902c2481001030411010441d80d500031942d841c071030f0002c5401a4911250141418841404054040d0384a40501e50240340e03000d0034484160b03201c2e41668001200404039030006801003100b29005019814803c0720307420508551401c05540c448191028807485040e6034484441e8030030076000ba500600c2c14503001d4901032a070714184010303a130b080d417000034124025860030303002481409480341603911a4038020003420403a150004100c8202880c4122595940e960300d100704540c1d8418002d03503008140e99200c2d00340c4189012809824440d003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 586798147 1250 586796897 586797017
    0xa031a1201141b09270a0f0b01020a0305041a070b07051b030a05070308070318050d0e0a05060d111308070312182303010f05011e08060115 61
    0x10920a52502c2d4400016501c0700c220640e03561082d070700d486400030714800301100384060f9100034070140201c19650b900f05c1c2d0f2031064014014007000000400492fa907008001016000510034401803041e00c603444413082039202013112041c246015501c500d007203000c085c0c0d5160003103800042c42e01c010002c4903c045042d16202c401460030f0070b0072f4210107040d91080c694001c007042810000a5041d40c0694003812000c01c010180f5400c4008510b805580d440c50032a04401041c011170300b1880500d4440d90102c1030f598050034080c00c12802945110141100c1d050003001044144141494110314880030002041990010400c40d4035509000507000700e0500c00608009428005080041080c01c40c0400c598041e5030020307407000d080c1e46001d4002c010905541d0305500341882950484000d80001d030580320402d5540c01e01c46420220741e00d561405110740366090f04004010841e40380312210340840b5000d141801400c0c885c4501e4403842e802200d90140c1004412000d02260000741402c02008941ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 586799397 1250 586798147 586798171
    0x6050601020a1203022a010c031a0d060b04140a0b0a0608040305160203030f0d060503100902010c15110703020604170c12030a1b0f020f0307080a031a120114 69
    0x8283c541c18607004014644005140d00000c030118100d042034224550504003419406100c4011000d0038060840e0742003007000a81007480d401b9500c00c196000d401c10aa0050003214910030940d02d810180030441d0402d54007960b2903000e81c00383c520b000841c0d8401c202c5501c2c0083c5610a110400c503c1402c0c603000901084903500030040000d030400308407510204001700440790000b051001030b1840c415484940546034000c641d40c41c1802c1d4030b402c42d009941c801c4007a20080724440403000304540c0c0151019002075107001c000808030300035404402e0540c1652102160900c007907040075000e0750003540704a0050f801001084103200c40c030300101c54040700c00410145803108024880c0d6992408462010740c0b0000000440d407108019806521810059452403100041c3d13558060615200649100054040c08100020503480071040b1129540d00007252801c050000c2000c500911904520441085082009501c2940c1c1c024000340503403c44000403881c0940301440c0007501d07501611103c510f01c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 586800647 1250 586799397 586799413
    0x160324020f03010311030a0210050a03180b0c03070504050a0b0a0219050d0302160c081f05090d12020903011506090b030405030403030c1511031014090115020106051305040605060102 80
    0x1c14000c04982c11650811090000d80340c1c1c94002034201160b078a8000e500c010f0940601c00d0700f6400c000580070b000300640b001c0002c0e030440050758403a00781c0c07880000c0902c06081c00141c82601d501000c1c1d50040a10310300b05080c16200c2c0089002003819030400c6210400c04103101300c4107a030400010414800420a0381402e400907542c00e80d990605806031414035802141c403164816000b00d4008029400141502d15250741e140000e0f1102c810951030728450b20584031000610006004480c0606480001404600ca40b080202c1d0003200380700d5800706060302041201403665090203000e282107060941010303410710700303240035002c24055480036071070300420f10030040030940c040181d90443e5050704001c001510303a4070300150a040030406140490b460141c4c403102800c556000385220304c034030141c192100d07a120340640c40316010072986241d00c002d80100610a407400100d104100700c20a00012890341c1d15200001c1140b01803071280d01c10305903503c04000074401e03580215501700100380090300000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 586801897 1250 586800647 586800667
    0x102070c06050d020706020d0603060b010c08040306151805060102010e240a0212010e0f1e060f010302040906080a110906010903060506131812030c0203160516032402 73
    0x3980d018403591007401000301c3c1004994400d90102d0300a1a0b1080007155140c201094507402026140001d841c2946050450890b5501514200b002c1c0380d0001c14a0f42031030b1541c0c0d40e080c00350501d0603c009a502401e000001c8070042d0312104c15088612081c0418186400000282100e020380f140c0e625540c044050019202d0402407109090345204000300695a00c900d003000c087d11400d58030550700c800034000003540803580c0b000170b80502c500c694403d801c0c0e00d4904c2c0710007107414080500d01c105245040417030312038130304460b1070144203206041c098206943d40882d00e007142c90b55485508260810303c1000d04120b80e244006009010446e15450f80c0e05120000038034180345800010301e4550b407840464965603e400c50210032080082040c0020700c110711a8804180e86e01604a445001400008000302d001e80614801241c0d2030307004506110b0401480706205440072001c4d42c00d8000c0c0301c1d80ca0010a0001490000765003c2c214505030000880000320b08007003c02c241c03499aa00c10b01c13941d143d17 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 586803147 1250 586801897 586801913
    0x10e010b060306013207140d05041508090f030a0f09080304061b030309331a01050a2606010207080303060f060f091011010e0f120c15091b03010207 65
    0x980e18003840c117030f0030706060b266900c107040e50300756944081e465001c241403041048000902481001d45001c6e40c591200d000000d03589805903006900c8060062120200041d2044405691143d01d0000702ca60181d00c00340d130076040d43d01890504000489800010410715004003400c8010442d0000444c40c19213002e40c0141150038141d103010080340c000078480280741c03098000e4170701c0381d402c24400c0c0481112905410000d070b02102e40400e5040031038021403040c10042c0710768040c0c820b01307100c601071907a0b0130801180c007a449900018103120504052502800c2184025464241c0b80d84071520242421000a40b4042181e441079500c0d91040003008a20344070300c203481e2900d8100352805a100d240c0800a81d00c5c43c020042090303002014180107104242e4000084401c0c910728000030860b211021079029200d07201184090341c1d50b4072003611a06d0380001e09004001940b121401d64500c00c1d00c0c5055900310344c0040c3c49441c0c003076000d460303401200a80000350b885401b2084000314608401a03a540403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 586804397 1250 586803147 586803167
    0x60732010605010e0d021c06050c0a080c0703090e1e04050a020f0a0f03260307200309010527060313020405130302100c020304080106031a06010f0816050d0509010e010b06030601 78
    0x405040c0d60447c3c80f01454202d080c051085500a9050205142008050100741c220103512400141d48201194100d80031784202c4a94503010340e64001c59609100c6443d0810708085e0880e03162504007031b0442c54018004440c140a24864405418450110700400c100c0058005180d131046d058890308000c80201080590210f0340c0c0300c40c10740c040350042203000f41c406260321081c0901103800800c02400540c0400c101822001c03039440c228200c00c815030055601d0192401c80b0780480d200301701404114807a900c400100143c2d110920100e6010600404d2658100b0b9034500d001e805a1303040401107145c580105584424454000740d129180c07a10f000b5503641c05c2d0540324040e136556a00c0c1204041c402d008480181130000e000b07121b0180d0324580780c00080c50554108000c0468000416841d600c902d081d211a41803c1e620082c09884080c042c00410702071004034003d101781000b81c1700030b42100c0e01a04c1d02c1400391600005059510501c0e141c07c1d10b021108841c800d050400420150ba070b08524940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 586805647 1250 586804397 586804399
    0xf06030a0b0603030904020403030e090a1a060306030705030708062505030105120705030d0c20153108011d03031602070807151107050f060732010605010e0d02 70
    0x144958440d04003103425171289200c01c2e50414000039010091507004480581c1c0c0c00130070346a0f02c0480e6112400c0f40c040380c00b104502c0c8411121a0312086a07032a0081c05103402507001015036002c1c0d0307600d03000070b858010594044029900b00703600708500000150002c1c80b4548442c0d519899051421200401030f1205000b0b45101c0c2c2484555000500820440c05015040141c2160717944e0b020101c01410401451030107c8941b001900b101001c0c85c00058081103588026041c41402036500e01e651903950410074005450340c006603800c00c9044400750130510f159415040750050541000c041500b0758020759242c1d1a01c582c02050000c44030000412241d214070410b410b00d03100a45004103d08007c4241c2c0100d2940c0706038440031903003004000281d002606d058840c85495050780c2c420a0701c0c0c034018072a5a81c800401500c2c4c80ba103091200050044a101c1c1128600700a94050300440600d0f480c803000280c4202084602d031100400d110302c0f400780900f42400c3d000004035400280008811038002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 586806897 1250 586805647 586805663
    0x13020f040f0b310605180921040302010e0603060f040509030c03040312081f060f090510030b09090a02090a15030b0708060a0e0c0a110f0a03080406050f06030a 70
    0x3400c0341076059071003110401d400400210a120001d00e092032515651007201e014441c61445400341d400d06442003408581c00903103441e2020040840c4040130710001800c0e0392480c080c88080341c0010061914403184410720440154407107085000060480c1c2d101101180240010020300c041c594620b01026042681110080361035a140d410340f6003103024540502c110317480b010402000300071144034003a01850503a034a451480d17a845030b400c060040f1900c801400640e5280d818484944901c507000013520840c180800e089550700c0200f40c2281c1c02918420010781c0e10f200450042c50a0740c2c0042d04180117600400c0d0001850700000c00400e03000d4076290301c0c0c6a59044480e1151a4072032144020b41d008565200c032454030038009058030000b2240300e44120289400420420322500f02e241c06805180c410f1410010080001c1da1001d003c1c140b50b1469100715950011118000c026414a85200355035aa201e0b09083c5000c40c2550805800c0c4580c10000c1c2c400c008031910f00003540d42c00c1980010079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 586808147 1250 586806897 586806911
    0x3150608060a05070519050306151309020708040f080c04110c030f07140a080c01110a05180a030503040b130b190c03050d1103060108070c150b15031e13020f04 70
    0x545446c858984014980c20510315407110054020b0051807081d8003e50f9195140d0010004d480b0007403040c20541d0030b03002490710041c02550040d50291122510850300d8603c3d00d62601c9044d1451f164650146040790f124403014521407c10307015a910000c1c007190300c00d0030410030000641e100c4c001c2d8200030160000c0498424144041070000c1d00301012600280d641d0300741141040314941c0e0003196909115800c0c0041440c5105400c0201c03800000c0d03a5580318140001292003c908048501c0700320380c01141c00324040702003001407000b40018800746060940d0b40c0314108560018080c036622014848206029111342c03082180c02001820b012441c18202e207290918044d50280141085014010b04d040006000e01074a90000c6000c1c103426201c0d0002c0703540d4407034200e0b48041c41c6000100f00159801a0b04403030f850903000000a5000140040740310281c0b100d540c07240790001c40b454a0b44403403020800001c46c42007001c0503005001c1d50244900c07042c0c1500405c0c0840f01910809010300d0703590320 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 586809397 1250 586808147 586808161
    0x2206110d020c06070314030c0310080d0f050d02090a08030d0f05060d03050703021e070501031107110906010504080a0b04140d0203041a0417011401060908071a19030603150608060a05 80
    0x10505606c40a801001c0e40300d0400f040707400c0c0c01ba00200c1e1124441d00c20220041540f010001d141001465903580306442007554501c01ca5480c0c00a408805180d0340a0203001d019550b0440000d000d400c80030000d50b11020070080d0b940940707080807409485640751000340311403178a90450200c0019098180320b543c0350114a41280340c487c2001d1100d50b240d1000c001544004404a03e81c011100c00340e809100e9502610038500e55445a620018042c140e1608004c000341442440d0942c0708c84141002c5040c039648640c847d0a100800380101c2e01d090310306080100f003200b554013a171070402c0c01000a0203515034a41000c1e54901c224007032014041140701185000e506440b0880303000d07100c41c03803580e005088280051400b0f025400d070300c1c580b0840715100200d01035101c0c01c400011600b1080052070582d1422400640400d100f201d810400642008080b003010215424060004169a000221a891404c0000100b01e013861500681400c0c81000c100703d61000a1072070f0400040c040015007070f29156 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 586810647 1250 586809397 586809407
    0xb0f06030f18070e040c0f14042a05030a1a060a120605210f190204051b03161101050f071b140f010e0a02242206110d020c060703 57
    0x400140d44914040031a03003080c1300080b94040d9104460707140540340c490081404586203405980700d808015011500b00386042e4003c0998591604100315100300700032143c07140b030001840780102150f0000203001a6800c140700d29120391400c218040d090f10b40c074070300050304c40c41401300000401c082e10030b50000703407001340c0d2100c00100002000030682001c02100005010131914039005640a8034032860740341a400704032101c90a50111140f03505946607170070000200409030892881020a102e01c802c2880c10074001e60080050003d9031000a50030403008100c40280b60b080301090341440c040c45142200348000d26003155003030500e5071081541c0b0a10b60103042d0710301009000701d548901e00b6121200701203040340c1006000c00007448040020220660303500002e8000075080714080e11074022403542c410201b0700140601070038601d806031001503003200075800709516040074140c4408003c00303500030b0006026002c440300075100b100c0c20001c021b515915880a00c3e80180c2002030202c042622070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 586811897 1250 586810647 586810681
    0x3020d210507110d0807080126030307030b0901151b0201020a061104080d020334140606090a05060a0b0f0d0203130210050310121103010504050a060b0f06030f 70
    0x1818108880d1a000000820f0781120648003034090080900b00710805103e02841445014262100221640383c462040c00041234004144d8804080e40c10018841c4420b00045008a22503074000c202584980204050140c0603400614500b92001d540700405802409484000041d5148070041e00740500040c1d060508804004188619100ba048004c8071241c01078001d03a0f050100300e0b4800011801c0c143e90340d101e5662601681a8103520800180d5803001100001020024500180c0e41e00d5503034040c3c1a41c54202d480826401c10805c101260902d100015806040403030140a00c1c14110085031800405004801050b440010310b6241c074000c00c0100d0b4071008446200b11358a00d010085001d084194200891040b4180021400524460401d40c3d003e18080021503824603c1c102e26000d2944034200121240c49101801c5100c1e0b690038400e25201c1d50142c40030b007141c0c2d100381c54120102c4415000c0c080c481ca0320403640b440a07442d07100c00e03264841140003000b092512401d14030a840c0c041 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 586813147 1250 586811897 586811957
    0x71403030406060f0906060c14010b030a050706080c040501172a0c0709141521033103020f060405100f030c02060f07050306151b160303020d 62
    0x80003060008110740e60303000c841151012203c1c0d038003207529456448140c80721440342400013040762070f50740041520701d1107940042604600000d01400d00402081c02d0034401c820a030750b690812441045075a800684242c0e01654010915140500300800a095009a200c2a019408201000032080c040340760342d1300b86040e0314031280c2d128506140341803000c550144205807101e0052550008032045940900069120b0306c032082c012070341da074000f1840302010898542c2e510541a00c159144003106c003a1494003945c01c100919990620a140410810740200c03512464182c00d40544c6c20303607081c608452090300e80c101c40006000f105079001512501480d005151300c1004400c400460f135821050781440390f29984c44c28050403540790b07400c1c1c2e20760004440369800346940c240050403092240c0e005561081e0300400741082c028490051034540e401c400d02d900b8a486400c080d840c0602c070300b004519041407680c6c030308280c201c1c116927000b912400c0c100384000038001c80d80c2c0001c0e5050040d50016580000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 586814397 1250 586813147 586813153
    0x31704080307120b120c03010b030109080306060708070204020f0a081317090301060f08030316090305210c01150503070911040902030603030d1802010e03010b09010b0903010e070f06141e0714 84
    0x405d42c40040e21000400304081c480d603e80006080b4504060041d42d030100d070410320700d03030079070b5541c0003402610340c000002164041002c00401005030348030700c05414209035960040c0e0b140ca403100300103400c1000113000301d2901544a0400c200103225952000b0300b8582c000c10890303c0d0b00c0700c2e0020a0261507150131408800c010100c1c0071401d44d030008090b5115400205000c4501c00104c00152288401400044c086e6001901c0101404800e0320354488241030601c0c1040c6042c2541c4159402c4a000c04095220401c2600040010f446e04102c0072020f0030524000300440c01611300d00d80340c1449036200e910102d40d00840059800da41c18410784850800c107a106000389407002d03904103d45121144208d000c510030340c00b00000c1c0c0c10140300380d401c01e800141c1341c01c3c410390825030824595080314010f41d9040d07480700040b18820809205100060124505518002d4104400905815100d0301c601c44040024010322503c00082d010100440f8070355031000c1c0c0d46142e1820045c200a0001520291901c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 586815647 1250 586814397 586814419
    0x170a02030d0315170105041b03030c0308130b04050c01110c1c030207030209040506060411090d0320030f190810120203070f27060506040e06040906090b04031704080307120b 76
    0x121381034104510072881040c038011310b100c00c0c5100f00c501084502001d030005220f11200c6001900600d552030b00705608801d801c450341d560f940ca11903c4c120440f011103981e0403030001a003882d600f0200c1c903e242c0c00103030302a00880440c2000306800003943c241d002061080303504803006050081c0204c40196401070b006141a150600300740d80c2e148010341d00e0b03500682c604907401840100304030036900301d40030040a03141404101e46041300d540307a44120803c500341005e104000a04800c03c001c007100c940340e0b05641d46070008100101c41d4001d5a200100902c14010200105048182e02e82c0e810782d02114803101060a00e40007007860700400382c002e540e0b281c000c10b0000c20180140610440785803511004890041e62016041c3c0a50f0068840e01d50448400e20080c811004c0407400603500441c060400902540349441c0c0c1300944110f400f0680e250661003050105040d8804800ca0408041100d4070340b6906040d074404802d880001c1909041002400140ca110107180e0032041849500030007200c00d00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 586816897 1250 586815647 586815689
    0x70605030c161e14060c030408040b09040f0c0905031902030c10030e0304090518070608010504020d150905040c1a0d0c0509040e03030603011401082e0f0204170a02030d0315 76
    0x1c8148095060300e14403a005c00507140035030080840748510350014a40c0d09041c0b41c00d40b00c455540209800c0e980c8a521284807905420280c41015103103011907a40300c804602e01010305050008013661418070615142d040c02c05a100001c0e110035007213064409194500354404110014180d681c0d01010714040041d002640340080c0c1c100c94050032803080e0306c0c0018422804a80e5503009071b03100c1e0034003241c1810010400c42c900303640540b00303188642c0b202003005000b0b105010f4005050750803da00003644c440078041881042d80c1c100d400742c04107007903016501c020500346c0641401044005034803180c0f5007505008542c0b0513419140303002c00c041d1003800700c1c09a4824050b1a504125159406507180407507010031001c01c1c0340218100c84890000d0306240404d006031442010f151083d01c00d44036034103450754041030141c0c03060718990614100016115030601103689040001603500032030550004d0101070141e07a0205041c1c80c1070b0b846042c000703450280402032512000180e44a85120070890800c220a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 586818147 1250 586816897 586816913
    0x2190f0302130b0f01030513020a030c0906060f0c020f010e19150e010c0212010603052a01140d09060e030a0215060126040c050d06020705070605030c161e 68
    0x96078030842d9000200c0004564042c11601e140084a9114281002804480d4025030081e6089090341000d104070003043c0d004150216840c1d8411540c5030350b0150104441540780c401c1c80c0c050500e52810358581680714400802d40350300c055010b032241200310040c0d90305a004004484041101400a402d2424044050301d4a00700ba48140301045500100000050740300703280c03503644000140c503072841418441d0244a00c60740341c2e0b6040003180d9a2843c0200102d001006511401004401c0d401010004006000b000070340c213811060500c802c00301e040d800f250701311040d02c2072554000400506008141400e0b4003900c41c0011001b09404005074482c0c841d940410440355000314443c0c0c030701c041d0701c90000458024401c0c41041410030b1580f00b00d0301500d5564074541e130b0814050f40010803c9529480010750002050100300d4411f43d0014883d07040181c2441540000d040701d0030514114500b820042c81ca82c80b8480324181144a11031800c010040d0b500d840041c072961242c0301c142582d4052801801c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 586819397 1250 586818147 586818149
    0x307030e06210f0c040b040e153007180f1d0a2105040b0f0415122004060c0213060303200d1b05150c0d0b0f030a02060702190f 56
    0x4000489400200002e0a41088178120b68000c85801d207090b207005500201164080d041301680c1004800c07845056550590f0381103414042c01014140300700a284030b000308208420600d081ea001560104072606268551496141150b44049034000141e58403100910030701d42c098922650f00c20810b0108a80001c2119505201c1c0b0003a048200410043d101c103480c4544103840001c00c104005d0048801d040701034080002801c44003401c1c651207210b131501440c9840381030800544551048030011802c0d0048a40c8040d01c5104401805419800260203207d18002c20781448032180d020741c2152104480c41d103201001750820041a03441e454010207202502c0d862410024880c08424181000030a4820380c000c42038541c90780b00c0511070074114062644080c240d403a40100018a8550301080510620509252100e284d44002c0d0703d41d41c0f8111b5404c211b80794007032480b09026890307a840000e248100a9011a030154403400b0714400522400215070520740c841e000c4038400100005850380c440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 586820647 1250 586819397 586819411
    0x609060102100c210b1c030c0c06020105190c230706020d0906150f03110a050306130204180c09090809060403150605060f0702041e09030908010606110307030e0621 72
    0x203441c100d1585045040c0c50170744090640c001003180c3c94146030140411580100c51290410440c44070198841c0405940d0540c01100980d46800410810070141034100c0c03440b001840302000762526901000f02201040c0044145811440d058017107140200300035141e11590001e825075440d04844084005002140b0301154017904228001708032900398101f034015282480c00030041146180c580c032101380503180c59141c008448110203d05500c0500c5582d20400c00c00402c2060a1468070501c400c807000085203465100740c080303403c0d000803141d50805080301c200c0c00300031802008a0510000780c0c46410300c40c0e9401080090000108000607405440900c8090401c003c0540c0d18020b00c1004d20400a0316450300b1410040900185090f40c428516a9030340300c080e941e40305000314103004860b03003002c0640100e40c00790000c1006e00e030300340541001341c100341c0b62041111100c61003440d80c0b40900c11008007445840480c0346459121181914400c026a44e0340240c8981885802d00100785c00341d98003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 586821897 1250 586820647 586820687
    0x150b072d061509050919020a09180c231314010608010614091c050709060914010503210c01110a09090c08010b09221a0102150606030609060102100c 65
    0xa030800030740700722072160a00c80094682011568040122881880c1b0100d9110002607804030f40e22000307200740d11200c1d602742c1d4294107040d07036030070f14640040c41c0e031340152040102288104200c950b0007104800070300094407004160003818050700050310300c0000c01d07482c03081044000589607501410003070482e1035540700d2035080110891590700c03910841d00c64680103142d410348120711605c200c002e0b86500b80664187d40d0202d445085440641e905a070001d00744545036030000d0489081c405004e801400d04400070124403c040c0e103e50074020740c001c4402ca51200208040044001c00c0d00042c1100c2c0180c500070781e0311010301a0180882d6110300610440c940750140800559004246a43c1a14550301005043c810030004000581480784600d01c442c450151600c01e108209d0302a0090b203081801c040101040790300c00081c5003030b050381c0320700ca00b04040c14107101a94542004994120205640c1d1001c550b68450050349040d4505020710010340c80d142460745026071006440646c00c86240300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 586823147 1250 586821897 586821899
    0xf0209090a0309050d03051e09011404030c120507090207060f05070c2102010e010905030406080702070608061c0f0b06091e0a05100302120105060103150b072d0615 72
    0x440d03989060003a002070104144100038045880c5c480300c40e1000714031074900245842031124030001c0004a8441d01c0080100100303030f000e80c079a0804444c41500000d168100d00701499a19142c451100910668000800040c3d0b21070603c8014410140501901c0344159526200c5143c52402001294491060705181070301090540e4403d8008291494000360351481c0c4103525142e00651800c6008100b0079591f0761603881c1c1071450280a1600654001d074082d5450318a00034000d441e20308014082c070219042040140030640d00039070030342d03004002500c551011804c0700201201c1d40c895000302400c1040440480700800400c1c843c0180300303d03019a0300640c1610354079085426400e03424004242046281c0005010080c0343c0c0c8646c5d0300810302d041c0c04440660325004600481e0706904000003503519041040f01d196054002c40102c10030224508003041e180501092071400f4100b00104103030000007074010000c1940d071401c0c0040c0326003220748554080510300030005040c14045201641180c0701c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 586824397 1250 586823147 586823161
    0x150301020c0f0726060403030c09051903021e01050a140f032a0c0a060f060509010b04030c05030a020f040b01030b06040f0e090f0c010804080f0f042313020a1b0f0209 73
    0x3071500014061900101106e407034690302503000c5c2081c01c060700c00f00000341c24001180d66231102d004212a8080f00c40f84000d40c2180103100301008040700d101680e80c023000815070566030140c01c40700040d0484ca00805101c0f58040d481d2054070a64454402403d00402030018030150034070350039044101c9100d00e0700c00c1000e110004425024040e903c082e40d402c42410f039008612907810100303403103030840c0d00081d100f1744902c0013802c105004e03002980540b40224050082041da42c50503005884118000d11141d03103140c1c001030185000d5285a400b46032030301d0325000d281c1d01075001841281c1d0020000ca86560719180e181c3c81c0d4850500c22421000b85410200d0500903012820082c0c0c140050003078131160050b81c0064802c080e002c0c0084600d0300f002c104241608010300050503034480440c2490341d49900c0c001c101080c0c071440040b15000d00414001d003250550b21451070401540e8440170168603621208404d48101da0440504900500410881c20400091001d64184544202d56450940c0c50710301c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 586825647 1250 586824397 586824449
    0xf0503130b0c1614220212160305040f02040c051209010e0d080f0a09170a080411100c03081b0c0a0c0b040311010e0423090705011403150301020c0f07 66
    0x403081e4401c507210560944d81c0340c00d00c100d030400c020701c80030000d814200d400e00d400b030100c0e40000b0050903400c0c1036205000c04180051070540c50551540703400d02c01c1c0d04090310f90101c505c6080c0d0009124540d0740424211050003841511100c000c0c00365400c00500e450030010f806080c3c00d610200c150300807641b10343c000a010703018942c00340c24800e000074000d1b80c03101441c5d00144004030080d10300d04030355414017a602260000802d0004155a101c1c6007034145850044a03010b0303183d1902e0300c540e149000c120007550340640d044008981510300801c40f40ca4840880011106c00c0c00107042807503000a0b00d403403140c00042c1808207180b04014080d0f1036a0355100403905170007640001014150201a01d10480d0720a4004070302c1444010400504440113074a80070b403202007a00032560b0000c50340d0070130040300803d01004c3c00400302800e10b19059000043d800d901440000c01c000c45040340000c08507025202503054680b0006110102c512000010204c607640c0d00561007074494024181d42c4505038205c1c81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 586826897 1250 586825647 586825649
    0x1080c1201030f06021608071502070f0b15130203180105040816060b092502030c150c0403051509060a110910180f1814040f0503130b0c16 61
    0x51050440e9082d40c0d1040940c0b1103628065074155004e000c0ba911446021841d844050b00c2a1072241d52610281345c0071320f8107552307030490596080c8140910b030085888420750050850b0301c40b264400503a03581d94000c40c0d1300b40d403819140e084581c2e0040b011161200da4010350081c02d0344406030f401d011503060300c142a10011140240b0404090054418407044c018200311154030808000c01c19a0b03600010807064a4102d500801c107a40090421603182500c4010b19007011861010718a0a0455102c2070340d204468034003000810300c2a000281c10504480c241c130059580328041e200600001340036448007901c01e0700d1080c01800382001240404640348144a10a01076101a900f00312810041108409401a40e2018000000078900b5110004190348001c0c10011070041e074080d0030301e04140c03080040c2143d001106407030426610030381d1110803911076005034481c8103a0307421195482d045046002d8038140020500d00034401282292400b009000601c460904407a40d200e0f13100008450b840407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 586828147 1250 586826897 586826917
    0x3020c0f01022a0303130915050901051e0904050a0b090c0a1a090d0c210510020f0d0f050114040c090b0c2107020414010e060d02040905060702070501080c 68
    0x40900b0801d07410042401088a8a010009126803003c0003c00710b4110390102050b510f10941640c81408000da440c480c0c0003984003001c012400f00760500300407400c2d100c0c041c06403501c40c48030382006400600030710044100c01d65018020303480300e04103807629540d41c05a0032405c90380e0410310307000a01c01c00c4000407049040d5030002c1c035031090703185800142c40301081443e0540d4140d040070043d2103646d031540f004401c4464400c40855500510300b81c0444822a400c0c560200c3c90b2100028040c040382c030000b000152014006d00060313444031400d100c6031081c8038000083d0a03290030249540ba4011381648214100c500320500302451220f24070030441185e091945d1a400b00d122004280408640e00c0058200f1700801d90031903a814a00717140ea103a0001e29810100c10380400024407508504107801900c1c00c0c158214011030f440d5040c5401201c1190009184d540224100c03040d42c802d5683d0b50300031a244981010036114203007800c00b0000d48851442c040c0c940401c0e80b08010644840300441140d1690039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 586829397 1250 586828147 586828153
    0x6190c0c14010603020618100507030c02010507020f190e0106020708070b03150a030f050c0f012c030a210302040501080a051e09030702040b06040501270f08031909031509050715030903020c0f0102 86
    0x33255070041d42e03650800b034000c1c4e80080e108110141a034451445850849084018012180389440800140c00130140c000300d08641104c0420094500001038180903980183d50b1a92a0380e01d0003030080b0207580d0035650940c042400000041403144040914000d46e001d90152450041e011051010510202e9045400280c1e540e81c0c0034203031107034801404945643d4a0100070b881c203021001a01e0100da13103000340d8001c28103140c01e02001c0d4034141007490084d101d041c02d40c181032801c4006442c030a80104130ba0700040e02c039000500c403000d1840e2804540038412a07180d09506000c0c410fa580c0360041002280243d180041440381403174210306407030031140140d44e580e135a010100b13202c00d481d44044000b00c1000600043c08143c5404002c01340c4050101c40c2c00039a1074030385028048600c591142c907034000340020b142c02840451211400d03c0d1020124140100d60441d039454043e24240b00396014442c848031644c11815040e03410741010442e103010384d08a49500c1440400c1048081c10388402c0d60150b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 586830647 1250 586829397 586829417
    0xe04270c0303030b010216092310050a1203080705160203030a09050f0a030c06030c0c06060e0412031b030e1c02060105040b030714010e0604080a0506190c0c1401060302061810050703 80
    0x6041c0360040480c044281c00c2c0b41080700270300c03420701c411068180c564003681344241800348460304001410b44020030b03044184044d40a034540300613100c0c00c8040e100c1c40030842d000488940040000e0580a405030340a01100d94540103828024042411070155a125102444d40d07445503282c14148102641e0f0018070388075030240b5121058008020700741d00c01d0180840091803802041540c4603060083c00c003003013401410b1130305282903144071360214034400506141c8014041014006000490026501c0c00c00051140502500a1814017803c019078501191080c0d00b400745640861458100e420030344040c0302e0385074007200b0184c0312203d81c092603140e40c00040700b8200c1c0d03610801c01c0c00450303000500661b14103922041180e00740141c4039001d43d140c1c6d105205001c00758260545503558800048400c210603882988010f2107100340b088050a041d200414100c4103c0c8298408001075034010042c903920300da1010300e0110710b08060b05441c42030421602100d4854000c07011190700584c5070f92003100750 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 586831897 1250 586830647 586830659
    0x60509011a12100e07060221120c0903100605013009081606020a0e010e09130311070801050a06080a080409020f09040903030b0907020d0e04270c0303030b010216 71
    0x4008500c08100c1c2882031036a0814450004e1280d00c410b5500c032800341c0300d02824408040d10340000c0f640c08942d0324014507030900d080140c00081d210f0001082d01110303601d440c0c003007041c1d28a01034a4200b907454003c850400d510407505611010480d82d00fa20358440707605050724170101180312030340ca0b109011030101480e0360b1001998024441544034800c400c2c2040e8484c0781c214890401d5640c00c69a440e4005104c040c41c0350410000c40360030100b40303064501c541f14000422104a400f410340030b48072031443d05010401d0700039140c52000f4007110f030071501c10030381d40c1c0d42190180c081618403c0c401c0b851324001107249a0701040d0541c02d1900048001c0c94185080d01d41d200070740c4400b81c1c040f0220000c0c02180016907031400340905e0a4026034000c2251189242003007204200640080d055502c9444001c801581000040c904400b0888001a400380002c11440b01c41c40803c0c08110081c445035a2101040900e03400c51082c4c0b4020356080003103840d2030005a90320100c801c2100c41f034441d01d050400c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 586833147 1250 586831897 586831909
    0x908160303030b030f03130825060503040f080d150f0803030c030406090b04230705091603023a140c0c010216030e1e090c03040f0506010e0103060509011a 68
    0x96802608807180c517604803e155045410820751020102c0c41030108100f800002c01807900303c40b840c0f00fa24512030200511800400110b807040c4800d021003c0000360500400b407002031152134010070b902d9558801c0d55098401032403203040541014408030070200f07800b00407004840a445c2c03860021880c540342c0c2e80e0544040c0d00001c008449560300c034885800045d402c40c4185000e0340c072504841500c0c800c00645819480051046c01c019544000c40070070040d6030b2510504d410900501107034103800795840c4100d010f441000c000780b1400544914000b02021030303d0244070140490300136604448422842c51068440c00c021000b0004101c8010820a04283c0014512481c1c40380005207405608440c42000c1c403c85e110981c0460b0052401102c1c17070920038911200126187d8003002c0002c02c12001034580b1001400c00112503d01100040800150201007542950490102e034541c1d80c1d5404240021507090108035070b10b504060100392918414000c041d001e20421481850328240403040c428 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 586834397 1250 586833147 586833161
    0x2010f03021e091005180d0c1a0d05060f030706030231080c0d0b04020f040f1401030219120b041a0406051f030201212d0e0d17070210050f07090816030303 68
    0x2440c070841c1c100001c0035900f800300600b4031049039200d2794407034a809000200f140c00080c01140240d83c83d480842035540c0210340842a90564200140c4a401000040b05504030009510108030030290320350300d410340400880011141c04804031040150030700240120f000640780d00030200d4803050007003801860807101009051601070710010721440d0400c46c1d01d0583e0300c0c010549060800280044c82942000316200074040c0e03080c514109401d150413003080704000c00300380140034088030300081360410500784804290b04041c0741c03079180581058100316005010a0783c5c4000740c0130014241131344200f4800c0150040ba0b405851b2026102e83c0b052a0181c4c0f42c081c0b64018140d20341c1c0d48078200d11110200d2400781c034405d08441d07200c85064128441001c460038000da0740da0a81c0070100300001d1650102c10b81481002c0348902011303030703100d03030703000780e1511422940030074400e41082c042007500080c00103c188507007000d41d40d80b070400f56078030202d9071903201c0103400c84d01d510590101840070074001c0d00148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 586835647 1250 586834397 586834403
    0x6070305060118030f03080702120d0b0d050f16150f0309030e1c0b1b0406110c03030f07050d030b031b0307050303040f03050f12040302010f03021e091005180d 70
    0x3c1e0050f401c159400042440d5410864155058864003c1450303030100726542d1065860000b002900e044410488207030140d1404112155202c2c41010569100c20790748009040d8841c00312112202c100283c207454120210b004540c010540d0400241075405c001c1c0c000307030000307035403510700c4180c003043c80c110042e00e2515000d40a000c5000e81c4841544ca800200182d1120010390b040b10f01a030303601e009156840050813801603015054904209440301100b03c0e000c54145050030722008040c1580c1c00d0820200410303461380760001040e41d1046600701c0b001800254410020b807035000090361002e0f41110840150b40790164041082c42c2d8009403103408440b0314200003812580042d6607400003a1445c1d00c1303034100c046240218082001048420018554854001e4014005860501c102554980141d1001a040228840c015424680664115006101c4181e0034884103144400c1c3d5148507841034840b240aa0702c1500c104403040d100e00203840101800f10f8802d03182c0d424200400c030140301151816 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 586836897 1250 586835647 586835657
    0x5090601110a08030919050c011b0c0b030604110c0a020f030102130810060f0602060c030a0b04020d090b0a2009011412010501090509010305100c02011112040b18060703050601 77
    0x4607a00e2801003004001d071070b2288160603501e02e02012403604080c691408000039170b510002250020b840810b18614030002860078000600c85040c510f03d07000802c86014140007840400401c04545410065118507010b450038004142074400141d0944203509143d00c060f00503280090040c5090b40c980ea441140c010009402d18404400051144540ba4021003c9500a000d5009000c0c9907002c2c443c01446038002c01c4c00c0c070a2070840041d4807454020102c0d03001100000000d2f01405059005014044016004648601c2c00b009040010024100192040c1c80301000180c04c0c0c005600a402c001441002c0400d689000d281004c541f58001d464031a045c04400c985d034450400103900641100807581e403018400703514000000d054521160400740c000c000c0d840040c0085100010000c8501a94100002c2c032101040c030200c3c010400325519040c030520001e60051800c0007003c00034010f81c003075621454540c40302c200003240401c5c0e80905c180b442d08180000f071601170095201e40d91042041c102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 586838147 1250 586836897 586836917
    0x1e040507021f020913090302031630090b03151c061e110703050a0e010917010c0e0409050d050310030f06020301090c021216050307060c030e1209090105090601 70
    0x902c00e0700141801000000b1603011480000c14500031074014800c220382c6070304000542070358a0080d20f91040b500c4500780d10700e04c58560750070406629540b41d520714403101c5103040351603154008684140b280c12400005403081c000410b40b004040f007100d0146810610384d00c0c2989805060000c0e2120320040049501c1090701c00c2c10118a0034015a0340c5464030101202d01805001c400c4000c9403a850b489800f0510f050100c1ca001139044400c0b513850088030308040d442c1400040048401443c103030400400d00c20310799000001c6007015005802c03403080b141c1360002d04038500070a010440d100000d028140c1e60101c00c07020b240e50300a03030003541c0140a641c0e036418070b252039440f003034050340c07160380c0884a0607400030040007440010b11038480c0200682c805400c2480701744000d82e0050050110200f101c480a003103203010020104102d13943c560f800b103001e1007000d40c40e150250040000310500002c50007401c001d4120010701400316070751118014a1000d083e4240303000c1c0300e034905005140906104a20350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 586839397 1250 586838147 586838173
    0x60e1f023f0405010906020c1003020309010b0a031110080f060d083001050301091505130204050a090b071404140d050f1b120703080a020a08030f06010e1e04050702 72
    0x11098007180541d5122981d80d40c40c24000601c0c64a5590100045403c0443c5034285542c0e100e00514400c80289409170710f82e02c4107078007a8010300001862560000c0c00f03001c00010011941c0c00b800050030201c503000160349030108203440c0d5000441d004210924801c1c00100d46203440000b403040c1c1d074000d4124a09110b80045030808070440d2405509a0400c104001c0b089141c12104a07409042c06030700078410782c0c0c650b60300d43e80480d41400004413515110780004103940e058605032444190020814406800c0100005d0f005102c0c203034065603aa030b00781c0005400d51b0301400031002140d0701c04404a103000c0c5003d00080e4241d4003881e282c0da03c14004030071100030407070070001c0c210824807060140000560050f0b5600b60301440054043c021800b410440303a0a01001c1204002c80780c0020641e69030382e11038101203080280c03030030004266080106c18028403480c0600344030310501003a241c51190700310a1082206000343c04080550b15200071010298508103074024035006031803801203a004011800d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 586840647 1250 586839397 586839493
    0xf0705010221040c0605040620101a090105032407020111030106050c010606030509030703140909090709650f04020a300204060e1f02 59
    0x20840b40c1c48191400a000902050030042c000422444c201180751624103c0050030f038409000101480301c004821905000301c0c18400701032810950b41c020096441c07800c0c07141e10300c00004001075025103d02d10000c20706040003e4000710f540312800744040724103280400c1c407a0750f5200400340b200319529004441100e1001304c020750f0217817031a512001c0e00c41f51812042400c40e805c65001c80205400c10301440115800841200c13413007030b01031804280c50901406c1c0b848051043d000c071141c02000b02400c100840b00046103007800d0303840074001030080e00008141c044081110680103d070201c0e11082c26502031040886010f01e0303100b480c0ca000702d990356003410f06181c04d400c1c00c04000c10240c143d060401501d000e160325403040404071811810708450080c000e00803000c4a41d41d0090710480c401c050b0382000e080c43d001c0b861a24004003995030b1900c507000240700501414445010b101c9490840c00000720440d078910407240340380d0007000f410390b9451215008144050480380349100300c0208a4401c0588 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 586841897 1250 586840647 586840687
    0x17151308031e0421020a0803130c0803131503051e06041e1d0708070303271508130f0201050307030e0a0c050a050105120f22030906031107080f07050102 67
    0x84c44402842c265005511070b0701c50201c0385080441d0041c1840b48001154802078941006481099034103175607103072502c0c102c070701d1180c3c100d59410310011617854000b510781c50000058a070581c06122144100da05c00303505440d0241d480c901c0e401d281c8030054040c02255030069901505c01040480d903081104000600790f00b140d0514003010382c64240c554119580700d441c40ccc415400d44001003541c0c074900a44191981c2d001d020040400420350104001d24241790a03103120409151085588107642d009200000c5041001c0c0e540401d07008000100180611400a240c0c07035084488030313219000b10b5004440c41c0d4030080000e801d05580b2000302c242001e041001030082d84c03242003032201240c10b0604001000109a0007641081410451500d1281c141c01c261508444810701c06030690b00d80d41c10f03001207003000c000e102040d0b0f480402d5038410f042e800102001101da040d01d042100806807440c1e000c25101b0040f014060100c2045043e03034242c054001000300b2400382c030005003060704000004420b0202 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 586843147 1250 586841897 586841903
    0x513020706050f060307050a14040f11040e0906011202030a0311250314490206190605030304030b1005180f0603010504020a030308070909020417151308031e04 70
    0x103c0100700c0103040c100960009040c04452011296140a2240307801913030342061039002e9500d5000082e8114600e810400744030030280c100c2501d854072030035480c0340c0c00c20403a403140f40d91191000001d00b11440b00344144880d50003034054058816076842c183d80c0c10080e100c03415250702c21003600030005c0035401002030900402c0818440c10340e00d0360900481108144403410001c1d0000c0401500b10f512680d803112030496260000e0700320450344250000040d055101d5051200019051240c00681c042000b51282c00560981a4181f200846139000c0343d54034007620760143c1c4104010700c045526401a1503010124003124088162160302044d5410310703103041104161881c4080c884642010b03001254808000d80080045103060380000c1c00e8450944000b906021005000c15a294400e010304005000540000c6d55115564031850070340d4046a40b142035a4011641c24144208000e2200380c0182c280302c01c4100c1104068481a03080d500181010150034118968200b80301d030511113103440750340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 586844397 1250 586843147 586843171
    0xf030a080a050730020a0c060c0f05030c0f160501150e150112180c150305090c01081e0901021b0a0c0308180319020111070e01051302070605 62
    0x1021405800d104028000d000301900344030401040c280c0c03128418483c0c4440a88107400040c0344d14100107405608110549018000128004101c0d003080210a00078440c14080103181da6007102210141d840040e00b200044040010a64643c48600585400c11a100c00c2c24a0b04420742c00c1480e41c512000c0045600340d4580c49080d030400d80c017013070002c000c240c2d08141c42d041f403a09420b4081c03242c04100780241030001552038410040130540c051400f1000b034500e403442030001400d0401540f4581c0c840e00c80e50740c103203c0409860b81d21074000e450041004c000140b130310480741801035403c030100a00515110101c1240c148081040c078640354002c0c4141d20006039601c042105c5d00c4554460030808140683c060095100010211200c0b40304980d0440c500d2501c400700151042d007003262000702c03158540b00d600b940642c1d02c6040311620a1151003600c0e50f481c0740f03603060580754480689200d0080302030711841c0104411b0910705004604900030113001450405c1c2965a28103c035026584030061038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 586845647 1250 586844397 586844407
    0x709060e100f0603050c04030b0a1e0902010806090408071505150604050d02010c03090506042606010e01120f060c020a05010f2c01021b0d0206100605090d140f03 71
    0x340d42441031030741003950301034020101400c08807a4903090305144200403c040e40c410000c1e6219812809650281d5408075150880703003004010040502410f400d210710316050503180020300791191041c1e05d10964182c482d410300343d6600b020040500402482070711800d2040100c0c800180f80d01400318039808944c40001394605107058424241101d00100c280a0340e404c12081c031040e640c060a16000b55824a4004410358007490100e0b094600b5500690300900041404103001911001d241c4c050202551000d490200300850143e17a04420300c40c202c41e80001100500000c101c14803180c000764011504048004081d0b5110320888600252040040c3c124443e070004221081c06502150030b1805014004180e04401101c547d401c1182c40c0c2e00d07000044001842024801c0d01a02d4580d0b055040d0200c800c0161700c0d00c02c0d02c3c2c411079490b0030014042d4800082982c08492021400d40712640e84031810604103070f0a00114140302c590940782c034a041100551400740030003503901001c0103000515110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 586846897 1250 586845647 586845659
    0xb2104210203030601090306180507060302070203010b091006110c0303031e07080c0f0d140108070515070f020114070506091e010501080607031820123903070906 71
    0x2811080c05060115041001032003156a400b0400e401901e4111a0001d0a070680b0000900704841c1c060300140725000b14280001c080d47c0607805801c69038000d500903c0028066800c00075140003c89240d5580355542006004061184040c01c030002c1c2c1c0282101c512200c240c0c000391540d00222081e0040da4104500903000801d2164401d811811a0505220b542004c00541000340a504520841c1e10404030301601c407010b69401003484600b0800b8990f0080d40c44010306601c441b41400744501035013280b14a0543c0707040c580d04680c541601301c034204440c26800e9004440403811803070611400c4500b48940401b0031070911080e402040007030001c04181310b20903100415159100050341c80c59140c04010400c0c81408a05141d0200d418500041d048065041503000a28010b070085c0c4544205150a000c0da42040c20420310704400721444841c8282c00c140d071581c0d403100503401960101a80071150300c4140d00e002c40310038080100580780011041d41020915182d0039601a191745a01c0390420014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 586848147 1250 586846897 586846943
    0x609020f010f2a0212030c01050c040303020601120c0b0a030b0310090b0415060b040801050103021e06160501180f2303041203021906020a020f03130b2104 68
    0x10403102030a20014405803210040c1030704001c1e43d2104490142041d121110741601c10590f840c00c0d50061254400000716882c080da80d80203242c42560b00d601e003002043c0404004420344040f01c0d80355001b089070740e00b88544905908207c910480720a880319401107032a01050340941240c000030703500041e07041a03c000309031919500480c040c0c03600d4504204000880d56241000350702a40044103444d207a000d20100f100240381c264041e5503e0711000c0740206190074190840d038101d0303000b00d40801501450655448036102e10303000ca5640316808000d5001011038218803059041d00403800091882d020380409003003134540f604107c602200035400c2608000c2140c40090342c00c807030040000c00351b0a40044087da0381c861030203000d502031180b60a9070200740c800c02c440ca014062403490811000c8944c50840040e40006805d60301500500b0580c800000001090350610042082e04015003454084404002d901c541140080d1051500d00c04010091940065000e640b00e400c2c1c440300043c4c42040891 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 586849397 1250 586848147 586848169
    0x60e011d011b05031504020f07020306100f06021f0b1f0f2003030103032a03092d05010f03020408070b070b07050306030a060e0a05100608101e0c09090603060902 71
    0x1080c40028828011100170038807140c204528243d40059072425282404542c1303000746c1c40020351510600b010040c41c0031000000b00c1c212211405c0340807415496001c160389403018010041a168180c804c00e410640007500601c141c180e000e0000b240054082020b90a041d103021071500106820340c540081540d844a003421b20300103e40147c2c1a0700401140743d80d120f20046c4005010840b0b8400c51907410a0362000161036041c40c014042c4403c4000c2c5405040f1015512980c00107080304808500c41d0140e094100346d07c0702501c00d4060005007008015140d00440a0660042590912000c11030500400c480300180041010780303a100d034000c0c0342550a807030004104000700328081c800c0c0a2551400607940b1409580100d0125080c040c000c00300d40f03042d50176100503181d84126032516030745502c16030091040d2a510b0f01500c103806070072a80780c810b80e40a4405110041c5c00100c100c424881294416044201180b410403a01956a1425000d0311070307640043c0e0b401c0c0e94801c40f401c04c520306060206 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 586850647 1250 586849397 586849451
    0xf0c120b03060f060111010204230d030804171201140f0105070c09180803070c050c0103060b030a15121a070311180102010f11030f01050f030703060e011d01 69
    0x8404280c0450120342c98036006407854003e4034007800031070001e0317025149801611600d04021074480384d84041c480e2a0900b1040000d054007030249900009041a80605e00040d0301070301e444440341c1340c1c1da550181d14402100b01e40e900c0754051065030600312002301440e00030600c1d0030f09500c8401080e810884480445517003141801010885031000070528400d030740850303a42c01300000701d441c00d81c415031051a005030801403050710008108441103410018000c00c05004030708803008242d0150066040f40c1d694060306074003084c140b0000d1080f000c50782010349108018032040969640d1210b03000415001d0b40c10488200e060702c460602c190424a0380b4907403004580c07505000f0003201920b40d1409225080c8542d0804019078101f01842c0d00135004416803036507840781004801c400710361034000e81d0815154030720701c040726100000c4c041c0303098801000013000090160500b149141d4a83c002050b405501c40340d2035403100001c428a040c0360004090200c0c0210001c035101c8034044ca201d6000110200071 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 586851897 1250 586850647 586850651
    0xc030102042702090d0303021201080303090a06020315220c0801051003230a06050a0807060503070503100e0a09050d0207030c060521040c030b0703020a02030a08040809040f0c12 78
    0x4009141c0303036002840007a200c00d458815210551002500640304080c50185c1001d29012444201945980208101003c0640c000030b0340c0d0b200c004403600c038030058600038a070745e00c0042d100021178120742c000c42d001030002500c4582c840d198404100620040c40403220318801559002940e901c4034050708260028034640007032076604040002d41c03108903032540c03101015520810928030091176603a0000705001030384189c21516207100f107079001d0665030240c40d006408501c000903041c040002c201045d01c0725034441d1400c5594811040310643c0000301650a00026600b001401141d10780340c4900ce022066030100f50802142000703483d00310841508011503010701c10800c0810030981a00c02074407924a0b04550751105007060b0301d0b801c00c0944055000418000c203001c2000800559038044a1254a900102d9910b01209904038000c41c3c20385409a0401c02c01ca1000c24803c042c243d62080c85910400d09240c480030206049641250b8a0142d00d40d0b2822549500342c1c0103401d0803803075900400e007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 586853147 1250 586851897 586851899
    0x6090212090303100e060102010f110406032003010902030907030b070c06062112140c070602010b03150402090601050d1506030608030c101116030504031b050d030804150608010504050c03010204 85
    0x450218944c5100c0c9140c01c3e00103e0204180740c1c07007904444c0703450500100078400414203400560385c5a00c14030031140483c0c545549088050001d815080d004480c002c040c0d13003141c0c40e000001001c2d50000b0130300c0429000310342000c00001c1389507948901610340d659440080c8001423526004845150300560900c018840b0f1a80c204415141d0404613281d001050146e905d0b10214151041c04241c0c007042449400428410500d000001d000e00c1214016402070103299110014543c44402c1e40d030400340c1c407401180000707004d404d10200c4160400c0062400c10f00c0e00281c40c0c500012110000144440451400000c100141c2c2c54003d42d4085c2041d0030256241920070400c0b550b641182c83c0b1107031403c545070003400d0924008802581c00e8000c000d4040c58480c9058940201035030f0103800115030700e00c902d0120b1420490040040300c192140503104a15040e520348080d42d001400500c01c6079001e60703844074904804180c1c024180101100000400ea5007130914049040c805032820f124040c2e841440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 586854397 1250 586853147 586853161
    0xd050f0f06010311270405101a070c0506031806070207082505100503011811041e090230070c0210021911010e030706081603020d06090212090303 64
    0x40140d40201d400d00b0b0000f200307030040440203101d000e072910200d6a9865401000c0d11002c5880d0305401d200c004585c1042560f48065043e40241c0250040c2d480f5604040640401c079114103000b0a01c0f0741c010780910030710650b10400111035510072644c8a41c8404e540524040b910000c01c40907402c40078500280410500305462580d03120445000e590b0034001071244008800004850100030f040701904045d0000c401c110003034025402803003929926101400c1a5034052003d03c036130032048198100944c03410b49400c245241d9000c1782104c4050010381d0300400100401d0b28402055182100d80c9001d0f0f01281e0340006c0e0412031004520b50700051b611030300b003101c01c65204004601255045070b240b190076001201c00c903e0114100b2550f46c4802e20000c4180900400b003c400030b007500241d0ba0000300d100580103051311000c0600c20b44012440a401007056079646d00e000c5144c41c0442e1400605210300c6600010540d980381d0303c01e101003070b40001c10303c420344c0c070005502e548200c11400640c03560070029 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 586855647 1250 586854397 586854421
    0x11e02120d02090307060203030f0f04030c08030405010b04091b053a0f060219020d080a022209060806010f142106090c03070501030603050c0d031407080d050f 70
    0x140480c0c0d108200186148074040154140e454001000e42111010390710346501075a20f600907120103004240780400220710800b502101ca1085a03d51f54682c07045405540340503843d00054004c64465480700702c2103049898078400d118102e402020251907009039070b043c141d003c00d1a6000180121004400b003444d8000c00241a990750080300c5034001d200155010000c22150380c114005c14801d8030121501c10b11125801a00408401c0c1c16180c0c2d40080c1408240d0703032400c0b01a242400f1070720050010b1070301a101c0c2e000d00104001d0302e0009883c1480c1c0d1900f0000d0005c0c1c8c1d000313030401a54441003840700e110300300130850142000e0b0303081380703592410f01c034004000e41c141e0014141300e000000742201080340d1a510b9449215442412a00103081c82d00080d5140c0313582d800d0b694081d11542100144544c824040c1d8000c89070001c0203460001d0416060080c04000048243c0030700c105800c0700030141500c900103150301c078003540c001070302d0305a00e9000b10161403010b00001c810055038000e01c41861005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 586856897 1250 586855647 586855663
    0x50c06130c0b0a05030f01120b0f0414250902030c04030f08090a0b0c060f130609050703081c06060e010f050306130f020d050a1505010f0908100b011e02 67
    0x300030303030140d40958580740442403195009030300c484801080500030590400c010354010108420f2520840e80c84101c1c00045040e83d010217415100c041001c501507011030003a0603002402926070340d140850740c3c0c0c03e0b245400200c840d242d1243c0005403030384040b428100340c0d000c094544980103500d1414455030075500c40c0540d0101400c6000042000303410040d401040b1039180a000c6d000d048038590781ea11008061300603001d11003030742c05140b00081503811086030f003c3c072a144580361413494895030b480d448e0080201c51821101c9215042000c40400c00c004050080c2500030902c5109407140032540b101503400a6108805100040551802c16078101c60f40e44100d1210b86011901d9682d844009000303500004000ca07a4240760650490aa115079001029001c1000b40207003c651250300b1080c0840d0392008a01c00d4440b0043c206020a62041014801a0750186002e01040781c480281905080580552641d07556440071088030365608030100c1c0085410050704060f5481426001949071842 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 586858147 1250 586856897 586856911
    0x1511060a06080a0308190c090311101e1b210203030106020604030e210c150c03070b190510050f040e0705090c04030c120303060e04080d02070606030605090705010f050c06 75
    0x1000000034846c1c10501c02c2c2c560007800c0400305000c00d2581c0b04c806008008a800700340d07a0b0030445580085541004003413210300480ca50b443d15032862003540c4944d03209200b02883c00410054000e00c2c00e01300d4412100c025042e0060b84952140810240780507031140d1190155030a540040c0b004105441d00400d00a50080c3c2504111070100c1c80d01001aa601d01e02c07001002d0a0f42c9441c402071031a1000103003c0d403d40c403082d120710360000003100040d00036004c2d10908411982c010401500095107030328100750080882421039030055034010005054403000c642c0b00c4018114060100b08624200b00e81c00300340041501c0400011110f00012910350701e05000e03040c081c159441c08162500c180000311801550404040c81000742c55007083c1b65822030b42d41c0c0c1640000e0030f1603000308914040d194224010f42d0302400d03051030a0810314104c006900b0860040e20050380c0c80c00c00001080080c0900381c031030040e400103041c01c281884000b40048940c20264010044c0c20b020fa01c50a040005940ea080b800c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 586859397 1250 586858147 586858157
    0x7080403120504140a150c021f0e0c0a03060903090e04260906040305030405132708070c080307020114090a03020d2102030d1b120203101511060a06080a03 68
    0x103244e040c40c01d408a9524034a1200e8410655001c042c02080c1500c802116074130f0311300303201203510024100d0350b80080e40c0303600c404402c8004e40f20307405401c503600282440d40d842c02510400d1036028002001070036203a0060301c0c900d03201c124440402d0790140c040f42c0070f03008a0001d80018200b82d125440b2140c180d0042c0001d04075540f16006031600c415007600c03a81c000082981d40c2d2151203151007070f00c80d0040d106031030084d01c0346500345040540c1409814004858400044440b5a10348a40c1c40c03c0c150064040d200600d0401c100d4000c28020300c0c014026000c100c0085540b807019200041041c0355101c0c1d44011810b0902c458245903a84c0078040f8103d0350120354003aaa0102030515440322a181c0c03d008040440e84035141d201d031a000704c0540241c201258013001004c1c0003400035516014008041000144417520b0ba51000356940e000e1504401040d00030800e80382c48020300901e84000740c00510105001c000581190282003080ca81d200364101002d1200e240f40411581ea0786490364802000d01c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 586860647 1250 586859397 586859401
    0x61707020a0501020c070f050a06141606061d0f0123060c060a050906010b030405060106080903070204060902040f0b04230316120c0b030f0a0209190e0f070804031205 73
    0x2482080907040280d04980215a104004110150f40d2809172240308441c440394500082c56140c490b408008941c03650b1511440903002e00203405680c2c0c0401c1004601e2212a5a081c010071420f01c6264041e0130000b440c0d2000f20000c4500f81d4030100c00a0401c0507000301540148441c0007241621a82c0561050000240c03d0380032001461a01408460010034407a1108000820803c3d4000e94000d050980945d00c01e80d0300c41a818005100441d40942503038003940040001e00d2291280941c0a0048401d030390400406a0010f42038031141c3d8040504960080b60620900c00d80c0400300005181203500289401c1c6414014152030f00c4043c1c401d244510140c0000c0313207540302488007800340402184c54801c180c3d12010314048121640000b17032483c20761144c000c6034048a85084a004041c000708032003e560310700140740080e621a03180d0035001958200d801c0b076105464640d1402618004c03561402516100130200f0084400410680810a010f41400082500482a0000940c41c80800304240d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 586861897 1250 586860647 586860661
    0xf2009030102070b090127030c12090b0a0e0405130f02090a0b0a03050d03110a022d070e04050c01051e070c0510030504061b0f050304060b03010e1b06040617 69
    0x9002d1000040c0c120390420003040b05141040d800b0b40744100250390501610840388803040c147c4401480024081810701910f100450000c81465201c18050b02c6c14850040d00d81e680458290050102c0c0404940c200308842c5043c030f4140a4580c1c00203201d5860078007004152625500c1d1541e0f00800380c0120202408a64030003015040f962070248043d00304c405641c0d8038a03045643c1c42141c0c661000280c540040c40d900b885018007182d01075480c0e40d00601141c030381c54568102000d15842c4658442c0c1a09089240c078103814802c180080420074101303440342c505401c0550034001801b855a0402404101d1060220011380e20b400e9801000d5504a4480c212860a010030f0012034000d25880b16800d130076000301a40c144c100034401e80c4a500240b0410710340c101d94002c003d004501000101703d401c012117840501c5140a10762060144401281069a443c0842d00b100e100003042c0049411408041d52120f107151b070818807411017030307400358034180c50141e000f040e001080c1c00801c5d82d04c103204081190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 586863147 1250 586861897 586861901
    0x30b220509030d0c0809010501120c03060209120d02151030060501260714011103091503041403040807031712010e010929040504020d08031303030f20090301 69
    0x11290504013000300f40120807001d8005c507412100032040d903007402c0000c00c1041d9003440141c0e410b0384c0f04410a0100707046542d040040d40004111075000040c0c803c80590300e550810020f000b0381405e401608144000c00301c0385001440052030709041440c102c1c1c04103c80c1c0d80408900c001c1f0800201c0c01d041d03a4400d4809442401d6940f18080d0409080170008600e100b06c07a54401024005030740840c1800b0044004292075010344d01c1413100822024060440e41d50049110050513012041580d203060705050000340780800c17004582401e002c0100820040203d41080014844402c0009500f49032038215281d0790740d00c49000c020711000310f41031054244140503003a20307a55045034100c9400ca40c1c58070380c8088060400d200b0350443c14140820301050030f0015140c202041700e19550002d4195030350050001810002c0d00403a04003494021b0480464070a10266005010078203c071140400c05050050980e07551036420040180341c440350340480b0300c056190712400c0c330606600f141c8035006440040c0c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 586864397 1250 586863147 586863157
    0x40803060d03120c0801150e010f200109060207031407050622081209010605150301050f0f0616030207090e0d0c080c0313090515010518061b010903030b22050903 71
    0x3a4141054121005141c00c10305c0c2d42d0503036030007030b00b000f40300d800000c802c450101c0c0750014a40071404001310480450320614019424000c0d03018aa094a00b200010b1401c403070200750b051318819400310f0003a04041d07001e040d02c10401a008403139400c040301038842d16102d80e0003030049815004c514503110030303d2520b907105860054010119903100e820045442034a02c00c2260b08126551801d280424186001d0302c604015440140b042411a0309140504c644650003c2000398040c10300c1c507510015541e242c00910300340c500141039141c01c44a07854003914000c0142c006007841410b002d480c000d5514000303070790750b40c1410318036204401350a9401e00801c1031003200d0b01c000440c0400900d120751425460003501c21900864401c0111b9500d64042c40c0790100c40d00d80050025100300003034884080c150b0942480024010450b9290030620002290050101c01d070030703500790351120301d10703000d01d5014881c0b880c5200f419100c240090b200300d50844030351070629002034401555440401d1840c2d0b801c0003692 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 586865647 1250 586864397 586864427
    0x90c061d0a0e06030609071a09040f0204081e0d080a0203040f120903290711150703050a14150126070309050d05090a1503151401030c0503040803060d03 67
    0x111207a03200c0481000c0c0784012124103009118120228400c10b000245200071204103903002c203103c10b0b40103616600c55011038005036100751110140013114040e80b0080c00140b810230300500b40206210304108000b400c602c0702000301e82185000e07035141034028030400d9101941500041c0c0e29a0707686080d003403012400101919070440c2c0d40301e0124058100d80f004060301d000300904035a400d603071580b00301c0e403402310781c41503992041d2040441c000c240511002d0f002525180155607020003495108414860116410710002c0d03242e60500081114611580101c2000024015540e203010005510081d1040712841d04000380c02ca100c40040e09030740500c0c4560201a100581c141c1402c6030020b01600a40f1020b80711030040c05100850580600c00315100e02c50b000d0400f45402e03243c0281c1d1125400c081c0300720300c01d058484140311404440d86001002038020340c1031500045c441000010308450030403200a05026003001800081085402900c0e445001100c007419034800342d1030100d40301c203008a085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 586866897 1250 586865647 586865659
    0x70c1104090f06242705060402280e0409020307060e06070b070315080321181009120801152a050a030801270504050a080a020307050c0109032f12010501030204050703090c061d 77
    0x4c00320708214400500a002817076851001c012f030044100006c84409400081d030507444403008101e0140584601108a50010100c604002180d140c14603400e030200e81542c0001d07510150280b0000107501c4000c094241c443c01582440340100c80c3c1c512445903807886400b8440b00e807000511040c9416542007454880f141591a4010301e55010000792414002c1258032424005140440b84c3c800c0c280c0a040314403404c0c60106034600b0305070075144488804920b410a09501208030442c1c4030761805606058840c00060040560764140203002d0f030010f8110031004521480c034401c10b07056107010300040c07000c001000900e940720f82c9006031800402d035800422921010643d00f4160350080042d211141c050720560350741104001c01102c0107000e0703000040405010100007040410480d96560594000483e201964050700b00022020382c22005120340030b07074440b0014400c41c01c190241d150050352504041c480400141e440651410039405690704221015580710348440141199107603940d400f42c04 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 586868147 1250 586866897 586866937
    0x90c13020c100515060901020d14040504060305030a02011b020a02151e1201050108040b13020d0510020720030712060605040f06050306070c1104090f06242705060402 73
    0x42c8001a1004943d6294598841c004100b814200001218005401603006c0c10075050a42c0064440c0f0b43e040001502500090101140c280ca0701c2c45048003450054008607100c9094004c024252031000d50094003045c1a503c104d10140d40020740d020b51141d0466200310844044401c1d15920f01a401d8041030b04401070424010101610000309400c3c6030750307125100d50703030f0300c2c0c1c0c0055030038510070f5800400319451400001c40240e08240c1c2c2e8645144000c01641106401d500e81c68506101c6440d100c0e0002c4d40042c0040800512030f882680c507002c000d4500c0340340d5420000103030715944e2a201e80341480f5445022030080061541c4204060207004208001c0c0c2c001003800400105154020709010f48111000310306c0450091502603e00e0341d01c01c00e01c14102c2d80030010300028000e41c60040310002450815240050402d002d056483c0c030148a80e0140c0c94141072281c100c1c4142644055a42c2e00382081518800310050f203d00d194040d000808901511810b012034028412404440407100c51005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 586869397 1250 586868147 586868173
    0x32a060615020d0306081906090b0901020a0201060501020a05070501030203091024080114060613030b0a02030610050c060c031b0703090501031104081e1207141005090c13020c 77
    0x201200858669500f1110701400081044d8112822800740e2100d5a0005018540340241030b242921f40c1341c401c90b00400c03811510340d81c082c88900c1c183c90b090a5a500400c21a0801c1c4c0d0900c210340080c10244004c00749a0000c1c0c07a065142c2002e40101c90400d07400100041c11688104040034540c18600c400b00006101105003442e1004902039840c040d0020050000b20702c0414040c858480d044054070010a0321040c0400006900081c5030041007140d1203000008107070b510030543d1003146d0544000d44d40e46020010419040880454a010301c4010701c440810b2100000e80290300100c18091a0707030b20707216801031540c04034036010044007401000440804159000d000034007258401c1e00c0134840324200030b481020600a500919800c0e0380280920545440d6420700121004400d00a89208802c4090051665840004291002d0704004455480c0b0001085207400b4a0017100041101d401c0540502c1c0e19541d41055280c4a03020500d55205c2844035a412039010040220807282800d507840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 586870503 1106 586869397 586869419
    0x30d09060b0a0e01090b0111120a1716120203010b0a0302030a021b07170d0804060c200f010e0307030e1309052a03010603032a0606 58
    0x40400034568503842d010102409522a1061480d810a01c5000503903491a54450410000e90000c480004011600d08821007542e81040d5481c240d0f280101c81e4249070180e0710945402e0301e03041c0400341800d030321b151200c4001900c5018403405503000725802c90209200d5001d2407038041240803180ca100303500866210342014401410054409131003008000f000c003010015070b100c81400d100049200b2100394005010360000d00c7d034000814001071800c1d00140000309059204d0001d07110540c050300c101e60514008001102810340210b01942e90f45001b0140c0200c0e5500e03050b007440084c1004021561095099100c41048601c6801440216091010741c503401613640c00c207140000304288610140c07000c11102e0301c9040100121105205080043c03d18800d82c500030303040000a8010195005c0000c0d00c40003c83c00140c14000c3c04440b1103903080c0104450320300000820802e581c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 586690647 586870503 := by
  have h0 := BRFrame.cov_init 586690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 586690647 ≤ n) (h2 : n < 586870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
