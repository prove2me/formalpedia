-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3432
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:38:58.235014+00:00
-- url     : https://prove2.me/submissions/5d1f870b-578a-4584-9814-d3e03854e1dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 617086330 ≤ n < 617266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 617087580 1250 617086330 617086339
    0xa09120c0308060d020a0b0c1c02010b03101a0405070509091012020402070507030203030f0c15271204090902030606120606091e04030906200d03020a140a080f10030b06120c 76
    0x40c0408d11000025585001e21204404c1b4804582036030704c01c03800e0300c00ba0f00c0740540c198404100c4002400040e80007031060314511a4840c22002c981000c00c0079200f08440c4040880c2c804284401c5a003450003005900c03084060b4004c0d0368904110301c05003940c90f10706e0b0103405654086088420403400308601c0f800f07550028100ca40703070050015480750349c0c0c0c080701030600107020720020b80031130540804130b060080c558044602d00b0240580303424507a0325202005c0286502c185040c1e1490180700c4402003001d4050740d00003003031140c414018940780c92805002e850041c00082000484074402141e503540201003201c0788145510f544021a1692180e03844846008075201d090208264000e2601e100700c403c1511210116281c40c060490114608a82c030300c070075007084c11880c44c140e00c6039000b0b02c1c1040460030310209150725154517000c1500181c0291020403c2c000500c680202820b16660f4858903400100845a0465a948000c1500a80540d02512041d603906144174414000c0d0b03980f0720300150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 617088830 1250 617087580 617087587
    0x30506010b0903120901020a14160305070f0f121e170d1107020d06050c070f060c0201110a020c1e0d03020a02090604020903210c060a09120c0308060d020a0b 69
    0x203003060200e074040b188080c42845480c04103103d6004160543d820910140c01400d00509192985807010802c06629019402043c40b80c0983c540d0b00311102021b14000c6008003000d03802c01040f001d10300303010b400c007501a9074000c80c00c11580c008080201a40e80c1c0c040b201e82843c00100d402c80204103105079009295102c0b150010384500081c6003d40391b180b841e860b044c0030030302e03200740445180c1c41800c0d80a5001b0021403c144042100c03908001d4009080f44840d529000e003a40710350200e0f20a48800b118440d0f25552405686a07090050602c40c3c101b51000e80c1c40d1011121002c1c0d40c4048611503075004800581111040801d0f4500ba000c1c0e0780c4002e0a0b150348903a403450000d46440d18000300f28030035031055006c04c80c142424070030745410100c040c0080002011407150140111407000c00245010383c104003c081111050100c24010104654003240c0120a4507210503420840f4080800304410001150003003980700e13071b910340c0140082ea24070060713036000e0000c25140d06050704030b0301c107a50000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 617090080 1250 617088830 617088839
    0xc0302040f060c051203010e04230f0f010b06160308070903080d0e25090504020f0a2301020610050603060d080a120b03030903070e2203050316110d0c020a03050601 72
    0x7510f02c440b200e20810039030741594000b01c2c41141d5400700b8060000d656010307000060010f140e2129041d8901c2541030310030500005000401d243c40198400c08001d0340001061041c2c0c03410034091190800781c22180c01d0b091a80400d00c0310006190303400058100140310b07000c180d010340214202d13005035401003041c647d83e44c010384490000d8242c8406002c0f82e4171170107030417411981c0a0b1104407070034a146034124034401d1a140018018000140c001daa200c204004c800060f0395903210408000c1c0183c5192460141c0c58003104e4244034000b40c0721906540006082007907119002c40a242515011a6520703100d84504010628243c8500001480c1d0000000c650110070340000c204020b83c80c1c2420244214150761080c0340d2640602c10400380c04d0361182c2010311800d0300c015181a840303a014200e000290302c0c9101c81141e95040400c0c10ba000c81d8002051244420240b10785032064145400c10b032500d004031100103580e07082002c009400700102d4013010000c540c1d40d04210002560814200d86d881d5846 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 617091330 1250 617090080 617090087
    0x606040e1216172205010f030c0203040b0c0607020d0807020c011119030207050a120b0402090c07060c1706010216030b0a11030f31030c0804091b030c020106050f040c0302040f06 78
    0x80e40035084d1160100c0b80354444680e03a071150782c252001a516030b01469401182a8040e103042c03142d207001e5000600c001f00e0045084006007000c02d861500402d0345040c03026020b820f1400d84034000c001c204103c0c00300902c0f107400050200c02d0203000c0c80d00a410a03c4485590700f460003484070400304008094801081c1580020f0750785c1617910840303080b21000d644001108050100400051507410010000340252810003c96540000c3c105021490302031140d49010855190b4032032140420302c030004034040000741007059580200700780004e080b4200c070900c0c0e80086030491f20000f4519401200080c0c0b05100b2600700b00301c0075020209043c0c41e420070385400200c5080448050b1006620740080c007020510480700c0a0303228840c0c15468014056a4400b180d140c08c0d0349000f910300e4030040000156030484c2e885085442107000b1707a40080000140c0008050f01c81400315001168140002800542e4170340304807140c054421140011001f000321001e60103800707582e01645180e1103c0c540040c200c1d41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 617092580 1250 617091330 617091337
    0x60c03050f090705090a050601030b10080f0105010305040f14160324151401090e160305010506031b0702120607120f060f1e05030601170606040e121617 67
    0x18050900141ea6842d482c40d075a0307880a03c1050352280610021072850480c0e6400700d5040907040c5408610340c8292408a41400c0000d6100310000b10b50004225480504a10035405040c0034070f0240414106910f404c83d13580080d000181901e40800604082c501c020440403400c40148400028fd850f0361b4100840621243c041c4201c1c00e1407519140300b0380101c0c5203c0c0f0040b40c8552202407100e2070401038a00548180030030600d040c800d18440200f001c4940c09070003482024040540c0c1803508081500805544040e8030880c000d000920034012034195003c190214071a110000c0c80c0c55401d2400007400c0c64061801080290040c4014064076035404003450040710072081060003d00380c8034866204540117880392075280c040010080c00042c00f211a0707041c40c216000c460400c469192800242495002e81c030086400c001114410a4103206020315540300d102245c0c00c03ca903041030200c06841e8014011885d52810000400001034000d00c3d58000d2910b0f00030039008180c00108089020990 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 617093830 1250 617092580 617092591
    0x13060906050f06071b0503031218070e010506090f12070602121e03340905040e0c04020304021f020a11120d2a150b06070f120c060c0305 60
    0x282010004203150030700d50710000003120007414007484c2180b00e40300c41e0030711480b07441400922407119100184070f940c1000542060304404401100b01e0800303e07024080c202c41031002c158030f50040c1f0010021010000700aa04680050360100d55034401440010081c3d0480745140d40d0040440003070401c818000a40c00096600039004c688807030402c60343d56082800789524115002010f840c3d07141d0203a0600700510741084c80c4044600c0c2d800b440c000b410204100b440502c0c12181400340044c4081c17a880340c2100c0080400f079400304031804044500a4440002116184c0580d80000116045482d17201c01800a8003001d00030044039421800000d450b940c04590590300400c030341030004464944503506400c0c50904000034000e0f41c081c404282da600501003a10355119004511003182c1c0d100022144502074440c41050060b00c481c041804211401032400e58000d09041c0038080000d000c144034105695041401e540c02401c680300111100c0050010040c04c00342040750f04031000341c00d0f400290081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 617095080 1250 617093830 617093849
    0x180b040308060901031718041b0e0a08430e010b0a020a150e12030a06060302031003080f0702130b091501020d1b0210080a050901051003080a020c1306 66
    0x1900d0b6041080310035607080c00040d000007401c2d5122004102e0b05c1004104645283c1101450345510200103130464502440280c031303d90412481e0030006500c21911325074903400b1202c6803881d908142d1000d0f5210160010b00359000011042216800220110b000c1540c1c06d2a04554080b440001d0701e5660034040d10030100800c2018001007080c019510646000c44100d900404d80413032603840b40d0032068441c0d80391002e810350b105450450000b0900007145480ca005c1c030300a540e8100042514119a8a507004038201841072043c0310081032481c400c0c0049980216200f80c8544241c03810a03110b10802000a61020b01e505220300e00c281543c000d2665001c04545458041d9110f609a011010202004600581202074000b6080780250509040348182d1a100151031110782e02045c280c08202c00080b020950710020001c500d441c90080590047e1260000d10050500c801c1210881280380001001c013000800c0c40c01130301c3d00c00c0041e40b9800034000c0ca60901c0d074000d8000d10004103400c2c001c3c003d29 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 617096330 1250 617095080 617095097
    0x80105010b0403020d0b060109031209030203062a0705010f0203310c181508060f0907030c050607050115090e0d17011202012003091806010f12180b0403 67
    0xd1960300e06450880350081c0120305e5607001c940d039650014400809540c1805005040440400c60b0f244122112240f50386070702103400d0850040500e4514001c00f0440403e6620542081200c03080200d1150b070205d02071050340b16800e40c034000d1b0162401201d98046180701104000c2901000c892034284815614520400c40c00300b0203411403080401c41c00942651034400d01004040c0342107514071405001c01c13000082e50200008454510160703035020000684c03118090014503180324440300d40050048006019661666513000c554182ca0300c10284580000314000040c40003c4d00103000c903e01c80d0076050b15143d2181d030610007e140c3c9034030301c41c210b00c5a4551108440c2c0107842540b203c01c140d0b031604205170300c0c100e08000402e4030348104134104061139031144141c48904141d040d0030402e11015584801941042c444581044045144c51500319000d00a999820820060760011546050300b04030015009010181c2181d00c0f0321440c0e5000000aa003d002403401039034040c0b88070307a8500d01da = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 617097580 1250 617096330 617096339
    0x90506100809190309240905090604060302030a0b18030a09051e1011120c0604060207020103090f0305071b120f2901080d05030c0d0504020112090b0a050702012319020f0408010501 79
    0x40c0541c0340706c1010540b071072010300c8985083c1c01007175400743e0000c00108007540c4039404a42003448200003100e290f0001020b001010500400c90441d1201d031000550500c11000c800a29448141c4541e501842c038080980d0440c0d20001d107892141038000d07041551400072000011300440d900034280d522400307424010301001c88030344110751041c00c1d424014151600c85441d004020b40c09600d0480c117150340c518034003002407021003051080c82d0290311025200c00c010b041101c03240c00d452034015030540c4031920900803107400c1c02050b10000d07003100c101c1c20340030480e00d040380608040003041c0340f01c2110380504089070078040c90f20906880e810000c0d112802040b09056600740819038030100c11503028402002c140e503407030340044d07806801458501c0000940c3c9140c00e085811445c0b041c0d0303403040780a0401c24807120900900307420103118402004002c01e042190504050004005259101d680300850344059001030703003040601c100b00741155034840c0d40155500303a81c0b061044031615401d01d000001e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 617098830 1250 617097580 617097629
    0x1061110020a0906120e0114100f12060f0b09130201170f0112060f150806060108390a020309010912230f010f0b0406090506100809190309 61
    0x102e03440c40c030f034640307200140c1048415503a07008851030000b45185e031503505100101007406101c3e0070703201814251006080150365103920342d201e504010080b000100d0100000813020125034100c1b50030090000c0c000c4c1d421301560b0003030600980e0007540030710000240b1201400c40004c0303c0d4600d00c01d89542d1030282010410070101213080700c01407500d081010041021507281701c028105103128290014180c0108418101290140c0744080b40b00c80c1c0540c0700b481405420808903030800400d0a24202c2c6151021213805508540c0a41040e1001d1241040d020101c152800c0703d18030300054440c0c2d40322204444000e54036001210300758005460b20000007100f856188c460506107410203854101480b0b0203441c800342c3c001d400e1050314030b4440d906442030481002c0c03003154803414050a000c22030060080030441a0303807144c1c02c44000325280c801400fa1568a030014040d0041440c1000305041d5220015681401c280c9080c0380d81180b21140b8101c201b62780000000305540210040040513982000620f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 617100080 1250 617098830 617098837
    0x1e01020d200702060f040f03050a02090a0209030a020f0a030c0b0c07060f0806300609010615051b0c0a0e19090f11031006171c0203041215050106111002 67
    0x501000004002490141c04c2c080001c1828030888561545081d64603070000c10040c840f507100f41c81a8214880250451814400741a0040300c6c11b070080d4184102c1d0030020352240d103443c800030722650750b08040f1481038503040410802550400800d0721041da560345148440d80c003c410005c807034007a0b2280880c40a010780c16440205c10ba69880c12680c8e070300c04013400040c1521400b0142c214401c0d0300403601600c510b501c1c0b1451001048050701450510b01e00250948070310307801059103d0085020740702000c2c0c2c8034090340c1183c902c072580403220070f6243c00d119080c840c42c51010360308444070312000305115490100e002d0083c010410140b614041320350102084986a002c010000c5801040341404904005000c40000c50000c1c1034410543d03200c40150125a500d41c09510388017001b0400016150040c02814003100c0010410007882444510081d2288554056800b4003071044031080d00f404060850744a9400794800104450350716441d0243c1030280c11141c0864038070410b01e0260b80d0392010b00a0313 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 617101330 1250 617100080 617100131
    0x80c010206010f09020c0a0f140d030e1005040c080a0804060801090203060604030b0a0608010e0c0405010509090a080d02070510020d150e01180e010207030e0102060a0c050f03091e01020d 82
    0x143c0344840c00c20018001944c40380c1d40c20f0600d84508000700010640903a000203046214407024039901e0440d0100906000b92804668289444e244400400e81408245c224904030701d0f1600148590351403a00444000f0355402c15921071140b00200002c1004d031070014015184142c96105007a80c0c0c0325130040030b0348800c41e800340c3c11071010f0204000280042c5000fa401604e40c50b80855a00e40341c180013400c60707211903da804164801c02e01c070395803420300788646809402e0a071011121486d1070841c4503641c01d041072008044c0d48000031512800611541036450181d805015200b101c00c0c0054458085c0d0403800e01100380c5490007901224044054140c0783c1103607101c4070036946076880c002c1d008a425101814400381191510f640704a000403c2c0700404140744251200e00140c000c404c0020701d84040144040070301c0b803400b00d803910a070303400c00140e4100e0103007520982c0e41e980e2150103040c240400555a840f801c80000a03818425206402400a658200b003040148070b2207a084449460120020f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 617102580 1250 617101330 617101349
    0x1415090907050f060d1b0302040f0506030c090d0c0803040b04090c0305041203020a021005090105010e060328210908010b0103060605180111190302010b0f1e1216080c01020601 77
    0x3c0c008807608005002e081c85082801001410070318400c001d20344a42c0c90035070341d00040d900107030500001d540c1e081544003034079003991007a00750718018003c02054072642c98100c2c852002031a0141c01c0024410100001c0d091800c1929250707035480f1811b02868001c6e01030324540c00c2c241b64041181d82d102e442014400d0343c00080c44031080030344501c150003c0d440030040030210b0140c52091603071081c881c0203007030060750441c00005441d85401a0090005006419140f00f9000140c81c0844c0d40c2d14030040b607014511507c2c1c1d1002602c102d28105072462800c50f50750080310080c001044c07078141c008106408039028500240070b0b80b14110011070490300b03d401072034007103181400301600d0200960a44070440c0c506041c99250054407035001440d0860726a01d4403066078100184008050f428001c18a039400300742c800421005010b0001041c4103030107038021000301107100c6516000d941e10450030101080000644044842903803242540d06003034004d0700340703c0c444c0c403160500552001510300e04a896850 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 617103830 1250 617102580 617102599
    0xb0a05040e060f040816050703021504032406030f0f0b1f060311160506100e01140108060301270b1e011710020f091c030918141509090705 61
    0x30048200da04040c000740c07040c0d5010301a00f03030020f42c000130104044d03001f180200084c42c658030420a1407407507c2078400c0040c00030300080000941c0400704080c8043c0c03410515020300038168040303005102603440039006501c21802030061100c4a42c0461645016507201d514950720711460a01c5c0007804008076a01c010710540070483c0521a600c51030880805022a40c43c142400b0000b10000e91400002c0e50701e90480b01c144801d401d0098051310080c0711a030140c00c11989880c2d1160500d40d00d030240b00d81070004190010b242580c0070340c42880000489a100c0011400804020104c2445d00074110750504461010844c50b07059509240304000c51004a40c40d142c1c24070015186422003002c1810003807248011041031180c56001514043c000303e6105521112140d00f002001d00b4580c0065490702c151031210004641e1182415040c1c0340c0c40e0020110446282a03218001d04101c240245030300008002d10254103c3e0b405004000d010032100075000d516024090b40e01c840f40c0e1f11496903c600e48a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 617105080 1250 617103830 617103841
    0x306010f02120318060f1b03130c170d080408030109091407031a01230f0a051801050103110a170c0708030703050108212703070602010b0a05040e06 65
    0x14240019009801d1064400c520303200e10744412590001d4031442510b00910075800c42d00101000102c0d4414a44d40305244541030840455000c113103408100c4c95020400000951603d1440003080c00841c1e1041181001c96aa000a040500549842030320365001d4076240395007007403080ba0014010341c0c2028845181d42d02e0803102c2e00050401c0b2004540504504080b00c4c1141c109001e43c1c40110300074040904075440401040c4c40c6024140c10103010f00221401d1743c01c0d50311071250710a01a5100b620800c460548071000500c0d41e41c038661115070b0083d011010311020b000600803060403600c0a8030144682c000b032042c01c03e001c0c05007050443c00500c00451100c1c01c51080350080c0d40040b1600003852034a41507455469060f88100d901da0f01094032803004005d100d808100040c03078555140552080008481c10304403482c414003403400b50030748520642d0b54800005142c468880d640c001c3c100c440c10b665410b0003a0180900c0c00c1c3d0780340700c0c2130a40000600d0342028090781e5000b8240c0320140c04195a10b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 617106330 1250 617105080 617105087
    0x207030b060d020a0b03090a02102d050d0614030d23070f0b0f040b06060f18040608060f0a0b0603070503010506070f0b0106090e15240d05040308060f03010b06030601 73
    0x2c1510a0344c0c4481c0940303000554400103001107000310b905001a00800c2000d0043c003d4480c1055030b0501004940d040c0c81e200c044030f5400c0050058900840200c180303103d05401c5946008502d81036410030310b480c038000754009485c01070180c0c03804186d0680e4401308822409442d5120752003015598102c0c50402c034110309403444010701c8054401e17681803209605a4941445480b4211400400b0b02c0b50181808140030303140c40590343c8007008481d030300d00d8101c51a12581e50b0b40102041011454500c501240c4550b4440e00242e0152550104580e454130b018264a4144241596801c0002c0d00d13000000b0520308100301101c0c070820f025210245580d10f08400e1085a130300901c020750318868851004400540b100380a00d0003000145e5500c0886030912804200b0800090100b03100701d101c00b00e4030f82c01612400d9402c58040a030700d0905034020000c1612000c207109100c262140507140408002c10103402004260041c1e0040d6070000c0304e440d00380300b45400c0318a20044241e02001c10700020b10650720 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 617107580 1250 617106330 617106349
    0x30309030f0f0c180f090c06031e0e010506090c07030c0f061e020306031207050d08100305010e010c09060807020618030d0519150e0a11160317070207030b06 69
    0x40b40e00842c0c81c4106649030b01d000380d1004d800490803c0d04038543d003034011040303010b4811421985403007017002c003040e5510400450805d106502c1819191030403014a144070709135a0028001841c0d09002c01e05842502d180201011503c00348140303070902c0810700b003511040c2507600d45d50f415201c005c070b40c0e0080d4135040d01d040b151078000ca90090b03c81c0640405254107908010a0021400000d0380700d00b4840d0406081c4000a10043d0314110148100070208500050940070305d651420003103c01d80310325600104503032450b0405072130f0b98280081c1d0700c1c03880015444404441065950710f5429a00c80408030751a11041d5035150042e481000443c4210030071121042801400900726840c1c01c00d024010030036214101d42c04104c1080c2040142c41c0c0c00c40500966141c2001403c0300c0554508041818403c0b40000e02804069035945000b012454a200c2c200ca0203944142030000c142980c0d03140007085a0140000c60003002400d20204e2000f500006503502904e0344925400c60300c1d600c05050000303884 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 617108830 1250 617107580 617107583
    0x804170706021201060f030e03072d030e0f04020423040605180a0e03070308010905130611031b090d080c030d05250c0f08031b0310180501030309030f 66
    0x504026410000e00188002c080c84401000f814a0942c50040c010b0907071700680f0700100c241401d290016941070004021100404d500c14203c1d2442c0100c3c81c01440084500454032110b4480119003100745a0800803000040508403600114038058030140700503070065100300710086006501c58940540a680e401c81c155001038400100039039607100192a40d00e481901c09100a551400d00000002c603008003680c055140c001585480300690340240b1706541442a181d03d5540c0e41c011540200d00e01002c0f5007a2604107000703104c0c4054002c00714041d0351081da082c44000000d802921000c1c400c03101910b6a242000f486415046c01030b45540d94240e10040b280346c128041000b00d071a40075424030903980241401c068242c0c4406146036526040c40b07002c008141408040c0e503e103000603c5c169154640b03c0d500c003064071b440b9243e40c4100c0c0003000b202c05d484401c4400c044100b01102031207042e0003040b03030320341c2e0309400321042895181c404551080c08041e00042c0c5052042c40454101502401000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 617110080 1250 617108830 617108873
    0x1311010c0302150703020a02061807060c0c08060c120f3c0108070815010f0521011e14040203060f070210090633030212010f0e0106240804 61
    0x56510000c6282e1100c3c08403404d0b000302c0d40c04940203003080e41c1004200c0e030280d10100640810b00201c541c0c0c50b078464040c81070300c04001042c0d00180410028220010081c4820400c0701c0c554180402400d000780c008900c00140c040d08440003d040f014400c01040c061a00701d80344001c0c1880c62240300030707040c0c103417903008000b030450700b0150102d681c0e580c4549000b0544e0f00c014212040c06c0c1400203082032120b41000700542d0320f650051140b154440c000e0700454404440c8100b100405405005840c0c130403c5140c074207946804800a5100703121a40807110341903a50b4204402a05029240740700ca00649029400d64081e0000600320210315007015041301c0540100ca07502d203200e020110540c0c0701040c0480760141c50700c135400d00500800c15040f0042c10101d41002e0403c038903004a0440480c0d504c0040d10546440556a05003582075020240c5440c000e4014031a03a052030644502805841c41480c0e903400351482400d00003101d50038818107038641659501a00e445603203c00040c028080d0902804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 617111330 1250 617110080 617110093
    0xa02070506090a0c080d0f0f09050d030903140a03090b1b07150320071122050f0a020921070e04050d170105030709020313170309061311010c0302 64
    0x3040e010080749100e00030600c010910022280b6180364828015031000205a0010750031854050b00300c80380c2ca402c0001071600702010241d40c641158010401d81c001900600307003403500c0b805c2c154032085001c02e49000342c035140200300340305a2582e40c6032010301000d000582000021b100400003080101048814a08014400d640794900c16080201c283d121010b40b5980800c01c80200303805025401c5111400303c000c40d001305c2243e020405a1162140003841c610380800c81090541e203040c083c4412320110b04552000390240b1880c10000e040565041d030004e1000b0b400560300280328000c46110b01805400d44400c0d4505040c1004101035280a80d013180c02a003a020480810f10102940b00e24090f0004041c0b04413003103405091443e1340e1741c0b80c00a070125440180100c4c0c600003040d100700e9500400050f625038698252004000101c500102889481c21074030081d484000c02550280505105454140c3c4810507410300c201c40b511401130045e0190b440c031112640c061480c220400d4041e0054800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 617112580 1250 617111330 617111333
    0xe01094e06090c03020604060815060702011e092402150402100518040f020703080916060507080c06011409070c02010801050f01211d03070804090b220c030b180f0a0207 74
    0x18a811940180000628440401040390707034601000c80c000c081a07403410710300100c0e0b400080404805000590101c4105031313f01040a2048a0001c0144a640044559407811500e52503560b18040110070040c440c0e00801c44500090111150085600800c5007503400592030080e901c9400c070105d0f00a40385006000c01d03080351110b00074403011000007000140d1b01d441501c2d0180130600098041090340e80503255590032013000c0c8072190140c2c0e80c182031080d203401c1c69141112492003001d00d41a0f0b1801500700015805916040381c6560303a1046031414145e96525001301c0340186c040c2d10190001c1e019100401081c02d01800c0c8149403070044c0b4101d10b00360190f0101d29248409002c41101c0b0983c3c5000d043d1080c40140c07020300081300c444010b54a030140030345901c3c0c4180664000d038480c880e5102c5e40c0c0c400a5880005140f0a00b900c0d50010707452400381c080000040008520480c00300f0b0402c010344c24a860100c00f4044004a030040300d01458445101031441c0440040c0402e0b521a420440c180 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 617113830 1250 617112580 617112589
    0x100207030c0602012c0a0201030b040207061b02010c020303090a020f0a1d09011b02030906030a06050a17120f1b0c061803120901020a030e01094e06090c0302 69
    0x90141c020381c0c00100d58100c010540b2129800520200300d17125220303031844102c22102003801d8041c90b80901c0c0104030000c040f0000350003449441d100511140c0340015404a2007c030302074940302c0c23043d00e8000b001480c101c8082642c4030710040b00d000c0c0c807035040a0500001443c0c407080362a031182e40035140d000150b03203a032500d07102c07541d09900807910b00c3e030f846003000031404090080ea40c3d0030301c03040e140d100c54020107035003c0e42e01d0040d0846039101d650044001001c0d2f515581c00318000340002402020800c0c0d40e050780642d105089208444d080c001c620300c0741009081c90044032441030401686c945410050f0406081043c1046000b101500400c0c5a02280c0e94507c00540800945010f03003855a07481350303040601d01a003400d0640422101807040700916a008501e04101c942c01d030902c00c00080d00c2c040101e40e01407464000000c241104038229000e802480103a80c10104c00d40500383c0051500012050000038600d020055480791b004030800140e840d8001c95881403240b82040d00c01e0307840340d0004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 617115080 1250 617113830 617113853
    0x5070c12230c1e0c0f09061306150201060e010b030f28020406110105011d070c050d08090606030f25030804060f0206011403120f1b061005011d10020703 67
    0x1c100343d0005280c2d0014400042c1c2c03104822004500030041320040c40d000c11098810405002d101321654000501ca9890b03412a041d03a20728065800c2040035242c0c51211401d6161a24180c01586022030226140c6004501c4a058900165009041d5038581d90138240d1044000d007a1042801016040c5907095810099525400034186015848509152009080000c0c0c20100b51a0360f0405004102005800e05088036984500d4002102c1d50764420050301c10034202000203150b03100e0030503200e0b10280d00006803401181c40d4002c0d40d5103078070b6000405903140000303120030b003d680024003460700e10040c500760424070007400000903000d1542c07030702c40d0200c031341190380724401192100d200c41c140c0a40c14400a8098007041c0095213061207088007007a40c03040300c0900308441010010701c90610401d4507013030341c0d14146d129141180244404e04020385504060302c01401031230400d0800b140e150302950318800701000d8a40d1040b4030703004035020000d88021201d40f0005501070407401001107100c20310403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 617116330 1250 617115080 617115097
    0xb030a0b1009143c07052a0606040f0b0904080301030b071b020d0201120e0a061d030d1107050a060b030d03021c270f050105070c1223 59
    0x300c00041e45802403110903907840c0503080b0031000d03001c0304002403641000c50004c050102d007244a9102c1d40081c150040140d042000c07138003c50f0140703080260342c82d4040b0090500302c40035201c0e040311075010240e0200301c1c0101e00c004a4280c0140000078801e0070141e0000200d0030103ca0082681e10100d40840c45262044d5410386030410000f0052003402030120a1581240040c41d02400d134281c04001244264a40c8100078401c0c0301e5103c240040d0782c071170106654502c2c540c80b000c200b5080040801076588107483c404542950404400d07424050303810543c0c501c518402d0f4091454003070303407040440041519406103004600107101076004079208010049400340b00740707000a40781d620321080520700901110301d07404041c0100a01c0104080040b00103d0201d840a00070030443c15140c808444120f0b11a06000c103d001992010140700c03c4000c51924980144002c001540f00c50f00101e5007940e8048001d40f200e030008884400e03407440341310075441c071306080c084007452507105141001c0ca60340071400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 617117580 1250 617116330 617116351
    0x806061c09050d09030b0f040302151812041206050405120703020f011505210f3c0303040b040326061815240406080711010903120b030a0b 61
    0x300700040040801280f10301603024142122040d141d5540e109400c07000502010040c500c140110b42014001c00542c480414403040c0ea50240c51700e000941e041c60300c079450703401d46403003841c03c50785448450a040303c0a0314000403815169800c207842c2d82c4045d15024000303c80c02d00c14141000b514030703080c9000d0845244260702030011000c900848ea400e6440d000790500003c03030000802c0286664802d5440c0035104021030300c1e40c0041424218078103080c3c88002002c61401821044481000004411604046a80c1000c0b149400c0008582c040302580c1c0300c6a082c5a10410108000c075002441156100f840307482c04a004020b01400f5071000807545070841c440840c000240401882c03c10385c00b03d41e0307051200c9050b000e0301c3c1003d503c0f0f400b0340301e900c0c080b402440307118061a001042e00c40e40310180c1191a824070341c1d90381d650100400e26001190300700c002030180388900a401a0600030200706c0c540543c0c5800e85034402c04038480007001d4070b0304010380c10f11560305a0f0b400107854614440c458400e040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 617118830 1250 617117580 617117591
    0x12050c0405041b061d01030c0e09010303030c1413210f15050903070209010303030c02030904060816120302121c140a0b06070302060f090a08030a061a18010806061c 72
    0x50290f4080d0307681d0070100600002d116007516241e44038444000300d60007468081040c2e41c02d00c0c0107a81e4a034070079001030703000303020f0b140080281601030304082000911555001c41ea04640c1009004e5405814034005400d4424070080080090768a4091055100068440c055100a6441410311050040100d07294800c1e040020148030f03280c814660301c4182880518901002c941c0002e454020500008003419035904e05120090f208209460421201500401c1031503103900040e81c0d2080e5608405448405451011a06500d000d240300691949900202a0002d5042e011401c0d5000801041d503010b41d5880e081800c2d0000d0700402c00c44001458503502681042c5e01007000340e900200701a801040c04000c0000060780c0015095070000c43d900c5100003030380703030b00b00c44501340300ca101009001203901005202c48540c80340c3c010000c894040d07004c035080181c5842200010300450990f03409642c03a0b842003e029500880510b50310039002010b036440c2c032803000e000070114081440c44900d401d030b884 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 617120080 1250 617118830 617118863
    0x3c10050d0f33150503010f060504050606090303041a1e070303060f0b0702040506061b060106111506010309112d060f04031b15080f0a0e0712050c040504 67
    0x210001016040c5000000000c0d101521040041e81103021104041d50b81d80760702d2801d60008030f61003000703050000e00a0055103507015050014004e2800390511492411006c40c0191801d881251050080500a18100f43c07920f0101c0c8030103c54603d41c000554020426500c0304800340780e9440c0c18440d07410031903895a5060400508441d410b030001c03c4100380400707003405030381d650b04240d48506134106c4000c1450f41d2140d0110707417a405444100403040b00304520706440c009020a40d18140d44250341c2e91881026007202d0603580b180ca164210384212203800100e03a1551081d000f40380058010b5914440c4a8000c4010403080c1100303880740191400707861a50308604d1303044d2000800109044420030304024181c0c026039120310851100501103c0d034424503000b040c0012a0b030707900401001c190541101c008020160404a0813030f40c500030702903200002140c1e1541032003060310042c8100001c0518600304002250804140b0f001030307609101e0b88c5241c2031250f032170380200c80c4142c0c4514100d03044103215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 617121330 1250 617120080 617120093
    0x30c030f06010e012a0b0901020301080f0d0906030504050c0d0503190c02030606280b0406110607020c0f030a0c08010f06120b0c03130209040b3c10050d0f 68
    0x740080d810800ca4030b0700c24516a0740002034050709104520030030344040d51316501c100c000c0c03204100184161030400c104296480198081c42c120381e1840b043d1398604004204030b944540d403e00028000c06c9203104180301691096108560051162044030103090890300040c205200140341102c8507030000460241e184c43c0310f221050000c60710308054504446542c000b035100d480c014507240c0180318000b1072140e035103c400c00c0c0d04807008070308081e1103060707488046209903588540107080120700c01a0118051402c00600603126080700d501515424840c5400c01032849014400c103585403140800e00ea011030181c5260800070440e070b1000207440d8582d0401c0c40c05442e1154008440120444c0180c0003080b40580d499511414101109980307940743c203000c06100c5600b00c0007a400c804040104406c1000c134400e154001d07c0240a12140c9070030000c91503150860008c90034418032903040e410115a000361407882c0c0c000780e1801d5100046c54403500810035100080ea8252892641568283e080c00718 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 617122580 1250 617121330 617121361
    0x1211091f0506070305030f0a09020d0c150c02100e0111030d06080f0d0f05030703020d0c05090108010e0705040e04020a030512031608070f0e0109030605011d0f06030a030c0c0b030c03 80
    0x1016100142002980d89018110380801024018040440c000048c1a0a03484e070040650946c024180c0705012039a0a1100791402c0c68002c0600d6100c108000d8400a03006000d4061b00550040452405d0038590390100d0741d900d090010a0306000b5128440895101d0030b0029240c11f40b503062002460901d05149185441607002801040360482403880322046e80c40a960400c20a8038200969282c861210440091191400c83c407641403500044050155000004200f0300d4003d03a0356020b243d884550840b41c80350140d42c23200100b08100810081120101925680240010f00496000da0b603601e03601c2c02c04040c4030044d079600384000104490010b40f8201a9070b0717150f4034584030400b40380080c405402d003020340200005014961716000b00c107a2003003804001560340958140301c0395941d505030b01113407040c601f07508403040803940009107410000d80e0340500c02d0300014010f000ca815103840c140c40e5800341440039500070350742c0c54010801100e400015401060121440c41d41d82ca069010000c1454 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 617123830 1250 617122580 617122589
    0x60b07031706091308040503010510180b031c110609070314010b03060106110313080102250206040603090212012405030604150e150c07020f06040b041211091f 70
    0x51004060050b01c2d201d4050242c0d01994807044890080d145003031402841c0a1944902d40c503608104c01c1000c0c62815105210440e0440441710ba0709076244000300e001c0d80c2501e012281c05900c400c1d403a050444042d40e1500d00d950043c2840380e10151004681d508000040b103109445900004040040042100c2040c0700d14010000030041403032454002910392106208400030048003600940c000c14040c801c603070b51300c80741001c107401c0c0a54078884103010f5007141908090a2121244506075100c0d0b0f1480b03000601d038000e040501d45802c0c104213400030818460f00782c1c0c00c900044001228010240314100443c80400749071a000300c115040313041c020601d41c0000340a90001018480015442d1035042089015031002150800b044e000c03107071401d8038800c601c00c41500842c0a20ec91848401d004010450007540d004035208003080a00c821446107203c0c60490504c104801c004001400c900b02c08100d00c00c806600241110400041c0b1022043e14681c0c103203018010541c1594503540d80c22030040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 617125080 1250 617123830 617123867
    0xa0e0a080604020d210206010303120618020a0201060b0a020604020f0d03051602010e04061701060b04180906060f0303030f05010609151b050d05070606050a03020f0d030909060b0703 80
    0x8500301891181c8500e0050310090042603554004801c03c1904a01d420408005c846001d1107042c6120f00255106000c0c07109402080351103580c3d9241c10b25030300070340b42a01d00140000240414591b0400000e60020144a0842d56190004949103001000800c60030089a00800c101d04045c010040c000a117202050312a101b4042c07034500090f000380554641c001c600610804c0f5682500040c1d810b441c69092803548540ba240021800c20101c4564440c8110080002c00000d916a00d40300018491401403950503031400d03000340204821a000070030310310310952010644c995aa4101c25900c089074008402198451206000a4140c1d1051900605440c58000802481e05811400f400306a9110740200030250050300c120542c1424034800c0158003004450000b600030f10000c2080e040000102d442c5802c2c10310000da1850143d4a0b05c1c10359030001c0204464100a008000303030503045030021018802c0001c0700140510480c402d040043c4107929102e555600e0a00e401070200303103407030000c6404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 617126330 1250 617125080 617125099
    0x5070609081f09141006090506030a2d0c090b0f0108071b05010b030a0f0c14220f0c021015030804120f06020c0115081c082a0a0e 57
    0x1030a2003642d01d090040c0907010003d00d010361401c01215200b0040c83d140114800c120030103000c109654407071030468461072020082e54448904264807210ba040010740409003001224203040c1b41c10105590547c4c0d00071000381d48520550703130079118011680c030140c055691249c50700d90074140504019464482481d100030146400304029090b21000e182000038000c2c00c104050402074250310100c07803200020201d0740350b034240d858403001007002c42c40304840d00000003400051000003032101080e1203100401c0c520b039a10b021500400003505005064002c40d490754020b10454509108442054036607074003512001d10700300360450a607000d041c02030b100300d03440e102c040001c42c0024098905844041c641d100c030780030032030411040c00012054017070026840000c6251110f00150f000440714060352044d0100540d507001c900f0b40703465010003480380c04440c00011400c0d545c4202680b580c032070b4900a00010918586204000303501e007140203800760090000da50f090b0b00b9000805000b588038100c031f95604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 617127580 1250 617126330 617126353
    0x1107030f35030a1d0c04230105040c0507120206040201090b090d020f0a08120306090106050412020d020a081608060109060f031202031e091002060c040501081806040507060908 77
    0xc050340300440a86607480440420340c511400c2c0c0024014108004500014a40300c2140640307031000240303172a104620300700700350541010501c040c0d0040440c400c240c0303920b07a10b00401d21015004ea40962010081d0030461440050904101d051049505178005c1080e490584001350268003a9041a440410103200712900c1d82d80e5503003141d03021503041d54103884490405001c5447e100003500308104c14012001280c0703440c82d080c80076501c554000c81d2002001c1e60303605400c0c2c40c01d110b00d004108041c5003000b0020003504010001e00b14088c03000d407400c030300503a5401101d414509401d02c950001203c051080000d080304000c81409401c58403020007a6a19080302e440eaa00300b1884002c004d098140c0808100780d00a0066543c0c890484110740c0d407401213034000b044140d0100d60014803900006014400c0c181c0b000030399a101d114502040d03490141020019210140000c144070403000e0a168082c010301814061103000b24801d170000d001e01070074284080d1400406800405460b404008502c6 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 617128830 1250 617127580 617127653
    0x1e170901030c030255030b1e0d0203070302060d0f061509170f060103060204080d0305010f09020c0f03070b2403030403080f190f030c0c0c0e071107030f 67
    0x2e4004588500c000c0d0304101200d82519070713078000703445c41c1c0c41094010000c0100d41c50803907030004010403a41c0c10000e0001042c100843d101c080540951120f082416200203404d080c90800c02c03083c0000d0842d030481d130ba240d0014102d41c0c000d20100040316101c92040c852600384d4014003001d041d010182c41040818a68020179078a6144580d00110ba03030b00c50205403501e002d000042d01d441484c02510301668603802c20f4030180d8020310504250b4070a03040320500d964880c0c420f50b81600d00241e0385119007032421010f0700c081c2d0040d082a2a040c0074028180d0000402000205240c0d0b1042c110300a5901d8800b903070145941d0345002c800300ca0125041035140d1540d0200842d4203895201c80d11a0300c9036003120003202c0c81d001d0a200340000c0b045003c0c031f00b00d0390b64102000d0b20414005a806200015420904030340c14410000014415400a141401034045044043d68841400e1920140c1103d81c01421884c0a4080e4825109180d02e00040010710110100c0450203418100c891a4860440c0c0e4984 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 617130080 1250 617128830 617128867
    0xb120c01030902060d061e09022a07120b090c03030309031207031e0e0f010b031b03030913140c09030c0907050f0a0201021309060e041e170901030c0302 67
    0x180c10940d40340900811599900e0641c0c1c0700c00c814200422000e926100c81e50b0b8401c0d90480b900108070354189000070324120b0307070003140d10325154200700800114403001030188040e2404014180e5029500011034400f05180c5000c2c022401070101058038102141124100300c4100c1e6801d0007500704004001e20f603000001220484c01c40310703008030720b1640d40003c110010800f1012005046601c51074401c0300448a80001100f01008015078034940582c5504070700700c4484e01102074158120070381c03140320101c4250000c0c501c480098180c03841d00c2c81c40b00029035070028080010400990300d0701c0300c0c04c1c0f80d80304a0b5400d80c082c1e030920b8894079041071031300060786d03451036040081d2054601000061545201d201961841c844003181c80741c0714240c04170042e01035000090030b107170006044000040e5800480c051801200c1c0048a240d60f5030b1119102c41d18881c0c1400c11000303a00c14034100c80710005660303c00c105401102503644580322050a00010b0981d1084010201010f0040c82848002407040700718 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 617131330 1250 617130080 617130103
    0x1f020703210b0d030201050a050601020118170903010509031c1401210501020a020c120303011203081b07080306091305030904020a0c0803070807020f06010819052b030b12 75
    0x3940c0e02041e10a09680900620281160020803412040d81099015000b16010b1052070b0400c1c07259035200c900490885a000300d4298020f10303e40c80034004214051a10000c50a203010001c2c60600c00d14046800d4800c2560030003d035a00000f4209040d655564400e0392070034a40c0002e100f02e00f20000c264003c60018028004086984445003d038521041c03015906158094025501c80215500280d15020200607150241104510b1900c030120048120b030f040c4c0e081d05581c41d242c261282c03400c591507080208401e07500304c092000038409014050162040e14443c4420a94034079116051040a0070003410308900602841407590005102100b9a0301d40402528010f8844140820444036060304031000391101c14000305110720130f0b6102501c144180d400e9000c803045034184106940d9a2402485a0005500148028241880c1c20700030f2108850095003283c4511041001643d054805440c58500d480c110420030032056400d03004400c41114101c41c022030030449000a2034030b40c601841d1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 617132580 1250 617131330 617131367
    0xe2104060212090108010b160c1e050d05100b2704233003090304030303180804050f12061e060f060f03040303091b051c031710080f1f020703 62
    0x3a04184102c031004288802d0341c000660342040c0ba92b4031180d03d080b0013a004c1e100d000908143c0082020704010300c44a100e581d10000420400d201030805000411208186950003211007840303142c0040c82c215440b0076a01d05582c4126241080d2620780140c0d5148528010503401c0c2c0b100b001c4450f03001086011000d00130000d00c400300685841c0c1e00e2031074001c80c0d5010f0a071100110900c000548004003a03c15648a1344081014000b9613442c81015011000001d0020408000134011070426200d410114440071300f110700440303440000181048421a8403860103100001e00450210300c2144258210b4020351340358142c19000c001107103080c800d0680320307007807448000082000c040c0f00ea444000100d80110001c418140c40382048038400d032640c482c0c2032144800b1110301c0164650b144c850b204841e0f1544900e003d2080e210166000345000a0103d002e00c0c028240c0040c3e0983c00f482030311044500000644840d94010340302c030b0040101c205c004661140b0501c562000280c100e00c2c4180c00c3c10081c3c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 617133830 1250 617132580 617132587
    0x1050909031c02041214070b04050d12050702060a02012f12090a080a02210f04030204050405010b131d030415120f09111e0f01030e2104060212090108010b 68
    0x2908980a440f45500055040c4019102c14040c401c030a8a049002c01c6c580c01640d81c241d550b403801d402c1038082c03802990f520100d59500d10340012180461035404c5581428002c2c101400d50700000c0054000c1907034180540d4555042c3c182201c2c02da110480208031006141c16903c4e00041480c845010b4a440c0c84420000900490380d07415041143ca03601c954088040d65852001200080d00c0342920340c00708100542e0f00d80e081500ca0101000d903000030704198a034070306043c556000c00000d810040c00549181d5a2100d0b1238110f51507000810040ca1411070020500000d102120300388004007082c0070005070000d020074009010b44d000355010075a80d9162241c0c0c0341c84484540340c018481101c1c0007c3d92460f14006404101110305240030700c8000f01c40b02c01602005240c42c0080310b10000321140d001030138100742c061070741c040c2d0301c210445800c0354225080810403a62031400900a000c458812440118082001590402141d60b8101008803201d090014810003e0300e181c8040c06080c840c0e903c0407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 617135080 1250 617133830 617133877
    0x1060c02040f050408030c0d140c04060801091802060918040524040503041202061c0f060b18060a03180c0305060c2b0e031306120903020a0213091212050105090903 72
    0x90304100ea021021007802c2c2014100ac56054405500510906000c662170b5800040c071000203118410f0008034299045402c43e5407035081154682c404440c50341d0100c020f10244101440e1040f085200d1849100104071004240446441c04100758071068215030f0300744104800103002105403001c90303150b821414054605071001840c180110640c28109508480010030300c01070315003037004441c1ca2400d0030010103865200329041407007545a40c0c06800c050303108010301401d180008143d040100c3ca400111240700b02191050f000500e5810354409008500c18418481d00344440e030341280c10002aa454202d141201a40651350000c40c1852200e20b194020810903203074200050b003038002070a9950710302141c3d130340c500403210342d016020020356401c2c0c900d89504031701d10070052482c0e09500146a4005a6401c001c030104600350240d9100e0340341e4200c000046d610b002880c00780012903d84001240840c2801d0f0b0031100140d11903072007109200d00b40050060080200d9a071261005000903581481 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 617136330 1250 617135080 617135107
    0xf0d110402190f08010b09010c200d03050904050c132c0f0405060a0203071202070614010b37031d1605091b0a050703090305010501060c02040f050408030c 68
    0x1c03514020558040d445080d00c2c0c0d03e81c04070460101003029281c0000b40d90302c1e03100304955130103440d621a0200b200054000b000c1006030030310011004d4401d07a07907080c5103a00000302d07101d904100130071004a01e000c6845001441d250107076541c071540351100c560501500101c100c0c0444130307501c0fa61050306115100d1904005190240001d0100f1890803000340341803203030340b16009000c102c3d030960b05800703944c02007148040d070760007124010245070b59640c0c40c0d0340001084070000d500070031080703607a541c6d1540329610212000fa2124020081c0c0001a41c40710291180044da210700341a0030001c0c0c800b0311030400001c003d00141c84d221b0300d0f0203140002d10580b689464502101c80310400314940d1051103500d9071808a407046910560300c00740d580c0306450300c5081d40500840e59203006480200000e10043d02c0d1144100c014000707450091034444003441d9241c4450f0300f1030381c003a041000001c0e21510701c9810750515028203400342500903010401440c2907141c407096400040c1181e1324901e0300144040c4240c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 617137580 1250 617136330 617136337
    0x10207031214130801140712110d050703051f0f030303090f0f050c03010e060621071503051b070209040b100e15090f01080c061b0d02010c0207050f0d110402 69
    0x4680062039075100b01280c00c3d061000244501905903082c1068509038541003009a0f02a0210761a42c41c42980f00c1c0c143c080282213042c0400d01c118105100906519405024950258200c0e480029183c18004c68000c0c110884604401c4407a003410001c02c1000e85480003a8200c2c1d40614000403d00030313a01d0030b0102200f80c41d0001d440300403e89044000d008000c074030000c9080f8124000c008075400c0041054450004650040d88540c1d58a800708007119405801b24043c007441040d03540080e00c460340b450030002010080000a40d494081040c940315511001c1241c00600c0782c0142401c200b80c8c005000350344024001001982450007040303c841c3d52a00074009000c501082c0310f060303d02003007415020545001c400e4450102040400c440070720481809040e103c0900160202010318001e104003503005201004062042050300c0780180001c3c04000041c403950b60001ca03603c0030302c0100902c1c000c40b0f6005144100e40302083d00c41070340e50b00400514450b41c407503543c1d840c0d5140ca90004000f0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 617138830 1250 617137580 617137607
    0x70e041709030a05011b0c0f020915062d030f240a061d0a03080d020703051e0901030614032107060914060106030c0507140115080a0605010e04020102070312 69
    0xf1071402e00604206040d04a081545d103580c56494a4080541c17003103030b031800606009001301c82d003140c5030001f6007003041440e030b40804084a044902c810880128100c1e0b0b1100c030507010820700d107004601c034895036540d4a030b40810003404800e0450826112180350000c020f4544520800b004090103107201101c1d441d80741d40380c8020407400d689951070b080903021400c01e00703601c0c2040b100030348824220324203000e0920907240c01540b101e0130f114580303071200000d5110301804d5060003014050781103400644620950f079000d0300c18400c0d1b1105803000002d41075608640200c680c24508a0b580300d80f98900080b0a40d2101c2440c41e04040440300440345075062082c0400a0806418035030350106110a0721070600e8410080c50031079007a07a0340c4000031412200c0482e007500005000b00706c807030042031600c1d941c400d00d10001c03400080e01d04026904e600801c0210341c000072258001c4085002402043e104503801490f500f615121985080d6000079100c0c3ea2600004200005020341400c0c1144140c103501d1141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 617140080 1250 617138830 617138833
    0x91e130c120615080601050f122d071b0305070611031801020a0804061d010501080c01020d09050603010e0c25060501150905061b0303150a0503070e04170903 69
    0x860500140240900700d15010041d00700140000d0700c5020b81000c100a03281660f5120441e2104401124036600c404c04500e800074051000790709000f650140c5501a0b020300e907100d0307160b10805518030118080142031403420f0b446601004202031f00000302c0c400307580d140190f040b1540038514003661180100800980010324103807c41d4801c170300c012300071030040c11800d052400300700015078440d0907840707120304e800c00180c0100b0104000400310380007061551300340341402c1440a1204005405c50b04264040d02d00e81c0e02002080e2841e580500003110480780500e04a1b030b045e4140341c0070804c00c0c84103110722900e015014001502c0c0c8500d070030503107201d03c0c025150111962505403103a05950110541a6000c5203010000a8800f20202c00c2006521440c0c8640b0f034103a01e8001040f8080e00107040308403402c200303100c2d00246000240001c43c818122058103a10103e075000a00808602c40d420890203a03201d84014410908a0501c20754040c0d402006200b4140c501f04004196015011056406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 617141330 1250 617140080 617140091
    0x80115092703051b011410050a0305030a1209080d0501090608030a35090601030b0703020414010c030203040b0703121a1c0201020c0a260105060d06020915160506010605091e13 77
    0x8000c541b84006000d08403004034940c1281d103884c00c100104100303220003071843c1d004004428040d8003030068183d12941c101000a210381050325200b4960344a0b03000500600d640b20b0050169000911803d800790501c0c0c8003d6060214000014122619080b0303c05000550801400002000a40300c0c0e06108a1424103100754100704280c0c680c0c1d8042030100715000000c200004040c4c44c030920968007141c0030b21210503400c0a03554019203004442404c190114001048082480078040e80209011842a070301c03003511044030b0b01d050040764100e909065184000941c1d54045580c0c7d800d0050307400e092040800301200d06032006070725085a180b40c880d04a47c44400020303580d5803649449080d032400740d1002207202c141e0003030142250b00407200d0561000041903a1000f040c090fa001e803c05100141486980718501c2e0140d028682140304040080c45900e4081810400180480d500514007400e040d0304201a031800503010058040368050344000507401000e46035500000c0d03404145540004111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 617142580 1250 617141330 617141351
    0xa03060f0f1b110d08060607210c02040f230c0c120306010305070f08070c0c180905070f0b03010308090d0b070801150801050604090213080115092703051b01 69
    0x190180340710b000414103100084003203036004940849460580e9840140070b03034500c030403c10720742c02080003501e0910048625520451343c542124004c454140c5404840003001d1041000f56a45a56590141070a003044140880100c03068140d201c0040101040c03981e442080b20b89042c003586482550512400d80031000581207200290700800080c5e0342803145503100241524404c9241e490707400020294400a0000d81c46030140c2a540c40c86140360080031903035800e2441d1384044005012075079540da455242c08001082100034024000e04c1211809039103010401c0041d404148800760480342c0026a0040c540d60f419502000c143d0300030101107440c18075400c0281b03140e809000d103d42ea10107258403031152602807903c0904039500104070a140134240203142019422a00f000c0058a020800102e0b400100780206005132400e84042111949440004030950700d031501891410020020303452004030f04602104c00301074050924075620701e490214040500c19a0a281a065280048941 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 617143830 1250 617142580 617142611
    0x151a042c0c0a031a2416150617060103030f0c0807060b0f0409111306030515160813020f030709090b040521070b06061b010b010f020c0a03060f0f 64
    0x80705001a6810060300509004c0c403012040d444082d16408544110280241300f11813000c40030194910403801e00b407032040000d80f0291040810308642c03400000348030414141541c0b0400005001080403840d049152100c45500e641040c04041c040100d49074554504a0280d21a28420365001000e15a11350f200d003030110042008100381c13403152121074846142c515160282c81d40c11900210201504600d040070030a100e00c529060001054481c04000b000c941d040c030032009440d45a441440292500d010b03400102880c03000d40806221f002c5003404040202081c061502990640b200c100104040000038034180385580400011401c0074040010003251205d4640100e02c80c01c1102d003040c0024020f0380c0c010000071068601440244203100104850100c59500020b01615403460400c5840d440281501c0042c0100300e05c1e910703040e0110741c40d64044240d0300c40410a00c0034001d201500f80006044445c28440038181944039220410b02d0f01c00343d8004468100b6908080041070f14600110 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 617145080 1250 617143830 617143837
    0x120108031308061504050402030106050d050303040614040c0b0d200a02010e03030f0417070f03050910020609061519090e1203060d030809031903151a042c0c 69
    0x5440010211000203a04a00140341401056849002c0c0244d0311180d06220060900400990345503480341000074081c3c0705d42c90034241d140e003d440034640c2c03880d0030306203c01503039202c1c1c1c1e00c50a0800000304100111b01d0380c2002d8030640c5d06070034040341d0750482e810310500030b0096590b62080444e00710700306a5204510384001c1104464940003401006514207405407a1f010480d4407011301400c82c00000c00044145a00f2541c0b046528901c03070138200d407034450100324071405804034041040011529014900901145034400380c52005007018076100041e2516050040d000b8a50000180c200c150280d40d4040d244080fa40d07141d8550740300e903135500e9422010300800310506d0354501800990390042c19440303044a00c503e00c003900c081c0c0355440030b60742214070307030002000c400341d900050180f450a402c8408220402c001c50b5900031079121050169031200c0003ea6000c0340c1e821041035030b40706a030348070700341610112450444440401d54248034044080030103c00c82c820228030010801c40f00ba18420040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 617146330 1250 617145080 617145097
    0x12030a1b03020604064d16020f060d0213030b0a09030c11010207030212010218060a0219060612060f060605090a030219050306010603050f0705090d060b010306050414040516030314070812010803 85
    0xb0740c2c4101c1c1083d001c01c0d0b1b91207800f074076001d06550600c80f1805400c11920039101c810025103d6490100d840c2040c00498105400b0801100b401c2070042040c0155000c006401200718007080084070003644d0080c1c050034207688014160510510180e805a0003805600003e640140c6400c0c04544d249416034002e40c00f505030031605050501510305a828820103540074a50b00760010030b01d1010030b650459114040300c00071070f01c19403281d00200e41c1c2001d1600e002c0540748030315404070b41c1000310801b075426200e054014030308101090210200702c0c0d503400400000c0701d805642031019200c2520000c0d140710130036041250907100b44d00000405640c1a4401071040341e0002d884091074440c41012100c80c41408159648562641603680c041403084d8807007220543c050500180b0340303665101080c1520b00c6181c00303405006545c8208424400280b001c0c40311040301c006822806803c41d50090200c40d21a20700c1c0c803403000003007282d030300300000c1108071180004c0700481c2c40791079a55401c1455503640040321 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 617147580 1250 617146330 617146451
    0x12051005090105040f030305191802041b120f0b030a0813082a0d05070803040f090501031a0903070203031602010225091a12030a1b0302060406 63
    0x8445140600c0f41c14000e561108806a619605840840142a01800c3d00c02e08004401440c002d4000c075101b60b2840700c5c82c8640645218850b4010402101c0d41c401041e0940c2000344408021103a00c1000c441c0e180c00c54000000742d00346192003100040100000442d0144106022001403145000240034110b407040f50041ea001d8507040826100c40030030061410002482c2c00c2e244000d0103165000c0b05180d0090f003828040500c54894520b005070540c4444c50340c1d0800203040c0700e12040105024040c0c01e20640c184080d5256a0f120301032089400c150095800381240442e1a1308000c2c01101c600c20340083c02c507030b100c18210b01c1040145021240803400340c0305102544118118608000c0780070000c1e101010b4519150080e588080c010200c001e803400c00c0c1808501c074031135584003605810f022803000210346410811901600c5c04580d20f40200100340720b0000400040d83c0000c0403544141d11800104d0902d1100c0b1054045020320401a181ca507009030840410256110060786030054030003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 617148830 1250 617147580 617147591
    0x4051c0f060e10060302090a230f011404020c0a0206072927060424150f1a030403030c120915050c121602070b04060c0201020c010807020a0303090c120510 68
    0x2c103c0d0201c43c1d041c840207402125081c0001c00c202010340c03080f4002c142d01c03840c0031029160048040002103003214040112a403030001404a1404440c0241d40b0107000e860441c9010b05400b01d880d0f0303500230f170840240b25240008520003041000f03001d6001c00c2441d0901c0e600c0b0241d8150729100c00600031070b01e20b10800810780c50303260b4142030402d800c1d10014141c0041e2045803129101c01607011080c803640310000c0206030a90304540020710130318011fa554800841c0c2c0160900d400241c1007d103039440854410f000c94440040110240122500aa4507050003c0c2c0615290401c1e80d000350480100c03012185445500014040e060031210903040961000f0002959145d40f0030149011b828a078000310841c01e00000c07101d005488001030200100e004a501c02c036501c16003040c070b5902035000b40340007030000c0d01c40108558041000307002ca01d0b02400e140c1d8813403030501402540c40b001404041c08154540442c80180401601164041c0c4208903086500306052704015540d0185055454002ca2801c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 617150080 1250 617148830 617148853
    0x406020318072408040b0f0a0b1c02040c05040602150601140c01050f0f09070b03060d330203070503060f01140c0d270605181f02150c04051c0f060e 65
    0x110130740c501c00d661016482500d0b4450071094094010f00401105000791b69620404166988070b10103d10007101c951000c0410125205210a503a080f0070884280039081c401442115008074807281c000104004414050f83c2c0c42004a841c014482d40000210400103080011080c0640100b84203c02cac2e00b0710040c0c6a00c0320061000184011111651b603070704284024040d0607081030045030440310080000304038100c00e0f21640740410182c044101d11800419490b0b680000d100e031001c80d403001042e011070030340ca407140b40580a880002c10803032052041d12001090f0343e0240c040200300c0b03c0b001c0e0205445802029451355540089072280c004548402503d01e0300b0765610728a40c424881080b20b5410300d615111094401e41c0000403c48190100403442e42d815032590480b800040c1c200311001d05a0b000304074400b85c00c102100000228a401d01c1007000204c008950494007192015210900d05800043c2d5088489020072001022012444030a00521072035402181c030502d60003003500c6000013038 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 617151330 1250 617150080 617150087
    0xa030c080d02160b0a0302120109090317150d08130b180a0f03080306131107030806010806031f020c01021303111012050c040312030f180b04060203180724 68
    0x380c1082c414100f10f040b4090100c0d0f4015400343c5400304035405d016040c085c4410190340200000d070841094150b940d2600707424541d011401d000c0308188005e00c18002d0800c1402984156020112107008000d04445c5004000e499000c442d8000c54021049000584a072904d01c516800000800e00c44800c501c074040d0203181c841f9205049404002e0540c0c07a5614590b602d204036000280b5003a07000100b800b40650b200c034140501c441060200220a039200ba0710329014210722005001d5604000c40c43c0104121a180002c5441d020032080d1041407038171070000180c602038801c0182800755940003080000400d0901e40031103060b207200c3c9812110b80c00c4a2400d00c000481074a4004000901c0d4487c0c200e640140c80c0e002070b400c6104601074500e002c1d01e81e101c41c442180000341d1030700001d548007520300e1008128420703041010001640c0500e01c14564030b444910010142001c0c00c1240c0c00000b15008942508401003038403140001d07124441d5850038841c0c00c0340100c80c07803c3e03c050010204c0b2400303140f2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 617152580 1250 617151330 617151343
    0x30c06050c0c2104080a0302160b071e05010b0315010e010902070302061f0308180a05120a02040e0f0601150908010c0504140111060c04180902060906030a06050a030c080d02 76
    0x252401004110a03030800903400e02c03503030f42e8010515001084045110f401c1400301e5072032103009030000c10881c40302151084160aa65014070b2000100340f04100001d250b1a03920840c8071203001c040f01c54034030141401c5004010b1011a143d01d80300313807540ca00710244500809412102c0c00590829140c0e0303a42c28440c144d00c038003003000700145c10200010b01600307130440d07a100092401120107001d054480d07845814592007010008508400403d40c100103142014152016200644035800c004100c0c2281996070301e020400240320380e449603d0340003490f804112510a0030561004c40b42c495070755002c2050130504030000f000000c6c1e10f810000ca80c2c644140240c0700e0468141e80c81e5484e0920f020000b40b030300410f00305c50340d041042d0700b0503c84d101c541c2007000c98040e401c030784042c998031864100c0b400d0104a030142030040c00d034200f0240d040940d03503441c140c0f001c03d8015252180d8950314581c04500030102908040d91103480c40c080031007840684401e00c001c0c1c84038101142e5101070032031826a40ca55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 617153830 1250 617152580 617152597
    0x4230a060e0115050108190504030305011806381b0d090501020601060f17012c010317030402030a0501051302130509120a0905040905010b03150f011412010207030c06050c 75
    0x300078040001754400d000b0558400507121000d0024400c1c0010202554402e403030940010b9100c070014006c1102803082c1c03019613140744000b0081207140034054a611f10204c200d070040c07900055007a180400c400c1d905070345600d07000c0c0c01480d9594089045080b5500f401c03416081244a420200c060007801802841c0554005800400e0268601a421110041c5140c0060304200e28402007590442212421034007920f038a402566614034003201c0e81103c0343d28118442022911500100003203503041f0981c03c0741e01d0409908581e81d070f403a800400d14101d00810024144e40c600003c0082090f109101c49005e144211a44845200342c40030364400c0d50026208181e030394000c2c1c294114200c5080c4c00804418501e406c0150b60255170300c0016084a8050009803041d075143c40c0f44603141d180c14807a01c41179807505c01540c40c59003040e0401300d044c0201401000f03082000c032a1500703810fa03503c9803044960b04020000350340e2001326180040c20380e0710604c0e048401c50305100c0814554a902d030705550030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 617155080 1250 617153830 617153861
    0x50f100b09150912010608250b0304050307050a03021f0912120e011a21030706150b0a0e0f010905030c0405180303011e050a0501051204230a060e01 65
    0x4007071001085503501040c0a075030080030003000085150745800782e1030850454800c00000e2100c1c0780034802c60410703030b071007001f8043c0000904c2500d0800c0012001c40041e6508802c01c85c0d201e81d07452805c1071542c401c01401034007612610109900705907000a20707019407140380076403840d0002d4443c02d183c1668204180100511011440119001c0c400c070f0030300441411041d008148400c444a90500b11031821000e01034441c0000780c0c260103400e1a20740c445014006062580d09005030468668480c0510380c0014a015110b415060542c60600324090140c1148400d141d0303200500d11029091201204505010b010320000c01400f543c05890300d901203e1014000e44036000b009401c0200400b002044205640201070b0002100c0400b00003450191241440c054000d18a104075401d5440c65603000512900625405100a0764804140e4400038a100004080c1c1c0e143c0e45002c10311110700340c0003941440900780c0451b405280000e1041c4215021b45000c02a9100e46940c0300d0999580e4031100c802c1d0f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 617156330 1250 617155080 617155087
    0x4170d1403130206040611060906360d05030711070501320406020604030206010e040f030c03030b0306090d170c04120305071506060e0d020307060e03010b040f050f100b 74
    0x118051600541d808200c407844610b100c016a8001100c2e60010740040b00040c20084410f40400380030014160003a988c140200800c1c80d2054080250000700092200c07040941d0886100c90781e5456050106003a00c20180c1c2d230041c0a92600800c0360f00115051400a43d42e03c8003405079800201d5028140c80d03040e0344852210014010212803031480140100b074034980c0d00001c00740441c2282c00741018004e0350340a0082402c09044c000d1800030306801c040b241c81a0a402d1100256500c0c032403120042c0d050410002041242c00c040c1c0060240c2403090303400d40612020003584d401c000c901902a00780c141c0f100700079040981801c0703060010480303580280550401003400002109a43c01101740d05c80d02d856450010780b55a040c0e03100b0241210083d00689078a818442e40d03411208850103028150b0350b012841c0310343e80009039210f40c1e910520050108070403440742c81d900c0a401007401079402500621186c4002c400c800c0003400200c0b00c3d4040400581c01051b84403107082112012620816042c908 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 617157580 1250 617156330 617156357
    0x50d030e0105160c15140f0a0c15090b09060915040609020420071709031e19050f0606010801030c0e06130911030106050415122604170d 60
    0x140d542c040555010000f08010561000504200524001d00203128104904402010015200e4070008000c2442d801041c4101315400540c901035540380d40305441c0c8034440e11114100000107003089104e1240441c1495070260a000907110880c0c01a03440c0821180582c0e200c0c0790003074070380c082481c1c1400c4070844900810302181c06900144442030008100041d100d84d01d4444c082041d09040940e191120301203014014800c042496034506007c0c40d8000740303402c0101c0c00080cac075144103d44013000b124280716031204110042284101034050120120010341c454144266242000c41c00c413280c0f0301c544400520503501c5a0010380c1241c0c4d10441c10108603044c1074029100340d03001803201da044942c064002516410a0282002103030255280342c0040c500071040c0b6003514100d82107180518100b0308900840a04404c4000c100c80180360014641d2585103400100d40c405c410003403c0d200241c040c0d1500281015004000310707041030303203c407550780e4403030300069180c04499198070b021407901c00d070404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 617158830 1250 617157580 617157587
    0xd020d020d120212131101081501080a090203030315040f060f15141605010e01090c0506090f03030d05060a0f0312082802030907120c0303110f0102030406090b01050d030e01 76
    0x10b40064070281c2c0035003404040583e9100c105030441d0341d00d4003401d5401c441e000b80121400381042e40303802860284120f180400205410000f10318129040007260000100095800e5110348007540d802406e491317803400c0804010010607451812030340305601d0944e00964560039031240c84100c406903072030280d1603464903a00030b551425014a10060000a20302c6400c0001440010301051a815100c8551550700d07050446c211801010030070b4090385415940c1020403140e64082084a80858a10f943e990707400000c50561603000382055014070012030f8091510390303540c0049205000980300044059a620b45080440c1c400d4030028042040d048060100340e0310841e1810340c080b6012480241ca1481e03004102aa140b6400304642050b40c040306001c1a810280503a00c01070a42d403007544080c0072251140051020507100041c10303c03210241d40e900c0040144000f00c05034103075100031501e07881c090400c140034264520701120010713400320004c9254a002401c40908076050b80d01c01e00440321f030a0054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 617160080 1250 617158830 617158847
    0x31306020c030d11040e1e0c13090501030b16020a35190306080a0507050607050c0d1b0504021801031d0f100509010b061e09040e010203090d020d020d 66
    0x60480d80410007507060040b43c80d0040b818002080b00c08190781d58544071031070764866406482c03d10043d46581103400840744140100b50030007007a240081e07440b0751030703100c2403034445259215120715130624000105010503540c9030b510800941445480c08104000102d8884460369801400102c446509031059004403c003020819002180442c0c40c3d09003402000d0f03a40c00c088018003080703d040721201c45882d4140100002070402c6002803820a05594555440b0741c80d60286502400c004076a40041c0301040014644507d800b510104c4100c07024240a51004c9003903030741210498544000144a040c64800c807900400c2221003280b4495000300110040d2003408038403007800701955113003503580d601803000d034200d0400c01004049a02202d01450306455004110389103a902d04007030715000f5161a412030b90035512a02a0b01407000b0b6407181c482c0d560041c0100c0070741041c5401910800c2c40e40540c0214050840c00c02100c1d84802031a50480e40c50742c4d4000090011b03045a1100317507001e4010740d04c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 617161330 1250 617160080 617160097
    0x2304032304080a030905090606040611100204060909061a030c070f0b0910110702010507031202040306113a0b3601090603030215070c060606120605040203130602 71
    0x800391020410800240c0070380080c0c0001265800450a410030141c000702043c0040c00c0a1314012042c0c03610100040150146104030018000b0600034110410028840c036003402c2079588086444a171078100040c14410603020700708805140107004a446115023200078a00700304d0b03503031151865942c000384a283d504a544201d801c0c000c03142c90200003424180885108017845401081c201e51000c006906503081202248042c000401c84440540d07840801c0341c4895403d4107060b03842402942000000b803040d54009881145480c14040405d00701d0002400c015078a2044001201c180e9800003440d044600c402030020b041d2200601c11600c2c1c140c02c8400c240d40d0042480c803001190f00d462800107241c0b03040000c4040c030700e041200d0710144502c01040c050910441c04000710340c20350f5006035580c0709001d1043d181020480003d504188603039940b000300c50340040c0900141d545c806006d0041d605107000380090a00300f217000306060600b403080c0c134810f0004079000307a5048840e480e0030f4000d6102003c2e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 617162580 1250 617161330 617161367
    0xa0f020f040c2105040f030f17040507061d030709150e0a0c030c141602060f0a180b13120623010503060604050115121b0201060504230403 61
    0x250401d54551182d880701607120340714402c00920b01049502101e188900c07280c80c05251800f44408240d0304118441c0d042c0e49800d12600350b50850a00b0b4950800318600d10040815400420042010101d0303a982240c05c0f43d12383e04110051151000883c500390f600007a0590311105081000e04ca15406c01e034102103041514450145d215043c264403020101d540040751500d810910f01801d030f05201c3c445032400107181a100c001c0c0c0b20745a0b82018881c00c010315401c13030003403034a040541d6115012610031082600089940315003805001e03005000b4410654801072a803000020a0162802243c018170081c3c404d110a290400a0315003103510603904c1074506907a103e1002c01d1801030080300566108103c00b85521a6240004051914000601e440e0042c0e0401c001005140c24040d4584140c2d205420400e0742c0d420006240c0000300030420001c80c02a01a50503030100c41d40660151003a10011f9500b0b21007042443d0000125100007156502010405000980441d10034411520003001030f45 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 617163830 1250 617162580 617162599
    0x3090c051201020903061609030b1005060c0607020d0807020d05030a0b06160c0f0f050d11030129030a0317040c05030a032609030a0309080d11090a08030c0a0f02 71
    0xc001c0344590410380d001901580d030004a82d00745140401503298000d00c441180c3c0c548051040c801000100741d44001411070003800701151480c00600d1001c0042c250240956440d1040340c104650b0340e44080e603c6001501850300134030301071481655202d10421654004204502c0e001c14101c81c25440100210111075403500c1d4140c0c90350b5100020071100480880c490810303002c6060090600003c0e5100c502c840d046814100840c1402d0b6120300d084400841d2420300914070381c1029541c0c4402e10b0501a803551910404402c818240d100c4000d0300c4070042200c82010524000f403580c6ca8151140140104001c034249225100a805a441e407192203010240b00c190b9490000c01d01d00f0281010403400b140094403041030445840d40411042424404100c0f45030400f461004c0c2c0b030303115503034132030042540b40c00e61081400000e008a8881c201d41403010446001d01142a8020f90842a0f2043c03003040b04130000645403100205a038160f01c400c80c00b80a45220136585c201070401c240400720380241400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 617165080 1250 617163830 617163839
    0x30a0f091205030a0f02030a02120901032c0106050d0f021903050a030504090506100806100e030a0602040608061f05031003060c0804050f03041805060a0321120605030d03090c 77
    0x100d01d400c088910400c011501c5001d0210040d00c14500d40388410115030040c007203c0c04c80d503400260b4100141d0035400c032582e107240e0a00100d014116010355204446200902070039041014504170340c40201c220020400e141c1c0720f0b4100b101b4507440260242104903107000c9d80002d45450354445c600c145205610b49c9a4640c1c035994603003062400d42c2c003039003c900089800c00c0810024080c0650000c01200d04a03415854500094a2100c020708514003c4410040100c0b01601809545104410003012148440954a4000e02952250040c1c00006003080c1c08101c030b43c180f40c000da120380c2c44100e03030303681c1158120032044500b0340006040e140320b407419031000000700d425446003003045040c0307503100d01162806050180c500781503130300e110b0002e80c0200000c100405220a5a6a2551015801058540b1404001008141c80c1e81000e0141015420b04000300319a4000d41c11400c07490381c8600910072078403650182182c940d44216070b0150411201082c10b0351081d40042100c40c4582c098901d82510b6 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 617166330 1250 617165080 617165099
    0xf0903080909220620041811040807120c06090806040f060209090a0518030421020d080f040e091f230115080a050601020a02060d06181a0a050102030a0f09 68
    0x10018151307030301c5644d8000b1500d0089003100300700140d01c064048500d80303440c041d00b0401c0094503400d1041440e9a86a07180c405c066440c040350020460001100c01041c1c580c43e075040c034408403802c216916001014002a07441c042c02c49041242c00c1c00001d00400e583d980c80720700e01c01c1c2e40d5a00441e80e15900704140815580c0d000d0000e4040d0f424283c000407503103072813098140070a504204e4410035510a120422200221300306050fa2480302c10519041240107101061a080884074020801000400c0f0b4089404000e0058800c59441494003619601c40d10308050712a01c0c0034200991611038541b6880e2048403540000700f03401082e041200c01c04580100c1e9626595003038000000100c020054003003150783c0324190f950040d0204a00b00071500306240041d644898240c0c0082c00b4603804105082c50030031641c4034a00070b0038140461005070340d060480a00912000990710071090890000040d43d007002c2a42d0713429030300180c000750f207071295200050314965500c0f0b019408200f501c0d540401c0c001803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 617167580 1250 617166330 617166391
    0x1f0f03090b0c04150e0f10020c03010f140c0c07121a0406020c1212130c0b040816061106150d080c0a0c1203050921010c0f0f0903080909 60
    0x1e01404a440c0e504111355141c020501a490004008030b50704402c4140e6121a07181d4041003044071070040320b441c6200306a040c00808070700654554a0070104004000e015040084a500b041901d007000c0d9540e400300456074064001c030030b11903602a0005224441c003004400e10b00e9409010303411007031602e5030407082000004680c202c40d400c4d00803a03d103850940410140b81c422410340d68450030241811581105008014002c0140e42207242401c0c0c10310134001014030117132050385c4013199a152120440c0741d0f0780ca403841c00e080604031004070024119100c4c00340710708800c5114014101945554404408650f42d414501d0380c420781e000c40f45400100c8150003031440c501801c0103400114030324201000c40040c258001c00d400c3d007810401100080c1d000c0300703c40381c44000b11080402034217604c921b541007103441d03007113500c15621300b00c0c1c80a003107a0007140400c984130840d51003c060940017802100d40c440070f88401040000c0074071900b00b1503d0a1481154040040c0c011640b9a400180c4480c45254 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 617168830 1250 617167580 617167591
    0x806010e1c05070f03080d05181902091003050c1302270f1f030c0e0406030f050d090b0d0b12070e0103060b18040f05011401091a1f0f03090b 62
    0x50074414441008000d10903900141929001d042c1c00910b1030302c03a0040d92241860880141b6074540001780d52220040c40203030b00c100d41d4030458241e000e07a580d2007103481c05040c0f0b06a210b41800c40c0026648400c040703d1b0400c2d203030f01a0152592207864010300900c012204c900d04580d43c2c00b031140c480c800c605c04040d000060406020b800010030b41c4020b01918000c0c480d1468042c100307c0b01c5d0180a28030450f400000400d152500040700405168101c411041040301c1d1580039003804800028020541114410240110190b50302c42681010581c0c40064a10540d010003100340150350740001d03c0c0c0d001b24510840501410030f4020040380003410108180c00072900d00170280c005005014892252800c010000d075510b2480044042c1982e1010000030001042405c0c2000ba90341003140a4001d1541c00403a15855002d9584a000910281518155808414200f100c45a016150001011015982c160320f100240a21a80201c81c490b0040400c2e0f0103042e00c4207110b03000280c4412803a4800c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 617170080 1250 617168830 617168869
    0x92a030605091614090708070302131203180608180a0533060a03060b030c09151306030206070204020a051603020a0c06080609010902090102010612050d0e1207060806010e 75
    0x43c038a400885400d40c064225000c500c0e0b0b0f200781e03c1001d8075141307440c0350884024142a4a640d450803c06c80181c854800207140c4010076040016010300205500b004641c800c5e00c82c1c03000105050002004c00c1141d10400300043c0030b040c04290070f20011940d204c2c4c0b9060800640d440717000a611542c0c50614241c00208803101c242e114141e0140f0700403105410750680d002c203034015080407070000d940b00c049800090101035440110340c065a03810000070706c201002130183c3d20945405c0356208130720040044240d02030100d012005203d840c0034072401d406d603a80104107905081e019002d06c002134010200b50000e00c1020412150184114603d074044540310764010402e00c45945001c41441580d81d000209001c1481e05100507541c0d001070140c1950002c03000140c58564260040f40900b100364080050780e0f050b074501d401032000118400c3e034014401d031513480e04000c41009106108003050074003085504085414400b082c420400d00360000014501020b81420107070015a02d50026056400c15 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 617171330 1250 617170080 617170093
    0x6040204051306090b09120406120c0507050105160e18220b01030503040312050309100e03040519150503061806030c150304140304060c060203100b0c06070210092a03060509 76
    0x1440e00c100820347d400300800c0c074504c1c2010b1420001a0400d800125201c1201e81c4441c5951480e074814000d03a2100c6400c04002e2100b4200309000c050f11204801d1080c0004000c07403411078060034021044540b2041510352441700366a4441e005d541e01f40c1583c080783c9806140e08201c000714510091540c0614083c0020710b0754ac52452401c0201e86008180b000b00f0301c0000d004004112101042c102d0204105031008101c10082c03100d258103610403078001551040300d840c801482c25600c80000815070305032110850214010f0078065034203000c2100c10307036030000b0351503240302010b8a00c010f4680c2058002d02198000d4410000203416180c95684a120546c0e0110400080c480704a60a0403041d101c0c0000d903160504007007000303024043c81000644490740000c0416490017159030700f80c00600138a84d4040e1541c044250180c1c070740c80162044001486500c0e05a00310003100d110351101240d100e480704601c41002280362180c00700c4161030030885000c08000201181003400360602c00c10240300030308a17 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 617172580 1250 617171330 617171341
    0xf070507170c0108060607140d090602151003080717040311280b07050c09010f06080c0a0509102304050117040b010905061c050705040f050906040204051306090b 71
    0x15010201c91012019034090341d50402c20f070342c1007400a9000fa6054035401c0e074610b01c50910040e1915013100b0000306218402c9280c4c1f80961008000042c1e034131035426180b8504104811200071902943c40a0715044040010800144904000c1a07074a1041d980c1400c2d501200126070311a40140e03006944841205421a40502d00b0f40c1ca0941214088030101520b5603242032000e001d0400c90103003805002000650209009041058890310a0014042041c0e0740e102c8200ea42d0007445403080c0c1010421003030205030168245025a987d1040703d591309801c1000d03290421148050020846c1d091004119100e04040303ca61074060074080280c41040e81c030f6142c000014441d585103010600d4002070103041c000052148190700381102e20741440401c0c04c2c2ca40340000342d01a54010300d1661800744d001204010454042400c0040358400c8a08008a20a04072040c054600444002d043c0d60007400000d40145401d621158021080044404e290869513560908490044d02d0695550480f20100b01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 617173830 1250 617172580 617172599
    0x1f03060609090c0e01080a06092a0504060c030302180423070c051903030b090a050a061205030703110c060d0501050310290f090705090406060906090b0d020f070507 72
    0x24002c18800307900300185a05100010300161542c80303464108001c4030040f07010446180c01602c00350880610070400e51258010079654403d06044a84d001841c6202c0440058000d005907411900b168440409000c2c107030350102e000751f11040340320020703841e45800c5080548880c0300d540710340b41e00b1885845400d5110b00510250b1007000308060200012281018001040807440c10b4031200184120382c040b4015240070b501400c01c42280341d8001d4052010000c1c40c5182d40c000740d001f0114034800300003164960041e55104d2aa000000d40075034020803d042c0000c2c4950325034019103203030b03500761898607000e1400602160b01c4100c400000c0745d15003005000307602d000d00a902d08448062801c0010300c000c59111240049070b1000d044496401c02a0a180741e11034596101400c1d2000f00f44240510304404003402c160050f04445004520308000401c650340104200d00030b43c1e503251600300c06145000b00103032550388403450300b1071495000d2141e2041100d0302e401400c00d0901c0340f405403110500703242414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 617175080 1250 617173830 617173847
    0x60509030c0f0109090906020906070807350c120409021b010501120b04080705061312090602060c0a03091a060315010b0f0a180603270812061f030606 66
    0x584103400b403521085060fa08002a882202c0b11240017160444a81c1400c4000b805583d0005030071000000f4200304011070030004080b10b52091201d485507490a420045d2241c1c00407c544009408002c18a00c021407000013424003000c650301261140c0004400340c255940142c1d01203600700f600403545907100308080b082d003c1d1945e0100300801256250201d0382d4921400040c024000540d08408581400b0b140e0080f2000d072030300300c4d007110200d0900140d0001c41460a14090310075a04036840021614401e04118084480b1907000700303599120030041201a0b4410316424040c550340e0308a10b400556814140071900c1180c017120400c43c9848000e0605104c0444200300081482000500140d01400151400c0784800302180e41c0b1a07080407420f07140f4030105600c1c0340c3c80c02998030380002c8a070342c96000007030010200d848032010018140900888080d08500080640405000b000e108609031407029030300072030080c10740c0c2800c810b01c809000c082004851a50012b92034000c24410160403120b030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 617176330 1250 617175080 617175103
    0xa0f02190305070314120a0507030b100f090f0e1503030412060903090e0901090311030c102403110103060f030f030e0a050406080c0f060712210606050903 68
    0x585040510034000306444111510020107001020824005141c801c600401801c803044008598960f030000040c4960f007422100322800070700703120008240030301c2400b50252a010203003c5101000303500d4000c0c0c2d40040031084400c100040028002202e00c0700080b141c0060120180c62805400c221f61165281ca000d02c102d42e020b03a2040204202c042d1059001e400b020782c204000041000c014a000c40720441c15a00101d0340c10003100074410044010741c440705c0340038400c2d100c07008400600c040581c0c481c05000580310f020313000740c81e004540910350380291801d103080c00f800d015807103100d10074001d01840c00e4000365854203803121404420b58040c07017281d0141c01c03508800fa01c090b02d1582c0703006a00c9922003004080201e80010301c80151540c0929001624000744203000d900e4513029102e5440c400c0c84401846000140c0504949040000458031a590000f000d03203141400c038201540c005e158042843c085480614080400c00d90a10912001d800c05565031580c5440010405203040d5007581c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 617177580 1250 617176330 617176333
    0xc0d060f0b0102070303022104090903110f0c1804060902030a2906151614010207110a080a0f050a02040203071106100605040510020f0d021e030310090f0207020a08030a0f02 76
    0x8217101081c1c0001d0301c0301c1c44507600704101000d882c002256641c2d40c020b551011540a062241310303c10036030400303415150078150004481031210780015003503507040c1c1c0c0310a80e604480c0c8515524804040f01c1e040700c1c7d0007401100042040405640803d03d483d048420070b40d22441076551082141c000104111004588038000da070300750030450000f4a84c0c401480c5900b207074410000b89001c950131051090700702e158120700d80d10901664034400501030341c0b2900f4202c0381c036103c00c032400c089840c0c140950070540706d00c0b000903c0800d0044c1da446001d54250707a41a50030340324407205600142d40d07900055115403140ea546002502140c016203191010140807034044100d41c1d4400e0000580c010180c070103c0302c0454010350000c104d1842607040c201c8145600d84507014221146140c950009006c00e0f0560034078803409207074403031200f2007a140d020944100901401d005800c0091945580125001c004e00c4100140f8050880e8000740725840158003507500c81d00003240c2010087e402c41c5070000000d00b10700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 617178830 1250 617177580 617177593
    0x90706050c06070e0d050a080406020c09040f0204110d05041b08010c02210403080f0306030c011103030c0d14070822051903051207050316030e030a08090c0d060f0b0102 74
    0x80041e15014001c3c001c40410090001d603030181ea5440d1031400c40e10750081c0544510056504004101f64468012007001d441103822403c07040c10401909803040c1e40200480c00100080d508001c05010080140c5104000c24428807000c0c035554400d190081d442004007050100400410f8401800c16a01207615a40b6155401c3c0000e5008140078140d468000b074469142181e07500710964500880d00098645600850020540c0b0040001140195412000c58404036585c80044403080e115040300a101e4106201040c1d401d81d902000d006d03a0f0400701404144110024951220b8180443d00c84000070b1114081c081d00c02c48032102c0440c94034228800c940c241e0072a0303da10740d0301c01407001d588903600c404420b02e90502d881401511601e405c01241c0c40030905000d0300c002e01980007a43c4801614014800c0c0b02c420600034411409509503510103941841a80f0b4415a4041001050058a4014102c0f0281f141d66401c200403001c40c801c56000030741280360104001241e03240d5a0301e50540d402074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 617180080 1250 617178830 617178847
    0xc170c0405090622050712020a111e1b0616060c09060525020607020616150204060f120605190f0b040807150309020306150405250f02010e100509070605 67
    0x22841c10130207000e600340c0429a83c9401d03104840800495000441c82440882e00141c2c0c564480d01070134641c2030100443c0e1141440035117070045509051032109441c0c3c0108140c142c0116881d50710078103844014101e505018480d100c0c422150900c04044600690301c02c910030b1810340045400b00036010b1490100c2c109003c040c40e00000440f1445000e072401220b105402c00c6541d01d80c00c840c034066002c1c09090301c448030082524501e56400c00d0407030303034642e041d0030074070700c900c090700c25213003110915a04c08180040840098a21001078017440e01d11070b8803581e01145a880d41d980b410a018124001807640500e00340e1442803480107600000301d4500e041000700030050380003071180252040400c0006604000c48400c1c0d0040c0742c08040290580224030421894a6501029461003241694148440c1d41c0b20061081020020b4001021012075000f141b11094464014403603032540c10300000440d240703000c40c2c00c0c0c41c0c001c46549444d6041c5d11034003004042d40081c003564006040600b0082e080c140074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 617181330 1250 617180080 617180119
    0x10c0201121b09080d03270510020403050d080708040b060f0f03010e03030907050402040b190c1406240108160c14030910080403092114010c0e0a050307090c170c04050906 75
    0x500b0080f510034007c042c00105000041c402410030201d02e040455440355030740341040c3c480130081c0941010901250002d001c69000c0c542c4d05115550100b140009588e48004101c0c8036808030020a4000c0079496041c03426031000d1048052400a1000564580c940361090368904111a005a806140180420000010a2025100e01540c01c6000c0c03042256020f074100c030448020354000d842c00c0d00081441c50480d902090141c0552207003200d840c00140c11101b4030078000c241001060008075034170005840a0102c81041c1e814213002e15020040b10304545810170390807081501a4429080081c45005610b00440381390320141003800e1000c118074042d1005003c4d4030f5244695032030010320a0808041d82c1c400f0700240552540544051202c1e0105200c00b40280108003496001c12002000b882c120b1814134048022a0002801004914200813030480507108a003004001d2004e81c0000c0305000410100f190700c51250000c02d2900e4a1400301001441c00c8043e24243c001c210a28241229030b40c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 617182580 1250 617181330 617181371
    0x6180f03350f060f060a0903031701081011130603050114030f150402180c0a09052d041d0a03090914060105180a14031209010c0201121b09080d03 64
    0x40b40c448a03000e541c0d5507010030408148440a60b80c0311a0008490f52801d800600d25400e681c000c0da6694841e55000e038002d0104602801859000e50203150030344144a040e4005c5c854524149404c0c1c0d04103400d1741007034242c03074200750000d20100340c4a4005115000300003003040901c0c00220300815031484001d640325200e0034284c0070b001701d00303802c580041c00350340b01c002c03010284070070b050101e00c92840d203180c4400c1c0c00e4001c2e081000002c1d1a05070005800d281821540403510620b140a01c9004080f00e801401d50142420700c070b410940399002c0c02d0600c407001440082c629031a00c00380429111354070313004041707c0941d0854480c0398900402580b5141c011421103501860a0918030359a01c00040826920942c80c2402035100c1d2807010f011500440000d16510132800c20303030861341404032200e400e5940d401094105800206d6062040c0e003d503100e0048030107584e115800001e0100c0100045503880c440d207100c5080410000c0c06c4c100494281000300b003484c9415450104105044480494100c58 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 617183830 1250 617182580 617182591
    0x6040206030123132c06150406092a0906021506040e06011e120203060c1c050f0708060d0c03171314010905060a0c06180f0335 56
    0x1074142e91111080c00c0b441405a000b0b0100426041000a280740f001005e007240f541c1440ba000e00c00413001003a140b03110744c00d80f018010f83c0c0180c4500e980e4412488040c90090042d01e9125480e60380000302094188078050240c10380c2e0032114008000c50380682900030510140104000b0054010030409901080c12407103e09040c85894440d220000041e0181c8105052020640158400010880c071600d0074500301c00368000c0c201a12036514015440d440b1481c0c1d1020f505a000800000c0070a6550401442d21100300041c0011450a05902da0b040760011110319140c0486c9205001005030040c040e00c2c0c0c8001c0480e14200700f04116540d0258059451000070940c142d85200e10f101540c001050322001c0024581e2866600d640d05002e00c0062601040740340844c81d1150b0125243c1003840485030714148549a5610f010082c2d640c04000b00255604454106116031185000a64a03120b80c10b50702c0c0139170382c1c501007840c2c165416001828000301810840d800c80400320003076071110541c0ba42c000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 617185080 1250 617183830 617183849
    0x901050709150503180f060612011a06130b03130b0a02520c0f0e13210512071d0108040c0506040308071b0515070309090e010c02010e060402060301 65
    0x1e07207528140c074098461780909800d65010b0380d00018800d4200050943c8071740c80441f00603049038001100a403c83e4486100600050a210110007507030805c1d10080015001c01100403100e03540c1c1e0000c00078170380c006450003041e07c9000c51340e0780c06006242d0051600b02d207c000b021031605610704071401000c0c45440c80c00180c4c010b1002d020200581c0c04010807800c40c8080703104400b8040e03040b4408000c090808040710013200700540492a80c181c00340c25402d417400b4502ca400b80752510880c4003d203005800c0b08854410042460251044617411802200c05803600c0f031540321b10b481c01108070980b900504c800d0030401107410100034002c4051020354800130a081c0000d0684072811300170185140c0fa04503580041c0c0015000003000181b1004150302e90148086c1c401407104050464118001846074640c030503a040f0b210f4201580700d00041040512a080881040d0f0752060f00d50140c48800706081c90903551030009160302e0b5028004e8200711284c84010f0103651400fa0b002030100e00040c05180c0e0403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 617186330 1250 617185080 617185087
    0x70608040201030f0e030408151510140c030d0605030114040305090418020d0f15050126012405040e0726191121121806040305030309010507091505 65
    0x1070002980c04100581706040030349903200c1d220080d20b541c440c0390111a20701004184000340b0351442c4000036443c41c040c01002d9103640c203c181da0484503010782900760900007004000601d8011000c01c000c00f800c0f480f101d0040b0714589400109408c590030451214600040c400070040065846400c5a8a11030100c0b4005060200e082030031034860702050000f5041b03801c141d5117805000300c2c1601c5070650b41c0300380c0c03405c2101408080d00a0a89800380f0480861000c100420745001100305511491040c0e08000020321805010a00d0203c159018100245813010141801582824080c0c00c10490000e00184401c2e450900c40700c0d10485100c0c80d007641d013041c204000140c00d0003405104040450907000c20103210f0642000ca4246058540f4a8030811450f140d580b80303010081e003c0e8815080b15800391000c040e2031444241c4651011041e990081d82c4d00c601e5032115038401c009030003c1e40c012002144c41c2d10385600c0c10f5084a001401e24800e001c80c5140400c6080700d680700000c0c5414083c41d00c2c0c0d85 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 617187580 1250 617186330 617186351
    0x60f031606050f0d020c150c0f1c18120f050408030405130b21011407050304030804050c03030a02010608060108120a0302070f060f090b010b0a0c0201030b060c0109080a0905010207060804020103 85
    0x70f05000c1c816a8990301030001a041018500015407080398a44000030360307180741c840f4503441c0d10380d10503420801d16680045c0917800c2070b0020020031007440341c0040004509500c03500b040c03008554510504031000c000301444010740301ea0040d400c100506140c20f0940c43c150409080c56613a000c0e40c81030500c40c0c903505840b80415201500b1441c01004007030000e141400311100c102855480c02c07000c81446600e400c80280a002e00d48054038080c4a280c4c0310249541c031f83d918201d80b9188014400c2d1507074440c1c0062841c00d03403010002070101c001280d0000800c3c40c00c11000900701901a8414450b56100350090403026a00e8411031385010320070b050060b6196094034284060824004000d01076a01c1e001901545070101d0704640e003403501c00c070001801a80c841000000c00d001d440c05281c0003d000e642c00310010350180d40036400d80078005124500348400240b1003800e40d00d16240c03c4076401c4000c15844040c0303401041c50390280070240054500c05090190040c841c050081001e410035460303040004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 617188830 1250 617187580 617187607
    0xd02091008011104180c05070b100305030a020d020f0703031719020a030c020c014122080303161b060e0c1e09071124060f03160605 58
    0x1000300301c984000d102d03114a184401d8a40d41107807041030300d040b00c115034145d101c44607841004215a541e484a03414081e03ea11350094000700200070000c01c604010000c004244104050003890055034002c2008a20622000342064070b400c004a0290340005010710009410000050b1b030080f45660100c00395580ca03500c01006640c209040d00900d20002e0b1070b100c601d0b41030f000030064803102c0d000c940c0c0100e43c2170700460307800c00c2089041100129060042c40048038400794601d411415840c42784080c04030b0b0040e100694040b881c0b04030040e0240300d0995100d030b41e09800000130f06003070f0091411440c02160a002101c5090900400c01c880be002e03803007449052441045032242c10240030403c3c001103050140d0380e88402d030903940c45828080c1c5a6080110700c1602c800754204041c21b01d4003580c840395000c0d5840c0a00c0c40311890607004000206d1074010042084010b410441c40c030610440c2062418040d203402c030400380a00a4101c3c5c0c1021510005c1d4452000071600d01d45042d41da03c030400303103020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 617190080 1250 617188830 617188861
    0x60c03140c12040c0e0907030204060806091209030a0c14040b09040b0f040f141f060308040e0903040e09060a050a14150307050a060203041e0609031b0902040b0a17060d0209 76
    0x180f0817072403407006100f5195400540c1e98141c038400d47e01008805d407502405a0348250481e24600c40b0b0b0310202d200c0016000841c007400e030b13494000e81220920480e40d0703201c2c0210b01103a0445440f1300f4140e26211240d1a107401403090405080da2003404608007902d0f00e00d034000307000b030681e0052480078000c20100100550703174500e415040000682c0c44101501d4840d101d040c51403280f4003040405241805d0728030342c0c0c4182c03001c982c1e00c11f4031546480d00c0e10354026584940104061040d0005104c00244140d0002206115a0300c52003d410a460b001c00d0000131680d01400341c1083c1c074540411602e41e50b078207841154101794504918000804400c00007494401103801094101011a400041058000015106465580044441070480c829030018009d80358441c0000084a0040c01c1011900d02040500352486040910303494645074101c0506030b81c0b0035484044007060004441c4e0040f680202c078140300f03032264403405000d801d02030000303140000c1c0301901a11507080f46e800300700c0a40420048 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 617191330 1250 617190080 617190089
    0x705070306050103050303070e030c01050405150408060108151003020f0918120406081b0a11121b1509030301090f02070c0303020a0c090203100b0c01020c0a060c03140c12040c 77
    0x203002c40d603103d2902c141c4a80041d106980840c0c3c0030794080003e4680400d9901d034140301a55038a05244c0f60504100550f007907c901e041001101300008601c0210a0101d180170305440350040c05019030f803030812146800d00409440303c0c07254a140500060b80c485000d0542c0c80701c100d0f802c941980b50b0345080b50b5035001a100c2516030344a8001a03110100701c0b00d01801c04c8031040c0d1500203640d544d44813000c20301101d060700005800e60030803203030004c00d0181b0381e10803903c100c8104a40c5c003d000f4a42240c1c03175500420010780718011400414500480c1081483d0b90941c1d1441441c900c0d04015001641e01d020601504d500d00383c8444c90001c0d81d40c5543e0641e900c0a03008a6440c5041c2c0d92410701039154680500c066800004008010400c444203000302c900541e00d0440000f8441c3c60803440750040d4004e410b000b859550200038806005a04024a140c00340c0202030000341101e00701c0b00903040310107a1b5000b00600e101401003200d03600300c40045c0d40c10303484030707030014481c80d81e641c503143c0d0b05079406411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 617192580 1250 617191330 617191343
    0x201030b03031909051003060b030408220308040f090b1e012c1f080103030806010c020907111e070b2b0905010f0509061303031b0e040c0c0210030207050703 69
    0x1155603080341d04c03008040071140181c07044440d9111124045040e41e106003c0c4000c50b84080001c1400125190028920b4900410f6113225645d14040d8800d00c014482d40261089480458248207100e80c0c0003c090040000c40d0301044103c0c5884003141c5404104100700d0010041c9615841c00d69002d6a04904002583c9046608015403882905940300315009480c1c0111048030f0100c40300d8941c0c0c00f00400c4ca1000b41c0711240c05a195513800c9520400081c5030700d04016000f09100b00507128010a58080e020380c3e100c0d1982110103c000c0c51030502c01e0f1800d6140c0c400710300603211150314042103132002c1d5084045041c0e680c1100010700c80c00341080301500351a030079110000e41071074070590b4090400940700384021b01030004001040015148151088006070308208003203000014400c0e20882018401e090200e07500c081d144101165001e841d082c4808950303200c402c10346500e0710b807180d0b20214015092040346aa181d4012400d01c10b100b0340d2860600d68001149028450100300a1000350303403110 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 617193830 1250 617192580 617192617
    0xa05090c130b0d031d0405040c0308030702010209041112091603080c010b0307033801060e1203041706090a080a0c0f0c0f0617010b090d060912020a020114090307030201030b0303 78
    0x160040402054040142005c0d13100b4141c1c0b88146004c2c0a80385c0900c1d041070034180d80038290f80300c00710640c4c4090500b41c1559030812010304117403030f58000d009080303c40303c45090f181c062100c2c5021500100600c030a00c107400c6075181058000200e03600c001901e4000d410396484403070300e03080240101408c5450703542c1449080703000010410075148070121001d0809955409820404040b00003401c0108000c2d92904500e005008080c4180240003c1010007081c035030041038007a03403107801e6510682003086007404500c2c481807055010080c15801281150043c107800c455501c8100c1d09018040c100810071060848034414040c496120207102d40d04031140300c0a0b940d5070001c0a847c03c866105081c04107a4089208110000728413145040b0340101510301c0c644142c0c003040041030155007000301c0c2c000b50b80d000c1039004a4604002503040d071a07160024101500d1900024100f51007240d41c0100301102001580c00f503403000704001c01120ba0a00b000f051440310980000d040d8003030304166066091804 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 617195080 1250 617193830 617193833
    0x5060f040606020619061703071e170c010b04090501051506070c06030b0a09050c04090e01020703020627030706060501031104080712140607020a0c0801140f0c210604050a05090c130b0d 81
    0x203c01007272001d1040ca001d465008925a4022081c800b051010345590400c1d0042d00c2a480e400c0001c00100c5684400002c0d080c01220000702102c02000b8141d90580d554410003040b2245100101c0b0710010403240c541c2488065174450342c5405090055508060312041140d40c1525013040c000c014000d51201800640b03460340040d002078005102e012002030524a02103808403040c401c5600d040d806a029220b80c3c3d07200c1d820803101640801c0c1c18048040e40d00b030b440600c030201b400544035180c454580031541c1490203000400342d420b8a40c0203200b0711010401004400c20004051003280c012008940c401451030601a40341c1402c40c200d08414080c80c001c0084807580070030406c04662140c02005007840d10b80b51400c1c203c0b94558001d480c40b110140202d45003d4591031002d612450030078040745068404203a8035800780b40c04c01750031488841c0d401446558601400380d03e510843d01102041146092840d00ba990003a0b10b280078000d82d222006030f6003203444d40e003045e80d21001c042c000c503404140c03d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 617196330 1250 617195080 617195083
    0x11041e050601020d05160b071e0801080601050a0f121a0405011e2c120430020a05010c030309060c020d0201061703091e03070905060f0406060206190617 67
    0x4403907460041c0221039a03814101e02440544542c0000c200c0722401401c126919960084809048071040c005000c025031800000ca0720f0f100e03da0312066507022032a501d01450340380b074503406802c51403041030019020303c035000c0c1766030300c0d070b411186028601c1030501024180f81038180000c0e07481001d01c40c42c5008010078010150024901a00100d00c14400e8111a422000448041080020042c3c1d00e01d284041d28031b403100c0201c8540c2d101d84050f03034099000541d0b034484507441544000303210460508125200a004004116402e00040c40300c81c1400441d0300144c0b0341c503514083d0506001c0b148400209152007507200c40802c0e40d10031000c01c80010606006903581d002856048015820300d400820325000d14100045442d450034021820080f4110400c03110103281801c0701c8005010022000565a0030010340c2c0040c103407407100260906041c010f000c400c0c0c0401d1140781c0030f9424202c0402032198001951a400b42c54000b0030180f905481d0001809050980c0c80f244e2042d45a10585000400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 617197580 1250 617196330 617196341
    0x71d10120c03150504020a05010f1202180312040501020a060911090a020c010c020304140906060c010510090f140a0b0d05150a0510030f020405100e1302030105060402040e0411041e 79
    0x5070f8402d400443c0307a4550103040c0d9104075002034003c0346401041089501903490440c0807540d40c18035171a4881440e40c04812078001d250280024640700e0051f88041c2024485c0c0001d190904402a10301400c00001030b40e20002200000c000a0b80c644bc807805202c0d2042d960034103c200184038a4040c203102a00001a4110130190070311546094043c40e0241e00010464048403095144504185424000c01c01e81030402041550025030030001a000318100b846403522078001c0c050300302400c50070942c425007191800030040c0754180c6002c110103a100d40d2034910329404400103c1c04100b44100d4400b103142c01d600d05000510034418040c5c00042d114892181500c03511201c0c4003013150740d0b81d80305249085802c601c809020419428020310160a01b500102d80c004007040084038903d50f42c2e00e03c202d24110488850355200707091741d4071004601e003c2c0600c0d0b405c0b4804450035428982807419910314401c010f80300a007945001c071000c00c002d85854000100718000030b06440d01052456000002512 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 617198830 1250 617197580 617197583
    0xc2001030b03160521060a05040f0f050d090509070e040c18030b0402090903030f1b0403020a29130501110a02100810060914091b0301090903030509071d10120c03 71
    0x1800d01d26001e1241d0417240c003a080000005c0140390303544440800c0b0780202009817094403030342c503000031080105040302c1c07488180611900c0241500d03160200010509083c5801142c851084101400500343d0f00c0364a074000000e0486001520100400c400d645c4111040401102107041d0800081400f62003285070b842240261110601981ca4200003902e0388000c503081c880103001c400200e2f41980d0075003a00250a02440d000030700c4c3c50b80317a0f0002403295010768490320b1085806040000e101030b080344098001060000751074202020b80c1c80c00d0001c00d16501505041100007010100d911a00300810051182c02602c01c1c02c120030b41280051040000f1544410f481e00700c80c0f000940381d4800c400407012241c810000020a91100d42003025420002c1c1000224000011411420380c000b14015402808140c20004499015103400740540314000c0c075444e0290000c040030410701503010904a4400d64a507071080290352004207802c1140352503045412500d1031911200d003004103030680b8400780e9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 617200080 1250 617198830 617198839
    0xf11070b0a02010e030c06071d220f140612070906062607080105061b120c0706093f080405040f0228170901020702010305070c2001030b031605 63
    0x201213139006203581e44211076040580c1c0d40030000041410b0b20581100c21500b8014210240420455001680154000f2094854003014519582d2038100c070b841810214100304500340180e102c0c9020481e5205c0c00101032501500c940103170b040c811501805441c0241c03504e03210800004d610780900406024880c0c010405c0d0780100e20f211300040e441303100c030140b01d004945d581d902642c1c200700602c0746540126400c0c0d04e503884024000c154041c4144003040b003800201b40865284c0d13004a004510b000c8560340500280500b191080c000788000003c1c05040c050803e500d03050048019440d0943c080c0d105900d003444501c6003090740c0c2084021401842101d20880341444082d0800031201e08a1058410340c0044126245504400c21544040810b82071150f080c98400e240703030a01d20324280c040c211a01610369500107034040442d038151041c240c00110030b2401c0c0351520741a03907a0410b01e4130104220400c030310402151582681c403c0e002502030400c00f9065507481c401b10014a150040ba500900c2e118 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 617201330 1250 617200080 617200091
    0x90606020d08010e0109092306071b0f140f1203070f030c120c020c04020d0603020301140417250305070c0b0313170d2d09120f11070b0a0201 62
    0x780c0784100c4500d81138038042e0074024402d0b482c14110324010445200101c4000c00c1c0843c0d940440702001940301020801c0f00050b00d410310701000001c124128620903d101090010860404250090311188001c1c0c0c1c4000800d040880341180c5500d00552900b0000781c91107000903e818041141c03025600901c00c503203481c045c00d1b900c4c1f4000e9054400a41c03200002800103141d143c600319050300030381c207104422300644089645590204090341d00001c2951002502c4541c00c00450801340b00c2e4181030075484c290300c4d1031800c0c1039881680c07000082c542070481950200c0c80d801c0811801080502c060f214127031001c1002082d00d0040e145800c80380b42901e80800140002a44501a804aa00c500700c50f0603841541c00701581c601c46039504560911114000c00c0c070005034440840c4c8241d4041e50000300d4002c450f0741039488807610500141155803041820240039000040c55168840d00746103581c00d10880362080c400e01190030500d820040d1030507114400c0002520414100102500991a07009102 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 617202580 1250 617201330 617201353
    0x19020d020a090606200304050915120f0307031b0804050d0503040b1809090c0319060b06030c070c091824051611061e13080a0504050a050d350409060602 67
    0x849008500c55127803c880380000050404c2d41040311412844001003841160556130f4600910b40443c5090030700f41d43e4000030380030302030680040e00e0f09502d10401c0e003030758040c3c009565954100c2c010351103541d0040241c02c0c44d041c04c110040c0251005080041015030b210300b1014040c4a03c00c241040c658043c04640b00810603410020400f0800900060b004209c0e41658521b40000718580b0002541c6e81030743c400c0c1c052280e5a42c08001c500401c250024240c44841c00d0038907501d0050f299001908551820b800400c003200c443e0202c00d0340a42224980b100c1041100a4808840f800e41c00654884d2405080109072415030340d6001284070540e0311f0300292000c20400c241d4400041d110480020500c2c2c03c194081c4000d08005030740044a1440c401005150703a03203040b01c0c0d41081c4071a00118801080034031180c184031240000030101103c4084280c522a10b440d5000f045039035070040084000425580100140303c16600520701e000c460a80e140d540395004001440b9900a00005000b24600742c003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 617203830 1250 617202580 617202583
    0x1a060f0301021206010e0112140601022a042715050a02040b09040209030111030a1a0a0605160305130b18010503040b0115020a0c03060c0206070219020d020a09060620 73
    0xe00303c00b50b21400062980b41c030300056888210065405040111924071003041c201d00e401601903180c0c49032611007081c103002c4006810182c68205555090a180310303485440700d0a0070884505083c10b980004442006a0720b185144c2120301c0d404842020094540b401c014114038038480c0700760b540f00208070b01e455840c0480c05a10451241ca2115581803000410070700d490b90041820b084020000295001d0904200c241c5800132200c80001036501c0c0034030030709e1861910103160750741000c0f0343c0e0305140c50500d0806001d5024140120b001c0495504d0284109030180c004c80e071040303510100403084c039a6650541032080d4000840400b503070b001080d0302c8c3d03074a502500540b40580da01c40500c00030350f8240555450342030000400401144500c2480c0c1002c1100301d580c84001e1405030741c0c081400d0040c3c2d10003911340040a4968030441d071043c106200004911039180302c4195040f07592660501c26400095008102c0b504100501454903000081c0d403608018024480c50503140c88220b540003019005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 617205080 1250 617203830 617203837
    0x40207063201140108060409020904030f020106090b011205280c1e0915090e0f06010215060a090e01020f0c060106020706091a0c2506020c0d0c0b13031a060f030102 72
    0x83d015180d142c3e8221003258040e0703021030782c00000030300001004441d580014000c410299001d80110701440e441c10601907082c0900000f0340f015980900a107051070f80000c1c061900851020703801c1d995940407400b000103000d40c1803118868220988040f54000759110000d02a0551003404103d4840c69203a05035030100c13410460082e2600d0b80d8103400d15004100702c0d280b45c0c0c000b021040041c5150007143d00049058040d0148802c0184454145070070b10000e441c0541a8510045195400041140760b80c2c40028102c19104101d0011034030303030500491107002e8025080820801c4102140d81d034001c0e400040c009048a4141e404c039402e0341d565140940751015180104030051560150315400040401c00412014a840080354414100c0700c1049003240000b00044004240b41070042003019410420300440b880704a40f48600c25015079a1180d100e81c09118400c00a1000b241c0e4403000722940c00340d80b0045400000c401851001588845c0d0003080440381644105011510a4918181442038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 617206330 1250 617205080 617205089
    0x516050a240c05121233041a0a1206060611101e1e1b1b050a020d0b060a06050901052205060a121404030815040207063201 54
    0x5440105210441c1211440c02400d800c1d28a07100e81c03000002401004001012040b6031900c401000382032030703001d200320706000d281011080000742d1480312814490b041a0003800000700c40000381e500c000c07000180d4050a0310f10b40c1d83e00c800c8010b00041c010940e07000c1c0041603440b0708010482c0c151214015502a0301102440c511039101d201031047e40c6056034050302e0030184006540e0500304100c41c1850a0340c00c000316150940c0c88240b0240304814190184592401d40d10107c0c011118011030014000c1110040f168041c0542501c40400c0c40b2040c031001c5c680c5170b009401c0d100101c0b0a800c09080c0542d040d030741035000d81c502100006203a8404d000365841c042c0143d44d11490000e4050003041c41f0b0401d15440480e2040325a80014140c2e1508002e10081c1038940300c00200c100000707516021a2441c1c00891445901c2908000010b0362042001e5031003052041c0b200c3e02c0007003a00100b0003c1c000c400c40180b0f02c5251001040e00c10f0881c42c040c00140d440580001c1d00100202c002604020080c481d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 617207580 1250 617206330 617206379
    0x1101061a0a030908190c02031203150613050d300f11070f0801150b07080702060318190210110d0c0f0203060705090a120201050301030201030c0c0516050a 68
    0x480740502d2003600012a40d5008603d010708081160120f041d07104010501d010200e200c503641503003113040500c28000101c01c004221f90444c40c0007400c414262002d900700a00c900c03800514040390294000d83c0038086e20028182e008480c00320b19000c45044080d00640b070381980a101c000d1301e801c2803480c40c0c440e41d07006503460800000c0444d1094885d40300c4c00300144114029643c0104103414211645001050b4880000c2201e642941e8800d40203c4070382c000c050b148a040207100082100001250103881c1e05458281c2c1d01d50340c83d0242518400b464805203154040c0101d40144100b0007900043c41c24000c0780c1c02d540e88144e200c4181da408171440058a820b030400c00c41e45940c0c03030160605808031800340c14000d0703547c0301c1070740001e091400480303034100810800300d44081d0b1424035100010251a19401c00040c180c0f00381c0020b0090700052200904144d02c6602140b1124403818001b20090ba2000c01c5a00e44640c0d801e100e1009140c2c2d00442d80551000607000076200c8a0105000704401d0307100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 617208830 1250 617207580 617207587
    0xf070c08120d0513050a1209051203090909070f03050318030105060117070e030a06060e0601021605090403111b1207050a0e0402210607020724030911060a1101061a 72
    0x10b1484080c100003000310041c00e141c08000c4000c82d0080c00420f040300d200b5014070145d4106988050b016109580110b400780340854490906074100004407500780074200ca480e15a5521010018580b01d11038009000062485000000301f04000000d81802090301c4540084507510009241c205d42d41203880c140081c029a15070303110511180740c920781101080c82c08000003140b50000c286410300d00e280864041e55603050401500702441d80d06c3d0f03000300d004d01c041c01c031030120300b104500c0c44080c1e0b010702d500c1075103800c0108007007502520385011100c4050054400720143c40f60b20010f40c3c485510014000e0115900da400300aa0215410703050703a00080100040d80c1c1455080e002080c00140300700d0300480c150040d0312480807001c12141239848008000e148614080a0003420704545910030000d844240107a8524100a940c04201200c020b140c001142107060510803480e5100f445825000180000c0100c00c4035441910520001c0441c00240f00165466054001d60f0f02d500941d40e0030070301c091 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 617210080 1250 617208830 617208847
    0x4020306060d0b0103022101150809030a05090d1e0b0708011a07080909010320010507080d0213030b13030e030304050603040b090106080610060810050a09200f070c0812 74
    0xaa020b80ca0380f04040c90010300b4000d100d0741401901000c401d154588003241c000410962030301c5015144000300e6442e01c242c040c1402c0483c3c1340d4074041d880109081c024003241e030200c1900d55982e50701c070450300300d201c1c080746170b18400c01e4151421145070165009604800090760f114010400d071030407a07600080f022524140c4036861b403c2500700c9a4215840d4200700490001543e644969a0103503009844030802240700c0600c4441d48184403840c507050103c24084000800c20450586000c40400800903940e44460340001c0b88171462034000502505144050283e642046076199040c0c07031094407a4982101c05004150742d0f40554400e07154403010400000d80001c406440154126010500128405440341072480c10a40100c3c0c08800e5083c0380d8101b00041d542c08041150001c0f030091194a0142c144404520103000b18040c092440b61214070300c0160078400302c802c10200342c1001c10b00d0b441e07443c846d02d41c0340f2650081000761488201c200b804108110041446085441a50486850000c18 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 617211330 1250 617210080 617210107
    0xc03021c0e041b022413030219050c2805010f05070605010e0403120e060f060a1802040305010e0715030506061b0c0928090c05060a021b0402030606 65
    0xe040032020045000c40103166030301c880c00788a1440c2045007403080c2500d40190002d2030002c0608050708880311450280c0701e8124521546074002d1401d2400b00202d0106003016441c1c40c0442e044001c0d40c000e0300038100b051000103d0190b034066012aa541c2902c4030208003000c0741139141103811983e9054170810045580182560640d00e9850f090103810000d0070f403211004c40b8030990107511040011003c12040590150b404030030118460f504020a22111010341e94030f001c02001c0701c5d1300c0303219407012810990320f44600c0d1004208c198440750b80341c40a207600e11701940061000300c40c25801c12407103404481000c5016010350b642c00307c00d040c0c022072040c0b0840c05030030090002030700140c007040b00b59205041003030b01171003200c2c1210082018122400034003211100083c2162004500900c40c0800c0d00d103012244031100c5640403011964002d14201246c881000b80d1003181c1c0135000080480780550081020b60350207000c2d900d10094060140d040c0010b9100450300e50790320010030455200031200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 617212580 1250 617211330 617211373
    0x14010503190912081b040b090f060d15050a080a1203020f09062209180809060405030a140609030306060403080d060801020324030c0102030a20030409050906070c0302 73
    0x7201e200c00319100350151200c41da030040080c0070b074002070010f40c20045003580701000380041e50100c2c24114680362504520f14003e018030b0098522441980742484c015940e41c0b0140c031824041401c3c2040411803688a10849134a984500d5004208514000402c1c000c080b500310720b1140c1100a4100502c0c00882c203d000354090010084240810301088140e0f40340d0307401605101c0c4c100501001020241e8809034003070a05a0f11112282e800c0c00d00710f407840c07503002e020005043c0e40251060381790b5601c00c0014683c0e00690b040141c0520801c43d06205000300e041c4140c1d4107114a40035582c05444200e8500e1701d0344801c07981280c2000c420401000099032080041000228000c800160b0907203c604403801d86c0c0c801d072074042c00581d80610038100b074080c1c0e028441e014642180100702525085001075147c0c0a4010110b05210140c3c20b066040701030300388154001d01c44402078903555611072104000424050314461098030502000031400c5000b608221360094040d0010030120f06081e16801c0182e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 617213830 1250 617212580 617212621
    0x10e07080612031204200d05072105030d140703060305072714060f0105121b0c030a0c03030b030a052104050301020301180c17060603070309050f07090614010503 71
    0x4010800005001e071440c00b001c3c000c506c00c00140308110b00b00c1d000c00e24125a08a0f00c544100b0051400c000000c5000a00d102110715986a9032041c1901800e24011150001006081c0340400690800c00110381c1d40f2456400d01c080055004607120400b046049880303501000381150300c0103105112440c58400d4016150030540180d0501001c698087c0d42540c4d120060302c075441ca031090030321042c1d01e8219112000c8210a2a0450400000c81803031001c00001820080501903622207001c501541c0108130348810455104495071034502c518000c10301019441c01742d0003e0f00d4462208a107150100380c1000c1c0d946c03c040140305100840004250754841081c690180d001c0410001829813420300141d802045144071050445e4545d110040943d82e20b44250743c00c10001e8410750540041e880480b5401c44070a484240d220b68078110150001c0100d0b5801904503c00c0703444d1170041000c0002c0040507100e15540c1405a16540c001901500b1900885140410000d00010340c0d080c042004804860 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 617215080 1250 617213830 617213833
    0x4260901050304020f040f050429060609040e0d0503190b0603040b06030102130807090e0118030f170f1608062b0b010b0a09060504030c0501180e0c070308010e07080612 74
    0x155117000020300301d07011100d44403202a02e4000304018004190456101045410038151511043d07404c107503140c1c02d000b062103201d4a03001c10303480640d4645511540240d940b200480d005d0b158903520240c051b4000f29120340c5402000741e50280d91260030300030040400d0000e4070140c2952a1659801824200188003d030151b500307001e01c82d0112800c00d10031000340011b2010300b603085d043c04421400c2ea80c400600060b03d0381480c900006500b452a0340c4400c0307a41501c0c1030b00362640c042a0803224415005039011070843e0040c18400407401126100380600e045500501e40c08081e007505490703144c7c046a48540c080d04008444031589100312a640310540d2507030450380400110382c4c4000455000382c1005141c090003091011420350401124009400c850820340c0c185803665507400e0203910503009040c10007a40202405480201e0800035001c0d00c4a52480510361822940d1810b040d00104070540000303050070300021311403c18002d2580941015598025a6541c500c10300213031088014181119 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 617216330 1250 617215080 617215099
    0x1206090402010c023a02011b140d08011d06010516020d0204020a03020703120b0306070f03020d0c11071d0406051b0d0506010807021f0e030405030a0b0426090105030402 74
    0x5076507802d440381c031012211425080c10603049901795a00c20349181049544949600d034400540e812494a02109006a4140c10101d8962500d00005d0700c0c8600c1954007485070203503c1c0b44030790700400a00c2c165001c916100110748107000c0c10304500003003981c10a01280c0100040b0707051541d00c1400c20000c034006000380d044411320343c0c04141241d00403e002c1c40080d80c0030600d1800c141d841111480030b03a0b124101440210960400603840781ca002c4d00311700500a4030502c800e800342c040d40544d00a081041001c1048010115000d0700074049444407d000b4000c1c210b01003480800340101d03030750300000c0d0940341d0364070341d1603035903110080070058a058905c540900d84480308180c07080090080040703440001c249803e110002500f40c9102404040564100c500411a0060859501e0043c0c4600210109440c10b8801c5c82d54110300c52900400d0701400740e8032814040c0001104a5070184e881600c5c50b582401c00e4481031904c42c41010800006188100f081d0540b03507200d03402540d042400102441c28 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 617217580 1250 617216330 617216333
    0x70807170c0903030f04030501020909090604080409021305090f01150f080a090302010e0703140106061106042a03030c12030b0d0b0613140603011a012a0606060512010801021206090402010c 83
    0x1961b41142d801119240c0d000500c4500a04014200c184c00c03a0800c0d0040c13090341010b9559907928015802500400340e800300350071841004001d8010020980030b0071414250070000046025414240141d00c1021103004420b802d9620071720654558414990741c074240c5444101104020700680c25040c2c3c110740d29031084040c660f0041c81020300540c0304000a03800c052100d04280d003034945540c0301d50103000c070052041105000c045551640305601014008501a00d1003180c9203001000b141c280e2a501011000300c200b40e0410001c0b24503e01802c4d2404008000301422425256039084042d007108000f590600014020000b44d0f40050000b040f0300100c000c0103c80508480000c0304602e04200e9850500c40b15042c2807048104082111141d40454903261001800c8118030b650f000c210743e9800c1500913400760a080807010015400780040c48125564800109a45c01030314105404194410000940150502c212000c2486148004c041c55840c2c402f003029004008009a05100310305107c4c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 617218830 1250 617217580 617217607
    0x1c15060306020406110d0203040302010504060e041506051201212d06060e15010509060a02030f0a02030403031404150f0507021305160c0206030a240905070807170c090303 75
    0xd09266602c80c0080142040c1c2207281000035106c01055400c100024000750364448129403e031442c5090201504980c00d000c500100b4800c6480a00131048034030104200d44c0c010000c0c64961070a85c80122546d8070f40d400b04014418040005e410000b00304040c10014400e0b20102c40500c80a01800c44040c0c405034600402c5142c5035001c46000303507103000c10b12060505030b51090f04504516140356103a0709201c000f90261150017501885900c0106035000c20324400c0044469a90744541996207904125902a41e00d81203400124045018140c42c2009414031800750380c2199400104051100300b55001628410014400d680c204602000b11a001d612891011249401c2d0168009043d00c0d260884184142060407071804120400078100c0150342d860b0240c81c1c10861511000920721820006c4101403510720406145442d0304100c000b8210080b58441485281d554880d40307015640c3e0392084400007109441090359044000100d40c14250107406030406880280840e032500b201401c980 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 617220080 1250 617218830 617218837
    0x3150e01030807060f021e09061c050a060e090307020d11091006033e04030b0f010f141e03030d0905030c010615080f0a0212010e040605061c1506030602 67
    0x40d110b07940d000551900708000c40c8a900c855020780d00c002c40c01d00e450001c620700c2d1b0049680c1e052080290114032805585d49040031552540044054603000200900112002d405c0c1160b51810140c64010700040400010760300601ca882e5900103986040120750800118100c0b01505031042044018000401c0e150720031024002c0c42090394940201b440c18200a0035189814028905a1040c040d12401207481400113046102c41400840c070b01b40d0f02000e801c12500540d80050418100700043c400400601000a030694000002d0b04034001c1e2101c1c4290700000c60404226005a18038440d145c4280d42280f4104041d10000c1c01e4a143c02c901d40301110681d02c406006807840d800c00607028907421000d216142c01050100d08034100203d840901811859000b0140c03400101d80000084a060880d4100c4d04c51b07510701090f03100d031540c40e4007520201c150100c0b4115422031400010078400c0c40c2c0310f4011046441d01000c6130300111042e6645111040038034040801080d02e943d80400051f0160025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 617221330 1250 617220080 617220083
    0x60c010504060b04060b0f1b0102040f030b0105030601140d02011202030c040f0527090c030a06020406081003120e03010914060403090f06050d050402060c0a0b060f060310050103150e0103 82
    0xc99103081a041c03036001c5950a4a0b8648a0742c5044070805c604140e1109846003200c580e20820340b1034410316190302c51031102c00d14516465200207008100c1071034444003803080d139020304501c04050f130321081410f55501d82070007102e0001c0c0071a00481050301d081804182243c1c030600d440e103148110061014141d0700282d4030700110440202d4140030310a00240041e0040030103d44070344049056091b800c5101d4880c3c0c103d09284450280000c103510000c0000c45030002c006002c44410747c0c094104034000350000d0040000050581011907002024450400166500825120420100d2100c1564000d46c00001c654065403030340c88282c04200b90b04051100c40107960050f007400d24003490020078600041e0491081c5141e0510248240c51340320059a014407545440000c640e02c40e030000554034061001500d14610588004a041150400c181070084005843c0240c03101003880402402c0e020488027000c0c01204581c0801c050361098201d0000d000782da4941e084402c1d12030319107041c03400d0241c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 617222580 1250 617221330 617221333
    0x3030c0711131b02030306090612190b16030e10020a02011e05091e0a030c0f02120d09050d08090402070309150309050d08161107090f0b03010e0a0203031b0a02060c 72
    0x10f00030460f0080015810040152020314038625246c0300241d060100a40b03c13034017418030b400074903001031010403a001f03080007030441d2007160005501d8031012a5034212034031148000100e0062600718081c0c003550f000c005c1030401404060b40c0300c15141009400030705041c4110764903020300c0d030001c0c008000401d074062032610010699260500a45103040d00c20318801068a00c49002640305010120b544850340c0e80c5071510f01b00c29041800c1a007a01c03004e6500180d8030a2002c0703020301d44114000740080c980600d94070340e50a80d030b560b08200706010f4004c4134050410f407010448400c0e145842c0e4001d050051103410024a5252554500001640d0080712180400e90705e800701014440100072003a40803200d8500611545041e50161180084490701c603400c0c0065003a5401c0c0c00c1d44144200000340000302d03420820300041c000610050300101016074025468040d124207039240c0400c0e000c0c0c01c6a00540110710b031a1103506494103150800e1754841e594041e040d1aa0016510710008051401000c1c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 617223830 1250 617222580 617222591
    0x305010221060109090e0309060a110d1b060b0604030c08030a1206120f060902031903091715040309080d050703031a0906060708040e013503030c071113 67
    0x10720080d6422034070600c400200905070704001c203aa901c9218042901c41280b408160091008503031855805550055948100040ba074500750340d5003d01c01c0c10f501d001074000ca8400500004094031003006080b01386e40525600035450000c2201504060b8080d180603003100d1409541e512403109044c90783e0800106500001041c2d01c0345548018130600c0c040900a0401449280000f2080c41494401c80200100d01c0d400501c418820254080f40606070080c0a80c1e9040110525140841d0402d03581240840e801140115140c0104862408d4202030640107144102544220320141d0f10005e1044003008403000d0040b071600750030300482c2680002d035100c41e525008140785c0602602e46036640170719000708000c10100981d407000000c68100405881083c2d44500b641426045c42c410361f0844070512510000004003200c00c2d45903203036855203840601008040300070707d43ca0308921080d20b6140703079801800032035050030050300200b41c3c0d54454000c2c018a03070080008246051700b2101c10168060795107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 617225080 1250 617223830 617223847
    0xf16030b0c030c09040e0a0b0906070f03140402090603070306140708150a0308030a1103010f03050607080103031e111501060212040515090d1703060406050409151a060403050102 78
    0x20340301207400051501c221400e41c580720035060414000c00c0d80c1d240c07065485904203249480207011103904d440d080b81c00e40d145851f0190141d0b50380c0c04107440d42000504000c0e041054a4443e200d01d289011052070319a40c0e9448540800654200280c4a2645400b8404000001034070512070302500e290000050072092410b1040a0300d01080280180001c04560307020765180e50301c4d4511001601da00001841e242d0712007401c403034001c146101c94200000c07000000850b07000c8500742c1d410201c0740318804a941c5a40c0b0b40c0c1e01281c1d840720a20004000ca142021003003030003480c21702c27054104034030351030030620001d449004c9a19040c1200c0082c1240b81e4008010b0010640c14000030086241040440345041d107080003040d0000d030750010720103072803001245421072944c40e6205041040c0d008000014600003003031150f501c690003660351074411817501400142c076013014011014010781080c054018104058440380140c0003100000c04a9104044485159507400d006000074500410006890f602038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 617226330 1250 617225080 617225093
    0x180e0d030b01140c06191b0c02100e10080c0d1a030c0301050c1b010f06030c170703320609070305070b0405062205060409140f07120b030f1603 63
    0x300d03004840f035090100a80c16080c500054456001044507078180441068813068030001c1002e1941d00c000102d10001c4145801c0e0f203d181d01031424003c565000040d810f1850986513a0344040c503940d0012204a00220240e0040303284990019042c0c1d2601c0c039205112224504841000441414200303680f600c40c0d1003400d08201c01180d040703040d8000c115034241408401c0a81c007030340310103044001850705140f070128002c5d00031140400d2504e030113201d1030b0b489241260b480f0005000b0081c0c02d80d894600314910b5080002c1c1401100d0b0802d2110100741c0001003074000c060042c160703039007085800032070b013102506042010a2003a45901d024101c482c0c2585032076402e143c0d40e1747c00000701d9101030000784495030f5000114ce500c00c034260700d0425400c103070a9441a0010541d400150f1001c00400e00241c2648140c00c44150100b01c00c1500c0e4403075503080d42d10788989100740c0b11000002c0a464807201c100255a11880c41c01c5070080072a0440150308241c0c6150440c2c901da0801001900b8900700f081145 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 617227580 1250 617226330 617226347
    0x30b0604090207230606040c0915030203160201060b040b210414010b0a05090c0c150906070e0103140712392a140a120905010315180e0d030b01 63
    0x129911550000e60700700c000175664000600614412942d030050000c40d2800341d08103000130300ea10603240b4480e2000d654060005c0d041203482c2d562003000f01c61000110f80c418841c0d1015a10441c0600e414181050240840b035001010100c00490b546940b5482403820031038142c2c400c6104006014190301c860b000076007900c3c14846801e000c0d00d06074100340150354582142d02c1d84100da101b01240c8824112810300d04d03010b0300d000c070095116000d40c1030203024035000c5245482248113484903210027840800443c203d03403020320824000089040424840d501c030745881c42304903900c5200841c00010401500301c418100740381140408140d0a001d48404102c0700303017000c41c94001d080800401c030b84c1c6003c21040060b10003201c6404624003540c0c40800411000012098040004603802c07140b217440c088204001041400e00810700b01c0800042541c0700b030146505103000c080c0c01604103840c00382c00c44040c0718a17100801c3c6041e11001c030598610010045000c03d03140307594012400e061440000340c202035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 617228830 1250 617227580 617227613
    0x3050a0f0905010b01091d0109050601210e15071d04060b0f03190b09150d0c0305060709170a08070503040306050705040f05010507080a050a0905032401290a030b0604090207 76
    0x14405548147c2100c1d2090300b81160043c6101203219510240100e0718044281c041142d1100d14802143d28800c8030340c0103030110200d1b40c007110144403420f40b040c110b1450031210720001a140c081c15141d854014049200340c00c4002c1c0000c00c40d0303034441040e40110381000c0c0072082017003004000c1000074484031024202000c001001044415064408107940100080000e00e40980032060800c041c1c0f5440420120503400c056110300300c5460b403800544613503055803050b00181d014000030541460703000d011032804158000500381080207550702c9035a07030420030080d40c00d4001031000002188040c0600d92040340141d451a80d01c0d0300700048613407000d00c145c1001d03040200a00ca101c0015400310b0031203003440101d0a16a44887c04160100d0345908640c210701c1d00741c001d1151a10f01c80d081c1d00d0050003c00351002c1d28255581e00d80c50481d0b03484036158160340340f11012000320204000500d004000e450020316001c40c2c960b8510b03011400640c41a400030030710035400101e10040c0006a944800c094 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 617230080 1250 617228830 617228849
    0x40f0311030d0f321005041e0b0f030d1103070b07030603120c080301050d06020c1509100510030201031d1c0f020c0a091e050903030708100f0603050a0f0905010b0109 73
    0x600308000c0001482102070b010b04200e5041300410003100910f0610310007840014018001da241d545070780220010803203007140c0c0e490300740b82d60b00c101407508030031085c079201c0c01500800c10000c3e099400c8031041c03a005450f03540c5000811000012581d00c3c1500c905c500f40d2601c0108105240d0f01d072a0102c2c00340050100200b0034603841c00c01c000b03031603203049031b0462f44100e66010792840f41c0c0c100740009100302c0b6029040380c4554100700d40f048c2c0c5503500c840c0c8102001e0040d1402d54452800450540340c046034101c070116401d210600066009600c0f41403000425541d0404400f10b8495080ca00309103500d071000503440e04404050100c2d4010903c1c84006014405000e4650741100403500041507400760907402038039038861032010b800380c9104201d0114444400d00c0700e4204903800c1e0352254800d64840000450050004280003940029103007101e0a80302040c080b207180820480c001d1001920f070220307a5444103242c4031843d001d4002c6200a6000314000206104200000351500c1029030003030808 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 617231330 1250 617230080 617230121
    0x100e011505190e04020c0a060b060a050306040f060f0e0a1a011b030e0d23030301060804030305060f06031f06030501080d0c08090a0b0301030b01050402070b040f0311030d0f 76
    0x481d038410240c07070007030310051010302451410724010f07103041c9040079001d60030510208888402900018400707440c40e001c0d1070200259002d1b00d00348800e40c41146000c40118000b0000b150385070910350321404440c52a840f00007019604d03024510100c01580d03000044154600c01030000d0a20540326404c0d0200149110303001604501c000a460135540410001c00c590350403c0e12424180254294141140003c054015805075840c260811840c1860b01100414100e0000e140300c010020460741650f0301c503213441c02c1a541d1680c00318003501c0005e1455070000925034426400e5250700f4007842c006d0315110302c000c0380c869480500303031040b4a4036030104040505060041022403004103213010064040e03d8000d02c1d010050500180340d100c0c8404a41d000511003100064402c032480256040e02d00c250b43c0403426981e1581000142c0c0280709001c0c00d01c45a6401240004042c1c0c01200d41191080c1818a440c9444100f92401c54103ea00c0840c0001d45661700c041110110340b103a03521011800526180 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 617232580 1250 617231330 617231369
    0x12020a110915100306031403070614040302031b0708420601052107050712020a020105181305040602090f19090c180803070210080420010c0209100e01 66
    0x76a0300110b212a030207000a800e5001e45144a504448040d603041f4a00000324084081c0300d079a01d91000505944070f900d40300741e090240f04008000d50045416500a508201020390030480c88001c00c00c4458051150200c005035505090154282841000c0d400500418084486100001402c444030206680700c072140480c1c885c4400030950009800e18056803240403441076000492240340c00080c0c1040500c0400c01c585034408010180e0b240f1881c5040700c0a15202030507070b5942c1a000000b4007140f0240840610501109039a01c0807031001820305500d4250a2440ca0445400741c405a031526000a0081e480d810f0401d0150301c0c01809943c508205800ca007081c4604010f980a0803448a86070078002e10314520400e0350001c5001c01071945442e2990b03070100a42d07030358000c9000300d003d8483c4992208001d4028a145032007a50490ba910269480600b0780d00900062450010f0500030300241440250b01d4024500d0b21604a404040d01075605140050400342c40503070011500a4803403c100c3d2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 617233830 1250 617232580 617232601
    0x152b050708190504030f1206051c0201090f0b030103030c060b040c030e1b0105070605060f030d080a0506100c020415090906090507050603060618130c030c0e030d0c0206031312020a1109 81
    0x14981c80040c1f0b48001e01c0044142c8841c080c19a582c80709500020340824820b007020b004000b4000d0038402d0720b6030f0101d144d5030803502d180d005143c801c03041806014801000441d0280020144c0036202d201d00044006a031000503044030f2030f0950000c0001c1d81c801d4928070101c410802e42c40c2860b0203400381c01c0c5603003024000815a00c42d5080007000d081c0c4030004142903480760907604000140040c10b07580401c01c81c48009007203050468640c81400d0801c80441c0740c5042996480c803044180380da4140b0100b007140c00380006440c0100ca82034400420382e500162002180c820a0a40c070701c0b90501060b810042d082003444d0a080d030300702611940c4c0400501c100342d501d80d401c031410030071a180008900148079001504041c411a0440c907164245810142459855401501400c0351622407500110220003410790340c8400d070a800c408a04080e107042c0140c58000c01541e4400c0620f07002c4655001d182c4c0c0d40c1d41c00c1c2d640b0b029040c000360b40030300749400820102d0780c44003000c40000d40c1c1401c102d00d450210380 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 617235080 1250 617233830 617233847
    0x1403071a2a030d09140109030503100f05091303021006081b1e2205190c090303050a110a050d090515030c0f0d021204050d0905152b05070819050403 65
    0xc51226134441c0c0a80402440d0201914108603400c0204121078060070040d00d40c1e40211028400c1021640c0d001c200e01b81044441c900b5a0030180407001140e4074103064054000b03100c5004e4041d0b1291080200700030f03205000b003201812000c030150150000c15070040c80002c46140c00f1a2042a2100c8206130182548900840643c0200c03413001e4130081090352032070020800e8589a403140d04100411403d060100c411000b03503240100304129800d801d69048810220901005001031401c1200ca4041d86c03003a032151340000032600c00d0381c9118005503601031800e086071090a0215250b0103081120789801c4141d44445444024014a10b242c8440d1414040c46550060b50701c11102240212040c25298140c0d0072612820101003610f092074141640d4a5042051040014050400208260619660303110300341049080044c140324000c0280e10700b200c1d1003100400d2030003007201303034a010b4000d0b8001c042c051412504e4403800e0741084c2c4100805940c04003101807501d400c000074000061b0f0701000d070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 617236330 1250 617235080 617235097
    0xf01060b160809010c0503120f060d02090c0d06080a06050f07020f030a0302030c07021e120a050316050c100f08160c170c2d070f1403071a2a03 63
    0x65690f2060800016201c5804521000d04940701c007203040308012060002c0c6901588010010400365941c0c20104540050803030402074006401d40c0100e90004c00c103201412820300a00c502240040c0c1707608076540790424400041c6e031040e80310010b2140d0b2007a5001007075001140e0307101070701c01d50010001044c1d803031040700070510405d5130000000340325009500948401c2540200b1400034514050f02d804081f240d0403a040c0c0c03081e100034202040403500050307202e00069001010b14148003501d0b000031710704212514252520301443c582c1f90501e039202c3d0041c085644031a200c440090645090042900100603c5214803002c5000300120941e007019655245aa00048011503030031280c10031003450048129800385445403085404658440c14481c80c110302d40040055012441c10243c035603100c6952147c0b50000007074420610100e80300d4802c00500b030001400b00d030402a0303174030031307040c210b801003405401c2c0101c003c6640000e4a00410b403001e40d4409000a07841080c803012091a00d0f842290340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 617237580 1250 617236330 617236343
    0x106020d18050901120516050f04050c0f160302010c08040f06020a02010603080a0504060e090606030f0901020705072c0c0406030c090302030318090a020c0c010806060c0d020f01060b16 81
    0xc52006880400c10786406020068040c4141c0d594856482d08448810341048501d030140b0705800201e803001100c02012a0402404100c501324440140402010082c010110070301b400c00c440c2e842c0f05480001004136803447d08107801c00d40c15078240242100c070303d6031406080208035018031000c500e500c150144600d400420059035011046402c0c4c0c0188140d81c8010918603020801154080d008000b50023203030960b849038001c00d4401d00400125842c04c4880c10350001d000c1c400316031000ea00906031503202c18244001480d058403622014901421944101610300104240d40744200d191035010481c9402581d00d10444c0c2081100d1001d40c1c0514050702c4201591401c601040c2445040c1c254025600030701035941d02c4105200010302c003160003800714090504080420400191482103400036104c0c08040e291041c108401100ca0410280059030f104138180104011103506210542c20030700907400411320381c400d8107603031425107170b80f544403090303004c024130524180203401416022256032024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 617238830 1250 617237580 617237597
    0xb1602010b0f042a030218040506060403170f0c0d090801020307020705300606010806060c0709020f07050609330c0a0203120705030604180f0b060418150f050106020d 73
    0x2000301c10034111035140c0349000030002d03004c28030050301580285424a0820300a028003c50001488107994007940e0351341d0055410403080012601818071040b80745500c0b94041e00e048a01c07440210b45801c0421840015000221849000c40d0441101720041400c030000350b0842c07900a4000e511141f0741d2184034020070980302c40300301050300c03100c00c03200794000e00d101407140080040d00f15503207110446900d40440d0f140c002099183c608041a01d01d2407210100405606062812400182d0010f40c0441d090071030038000100010400e00c5010320489102c0d00815181c20b07071032041101625441940c0c030150f0a910807062001400049540c1c0c4101e4102140d070751343c407001e00103e00d9489400c1c0b422002c0191482444a0a13038000001c601a01301101d05000e10f008401c24a514840c043c2c230018030103411107146000051420a001e0b40c00140104000340303103d0264012414803445010449140000031203503840340c10340e445000030100e108141007101c0e6040441c040e60b1654161407082c00c0c0038484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 617240080 1250 617238830 617238851
    0x907030501261207060506190e010b1e0d0f15120818030114090c151819060507140a030905060706090c14040c0e0901060e04020c0a0b1602010b0f04 65
    0x1c0043c0040d02c41c12100c0703256515200e08090005000c16201540714005040d00451415602c0c100700082d00c0390341c4154100769180240303031290303a40644250300d2810305c502094403050404a0250030700750340e00c403008102d44140c000400102c5042505c03030350304c0d101140402d21155403078041102029074051007a40d500e0b0346088408445240206000e541036007007142c4042004904910706000c0c40103138040312601400c0000704103015500080708142000c0c00e10160800c0d1001c10501c1101641c0600328030480140100d2660030030005400840106000007004410001c0b0212482003e50300c074809009281099a4004d0004c00703544641c600c517003804540d00080c000a0b600c60140f60764440304848000d9035811008140400f0348400912591501808407012402003000c040c0c00d04009001d14907503801c2000c1600c1c0503100446068005600388030b070048040c82001b6099075140030f203030300c8082840c21126815a6180100901d021a410b01e80c00391126103420441801c40300c0203c8001c0b50000a8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 617241330 1250 617240080 617240083
    0x60506040603230717010c08070807020604021c050609010c140f0a181707150519180b0324180a0f090b0f04020a081501030209070e0a03060b090703050126 68
    0x4540101c038071403481600800e00c1000542c090f042600c40c5880c0e928507030b079650000355000352b012117850f40560460000140180b03450b841c030380e030f50311030070714030000c400145803103c034075110040381e0000c17080c0e6450000c40d4403690003441e200f070b459588000c080c0c0f40800014a4401d14092000003d0503c001c06062013107040b1211031007070280c0300c2c1c850418403040f2083eaa0b40c1e036580b06807280a0b15000c1c500320541c0c9492040301201c01c020a0f82c1c0c0c2254076024030440c201c3d0f482c0c0030340346681b92103a00d106000c10781e42c100e04001c6016503521fa041803038150031601c103190048482c4a005204e03002e00c1e02d41741e810481c0205d00b10f92180da18080003945500082030b10010700308412000b040e50781039404102c0745412a0030102e00a50094512109c003a0301d0380401075075060443c4000707120b8042c0000400c014500000c550f60300c40001d1820350074000262002c03944041898001301c1b465919142d100200303040c0310b0445a800001444d00340083d5160441e0b03d000b0301030540c01e0030005000b414250380c0c181c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 617242580 1250 617241330 617241343
    0x307120507090e39090423030d02040e040b0c03090d0507050703020a0612060e0c070b091c050c1005070804110d08040b09040b0402030f0f1510050706050604060323 72
    0x44c400002e103840101d524080359800d90b64014861440c0500d446205003080c4405900c00c590010701040c84000e0311016000310045051441c03200c1c071042100f2500700145001400007040c05410811860601d481c00310304a9000501c0c09080e00818400c100c03403140005452283c0150390f0030a10707a5034105082c480c1c02d01c0c14580000c0d401290010000820305d84c0300480640c1103924940402880740c1f0b400407801e2150301694840114141408102c001c030b102e80820a410540e850104c070821041281c2d440e80c84181d602c10074000c1200816100041501803142c003c2032042c4500400c4a40345c40305003d00a0314000d000940b0244e128007042a607503e4195a401d0603942200745540c440d6a00d0910213007075442484002e0045091050003c510305103802540d000b44c1c0d2200c0111180c2e03440d202d04c801d02500042420b0110100d02c01c42c003041e0f8131001003401d03000340b1980d0707029034035010f904055059503806020140524130f0542d0070800306002c043c40080444c521110301d10070001c40215140b8140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 617243830 1250 617242580 617242603
    0x1309030210050603060f0711150109050a060501020d12021201030605011508040b040305030703140901062c040f0222050708070f020c0405150901120b09070e1b1204060b0307120507090e 81
    0x3140027045141da10a18100303d0403103187c42420b00c02c0d560385400000c1590300078400c0d1030259100081c081c0d0304a0144141000034403014400500b401038110003c1642d010a80c8141c1d90255900010300200b05680f148142a1040e4100a8030b0750030039554002941e080104050208080070020414640c42500025030b040007402d1070a00c03a0406180e414002c1030948224041c6090201c0d580c16180c030160b5503141000b83d602c404401545c2c493716500031204000100b01e034081d003041d1400400441c501c1d2801d00342400c02c2b00001c1c0302d2421081c080c00001018000c1014001c0301050350306220780c0041d640540480540700404ea68881c10b000e842041c00d4650007552024601d000803410b04040364110036210f0240c800543c9036102d90507603907110942400746020481403180000d01e800941c0240900c454100010300d4035116910311038403081001513400319002c40c1c494520800300c1c581000840040e02d55541c054220000341c2c0d0314190381d40840e00c03031104401c1d01c2e820030482440b414069660a40d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 617245080 1250 617243830 617243833
    0x31803030708090c0d05031605070b030408090117090a0f030e120a060f0c050d0e0703080f090a0b0913180206070302150c1611030c1309030210050603060f0711 70
    0xd00385004007600b2040c045900d000e80384200401c034021850228141415180c04c2000303103207820b183d0490307240000141c03181078980d0700c42e0100011303e510b06070004600c29030007001029219200c41000504144900401054a08288090200510001c2050517000c2d070321448114036a100c6143c2500d14030000c02d03040c1c0d80908480120400c81202055400040c2d11450040144040780c1140c0300484004040301400030b6400d025180c5c2d00c1c00aa03110f0003405840008031003031540e03039680c0c10906500c00b00308800c00300f6000c9000041800c09611503400760504074400c5040010800100e00e26007904a00310000640752034101c1504120600d0a00041e134000d00666640c9900b420007a549802441c02d08500d08650400188034034002001d81d2903e034406421182d441303001c2c0c0c4414100c0d000d48a201541401919803051195481e260200d181283c0f40c50042042407280c10041d0404200134091000079060804110300c594010400a031702c04282403601205807200d00d01129010001091103074035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 617246330 1250 617245080 617245087
    0xc02061611120a151503032d0e01020d0c12050904090c080105090d090605090907050d0618060614030c03070c050d050d0606020a020a0e0a0213090912091a031803 71
    0x10560007083c1d5104140c018402145440202505103017202d20500e020802003149640c02d1000a11800c50f815071039041e00e8689400024407400e03a5210142c6613000702c007042e0303200070130400c6580500c00c0d22110030050030410f2003416142c49400d80c109480100508014001484405940d190b51008481942010a21b030b102901c0e0950203000b0001a03d503080c40348203500680d00002d204400b54015544a90b48841c05d00100b00240305281d1401b500c1c500c00c1c02401c0c80318000c2200b1a129850041c0100c6e4601803e5800c40e020803000c48165411100802c5846034002503481d480710112604480d401000e603039642d88880084070340200056001348030b40690b55a0603082e55020024000d21144203008001082d5139000c140c1c5c1d1000c1c1d115000f500308031561803c00108001c100303da50721165082d000741c40d104c403240019550308815080180b00c41c1d0f903860031000380681150400541e040c0c41c1411404e050404000121000c91400d0000744410000002140402c0410300914001204401c8a46 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 617247580 1250 617246330 617246359
    0xe032b02280606051c0219050409120f020705150d0b060d020301031704081009110d2405011d06040b1e030d140a0309080c1e0d0c02061611 61
    0x1a070281e10050398403e040c00c0b000b14113031030070703450f81a080c8018154180042529609006452aa00307103012000111000009015140c1b030203480c0e08944540001c5c92503c0c4201c5000e403410081c20704401c00c641c803448083c40709494009010b800404501e50b2a601c442d00c15040c4800341500c3c00000c0e4102002050001c006000c6802460599200349085402601d00c05001071030380c0241c0c8103c07440341c1c0c01194030310b02a40c040d6203c465aa03001d1005410b804525801240d1100d03900d0708100e400742c008403c2e00c050680408807080c04282c201c80c0a0249502d8100c0f40d16006580c5840485030181400c040360070f581d1103502c080390401000e042402007240304a0b28028816051810138007a008040500640d207100348140040140c402010030f04000d081841140200100a8203c540080811442c600d8520070810301c0b8104034541151030800e080482000d0810001c56209000d12600c00da0308801650f0300011f40b01039120403410317503010401c0d5040c220340c40d0303005244598108a01d410300c42c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 617248830 1250 617247580 617247643
    0x3231b13022b0c02060c0d020c07051203220b0702012001090f0b1006050d2d050915060d1419060506030d170a02033102010e032b02 58
    0x10744400c000802004806070a81050361545000c507141e46004d58204047c42e8406020342c090b110b102c5401084800468440c000310794020110f80d20754103030b58004103205141c401820745420f02a002e0301c0754603001d00d1418000158501070b807030009040c002c40d04644401d01c001a145803007507c41d454028803080c581c50a1842e9076030902034040c0c0b1084641d4000545507050200300303a0403180d25036116403a1003044c103044c83c0101801809414010020604208030414030100c034000c0313054440000030300d424120111840c22580319504e40300084500104002c0d541d8801c10035842c80d80140406241000485205090552118800000d89035000400c014004135610962107160150210780c41e440b1104400c0e9011050f41c00e000103e040b160001460071403c540255802441c105c5040c5c0141d0a02c100c0c010059220b5680c420355000c031031585105543e4000c1502540700b8003a4083c0041d01e1821100840d442a20000c0c3c85814450105000405108020718008a40c1141045804c0d4242c0002503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 617250080 1250 617248830 617248897
    0xf0c0f090c020c130e1006170d0c0b070e011403040f03021917160b010902030411010e13050c0903010c090915080712031803231b1302 59
    0x1491503860084680d1801d40002149661280014000350200707101c02c8a0300c0c0500303004e007040001030003000328002030713201d0500071000500804880508140f01c8151110320b41a809000c070400c002101d02d42c200842c442801103a00211340e8500341043c41c0c1d204006031400e00c441c140c5d00408401c0001000300340401c0e1500c005500f4030a600b660b8402202811441e0703184003400d0007601d40a081001002440e44840042400440c000c1c0303000052801ea0b210110003030400d03400440c41d00c2d000010081003054405500b500203409080110210603030034045641004d00901c21034a19a4801c04900c1c4011028141c0703811f02d100034000d00010040c140300804008051013402480b904195030f00000340412400c100c140d44600c8000d0075401e15107284803050902c03225040d401e00c06003d4006407091410390104003d180180ea62907500c034800d4100c44003501c1c446150584540006e03d4442085d460841e843e001110110307560b0410040310742a940c002c1c420003000c1e1400c103408401451071034080e910b10 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 617251330 1250 617250080 617250089
    0x70c0606090509030d0509160807080f160504020c010e01051905090d050f0a03110d0902090f011401030b040b030d0c03080a09080a120f06080106090e0a15090f0c0f 72
    0x14400640d4400300c040030307a001602d0301c1c078054005000c5c0c16070003440c80d4401680f10742504200c4030455039201045a0100194103d0000c40d003042d20141721003001008650300c4148a1402004c801e0400410400011528040c0510854001440306200b0b0802d400140c1034401c001c000f00120704090140f81047c01c10940d0700d1790010301704000070700300c3d00b0045089540e6810546070f2601d080000c0c09130316205e0303102c0200e0806142d039440c005803040b40c0d4440a01074491001c540000c1c1021240100295047c000740468408500c40005108510085e0b80310650040c007824045001080342d80010054a4002d401507054880c250703c1c2c0440300c0c0d110821000080c007070b84400e460313600c4001d07a000550301113400c00350001204028000b80c19203d0340001c5092900d850000451b1040e00121034140c810543c410781087e0744801080c42101d060b4418603480e080304500409452840360741d80e0030f035a603034600d400b4a5240e890030610b05000001400e800b00980c4407000c4a8400c0c0c83c3c4101e0301c0312558a014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 617252580 1250 617251330 617251343
    0x1c050a1505040603080906090a03140a17031506160206190f0c12080c070206071a01080109050616111905010b0f01020c0f120d050c0c03010b060717070803070c 70
    0x280040c00303060034402c03c01600d810407519072030b2503034035070a001180d031003404100e40100c40b500340003002c14004c503044003503401980080c2047c003225080104036019458034002c05001c080042c0400b04150a2000c1c4407590182d0b680d54403851200c041400c0051076600c0a908868005903001003000460040d0203601c1407a11400001690040111031825031840000c1098007070f071000a41c00b034003030252643d00141403451685451001d81c0400c5143d00031090480f404091501d207850000d90b000e008d20301601545008206020054913426500c0c600078260082c00c00c06220b1082e0704a128003035400c882e1441d40b080310301001d003514075000c0c941c2e41c004007600e90794030300040e5400c0740c40d0001c14010301d00b00503030041981f81481401c000407004140d04980d844443c803400c550f0850170510501403d10250340340c4903214400c0c40c0440303007007501140c0e019100e03901d0300142d108560348002c1550302844c1c100340101c2d1030030300b2103034010150f20401c100a0801d28000c07041012007584241c081d07180501c00c90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 617253830 1250 617252580 617252621
    0x14070f110f0c03011b050d0207020f04090302010e060603060c1209160e10121106031806070c233003040606091802011209060b041505030f06070503010b1c050a 70
    0x105d02d0010754a45550140000d10812000040c42241e80140207942d000070600821a02100005800c8802d01305044016035111000c5800402051080aa0008090300545014030303080b03890f80c0c110f11501c0007a84a100c1e001d000f0036101502003140c4844d00981000c179800d196243ea80e0340c4402c2100329807103401200c40710400b00343c44142454203090540c1c0458005203a8045904021281c3c000603e0151100202180c1100c3c2030400c1001d82e014400a4a030005c1e4181c1a00f003c1554029064140b84c2c0c0c41c464404220f41c080c0c00082c0c0f40703020360803911103010700518000c4c00d0710450400020720750030607008070510050107641d51003c012120f05d4807003007241044410907c40260019403005e8049403005800201c2c2201c0b90304100c0c08c0300d218400c009280100400014200d4074128280c04202d0100042030006080410001a151080200400081c5000c080042081c0310501403c81d100b04040703071f860704000c00e072030340c949500c051450203000074a0f204881c4801413507403c603103007021001ca1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 617255080 1250 617253830 617253851
    0x31d1006080d0c080a0302070516140310020306060d0908210609010603090f03050306120703060c0f0507200117070305071b050703140c090906090c0414070f110f0c0301 74
    0x703d544145079030b4002201400d00d2000081a0025084103405850318017902c4800c0d03046002007039500028214900c1684408115101810f24010b01c04404000d034510400900096a4400040e0303520032008030070100740d826072071900c100180030b51035181c0c8618011050415a110300c1181c0130b4826081a14a481940e9942c20308800380d90b140c10340a4090040e01030303c4030110b881030005550024002d4103401502d00082c0906240a08540c001c1e207019560340000050b082e44002c10032000c0f2081d00d01282801c0040c2c41e02d20450941041c001d20420f11001c5490b11a4020302c8425041e49000d00781c44818600041d001d0080c2000721504400180160849071590481c0c04c5080201500100201012829540e0340c04100c8180b001d90403481c82491070300007407640c4048040d48100203140c00383c00541481b0014901d4000c515107100d10441c00e102600d520107026103400d941c0502640750100400d00c40300025150a5200c41c1c402e45540a110364031111944001420382440354282d008000080c0344 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 617256330 1250 617255080 617255087
    0xc0d050306091501030605030a0305091302120a020a031103010608071202040627050402070317090105060f040b04060807380316050c1e0105090c01020d031d1006080d 73
    0x88401039440b8002e030002c00d2001c1d10f1180d108903400018140042d08a0311a00040c0c600103900720218009000001d0400035070801d9149220955206a02503052001044601c0030f41480102110b0720706a01080015036248250420310300c08102d1980342da40ea50b10307884010040002241c104003c10072403088072030608107074401c231011100281e8500d160b85a9a001da03130441c940ca210300010f004200d170008501c5565602c010025030b44030341c4a2250030001c1c9180c40188100041410509074940300400c4031a8880071403440e50f0040446000800c0461a00050002c0c4202d03044000d80d80316175900440c40c0c3e05140d61010600e4030b00d00c0c090030460085482e0070b50392031810b0204010202c046c008a000c1807610309200721008000c0c14050700b031200014101d03207440303403546800c0c00c01002c1d0130795918070000030b2082c0c0d034210300c0300707006070080144000020350b40c0c50840c0c0c144420180c0e80c42005500320300410020481014039000d84001000b10b450300701c041e040360301610f842da004921451103090b02 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 617257580 1250 617256330 617256337
    0x906090c090f06040306020f0c070803130504020a0c0c0f1a09180405120a08040606051801030327140f01093b070315050a06090b1b0609030c0d05 64
    0x4045164600d02960382080c80b8600d150080c41a40050040c44007100182e03182c00903150341441c1c9809036441e14000c0b040145001c003203070700031500794204003d001c100002043c03800069440540c2c01580d00e81070614125124180e000d006003501c91203644c00300d01100e040c81c40004031401d0855488100a00b41c081010360300c6a0082c1341d0784640002032681d11441100c41c526032281c0114195000c072100112181c4a42c3e003d07800c0200003424000400c010086c0343d108500241c80c0585941c0c40170b103a04160041040340600002c1c0a00113003070682d1034401410769421504641c0240b00c50b501d250307200104203c08081812040c801c800b80c000c030341c1701c40d40300d018118100c6007500400241440b40b5480c4003030001c84401225a024051007515450700c01200916000d01150f84c2c00041030b403196280030043d060a07030002c500c81c803c40d501c02c0101940c032210b00ca09550603c4c02482d80d48248103240406c0d602100e1039a07565000b032034200b1402c46004000f5000e6030101900f5100010400441103e0070311 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 617258830 1250 617257580 617257591
    0x3020106091a0405040230060717180106050604030c0302090108010203060d0b07020312040515090c2803051e0606031c030c200d020f0a11120a021e090609 68
    0x45020b500641c602d410b03045241c005001405003014089801d000442514900040c1003803554018010b040b00603041040d030343d1000c001d15048885d000148141c00001d50098104005030020b030b0f41e079006600080d405040101001041160303655541d00d8481d03120807141c4016031154908000004183c03106000b280c6c4201d800400709800f1007100e40d10304c0d44184026040c1021403006002c0c3c0340007420709911081c0154001c0d0014050007a0000710703011184c4c4024107454240e00f212041d00020703110f43c0e207640d20104201440412400000f60303103105d54840780d4805000351007559242c9415072007030000301041001600640721141d03225000c2c550390701c020f102c088650030f070100400740c80f0511035488500d0006003032418090450b4408030102c81c15016400314485900f01090400380f140d0100503a40d01800c40c0307405011b81e00481c0d281d4210340c000008156005203122299549406070901507050721642c0148546a080d03160082c0c3e030301c0ca416003e8464010344108000c81ca140c0b412083d0b061040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 617260080 1250 617258830 617258861
    0x705060a020c06030a0b190e090106242a23060c07140d02060702010f051e07050d0c410c010204050303070813330e03010c03090302010609 61
    0x400510140300d83c0e607100800c0e0140702507641030104142e50f0303440402c1e06d00c805a070105691042c242109a4005c00000e00303401c40076803500004210f09080306804400054050811100614452034240e411660b80b02c0800f25809401c43d040d4015400700c0581000030b4080c80f0842d104410350b4000010030468101c51050301d038881c00006070481c0c0054001c1081030312a42d500c031f050042050303d852504bd1400b1580c005600100308029125509208641040c40d90700800e02a41c101001043d509841c940707800c0907040302e2074001802c6180a9400c48800020321a81002152030500c2c00601c1c3e80c440070a007449190315000000b03110920401030391000250b4625400507200100c050741040ea00c420340c1c444041d5028040002c040e6018006809041d0003032581d150307180511841d08002c4001a0400301c10745e04441500c8111234480ca500b181c516480629103c810040d0702e006070380c0603900b038100941c0356081c0070b1191155941034000d042d041e8480c0e0004c0c803c0039181c0b02b05100b601c180c1c0001003200b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 617261330 1250 617260080 617260093
    0x601110f0a052509111c062412020702040228020616050901030b0a09110405030d02060c0a0503090712060c02210f2101080327090a0903022d0705060a02 67
    0xc00d10507500c1605c40500380d0b50b00d14030f402ca0340480401800914110000c80560300e800800c0414081002c4100084181c807016a00c0306800d0005448009080e07104808294049010003c548890341101c42a40d600d1110310b201d030f00401900c1070030821450401005014100102d01010106180c00e5030440f45500c80c14100070420004500a041720341c1c981d640241003510008101300c140c4034130001480380400855685080105140c64070b50f00d44481001c66102000f0002d12018800540d8050900391074400d90b03030f0700c80313607041850411144c110500080d031298800041040701c0e4000518219a50260f82c900c4210121046000c40402007206101204001160700c3c03010440003002c081c040b01c40c0c407c2001c001420784a11031403003600005080d5000140401c1c940d0314100c003040b01c8800840c1540201c840303010106080030360107800e10160a84601c000401c050007841483c003003203404c1c18a0302d0204c401041c82c159034480313072404d41210b0080d5100480e04d4109401150806c61160f002000f6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 617262580 1250 617261330 617261339
    0x317060f060d0906060602070306200423040c03090605060d0209061005190504030506011a12070203090916030c110a112b020112021608030601110f0a0525 68
    0x10640c421460101501d94030f5101a00203070365440b80d8000b5101740e074000c2210908515041c030458170203001c007a0080c0d114a0003030340010515000ca400f41c0b1400c1c1c8074021403a00090687c075041c40203040d41030b4010300b400184440c031a4182d01c0300030302d03e009a81c103002c0c5807184424804040c00d0504065003000c83d100016029040000141000401d0740c500b40e071030f100ca61b0f4a405c4e60b0580c2d0703012120000b900003504206100081269501500c0280640520001082ea0034a018458030350700002c2d03800082d0010304054024020340d4550f4038003a01001c81d624020010b4048d802c45040c0740e0011030310704110410070074410451042e41603034a0300200038981c0756884200d1002034601159078032000011200300b841c81c840b00c0c1c214410009894140300c581085c800500700d01c049074648806617106101c0a800300140c5030044442d0b6800940b070035565103814004070b641702c001c41c1c1cdd207017247c0c80b813401d007250311000025000d44403901480079078010360150281c40c103825401302100a101c03d4581d80902 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 617263830 1250 617262580 617262589
    0xf070c1202030702090f0109060b030907050f06040b0a03050603011b0804080318030406020a051b13050601090f0b03090d1701060f17010311041b050d0506040207020a120317060f 78
    0x168905250044a0600f0030766400191031190455401442010001c0100300c59043c42c00783c040540004ca5540d4154582012000c0c0d0358606e0b84141313880b1300040d180e00b1710652100c07021540980490b01004da03072140707000005406004242c0d5264000e620b0180c1420a4000101c0d500360442469950709480e52210345655a4a41024100115000d03402102640da1001000284001d1403580c001c1c1c03800c1219030800f241081c0b044045440580c0b5a624070500c01d5030342c040102502900020002806d45590300129a07100098009000302400328030045050101000070750f01c900c4000003111100c54030b0b81c1c4100c0304100b8400070000c020f80f540006005c4140208001b1080c0000b40c5080180345044a80703220804400383c1c016210340d803c420301c8840341d0820307010340700c8121489a2164034096650314010442e00c52580d2094845560b00c0100d0f8440d070311501103900c820b4004005816543e01c0707200751040c015800c00214007203802c0c10544410402d07402c0440388261001040001d04110050521 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 617265080 1250 617263830 617263853
    0xf2409010204090e0a03030e0718020a1806020106051302040e13031211030603011d0622050a0b160918020304150f0506010f0507051b0d050a0602070b0f070c 69
    0x408580d50240400318281030a841100544d01c042001001184410708014040b82d50301180c0306105d801418080c4240d1070890000c5074501c030341d400016500c107596002250a5100c0ac01c0800c1d00d20001c840c00108264150045020313030300200c808040809100d82d0b400200d100398400c080590134610f0014800612070b19412054900030304003410b01030201d01244089841c0c040311107000c1300b008030a014a40c20240f10f501d281c40307130700301e01c4d2550541e540c040d081d034500e0001c1c04145980500700203101c107401210b85a103903040e0b020f41118440001454406411102150524406900e0030b640e0a05148240807410860340560102c807072025140c000a00070f980014030560b07402c1c65000b01503030041024420b01e00928a20140011503041c040001450140c3c17030691001046800c0c8201c0003c500b001c1940d440b6111508406904a201704002c64980380131484050418000e01d00b01d641031144680040801794421392518005544030945a03643c7c0f030007610204005181880030600080034103004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 617266187 1107 617265080 617265091
    0x9140603010c0e040218030609010608060f040c0315110c07080601091103180c09040c0f0b0f031306060b04091e020313030e060706020415020f24 64
    0xd00c141d01c83e90a0a11543d8005030b00c5d5030651801c000c0d03421410015098030001d18180040034005c04051054040d1402340000003031451b00d407810b2061080341d201c0d1104031441e00b191900310808842025a0400c140c0d0340f0072546042a04002804840b40080c0041200318100a030302428101b06a020709601410020900544540c440981341e1002c195010f0100c000650780d9018a0814550002508401c0c903505200c00d001009160b030741a01d03240c4c2d15081240790740b00100c000c03500c2500000400341805102050321001c5075400755450130700078403002c03840b55203c48654038039900940c8100a0196280c00c2c0b1002e40142c0061741e00201e80c001011070861403d1452030392881c83e641ca004040124000e581030065842500b1780f40031030b422075011502c0f140c03140c0c4194a103400701191038001d031041004000c2d03a00c200080b40307008c2d0140a00c0941e13201d89280d8510543d034201511 = true := by decide +kernel

theorem cover : BRFrame.Cov 617086330 617266187 := by
  have h0 := BRFrame.cov_init 617086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 617086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 617086330 ≤ n) (h2 : n < 617266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
