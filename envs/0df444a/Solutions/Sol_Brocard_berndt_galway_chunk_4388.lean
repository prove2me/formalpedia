-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4388
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:36.445425+00:00
-- url     : https://prove2.me/submissions/8666bb9b-0d92-48ae-8f26-832e201e43ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 789028776 ≤ n < 789208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 789030026 1250 789028776 789028787
    0x120b0f1c150c051213140c09010b04050102031e0403050111040e0f01050d080d060503060a060608010806010501020a030809150a020301051c0b0a090201140a090f09020c07140d12030b030d 82
    0x414a403640d82d981481c420302e6004002102c0900b1780c820040715102540082030200d5582000400507100401080042d00e040c0103840c20140e0000503d5802408100701ca0398001c0120740e4107041481d80c0b04500500540c000140c1d0246400c0980203600c0c08412900b020607410082090392850420083d05a4601c6105a200e038000d010342a00401d200d6013603000150500c01901d1410003081d004a825501d0300042481c108003140c0740009107481704c00421046070006034840c017411200c80542025814280007170360f1001000e1004040000d1030000600740242409820245504011488000d04110341484003941082c05841e01c507910034600c1200201c5a032108034401548031051000c00d076102021034004049040042e4148110003601005c45d625020080220b07046179103400343d4641c00c002d14106210999040704110a00c1009038181d50680051568101c0d1020500c08289001000100b034500d41c40d0790008041c000d480310102005a01900088000e06082d4111448002041e038203c40303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 789031276 1250 789030026 789030041
    0x14071703061f02031e0d050406022a031909081603210e150c03070609110d050714060d090b0702061003080702061b06010306090507090c120b0f1c15 65
    0x340c4d0080101002c0c22481e00c451440040700103a62030b0404124800c0c070004d035a411507003103d8003a800542040742e401d05581069100740c090f2407075262070b202c41c00c40c03540c3ca10540110307206981c1c8000400c80c0c0300d84212a4000940b1001e41601c002d00c28103030201c4501e88250008503000400f1150b08101c5021030119a21842c0b80e90341c4000303114001d90203000c143da26142c800b181c011000c02c0500700c42c2c0000c10091540394422840064004201e04200030791050070007200d4807a0042c0050800440c40008008050341c0340d158803021029030340c0c000a801417061034040ea00e42802e103008401400414a0740620441c1a40c00b541d400b036175180d90b9481c4100301800005d10301d070340a120540160400c0d90150005451071154060700c500306529851814030b01340d00c102c41c3c040e20342d0900000c010050050000422041c081030115102843e00900080301d03044248084035901c84103060165640d45280d9401800640f031401244503580d02c40416854883c0140c401b80501c0142130703c0c682c4540714001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 789032526 1250 789031276 789031339
    0x212120901021b090a0e19030c0b0703050c07062703030218100c0b0415060b0a0e2e0e0604080304050411090a031502070213020d1410061407170306 65
    0x3500c40d40c45c81d9503080105889852002c1030300c28103541c8200e03c0c0e62140d51228141c02902c40c0e08214400d442d00c08541d01c00109210200b60a003000d00104000080070f40b114254004804100f14100c081d45112504200080c03103124601000d9007814190994001d1070800340d004130448814280c01d00384400f03090240b00d031400280c5882aaa00482c04c08614141c1161255100254014903644e029080d40d140790020b103805080050803401e21a00721444103000e00e0251004540c0600c00d91610b5044030410845803e41e84400c0b407000d85031172054034004c05007000201000c2e01c0e10344805106669800c2405021301951030010791040c0038015600303555802000a2290161608683e00ca80c41e02d0240500520b8158080c010040140d58032255100300000c5c6400050715151302002800594881b00c010504001ca400140f1002003107843c8400103a074901e06182101a291401e000103901c2000c10241c00d9003081003034054208110360080d4000d010840b802c44900200007a40396400c0d00d00c0380c04a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 789033776 1250 789032526 789032539
    0x7020f0c06030a1a0a090b011d010e100302070516050f0906060d15030606030b15040b2d280b0f03010e040303060b130f0902071a040212120901021b 65
    0x10b0105903041d000145182030f071110f0400e2a0050703c1c00f0840101907900200e06d403d8852055031b0103941d0043c0c025403c40000700300d4080b0701d102c1c0000039001300500d91119004a04000201a1440c0203070110b07110198440210f45c08103103441f234429a0750314a8000c8030b101c1d0000d201012203526041c0b071114011800109500d150104d14120b04c4000c1184c030080441c07030840c409001000c43c110b88100c1000307501491082880c0e10341102d61010386031200740350701d21651070a28140101d072907112038118150b0868807031700c200900884040038451641c22444e6884040b9107544122202e0b43da1b14543d00032800c03c502a002c50702c078003e141d2240a00301c0c0039540010103000401500c0c228490a40e0814000e08002072555100e035510340071a80525644444a0442c0208020300c16203004624000d005144085003844215940c803541c40080c98240e2000c450404041010b40d590640c07082e1000c04180c0855501402c1c51003885159040418100d0140c028410b00b0b80d070200d00e9615003000240002c140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 789035026 1250 789033776 789033781
    0x705030703080f031503071206050c0304080702040f1821021c180f0801020c070510020d0509060d0c1d0612040b04050f0d020304050301060902070c031e080f0307020f0c0603 76
    0x2241ca40e000145818611801c5203042101794800b4800b580180c00d4021401e048507400b810305100341c42024150340400b910401c108804554558142c9000c03541c100c030040f81e00703d034803e0380c0d10151101200030070301c441450402104100c100b00c0400b48600803034000300550504924141c0c0c5500c1d100440c42c2c0d001e003c150f280408640318010300d604102c06480801140d0791190107815140ca00350f04240c00d079a40c00a00329104800c1040500c0c01400210384100b503e03581000c00a449840d83c040000c14413102103002d141c0c955941c0240c03030010070420000c10508502c441c00a240c039058442d001601060300d48081d1440c203021081314252005000d854116854075560440d000500500903255400785413924030354040180801c61480c1c45541c000c5849909060806085a1141e4407030b040261040040c0d50010700101480c600b120303040b01d02500c015404c1110b410f540c0c00d107020b00a02d800000202e4542c440e8160000d14082c0110707908444026004d11b00c0c4594407040000e41a6004034180300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 789036276 1250 789035026 789035047
    0x12d0e06100e13050a2a260106180c08360a020405040b06011205010f05120f0303040503121f0302060306060d06080303010512070b071209051c05070503070308 70
    0x4181c01c40c0c5601c195000c04090741d04c4160501d040303000212200d02c0c503121200c00001e91824030340395100f00d0112182050385000070f1441c2010504003504076210700300c1f582543c1200c00794001001003d64503600011150711518140091640103444800700741040f020541c1c22110004075038206081c001100200208480c01c001260030020b40c0d00c0e511300c2162540720050300c450150b1070260303116520070146428401c002405501c0985a0014218901001041405c0c0c22032105812990141c40082c2003459600c04203040920036a001c01c440d00c03002082c0400c121000000b05284c81030440c280c030301c648440f00c1241000c0401c2140541d02512180244091325000300207580200c0000d111030b28240c241820402038622a5102111581000c8010030581c14120000e10f81d00c0c41e8500074203411428881c16030998000c0364005040840841c043c6411725000e40e4285014000080c08200054480c18528809103403a10040307415002c0d40b80b000803207080c00600d8400340d03a4030200c124100038040c00e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 789037526 1250 789036276 789036299
    0xa0e15090706091a1e16021315030615050312030a110702102a030207090c0507021509040908042d081009020a03080309060403090f0302011205040302012d0e0610 71
    0x10f007034001721071011407110760a00130041200c0490007044480d1054980100409400c0f410341020045007002070302c900350b4000c0150403042e02e500090006a5400d000801c19081c03080ea0019034051103500e4034600e00034205005184180b44040050202c000340a40c0c1100390f000e6410000d400c142007012802825029440c8016401004013200040348010050a08201040741c400c0d00941c00104040c0b01d520168004c02008140380d08080381303009001d501084206048084035516031001140b052900c0e0307102d402c1003910680000c42c8a84480e00d441610030300200b42e14005002020b86217510201c5103032009650210399007900039190700381c11072109102400031408200e0f0b100504c4030001c4000750f03901010394000c0368000004c05007498286005000d00d5485d8120240d059004001000140c3e8400819008100c2d0aa00441c031611a85002c1c3d001d0401704050001449035a060300300e203040880d00c1c4c03120040c0e0b242010f1000804c00700e122a12103d00380e032181c03000c0300c103000240001d41d145c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 789038776 1250 789037526 789037537
    0xc0b04050a2303030406030b0123030103031407020324310507091103040326040204020c520302040e1c081501050a170a0e15090706091a 60
    0x4401c19001c2c800c0e0440040c0c20340e4404d400060209039506010016547e01810780001c0c07002a04200900510030241c003800e074001484001c00304110001c61b205100014026190502c0c1c0c041c0884292140403e400d1000c02c280008081c2e0042255000442c0f1007030342209180c00e03501e050712011344101013900003000030110710016a40d6118000c00003c205495200c0e0f1f42c501c1020245050322800e040c40e00414812a90502c0c2050440c02c01d41c030706885007200324440d001907040300d00603580c030310580b0054100b00055030040030300120004414060b07204c111400c034840c074403440d002048407422005c00c809042d14038040c10b401c9a8505003400141003070383c0035a03501e1000000703e41c0036a5560086c50305a02c2c12855500005a00c002808440c1c480c004190007802c00908045042203402c40c001040190900507491030b250050340070400700182a1301c590714890f80e400a81754004076071b080075040c0302c01c1030b240c5c940e00d40b084290008285100b030450750259040320702000c0a0b8421005007060f2904603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 789040026 1250 789038776 789038819
    0x20a15050c0702030a06060821030f042f040b041401030b040305040e1005031203041a040206040f060309120804030203070305030405010f0203090a03020f07350102030403020a0c0b04050a 82
    0x8201e02c101681d4208000040355110b02c0c0081502c6041580c00c0c0d04194a00104800c42c0280480708100f251141303080e40c1e0b001034400c0c00703038105035540e081a0304000344114110315040a400320f0b0304109403645080d05010641a0350a05c80b0019860510049401c0c00710b80c182402d0318040184005050414019001b03802407408174245601c2e04c005c800003100a460000d8980001141005141014492803403035451019601e419803510b61141d00d0306901c2e40115210b0303404200e000600b150360301800c1d01d024184000c500c9034801e440d04d4000d001070080390410303180020f110300081c041c2807103100c807940305c0c952582c0a1420070761207a0302900c085e000600102c44654aa5840030440030803131000e18805c074100001044154207504029081022990f1100240d402c00f42c024407820750a000d455103030682410342d0b8880d540c15400281420034200c207210080754000010321052540c00244040014010f401500c0c07216a141144402c41c4107900c100c9410081d246010001c0510746000070820140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 789041276 1250 789040026 789040051
    0x3030c05030d0617060915070c26070201031107020d2010081f0e06120c0411190201060602060a053d0f030c090e10050a1407020a1505 59
    0x29030b92992060f18035a82200901800105040c04003400070040550000c1c00c92001d02a100390821024508941c020200b0702800501d0803280100145482c1c8105200d410703203c001690440103c1c0b02e60241e011000c00d90009040245440c0301902d01c0049505060340105803205a00b5190390b0081c0140c03030290704004d100560324280100d070300e4544200c1d101d03c14554070100c05144c802d50100f40c000c9042400c05a06603000700c00d10001000e001596001841140c00c039040130441c8940e1f514040b030a100844c0c2003818002000140c00b41040508035040f10700000500540e40e1280483c00c0303c50610800c001a80004080350300070b42d20f54055900301403900c2d0040702e60a80c15004202508101d081040f40c881c40321780c689a184e0304c4940000c06050340980300d080c00c078178644540031023240078000c18003129602e9014819003038042140b004c1004030506c0901c410304e024081c1100038030400304075981f40325410000a480a1020031407134111036100240001900c102c0c0d4501008201c002c085101000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 789042526 1250 789041276 789041287
    0x12306010c020117091e06060f010818010f020301032d03030b0a120b04050105061c140313140102100204060c1523060a0f0e0114032d01050c1303030c0503 68
    0x48413400912842441c80100401c030702c00c01c10480d10403a40130142c640340d013040e01032260a59031010902d140200034038081d48d1035142ca01641c4035035003825003885065031130700962032448201a005541203e0092801c0f05100c00c424403603023098514000c5030000f0044080004002a01070340c0162070142024010100180c2c031a09000c441d004061016280c401d425020441000424000c0550244080e01c0e450690407030880f40c1c0d81c0c00b41440900500c80482d01c03130b101c1c11054040041c0c0d42e000440e8441c004a82c2d82c2da410b5401d9480c910303200ca070700500600100d809604000c0c003c490484071a0341d18182d2046094988c1011104201008100c41e61108641c1c8000c07141209580307007105c1c01c82440d00c0d0300c4c1071140c20806c031604503034402104405158410800c02081820304c5044070201001143c0555503400041d042c00d0003101070340c142c100b651a2100300c640c001e0305101552071a8400800068540b8100d03004075014083c407c1c017040090711340c2400041e10881001c0f1010703106d0000c490805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 789043776 1250 789042526 789042557
    0x504060c0510020f030a0b191a070227070306050901170a06050a020913060812030403090e0403210e0c0d020f1806030d030506131e090b060102012306010c0201 70
    0x9034401040c0c405083c20100a0140b40c840920460710020802c81d12840900c3d22110030103a48c06041c8a002441001280a1405085030004984000354010405410344109585c409003c216070031230250441200d500244142d8040d10070802aa10300034640f01207a80392500d0040301d041408101c9103240034840c440700c0040c44600801d400b801d2030381e02c050f0301c1d040e280003880b1205089000390103076103041040801c000c5030b021400030052032030141050b9682d40d0301d08041d9054403035607000000b1308403408200000c0c10342c0040b42d10030342d52119060300200d01801d007100051b1503030504592002e4004503010303991864005d910203002c03440078241c41c140a02d508006580702001e44407074200ea2600314108030f1240340074031402003024440d003410011814440c000c40e001004020114a00c02c1d03942984a0240078001c9180007090510b00050007140d00900e00801141400d840e1240075600704140d018144d2009100504a4901000c086071150740b10801100c6003803800205905021001c2c441c010003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 789045026 1250 789043776 789043781
    0x1216080309100305060603041e080a02100c26100902070602190518041a040504060b1e062508040b030105030c011b061a041a130207030504060c0510 65
    0x9155020103962a41c40a81c14494081c4400b42244201450301c800c0141c01c1c2e560700d0540e6001038102070f40241c4200038043c1545a0050b40101400f090300214080c130340030764001150050000419018819400c0d902829542c402c200c0341b2070220300c0201c40341041c00404090400b0351110041d06072412550ba1040b18008a81c409482600c05540010760001d8072031509002c1070000409240c110301d000b106a103494454801c04230442d11036521404e412013403000c00010a48081001401000181840d1034244001d00506200c98011000800441ca11402a107446001480054849441c0c1110410780c07281c0d010980389940e07648400b22a02c0340200d0034000260004c0c0074000e0100366a03504101c10180b8045180032058104820b1242d40c10400000c3c18011900941c40040452040a08420034010682d4284000d40051a10b405050071610400406001400030b0303c040680010400d406010b921465101070007241c001c1000300012849000008000c502038804da504424808038071006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 789046276 1250 789045026 789045029
    0x40510020c03010e0d021b0f1003050a0605091608130f05060708060904030905040b03100f202d070210080702010b0301060e15240a110613021216 64
    0x59100c611800110304091040c0e0a03000c1e400f0000b01709090b88000300130f41c4c4c1c00c45248650440c81c07124441c07010580b207111403c0c6c4a14002060441c0e55869070800030001e0004545011045080600008541c1071a58890b40a5030340c2c1c0002c11000701c5440b200b40d800d01009000300001e00d2140080801241a81d0003261100e4420800f81c20541009000180510340c060100f82c401c422110600000a40044c80d5000726078060300c003c10807000c3d4000103420700312140e1021406a003490f0001181d184181d001d2088481c40e00888505030f407080c5400200e6000d07410440820f10f1301140310b48060000d00c40707080d4444c2e42c01400c003071a00007682c0c046030310b0300a005102c6010a42880034480c900b50203000b015a03080040d0300800210b4506288034440205c050841b902211080700e8003040d5480d50381840c0c44200c0c40c004c80540c01d00d01841c10130180e0740706214517400201c1e403400c4800d000704040f941034090300c500282e29803015119001c0003116074061040803424403c20003507001392003c541c071020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 789047526 1250 789046276 789046309
    0x818030c100902131503031d040f0e0f0c0d0f0f1403040e0601260604020904090507030204060b13060e120609072103140d1107080d0b0a12020111030405 67
    0x40c0306002c51040c071420140c02580350450380d081041082034142e02101d031000b00c9405240410040e4400c041c24170240c4400e1b09003580141c02c1040700032040140b40c0005000c203d40300100c450141c07032004260f1320342c680c1c0c0d03920503446034400c040c26001c501c4038100446100d0003074540600c0000290749849200350401014a42c42e0800308040003110107410700305030f0000302070230303d03001109445040c20a1a0307100440388030302c106400041030040e201c03a8190b4500b42c001400030859100c880c14100da4504051000703e01c00c1c0e0030088042000d07410b80040c0d03240348106946c4007401900340b04082e181d450381c4c0482d0700e4200034800d039549800601040748600031500c440103840064101146860074503444024918000c03400c964040000f94407041c080700383c0402442868a07004544103410140040b200001c281c01d0001c02c84800340010f0400030800c54080710307400c101c1303018198203001c00c40c08984100070422505e140054099400707035890106240380b0718192031800d170312040090004200484000f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 789048776 1250 789047526 789047531
    0x3200d14101e080c01030911180901050703020901090e070c0606090219140a0c14010501150905032e0f0e0d0e0a03020a170a050304121b060818030c10 66
    0x1c110016800100481d1004082c4a9076981c0d420903102c81e955200b4480c5150400d540c07058810103020503200c1c2c0d040d408200910fa4032800300c0c480d40c103a1220909940d040740c03035440d01e030224481138024400c03521260010b859075030b070551500403000303a0250005e104100f4080350802c4800003900c0ca00c02e100c0500f50f00340c0c00503111500140d1001c1d0990070003007140f003404140d03080c1c58624000041581d1149041d0302d0250786c0c600d0a032418659814660b13a0647c11582444001b04012840c0100f03191968056a12042625610400c02d5500e001a42e41c011201900310344007013541c0f030035040085c10790850100108481c01713100100c10490385000c081001e140c110184508035607500001c0381c0c52440f800c075101030348076040d0340015030300301c0d05841440007035080b15100e0081e540c2c05100110045400c50705a0341c596544180685000002e42000c0740c07800c401150313503107030210220100020341728113035102001555081d44800082c280050401c200380300c1803081260221080204884210460001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 789050026 1250 789048776 789048779
    0xf0109030c03020c01080103020a0b0f04080a05030316230307031509150915061b050a0b1005060705060c0c0c04061211030a03021f0b040e0f06010603200d1410 70
    0x2030520b1000c844617410812038100400143c0c0d42c0104030f03820f44010003043c0782d80d584100000203c030300c41c590180400b809030a425005110700032000d18842c1100419030040d003072414008850031071942c0c1c00301c0400e2400c00420507141109402641d0310503003078100002d0803a00c000c4040060750340ba41c00784103100d450b001e051005610301c0d10b010b40180380c08001800f104e03181d403114141c8005a40210b004102c2144d101904030345c0d4066180417465082070503030710910680d0070300d0f07022140100c500306d51120045000141a007801e80c1100c411507080b0010306103545524200c070401e98042150580e030352180f00c01e8024540e44500c42c503002040e661000c0b42da48078062030024074030550f60503407038440c1c1c00540240303000c00d8000c03401c4003d5040c05901d540800c081d1040110080c00c4024910307400500d480744081007140000703a8401ca00304105c0881d0310300d80e62014114103503044070038026142c1d040c13140c0038885c2800c01d03000f030809200c8102c0085014025100c0f07074100e00707008441c410380b003013400e690 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 789051276 1250 789050026 789050033
    0x709031b0807051e1005041211180403051603110d08152d06040b0a030b0310180206070c03061b030c050301050a1404060806150a050423090f0109030c 66
    0x114500418040d94000c8655038010144c1d154400c030100d009000d03400c020f58040303c1038032a00c2141c000d010240051481e000541c288000802d088042e001d01400d0504081d11541c50140245403146506990705842c101081030b0700f0b000345500780b00c110203010b0100805036031550188040900c3e0100c940d0f0349202440e00c01e41c2d80190941e1103010034000c0344880b20501d00460003071410214542d100c0001012849030001051291086078000807410401040da0b07060241d042e0801d00d0395030001c4040710b108081c0c280100342202e0b040045490181c2c0c6004544005007045005800001c4c01400c2a0300c000d0b9032511030000b559119885908900b203a1840540026007500c6010324640fa40d1600301c1c1158144000700714541614020484a035040080409150351590041c41c040d00e2104252074650030950580358803036540394a0765200b07108901006c01c850070b040c81100d0f803600031054403440d4020303d0f02414010034000b03043c00085005002c20108810024024416100d11035603400e5040c215504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 789052526 1250 789051276 789051283
    0x1a04110d0617030a05031f0b03090d1404090f0e0a030926030a0e0f130c141204020d03021c02030304170a09091109030a0c030c06110d080709031b08 65
    0x10000c400b0548590200b02c40d00c4800000d50f481e4011500303042c2d07582d8440001c03800501035400d901f0762503c0302140b00401e090039800d000d10700801d100c0c01200c8085441120a9801d100c0152180707400c0d45040c0000c100c02c0109400000a100790784030005403a04041c81d07540d081c109000b05c00d0b00403600c01881046030803088481911309a001d0305501d002c490311a24603907124403400c03400c10200800159076480a40d0340540c0c0017545140140030504100c0c00a46403c040d04c9001d41c210045100b499000d450880e84200f143c403e8501581d401c0191343d656030030030140b04c00f2080150110b11621540e54600b002421025001e0045c0e42c00075601ca142c0b038603000c0030f00c4182c110050b04682040c84810704d1241c20003c1700702600c01145020907252814900132405008140e082c82d03041c8900300c0808140300614440030300f643e025005412035140c0300c80041e6411842482000c1d82603201131000703100319100e400502e802c0030183c540f1280066490b2075043c0381c0c072050304c0603620100c4401d008000390300c0d080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 789053776 1250 789052526 789052529
    0x60102120a0503010312110313050109060302090d12050c100608061312230409060302190509040f1514090c041802010311040e090f060702010b0a091a04110d06 70
    0x10039000d2402448400040240c041884001c000b0004c568001500c079009070504030100c1c9080d012280c81c2d0756905845c403004c0f0410311840e800b00b00c002c0c5011030114441c4c000c413100c07002d018208041e01d524a80d290034404030107941c0981000b0301072001d1408004113101404410740e16203c041007083c180f0200790b0402000bc1c000041d101c0350140c0740b4000400e5040410396000003401e0503034007070f200c00035082e64100c454295103038007080c0094003142212090380b105007940d0080c2c4a054a1102c0c070800507100d403480f03000d4982d1016800000070b0014400413022006e484c485c5509086100c045100c00c01034404400c4e9503844c0340c1007141000541035042003080d420400c100c030180404c22011010f42c502e4519414080d04240c0c41d003420b4008441d1501c1194010050440ca000395440e1141401c3c0d00c0d600f20300302c48a1540220404140143d1050043c60640c02000b041802860701c1d20755010010714021301d00c160f10b1280c01d462060159254411880c3d03910307406030425542c9008484807421201107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 789055026 1250 789053776 789053803
    0xc05010504031208090c0405070c053f040e16031a0a0b1b06070c0b180606010f020a060f0203010f06090b03070305180a061a010f0f080c07080c06060102 67
    0x41c4000c1010400c10740300300d0364082c09030402d2106a140c0407000c604203100c0000700e5800034240014010703615442a0894229802a000e03100800c106000c0c04040d090f400c0d000b5058007901c20170a000810a00307004950440200c0700702c42c9450ba850200702c440c00d00c1100c5031035035002d40c00b11141c0415054010f0f00740c0c07685040000083c00b1800300000b1415149805102410440801c401c1c0c0d030b0036500200414484407000844025103000d40c00107201180610085601c0c01d598008104c0040005080b55094900030016080325030302c0c8001150740d01094000f210441c4602012000401c146210b56114155441c8000d603032076041034070403502001550b0005003048880f810411843d03400e1000d07240c0040c050700e0040340e5911a6041045861204903848010780200139440b410894164800105a0144051940e50303d84020055544040300d015400c08a60305c0f4400c480e43d00d01c00e920180c3e22641280306035050071000c0d20341901c60b8009040c0041640c4c00141409034640c3c0400c03058100300c49 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 789056276 1250 789055026 789055037
    0x15200309011d090a022505011a03030a0215100306020310060207060e03060417191707080106080718080703060b04050f04022d150735130f03030207030c0501 69
    0x1c1a00203e481440d00800e0f602030107502044603c2c1d004242111018803443c43c1c26001c40c01442070601c0c6000b00241805010100d0116124014606000c020345920700c0341e0742c006d0074240600e0303804014980c000034401b00b0000c80000010000030310b10700c042c5000f5800705560140c040c1c04d0150203442c24090b0b03049101401000110b01c11660360000d00b1a5206501c140400c142c5106e185c88001030f03000700550ba00c0290500c3c0d2030f42c220b05521603402413210340110442c4030251107009040e10411000c1c011780c0c1c006000f00c40020400ca0141c0351002d2500b8855000e24209903545400c3c03420960309400448040381c4625a0b182d40d4507240c0a019003007141e05407413641d00d04007a800100412082519241c2200c0c11200e09a041c513800341080e16910405000c09000804c0c4e240714446542c030484044880714000060702204c1d80f0320b00c61190300300b84020000740481000f4403000c54907401c8041451149016260041071002c50261190025482a0010702d0901c5c250700e00005543c455400c550304101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 789057526 1250 789056276 789056327
    0x20c03070602280219060c0605010b030402100807022e0e0721061116210e0f0d020310090b0f060a0302040506060d110301060f05070c1520030901 64
    0x303054061006070f511a001c086403d54039601c0400c44c140400740c0f020752056284400003c0044c0c000c520b003071401d48654410042d82c1c0c1c0324010405503000c1920069000610307200c031420454080d00c000c1d030b08943c2c2c1c2c0c0112980400586000c0ca902c00f0140f010708a00554031012000541c8240100d982c4095942d01038400c0030700f402d07410320506c4568044018a003410182010a00c5460360245200101c41d0402640d108541c04ca507a013099505c1c4002c4410101090001d2600d118400380d0b40e02034910303591500180d81c2c4003c100140407103030450303ea6101102289410041e03608001012a81e01401e0022a40c8001ca050641540318018100f518101d202c0301080f80e1681c071100600256541202d0000f0b96484020115a9078051b000200c52003914168056081c3c521081c003a5049841c280d0f600f0162014003201100d4500928500400b0035040342014800703c030710f6540551b0303804035520700810742c50b0f000e2122003402c01d500c601c03602c000e4000052403c00c42d6440b0101c03010000074040301900d0307030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 789058776 1250 789057526 789057553
    0x2151b0a02030c2e020c13050603120d06081906150e190209220f060e0a0b040905030a030510060c0807110301020c010e0303010f14090a240303020c03070602 69
    0x81ca51208203a200310500048104140e22180a44d0101012504211101e583c00140030390b03191a5040902d2145460f00c0092405070b0044c000c0c644505030290240030001d4000f042c1d040641c2207034800e0090291901000306804108214180c0a0840c44603000244130b280c1c1424411900070100144020110200c24004c002d401102c00b1b42049031503260b28a495801d0216400a000301507840d5403100c2d9416524040c0c40154203000a03501001c2002c01115000b43c51400460b9054070800002070030a4000550070301031a40400102400500042014807082d603e941c2150300107000100483e60b5441801300000d0801d10f001c02414990030f0038101a0030a4440d84071b40d00444400030300c1c100300e50304058203a850a4056448188141d4000d0105820002c101510303034100f4010076100b01000c00b030009038601d4507458a018020064a101c240780c40d048140809425458605114002103001d00c45656056503401c0000b103001c0d0f409455246044c5080508000c110b074840807c5601129907107148 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 789060026 1250 789058776 789058783
    0x3160e010b1608090a050405150117151e040c12180312020a020f0304090914060615030702250e070e0603060f0d0c0602010605090c0c0c0108040f02151b0a0203 70
    0x1c0580003881031362104200c0300015403401c49a007100b41c10a007808144031800603c003610480c0c4540c262035a10711025540d1400f00c00c90021101009540e43c0c00042c01824204182c5030b07050348100702c0c0c103101c004d903546e004901500c4ca11500a80040d20311505552186060700c5010303c03030068080300d00c0700ea20603920010082e045602c0056032403039002401c030b03003c0c0b402042080c00660501003640e032580e5968038000700400015009490491003250000c07080000861028460440100b0300d504030104070801e01a03c0d00700034120001c0d849506200c0e40f22451112001c0c0350000300078000b651441c141507042000a0014103803005000e019210002d442d40c41c00706070782c0e100d074059075000c00e803100e0b0000054007024414030203032540b40c0041c170101c0d41d80d07810340240781075941c02d85042220361a0031003051400d00c030b1441c00c021103811041d1a4200e41d03104d004e640d0b4010307019642e6111440c4c1550001410000846021440740d40009650421400001d4814042080a10107130800c01ca460f0040780c0c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 789061276 1250 789060026 789060067
    0x11505070c260601090b0103150509070f110604050709060e0402090606030615070614010b04064a0108070c0519060e07060309022409040b0f03160e010b 67
    0x40390700d104001602c45035045920944415103440884815580d107902d5480105015100b4600283c2440c0f4110383c0030b90345041040071900064075803e050381e03814208451030384180c2c0c001020071404c3c0e5004440c500342000810702540c0610040c11442d458008414121011640003480c0e8501d1682003101680d562805568400760984405135643d469200240914042038411a04100085070a000384032665001c00f5581c00d0325100038280740d813100c00920050003503202d038000142c440c0ca003844203201940040c14241c41164009400d2407190b50002e4100708204422000c82d94840c0940ca0075981e110341c0142c0c001c1d0780c0d810100c00c0145161030701d54540c0801c126038241e50001070030f01820016142c4c080569556103200351182c4984443c0003c01419481c0b2080e0710881030030a001503030303119002400c20396100b86201d60f842e08041c03d0602c80500440884103034086002d0008514607103052005024004046505021050802040d81c802c40010381203820518000d00550721294610006c450b03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 789062526 1250 789061276 789061289
    0x1507120614130e03040e1f18200c060a0c030507020c0d1104141603110702010f02070305060907090509011a1903170a030c020f0c0f06190503011505070c 67
    0x40032001e0b00c080305400380036944080c003040c2c0300c00200090081c01d580d00b00f40c014680c6901c104080c0c81039103600c0d54a24424000c0c580c4d0414100c000f035140005a83c000c18070b01c0841811307984801c400300702d43d2946030007503001d10655410150401840264510892840201e541800c1290742080040207607190071491f401c0e4080d181040d040c0307060040180744420081d10060007844070450b1213242440300311007650110480080740100e0a40c00b0302074060300c05254540c564560411006400461702c1c0e03400220a00294090f540300480410420b01c01d8603c80c1082d40d00403d0070b9031610710396004490001b405d11903503914140780c10f4215a110105e0720465182201c907100001c040c0c41e01048a40210fa00050102c03944420501301010244003410f80702c1682d440070001c45210341000c0e0385481e0354100700b007215085030300e0429092400d815003244c48500035200b203003042c80790f42040d0298030340300140101203180400100000aa44040c13815590f8003442c0c02030030320103a030380c4009100341c3c2d902501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 789063776 1250 789062526 789062539
    0x30c05010f0315080c0907030c081b091207050f01020a0c1a1b07051e0f06030a0f020301090506030d020f070501081302040c0c1b030203100209121507120614 69
    0x141000303120381c10001c01d0510340c43d4201c02c000d41d142d0440ba0342d0700704d0150242c02810725000040c4864002d124810303071911191259890f44c0d81c0c043c0c0340300c205440e0000705010f145040c0300c0101e840d02c64501a183d10000c18009203646800c0c0000c03c040700c500641d2950456114001ca00d0000d210000502d089500072014600342c2100d200080001d070042100b078a00d80b0b050152240404040026044203c0b58141e80b04c40420310001200001c1d480041500c42d0090714040c40440079007446001580c0c003200c02d6000203070480b400c0000c02d059038130070382c00300174216119414040740b45018042000c072500039000401e0880400e00b90182c542450340302e01814040c10078001400d5110340081c0002d0580c1c014402c10903040b018a02620b40718071040c040e200c01300303c102c01c0100800088004800e8980080044c110390031444540c0020b5404810704a41045821861500c41700c0208038690252454401d460902c0c503009000614a0084505000310a41848e1007000000d0b20700505500d00350702550503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 789065026 1250 789063776 789063797
    0x30a180b0a0e0f42210c0d11090901060f122d0507020717030405150903070303080f0f13080706062d080f0c0108091c030207050c0406030c0501 63
    0xc07071318484008243c041107050040c80c02080c283c4440c003440c26140725115202c0031580607103102c2d540119a00340352900d845000b0003443c14894031006501c0202140c00f030b4501902145548240c43c1d04907a0041d00d4040440c24003207616002c107003240901054946070102d010300707490090901c50081c0a105035196a00c1e4164420314000349528810700c0d41201100480c10f540031030300020f040442e6018014003c081c0c012910901420100d15030498500046003454286800c201c400345802d0070f045180401004901c119413005d00016000794000d0700c0e01e282c0c9141034001e581c07411400405400706040303450100700c00301e075100e1203a030310543c1c100300003070340301c24151130303da0001c2c0002d40080030603081d070502420b0b0800c48a00c140d211400245008180503980359170003a950b00c80c104a131607607a0403d0303064201c0da511036010300341d00120040c22a007245c0307041204a0307002c0e03548031442e0300003c0c0c00050f00d01c14403104100b2003850f0103058500b00051465620b61032103051890145d00c4c10840e07000e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 789066276 1250 789065026 789065029
    0x41403041a09030d18170118060203040210050c06040b0408130e07020d030618021c0903080601090503030703080705160c0e0403081006051812030a180b0a0e0f 70
    0x40e03802408401c1c1040c0719004004a064a25400c64440741c0d200e8030410718400303903151140d590102e00c180c6943ca00e1110508002601c2d64407248405071800665840400303540700d4407a001c40540d40d40c0a104016501c1c00c160050003080c80505070000d060200410806001807800142c1c42e5002d1341100c0145e5440c2ca507443c00b08180c0c401c510b02e4194200c1c00850200d50003242402c0385020b00c4546e0215500d46c02050000d4017500c001e840355005031100da083d03044a43c2100d03002003810005a001000c1080c280f00b02502c112808038900707074000f80d80030b010084c031540c01c10ba600000d49011002541882070740d6030010040a4010040c0c4d041010108440b10b81415440c560007465520850b01010192503002d03040040f0411101500002c00400204103203041940c0c441080c0c8000d030341c0709407522591550b80d89480c0410481e81c1d812800060303130102d43c1101403000d41441c0300c01c0c1d5140300c4510f60407503c103245ca1815130080403203c44100101d1030500d8000b03081241c1000d05417240d2048025650 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 789067526 1250 789066276 789066283
    0x170d030c0e130c020120030402190305030d0212010f030b04020d0813030506040516060f050f0f030106030905010b03030f0405011202190807110106060f0513080709060e06180414 78
    0x400094001820b412070005032100c0b50000381408070300754000c00504200f4001c1c1c280c0152400310800d07002d0010400b10b80541455003c040002400d107075078810301540c82c1c3d0340c0780c5140c7c0125000f04040390702041030000e540100c0c4031540104902e0403100c00703850a42d02c41c040ca094015000030720401d89a0820310800007248141c401a003100411608010350301d090543d100c5c9003c40307080b20705020380c0342c44425140494000300c05407603880c0d44010540e4140501a68a9407250761a00c03c2400c082c0036030280da907400300065010b04020341d804610340b45589080c0b0700f03407000048070074070980050156080b030b03034184803c0e03404442d02441c14200c000545080c0d00001e1040c46801c2c51011404400030302d0461b000b140c164010a0f4a42d500720356090403001c0c8500f254010f0061a0005101192120200380301d00b0242103c0f2640c060074010705662645494130304441ea84c414210140c4640d01005003516002e41580d001d00261500c45620014210b40b61a15000401c001c2612140c0c40d542c410060b02003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 789068776 1250 789067526 789067547
    0x70315030210030f050a0908030613020c01020304120e12030307050a0c020a03050102070b090c0a17010b03070f150e0901030f0c0b0d02120610171807031b170d030c 72
    0x24100307450400002c0c0000b40034100590302465800c0c200000300740005540d10558080e5a04143c00a04585842c7c04001205500100041029800b80003c0c07a05480a100560140340f1804416490038240440a01818170114000e4800c1100124200c10039201100b00e80d401243c6180c110394420300d0032019242c20754542d0010f03421a062074408020400154000d110f00350180f400e80c11151b82d5048000d0740c0b020340000054205460000030800c00348030100031350300c2c4901c42c00041600c9100101080c9440c5159011102900900004024813045a0f0000280080e1840e01041440c3c6c02c1001c190505410701c0700070726025048104c0803d01c948040c0400141000051881d52010302c01c0405000c2d41011121050103800794000c5111840d04160070711926010361240301e80b00040a17429001c120006140400c0c00c01520300c9807684d89014400000514031411001807600030114240250407025001040302d1b21407816100e00f804000500c0d480e4641e21450302040c1308407140402c803900c1800c1e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 789070026 1250 789068776 789068779
    0x320f0f120102030c0c0106051207030b0604090b16080a06060207141512090106050402161b050402070602030a060906030305030f07091a0a083909091009060b030402090703150302 78
    0xf00a0100410501c8000c0c618181000001d1042e43d4507482005a400c01c4500342206581c4500410000940300c08061940300c0c100810028404c0c2039900c0c0c814110314200e071410600319082c104030b007019801504907500a01070400801a003810944040e668500b14042e254516002c0d0801d4142907489980314122141c04000540d03d4550350050004a000103403580411542040030108481c00d10b4800d8581c101e01c85991050205c0e85901c0d60681141d001400d0345640720440c13004a486e442d1800180b800f2803246000503600d20300f0485203400ca5a8941045401d40e0408404001080d4420f09a81e00300b900406034050316220060242c1c1d40d407556500540c0070403168800d0383c00b02c1140201070040d040458903810410760320b0048185140418180745803240c0301880301d84000380716401d1000c0581c1c100700f1881780750107000360000300b403400c045402d21484050354009000d090b0bc0c6029400040840c4500107007503083c43c0e800a240084001c005000b015600d00c0f0000101c02100320070801181c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 789071276 1250 789070026 789070031
    0x5150f130807030b01120b07081306060605090f0901030b160201240305060a0c0f030209010903020310290d030503041e03030204080c151806040e01320f0f1201 70
    0x1030300d801e02900c034072841c40184d8124582400001c1c0c07007076070300c0000c00130399034090340c10600d943d210b010950701e66001038201e40011134480f000d0340c00640188540c00c05080d854540e5600d5455900030002c0390040b14081d1801541d04070010400074001350020394000b44202c030740c0d1000c08a4040f0403401880c2c4d0340b14800040f00300802030308400c801340803030f0800e490141c0c0c207032802030351042c0090050324071404484c0009a50703c90850220b900c240d016002c1d5407414541030302e407903942e9000240f920b00c00c00d8000213810b90f00c882c03d216500c00c43c48103a81128400591100140c16500015100311800c1d0000c0e050100002c0010308006650958460402032808650040728a40c10010000d4201d4025400f49100f980c1400c42c240c035100c5040345540800a4010303291500442080c650761074010103141d0801c0381480081b0301400c2c000780f041d02904160400d6020191045c1028014002c40c08070421942d407000302100450302c039122081c800e00380980702c050890980070080b03000405124a2101d0035403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 789072526 1250 789071276 789071279
    0x50a1e08031306110705060610090f15020c030d050a080402061218100603080702040f020405090a090201120b130518030d0b2103030414120f0706140105150f13 70
    0x2142001001e00e40110000c001c580341c0d442d1201130900c18003902070180d03403003030000030020302d0310660000c440c80452408214059642d00c04801c440c210303811586c0d00c0f07800601e00c54055641003020b04010b00084005001508141c0303005021841101091000c1018003400101551a882c00700d43c00c454411407161441d1416203815803a66902442191040c01502031800070404030f40140e40c10340340c011700c11503c0c007000d40e42040300411154846110303480e0203100c005200d41d115842c00c0d01c641c01c68000481e0b141c0300341c400100b00001c070303002c000d48151401105101c0398586081c0c608985214060001d0161207903c0303000940c0f0006440c10141340300001e103030010b208040c0c00c00052814156141500442040001a0b030b00040d5100030b1665402440000d0101d20801448071030b0040d4030080d60305250030440c2d120584c0d1702075054a40d404c00c0004030782c42084843c1c0703c0c0070380304c0300b4a1200428039410100050340f40c410790000d1075443e28002c1052034000300c5600440703c031454a0704551081a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 789073776 1250 789072526 789072541
    0xc0114010e060a081f0207020a050a0305070e01091b030b01021c03140c040815040f02090f090c2b0305091206160804080d050711070e01051c050a1e0803 67
    0x80d04202c8906015040b600c1c2e0014061400243d078100d654800c10301c2c041c00f165440c007020002c0d044208103a0f4000315040001905495180f0084091400341d80580745207401e12081880210040e8001680d8610700710408104d1100c81e2201d0b0419040f625000c07400d4194080100c0c44c122140c03e81051107060404603480c1c40f0b405078004400ac82e0480311210381c43ea64009908980d02641c4180d15541e001748400300c0c444070203002165400340c8102d0750002444030b0b83c1c0114000380000c40301140041c1c2c2d001f042c440341510400800c103c119084815141c03229000f04c03d44840c0000140500c01c685903007440400705401103041d54030080c4d01603c1e500004d4203c01e90300e6611b0105540b2454400d05152890b02d1081c85954070300c0c07180c1d81201c0c136286050606003400e0001c140c007d12580410502d442c2018540005200c0e81c0c0003468101c11428195051804008150401413100710b505120a080080000d101040001065030803284181d0880c401d51401d501404090750000d102190020400841 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 789075026 1250 789073776 789073799
    0x9100c030c030f15030206030c0d180c051c140316150b0306011a0d0902100804050606061309020310030f150c09050616050c10030926030109020c011401 67
    0x1a0002541c040c0b000d03440e0f02c000242203a601d40c0414504081305281400981000302c010354022507217592082c5890b5046186204450701020070b00d403d002d40408641c20700658402020240500b11440400c20305454803440040b88602c80040441d0440d01e00020b070345c0814410f5481e082c2c04101910142c07403092403c0080344446038004208207144c500c1044480c100080e045060390724540c141100d0b40c0400881010581012640b503080c10f0300c809049006880300c1c030041c4149490794a654840d81094500345007803c1c8010807141c05480305000003100081500b01103422161128001070b90b80e15100403907a05510650005000d8400e440c1c003450030000051380141c82d20341001410450544000f02c200c50840984c40394940c024001d1141c400d031981c010300344040342c0c1d00c0342c1c04503408080c0c0c2c200413131090344505102c0c00200380c2d84c0000b6400e101c1d144801a0b8004a40d000324003016250340c81030140707404180a140382c5c1c0c0d9800f0131900c8000400f503000390342c503190303030280900c0d10744e03494400041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 789076276 1250 789075026 789075041
    0x51f021c08100905010614090f0418020a05030f0d050c010b0a080a031d0105090906012c120606030d0c050708100c0f020115090f1104090b01110a050a080309100c03 72
    0x144000d42c400101022907100b032905070b076104d54a035442c1c1c54151401d03d0351034001140341c5a114030b01c40c0f0011042e580d0f9100e000c1502211403c40c85550440d4010060f10401503800f06010b03810000322840c00500100b55407500040c5030407c181c0f0744100c0445107004082e5017107980e0b0404d035035007030104002e01d0000f114480c00b4481c0c0da07160300900900c11404c5000769150580b03808541d05102034a5145089081a41d001d4011f1611000e52902c034440c0c0c2c00683d64100a40ba180507000c52046003d04280081160390101c1b080102041d0400f1000b10b960b801d0030900400c20003000784855420807805004050051000380d040b20406ea810030540c900034000b0740721100c04240c01c03005c182181401030045100410300d4180da509094a003516041c080c0c81002c0e013000100d60703607410903282114900041d0000d0b11201c2c030300207284642100050b101c803a80000c01011a400341c85040b001400000f4416230305a4084129a203940b6030341c2c6203130318240541001d0319525040c00920311559a2680c007494 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 789077526 1250 789076276 789076291
    0xc0306020310140a0302460f1809051c121805070b0a180f090c170103030c14101e0608070b09010e03030c0304140a051f021c08 56
    0x607075243d03646841d0000b01c141c00d0111600040c1c0e410382000549000b10002c5150709945000c004141990090145007000d04000f48581007842a080d10291921100e5075024002d00204082e0715030a00818071040000014043d00180d160304920342046024410320040c800180c82840c480c0c0803091000d071080c05295484103039103141c0035605032628a50340c0c245001c541c1203006050441d09181408903642e000c0400c07074042c4840308100c00107841c51903000300028401071540104003800c3c10b9500058441d0798400d003040050b07407140c1d00490f10400703148504403981030610300c4a0164910708681c1c0d036018040d5442e540e000350441134001c031800b078108981c1680360f0800505000410a018411600d441c000e980f10303a84441000e01203030303060340010440480141852060b000b000300010345954014140040c2c50707040450108000100460ba0700b0980504803500d4000314240004199500c40c121103010814500c4564001c4080c004d00a05c501502c0068500d0030f00343d4002d001424007801981e110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 789078776 1250 789077526 789077551
    0x3080403060e12160201030507020c031005090f06071b060b090109330302010c170c0304090f140a0906060503010f061a0301060801060f1806110f01060806010b070f0c03060203 77
    0x1407441160101160207031032000d61342c2004402142c004500400d0020030400662280e0000000c0a503001c001c1514080e182a0021407103151800600d420300c042600041403a50150042c000d11075040855030100b10400c1c600b8041203841c1d07083c214050010602502d03042804000080381c031410540168810f2800a140d1642080da901240d0b410711a00b80000c401050403158140010340c41080b141403070901452401900010380302e2400c0280e400003a0040955200042c00c011404486c05050700c04500d0100803c2000405903a0590060f801040b100c1010b95480e4031004116465000002030100940200400d558a200300c43c0103000d140500c448104a50300c071440e08880b503504990503119076986000003640b901509403043c0700065101c4003407194240d00c0c1e5a149021111800090881303566144002103201b01035420090740032102803440e4149102402001c90014100b0b045817036000c01e80340d544415040074442c00f0540300c4005c05aa04400b00001071205c1134002d10f0040b1030ba11200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 789080026 1250 789078776 789078793
    0x2003040f110a0b04360f020403021005120f0603100f0f0f02091c02150703020f03030702060103171315090801020309030406260402041509050414010c03020f07150603080403060e 78
    0x342c030a01003100c403252101041e81140f8400a8085d40c00051039180324000c05802d0944a60005500c0c07085804140c001401c045850054080304000964001022002d210a54180000030a8807540d01d07000d00300150ba122441d8502c100003550011110710201e0000300b1088104000500c040c2d84414100b520410301c00302680c50348001050301a02c0300e81d004000b0203100710115030303c101e580c0140300e083c0e080d402264880440480306000640c4660400c0e0f02900c141d48c11071919090034070343c03103560100c102c00170301034681044400b6080f03c041d60034003002214a100a000c08451954442d0081c040950010040c8003096100001820580f801c03506c0b17180080551000b200c280c86614a4040c545400403808200942050361140d815140400b26a8000540f50440001a640180d0381280c50520781401130b445907000b0310400c92068843d2078207600e0079014036129030700da02544a0151106a5401400360307803802591003400151b5108003619240e5586e42007000081c00605950a82d40c0100e240 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 789081276 1250 789080026 789080069
    0x30c0b160806010f09030b0c070206070f03080c090f150d1d070503160b0f070b09061b040807050f060714070602010c02010207200d2001032003040f110a0b04 69
    0xd400130b40a1555a5594110700c3c6854a070900e41d0301800c1c001d40391a00704040c8025131150002085e0303d90041e4405060640740d881c0017450140000c0c030013170310750300b003407084040540e101d601078a42d20b0b00843c0c800101c011858000c0405124402c0c40f40411444c0040d60b511000d801080e218a2210610581c1e24039591402810749411107070b04081823100c9452018800c2121020280501e034480500b0141041100c0d646c1004840041c0c86020b81070340f16000308954039810040c1c0c409183c00000c52141098074005620b991740c0c00c03500510b480340309500703d140c4580c0c440406643e90240c200c10810000f54034140201d071180028000d000065003001100311040c1e00500813148141e600034082c0001c48401200c001200c4031581070302d94007003420420750300401c10018a130702c0d20980d10a00008400c611b90f002500300da01b90036140342c810711590010000d00720014150780d44942c000780c0080d0700b02d1241c603090325864200c81065034020410354000c942498840090015038607603681c80c03034082c42c0c40d02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 789082526 1250 789081276 789081287
    0x90414240306101703040f03140d11100903020a0204090b060a0b2a0c09070f1701080d080601201e03090a21080409050a11030919030c0b16080601 64
    0x4545400fa0a9090010419031000c1440d074948100c80c00f003581e0420362030342442076402056500a603458140d0359615030256034240040d00d891106d03820311401010fa08500725480317410109060409951f140c03807000605000340203c1805a60040c010041166545031a00d0071715003d443c00ea01030001101c01040400340c8100302c40e1089103001c1309109807852064a0010366440c0c8041d0102401442503517170442e160b4009950254003151502101c00e81c00b01030081c5520000c1840d00b8041c0801001000386100200d04100b1001c5d044c40c20b03480316590750b401a00e058903405024000040100c01803e540200400e40840054101e8420381007600070f803051984c0e0707004810029a00003044041000401c0351140c01c0400f00c400c404510801d0242c5d80c94502e15a081580461a12504d0b082000000c002c0d034030606441020b91101c40d801c500f010720001ea602c0c8045c100340000701d1505501c0c00107240c000c2180902260b44405050464070300450064010141c6500c810045410b0b00041080c640c0201d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 789083776 1250 789082526 789082531
    0xf051908030402040c0c0203010507020c0f0118050607030c020a030b0115170708072001060521120706152301020616121b05041802041a090414240306 66
    0x90100350454803241c003044010500b400311441809049100000180c4003802100d200d100942c010304101d8103560140803040c1001d40354941040ba41c030032840c0880080c05140004d80300e060f200b054032081146801c0e5901c0600722030196000307910000000400104600d00c0381a00c109425201006200080036030724201e89803500703460340b2a820001210207218413141a404105881c0a21003044505035040c3c244840081e10141a51200702c06c4c401c0d418101c16545e40303500920050031000c1c010500341502c0d5038001c01d01d2b804030440040c51710103004050f002400c00900c10f5031103a181a43e034100369a0500c007040003100c60303410b82024801d143c1d070010507134070b1040700c80a43c0c200c0e07411607426003102c12603915115050500d582d040d00000b018145040b840e4a40d50720785a00307a4440c241440200f403007201502d035000c4139004100c10b201d4959002083c03a60711240e0411503480316407543c0028054400d0510021642c96140d04100c1007941c01940c103030340c0038003034410000202070300070074542c964004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 789085026 1250 789083776 789083783
    0x5011808040303030b031c0e01020606100509090a0f0203010605090111010e0c1912051e010605060a03020c03120a24031703060a080312010e0f040f08090d06090f0519 73
    0x41c0000c101007800390700007130f0f003014004007610325121206105202c00320701808070304002004452088820750b010000941c03c03140071102d00001480d5043c000b403080c40b410900a00503001400850b4071524960404a0092030504041d500c96842d02001442504042e24050025075071500f4200d0441c010702c41c04605140e644061304000042c00180303d0b00e26100911002407030500b240008915407417a0341020f5880c4a00041d110303c040030607020400b000684001e01d60741e4500348080100c3c0e501d1400704e07410500d05040c0941c1380c134a110040707070071402100700f9040e18a00e940100074000307008ac0c4c000200142d11403030700700340c48524030700d80c0b04500c186000c0141601520210190030110f0318014642c0308000802d900b184036140c6006ca81150070020400098500403401404006841204258088108942603106150588500710760246031000501b03080e0000404000341d44448170501c903202c0d00220709100c406058a404030210090039400d41d014001c050300c11400d80c0c54181c1461034141c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 789086276 1250 789085026 789085043
    0xa03050601110d0815060d020d11120118060305150403022a1c120f0e1203091003020408031b07060207050d170d1107020117101403030c010e0703050118 67
    0x30380b03d401d07116680d02420412042c281ca40e40c0041a548007001020b0045840b00056119080e445620041c1c0300587c041d4050100284441c4e0030001c080c0600300e04407142c01c107408103000d41c0e03048d480d001402e080d00098071500a480c41c800c14218081d6805000c6e46c0300740c0c01c54900700d129800e0780392403000c540c4000d0b41d80300c0d4020612415107030000788240d0401c0d00d1440ca07410341465039124140c410341410408045807901c2485499203402041240852405482406140001400054491040e248034511a0701c84500000c2151700c65030559000c1c04060040365650086141030b007040600840301c12550f03101c0c039100440d685102055807421034601600c40215a032840c0e45285118100c03c2d0768003041c003001d020f007107840f000901540310409900b070507165540030540001030040f03034024000322080c1c0f021428000e0741400c55240e00e044555442412590b0381184001030304601c14000308208075800d221101c40188404195041100d110308005c0003640000c0c640703a04280c4502401900720702 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 789087526 1250 789086276 789086293
    0x90f0c01080a0b1008042009010e070c06050709050a14010203030c1c02040e0103060c031a120f06041a070207050a0308090315010f260d0c03090801090303020a0305060111 75
    0x14041c0324659040540b158020a02d8610403000c00c10b5040221004400100140c051106002401d00080c52002040b1a04204114010b01084403900188140002c44250f20001101c841c4900010303c06594416400d1001c0e0400700740007000c84081e8001d15100f040c9020001035a074024005419005a068018504603038812080d01e0702c580000c0c10446606803945844090030246100500c003820410521141950450802108880100c01c0705c0b404c0c5403a00c0090100303d00e000300260064030084940304580b410702940281880d6141b2a034010510421042c0000c1211540c000c003042c000042e020242503071848012a80c0e040288280354001440000900c003140315040180704640014045804c121410b0960000f011000d920404010846035014800310080c03225a0303a50301282c0c8401035016040d0b000d12034956010340034030003e00a5800514040502945072031001b0a0200020042c40301c1e50706024001e03600c0700000c080068681000941950b000d01c1d4a10000100c400090090780e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 789088776 1250 789087526 789087529
    0x1e03180603060d060609091406040b0f06030307020d05010509010516140322030f030b03030f22150906180308220f08030702090618220b1509090f0c 65
    0x240e1002d00700b80d82101910b0704200105009008400040104000c000ba59003042e040c03000b25090f20b842c110a00307803c40420b1001190000502d0b503040150074000b80790946881000902c2c512440c40d00070342100c29000301800740041036101e5442070000034024003695035803620196880e03c068013018082142c0702100f1682000c0382019540c4409016440700b0036510080708003032203250b030030801c07030000e00160a26000150305018000c0301c408158002c6091601401405440d8080d488045451914010300303103a100914428070700081c10001c03034029203030139102030080c0800554090719000c44d0b2010708440c1500b10300f0288004607500a8025800e006c030103003440801d000360b0b40070252501c610001c08100c034205883c80e100140a040000c641d200041d10500c18910001030007a03120341206960501002001c40802d0790124040460207903a0510382030f9407044010f800c80240840c1d19240404c40901030720044c01c410b10300c0440d140c03142c0f595243d101c150b5482029200d0f00103600b0881044109 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 789090026 1250 789088776 789088789
    0x518040b010302192d120b130912180b0703030213030b07230f190903081c0b0907020c09040602070803100501110d1e050f030403021e0c090106200604051e0318 70
    0x8407400030014000c5503004007204040e1805a400ad6902c14000703800c0f2034050381c00507008001d900e0b84070603810b042813400a440b500d42c081c107400901030640004210045059a8508002455101d401901c04d402c0c45000280610381002401c17030111005140700724003403081030030b0365003815001201030700d08020420040c003442c59201d0010103001ca0b460003c000180300002914010078405d50b20242c014441911a042d59489034250b0300405d010001d11000c1e030381c08905a0144d0748251a090340d00d865600d080c10007445842d00c0a0410000801809204402886100200c5409071ba4600e02d00101c0070b5400d4032014540d410001250380b036407100e55644080c01c240312104210781009810800888400c801d15801190100c0068000210001a1061595521104e8104100105003580d250004100660410300a8006205008960010941d203200b41c41c004040700100390384085c105407800b141d84e51580143c50102e10b000100b0525805000030580e202d112503180b0710000517810509002c0e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 789091276 1250 789090026 789090041
    0x603060607020d060f1512050c061c09030c150c1e03021c0902040e030c072102030109030914060717030405030c16150518040b010302192d12 62
    0x1c00100030f62419000c01c02c2031252448960b031441000c5000c5a10840c0303085601a10b0b00443c4000c005404003201041000502e27005159064402c150340c0c074803c212035424140d5104a20300e010341001d1000081581c0120128100b91080d03a003001030101c000032071001d40e0403042102e0001082001d00020402d40314400c0da20000071800c0041c50014050381c9503000c3d0701401c1c0305e0107a031500c44015030b0850403c2d06c51102084444800356003403507604601f09480b0903980c49254503030b1440d04041e6500b5100c0d1503403030380d02660042c001c010441561601034040700a138821511089190b9104102c40d0038000100c0f0340b1585e20038019100c03a03809108180081d00044c000759481d00c0240300701100c0309810410403a120340141800000c0c58581103107aa0100d1a4040400401009100c1c40c6400000c0100c42c400700c0c1401ca80c0407402c51b41c1440120000d0160300964100301c0f19028070140c3c0907403c8500c07103141e4030060034800300702d44010001003081d95a542035100040c102d454040d1a03601c2c6a4004017 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 789092526 1250 789091276 789091279
    0x2705060f132301061e051f05091f0206070e19050108041b0b071205070209061e041a1e01050702010f170406060e090601030b060d0515090c03070e06060306060702 71
    0x1a0300300d800540c40c03800c455045e0040c44042c0c1d038842d1400f400243c0c040318000105021a107520803d4a041e05255000313040d0901a800e003e0042482011a03880303d07004015000d2181c0700b102c00300c1413a80000d55034003044d5810b40104103c2d0501819500308683c040c000d0000f20343c9902041c62824004641c800720080090310714100065249100145038260b190040c110380f018551500c03080c1c02d03c0000456107020000030701c0300800800c001078881c4c048143e8011001c880d82d400212581028044071400000c6143e031103403030800a007038031410701c050080a8090945003411030040004030040f101448500181c0810301c184000c1005600c5a01c107140711810300c0c945406d04d68150f9501200e41001507600300c6030307140c9540092000b40f96a0381204d6203e0340c602c004000c613501d582c43d601c140010140110380984144000e100500c081000448811207202e810072801e450801c051980780e580c0c0c502101e1080c000d40d840058038505400714540503680041150741396032542010001d1603131002c03000702d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 789093776 1250 789092526 789092573
    0xe01050c0a080f07110109420c030f09061b0320030a090b04030c140d051c0e06090a0b03130213060806010509190f1404030c0303050a0c02070e0402042705060f13 71
    0x104c3d50321406820008c3c00c080d10340c03070b4030180035120318019102c0044020804c04101e40c0f20000c01010380c4c0410021114000100c080c04d2507040341c1411030751112003056218444403a0800300c2d0421704004010803e0401c00c4c0e035079140803911048080c01306d202c1d07480301a2007054007020a202c1e4944440340080c071b1b0351008001c546040d40944d2428100504020101c1d909140c8800c0000d070f072034000200c184035035401c40e03070a45003822220004007a813003d8081c50480400c00700014140e00e83c00c51030b0f6460741d42c009080d038401e01c101c0c00c18600900858010b85400703014403000000c0904200c40800c1c00b900000c140b010007a5452003500e4028418100c001140c2d54489185598441038018414041c9000340d0381c0810034441414040d003652005890038003024034018017102a1a404200c0b00103807000541c00500e5500c84d8000900034208442c030031420006126440260f0f0fa020700d41012105100314140e0751302d651860540380c1c0790141101d0200f10400d0b031100d5203001410701c040350003000b000c61780d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 789095026 1250 789093776 789093869
    0xa0e0a05090c0901060315050409030f0c080d020c0309030f0c0d030f09180c0809070506071b0503034005100908030301170c0405070e01050c0a080f07110109 69
    0x25803c1c1d20a92103280030940d20056a80030507030b0f546002018040948051140c180c1a0341d00030550036441c5030700700422920081020812040c8001c0740c003a07883c54201992904240d04400307441c0d5000300300e0f1038400d01c214802001d2841020443e110050002040c10700d24004546058418544490f094410419942c0d004202040079401c060080c03000c0d0100080d510514650252041501620460340b0344c1c40003404000503943d00f41111b010590002c43c640740300301c80200401000c0499009103070f160001194051001303102c881880c184c4115982e05c0810450305040d6000b41030b8801e035841c00e94012a900030721503424250540c01c0c60442c2d61038481c0100750354071409070170b60700207801201000c03142181c00e1681d414100003101c9200000c4a08200d141030891000e41071000f5400e540741445804a60128040c200703001200c45160800e80e06035071280c0628101206502080d0111000e070420000140e543d4460241e03c03068420510940407000302005102c40c4030890403010740b04020b2100305 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 789096276 1250 789095026 789095029
    0xa14090d170702030c1005090c01021c030f0b150c160e04030e030f0a050706140315040e0a0501060906032307090e0321040c3f050303130b060a0e0a05090c 68
    0x706c10f00241140000111070401184003800c0107030b8075111031304551200034041d003000c540801421000c03007035040004c0c1c241031140025015003100850181d00075210044036113140c040700c0003042010700300f078241d880181040e43e03040303c03210701c5d802030030f140c4c102900000d800a0b01811206a0441000b400c0302d0542c01c4c045031880c60414050001c0b10690480c000c1040200d03001649400790000c0c6050050540c5441c0700d141d48110020204240328a44913002e071602c0034802d102806402e50090004d121041c0c58904030301c040c0c2840e200454441c480c00404189003400703070400301c818140c0400a4030107180303014000405803490010046460004004209004d14034041500c0e40d100ba4400170011898241001500300d019503104c0300720b11080b04d00c40a544981d0030001c44441c11070312000d000312520002102052022010028107510000007031004202602d0300080c0a5440b03261844125a00c0e80148075010880b403094900000031100070514400c440e4203d141e008210070b0859540c0b80e01c400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 789097526 1250 789096276 789096283
    0x603080c0709050105040903020606190503060705041401050a082a0a030506040f05040b1812160c0504152c0103142a01030207030e06030a14090d170702030c 69
    0x480030300856115a408005540b594007410340186000c40c1c0410100201c2d84020352602c60040c0f569109031400502c8181180d81c00da001c80181030081e088034450300d44200302403c958054080d03151452030a40d01894650302c600121080c080d82580c1d10840c41d150303801101643d02581c03c2c459080b8000c00d08103020150480081d1414108a940c0410b150501205100c01c482808484d001c486003054204400719842c0f60744160018088484604060040100340b410305141e551110b052002c002028141c0080b091814503c050045082464460b600c408100071251803605c0c0003a40c0c07188800c05c00684002407038024034480c1a842083c1070180d40541075034100d00036001100d103403000d82c00b9011613401c1005400c2d11070a8123042e59090040102d02c2d60f0b402591180220304241d0009003003400c041c0304e401074072110240640069103d003481114507015048920fa00e40035038400c5000034000d00c0001914286210440d216a01c00642e00103c2c070081d888010031200c01d500c8200500c401081040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789098776 1250 789097526 789097537
    0x2208010c0c1b030f02060f07020a0905160c030f050906090607060606090b09031209120d050c01151a07021516020a0608070806040e0f03070503040303090e0108120a03060308 76
    0x16541c82508030960724104010410b0710000d149200c0c0354400a01c0010140e18604200d40d404807011610f48491085441180c441d42400940041148100281c540321a41205014541c0301200c444001c4050004555401c01d002c4060000f801c030480120711305002e4001411040c1c400f40c40c191030030606d8008070755140d000400c101c1d00c0c1a9a1142084410b84c006582c2014180d08181e6030300d003015050020366107052055044410342d0000803258165919880c044810072040b100380c1d24940714640002d0002d420001500c040755080c90007800b03d41c840d010810302a01e0543d62802d40e00381d12902c90b0640c68201c988101d03040020003911051079280341d005003e542101c0c00b020340c1400986d1041c007220b41083c0d4848001c0c450207409003e001c640018590703900410039a000034905c0081c001207450149107814024640c0400034800c0c06211003c4001c10030748e8003a482d08001c40d0b603501c1100d00c40000900c0ba61106802111840c8001645d4070300414a5109519010079900d45985030041241e001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 789100026 1250 789098776 789098801
    0x1403010b04080f1605010302310608100602071206020c060a090204061401080402040906060518060f0d0c030636021f17040c03140d02070803040605220801 68
    0x1ca070400c0080820420306120810b54000392420b48031103040085500818092a414160046016500700e21041e100400c19205182001603105e10800650702641150240400240d104000150b42c0100080c60808039950756005040c2c05d4a2300c2014001018055011510144c003009580c2d1040d1b000c00a81c2d00402c82200c0001e890320f12481000101d40d071651208070740000c408144c64183e078100c1c0070303194272503019a0003040d003400300d240c00001040750b6004240d2103010500c0c00840c480c4100d10a510801c0280c1d03100988070b007810b0411a99101543c40142000060038061002031280e402040d001083c80c404d0442ca54040701c3d102e9030f4440300058080034000400550300039031801100308001614101d102802802d0070000080240c0d50013840c8012068484001c501000308407d5110000d541000071144048840102d00742c13550b01300c1d005072005105902001c40c01503070101c100c030101d9495886e031300d140070050641d070000c4042e01c040c00e0a10192000000030144828020411500d05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 789101276 1250 789100026 789100049
    0xa020f0703090e07080708070516050709020d060b03060d020d030e0a120302100c0503131110080f0a060e04021309020d140f030c070b030405031b011a030a030905010f140301 76
    0x4210700c04a81060081403e420040030b4421b000e84280c11031010b68200f411440c0ca250b9454035448582001c402c0d2040044c118403504200084aa5069014040b14a51010107000d5240e4401074a500c0d4082900c4550b0301c00c080d40c1100c8014a041e15410444600ca814070340ca4105403100040c011240a502c501a0b01689254400401d54103214501e407050940320100425151100024800c2c00010819400d42012800301d0090129000c03641d4400c800052181c103c860f00350400614003802a640454902d0404010076100c01e958000c40c01500d400140d4a543e0750340b140c08111084218441d800c50103540c410f50007000d42c031071103007172180305000d00700c9200210702c41c01c0c07040e284c070803203080501d00d507002808155070090000c64500210b0b200c1c407001507100c2d2030b2414101d04520504500e51140c0310000d403c0e007510001904048480ca20301d1140e5181021a00c2c00c0c0368880900c2c5070020005541c8840134052580113124a400103940307403408902c6008840a5000b181d03000303030014415240f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 789102526 1250 789101276 789101279
    0x906010302090a14060910090e011a0d030e010e12030a110705120304181806060603060e07051603020f0a03051306050c102004060807021515090a020f070309 69
    0x74202c2003143c00c5860114104140491130708450080040a403005100c0e0307404601140c031030f40d031102c0310308050002e60104010340024999454000c1c11006005002115400100852440c10078a074400c907035050b071902d072444902000112801083d1480040d801a142106000125000c00c0070342031b1030100b81c82d40029000c1e50001382c0d1402203d0790040d4030a201051382c420300c2000c00f000751070456802c10075000c1040c84020441c00a81300a845220174115001600c50070b11541e50442012504241c404101c015101c480c2300503188022102103000c22030070089c0e182d100ea80e0854045000f8040e2041e5110280c0001006e810b00e9912141900003620108541d03540c50800c0e54250000c181c0d50030f01c02e01c0e00c2d5840100b907440e02c0601421400495454042a03070f03000ba4150b801d009501d01c41c64141d9900d444003c05060f52500b6660000144104154071402c2c0f0f2400c5001c501903001c0c1d1a901c0c604900c1d00080006004008001d603c02c40d4080c000d4000100d0034002038023006101e6290b03070b0f0b802e9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 789103776 1250 789102526 789102529
    0x100e010204240306050423040602070204110a0f08060109050d03180b13050a1a0c01110a050417280609020a0801020a12050c03160c0506040507050f01030b1003180b0906010302 77
    0x1a000d64005e28400c0f4a0700040b640c10340201010441e00900242c03442d2070507034407410054003d0148a00c082d4009003040020f5281641030341c002c104e10500c40d107503001072000f84501200c011100701c0f075141c0401c4c8440d0707090200f881d0090000007802e03ca0704e803241490f4031414104d174454070f03036900100c2c45080201d4200c2c441d49030000c0030790241c80c00f610802c01c2d140c600f04079400c45201680e020592070b000050307040390910080d00440090007414148a07519115008000c120b940320384140e2043c10203001240382c1e103410105607140301c1d201401d041c01812401c2025214024003a0714105ea02c030360740f65242801a120102c80c0002030070114001a102c007008803002d481d00448592100702145040304110f00449000c050300c0c0c01c21801646143c10340c0034203500340c910440c4c181001d0410301c00c1c501003004001d000031310102951000d40d030890000368400d0040d002d881c40d101b00a0340c40440d0006054955100e0b40c046414262a1075503452100c1c41512840083c801c00e81d030342100d6070491401402503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 789105026 1250 789103776 789103781
    0x150c090501030e0303151212070f0201120506030a02100504090908040905011a251505040309080a0804170c0d0b060108010f15031a060c0a0b18100e0102042403 70
    0x7018103078042c0d171961030044500707400710f003503260524030540403101c3c00c54050208004415001c001f43c0b0710b49545401c641040415449500d40483c0000c84600c54082611038902486000e030b900600104002000d590030055070210031022a1300b00403081c840011140c196010f281a0240600c2d000d40d078a505040760740081e10130580048034042219010302c04000b983c1d00480d40c03480c01100c0c401d1106540100c00d1240b1400c40752003d00440040300e401e9801003510b602031406540300341c0340c1e00d61807541c64110548901210102810881043c0410002c1c4805501076007540741e0214103640e100d000796030000d800b4000702d0000341d40c034826080070441c15580100400b405050200f10310200d079440c0c42602418148004204010542c99900b80f2251310544842940c1a01d0000c20803a210400381c120301d90348201310003055a03008a10404103a10341c20002085d00c0e05040c04002d46401040802c000020300b83d408002600b0f0b660030800020f0548190103005030703007250034000318004c145100c0c00405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 789106276 1250 789105026 789105041
    0x3060c050a050f07080910030e0c030c0f040f14090607020c09010f060302091908150606090d0b0c04050d030801150e01091415040902030403120603031704150c09050103 74
    0x10300038100403074000c0c150040199865008400c03009541d035009440c003925507001d101e00b0540c002c02103803c1c400641d509504001400e4038004102c2d104105081c0805585a903882c0045400c11003820380355400c2d0030301e50860240d08000080215203100540f52004010742c044032030100e10381200c41407201c2d1544c14421205c14000850714444154148207500c6480030982c45490145940051007802c20303220211b00210b00d0383d811400520161b07840da809070301c0b181100c4017a1034526440000464600c2d014058541400000e0500c04030103c4030b548441c850180170f02404160801800002031680d00c02c5540004288240c1e02c0704901c0d4900049918880d611085140038014216084041664441c40e15003c80da0180d011401e88092080800c00503140008151303081e140019003c10300c0c0d495500118041c9200380c2d01e03500507084180d08401202d5940c00024002100308942c032140b9000c0a581c1501300707002c0e5400d030b5000300d111816041240c8003406144e01061206104201030341c0c1602c034004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 789107526 1250 789106276 789106301
    0x60e090109060503100507110f0106061b170f040e0c0403140d0225090207080405030c180403050d0b0301020a030e1006061e0e0315041b0308091012090308010306 71
    0x711450505000907114101c1c201c0c1c121780385603600c0004001da80316640800248403c07906540a075400c030106c0c280645803501075280410f10103071102d0424800c1001014082c1d81000d0300410200040822040e10381c021405050030400c24840802c5203c3c1c80c2003040c0c0114010500c0c0b681e103919600d028480480f9030010b10701c194107e00642c400c00c9401080165102d0420306030030303000c1640500e90003604625500f03d1299284082113050400c084400180255401202250b91150300e43d0200000340c04c4180c5009501c2c40440c02003000240100f01a1500c800d56410101c0c0b41814280820708a0304400d025000082d10303820704040040303080c042c11412035103032901800b14605041d405014450920400001d5480180c4504000c40c403030200c101c09200300409a42e90b01d0780c05210707035610400c103642c20b656a041901e165490031303400340c50342c0d001c0f65404504a41040c0d9440c0422140441c86c40c0c01606000c5e00745079000c0000154810074460f036119803100e1019504500380394089542c044e1841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 789108776 1250 789107526 789107531
    0x1b0507020d0209070318082206021f020f1c0c030b031e0c120607030f0c1202130512071a0702011b241b0c0b2202030601060e090109 58
    0x405600c1c0ca8210428840e01503a00c04a140c8130b0110460082000580c103100f07000011032248100042c0b803009040c3c94880c10a50f008071120b541d05000384a219202d0100540e00c102c60b080c0c0515400c40003801c9020310280011704040381000d00d01d0712907220300e8a648003017001055084040c4034a200d4128401c40920b0204081d8241d100801d41d03900000541100c046c160007a0400d80800c204a12800c00304003820780300540e0070388004075907223450944151001c01e00b42030300c84403594124400c0c01803e414590314200c0c4036007040c0c07c4c00000d6204d81c411903402c041c40d50020803942c880f4003828141c02032107001048010704d441d800e4080100d882200340b1808004001200150385d014218220a2504c498600c1d03003110141791103102e40924907030307822840c030361110b6809e2080740c0359004150342d0011412420340f803c100c1703070200d07480022200c004124540c00c0001c030309507443c03a41c51081e041054a2849820340c40c140c002a2519000364052000280422a90006414030b0303500b0500500503d48207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 789110026 1250 789108776 789108787
    0x60c030f0507052a1005010501080f060112020306031603030504080d18030b0c070c1e050d0b010e0601030906060315062702071505090d020106170303060d11060a031b05 74
    0x1c11070b03c0783d441e0310304104442800c4c0c91071407822903880848481240c0b08464030045d8507000c50300a49030074820140402e00707180006151f42603d074111446442c05030341d0401503491000701a0001e40028207855094410312840d10b40820803800c0313050213140030b43c8440c0c1d1140d1420b40e00600d08200145080200101080700c46418680005c1c42410f0344e601070f0740c2c1e00d1030b80c2d90420500018001e0010107050344440000010b070324640010644001e000042c481c403580d9489405002c07581e0b14a2100511030000d1100402c468008000300039007200c1c0524010401d01150346850068500030b0300266901c1c80003a841c1d04910446100d610300400754100c80b00f03d000f00c510403400040344004002c1c0030054000684104001c402c0713800c10710840b000c030000c00180c109081c07113030f58960000d100c00c00991318003a00418106101c00100300c000040030021491070742c0380400c0c03101d03212030050211030801d400404003065940d0f1402411014140c0c1e500090344400d14507085d030f07400c00305070000000d12104102 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 789111276 1250 789110026 789110041
    0x203130302090703090b010909030816020a06090c0b0a0e120d09030318030204020a030b03010f060f05010e271f030209180f0d020102070303051b04060c0501020c0a060c030f05 77
    0x8105003220740450700300429565800080d0082e10612800502c0d00c820034001256407601035000c180224040d0ba1403120698900010502c002054095180540c0c00b55000c440042d41c00e0700418100d91003410882c401d25a02c0e26800005e41000200e00c1c0414000b98140e07429042c141d06901500c44600006c182d00310709000c0142041f0388030300020707040141032204140c0310703261020341d200116800f82013151303108144c1000500a06103004031a00c2542040c40130198920980202401d039220b07500946541440c1c0b0005407280c04003900500d8105440044403644280e40c104480721209032908103517940d1030308000c840000700e0456903c01e40426019410300140c5c07030302e81d111a48000b111041074440e80d4400040e601e001078a1a00c441d0511541d07001c0f0310501e9042d005060078521a450900c6142c403842508800c10b4918021041c03840703010b02080044900c508400609240110b0005140950302d170f54035401e150f001e42c0300360b80c403986581d0088422a8540701e0726510410304c10080140d81480c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 789112526 1250 789111276 789111307
    0x30405010c0b07111009060f090803150d0b07020604021305041a0702030c16061d0d03034a0c0a0311040f140a0c02060112030c0c0305030a17070203 65
    0x4003500c0803030000c00040c012405080500300d0304043d1300c1203983d10b0054a9203d00500303030b03541d02100e0107400d180e400c803c200002c1c0500011603034400704007810350b0b840a030200e1850000b40c01e10742c0e0182c180a81c03035020421341c4568034000e04036079001d0610b519143c014041003003c1c45040212180c64001040040380d9000c105203a400c1c0c080001d1649615507450803403550080280301e0350a402042d00c0514a0b4002000320030485065031103001804640fa01011401c4d900d084c0c0f041c1d00058031001d920000f038460742c0949003024030304540511680e01020b0b000e1003c030300000e44240c0341254541c010013003807008011007051a621802001c0c00b407100800f1503544c1106110040c40540b90380312510711340d036464000e040c42c3c080e854001c10200910030844034190310181c44420030145072a82c10f0160910100750340d41a10b81c01001c090003020f05540c1143c1d0750320320980a07503002100001c017100168047c0020700c218646613072403440060031044040c0d01c2d1300014001e44155402004040390040805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 789113776 1250 789112526 789112547
    0x15090301110712201c0201060906140f30010506040204230a1503150504020430081908090606030a0f14030a23030415052503020a020f03040501 63
    0x240751138000305544410500382e511000180c040c450090f071401c106180d01c030071642400545540d00038080d0594415861702155518003804807038a208003441c903820704003015413186014029010340d046601117650075107060800c0012a002c80043c094a81c00c078042405501d810074000c6504502d858907150600c81072127556a06014040700743c0c0c13080851030b03480412800c02030140080c9c04010410aa8008004208134242c007180d98503c020082140d00b0310340b00b070b10141c420745850111841da4964201455105501c2500360700c50050100c840003484840240c5030180c100d1034500e410042410001d88081c0c0c00600006866014100b04005640d0000e041070403250070043c00c100b0440c1e1810314400c6400d016404140c02d201c00144c03e50120f0788080140c0c0e000b68170030000c03209250592000007079440155005010006410031106541105a10850b00001200c110745a0114200d4070b0800300851240d988003c42c5e801300d1461340e4103405200180e241d80301030020b1807505050070000790020425 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 789115026 1250 789113776 789113813
    0x10305150f18010b06211e01050613030219090f0b030d0e01020114010806090609010c050f0f0d0f06210203031803071805150603130201050a0c02150903011107 70
    0x1e0100141502c0e0302076028110260014040a960300e00c1000c3c00d1107030140218100c0c103501203240004218100c1c1600c1c0c40d032080d81403031084119920700010005140c110808072400e500141500000507a164115513214600c8000700840280c90305103000100d80c212400e035500182440c8050800d56004103440100d4030003030401e883d061040b100101c0c01410842c000c220f42c00c82c3d10700042a0382d0400200380d8411604c19003102ca03c0d58030502c00c01c0c240d4102a201c140130034006e000035840000ea04c0043d01003c03020000050610150f00301480035240020f86081107540e0350701c420b00590410381c21013407106a203100318a1120340141d000c0703552885a01e80702c00704d5900c0380361f41159613a0140106801829141021910068240c1c40c51004020079110b103620805070020900b6030b810b1070001d42e40f054640d1229988801c180f60015135840c1c0c0f00b42c445404000074101c2c000e0050b9100b544108042c40b02502e4152144889000e0600f107404541c503500360b0050902410300040d00140344460480c8070b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 789116276 1250 789115026 789115051
    0x70f09150b0910120209030109060b120316081612030c0912030e0402030c0c060405160509070e01120b0402070f06060501052803020417010504060501050105030c0f1e0a08010305150f 80
    0x464130222402030084803411035040d42051154018082c140e084841c8481d4100c503a0062032a03500500c0340c0d00e210380b800c04506441c0b0110840c010480e9803020f4507070381c0d1403200c12594840055075040311415822401c1c04c01300b65107850301350855900c8917084010f8820b15101520703c210646010b412011882c2c0d24904c02c60f00000000c0b100300c111010791700e007084444103e800c0c5003040e10b002501c80000318001d44a200580790000380390b10700680c0950103011161030700350025440d413004540c03803213401c54071507503c03a112a000300450320b9502c01040140c0c020300c0c0c040e01507a84e0b80303080ba06480d181e0b448241005818030024038090b05400741005130200d11550500c00b1022800140c0190140d42c2c41503500d0360540e0503a1421003410b4010364403480c8602070401c0140e80f19001074440c2c7c0420358020325040030034040c526a88002c40010088421066040c510800b2440b000c1140c541c013801c01d075030000724402c0040081050400c1031011203184500d4100d600c2c038115144003441310005041102406 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 789117526 1250 789116276 789116297
    0x3130c0503210c0a020a0308210601140306041b0c031101060b032212080103050f06150409060b0904060606120903020c010e19030507060f08060d14070f09150b0910 72
    0x10000c104c4109000d602604000c90740d5664184a0200d802001e04910541e040200d180008400b01620321b102d403c050b1a000341441c9900b00065450300002c000f5504242d549001e10300f0380ca002c2448607205409991030422201d0240307802080000c55605850740c1d0381c10080144500d40d1510305403680700c500341d13070200c0d5840e1010022030020325000d03101508520b02c0d442e440c030019078841040e9050303034001c2d41180c00e40440e8404207030765414100c401200c10340520401401a2a25400200c003542c020000441c6080700364001418000c0c09170b400312841e5942d02001c203d8160400d808111508141c2e5007008034005c1e540300a03488003800d5100e0f90420114048a1b00030303503115029407003c45811465102d16945902c2c00682e02d1802d40948008600141c3c5c103025114491241c1d50703c254809083c0d03a0310040c00e43d507003200700c3d10200c0040105004118000c2580341c50f412088004010005004c1229078000203403003102000d64100b2210f41404201040141c0c9034188403480003001480d10f640c800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 789118776 1250 789117526 789117547
    0x30c05060906041707030c0e060a061d031515150702270a0e061b0d02130e190b01171602100f050402030105150a0603050601050f03130c050321 63
    0x1840f550308010400007812140148040700040e54100b40d80c07080f002d56101a84910840c0d82846080300c001d680031103d644140f2015101d81c9014a81180030403140c0450601040002e0611030500070750a440f034200b40030407a011005031140a0556019684030629042d074002541c404d2140400c0640101d81d0f0cc14256042407128000c0101004a00c2401c1c0e0203080c100c58600142c181008400c165101c2c5c08046040fa0525100740c28180794400e00942c45c2080444031344000c0d4022480300c02c0700040c2480c000844080004c0c0581c410038080c01ea06502c0d0b44c0d1030054000300c8000506c164104855940c211201c214041c800c9500140d4441d08044404500c203c00c0b0303c0c00034003030bc080d1501403c02c10440700c1d5007600d8000718060b80c822002070001d6036441ca0224a405152641075070300441d102000c0242c58040c1d8030640d084103041c5405468102802005915940203907000f00c07002c0c044490354014010741101260150000710043c00a000e0b55a42c05215050f804220000100c40000c00c03a075003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 789120026 1250 789118776 789118789
    0x80106051c091410020a2003121e07090605030f040f1415060d0512030703240602150c0d0c050403171b010b0102030d0902040b0a1410020106030c050609 67
    0x2044400700248007400c40ea02d410300000c203072025605068455000030300840e000c03e00a03500800b1132603580b80c2880724101c481e501d006170301c2c808003626804100400084c0113540d030202c03031007004245112040301c1c807009c20315118458010718030301c104940c01d03a040c0031044c5d02c04200c83d00078075a0482c01d0001d4580b41007071800d07005240030051401082c01e40c500b611078000b19031180340020001030304c50740b503035500148070040042400c001c00a0b0410000f400000110310007464218034549800200c2c4124907401014492118000e4819a8549501000313141e9040007d58451a2006103550107824199107042c85400b0b85145c00c0c0c54180c940e048500010b20501c00e4400468001c05075141c0f280618801e00c450358000c1035803512035003031140003100300c0358140141c1078044010b0b8000c42c58284241c09007001050074010807070b070141e228144540580c3d50607444034050b14a4090440ea821105000c001000914154120669040c1042000811002207404003103e03070036154550380d254201c000948 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 789121276 1250 789120026 789120067
    0x8030306010c14031603031508060906040f1401060602010902132a020c040908340b101d01091d070306200412020a06050f03180f0d0c020f0901030308010605 69
    0x81794100d030508818140d040e00400030100c800300c0e40030222038441d10025250041100d05218542c04800450000f0326141a03c5400c1d038012501440000341a861103070070740c5c00c07541c01040141e440d00c40c41c80c25031030807a141e0442d45000f0740b810010703100c407100c44886844e003408200000c1c145039552150b000c0c0c000e00100303c03090001001084028558985140d131500300308035110010381a101841d211120010041088a908042d207074036071380d000c1d5580d4a81c20001020080c554501010014a42d0311211200c500741da8030f0700d0700119540c1000c0034001100c80303658080c40440d2810310701c1480d60901182550a481d044040400c0c050460321920008100e140c0c1001c0b1400d50006001403100c019100071580f00384200d0f0124070407680e07001c04407018010340d8002000d103001000030480420383c4480140712102c1d407506940700050b1f03002d91030b802c000101131840c0209100007440780440c58074100490410000b140c000b0015411624002c1c20000140a01001d0180002c2d1b401001c5c011401481c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 789122526 1250 789121276 789121297
    0x100e010213030f1403040506030c0a0309140303090c0108070c0215090603090619021908070e0907090602100e0a0f0314070309210201020c060a092d08030306010c1403 73
    0x1001d1580da490152490300044805880c2c000d4400c80d40e4461000100498044813401000503045440e03404d0b00c010590b010704c10341810306035680ca8130303000148010b40341c079000740e0307a140956281d10700f0440305814082c4a41c00300e410002d80400b001030702508a004684400d40568501014021142c2c41100c50b20076030401c01da000c18040100800c0d1080020098032610301c4010300d10320202c03004900c0b0203038016001220107548a88003c0d09040d44030300446903109084d8600164114850f901085504805071064000640c451000707104403601000182c1078140c20301010095a004400850f840b91140c0400030540d16045040070306140c800d80381042c0d5000e610b1000f43e5290200d01d400f40c103000c080d120b1009601c0d490900200c0182003c90544d10756034040e0050100045403401b004007550102101c0c01c14003140b41d001003840c040f20901460300189040c0820242003070704482c601d802d01e25a001d91100e900c200100b00b10341e41c0c0000c08440e0341c0d6118a201601420001e2400d085008803207051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 789123776 1250 789122526 789122557
    0x1805150d0f0203090a03021903080a23240d0b0103171308010f062115090507121a010803091009030204021804060f0303020304121b0b07020a1403100e0102 68
    0x3d003131180862216403044c480c0d022180b05025442c00f00740071903003500000d404100c401001400300e1010360424a00d8400440340001c001c01e80700345800118000383e42600c048500c02d00107040c3c0268404000c000c0c038004446003115034100e40c0e00d00c80da44c04140402090740d01050300c1490300c02402c00c150f0b809003608500200f40203440f103500e10700800c080392080d00014281440042c030600003950001218503014102c1407002c4030740e2500c0c1c00c2c0031505801da514050355a5070312004100288003490152038002c3c0350301b11485590422091014010000882082e401c00040014450000c01c4070160b5500381e900e55400c82150740c05171519559030b070001e904540005141917a0b040d4210b80385020000403501006030640396441c461a0f11041e010050141c0d208210602044ea58604001e8050748902e80c14050b4032078010708c5150403541035018555004003c42d2404c214030300085410040d150901c84840c84401a0300001da0700d40e5070203250300c507880d034510320b00f42400707003c0d01250714440418000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 789125026 1250 789123776 789123781
    0xa020d060b240c060a02030c070f02030705130219020c031c05070210020d0306090204060e06030c09040e030717132105060705180916140d0c0f1805150d0f0203 70
    0x110036040d0b1000804610f00c0c00380f50006401180c543c1b0035217004419442c02a4201442a6140d41816400f001c0c166818030907070300700081e60380d900282e54070600403a90000d80c90322800c5541000410f001c1e1900c2c004e6401c002407844039a100042c0d00e45521344840c22140d15000d9811080d10385100b680000783d003214a152a0401045d0002400c46d0000620358080015660301c401000403400b0310700988000900e4400006594a0144050b60700600300b2950946421400000101260703113aa094488c160008640d01d01444050400400c43d141105c507142d01e4504000300c550356601d49802062400c00088481002804041e03402000742e603400030441c1c0c044e080040c0c000d070068014011106086602103680e40150522105aa001c2d00320390540e80b140081d400c0c410f469070b48109000c400001000d101c00000340d400b5014501c1d0303900c415191105908414074000b801070000c071034044900c50b00300c4010085511500361746289102c2c07602c2042e07190030a0540c40c40240041e802d87c110301c98000b005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 789126276 1250 789125026 789125089
    0xc120b04050f07030210031505181f081c1e1e051c1d0109121101020304051c020102131404060806011505070602040302060d09140a020d060b 62
    0x412030285000d80111460340140d03140c49541c039885800001d401c4494510a180664020703084020f003d03001900c001845602e034004125003403004074000c40201c20103018000740c0c000001d000b19003031501c000c000d031905040440d126510b00c2d0190700c520800d0b110480c14a0b60314800c1401c0c42c40b0011200665596810121000b040c6803000032000b04582c0d03211140f18075142c010390844124400312100c44d600e4500b408000c0380100004181409840303e0b4074008250801c0c223204204c0d000b4480c144c02d14856000b030030010103040701c40c0702c4201160701c10024040421170006145902180c51140c3d00180007401d5412406401440d1259200d610100d1011481e02d071240240d03114600c003920200012580c48810039500c41003807140c0ba07a41201401420f14844c400c2d001460b555000c2c03030300589496502e5000c580d2580c0150303900040182c1c1e85441d0020404c281c460b048181603c0001040b0000d03264002071221849101d000789025603071101000741d92504141c2d10b410039040104420641480321 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 789127526 1250 789126276 789126293
    0x3090607030c02010c171f03050d08060d020d02040902060409020a031406180f0408120c0a09060f050412051203180d030606120c0e0604080a1704050114070c12 70
    0x4810030046030801c410389003a2841446003800b00e1500381c0d034015800000c0c2494220407880900207a4254480003415814451761440b07c80c010f611607401880c0d02e4450030401804881c3c0a0701c4180b00f620340c1d00030100036a46210305541c4194044400103415010341c07001441904c91a8040743c0d000f8004205800c00c0d036090741c03110b000c129010100348080c7d035a01c010024044900e881180210722800b0100d0380c0c81d0680c1c5102c6130b0291148c0c455a2a00500c40d4201e40340540440d201c030f002076000222240042c0d4020340c000c0080c1201d0800d201404501e01003d030850040c6c4c021071a030004150400d4050007400c00005c4240740c0c030f5040c841d40c1c0c4c2c200201950f0800e540100e000b400c612601800c42440c03032207171050004441c80d039514084004c0050700c2d00e00c0903000d0f10740000c0421182450162455903034800420040450000038a00000c4502e4025030000340f40540440c8100c0610040240d1b0341c1040802195400d09425907958020074901903407400e2864009840f449400813911041100b001c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 789128776 1250 789127526 789127531
    0x10605280306030204050604090b01120f060501030b010510090602031c061a031015090b0711120609070801051603110705030a17161d0d050609030d0e0601030f030e15030906 76
    0x81c5e40c240b0161341e50340140025203011400041ca100b850713400400000c410b40240ca00418440d200c130920441c42c44c1c8601c02510000c1c0c1040c3c410a03001d00040042e80b82c400b44a03101c8001d02c0c02c2c071807080c81c03418401035105d004100341c0c51840040c200e4030810003881a4000806440c121810706028145070300041802c0c0c10854a01654680e211000b01c0c2143d43c01c4050114054540d5444003064142000400c0b503400085086418020002403500070f80d840d505024500c40c144002403075146441290b0618140742030788603280591524080c0440c421024030360101c40c1c075090030040f981c00c101d00700031041c40c8074640d80039100e40404124001c00d603900c890100413005903452100480c1d150840a040621031075544031011414407203e01c0e4221304103602d07400c224080180300301d00c0e54256440381828071108981d10207040d00700042001c4684100c3c031480602c02c60900007081158115520b400010100e00b0010f07041c0709207807003c02101d0b80c80c0c0c01e068460285111415440342081e00c00740fa9140420f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 789130026 1250 789128776 789128779
    0xd05061602070501020715031a04050f1b27061e091003060e061201151706090607170a020d18020f040203103003110105011406030106052803060302 65
    0x310000050251700c009800400d079020f8240d500d45880380341d4001d0380100120210000b0980c03260081444aa40318842c8a1003400310700c0314400c00d86010300003503a005039520042c01a480c02800182d012070b07000201e03e4040b02810b0030000018141c0ca0004045010b00f045441410307000c0300c290b01950406030003074441518255400002000703145010f07400d4500d01c1c01104260007400d00016850324007006924031800c6400000524050104000381c4030001c180c00450034040c0e0f81c0c040104c072101c20402e0560200c2401d01804445c205003600911003045a0a0004040c800e240403c1080c47e080e4112185c00e40c18000800803d0201002c401d5000500503090707105162404030715039a41014000c4034821210312010101c03417402c12020300e40e20701d00f940d8014180c580840b580000203d40e05801c642c028000c3e100c1070a06642d9203403190946005810034801e014560700100030944131081640d041d0b032550b040c40d80e01c0700d00c055005802498400b0507992100c1d0307010001c41e0301503016401201680e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 789131276 1250 789130026 789130033
    0x10f0b180306011203170123040b0901081e01060501080f072705190b0a050d0f1815020903030a27091b3906020c031312050703110d05061602 62
    0x25015040943c06d200f48070714100401d86881105d0030307a25207044081c204400030300c0005d6081d6000b000c102d4030750003608851303003e0f441601075001508004050804543c40340b030003407111a003090002070400d04013900414444401c0004100e09500444041c02121322030f846619070081080b81c51542400c036446410b000700704101d00a16070304501800c3c10300350780d40d0a1005142151040d011180303640204d841c0c1c00c00c00d03922450300c3e0b0311103654062200c244880d8034502c18070382414107081800240810075409814410028052551000310a40b03c0161042c00c244140e001d8031b80b54030303171402c40004e405e140c40085948045a01c56440d8080050302da45880139840900c3c40140542c3d080c0c3d0307a071911a4490034500b07141c0c042c0103608035110000140c04010108203082513038234003050340c100c27540c5400d15070000b0400340011900014003000400c0c2e48400c00c00d400b801626055140d00550001030052044c086d81c80c960354441c10540610340d40d101c004c40d4017500d880340d0606031390316020204000600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 789132526 1250 789131276 789131297
    0x200f070f050d020319170c030603150f012105060a0203060414070c0c08010c0504050607030509130905060708190509010b19030c080a0206030711011b080a050a0203010f0b180306011203 81
    0x40c40f643c0046c00c0200e060b01184080e40310b0241c005516040100903a41c50700c03d030001c41d42c02c00c0840d007505000709886200010b2650604054111102a0180502491900c0700c1001c011a0000940c6034209851220061362034407020040b5016114604c11020114031550501807401d0740020f4030a41c6030300906113030003005d448200301c600380c2c0c030981c0c0b42c00c0004a09001c00c0c001c0340380c50001041c04c82d100b81402807a090b0a9804989030401103a4071008003540d42c840310301404010302110740e000c9080d00d025801890103600c1c0040040c032005509110603507840001e006510300f584a20480d1030018402d15034100d8039915210400303068001106d00c0c901e488000030f50030381e0005040c4070b00c0c1e078000d1a4504640d106001103865200041401e8403641d01c40501e82c031007d466444200d50066190b4401081d441c1c0b14042809a40001d4021001c591040004206400001111800f03907901044059561450008140110b0b444500d0013503150058400001d00090807100c101c1010340b0130b403104141d00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 789133776 1250 789132526 789132577
    0x3303220f1b06020a020906061b030c1203010b030c0d15270504051c0c02060d0603030e0321070201020304030c090203090f0109050309042c0709200f070f050d0203 71
    0x140500d10845003d030f070100c4089001071501805403070b4040b401502075418200e002c501002c1400d5a01c01021203500005031601c0214000c0c4180d21151004d680114a0755244c424116080e10000784484000d001c0459000c0c1e00d0041500700c1403e8007904504100c01a85500c2200b900c020f030030003001140140d01e07a40c00304000c000d000355442141c011011f802140710310f4200380d6082454180c0c18082061718800000144d44107006403800300c800d2440082e002c0d0442c54044c2c00003244640140c400da00101001c0d2103018200c40410001e4030035001d06071500e0680c40140d10714042c1740c03c020182c085001010442c00c1c0e0035409944240b0a10040b030b01d00b007258600e180d00300d402040e8083d0054200b081b076600e4a0a154200b11360140015540c1f68290b0b52081d000f4642d68109980d11843d5089103904000c83d038103501541d201c0314000000c10f90300341c0c0904040e1130113101e910072a8080c16404100307201440341070600285129000740540300c61f40910345009450f50300c03144244002990070a81c03243e10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 789135026 1250 789133776 789133823
    0x10201050412030b1f05030609070c050736090b011e050f1f08061f020a120302090303120103061109030c0103091415063303220f 57
    0x140b40c11580b4507001890b1254100c0107806598074068006030404001448104811000101802d580d914952603090031003c01c201c012002c1e000ac020801c4a4900c5c40120304042903a10859410f440c0c078028008041080c5c04d18a40d02400c0c1310b890040c00c0400c003400c405141c0090b1b10300c0f4030845402d0002d03030301c0e180700811002201c0142c5c443e0016414042c05641458558070100007002000040522483c121807051b2203200030403c0d0000d9680d01c280304060411054640d01103003503440c0355805010550000350346410200c8040e1042d401d4801440606000e0f0f41100d01e42c06e805026070741d54045906440740540030078881103480501d4a001000020b01c0b610139240c8210000f409011a420340000440151000c00380030b803a1b4003042c480b5840c01060401c556a141c0340070524110720b51920303404008600d0394060072228030b0840d20700c16142c10500f844a81581c41c108030503144c2c40341c940101c001d0603076194005c00d07485200b07018003c178203200172244282c0c0e005101c1c9108590719044112075509 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 789136276 1250 789135026 789135031
    0x9050a022e03020f070204050c1e090105160c080d090608070e01050a030902030705060301270903051b0f0304030804171501090c0c1208010e130c0e040201051b06060f01020105 77
    0x119145082000070200c0c882d400529211580004690074a01c55800080031100c3c19600e600c224240080e4501041648804804c50344c201c021841d030802007807400180681c4a0b0002d0300b50304101d1214080304200048500708068000c8a003198010704007200040e1000006000b080c0105109000044505204038240c50136108180c3d2600d050804100c1c050740a08400d4404903414083c420b80841c083c0c5074003000e140244080725220005101805888205501f80003c1074405030501c0b4078030000c82e4004044417141000400034452180c0f401c0c268905140d01002c1c848118040020b0010601410300e018106072120304005000c00010000031a5441c008000f000a007404113400410009646038031218060701c1d1750801c0c4408599603920450300381130205240000c0b403102c800502200d0341880e4113036400181c0e0b4013070441d2600b86072104100001c69115a4640700e000400250469120f02c098491079032131100c00e0741c2d8420302400916142d070001c80703445004000207003c0403c6507105028490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 789137526 1250 789136276 789136339
    0x2406030a0807061e021803010b09040f150c1d0303210c0403080c030a0e0a030b060d020f04050f0402010e0334180507031a210106080109050a02 63
    0x2240c000c8541d1449880c1e04041410f4982669840c9540d04031181076000030320203000b501c070043e614826442006040c28490075110f019a00d0254413085d00e403a840c01c0d003a046500084103402624641c500316812100c00e4184045842c2850003001c01c464100302000e105c1d4000c15400c440c460400f8051640c1c070f0050f071601c100a07141c0c2061002003404441d80064021070000051480d02e600c039116020158002c401e1030001c2d6000013002041c5031307130140c40d800102c80101c91b40e0840324a03580328101c140901601c443d1047e00200c41c04800c55807803c604254a850140007808039241200185454180171902a4003041c1880526801440c0200300c4480080325140f81d10074102400c9241c2c030302c003805494030440300da480000c0421180020340d0751040c00d40700d000002c5040c0c46c000c1030040960b160300c003920203a0a00a0f50000950343d80902810603010f0340001c01100440f011030190240c00701da4032000c070300d510708082041405070101c0d0140c1340e5802a91905400114016941e40c088032a26004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 789138776 1250 789137526 789137533
    0x10091d2401090f03050a0501050601030204151805041803020105070f02100e030f13080d0c350c0a03020c0a0f030807031101050a02041e030201020d030213080a05240603 74
    0x8000031403228001000c8a40c1031508403002503d50b00c00c00c0c2014810b40040c2c07056071240400d5020044240506580104286025030070140b808200d00c03101c00038503124000703002461403c6810111070700f420100612004000b84500b0486010380300b803082e0042000e070019400c050004046078041d040c651381d810026401007854084070341031b883c01880100410030040c041003005800d0703040301030090050311141140342c0910a15000c6d059140022a000079014070004000810115284024021640713003d0000005040c51a04444550450158811100e1000440c3e424001440040c0c00c20189101360226070780f50b1120010010f1203420384c410014507803c211001e00000c1d8525018001e4184207081010341f5041206c1124250344040318003644c203941c049020882901d1500e800c540c2c440c0e080c420001840e0450700000c1d20703280c00d00084030900d0307000241e05882c0c250304661240205440d40903940c6031750181c5891390f00c40003c1c154001924900d15800c0200345031900b200b5000d00d4006004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 789140026 1250 789138776 789138811
    0x6030206030a110702060d060e01061806050c0a020a08010b0102070b0306102d020d08061012050903070b01090501030b251409120a061a13091110091d 66
    0x84090103c0701c02000380b54106000384d40068a5450107441590a0064085011400c0800041045005912079410042410846200144440072042c10b4840a14005a8584031986802c0c500024000002d400000100c00098100411340c00500c4000c0240e0a81e000c440e90791251a031580000e8a000b6072003004152004015070081c40d564410030703161202803074465118542c01c1012000c041d400b901503040001401034a5a0083c40c072075000b41c0031140080c180700d17017400041030011310540c00321440d9500d00c0400c2c02c80780100190b4403410f40c8110b02144a43c1c46440c1800034080a100c11100044500042500042e01400c556940010700c0310712942110007140450701040c2180600801c40320400c180e941c2a110003400318920700051000b0400c84040c0d1a083c81202c500316441d41c164001d0a0b8001010343d01c5606043c000c50105801062110391410300403070b4100c92000391688040c0f00101144074035080340e8110221030f03001c641e862000300c03000b440b819070b003004031035950a488106a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 789141276 1250 789140026 789140041
    0x32c01021507020c15030901140c03040308061507050c150c03071b0504050a23090c15040b0a09030303060603020f030408180301061815080606400f0603020603 70
    0x740e5a406065032044500d030001182c046082d0b460420ba005c0b071a0b010010801044120034091008000401032a10000b403038241000d004500028000804115404011802c659251030120030034100c08017407582d0350a01807605513900c4c00380810f40c6014a000164000c0c4c00071000c01900c5c9035a401501035441d00025030756035603090054200f90140c5140c44140496551164810f5901c0740c0c2500750009074804800c0c0400f050f210342c6d9848c0780140d12303940e0704005c07658030041118641d9800a80703562040b06401c02c082c204500907904621200c58003c1140c0001950001884084034020b4604002e440d44501c0c00700c040c0e2081034906d08040c441000858002040b00c0020900041101102000d004644001a00351203481d031001251044290050040501e1440780c420005500c0040701c802e01d00e0048142e45800e0b00800301c91040c40c580501650480c0f44042c0c0003850ba511455020204015200080140c0416800004640d00c0e101301c50040d200300788112810359800522030340c1141e484c1c06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 789142526 1250 789141276 789141313
    0xc060412030f1202070c05010206100b04050f120d03151205060f0403051303080307030b04050105030d1812030c060f0b031b010309050604110f27060109030f032c0102 73
    0x1c940002c0140284603c1d00340840c601c00340800c0c0344036a00040b0a907140c03800080c0b9100000d001b80e0201038110344c04004104400084908840054480802405813107000139982400c078a15044c241c05002c800d041030329810b500c000080d00f007224000402940780c4c5984802c45c0c102da40028419402140490100d600145003d0b510912a01e0500c0c80d00c4184103102d104030030302da4030031241c43c1008014041400e4250145613500c80341034804120540c50280026503400320704003140d092084428130301850a1002c0e85200181c482c02c07003000b51560039440c00500583d4a008142c404524240c5180f030b211540340900c6411040040040c100070480c0081060412481c40c200380c103060303642090f48009441441307989e1081340210400010812080d0612101c2e0030040b607900d1180000e03120010440c18800180b04691030102801e681c030740d50303107001625a600d01d60005808a10003110460406500c03030050070010001140501026280881c003124034043c2246036800344c0c00c59040b0580105130304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 789143776 1250 789142526 789142547
    0x40302101103180d0516090509030a170402061b06071b0203150703060f09060503010c05032a070b151e060a140d020304120e0319080705070b030901020405030c06041203 74
    0x4003c203002c00d49503a24a0b03d402114206c0d10412012000c080005905910490b64840d0f0130b400503501d0100f003030200030311140c858801e505602040801140a5480b401d09881d003a0074059034052140140c4040559900012280e100010f9103032040d045003115511394501500d540980142001c902c1140d07809801040240200c041503614280040c2002c0c10983e014001c2188500015015082509050030f481d80108400c0501004006100c035032011403104c60b09500c03158803915924071010184a120744117a640c0504895186024041c4100c54000c1c5404c084104131040d64140240704642c8203000b00000c40594030510900414002030702807100c80080d4206900e80510b0b14405520702c0c4101c0e00b050f40c080c4c92310000006008184c541156131175040000850080080b984580e0455540094011000b050382c2400f14100c0c007040402c100c46000b90121800b029181e05d000d2048a000750481e2103107611130b20030001c6850607410400129416108583c50701040e1181ca61404d0304e418284 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 789145026 1250 789143776 789143779
    0x8153a0c080d030b1c02192304090305040605070501020d020f03070809061b0d0e07030506040b070203040f050f0112111801031109012f0a060e010218040c0201090602030c04030210110318 82
    0x28940411440d903070020010048c2404121f000300e0000c1c0440c0c890910b1a1800c1c1c0140a285131652244c00710307030800c05480c11110707036190542d600d051502e010f5019000d45040d00c0e070f04500119588881c01c0c000c401441c03054910f07a891102035a258000381d545d84005407208599002d501c180020381381068002001c1c6805019408640c00040008143c80c0041396803096480d50003040621040044180c090bd401003101e20082d0b0030181041e2030000100c28a10070b00c2c1c440c80826101413901e90082d140c0c1a00a000b50340e04004508200e8107944556001c101044081c41e182c03c0c80c0c5180358000d10a41c420a000000c0c407034180043c002c01958482c04d51041c0b640c5041e055401c181d900d2074690a10446d010703100f0301420740c0100768601401030382c1300291450342c284d0050000f5021020044c0da00258044215404940030000c2360083e8018480d618001e81001e00000c00c01008007642001041220320a4aa10300640c130b01200485c1d428001090110064004001c0c4600041c0060120003413440c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 789146276 1250 789145026 789145039
    0x4050603160510200d0f09080d05071a0f090c06120402060309010603120201020909010f0b030a052517100f17011e0c08153a0c080d030b1c02 62
    0x980884014240441504d40003644246149060303d6881500000a196241890360703c06080c5450551182006000f403000c10001040100601150003905813042200c0d02c902441818500d8a070802180129a100c040c1c1c03282d10050300e82810a074088804810f600b0f8510f40320b41d284e90382005001d50019200c441c196481d00380203c045140400e681c00c20868030340006a07900d6140c0e091280320081680034015192159508218490001017103a0f88962040c0c400175041e5140341e0b813240710060352000d41420541d60b4001e050b68607042802c41001e43c0084d040b00046941e80411003030b40344240d00070b202e04002d15150400140c00f11001b014420302d00132002192840380760160341000c8610326114050b50381c540c0c1d500e007141500030310340a42100403090010284c03030080010840c4078540b640102c0c00660782c0c803801800c46030314409548030240d09552401c242c0c422410710280d41000e6000c2d8960318000d04085200b0341380648505840400040d04c410b86080f0300c81c910654402a142d03050fa000765 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 789147526 1250 789146276 789146297
    0x120f030c10050a020304030e0613030c06170a0605060703110319030f0f0603120c0c180603150203100e04020418140d0c0f0204181b0504050603160510 66
    0x4505001600810400e080209081c8022414100544102030034051100d8810002c0c44080790703000e59030442c2400207503100d650b50207080a40303091401960740043d15a960124004c5103050b81310603100d00d031311000c0c0d41080d000d45801d6050001c44900d44240c540c0142c0800004001034000d1010300700c0c03c14103409913070a1040010780540c9082c0302c5030303d08001035540c94802014650b14805c45241c10319050040002c20704594500c1013a1b040394416005200104034a00c041046140c2d048001c0c002460b0012801103001000601400090100310342d164180c00c1300640307188461095034814110711051627445803130034806843d00c0c500078006a8005d82c0b9640d0f194801d000420000c00c1c0c2600c2100c0726648508030140c00f500b00640070300c805041100070348840000c1880c818000c010950111800500300c0104c64201c0b0a80e01161030050844021007200701100c02c00b070380001e0454400351000d0226035903600800d91901c9060704410412100d0500a10803410500da1841c240b007210f05120880300c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 789148776 1250 789147526 789147553
    0xb0a260304150309020a1e05010302030a060801020f0d0c0c0c0b0d1d0f060109231e0403020307050d08010506070b0c0d06030f1b21080d0507020c0102061008030912 72
    0x81d4503001101c010075180d1310035208508144040c0c07801003000d545801900000f80c0b12010541000e4800c03541016001702c040f4100810f80d50010008094800007190380302c00f103014101c40d98000a040c80146841d10800c0148a4002c212460740f059110036900740312410058900c2441c1c004003841c419890f541c50a40740c021400c29400902202d1200040c8a04114100c506190100503000b01c03500707900703200c02d8588446000c102c46141c210b4600c0c1104075540c510025040d22100300c504024804148400e002c24190040300403d507042c0284c054500045030035400303a500d01d50a00c54550001820020bd40100b1014111103170404a41401680f800641c88800e07815039015400680c0c0c007440d40c0000b0020040120211303050142c0d041c1031200706614010320b402d4a40521603188641041e1503004034204500034085910715101c0707940400503030519120096960b60601d5500740980701e02000b01c1c01d1a151289000c040b1001880114a0300c40071606020303e00040019800c00c1b446600342c0c11031013 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 789150026 1250 789148776 789148799
    0x40e0901150605090a080106060207030204021c1416081501050912030f0c15040f0f030e0d060b04180b0703090f0506070e10030207020105040b16020a080606040b0a260304 75
    0x902e082c0e61420b445548610810041d00303190f51110070036a00d03051081103100c1d008151401101c0e0112801078035110711070141c80078201d400700752411086ca01101141d01600c0001d045001e28070b00d08140392540e1280710300341d6081a0903208621881160301c1020740540c0301c0c2c0018100701c48042d041d03210100c01c41510034510740101507650000d5402084030881030000300000d48100b40107003031000c205d042030340341c0000b01091044007034240c0d031200d640d0109240c0103254a811350f04000c0d00101000110b400d040000b0100011818411800c1404210741105880d1a540390103030040d22500d100d407149041640144a02c0008907014016601004041003040c0542d03031040c1e42d036450f040c0d11040f110302082607002d09144184203142c4103003d4040540da0040c1910140c55800b02e100c2d6548214030002c0c0c224500b44a8000d500c0340c001e10700071a00c400b0214150340214400d540a004c41103500003000500358a42c09002140c03020002520210390390301c480304410038100320550786050384542d00c4510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 789151276 1250 789150026 789150029
    0x301380307110109021809070e0a020a031802011d010905040e01020a0206010806070807080604110d090c170a11010509030304080109020f1215040311070e0f011703040e090115 77
    0x95481000c001c1000791900001c41000404000c0000c10036100309034001101e60b40c13034042920071254003200103078038a00200b240708007409000321911214071b040701d807a0019500100c11980001d0a01c0a0030030041c100c1d4006080456058595051105621101d85c0c0c12001461078941001042c1900040b541c589200e003015603d2030384005131307503a011108064030382081a800954030b41e005d40208080036a02580d05a0090702510f080340b80c903254000064042c3c44081d00d000008100000c012a00a243e5130100790500c0c07095041300007060341e0b80300c0d8003404000000700c50038036003100362401d00103031000d00025848081410a0340c00c1a0304030000c070345140c100b5005945903071365401c0710000f0342c54110700c080c030064000c90b080125480144203031038a070405145d101460395000c002080406010b52101401300d1802c80840e03040e1903503003640740c0d9840b40686800c2161140700d00007045080081c0100b0b11a9100b440045d85082e144c55000840110004c00043c400d541c1c40741400700d01200442c0410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 789152526 1250 789151276 789151379
    0x60f1b0905040c0c050a03080a09080408060f01050f0f01080a0603061409070b090f1c051c08130308040f150921030e0601050f04020c03030106021c02010605060301 72
    0x40c1403400d0606002c100c0d0b451840c04014082100340820000d90000350709103100d58035151544e826242c04000030060300103400028200d00000c500131542c03050000710709e4801e0780e500d00e0160b696640c8070180466020600c03940750f0041140200d4820307075405511041d8002100d10400100103a8a031110300840d806407004013007048880b000d001101004020510107040702c00b034100e10301940100050201c0c03040480480c040d641590804441c0303d54140d40382c0b081ca400200361010310b20704285141001000380c81520101c0c403030201096100080c0710f1004801a4180c40e8a030702c0303846580f18035920388100002114040800d450401e102c000c14000c0644162203419050301000203075038642d9601c1120301100040501d400c1485c18074a80000e0301c141124002e45401040183d00800b0034081e00c00c080540100340b0000000013013142c0e0000d8440030303640071503d200355510540c400c128282d61247c0b048641c001400d00041c401c4480805143c00000140c500c0d881006081ca0443d18440054a6502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 789153776 1250 789152526 789152537
    0x6020303271b0907142b0911010315030503040905100b040602011b0e09040602090103020c15060f0d08030c13180617030408060a021b12040515090d060f1b 68
    0x1d0443e080182c4295003200460134990804003010211a5450003040c06411181c140351544642d20341c040c2569407036a401c10304d02030041920601740580d41420100486000138900200c10030580c011108440513281c0c45000f80d031415141c2403103039002e44009841010001c240020018803c05450700410041070f0640010943d010150140000c4c4449004003000b4891460b54940f525611403110b1580542d01c10001a00c40d542003004900a0182c0074041c400c52081c4003007030b00454003080409200303074812103000b48040c075540184903041da0805002800071030300340041081d03e655040a408803121f6030180208071951051034000c0032003418042d0b00206d54a10091142c00360f00758a405000b0380d100011890035140000362540ca25004041c9410a42c0c0819900389811030350b1600002c85801401312031020840c541c1484d02a44035100d55403103040c04034212110a02075506803045a18010521002031800391140f00c00b0300f000d00300300c00f14a0350700c806408180d08100c0080c40e1883e45d03a50380 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 789155026 1250 789153776 789153823
    0x203060408071419060605040b2107091e05010902071a040f0209010b120105030102130302010e040b032d0a030c120c050d0c0c0e1515070204050703090210090602030327 74
    0x803140c1700c0c7c000c10700450401521044503103c0b4141e03100d00c40d4a4401c0054440c400700d0b00c941c00c2080301e802450106082c05283d69035220a10341e400c3c21701500c3d180401042e641c412815049104d1000700400c250501800c004858012140496000780a03d502c0725241d035081e80054a01d04090f0006c04200307034082000140c0700c081c001d9140c05804203030000c6280880300c00b6901051170760751100904019070000540c4554483e50018240404040c0880f8030040300c04c14400391201c0c0c405510180700c140e076003000c071ba90a00010407041d025059103800362070803043e03100d1400d403400b014107071002d00451104c0400048c0e810002d0500fa03c1c2a6515042410107925054940009652100300e01d159000148040d40c80da003144070060344012a1040c241040c1c0580840781070107404006503000d0302c0c20082200007a010382003030042500c02c60f001d00358000c4010068842044900803040103a00500000b42c10240c0c4c0100700308090b0404004885040a4010075480d2504251111001c01c001c44d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 789156276 1250 789155026 789155033
    0x10030b040f051f05070807111b03012901120b060405062a0105070e0316050105070c090207030c0b060d0c06080601020a0b010b04050a060503090307150626070902070203060408071419 80
    0x589500840289450451081d1072440c465950144140c24440c24070100b4041e003130340c2e4003584001300e0b40ce030340500321100b030004481d03440d001451a0807690126099861000000038144140035415000620490805080070180b02e40b5070401007200f2000408440c01c0390040200da001c2c01a8952100c0010402d0720f40101d00405515022003a6400f0341e211010400385114200c1d08401035800078a48140c0340c0110b414a0300c50130459038018950743d8070000e209018507510040f444401401752080c14641e84540c800d1000e491080304002d0540f1440e10414012207114081039a04000148112076059805440b4444006020303400382140c400c00207030400450801150610041525040c00d50035480c01e40091900c030f1080700301c010000d001351302c008000310705c2030f5101d000500681011580c1e145401082c13081e03080c05150300044d491203450720005225409000302c1385c000f0b0703018000e003040c0c0e260b07a91490842d401603141210a0220002800740c2c4140130400302500c0107000c00601c041022509 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 789157526 1250 789156276 789156287
    0x7090c03060902190e0411030f04021c051513020f0d1b0b0304050f030307021b01021204151715010e130c08100e130f06110409060e10030b040f051f0507 67
    0x10701d041c0107e04080715545a441c2c10415241d1103201500500001ea8840c80020003c0c0c442ca01d00180302d4408000e00410711200041d001d0103492000203d00341502c0c2c040c00c010110b0a85140254014800013242940e0705000c00c15031810b80c030800e00b42a80c0214060541140c00c4a07401c4042050b20110801050140070011f89103950400b1014520f542080e460007074492032030344075018408055003070708071490f4402c10002d12402d100d460010340f10360b158805044250780da248800009501084229a2000d01a03038803030241d906035440000c140070b0f070401510001d50003d070440c3c0c04052403590078180d0714980038030358403060740d56110700c80741c80d01010310320044540380c000c02d200301d14032000c210244600311504404240c0120b00107591010760b02d0400050b000c4000c8003845c4010224001503650100c3d0880d2007690314900d0b00880c0e561381e00140c0e4140164074032019042200c8180030030049507003686030721000c50040090341c440000701e600d082d81100400030552051562441000a26a0f105 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 789158776 1250 789157526 789157547
    0x3070e030c1005210c0306151903091515090f0e010c091e060c030e0301090c080303070311120a020a020a12120c0201050f061002330106050c07090c0306090219 70
    0x5100001c0700d030400045d2207502c0d000003081180149909000101e58190410a6500e201e850710380c102886e4580000003409410200c501701d4035040b1100e031051200405000761414044060300403460701e445d086c4186c002d08a28000c0038229560f0745602100d0501c28042c1c00f90801c1180c484803211481c0c0f1420001c400f4040031803180503c00144144031a0390300c50000b2001d19010b1404042c21983d99002900410340a580101040080e400000e0480b8010000e1071150314140c6042008582d100c9070140548204010303015201c5078000000d0f46e1100b0741c0d002e00880680c6104548142c1e030706c0c0d543e007501c0b122452002d8000c0f030740d10144030300107082a0107000b80041d410310091000c0d040c900381504003a60301404185c800d1542ba204008864801c01a94034400c2c50b0000320f0482c008044103000c450302c005020a044d08141000114010b03026500f11945042c10100401d000c0c1c1c60890094010300380010038600f00754588074000780702c85460000c2c0507001080141d030000d003000c48134044d007000031740c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 789160026 1250 789158776 789158827
    0x1a011404060e04050402061b01051501030b0102190c030803012d180e030d06121407060c0818130b1318150905030a051902070b03070e030c1005 63
    0x42109201e80e60b40000c03101c407840c00c25140854035489603c0091040d0103500341e10462941010388140d101141500700341e01840ba007a42c20003000c004200118240d80b0740310070f130f1030150b440204c40c03604a030b02c4030300442c1c0b5081c020301000004940300c2c0e440000790b42c030a03401555207454080418680030000c07284400c40503144000600c080b45045041c40304100c00c0c240c0714043c5a034480040b0305039401403040303c0ba66100c105d800c210180d2610000e4160580040064030682e13084240c00016180006806c0c064070780301c2c1ca80b140c0c00070040c4d8400070345070f000c20b0702600c20462b120500c440580b14911001070303884803400e001c5104130b10a010301a10408030745400d5007585c10160590410428102c52102c40303a0821070740c82958072001c003400060428071600910038400015861180395101024280d201c940c03040c201201d070b102d00002c070b0f5030b40164000c0d0591180100081800c1500a481203040440080c094403212020100001d0351008401001c40100d100054006000e0441d8844082130841 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 789161276 1250 789160026 789160067
    0x712020f0c0102011e05070e270924070203040509100e0a0b06040506210c07141c0815151e160f03050d050103050703060614100e0a091a01 61
    0xb103400952030110485c080c2c0500d06696a003ca0022840b030700c841c00c40914050f003188128064014070000700210104001c40c0390f8000008500c0c15103000c1201d000480a010342c0c8180d140d001003084c12040c10180c051425803100b04070006164442c445524490106440c1000301c95280a13200b008030318005120b810720500e811201515a40c035181030701c0994400ba140c00e600c4085403203c1c014005a0020220f00a204281c104a1804070003001048014803e044c0311680d00890340b4031940c0c0d100180e01b00c0040250f031442d050340e028840c0510a6121354030100d801c0808034a000071440c40e00b1071090080d2444000200829004581a15003075464444500c403454500010b001d1b03d040c4d0700951000f0a03248118008800b1325100b08241e500040140341c00300444c0d6541e1803c203a50b202e0a1004641041c01e040001030051034044501c40c0d00341003d8000800c00c2c1684074110340944450b044503074882103203400458650403c1c8240304224a010001000c0281c142c000034001402800b0660079001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 789162526 1250 789161276 789161291
    0x25060621050a0809010201110408012003011a4f0b0906030408040519030c09050c070605060120010b040b0d0206040b0d0f1103190b03070513020712020f0c010201 71
    0x41c0002100031403241c11041581e01e131012071004030301402494050301d4041c0c0f00490b010078460019031012443c01900704030320391040c102d01e20103003681c0024130403101804591000c40000ca031001e0700418007140c1c4142c081d043d400e0309455404031414a400c0c5400002070114504038000440141e000d0f08072040e040641144c3d151007041c2c3d0481c440c94420b41d020300c0011000c2410401c02402341d03805010010490f410150510b00001e14083d41440180c500580c1401c00050b00c58141c42030600a003184400146080380b5a1140c40242c5409490b1504020108070700184c1c0140c045100030306643c411001180b00c0071042d080009903500c40c0007042c0700b0044100c184006945150480e4200c2d0240c0218503250201122110001c1c040100300000b600d051614020a034000d1344001d40c42003000d01c80c5488100c0c80801131404440104695680590080700c06014034601405045140403900b0805498690190765004181303441d40c4031000075038859001005100000c0c001c8000c1804203100810441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 789163776 1250 789162526 789162533
    0x30e03010b0a060e210307050d0f0804021e151b060903120907050a09050403030e120a050d0906060e07080a09021804020d0f0507091104030804050625060621 69
    0x82c95104480500c1141150402c050703c891100c505072503e184076840001040004454696000311411901c50044c11911010513009010001058038642d480010554840d401e01c64480100b85a54141d40705402142c2c21a0303880d244117240342189007031081e031102d0340346108480640201d140101140c101000b0000d07201c40000a40740c01c14080105400300c2c0c0c850010140c01c00354160001a00b10780358500200303249a031500100c0c081c41c800c1c2c0d01000322100748020982c4815801a540030211b030100588802c00c0e100300c01a080c0300d4180710000031010300e00c0da01e96040b01c1c0d203603010080c1c2d4480f910070403e0568101c2c480da6803245547d1002d000b11041503000501c5540140c00010f0301981c01c00c08541592141a010011154465000e1100c84c18a042c1541c0c0d504883c81403030b070781d02d00b45010184071403001410348044a0b44050b40a0810f401d043c20041c41f5001203003220f800503c2c41d07010741c10090100502921032401034900003006e40c10407c5116003c1c13540c90864881250207104038002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 789165026 1250 789163776 789163789
    0x60d110a03111c050c0403060908120f060f04020c010f0603050114012106021b060f1006140315060c030f041a0f0a030c030b030a0303050f0610120203130206030702010207030e03010b 80
    0x10841c02001440b40c3c0c6031174042113540216000501210f14201c0300b0710400c0001e0f0001c1040303005464000d20b803aa074401140c01e1611044841e950490000b0110603440e0030141c0103440552550700c000305054485240170812280301d80d009640320381d100d9124950b50034a10040c54003415840740300e0400203c2519130b45007030301401d242c01041c0715400546000065000719204882180da1000d42d402c506000a11812a5005540903100842c240c60300095440c064a114040007801d000b5650450b40c4036101206003141340e256003074012404208800041c0003e1004007032480f43c03601e0164589041044240403140c0e000ca526400304e008012108145170203034180d400c850581d00e000300d910840341c42c0c00c030094107181080310f0b0148200b00381c01d404c150705900101e100e0119400c0d04001d582e205410040d072800c0030b00d00c440100700003002d1016a060680c00955000e01c03103410f164903181680d800702c0d402d544101d0701c480060350f01240d8041056440f40c050101c01004074000c0c00403058a0380042c41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 789166276 1250 789165026 789165067
    0xc06140c160201020a0b040311010c0e0102150901090f1202011518090f15020a0215100e0705040e1e1b03060d030c020a080606090f040b060f060d110a0311 68
    0x92100c9901e5031401c5a100b0045540e419602c40d0305190a41003515000d40400607001c10082c4035400c0226204850b4401d015101c0c401105a0003062100051308680710320000240601916540300c00c50100816869a03034400e1841c4998a05409001500d000a085907961b0411103000c000c004030403c800900501c3c50140812110310002e851007661400710b8842490520007800c0080e0142ca00b4540c0c0c0183d03016000b1050550245d985c900e0822411501c800c00032a00600304840740d000900c900c0140c10180b5501032000d051451031b06440390107508141f50211145804000380c40c03d0698032880039540243c2050401015032144130540345000320601000340f0840c00340c4001010501814481c10440c1c1e0210b4010700301800c4161076010145d1501003c075503950241801e030011542416510050500c507507048a001003041d2104002c00140c40c910a006a520503070a0001c41e06009481c032500c1502d41c40307100700302e50b030300d00380c0e4009401d0303403c02068104070100c1441860301e9540c0d0202c0040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 789167526 1250 789166276 789166297
    0x140916210f05040501020d0b03010501031502033301090e09070b0307051c0606020607140d02030a2405120f060c0307050f0a0309020f0a0602100c09080d0c06140c 71
    0x300d403410300c000d21000401c503080345803411604042c180400c2c010194010505081c1c100001e00c441820318044c1402d803202880007c00c0c0480d012020f0034101038507406141c106601e191100185050f034040f140028440d00b81e40071200c06080c100380010b43e00140c1d1030b4000c10125000c0c844500e0200a00c5490303100b03d10400c4489a00000040c103030f01d00c5401100c405140c581c02030000000560b100304000c0803035000e448054881c0c0e4001c0381155000b07104001551b030034421940e2826000c141d417003029400240003615001e0715201d00c07204040752050010b00d00404e070400982ea45181c0350810501840444031b148494105000e00030038400040365455100365542081a966211150b04865170300c00d1220402e01503c0200307900ca8400d0749034004120407802140c003420000020400c10144820034801c1001582c402c00c034a56500303900b6004044c3c80c280342d0030260002940d451349181440034007248000022a042e484c1d0b01080018425110300120f040206002ca140c00d9082c0c1f2010703c150340992 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 789168776 1250 789167526 789167567
    0x9060e06180a0f110c0f060f091b0604090f0504030311030c04060e030a050f0d0207141008060109180b03060c16170403060c200c030304060e0f0301020301140916 71
    0x24103e003041d080715500002c070300200e980d01c80007103110304e8881b039140301090103900464000c5076075211603ca8090080101001621503400a403003981604d8883c840080c2c1c0080302031200081070344140c1b158252608019001083c0c918042c41e004048605c480640f420503c4144140101c441c1090240c405442007410503039020008500040d10f020340c601d10003010b41c410102c02c07103000e03680803a2482c00402143c084510300d5440784010306041c07400c94400c42d0081e01142004101d00d204003001d80d0050410b040400c0022380350028034a00c50500c83c6011445501d502c1401d6403030904001e075561140d001d946c500e080c0340c6204030210001c842210702402034468410f051803c166800220341c02181d01003820060b0041c0c1c181c000e08030203003101c4803006094003200b001c07000c1c440209804003103c40041c003a41c6003e04080007034860284031319009410503641c22140c000c5440920003907018100c110804490b107a616410000c0c2060010004c803012400d26802c0c0200c0e0707401020100301c00c03482d503120307 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 789170026 1250 789168776 789168791
    0xb250b1501030f020c03040302031501060807080601030e0f03370f02120c0c090112050715030f290a1401141612021605030a140c06030109060e06180a 66
    0x12005000b00034803c04041d4800908132948000003c010000c4a1085e400d4890348441380b042e14202407400d00c40c2c0004601c5100000301700c64481c40740c02d03038065014100014400561880b0500c2e040d0104003403103203580300040300c00c0d05401041c2c0b940700700c1105110361401c540b440c14411500024030410b00003401030000d402100c41e8024440300b0035140a01510b0f549800365020320a94951910b02014052144640046007003600c00c171b000802250404010b0005920304038048012440e200140f204045c0c5d1881b46928a101070b0003940700e00c800c24260003a0320024940071840e51100c0d58400c1e803040da4240000c21181402080a03042e1150901b808448038445e41410046032049400b203107030030020f4452034010030022600801100305154200c1d146da0300c0e090700500030300c125806900d605602c60380e204400503021340304446c840c3c58000c00740c41c500c84190340800c4a0350000c6c0c1100004940714003051040100d20050070703a10000c02c460b903541d4201c48240a24948101804020315291a42c15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 789171276 1250 789170026 789170029
    0x9090509011d070306060501080426091809192109050a08010c12051b070f0512190c0f020405060a031e05060603010603030e060309070902040b250b15 66
    0x8032081c41803010b40c000c41c800004140e03865a01c03d000444019242c046c0108855201d0020f0300d02c910b612500541601c02c840301c030150002400203518003d601d08003c3d00d8240d403540030150071039011180344642c060621400003810070402400700040001101c60322401301740140b40e185101d200102d0340c648003400040045070954095000181c210441400000b440241540440d00032491695040024001c14800400303440060381c1841469820301d0040221003042001407203024403034410380014900780d40d112410021026904c000411000c40c0000301004142810b460f00d1809203004814800c8907520b22010780c02c1408040c1c051540d98001454607141d40c2c000301d01541d0084040100d45403103404d00700e2808140745003241c1380d0107900c000c1100c80c01e0500035441505e0745034844441c608070328000c3c4a01c6820040c00c8100600c220a00090310015a01c020130240c000062640c0d0399034100c0d15240800280300c0c08943c0b1842d141006600426461488680c2060040314080f444031382c0e110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 789172526 1250 789171276 789171281
    0xa081308010908090118030506060111150a150f08100905030d111305060f0a05030709030b0103030903120806030d1d0307120c050919090204090f0c03060e030702010909050901 77
    0x4012400c1507190421030024000c1c0c0b0800340092182c00d9813030a41c05000c2600c01c001c41c100d2031100a02e968010b02c0826025805002d1a0106008100484180040103a0150f019580584120403115910482c071080c811360b944c601405081c0c120b104041181c90418820b07510a43c40c92204080b65032449034600300402402155460f00091400340040c2d10002c1915545038442d002c1940c540f440d03031034000b900d400c0800507203045582c20210641402d6200381c050b12540d0006100d44204000361401000181401c41c610f03000e1406a43c07110109411803420b6030b58009515070300e505010341801085031130303039000403c195070070443d16100342d4200031507400c50003403000d100f46e0380d5050051300c4e00400c0d540d50403481c00300e405004400680c00c1541e20380c20f00c20b80032010b80c1c40c0c00c00e040d9801c5001440c04000e40000b0030192001d80001202e102503220050f4900d00301d00102c0f00940705601c1003040c40214003070b90040c1c18503a0040c0d1319169990f4006000d004540c415011440c0d12100084d981e03000c2035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 789173776 1250 789172526 789172529
    0x180f0b014e050607030c0e0109050904110604030f0503040302041112061002030d2a03060501091211060304030c030207050405010b070f080c0109080d0f050411061c110904110c0a0813 80
    0x841d88a07044c6500040c0141c8000d84e6144c000500c0c0b50040c1205622a00001c070441340e0241514100303032100c1d1900005501c6a04203540c010740304100000010390b4411b800b9802e42c0c0550083c2d51614194030422082d185132602010041c50140082845e1804000c0b42c0e0f034121408031840c030b140c107002d00000e03411402264080e51055180a0700c0001d032103240756100c0c0d1541081000c0c29004a1680000d40c1102d0480c0107460000e00c0c031000502601c0e07081070359410a076008500d030400b114469000601507600440b805c40009804204060404d50108039250192101302d5040c40158185002e442c0b00303012f10301014060308601c00d0008188003401c011594030000e114000e1100c400b03542800f100e00e81c0b0806540c65458603015205002205c02d104076030040394885181012900b01000304005070300f01c00981d4a14203e80c9075240c2c0b07100740c503200328a004469881c4c81c58a8103407050030001181e814001240c4032240400c0401e105650214001104c40d0f8050b501d03517107810000c2c110300820040c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 789175026 1250 789173776 789173783
    0x7020109060222080d170702101e0e060f06130e071e0e10180e0115080c1203030f13050f030301031403090109030204180f0b014e 57
    0x9903d400703402d480e6180744155140b010260752403a40e1390503a140c0d13031084c04944400080d1103280c4805040d00140340c2d160072180740e10444a896070400c00c8682120008940b900202d007041ca80300303411020038090304040720b00040c0500194640300c1640b8511100c003c2c0030f80c0c41103050008182d4200d07200d5100750310710705a41080365035041e2034640c180708408084181034410504003000152459010b004075100f08007818040e0700081c542422a907200c603500c0030700d81545e52203410030151030307109214040d611501400c1e900c0c0a04d10b002081c0341400040c1c0d850501840b240050480e0246000044a8009003240400481913607410308600c00d8982c280d100034a10300600e20011b00c180800406503069a000b0814090403c62500310a503503441001040360200d2000d1404001500c0c007a8840703406010540c001c000c22070051b03a141c40244680c00022104800c03484d0061029401d03103500d0254403940000103e40c207400ea1041003070700f842c10368003540001e106406004c000c0360304940b00c0c05c0c15590 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 789176276 1250 789175026 789175031
    0x122d1401030506010302090c0a021903031e0b0f0307030807020f030c0a08030a0e1c230109050a060e06010f14040f050408090909031c050a0b031510050d020f090702010906 75
    0x840386060b90321008284410781c07042c4002c802048000c520082140d0300720649400a03c0c40a0509a4000d4454158501074090594603001d0000c0c1603c400071107184d0503030070500068100c00810400c800b03d006000502e002e540105020706c0002c052a0868001c160103c0d01c401d020301740745c4002454588078680c0d89400c144014000110f8100c00406844400d0b11615085034049080042c007500e003862060480c104001c030683c910119020ba00b001034519504141c10030003c085952103402d440c0d881000302c0350313540010900703c2403142900c030b1103403550400c0010700125454001d4501c0025554014850300618244004040f907503294440301d04038948060034021440c007801d004801c3c0e002100524000c030031030400150080004400c56035035a01d90001c1c5e054045414442c2c80082c1402416402550b5a5841c0d0f154546d50420a454400041d002e00d42d04500d0405080302c12954039522190044420341300c0c0c00016640d2482800c1410380903540540a640d40860172405010f9070b440c060302151 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 789177526 1250 789176276 789176279
    0x72d05030405240403110a0c0e10080d180906061e02031309290105030a021e0409060f0e090703030507020117090f0c09190b010c08030f07122d1401 65
    0x11034100c3d90034840c60182c0c0b82c054285c80150012030719031a0400b00207003041c411322400e20680691981140e00300343c040e0fa132034100c03035100d000051400b0b50380d025880115202c01c64031800c0e0b900003641e18014000c00082807095a00c0c0c6003000d010446600440d5894080c200f030f051169038400c00640342a114a076011611403642c034003035200100f45903401020549466800c1103183c2986d140c207100b2100040e90b80c0e80c9959038802c0a031009400440c0074213102e4040d1a4840404500003000d00080c200000f00001c0300307450700c11300c240000c6a56010341802c1240e001000149040420740b18126509030501070782d90005480122491424100348620202e00348080c420000d0001a20110480c3c40d01e003110a031080c55010415030b200100c035041c0307034890002c810000c0102203810034840c44206062543e0381c5c411030350714000650403c4800c0d03d8070320106000c02140d2513102c15211f4049150b8181002040c41140c00c000029681003000601b484020034212110980e41d401112a44800c0048210340d5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 789178776 1250 789177526 789177583
    0x3070c02010f030c0c170c060408250c03061509150302040b0f0a05060f0f0c0a26120601050f040303050c0c09130303092108072d05030405 61
    0x405800a050303001840112100c42c0c1c03580030f84030f542c2003a8016101d0111644040da01c081c0511800200042d1780c10040c054602c04460400001e03006502c0303a984651100750501008549801e1390366908851101c55800d400030030308001d107010640303810040101d18008003840c101c50140040c0e01171822207140c844200f0110341d543e208901136a10841d401d00029040d50100a1815400410320340d1000d9050820400707840c0200082030840d1107040c040e42001c001c0301c016a45500034082c166116003180a00d40d003080443c3e0400a82a000e41c0592242d02c00f000c58005902c0c0100b01c444212400f1500103d501c0d42c2c0034000307880818400c0d0880583c2c5030703268540104141c1011556100c00c4c0706a01030195076103444600c5d6480307581ea152840e000c02909482c120080c003c070400685103c1002c8406440120b42240100e00c09411500c48070502d040030007004000f05910f003000e4442a00e440d0340040c400443c2c01001c0c0c0224100c2c6030040c1caa46443c1001410140c580c801c060030f40c042001d140070207 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 789180026 1250 789178776 789178787
    0x3050d021602220e0706142d19090b090f0a080322050f060a0f0507020604091e1512031e03050f01060e0d030302031e090c1207051f140307 61
    0x904075040e01c18000c03061241904ca5403480980109000b00d540e944401a1000d44040600320030101481103030403c0300c0c2401540002880301040d0f07401580e0000324420f0108100d40c2440305c4000c1031628860369441c000350700144d400303000c0c40f26124040495038840c80ba603400ea420341c054400d41e0150b9550302c500c4e80b401c410f40001103c04242601c8000e1b0000781e10310705070410f000e00d401c025288a103000b130b4100c0c0880e00d040c240c2d15818248071080c000c140c0541c6400010b0030140903050400104101d805282c40020084901ca11301c42e9400c15800d040c0f08440d54082c4401c840b0b20380d6980c0103540d41c606d802c0c0c680420404595025001400c04245030700d80c190000c41c050700c0303d200350403420790301da1204030341c2c03403054080701c60700010000341d50f2000903c40e81c01181d1140b01c100400c40c0b0f01704110b010681c1c0c00d000317a03084e04c003503406441e6400e02032400125008080200310014036900b454080843e6401d002220a501110954a100840e280c001c005100070034500e900080e40d0391611407000b406 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 789181276 1250 789180026 789180079
    0xa020c0a141f0911011809051f120c140102030d0e0309120d0903080a051b060a0c0c050a060c0e09040309081e0c0d241a06040303050d021602 62
    0x240c241250002c004001c00c0d81c8501d1400355005101c00c5075890121005441c0700211686d4503a5035480b80070005a401110b202d05402402c8428021540e450342800f0780d091443c903038001c104a00c00604403180041d0114050800701c1d0f01c150034130158000600010703415400741c40b05402d445404c0151112440601100409120304100d0708140301d00c0401103826a165000344084001c074007000e0042c00840c4044c009025039090514005241000b01c426440041c204103602006980c00070040c000c07026994007a50a04050510b00040c1c050b0706600c4081c1d407441140c0c0c000d0700d01582e40018200040c882e2500220308140503020486078106032400a1401d4800c0c800c113160760041d03440b100c0e50800c4406010180005800050150400e50700c200070f000c1200650449010560340031842c8444c000d1490114404101c54001518041c4820301c070b05070460f42c004052140700204000d00000b5040001d840840c0402d080044e129405a219180d074a610380c240a940100d060300003841d0340b1400f400120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 789182526 1250 789181276 789181303
    0xf061e0408060108010b060d05090703020d030c030e0102011a1332010501050a0c140f0f0115290711090a050415050106090512160605070302070803070b0a020c0a14 72
    0x100c1984e6241c107824200d03103000403420f91002c1c04014407012035000e0740241c0c0d000203680c016103202c65500e5002035811514480c08071301048043e00c040050541058543e0082a420300083c420580d00580c062500040d05800318403810000c10850180903081d8012a5070000304070407000d40f030f41c501c0a21013100c04000903103003d500c1380c0f20011405520607000c0d40c40d1441182c0f41c0d0003070015a40c1d100c0c102c05c1c3e04034146029610a0000526070800c00308003002801896100001d403500d00c01589000303402d025000f44500c160500f0b000310740c42c0300c45803030380d1441d07074200d46099181c80041ca00400300d6175900d0300940d4011f42d584148013407248254040e60045219001821310740081900d03c1003a1402445200042342d0302c40300400550810a00f502c2d4a180d004007510311022802c2d070752900d101116002030f00016404140308040540400981c80500702400007503042c1000b681e204a0322980c01020506100e4020428680060040290700705040c0c0c84210440071001003040590b80d074002071f0405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 789183776 1250 789182526 789182533
    0x70b0c0609010b0a0306050c09030a03030209040606051222080c100c030b0907052b05070f05031605070f062306220b0a1e030510020c0a020f061e0408 66
    0x40600c1c1052150301c00c11807015060088151668883e20000d050041c40012400e01c00c00a00c0b201d0f940074003241c0025407080d180161184140e00a03c011211160030100602100f0000060b200982403007a0341d00c80c5014084540c1c0301c4070bc24a24504841c102c40c018410000429881c500000200d584800030180e028200500c040c81c1200b10203881c641c0703c107a5041460100440c90841c4079900400701c1001081c003c10812040802c0c07110040754800380c16030019915030a000d49907a01610710b65403c005880d003039085082c42c14521515119106000c2c050000003c1d0300e0040020782c030b074a45040b0b6001f4600b00015820303100300030300c0d034500144000d181c84a03000c0019501e1600701d00d101c6000d50008421110242003103404402006a140c01651006110200160b180292003241940501c42000c85805d2441c6241680c9452001105440310701d0041c084e0004134000003800301c8007184c048038009218034580c00807601e54460401d01d221840103840003c0c910790103403c010801ca804100c100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 789185026 1250 789183776 789183781
    0x100305070e060a05071106090d050604060b120303071809090503030703050106050c0a081c0504230606090c03130506011707050f03030913060504060e07030513080901050c010e070b0c06 81
    0x3006010321880303500c8400b08005203e174102003114030902d04090100608110715056501002a84d00c0700f0103030b4221401c4e03104000300802c2106d18013554103c140250b440103020000720007400d1f10390000030805420410075507070041450701903528a100038020b001d000c000e018141d080c02d644075030088400c000403038245000081c8151090302294900070a03030010300340f044215501d034200d55204c1112024140c0013101ca4903110321040c850240207510452802030005918807114285107550384541c001c81d0040c900f082615107900005690003c031a40341c807170b540c0d612100028480c00e40003e020306a031090f10008140714508502d60b402c040c405508a6070016a100300b0040c0c0b4100c3d581e04260160010700c80d18150307040c00d0f06035411801601c0b00100d0360b1503c6802003022101030354412402000b540082c41501a09031048640140c00f0346803034499016039031111462849449642c0c0e041241c005180704181c40c0030350010017042442c00c280c1e54900d035990b00313120750341d000701c8400122405540301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 789186276 1250 789185026 789185029
    0x211e09012924041a1308010c09140a18090c060306080c0301050c040501051e070809010e09040210120608150105010206010b12060f0609180f0901060513020a02010b100305070e 77
    0x81100c19510002c068982070500030320300c0f0042c0521400100c0c9400038400e08001c00b403400c0e0400068109900001003030034261100921100c041ea2110031546c405071090b844d40d45074400070005507410760703041040c003502c039500110040245680203440409091004106140c1c10f80000c4200d400707030001c85074111000b40805080783d906803000c4c00c051300c003040704001c1c3c0d502450103405071030503504a04802024690b00c8609a03840503904440950001440c0a099a00491000c41145042e034003040c4924196001c0b0b030a00d0402910340e01802803c43d064bd010751a0350f00144058034040c002e4800704655400c02c05d204101c00c0c01018058020342e400401e0009032001070700c4010004064055842d00c0d100207001c3c5151811700841c3e0083c10403c591410744c0c030740c500902005558202c0c2d000041c03a00e000d2071000410301620390b02459051040c20860b07680d40d5504426001c03801c2e0f10069882d118008240e005003600490305802800c0780d04c24940381c507010703030047d44207084603144c03031085102c071a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 789187526 1250 789186276 789186319
    0x12071a0a0b10110a11150a0e090115022a060c0f0c03030316080c0f040608090709110703080a09021c060b03120a050c0f0102030c211e090129 62
    0x1c2a82502d44c802c240c100003048022844000308413024040c0780c841d00000904520030b500003a026004079040011030365603400e008007200c1c014429041c0404c002401c900340251140c8100f0070744418065141c00c031281d541002ca925601591004021342d07911020380c094a915492401d0b91803043d40900a400a0107060201c2140d20039940c0c03a81444207000e2b01c140a41d403040000e0403900c41c1c00018040081c1d84849400200068621340e02ca07441c20307250009600303145c281d20f41c0103280c04e5410910240d00c036920300d50550f40c040d035160410035415034440c0ca8401c01054881c034003039880178141640c2e0703180e52400d0b240c0300320160242e50b0500120304440f0a0656545240c0e0401102403020001000014440c0c400b40000c0080d40d0f00703075240c035000e480c200c5007642c0041c2c0e440030f1280000030343d4820ba07450344440e48002d250001500c59031840c4c03400004002e05d0841c9000f8104020744000034221200a60000d00d60300300c080314441c4d12042e00411805c003501000010303401038800c0128403007801c4020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 789188776 1250 789187526 789187547
    0x201080f04080a051b0102070317060d030e061c090b04140d022a04110306030d11031902030408010f05040b13020d030e0a0314030717030912071a0a0b10 67
    0x6542c0b070580244000c9484d13500901c601a09070280c86200d42d01148203000600c401802a0744000c02c43c0303c045217050740c2143c003030720b02c03071180c0300000d107a4000070342003241030524410440e0700340d0700c604010301e0150281070b00f500020030091078100d50504000d0309429480c0194081c0101d0b03840c0c182c50380b0145548042c42691240560710080c13403000c0c0ba900602c0583c0c0c1d1210742a004440c40550880403406644a4003500c4040f032078088104410303070604002e044000700d82032800c49500d182039007910b600c9110b48414581400d0f1040ca43d014454001c0040b1401030030100001c00c21801e00705487d0000705001e6400f03c039a0104032001c1031454801c05000d00e01c09400030704101035680103a13810340d91000d130181e005030402c00d1100e0000100e4038040c000b103030415500e0b016640d920164a010701c0007805440c4003d039184400d1090050703c0c07a0009a910200e0441c1c20083d40e01c112504052040392000c81c02284142c0d0f4a0003041080c0300c00d6042401c18500a907500d50b001d104440e01031321004140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 789190026 1250 789188776 789188783
    0x90218012d0c0501020a0e01022503020d0314180f0f010f110f0304080f0d080903040b0f04150f14091302070204060509040c08060108070e012616030201080f04 70
    0x1400200551214810700000d4684001d003800403041c0703a25620305080e6041503682c800030501e4150706128558040c03104041d02c508064031044400d0072800c041c601d03840b03d8003019004031400816a03080500403c031100d0307150351042c206c90711004040c01045646c4031100065005218103172411a45082c1401c81008480058440c01e0032142c00080486100a504521420350f10036685250711132801032004201520320313107010b803041403d540c030041c1c074010315114580200305484040100c0d10300003000f510165900c2c4414169a0014221004514040d51b04468065000d481c1150700d01600708800040e40302a5403951840c8001e070881400c44c1e40280c10400c2d811825010040b0340700c400726801000c08510084c40003c201b5100c80105512500c21101100e0b400020386003804654410494a401450204010318201c0d00b840302030249110103101e40021388034064817001000041c5c040d03054030f03080203800b12110481c2400946030400a00d01c01a804503200e070380415440d0000c400c2c840d115070381 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 789191276 1250 789190026 789190067
    0x9100f0608010308030604090c0f06090f0803121f0302040c0c0b070906020c0d060906111b01110f07110d03051b0708030714071d1602060f180304050a09021801 70
    0x106c1d1b40512000e03009104048075404c13910880860075840d410f080401a00c040e03614100c200d42060714201c0081001d4101c0741c610b9200380407916205160341c46603644800b260340f295282c030342c000048200d4507502c1e410095001e410589552040d41d0b10558800045001d440c03080c3c100d884450060301d02d00c2090048000603003202c0000361460510a01c00071450f8451040050603495640fa090200c8440e61901420b1101c0003614846102a980c500100c80a0b10002000040c61140c50103900d80710310300d003090032000081451002e2040b55140d05d11a0b01c0003400600c0481d006150041091748031440c0750285261130814611300260000303440702a15400c1c0029450240651500010103000001c03199052045601c08a640000402103070f002c00c2c01c1034485403060510740317111102c1c60304991018045520150801503107510344640150000c1c034200c1c00003844889901424214400c98002541102c90700303400003016400d0364001c03d40468280022651280d6500044691000c000083c039035110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 789192526 1250 789191276 789191281
    0x81c0503130b071809020c120a0c060504150e01051009090c0e180a05030913110313170a091410020a24090317010f05031906020909100f060801030803 66
    0xc0414a849810460500f044c2c80001c030140070039924803055401ca03c41203600440d9461081d42c0800c040811001040328407130404c0e0308007800421640b0300e514050103241d203900108080c02507a407132004845003a01c10611605040c5005903000c1e01e010b40b240b18081c0040d03080064006407510511b0b01c0b1035030140601110901e03050186400e100e02800c030310540d003501c91610741c81d52800c015a0340d03018441d6010390740b070305c002c04108105403101d21049160301e030810305032240f075009d6001100da00c4114401c600141c6011070809114411101c882e0301c44880c07000034041d07030445c0c00c1500c07041120001001e200000305400c007880700c0e9000884968001d60701c06a40c0742c000600c1400120f442c940c25101c140401c800c004810320548008034020307070120713100c4800300f41300c05082c5080303d004d011000211039181d407920300825940c100075001c4140f6044003428040810537560112109400c0c020903016441c188200c4840590715030344039106c0c40c1c8180c84e0f40056100e01a024050480e50400511030559 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 789193776 1250 789192526 789192533
    0x10c03030207021206070f2304050409030908030a050c010501050f03120705190606090b010216090c09050603042405040507090b01022103061513270501081c050313 72
    0x250410035040744c0c40384001c0c0805107407070700401040e40304040710303a6003010004c501c003130152403032122200025803008240d03480c0203208025400c503000c445c0140d40024160400c0e050840c3c420142d50480c400c14080040c0c441e1620350b0000c05465204000ca00030482a41d0340c1c010080062007890030a50181c100c0031700348400030000030141160300d015800f84d0f019148400c100407560b81005008955107a80c40e402072204420034460b1603030303000342800141001c4207440c46004081c0d00c14807030b40c04400c1e15607400781c10b121b2050500900600e000b405aa80724200352074000450040e000d000800c94803142400780102d030160040c1400341da0002c01501c029406e061030003000e07180403003080f07040d0303c40da035051000300c84c810718003000240c507902c011f68a90400c00200300100652200c501204807041c40140544454102d4540480d917500300c0b9000d608810080e41c95294014942003c4111318040c0000784101010483d2400d602880744126a0995400d50030b803070a0200340c50701d0b180440c641e800711001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 789195026 1250 789193776 789193781
    0x60f08060f040311120a1206050d0b0402060d060512030406140f09060d06031a040501060501020c1f140403060b01030c050705150423070f060c0b0c07080708070b06130209010c0303 79
    0x5401542c8192540000174080341100c81d4811a500c1c0300240c00008088007052291103204007610301100c0b02841511103403078a004c10900a0b00180c4568000548451000c105500400052001902080131107a50017092501d80d0801e10801c8081030b988100e0301d070711481d404100c4055500309a002400c15510706c084c08500d030420b0550441d89940c40364040b02144010b0b000050942e40040d081d40300386490b10b011400d4031429032199055600c00b4251120550312507080d9002885250180c21004003148403c0720079104100c0c1111165a000801000740042034020a01034075080e20140f01c0e40841070740445e268030070904081c000341c019601200c0780003005428150041d0207040c2007003240300c001921b901c041c0030070031540245501003030b002c00c00440f0381c1c103411009005904050300001c500380c80d83c0442200050020000c5040040c94508000001c42910f1815804c00f49080d11091246000d000c11201620014442d07030b1894482120321405008032010450103035144443d00c1c000e694160003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 789196276 1250 789195026 789195047
    0x303030b040f060b0315030d0f0305220f0605101202010507050109080d140a0e07030201082e0806060301060513090f06050a020301032009042310060f08060f0403 71
    0x5000e82c0b42c0050103100501402620094089036032426a00e041904054204030121a0710307600075002044084040c1e81c00407140040e0f0245401c4c00304240c0c1d903030005004021201307011040010b1620a807203041c802e40d03030405d0740b84502c50b07031003005282c4400c00221032041e00361240400000e100140c1100551051011323280c0349105a002044000e0290358056268000700348441e166580c60155039501c0040c0f003045600404030304020007070324940070182e0392521724500020f070501c02c0c104081103801c8002c18800c1d81c0745840a00c44942003c18242051440b881c605c110011841410f01103a41440c041c46404211100200b00d400344050b20140318001e400140e00641e40440d50030141c1c40400c00030701495100702410140140e6070340c1107203480348d4600074082c120724008038240000001612640d000c190020741041c2e002c01140000003102801c00343e02d0082001c1800780c10101c4800c1d14598000c00c0907600101441c144090b12400e011365182400c0750501c03020500b890110b0302090281440300c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 789197526 1250 789196276 789196279
    0x8010503030306010c081620010e060712020a1a100501110a11030102070213150f0f120f0813060908120d091a070c03030f0b06070210090f17010c0206060a0303030b 72
    0xb42040c8010f04c59001c1408816003c0e41c0b2130300440a048030301c50407982680110242400c04080c0e0b04000404032f8001e01a643c1d0080035180048030b0412494020407000d003043d81c1c003c401c02d141d0034151400844c2c162042d144d0180703080102001240541c054103121800025007c0101201007142e2111441c01c108201880e801d550b08111300005a00ea025102c0c0c1d0580080b080403c02900341191512100410b51041a00200c0707c0c0d0140203298a8002c01c000302d0b090f011002840240c11f0814503000728160368010440000000c00c516100c0022822008544140c0c80b0341380e0703580d641e01c0200d803201030840302c0d020840d00400c8040e4150296506c0b22600c6405506240c0d00c0b000000b40803844010183c40180100d04030507901004c0540c075002d5602c00581c400d03020f00c900448140404c0150040b800024410394102d0f264001c11485900d0440c01402a43d200d12103143c0d0750300307007542001200e13541d1070381550130300103080d00700da00004426001d040060b104003400ba25648080700280380b1010011b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 789198776 1250 789197526 789197543
    0x181a030a030806150d0618050405030703120204090e0a060b060307230403050f06190204030b010e04141c020609070e190e061503210904020c0f03072108010503030306010c 75
    0x1102014134000505070400c1050400104c290401c0c445070f07250952403003500816410302c0d040000041000c02550f41690385810003121610407003009402078001d540180a0361742c07514150b480b11020006030032a0352030081e5420000c0d5a804010301003140320171140800030501907800b03040c5a0326403850603461500000209801d15840360385140c1851a0307030040c0c04040c2e001c0743c18800c10b40d0305500c0070308100883c2034045240c40d245546e0310540e07200510444101500c1c2800150920260400395800d020b0341030291025080302e986032030704070704400200100604c60240042d4140400003280340646900d07420940d0300ea40c42d41c2d04038812010060700c001c2200e4407950380c001e01c0d440401c80c0a000d041250442d003256a0420245032610440e0b030380018401424080d840e0220344080304450080130165805640c5154034500d080c6001d061106402080c1300004215041c84420081c0c0c4c0b190303038281c0d4010128100a030a044500710000e0040a50540003000401e102c0c3d801640f40720001d901c6060708 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 789200026 1250 789198776 789198799
    0x20102070302090c120108210901050c0106061d0109120602160c1418071d0103090f08030f01080312010506130503150603010509030c031c06050a181a030a030806 71
    0x214412000503644080704c180c003c580f50005000010740640035280c2c090050001d4806081c03000d0102240d5214081c2c5910005042c010b1b0364421401ca0f0b01c580c25080091181d55910400240907802c0341300021140f0190700c3e0301c18442e6110300f141c0310403a401440b05c680c01c403a60b81c81307010085d031146108400c03e00c440f20256000480500d82000149184058403915203030720000d001c41904003050340c107210300901c0200402c1513000481c140c0c4480d001c499500480c42d143e401a4002c00d03440c000604907130f01400a0b40208612800107511075801907401c6503003641d840500c40c1d503900400c200b584003c8a802d006000a0900070301800040da254080300c0d140d21b55620210381080c10400d082504c0106002c100700c4681824000d054200a18100079880e01043c00c1d01c09480c3c1c01064408030414055000b50400300d001030300714801410006000810303496440100100c41c14191070507000c454100708a03488030201d1810212001300028002d001d821600c0d550403907224030010308803980480b00e0b400c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 789201276 1250 789200026 789200029
    0x5030f0c0c2106010504020a0804201806040b0f0102030301091a09090109031706031e0f010c02071701050c0d0f0618020c1501050307061409031b0f010c0c12020102070302 75
    0x710000910345141034140e0b80840815282000300507007180303005500400102c41481e602030b03c1c0a0b40950800305610002c459a10036014540d00301200e00d0b48000d140e1800c0601c9852015041c0c000c0e0421201000301c94001400c0c00700d510405a40380340541c03c240010030500c0420b8200809068440c80c412040c02c0d540350003d52003110540365041269503c09841c4101600107007090b21481820b100c0307442601d0250000307551590f00301171818484c0c10040c0c0e03508021304100040001c808810000f8000713452251402036503403180b803103041041c6c01c0400100c0e0414070180f01d810b02610f0944078480ca442c00c0c0903042c402501e048900c11149a41d1110002001032503a4100b1b10740644010001d0b907210701c00c40d02c0310300e06150005c18030b5038140399038010442594000344e2401160114100190b540308680d202c0e52450194003005c503054010301c400c2030038034244e60005003850602141c490302e901c0c0c596801110f4100c03103003c0040c4200e0310010140320000b43e40000529507481403048a140c292650f0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 789202526 1250 789201276 789201289
    0xb070b130602040b0415110706051c0204081f0e030a030b130501030506150a5109140918010e0102280f021504060e1906110705030f0c0c 60
    0x180032410304900402d082c0014080d035402146d10300799078071b00088040b0b803003546a83c0710301c101e1060100f80800004d0b000351402c1140e00102407040c0e0b04800f151501d5a50b51030f0b580303600708200348812a8000c4007100c0c01c08001e91003410104012035000718100580960300b85e00412548a545034000022960304104401078014075010710720410160951307042008031102c042015100052050b52204418440c940c0e18811090311200d408401c440905440500400c80521080003081c100400840c00303a08820200c2c28250382004030b42d203240e1480d07038920500200f0408004811740c898031410224004c21100c5020000781c000074030000940701c00c0810041e0890348204004404c1d5079940f005240717080c6112500d0011a6418180b2107100841600001d46a92042081c1c0c804800740c10003040510120ba880481400d40180031100c02c017081012002d02d00c02f0f0000111481410844019403210b071031010741d81c2c0568024000c505000701c0d4190a41d540e001424491824401d2001840c00d641d2000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 789203776 1250 789202526 789202529
    0xc030a0b0d0209150901050312120408040e0c09030c1c032706020109020406060503100e0405120705100608071202010809030c1c020c04180b040c0302090a23010b070b13060204 77
    0x4c04044081d192060306020b11810141e000364842c5d0030a40d040051420001e04841d00840c2d0b43c050101c6503550303860184120300a036004002030544107410011482000c000420a2810440403101003040c040d00f00807440c0c41404020714201c0c08201e8041c002070040c82180d600180d0711002a05d070b07d10499100351001c5240d8070200060f911100d401056003854030030240546824030b0103500e10701d07044400f000020414030039048410503240c006000d00c034050140303400044d0b2100c006a66030919050203540e88a40c0e0401201c07091500c1c80010310300c04000b452400b225910402003088500d20340040d0341000009100d0b07000d0740030820001541801c00e2000b80410100c030700104154040350391000341742009100107903014501c2c0c00c0d1106188e01c1ca28090112596201d071040f1107a6a4030326041c291800558002504520a83c0a11100117410341201c0081d100240900080c5e40c50104440310400c404e11036046001c404102090100d241d0f41d00c0706d46d0012940b4012000400990341301000c03a07029 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 789205026 1250 789203776 789203791
    0x1b0d140312131a1902160c05102019080d050f01082a0a24020d09140d020316080f01021c0b010908060c0307030b010507051b01030906110702180c030a0b0d0209 70
    0x40c2941c06e4100005549401c0c007604050f035410014610000300074000700010050402100b12500d00100e04106c100090400c40400fa0380c6844400480c0c0b43c69907103a0408a0320307184880c2410009041ca000c08484141242d61500042604202100700b8034550b4610a100081c05051a402c8100540310720f101c06c1e00603e40c5589088153300035610418043c3c0000b0001c804541255801425041d403180d24001590134500d11000e11020311b8002030a900d11030030000350103008280e144440440d100f0440f200f00c80041096418002660030b0711802c0f445060340d603804584140381843c00385070386540214410441810500302090b2180350f07251401000301c0f40501e584000000304038a0540c54003c12180c0350081c02d00d141803503d2552a40e4070b0f8071014001940305031952007960780580c4039800c041c40140d045442041101c540d20340501043d030113410180c1c02540070b8040354000030b0b903052149104011040340d450550f1500d42142010b00080300300c03103500c0405126424096030310b04200d240180103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 789206276 1250 789205026 789205057
    0x30f02010e090f070e04090b0907030c120c0e06120307082206050d051b0d060807050108060904080901030623190501021b0d140312131a1902 62
    0x452000410110160554600810201c018072040424180310140c0040290909554901e0312102140040c15440350260004010b0014402481804140034003500d0185401601d895200d02a20035100c045a10040c5800f0040c4410021aa141550143c002c50010172080322020000455899900503a10aa42c1c00a0006800c800482005407064094080304181c29616107046409001800384441100c6c400340c0703c20001761042a00b40d00741032800942140240c907082440d100500030140381c09032103958484c070200800c0a44c0079221040c030a02e002401c4e5001c90340d0359901c440990300b252411a041c19107070607002c1100f101001c03504401e18800218020b40003904c500300300c03040380c0c10303c2c88092703803a1502410301450343c0c0402d04c0340b48010104401c41001660b10081a0866000000130f07004618a021b40c010081001c001820104040d003441509a2161072503240c0e840754654005240c5070995400060030180b14101d113511114030680f41140c1c890500e80d4105980c41811030000050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 789207526 1250 789206276 789206303
    0xb0403020312090c090115020a020901060c03120e120c010605221424010908121b07180b040207060e0f01061a031f090204031b050d0c060f050c0703 65
    0x411242198007030700f00c01c000d04040e03180502003102200117004940161158101000d440c0703008205490186a004d0004859580d4031500140044203c860480009280001181d1003004030b002c0c0040c0f2200307003809000da4284000b8044070715841000303078502c55501c0e03003030003e80307940c40c01c2858141c002200303541c06055064698107411105890bd8090310607540c0c1d410b0020006d20030216038403000310740079031088420b11500180d52807002d69215006a100d01e003e00700280b81c803000900043c11070740e5a0002440c40c0d0080f81383e1a25240d008280c440c03000c0c214505c00d0704c09260041008e03207601030801444d0007004e440d540140c40380b0b00707402000707944915950f040c50b030024400c260052807600f190091541e0300100f042c9040c03002600d001504010101d41e11005503a0f41a400010200081c0440d641daa59261190701e042101e51012541c1c688003000203043d00749100030030b4200741c0c0240c40002c00c83c2000004d590300c51301d0b40c40c00c2c41002000c1c41b500c43e40a03010000840950300a210701030450303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 789208633 1107 789207526 789207547
    0x1e090209040612060b030d2109150c09240516110612010e06011106190e0d03051009110a080402040f050411010801230d06090b04030203 60
    0x41040c4180f0f1004000060340981808001075056034410200f082040c0d88400802c0d001c0b035582d020119000d00c52002035407040c0107180c817900d8200365007020340403000111042d4280c0c40740460604241800000300c0b5900081a044e03e6800d420141d1054180c020524003d24501500d1160000a01700402002c00c07008680070304050550307a240d00c50b888d08094a00828420051500d41c00400f090741035102e180030038401001c0d00014501a03c03003042c0e07030700c61115603490f07801e48960342c0311101405c82e4148045403456103203075070215884c200921100800c001c0c82e4450f402d800e01c0c00b124900000142c0c02520411405801e00c404507603618000b00b03014240301211146210305c1c0904010410506040505035503e0030381c0c034007960341e0722040c1090807141c18440c950f4030405051120b91f020310b4030441401586101c4d6102050000041c0e0380c80c1e0362481c0980e01100940c20204000c03d08 = true := by decide +kernel

theorem cover : BRFrame.Cov 789028776 789208633 := by
  have h0 := BRFrame.cov_init 789028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 789028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 789028776 ≤ n) (h2 : n < 789208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
