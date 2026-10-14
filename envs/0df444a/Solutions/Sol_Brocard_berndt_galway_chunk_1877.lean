-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1877
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:00:08.973637+00:00
-- url     : https://prove2.me/submissions/4c02e5e1-d4a0-4af9-9b70-298596ae3b7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 337410071 ≤ n < 337589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 337411321 1250 337410071 337410077
    0x1005090a1209051005040815040314030702070f030b040303050f010b04030803040f0804080610080105040213051807062007030f030f090f03210c02010f050d060807120c090b03030901 80
    0x4007600810031203030494030b5000301c0d40024003091000c841940c004024002c80305442e06868251580c1521202d44a809031030140c00907041140d0215050400d000554112503c0c3c01102c4409a55590081c08102c8941c0300381c404c80344800400043c99050300910740d11464148101a03998107084500c200c60242d80005003040c1070100c0000e0401c251022103000c41d54100312002c0e1201c0c0e0324184681d80708401c44030800d44101c850070000c0d40620500815005540c000c16840d6915809a001070040500510101503164018000316005000384030000207000d4544d03d00e0221320320260401100819422040301c40c3e408940100701080341400b50b4284141c0c14501031401807242407080f14405002d8022800c0c0c12943c14000007000300c5103000074202d400444508844140e4400c0a0b207260843e84c1d00680441e1403100041003481c0700e40c009025425107600000b5241e92a403401d103250603041d400043c805d1010300c08003814011110003200082864000510031204030710b002c20340700d001b60030350503040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 337412571 1250 337411321 337411343
    0x4020a061202090402030a060f0f0315052706090f1606030507050705012f0c0718140412080912090f041e0501051207050303160501020405030706050c1005090a 70
    0x7540300d058040303454880b00240155228202100300800a2445129454450202084c00686881da801e00b42d8100c9030481004400b03050484841400b5100051988202482500c3c1702c49030346103820100ca5030359031001c00030700580c40c003164035901d0300d450514040c0d81c40c0c7c481a03c1d4101c4024403141ca5069440a21300850240c50343e034410340d0310b4052018018415400d11041c0365510035904220710700319107450003013140a11013860b03c2000384250f2010090903000b000d0240100d41ca001086504210a480005400401d0b5856445040c8098604072002c901500007800c8150b07012403c82c3c0c00c8124400503105010644a00071140d03c82c1c484035a01640181c450700c62180d54a43c44400a02d00c0d02980601065400409070001c1c0024041c85129a5100c6500c04a5120010340b00c4140c80d4040c0041d0710b07000900030812840403881d10700b00c909640801c404220f03510280215002071030f05031510360300e400c212320f00e56003442d40d1980c0c8040346500c1d00081214402001445c062519040840507030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 337413821 1250 337412571 337412597
    0xa0b0306040e0a05060108030d0501060305220309170102040e0702031201030f050c0d060209040501080111160c210302101a0609043b0102090f0105130503011b021504020a06 76
    0x205222a20f030700548503004950000484450101c024056840415410802130b81c0307804003541113070003c0c0c032000c45c140061640380c801402414040b02c41c9900070304046110660302d046031040d030000c0c020744c562165000305040140c007078044851600001c940c0082c505004201c20380782c0031043c051001400402405260f841030000c01e104682c0010b074003502c030a2030b5501c10f040c500080e5001402e03041c0101c1ca80400010088011f00c514082e03802e00f011018a4012290020604904400025112107080c4200022281e00c508941c40d001c1260710342051041d11242000307424081c4005942e003000d03042410310100f505010382406c211800480c0c000b40c450560601041c001c080f803444600025040710318582280d0110b07010b0800030030300300c00c21005c8115060304c458280e014000045800c03480c42180d0b141290300520107482c0300e841000b08805071513542c0c4002401d440b5402c0020903458070000c1d18a2301d850703061004040a446080d08014641031a038007280402c9001d00c41c0b582006115003080c0c4d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 337415071 1250 337413821 337413823
    0x507080408030c0d0c080603061e0c0903070f0801060e0f0408091c0b0108011b2c190e07031109030607050c03040806100807060809031801030609090605010f050a0b0306040e 76
    0x4003d40e002c110100710ba200d1250700a003203204140e1f10310744280722700b00016003042c043c1c8042070051460340b0351089040c0c590050301944c50b000301c031505916002d80d02020400b980e06c200c01d180104032a80c004145180b903c0300d910361303841c0c1c09014104451380b00701c03c0001040a00003104c6480105890340c200ca100c01100c4046500000200245130fa14010000a40500c054103c0c605100315442d55036500c1a00e2807050383c4000d41404505107400d140d400b51070b0390107040320084a14480150000c072001003a054110542070654100451260189090008499161081d801001030304848a440c080e854400281c1c0c88100500c1e0300104840012042d501030001c0c029130740101420411180e1130b05000a1032031400100780600c0c00035219010b40040e20502c140f0400303000d020203c000d946044801448440c1c1214070801003414181c4503180001d046081d8450ba0b0b4415018960001d03655040c0f8021000985440c0c1c002e521a2400e1081803001d01e001c5004c076500500103e0740010040c0b01640c2c07003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 337416321 1250 337415071 337415077
    0x10807030c06260f04030306080307030e090402031903210b0d02091008070b04090b0a150806010c0c0602030306040b010e28050616050d03060e06130e030a0207030c090507080408030c 80
    0x10143d42c40e1009000e6043c2c011400e00e030140c0d01c40e8a05000b083c1c0c85008040d928014a0000f60010301d0b240300203002802c081031032980060014081c0e842c841000b00740c040580007401b2003240020304d40704120300c994000e00a0180015565601400100f20b070f000055420081144060322490000d00492000c16141000c1402090a00701b40c40c80d25551394400c080d50382040c840c020106040c40e0400c005840d064115405440349165041d00201010504071401740d001010903060041008200002ca05090480e0303009050790760007103503685003040620040d104522120f5050000005c98040903542c2c2a0b004040d000c001c0c043d508142d25100640403111004d41d2140c0d80220340000c00050400703040101d10000c2e8061411100c4001082404500b04d42d0b1030b1003002c160020981c0407607000e14000044042407180c1031000b290014800401b90304590080481c440036901800c0c0c1041040302c00c90010300100400c420410051401c11009007603031000a200605c40b40c0d001001034a111801d10503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 337417571 1250 337416321 337416377
    0xb0f1305160e0a05010509010b07140628051603110d0c09031719050f0d0507020d02010c030203090709020a17010e182b030b1804030305010807030c06 66
    0x855800300c1e0352400d005058280303030082001880400d000904031000368042d580c100d60001d850f14030b05030f10703082c142801341d00019000c542c40d07178440000e241030070301c200b14444c007843c0d182ca01c8800d2000040514048030701c0e90000f0112150030441040304c2c0740c0e910030700b00a9028903810003040a65038507a8256103442000e5039200b1141c0b030205000c0030503a002c1e0961098a108125001a004108009280d5400380e40c038094010384044541f6007085110304050001d0b0400020620b082c0302508607148291207040342c00703000503409216000c0c0300d25824000e00070201c405007811461401c00c6005551690b0751800b5601e041c030780000b0b649103558800c0b000c400c80501008041c281c1540c60740d480040141003035900c403008012040c01c14100c840d01241155582c603510004007050a00149003111201101d6003190034140e9940f00c00304c4a4232882506103411051143c0c41c425440d1914024007241c00c113801104c41c40d801032100380001694080c1000680344a030602010311041c1c0070701c081042c004406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 337418821 1250 337417571 337417573
    0xa0c080114060a080a020609060c0a030e191a070f08040801050106030c09060c020f150d09021809030d051510030f0b0915090a0e0610090e030301030b0f1305 69
    0x40001112001984074611503580c0c000300c400d141d11110200200c042d094001c3d0082a0070101d604001031521740001c000340c0304090060303400c05070741c9814039042600b51807055000c11010340ca0102e0038134184171251a104c01200068400c0c0d410004269110081e0301811503100100081d400140b101001c50040f030305034404801a9250b0303ea40e03001c3c3c0179090a00c1060040b1741001101000039009161144c1a01d00f142d45101c003e520540030004d102c074404401c1da400200c144104808105000010800010b4240c0c004c80c450081d03106009443c0000a100b43c140713800d6a082c030807100d0020044580c0e18509a40110305a110048000340100d040d540440d4080c0c550307c100c150403501500038078840003440c9001c000d01e004072404c0c001000011640121800c88030300d031b5110f0b90700e0303d01c00664110b1149072001a28881e804500d0b031070200140c03440082226010400c1204041600482d00c2902c4400b01a60540d451692841c01601d00a0460598111480300054070401c41c3d05c000c20348070350014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 337420071 1250 337418821 337418843
    0x7060606090305060703060612050414030301060e0a05030604050616050d090f2609010c0606030c0b030405071208030c0a0e090106091e030f06051b0d050a0c020f1e0a 73
    0x100c005062104a0310007100c81340614070009040500a103d00000c8034110780b40d20400d204401c080340010000140200c3d0ba05075105840c040a042c104080c50182096851360007040c00d403242004540c900c10b600580c0309900407410040001c002282c1f0540100f501c3c402c1489401300b2803400d49807030051000603203e41e40360040380b40500c51402d84a00001d4090045a031100d01c0c000100b05048004c4250300050020411400307050394410010350b8000c6004800c0012071540381e5681000e40f0712594082c40c41048003000344014004203000c01c2d0010000394071100014070b40e503510300d011381c00010446503900c040401c20700310103800b801c060b84208400802404040d030f115500a00200c04c40c1c050755030807696200c50080001602070a000580f60080f03207591400300355607540405800001c040445e0207105040c1c58403140d00640c0644240b48030380c0c001280c58980440c0740b60803261010300e0441158040d00c8141d22804001c14100c40c0807105200f9144030a04002101e4641451400018108502a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 337421321 1250 337420071 337420079
    0x3040c03050607090905090105040b0c03191a120607080703021b011407120c05160809060d0b010f08060d060515030a20150a030b1f1106070315051302070606 69
    0x441d1640085e62801e0004000c580ca400264a08840c01190010300c400740328030120750381c8400c81000d10b50040c01d1309008500b41c50807400b44403d407100c44030780c9000d40da540c05d944046c0d407810141d51503000d121000105110703c1c8ca954010a1702d8805055030090650002d40704610441a900880034801000e000f070282100f14502c10704124001c807200303400108050038200b0855600d0054074240302581c0d0710766061a00342c0c01c000f02c3da8501190100c03044442040183e034940c5400014100350120580c00282c1d61402c400050954480c14000d9801c10400d03001f082030a039202c1c40702d0100184c110710000340c0d541c1e5035042072141720440c0510950511841101d40204a20316003811085400c001d000c00380640900c040c811442d40340d003884980050b0034050350048038400c4d804810313440700090920040115501e031400c0400d02340440100021180e0841c07510440741041351a40004180c40e08204035041070848030b111110703034000d8034890155035101c210400d480d50155003d05400410400003a560b07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 337422571 1250 337421321 337421327
    0x703120f0605121f0e0c040209040f0507020f0f0601050d0f1106040b041a04061e02070e040605011d0601141c0513050d08060105090d140a050c0a23040203040c03050607 74
    0x80b0980c1060040805004684c00c05040c0c0510031222286a00070030041340d5850821010b90407a0030a580c100b50b441004407082c41d050b010b9180215407940240c94690b05030781c51903092100c90050040745500040041141d901d90704485c0c00400d821004104180c841b5140a0a180740c46070101a032003040480c001c25507071100740c0100115a103503140320128200d814443c10309030103184640b00c0882d0000d401078090322042c002c089030051840c41543c81c280e44940001c03030000030994060f42c0f002e81e94401031180d03c4012124802e003400920b501080741c90320f500000c0c140b0608496190342e105000c0b0f120142401c06440d5401c000755010018015450289070711400021104016980381c40340c0c0903045052400b94490034010303074042e9039080c0740241140904c030003c90078200c2100c40c0d11740784a0340503d62405014020400d4401d80c041c0050f034030907404201e003140c0307207030483c1659160408180501a100034240c1411b903206070380c00760312076585050800d505401d03980081d28500590040201d1164 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 337423821 1250 337422571 337422583
    0x2070b150102070503190611070512030a0605030a12030e0c090405010207110105040f0e041110080726180106030213020a02070f0323030d06030f14030703120f060512 73
    0x400e070b00701c0701180c0d82d610130140c0da4180c0202a02807540318811500100d0050f13000b0003d40b86640340f1091404220350f0350a494000c05031081c0010b00c4000c81800a2283c0760701902e001030000300d00408052003952108008210000700c08400c0c15501c2184941e251401d01c400f0492001c010418500b900d89070038075601035070000c4000ca0700c01c0c58044240171558003d00c02d44080d6800040340411079402c18840c001580c1c800b400a407420464039401c0c164540c1c0d03000302243c5540080e41c48626030300340a41c020f0040d00030740130004181541d185188103070524054400d507018140d80800e014481c5000420340c014a425000a500802c4d8031b4890941240250020701c80380708580e0884408e0f5589005900c1e9400701da0100401003c1201c0c07118180c001031080e01a050b660040690b45800803611030b4030100c0d80550300441f40040514080c20903c11940e402c03072040c4603c40042d502e000341d1564000d20034456512107400d05607986030b120394801c4507540404003616015000b412a450b24000c1181c3c0c8070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 337425071 1250 337423821 337423861
    0x150f0d03260106050d20030c131710021b0601031a010b07121d2706030115050d0807060903120506010c0c15050d050406020a1202031e0a02070b 63
    0x108115550303816020704400e2641266110b60b03400d0309021145000102400c0007161415803000c00380300b07040d00c0d081d81038000c40c0607500745008965245624040c5002e000c1c00340e07005403080c004082c1402515100444d07403081d8005080350040e652040d20804c151801c000389c2c60008144503010010040204207144400c0d14040907888200680c2e841c086980188200d042c021b017003a01070800386454602031110000c0196400890000341000000468500c0f8250800c0340041403000c8041300c440c07840010f810f40c21503800e90081c000c2400d81c4846504205103032080178003c0701d00d08030030010700c1011420354400030360044061000c4940c07414024405007521810400c464540f10110300c056009010f6840d40315408580d2030b20340c619210903100240078070408001404000c1010b403050040078072a0703d101d64821500140c8800181d07000510590f800980041054410414081980c90043c0070341014003100c0701010481d900c0b966080080d01030620b0007401c84c24404244401c400700c044107000e0038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 337426321 1250 337425071 337425107
    0x9060e0613150f0b0409030e0a0b04051f090801051e011502060a0f0f090503030f010b04030c230301150e0c071a060102010b18040605010f06020303150f0d03 69
    0x544801501501007008004002d0101140031102c020324101500300000080da880350024110500341c3c04a403c1ea003007210201d001542d05980c0d88440d2505031070040191903040c103010704203420200415040038251103014403503040310850901040c4640e03c80c40103441040b0080c0310324105180e19180c6d0059805410092107060350010900c10720383c1d42c076001044c0c9640d0007403040791110512500101044103079152480e48030b200140d000e6030503001d182c200d81c3c03141005540c3e07442c00350540107006106803c5001f11840412080020500900d2010141c2d0054600e0740048000310860401c41d4503170030015605542007000359046284181e903000c04461300c140d250074403075488102020052054120081c100408d1505074440c1c001d8110546902c14818000090b481c040e040024801003101c01c443c95400014204200400209001b000e00510110240401142c2082c6d406512070100070610050f50500c030079480e09a85e00e00b40e2241c0a0b6801400302070076440300d4207008258440603d140c40103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 337427571 1250 337426321 337426333
    0x412051603240507020316050c1c0606050102030705030d11120a09031124150a0e07020723010c0f0b09011a0a0614030a0f140105030c040608031b07080109060e 70
    0x102e541da42c000c161113654140c1c0903500d0b202641b130b20a038043e083d001c401da90910038039042a82c1030320f034134046091a10700c800c240c50503004523181c510b080ea09107030041e90442d0014002c09000990000603108026840307900450806050491603002c0e002da42034000c0160000b00912800090603480341424078000c1ea0b840c180030002d0906142e03502100c2450503101c07118000010003001c2c2c01c144a80d044000300440da002d01340352100044003400c46411071510f5154a5051240f01501046000014420400d50440c1a882c4c00c540d81260b07030990481c503041c00081d050610030400e103490a00d8403141c0c014803901690400c203c141d802401c100d085a0352000102c4100001841d1145075101183c6a940d0340412540d000440c5400c0380e0005030007600c0654880344090a007851502502d0700d108400100d100d910b42c034180405152001c0402d0340e0f4003031481d08109008281020003100c01e024010340c004803079540350401030742c0341902c0340e80311807065442d10b410700003004915008107400103411011926 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 337428821 1250 337427571 337427633
    0x270518100902011211040e0c090a081609020a05090406230a03050c010f02031c0b0a09020a1e0c06050108010606080c0a020c01080c07060e0a05010e0c03030412051603 73
    0x700c41c0104000303408a1602c852081807842d1980084901c4450711141c14101540c0302081c0c0c40b04a02540e003030200c00008130f251740306410002c00881c020b0a03507900624100d034600c0100106d1136400c0c011690220340008403c1419809903041300c0714510301401c10426540c0d900f09207490783c003041541da0150f50440380314036034518050441d481602d412001525003607803c2c10065401c07081003011081580000e00c00305070f6600c40c0091480700d0800290020490082c1c0404200308040f498000c104440d2041c0301030b0005513071080c016807540c104a88086030090100c1020b0310320010f5284010300300c504040000c01e0741e020642018085581380c0e2620000c580300d20041c00040d008801040c0010381c4414810096984120103564204000080302440d121003521082c0c191820312190401d030b0340c451020758042280901c6990380c0484108041c000746640c00000940313a00c170301e11a1114800d8100e0521090002c01d002d0300c04d5142c4009100809155689000072070a400c0041e00070440707815034403440c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 337430071 1250 337428821 337428853
    0xa0c140301060807050405151503010303080f0c0a2a0311010507030608030f1606020a0503093007060e150a06050904081611060c03120109060b04270518 67
    0xb054032144800b6060a60a1900f4030000f01001000742c082c145500100304c0b407640b10f030056000d07248000c0002650365811414040d014944c003400802c0c4048074402004403403590b0000391140c682081ca050180705000200610352613920306420504c0000c0318000a04251300705c5271110100d0340e40002413107555500d0100f54102c80d0584152441d036042008039210241c01400108024003101c2483c50480885444090898120b24003100200c0c0e000428001c10300d5040040000c981e0010000076400a080c048040c102a0401c0d03000a844174041200f10400c1966040306408100d81000c40e4040d441c140c0e0070f200d0460007034070a00030342032a1400101e00740c00e080080d14426604900030030300e070a01101035090101043c001c00d032900318504400e04516911803004144181c03000e4001c41c3c48070303200c4810140388101030f84080441480c282c41000b60b00700d10070a8400f00ca6583c032450180382480e0303e1103607900295064500001c2d14000400124001b40f040300041028001c0460745c1d004c0c03a4451071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 337431321 1250 337430071 337430081
    0x5070c0807030b04031202070507060e01030b0f031207021c050106030209090303040b070e040b0301090303020904110c0706030c090e010806010e0c0c060103020f06070b18010b09070c060504060603050a0c140301 92
    0x41c2c24243e07030000060109015455001c00e104002c000186080200e440c1c050500d020b9801c940d0004000450114056a0501503400d00500484001403c41c80b05000281e48102000200c00e0300c1402040c954195075840710764100e4103001c0c4018400e04155031a0990080c041800120320581c0784601140a0b0000001901d00c51540000120590340340c80f4424bc80c0a881600e505034866184c0b801d4803100c1d1420b0203200401c40c841d44016032a5030540741048191405034200d008145018464195800c6000594000f01c2e00c503410000b901007038102c0b0407540c954083d006454510000c60002801d41d00009100341211414114400c840e103903540481103e210320345000420354803100c01840076240440e007025000400410540c40e1a60035600d20300442411a201c40c00c5051611010380d400c0300a005d040134400c811190381c281450501005041d035441b444000d0841a076540c0018200462a03204401075900101290f110130300c9403800b1001d410650007442d0602041d84540200b0382014016 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 337432571 1250 337431321 337431323
    0x18100906060519081b0d151211101106070f0e040504390608240d03080c091c02100806010e041a06041203030c020601030209061002120a05070c080703 66
    0x100c0e60600110f01811102c00202504500510075078504000311400014010404c00c0420807022400101e4411207031001d2030580c2c44825009032046050300001d041515009072000d0450344030203490740b000c6080316003183c3c8000000c1c00d88101810300203803e801c586000300445a40c0e480c03020003003103001800260340042e40c0c0200900018004069180d900b201c1d045400501103030860030715902510400741d40142da0b40400003141000f0b0502c011504961030f510070a00034295050615521900850b0f009003000300d004c2c081100000124451400c01012100035440003001d0b035200d0854081007034101e03001024120300c6107007000c44590499004105c45482444141c451588225132002400301804101d1210200d0a00c0318030800c4250742c5841c05400034000409004070108100d00e4054129181111303c081554841c400400040e603650002075480316080e500c050307400c40c02e80c10581c0741054508414400b208040350000025500074003501c0628012680c0e40101550ba8011030340b01e038403a000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 337433821 1250 337432571 337432597
    0x20c2a1302070302100c091404141326091314060114121005010906050405060315011101050c0931090c08060109090b0a0b0307050f181009060605 64
    0x88002180a0680c0030b45038041c02070055801205a4583ca542202c484103a41c0d030109004000601c441b03001122410000001902e040180f0000107212152441c0b0082c804117195800d401c4400c208038122504856401e000b00351a6402030300e180c0c1d04102a0044001c650103044422084103080407540038400b103000e03c810f80c100e031a44038000110751040f808030500e54540f80800038880d100003108420ba20401000301038402e401e040800051144002da4131500800c482440240020340e10300c4222030300074000c807801a00c1032501a0043e00e61840e40014410799501e07003410098100c0b80200108040d0404680303015191101000440b904040c581c8544840e100782400d440100c10542d02500c0240d02400d19069017035030764501945804001d81048110320f0300d0310a5402002002d0b42d0b09900204c50b1380c0c1c24450a82c03e0f031302080e943c61243c882d0501c580c1d00310300c1811058a8041142106014000c01c00c9041d14240c0c46451514600781308003108645481400118544520184c96034a02029 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 337435071 1250 337433821 337433839
    0x150904020907142a0f1b010314090a02100203270a0e010303021014070c06051506070818090103150203040804170610051f051b01020c2a 60
    0x1400780009104000c0c1007105005540004050400e4008040d08500c0840e503548518000c6201190300361080380221a28550310805010030410310102d0440c03066921070074000c1e0795003d82e40048007d056143c2c4080c00a17182e4400340032041402042d4520114002e850f140781c41c50300520106c0e034038403510117480c035500c503900c074089696105c15000f0500100003c01c14207220380c590401c40c0f02c1210a134012400760b4843c0300709080c0040240130b0407400d48490b1546005900c3c181c10082d0409481c01001001c155882c800902c20301e45080550b80e00c001c014008a440f0519071a1805990740003010b00392107500605c14020592401c401c515041ea0361100b0030500c001d0850004501a400c00703001120560b50070b0101042d82001514001000b800803001022107080510500c1c140f11a580c0010780240c025200e080201e8100b0125035a110780e0320300e4030695801e403260310f022060303180b85000d681e50b5000040b441c0c40440001050090840c0d080840703540002c0003403070071403003042c0c03126041e8001d1074074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 337436321 1250 337435071 337435073
    0x815060a0b040b070c0f29070c0315091709030f1908070606080109060618110a121122080102181e090a0f201e0d060f060305150904 58
    0x440f001d00300c42d511640e00c034100c1944580a8620101454011020741a0380e0710301c0c000f030403440308104030000282030070380c0c0c1c03a0039819207400c400501c10380005000d00d400030311070000c03d4249501079030701c00e40c1000075038031545600214000180d1240c0800703440382c80303000d000726140c2001061601d00400003843c0d40401d1501c641d00d41e0801d800c035036001d55000e540ca1a000801c02000c2c010350315003a2081d0302c0080c1490038108000d0444840c100b000c110a440e028624103100003100840301070000f036050498501c800c11740303410080e010070400b14010740c0380801c03186400001e0015441400709248400301041e034079480240d00b02d0040d1000c07034070a040d1150b1010745904208056144400c4503c2c900c01c842103000001c04d03001c10703050301c0350b507600c964804418030780d151548203808903421044110201d111960340242d0580c00b070140c603500740003180d6013110f60b0707010f240c0b0481c1e94a2003211010302c41d0558481c0340f0350541c0b12900c6010003007414000000c4003014100403592401900419554194a503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 337437571 1250 337436321 337436339
    0x906040b04050f0304080106062d050f04081509010506150f0a0e0904050703050f070b0306270f06100507030210050a060b04080c030d0c080307050703020c0a0815060a0b04 75
    0x780c42940d803800380d039145401c0e56400740000c002038010280041817141c036220b0010144000390580f041e41c0c64102c000041c054032500340440700801d030392034a1600c03603c07555484d00300741c0710b00d6020145510603030640b0ba03003404000801070311480c411002045642d884d181406600301600030b48488422007000051a1154001d001c0c00214850745400103207400c2282c04540c910f041a03e0650f1503601c800e03000c008202c010440e8881d1300655001a10b030851900c41e038540c0c3c6000281c08288540381440503501c20085001c81c0c080700c03070101900e081460400440941c1000401e40d0002d0141c603149003603180b01742c000c0c01200d075069130640c0104041d020519503c0000c003c042d1041e006182c0310000000c070854003401401c0a071030305102a0510032280c904040c81e180048a40006105001c480030340410140c0044c1d81d4004203a041081d540c000d940307812410503103822183d0398007001200000c2803181b07000551501900400c0381c2540c44d03403504c00400030b80f6041881441c090000c100b0080c408211 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 337438821 1250 337437571 337437593
    0x31e0303060e09340501120e060f0a11041202090615030c2d0703080a021315020d1701050d0c080a11130204030201090608041b0e0108010e0303090604 66
    0x802880c00241007620385030044280e98042d1082a083d5000408050030f200c0062507034821500c0c0d01c559003140300241030f14290003554a2088a050180c404050b0b85841d6141d04904001e04400007540ca1610b0030f1000b040c02e0000030740d8000340407494040601074020b010000c031000d8544c0e0300902441700d000d550030440b941c0c500900294014a0f041c10118403010b100c0042d40c001c9848018042d21507003c00f8149910011440c04020009040b80d10030104842003030440d08013030307014504403085580340c46441d0041c5c840d41d1103900c22506070080c00503007a407000762030703500c201526420340d04000801c5004490002440465a000f5072012004100c0c0d407400082c040c3c3c0d5544a0308054554a039580384030707410808941d20946000c17a01c0c0c11943c03410324000118418960900f482141490304580008040070f1544c013800041c045204040750600250b2161400040340c081400c9003176907112602985110000c4c41205950f60800b03801990380c9a010003a613209da07803c100105107990b40c4d81c4484070820 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 337440071 1250 337438821 337438823
    0x7020d0e13020912010c020318090408040512030c0706050405040c0e09060f01030915050a050f040804031e0516090b0409051903142710080a0b03070b130e0105030106031e 75
    0x107021001c200780040b4086c01075030044420b0b0f402958403020582d2940e4946c4201c0000a8400d0a82c5010040003403260016a0207032403041d181502c800150300c01c00ca246201e2060080103a01c01e0074070005506030300000410035940d00741c40a200c2c20f0b501c0032003981c42c0040d0b07d4445502c0400300700003071560b08001ea007440003420140b402007038500b42c0791541c280e80654210b01d08841074071002004035110312401015088003a0680c0229a45040c0d01c40c00d041c0d01407800700a10005162a8600100d5402120f0000c2182c103d01070f02c0c030b440100d220019101741240700300911181007244640e0f0903c3d00b407040e9400c05401602403d0b03001c14012114a05080c100c8045040c800c40072443d1000d50b60100c0a0038080f400b507166035148c01c01d0201074503006400042e000d40700b00035401440500e240d015004940003012082c010481104500009091401036008204014008540c501c0000300070741c2d1101c119010f404401c1c83d11390300d807020b06099410034040a08200350b610003038150a821010000042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 337441321 1250 337440071 337440079
    0x182402011506080610050313030305071404060503040c0e070c08070501270308091605040c090e0901021b01020a090303051804021204050606010309050618010207061407020d0e130209 80
    0x228010081c6002801280c101e00e0010300d0210070800341342404030160943ea420b5041250461a000444428080045400508250304c1c2c101240c0384074014800314030354018150700c268a454a0b02401000743c1c00840c0c0c00d44030341121601c00505020440d69080c01140160343d11055191030f41c032080d10980c0561412035441d9030ba000e42600f820055a074000fa04640c030340b0f10003160304081c100200b04002c082c046001e5034000e0b40d80e041d2103203440003c50044610940740401c540d64490030a07241c502d21940590114401401086107041c410350003444094a04500380780c0d21542c504c0441c1c201d0040b10030f558041000c0c1401440480d018501070028030041421228281d010f482c003140030ba0b001310720294441713a03807a81480100402444580e03404a82844c080248602549030503a484401030724000c0403c0803503604e019109020b404a4000c2c907008001801664402c0c0620081000102c1e0700d18014042c0410110100c0c0c8501c16034204154018414500c0c81d4400c0c004200035401403010340d0340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 337442571 1250 337441321 337441331
    0xb0904170c1002040906031a010e06040b040902030f1018020a09051015050d0f0203090601060806150c0705090c1e0904020c061021030c060203150a1518240201 70
    0x2d018640010000340c043d0f00c0f000306000d46149030041041303070700c00c80840d0303016060801071050250040750107510501c1102c000c0307080c0e540e00b000310300104a42c1401035018001c3e11954500201c00085041001c0c500d402c04101e041c00042402e000d032805180300a41c03221380580d00300144074445d00181d07000119405c3c41c41e42c030307a1340f102c101058002c1c07000e0b04400300c1d401060001c1d2050f130301e1045a0f141f03c032088007035242d85444503d840e140e103814054103081c0704007180440d0580d100e80d801c0d4a40329a81b41407495aa02c05a126242d40e50210f1148c02d204100d510700186619449406680704205902040801c07035010000060b01600045080b0b50440c4c3d00340041070300c542c8200700b5940202014000780911500784005000301006040d140012036048c800c2140c0081e0340a00a0007c1640001c001612600c3d0380349401c80701e00c2c00d8a0410740c803400a01d00031640345c44a180d0700d51070310900d44440300c0d00032050024400e141090300c110400703100c040445d04200710f450b02450700e550b8400c0c800060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 337443821 1250 337442571 337442593
    0x909090118060608061015030f0b060d06050f0f0306040b330301050a0213141f0206070224040807020d06020a020c18090606011b020303040b0309010b0904170c 70
    0x5001ca0140d44207035a1140c465004103c1d03458240b002d9500100c02c2000b102c102402c200820f800604882801800c150391030340c0c4a8420340440d404010ba5a40080403e82e40d011500d0124010702194050b00d8031408031042d4402c098501444040c030000c0001d40034004590361602c4504810200802218440c40500c9040c190003a60000b00040c1103d03505000b00000d03041424542107400090081862503c10401d192001c9201c041d41d83c02c82c0c01d40401001d00c580854041121911280d003c0c0c0b60301070080c21a46009a000305015100702041d601b1a1000d400c240486080d000e1a07100081c0c0b080b440b040850041a0a50300608803540082c200130f840c0020380d07942d10202d9200c03000c2c820061300004d1909515281c20700304a4034000100c000480c1c5402d00040c1582c40344030203000d003070500c042600103d0720882c50105003101184c004007540e4684d551480703600c00c0c0d644119002c410782e51030b0030009010384c504040001d000d1a040450310ba0b005110002d0180369070301c20000c4420b0341c811071000318 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 337445071 1250 337443821 337443851
    0x5010203070c0302010b0910092c0a1a15010f0c020d1b08070e06040519090b01050a080a03081617090a050f03030f13170a03090209090a0809090901 65
    0x5030140489540300e9801d0801401d00900311460520490320034448071f020300940c3c5282d00820320030b680a50500041502644003904481315003245d504844100c03010702d910000302e000c6000c100080c0a03e2113040e4820f0345030408060641c00b00c079160816089843c03440c00c1c6501c40c0755015140140d0f8107049880101c141c0000704401c3da030380b90445000410111000c0b100010752012402450480c004054450515403071444d01c0000608142c09507030384030001658210a03840782d894980382c03100200b10f110b0460034501c1ba0304d04240909401a42841c1c00050004000101081e0700c03174041c1ea4401d072540710301000704007440032039051a0801200d0302d58040d500c0580142c890141480700002c1005884903e030203414400740d0754201915030424810070900c00380911060350f01490140340004072011914143c0030b02a80e0001040740480301080035810550180c1c401c3c05568000c40e5001c00300d96801c91590340d10307030340500020300e0b40e101402079000900340100600e8000400c6800841d510107628400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 337446321 1250 337445071 337445077
    0x4170309060103030f050f0702120a0b0c041e14010c020a08031b010c0f080103150204150c110306090a06050405010204080a1a01061e08040c2c093403050102 69
    0x111140d00078a00400806422100c400214622401c00300d00300b4030304ca035800742d0500031014003a024011f80014110b5601c0280310001c0e4866101701003028605108c5450240c1c0d4105005070140320703070a1810502c0900204481c0e0088991a0102ca02c003840390000444070801d10070001c98020780c001c080859581420f101614a202c091800d01402a00692440382500c560804a0090000394601da07014180c0c0b00402c01e054075080f15011541c4a03010b0080b200900c10750b0b00007268480325882206600307910000c030f41052401442c2c0d0320341105904c000c06444441c00c1d100c80790984d10104e900400a00756810603684140540d00050810360340302c08581c10551603460849000d40c0400342e4440500c14851058054196850710154404030071200c41c9003110561f13403d1080c400b07250005002c00c0880c1005001a182510681071200751444844915088600d0410307402100000058148400001c01101441c90060921041150420312a644125620060540005296000c40030400074001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 337447571 1250 337446321 337446331
    0x603071b0822050f090103030807020307120906022b2609150a050108030a0503090c10020609070b1305010e0a0806071206080d1e0e030a060c0e030a05070e041703 71
    0x140c12101e40c000610b25420141c035080103100c0e10b68490110501c5d11880000b5066913890300300400691074002041e45103008020008280c14101075114524170392104850080381d5940c0c08450768480c0c9002508408480c111030007554200320300c0044000c0748a650301032000c400d40c00641000345c002d64000d0090000480392620142e00045204280c2c200d45400d0540c0030064034001c000c02d5051405c0c42c0c3d1244220b00480042040210104e01d1812060041405d100e500400c800c6050f500103a0294641e00101d079440e03c2801001000515102c90400301c030040080800e1803c44581002c005445a2400c00b0711207030068139814010030410810804180621307034940302c01e2490b182c3c103c40701c0141e0707115805c07010300b0350081c02d191581030340c000c2c280311004012111040c040c0501400112101108035800c02d40c5440f40b0220241801001e500103d180d400c0c1d540c6844c0022401818142d86d489504001012680211810440034904c212165041803140602e50042c40941c1136201064000b03580d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 337448821 1250 337447571 337447597
    0x7030b121c020628020702010e030109030c0b1609030f08040e0c0910111504060b03010c110c030c0a060503040312090501140a0c0504030f1110091a090603071b08 71
    0x203010215010000b00e50700020003020011524041e8561a03075032480f8084c0c02600ca074021500c0401c6a005404c0c040b07c21401400820402426040003010655044000d41d198a00403000c66400c252051030702c940480c454aa240206245a40300403050140300c405846007201400041103000300b861803580588680f008082d1940c0d4450100000e0010161483c4c0c1070090b09a0321012090000c116002c050b0203030018000165154109400901801140598503503c0e00e42490205a0040b80c15103440552404480d585810981810b40c1d4981d0110010b611441c6281c040010038401c3c00210750041c480e142484103891898030401c1603c030845003c41d0700740d46a000502014104070341990340240004000c0c811108294809043e9119a0101900038100840c49400b030201301d8480d1b07252030001034075201ca80400084000d101e0403190042d40d1403861400c40c512006020399051300c91800000701380610f1600d03444400c3e5a0000c030240c207224000d1242c0402070200344e001c0098944044605 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 337450071 1250 337448821 337448863
    0x40e0714010305160807020109020306161706010c1212180201081b030a0905010e0304060305010e0106030515100c0f0c060f0207030c170312150a0b030f07030b12 71
    0x14a40c50401081050281058500410040350b5000240100b862241c01d05080145499000c8124050884414065010305c502014001c4980c0381c0e41442a001c00c150f921000e00380743c464040d861f544801d4618500140d00d58421a020440b0b0f031103510803661407410401c00b0b0b5813440703040005880e000c0b4900e4403802500c40c903400135542c0204410340e005081d00c0705400d0061103008440304a00026180c0c100150b0346503450010400c09500941c64a5a000e0440f520f507562480010080d101c24000c09041004020001401c58042d0145034007400c0d91656803103005640308244620444050071240c104124582608085204204610341c428054240d41e1200c9003000c00c0604038601c00e0050f0310456100034410804501080048016078051002480002002d0030850745180101d40710340c058512924280311001416000c811002d240036200804190f42e208459586030104a1301c0280003095a000104628800d40c0b1218480384014801c04081d0400107055103011041010002008202 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 337451321 1250 337450071 337450079
    0x16050601150e101110050a0b030d23030c070f030e1c030509060f0405030d210902130e1c0306080111090d0b100306020706020a14040506042102040e07 66
    0x2200c9007051404440c10014116441c4002040c1d0000c0c110400c0003c0180f082e000070240b101c00e001c6200310100342641400130b82400010000100700c020348692180c0b0503407640c03040407401951250f00c80381140454050002484d900c0d00c41b5580024241101490104803210004000c1021305030f50703900903550343c41a4041d2005201000b55410301c45400c600194082c4400603038030200b10742c08140281c0300c4c5a11042000c504241034015038001917410700807103030410400c0e44d1120880d610115056003500520411000110407034009003070207074100b410541c0e400d109507844e41015407407402000498101903280f80c24004107450042e4103100082d00c50008008824090140500c29108a103a581c9403a14000028035002c0c5c48000c0101a0b211201c0041c0400104000d000d00458000e18150b40d01c040c1482c10b00003d61004020320b002c540400741e002260380c1d921003034800782d13040a80b648d854207042030111000d01d100018894040240c40c1d02031401070b1100d0146841d10100b4030000d1a01d5414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 337452571 1250 337451321 337451339
    0x209040f0c080102030c162d05060a0b060904020a020c030d0e1302090607120207120803090613020a09090215040b0403021203070b01062706020304180e03040509070516050601 77
    0x1070769000968680c0180184007444000d00d040311031101d800000d03484500700c0f0f031500e07150043d20038a4802c03004807004d02c90300b02c00700580c150320b0034540f103142642c616590702c0200004031405150010b0b000fa6040c042080030b41056030040280e410540102c0e8030f407036000d4002070314200c8012030080000350622407443d81801c06110211704441104070660404441c0c0b008034005004424003d050260341c0c24009400f2802030103448081c001c0d840006869407070608000300d49500642d2451005e200c0c000004600d0f10400c1c030180e010300d9005052400c070351700d0583c20101420070300b03005130f0380b140d103002c250f20130882540010001032222540701521145180100140c03100310401c1c003401900200300d400d000030407a0305614151081801c0c41191079022642602100801905490451880040104606d600000a04110b42c4903200c031100748000407401c002901c0d449141a4140d038401c5c402444140381010307001d43d2100039442e1147c2450f031a0840c0d10350a0392456016a15504480018407440e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 337453821 1250 337452571 337452593
    0xc02011a041808090604090626211305040608073f0602040b070c090c0903050a141609271509020402160b0f0f0f070f09030209040f 58
    0x60110360402c0249048020914000400500100806030000e0140b086030344103003d940162045900420001c0d460fa010010724582c1010f0f0300301380c5800e40c0215009070800182620415035103003004038003a118a61081084e4020141491112155a10100b0107460f2442258018184180205040c91501c9900c90b07000c0d0780e8400100813082c3e101464203008420540c10490401008005100d052450411800034040c40d00074a420410006502091003002048242900c400c82d00800069100c504103840402540c0300c000c0890700318080001c0804c4006440040304002c00301943c121a0780403041c81d284d40802d0704101030241e81c40300f00e2920440c00c0d0801181070b1142c0102014107040603160208038160102c004e1143e152a00800405c549541e01900c0034011040b04004040d0300c40d11f00004940400c481600e4071404543c00207009842002e0207038022004400c1c201c1c1c150315a010211408034040041c0001c5c00003c5000000686444803c10300c076501408020400800c03904e00035147c0c1d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 337455071 1250 337453821 337453871
    0x6040c020607080408210a1d012003060f061308060a09030507080903070e01080f0613030e0904030c05060a020c190201020d050a030902040e060115050a02121c0c0201 73
    0x5400704003044121500000203640184e00462002e4031081d03504014004d41c221864240c403080c18260a00ca0003802ca81c00c4900e002015440d070580044036980302e1800c0fa5400e40758100d4461820030062917005021000310b03000303440a07004407a8201900040340159200b52032050701d00907240310410181500b4040142c00c01c5230042c051041806a8600910300e024501c0041d00c0a40000348103c096541007000100410902041c1a80c1d0360f980c001194582010b03602d42007450054600051043c4296064510000c2d0700da26030700d458081110503c182028010f10440510000c481303001e01050b000c00600344100c2e004400903a417100c0044007603013490300450000a03003180420080300143e0700451445c0d401c0b070303042c50426203820514004902400f50041c010750842d2604403030b61040390005c42ea1038140c9000102d20b810f1400e034000e0031582845064021030043c2c02c0f100c0d40c3c601103100580141070564012440c10718500a11011004494907510072801603990b5482024002c0480c4844180c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 337456321 1250 337455071 337455073
    0x603040809011b0b27012c01060f030809010203070f1110080405150a061a040f0b03041505040212010f05010e01050d0302060c0a1701080604060510030213050402040605030d050306040c02 82
    0xc2d105603540e8480a81c2c042c0400c0710403160240301d10380c02c0081d0007a0090240700003000380441030341c50703680340982040307800340c100c1e11001420000007c50050041c5804c40365811a40000c8901e951200386e60b40d040b001149045000070460000840d0314107240c0c040b5a030040e0050682c03071030201c04229680d9801298602030020820030480810b2001c2189103101c204004003030040d0b500c500b04d02006000c0c54001d00860b200540c1d444c0c135005618005402507801640307903441019100c0e0510040d0340401c690041030b00380d107010f550b51044041c0e04590303045480640071940c11094038041c03a095490301c01d017081d65141d4401c0100f00c9000400c41c003d0061100351000c20340c800c20340e01c00a4076000002e04035030350614005925050540b2600c01541c5180007034540d01c00e996121074805031104000d840540300c4500380b00100c0c83c85651414086d084903801001810782801c40340c1c1d50b0025100051003a6842a52520005200c1d00d0920056410302803a9654540d00c1c90080b00700411560340c10402011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 337457571 1250 337456321 337456367
    0x50910090303050924040303021e0105040c1505071505061003151229010608061507110111070b040e0c0a21020705010f05090d021f1802060304080901 66
    0x2c02e0b008000ca4200d000c0c01e03030f8840754206454002c00c400680800e07040400200005000050603400b080c40800b054003855070b0002070640c140707158240c0b41c0680b800750001206007820080e6036644c8481a031742004a00307200e4149200f584902da5061a07041c101c41443d0344800400c2a68607040d20921071014150404020f00ca0004612441110482c001d81440c03620080b40b0344180101d600c10b040020080a050000c0d41c9102c400440c480d47c800c0c454440480d03c40008902145001d04441c1190b60810100714141700094031640302c03219800071030380e0500c6001c03402250108000d00c004400361600ca40a107940303503d08260a4080d0b40c00801c80302282805000b22170105611010031214440d00103071961041c0e0200024074028482d0650043c05586003c005892542c03154100a20030081041a500350440186090740c95004100030403030500b441c504503884690b100c3d0f101c518100900000340c10442d481e640880e0700750f403080d20305540011011a901c0c0242da4000d00c0e01d21802c0c60f103120418 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 337458821 1250 337457571 337457573
    0xc0901140f190506090a05210d08010308120612010906051608060f0904021513063c11060408031f0b16032a0b0a06080a06020c0307120509100903 64
    0x10b0000c1c0a001d028441c41c400580743c56035581d20040728000d07003001050501c60503422407402070040d201069008180c00781040c1d4030300703150260000030304994000d000645090f000d40c10b440c1d1440401407000b039100e08001a014003101e001d00c40e99101c1d61140300700046a0a02c0e03d84000c8028200489004100c021000c001085c0c807650850305140800313940110b1103031a1880041c2410702c5911031009031807000304809807980201c9102c0402c981550300c5819908852801c003051030501c00400640f004040c0e0f0f160881d00601034014a28802245001103181041014043c1895010740d01502d25941c08420301c074207502d1071140f0402c190451503151030a146041561034090007101d0000c145c9281c244061003e140c0035401540b801ca110710508041100c6e40722121030001c4040383c05a07210041d03400000d4211949105140a0314005001000b2403100d80d55000003a43c0002c0500c00b10380024070280d00040e1111004616401207621500c4d280c8203a40280f00004005515880c204011a00200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 337460071 1250 337458821 337458859
    0x22b0c2304090b01020a0f050106060e06070807031110020a030b030c0628030b060406020a060c18050d171902010f0515060c070b0a0e03011802011e020c0901140f 71
    0x74003190b00803000816001d01050050b8144510300b400a01640900c0803d90208001984107105a41d03081e2184584070720302c902807100300e001d081c100402407981084802c012038010001054411200402c0321440800e00c6013180c140c1c0c000444030804280c4032506070125240078494003000d01c40a42e01c82e0b003081d0346001140000301c4002145111010010a2000703014802d8115004030240540016943e41c5c0e00d031310003507607401c0c0d030b40c4250343d41c520b0b041c45c18240b580b164008054110190b082c54140c2801c205c01c110303840c0c1c030f0701c0400c541078001d0b10000c0d40e00700085005000103025900004030a9909070701c01030300b07446400e030007400001e10304810810926100f02c001c0d0043c0d0400d541ca141c440150119642c542480341c0c0200f4601e12004c00d828004075440103481c050b607441075000303020310503941c8104a040411268004d004c6025903020000f06052a070800000305001c0c41100c060032041c0c0085442000283c0040c120b210030408186210f0418070b603412040c80c0283c1c1c074030030b0a100b008880 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 337461321 1250 337460071 337460077
    0x20d1b030624082403030703090513090b07050c1515030f0708070b09012309010e0303030f07080c28030e0309031b1201051905010f0305060703022b0c23 67
    0x508100c0d00d0050400001486441e44e44401080150132641d54035903e003006410aa200d02c151440344028400c54070020070705004d00342c0559842080215035841300c0d502600c0301c0d00003e501030131610605186500548000000750701800500403900e14030408134091609060b0b9a000070221907112540800c022385000136150202e406442040c4c4e2105600710040b43c000300c650040510b81c00d400606041314103407040041c1041c0000340c0381d441040101c00180340d16030008944080d411a0188000349150307004440ca540e1160000c24440d142582001c0d101d41c1c0d12031202030702c5444140c125003518071907400d40300f18451400750000840c202130381140060350b030780b850000310203d02c0004003d151960300c0c1c43c0780c150140c03072010f0028066480c0c0440d0912006032900364448100d820600001209942c0c10114402c0c1e07600b2034087c0c04181c1d503030001a006541b14603000d004110084810103860031030b00c4500b24407100d922030041120741491f6030043c0343c0c1100740c088100714200588a444d40000f49411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 337462571 1250 337461321 337461331
    0x902030609030711040b01050d0f05010810090209060f01050f1207024c06090504060c090602030301060e0307120b07020c040c02030418060807080d0807020d12020d1b03062408 77
    0x10200344103040c1b4004031400e0280b81201842c090403c00c1c1207001c3c4940b40c00640c141c4800000701c82401e04d44110b030b50309075000203001030b4010017000003242042c100a07544d05100071041c10500c0c0340a41d0020103000903406200d541600c0007002044c000040d40c1407040b0101ca070840243c4800403403c1381011000c068040785407007080d80060a02642000c003046440612240f0140e04020b07199440180c500585021102103529500d0800f5520720907000b8401c0c0c1c1c082d58070310b0303004506680c01c011040d0342884031010f07503d0340362103400000510b4410340d8195450051143c148026141003442006e4901003c0c0c01d0118401e5040c156611241076000080d42e0403240e155207090b030790450a4184a000740a40d4000190f40c1c0120348002c2010400020404881c4840e541c03001c503ea590520120b07100c2d500c4c40c0c8400000380d40706600f40070380031141c2c010300b00c04400858001a10000c0b03822804100c0c840a414802080d25203c0400c02c03459a20051030a00c000240d40c545074440d42a0014406079005003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 337463821 1250 337462571 337462579
    0x5090a1205010f061d060402040305031b0307080703030606031d0d0f0309170c06010602160603020a0215010f08010605010c050c01360314030a0e09070318060902030609030711 77
    0x1140d0600000b504100700f0700c0c400c50740803c1035540b107100c00b910400054042c800c4240411002ca1090b003450703c2181d0440e9046000740d4104058040c000003d00700203c041d0505100900030708001c0341994000b1b215003486610001081860450050141c8410f0002c051001650455496000c10049100000241949000b2980d149000c10503801070040007000b03000040c040600c00c03c00403014000b841a065510704844244c0ea9a0000702c0c0d03540d032140d1882c0da08000712030041010500a40140411046034016541d4910b881d02c46002d9204003640020b844201540f0b04110505003807050f400909005c2ca400d071603d15186c0c648036560b09d2001c80c041d04201d2110702da8504c1450070290300741d0800b03d072031601000c2d014000304080d0030320311800182c800c4100010b4060b01c485000003111b403644003d484181b9005010010001c41d4000104110107040e2541c4080e000c80010302640e251951081d04000380806840c0141840e06100810004c1180c0c01007110b4004551a40004108030500b12 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 337465071 1250 337463821 337463849
    0x31b05120a0f0e33030405010f18050c010e13152301020303041506030c09050f0a0506031f020c0106080f010f02040f090e1908030405010c0e010c06020310030c030b040b0705090a 78
    0x120001c0c1c06881001c52900c1c05140401440308000040d00052008020b510007171003d03c030400704800d09410b0984005208cd0b1010300419682e5014485040e50540010001c0801d80c3c1c00f18680b9080c0c0c2c0105c100c900364042044030501c000c0c07000c0b903403094030300c0c1131640040d07210905040040d50301d10015001401800c00d014201e0000b140c00d40003a800396074840c87d4007201c5a5505030b101c0203002c1c10b5402e200c00c99030510014484502034480d9138492000100201000d0314288100040c1c407071180080c0716065000c01c45082c03100805d0040e40c0040442400900e03161368140044c9085503004024a90140d0040004000700001d05109034140e40c507d1000003021210015240c0c6880b0443c5a480391500080f080d62003403280e610080d40c42140144002d00c5130104261040711420164409a4081400d19141e58040740407a4040c41e4040c0105001100680e2262110225508541c1c400c480809003401000108403468001641002a90070714906220101c1c001428451082c094254117101103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 337466321 1250 337465071 337465129
    0x121803030c0a0e040e0f031e0702010c03210c0e0a0b0a090302060c0c040f0506041b050f07020102070e0112030f03050c0f0f161407061704031b05120a0f0e 68
    0x4e83c1c0114250b440c80c1003218041c00c80c0385201e64a13038006201d68918400d802000c009043c2d444c5040750a4283d05035140768030145c2c00ea40940310982c0a0fa08420b06600b007002030048050385101c5c201d048181512483d0b1804082c45c1001079a0340141c0107903011042c14403440740e1090301302c0100c1302500e50449050352694901e40c0001c0c981040034041580c0719051014034424a0f28aa10136402124180c0f41803040000d054011b50039083c802c1071010015400300056400020f024000d081d04510500c1901d051940d9040788021100c801c0e00081002040b620309282019040320144030585000d06050001349800c0780e085d1154003a508207000240e20024003020300e490490102d80c040c0d82d000400a0004ea00c500340b601c2d09500c881e0b1007030440c0c030881c10b0215506020f00540b0b1226000741e20201c00b955590740d0200d90341a1480c0711441429050a0740c100041c200780000100c02551003040c0e40c0380d54001d6401000c4001420040042c092114030000395902c4040c0301c1161080000c4040c0500c6000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 337467571 1250 337466321 337466329
    0x904030c03140d050601090806070c1401020906040b18011b0210050d0e0a0302060a0b09060d020411030405010c02060c0a02031e090a0801050603070b0f250206121803030c0a0e 77
    0x414842d03034111650010700100603440b95401140102d100383da82041d003d40318400c096540c00f00fa40c80101023100c109010002a101544424045444400260910403035402042c203e40050b00404180e14000ca050f4803007a2401c2a00034103a0000d1070042c1c004580c00c1208100b031011454080d0243d4a299205040a8041c900300d0b0051200c0c4241000725100000034a078443d194024110014042c2802042d5044040d009501d081c0d500103108528035140c0804110720f02c088003d040b608aa15410846048440140030710f109a00503400410a840c00c0d00c002810722200500402c04540c05000d01c04015074008190387c080082c2c401c09881d01e128200091649024041c0345903845420048042060301c0c041d00494003a1200380d046a420b5a1501070506007401814607402846000340190b00c90314500e564440c02c542c244030070401c5850190b4020803100d0740003000d0015500009024803443c0244d400351050180094005113080d818030058004503031180d80c1154080141d400080c4c50a640d0f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 337468821 1250 337467571 337467587
    0x3020a03022a0601240302070204060b040308071e0f021003140901020c06090c0f010c240902130908030a11040503070906061101060501050322020a180e0307020904030c03 75
    0x203090060428110716508070120415201c0b02940c018028a8000030f504144441054000708580e0003e100405000700102c000f900f01102c02c0e030b81300b40c035841c2c002050042907004001075400b0300c00d699919482c030300300300144c1840000c04800f4280d1305c00c2e504010807003409044507030b59411540004580407010003107000e090200d513142d0100050000b0301807200015401801c0032010902a1103203940c92201041e1030311180c6a031140c0040003241c80e080c42e58810000d400d40544513041000076000080610700d503510749200c82d9080305648407401e0040d41b42510022210f40b10707900b030600c8101103c1d0384140f0140005400008006d88404048a030032a00700250b5024200140844400325503a003c1ea4001d01440d01c1040c0109043d000300c110044c00600681090b9101a1151451a11080341f50380c8055420345403200d48200c1c070002040141d44108007480200210302d500c6400104046a0404680c1c0508086a0b10703442005508010303103507000540c0c1d205c0d8040c104450000d02c5800c0c142c5440d5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 337470071 1250 337468821 337468837
    0x90307050d08191104060c0c080607050d050c1e0c0307060e071d1317091f090504060e010509040807050a030809060c040b0313050304050409030206010315021903020a0302 75
    0x1010744041181070340d6000644520419034807030390f00c01c4061001c180d141120300002d041d000d9000104001e206040c0600c1e1041c07207080c480c10080360107031ba40304046ca00b00301d0256000c0b070003e540000c1054001585008a6410030a880005407a00141680028a222080074440c10681d004502001e0400080c42550851a0014014446c0305a00c0c1002900c404841c007444c05580c21040c481481e082d440c0d00e01c9072103801c03207074541500c0c03200d00e44074080014085160308500c50001c000041c41131301c5000b00c107111507800340011580e0b02c0100d540600100400d401c000c3c05075103400f40c01c00c080a00e400c0294111001580c2d50740d1262641e040c0891980f01d00c0ca800360041c402d203380d0030100766000110030310449010342600c00b2920364809900251065200e1490401c03420b0020a42c20310907500c03d0300b40a80304034103c0389041d50310000b190546503034040a8002d0b800c900010014071081720700c040310741103070700008501d40030340c40300000d1091a010340b1010401d50b02140b590102c90081d0b044810b15 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 337471321 1250 337470071 337470073
    0x50f0a0c030306080a0b190e06070e27070f030c020c0609030c06040e040605010509072f0d051c02090a1503020702060d0b011805030d180b0301060c0309060c02061209030705 76
    0x1048042c2040b000070b610031f441031041c4952264041a88060741c0c414411180f0103500944541c0d26940700484009582c40707800f550059142889e1850491070240036031038a0b003071100c00b01c1503251440000d0040b800da42c110100749030030584089011980861178421314041121200d849950140100e4903100c61581030f142c0003040060701240084400b021a8400c92054805100c030381c0e210b105100202c1815121080071403500502407a0003a80224070380a520811400d1400490304401d8591905490516040204200144401e03a880e14400382c0407288a801c07500794035208014000c0750081c03406100c0c0044000e107200808441a200b6011600a01d40040c20b2907201d800b58880c040c0100403840007980890701140d0f90b50b03507060151618070229500140039160802c990359059078041d0801895031800d8221140c0482c9000164020f1070203040e507690360f405142d4551501804c03090650300104180301000c01c002005948443c03c4980350304c012040b07580540c503226409840d60050000007441 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 337472571 1250 337471321 337471333
    0xa0c090f02040e09010b0312040332010f0e0d0e0307150c15050a0b011d0f1809160b0705030901180e1504060f0315230408070c06050f0a0c03030608 65
    0x907008150003144200390100c7c1a900c010350341040c140182d108600c00103040071b43c0c500c018101595210191081e0301001c00d070f1524003200f0403400c6801c5070300d1042100700056803a18200c5081d001040b014000301064200101c18a40c80000240e49001a1103500100410402030218892141d40d1954170a6032003404201101c40f03070b0f00003401920089a80007140c03464100d110110b58443e41103a41a404085412801c403607000c0c0070710020750004c0700501d8004180b0f44940c080d0351074044100b03206605510190030600d00d110010504c17a4115800305030002024000e40012400c044110b80342c01c80e09084c002a40c00082540340d951140307035481022009295030800a2281c5d10200c04100350004613010010f0548511210040300c9444c000a008041c1e80140c0c29015085c0b584607000c0d0030318206401390a400b4911413500c4050084404a40740d8170301041d00740800c030315543d25030003600440c06d210b0b09140c0107a10003449409054904401c100103c410101494029440346001d090441c2c150b5007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 337473821 1250 337472571 337472581
    0xf0c1e060403140702060714070b280e0303040905070212120f011e0308030c0d060b120603010b0d030c02150c03040f051c0807050c0315060f030a0c090f02040e 70
    0x14031103404603810b8010400da01d02d03080c0b07101c00c020102c0d4000784d40144400c0c10000691030b05c28000b4842200460140319400003c04e1007007120300981400e86480d03070100780480000c0c440c21701e0700441080403420f000f04c606c070500701940c02000303550994601c00303000140e81d0384009040380b900c0c0d010700e0889e42d00200020300c0b100300e403040e50031070788146215650354482c2d9903101302c00c020420301d00c900c10a1075002c1e5172040c00001e81d204c00440d0040e07104000d85090000b00108801110f0351980600c0c141d6a000030200049101031403403c0d03000d04214000c0045a00c00d10208003a100c030703150010704001010300d0a800719540c1d00444c02c1e0144000410507124404040c161340d4980c024090004034400114001400d85010030180700700510034441c80d140c0c280190740e86151500701c18411162401031404411240d1401c101c500505980320600380401d0030b0020900a44508060007207000341c11240007000070070b00341e610410465009036400505049058a440020f0003a500060324860501040c06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 337475071 1250 337473821 337473823
    0x90e1003050f0a15150504060e010305060a060b090f0415030b060a09052401120c03050117010513110103091a0405060702161a0c01020706091112030f0c1e 68
    0x4000e5038400c00c211501524400441d541d54820944001c3c101095801a204601056002040030300d02c0c80314000c8050791900d0000d804e03076455410699042040200403c04d11104002c0103412030903c0c102044002d042c110514803600c584100c0358010683c4a28201082e2120340c03152281000203c0d02e540b82c01e4886c6400b01c04060b083e91a2403281d0000440401d6030740b62880b41c14001c5501c5c620516141300002d0003240c0c1d4050509119041c06019500101c05862038015100c40004503980042e0030341c148000d0f1154180c00c070b019141140c2c90715041018003502085103885803a080101c004a651041340100c0150109100c010403400c03070308a8070110380344600302c4240590720403000e8800d2542c6140e0200d03650060050700c60881e95054908200341c241e00700c0c45103c107014203d441468404c204040385c4c2668040041111260364445018040c050525140c648100b412540d40340b86031942c0d800e06d80e407800341800001c220030002403460075410041149900804440203004403038a6462000b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 337476321 1250 337475071 337475101
    0xb040506010e15060409090c030b0c0901090b04050f040b060c070801020c0c010215010e270f070501050f0417010f052502060105150a031418071409010b0307090e 71
    0xb02d20000030000401c01d82841d800b03050451800291860781060b150204050103014840c0c41601c5d052075400c40070000c1548000c44521804410170626660f8100700300040c120781c00c80d80503e00e0248280014401039a030403843e60001103040310080b42c0c0030b85400001d585846100b805462510510700c0002d034108064024100d05e0079480d0541e2042400c0d4801a45c8400c5150f0040c01c070b004004005000c180d80c1b60750b0203604a40b00d010321400a40480c50341020b8a060741491204903401004034010140c020031820303001d00030a203000d50402189d94103c24070b070300882c0214128010300901c44a007041d802d5001d4450a03403e04410b1040b41860f903610000c22003400d08a400c804401c00380b0311201400011054101c520281040103060b140f0580300107a6005080032204050b00e40c02950050305408032140c0c0075041c44801c11200e100c4014a251a06485500602c1404071210b58158640d540506032411107840001b80c5680c0d075585201242c1a283d280c103d401640d140f40c1c14000081050800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 337477571 1250 337476321 337476329
    0x5040e0a15080f100506120715030b0d0b0603100e07061101090203010c0c0212010c0207030b04020f0a0e0109150f050d080c01020a0801030204050604050f0a0b041119081605040909020109030b04050601 88
    0x1300901e446d040b090081c0041144600d002c00d9210003c204401031080007040700001152400160724602d01c0c0c0000d02c194115a401e1340e400403131000340724a0345820301c40151064440d0408100d52004541c48036283e55880c468203041c80045003186001803030070341010000c1c0364010001c01508000b10741c040c1522800f48026405100c1144a000d840501413203034150106868004148051440d6a503c00201e4000c000300e1f0010180349c03182455844044d00140503100200300c940342981040d0009085545066070078404013942c07902000403284600d4540295203043e114190326420031f04026404d407007844401e602d15840011110b0040e940102c401d41a2803080300e003405151101000c00082c0da005607880d481110f00c00b0045107c11507158003200e45100c01a101068280501142031066048215000f01c0107281500d13680ba541e81c0303c3d4003240c0c01541d000110a2000b80020010305a0140f40100c0700d200355103d80070010744e800b48291f28020b59100c80310007410705d0f10749001c1c0c1d00d07000c085c49 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 337478821 1250 337477571 337477603
    0xc09041a0c040308120a0902030316170901210908180103180201080732071412030a0f1b020f0c03060c070b060a0302060f0a0f05040e0a15080f 63
    0x404200180e54a00840d0200c3e908624032500f040049a02d4854480c4050500845150b0300c00b01e00005031010b00182068090300b4003020302801040c103005a00301100356a00c880034600b0042c84005a07004600c65140100d541c05590752a080c2d684e10b42c1c0101401000546840c4020400c038420700c81e050021320f03416400b0380e001e0003041c43c0c8109074211a50072080090128010000203a42203218203d0403000304044203076600140008541c04907030300a0100355201581c8001621828000c0b28031005900390f0a43c4014000c419202c4441c907120f0102030031507c581c0b61100b03044981c1e080c0a42128031040c2440140c291001603124019564280c0c1c03100345d000c20b0045850a039480d18000c035086101e203103140002403412065613510f0948500041c66242d002826040120250310341e50060701d20407188100060f5650007542010f046c178002e0020300b50400500300403c0c070116500300c11880d000f04035000042340601e1410880c8a481e01e044e00007550a21030000020291040080e01c5d1480b501560 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 337480071 1250 337478821 337478873
    0x30a0e010923030310062d09030201110303010b3007090e091b10142a06090a030c21020304091103011202060a050d0f0b010305010e04230c0904 63
    0x491070383d84070300040b1105100c001c1210010042c06004907541906500402000c01e040264400080301100c1c169400100182c180b00c0c0620840d40c110b544411100240c800440c1190314020080e1001d01c101c0e0380481c26442202e05003845410ba80e84414000e000c4142014054501184024a001101d2081045e055425000b00304802d0300400c041e594544804020b07501551141c060104400f0852122002c02107220082d200119170303100580481405640781e41405403040b016010003940005800100d80c1141c0c003440f5290100141c1072036030f2039150a14603407020b29401c28100e501400c0c60800c8030345401e00f400c8c03030300281e011000f001520b90b80d04080200390f50581d020642070009004a004d0b4980c190045801342c0b800302c000e45848a050b203846e91403c8601080001a0b0b10b0036001d05280c2038590052800c15a0140903840c094101100030b200c032440c00b500c0b80507420600340a801085040380000d150328400a00c6500c05200000c1d00700d541c581410303e001d180c0d001401004035454030602c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 337481321 1250 337480071 337480133
    0x406090c080f030d0f0e0a171c0905010b0a0602070e0c09030303070806010201061719081e0c0105010902031302040c12020c0c030f1603060506030c0d1412091005030a0e0109 76
    0x15210303a00708246820010040b0030019500c4010900d02c485499503c0202804039008040c1840c0008811001002010031b080d0f002f85401806c3d00e440039031f45c9100c0c2c84100024401240d00040b41ca0407a01514a00300301a250040c0a078514401e0001d6250140400810020501e4008a042e13000f41c2083c0c0c0204000c540d00c044071108440f00e21035141254000035507665171140820340c2d1380750142c01224090300d4800c00080c060300c200c0c1da840c1500741d001000724064890440a2107214014200c810080d80b65191950400c8001071340c04100a104503900d003942d80328184106e2466082c840002c10440d41c8a02c00c0c00348581d5400c442c140b040c802d226aa0704102400300101d00e29480d01d8203403964074141c0e410340d030303800c030280c0402815960544992503201c607155803032459907581140079100600000f500c1707001c002e0030b1001042c0501c00d8140c0802c40c95030303291525044c1344960411490040e4407500c1e903900c85405001c2c4410300071819800c000c405400c0c00003005414112207900140844c0e45122 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 337482571 1250 337481321 337481351
    0x40908031f080705010e040612030f02100b012708070620150f1e160201140105010f03020a0e0409050102030123031b01050d05010f06020c03070e0406090c080f030d 72
    0x54003070400141c00140041040e54080d046c0c9612042c001400420030369100c0c000d11880c104940c4003900029851510350000348c1d018052a24042c00084091003a0302c0304800182400c071340641e040b401d6014403521100101070008108016240032030070742c2d01060b075800004040030f40d0402c1b00b11680241d25942d40d1540c130f0018888200107100c03012484569501d640e01c0564240040425414100000641c04110b0f6401c6c0701c0c3d03215003200090520b04120303565000382107404c0c4014005804640d4001403201c0d070b811020110241c02c09241c056550fa0201104446228607200302541283c2424503001c104101034000c0c40c161101d903072001c0301e4454440364401c405c0002601c03058042e0881e03c00c074011186806459101000c043c1030261821030020050320898500340c0c0131040351628a4003d1042940c1804050750724034048004200c0c2c1e5040136403640d807011000e000100080e640d10400340810455410740401002d02d14141e401e171007100400325480e03501c49a00158410300d0142c101030765004c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 337483821 1250 337482571 337482631
    0x1515080705041404140307060e01020a090602010903020a02040e1908071e0807080711130c030b0d05070b03090703120c021306081c030f090c0e06150f1804090803 71
    0x5001c62166003543c5698954030740340458000308140600003000b081020231010f001306040f611000c000103036030b89124078005000141c10703048031086904100010000c2540020301524054044030700003010340352091000d160111081c803108140440c85081e0040c80f840c000a8000c29000e64080b290350582541d4001800c096100f000b0403104d0b05104100c04940ca5201034088580b18003000b01540000c1c50000342d0120140c241c6d904034684071500904800c0e40742c020407420720026202c42c140c4038442e90319540c950071540195601d2103c040002080075208008410085030441e1814806040d9118000c08070300c1980c80980c02070410a03600804400783c1d200341030440310341502800c80d02c0c83c140e03006c4c4424190010341a08060703c2d4400700741e04600c80d00c10303900c07000c8c80f400e140b20182d494400c203650300c00801080e45102e24104040c02c1040c0c1f40500454080004c032102c810341e900050502d0185000545402a070490f19040b00e090070000381304029400740b004007400c0c1d0a60820858501c210b11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 337485071 1250 337483821 337483841
    0x60d0c320307030908070b1305010608010209221b0203040f0b0a09060503130b180f0105041101230f0d0f0c020309040c030b030615100801060e0904151508070504 71
    0x25000c10020701c200b40f20354020000c0700c4c0304d600003d18185041d1101d001e10072041d211039400c1038240c2c00c10b07802c101c0e007441004002c1600c000258100010500003c00041001c3d04030380c0d041501001c0b0081c141029417108081208840007810843c2c00c50030f0003540ca03001801a907048090788880442d07105001c0c130039158420583da0310341004a05140040b1000c1c1c002170440445030441804c0b4030005805c0801081c416801324040c0d0300032141d009690b51a080840c514000d50703915110904c030100c2d6020060300703456a000c6c28010481d031403050000e02050401c07042841c0f48400828060104d8a115005051040305035000380b14040d441071003102211418200180580d0041080d00385a0900da0401e0403480c80da8100050b00c0f0903110046418400d013220500001622086061100d140c2803448500445851900c94815810b040000c1c0c102d021040055105212080c005002c002001c1042c202041c00700106104800700d00c2e0103074440621900400c083c80c019010f01182d10300f42842000301c1ca03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 337486321 1250 337485071 337485167
    0x11403240112030509040603121b21120f09060b01020c0a180e1608120f04051318030c0c0501260603010e0f070e06060406080411060d0c 60
    0xa42d1905038842003a071000c9004a0500c0810b210456169813241724806c0114055511000e01030a0018014202e00d10a07070410001c80500d100305c1d02203807000404140740318108101d1469a901d00304151400c0e103103e90700180490400b6002e01c6584010b4101c070b2941e9110742d0043c03010001e00401623849100f62100c45401480c60ba40030014200300748212102c2e0200c280c00090500d0100c424903040034411880803091038803040040001410420034a03a0205420321480d0825080d81e40c0e1020b184118494a44118034400c1c0250b8120710035449a0745194005000030030904081c5409459162031000603a8004d1072210b00050550145022104401514042d0707121202e0307402115142e0800500425010b641e07501001d10020401c1040035880511080206051031410031612a4140001c20035070192800780003c002a1341c12129864019603c181403d9803003111b034000c03a880e406118902000c045c102401e110003183c000813108003200b0724003044003c1d040d00700054200c69261002080034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 337487571 1250 337486321 337486393
    0xb0913060b0d1e26130b090d0b0408090604030b07020606090c04052e08010e070306060c020d0f06060f03110604030308070807030615030605030f06072106030605011403 74
    0x2142000e00802410f446600c3c20841c280510340350240b90303101c04202c044203803400200070300018600300d4210020700c03210710614507200c0c1f1000850b42002d00340c50700400103000103012a00f04401300b419540b42000103080720b03031540d980341058442c4c0e080507206640580108408901c8078180958218850002110842c0c0b0b0186001e05000f00500c048410156000005110800401d003480c014a47c41c0c4999036000d8140d41004141325605501411400c1818a8a4010809103400c240344045003074048460105450030750034269014110904014002440e100d0b020803900c1841c1450420340e80284200c01010f00c6000030302c10f07507200303501001e00803070200302c00602818441c1d100194000c14518000c03421a42d1543d651f00d030440c103201d544010070b07250901070205050810105543d400408001c052504007400003130100200c0a001c10740b07000400400341d1558482da080b01d4011075004900700950745e9206100410b10340800c542d00c0c460b000340700800d9420082c600e080d02c28041c880c502059 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 337488821 1250 337487571 337487603
    0x70614090c2d0301021222020109092703050d1503170a021204090914011e020d02090a0306050a051b0301060c0309080d0c0c0b0f070f02040b0913060b0d 67
    0x301c4070080c411001000c422203500c0700318940f004c3c005442030189002e0518942d0901120300380c1d400d0440c1092840f025655079100000d80c0e4807a0010342126240d000002e0301051040340382c2d21044903540c0309240c00d050428400100356011000305803624084508000d031940e01c6085920002c1e007484041c01d06000c561103020224003440003424070b0441801200d14600c41450802c0d903d4000d54880c8110036600c01920062001140442640020a4000700704940c1e030505804014500310340b80f100c000398003180601410714543d0464000d040300070295810136503a07142030405080d0858400007210304020108952210510900101407580da80c3c00c0e05580c02e01e042200c1c400110f0500380d0800c0300181c400181c21030140310a50031001c59669214180b4102e04100c01c80c5515540034007405c2d50b0800c0300380d606400c188155001303541c0c0521080070340d05450001034050051101d01c560321424074000c0c8011503000c5440c80440c284a8a030030f0005044210800007501120340001d80b00148081801d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 337490071 1250 337488821 337488859
    0x10207030b0915010801090606060314040b10082b05040503150613090f12050a0c0b060607080a021b0f01080609041419020102010516020a0f030212070614090c 70
    0x507403099050b0200c40145031500180840038000381d01c8408943d5580320410300b03001032405408098402c500341400a991039100b00d102c8420000d0015105003540800b05050500341656040186102c4e412281c2011400b01c00e07114045800c1c80502900f0401030850014070300a03000c3c3c9003110f00007401b030b00c008104c0707000c0080034810003400141e00c00e50540a043da865a6480340071202c0c2c0c004c0c0d0780e5400394100d0340340030000014540000d005210060002500e580da01c080c19001007544201542d449444960100b581405447d13001828454003045c1069559030009504080601c2d821ba496a802142c2c070900c01d84100000071b1500082c160710001d40d8904100300342d103800034800c41003581428403c14140b03007000c06a151881c84a50354a000400b0b41da4240945078009078a46204841071441c0320f00a56650640300004000b050f05610000616009000c0c41c5828500c00b00c1c03844c0d68200c01e190140003040000388400400011b1004982040c0e4001844a030f256009000d40290044c42e541003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 337491321 1250 337490071 337490093
    0xa0e030a050a1709031b040b090103020a12050a060515091608060103020313140c13110301150210050708250e010e220e1c0509060310030f050d02190201020703 70
    0x14110f15542004500400c0c0c40410200c2d5912040d1004841a0070401e410002a1264113141c0c91155020f00018005641c9016241080302d11403d070800c8465420710700300303040c030402110180c0001d140c80d0420041d01004485400101021aa1400b465a40c01000b245141c1c0c0d045100002510301400903a003540a0f070300464104112003055086c04c5a40e41d101e071000c0529001443e096042498110f0340d0b418070240136020750071041d40600000c284144100018041441440d41040d4141c0381049042c1c02800a04075002e004032040c8510b280800001c6c0660741c0a0781d40d40a40241d00281e000d0846504d0030075600b43c0c3c0250384085421000c000110307012202c006410b540035503c0141c0920005050185a004034922400850f01386508803550b0f052a04507182c1011112080e489540000d03402002c550809001b00e43c259269150181d444130480d0300d03a0402044854080105810301400080ea40d0240100340c1c210340340702c0c050b1051142601e0406000a015a202140600c0014950140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 337492571 1250 337491321 337491353
    0x8150402090612010203150406091404080a0e1503041205040303080f06030f150603010609051e04110d1a0619030f06110a0903050c0105072102010f050c0a0e030a050a 73
    0x4020b04030000403d065003203034415901a00503000c01c6014542909090090000030508828204000f18060180c3d483c0b0250090009000700c0000548100c0d40307005821514100c4006000750681c0130155110f800994010344003038030549810981102034912030021103099940c150b41d115419181c08030004409400906010350500584107500400324040015016158442c07036540c1980c1041c800741801c6400940001040324141000c000007090811020300d00300515814440259480741040c9003a0140c00c86082c3c0c2c482c140035445000c1c8810170f40380b0340c885105413203c981c8584a240400411500c0d86490402c8049060020030100b60310190040c1060b000da034000c1030702e6001d180a01150780c070040052001c80c0d1011010b0050180800a0b4003c4841c01c0c24114a041076944400b00d50160315500c40d8140c5031b6000c050000a4403c6d080b201c194080c8a405005a080094241071300750410350082c00000c80c40f0038011880d20300000c0641c0700b640c02102510aa007281e8889650081003046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 337493821 1250 337492571 337492579
    0x1606020d0f020a09210b010501140705070b04090f140a020c0102041212090b28020a0203100b130204051e01090806011203030b04330b13030309081504020906 69
    0x100e1000d03a0742503000509000c1e0766581c5101c42c06040548074454500c3c400503d51404c0307210390444000071200a9541d0544509007042d02c07202c0c1001ca494251071040082c001d280d8000d800300004c0c060050303c064010380b45444802d21000c00d1444803401280c10101c4154001d00401000c9a04500294024641200d500c8005031400d0f8075480002c03801c08100c60200d492480348090041216030181903c0c000e824084003c62402100c4502c400c0ca01c80c036000d0490300c0c070001014510f8050300800880c1807445d80501600c14511034090090f0080c02d070100003a0103410300580246800909201320360903240c0082036070800000c40d0041c2084c00c0c140801c004d05000660f40c1c0446c42d403408009046c020081e00005150039011884c009080d1021480c00078012400e055070046d901d0700801c400d02c180381003400d4070046000030150030030800c048e961200703070031850003d54a44998098210901a0384c02510341c0c0c4210b903640d1502603502d03481c01d40c0c80c04107000114041801494180c0d0341c00d81000d8010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 337495071 1250 337493821 337493831
    0x60509031507090306020301141002071d07091d0406181709040e0307150605090403120e07050a032d0314090307031e03020f0d0203120c0d0204061d04021606020d 71
    0x5a644c4041f03034000c7c0c001340071011035080e40b0780243c544010040101c0342c3e079101034011245050f060f078641c0d4502c070a44895204010000a030440d1003800944018205040204082204544091813a0710181c40580e00315040c4003441e08a1401d0000103000765902c09040804003013000c640c09032035000021100c3d48691910045000310700100041c004a50003245920218452482c4c500115411030344034500814081c5c0400000c6074201169481140b00d9200100d40c203441106110700303003009174102a920040c111401f10038807400701403e010054000f8002c1c0c00d500c019000010700542c00070b00041c0010014403070a8022070180000e408000360140c21100c005440390345108070244070b030182845424000c0c21020502d54104590b00c104904480a000b50400c070b600f000f901c81c80341e00850b403a014040d0003c111140070715011551f030302c001c0103802c54440d0f4403101e00502c2c01c40c00c0c0ea90341c2103007880c00b804080c0e2480c0c24421100c2d00c040101407a60100c440d9540d0001030b401240c9250341c7c9666030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 337496321 1250 337495071 337495073
    0x203130209040b011701090809090a0b1e13110703050c07050334030308130c030206030a0c0206011a0a0c061d010b010906020610030308090727060605090315070903 72
    0x103022401148248100629581000780c5c8010740080d0070800b4940d07030f04200b10200419017031412101e800d1401d4403072200b15070390b009050004d011044d032042e810592000308004040b07422030142c88820310840d100c000c804c40e0742c0c01000548024600034200c0c40c40400c00700000a0240b4014149030192000b500d61056480340060b0802000d8800180c0103070505610040c07103580004540403c0b04180b0f5540050790858a0042c000c1000501441c061103400b02d141c0180100040c50704000c6a0007840250b032494103000c5a0701030840c0362030100c090f01c03903a00040b03000b000345004903401000c140080d0f0b0074800400700032184690f03241c0055501c0c81d81c42030b02c00c645560036403070880c058a1000012484422044c0010b0100c50242e004100b150030400c28080401c1c42d01224908480d05807401441684034800200d082c90020b80c09004814502e041000d150000b810302c00da10804c44000c100842c80e550320b0155028441c220743c0c80ea160f0004c0703108400540e84580c2640c1c200313510b403900b14602c50312 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 337497571 1250 337496321 337496329
    0x513050f03071509090b04090b01030602092412061c030309081903061806050612041a090105010e0c030103030f1107050a1706011e140117040308040317070e010302031302 75
    0x40c1d10f0410001460015050080d0017050040d42c03818001990104401401da4484448044060000621058000070304020a076208040440b9034520203490380500c8003034903072040b0107a010400b144800c40380307200020094905205280c1900075904000034180072075603412801440790040844040400344960940c6482440d640f89899206850014070b4904010348103503100d81401800c03400d50f05103d002d11143c0c440c5000c0d40c0200003c8110015503445e207142c2003e040c1c1020003071030351401511041044e00d50054000341c1c101c5200b424034155036129414009100e01c400d0101038007107228010040080c1d445100510314070650903059417107880c0c40d0400202e100010750b02081d60945030f00c141e09200181440b180307005200380e0240e66031a80a40f10508041c4946110f0022000c1d41251481030503406000442c1e240f030302c0c049203c030941c5400d103005810b401d01901c003a400540e88441484c0d01c0c41c480182e80703015000680361542070580b2180110083d5000500c0a100b44800844050058035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 337498821 1250 337497571 337497599
    0x60902010c1421131202030c0910031703160509190602100b19060c1106070f03020c09040b0a0902240406022401090207020d050607020f0d0513050f0307 67
    0x407840007520541d400400c8042140b001520110b480b10f20400c40d0662500e0b90045050445104504550064005000003030070300b041001c95680000303081d410400040c0144103054280d80c446c540303010380d405080861031018081110500d4450400d50008020380d40158007410f0b1107907004105c1d0310f88209618921811000a500000269006000300b40d011041409202c403001010794101c1d40c0b5800c00c404e10001c81c2c00034030400007444402070a0381c0074000201482d8400d070102030031305070359544bea00d00700d00341418640c801c1e0018043c48601c5023092a00b0980c1f240680d81200710040f6546410480314018100303c0002c0380d204007840d03081c0c80c030360101d014a2412000f504001684881c9080c1c4041d00348a10306a603188c40c03080b80400c5088070020088001d0644105450041c1c03a01c95030710100b44400030b0400050194811035003008105540001d682c3c2c0c649003410240da2190f541071070280c03014000c0c0e10045011030031f2035006120b81d040090501140d039400070212020b890303803121a441822 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 337500071 1250 337498821 337498853
    0x4051e03070b13080c0a05061e03090a021002030901080402060306031e0706080105010503070203030a0b13020c06101a030a1a0d05010e06013c0b04080714100c060902010c 75
    0x100001c0b5952200d04648950303c0000c00682e4054000565000c00060300100607010b0103100718804101c0d00c4120f00304e4605d10f00c4d07031400c1200d21652070900c200419511030301070b003049100302d02c0200011101480807069900100c810303160f00300355481300c1e400c000c0c494000400085c1c040c45002c8450505101c15803001c07100561180241a442d41065002060a10140c21080c148041001400302c010f500200701d0341d0164000324002744100c04000010490b0b411141c6000100d4004615242c02c0c0d40701242c0ba50058400024040ea6a6070302d40002c0300600d40111511800704c02440014449000d5411183e104000501c4040103140d075840010b4039030038040420381d401c5c3e54030b4481d004908400c000d1103000d003070704400303151103c0d0040e9452a10303d41c00c90b0300384081c00c0c40520020329440303000b0043c4000c7c00540358126199500c0e01c20f5156100040e10072116203a840c0c0000e8035050421201e424051015a56100d102d003020f0745a040182100807000c07810006400e034120301080c2c4c92985800381c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 337501321 1250 337500071 337500089
    0xa0b01080105070201060e0f060d1a07020601150909150e040506010806090a0c03030c02031509030c19080306010c03170a0f0f0c08130c0801050903070210021204051e0307 75
    0x5541019441421108014407403015689013400a110098211501d5035200351006c101030700030b0365120045030b0280d5200b84018002c1c1d40480b620700503d20400350240c8141e0303041d4211041c030f0317a0303411424209454420420300418241d460520030428180c20080210219501d400c000030303503038030500d8141c44044a081e07503d500560010300c840681440000d030400302c21b10080400c0ea559494207480002240320040a018a05148504545051000c5c51940c404505020f43c00e240842d03000340c0701e5120107079001c00c0740980c00c90703e91070300041745914019503048021281180c0d00d4000544d00404150000da0600c40300c2c9045030001202000d21038410344543c480820501554544641070310409400200700c281881c01042c83e065002070000e504c440c2000d00340c40c1d40c01503801c00b40000c000a400683c05942000100f08408a0010040c000c0500c20398044510383c0f180b00c800c0b138540c0300846c00300ba8030343c900700300c01c210500d020181149400c020315425903d031800e9000007807521015900a0404e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 337502571 1250 337501321 337501343
    0x3160f1406010f090b0319030809010c020307050a031107030f061506081b0d0e1005060109271a061206130216060903020a0c0609030204110f0306041d0a 67
    0x800510610903046080d040c4000c0006504000c0c00031030980700e03409410388042d40e40486003842c0e0380420845601c4c13140741208520981d00c6003802440040103d603010400c0d0708242c203030028030784008100c641058220000e0080e8031282d03501195100071002e502140391140304404000305003007168042c0820700c18400041c402150208006103920360b40d106a00744013885081282c400700039030111001e600c50062084c3d4840018080000401c0c6817100400503104a032180c03140d14240780d000b40e000c0c40c000d80b101d00d8219501e4007620310205039001c1d40c0c010340821510760300c80803181c1d170000100b42400c0b02a8024469600d0041020341e044207401e0f22080c0c10035003d02480303043c080809941d00c2010b180942c503100c14040d112131a00b890030b070700038292030b42c50814600341032090180c6412158406e109021036580c94000404040a50000780d220301e01c1c0041d0095902555802c481444c5181054a41160b4800d000c110061a6484c01ca40a2070082d001c0d40c0b9000c0c0301030044584c200e00c6242c2100d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 337503821 1250 337502571 337502573
    0x3070b0c060f01030f11061e09030f010203160c1104020c030d110a020a1b030b0108030301030b0703180f0303060b13060e030a0201022812082a04120503160f 69
    0x440c00c00054040c2a02d000158018808108100705000030290002805200c142c8188041080c501c2148014580c1c0340990424101200c4140d00800d56528124215440f403c2ca15949a00b00d210542d43c0952071016040444010b40c094a40125554010150581c06680e1031004c0350a0383c3c098220018503402c00204410381e030219104121754040d115042c030f414030800100282d9109801d04001d0a00145054207001600c0c51201d81c130051a07001c80700c0119565241c5101da541d030802e02085504106410005181074464400c502d440720542191189440040c0c0390603032403484250f01541016155080410420840c400926003480e54640040d8100d180c201c0040240c56085500751080d00615100d83c05030fa8000341101d14814094042200528248107010082071002e0340203051603170f0441c508400540081810744101d058a584103184001c409480d51012500095035500e07074020b105c14004400340e200c4080c3d5980c4500c0c1241d03d8a010244001160b10144208480c41b0f064005560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 337505071 1250 337503821 337503823
    0xf0a0b1f0f080403020d0e030a140d26010b0918090d020d0314270d0207210c03120905040e030705010606051e09011b1b0f0e060f0f03070b0c 62
    0x2000395a10707100341d483c200f0b603400030744402c800c0300c0b84e2082110300034414210355418001020300542c020841c600210201c29090b84600b898440704002c100e681ba07460f00800c4e41015035a441120701c3c60350884903030800440c0c009030342003a08499040340764101841500311141c0702e040d002c0c62004d4010b012111842400038a800864400d100c1050300b00700407007a4000d06040301d01d03040440b402041c0725002e03051074606222002403400c51024031600101000310f0390041000707410f65100c800c14503d00103d200201c40b501d000c02c8001004641115001c00200b018502080317444440c52074000300c40e0340c0e1900040c040d5a20301c1101c01c0395800000e84101000f07402d200348001440c81d410b1450820f03141c02c060104910600030001c50343c0348005041d006982c0b0906642c2c4155101d03250000064940d818070303000e61840000607003031040034886c0100d10300420007140c4003221440601981c181c0d4821060004c00500708a00c1170304602d110b41210a140d43c284880c1b0054090002001d07140c20020b03000c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 337506321 1250 337505071 337505087
    0x62102030f0a0803130305070b07050408010531140f100b03060f0103080a02070b2d0c0a06150f12050106050108190e0c040c120b03060f0f0a0b1f 64
    0x40720039548030150280003c1d01d203c0550358010100c2c0c084984000141c1001e42c0c441c400c0420003400c1d031030000c3c10406100d4220001d0826242080d00800c002e80d03034002c02b074204100344d02d805016400b1446411050700320300104404918820040148191070007501c0c0b40c0341406040c05002c554000c80d003003c203a20107034400c51215540c120f0041200c1c1c148070101c220354100601020700309550018181007103a000b0400c04000b081100c810303a9640d642231290b88082c000300510800402000ba0341e04200c44424015079000c0d0056001034042c1d1240c51382c0307800081000b071311584402c403040600041d20b507040c032139480c0c0100000c1180e41c0c9800258544603084944d207400c4139041c000f94a00344600301030001c042800f4005da212001030058480e070f07461898000200240c0798000d00f090b0f030340004960701c60310041c14098645001e100d0001c07903400301078581c54112480f014450341c040020345004a07011100350000719440000400c40403000103d00e9000d580c8150368071110001d081c150560303a10200c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 337507571 1250 337506321 337506343
    0x9050901140a08120a1d3d0c0b100608010b0a1106040f0c08030f0a050c01020c0708071509050d030f050f030c0304020a12030c02121221060d03021f06210203 69
    0x6c12905003003480005076031f140f10ba8080e00c511903859496140ca0140400b2251880001c480c2034803044020500020070b903481a0f0012500700d00113a0104482088030350218090742c0d0309882d1411640c0c00c041003141c460b0410305503481001100480c03030207824020b100d4103000300d00550400c0200d00d9142171141c0c40e0440759001508980c030400880302c40013504c03802c0d03540515180c60003540d62003d03403400a02900842203028824080d14400280940000030090125481c1c500100d290014600c4152103803000c80c032a450f082603a0102074400284640c840d00c50429580c20514240100004036200c01e4108481c0000444000000e001c250308e4071105800081c00501c01488010300581e90003007143c04101002809540608960403140c01c06012180418040244540d10b0309881c4028807094601e41e01d02c0030082da081e001217000c40c107007650500f4103030b901500142010201c2000b650090400401c4059a80e039039444080740d4080c43c842d0032181021078112a00c1e4090704c0380101402c04d03280200c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 337508821 1250 337507571 337507607
    0xf0408010c0318030504050607030905030f0604020f04090f1101171501031b0f08060301020409140402040501090e030406050f040e0403180602011a150d050c0304050d09050901140a08120a 82
    0x440b903c00294008202c2d0706484058407940e4490890b03113002e0361603000c150442580342c043c0c0c0080b80c0440b0400158207101324002c580440f200010502030000b101d009501c060820700c003c20806c1c0105c0d0101c43d103101c9a00bc1850040c0c20049861100718601d50181c0d00e4950402c8407480011041d070745401581c1c981e00300f94181490720100948090114140d01c10f4441c00d03c982e01000134040c0d9420b50603100103106868003031100444412869882240450f0f040b0300c41d43c580f4002141030110f620071501c01d4200c4100171031405080c12030603034003904440340c0e001d0904820440843c0118214142d540120f12075117900000c1e03202c1c0454250b041025820410031680f44c91520640c20003e00c54442941400b503840c1403907014411100d80c0c040c89007a41c0d51001604140611818143d02801144580e0095003610f052501081007111382a843c3c2c8a0558011005801446254146008a0301c4a0001404d501c46a6501e01ca500d0070b1500f16945104140d80104410f00d400da040b840015103c110f0503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 337510071 1250 337508821 337508861
    0x9050a1415060102060114010e040f11130b031b0c011b0c0302011a06030109020f070804060915030c0503040b0a0b1909140402100509011404090c0e0603090715050f0408010c03 77
    0x18146a84d06203c401c1140c100034280e09e10310b03e01d440d6540a041c0240d00c0504c1400b1a5156101d903c449510901c899256101d100c040012080c45220599009580700d06040701c2e51184ca0800d03105640001030780c000c25541e21079102c04807011039401010030040649600e80903088609019084a4540990142072301040042e84070580c1c801088a042d940c1d40100162a01c10300e501540c4d2130f00030014010110200041d011419940100c1a48119480b2404a891040103e40100c054941c002409030100f0400c1c408540010801c48681e0703400100e18000145d4851020001802e11503208101c000c0c0000b500d20a01440e00d00d8012030005101000d110b01d41810580d000c00c0c440704094803004100000807901402c5684a22254143305401d0159a61902c0c0c03141e1182c00145145e41c5614081205a01c522a09003000d00682e0300c07a030a0310001c1d1035010b140190f0014030004c40d031500c10070802c0400c6106022500103026001038017121000003206024100060225000c00085201110807a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 337511321 1250 337510071 337510079
    0x60302100507050d081f080106050a0803040b040e060d0b0a0b131802060703090e010f0501030c080408030f0a0e010c18080a120e0105040f080619051003020409050a14150601020601 79
    0x80e840701051400e2a00305c0b001c5d900c803290315103100b5807074002030003890f9042c03000540c9640541081c800c0c1d42003150564a901d0f034400f0301c240d03070303118520807058000803c1c0020400010907a1409902080103000c0c2518450213a8403c004141d045490b1500f00340d850011860320300b06240c03900400c1103210010004807129449184200d402420000e100307020000707580040611a0690f2070043c40c4444148206585840d142905000c030340c024140000c0c64480e40f0380299108248503030140f84c00540c01e07499034540810b00381724200d000b05200e47c05519110310301041030b400d205007825a0b00d02d581300001007007c1615002c10f521507031300080281d0310540994000c00c000100496694180382401c0d00c6c0d0624810060346c590185520140c40c0c0712120b00005540e030808954a4850071080300c480304600c614140c141e08851054400c100035048000041c001414a0383c454030110b4026011604003030341c03a550740390300710701850103003041368001d031071006903c0303010803120354000c075090020300441d6040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 337512571 1250 337511321 337511323
    0x50315120c040b060d1503031206050a090b01020a08040b09030601080a1101050a020a050a12030c020610090e10020c0a05070b070b040b061f0914011b03030b120a0606030210050705 79
    0x764680061080703584010812003980c8900c2103d80c040900c85007440700c0500c82010190000c02440194045117030525410b1000246101d0a400e5550040885400a0030a42000000d00180707980605503c140100b0130042124000508018a41c0c2d01d40c45176140001c6041c1030504a046c0e021035000e41c00080c50000064404c03084485412081c07070300d50749a6401c00c00482c0341c0741e0882409801802041c1041040c1706d1200d24161a591480c1c44c244100d00019504990b541001c980500340c0c511510001e001c001c0440e049154a00200012108041a0001928100d03404450440440d038441c0b03905c00c1c1080414407000d030042001c80c4242d0706010103601c820440802c0204010b04462494000480a99500841c841041c85080c035040240488040c060120704141c0180c9454408904940c0b41c03c0d8807030450004009401c001100c010149aa0700b03402620100d00c181d507120600141e04815407030100b20807030303049014401c042001840c41c014070110055403006e81003007100c1001a02d021801c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 337513821 1250 337512571 337512583
    0x4050a05122107060615020604020411040e0c040f1d0103060b060408030a02070e09160b0f0f0a0801030b0a0e031806090a09061e061b050c0d0305031512 67
    0x905441510000035180115400e0090b0a00d02c0e5000794003204000c808414604042c10105101e61410842c8645031104901c25142c0703d40c8090040e07010500040c0142096000301103c0100484211306060700d541c00c0206522003182c1c07030000800042010400c20a0503440c503001424201c03020701c18a403070280400840201400080c100030384030003451426442d2241100c0041415505580e22485000f100075240c00c1c0d10300c680070801e1601c0011901d00032021404002c8140c142e42d800d440140303070005111a582001801c03105082d070031b2003038a2007207441c03000400d0380e000c1c51354501e80c0303030b44c103524050350204005404c0c114010301d8260540b2140d0400000c680d00820414240720501c4001c500094071403055400d9590031122418001440030f4007904040b041e110851021005441300310184900100c00d44580400036504103d5509a001c40306151140d0358003990603244c0068140021949451440e03a045000813000800c102c2d90000043c1006405803085a410424503040040b403982c4103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 337515071 1250 337513821 337513829
    0x32090306011413202106040605010f030e0a080c030c070609030305040302091906090902090108030315091b03040b01080d020f030901050a09090903090618080d08071709011a030304050a 81
    0x30b685500c60501501d00a02c2c02480d0039108000303590305c40102d110640795043e0080c0c1d003100a5103000c041001840c00f4000c01e000d95406943d840303070849008070210080d204d41d00d034054140c0150800e07807011540541c020000f0310a82c10040d0f076201c0031588141d00c5c0c04482d81c4181d00300b0502c00814000640d01904807002c494040721503e0690f1140138002d442c22038007051403004103240c50030000c1c0c8a03045402032007501d402200d4604c001eaa0b5070b0710703440d100c0c0710071a070400307000e4418100020280380c00715685c0d0f002940c10a141c1c00d06a2280c03c12013050380141c5050b6102d44084d001000302c1102081349015440540c40503012803d540516250b4900606c4891414480c02040d060b000d2803090400710024400e000080c0031503440c40c02c0241c010b10580c003c2d140010520b05080001c940f82d210404203c3d408000100307102d43c450042100d40e03080280012b000c0090340c400e0f2505031501000954003d032910000021124030900e50068084030f0120701d5402030b0000d2200300416035035480150b0440d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 337516321 1250 337515071 337515109
    0x8090601240e03060a0605100504031e052107021203070c090b06070503040f0503070b04080607030207230c030c04090506182e0b060c0d320903060114 66
    0x820781100c0a6030030381420180345415104c2c1d001045004440d42c1c002038200c0c3c60a40317445522603600c0d00219003910450001030011290f111000070000c52105110407a20f0098065504000c0c00c600100c106020301c034040c046807440419108150b180880203106000c554000451510442d95510f41d0002c040f0b100b1240119581c0c031613032510b07889620449240a41c48015a59120f4490b0a200b07000301040c0900c80c001c0c03260140100b0301c9540c142c01c840544030755800802031030b074898108130065400300108540400c43c050101d43c068080c0c86c42d405568000c2c002510b0811501024540f410010ba42c44502c22130601c8124404908081a01500403102c140c004003962035110f8442e00c1d0040c00e130924000ca4400302000241d4896000701a80b00c100b143d07205020052280c820040b290054090010803908035036100058280606500c181801c0700c04250100503000007030441050656041f50801c80c000050170800314542884104c5c05881c00907191070030380c040e80000c103031080001e48000e004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 337517571 1250 337516321 337516379
    0xc12030207050d0e040e0f150f0613020c210c010509190f02033307020a020603010b0703090317040e09060907170708060a0c0f03050c09130209031005040308090601 72
    0xe031290f80040b40803c446c103080b99040c4640354001307a03640786440d41c0309120341c01000115140c1c1901c2c105181c01038000401052202d10468046c000a600908258a451050130300c15151240c041e07405c80b500003290200701f0384840950058600f550002064089550481d02c40ca00154129203500f4020640084444120401d20b201080c9040d10018400481903286080ca48030194800000340c6445622000002e20703485007402a1f0740c0d2100080001c2d8411014030062010b90080005001c0045c004d01d044451503a5940720803c16004c0c050a00c940322600040511201458610345038001e0054401403440345070401c9800d840d601c0500499240b66490f130000f1440e00010030032000501005810f0320414101400040002c2200030f4451000c15110000c402c2c156000c4c1c882c2d07910031002101d0207440c0415020400079410700d0406400c2c5440d90a1080342840d89081041382c071340744166500060300341498100034000810040109543d648054010310000344083d0000040e0102d2414002d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 337518821 1250 337517571 337517597
    0x2040305010e0706352d010b1803010b0a0b090406051e060a170a0c0f030905060c0901110a0501091403130504050a02250201031a0609131b0c12030207050d 68
    0x3412049801d0100c05c0441c81d000d02c84290102800501e8504a8829112101022191540089000f441b0b00d00e015441070102146078a00303410141d09000c00203000180100903031001528200039070300445000f03d00420b1030300b0a82007034030a11000d03010444400f002d01424420302d40c48000f610803002d0280d072000c180031540e00d0064500b11032521000104951602e071002781d050003054042032481c0041e10084c001281d1318043d1041f40d03803082c0c04c40082c12090b074440c022100035501c00c00310380d070420000b02203c40e10368405102c0701080c60322800010074030280504003007940c940442601801500104996008030244148410498800b502c2c0450641c2d1000d40050007409440140030303440c007505441803e10490700000039074040c408d032410414100381ca910880030721200780f4115080642004607260710329101d121055182e2000b28089144000341546400c0322004400c0035011580511000c0c041004800e1018403440300c52070210b0810319162103440e52603812029003800c0c420401c01002c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 337520071 1250 337518821 337518887
    0x5060c09031c091a031603110a030c0210090c050a0503070e0103030804080f0f0a0201050a0b010917031b030319020a050d05040507050307080f01050f06060f0c010b0406060302040305010e0706 84
    0x340c014034070003070035031359000c2010011149036004441c2903000d4605450360040302c0d0b00034403e020504042e03540c3d05042515801083c0c0090088482d0b41d0f0940c41010352100c010b10150191040e000d01ca4901d00100a1421091050780b181680015101e600a000b0500844044200e01c0d03044a401d4544461541c891303040981a0384200f034060102490002881031a45294000920441165038020080707540c900c01608100c1d00d82400f028006856070904016440018400d0280c040041c401d803441c0444060313500786014054407841c1a140c101000300150300f8010303020860360220841081d8509000c90000411910920395600703403056036080844d0600804000c1480605000741c22110640c8d01d07500b40c1075540c2c001441c0385280350700741030004548031109070b001c82c000d00014000e1804c04040480d21020758000d02c0a1041e6990781d40c40d000f000d655035004110051440352001a9201d046060450070b50701400c00c40905a0b0140c80700f00501070344a0740d40b000d000384400300f42c103414462800349 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 337521321 1250 337520071 337520087
    0xa06021513060c1d0409120509030118062c030406050c0307050609072c01052e09051215160320131a0f0706060b0706050405060c09031c 60
    0x41d08103450440c1c40340310303d500406050182c1d0f525008601d0a05801d000300019550b085200800504694403103004450007003025151144004001007440c01e040c80c00103100c41e1444000b41c42d9140c4400090001082c3d4008480310302804c41d0420b0075003800c6c070803600e41c1c900c5180304c0c8408100e000610708480140c140262030300f0035842400d441351410000303030b055501c0030140140020052039091181c4600c0d03141c0003401000c0c0071200050156031030f0a00b000484400305044a00b5100c25060102d07031140f6090003107110698580341d002c602350034a0180804011089030301d0f4159880805040900300500b2121a440040c83c40000109150401c0c01c4016210401510341180540a41d030440d121140300070f400841c1e5500d00d0160003540c2e070644c11035000d1500c044d03010421030420500040c01c820200419540d0300805010070703403640d50b010714080c3c0e6022180644419036140b050008201090100b2070700100035009850070490918002521105e84194100007210b400c2200c502c114001c2101c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 337522571 1250 337521321 337521323
    0x807080d0b090106050a0c0b1b07030309110109080604020f130608031815180409080a02010c17070512040611030c07120c0f02042f07020406050a06021513 68
    0x106469150a4004501a00081c558584200c24000003ca5440e120304240c48104a81c1e6841d141805017586a10001800141460951060b14a0806c00140040300101405846980c0008042c003140c01e15040c0c40440c04000c50402c030005104005c0c003140020855046a01103600d20f041502410000d02ca5001402052401d1410410001002100807001e4040660002c42030420901070385c0c104405002c0ca07124103403607100e06000302003640110001c10344002c68050300005120280b9160410381d500b00b0000c2d400140e440d01c4400401d40e6210301e90101d200b46c0000800d07224104200701424034011603c00101d5500c0040c002000e20402d41c00220400070100c2c140b55490602044070803180d1700c818000e81d9420440c000e96081e4921544601e1004d5030404444032801c1d140b0342c00c103c0a01400030840c840500c03598601e24201c1032002800007038144d071120f4036075120f00314410320054807000c1d84058494400080c0805c207658011600f0840041c0a104806440e80c0e12909110070f50100d8070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 337523821 1250 337522571 337522583
    0x90106030b180a1d01020705030f0f0d110403061803021c030209040606080103020907020c0d0f050102120a05091204260a05030409051012031709031e0301031e0507120807 75
    0x14442c4892180e881200301e008405440113004030b184480f18283d2150041c0100030750300c10060420f02d4010070300501403020f031800805141204440c411029208a140d4401c1942c9001400304204181c501c503841c0710403202080003030241d980b43c90180d160056004001c90072900301c0350007130000e440380c1c3c1220b41d240d200030000c21035552600300003082c200013404128050303502e031000300e00c4460000ad11415510401003c0030000c20035036840b0444404104c50484640d9020300c8511104022250054410340c03032244001041c0c90010000c9103029819034803000c903400104000c0c0b1030901c540120b0480c02024800c4502c92500356544280703480540c00000e031050002080c0428070304401d803c810700850711400c0d110306d4141c4032a840e40074844002002004a08005880f9103404c1001200e06e902014641c280c0382410034142040643e0110100c1c04012102c0004c014001c02600010381501c0c0008a00301d00d03803041d0b41c4e43d5000d03035981c418029083c46620300c01c2000104036055080310302a640c461 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 337525071 1250 337523821 337523869
    0x151005030a08040329010b1e03191104140415050603010306090b3106020f0409140a023c07060b0a062c0d02151201050609090106030b 59
    0x10500d00029005400704807050f9003c0c190050b800c10501c005d8001c0b081d49220000c3d0907910346080181641c0c014613441d400c0c14085040010041140405588512958070302c2c91034810300c07030102d18100c4944030044000c103682400103020003c1030035000c0c512046c040c0e40000d056288050355801c2568580d000035806440017002008001040c2c012a040910851484003140c40c1c420390100305c00607049081c028000707002030310311a01b08282c04200d0418020100140382c0311450018a445900c990004814a61225155000c095412106a0744402880011070800003e420382c1c000004100c030302070710a40d0b000c040d0710f4143c11900100800050400c00d2082c1d03075483c14a0070f400a0544101c01500c04ca0400d82d001550500405400307901502203014041500c07817441c00c03840900c14003075515420440f01041000140c841094410307a115050a0350b41e00e500c005c07602103051801c140c0050b400b4081c10301c0380c01c16613200e0440355410740d0401d040c0412140b05a0340840c0416031544840c3c4482111a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 337526321 1250 337525071 337525073
    0xa0b0f0c041716120308090604110418020913030206010807050a0b0f040f060309020f1e01030c0c08070f050706030e0307020f0102210c0106090212150a090615080601020a05151005030a 81
    0x41c60130440c840e40709845441031030b519810003d4031441e003190060b01c80440541101058501984550a01085408a0f042d8001d0703640218071076403401c41300300c143c043c4418064070516804020300303401403da510003450550f00305030102c0c103814440d01c68041d06d407802190f0341e039104035004140c6020b402e03103000200e65181c2c1d410008014140700fa505074010070550300d03948102d05100c02d170f00040e2200030b80c00c4002c03442c0d0340d80110014000c4445c3c0360100240144000005100717007004004041c00b1300150f50400c26241859400c007815503002c00141481c28036104280e10012055900e903d0301262190320541c60880141d00b0160108070510200080141202081c106c190142071103040c4400200070440d00c94130840124419541404400c120a100080d00c00c0d100f038080c0380d990030b40035140400b0342d65100e040c0c0707081c1d45181d00894845201100300160f00c690281d246640010244001c20f9000059160103448000c14071851030b455070070300001243d20764000c0401009203800790440b03000400c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 337527571 1250 337526321 337526339
    0x30709111801050c1b0d020306040b04030e0316090c030b030610061b0c050405101502070303260a0c1407030201090512030c2b06080a0b0f0c041716 65
    0x1c014149a44941c44911030500d521a0040e030701e2580740341c0020f101070040e10800441c1d91400f129501c0c3e2000400340140011b031818000035000390b00c220032954503400c0c0b41c039014250301030300380d0700d11b00070382c040741184080b10044403044040b10007003440010303003140030305089005d826803d00e0a0703010f110324000c1c49900e61480c1c0200044405036034a0b84031f00d06001386101c00548013242c000d028500502c00034065071400e07030720854006030403118294040c0da6401c103c5072021000440d503800340e0088441002455002060913240c0a4007954401003003880d10455034141c200070b00b80c1210290380e0074000c0107584c007900782c107003051a00c410f01ca0b0301d80601c1d00d0024041d0964500407109401141880a41d180090050f02e00400d03002e070b1864140302000071100c03042e01c031640300828801c408107502080d215035441814080d10301c0380003910b82002e02d4240f0180001001e8060080600d5070b0307040148504444084d1015a03d00700f00f00e10011901e00801450b105020004c620503910b100700c005084c1c42 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 337528821 1250 337527571 337527577
    0x10b1507023015060109030204021308011e0c0e09130c0302152101080c060c010f06121110092102030d020f070602070303090603111605030a0e0a030c0506030603070911 74
    0x2448011118a805150300c4038007003c100707036901030204811140c2440186400d030094a03504a60600454103190b03140f014030700351940050340208180e0745440e10242c850721400f50030306181180c1041a20350510f1408195800d20003080444d0301c40101c6100401c01c50a06075100065030014818101d81c100c8283c040d460b41c1c059004503064411114641300d0200360704c0446030481e00c06002500e80072a006042c01030302d602c040382c0080715560b2654100495211449800083e014810001054100380c0c60f000c1095422101854420100340c9141c0c03004941c45801541591600c9560842c140d01c290001c1e6120000f0001c0250300d40242500d03409590b83c000744070800742500e0003c4401c0e05a51f0801680c036031160f40000380001e0320142061207410300981004d0b00310310b1001c41042c505140398400440d1071010300c00480d2a900000f450b941141d44c0a15081d120981c1100e0038944141b41d03650322203400d0070038401d40303020f40030100000b00243c0c0e0510001c4000c01d441c942c203129604202c4054a0306038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 337530071 1250 337528821 337528909
    0x20a0c080d02070c2301170402090403120905100b040203060a03060b0319050c010f05041203030228171509010e0a0905250e15040504080c0a080318010b150702 70
    0x200301601c0c640311984100c2583c4001307c1000069003650b02e8a40a11940410081064062081c5c044204034003d84130300c100903486009034060301480c0c0b02e4620381c00c103846d6144405031180e401072007401b28550b100c480340401c0302d40c050b40026005c180382c40440d061480718842e078088e001440100380c05118012813500c0160200b603840700302518524a040c0c03020f00560007058143c500c0101c40320b0009001c0da0013050244c00010080c10202a11115a80310090004c10040085d000b003800392080388040e042643c01800818000c2c1000441501040d045001442601e0103250300e00045100421241d00107181503400406a8220803091500b0400540c1645a03c5a0b14480e00e24001345400e20451814042d034000242c0b003042c520380f1030411004c0e00e006001561948420880104819003c00604c01001e20806c1c9060316854030f189610613900d4502200c0f06940d060140040396507440b0060818102c04001c41a62214210300100e10751607403001180416401d41c0000915401c4940521105c42d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 337531321 1250 337530071 337530119
    0x40b0f04020a08010e09010203010315020a090b07030c060c02011e090c050a0f0f05150324130f0b0402070809011404120804050f0d170f07050303010e060112020a0c080d02070c 77
    0x40c1c46e0103010f54200d110912000d0040031032940501050410b80e0000d0405c60120f00c1e00885d1551140703030315055640440021404a2800005681045a28082d68424802d140020481204200724004002240104500c0ca099903229810100800d01211801410018041d8580e458480411b02680d00050065410100710000000380501d486441c100705030030a2a40c007411901e8605c54060a100f1000c07000100c2c005283c07180d8101c1d04c5404402ca4000404200841e0440e40080740108940c071681400d4002c034010002e034804601d444088861292081c0780c0328060200c640c0303400c28035018a400c05440c00d01098901c07028071415130042c0041c1d4600321444607800d03c81d0010000d54a01d8044010100b03284100060f0b00c07201904098881c02c6d82c0c0b440b002e850007400d503403840d007581e2091b04100c481c10100300a124042d6400000c0c030980d45051607085140a0844034080c0400056007401800d514000500d505009600d4054401e0f0720750140a01901c01d0b1034242482c5800e0544840d0602c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 337532571 1250 337531321 337531349
    0x60d170d15080a0c03080318011407030c020303061807050d0612030e0103020c070504020a0e1206040b01050915270a090308160801032a060906021614040b0f04020a0801 74
    0x5403480105115890f02e0388040d0001c4d44078034603a02c04119400080107410b50140c0c42141004070f240a000d43c001c16000d40410b904c0d603252949028003110b009061030700031035200b841004219200d03a060840000d0480d60070002503074840c0c00488040c814594003201613030038440f00182d0002290401114648240c9500e80342100c1900114101d0141480701c1d072440d03200700c004105605140c1d00405d0341041e03d00e80484011441d40109000189055a8040a6102804001c207110001034440d014200840c2c0e4440203080003500380354940c04103488180320781e5400c0c1e0300d0240da512510510102c1140c070740a408062404d4900300d002405402d800382c02042e86840000d0b4159803c0d800c0e0850a02e40c0d454070a20303030742192075000700104105075007100d0046480b40c801a07403407074504034402411180c0c3c4050030142060402810f100301d4603000b020b081089a414070080e58135a075100c100c01010703180000c8070490000011039036001103140c0c58002c0d2002074070307000080e44000000d0680b0100866562 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 337533821 1250 337532571 337532579
    0x50306060607240c03141504050a061e031a040b040605061c0503030712020405011205040602091f0201180b040212070312050a09050901050d030503040f0803070305041a040b060d170d15 81
    0x7045400894400403d004881f0100880317140640c0542c0c3c101c050b4040000d603003600e40d00e1005d0200002c090345518074540340800c00802558904064400841c8000d029103801e02d40d4a401440344040d0006148903140c00000304542c41713420f5840c00c40281c1084502c02e84020b0f08003a903d90f482618404001688003110801d81021030003160215041a07542022100e242014000209409407003107071025000c201403850b56582080103450440d150395000c1008800540203421154100c2e030700c034a115002584a40800c081c28400ca074001d40584403078000e26040005242011201e800c0200044862001c0000680e4000050f0a0304181c90321421585074a48c000c03c9a601400d118059001e8003140b640c000091060020350b4003d803040454007004411580c52107d00d8004a85100c002990313101040f080c000040a03004225644680c21101400c040d1149588000300820450003100c80100000400032016025180d90540040840d100e5980700c81c5035003d049003020b001410700780c080c0081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 337535071 1250 337533821 337533851
    0xf07021c030810030b0114060904023004022b0c0305011a03060f07050703090b04060314060d02032d011802100207061b0602040e07081f050306060607240c03 69
    0xf0068a0700003030104540ea03e00f90308038403080701e2410f01e2504181c061103e8506a02c035400075003150054074580240307400e24090070051103800c0c0c00d0440e20344d00200041c4405a22407180c0070500d0845818003c98403808401179840710341c182c40004121401d0110000140181940281580410079100c0080c80842c48201590740380300741e80e00b5000640030f001040520380218000d00d60340c3e00c2400c00c21242651130f4107000c0541c2090b800100400d80f5441c1620b008840340300a02e41c084c00465205105041d0340d00404d55540c009803684c0110712000c00105000c120301e000303c0e2014541d4000138000d031411204000c07017102c0707014802c81c001e14801140e100d6079030011851009854013640d500c20400e0f80720b04d41c1042a004030300e09030b038184d5080102161075806c0000c918400c01a6858401142c1070907201c081c031600396185a00c0141041e241c05200690300400e540e038000b041201c0e8191209007504002071200b8070040f000900315010300000c0d002c907245d074102c55116100c0c0d48040280c0c650280d455 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 337536321 1250 337535071 337535101
    0x4060b0703080f10030206070b0105040f0207050d210c02030d0c0207054005190c210608030406020a14010c0f08070e0301020d060e060301200f07021c0308 68
    0x1c022400c810002401c8008400c15264052001407448440355943d07008501e00e41c0c49500185c5035580d44000500040c10f01d40244100140c0240c001c62800d60103403210703504c519000d10039070100720b090100d15002404514100100924403a8100711550045101035501d5000c51981e203031003030070300b0003816005001041c070a04989014004619900b04071103251008000c03407100c04030001a17038040303e003440004800071004e002103250002e40c0d03040a13800d641c01520146410303038141d0b050960b03102c41d840e071003910f0742e903020311503110901c0e055140c080c108041c0809800810451002040009001d640080c005400c0e9020b0b642d90700c40c2040c01014a42a03507010b40a1070081803100703000c0a4441c1c8201d120581c000007078501400d84080c84400a403da03800440884500e9803038180c2804000710611f01c0c1500004120000c11081d80e41104186110500b40e00e080008040400e030000a021400308030340446a00502120118180340200004003144020990000b1904400115401c50034507803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 337537571 1250 337536321 337536323
    0xe0910030807051501060c02090f04031b170a0215090d080c030408130326120c0c03070f0b010905010902090108060f01090e0906010e070f09031704051206010504060b07 74
    0x69040a055803595041d07940110300031140742c400c18910015200d81804164060403d698540300784418070f004100c0f085001a00d58405a96072505010000313400200440c5480c60801c0740d164416004d007840185001c00311203404004900281c2c240100e03602041441c41d46080d07002d403220548841081d542d8071400c0444500108402401181003002003101a60344603101380040f41c9081c00c4100b0001c040030040c3d0045030f4490b08805005040642c04803012205c030001030401b810b00340d210841603100300010302010715041c0009265003000c9001d0049034580c9401c40220340810406180130000800d091069006880c601800800c1305c8225000311403220005945011140d180e48082108404500c0446410300c86000300020384e602010107940c0c815030210020700380e00c5d0f00d0b1141c400d52a010040140003040000070940300701c140c004200383d05583c0c12200101060a241920031018403560b013005a000300140d1104440074400070306107050f95003e440c14070609a0350008140079010b4400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 337538821 1250 337537571 337537591
    0x60f15020a15020904020a030501080c01030e060f0a02040305060c0d06050d0203030909152707030618020703200f1b060405042003040b040303060b03010b120a0608030c010b010e09 79
    0x850740c0042440e0504000d22101107210040c540b443c3d000000d0121b03401340c007124011030b4450004000b80304003400003051200d130a08050180e0101041071030348842d0004d040c0c00d5500307420340204456405030341c10f4401860b4004101c1d1414100468410301541120301c90300407060406201141608000001c003060a0303001d0002d60800c050b050800c50402e60042644040c0d04100003165503950b1a010751090036100091440480d030800c0c1d084061603d00140000140350600c5010001d89082d9090724170300101070240140c071039459203000c56020b00700e041020741000108000801c062404103800c1c0b058115201101e4080d00d080d00420350b8440141d040c20b034007240c144020841c6082c660400c8810000380801c80e49492104520f07002c25810545095941143d82c004100405406103c0d50000e403140d2070314076003158074000c074000c050720900da5042c00950030000440e100300d10b141c100708044d00007407003540c0d140c0341400c4c4103d008214641d00b460008a0340684c0e14141c2c18005083c90141d00020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 337540071 1250 337538821 337538833
    0xe030310030b1b04170a0c060509090606120c0703030b030a12020607090503030a0c020a0b041e1409150103140a1509060b09060f0403080c0309100206161d0a09060f1502 74
    0x64a5241c600000503402040d0700666511200140c0d044d10b006008e4402d80d00d40c1601c1c2e070103150501c680d4900c0102041e008040030404051000c0c01d1806070b0b0350000c044c00b1078542d1260180b804a018003001c001d4190103104001c44042045034803015101d01d070809034201c50702952281022900d074156442081d8043e0000c10051303100b00d2240e00e82070241c1d400034080c40340c120760318501108654400c1c0c1c00001c00c840300340805110f280e07800d5a58001094000900d54817801140300103815403001405142c401502c41070207411507400b80d00540c1360401080c00c89003480c070f080c01c9010090121600d400e03000b003007101e401040d24901071043e1000d6400e80140a070800700d0341c005015003a807224a940880200c00e21000000400e014000c0510180003000396491714000014440210040b40310401590044002c01050003660050426001c046203031a080d016401001040c10710080d07090303250803218041780402c520120390041e03000c42d030041c0c1e00d141086644407441c3c0c401b002107803d23030340041e0498 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 337541321 1250 337540071 337540079
    0x1092a1d030604020a0b22090506010201060609080d030209040b100c050f07030c120503041502030c0105061c0f1104151a07050303071202161a0c0c0d080a0e030310030b1b04 76
    0x1001419208030502803503039400e020b10b584080c41464540c0586070340703034407a27041002a590a014880040c4070740e040882099050041090319240c41c2101c24040640c003041540d0300307a4860f003007003507442d0000d44555540000030000034824504050705442c0303445268402c246035400001c41004032a00245850026810840c0340100c1d03500290080c0e03182d100c103100c04641c1c0024091012603119458009580d10800d0034030850079104001c0c4024415540003004031481c0301da0380f401c0170841c0d40c42a148001d0104501c0d050b464600394040b1150031034a4044010755282e50b5024040607210015043c0091540030400c0a205101d00903008100da001400404c0245000e4405c000380040540009400d01703d0000821444086c145000d482a205518a940c04900744928a6401100300714075903140c0922508005c0e42e40206204803030821994800143c0846d165601082c0c42c14801e0303003500d680e420300c064520602c4607203010558200c901c64001c46d080c0300000180c01030000d50300c4070980c245860 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 337542571 1250 337541321 337541339
    0x40330020d0c0206090306090709140610050a0c1e150c0c0f03170708010905060f03070b0921070302120102190c020d02101d040e0601092a1d030604020a 67
    0x1c548012138008030240800401030b0307400d2144c140b0030130082d00180302d81c92030112050160354013881c80380080740c42181880140c1c1c4a070070f01030150162504210341d03611200c100407149040308000260242080d26110446211020031660b002401905054130400d94850101c00300c2d6010400000800c41e1056070350002112040c600e0a518068204003000181c1d0008514003900200c94200010f4100001840702c1566482136641000c02911501e25450b00c010119070380da1500d00954903040404211101d80d0743c1d0300803000882030b0015140c000d121000c944107554070700c0c0b00d00080303214418507500d0f0f110564052096071f00c1d02c0c1e007800c030300203507a0505c10056468120404041e81c2242c101202900542c54017000c40c015440b46560311a108030034110180540c0708000d00e4180704605000312030340600000101103045d10703c0c0d08c100180d44441d40602d01b850382440a900d582040c0c103140d5400c8000d801000c001c00510340011941050101001010380754101210000d5021f5807506061000d105 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 337543821 1250 337542571 337542587
    0x603061203040306020a0507021f080103060e0304050406090f05160c0f060914161e03080c010612030302070b0105060903030d0915021204020a0f060807080901020f040330020d 77
    0x190140640c0d18040d20303a159042030360700c020f0b000400b2810009008045081080300c88d500d2610388ac8040c02d107070440303070030080c40081d06100142c4010b4071100d0a15001c0814005c650045c0300042041041c0e566442c010b00c05484130740c4c000708105d80b03083c0c00600c0200300607010b40c0c1207910310382c2c855038000d501c0d56a0441d8100f5905050380c400b65034500d01400124120b06c161850344006c1c00404c00700d06502c101c407908032030a4110140024440104038542001e4409072419203a100c070000f62a01d1480345214014140c03035022040031850014100b051542641c0140748860046111180c540c1e210410310441d803251580d0150154410064002e03210403d81c0030710390181c4100140c0150350041c1d01c1501c10380e00f2079060180000b0480c001d0000714074028080b40001c0520492001c0303454a0316602402e040c90081c844400d010210700000c005402c294100c134112031413248116100e07922414a45018401d030401c800c2c814544a82c42c4100c00318006079240394001d154020300000020a0085401217 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 337545071 1250 337543821 337543849
    0x1003020d02040306060905040212010c050f07020f0d0c06080c3a02030a0209030f010b0906011d10030c02061018020a0926100c300c032405060306 64
    0x541d007032102000088260042000030b11044001103854109070041107040021031912810583c9460200500745410038150782e400d400b0074410f50f031107404d40d0001c615a901c80c40c010907403051f02200c485003041220140041511615903034004195603007440600300d0310030001c100d06ea0001480c2c04d444890f8482c1c805e901f09002c0d07086518044030300b50300c0d02004e03a0000d80d6803085098000c100e14080d801e007041514141c225200003802582d0b911404184556009440c4904010a1480c03400c0741141400f10741c04007040c05002d50041e060030900c0240140041c05515006018120102d0641800a590041a41c00128a66419180c4100c0e400003e6002800000a1003424240050010b011840030a80441346c10340f11502005000101400c0600000c40b03064101c1c60070038003d1080e9401141d501d03102034080d00904455040020400b40e00c05517407500e551450030300c11564021903140d049118004207034558182c842c2c06800f4020b00704c004a0040795003205007800020710382d00d000034801c840342e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 337546321 1250 337545071 337545097
    0xe040c050c0601080c010e03010b060f0a17090d091706010b0901020a1a04030201060b0315222310030b0a1d0303100f0504020a0203030a050a0209030a050c1002010506100302 76
    0x2100710381034481d0034210240e00154060700f144a00e5036441d46c0006d851040040114002c02c4240d80140014030a4050200c03400c250b0100480c4081d5070500071a24a440c503500381c0349541c0c051620449256a403400c1c2032030365000230081038001546031154000d0030f80681e1440003a0855a0820700a00e00d40e8103d0080a03046204400343c440204240320b01c8040340240088050045150608007e42075442c16800788890440410400000a250a1040e2440c65040b5080700150081c1402054200700d1150244151460410703c1611070009a000f00440142e00c40d19034020f545070300d20141030300c540b440302810050554001829940c103d61012042d40d10903a40c00007000d1401e101686507030003c8422144044440d1781c240a591032003844d61006200454041d4503003101d01d04004e442e13000141c01d40c2c02441e1600040b50300b180c1c182c2c05a62044101408450340507a46003001d80e030f1450351001f002d00030340c40071b00419803ca2041c000c042c0700380c8000e4282e0043c942540d41c03c40c02580441c031080d1700 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 337547571 1250 337546321 337546327
    0x9130b0301061a041707030c0612140108030712031b200604030513140a05040203060f04020d0221090a030c0507180b030c0109030308150a09060803070c080105070e040c05 75
    0x1002c0000c2c1d40c440c3e291020000c01c60300c0d142003d40110105161001e044450780c0a01030400018080c01c3c01c00041d1812840e0214501191241110203041c005000025a8504c0800422040c9000025041c902e0088490302058051500150100c2d50b42c640d40001c0c08511000c0001d02c240640e408042c080d01c01c40e000610040d00341030003424140113aa0850010b000060841190307002d804804001e426004d81c5050740b0102000007a03101441485001e00468011002600950b540c20010b0280d00b0b018000390340e24200c1c410040000c2d40965009d00b12a0a03000c042c0702d0780000001414403d0a6901c001c050f08031003510265201c40307110600301c5141c4038014001c250748004039140707012041d014a0104210410104040c1418070001c212410044010070400219600410701604868040360b15070310b01c08507a02003000716032140c00050074141003440010342500f0000050008a00949a42c5886500c1e03980d914240e9806650000004411020301c0082d468598000c1c1164402420001c2c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 337548821 1250 337547571 337547579
    0x240702090906010503071401080a1e1a010906110c04091704031a011203020c04020a0e0a0b0714030414040209040207020301090b0a151a0f1e0304050d0509130b030106 73
    0x80c50610488240005400c5080100311a05003001404c014101001d2041048180e1a00080c09108010401d902c00342c0c50709802985551000f03e480000c00000380f00340000b0305880701c0c081000381140201030015003681d000140030341c41004414030508101f400b03030161200386001c0001078001008142d4400148940d8019442d9125004200448c82001000c501ca83c40d1000d442805605910200107007000207241c1c0006540031542e0664004111801619000c510b14125442c424052450f604041d42c03080220b0030030036074030140c408030344580c0c0d01a03c0701401d54080364490003507204211120b240c1d60041a000d142039000f90889440c06030006041c42c2c02500002d003035844954064884105083c00d00210751034070300850b038682e840c040042600700c5c64004055141807a86000d04129a030101700d844c02400031000f1128804420344d11401c8420300f920b201c100640c000c2d6421100c51140c0a0f2916506004d441034410569004129954440c01e6050450141010340e141385d0341550b9801c4081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 337550071 1250 337548821 337548829
    0x8030606130906080c011d04110408030f0301080705040606020d03090f0b190b0a12020609041508060702070603060501090302040b150c0c040f0924020d0207111806240702 75
    0x500140903440b40407a25034505040c0301e0506030316050060400050f010386030f1055484030300455280758148c40010341c0500728900c03a442402241c00c002840d000004001c0f03543c40c4107101a505944260702036400899840341040121000e92243c0d4015800651500070401d01a41c4941c02d100d025400d8003c06403180d40e2609075000080311440030803d42a05031002c4a80305105040c0e0840040e92008212414480c00c06106015058024032607400041c11a1058440ea0041c845d50f560140c5e401e000c030f030f45034480b0301e448410440324100184660140040c01511034001c003400c858040e10307501900303821030b003c2c48060544c100115070030001000c0c85108502040000344140740400c0050185200c0440411090310f1a00c010100c489003805030704004100d0070307510240e00d003075861516007000c02040e0ba0107001e4003840400000651010030300005002e40107081e09142c0c00101c50f1170028102d4020700e404003420548440350010408400754544821942110a0407000e0400b01810220f26034005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 337551321 1250 337550071 337550107
    0x7080f0616021c081603060302060f180a030f02100c200402121f08011b0503040318180c0302130b0c0109081b070f0b07111c03020615010507020d08030606 68
    0x38000134400c007081110341d2480c4000700c3c4102201e0315040c4100c600d90340008035140200c0350070f00b241c10780000d43da03401d01c070118100030002030b805001c510b40300c0e6480c07c0a0b2182d8068020603400307a0200419019614802c0358034012881c0d000e0341c1039400b91000020820416902550396800c80e03820081061030a5a00340c8242c400c04c8240b0030751230b100036400300d0000341800e1a031007104035a041c0060b181c0310304101004003001c0181441d2154480d43c8a040c1113a0300d03034070305101c402602c842074804110010503184400d98800aa48280000d10220070210b0481c81620503e041c111503140c81808005100b000406603a0704890001c20700410a48561009030301c11024041021140c50000c00405818171038580282441a00700c200e10b45040d40701c100602c101c800013020304400104e054496510203031a404031100340c0d000125010410303d0082e546080c240d907001c40d10400149241050b6215008442c0041e60181c00c03001d02e0329980e6140e00c01d2381c0014110692200e021b01924028007001541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 337552571 1250 337551321 337551373
    0x1110f0a030b1203130906080f06010b090a0b0d0506040c0518102a0203070519090902042307111c2a030c0c080102040b07080d0902150c07080f061602 66
    0x1416046c0781c81964401ca4046030b00c810916003013400220051030001c203405044a0034000c5441c4d0315a04480011140e811a0b00040354400b80807071001642d611a0344040d11840c016901000081000c0d00103a0703041c024854030042c12007010a06a0150a0110200101e5070780d0742010030710352161002152058141840007044814451110000e42c07038204001402050280c851521003500b14000c4200b0701018042c4200c0e481e2114031840441d144c60388614080841c0c1610650390504001204071003043c1034036000c000801c3d07040440c1c0e03000f0000c18607501640118884e2441000081000e5070b6040b8910018002130f8428241183e01c4030a4403840c9807801d100760b4410103c4840c034907081c841010039400600341c90b841840244408200d00c000c64401030b40041d11070351034080030040c1c0005045442d4000350000d120030001080c040d500005403410014000645940e40d4840c9044d6030f841c0090346203c0359a0b407112012444500164074075002c91480fa02c10343e1080c0b550342d040c030b210758141041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 337553821 1250 337552571 337552597
    0x2030c0907020a0c0f0b04120c0503010203041119060504060f02010609050c030f07090b0d09021c0c050a080309100c030903120c14030702030a06051009050c030402010201110f0a030b1203 82
    0x25903d041001c455283c0d03000d04008543e0568031030400b1003002e4640554000c0c80140000d034a07180091219142c0e0740b07001080300030000c0d0340d6031510f0b01e040400201c03009540c0e8040c540e540014000950044440c0c01030f9040f40d524181428540001142c3e9070110039003600a43d581c482b03003c60784180c0303801210310551580e0000ea07981d04001136180d03ca4207005010000300405000c0502c01e066100045944c0020f05100100d144222800003404040812241d21020b424140c00e400402c1256510340c022550700301e80b00f00d0703001c0d51078000036140c2c442e100100b6032000001070030200c0340d070180c2c4210201c030740240744c030a03c4641c1325582c80391071000804407070000c01c0b040084002005190020301c02192500342c05035007061101c1d40442c2e594540080700404060301d0328000703461341860742c1d100d00040000c0e40c02032049040100583c075407035000b564264015420208010b0701012144200c130310400721360981324903043c85600101c00410011000c81d80c4a001241c8806145030204050180211012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 337555071 1250 337553821 337553833
    0xa02120c1b0f0a0b0f04050c090402011e0903151a1201021c02090418120f11070b040e0a09020a1e0512150709050105041e0b0c0d02060c120c0702030c090702 69
    0x2042003440404c0060405410f040c2c281e04100009001281d18201c0d890103a035484010749071840144c840c03000340c100c0143c6a001000b8001c01003940261510100ea025002d030002072500441c2c40016110900e0000209440c01c0384414030b1414499410001101030344001424055041c290300d0081601c5510701f11101d4020814505500e17041c451410407045981c500b50301c0400540c0c80c0d62082480c1e107a2141403044107211611164001d0300361103144080c1502381c1c3d024076155069800b603034109000d42c0d00c40040c3c2000040c0d184089200b4454040c1d00105a90f42c10742ca03010080711030442d00300c50542910b40079000024a07458902101c41040c2003240a0801c210180100500b210001080d0500f005007640040001e6600142141c05545100c07d4816440a05180e04101445030b54800300b070000002664401f00c04002c03601c0c283c0819654280c074140d48408a030740c1c0c0d29005040310029546050b801217021021000020036100b0700c040d0580c1c00c503c0d0303118005445454100e60343c502682081c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 337556321 1250 337555071 337555073
    0xa08030106170412050a0908011104080f030c061914011202030d031b0c03020c03060403170702010203040c0603050a140c09030f1c0806120d0201020904050a02120c1b0f0a 75
    0x10550740e03041c1e00ea07500c42c1c5502c0d1810340c580c00300212641c0b8124082c0840054256500b0744036030000d80c090004200284200c0c81410021502c0303910030300c5090700d10b02542100000b23090010040300c102102c0c0380010102a203405448059240d036075021078151075501c0e05805010900102c0d240e00901410050390451310060040c1410000052401803c00d4a032901800030819000d801d00f901c0d001d41e140049150b401792400341d20344481031508542c540700d804200010180c0c804905101c20f02d51020280f515140c04000340d09038001134a00510b815980c8000388a060b201e54422030f842031000201240051101c070468640080c1500c40324900306000500f5900760404001d51015034401030000c01080119050800310999960102e02c200f200782c601080c000c3c1c1d01c4039207416114690350161076201d02071040182c000d42c03014040a019505100000344032013210720a8070f031005040180103286030b0b00d40e0003201190303101e00442e00c03040303425500c1a1120703e410848240d170f0079400c40c0201004401 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 337557571 1250 337556321 337556327
    0xf0907031202100c110a152007140d0503010312050405210c06120c0c0c06130e0711030714030d0612060b04060302060a0c0302011d0a0b09010213260a08030106 70
    0x40c1c012500900c40745024842e411715000465100700d5401c200005c02c00408124a10301600c0e94450380b10140c4400c0c96448001d45e104030080102c02d100359480c800440903800d203241c50700301101d04c50012810620042020500c04000c2d60305500c950301d04549015100c400141901c00c0354280482c1a11400d002c40c40303002d070104000c504e20541220750b81d082c00c040c0c00c4000180c0400420401e40c070880800e003200007000c10084146a2407004080300e4513110700d43d105035403040c45445458a10182e2202007071501d8024080c00d040300c4c07144000385150210a458445000e0400307030000036644410000089828903e100e4800900750100d02800818040c0c04c00f00151652225403a12842c0340c100108016600c40d000ca64011540e4203190048032014282a80140303000d91003000050346214191090410214800240501c10494801d031915018025402c0340198082004001d0b202e00c0c5c14045035002290b4400c14461465090316801c04c2401c540d402c1c29488201180c4800f4088014810f141d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 337558821 1250 337557571 337557581
    0x230f060906010b07060e030403080a050d050105010318020f030f100f0e030a21090804090903121517030c010c02030c07120201080703090204021608030118060503060f090703120210 79
    0xc20000900e540d50410302e5040151064280091407150380c0c40404002c00c10a00a41c0c0c000e60300209601c0e2140e8124002501d694071050070301c134120307140000128003503000348940d80301c010348201520340d040c40b82d500303010441050440545e4180305110841c00c0e100350400c21100c000301400d4020540c18600c4801c81c040c0d900c50302e00c0c10890703001402005081d41e40316031400003290b0008810135000809140010007860383c1100948040b000050110740108240c0080300300c64401d5030303000384011503c05600201c851030032124150b04041709080240341011100c601043c0110300c20b40385809400861282121210303e180c4026070404151300c00402c400303010040080001030442041492980c1c002030138540003c140340d013855651031803c415919264140d440c0a412019416070749240d074182038405070024402c2c000304010015507405d1141190194804036000500104065292944285005000103000c551584a10440040850145809a151202c0c00d401616141d141c1919140a0322 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 337560071 1250 337558821 337558831
    0x705100c1206030203031911010e160605120406150801092001090b03041704051309020a06170f090c03030406180e01080312090f24010806010e0c07230f06 68
    0x1468003000f040540c0340030049507120310103032901103005000c10380162540032409040803140c6d8a00a4690301381d190000d0000b04559002a1100090b0343d900e108886a100d480070008510045001003000200c81d60041104012400e80d0000c980c0e481e50a07240c21034281c060181c1e00c104c503610140c040707440006010b00c2c8684003880e04100d0641080041c1030f0350701c0b01900040046008054202d00c0c1203262040c0c401810340100440e6901000110000182007801c5041e4807908000ea00054158054040d85c0c0116449440b40c01d110790307520700346035540840104446203501a80d501c041090740d003400101f020300440d4541c901102c0d044507200d00000d004d41c00c40381072103c6a20041c402d16030300001b40c0c0c85520a0001c014020f40d24100000d051030710000003840f0901c11000d03a410703000895484540140c1030b03910140b9482eaaa1443c450ba51345080c440c600c0103c00050104110000c1c1c1e030014055030f40581c1085444506080c000c58008942000501041d0042d9002c02d05018051100c20303000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 337561321 1250 337560071 337560107
    0x1c180b0f010f06020307082b0c03050c0408071415040e090c060f0706180b0a020c0f070608060d0303060e04080d0b0405060102061512030c030301031b030c0b0f0705100c 74
    0x8a0400300065546c2c4104600649501c1e17000c01c403d0181e44045460800700124540480c01c110491068a0050700904a140300401d052000007541c44a4041c04d81d01141c181c0001801054a4003040380c0d81d42c0c54101503150010f09204040c100321200310014001803030301c2d0b60451994500000d0b9942021354000d07910303110303680c02c1180d809803100300020345a000d50090400030b10b00040047d003000c9581391034001001c80010004001041c100c2d5409051111106419034612403600c0d41c05988600c001d0044801041c1c1c0d010100d0028106034814101e4944a0b040005400351a00107078a00d000c4222012124107200240c0a130243d166805a4084590251030600c01ca040010003c1d407601c2c0018510b0300c1c4c0f911044404401692a8800c0d150806246015a540c1d0070403858065101d0f4024002910f00c000040e4003041140420669681160341060b500e40d691800c6c902001481e40c41000303003a400201c10301c004001302d0010300c020340c4d03072845030040011700c8599454042e259100351003654106c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 337562571 1250 337561321 337561349
    0x111204301109060f12071a0304080703080601090914010315021606051f0905090d02030406080703050a09080307030603021e010c0627030c1a0c1c180b0f01 68
    0x1a0102405411001c400c50b0384800a50700c1c0c8011a2420070100c0e50550722030194070750340c600b080f804250390042c1c0340605092108011007100d5401c40d4072054400502c520400c0102c2001700344547e1945130483c1c41450b1090902c1c3d5901d0710a8143e5881311550300c994210700f4010400c10501c00c1e04858502e0800300c0035814088a08043c80740010941c1d00500044e0325a00000e5026201c5441c18106868042921544d0b07601c40b050070000340800c030750845040c4202400701d14060300000c1980e0444541d41d440d2244c0d40e5800504501615002d030034110031075141e40214000402040140d4400c00207583c001804070314600400004645a200104820480900e400c0307250341c0c000b41d0010391903000b403c0447c52001101e17210400403003983c030180d020003010f04d04904165214001c10200ca000350340c45030021860405e41042154144c0320210103000410034140c05141c040c10514518640c0780000600c0044030721a40c2c031031580e5440840d00c441f01c0030100409d1611007010303d400742c0242e52603924 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 337563821 1250 337562571 337562573
    0x32b0c020f06090a1206020307390302030f04081b0103090f060b0303040306050a0e1209030309010e0f121b010806100807020a0c080a02010201142205030c10091101140a11120430 78
    0x4c40c51140d0ac801d104810b503510001051500801c2224040c2c0c1403c140999240d9981c00d00c1e075124080030301c00d0b2541050600710308046600c240a004045034000c100f14201084a544441c010105840101c1d01400140800404030b08144a070b01d1150680c8140410030b84085180c003800c01e098610295140c640c10b200d03e07001d41e10004242c0310030311402c1c00c1c181010618200068040b82a08003015801828100003140e030701401b05500c02c4503c0f48160300005900c0601c01500d80c0300048a0f0242c20012880c0080c1200b0300c60321b0f900f03800408900560304050910340300e500c41c01d01a5003000707082c0c0c2e0200103220f046590902c0b4800d0040d100180e0180c0c40d040a810900041c00d006c403941580301605410041484014800c449441003001e0840f0b9036212610182c0000d4101c3c0031007030341e03200c04825440d140380d4082c99680c0180f054046242c3d24083d4002016941b0741c0300804007000a200f05a0100300004104000380046c0c01801a4441c90840c5d40100424440100058050402a40400328 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 337565071 1250 337563821 337563887
    0x30d020607031a0604030f020307060801080a030f0c0c090b190e010521030d050a05010b03040f0b070309140a0507060504180c030902032b0c020f06090a1206020307 72
    0xd6004651441c021500040d404520b040c594681e41245078404000240041000302035200451820300c01d8081c0c850306581d40301c087c1c6080b00240b0035918150008c4462600081c41401400d514507240d00b0301ca4112807458441c6d001c65041504445213159440300e1000f140d103483c0c22480328010003008a00c00381c07801c00031030900401061252a006080b0300300002ea104080e81244c20102c03420608980d11040c4084054016041c140d403080300302482c1070000329a0501040840748035a030030050382c031708038011a5a011042240200b0041c10950746078090b400140c0c2c2030021360180d00c151001460b49140c40d040c428180340c1160322030401d0001c10001080203101e07408081d89584541c42000400b1380c000641900a0041020002d42c1401083d0140d203c0c1102c400070703080c05035900c84142d8959030003040103440c4009a880081c1d03020344401c01104940c600300005205c1c158010f407442c2000f540c0e03006c80035034881c1d260340304a4200303801004022005511081c0c0340320f011013603150142c0c2401ca0314520 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 337566321 1250 337565071 337565083
    0x4060b040e03070212030405061c050c0a0807082505070506060607030c0b060312040905040c0501030c050708092b0501051f0608090114090304080f0a0308062202120106020c030d02 79
    0x2c0c00b448039090740705400c5c80e0074004d032001420301900150769010801030500d0080d0329038030103086603407401c0d01055240d00e414059901c031075440c1d10b4121154882840aa50720303603004100840b0300c00d521007a07015001c0a070102c40000c104c4c5459403a2139510381d103005810500300422080c0640001e12605004c0390340101c0c0f440245400001d018000d8445401007800c1088158500e0107001001070700260030b52088d880b00c3c2c0f0441c01801000240741c0c45c1e000440c01c2d512440f8454000500038840800412820350003051007a400420640d402c4811504c42100d007004e02c071504040c007069135030500601c230302030084903400b010b0103000310041b002c64110580c01070054001d017020000d80100080482200354000d5200c080001e40050315843c0c0003e81e659280d210340220707901e0740211070440c40038001c00140c00501940c591100240e55840400384120100d50814801c01e5090289507200043d20a10007400318915403880c2c14000d40c100724029241401011485010340c1c40ba081412901d40d01081d5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 337567571 1250 337566321 337566323
    0x705130b030c0603090a02030a2003010501080d030f021210030311060c12070507200102010c020102120604020c12040b091026130206041509120305040e0a0f1404060b040e0307 77
    0x159510785d00c0344000300345061404c0c0d900a425224070000386080c0014074002d56552582d55590b90003500030213040c14203880081c46400c9296014040442c405402500480072120140800600340480380b01d0711b400c0d65406075101070a000c0c080d5018010b0683c0140e40b454496445d000500d494180008164518496001030258411203803001c503085c5480b420031176034010380003e4500585011135000c1c507807008000d0121409903181030400c4020a0042c005d03500440d1030300768461030565420f070502010394004281d0f12030900540802002606158000d400a080c050090390f44400381d040c14406808806031403c0184270842c005000c0088901183c1c0c060340480852420858580e0744001c41100c1c05814025407046d00864003098000303807a86134411030b04690703a901500039a1101440040301c1c0045000d030001d001003005104010380e1031180e42e000202c10134001030091180d10408201c0750071408844e0f119040c4014001406424010b07104c01c030350120f07400c0058540304403416a4920031307408 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 337568821 1250 337567571 337567579
    0x221223031006180e0109150306020703020105150406031e03020111031f0b0304050d1409040f1e0b010504171e10061418040c05090405100e0a0201090915050a080705130b030c 76
    0x1408076168203824051f400840d4021819500c8100c2458081d0207004210303025031000040d85091240703890140513610490f5045080c22450b00d14424041c00d0002c0420020760541d900c83e40021a08118031004604c140c1c0d040c8524500138581088903a20034002d0350012804000038401d220110b94040351005420115007011040c0e83c6a03003d01b4012070103003a43c0c01d5406880c0803060000b5098a410505c8a50100c020354595015649091811501010201c0e40021000e010a21080515030b840b0100c4140706e20403106408075030990444000310403078007444950004000100d008081d030107150090043d21540307c0600744150045a5000400520786011512040106041c071079105040d41c013900c1d000d042d07480c242c501801c100740c0e81c4a04d90304c2040d1440c41c0c107aa012010b08042442d01c540c0b42d0596901c610070346082c0100000c3c003542c5000451096020000180503a41d00d14480700410442002d840d085181c1002c1103500000548203031061410080310707000c1aa00400c07510450b0008907 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 337570071 1250 337568821 337568831
    0x1a060d08090f0d020306100e060a06140705030d0908040914010806060103090303090b100503100506090403050306042315010207080705061312060203221223031006180e0109 76
    0xc0005444001c3d910b102942500401d030900c2042501d007011031040da060840d8902c4079495941c103104020700c0e140b20b204000750803031060b141911000f0004000d4240104c04072402c1807040354610045038400542110b0310760f00050304200145460040460200c0700d207400404643c540410181c4410340103040d00e041594900500007054082d50241c2c26035500700c02c11041e90303d04041d00c01c070505010b000c0e1078880d1050b8031001d0012a140d0080d0f601c903040180030b0700ca003070b1240c5c1d4081c0c0d5140c1018002540c0035407a080255000300305030201c91014042200910003c2c10854440080e03980c0d92140345046422498092110020008000c012108107a40081d40c0d100d2040300200001103030f400c68103130500c1205580c13013401800c0d0050342c0644082e110043c7c0300c1c07251189440f8416090f6800a24001890813101005801442c69a1491992036402c4103a100705c0b10205095a00440d00652080041d000c140078042d400000c1468401840c1d003072520141c14010703448498801407184807601a112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 337571321 1250 337570071 337570099
    0x91e0102070614040614070c06021e03131b08030412081b071401032d0b040f0603120801032f10030b040b0402040f0308251a060d0809 59
    0x2581200e0006070880401c001d280c80410071040c00c2c1006031130a07695a03003000b4109009032014042c0b14042d91840d02c0d0140703040e0b041d41c0c869019400800c880b0074049280181c40e8040c1d0b40c0c2e60021032280102e4085018800c00b546480005000b015240c60340c5080c0101c0103106940c40002100c017602c0b08107091060310091480c10461310301c100103000800e0242218100300c410f0001440c0c00c00d0311400c10b607510030f10502d2801101103800c015512990f170302c501c54a100760013914a10307a010a64054030042541c001503404582900e41c0315019000d41076580382c0070400e00400705003411004900c2e140c05020755245450b83c41c1e403908103d0460541e280c220350700c80040309000510001641014003041041254003130094001e1148140e500c1c011400c0403c07603178080c0382c1032088509480702050710701c0b20305013035458135503158210b05a070800402c0700070001c400c008854259a407025206400c40c6c41256000c2940c0b948020014000c14021016000322a00243c401011b45071008000d56001408a43c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 337572571 1250 337571321 337571323
    0x50112020d060305030706060605090105040302013209120604031e0201060305190501050a0603032001020412110a150512070c0611032d010905100f0906060314091e 72
    0x20709800d0501a500d046400410031001202510b40c003809044204942076444500781e03141d21844420500040082200b40010340c000e1000010a001f61000e48610700f102c00c6140084214003d1001d907000390205a5222a00c0d010890300340c08000701011b000c0c036042039600a40b03a4800c6041c0303803a0b07081c524000050b54910035800300c0000c1d50060100c80c1d42c1104020503420030303402c0319029034030307542410002500c0310301074083c050450358140da903114184034441e0f080c01c00041641d0b220546540810000603a0b480b070511a94000e40200c14002180a280007003040601c069840003070a5000e07455844403158211054800c181051407001800d582c41c424111074015092200a141c1c500d44031454100c4100710015501c11100f0f9030904c42810300020440480000c1c2000888500b44440010301040c2c04c81d07000725070000d4103000c000403952b8132013652075071159454100f00403860f910003040020750f42c140910400841d8050b1405c80c603042c90380d003032621035900080d0a842d0100448140e400400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 337573821 1250 337572571 337572577
    0x25050a030803041b0905060109060206100603150b131d011d270c0a050105070c140d020a09020315060324030f0d090f0801020c101104050a0311210705011202 69
    0x40130340021400c541d2074900190080c00107a90081c005800d00030081501c90000400d1170213240b01e200300075041494400b08402803d80c0100800b109514140001268205038000e03010303c0d0089003074a800c0a0404d03418038000d00300078502d010744540202c0104280d0612078040d00034400154041c035030340ea640c800380200c0c90b12030b1924031059407212080302215910201b1103101111045481d846c0303003a0384000458160052401c0600034000c101020403105c107014048080b190009000d2069450303058000030b520f4240c1740e218994aa40000c10400101a40c400c81b00d082c440c00ca5a55045003045800c00100a54048449811803101e0000800d10744e000c004c04280440084100c0d003505d00c203404010300000461041840e01803498902042500042c02a030315004004002020741400030709146001c0c1014542150165104200108254030f50f048a44040c5001754502080b440b141401c0c4218205512020141c1c22006a0701c001d0300c0350301080c0507080320824640300340d0480107011580002c0c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 337575071 1250 337573821 337573853
    0xd051b0403080703030213030308040c051f0503091c1806020703030e040203070e091504050109050702030712180e15030d0e0f121b03160806042a060225050a03080304 73
    0x1001c00c0341c00010903074051030ac3c900c1148a80c0d00c07001c42c0783e40c51040c49407a2517512404502e40f014006898219480b81000e1948070708100c0880c0c451001a0700e2880301d84208040c060005800c070094080c184803030308003500017040c1c0c601c001c040306491520f00620031002c1d07180c1648119000004204050f02c42c00c43c518582e45d005001d1170440c1030400e107d0543c0310a442807280214200000011040f401d803041c1791182c001900603619003050b40d520034030440c080c00c10600c2401a60110041250444145200507142070392481055003000003404009003180c1200ca880f941c44814801129039112004e191880c50556146104891010000c0d20311302d908511f186442c450104e000303003140c1398203164030348100003030302a20300118101d45040302c4003c7c01c0c01003039130300da0028011500250032520351906003200403400804000c0c803c1810b45200410382d10a00060b4042801c0480d10903492000290020800310b01240d1646050042012114148000350034520048001010322419414148646e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 337576321 1250 337575071 337575097
    0x12050106051c090803040809060409020d0606031b2102070501290d0f030c02010302071a061f0210110c0604030215180604020f1f050d051b04030807030302 68
    0x1580c58040041072034001410007450b009514050001e101e10500c03880c40783c103030094041c2d49150f0341c64030354400541c8a0200c0c1900700e0410000013441408038400383c040c051007080e000c14807a00e003080040a4070203040c0007121918080010f00301682e000f105d0040b02421645000e04e80e00d010139050002405045000b074100c0d400c00100501c03203214841d504203948a5094190542c070b48180c00e01c85141202075000340512401c0381c0100100340524140c01503248145405840c10000e540c400034481c50f40c410594680d02c060301442418a400700028075015405551558200b2002d20020750f50800101c028284907038031501c0d0074000d10341c03404070707903084031480c0440e52035007020320303000b9902c0e0800c3c0c1542c505d2301d200728003003801c0060041e547d80b80030340b8201c000d0449480ea50204041e6458800700107512844407402c0f0f401110940240aa4594981d01ca5a8640307041d11044029103c0c020002c40c0e200b4004441301c881c990120f425141030b01d0700000142d80316825440e00340c0c0244210b038120a46 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 337577571 1250 337576321 337576331
    0xd030e04061503060305060c090a17160e060907020334080703050301060801080a020114090a0515040504050906010e01030305030405030d0f0605030c04060b03191e0c020613030e010f12 81
    0xb254150b08108120792046080f00c1e0140e4840751000d5040c01540d1131181e01c180303841e0701001404403032042c40d0ba600e4548400d9a401c4001e0f000040095041a802203c8081c045410400c5502e01641c640d41d2102d07075800030750310700748600100400740c000300302c0c99114281400405c1207058645684290209901044541ea5004942006045ca400910403000050000e400201b40500040703030304600701c0c3d8180c40d541144980910202101d402c525106500092000d8000406030707294400a680c01c54054a0103540d02d0505e01400141c034001400010958441e00c010401c0001d40130100b070469030103141458130b940f51880c059040d841041521514182092200030b0503031a580d01100c100c0c4c000700c044910514002d0b0600050b28030611034804c403180e080c400100c5d04e0401505141da0203245510001e2840410f039a001d021804540203a20f00d213030703100981c0c454aa01006107941090000c030754400c0010307156800900032020b24411034100a4911203500700320b03004851126030890800c0c1d040c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 337578821 1250 337577571 337577609
    0xb150c0c090c0705070f05130f0207060c030608070b1911030706050f01240f080705040e0405010b0415151808010c0206250c02040b0307050303030c03011505090d030e0406 75
    0x240b280c2150009865600519100080c0c8502805040f4111500581071110784000c0060783c000400e42c030441c04c01007035003c00040000400c2440744850084131501c001498030300b8101002d01d0700100d90401c510079041000000e5030003030b03600b42d140d40d0040285071000801c4144d2604600f90f00840f074000300300078180401d00c040c882030b094045041e20142c00100ca8003d114407000e00320504880141c03004141c0501c072000200e4802c205240e070280036030408034506652901c04d07031070307010007100c0545850359115112410703441c02d4024603000f0540f034500400f1880c00e01c21101c4805a59002c0d2200b071296520040c1d0a40b41c40c0c03003400c0c000f0302c070040c000c00144811203800303501d40030200c44074055500c0701c449405410406030307910908003180781e9881c10844a1642030100401c00b10350a1a8113124025002030203540410045110784207a8001d82c0d100d5150a1a007084040700d0028481400010300150009444505040c0002601441c01050581039040400c00510550300140c2c0d00452400d0004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 337580071 1250 337578821 337578841
    0x2040b0d060306050c070312050603030c070306050f0a090201080f1b03011203080702030c15131b080c040911040f0b0a0b1809060d030c1b06120e010b150c0c09 70
    0x1411030f07001c1e42c01840a6514485401d002d845110802804140054014541803059500041e0301060103030450780b50850f1440c00a290070141d0b8030840c1c6c0c894842081101d124000182c0c19007080c90000144540d0b002640060440e01c00100b07034a40aa40450001d10690407102c141003078041804003007030b80c81d615041d01812481b011401a80031070780442c0818905c0740b000045809010514001d8403442c0c2c0701100340141d2000c007410071a0301c44410070310b800c003244205000c4e049100700c0d1241d00f8a8549007900041c1481600b146043c407a52400101c00302080f601558480321410449000503040d9500080300000c000c25140c0d141c0040700040080380181d02500180600c6d04100c40620b40419141d041000c2e904d41290050b400510580c480c10009000301d201440d4640704040032116204d03046580c0284030391582c400ea0000e4421281c000450059110780040100c0520081c0586000000451046004510a61036620b000503598030b600609005051308514020540c0e01603082c049025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 337581321 1250 337580071 337580081
    0x30f080403021c0503040b07030c0507090c0807110706080606120f07030b0301150905070528030e0606030a0201050a050c01111e0304030c02100c080d1e0b0109090207030302040b0d 79
    0x100d0243c81034507601c0100d10103621082d031180c0d0744900250301c0e0504101d0034242c6070700482421170502801c000050000f5005002080240c00310820009071102c689030300500c40318000d0141010b00c4144550500e2103400810b1882c10b486007802c0840301c0742c40c2e500100741035104a81110180307010101c20711580480f10105c0d1805200c2540d0140010850b031000c042c01c90782c0b20200c420407005000c10030026105a0740001e0350246107420034600f000c1240d409210000e81c2c8086050881c01e80e482c0395411550907208103041110007800405071403030b18502299440c41c690030046e041c05800300e800e44540d440361049440c7d6545900c000d2204103c4042c1c408419002001824040010888040051032803201030b284629056940d44500080a400703002d6511402c807412020841051010070108401d0002440d05006100c0002514000805204800ca01445054000504090004280740c2c4c5c07240080050301c400e11401650383c8070030b240c158000c0c416a40150300c0300e0004503117170081001036440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 337582571 1250 337581321 337581323
    0x17040c060201110a2106030c1205010c05040302030c191502010504140c06040e0a02070c06110705010e010527032a010207230d05010f09030201060f06022104030f080403 74
    0xa000e807400500d030150f104d01480c01300303100265000041c1182e800785007107400c0340060784041c0014007030b88945036599040b001d030304004030b2880c0081c0250b0812200344144504429145044d80c2400e04580c0048d440380e4240310440c0c8602152034040380400900010703403000b4500303e2440c1c0b1565032020000380c041d00e421241a210446c4002e03410710f800070082140044c2d00b100034109454181000380382c131080b40b0701522031145039900f0b016500000b8080b00c080d4001c1c01503501d1b10418103080408041c034020280d00414100320f0208005d14440c0d07005802d49031035254108440c54500320380d0440c1174204445c0d90946506101e140b07803050306141101c4c07000030401603286400e0304400c030803401685d513110240305101104505611004184a103030111886213800105829400c2110740c0f07800342903030364004815144643d0350030002c00b0190244942c80003400e24190340c0a500e80382c440069102c0f40c2064420001170403005803030b042000340404880156a1026401445200070705146010b80c0142c00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 337583821 1250 337582571 337582573
    0xe0a03020f0a12120b0310061e060503010902090d05011506021c09090915050a06050f120a0311070308040603020301140913030f020c04050f0604060e2517040c0602 72
    0x40312000c0c00d0301298204190f41c003d500c80101c0201204200e40041400780c080094507555208800b541d5000e00c0702c140d2003c0899000305480e424040c03c80031002c82d85140304102d240e0300c60100030490308481680e04660181f04010784804800001c05c80d0540e007880000c200d94600309040c0074101c6140c0c840700903200e01e40d01f02d90b85500c2c1c0380caa00464051066400700410810034007048400125000a000503201e0503686410034040303c0b001e016140184d135900103082d02d6103810301440c18040f08100904004982e5010028903d00c0c1c8a40c80d00101e20001c2d00304400c40c0002403284100300700d4000110f03800055a42e5443e039403030004001303400038010b940721300185240c04038641c070700040b035540544201407460135005000d80d17068440a40301c0d00070b903066000700c0310007064036555031162610614070400304c1d106170b1505500b0002154074035004140e030b03280c291091082d08000340201a0003500c0300c41c401e042004645605856010500c98100340244491042008006c5243c00701021601c00350 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 337585071 1250 337583821 337583833
    0x110103060f0b0417030c0a0f0f05010c0f021603080d150803160302060a0b0907030c0908030a0306050f15180a09090812010e1303080a0b030f030304051603150902130e0a0302 76
    0x4e44546a2041c8004007503e503204620340c0340440c8041c540700d4441480303003c084015032040d60742c3c542035070042a4540007083c0c0e4440504201d94044c406c0c56604901c104d000514103003183c2d05e0740e03414080d0000b00405d1070b90304d14400320403010311115400076080100480c0c0d2580002c54050441085500c0100c1c018001d660128400d071065000c3c50302c4024005020074080c0c0c1d200d01d000c4006040910a410400c0b103c0040000c000c2001e1000b4100c21075159004034165060006021a40341b650394143e000e07801c151100050041c101c01a2600001d800c92500642004000011401c4000e5040307240114600f0b2407840420035072400401030b040c1803041c0000540ea898280780c1c1017006c2103c054104101c000d008400080c0700c1c4d00610752112106400103642e1242402091420b2803e83d0304c00d8280d800003040c0800e1001c2002154034408141019690960644c0d0745c0802e0f000c2070a040f02d003010345450f101c4c81150344140032040f004501c00c03020400d141c2d0040c450f48c1e0310300c800c01c030540c0580120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 337586321 1250 337585071 337585109
    0x4030507030f0611090d020f030109060516080c040f06050d1104090203040b06030a020603131704030c1a030115050c0118110a0e15090403020f0307080d18050604110103060f0b04 78
    0xc03200760381141c5d40003084001c0e41c84864090064020001e14125415540c0d0340c0c0b4003001985500c01e2031b005041d4113100c0c02a69a0b061409440d5440107803140748914010300040051501c1c003803120084d00da55190640d240e4040e00550006804041c1c040600c00310041000702c1c180c04c065015611540c001c045581c02c0b51112010b164440900e000040d401010400000b800400c5d98815404e03107512400040304151400d010300b540c66040303030700211020011050100821444040c903600030700001e444040c40c65140264003240b0340741800b1100300340300c400b184164503030340298424003034000d1200501c501d804144c40c04a5500f00c071400c031144038140f400d1000c0346140340c0c01e84a5202c0c4408986251155080f481045280c1000400440452161050044480b141800689969403054000d1b03910381d40110740040c26141c29200c5209141c145d81e44890104000241c2c0d0f0760003542000f0071240c07220820004030041c0210741c2082e480c01c064980002462030608000380100c810440c100440c603540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 337587571 1250 337586321 337586351
    0x1e050f070923090a170f1902070e10050d14100c0f02120f070f14100506010c0503030403030e01111209060a0e0a062403120909061a0304060204030507030f06 69
    0x30640d0710203407552004d80c01500046100541031743ca07000003540300341410740c0507444a2055000748000000b07160020503101c84650100300c1000500400780100200c0c0c5480c0b08403421407074452040700e00c0307280800c8411060102c40003001c4030785641e4800b602e5203100000350340006058011040400240c2e91240c5405941c40440c000340c40e08500c18820b40790003021082401c198010010076140f0501010b20000001d0180e510442d11a01084c081d11224480702d41a0040310002007615041c818030854040c0003960210031a644140c0c5400d000450345125101c003030040c10388450a050b0304000040d484c24509084a0580c41010803a080701d41d00c0d0703a00d080320f03401e4481140038000e455200503003036000100c2a0300700300410100440030100707501c585240e2000b034a86650003a2404400074032200341d45da5109990502800700c0040900c0510315003130403600010000c1912801c189030220204040000e950100e4000f50303007290407075444a4403400c0130461000358803800c5455034a42070100050700c138 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 337588821 1250 337587571 337587641
    0xa080106031e0b031612150c05031f0512030c0f030c0d0804060b06040b0c100506011d0303090604140a060309030509040225060c021005041e050f0709 66
    0x11407141c12246030ba041d4890018010342400036034507024030445103c1c03800100111034001e2090b0910f00c3c0440d9032900b41115210790786210b00d1109230400b031400000a40201c21207030002d40440c58043d640c401b80c01801c2d0706c0c03c0c1c160862648890020035030180c0c0c0c000007024080e03a041c000c0645120020b1000300c03503600e21072511030703507055004290942e040324011030805610501810b0049071054580c00000e0070703680290014000301601003a03030a2405010090a02407500c1c0c80800c00a40c1004800070b00703951080d024250404840100c410741546061094a0030f48602824039078903035440f0450103040e80c00c031070492802100c0164000507128801d0160341c41d4540c258681f00e16241e0758805000c0a9800989a100069905000c44010001c01c0081c07502142c0910b40001e1462182e110090400090310a112441400c16082c0700201d045440141440070504109c0032007083d00e85042418801146618003060241850005500c1920f070413260721250201d0044460600820542c03070580 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 337589928 1107 337588821 337588841
    0x31416051501060e010c0b06130905030309010c1e0813020d03020f01051b090d020409050703210c031205072c0906030d121509110a08010603 62
    0x21000711480318007410440c0f0b810202c0410800000348200311284000d0170604042c0080782c1c8070b9803042100f0802080c012010700204585003401d40e2a50011505095954206091200389501c204424466a2404a40c144040260040c11666018001c0c65030130142a01480348015a0b03a200901d4021442980100b45890090505500703403031004e46051000a587c5200710780f07000594003610024071054031100b091001a00014000d4030080b040a803142c040d0010100511811704a100510f404841002c1c20400c0e001130211201c541081020340041c1c84070104980d442e207613030801504480b051800c1850180201400d0248001c0e0b9030022009415000840d140307420000c0045e54020001c0307028184c0c51501c410050401d1010341945990140c1d40d6090b4043c0724000c0380c44c40d0180a0310001007140034070326000306802c1c3d03003c800c80c1c0303012600c0c90340001a054464007841e0040 = true := by decide +kernel

theorem cover : BRFrame.Cov 337410071 337589928 := by
  have h0 := BRFrame.cov_init 337410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 337410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 337410071 ≤ n) (h2 : n < 337589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
