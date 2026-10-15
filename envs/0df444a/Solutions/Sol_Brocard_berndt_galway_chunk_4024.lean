-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:21:43.397987+00:00
-- url     : https://prove2.me/submissions/0df1a0fc-9755-4bea-bcf6-e1d4f761e139

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 723561151 ≤ n < 723741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 723562401 1250 723561151 723561169
    0x2030405030d020f0c121b1c050604030906140a030509010603050a0f06060803090114090102010f061401020601170a12030e0d0903051b01120b0f12160e1b18 69
    0x9540182c0081e0001c48145200b005180c1c801700c81103400300485101c0d03041c8260b5480c19060b6a0000140452590010342c403106154034040c20080c1d0100d00e41c1c10703a0305110360b03a41d80980b01140041e451702c03000200f4502ca8031001640200503a055494600078001c11809070901920f6203425550f078020010000e0000c012916505200740e032116407070101030418100306c2d00d41c0c0c1d0107401981c00400400c60181c0c0d0182c50560302c161603807034007622501511300403030040070880801428140b4141000c103c1c2282d031704c038040b00388a00743d080720601d0b038903141c041c002001e101d581806585c0c441c01c17020b030000b62510914011301481e8500041d80c1200c180007a0b20b00707605d55100c580441c140380c506005100051096482032241c010ba1880c10507510000205011085580c03001c1c099075484c030306030280e0b464806001e1070b41d90082c4002c111204000405842c3c2c03074119403080c00b800100d0340010f42403564500c02031240709450424550f282c80c8140c00c4046600418401c1241c0300c1c070035130240700343d0386201d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 723563651 1250 723562401 723562423
    0x70e210c130506150c0718090c0602060105030c040e0607050a1713230604031407301803060c121e0b01020714040c0c210905150a0806010203040503 65
    0x1000c40d0b02d040c444103000b010304582030740f540300030020060303280c45c0e80001820700200d640c202e03044192070400d05000d6000740705450340100542d19402000400c583e000500340d060322000c60603a40f00e00d00c0c481c100011111181200f01454204c28005540c0170300400c003170030030300e411814a00c03000c9408491201d6007180c21a8880c00c0c0d440b503854050203220021022550307004040030700e00005c0b034000c40d0f1550344801c014401002c00019560344000116070030705580138590701c4402d016516102400001d2240707492162001061010780b007143c1c1d0648107402c02100414085400f181507811929644041c0038420194018040040070080000113a8416911842031480200c00094441301d907500c25940c00c0b00f4118115480340320706200607480300c412481c07060300031540041d44849074001620403c0c0403070005460321907081c480304403500c031070503004c80303428450354586124079110703000c00469400d4400d0381c240301c0509202c4c01c2004e9000e0750700c031900104c0500450741813035500c10001c1e107050700203e5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723564901 1250 723563651 723563689
    0xb04240606020706090b0d0914120403140109020105030a0b061603080610032c07080304030305070506091b01030203040609121805041b0f05130b040e070e210c 70
    0xa02003010716418086207001d01400c0c903164030860b24000d0740c0d40003801892044451180d0f68001c08080004511203041d40b8450300090314003601e0307628010b01c2190030034401a00c1c01d041d204040c92201c1c0e018403e40800030b505844003411900d881d00c4100007016210149504090704001d80101d8280690b14010384602c00d1382d44181e03618107603062228402c038540c8000141410f009a038140020003002c490185c0d8515403010440a04070b00c1c0c903910b049582d5210304154040018040241a4804000c08411380140200d5109842e5000400d644829650300d2140d003041e01c040c501c60542c0b080e0000c68109014441c04580e08140c0c1d02c65a614816110642011451640d20f64560200c0d42c0c032150001c03e0111400c0001e1001c0e20341007928950104205004c001e0074825411f0780501075010703503e015640308046041551075003c07503281e40d8028021051441070000004034054811204500e202d80003901100d103540c0310302041c08021301c4500c070350021400b488002c100170f6244e070224141000c400305 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 723566151 1250 723564901 723564911
    0xa0b1503011404052814070c050d300b03151008060f040b040c0b0403030903020f030303040f0b1506180405010e0106081b09130c0e1c0b0424 62
    0x4051403400c00c010860b11405903040000700f286071001640da89041d5580607840c1c4400d134900ca4041001040f4203e4011342c19001d040074400241d44c0b006020816500c680d044400c01042c4a000340e50300c1442000a00e20001d21949210f540d4803034010050364803022000c085500c0c80741c0c000007410a0210940143c5810941041080e42c803031a000f45001442101c01502c5682890440c40e10403400040005c0c02d1840d0040104041006401c0603400805210828948894592400800001140c030084e0310542200c041c0e50910700d0b001c002c40303005507804100e0f040311944603507900702256001041c8c5600c0303004d03561040c092511100d00038804a80b6071001d10301c110b214070041000b103840c1a0058041605041d00500c0440c0d0000c0e0783e1a001212b0b4071095101c8a08002200b80c1840b680030003076042540eaa850b8040070455030050f400c000e400ba2244107800e215401402003200120380c040344400304200d105404600c0303120340b02d500117010704801c2074090744510024a0501005c1120a0b1051f964 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 723567401 1250 723566151 723566159
    0x20a0e091614030a140c0a0806090624130204050a090b040c050f1c110a020d0201050a051905061309050a0c1203050414010c02150a0e04060b0406080a0b150301 70
    0x5444507002420080201c0c50740ca0380707210007280d521849164010644000000100e411000070440402a0303e0014020301c05a40c403685c2e07070350300d0350401d60321304500c1e00c00c5a022503245940b031489000e03001c52502000002108010401c003100100310100a000b075820040071441e0344030000307240d004d020a0980800c0e400406814441101c00000c036110400034107100d400344030103100f42110a0181c0140c030381440c00c8141039000c0c00070454103804030301c110702c0014030380c028075000b15090000c562290020842a41e41a6070002542c00807264119105141d0720042092000d6a00c00d030307001680506959184820076108000320382e990b44083e0307915400034000e40c0800c4203404144011340750b0400075082030b00c41030b90050900c0c0154040d860520410b410f06a019900c074140d44204a90010040f48070319001d80030f090f15650080c01d04c80c0c00602580c0d00c00001b8101350003800700300c510468527249400e00e4039000f00e40350701d0007500701c01030761f6202d07440b9011650f00d000c1344001c0403001040c2d03990b036075140c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 723568651 1250 723567401 723567433
    0xd08030718090b1327140714032535150901021e09040f090c050a060c021020010c0203040608150d1412040f0f060908030405010507020a0e09 62
    0xd10b8502076030041c100112042c000d0b660640017a1074407035001d18418840458a040c0c2180c0007105030b0341c071344e0744a248400034100440e482004c000c004281c05880c0031403d20006040300d2a01103101c2901d000d00080c04218a000303113007116440d603264140e0341010421000a6520241c0140440305590b0721038204880e2688629800a030401c807180001c61070310b164656242e052640c0d07144000120040030910150b5a103d54004240031085c0300c0741041a44c1c41c41c540000000c65070b02881e401085c10001c00310340340d80a00d007110042da400a010090034406d0a40403039a0306141c000e400d811381c826091041281c007013400340702da0900307254000d0340d191410408001e0803400d00400114000724880c500300115203584500c106201c0d0003081300181c240740c070743c0c030306182905202842840041c00100040e10040c070124072400c1d60506041d000246a1b628800c682c0c0b0b00aa028501c160f0b00100801c002540c0240000d00703030144081c201900c0c143d03807010b0751141404100c80105140c3c102000d05245550 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 723569901 1250 723568651 723568669
    0x10e0420071703070e150f0d0e01050606180d030c05190b07140711031204170609010c2c0d03120605040c0906030906020c030a0f02120301050d08030718090b 69
    0x49a41030f0b09501e00000c0040c4413001e10703010180038900904150300b02c0680d4104503550705c160020001d03541d1044030740000090420340c400c410b0951a01020a601e843e14408455030711050044580d500d504103400c00c038090790000030407000c4c072402d40e90788400903509008800d00c940f03078030b0051401c4011780c4c10700840350b50b00144940304010000c03156031400c4051a081d20300f5540c0043c110552208224046032402404021050450a01080c00513284902070044009411a04191591601e40591603401c5c0d4801c3ca400001140341c101892003c1721008500c08140b440346030030794a419200c10081051521298826000a0803840e80403900311224090000144130070b035020060000081e000034420342860040c1401c00d502c9003150005c0c001281c0668101c0c0303d04509684c0e507107841581c05005211048089009400b60187c0009501400b0058038100c9401030807208001d40550345d016400c0d072000300600244640c840c10200c041c0140342c1300d100030b4084400e0000d0240024420011035003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 723571151 1250 723569901 723569933
    0x705040c170907170a05160e071805090c0c0111071127130212070605180411040b070c0b0c0601060305071b0c0611030c15060a08160603050114010c02010e042007 71
    0x1a65030000304442c14070f4000c0f6581c02769451a044c3c410745070421900307464800580c41158494421418031211403c0d100060000b001c0540080103400a2424040c1d0a80030748140a0700b0781d1085c101d0b0002034140349028544132407805801d00120400350803011110b0100340c50490b211010346922904504060144600c81d114070402010311f42e2402d04014058401c0e40902d4440035605080c02040d501c0e03039000404040c0b40b41546540307032900e95042240a8002c03030300588441c402c1e884000343c4007442e41d0803a0141900e076405000903030700700002034018103400303484d070350800040e01100e05002d00d54003d01c0703400c0d51041110134a1980340c694010101c1c0d002510700b460780e0f0810400307141c2544c0c0008004019030003c0101007060380d50100020105a00d50380f100980e405a15103074801151b602c201c060954030261410061a42c898138400705c810007000c20180030800300c202c664059030152001e5003c510006101141c444070304260162211207030a42201c8441001ca8030303a0800c12195070520542d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 723572401 1250 723571151 723571183
    0x50106121802150c01090203060405061b07030507021912050c0a15050712021608010501180603020d030c0c17010605091302030607110a0b070e01020705040c170907170a05 75
    0x241c03980340c00043c11002861440f5009410025003214003440c01e4203c4060b10341c005003035a00d40e02e441d0a0407900c580c0c0880340e0b150b02c0f4014884040e000040300d410355100503056a182c40c10034800d942807000e0421805c034920503000c2c0c0e517180014443c0806c421072800d0b9106030084c15001d9112414030004150980224042e00040c0021011950784a01501e00340d582084041e1502c0030032140c2a411700c050b840704c41e9014080c8090105103030302c054014138100d480a81141c041d4a0b0f01080000844d0020301000303502c981c0c5018101d010900c41c03c841141d04bc02024000c8041c0d40c2c0394100d46100710460000d00e1140d440c3c090400403440c1881c405039012494070400542641950300280d101d000091102007480062540014420803c01c008200260301c281860043d0925500183c08000700180090040c480c00b080803c05040c02e015050080006454030140c0b581103070748203055440d000388207003130a01c2a01800151130000100b030f03922840c80800070703000c90700b080d040c910b0510605d224441e0031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 723573651 1250 723572401 723572441
    0x90b04060e1c0813030309050906100f090b2b02070b04020d06021c0b09071e050906070818130209010206130302010207020a0e07110c0a2705010612 65
    0x119006008407003121002c4403000303000849400c4100950316030000c040e00003240802c41c822200000c95458098a0098682140c1641e545040107a0780c0d07002ca03031103504142d002540000c0d1901400460b204600d00e4103000303013440e4aa4a6200094220800603071b9984050b02c00000e410341c030010040040d00d207011003545007660980390301e10000d101a200a01400c410f4103d8000e02140fa8140c40c480072490845410038058828100c1c080e00c880c41c01103100d165520042a01d480c01041c45201505104060708140d01460b142aa25600019002908508108503c4000a031030a0040c01c242c103c110300f01003109510002d2007408654070034061400c6204021141d2242e80004616030b2104d6210a10845107810b0320741240a8060144003d402c408000800f054040d4a41e62880c03242015aa03021044003d02ca0010360310b00b00c19580e140c2201070b0000511881d00104503003a5488035181100c0080d01080941c2002c4500c00d07400500051011044808a40308a02912442c0f007881d01040359 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 723574901 1250 723573651 723573659
    0xc2d2a040b03211209060103120807020604120216080106080f0d02030315040b060307020a030e04022b1e05010501020d0f020c01080a06080a0f0209060901080a1b0f15090b04 76
    0x6070f5030540000003812454032800c0e02d608260010304a5400d850041814609030410b41451540c0f801c00780070803111000d810680034815441509164400d8209500800d031549564a4011040d41124031210445c080c1e0261254016101a1144e00510f464000001e80a18100b40701d030402c14015085401c03034101c80f9020701c100c0e82c00026aa040b40d007804040f40d4071111940050000c0222803c160b80000010003040402d0f82c0100702c1d40c09007806a1100101221210108401c9101d20080340076090060100130030301d10b469814070150350340c02c0c2100003605022a00b4010382c541404081000241d200c100500003075905012140f5000c2041c145080781803140600030b526000b070300c0e0300181041503480006503041060380103000100800c606030340d0003014900380b01411801112060b8000c900040c0400c00c0e5040040881c1d0407508c006001d007040c81f604c0d44d1007090844481c001c01c2842099144049008010b841d00c0500806800f40d145034000e4021602621400a41d03100c40c0c01072000740700c100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 723576151 1250 723574901 723574903
    0x920010c0201050703083408010b0408150a0906061e0510080a09051c0306030303050928080c060708041202060601020d03231305120c2d2a040b03 64
    0x100700d251300d41840001645d401034448805154000c0f01010200d0004514500041c01f100e008140b40c0d003039030345a820f0780e04c600c03072a0514821445415040c0d841000d50b58201812000041d4000c01d071600007003480720740f82d03d881c01941e8003030b0000b0500001c1c405900d207690501d80179040042a090f104111401111540540301000007004d0025254695061070b0030000144007032008403160f112441c240c030088103270050091449000440100f8a0b00020980e41480080c007411820b040d00302190000813020000589000c0381d4a00f1a01d000c03007800401644501401071034402c0c7c2150340c9001c039901d0141800c03601c08108a00680554219509001090740c4c04030388911400d101742000309403940102c42150804030054862245201e518083c4081c64032582d500d410480d000d081250348000241010101501c1950002060380d402500f28082e03008101052244010215030048a076100303c1900d94240315242d032501d03c1d5080300c48040520000f041c030040e010810b05540c01c0100c60199400310b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 723577401 1250 723576151 723576157
    0x5010f08060306070813020a151d0306010302010509010908070602010c170402010828050c0a0306080304080c0415090207060c1808250512010b0310050601051b010f0920010c020105 79
    0x40000802c000340d10140c40c1006c910782c481e40508003a200995541d21042c0c0c440e41e1a0340b4100183d160013004002915a100c107500c041c4000b0040c120507440c40d4019281c5e80d10018100741401040003002451050034002030004048507000850400d03048600200b8113411120607881c0034003075405200250741d0040e20b40760b110f0500301340d80d1102c01e1948030890000203d5108660014103010401000d003c0501c058918013a59031028046183c81d100840d44900450241400382d40c4440e03080745c91403078a80c1002c01400c01c0b00e00340c00507882c1c80e52001c009903880800e09541060f21003a1184a03a6400101030460031406201400801c2c140014507468000411407201c0c428030b40000d03000b10100440f1100c0040c8801001481000c00c504549030207442d121002134807d014034801c2d9405c40c440c501507980304600c16036a07103240c2134051040e1000004400c40c13410117590781c2c511030030301b0380e406224135010070703000d41c90060b1851076401e0309070403818204001c1810001d05982a4005076048015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 723578651 1250 723577401 723577411
    0x411040311040b120706170906070807120f09031d060310050103090501232d040f050114010611120703141e0d0f0c1817120708030105010f08060306 65
    0xc2640d0100c00000344000840c004c280a0600030b00a0000d0040d03001410401c0c0c05020003200c040c540c0d940307076084d526444222020b8001c00c401000207030300b40f48120240007084a500000180c1d080c00742e06410106c8014090490100b081c0c05e407440c8080740b5405c043c50341010211366080c614074004003081701ca6025441258141a00d42d40540c04200007034000071741c690380e69403d040700011051039004590109075654143c0c13829001000841c00c0c008c0c2a1035608009543d1888041d071a1a9160001500342030f005541555803080c07000640410510114020885c550701e01065021841c407443c20711005045101d8116410020080080c1e00888a090001351400516858080100d00800320303000b81c064080a00000081440e201081e40e840f0726690b00001c0700412140e034601d41b0584100800d82190400c21a54000400004030080f5511054642400039a401e126041c008005607421011048480c1078000c00148810350b44600c551000f02043d1524084030708255001c03e4403150080c20b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 723579901 1250 723578651 723578659
    0x100c021c0c0203010c03020702090903041202060d150e06031216060b060f16061b08040605090c060d0204030b0f01030804031707120201140601050901090e062b020411040311 76
    0x4003010086028426010072650041c000b0b019071406020020025030100204034410840380780801d0f0140380010542e01071700c244040071045000c540d0200056608007804140a454850303180104100100c090301c8000c0224500400d503900b440030806080124008100c4901c100510428501c030707941014907403c01e0342003080026038801c0c10002c24524440c41020b2031840da40040c407045ca4194843c00d1194183c0a03ca040141c00070025003141640d01e50b84040c2c7c001681e4002080c04644140d020315003200100040741e000d4041c441c0403907180c0c0c0001118441103a0f01080c20024010390a840981c0b001d106200f89502e58150341d02c03c182809280000303850320200075014040301291408944100c3d8016203c00800c80c0c1c41807009000e40f80304100b0020000300180410010350003a800e803085014141c492204942c145949e8074942c903002000154890982a80f2181688040451007d404150f500c101c04000d002d0042c0010f91b00307180708082e66007208000800114003031701d0340550155002c45d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 723581151 1250 723579901 723579943
    0x151b0c040e07180b030d08070e040b100f030e0a050a0b070e030d051e16050c030106061b0204060302100f08070810061107051203070c081c110f0a0311100c02 69
    0x1c1c07034005041400240e0703014030401c0146c001c1e84c0c0d00f0507545445010282d5a08091111030701c24401500d10001e075035500401c91403c103000c042c0c0181c0303404028684910b40014a405413036001d51400c00e03d10010341341600070700001428000f90000e80c644c44599800e211110070390f01e10110344d44800a0b8400b204001010071881c1d002c1807040c5000c1c402012440c0c00c103485060b010548248202005800c41e854841e045003c02c950030180240400c0f1034503900c4950400a001e82c0f20340d90050345400c00c90f80507a13100c1c0044010380d200d450075045841260b480011144c480000030b4508040a0b14400c10300901500300300103440060418000d44100d407031b20358025a022140d051a00050ba00326650212011030609141c65000015216142c000c1442c0695680c1c1c540d0020b41310444d91070002180d000e0308000c042007500811b2400e0781c41d04103008840d0700301240b1110f2707410254a14021400103035040100d03000018100010300303418012980400c00159140e10196480180c4841c88d242e01072a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 723582401 1250 723581151 723581189
    0x903110f181f0605030105010e010e151605060705032e0501032a02100c03020301051302070c080d12050c03100311030a08180414040f06050402151b0c040e07 69
    0x2010b42000c4100103840001034040e107a2402a180b0340090003500e0000700d4a0203541d1942d07102d40d201c0180310394090024074010609050048a940c0090105001c001008a0703039000600b0800900c7d200e00403070759038203449091052419074000c1d407680030100008941a0720310001e404a83c203030300c06c542c001d0800082c2a0560010028107100080442052002c0c0561000c0c0c401c1d00440d00303502190b110b4404116030b040e80c41098040340001e004507508251000c646540045495000745003080c0907014841070b0315503031681c2d80c0c9099441e0b002e003800250003400c0416481028014260004240d0b681c003411450805400b04800503144000340c450351148041d4165910140040c90106410850b03c90b41d880424903000200e001103000385015500e0080030f0204040a403d4060281f0303030080c004003e41040703850300d03005000c5c0a0005e0342d0204101200310401d9240d40000e001c5040019800c0c8204500116407078244190004410f004a040012540f0038003030100e07030303031041c0c840c131403c4030343c2000f64 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 723583651 1250 723582401 723582421
    0x5070e2a0a0e030d02060405010617070b0705150703020c07090902060a0309060b06070c03050f0304030c14060909040f1511090411070c08150c1204020d030e03010501060903110f18 79
    0x344840d03c3d014012002a040c038a940403600c2c620942c003c2c0c2c028411076a80b80801c820881d58102080b40d250481c0a0901ca4080c00000605130f0740e004804841c035030b119404840700131900075915140803e60015560020301010703c0403d0003880c803480d08100c0d400040d0045502482201146800c00d40c0c2d8058103410031401c0c2d8092012608042d004070b4841c55140b51280641d1014041aa468840c41d1000b4505c00d0001003124250b030b5002140013500d5140c81000007a02c9a4008050762014080c4040f624176296441e41a00c40d074020480994034a060703043c481b250fa008103141a000c1d80c00c02d129046440110030440c0c5591009813000142d00391151240c140900412a00820305e15000c400000c000300000303a0309070070203140c08031007640d9206d01588940b14444c88120840060900e0001409881c094800c6801c0b103009042c4181420303220b41c002800c41303400b604510003041c0d00031010f10030300c000c00c1040c10300828141c41054404403d240018120b13020100041a181d81850015480d042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 723584901 1250 723583651 723583667
    0x30102070809091807120c080d0f08041511040302120a021c0c030203010e0d09151e0201020d0f23010506030f1806040533060f1c05070e2a0a 62
    0x7110506072441c4944400d20401ba0076000d08055030000039044d800302c0c003828042241111000c0684881700c036151080b1040d5942ca4000b40305076044665107546c0e2607005818000c04061808401c005135440b411441001603075a14070b0304c014910b9020104060068a0b1004055080c40030b0780ad040c014a08a850488940c05c2c298100940550a002011442c0c440009a0751440d9001d51504804151034601110440020340e45030b01c00213081c4031002d00a01c04801d1100c061503040d10015191441a00002050b00c07005911040c4030791340e518050790017800b4071401219090440740d081540c0d5150500045c0c20b4000a0046a1030310310030004180c081207030700c000504040852040d240c03285400d00b42036486400c1c04c8030359038941d03000c001c001c007550780740c181003a032010149440d500298540009011188a11105907a044804a141655400700051281d002c06200308000d14900303040603140c0c0d240702001b600101640e4001c0d808004510b5100c082c2046a8103d484800d8582c500c44004a407107030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 723586151 1250 723584901 723584941
    0xe060402221a1011152e03170703020307060f060f030809030601050d050a11011103040f050f0a0608041101140a0e12190807051c02031803010207080909 67
    0x586440380200c000c0c45002d078941d8090400f200d60081da151448070680350030402c01e244601c0f64200310070702035203110001e2481c1e8010613068144d02949400d8124480c0c2820000b109a01e0000c0c450001c004000702c036051b445058040d02001e905111140da8069600c0c024880c00a040503110403600c450200d46074041d0b4001c0c044005400c003200e55a041621999000e4615075020f4021140042020700740f8403451920954828024064103406440c0c0c182d10610251941f4104482e00000303c41e1490f00300081c201400d00340102c11b042514110030800b61b0420105054080c4480e050708200654000d0030070b9620541021101071514007000c012100440200140b003841207011801d102c2c440d91110028041d01426100300300c40e124503448490703079242d16a585840d46403004c40e01c00f00213080c1c44094101c082c840c00845001d42c4803c142c1c00c09d507030301c0b42510f000140d00115460030044040103000c02c00d110241c000718900340e5151500501e910588441d01d002d070b005a400b0441d00148000c1c86032400b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 723587401 1250 723586151 723586219
    0x151b0102030c0703020106060905061909051201060806090d050f030a110a080a0c11031c020c072c090706080718260303060f09040c0909050a030306090e060402 70
    0x40e02c2c1c000666070058100150a400541c070b0708001140090180c0c0d0404143c070700040c00ca6041101c2440240c8225245504081c00c126060b00009400e880d0328051441d0120400c0c00458100e0521060601d45030300101621a207a2020599110325500704003110201621280e5150b641c1d41c1d900f04000c05400030451080c07010038000783c3d8104a80c3d0004017640151401c3e0b1044c80308164050b0116000410b10a0044443d0010030210848442c0717110104810080480b000d41090801340443d81018080d03400034030304007024042011403c100b15001800d0404141d43c2c8003103402e150130a190381d2421400f655080c845104045180c40e4002c00d540303005018481680d040440d100e8101000d91400c0320900c24a81170710100798030308a000030003564460100540280c0c0c0900d0190300b001804003000e4030035100152003181c0441c85210a00030b11008038050300090580d05400d2400904850003640b0000700d4074038010381420906400300e50140c00ca60100c404100d0b11401d091840050100301042c9411 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 723588651 1250 723587401 723587407
    0x8030c030307111b0616140d0201060e041109040f020607030906080907060c0605130b1e130b16050f2a0c0d0f21030207120e151b0102 59
    0x144840000040d84981499914515aa0022080c1ca60303250910205030a0040c4076105a280c1418464060003194401010380e9810600603151100da95007079242c560003070303007041100b4021542c090042000508600c2102591440d05d915444284075522031800e1241c42c410f800b1a02340000d1100c586203058004054a984282d1071401900510492140b0307000324101600184003140c011443c03004640301c0c0d85032841c0d102d40a5845400910005000c070300091b010f042840080f608048100d4231602c0c04d4400310201c00c14101c1c0c3c50210b070b24010012074202807480f101c0c40000e034a0103035850f0412441e517440d0480298040701918076000310b9030344205852001c2000103ca81c920706000c0340c0d012801000e51105000f43c28070548440c95207071019006038551100c000014561009003803442e0140641c180a031808800004041c1d4441c90090002034002c5040418411040403842e01d001107420400c000311034900c04644030a030703003125116103604041000480e20001403a10011459460001c541d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 723589901 1250 723588651 723588667
    0x90c090a0902190207080304080307080c1006030c1d011a0c280b10060504062307030c030e0a030c091a0913150e0601090b01110607030e10110304080703090803 70
    0x40032000043c4200014030038000c0005012401008aa0540d01a100950f1411003291103051306a0700240070130040c3d11442c8145800c42a1510594020354032420090104502e00000c048030400b0b0713902c08500d41c0a50304010041c00216441226a80c1464150a900c808105150030700f07190f103d41c65001e0f07030349103107044a505c190700000c828592442a20410000d80b69901c00d6041c40071103000d2480030401c00c00c000d01019000f192008a861240255040310b85c060301075900e155048298100d0215016100646c105074009101c2071440c00240c0b810b0704420711f181c40340d2070149028810200358075643c43c091181800e41c959558140c3c0341c003420040a0341010103691010074034075141a1915800d4841d2003055010f10b01943c02001d90190040940b03900b0705103800c0080c031101d08528140110000350031904182840004e01c41c003070035107001800503003d081c05405c010491003080c000f5880c0c50f140c01e182500000550782c0041d006408103884105a142c01d03a2440c0e041d03040a2914070011981407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 723591151 1250 723589901 723589927
    0x100c030209150406020f012721050d050108030913020a05040b0309070528031b0e10060f0c03021203092805070501110a03030911221109090c090a0902 66
    0x1204030340b2150700320b0700b1b242c1c500b030745071400c0f19004204288013846074020b01e1002080d80c0c040e0481e50b401b54091101600750905404040030072440b00e00007150f408100a013450701c9500c04d240c01081f0008c0070714545001c050000d00912906841c04040030b07404901c0148076881101950b02815500c07050a40d00e00302098075a0b5160414840c2c00d110307240c0d11a020120302100710b07603030240d000424086000141180d980700300d0035420403c000310210400c1c50015038066a040d00c9070059070114507044625007403140c021f000300940c15920051002c2080d420001950008420700c0440d03172600441c5d140d8030790496507070401c90341043c00152503207007a0ba041099407001c41240300c020300c104100e5002640e00c3d001500d04507910001d040b290740111010750f0109011750070004440740b158000a041200310300000b2540002e0100045250009a00c200109145881400743c20000200e40e01d0030074130108006041060b00809403c0080404a0040d10329240ca04101e80908000081552102100300b206 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 723592401 1250 723591151 723591157
    0xc0f12151e10050426011e0b03060705210c091012180804150c050d02070603201b01110d0f0f0504210207030803010e0103050609060603100c03020915 66
    0x581c4612000c4901c0c41c10140194121011a0030780e03282d4041c4022031202e82c007402c210705c1d01404025500c0701c01c0301002020140ba0005140200e450000e8900c400209052418000401103020b11808204204011452007005c0300d01c00d02c007101036900c03585e481e21a8080ca020742c440d41d5070819004c400311002c0a4201d000c91074000066072017004141b1507040d000c104010110805403103224100f00c2407280074010400c0c420720a0081c206451140202d41d506442e089810314000016001104140856a41030141e00e013596810251482902c2d2985800c040520410100e54015024101d81190041c002e41100740304e5405420501d2b201c41d14803c207000505510640e0700c01003454480c00207150055441500d00458010b400415503007160f0102c480c5062168076090705510500c1000000602d00c08000e40c042c003d18508483d80d540b45d8588203103003403009410008960080d03001c11400e500c001034911001d006490012038100c1e50800154001e1280039101d9400a42d00303c42e22850080c00401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 723593651 1250 723592401 723592459
    0xd0603060204060210060e07031a0312040503010c17130c1707060e0d03090603020c010f020403120806010f020a02060f1c0603050601090618110c030d0509060c0f1215 73
    0xa1718205c0c0b800d03403a81400c807920385c05580d40754030402d404910b40c0d505c00d41c05016640140344440f02e460b070b0b941c00000c0c0381c0280d02214162220000500f488076017001e0007020100314041c14000ca95543d080480c0032100340080c00d02c241c0311644503a02081c000c0c3d4148000040441034200200b1500101c40d00ba21600f0b04e0246201207501078138181d580e81011000790600c5505959825281801c00004034003a42c8094800d040c0380d0340f6000100141017203480100021885080b142850110000c0007810f0700500401c1541401154041c41001341d4010880313022140d41111102da88904c4440d40c0c4055010703c01681d019000c504003000880c0180d0707884141a68005c8080b02c440d60b0707880400d0019106503005030089154043c1d034040e50b900c0190400c2500f258040303083e03030510010510b4a85103800c1070b40b145140e640c403141808803a2030148400fa4010541c0511140703005003408450f45a803207021a1203941070a000000381901d48080301d235000c0703400c004005403d40031050031000c540c012070b040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 723594901 1250 723593651 723593653
    0xd020f131410020312180313090f0b0a0e0c040e0c0d0e060705040b0f070b0f18010b10080406111b10060311060d06090510090507020607081602030d06030602040602 72
    0x1005040b850400380d40600e0078074590045141c40e0030343c0300303042c1c4400014008820242e001c0d00301e41207101003400075002000140515001180c90281d07120241c90001e866103110600c0c05141801c81e445880c041000e84a95404659003516906a110054420350703010200900c100d0302070068444100c00104849038038124180035128001d1000380c1c4440d42a0340c080f02081d8100030030000b84442d2400b610801260150329424171106844403003c2c403030202c9520318144032090404c60031061610403040c0345000c441c005c000c400402d40100741c80190811014050049180000d0300b005056000fa4544000e44399045440300b50b01009907240c0c501c0b40103442118025070340b50350b142a50310721503074040740e800c0000303158014048410300c6100e0788081d01841e1130544030705001c01e000da080d0095501545603240c2c0305035500d190a0440c0100c400c090281c0d400c64100310188403140381d1000040b5000140501c480d40680311700201a0b15500c82c082ea0740b28803d0410200005015460f40a8030403604960 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 723596151 1250 723594901 723594929
    0x50a150504060b16031e1e09061b020d0b1f0f080303010612090c140414130b100f151b23030d0e060103020f1512071218151802060d020f13 61
    0x54082d100040300340603075030020b55104491980944ac0050603081d060001e000d00c0e00400c00c0e81c0302d00204805c121400300c2c101c40e180c10540e1460700014100070042482c8044a082142070500321a201c1c401032003040c1c1002400d016031090840c040e4051010913034080402d50382103907540350346004030301740309840c0c0d2060f403808a1030038060254240681c86040425096180d4404580e9000c4c0072aa000d004241003030f0700c001010a131a01c3c282e1500014255449042c40d240643c0c0d070000380742900170800345041540800100000681e07842e020440b0001d8800c0000700b0640c807041c09485d6000707081c4024801d90078814413401707440380454564162070003500c00f86440f96800052284c400800495160042d030100000c01c0c0d940544c404668200840386458500d035800042c40000396012b050b8410038260100c401c50703080258181d249011a80d002d2014040100500301a0360002400d0707034040e015100000c1c000826100c5035044882c4940200300854854500d04450010342516008004000405c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 723597401 1250 723596151 723596207
    0xc0b0a030c0e2707050723070b0415030b12070603020c060a090b04030503060a051f03050907051c0503040e04081e090906011b06050a150504060b16031e 67
    0x8010405003154800c40240180a006034a483c010100821080070004144040fa0000b094a08400c815204c440d01a8000295007169181003040a43c40f2080c0480104000c1201ca100901111400c003081d090000d000c1180a01040d11401e520000d40d50702e009043d00461801d8260740075083d9030140c0021617507260394010030042100d03102400500002101e00016000901c5075000716403110001e000388120b01e5071800032a80d008000c881d0f40740e95205503807450710300e00c0e8980b150990185490008150251030140851414801d50307038484801c03840c00415100b400003c00c203e600401c3c187c2a410500c1c84d203400d02ca403c2d900a5203d002103144504902da00c2d00c004d40050741c54180d801030103a103050716024015145005140115282400c220745460007003406403082c00c0c420009210040f55860b10140034010945480e00300368850303480e04c4400e00252084030305a540007400e08608030300308540782c24252600c8001c80d48104001c007012695070744041d0700180341000141c81c600202085242 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 723598651 1250 723597401 723597409
    0x60e132a0e040c0e240f0a02010510151409091005030706080c0306040203040302010b031b0a050603130305221409010e130b070309060f05011401050c0c0603040c0b0a030c0e 76
    0x141c520710f28005080070001045501d4007480994400300c2c1c401080c1004091516903200c0b94121034601c800514000c1000520f00c0d40a0040c90f601c071a80b09a0940312608140200354400c10b2028490100a48201040c3c0013000b100210761801e04002c14201c05803030071340801c2c3c0c81050140201030080c0070700000064003038003410120b0300a1450303400140c1103907502000c0c00025040104250119901c1c1c800e000a0f07914280306044002c080c840314080410f6152042c0f0500302015808a07020701c6040081080d9640f0000310303a0846a8035283c16a96016240c00c10003035546a00c90b9a880790202e4880012800d102c1000351105600a442c80380c0341c0d03030380d6444920700f825048861007e0024034580c00c9c1d0028100604141d0300080608001917200d03115120a000c40d01d80c2101d00102c560754500600506c1c4428800a5040d082440c200c0d02d4080c95215a680315042c10001c1c9d40180004800304042054810421700074014a001980c0c4512000d0401805480b003d0280c5010400c0c070a950011820 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 723599901 1250 723598651 723598661
    0x21008070f2102031306060f050102060406020a1e0f09120f11031609090b01080a0f1205070609030818010c0212030a020d090b0405011104060e132a0e04 67
    0x5240d84801c2a41c080307045042e00d990020741c6040c007400b07070740b4841c0040c5222148051030003040c02d0030030512520100d05c0c1139030858403980c0050890204186040000e42c3e40003030010351040d0700001c056225142400e09480500328510703901c412091004d04403401e19444004c25403128801d51350404601c1e40d904180030380c514a044058810002402d604d80818035880c252100014081e00300c0c0d0382c096035008014410900c6400504540f40c0722140041400980c0704814050f048142c00380c10220601c0c0e4808600440d02c04008040710b0740b03450b080c04414000c40580f10a10703004501400b410350181390003000030700216040310188050307500001d40c0c2c40c814429407040304281c1d00184203d6030b80c0751784500d194000500b034810140e001c1141101d0051280120003d1a200f815924000d0400e840c0440c00d540c1c92203904a0750b508180010001103074040c803503040044065480c1d04034031000c810504083c0903a10710364548102d0b54581c0984205090000c51403210a030f5940e40d2801c207190003003105480d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 723601151 1250 723599901 723599911
    0x507080f010e1504020a11060a060503060c120631060302010206090a02100315051c03120e0d0311070203340308040501050f0d15050906060a0807080c071707021008 72
    0x355851091501403e0560040031b9002980c1040803861080c86070306894100d04942a2117255120700041100d803d042040d140c00c00390400b00541028200c125000356000020100e602c40c0c05501c070405014101d88a070f003440380d4901181c000f9035a04d81c0900714060001880100d00620030140010290740d4042020442c541d8010003208001c1d29544007100038281e0210f1400340d03000300080000e000c0c0d8542d48814040e81502040c4151803501d8180a0a2000b01c5c00780d40382c5c0c00d82007407a44c8010500115480d00c8011007401e0020b20780e188100101001d00444000a4040c482d04108032002c01e400d010007940d6482d5410900d8031400d19011922501100f40300c020180390080c030050001c0d60203a40680540d0000f04562800c091001c408107055a04104c8086098580d88200380306601f0b1122010b980a10183c82c01d44c0b8002c1c40d10401490750000800040800030460f012411401c100c4007103541d034079040040d4081e1f081d04808034502d03a44c4a58012803140e102c1c2c0d140c0c80c10850150804900c16 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 723602401 1250 723601151 723601171
    0x506101a180103051509090615060c07212901050d02030307230d0509010806040603110906060d060b1209010c08010b0d090c0e18190f02130507080f010e 67
    0xd4a8290010b4019001c00703003070317480c64005210100c4120345601c0c0f03030300344503509020003815642410354900c08240079111085024440070803000d20394100008645003102e03e4809000c1c100c1d41c1182c000c1d90314244030700008088901e1140d242c00364040d5000a10f100068070180075840740d0f80e0700100011031000340c00081d0950801e010000200300f4105041e007284c110018407165120000b030240d42064403040074070380401d40100b140345080d68002c0c1840d500c07290554080007580c0c1507450352000008008021880343d441c40000649ca42c8420080e1900e205c89120180452174a542c440142a0807842c030a20006039958005202c40358140030700d940114558071040310300d9007028800c00c080c1e03100b456000300d22900c40403d10006074505041c1c81c02032960f040d58a040b070520310500c0703a172051022030710442c5038081c488121222400100251010780e0002000720700000600c080346190901c1020104454504002c0050040e082810144289114144008a60b0f07e50030400c400c000141c0344c1c41c001e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 723603651 1250 723602401 723602437
    0x20d090326031e15220e07120203011808030403111921140307050a0e0406091d010504080712032409140c03220506101a 53
    0x480e40c0450241051086040c5480798030034190111815944181e5000300e02c41d0001c030315440800c620250503030300040c107007860340400112003000540034500740d1000c3c5000650110f0f0280d84074650743c445600c000c403281c16a6482a5150140c5400301c0c00803806900950803c01350318566031543c190081c0f4103500c584101c0c10340d00c0d01c2c0c404551171408084055038a206201d0350401c000c0302c031100b03903140c10300c0340352581d1081c0616040c01e8400a89012407900380080c1c1ca199801c420703807050640e07034850b00d1483d2580c0c4440c40d10328210740d03034280c140e07160703402a107407030ba001c01c0c052a160040100010071090803030f000030710b21080c42c0c207c45049801030034260702400300d50006001c0c0b503d01c2c0d40c604107510780401c0740710f05685449001c0302842c021056001c09880200702061050203005048610042c48041c01e241044890301e103840002e0001c01c15072007100d4021040742c10429024400354114084075240d18000f80d001c031070071a45005204200c0450003100c40704445c140708444031211070400c1511 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 723604901 1250 723603651 723603653
    0x4020607031b06060306090c0e061f02070f0e01090c050a12020904020c061302040e03070c050d02010306031b06140414041a04090302100c020606030a0f05030906070501090c06020d0903 81
    0xa00e03900c9103a00b600c407041d030700400d20041482030080344044c6000352400501d180c01031816151000c1d40341d02c84040002e9100401815566407085400f1a41082ea4002146000084101e090100070380200c51822240c0c07101248070001c0e405101d06079484114104484034603800103440c1401980c084800190f6034602c0e8006140113600608080070010304003604040c481c191060500404942880c04110502014015850540550309102e52640081c6103020071036203134000c40b061280101c1c1d00031080390381b9441c2164446c1d07211030029500110103082c0c251543c25588030006403880346c82c0000301d03424038206015a03104103c8044508c0e500410355040810307424400900110f0701503054800d032400307606550f40c566015a000682c441e0b17001d0100d0010b60000a0111030050304090708550000e42049181c0c0c0700003456040245c1c000b540400011842d00c0e20034618401c3c00c0d01a40c0000011840000b000700c150881103041d842401a001865210b1504980d210a0690320b8000a080748000304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 723606151 1250 723604901 723604907
    0x406061a04060f03060911090103060e1605070f0b0915010509012301090f060512010b03010303081b0705120307020d0216060f120614090a020c0a150b03150a140402060703 75
    0x203180f100807800e010941550354144c103c11910841402440d41100080c1509030b503078144280009011070212000d62400d003c0104982e01d88421050001d100e03000070500180301c070000b40b20601e40d601c6000c0184615200100c99154620001d210503828030380400414286011441703203050b01c844086450f52060520550540c80c4032590209060020780301c0d010641002c0d00344840003400c140d40f48cce282e030b4034101c0c840000401d00503400100d01607402d03c01400000d6100c262150452031860340d0046e41d0b408140c81501c0d82c801d0600c000e12511800030803901c00b01006018600c10034283d000c2d9100720540ba907060307072200e0102043d0880d040c401d0a082c0080c900900070391142c88180d2030701c2c552484a446010302101c1113a0403049110300e100c800d0b0301d000e260002c17451b54031044d4424190704100c0c50100050707446440441c010100b4002c030990300003d03c4650f1158a45070345c01002c441c1c0540d0076192803030000800b0784000c50000c2c1080074041c1a510f00b801c0c482d0140d5405416a4030f4032080e503c00f2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 723607401 1250 723606151 723606167
    0x2090f010c080d0507030b130608121c05040c03110306100302010f120f20070c0302060d0f0f0509100612080c0c12160e0618041707030302030406061a0406 68
    0x80b00c4070305052100c40a01440c0744940c52184e40281c07400500d07100310504105c441400c8000700030425003071800520030240c0125200084409a44500340c0705c0e4035008aa082e0301c1000d60071060103034600b904010500041c100060200c90040700840455081d003001e060700c81c0e8040310000071192001c03008100651140c40034621307000d6189400d020034011403600304142c070f22110243c0e0340503440c3c16000d900907a40401208036140341e9508280f6204040d03450120107101440041d2003001c02007a019a5010f0707681106035004181c0301c04000c0d4005800710a40101b00907100c1c00b01a00c2440711803003907403140344940810344000a250040c849038569502d42c0540c03250111f081c4501505886e20f0307258444070406441d400c003040c003511b0718880c55924451135a80c1c0790b100b000f072840c220007032048a031280500c10400701c1d01030b4840703c0e050b82c1d9030900710040700074400000b5604c0300000b88141070662580c082c40c007031403041e81c4c103201f8a5503e0309044030304603c2038641d803400c0008102c104207940c062851 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 723608651 1250 723607401 723607403
    0x30d140105090411150d1a03030a0207060e0d0c060c1403042102030c040504030906080906060f0409051507030204080c06030103110d0f0f080d0c0f0e0d0305040315020c1002090f010c 80
    0x6200c40102c81e0030017403800c80d0041e4541d504260b0303c40b9000c0940040c00b51010030054000d800030740c00c006800c08001d59482045c0700e4001400780b408000045a103466050303070143c03078010700c82884a60744d0780b800421120052000391280440c1d1540d45030b400780c011003150100c0f00003525822044c020a0303108092502c107208200d030b0520511507526903644450190900c214060740766071520525111018141141c020580030359500940b0800c0701513035810004448422041c1c0d4005080042860264070705983c07102d401c24030440b54003c000d0701c41c0d410740041060f00e6001040d01c5a00d90f595090002c540821300009101144455070003500c3d0030203003443d030b075801e0040c00686207000c02d544510400401c0000103a84c10407000941e083c10103401d00a43d58480c2c002c0c949268100c2074540000c0c004e501c210303a5603101d9a00458003000341841201920040c54001100c0c08550a212814000a50141084013003d0207480c19019141e020392003616041180500000800076011004694000003250 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 723609901 1250 723608651 723608659
    0xc0e15043c0e0105010b030105030f160b0a030f0e030a02010b010504080d0e0d150f0b221e290604061b2102010b0307120f12030e030c030d140105090411 67
    0x1110090b6030301e0901803d8005c0c2a0000220750703a50522040c0340c01c024500d02c0c91001036105110103403a40e03080c2005003040f900241c24103500c1f420b0b600c00c100c0103031803240c413003005150030042490559030740400200781000701078008100416000d8010741c2c050195100d1201c03070307070480e0080c2c44070b090240b1540420400c0041c2001209001543c3d80c220714120800300d141129a42c00c03000034640428401c4084154040b03070307416043c2080618250340800b621003140610b503124880f903041c0092002d8916a5840f580f602030148010900000c0c0f480b460f2aa1406c144140300484d440301401d00500300c41c02e445840d40d5440c401407000c031401c034586c28071100490700c0308140e07080d491144401242180101d001f6030b0001c9980b03114182010700d060300c107800a00840c3d02e01c03c1c264001880c2e07004c6414545501c02d03c1d0b900403244204050300100f0380718842ca2040e02001605005501d000310042801e4045000e04000800720782c0d121421100c0240281600030000402160204461900c68944550010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 723611151 1250 723609901 723609911
    0x12060a050904030305060103050a0501032003030d1404020922080a02101d060f01061d040e0f0303010e0c07020d1b0b041806080102030702060f040c0e15043c 69
    0x18041038116004582c140c00295544060250703030741c4d02d801980c0e00054402070038003555055468516400203e41c100305076200e00815404a40d480074801e8865030003064104222030713044031a107108a000116400c92056000320005502c0055901070000000844614031642403807a0f91041c015900803040c11041d44181019121540003034000c1c41c2101c1c500251040c820043ea400c41417a001d4080c0c40700f00e01c4802c0500501650b40d1210340c549003843c0700344016444040420200c0c000700300d100041c888902800c500500b0780d02000000b1412600c49a0341da810341d54890396801440c2c010403100a40c8a5202541d8001041c4148844030002a1040600b52055070b00e510160055115603c00103400621041c6102001001e00c40d42000b03003102c40080d45146042c0000a440f65002051051a142c092000c1801e002c0da0841510180c40030385202481e40c00c040e09080505510000c8241c80756042208031240b200c0c08070013040809007a040c05c0f042200d580300b10034110156907200740c820389551f9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 723612401 1250 723611151 723611159
    0x330503040507150e01030e010506131503080403050c030d02010b060403170d050103030f09080102210717040b0411060703021e0a0215130b030f010306021c0f0b03190812060a 76
    0xa1003403e0541c20103455807100300412000150943e4032030070130140e0781c0e40750408004d8a5224001e801d02104201140000c00c9500100c43c0326408815401c0500002030100d004401c00200095070051840120202d07a928614003208a007a50405c40071310b50042003d00c41003001070041e16407200020724085940b800c0440a5440c070b0215002640160000744080b03050f000560b0300b002c0203002900c00f4100075440c201342c2c0408010010234160f81c0c102100342100018214a10915100341e2001c01d410100090382000d040070812910142c4054074203190100c5001510301e0a81c1c1203070511541900548200740d02d6030b50100100460024021490086000e2a401030b5070301d5100c9503082e5440c01c081a150719108140c42c0c101e42c0d680e0040000400104144001b00e40d5445150341141c0d0301141c05661802c84246581c8030324086402c0e600b150742400c3d00b200840d40c1c2c81d0070075001f00c034041e030403640310180700002c0f22070080e813005020f4140c0303500301301000091000802c21b6501003809003019620540e0307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 723613651 1250 723612401 723612419
    0x70b04060e0a1112150103020607020d0f030809011506120c02070803120916081221010905040204050a021306140403050f030a1e05160f02060310330503040507 70
    0x100b40040322460101d818400d22842c0429010020b00303109401030400c01808418044e00c0ca8040c00080d10508000c0b906404540d2410000c96120f54004440d0aa02c01d60f854062b00381d41d030903500442d41c2c2d400d245142e100b070319802e400c0324115050f6075580000c4900c120410001018041a00703003c6004a14020541c081d04000902640d11703601d4241c01d640c60107401c0141010400d00103206031801e501c0c1c2c100600b01c00001c0080c04803050340141a6130701d40a1a03c40070070424140b0540d4007580c09000004c5540c0c0707590000d88070314001d40d4140502c0c0e0365880d60740c040340314604031099161307007003842408040d10480001e5000301c024105649000c1c0c480e103d05141403a000c2c2c088003a68400104100d980754840e543c2c0918007461280c0d40414201da807006001402540007410030220100c000505119403000c07030780300507a0090511540e1307090180d060017205103980207160030b801c02450040880c055009080000001d2003150000c0402000011255640044c1c415075492081c501c1c0880c003c0b107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 723614901 1250 723613651 723613663
    0x507030c0f050d02150a0510030b1504090c0302030c0108040213090501060b0c060702070b07051e031303110a1e0312020a0602120118020307080a0f020d0204150908030a05070b04060e 80
    0x1d8250000c1400402d102c0c0303031800c1c1c24002050411b40b507041000780300b440e00c3c04604640c04d490f40714045d1045070340c540030b410503440051140710b58000d04101420f001e01003020003d41c1521700a4090b22030442120006403030300d100c01e65000b03400c842c07909600d0320040015402480d80c14460000800c2503961a1545209030708960405043c0e50000070902103060b4041000500820110441d1810200241c98490310744000d400c0107e00750240d401c401101c0e080c28412910340c0101075100e081c0c000d40340e04190b240000f01030041401044030b03400100e43c102007441c0011b070141d84107040e94065130460790381110582038004e0340307419482180c10090000720303580058101c1c1001010502c1c0c0f030b507141859182500c140c00c82c0800c100f40c81001402000b9610102050740000814808182004c0d6160364000a2003002200c4078000e102040100380034492106026000c03566654200d03080b03465000f044e4481c801d04103144081001046400005010055000d62180c020003000078079001883e41d080c2009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 723616151 1250 723614901 723614923
    0x60e031005041406012301031a2d010513090c0c0222060501050c030a1d0a06120e010e1903090906080a02031c0c08030613020a050d0e0a030507030c0f05 67
    0x48036451100f00c07020080000310700402604072604200504030008042014000708018100750300d801c0004101c44036800340c0390540301c000d4043e410a88004640003c5014841c803000b0b02c410544604000e150310440c20350b0a400140712182031001d00e0200d00c1001410b10034207841c00d1080b0f4000400159403003203020b80403441111200004a511610741d2001c840341c50708654140803007480007410200303000cc20343d0900340082c01e003800c2c3c4542c4180c0c98111141902c8003541c2c003d8001c203012038400d9000c0d4500115030410304c0c09101e10400c100c41e5609075040b8507030031075180d0712014040021510030194542c032140a4108001d1498851002000350f507483d800500e004d9000329010021410701300000e10000c10201c3e0302a0030898150070080c078048e035460010b000302c1c03004008145d850759081c03811011380f454104110350ba02007800b006440303078001c980800d06c010300d04120700d003201202240300e40c43caa52556810740790040c1940c003921610b401402c1034030b0000079900e420713000820030090746001d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 723617401 1250 723616151 723616163
    0x1a060d0b10180911190903052d030406270b0a0e030c1923030604050c011e050915090a08100614090612030717030f0a0b0a060e03100504 60
    0x2a410005120381000c0c41ca50090450074a0804411a803000f02e4003920301c89001c2020118043c10001400c450b0075031640c0001e0000c0c0642107214500380c0c422407a0101c1040d1403190840380d140107541e12754590140d0b205810100303000401c1890f20301450405513030307101802c0203000340c41a07d41c0c00075142504082c1050010502030744d881800e0380b074100016038044001302c94980403405555891710001d415842000c0d4242c200c884410389a0707a031000c0d0300c41c05850140440c0c2f1186001d0901e00d60f030f0350001804034042060342c4001c1c00303c7d800c2c2020030017200c42c0b00e8688600c2c010407601402000b0b03070b0286400c0c1c440002400040c4072030340c94195600040ca0400c0080c512070727511000d41400c80d1b0030341e03124003100740c1307040240c80c2c003521000b040c282d02010880e0301c240d4074265080c1c0141584207096000700311050111198403254419070103140581c81c10342c0000f8455840307101071400c991034960100d503c2107012408020300c0f03106030250000c2070405030555090000c42440001510f2098808a80e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 723618651 1250 723617401 723617417
    0x6180c06021b03010203130b060402160f031403040302250801090506010602010b0111100f0b1003020406200615030102040801020a1e0905090f0c0702100210050a1a060d0b10 76
    0xc0b40340800450854100110001c42c514240031810390b0a0b8903402c00010903000c0e14200040f4213942d0765060b41c0c0d502200010305400035401e07181402102420b0704080f00030603d4075070807a28085d85001601d02c510383c190010022401003004c0300c0501042c540c01c1596011100c04007041004081c05070b0721030751340714030010802941850300282c2540e024606142c10005032901d2030394002c20001e46001c004141c2c00d40050002d509000a0024044d00345440360030829040481014070382c1a40140221591541d412451314a4507a01c034a00c10035107917034072090f54003060105132414454244901244002000149015502c000b05426a007106802e8008548a12075403039141c41d038921f014034420018a85901042c2c1441d00103200b2140140c045201c82c00c101d00040e0300100550200c60700690000c020302000200c80350002e54400032082c990220f98103042c00701c1e401003681d000f220b820084c903518880308040b0000501c5201d41007407418440040e15000c25103050389510500b4072030ad80f0b80c3e55442107 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 723619901 1250 723618651 723618673
    0xc0a02061603080711071a251101051207081e01090b3d1416032003031603020d060b09121c11030c0601060e2b06180c0602 54
    0x1c00050700038481410300805d104241802c440104110060702d0b01c492511695200301c1903220818080d0008010a449900386003010048440c2d00400700035101e03c5440c07031a9400c40004446a0223414036460000303002402080040f4007528895034010901c400c1c40600d856441c0030f01c09012000e922400791b0b246d03078a241049605000c2001e881010ba0100390254107204062030031190040541d29660703841c0805900e440d190300c2040030480100003840140d40b180c0360100354480b0059501c508a021551491a5111840524240d03070500606507016500f90390b05c0b0601e12745002500e0201100b003660801108180912034401c4074040c2c4140410903484401e00010300250f030002d03012002072640482220401540a040c1d04600040685080c900b040c4c240704001d442d6000f828644002c82c080c180002ca481a44010680b11440048031005c12820f54411401c40c0c0b0249268489042c1890241f03001c007182e2180c1201005550444900c034030f460158440d05030310a136540003400141c1090f11800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 723621151 1250 723619901 723619907
    0x13050603010f0513030c0201051902071502011b120f05040501050702120c0c060a12021b0c0a05060306091017030304050c0a1206050703061e0f0e1b0c0a02061603 71
    0x1251401c40180b040105060180c6140d003801040000203003000741402c0c03401b003164070803410b840703540c4d08111000c240c103030520313074040d44840490240e0298000114032101529205000e80032224100e200c11403a4918150800c54138080658900c4070b0036910f500741e014080c00f5500c40c2c2ca01c6039014034000921070820520083c00c1944c1c400f04103854420510040e03544100100c0c000811407070496940d075817a61982d006603640e04840295140a91000c640f800c4910104d00000300010800015604058550b000300800c100c4640900c54001c20203000107030141c2800c001480d001035401c80704210b05070f07403010889480c0d803521031040e610350004014001001000c03c5601c03042c0700b0440b0285079150508821141811951350007900040d107800200e04a10300a40c02900034010b0380e0700d28588482455400d954401e0140701c2e005117090f80c04000503c082140e42d01c0e43c014081040c441d07203052018800041103401c408425941d6008049100c40183c4e180d800800d060040c07104c864003081c1c0141009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 723622401 1250 723621151 723621161
    0x201061502060114010806151806030106030914070609090515120a06050606040b0d090c0305010507200705030304030807241b030c2007031b0e01060c020a061b021305060301 76
    0x1300c0d040c40044018000705985e268110422814451040f54440644103001d14241d0100004c40343c02210010000c0f500b0390303250f0001441c030781c0507e6941c1c0c162244400c04c0ea99600c41840b80c0e00014000740000e20191200c1d81100340c0054188415000350442c400c0000c1950300d580001c2e0015510802401d0100071281c001c0a50000080ba81c4900302841c010000e24144a20750000c803155a0344c40481d02040744481c444006950005d000704441d00c0c2425020700904d0303500a524401e10100240072042440c0003599105841e4040c02450402d455940c81c04055084024221840e6019181003000142407000007100d10720f40e04004078070441400340ca205404140c1d200396082605000030002000d07080b801084210314246a80310780404c1800170b003400e25040ba000104226096041c00445000d60f07980002a20107080110600c0d0340c1e5003c003907585045913140207400c403002d900c4c2040114042d94400d0700041a050503140015487e41c000b070400c2580745502e0008550f6402488024142403282c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 723623651 1250 723622401 723622439
    0xe0105370c02030606040c030e0d0203030a0f1a2202120103020f0f030c0f06040f080d08010e0112171c1509021c020903010e16080c01081e0702010615020601 69
    0x700940c940c0e415004280c0780c4070000c02c0305003ea500d460301d034031502e813203688a19244500700051703c601c0c0b10440f100035180d0344207444091102e4289404850110140d10139400510101e0004007542c013011014098000e61400380c83d40805d0403c4807401c45070034140002c002e07184041000d44180d60640c0304011210001904043c040c091000c502d0b240e5482c00100c6403010641112440441a9450b0000b9280d1090b81c211804030700002000094041d030006205a80c1013550b26442d0308c903030721600702c2c547c3d200c1d091148030300d02407121001c1004203258400510b20a010365503520b24103440007a503a10600c1c40b80d003003904816512040e0702e000980c4400b200029113440e003419450082c0840c400800c04038280b40b000d9480350b0024101c0c81340d44d000d51184070514490001d442c581d07000f45030402e403803461a01c14500240155990f480640d071280e072200d0f100b116540f442002c5c0c2c200d20701c20314400c104000c120070150345d40c820000c1044200c03a010082604016402001c0742d605060b1404c0e0980442c0c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 723624901 1250 723623651 723623657
    0x3040806160c1509081605060609010b09010c060504020301090605090f01060b04050114130801060303080f070804080d4b020315090a0605040203040f031706060a0e010537 75
    0x1c0300001904070ba06083c00c4802c0b6a1020075030b8007050809640d0f80c420316940d090300620700441e09082100215815116a40803507034514a0f81c1e031140703070302074a01c40c1c51030003400a588000c18000051a030341c000c9400c5400980001481b02156649000f00c8006603000711442d408170103006038117402401194064207180382443d0400d0318000029015402a44250190342e4010132441d1210100a0301c00c1d0081c5414402400717001e5a80c10040c08602007941e40140d505041e90024400c0b60007585039030700542d840f420262400124104900090114140c04020308400103a901000d42c00304c24041c01640b149501544418240c0c1c41c890002000708240300039041c014001c01001d0380c4110f40902250f4020380350b000c643e60750502500d004003a15040f15a009101101384420f1108415214001a11076211080021b02204071141c96413011211154449010010038182c00c0c8501e054406007001810b02904220aa2021003034001e0720700084600007071342191988a0207522181d910220705541 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 723626151 1250 723624901 723624917
    0xc0301090e2d01140a1b0c0209010e04020607060501060f02150105280801020a03021201050108100b090a03170309060f091510030f03020f12040506071101110304080616 74
    0x41002c0301501c0031401c04410311444440c80e03028034034003904108200c2c070351801e940240d444c042c15a00000c00100040c00a00d924000541d188a4080c9200061151700141303800d08581c600011580c1c003032001481260484018410000012911b01566010b0640c0340c0300c0001d0320081e918024a080c50001600f0900404075004000c40c2c2c44025a60b100e106410300c4132465400c0040b590182120301d50700810079513200140700000c00d5856809040500c020100521060760784100440b55018180c4c1c00207600000c1c09000c1200c04c4d80304d0001c02115002600c00c1d80c43c2952900e5201c0814580350200e08421000410441d08100c14800703140d000034040121203090400c1008181c1d00c60b2010b078603880c464007000101da200c0c4008001d9000031540828980c1d203490b96460000d484880001074442c00e44540c0d45480300d4026480c0658040d40d5024058908200c2d0641700e60f03000405a807120b074180300d45124040c00034141030000300040c0901c04014806810548040001403011068440c00c0020703c2c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 723627401 1250 723626151 723626173
    0x40c170a060f1e050c0c070b0d0617030d0c020c060d0203090105010b0a05120a06030f050a1a06032505061b2514221a190e1e0c0301090e 60
    0x580307490043c0c0b103e402d43c0041d080c1e685000078071485c4a001c3d802050392040900024054410340010143d820f0003480c24002c1c01d5603542d40220001100161142c140c00621a401c480150f541c00450301c0962b910495402000b800c010407240e50000c203c0c11441f540010800c05220070900601c1d004005a4a41c5864407900d482c0042c01d034052107000441c480c82c014003003141c40e04240c03c10006980c000443c0382c22860f00b480c000ba60390410390400c60f48080c08007030044400c3d02c0522002d10510000d00a01040000156000b0040310301c42c400030005940c050700811151500806026600303028001410b10481e400e080e64582980c0c2400440c07040c04118000c01d059a1a50741c07002210b500890081da014521000144505103803088150510000c104030410200780749c002c60030070916203005800c1c0313200704418803e110f2465840001c0006440c1c0080100400010400e40d212a00500803200b031200b002c840d6030940419504001607020101c01807201c07100303074440c500004468a00030702d49a424 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 723628651 1250 723627401 723627431
    0xa020a09140a030305031003061b02060615030c1b070914010e06010c0f02030f062502150106050c12160c0506090a0302040b0f0a080d09080a0c090203040c170a060f 72
    0x250000408005010011640d0b12406200040123141d002c102407210010407045642d100ea00c104002d4018801e480110b001410500d429070200c3c4080400076266030703282d0740004844c1e8086d9070020101c039001c08150301d02035828450a40900310705600402c03a60800340d480c4540c00d0341a000303845082d40303c40c103115a5030f0300040c44101c52544405082c007800100e0000a0402001da516521240681420054030706d0b51075014061141c03100300841c803d106098822a41c9241310202035420707020380c50050001c1030065029084050801d0700f22086a00c4034281d0031820380000309000840b8000d07900d0340013041180b000d07174005000e058541030309090381000011440c55a41c0b10190040c1c0e0780e13000903803041c0c40b4440030035007002d4003a050700e42c0303182d030740b030101d0381d104110706202001803200300001c2003003070b000b00700f05500f141c0100c2460640c5050010351402540003400844010700b0602c0005503c200d264034190b100b40b820400f418907800b0f58104442a50f20480d10600361f540b0301040e0301c0c51043c1c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 723629901 1250 723628651 723628669
    0x72408071403131a0f010314010c02030906130510030e1c1d030c04021201050406091803031e090b0709051f030b0a05040e07230a0303050306180a020a0914 68
    0x32501d43d4140c4459800d003040b42c42c1c0c0401d02c0205850350f4400341042051404407050074100d902c22801c41c0894004e0803000341c01c0fa0b00f40382c950320060b001001514050b10342140504540003d81c2940e55000d82da68000800c0d0072031000304203000c251038519149032101c09003c403040142e1221520582840c26020041c400085442c810107d001d0104a4000725202003000040741700010380b00315600c54910710201243c04003480b40c648150b080c96408034121241c1e008058030303021010f5071800400915a02500580310300784444241e0740d05106040c40c8035a5038054000003a002c0d151284040c100a00014412100c940140e0301420501c0040f0180c5541d50034180078084c514038002032580204000515802800e51010b607100d401d1101c80c001c0c5c0040824880c04544110b100c2040a108010703091108140680d65076078000b900d4141040030038000c0c4011544050002d01288426800032800c0310b0702030040c1d801181080d8042901e240d12a00041003902038070702c030200d00b0b008030000c6000803c032003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 723631151 1250 723629901 723629911
    0x50c09010f120c0e030c0a1a03130503070f0219030c0b0d0f020d050f0a110a0c02040b041d071205060105153a0b031b03072408071403 59
    0x4006081010468455201144854681c0106004181c03d10000801c11054440300c0c034840c0c01903444604c52882c150300e4041c102c41219007242018081805244241e0b00000d025450740406c4011790700028100703000404400f4170421072211401b980d40140264030b482d070138982c4d0b40041120810700c04240e07201d1054040754a008881659084005481000f40010910070402d25002090302c4900700050f410240c0710300407800110741d203590303414003503429103520f050044000d8000b04120085107101c3c0003c501c140e40050710110b0750300001d80208040310707001400c0025a0884100d05200c42e5014048100240340340c076540d04031006980c0794252501818801c2c0c42c0704111140d00d03c0042103910040d40c0c184032180c07403800395410030841c2c0f214250014200101000308003189105002d50346100c1d41110080140041c450450128062820541403801480d89482079030000205403606000703040c40c140c01c2002503501c1c480120341c05002d80342c000c1d00407800d00c03480c0d46c940a030311032210055039400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 723632401 1250 723631151 723631157
    0x10e3c0f071d060c0c0a170105060a0303120c0504030b04050c01110c0612090f0303040c05090711030711060c010c05090915030a08031003080a021b060421020f100c030f0201050c0901 80
    0x10340c865007141e0b0716085d0400e01064000c1580740c1c2c001018030410285681680d120703c000e20040c1c1c1c070301c030802000604a01004001c0750f1826041c43c1c0b041159031083c0302076105410034501c1c1603100d45409884001c21201150340e64000b2120b981c03a03503445180c0c2d41144c02030200900d03249000000041e610f0158051107448801217400141d80c2d503108000c00c9241d0b0403044152580c9003018203107092100028050980154000303004038000512500392100702100702009141882d01980d65840121040c0340c060b03900c00010321102c4511a030a102e804d42c0d00340161180c541e21520041440b600340402440c218218200b800e00e00c8654801044101f02d05030720000055603595810300304580030109420187c41e0b00310101c2d80c2e0964070b400041901d03202d504d800800b126002c04c1010480144194022075a249840910a4000e035818040e0100c4041c802010b295241c0c0e60217010400400409606e400080c0120480b002415044140c4400d0a1458402072251789801c0c1c8900c0d13190301c1604001810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 723633651 1250 723632401 723632407
    0x60504020604030218090f0a0b0403030f0603080a030c02070909080f031e18150108070501050a0311070609020a1202060306010f0318030809010c08010e3c0f071d06 72
    0x1103503500022103010319401400030885d400b040070b0890104400702d0b8031255500c01c1c12030400607c18001400308189501241d24051660b407554110082d041020440500c03c1d00c5480200000380410040d082504440e0b50000b0610144040281303460103e134482c98140d46003045d0080840c0050307049420759900381418a58945450070b10304050103070b4050b40004044180c00307100d00a02000f1a500800d000c1c5000c43c0c1b070a500d1103a15464002d000c0c03045d882e0b19440080104502d5000704050504050941000034032101e401803003150551000d042101c3c21030340c0304440000c500d400c4514501601d15124140c3c42000103502080c1c1612002d02054180850460001030a038841d40201030ba4111484e0130200206071490003030503014041d02d10340025401d180315080002d2041401380d0403100c0741c60402c0140c0c3c6603220600991211017940d00e640c1e2007801e440d01d0301c442030030009140100c8030380f84400c170074680062510581800540014104000f01c243e44035102200a5480a01a0106c2e41c17155 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 723634901 1250 723633651 723633653
    0x20d0f050c070b060631061806030e0c0402042d0b0f1c020c07150e0904110303071707050d031127040e010b180c07080c1006031101020f03090d060504 66
    0x702c140501e0b925021440c68030071101b206c20304018501e04a1519021500e90300c0b45c1c49480c02d036440d03401c130340c000100c00d048181d00b004868402d800420104102d141941c0300d0702d80041c0418107980c080d4020216415040c51010903006441d03001c00c814044c032021110305203041900300c1465100e02610640722960100354400c0c02c1240f00c403100f100c3c42640104540e106208680c10340c030b44146101d00c40409a0b003401110030140075040b0144d03080343c020201441d55903907590f4100007014086040750184418449a00000c400702d8425810400710740ca12600d800f403074581985000d1320441c1c42070416007000c142111100d81030003500c1d00014242908101c9000203070542c5014140c0d044000d81c01800e101c07081c4003005040d0301110300d000c41034a440c1c50015440640c420310641c00d68181c014a1410044c240100d002070740989001d510110944245010090b60711066640d260402c3d41c02d5111341c0000d480941c0c0401115420b451401c01540c140309441001466552085030041e260540b00c0c07000030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 723636151 1250 723634901 723634909
    0x10206070f080601180e0906060405011215110a02070e0702012c1c031d060f220506010b120a05101503090611041e030b04020f030a0c0306020d0f050c070b06 69
    0x1c1008403900032845649941b0340b030b0343c40c8010041d0f82c8403134240542c0022403c1c0b400c150207541d040c0c4080e03240c1000c01000383d81e200050790b841c2d000510324030391391903910004414905000b0b0510941950040080508104d02c5c200b00d41805489075055a2600101c03902d81001e8144916518800c802c8613001101080605820b03c0301c002108040105c0d511254030760f803505644030005854440d407049111841c207a50466840b8801d580a5500201c0080011703c0c11000650392240c2400c551031340d031a55101592400c2c0b0f0141c0a8102401e5207030003141a900300d0b00541582c541c485001d20341401103040caa007010400200a000b071811417418142c20009580c041c0d0003801000340d018030200001d2080410581e0a90041d004011110403203051803800b50070703400d14101c02da0743c020304016580d4455508000800200000054150103109040c00101c0c103000c00740c3c0001c60186201590383c404511128048405003020850454030300702c1130042e8a01032200751000c6039230021281403140c80f118002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 723637401 1250 723636151 723636167
    0x2030906041712070504061107050d0f0317040b060103050906060f190b04092a02150402361305070e270106181a1e13020315010206070f080601 63
    0x7680f07010100740901c569000c401001103411550700c481703954410303141464940c90503104542d80115050403001c0400c610780e1440a1a61180c144126203403036280c6000b210407001c90f0265240b281400030800a5605400741030790200703583c030262186160090001b001c84280440d401d0050100e0a0828008014445c000001c0c242200041d51200e230740301c0d50306004d082c09010f081d0751100d02983d56641040807904150324291250082d0040446210070b200000c1c0009000740d07407100c5041074071070083e030340c40c1404d4001c80580b940116a011400c2d0442c022042c000d450103040002100b60200404c00110700c40c0c055800c00c103d5112251543d80b0711084041e840c5d0300884031100030001e40c1005140c150b0010303086407100c01c05c40d1202d111209000307044810f62a0200141d03400190a02080d1800c80d50200c696044115004101100c20b404140c840c1030100b80d2118044c0c1c0003051003005901c40800c0e50394840244014015850804002040824018025002c1c4a040004110241c0c014140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 723638651 1250 723637401 723637417
    0x10f06030209400e0c19090203071809090c05030318010503100306060e0a0c02071a070303060824010906050f0123120403170403050412050109080c060601090801020309060417 77
    0xe000303522651400990082244132003015041c0305800042200d400d1280c0d034070b4115110092111300c0c0c03624229490004e076100400314030801000c1000702e10320340c1d1100d1040000d880b04000000d0150705500d000185224160031052099000348802d0802c0041d298640700241000e1801e16140d483e45020600d20032115000202072900b0564040b030204d44103d01c00384034000c416018840410811001e076100c1c0514011043e0306070b06c4a00100380c15041000916100b842490002901c0341e032890200d040c4040c56404071a010541551030760344081140ca542d01418901c7c1c001c00c9120f2038240011410300881d5001ca040c40541c01062000200102070b1407181c151000010380c2c0c0d0b00d0f074044244070207081250100c000c509950750541d06190800b17a21440341d541611151301d1300e420304420034041d00c1507210481c1c10350348418030240028250f0703025088a244030001031420382040c000140032100c10341c00840140c1c2c81481002690760740094060340054000e00100e9501484054008051041c924 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 723639901 1250 723638651 723638749
    0x622090602070f05030c1501031a070c05101e020f072607030309020a080c0a030321020c01020a0905030a030e0904170a0e040c090b030114010216080105010f06030209 73
    0x241c0c0050110100040c03c09144086c155030541018441f000700c0306000b8000507102054181e0001512108000c43e960840418100342050916035620f4174030701b60690a07841502e940399030502a407400ca1241c42440400d0b6028258100407900001c558580034a02c0007070100514001000c071920050181040000030340b4a5507580d230b14417414080c01601d02400103c0c010086101c2c000751042e4040b54800901030b00800e202d03440da2030740e01d0840712121b541e2103100341d0300b4042116201004062004198002000e000942c6482c061103001e004034005d9800580203420010b86000025070000802a01c100111035054558855040001c80c2c3c04850b0b449a00c20b68000814071082a04a082c00102c01421201846026861202210070f16464481d00004940c2440188007005019011490242061044420b05250706108009070305455104002e16591400148450411141118040d00240c01d00350b240c03d1440012440080c0d40207042d0102480b15a5000170702d03a0750030642207240d24545c2c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 723641151 1250 723639901 723639923
    0x50702030f0105040c170a0f11030712050601060302090901031205091c02100f020a030e040e06131e080d05040309090f0f052203140c0706080f062209060207 69
    0x3070416000305002d55044e81d42e00c00411000602c000406c0c0408000c0840c0005010398034141c4e655152079800410040391600c05004241040d52420040d880040100007040401c48100741461410403030181c02000c01c040c010484102540c8402c0f801d0350440e07600c014180288005000700302d40034000d110680d0360212400084c0c418204030200307200c00c001c0c0200c60741340f20040701100030396190513103d100002581058002002003400359940c0000d044000d44007017458444070607280e050020844500c100b0885000d9503d051041e04030100401500048240624003842e845051050140b51641824203496100003001c044c400e143c1807000b4042340c00c040c00748000f4001c100014003500b016150703100e488c0c40c001444615207880300803110303442280c16910140310358400301d44041480c4000000315008002545901c08104a10b9004040641e01d1000d18144803c1d805202000646142d10032450b042401103141c80203005044803460901c800a04c0314202d141c6071000e0b0180071006800c1840d16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 723642401 1250 723641151 723641173
    0x16020f03030115033b070b0a0507150509060105040225050318010504050612090a0b0c1b03072003010e1507030c05070c06030902180a0903080903041d04020105070203 73
    0x1907146221104040d181400060720300303c030780d119820182488490b01702d02a404003000104000c040600c01581c80b00f80c8800030381b00d100b0303280694460845280003c5001851f4014011104070400c1c0007840d11a041c030041c246a4461591400e040c080d03244a2075001654000001c028540341030b40e02828071030912034800c542401c0d034890f00032445a080c4103880e5040b100c01503200e2000c5030150b40b0000c192508002c880c1407494402c110040ca54031262140d00c085501041d214403200d0305c00c40403050071943d5440714802259540b0608104602c569105200c03030000203206a01141c0100d00c0000c05514801d006c20010340500062000034100340180300c080c2000c020b94a5030340b841410140c800303210440743d49908594611803884c0260007407482c483c0a00c2201d12a0f0030501105000401205a40754094070808280c803017a1a0b15801503a00d1000da4100b581244240b80c3c0031852001860800d4980819040403040c402c4060504040c080d00080c11a03026009441c45a6005400c40380e550000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 723643651 1250 723642401 723642419
    0x30b011d0f1305010c0e15040e01090905011107060902130e0a020108060120010e1b10050702030111030f1b0f0901110f0106080f1b01090504181202070306110702030616020f030301 79
    0x106411f01810355015004034000c080e40840f400c4a60034185c3e403085a2800300c80c0c400418141000301c40954850541e0100146108043c0800b81c1c020100000d010245204002c0410810940c400d40d01d403d000140c012800e0100e80455030a0702800c020090365107000040303810040148640c0001070340b44600302ca2000055028140304560982225540400d514012a500084c910000d9006580b13860741001d0318411400780c42014405800807030701d0080d1858415007500304440d100090a8054200070500c001c48203c80c0682d10801241c52a1101c0040c3c002000e01c19416400c1c14000d0041004000c00c1c01007118400c0c0240c0a0b00800c55030f40c49001e8641c41d0f0004601248151003001d8080f10480c44010900907101c005031503540d40c942c03919003880003904803920b40d103108001080daa240410200c2d0b41d8031003550780c1035001c0c1002504518003075003204e2651100520f244c00c28000c590068800090f02a0852100310780c00d1400b00326420124500b540c0c9650b10340113408040000201c100c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 723644901 1250 723643651 723643667
    0x20c10050a090311011413080d1d010c09140d110306180708031306110a02030a110a121109190f0504140307170306030f0313030b011d0f1305010c 64
    0x40f00e59a601c0010640081442c00d90304a0002c00c20410b000394046024034000d0584408150710445015003811607a12500013241d503466180f00030b0f554801c0400c0c9903001d082c814059006450309000407101c1c10202103c064104601019004081515044040c071201076045488008010222900342c64103241144003202e00b0b07207000740301d40704600012074042004800c2d03c115124000e071405d4200e01c0c003201250200c0680034448480c1c0144100341c8003584080c803200c0d00c0e039802001a208048810024440f5140e09540400c02a190384200b480c001440d00100c3d82154200315941c10683e15504c1c203a0650f9440e03140144202843c01c4010710400610b9040548200c0c050811408040702408000b502d85c442d1500040200c803505000400001108000d55040100902100c210b48003031150140346030b114814081c5a034544803000c01c100700c5040046405004e00c40c0b00c4c0026040d4003006081c13604005402d0701020b00c287c00c00100d040e1008050b030f484503a080310090010220b4040c1c080c029503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 723646151 1250 723644901 723644903
    0x2030106092f070201050904240602061305070308031e0103050a05060f040302060f0c0412030201060503100903022112040b18061303110322090b04090b0406020c10050a09 75
    0x26090150740040c00d2514070154850303841103802c80749040c0c070030b50044455601c2500c0a0b540030f90380d191440d0703004100303c50705085810f4035801c040419080401c0680390143c020000c8a0040c000b02000c0c3c0001e00100380801220303030042c1603a0f125117034110350280800c2d00c60700300040a00c40713500000511600089140d0001d00a40c143c41d2907403100e42071081d038020100c40107805030307000401080c0782b80d0f404400b0503486840340c880c003821b0988030441c9144681d2490002d9005039160b500901040c6810305c11904400003003c400c004a40060341c0181d1940244158640d40c8180080e0321984000c9c030700129036608030340e0b161000701850207180050404e00705540032040401f03407502034441c0040010b0614000d0b80d0a240f401d414005640d800c442005405400030700b0f500081c0b1620740c00020107181030310300403081403c901081d81028050021900303048070303161043e410202e04c0c4012408800e60103400c5038109202607a24892040e119160615820548400a20f018100002d241c25030788406802c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 723647401 1250 723646151 723646181
    0x160b12151c2117010b03060a0b030402030a06150905090a12210207030302030103050114010311220f05090d0f0909050618070914030a0203060114031005010602240f0105010513030203010609 83
    0xc1c0d032030340d1780d001240c00101da209800c40c4045009105607810302014583c460f20081c200d0b2040c5880795614015074803410b04105140e00215814400200c0381c0c02130b03643c005202701c02482c080c00e80b6202d180e003401c09000a0001d110001c90307503540f01d0822880c00744c0040e003080d41c15035036420325150081c0294002d210540303965180c10001c0c01e4203401c0308030550403a900007030500303000c0000c0d01c1085030341890300181c4200c06031300c00d10620b0081d1103801850032600800310300080e18038014400d507003800c87c07482078241040068003d8820312074101c4a107074181c0e004060000340d0b40d81c42e200480c01d90054044030382100155001003200403030340403c1c5101651070348014040c10500035130070b06986400c0c01500941c5a0800c20040c0403404000741511070480000302250790520040308440d00710307002a0007840040c0c120f2900303610f81000b4000d644502218044004400b85000030340c1052201c03060190b41d041120004a908854103d01030032000f450300207000304071641e07460744110001d011200c001400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 723648651 1250 723647401 723647447
    0x50a060f0504020a090c090f0e09010c020f190305040806041412070803011802070b0106030c0e0a0602060403111e0a12110d0c05160b12151c21 63
    0x15000007402418011680584580c0305a8144455940602910751495040010200b40090302e00320700103241c07005240c100d4602850782019103c1d41e0030341c0c400510340c000350360080f00c0301120b20303000040104541c140740e4111048400c2c02d02c0c00700d43c90710895000030000d00c21003041c4000d100d08400700707000800341001101c0041c048100d00381120b025044000c1e0228005000403c901460b54400070b03840340c00034000514200b030031b603a8410914400e03044800020f0392104518400c50b0080180035240c00111000001c00340303484d000075075510300140010100b04000b0740d94181081d04021000c906111400e42e081c0f0010203e01140d030701d004544050751081c081c18202c9081174052882d400c0700da80c0394005030403484a13986082e01c041c6001c1500301e54030f11943d10740b80e95484003480c00e44c02400640035201e540c1d4183c100d81207000c00002d80810740444014a0301c40082e80d5581c9903e0400403c050054585081814024020103c11091550141c10b15894001981d401090048145851281c41d1311b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 723649901 1250 723648651 723648671
    0x10b130b1b070f05060d1107051609050f060d021e041b1707171803030c030f151e0a050d03021e0607020d03111e0c0706020a0503090d0c03050a050a06 66
    0xc0d40c80a813158582046080285c0951001a43c022191a15400038224500f40e941e81d01c240c6400c054000050310300310012070a010f0341c102070044ca508940451400714147c24054001031031a500c6047c0240b054901454584004441d100411a80ba000400801040f25446108000342d040b09909400258080c0946000ba403514581c50740507244554030202da46c2c40030710240700c011f8006869001c042880c0c800036100194200300640c80391307803c51003450300e9081030300302c114150502074640400c6807480401c2040030b403584041c28290740c01001003000040041808520001100c2e00810f4000c1001e04d030120a03d07800080722103d002e0020412141ca5091804280d240c0b80c0607543c420050304542040340440c1c2c03103504103000400020240728a042101d00c20140c8108050445e040050f034081105540d5100511030107004000c140040c0600c0100f0355181500d0348240305000f84142040c4a1a1041c401c0b000d1049014603808411138190f01e2441c00c28540d1044210f00850780141000d403116 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 723651151 1250 723649901 723649919
    0x60c0910211d10110d0903170702280f120e04090c0e101215020c010e060405011808030604020309070806191b1209150f060906051503010b130b1b07 65
    0x6848880d880e81c0341c601700120340081001514202c6016020040894502d03a4001300200f425130288138203400030075802c0084141103811b48421355121443d0b00603103d452000c140d5851680008962054101c841e103406000e080d985420303c0c8050700e1b00301d407030441c412040003807086212054a0303030302a84e40c15070394460071079090103100c500955260700b000340600780000c1d0754940030b01d000f40716100016085c01288500c21303007101c0c05030800700500da12000601081c040e0031710520788441c07940b00d035200305d55400f5110003119100250095016550000000b102c445017404640702400c4500b094171002d0400901061092010313800f80c00f642c9182a100e51000c1402142c09542e04006460f82200c10000340b40182c0184030006c001c0d144852801c0c0c280801c003629220b0b01040c00c0400304000740d514244030054040320003a0300039901800006100c3d190a2540000b41c0c3c2c1180e420088213995031400d641096007141c8503600c00f0118180110b080503a01884464401c000b46029003202c40072542c0c1d08002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 723652401 1250 723651151 723651161
    0x6031801060b21010f1a18130c08010803030c1b011401080703030914010801050d0204060510020a060e030f040510120c0306090b10050d0e0c03030301030303050108060c0910211d10 79
    0x41e4140c82c406c0c5061917601440d100c0900300d01e0f00811020351a84904c0c8011601340e0748903128a840d00350b03551014429060f040400d40d4003402d48c030b600440c00c0d49089282d440300c0c1d03c81c6030843c0640c03c000c40014512030320250400ca44a103582d000012065030745107400d030381c0c48840d07000840c0802d094030804a21005841846c4801d10016540c41616034038020a00180e51070700b810698000d030311160040742a4035a580a0050038803030303038010000c884103400c22000316100951140310507041007220131412a0800151019100110b0301d408403001100d00580d41100c0f03038904520345030709001c9400a41d6406a02290454070030f18814081d000480c820803076012114813a1034049042032282d150310111607131244200c47c50300d400303d4015801180000b850360304240d000710b0001362a44018012050148072640c1c01030228900182030000e8040001d0089030103921200400c101c410764544179100040b01c12090058401c81002100d42c42030f203203805426400500c0d82c06200d030004c0d52090414602c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 723653651 1250 723652401 723652409
    0x1020d020f03030609071e1d010305011211060c15040c090c020d08100b041403011b0903020607031b030314160503010302041814030403030f0e06031801060b21010f 72
    0x70350f00d5550b40b41d04100c1040005000c0d141044156100320b1844002c51042500100c101d131128544c0221a0003800203166088110320f0416007000010083d851040614001d203503030120340c0741d1010f01100d0214100740100b0424180710300c1780c120304442c0a4240d09046004034001d105001c081a101d050b400203443c42030341c0320f0780140d1144174035807001c1d880380c11404d0300304601c01240500381c0da40d00d4a40c00c45401503044400d01158640074031041c0d1400748901030084c20307542c8800721024080c5101134524030a51102a0041000207500307401c05204207200b10781c100a0080350703084c2c00c00b07a00740100281001d04404e205222904041084180207925030014100c0c1552594074580c08c580c00d102c041c02131f92200380a400041c6502c03400084e592080d401c500f402403c02962100c0c074600f001480f0290f5842d108040c403400030780242c220384460086980c40008071841b01d8030324810524042c010a06030303000c1e40341e0500228807008101c1d140d14880c084000384841400350b50b600d80c1c4810554001e6841 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 723654901 1250 723653651 723653653
    0x1c210323092112090a020d080c15040506040b0c0310181401030b0f0c0a0804020622061101110a0507120c1505041e020f240705030901020d020f 63
    0x518180c200c0d15000201d60004103241550300d18040442d030342e08400035075403000112500110394440c50b41061014240c0c001031020040180011716004078641c1d03000d1035070141c80c804002032203080021003000325642c41191096500e80b07604c3d0a0800c60f440e0503064604440000b15207012580251000b025640500780d068203440c1c2031481c262500d25502031103061080c00311f85503181603c41e00540342805009501807418800b031494442400c01d80100f008140031201a0107002d00680d00e54440005036120f5810380c0c04030f581e0030001003140c0c0f150700d002e040071607140d9050001240c4d00341d129621610200c0540001c0c41703085145100d507042e500545c603d400c000344d41400a0804182500981580212141440542e480721500c410185900440e02d901703050342c8901c180720030002151209403140314940382d480c18100450307001a1921045000443c8038040d140f4201005c041d00103040c0c5040001e40c03890503910719603481c1c816142e42080b181180503028507183c1a8110b4008945101c154101074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 723656151 1250 723654901 723654941
    0xf0c01080718081e0d08010305031e16050309011805030307030f211a0607020d060c020c0909010504062d150519050a05040b0603151c2103 61
    0x1120441d040b01d000390581400b101000000902c59105110040481d03e02070000c0404000d5904210700e424540103250040100240040010038004001d46114281da0000020603142650079840103004419030007840f520a8040c580400c4400001010744030002c0c0ca8401a80b4107a18010314003440300d21415030141c02c04c10410300024410214011407070200e0920481d079003440901381c906656100303483c00d4000c1d59400c0c241e60010303a540d81c030f041e500b200b2100107140c07034010342c00f24001000d4403a00804180e00d43d03d0141e400f330b0090206501056014040d010545081c17130400380030300000d4800351101403400000a540400c1c1540800d10400c81c0c0307264800400342c3ea400c1000410211080900501c0c40708004284c60751345003100044900803115090f80c0b1801e003000c00080007000d600c00ba1145260004403400f946902c0262640030341290466071150072543c0128092035036041c401c80036011035007402805c00c100d0b480b68925050402018040a401022090b02180d10011010035071200310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 723657401 1250 723656151 723656161
    0x10b010e0f030a0f0305070c0b0901050711150a030b0a1d070509041103010303050705070608280f1112090c0d0b130821090106030305031b07150e0f0c0108 68
    0x241c0924001c00703501030100e480500f020381302c0610b03a15200300101d00041c4002810802c3c0b00c0c1030592100a020041e105924215000340040c00030f103d00b600c001d0030501e9400d0769965560382d0800a400b0071154009141d40ca030840c110007802040f40c00240383c428029401c1c04100b8200d0344050b040e8200b01c1d4203000b11310391140300055520f6000001d15941c400e4903122440220300051010310700846c07003a05c40a440e6a030b20321f8240d007040c0440d01700c0d42c10420400e042104200c64401004842142d100e4254540311050f009280a0040304443d05003250524503452013006a0ba002054205110140c84116459540a09450b01c005da41d41580c80501c072400c01d00481c41010025400c60342c181008003c24400366a21f039129002001d42480300d8040103906900f0303c0204511543c005599002000f0640c00c40c1d401401030701020780700050b1182580541c7c03607403900c064100e030381140e0032020403d15550310020030f001800702411200c01c02d0080605a042000c00056041c44c440d2051311004215900c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 723658651 1250 723657401 723657409
    0x60306112a03040b040905040b0604090819090504020406230f070b0a020d1d070605031303110a0f060203010303030b0f0a0b0a12021605190c090209010c1a0711010b010e 74
    0x101e003030005140003c11001500c040c40400403c020640c0b618040748904d4242480c0b8100c05004054a00a134140011b0100103200002190b5202c00506030b50008041d0254046034021042c0c0c1006820900c001408294607403c6404000601c2d08000c50800c4d40c940300c05600381c00c0c06914900160800144600c00028441060107580401c084500509102c52090303d2010b0346c09100010f0803c0700c2400d890903100343c00b8802040540b5040c01c01c54650700300f4402419400c00b4294001e4200320174803c440725005001c3c80101d28032600420210086005810300c000203610070710007140468a80148142d0b141040c006503804640c3c0100030419807441c0c805021007590100c0b02c0041003001021610b211404584003411845444010303200350704001d031030103070325004094400700f82c0241e40e14654800034221b004500f09a07000c1c9030001d600c070300030103005a91031882000010f040900c01e401c01c40c90070401818507441404a83c4d980e903015847d049105080b40c440a1129001030f992014924050030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 723659901 1250 723658651 723658717
    0x30f03130b120613020720030c0a050319050c09010609140d12030e071802120c0705030d09021801081b0a060203070f020d02040905060405011112011502010f0c0306030611 75
    0x6084001d4540301460347d501c1c566211503415034168009056020000b4101000310a10400e4107aa50001d52402e00c070000784c2c0c41d040905030840f03504080e0f1100301000001d00401401b498003a000d98a1541c59040290003500b4a000d41da20b00011088202c00034034103d40590390003134005e80700b407400a000c65400c40141080c0b01c006c103c3c0f840707101400113004c89042e61741c071203506051714010307101d55180380850252100a86103032016101441103802240000c81190318884079240000780d444c2261012070078001c016500d0071a004180b0000207000c40b004070342402003c81100500c0110002003081011820250180340c0c0180e109000ba400041c4003210123107481070006118606510855000074117540c11198200ca1640284040c4400c1020902a04500b82d161501c507038103102046407045040381d814403610b007080b516140901c0381d5134000c0d4064400322101820074400c480ba40080500a0481480101d500d1403800c149c04100411400a640c40002c20f6101d200c4400107091410300906 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 723661151 1250 723659901 723659929
    0x10060f05071b0b120921130b0d0905010b1005040605130305030d06031505130f06090b010e0603070b04180e10140a0f1a09090705030f03130b1206 64
    0x1118220900100c5031442c0741c48020030b48000391a07541c00c00ca8504000c0502d002d4200252544a04107036a5a80d608043c0e840440300c0003005c01d6110a003030f076034060700d20038180d026071006000000c1e0341c80030000e9a086080f0003400362009000044901e002d021101130b0440411001031390038001884201e201c0d40081c6250b820140145500c603032a07840700d50a5910040811703560300d5443c0401c20030072008040c0142800000d030401c01c82d03481c011000c1c5507120182c0000034044c200c00d803c0e5030200706150780048030031508140c019101d0f40c0c450407809070241d025a0060b200380f1881400040313041a50302101c050711941036242d01c407201d8840008000d0511081918800d0188080d800c5958040313200ba1092005c0e1800513882d80c0c20189034120440d032040500c0071a55040ca41c40d90f4540b140c1403540e0300f000720700b138070302050568410781420704165640e0406a07040c02070781c0214a1400c0000081e0921b03504031641c0c8054a55141a01a020b201d511980c00c10302801c0d80006000b460b0080040c0009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 723662401 1250 723661151 723661163
    0x307050c040c0c0c0b04030308060a0602030a180b030f0402040b0f1e01140f04090b011d01080703020408031b01050c0903150a090c090c0306050405150f0d0210080a0510060f0507 78
    0xc283c181c3d226460540380b90070518240a02103000c0061551140000b40c0003901551106025800c00b00002d40303c2c800c41d040c090500801400441c5c220031000008002003080108054403400c103103807905881c041c00e440c241d00ca14145071518040e0300d0704025000c142000200340520280443c5c07007000810f90040205414065032042c45458000000003d01c4240304000031266510f08041003c1c2c100d824107046c0030704010100c0d40c40c0e03c0c0411201c0480601c5002402c2610355035441d940220003038400d42d005017009020100b5042040f0349103454112007100241c0091141b5a144410a04680030340032100f50b060340712401b1440601001402c180c1c00c454400d6020a480009803a45000300e440b81d840801c4859441c149010002d07494810a005031074200c03024081d0341001c044100c01e80e0700344100c2030320482c5003003010190360381c8428284010b20390207040070505140d40600070b40350032000c4070702444c2c06041c503000407002c0d51039990380c2c1c041c2c40c0c40303840e028141090381b4011202c603040b5400440d45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 723663651 1250 723662401 723662417
    0xb12010b0a03290403080a060e0c07081b0f07061b020a1205010f06060f1e02030f09040b09130c09020309030f16020330031510050d0c080f090307050c040c 68
    0x4403501c103801480c484e60183e02c60100b142401c040840440d44c59501c481e1510405074148056103640c1000c8907880f5401188154440309031a1205241003e070b444940040d11a005004c038100c0303c00f040f0fa0040300c1c400d0b111513409101c521001d000540c1da100c1c00950084800100f44072440d82c1c010006810b9001d03d00001d0048a01e801400c2241c203240c020001043c81c00c0002ca07581c03903108014688240301c0c1407032008000b043d0800a9078900801d4100ca125010205808c04030b501c1e1075100c000c68031070041ca4080c050408841ca452500b2000308190789020500c0c2c2d000c01d80002d64000c036401000f07507100540c501100084281030307541058541c1400d601101c0c545001507038080100c2c0746000c0340540304040c0701441e0300030322074810314600c0c100b20070b42403e000300181003140b006003141241c8280e500b1200400310314400c541501c81c84d82d420802c54a8442903500c510b502000300d03842910001603800441d140e80c40d11302d80ea40208a0010035030b52001d4035404c3e11742841d4002d41c118000354185520 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 723664901 1250 723663651 723663713
    0x807031202040f050907020312042004060b25030f0e0409080c100e0c01090e0903130b130608010b0a03090c170a021c0201090909110a0305010b12010b0a03 68
    0xc103030b9009900550340050054018400e80c5890006280c0040305800107501d000440102c440300d10000030000750603203010100c25a0000180503490592140013002013110540f120b00c60603045e00902d90700c0708110040502007060762403407101c00310095015180c048810b90740c1807044606004890311103400a0301d607684100054113000180251450700d501400000001c1d6003020108c0f0300d0240d014102c0e6022030350440725039030071008544c250b481900780400a9554114071500d98404e20780c1c05400480148800504484060050a8040c04560b100f1032001e0750384030304880e070070001e02440d201084200100c4413818001d90000101c50b1041101a10443e41d807100c2c040c03c1810281d080071150801c0025104606c4c00e2001c0381040080401c04807080d84e442d8000801c100681d00070034601e83d40d507010540c00d2100001d294184964020300500907282c4916205028003207441c140c5014001c0303449400c83c04001030013842c0200c10301401d01c082040c55512070085084600403d40c405212070281c8607 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 723666151 1250 723664901 723664937
    0x140303180a03060905060702160b120405010b0916021507050a0c021908150a050c03041202010906151707060e0d0305130b0c070609060c0803041e0b100f0f03080703 72
    0x41000380c0250051b049601e000c60002c0d0600180184520041c03007030a00034085428404150b50310164903065481040c1e8561609030b0040c00100d1402c4d03840514642084102846d22418100c20b00c01c0787d094500840f80704440511045050710200040350040c8207a5018030721480c0d00203c910300040c80d891402c42000164400c102c81c5400200003600001c038901002c500802c4020340001d140f8404010768a49900c0380101400007400081c2038946104c04c0d0036985100f5000311284a0300039074204440000e40a00d400480228890f0414042c00000d170180d07504000304078441112425281e16071001c10350030410030015521042107080c410140190180000d548481901604110b81c1503a0395402420000d498400154032480070842e00800c01d02c8800c2e40000702d41c080652040360f09460b500e6900e000c0c81201021100132510f014803100c48800e121685178802d01942841040601858464510144400c81c9020b00720b01810030340320400000d00d0b8800107000544c000e18104807003030302030891381d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 723667401 1250 723666151 723666161
    0x607080915011410111b0a08030d050a1d1b15030a0b1203070809400b030706020c09091603050705040b181303021c0c0606140303180a0306 61
    0x10798501c125290f0140310f040007040b1a030000c6180c00c1c2034400d48250701e585a642d00141c0c0b081080c226420b80080142e171284000440945401410350740c40b005c201c8041c074010401203441004480c01c0000607642454030011408850852074060006401c3d10040742015100c4040d00680200e809242c2c4440c0c0396001010354020820b038880442c031000c0c00000c0040602992884001942080051400090f001400c843c034504064170040700b00d00d41c07841c540701000c1060016098600c9108070240c250001d00009001380c00f44081d00f00700300301c48441815506c0c84207020f0035015031f0019000204615290740340c903034044102011683c2d200390000020308001c61a0388100c0d02a40020424070140c07805000d691400d0380c054400f0102c1112140008116280113490703ca1f0850347c0c00011002e040c420300c1500762001d03071703040c484003103440290740141b55510b050030658640307207020804180c0300d45031004a640100700400442c2040d0200040a1042e2960014698441000840000094402d00031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 723668651 1250 723667401 723667409
    0x406090201110d0305090f010204181517011401090606050d0b06160f0b0901050601120e0703060203010b13080c09061903052a01080108100b0103020904060e160305060102060708091501 81
    0x40443d486c14080e00c0e851900e4602403114007a640103110a0110f40d00c82c403581c03400660f4114010410003945d46950360286a0364001403820030034080000d032000b0054000c404c4000070a40303882610780e86c50b800c5c40101d4200d402000f000030400c0000c500300752440d41100d180310000034085441c0548406c80650b036070b01d2041048030f0001110080c1c2e0280520b0010303199000504000a22a616120700020900c2042850007001a81c6e01c00d0141009401000741034055030303210608641d02c0d40c50310711481250304003c985071001142c441c3e011485c107901080c9072490306009004e00516440700c104001d50792285107100c840c0200700f5500000401c03420012030000d91404c0070407500d0300190000f9034036404501d030a10b82c10f0061440041040300400141ca12440c1400302c400280141d1240048010b445505480d5178000d090000200b00c4c2d040000c1910f0041400010501440c1c00455090b801e03641c040742c0ea140541c00070310002d070043e4000d030441c5610844500076a4540d6898044040c1004020b0b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 723669901 1250 723668651 723668657
    0x306102d021b03070e0711010c2102070b01050616150b040e010b0109063608210708070f060f1505060405150d321503060406090201110d 60
    0x52014400d40512210b510180365107000900104031a000c6503694006105488000f41d4180c00120034901c03500740c8804140d1524001d1150350710112009041d01000c0c80360f0a550205a4041c1d0384400c4544205c802d00b9078460324200150781b0309000c1050075001145012100c284c0c0d00040e00020710a1001141803441c15400020030100040134401200c1c030031040c03141582e2403c6d00c02d030b8942e80c000784100119612880c15031a43d005100c00b4450300f24a01502e040303452580e141c0c0118480c1c1e014640000c2d40d90100440d40d2200003503202d420074940c0000315201c2c00c2c4041007030101185030359000b441c04030b0241c502680d0074243c6684260407a80b00c6481500400d030b0b204644655150540100d20041c40116101c0f400c1c1414240041e0a0150071180307440c00420000c0d086a41019039044154611142c207201013079081d0300c1c051a203810b10300414040c24044040c0018141f1403500d0b4154141010180003414142d66603503500006110030b0105a050015484003204015001c226601c0250803035030b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 723671151 1250 723669901 723669977
    0x403051906060911030610120e0715181203140304080d0f0e030d15030803070207080c0d08040513110310061706010e0108130f081b010b06030610 64
    0x4100002103032215001807003070f02d00748080c02c0583c001d2031081d280c0049088622042d0408224419902c401850500c0f1030320380d0802d0798030401c4807c0032038803d0440e00c11009050f86000745034022502640c4881400707500b8440100305204014051b0f125181c9103100742801840307129803510190154100321002c0301d04007400120f072220b11700d681c0280c01001001d810709224008105c00348031341303a01a401100e031010b03a44054006a0400c0fa0322644011500300b2052956802c02c0360000f07444405502420741d09102d41901d200c07040c00c040c1d003a01d011a4200200c0d074201800c1c40100070701d8181700140408059129501202d0f03040c01000110302840c0101c640303800d035615204014180030b20030301329881c1400208040001c00d0341c00412120390300d0300902c0c01184956031031f89000c0000301d81000103011046e090303c10b14200b003a180000c0c1644c160425051420158002c200c6003641c243d00841c0d03030882c800744040740a5003400d0301c001c0806051030400c0c250596012060b00d5010200d0b0382d075480c48100329 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 723672401 1250 723671151 723671153
    0x3080901060902040f080d090311330a091a0306011d120304061b081204080c100902010e030a1511160605010509070c05030702010f11030a0e030c010309110907030204030519 76
    0x20024229070a003a4201102024650f03259a0001c84622007103d004bc0c4100702031140480070100c2144d04415143c0100702d44401c07510401403541c00001c5040081a224a40030400c4040c544058242e0f001c00e10702e191965603003400441e1000703070400c0d6812031504102c1d01e281c0e55589056007214225110402591542c0c58118000c00c00207410340c994002c642005110404282071740219204200c4000401c6056111450b00c84460b1040c24500c892500a0301d140444400c000d070000e00806000f6a01c00000c500103408154555001c40d41c003c00c903d0290b51000400e41042e0803038515140708000c99410818070369040c446c1c000034110115980c85e0785400500251030309c2551641c01400910707010407400d0040e59880e99901c90b202001e0306110592100303103c600d120703008007546130750142c0c152a00d42c0c1e00c025000c0c01d81c1d5420030845200b40203010510003194401d00c40c80070951340281044120210364410b000348160090802803c0640130003011001c03950070007441c6100e00d40868100d084400b1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 723673651 1250 723672401 723672403
    0x4240e15061009080714030f121215090403230706020c0d03050c04060806060d1d01060503030319110f04030b07080105030102190323011403160303090303080901060902040f08 77
    0x400b42100060010b0b080c41442580740c00500c0d8810b4a0300c040f02e6503c000c914030300180c5081c03e64140c10360b861003500c5800402404c180013400040c075120075903400715121001450f11010000951030f4000601c6030020f40030901c42c02c0b030142d44104034804800140e00c04000b5040300d9102c0340003074801070b400143e2440015403c0010404200c103502d420841c60514600d403048522403482a8030810070391074089a51036075240200c6021000a120030003000350303840381200072211040007031199546090000a003500700482100d10414640c440c3c401d4003c80070001e60014010308910314541981888119560148030300108061401180e02207110300d84200c0003080b050301608001d00070b900502c00034610500224150407914070500300860b0901c00100d901800d41e0000641d60340d1035103072200016600c07010144a210704001075081d03401002d6194640541000184802800944402c1041000c03921800d4815086441e40c030000c688a40d542c0b440c2002d0740c106802607000c1e0b0740c07644801c20030008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 723674901 1250 723673651 723673669
    0x12010801140712060504020a030b100f0905040218130509240f060d1a150f1f0507050a0506010f0501022b0908010513170304240e1506 59
    0x120028010554101e092200c484030150215007400700402d8043d041100a40041e030242002810440d20340800e1000100541a1a500b9a00440000508032031252180040c603425130056152090698905030a0000940c03000c8100000a100e00eaa04400f80d40d42c2e915043d452550b6400c00300325418a4612070b401c00c0e24500c2002041200021291255000e030460183c2c401e0049c4200c0349541d0351000420302603441c0000003483c0c0000100a00c2213100c140000354083d032034081d003410301c001040c1306115054420100c0c1d80e134099611484513035240442c201d45a548a85481d103582040c4141d92035130b140c20418201120b02e5005030005104010001e11002d0003007030240300a05043d10100032207854840a1800107900040328006501a580200711600042111100800c050b1404004955540e078140000312002c2d4600050030400099550969008a030440c4040c0c00804c10380704409035100c58034011024180d256002144039180c03d0044040035490070b05410341c10302e442c00411103184 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 723676151 1250 723674901 723674909
    0x909010b0403120f0905060c06090f07050109090207081b150a0504020603151507050705040b0103020c03190c0c03050606191211031203070203046201021201 69
    0x11030501c820000728040c0700050b0034095141c2840303010304240040c1101c0c4081141c20850300110000f807075002408000a180d8420340c2000c083d03408003a08031081e035031115628811640000e90a503c180032111080d0300604d075051284105030301e00b01c01c0c000c00d07800e0050a10741180c2d4075040003100d44c040800c14688241c0c400c0d041c1c01e00b0041c51625900285e101e00002d071010541103034a8003039030b034146c4420311090016002240450b0321240c8919005544502d14043c00d4080d50810414010650080c0250360480308108042c50900200180f4560b01c0c032041500b80c2c040202d4110046c000c60401010080a50b00940c0a00b890303281407014820720400c10182c101d601080584100101100f000c403890b48641c0c40803260280c2000e00300001d21b0040c0400e00e00211081c00402e10050b20703000070090040380e000d00c0721042d80e95180d90035504031110f1081001c034960020716260700c0b6a5480c0b01410b010380d6200b11b00380511801c0c000c0d0001480407009401819030750000d048a540ca8591403814010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 723677401 1250 723676151 723676169
    0xe0a05032203020d0b061210022a030301031e080f030405061b0d0906020c0f0a140604050c060a1707021e01060503070b03090f0a0f0b0a0b090612030c060c090901 71
    0x105280d80c3c00b2514000c19150003401e40c0c0c61a00c0803c00e0740d6a49100007500c0902c110031620362000c000340d00d00080d404070311a820b4100c0c82c504112810300540d001c01e40c00c8407441c6c014605607861511404240d030f02d0000700100e103005001c0e032400061122806442105011301009880386024540640b8140c4042d0a242820300c0e05105441e000c00e01c403040701c4160070240004150b81501c6d1a101000c0c0c014050900c4950281c0707480706504d0100000ea00302c1c4a80035409288121050215040d00c5010503500600380b0b8011480101041c00c0210082c40c4050302450100f1000e10801420012440d065030132000580000e0984a0807032101e0303004103806980d102c02000300385d14180c00290f64032401c0c41881d1145901000144115209214000e0003074000f10036513210b0030481c5401c45a11404000480d12408500040703400e90041744140c82c0070748006031400c0d00f6526000d081140d1411040c072000a284400c11049200c80000e00c0841e000e1103034000358680f21200c0340d04001c60648141c20240c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 723678651 1250 723677401 723677467
    0x4050a08030106021c0c0f03051c1d060f04030e01030b30010b012c19030303050a0f0513020108060a1d04120c0312052221030b0a050909010e0a0503 65
    0x104400c2021005071561504000d030f82c0d0f0500b603c2c0c8065442c8a4ac03040c23400e0501d00f20038440701d041d114010208441040042d500d080d5200040380a11800c151409000035041c444101a203500a5114580d1460300400c00d40308201d5a401003812101040381c2540b9000c0e91200300762908000b4001d0703581c62117090170a040000f145401451f285030107030402003404115800c11016035211071104091b540e100601d01c0344525104d0902501402c0c0985165118a28010200b069015103200c0e8034000c181c407246e0003040c07501c01e800448400324050700e0340781e000b425410001042982c001034541812281a00f1210901d00790400304002810071400340148812101d50200107640042151700300d1902c007a0000340c6856098140d42c90704806410300104422102c1c880c001d11a40c0082c100d003420070340355507420f10b01c82d40318100c040c3d420401040e41c000411840902091411047c00d5622000b01800080c1100b0301d0f8041034604800000151030640002882101a664002d440048141042943d00c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 723679901 1250 723678651 723678653
    0x150705070305180d1202100b060403021e060301060e010e06120c07051903171014010e0409060c0e030601080d0c03030b0f04050109020c0c0109140904050a08030106021c0c 75
    0x1445003a10040c01c0007800200e014082640b880c00540d50350b0b01030441c0035100b00c0303440c20103000301d107002000700507100740c42100c0c14140341402006003040c0040c0141e07050030701d190b00340000c03200040e00e21030740c00340a000344140584400c40594001c01c0e499841c0030203180050005032111400d21183e9003e0718040100c2e440e805140048242c02c14030450210707540d001c007402c10340d040018110b0044181221a20002c2c00c2c1940008003000180010800104030b884280b00880404c440e44035941d0000e95840b01c001c260360003211340d6007e5590103000414840082e030355100c110703006500d882c0c010403d00440910682402c101460140c491100208034011909001070100f192907107000b010151140710046176600c070341d941c414103000f002d4030911155840d6640030020f5013207002412414450602c0300307881c0f0b41c4928041001c560300d143d8601c40e620700f48400e224611340e0042c405c0d6114411603000c50001410740d00118024416075010705402c00705888003c460098046680d801c0240c1500d103a0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 723681151 1250 723679901 723679907
    0x210905040b06190207030f1b050d050c0f120709020307030b0d11060f0706050f07020d05070c09052d070e0109051c03020f0706031515050409090305091c02031507 71
    0xb91003407141c030f111440d40b002c6080049140c0310380c540004000300c85000720001008821007004a049282c0c01c91001015215403d0001c102d0171154041c0c00c0c3c0d800404640b141d800c00d0340c00c110b10500c0180000c4e01c42014046170302c0c501601d60780008526507001040007013040e0f15225401355048210345250b81c0d00034a8440708592000480f0130781c0b068400085442048203160200e518941c2d002806208500d0000c5002284035801c0312000d0142c000c4007440781e81e00307100e20100c50000e94000d80100c1c0d03085c100b03200d03000100001002810f0b52441d00e41c81500010181301084961103820a00310090300e000781009060409050207281840748424052142d680c4640840d0122039100700c005030515480c0c2000c070328102514200381003c4c00389102c0411151380c0340c4c015181144030320101c075035050750350040304603000809090940050000e000600207040c407034010415030750084c40c0c1641020300500014440c8002403900011100031815440c003142001d002070f500403a44600c2024042c90020000703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 723682401 1250 723681151 723681157
    0x306060405010b070b06060d0603120f0234030b100609050411030106030504050c191a09010c0807080f030f1e04020f0d050a0c0603140c0405010e060313210905040b06 73
    0xc00710005c400010390f60742c40e00c005075a11035240700420300400e5501c0c01c0141c3c2800552154800080114031038064460000610185454440406000134030000d08001c0052440c81206807a4600c00d00c000404241d144091034010311800302d19074050351500502820342d54080c0d120b54002c50400800354a00c56203101901e045440c182808219039071a072524600700424030000302d500c48061101d45103003180c01c2c501c4c1820f45141c0514001d8041c41c0b403040c07a200b0702481c0c880e40d00243e009200b210008400300041c100342e521400c4000d04003502c0359082803064000b19015650004924108402d07040e0801030511020160318001e51a400d042d0040390b0380c0c2c0e0343c04110600030070300d03000c1000400504012101d41942c000d02d0381e40c442c5484507c01400b503c481e00201190008080214212024070b0045904071501615450a103400304014010303507403c018100c400721607641d03a03900040360406141501100f03900783c0c11080c2548660002e00420300c1a004107001e5450108003813101e440b01011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 723683651 1250 723682401 723682403
    0x912010b0d0f21020606121c111c030c090b07171c0f020a0908300d0f0609051323010204270b060f0a0e0102030d09030e0306060405010b07 61
    0x1045492512420b00191016200300300f034081c10242000d80f48004d50100794a030103100f0450341c4640040b0310701200d9a0301c50500001d0550b9a240c3d40210501d0b80c043c2c441c81c040380582400303860781c0c034444441c1c1510200714414a400840c1c2c8071160b440711f040d4828204005010400b1034075003088060b468048804503103248030744c0d0842d40000c03001140744023a030200c100945a40001c1c0860411304c030f40040607401459400020600012010030a80c03c0894038100c3c0d8204c0c1c819144440c0f008040c03031100c80c0c070201b96400b104407041108d00c4000d040f5004540c00c03c0380300e02001c11001e07c0c140b041d2086540043c80d000c1c10308259114100002c1a0341c289241c20840c0c41c0502400740c1d507900c00d550080c0718690120f284c03500700d04286520300f000481c03500214031700e4072000c1045030703418000e00c4403074400d4410141d030070002088100c2c4100e0041040702d54414040c412641001030041104045840034201030300820903407072940c52141741c01c0186560148090318180515450241c201c1c00314020118 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 723684901 1250 723683651 723683663
    0x5011a0409050624040e10060909120804080409110a020601060f21060509040b0a050603010204030b060d0f1e0506060301020f07021e0904060603120c020a0501030905030403050f030912010b0d 84
    0x4900c10b294126044611044000174003c00040d4407020000340d860540c2489480300d02c2c100040042e110619204000e015070b002030310782c00810700b03102c1c00310707060903004004843e422010710010032004114803e05018202054859a4510700c06402030301c2d000c0168024000c10010074003145916510201c0d15076030903c0c00c0d08284d004d40302c1341c0d0301e100504801e4000c1c94104454a04010038018184c84c00c6002e0780d4503440402c2a51241414907081c2e109a0002402510b440e1000ca80c1c4c906020a00d1408680641001c9800c031075103684d60f01030101c101090f40b8140e01003105080912009011090f0010001c4008500e4a01e00b01c40d803015500940001038452030045400f030160094002800904030b500400880c1a40340c5890008003d04490200b80d442100010500440b00d000d0581a0042d540081031540c815160000440180c2001c0400b01d070f15001c1440000009001000321141010b10303180a0740e00c9883c11002d1100d400700c400004000e40e81000d66400300c944410b640b102c842034001d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 723686151 1250 723684901 723684931
    0x403141b060a0c0501051005121b0d020f10020f010c110a02010f090b0403030c1109060112050903040b0d0203090d05030f071803020d0312050109020f250f05011a04090506 75
    0x40c82c2500c002c49441806409542400d04102c10f00d03900324102c0c01500c00449408c80141100c440441d0b1ba24401d4803007001e451421404881a450a075080c80c0e9601e00c01040740550311102c80c08509070310425508400503074001c0c2c104d060302850a01403121500e06a10b400c02618038402e104036999000080003a0510005815000000d485031060786c001e06840d10080e1398480da24980100303e0540d07424242c07418621503840c4161807500050450003800143e4a00781110140417010703000700f201924201c0303144410080061200d40c03210207086c07d00c010041c016181e02d0310b4540c0794106000d07455050b00b049000c00410901c1c04016107159040f00c4240f400034150a04880c01401d00350258001a41c8000c00181c41010150f01c01d1580c0d61130b07a0842e8003840941d90300c007150003d03170144078100301e140c000a01400414591508501c003510303402e1034000b01000c0241c3c07900340d903010b881d82040c0d8442e5100d002d0300001800140512840e040d0135502000610707010744407a0344429002e0074004001081d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 723687401 1250 723686151 723686167
    0xa090807080307030b21070b0c0d11010b0a090f0e0a03050d02091915180b0702010e04060f0b18091e090f03040f0e1501050f0a05070c0603020403141b06 67
    0x1da210455000e8041d00d1030030038101b600c00c0703064019908802a00180303c5e4200200da01c085207000d407003d41c1c04d40b4000b4140d01d03040c2d4005407642201c1d9110003503070399611a42851555541c2c1e130b02d038004009400300007034202d640200c0c002c1a05e0900031818502c0e401140f52a0000c4c0c0e11034215240e0841c405001a258104100050b4283e0321513402c0616a080000303000c51101c41060310000c10301c031070f0380b2458003401c100b544848610415200310344065800b40070000241d4011310f041000080010302c0003070620703211520f6000d02151034000f4000c40030003080f20940c645c0c50340e80034240b804042319070740000d01d0550001c444030141c01c1d0000c0255415800402d09035070b0300b0480e10103014040401d803a01c075901c0d498204c94152580c81524000215600811090402d0078640c41440c401a55030724900f40b802c06d00500903a1084000004004c010413125020441303103501000545825a40584c1d00e03865410307d80260f6114a82c9084103404c08100702c6484004051195602201581c2c0540c59000e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 723688651 1250 723687401 723687407
    0x304060c0f05070611010507020601051f030b030609010c1116090f0b0d05030a181503050903130f060905040213060e0303091f090f06090501030f020d1b03050a090807080307 76
    0x1a140e030081051140903c0803d02e1504554031450125402000b042103540d0302204990b2403400f0310a0a400c0110420a0894131081c0745407899038804c0c6040118121442e01c0110307103800300446124041d40d640d0300b28500030b9540031201d032070046034013002000f0302d01000b503051090321017034800c0c0f4424564a80076450892920f803c10510804000c2488001140038141503440741c1c031040706403000810b00449400a0488040c814054424520b076212000b02007202c1540180000340c0000481d01c414030075040d08011b034001c200c0c05003c0000b900b149032454050050242c080c1908241d2050b801440b9404180f02d12019440840d801c0b0f103081050200c4400102c0c0c02c3d84078815149400c1004800440e5000c654070001100c80300b440d540fa50401035807103a2039540c010050040200150888174100000d40c0301e604800500000a2401490940c40b403181c10304a800c1e4502d4900d03001101125141129094860b00d580680007401c00c0c40302da07441c0d50300c02002d44144c01000700b00b0140030003c03401041c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 723689901 1250 723688651 723688673
    0xc120d0806041823120a0c081b0f0d0818250b0705030301051002010903021e07090501031a090c101b06020a09030b0a151403120f0d1107050304060c 65
    0x2d0821440700101070003030f0081c0004d0a08542c110901d109030079550140e82e50000c01c0b034501d00d03090b56580e001080305139281801d07075201e8402080b049142c40a00040144280041013105210030000d0035500701100c805802680300400301444805509815400c501004c0341e0100100c107003800030a4035100d0f2030741003a00d01e401a00904918400860034000300200007005605940049a00701300c0c1070a102000c9087c0d440180b0000c0c0140c010590044080b00e401d04090a0030b035088042e500380d1501d034070302d900840c0c1c402d9105460b8100b01c04194150980c1c8004895000740c008000b6090003c00f00300810b01c00c1200403441020050145165047c8612681410001d194400803e561b6580345400040c81121030740000e4070002403541c086490115640329241035485644000841e1502d000c020059980c0081d80740703274050048248481604400f08021702c6003030070800409880c0d408110300c0104035030700c440b00c10355040d1082121030040fa80001c2514101c9506140080b0790000794600743d84010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 723691151 1250 723689901 723689903
    0x2061005130e030a05090f0f0f060a0309060c090e0718230604080106150c05150c0d0942020a0207120b0a050f04022413080c120d08060418 61
    0x20001280c00b107070084e802002004441d1b0100c680004451501c000c00521482480f901e59000c80d203d062a01035082c680c000c1c24441100b8103001400c542d1940b500c20941e003104901038006501884144040010340c12880d4125140d0f29001d00a90504044c0d17440c203540134020418150b0845d061495642500e5424211024000d0101500c80744d41d0141c284c0030707124601508140760181d003c02d1340503600c5060020420f582000080140c4160749a00c0c6444010150000703543d02c00800420600c08110301620b40960710a601c501d0700e064001e80e1000000e81d100c00d0f0852003411516080f1405195502c10403c05000b52a005031b031054124401d030300d05902c907408102c00614140c0e40c06c060202803501c16104108100c002d000a0740c402240d40c03101c22040700c0c000e60200d07040f50064100f0300382c4040d03038010820440c030680c58136241e82803001403814150711a01c02d0340d00440740d091140c2400d81000c00c1c1c07100250014120750302840700181100500412660140d9600c1403a4804542406c04a030360311 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 723692401 1250 723691151 723691153
    0xa030507080d030c1d010804031214330f0117010f061b0218040c0b2a0d0c030e03011d0604120801060212130b04170d02061005130e 58
    0x90307a03520310564030381080325500390100345410710380d04084d8003d0742c409001c6822a0b60100030841043c006403060040a44154204a00046022061241c91152151002d181036000400345440140e1520211156184580f000380300b4100c5d00807200c0ea0b480211510004965a600c2407036140300403115145c40c011051000c80018000040112280c81c1c07560545566035034410040b8002c07000600e039240031010094104400b081035440300654060b40d1500b00388544105500c4503510034404070240c016841405810b51105040c00101d51360390110020080161301600e03a140c4043c00c0079140508001e009424003081d07003071111403541c0a41c40001840c24035035080802c0300e880c8c040d0780e540715011141203541c100c6403580c240806020380314850480300f960380100301840f0840320035032080c1c109801488120011440210300c08583c0d40c05071000d08a6002d080b5480500030080d02e01d0b09031440d514805540020090260422400e03601400b40c0d003007658220308801c000000c11004006060b040349031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 723693651 1250 723692401 723692413
    0xd0204020c100c12050c07020d0b330102060609010f0b070311100501050310151205070b0a03020307080c040b0304060b0105130305060106231e1207030f18050a020f0a0305 75
    0x22282c10500041c054004c0701c804220310380e10149605400e10884d03002a6025054103c1d40b400143c18a04203030384550988621100348000841c6185000708030700710396680620301100070400d96030400c070280d480b0300b0803079401ca219490f00c03c419030552a9405051030301c04000541800f850b000e0106665161039000407a40b094020305a454000c080c280a124071900070100314008074451400740e80f0380c81c1441c3d01020070452404072418002400c1030300c00c4500b401400c0002540340c0a000c0a029807141d0b64402594902c1c106030b00502d0010010200201040d040c04280080120b04090b02e9100b03034040000142e525180b00103a445028002041900340b10749000801082804540a8100c0f21a61141c00114901a0b0561422000036a02e614080010b001c980307140646400c1401d9480e004110b05854070500c100004100c030300850380003010980b10906034400000074844c00b58951094410403d00300d25a5503200d841e03d4040c90040e1140105403039400c5142c0d151512840210b0780901143c1e8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 723694901 1250 723693651 723693671
    0x40e0312010801050412021626031c0e0a1a070c0f0309030201080a18110a082a0d051506030f01020706050a06080c0612070e09131b050d0204020c10 65
    0xf0180004490886110145d95103843c034503400011500f60741020085490046800c104a0507400700149410070716100d02a580c0c51900b203000e2000701201a01d0f0003810100401e6401608290354131b00f007000e001030344040440b00200c0d400840e103110000c0340e811141600d8684040490b010211500080c0125285403012010540c0200a1000b1a8400c0e203030100c0b10707590001501c04544c07504482441003d400d0340c0d07a00015256406a0500340c0001313100c812026261b00e022441c144184003070709864101c0d45d004508012180915640410044550f00318207004c0c0c0c1d44040e01c030407c0c903104100849000d80405c015640038842c001440102c0707802192031b1041d504004003e018103607001507220b81340c114085a824008110f4440d003c01c091f1032280b82a484a10222a145c0c00500201c01c10100d000e44113001d07550700d8040340c0039007003010006032282e9090518201c0c04181c007203c9001c0e0b80101e2030030041c0340c9400b100c01040c96012240103840346000c40710181048640361074103140030300c0c04000e04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 723696151 1250 723694901 723694903
    0x3130803070c060503011a091306031202070e041703041401240905040b010e0705091f0f09050906010309050f0307030903050d020316080304020d1a0a0f0515040e03120108 75
    0x100c022070249481c0d0811583d9580203899505c400c1c0a002c0d12101d000014450b6800108020a0300e07903c094402090348800d04503407001c0740c07015042240d981010016900703140341d04001c680054006250f10200c103040a0f0303100020201c0400e0013131000480400040c05004d050462181850307030140c0203101050710f9030055108030354140844040a90100350101d5101c0750b900c200da202d20390100740d9818907424055002000c80004000f41c003040f80c2080f0744611501c1d4260002070748841c070342d0280d102d0703025201d0144c0b81030f10706000b210420210302d0b400c011540d035442c03c0540220b000c0c20300140d40349807410124105210724002803428400080d080381010341c13000d005001c8900600c01d540d0f03d05110a0100d07128410001c04095181c0d00c0190361011842000065070000d00c000c3c60400402402d5440040414041c800e51044c2d0b0140c00404c0090342035402840741c40e10b0002070070040c1d450070b410588001c078103118030385005503034400d03505412034410021520080d600b100c8070034056075654005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 723697401 1250 723696151 723696157
    0x270309041515051905071713050f03010203040f39050312030906041106040e0a0e0d0c0302120d02040e010b22230310090b0103050f0703121103130803 66
    0xa90500c45200c8800e9000b00d100d80c0589500d600c11294442e1125150402151540c00140003654000094440346009203d01c0c0000c001d6000c141c004900450710342000c01c001c1c5030301800c1e068001d9004004100000700038049041a240c1e014000c03c07082d40d2049a03080e800d4500066440d80d20688071142c5d00c0140304464001f0455400f207040310b403500c0e0407400c5040380b404169a1020182d00038404100064204041900095400340003e41410b640b03216500c64910190361400c4000c0e0741704c1c2103101080080c081d600d88241c090900003d041203032b40d4001d541d815910000800d83c41e01040010a5041c1074040b07600501d00c2044035081961251181c0b441075204100e0100c0082141080c070007660101d2a4a00407079403222080c0312039070302140c0c3d4603050940c0343c08038079070502a1a040d8206d040c03451003140307580303401a03250420340d41c1035160a603d490508410307e6203a034801d4000304001404020882c070710b9900c0349084c210a142c00c0002d94554004c600a1420181c01544081a544800405 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 723698651 1250 723697401 723697409
    0x904020d0510051002330106081f05010207031b172a0f01030207020f04020f0405180f130611030f2e05040b1302032505032703090415 59
    0xb040c5060b80d5030b0002c000c0324030f5805200c1405600b000d645210000046102020603d0100c10001e22a01140d0810551400c00343c10a201003054401441801c0080e00071004160341000c0c0703000c0340c903401c04002030750342d2680344001044100c5000c0840d400034103143d02c100c010f200030460459550200c80459071680341007010103945a0081c80c5110702401c03885840c1c20001d802600410440001e200110069404480280e811080b100c102c02e4a0b500c0f244028500c4070b0f2021501600c440c00c0904100e90300c071400010001c0710745072a0612200c03003460250550001103e0052a00c0c4d100180340800c00741180c0d1681c090000000300c03c110440984144181c030810f20351900c1c0c260b0384c4121709009840248540c000441d1810380d0343c01d0200b410940e0040a000c50020284400e115031492110b09aa10894a0300c0c41d06001040040340d8406241c04c1c0d988030f030b2150070001d00718a4201c02a042c0c40c903152840e600b0080001500514117082841214030104018005000354503800d407900506144901c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 723699901 1250 723698651 723698671
    0xe09060604092109120506041407050a0308030903190e03070b1908040519110a08012a1416050f0a0b060d030504090231030201120203150618010207050105040b03070c05030904020d05 80
    0x101789c282c80b540100e0880140c8500510391450302d401c540f6010410b8000030036514152100300300350703ca51283c50765510800790840d46d406648082802c00e00d070821150364440301c01c40b01c0502c6411000c0c4072000c103058403085d05180c04542070b41d4600b00646005403189a0310322210300b107007110040c0001781040700301d4640103a400b20b4010b5030341c003000e03401c86000c40c0c010407240700740e034a01000c040c061343c50034603070900300b071a014203482049001c0d0f0304154000074010f40646c1c06803416004102d0188140342c0581009409080c1c04605501e81c2c412101004000602c68507201c080c032800c1600030403c2d940039129182d01191211000c1c4504c01022001400300c86116100e0000c0c40501e4405401c4401a40da06035510b1000c26840303007441c40a50005032405080340e40b00061203100c3c1c0c07200c6000d04080141068030640c00e031902000641040c00e941c01850410200308024488503916000321307a0040d4403850290141c41081c18414190b0082c6c03096244e01600014100380e1401c0c00c0d1308054010074900c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 723701151 1250 723699901 723699923
    0x12030604091e0b060919050603160e0109230c0f0d0c110c100e04090f120906110304030c03020616060f06030b06180721060e0906060409210912050604 66
    0x2004000c0640f504031250388012105490b4002c0346c5400d80c2100380c0241c1e003e41141e100c0003500184116031580c0c0d810043c180280c00004100c4c4200e28000c264512500c04c01d4921010054051000030003001801d0003499180040c60100c561070746400c0b00c2a01c00b4100c0c04022003002c0041c0100028900040c0030020300c261484010b01385010b040d008180000741d1510030301c01c005002840064051454260340100d480b0244101180c00507003e40b06168241e5600d040c11070030300380c01078040c40481041030129442030206100050940200200790303a011030350751707446050712480e020a400c000d000040c410360818503101e0703503030000b034001000343c9119500001e0240d03100418805200381c00d209040c042c8208901040040307014a59515080d20458860061040c070820301300240d850729400100d00d0401002004070300101480003a4001c002150140300d1085075460740040741620401d6075241e03502102d0301d80301880c0184251401860400110030502c40e1505003242c4940701214140c0b01d4071444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 723702401 1250 723701151 723701161
    0x18070f17010e031605100509011b0f0806040207062a26010306151208031b19030e2a0307050a12080a0e12010501060e030a030212030604091e0b 63
    0x60060500b0710344003500031403d000180b800e941240c40c1424065900d07010749620320340800c4003400340b01d200c0d00c2e41c0390000c501e4070082103895001d4000c0c0b200b00c404100d55240d020044030342c0a03c0203600158101e81c0135840d2841401e04c14014500d08070340400c2e00c0c2c41034000491170345000c01440007460068685199404074901c101102080c1c0394249a044060300c001803000038119070204603008a412010b204040e103d0b840401d0b2032560203416a865000801007003110000e00003203441004840e403809040c121104200360700c048901d0b000c0414076803507030313007241c60720500300450b240740f80d40c5140005400c2c03202404031000c0641c4d00300c800d0080c01503c02c04036250610300403034000ca41c1030030a034420150140d21345020340e402507100d4404200c001011810241c0e915001c0308012010040000b619514004016001c07201c0c600c2114060380298510f580403a4012446444040210010039542c0e920580090010030300c1c804010011500e080c2c3e001000a540050400c1c0c4501c92407104241e46c6075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 723703651 1250 723702401 723702403
    0x7170703020c0319030207050a083601201501080c0406030c060c061103010b090306010608061e0d0b01062106270b090a0209040f090201021518070f17 66
    0xb480c80c544400d51003041204e18011408101640c42d883c280f41c01400d01456981d001c0c1004c240071400e44207003401003040c0c41030904828182c1a040342c0b80340c500042218450898907070010300000d060502000800e090891494200c10760030074079803482618140c9021401c00d200941080c0a040381d03910a082c030441c07a505151003030b4004c0d650442040c0c0c00213031610804540ca03441054040f200340e0780b40c1d9841305140c80260f0155001c3e1040503002504c0d071038400c041c5468170350164442c4007000301100c03d01c030321500d40d14503151800e00c8040202c4c148040c00c901003040c1960058004113003041010001911652000203030200d00380c940580da503250a410786010681c0d03e00e0185001500d03c0070340740308201c0a10010041e00e8500f800e00481c01d0010900018885240dc50701104020b4000680705c1044c541481118003071904240c04004008658000075507034461240c41c00c0c0388209020200d14000484e00c000e0030300d1120346049441c5151a5002141c0c50359451150031120b90300c0918854103008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 723704901 1250 723703651 723703657
    0x2031c181205030f07111504060f02011a060f04120302030c2b0305090c03010603060b040b0607110f03030c07080c01080f0f0c0306060c0708030403020f150d0515090717070302 77
    0x10b0400d00560800d480d071000c414503584985811200341404105040d403a803943d910310843c4081905206403518030b450740c05083c0500d506c0700802164500a8440300080c0c4003034040c00802820f80f40251200303001e50f074040c10391046412490300b44002228150405500000810b807500104058a100d0400400982c031606851150000411140444104038038880d0384540e901202000c200d03100c005084000c00c2c00c4a00e6a0016283c041e1240d800102c0c80c14280201d130030f0001d045d60814030b05501c5858401801c0b911a5443c1e00c10700100c18080011760301001500c484c6034110059034004c698811802e5910180c5000f400e001c500000d001440440c00c0c05d544920510840c410343e0703055075550b449083c16a100503c0594441c005100c0c04005040c100460f5001c2c020000c015552541940100301d10b100404c9820f610801303080f01801c0d50684142d0550384840307a000000b06040d180e02c1c0401104810310390145070002200010003e03626440343e550940310f1316000d0f00f050f0325180c00d0405c1b01030344 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 723706151 1250 723704901 723704903
    0xd0902042f0c03190c080a08071e1407170c0105010501030f0504020303090d02130c120b2707300c2c060f040605182b02031c1812 57
    0x90001c2c0503401c10400404c180e951000f000e840c00d110450075985d507118158200190200004040e10100b10308140c00840c02411000031158202c00e58498800040510894044559400e640403403160104600300007a03920242e180017210741c4034204100c040f030080c0300034403505001a0903c16820a1019070b413144502842c2c020f030107546003500010500c1140a040e05080f0b1300050142c103000c0a01c0d4503031040b03114528041e620b4000754501c44581c0f00a460040c91240c1c0701e0b17055083c100c44008450843c05130f100041801201195441d05010f58400c2044105d1000f0700207455101c0d6000102107049000348000000c0030401c1c5800d8520482c1c0d00100820301850340000038034800e00382030071104810004400248400d01d81000c1d0f4200c12441c0e0010346c0500041000820415a000380161005003584d03010303153310201c3d440d040c900c0c02d500e5184030345000061428210308015900c0a002c0007100070300441c841d101981d10303000001c180d50288a0700480e0901001804250558901c0e10030301e8103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 723707401 1250 723706151 723706153
    0x11090a050613030b0a020409050105060f0307360e071e050c010f0f06050a061812140604030513091802061303050f06040b0a0513080d0902042f0c 64
    0x1050902091107900d0703021160380c0140c0e003150302c03001000032000b50101c1d04c108158100580c440d0b1609180300c094500607080ba6202c0e5006200d0480c107a882c007019a0b0380415685810b402400c8000941400340c1a484501e03c85118114044825400d061503031034204c0710101e1070264540d4035001d00300d45030014001c80c05880600240c034003030054414005449840346038000007030094007401c03003c130484624100001c0c84c0343d29444108102e1800360104801061a4200004c0c109178042c01d03480842000e002d83d9503405801d00c1c0300420b12490740000c0710728120103802c5600030306080c24003500a0b00180c100c4100010384172000704060b003c5005d07401e07190381c082c41c1210340c110656080140c030b07401c59074559803407011165001000c90800c00004000510120113854142402e04220400b402e00a2508080c00e0a10007881100100032000d00000c6400c0b8410799152601c0a1a08002d00419180a0b5215040188024142e03403200e44105d116466a00c04400324003048181107624003031401c021100d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 723708651 1250 723707401 723707419
    0x6030b01050103180323040e0108120c06220203100e0d0c0c05041a0a090507080f0f040b0711033f01030605040203010b060406050d0c020601080a03110f0f101109 71
    0x1034010f4440301d50303203900780701b0480403d0b402c0301c14005903402030b80c0450101c10520004200c1c035002809070300e040c0942d80c2801072800c4e4424100071303940c503c098204485800074410900200c2e00e00f15803d040305a008084e20f00311070103002070384042c00d20300324403443c0c50144d103100c401c400b4029030510b04004e40c000581c0c41c0c82c62800e010400107041d5066203260840b885d0310446000c2e5209805440507003200c880c00595402c00b10002003021400a152a00020240d0248100700300140d521135482070f070180581c161955444000c8900321811a001e141512001c100f05c03802c03c1e10703030042028540c40803810410070f90301c54134628a001c50501d101e004038441040140041031300d0f40c00aa5000d800034001107200300e24840800d80d20f0780180c1c0908009500802d09005000f04c60042d81c040005504c0206800d50520042c55115004580018180702801d00c0780722446200b0311151600210b001c0503205100d15410b0007d45131007140500743c1780345190480c10110108000140c9580300c9003e022110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 723709901 1250 723708651 723708653
    0x20102033108090d05010c180e06060d0c030e0d090501081b031f120c06030e0105100504020702180f070f090b0703030b03100504032609100209011806020106030b0105010318 76
    0x40309500a10f0f0150300700c800041d540004c01c000740540d15038030100703503100b2a83d03101010304040d180045401001201c0120380c140405641eaa0b419505013102040b000142d030a003d07041580140108000c00042d4020b242d60000c03040d4008008038101c40d000c0e2a4090f0984d40c040390080c282c0340180181c84d080b10700b4000306128002c50700b1003030302c50011034448442440c3c407410895101281d004040390391076076940040c02a2039040c054140484603000c02030116060480c0160b038000c465000c0c0c0c1d401207501007141025569400080107040001c0b500103122810003407000c803600d5908540c800007181e0a402c1e0b141da1544162046c00c102d4035140500390400d08541c3c0d00700c1c003410303001d030b202ca51605c1a50726003186400740c2c1c0301d0980201d201c3c2c1c0342d184c101445d101e0510121440d5003030068207100e00c40d04000744124041041045405540d07801603580548000694030000c962440850300f5012036000309060390158030800c1568007038801c0ea01682e0b40d510044003502d440c01107400c0b0202648101d54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 723711151 1250 723709901 723709913
    0x3090f140d1e0309081225030903020a060b0a050414011511070b0d33090b0109030b100b0a080405061005010c0201030f0e030a171e01030f0309030209070201020331 72
    0x560162041144906d002800c07207074504c5411044d14140c03040030030368141c2070b907181150100e0310700a0481c2c281880034068584010b511003503801702c05030000d91264040850303640c40d0351400d00036110062080140ca20079103610307108401d090051000400c1d00001d0309512a00541e041441c1e0703140e01004001090412503110301d40e0304406030414100da150030740c44c10070036450003440910081455403459800c2030040503800100070356000f13010051030184804c4071030f41c0c000304480c2a2030308040d040282c0e44601a071910091690b601c82084c0140c089078034004981e004041502441c02101120155182c130440c030b605200c05c500c5024007140c07503401441d0040d4000d03000003c0ba011064000100c1c40f03040881c007411940300b040054005648048444000c2c0c0351a03031200e810498201d40c0300030b50828004000d200d10018000540101003801d014402c042c4500070540103194040c00c0807046081000c4068080d4000341c5480c1c0c1940751f940c407080389178022686108500024101c0101b00c14816071505 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 723712401 1250 723711151 723711161
    0x30c0b0f190203120421031e0203060604080f0a03090504020a0e010c1b060c05060a05060109032418060b0906030d0f0212030106020304170c0105071203090f140d1e03 73
    0x503042d8042445a00403041c507603414075100b0750084008400403a951031403044942010b6440c0002d1500c1c21041b0071000c101c03a80d044400d0080443c0050b40d030344603100015500d000c0da071f10910311441047c079601b40d03100c80401e01c1004140319485000d4400c4c0c0300c0040005a00030305c080b420016844c015400c05548c4540ea44001880c001c0c070700104001e00d11401c801d01600290041000b044650411004120040182c01d0b845841d03550100210f0600d000020410303000c5100291245450100c3e003004403072007107065030340644450b80401900100148218400300c0002068481c2c03440c2070300030412401c0c050354041c4100c9004000e0140710800c40d1f425240d415407206c1180861280034003803044c00b5487c1c1d0095000c0c1007180c0045445500e8401d09907140000040035048582000103000d400ea6000419074443c980d00072000c907010341e0a480c040f001490500000340c40e4103010754a24050042c501191104c540c1c0720b1080d0340b40940c0002c2d040c3c1e82040c989941010207444039804074046413280d482 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 723713651 1250 723712401 723712447
    0x16030b07080601030f0e1c09080c060a09180f14190f020903071d0106020d0206040b0424140901061802070606080d0914010c0b0f060a120c030c0b0f 65
    0x20024040802503040c000302e0310700011914055014540c020f20614210546d5204641f50b445d10800c0c0c1824800030544400d05d02c3c040c28018500071503040d61190040505c940540201e81c8480585402c81000b080a499020340c3d102803145414500d6906440d800c0005115060308000580c415070100050001418902c05d000e4581c0c2d401e1002c0f01555406010b03100050040540040d51141250303500b116544040e1302c18400d5500c4880400c140b641c003c10100e030b00a03040f0b0401540d5940ba42030005440d03179100581452030740c10f60701c55100ca407103581c029003202c0e13190110900c0d940e44200c140c40c202c55407402640d94038081041181981c0700142c0040c008144194008030b810f81e03840300c207079142c528003010304800302d5041c0d1810700035400c8881388082a41001d19103c400308500c3e4550501000d00504004800d2085000103000b0b52500e10040740242000400c2c40c1180c401030030501082e4011f0702084a801008150011754070560340180c03408450180c1d052032a00120b0080041400b5171920b07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 723714901 1250 723713651 723713657
    0x913090b0a050114153604020301120f0804030c240206010501090513150e090d031107290901020a090e01080c06130504060902090f120c04181407060216030b07080601 73
    0x44210790110810f241200007411075094406c240703036040198013a1942c0e41e000d24810300040000902190021410035003060141160000781d0a000300c1e244107603080945205502caa001540f11414816403da40c030b02001c440c4002100f2203030481e16240203200310303800101c011030b05003c0381c9042c2d140800103030f298001c001443c440f00400614401c500303a1101820040e03080c2000365106003802583d64000152401700300ac5031220004000030300a013030028044041d085000f0007070752101c049915000305030381584002031402e6200039010303500440400e40002d0384450002007070304e2000d00060684422101520040d02800107011a6401156248a9a25408070002100d0f2240d12900000d00852400580c0e07403075404052026413041d5a442c140200c1c00340340e0804400501003080d03600d02108440200d009000c00a0301c01c900002d0f0386010f00418211040c01000ea400050391104613000f50f02a140d50b642c0c610b00e00002c1e0105e0b880080c6c500702007480001d101342d124101e102e070701c440141 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 723716151 1250 723714901 723714907
    0x6010e0f1009150519020a1509080904091202070501032c1c032012011401050c0102030a0f0c020a03090306150b0a181221050913090b0a05011415 64
    0x1043c021039240642d00100e000c10000a195180d200300c1070b16890805040780018201c025456440c090419150058a40c040b0360328802881000101d4088807102c00c4020030034041084a428070300030180c40700d00484054450a4000a0194024000c0c07003010820401c81c02d01032180c4411822915208185103001e6015031810f2503a04002449401603144660358001182150016640c00340c801d908110b0070026010b0091104500580404505440741c1507031403030100700540016102406a0b0441c07d03c0c07540041304000032409164840b2015111510042c010764050460a81e00c40c2c240301e4002d00020143c64050000c03070603035000411401150501e0009860351504e19280c103401c000313006800201c00400400b00049010044006071030b80045002c241c0d599030f0b070ba080c00350040540c284201c00e000c5c1c0c90244181d0040d41a00c480003000340c110b60f0140c00840c81d10009124020040394a2000176020030844c580c42e219060690341d41080c100340d01c6c51908100500e19004401c1500c105000b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 723717401 1250 723716151 723716159
    0xd0201030b03070608060307210312062706060e031b01090b0406051308010203270118050304030c080309010e04090c0302060408030d050a020906071e062306010e0f1009 74
    0x8003c078500902c42a0340b07504060514038101130030181654007101c5110121190070710b2102040c03a11100d600d40c1410071000451a040501001c1d250603408507840c4e21400b1428041c031b07031030040001b09038404c1c100100006601d80320107442411803d200141c25500103c500796414403079841d000816a0141080846244da070003407010036a115401144c00140041040c00580600c180c0c14405060014025811403a020440808072040804210103210b0f4108501d10a548203601028009100b60004800074180c0d00708555a0b40c400d2008990180540c1030005103402d000c000e46101c4a4140e41d40c82c01c042e10402044080d00e01d0140a071045103c40b02c0010059039454010b00c020603d45002d0358444480140c8801164001881c401d2154010481c0701901d80e1510704545070b01e03600603101112000c450b56054505514440001c12503854002610b07a00d4194042e114a0780a541e1840202c555400e0011248060815545038101d120703000070108501c0c1c440480b00c0d20784041c0c6044549580e075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 723718651 1250 723717401 723717403
    0x31503120702130908190302270102151012140604030305011d010312080903040314010501050a23010e0103090f060501060206071e0315080102131e080c0d0201030b03 73
    0x556048180142000554101141821100702c05020350724142007154101640765175249201d2072904962440c19000100346150003507060b0783c10300d0345008496000c2400e802800e5001c00402400601600c10700484c6205203803684403072032040c02c600d810752108918060094034040c003501800c80700105d4001320990311600401903103201da40640d074080703480d514007460041e20a81074048241d03050050750040c000702d01641c500608102c500d2038258469070340c0d0390180381103021b00e40004041c0441c20058200c0c3c41015007000703043c0d400844882c22029910214000211200360600c0c1e0f946c141c15402104544c0120350520742004103040214a1615580c1d401207411a03008046424958800040c040264100102940208075003044c40c5404480c81c08140b000144011030010562200d10102096460802c01402496580000e545550010940001440c002c0c040d55640c04d655004c441c2d401c500700080042180c400c000584030a41204041c05040d6449000030ba05040c3c13109042100b0f0f440c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 723719901 1250 723718651 723718663
    0xe1506131805010e150915030c0909010e12090d15110c100f020a0c0b09030f0309060906060f10080606130f030302060f160e130c0e03070f08070605031503 68
    0x41c0d0320000100c0c3d41c10071120305600c00c0080d040749540141640f03070740142e4070b4144089400c030900d01590800d9075002c0b070000780750030002d81c8144d801680e80c406201d080d020540003804c1c442c0080c0c0035120b01f15101c0000041901440044a501041d80340001d0003180c1d0303106840c01c581220420206901c11000c0c00751400364000b498101344e560103200c40d018100d10910810814692082c1c0c1503141c445031410050448150f200003034a040840b2010074800e0f8010801c8600e006295120182c685c5402c150064072800e0445402101c3e01480e40002c0080c50b0008100c0749100e03004008409009103908101d48502c8010506504000c0c10440ca49040e010180910000c00d0102c003080419800c41c43c000741031042c0909080c031140f007aa0140007000c074040140c4410040f65142001d5661451000a8604448800d140d24010300c2c28005003280390788110b9240380c0c03401c00d6088403e01903450f00506051009482900c42076002440d05204a520480c002e6070000c0302d64000c000070014440c0006d041c40c0d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 723721151 1250 723719901 723719939
    0x90405160f08010501092003070e03060a024501021204080a02270402040f0f0c0f02250e0403050d05010e01050a27050a020c0601081005010e150613 65
    0x45100c0308020b01d82090103140c2c09468007140a0001a008041c880300d8844e11540d0403212030004000110f4181c0700b6440e100306981c0080890700f0783e00381030000b08000d50000060842e182601c131101040540ba4101d407410242051101d1403000c403140b4459605030000b41a41d038114010144c1217100c0800c00c0002d000503081c0320000c0c002030348d4248100440d100212000d590480c001c4080c0014804806450562094050702c0c04608511428180b1004003184210944040d2602c0740c003446440d070020901d26164401d07002c58014800c040309a00f0110400211010104400b031402c0c0b101103800c82c10300b81c005101c0c1c18481d00b000040c0708150b041c0c842c03d80201c80c4114244004010a2902d104204002c0448000d81041c1e0004040910f180c002c00c0c401c0b01d4109a00c0320b010400f522000e82c111b40b0b1100401d01501c02550b10381c045561a000480c410103142403c0100109440824200060081002115000780b036070009082c070445400a50103c1c500310008680062001040c0400c04880 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 723722401 1250 723721151 723721169
    0x60309010c030c09080a030302090d14150606070f020f030304030804031110170a050402012007151106070c0c030c08100f15090e0a050d1119020a030209040516 70
    0x7504000000804580080c0f40000804c0200502000501c00201e50581a07641514015948040160200d400004200b0000305a2503c05d98008629200400c0c0c1c0c0107095006022441c03586c07940c008000c550b0092200203440000c07142c141358014a483c400501d01c0b408050305580c1031598948428901c0d8100754800c2d103000c8155814110145840e8081c0c0b0310724446414040f0060400d0307041c00106420007414400081d541c2c0001c1001e5a001e000044a8403811104d01000307800d1014180c2c1d1104e03054071581960410141d40c1c640c071903015459100107010b01c030000700b2050f40d942000301c80142c41c0c4001074582c00b00c001400701c040b030064049140a010250700034144a50012400000c40d061a813401c246240703480911000c0440300030281c0200c1c1c0b00b8140101d02c80110824180c105000014000c1503403260b5107225411541100c0d0007070f504034814043e201c440345001d4110004070a0070700000d40c003239040d400c1400107103840007003241c01a00440484098440c09180c681007800a500a1070130 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 723723651 1250 723722401 723722411
    0x40804030605070503040b1611010221060a0302180c12130302060604140604091407060f110c010203030a0905031621050f181527060c0a030f030b06030901 68
    0x1d124841c001e080d00034030540740980c95032a06031140d190452015100c50352100b1000c0d5110651480b600240f40c0c0405a030000f1903441c0c80801100b810340e00400c0c2140d01d9030401500103100c81c6444a20701c02125000303450980b901003541480240e03510004d0030784600e00010301c00c0141c0e0207004618a031080690170102ca0741c0c0b0526080207803520350001c03c000d202d1410072100c0c0c202404034145441d0000015100030030b900c0080e240a9101198851100c1c2c140c3c030a0803000035110358021420920011161222424036004a5030b46d80c8901140c4032941c05640108003148449035503520145038503008100340c9041481c42c121500e01c820003c84113580d0709000c070b10b81c2d8406500e02c003c0480b02c00c1290901d40d15044900d5550003d03805100340d4540e0030100c00b6040405911990500d00400d00780008107a921000a40c16140410b40c03080301590391610b00321642860b007882400c584c01035a40b440140740307031340485c2e03021140c091107195140e04140d2070311752014003032700c5400285004459042c00490 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 723724901 1250 723723651 723723653
    0xf0504090f0204050a140a03110604380c0d0f12050a06150e091f0e0a05100909030813020f0d050a12090e010b130e01031119270b0904080403 62
    0x300c0c80e2901d80107a40031b440e1862800c8140e50b40c03220102d0441e540f1402070b958118903000041c00714059a4010505041d2041c080704592680440000030356040144519040c0a07135442100c01d401500680346041c0d02103000c0c500001c1c091612007401d4a00340c509042400c0c20681c1c140d082d2101541e0030b60b003042c1c803080244110b10b00d20301d140800040368502021416948000100200409080010162907980010b22001c4608101401405800d21110b809051184d0039200400007100d0601d400d04c1c0354080840c0c027141c580a003001c0560156507400140c1c8403220f0b02c00d54032410301c00c202e80c40444078414504036200e904001d500d86010745d014002d048150f081101010b002c1e0301d5601c1c1040110000ad0184c0306c0024419810b481e0802e64840d00d4903880c00000c015040940c0220007141c1d113490002040020420b00c10400400544031008030406214000030900c0c030034002c0c0d582c610807005800380c420404011a00307190781810350104090345c5070306c0415010f040544041e12410700c0014180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 723726151 1250 723724901 723724909
    0x306040b043803030403061a0d050f1203191814010b04050c0f0415020307050106030b04150c0509060c030706060b03011d0106020607050c0a020a09200702100f0504090f020405 77
    0x120019500703100d82c10b480d4000000c0c1e16846079000080c512640c858515090350031540f2008400c40018015400240c1141019a5203800c1e03e2402381030340c410600401c20148041041d41d00031209040501c4039560600118000b40420007101d202c40c000c4040001c01283c0c005182d4021280c1145c00042d01080c03581c148000c0c1d41009084203103a6808020080380b005841046400b1910b16003103030a210101c584007241180300d1404041c0035982051408014080d448a40c54001d504c207070b40200704000e01c6040503007922240d180d11808100f090206003810705255004045c4c800c1d041c819245060038968402c0101c0e180394014903404000400140701e600c1c0c081402207001d00e07060315a48200c2d0300d42000250b40319402018081040b030089084205208100800c00c80d2236401010b000c02240c03210740c01e01c02801c44d070341038180386040a455000c502d03601f8411902580d80103424180d0780ca040d50815210080b82003980010040100000503403040d0522030503007120f00b03c3c0d034056948c902d050204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 723727401 1250 723726151 723726221
    0x50103150f090209060405130803010b042322060b19020118150b040b0603040308061003091a07021c02011407140d0b04020c03130e1f09020306040b04 66
    0x1c281c03154602207582c0050307519039443d03a81c8100200c5020481d6921031010701044800c10b40d0061000c0030210000c03034014000d90141040d1512030000364180c80c141000400154064203919070014001c1d2121900000c0014140560080d02c40002c0784190380c450b01d0352429402075094418281c0265009100c00f42e0a000d8440c2500d82040c14181030511500c0c1d0080a0395034111078001e503a41d071401d0407900d881c2c50f0170a140b040b00051200e43c8a1a050601906a0208407044c0d88290506c41000b640031b4041d101341071007207800c100503403d46004400300d42142b12000d4104030035803060112050b44202da0002c0e4050714100b0f0760000c1460100c0d07452089442034054014070034450020404e40000039001d003079940041e01e50b0804103110b000d41e0045002445010010286400300041920100040003218411106d640a00c1011030707544946031540c3c5e01102d03500920000303405908024690058001d1a04558004c0c00056800307a1720f000501140e03100c01207038401c000e84003c5024000800e81d90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 723728651 1250 723727401 723727421
    0x605090c0f0d02030a11041202120105011d060d0506130606232e170a060501080f091204060c030206060409030e040218040e07170d0912030c020405010315 68
    0x50030080c00c04658038050080c4900d000300c2d20350110000d62030382681e4003c2d1035100c410144690361691202c100032181548000180e029016021440e01c00703050510400741200c034406c1d07442100e200f04400d03181c00b2000141640342c0c1b0244812010f8041601404042e0040b501000071440140300ca00d408026a030880d4801b1040c51440043c03010708000780502d03c4014001224050030941c0450074048081c800e84880d408461032210102c1e01c0250840c1e02d180204c28000d80e040c0c0300d640c840c0360503400c0d500607009850018840c4000304582e440b609540c6600850300c10b0643e5240b180003245c01e909600640d00c047c0004082c2030a6105040e010b10041d90081c0302642c041c4000100e84e00d019007002c2c0d103000c101b8005c1d40d000410200c3c801c4d00724044910fa40c00204207100c40100010340c41e40d1040207010301c0c401c4034030324046401c64402c00180c0d1003481d1042d40341c800e40d80c1d00d414041c0e0341401d04004180e081c4185400d40c44011303130303840c86064080c500c00c2200d46030610a204811007114540c0390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 723729901 1250 723728651 723728671
    0x2070515090a05060d142d0603070614040e0f0403030c0c03140a031815060806040b160e03010207030801030308060604030837030b01170105100311130306060509 71
    0x1c5404419100c0c44044429207105807280b582e00e03420085820020400100c1e160041c6417202d00380052011400040700061400c1d00c0d540c0740113240098106c00f0128160307501070341341d404401c0401c0712901030000300c82440d40c1c142c00c060500fa0754030081c1904001c21209a800082c003c2c007040105a050300c01c8403064041440c004501d145195005482c40000c940d85010540001c28075904891080d00003260385480f02e180490410b15503c4c0401440440310011600c0e2030800302d0102c1d0050001034441d200c4d40d040043c0b010540c80e003074a50060141010b6054040000c502c0c410302c0e440e00c0034001006844e00c13a40d10303140c441d0b1441c1001800c2150141c40148200710401040000c6207520f020340f0b4841e983c00d00f0740848a0b18015115450629803a281c12202c1503161480c01219055444840014001c1e25001141c110328504025040c2e0709004840d0721400cbc564002e40c1140c426804419075003019400d09203000710500c1c2800d42a81c6c554400c4032043d44a941c107026608201e076899802c019110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 723731151 1250 723729901 723729907
    0x1120b03060f0901060f0b03010e16020318012a023c0301061e080d0503060a03120201111303050c04052e0302060418150b03190b1002070515 62
    0x100081d01c501e409005442d11a00380004500ea00c42e00b0761101c4010b01c80c40d5005045280c0c1c1d05505200f03500309200c5c66031015103140000b0403c00200c4450a031002035680036500d0465121003a05061552412850400102c2c0b10f00fa00e03c403d401c01070140f101480c4888409050880c41003200019545c00141d951007038500700001c0025140182403502100d044e030b2070180280c0080130034011304099100414040c011b144d1105041954801d40d4140c2c3d41c6c54056803030701d00724400291191302c003d13550182c00c20322910041010890300e07200095044a82e10020400300c03298000c030742c3c05070004501c183d50110080000c004012041141c40300c0500190780034003441c50701e0298082100c0c2d51001e078440d50400c2c40610504070031201007120145500402c0e0710b4039a80c032022010030083d0f600d117120f0076462900201d84040c0c030002c0390440c221502c0c14100740c80c595801c40480100040114560318143e10303040009520382da107403526a1098065030040900b98030b02030400c010650501d0b580d00d00d284c420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 723732401 1250 723731151 723731171
    0x14041e0503090103091b0b19020a02010f0503070216030302030a0e011713020109030503030703140708060a061206030c080f01060b040b09012607020618070806160509030a0c050112 79
    0x101c1550b22a1009090002e55102d05040c2448040c907580d400e00b11001c4d070180c0c0410070700342210160611a0101100050040c8851000daa42c1caa01c890b01038080769040d0203a0079036500c5000210b50086030351050b84d00895580c07410b2005200301e504120096000426281c1000d5400040c01042e54024640040c03010341c810b8107404c0150018000d01c0460144c06410801d69000314901c4000b1540001181da99141005000f4028810300d4900c0108068900100341d250340b0a06410707004420003041e107d42140b4041082c5da003000c3c1840e0225402e51590000804201d5400310340380108080801707040030301203915065084030011b80013005a9502440203110903071410301551400c45082c20028103a01420000c110113808161440c0008a12035042180321913000c2501401070111000d11402445d004543d1a10307000c4a000300e03409580048005101424200c1c0700492030448c60400a14283c004030200c1d0919101d0034040c0ca00b4201d011081000c0d50388040244c4845080d9203040000b0000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 723733651 1250 723732401 723732403
    0x2d0515131107050318040506040e0303060409022808070602071a03370606020c13180c0308031b1305011d100201060303080c03040b130305040914041e05 67
    0x80900c50042580d00c559800108811004450105402c0070032a03454644031214050f0400e102401207025604090202e50716060074011000d40b8455000030303600396900c1b503040c0b2005000301d100031303a4000d00405070360041c004132000d0034020f900c0c094510618242484662440d0130b40c2544141c045500550341081240a10803400c0051540522034a40c0e80d2651540920300406843c210086038999604c01d410303c2c402c4003910088010034039070900010707999000036a141d010322048550090404d2401e459150580d9120400300c4007a11001030f07030039501c0e480d4440102c9064000f15a8908000148058180052040c00d820a161103980c0d181c6414000010002c04070740c46460f042c010010801891a4114070000c0705082d4042c20113520001c0e00c0100038007074a0203100aa011410f24000b2a00701503260040342d02c92500982d07000010748426416075680c03c1c612805a04128040c00003080085903800390040c00004418181003a007000e003051402c0c1c0d8250f58802d1001c5a8070f100344000900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 723734901 1250 723733651 723733669
    0xd020f071409071e120f050103080415050403080309070f12150b010c150507030b04060b0406050c030c0d200307030807080c090312130b030c030103060902042d0515 72
    0x4001c1e55a40907a03120514184c1d000600b100c800c03007102c16504e660000c401d038030002a11910304030903028020224803020000031070300b00380005880e01401700020b000b810401180f81c0c1580748a0300c0c045290035620307114030800b03400698141495400000d001c1006031444811f04016000c581c8068002d02c0695031801c1c0c031003c005601c811201e880d80e42e1100240e0041d20088122a0084c5c3c0451840c148021a04002c02007241c03000c000c28030302546405541454400e8400b42d988000d805440c1ca03040c2402900c2c203400080d41c0da61940310400c05410000c0050240440b02d582540328460002980e011040b40300c107540c824481541c0c010720031040403076403046c10145c01458506118081e074903a003080201501c2241d0500d50144903040006181030038400080804202e101400690303242c41d40c10b804120b100a80e03031000f410368140014030204845a22207030205200400000b13191041d84c00101042056803044010814540c03100540117085008013075200f000c4000d588003461528000071201c01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 723736151 1250 723734901 723734939
    0x1104030c180507020f0c0d1a040b07030c030207150e070f0e092109191a19020d02071a0d0c0215160903031103211e0f0103022205090d020f07 62
    0x1a80300320001060000b01c1d82300c0c5d000c1d8210f10929082c00c0c41d0508283c07980042c02d07034000c4e00107460107500d160224807a1080d511303000e90003100c19118210b1000b002002e0491404000bc2502440c10b00040d00c1c3e207000b03200310052400300d10701c410310b00d8100a80340c00d240010620440405450300151003024000e42159a110b604440100648a8081e4041101c20250b00490138940e4203001d035001d140c2645000e81616021611400c82090348560201e840e54041e4040002680c400c100078440c030081248002940a0455002d5041402584d081701c20f4030109034140c4096084003c2e000000036107100240e9212200c820303a00031003a00500c009040805038400a42000340403d5002d410032001e200301c0303803810308814280320140850030a01e80003440030744281c2c118162998581c601c0b5102171900c50700c995480500c00c01280e20f15028014102a030383c403144d0f0801509520030078180c0c600e20926005042440080c6510054800060320700500310f28a100306a025203002c0003d140302000a1800e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 723737401 1250 723736151 723736159
    0xc030105130b09010b060a020106230d080a0507050d0c0303050f16030209010e090a050f0a06030309090e0c03070f090b090f0105010c0201170c0307091e05041104030c180507020f0c 79
    0x7503403808405401469829445a4069000107514500c7c942c1500f100c001d854901880030804001401c100102059106d202a042070356007445001048001001d407022020307908200b031070070083c0c3e5134080c208041c004100700460240102507040c141e2521400761711101c0400741e209141004840f07002c02c100140501000c06800040707030344103a4440c41000426900103000401c1034180040c2d000c020300400c03136030b400c00c50102c5000140c01c003455000748406c80790152103400c062403c0051142c05880207020342000c5100f1720700c41541075281000500010010744003090491414201c0c40b1040d16078000c2074138802c5106005000942c07820800050444109084c01e0070350340740d14070040e121100d8942541c01920700340010801c400740244010341c4140c030710781d580c024050f4a03900100c1003038458031840502084101414082c83c106a0300980c0c6980e860503025043c5a0760390b4030301403c00090307040352401304024100400c020f4018029145c1101a5002418072480c100c8d41c2e0315a600d55040d03460380310b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 723738651 1250 723737401 723737423
    0x908160e0603010b060f0706110f3a050a0c031103060d14030705030301090c09060f11071a0717090112020702040b040c210501060906210e07080c03010513 68
    0x30664096004001a42c0064035180c0ca8146e10710402216801100c0140c90840c14907980e200c1800100080f030311840301401d102800d054010103184121111013140d5540c07000c04608003240340c4910401e42c41070074840307100480c0d2450b111700000103071444180c00c0401e040c10304a4100c80b490540003560307805602910721041d5201307a82070002c40c500079803c7c440c4c0c0343c2c000040c11006100003c4021070607265100d4042c05414000320088030804118030850340000d00705580d03030071103a01c10320400c5203440c1c0f40412250702d1619141021020310420b10141c0001034001400d0301045610708a01d00b03000560007880c7d0400b01000b00282000c1c001c2140302c080d1550018019003190b465900c80b21654401030000c014003981050058500c018001680078158249099841141e5440c02200c0c144ca18a94800d809685003200507100405041840340c01e1000041500001d105944070340b02142a04038020150304d46010081400e28001d1a00c0c40e001c1d07410320f001c000c180c8a01d1042d120501381c0c44018410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 723739901 1250 723738651 723738661
    0xa1e05190b03370602041203020c0d0b0601110c03010e0a05061003050c011202130f14030a12050c0102041a04062307080a0302070204050f0901060509160e0a0f0b0a0908160e 76
    0x14944100f41c020509407020601050103040c030000c0c0200c06110342c01703c0c0c8205054804000101c01640c600070000300350342c1c0000d856540308088038012246598105c52040c2c10500c0041e0030f54041e02103004140c0d100914860a12600300a1a170300007100300040d0f813180e400c5481301e58071111b07a404082d05010500515140c1d071943c0398100c810303840401548201030781e162882c0e150a042c05128410301034194458030b21140c500499402552940445c45002a0402c2101981d09030840c1010b2040c0d07540c20310001808114407080035040440318045540d4460410310003410800c008500d412082d00b204440c0200710f488001182c030880e41040c0c0441d220450031800310040d00c100b0300025042810b00090100c1000701c40c90031802556880002e01285e5110403d21040c405d02b03c8602901c81041c1114501c114010f40081d8024031001e0f001d511010f880d1400a565811070740d0241400d0380c400038540200e650b0200b0350001820302540a07058012150512a14040241c000c01542004100c0031070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 723741007 1106 723739901 723739993
    0x50a080c03070608180f03071416060e0406082a040c05030406151a070b0109181506080a0f0c0602150a1e05190b03 51
    0x80ba546031000c1180c0100c1d020304039a00341e03c10fa81d4041032a040074000702e1a00340e1a43c0086076030342018a09040f1280d007040d03042e000780d0070140100468401e003031414000c541c3c0529000c1207180c0501c001400500e03495202e4500c5100e81c581c65458004c40100c0b1400e18203801c3d0306c50441c81040010300058660b084680070000e201000090002036817a40410080680071104800d0541c0740c01c0c480740402c100e0700518149890110341a0104034103d4100c42c05402400018841112180c000b500340740c1003004010600307041c042080c0d20081840c3c0c401c1000b0a480b108941404500381000466201c032944103481c2281d04507004600540005101103030060400707200311899850030200001068070030448100e0405100420f58129550301880d07003d868900060140411aa08075400302e80c3e44840c014001e4100c1920024084c051040c01d03509100c0d907445007425a10316401395 = true := by decide +kernel

theorem cover : BRFrame.Cov 723561151 723741007 := by
  have h0 := BRFrame.cov_init 723561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 723561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 723561151 ≤ n) (h2 : n < 723741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
