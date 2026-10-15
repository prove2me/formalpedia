-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:46:31.975132+00:00
-- url     : https://prove2.me/submissions/59fde4bb-f4a7-425a-a3ba-509dd0e7dc86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 918705035 ≤ n < 918884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 918706285 1250 918705035 918705037
    0x305010501050f0f1b06090c04091a1806100f0801180206180d06090b0f01050102030d24090608190c0905092a0a06031b050a170f0f0c 59
    0x3900707010400c28070001001d005110b01419141c40106040c038940005e100044c000086240340b01c241941c445010449090b0b8240220b90180d00309035028070400c5034980c2d40c00c0c030381c3c21002141c61003d1900320005004002404070a100004610261000c6050907499484680024007030510580c1c480d0784c000800c2c83c414403861180300300320030034828000915030801541d64803001c1032100c1d204410707a482c0040d80c0d5410030710394254803403440000c000c011403803c038925810040603501501c64400041215980120442d03804091000b40044d804001d0f0307040b08249194001c2c071b034015900a420104031402107a0003441920705401c00c4546060740300c4514419500b039920014401c82c0000e000f004004202d4000315045110ac005540306c0c0014000e90140c3c0d8a5030f40844010f2002c81001e00a590909d0300d0018060503607454140800c0d035a1244604c06107a42a069004210300099034004641c424030404403034003070f418140a91790420f100c52003110082030f60120202503d4002045400130468 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 918707535 1250 918706285 918706289
    0x20d09080c0d05160b030609010b281106010801020406110a08070b0a270213020a02060115111203070e0a05030d0f05040f180c03180f020a170c10030501 67
    0x600400040c103401d41031000d24040c40d50215458856005030140492400000d58050011000116281e1074100308002c00323500d040c1c0c000007040728108065590401c481c0b074845901c2c4055154100b18415040c1c0031103241584040c0c01109001e61000490000d206400820840e021541c42400b0f401030181044c2e101d12144100800d0880c6c204800c20004020540455004101110003d0440d040c807841c240c0440c82d256928190700100000d1104616025030302d4481040d01e9541142824a5820041c2d07681d901030144485402604d07080d01c1000f03124114680a4250072000c1c1c44110042e0708214095810a0303418501182c0c41c0305842c001400c080c1c40a0f0206d03031004000385111205c40f4400c0d910701e1140c0500608101d4200720128540580d030900c90003c1c05441c41d032840489282c1210000c98030703410040d5080504040c25a4030108e1402c0285048a402c500c00d114548403910005503840c21550014600850142440840140114584e014400705030303007038280303400c1d1000f080b0100c480034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 918708785 1250 918707535 918707549
    0x100b04121505060102030d0522050c280e0c07050a08030f090606060f09011e050a180f170c03010c0f0807030c051608071e02010908030a050415021006030b07020d09 72
    0x21f000c0c01e030504880b43c10590700060800e60750f00c1d03c0c0500b80400c4501c070a004009691340d41c07000b03207424014100103a4118140c10740412504420a0144107001050b4a40c8650f05150000300041903400f00003d0844910647c0310f004c0720754885080c6441080c6800441c3c454003840c0e443d0000503048040455182d00c01e0100414462030000035404103a869040000118100079600c40250641c5041210b003a0655800b0b4a540e926a801140010700c3c41180c02c241082c00501a442000343c1f0158041d00300554090703581031003448003c001c04500d09120720382400c0d4590700b0304044014542d0800540308180e00d01350384107629030382c4101d000c6e0152440e01c6078200010740200300706c1c4c0100840c80c0c8c80031540c80c880d50543e444c1c000d642d1104d10b414be6280405440120720144420119178000c2d0710302c4024017501e006141856840840a4454000d62040444c0303018042c1c03140800600c24400c02417040c50350441040b409490381064004005d007180c0c030801600c280c5003204455401985c9000c00c8691f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 918710035 1250 918708785 918708787
    0x2190c120b09151314011409010f0c0302041211190e0a0b0d020109030318030510050115090b0d0203060d02030a0606030204150e010b0c0a1a1909110405100b0412150506010203 77
    0x10350385d8640c0c400703146000c41115545e0780322003151400040c8000c5018150030390001c00c5010301c104100781180c450266400505204100402c00c07907604032410000c080d0050a00d181502d0030002080b003088405203151100d80c6500d10200e40746180780c8115014155a01c0100b19119100f0280410415600300203800300d00101302c108006403144160410302c210820310111596581e13a10185400070800031041240e498100601004502000900d450b0078281740c002d02203460f28411881a208a940c1200d000da00007000424540303443c0203858141e80d000d0102c0d1a07000b60f40c1005c100601d024002207106500345980c0c850820008405442a15038012489800341d2034040d00b00700ca42e100303400341d039058028080590082619000b100700d40031010681c281542c540300c441c1c24040c518a541441c40d407440c015240703002c554011051114000141e90009003500e078548003800954090b4803005907034100140c04519104980d41501c40c26108150781c00c241d01650000c0c1040da10201c44031801a40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 918711285 1250 918710035 918710071
    0x9040813031419032715020105040b10050a0303110102090d08130e092a120d082a0313050d030b04050604050105030628060605041502070602190c120b0915 68
    0x24201c5c4980141e20001c0742940c00266185030403c21019800304d00740140c0d55a208000500005500c540e03070122006138480011800c00000650917103803404082c0420041d051030b840480320950450710361120061644407001014640622030350300c0f10515000600c020280001c0c8440b01c050f003103000c0e00100002d08030401d601d4a05001d540ca40d01c62501744203007000c0c1c2758611030b19008d07002c1c4200c640100280c413958448000160402e00c1c0039103155526101030a40130b141010720b039034151600880301d51059617a107640c64660318050202001074141e004003d000752100350154015052003600703560a00240d0b9a142c2040308032102441002e4054200400181d510604036028182c000800e16001041d0200030740844100e50140c1c118002240000a050212681ea605542c0038034203240f005040d000c1c00c00324001e441d0441c030003040e24001c8200f5003d1040001c81d400e03d04c0645100700324149096001e00380340c4440f000135136104002d0b004130540c101c1b41c1c4a028580c00d20a0300b044064041100d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 918712535 1250 918711285 918711317
    0x20f0a0203120c030d02040902040302010807050901020a0b04030210061401031514060f190906120c0e131d030d0c050408060606070c05120d030c18050904081303141903 74
    0x1d840030001c00f015001c03c00c943c048840d01440a4806010142d000580b01c80c01d602c00903040400c098801d105000060284105030b0b0303400203080c100341d60701c007070008416291494142d140610f10300c0c1c020801810300170082a8810300c041194419402641c00780f0040c84551b403149004d9a43e402981d03e603000300c107034440150070002d0007007100f5103020b0320152520325211004810141039400d2a0005000c1e080100289980031402054407592500d013000900d0720640068801c9030a81041405900d55030034038004800264003841158802d0f0703225005540c91582c100c2d8595104204041d60765161a40c8200418410030645050710150700051060b0303103451082040d01c1d0006203007222a0440d00e000030480e070710313880c4825410114041c01041d051040c3c01024041d03d0102ea441307010450144c0d805005841d0303a030301c82c03402c5400c141e0b8481e103d81c0300e9040c054410b11500c6d01604c1c03000e40f41040001002540c5000040071800d000c203558030501481070200510000c031401400240032400740300154 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 918713785 1250 918712535 918712537
    0x6040b04053f0c0a0c0312030218010c030e0a08060f090a0503030c0f1903091109160305040f020405180d171f0807121b06080c0a0c0206040e07020f0a020312 69
    0x2540c14951141c00c0c0300300781c1401454007440010846a80e59485e00800170800c048860481c08892410190304040c818104001e500c20654202410002c3c21450364003858011a005204681c4c0038051443e025100d558031507540d001982c0e080c860a0030640001d00d000307030104001081031f5001c0702440c0b6503140d602c0038a4880e003000b2071000340d0b40c2081001220401c22000060341c00c2400d514007081466040c14a61105440da9950034060100741041144182002012181e480b500c8d05002030035803030394201040c10410007a00250094940010f001e000d20342c0180e545424110003044640c0384411a40072100740c0c0c01c0e21204402c00e454400401c1040da40703090041c01140101441c00d403115564120103281c01003951009000c032440743d5820061041051110740c1501091281c040407a02e416001010b1000c0100350030041c0d01c0100316a0812403196444032801900203015940302d40e00c8080d190044542a0b804101503c04c031001c5104421000c20421611a0000c000c0c205a034081d405071811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 918715035 1250 918713785 918713893
    0x3120c030a080c0913060504051803190507151d070501020c01050d0e070e060a09021306030518060108011d0a05061f05090103050102130e04211106040b0405 69
    0x70890041c0b21080c4d941c0c4941560302c03a040f85108020070044d1809060000701c0d00050700e18060050803082000c0b000c68000125620001f07002400d41e1400c0c0100700c1141c2c0c82c0034204000b010300e81d08050240300d10080d03820070040c4801440703401c0590341d190441165242501e01c40c043c050380000d03024102c00c5d0b01800140c22179100d1040f000c40c0c0400c1c0d0f03606050409800d80c2015003090a01c2007800031030701b4145450805800880006c52600054903411003a4040c0c500c03c20f400c1645401c0000c82e5a54440c1c200c002c00d0514508030713a40c80d41c440850720f010340383c664001129a40d410004045048001800549260b000405000a5114030210580e0318104051008450742d0300d94001940703440d1414014000c60240000580351034051a562800803032681c040030408811005000200c0d001e41c605114281c01e8690114440c0c034102c009032844400094082c0b0b9602070b04042006104040c000240b20314481c40a680e820322110000002c40b8a100302e560102541e0150400036007010803a0b0015 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 918716285 1250 918715035 918715051
    0xf080a0605130f03110f0109080306060c0f030301030b221a0c09030d05041a040510030b01020a06290604060e131b020d03050f1608070e04050a0b03120c030a08 70
    0x889110183c84200320f0154001e401c90005150340011900c0c41d0003800789a41111001d0002c2c008002c041e01c0b00c0f1030600001c0d22592080f0350000e500421400d04020141c511000f800c280c0c0d84a680d24200b001c4642000c13103d200081416a1515003504c02031400c2010040d44400300b801e201480341920b1940d080020b16a8441d40410800781ca181c0e6010845008440e00ca540c406907200c0c1440c03604400b60308031040c3c103800a17a05200c280413079510b0481a8040102516000a11010b980c004074034140300c02d00c0c05400f207480e016034803010000c90307461080903240c0740c080004c50700070b444180601d511540c400c0400080381c000c442c40d52440c0004406443e4040c04402040c031034180758903403881101d0131201c0405a8407911084510907094081d142d4071000080c081a29403400240080400a9583c174500810400300b00044000b43004404003a81210050000c00c00c600d85200c0c2e1600908100113003c3c824440c01ea50b00f9210600c00045a000c040030402450401c810200e082c1c0b071003000030709110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 918717535 1250 918716285 918716311
    0xf03020a091202042018060909070c0507031b0311010f020c040b030a050102030f07080f0603070b0a02101e06051e0f06040305030c10140402030d141c0905070f080a0605 74
    0x241e200070400045c1d41d0742c0c03049000a07980f20400c88400034441e000c078000030b000711800e1113030400996802c1003199000c3c405040822925000d481c261303041007499000100382c05d01b08100003015502030124041600d124005200f031384100da03001514211803011000005910075004c491203800c041d0412000c5000160898040e01c01c1c80d5600c40c20390308211800e89000030038004010380c51398069003158010009100c012118102322001c01d0711040280070700b43c117198002442e0308040340b0030801d1844414802a04001d003201f12744e1100c001034043c030a090116400d08002080324500100d042c40c028041a0500400c0500403080c00b6540c0316642c000e42c0d00c070400340400800704400740020314985c040c0c070003e4010891507498500031242009540207110b0302d1030b010080141c4002401041c10030f040c0c02d00740c0301c02c045250a00c240e80b04401a091122503030202031045240d4a800910b4424071441c01d80d00c8140d00c03005002501007581c800c12a140e03100b1010030f400300b016940080d0300054035034104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 918718785 1250 918717535 918717551
    0x9020316030e0c04180303270215070b090c01140412140106030b0709081c02030702010e040b060c07081905070e0c0412300518030a0f0b070f03020a09120204 69
    0x60111140003105d8107107030f60280b05180800d54184a48041d11710a040c040d00c0740020300107031500886c102d40c0024092201c83c41d142c21045a0b8002b502e0304564840700f25405440c02d106801e4807800090040b80c045a400b00b5071520078004807007580c059820240c1401740e1003425841d82c8010725007032507500c40b455580f18004008103003890000d5108498a4646000c0b8504d4802d0301c510700020404c206510518003038070044110740c0441111421502440c00c0c0c00611030140014009200c031402e110360000f00018041c20b007800109400e400c8828200545802c24510410411a40c29401004111360400182841901d680d0010160000d48500780356080c5a1100c051070340440c070f05201a00d4020082c01d0000300c52506c4401200a810400c1c0d03038402c16401840301030110b00030501481808400b8900e5002c2c0c0c1d85040040300c142c42e4001c4410f83e0000b10b28100240050010707610040003403010f04403501498041e008072400390079641c0c3d5801100b85011075085240301094012a401610380c208 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 918720035 1250 918718785 918718789
    0x201120e01020a0f09060509010c060203040c05120109030201180503030711030f070c0801200912100504210206040c142e2d03020c03130303170109020316030e0c 71
    0x9006003002541380c48210804414029244d00c060f540800c007000310403c005422a64022450b84215510610144c0c4a440d40e00d0103102c0506550800340e0008040c90420381202c505403c02d0104501a800812000b044e500c0e55480125440001a00e29031040022807842031144086055820944007628100102011a54001e2780942c40c1074804400c880018400340600784101c480d011805651190340c00c40e40786035110300b03001d40c851592254040c010313045400d0b042070200c140000c0d100c00003006641f40615101854840e2164030311940d242c455640c0001341c0c00025400d0180f074024480079a603034907000303103010f800798003401050b000b8410800391100c62010351400005198030310307000a100c4007028030082c03a1302006404000f0440d05140c4002603a1032440003203010034041c1c6005a51380c9468100980ba500c0381500755082c41802c90317000003d055101c2d104040f11510400340c0025642d0780c5003032500b85d0105441101c0303015001200000741601030351181c0c7c400c5003888103460104100d540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 918721285 1250 918720035 918720037
    0x703020708071212021b060a030e030318213403090602010b03031c02030c041205011b030b1003091106040902220e070f091a0919120201120e0102 64
    0xc0490402c0b004a503984080180c0324242c0071000400340f009000f81b402c1c40c80042c10458042e900d0364003441002642d4245180701c2c0e003040312449000c400301c076602d0900c4d600b0510018610101d181c1c5901030b05c0355140c1000402c140220031500308490030740c10100c0c3c0100c0c120000381e1004911007130354181c00342034041d4040c114403450105e009841e0800c543e440c0c01c6002e401d5503000100c45200e504204141400030701d5006c0f1350301480d0103681c001622540d41c103c10114510464202d00501807159607a1300c1000015042106c074228601400400c600301490150706448502d02e007150b0091340c19408029080c031a5121229241c0148102e03100480305601180700e650041d0448020283c000030700e0650b600c10440143d0038840c00c3c8600422407032906241240100e0064118804c00c440105d0503500184551400005001041711100e65051041e003884241c1d484035041c1800f50b108201466410000d0800d2641180da020380d035144042c02603401114029000300c2152101580c0f6401c104642c1c400344 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 918722535 1250 918721285 918721289
    0x220207200301050a0501080a0b0408090301051612051306091505150306090d0804080a1823151801050c010606020124030515070c020409051e070b0301030206070302070807 75
    0xa00200031000030300181402e40314000e22100c42241400c004125181e0000342e4401402d801504030f13807aa0700c82e071a002000f889144401d99056090005211803c9500754001040c214151149400b1120b6029204192a4200c0303241ca00740700b0b086003400200c0c3c0590020709410784521104498440035407610340031140b0580b03e0480000f1340c644c401e00981010806960803062100040440d41102c21006040c8000100001c140c00341c0850494040c0d0300414060791005145159801816110030168007110305500c00c00b0700c0010207250210f600d0610310354a1005105480480b464031118004507207000241c0c4e0501410803c042209420004088c07245074040c1500c0e0380042000e2200c2d08014550384405080041481c410480c1000041d4000a0021041c43d503c8043d90041d80d81900c1921540e207030100107504282010328000030008041040c2e0b05590013080040001d9500041c003e9845119002d0394082403000c10040c005807030110090103040b807007031048400c540c0d00c5821082c01c040360340e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 918723785 1250 918722535 918722573
    0x22d011a0a0602010b1e03070b0d0207060f022a1504051b010807080412120c0f02120a051804060803040b040e06010509010c1401200301051305010302220207 69
    0x4484040c200d103881c85041000740301520080c000e400c0c1c460001044c0d40c60f1000d0703905010412921142c110740b400d0164030f004000c0102c000e07498010320703160100690704c20001120304500e041c0302c911400b843da2083d20607204000811070503180c03060101c005108000a0300010781d00c00e0b00700052442c80d40100c2148102d1091000d0719a20703032406041d61641121850b01818041c0c40c43c10401e802d5071000b0381c7c83c0d210340c200201c0200305d410312000342e03811010004c03154541410151800300d82d40d0000e0050700d003030341c859080b24002085c07003220341500d02035211010005941081001980034030803488400207000100000354150b920450030b0b186910039803222020340b001160400c1035244402d101e82c1e01203028205a45005d41800008101002c0c042c030040c12280c840b400f01009041c00d50000741c01c4070041c21964000c45544000d4030b0503070800d01c126885074030341021042240c1c800d4021141203d0340a081d10001c000d5506039614a92044d2586c9103040b6824040c4801040440b03050706070000390 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 918725035 1250 918723785 918723821
    0x4060f1803030915020c150708010b03130c0b0307080f10060207290c0607030f02040f0608180303100302130603030f1d063606041203021606052701022d01 68
    0x2109040c0187c1d007800030803101c00d100d281001040904801400c813940200840014101e14441b45016000804282c00c6903203c800080200280c540e002080c03680a008840307000f001c0c0e03940b0081180c00f0030859004a10042e00410001c01540b9103a003560440031b004543c0d240c0001d04c04081c494410380201c0002d80d890340c4004140035060790180b254128a20910509502d400d04203c2d80c05080e203640c1c41240300300010200080d0905c845078074040d01540080d41920b80ea400c00c458801d94600a60005a215070400c00d40071001034814462541140c0c0d040c4c40f81c00c907400401100751a1044000c1540030301e41490000003074580d480f01c4c014036030340d1580070b0f02c0c103e1107018400100d000c81e1030018080c00b580c070300c40003100103640d41030998080b0b450030036800120844600e0124144060410101a04214100c01183c019003007006001003080944030002c0013008107600d0200c050815403114090f801035050340c0d01003d01e5940319030b091280d40354052803004d00310704214215869102980a0160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 918726285 1250 918725035 918725053
    0x6030f010f09050106051611131e051e04020a080f1e0a0c031106070204020c06160c170a0302120f0106020c2b11060c0604060f1803030915020c 63
    0x3201c9070903480a0051000e080001c1d6041c8280170b4828414083c1003910f1044180320308040042040c1203c00124005d00400c4120301c1410f02d00c00542481090801e0010b55420340503d0107119119440c401e41001d02c00c04140c035403c1030228100c003800b90040e40c1147c2203c0c804100c00340100900310305450408000d003014002d10b23040007000d00402507000215046500240d0104a4182c07a600580e50071612802c00d4040c1400013949500c50420029006400030401440f001c0f0702007405442809401d50ba0b41f81520300b803504880e464941e0400030039188414054101e014205400f0b0726051120f41001481c000c405625030405010854201c0c6050000100601c40a903040c4011043c2d424150380c2521003181c902c104020300a00b44040b9420180610881030a000c1c0c2c0c0c00070f00040700c0025000c103075503003010b0134800c1c0c0b5800201d0713068541906041600107000e20350301c51580f0b0142c984107102d42c0c07460140d600f1005082a41c2c020f0701e0001c41841e28004400307142c07000f40450000030004041440b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 918727535 1250 918726285 918726299
    0x4030308010b0405300a03170601030219080403021f15050303190309051204060c060506090f0103060902030c0a0605210105030a170c06040b0f131709010201090206030f01 75
    0x100c0c160000c07050060107000030081a01c0c0c02140e9000350b01c0c4a030321404d49080580b01e080c508080e1000c2c00100380f007022881024136800803d01c406103110030701841e9031543c6d81030041d01a84602c0d401c10383d051342c2e4604151420351003405841c0d009442403043d00c04199450220301e002d05031040f15141c0107961001c41c08401c11440d49503400034541a0081c41c20300100700018a20904292405010301d502c0d0460710080100501560f548945104865912203484450040011800b004110383d00c51600000c1140c40ca00032107150302c21070b000861420035030300303550701c0d80f02074640604200c0e0103229034601503015544030340c0107401811306542e5040e10390111400d4481c0303501070205002e00c00c0e448000141b0840d00c1c0403504c2d00900c3e4224828900161503800282003d00c104130780c030541402000d060004210500343c0c050301880b84c010281e00980c6400c0406070540750f06181c020414202e004109900c06803c001401c1200c40c1400000b07150301d8150045042c1e07a00484406010780c1e40600107100300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 918728785 1250 918727535 918727547
    0x3040f0e010527060f01050f04170d030603020a050f2e020d030603020a1a0d110a031406030705270103080c0105090d0507020d06060503030d14070f0801170f030f040303 74
    0x50440042e03e02415800355050710340c0002901850040b00ca60f04264943c4c2d000f0011244211098241c0c40d40d1240d40e122904401d01000404c0d5681e4042c00c1d00d03405010b4032038043d4005076a0003c05401c021480c0c54104801c24800304007031504941000d07011400e203c2d0a1816482600c0c5d00c800d98800701d0f80d409802800e01200044480515141500500c0503850f8400c8900984d222190790345201500e90900010f10301641510396884c509151360300d000b00d00c803100506944001794505001c804107040040350750390b0045615542540c8090020840c9203001d00030210320b44011845012a44618020340500718000d030001c1e45c09840008003000024800d00c43e403948074202c00d014240d49844104001c00500c101d81000e1304c103003206c50603042031116507400f03070000300401801c69503611007442c1d1140290142c0d4081c100162040c0c0006601140551000c44030441c140d41ea42c2d51aa00345600480c007400000a02e14991280c4640030428181c04c0008210081e50b560381c0c6601c40c2d1440c80c2c01004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 918730035 1250 918728785 918728809
    0x605010f0e1302041415030606100f0305250c15021c0e07091d0f060910020d180804080d0302091e04110f04031a040218070203040f0e0105 61
    0x5020028040120148020701160840900040d55801c19810300024000d0903152005840400e040801e015075640840c0030300c1402c4900b941910300503030301d0130104021000c0354049000410034090002d102c1c640f00e0344c4480d5100c1c2035150707c624070300950041d882d101d00e14150780300c01050b803911207034007800102c40b001903518061040c2945421070341507100c5600701ca03098845959070703241c41000d0f022140030b0010002820190b941040001c1d040b18002d1807103180611000074038014603060000180010604c94403030340480c0c0007000703514107100039107000790702229150280c07991384c6c4400042425260348840007903004100090303c450a08030003a0034641d2105030380040c503104200109581d1204c03c2c0c0b4040038071100da86445805e8030a400320b03003d40005500104c20840000e016000001490f001d0300c15207000725880b602d0340c1c0422601c0b0005800544019601c088040155004600341100c403a6010403e44140ca08255460840060120441d009001c04041c090014000c03400e1420390010303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 918731285 1250 918730035 918730049
    0x50f010e011b060f1e061a0f04030b1314060f13240603020109060c050a060b04020705010606050a030b04060509010308031f030606150201150e09010b060d0c0306080a05030d0209040605120703060501 87
    0x1a1b1441e001040300e0781c0c0c044e036403101584a400b00e510b2240c0700006054400842c0c0080300d001162511080c5075400c800000310072034980c00010030400c1906c0e4002044c1c2d10a0000b800080025103602070701d05244a01d0b950204c0b0403108102500181c030080488809224902001c0820007606520001d0404001900000d003001010145035020171400101203401329000080010390084040201c0c01038401e405000e4415030130302c3e00000f15990300100520707001509540400040400b4410401507403244d10555500015030401480403034081070003507070007000e08480452080d10743c1c103000703000340200c2d03005980743c1d56074190401511100e082028109a401e10003001909090b10001d803002e60b181c0550941e03010310700005584920300b50b01c205541c88008240949a5100d07100c100090f041c0c21040900107030601000151100d4002000000e490b44403000c0c2d400c2080b2100d8020003900240841031380240c0340d0000007095101c144000300200f41a4018055150441c200034045d60f01c1a8015030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 918732535 1250 918731285 918731291
    0x6020708240705090603040b0a1805060c0a0c0b040503030a1b021903690e130e0f0708120c030405090903040807050f010e011b060f1e 59
    0x448020112101203401d01c0080840d1440c0d072103400c0200c5160044004603904400000103000c140710750700c80091310030078070000c0600620803906603da64240c00303403500400e81c3c6d2080b400b0802d400160400381148040328942074000d078501703440306408140c054905031003d40000041c8519240075000c0d000d80468041031080b2900b104000082d980c0c00600c201552043c0b1302e1004200f0180304010340710380a480348000ca00303440c1c424031019071804c1c1a5000d4041c416034007000c0e04803002c00d88003170302421002e240c45031000d0003a0801d070a21400f401d0110340100482003038103202555454004454440c1c028900056141d1126512480e000a54689a603282d00c5a0410441d42c180092503241800a0b10443c680307400000c1c8265140d8040c54001c16480300048003009480b10000000d002101c001e80101d0381c0d0315039544180311004009003030850010304103115102165014845403000148043e0070080e0011541e20741e98121400008101e183c90b441d074541c0c18252013802840c140b82c040d035042c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 918733785 1250 918732535 918732553
    0x20d0921030c170604110d061d040c05060c1f090b0f040c0b0d020d110918010605090f0f03010f0b36060a031703040b01060e0d0b06120307060606020708 67
    0x241c032000c3c06904031004204440002052915580c1040004e103266041c0706450362003102e0003c001d0462400b59160010788000c0e603880400c100741080e405960400c240c40c4d0313594100806c0c40031a90003105410504d01c5203881d00350307108002c0301001d100d44036a5038001606509515000304007017005000744d081d000c0c079002840003095604044000303e620361807401c4d5a8000106407a40030b40283c4081045051800c8400035085c140e420040090342800c460401904103010703a080d08400082c040c0c0800920140106049402e10010826138000010900413014a600000070b0968111803000b079860360700c66020850b03e0030b01800180c1310901c1c040005600c003541298592060600403584d507440b41c0d602022032110f85a110414014541280304000d40112004069616034410707102200e42402005c00015078510400c44015000f00040c10b402401c0103075290f2084044000d0411a4450f0202c1c4100d1003182d000c00c020520340c2e00c54900401c2c01441c1a1010741840b446910031030280c2c0089040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 918735035 1250 918733785 918733787
    0x6010c0f3206041a06040e010e0a0218070e0d0201030219090f1205030d0504030306031e03090504090f1709060c010b031041040b090606040c170406020d0921030c 71
    0x680344d540c06036548216116901c401c0094082c01d01c04403820384035440d1020b0b061800702c0c04101c140f0030b1802911009111201c0325101e00329984110744050009a880c0f03c00c0240746080c015008049005140c00f50500d442410804103240c42881c0b100003080e9108020800d10440861b02c00062031200e894a5520b902611aa0707142d200707a41040040d20313683d0000608250103940b00101458000d0b01b5000c204500c000c958104002c01c00e402c0c1c0202d070314107800050628280c00340d150002d90044080362490800d544600440c80300e4800b9009000c8244064070303807a158000031345603000241c070000c00e806001c0c806040c140311500d2444484142402c003680c0800000011960210120f036600d810414a260100400542c00100c20300b1019480f1b0140010f204051540c1d038021940380c016168251581e40400040383c540b0103101c0041850500720501c0d0081520850f940980142c40152030500103d6003c8204e80c00903408480328181c080803041c00010f650403c1e01341c0d000ca410204000000440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 918736285 1250 918735035 918735053
    0x240503070f0e0618010b1c11070212070b0f21070e0904030519050a03181211010f061707140a0b0702010e0409050d2606010c0f320604 59
    0x91550b98840300740410020345074162020b8580420541810180d40c484a8000e03442d8807030380c8010b4480d070389010724904241051207103640e60000007002520700b814030b609100350b1882e020501e840d01d01a1650015038a1a048010810189a501c102c1d070341c0c154400d0542034010580d4141d2032105840001c201e00c00360000c0d0300d003101c4401106c00e01c0880c0c1d81c43c94212942c1c0b240002c0e80c0b4a1100c0710740003d0100360894041c080640c03107510148a06070030380507012aa42d4000c100070300000880510b0150782809024211b13020540400040345500e0b05a207113a0580c0d246e940b001c01e84070030410600e0100c071810300810029000040403c0c402680000029100c03444e00c1c041d202030148005501c40c210ba0141c0c82080034204054010300c10800309040854407003100a60040c00700d00810201105400700400301e40036003909102100d00c40d21006d00458504040a1040320444020840c201c04522000c2e031803621601d000c5003c00b802051490030424860b040a40d962060340258140000284884 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 918737535 1250 918736285 918736289
    0x1820130b1c02060c0706120501170a02060c011404050304030c0506041409190f0c02010f02090d0b060d05030f0a020106050105210c041a030603010c020303040c031b09240503070f 78
    0x3036501c00c10115400050481d2040c0480600039120b1a40c1c00141c0383d422450003d205802550300300b0482e030362171480283d502c0c1058652115a040103600c00010725148001d089581c0440000090b440d402450924071084161015a5103900c0407808004000410021001a000c180c0d8010305040c9040c007042d0901c4100c0e22158131078041c000001d0035205941d080c070020020b642000340941503460030031200504180440798019400d2140c1c40407074480f01d000701c035034111000d0011142c201d40e0751110003004401030b01c9580d0041e050381d000d6006c12020400303007050003c0880b0295507002d01e590007070b003114025071000b81840f109000e400e070010130048800c403001d0448000e881c6e00d541c40c604002d00912454002d444170440c2c6981541c0100c0340d440145108107016070081100f1416204140c0c1d80e404111002407000c846140c0c01e100052400260000c0019164040300441d901da98000c401c0c1d800882482c0c0300034001c01140d24040c0d2000c18048001c25040d009080c019080c580c1010301401d0754 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 918738785 1250 918737535 918737569
    0x20a0603050c1204030c152c010603050a120305010503070b0421120504060e0d1101120b06190f0c0512070c03020a0f05090f010f03061820130b 63
    0x1d4000900800d40040c21a80ca0701d03190091106540361a10380036103000303510142900c481071012522890100988900c0031690540809844002c0400c2d644140c0c0f02103910b1000015504c4050000005004100540c407403442448010b021030503c8400400700d400580c801803103548007450800c401e80c909412541903499420b0084d816401421001d10b40440c004d200400c1984540c5000030704035803100c05441030310f4440d40d55010742d54016041200031a070550380942110b40800c16a2039540c0542e8075015111039500001c01d4543c82400020816007210860800101170700b01300c080b2155208094100c54425401e0500c08441c3c69220541c1c1c0b41c0340510482e8096000041d804e09020b04481d0030300c01903900400a01e000350b10740349901000e0b4100d00c2504d01500c1c107507000c220341c800032407107090580b069900074400c09495a01e8401c0903008400481c00d41840c0c02c00368501144d00c2020000b003c0706c0c4200c500800c01980c00511001d60741c01651020090310f443c3c5007a4840d603c1d80c440d501035082c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 918740035 1250 918738785 918738791
    0x224120f06063a061511030f22080705120f060103110a03020d060b0405070906020c0405040602040305100c0206152211030a0e16120605040c05120c0418020a0603 71
    0x4490b140101c04003264143ca1903c924248005901e240d582080c8113942c500680300c440000241000c0d2040c20603540700304601d410070700030641140f103a000076040390508456030703520366035041c98a002e40e201182c0082006410404041c801403e00c6003184092201c00001481140c5440e146a030700d41d001800000e1411400040c102c0e625900c0c1c3d1b900b40c018503001030140c0040b070a946019001406060300ca0b0b4020707420031000828940c002d0032141d08807403841c2c026006001018040100408ac002c3c011510607600303220200c0414403c201d0341c1e070a42a040d40000302103680210103450710344010860a030390000801000c480d07440b8101031014411019070503603e0b81d9072200041c0060902841400d109a078040104444101d05801000c280c0e010442a10003001c40c52909508101c3d941c058081c10481180328500003034065800240c1c0239002d81c023588030f40c980721400a440c01d00c103039002020300d0f4443c0044540c0b610b003600c0b44101c481d0703416211a10f00f46040e030100b40a80c1c9036100d00018955 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 918741285 1250 918740035 918740077
    0x71d070519050903030d060f0503033a14091005190b061b070608010e010e0f04020d020415050a0f0509040f080d1d011b1b0224120f0606 60
    0x2020b401503a04540004003926104c211140d092401072607a0710901110000c1c20340c0008941c103000c03044940702100c12490340c45259086686c0e564031100340d030303950020101c45200030440000b1842a0304448140420100d03460826040091801e2415452000041c2c0341c40300f80100c0b0b0324030540724440c4004400d0701140b0203040d440095064001c0d200e040000aa100d99012400800400d92809907a003948810320682d1300c0d0781940304000002d020341291844003c005c20300b04440c501e0810f82c13040c4010800e040c0b0001d039a010170203031406040944448110407030240824030f09000b8080140c40940c1100e44400d182800040e0b408a0143c0094007800200407510207000100e812200c4040d920074050026082e0191342c0700811100e5900300005502e459210240803940040721100c0c440c2540c1d400714165003c0c85008910841880102e138840c00301d4090401e41540c503568010340343d0000507065203035400480f40c0100194010718113003030468030703004021096503900705580d2902404c00c90101555 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 918742535 1250 918741285 918741287
    0x140706120f110d020301051003091a131703060f0319080306060d0504110103050f070207140d0501050a0f1103040f0618140606030c1206040b0702070b0c071d070519 72
    0x841e80d07400284802c0e20004000354548860780056048500a0700c5140c02081c4034901102120070014000700002d10f44e048100046404400ca03681009105c03121001403242e5a888080a070385880c000003c410300441001003910785940c1c0f08079040c1e0184d000d0548207030602d00325054009000c4000304503442c0400400d0440c1c9130902a60709088000c0c004010504050601080141210b641e80340004c2c01c002c0080d524104413072500f402584240c00514a150034400c480e5014180c1360005600001c201c42c2c1d038030109a0074021280621408ae030b00040c0003d64440803000c2c0d581e09808200052400c0003400002001d2b0304d051000150040740014a072100300009601030901100050224201d4185001e038018000c03070014001c017412002c80e0021785040085c0aa504842c000d41d68041e040b11002902003030140d04805c0d030005807881942c1c072050300c590602d4225045240c003c01c80b0b6100403400d02174802c1000003100f002604200d07060341c92814400007025403050b44819000f03003001c40001c030946 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 918743785 1250 918742535 918742541
    0x120a1112151017071505070209071101020d0204030f0b0c070305251202010209130b0d020103090c030605180d090b04030f05071503140c030c2a030301060c140706120f 73
    0x24060394100740f800c000380030500ea03603204401d01500c0c0d4040e100362409491640900111034203a6400741c101c01d540c1e61411400d0311411051001021070795000c200c0f2510a00d150701c010000345201c2c031620100030040e820544240c1c1070042c00c00b2010a400c10035480482e81020550325030405a01c9903152801e0450080703141003044990041c45048100f00d822149501034002c1c014102c81680d1208400354010110419903040e02580b540000a1601d42c80140d4402c0e009914094000c0c600000079503a07a903a540d046660032102d2075a070588404921500c10400c1c00603114520394ad117001c606560420b45d00390450303c0b0b0b0344000bd141041d211940800c203d4140410402455920130443c9221400f1f40042c014101000100000e0003c4a000907081803003941a2030080c0003c0c40701e07d06105004003111250962503800c40c9035140c055003800507200b010401180a4040740c1d40310890f0b0032039481d000c038000d8080030103c2d10350b82001074180029544454010710b5600100b001103004c803050844503000f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 918745035 1250 918743785 918743789
    0x303030f040f050d05091f1e0504033503040201080c030910110a02070b0715052203030f0e060403080703021e0d0917030c0405100e120a11121510 64
    0x14002c04c00b000681c5608000501050342d401e9841c0c220700300780095600e0170040d403402c4401c040340844020000040f45c1440009246d42c1a04000340b40580700c1c1c40b1034020740604101e0740002e5111518070401c0d04400c1072024500c00d8204806419030901d030380040c1c000c1e00020007280001c1408000204e0f20701003006403610041802c04104080840c0023000c050941c01140b140c0e015201e00c08000905584140403107403881e80205515004015082014000d0000900355070401c00d02a03039012410a44444401e1840340300345ca00280f02040506410156481c580004071150080d40c10040465000305000f6448030b0340386001a40d6080c10841c1951600030400d81e2040c84001044c100b0400c0d03603030f6101080b80c81c05401122000d055082688680c0d00c000c40e50300203401020302040000307040041d03280704c00f4006030800c03040c502900000b140c510040c0714042800780e401002a0014014818008143d00c2020b0300c01010501c1d04820035660303a42c00c1e103140d115070301c51140050608808161a540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 918746285 1250 918745035 918745043
    0x14090f0708092a18150105031e090a020f0a031505060f1005071703040812071107062d0f0315030209040b15090c220803030c03090d180e06130e01091505060303030f040f 74
    0x9c45007000e4402a41d11810f100c000c034005e04000301c85d000380740b0b8030038845012070794402d00e54480c00b481e94844601901c00a8440b903004034012007100050394401100201c801c8480d036515841b144c842c00c00350704940c460401d003031007030b4000c0050002084a00701110380703c04105098800f1900d410b0000c0b9071000c2c004034080e0f02409504000701d2026442540c0301c078409282d0302c2603040350401c800041140c901080751540030440c00300d0791409282c020303041a11110020102070110583d2a0040303503000c24100c8085803481e00c00300800040901c0718041440b048421740301c1224610306506416098130440d1300d2101000e542c1c0340920300e1500c09550700b502409111050701e1303ca08200042c501c0913001a100c106540c01900c2540c58014440c4254022103521070318504d411600d0181c2d1402080d00c05081c4030f030460f8001c12800d0080c400ca0007440c0c1003150000000501f0320207070400e604011841e9100b81052330800d02804002d6400205076a080810424410401e849501d03008405030100c000040c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 918747535 1250 918746285 918746341
    0x127030c08070501030f020a2715050703020d020105150111010b0d1101080a0b030303180f0109111e1e1f0914090f0708092a1815010503 60
    0x1180c040e5002c2412000c507802a2401c4c8040f1036211072240c00c1c2c3c06410340e81d0300020b400a1682001c441d076614204050040c140342040c586840313280c0c41a0780043d2017407c00c0411030004800c4201a41007000420303a90051000f0456402d003042c00c05201d003a88110507041088401031090307020020f52007122504001001625000d00c940303884140150303142c404c81e000c24405000100c1110307190042c0c8a42c010010091032459494408501d02e002040d1442d0307403e403041701701c0d0a030300030024403506d250a030180ca16100580c14140c100545101c150094102e0300c00b010340e80301b4480d02d4004041c00880b8041e00b01480146c60007001c40d42645000034080700c0a0206452656683c1d01f0001603416a120303554559044c801e84410310070034403015603448180303100c22000505400d104996940d040752070071003560300000545114042941000c005032811020f4800e103010303203240083c42d80641c2c64070000992107500d003403500d192402d01d03190b0340305050020000001c4d803c800041118030b079071903803401e2032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 918748785 1250 918747535 918747539
    0x3020d051e0906100504020307030f09030e1e0108010b09060c070303180902030402030604060b0a081509010f050106020d1110090506070f110709200406050d0513020127030c 76
    0x40d2074088400c0d80162007901c034480108407041e0b404940284501680c82c0e00c030a0301c2d031404003840001d50000788030000305079503070300b5110044a02d80210150715010f9514803110140308020414080c1042030a000c0900c1d4000c4040b0301da90f00010464115400010030390b8a60031aa800700e105032090706004410380c0680c03507000c020190000704c002848042d40b40c62482054540c113850f0708078030064078040d5055000000040010703510350094200c28501801030390509a440304042d2805500c1c0c12002c220900003010096408030905c20300c03ea0586a100910165140c14000781d21080c6030340c20310003008140885203403030031410040160304480d1190f04115458540c10010740724030301520003400050120462940f058030a015000f50742014074080d0050a10340612007000345401c80103000c0f02c501c2c1b03e55004941031010040c000400c0f080e192565507825881011040303da0042a02800070207500b204005031364840445580d00150079a65040c2e80d444181142c101c038100c2d030005040c04c41003640 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 918750035 1250 918748785 918748801
    0x2060705070b0a051c0203150d0507031502090f100905131806240e0604020a02070e0403051b0a05030d0b0111011505040f060b070f02120f0d0905040203190c03020d05 73
    0x2040086000409844017944007003009044e84000e9803102c1c1f1404c0940b01c581501d1600301c030203403a494030603022111510b0392075481c030a601c03804010501c0103550105025290f401d000e01e500240046c2110300f100b4011300c01001403c9020300f070180c28001c0804131407005c0c3c0c503103c41d0f201109484915540190700c0d1002e1400700c028100c0079020700c801c24810000e0780c841c28800c03540002503c1c84903080c41c095644940500000b5001000b246003103100b844000a4050355403c542c1c0d018130300940d01c45a981c10a8108440d01802286141070164401d002c1c08004c01c0b07011098503103005124002240b9840002c0040b10816101d040512955180c8110341081e04000108201218000d40e801d012450f005503e143c2246d4240c45003500282082000340001120240100b0005100030001c00c1d8880880e07404910300455200c0d42c61280e400341050a040c1c3d500051940020442110f0543c51442c02031181025800b0410041c5211911210680c0c0c50a000c0d405a1f9003500c01c4000411003441d140710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 918751285 1250 918750035 918750037
    0x9031c20071a120c0904060801051501050a03060f0f0e0709030503070f1a070314092a041e06140d0809010305220804140d0b0403080a020d0204080109050c0406060c02060705070b0a05 80
    0x1782c0742e20a030700e0b000c0d00090280060080701d100d1254240b501c0014420300005640701e43c08008503204040e41c501001c9290380c284140070317016144500003a07640303a040c8603c80b071054202600364024400d00a10400008400104a07060760360b00c81456009540c1911b48040420119420b840d9101003803020022207640c03560246030820b44c0070795a024a510380703512050315940200150800160700000c1d04449903410440d09400301c402500024901001d10621801c865401c421840000d4845c1810007410a250500030791100007216031402141d0036a42d19210341c4501e0030245d061648900000d581441c90060060300c0005040c0c8049600983d8a020790056115024801000d5101c60b0031440500700840d40b4003070580d00051180303a503200c6403422360740440300070290402c15400300002002c030070302400500000e000f50000402e03e25018a04181000385024070580681d141c034604210043d4016001070311180c054944a40c0c445050519134104075454000f044178030703030000d8011441580704c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 918752535 1250 918751285 918751297
    0x60608030c0706030e190503041a07060b0f1806010e062d0a140c191a0601230d0209030d0801080f0a050c010e010509031c20071a120c 59
    0x16082d00c1525441e54010703070856958070101c01c4d03554480558000701d10300b01d00b80e06150901420841e400d06030758220026521034040c103026036214021804100300880780c0102d44c0d10031011a400c40b420500131001c00c0b0404010310071900d10324042030101d6056401140a040406c5002c1d040c50780c1c81080681d00c0d6240b0171045502043c0c50900000215020811015105d64904641d290301041916820b051810b4004400c0845070f40580c0c0b009010402c00e00c01e60001551040740480100c10082e5101c82240500030411814005903e2198100100d5001d80c101241128141540c89000c0306824034024081d0402994051140c2c1c041c3c6040d554200344140d041368115070840d4a920300c0f0070031168544403240e400608590000454541560190038441d140c418185080c030b0801d0b840400080c6030803d1820103031018012034030030750040f0394048ca80c034500c1c005044a00368044050080c05030b03a0403051040c80c40c3c080550404d003544101001c1292a00000010340042d5030400034441c04d1564016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 918753785 1250 918752535 918752557
    0x100305090c01081504150b0a02060f0a02090132030c1e0c030306091e07030509010b010e0f040c0e210c0117070e0102010e0f1b01020102071e050a06060803 68
    0x11a00e01e10056100e014210300c200f4035180341602c01030580c814080500a5540180251284c000d004160300e00c00e840a00a440b11a5006010505000300518100400940483c0210f030042100d50610398002c06d0141c041034200071694140c031121681841c04101c1d01c00f803140c4851001007441541003108002d0440b400c600300c80c5156409240046406c10304c5019812a0741e40c000344005580d501c0c103001019841040407001289040100c403c0c541c01c07030001c444220100f46e944040c052100d0092248180030582800c0c2004a5942080040c092007010402c0610450721144c0d0040742c2071050007003d44682019190314040720700849a40200901307101305003881d1040200e0485150710469901c01c100040c40b04409140d100c80e00111410741040c01c0641c155903c2d00c0c0d000c5034046040000c1d8036580318001c0540000c01c000b820700c404444180404c40c0c1160b0060003488042403000c43e482e010040d070032180f000304891070f15005040a102c0880501070380d02c1d054001a5007400031004160000f94 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 918755035 1250 918753785 918753793
    0x1803031401060e0d060504020301110a05220506070b06060c15040b0f01030c06081312090302011205010308040e0a09080d061e03210909050414070602011407050706090210030509 78
    0x200c0b442142c20001412440303510100e400c1e80140030403840d5105940040c0040c0c00450145401c2a002c450356004130440800207000140c1104a01c003590380402841c0e10842030042c070540307020000744040c000c250303025020b8940c18000c80c05660301c40c030495009464843c16200c0000c100514500741d0703041100c0642d0104803500000f1000c0c4110402d4a050300d0b407201010039000e00300501103500100c0240100142e140b0301e40120040f40d40c061168171000c90300d540e0390b43c242c1d05500c001040c81c1000682c0860703a40c2000300600000e44920140c4095566005004285580b60400c00300649001b21014004000c0040c000454410f0b5400100907071b02c6042142c20740005d65001c90f149070f00da40c48081d0090b0303100303200c00740b281c1108544104000b03c2d900d8403100f22a00c0740c0b01d00044031403c0d902244d4003110000304104002d0f040c05050b008081c140002c00036180d0720b040c607411143c070041c4100d04000000401d03808110790b0742d0101b404241c018054400e10313000e80c0c20280050502391581d0b402446 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 918756285 1250 918755035 918755039
    0x708071215050403020316020609090a050a0e12042709030e0f011b020f0f0301180302160f14151804060506091c022b1104060b1209011803031401 64
    0xc80d0003528020f6505a0046142c640103201a403045800382400b2a8000720800c000b500990300c000806002e20403039140000c641c2002c510b40790032250f00fa03d4008840d00941034007030405021030b0a4408640c030310a50000d04800000c02c08070902103020b90100c444c3e1034141a1410701d94007401501c8000c500784c030514a0b20464200647d030b0b085c401d51405201201e20300010006082081840100c214050240d081540d5002c0c000383c00d44982c4160206004503280b880c1e000d00d40e0408c14403070f05006820010786150300305650618902c100303006502c4140d400d8084500300703880e90000174601c0149456515120000d0945000740c02406800d00341c441d07070401d0804203480c03800c1da0446655402c01400e540200c454000f00041d00442444143d900001c80c803502d110011040039404ea110746000164010310a00d803a01d6040c0c200c0350b045050280c0c0c540f0310f0500841044104903000d94000b101c4040c100d6488140b21809001d0f50028040b200c44c01c0c00c130000400d5055002880c5070020413400400703607a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 918757535 1250 918756285 918756323
    0x605030c090405100f0b040612110607080403031b060905010507090902040f12142e02030118021b0f163005031e030105040c0207060e06090307080712 66
    0x81d0540303002c1c042d03801c1220684c030080746a07803007260151460308000c0b8034481ca140004e4100c072404d0b032001c0c0705100744042c3c5030300300f00030b8004580344008200c0d121424001c180d1030308032a50069000003410701c0b004012205810816010004610b5401502401056014944036028042c283c03026404100107a1001c00d40380690b00a68064811298102e4241860001d1011907080c9d1454181d448900031340012000510501224087c501034528051034403419048400181070481c0c17424200502c144018041807001d8607603800c06041c00030b0096241c501c030503200d1100e652400b0303540c860791007814210490020040350300c6d10207400f861310368034074550f65410005580b403030b21203d000c8450004e8001c1c903410200000c000d2100c1e020b0f030100e9042c44d8141c46e42040380c004002e0819032440b0040b00400103440d040c01034940030000c07407025082080c80c0c5100500744140803803100f0f12480c8045a281d4513a1030400040c03001703040080842c0e10315075641c80c065035603a0b58100d065413010030080c01300101c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 918758785 1250 918757535 918757549
    0xa02241b19120c08120405150c0702010c2307030c050103140112030809100f0516020a030210020c0c0409080a08060907140708040e07031a15090f030715030605030c 72
    0x103604042c48110700d90804204075010074101da0215204c84051102045415512101500c01c6110300010802000320b4800c1c070050320002080190302c607e040018000507640070003440311865100159612200c14070000c0e9020301011401d09100348035103070002040c080041e802d10f040310000c0c2c03404c01c00d40f8010350f042c40111609001d48100c40360400101e800092040400d01d81c03141144099542044440306110140d40b244101054065111010b000055030412481c0036100b000e80020150748200b07071b8000e501c84030703188951000d059010881281901c400e0081c0900010005e204101a00307052411225581180d0403c0300001d0b041ea0000b641070400910303d9004195644072100c20f43c12048009a0b260721501d0204d401d09024040040c0413141454030034041c08440c3c0303000c0741802ca21007100c2410101041c00a2154a8590070303c0c142158030b40440b0601c001c281e6803107c01c1003105001c0380c940b403041e0b84035020300c5c080003075207100d4940d056000e0416184220140c3c2c151261401c10010a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 918760035 1250 918758785 918758833
    0x50405030312330d1403180916120c09050307060203120109020f070f05100504080304030f02031305060c07260d0206190b15031f0e04050a02241b 64
    0x4001000320090509240090250884510510f5900d444078101d1080900f11f0b000345070b90020000ca40001c1d421281b40a1014070351120003031811804c2211300b0790340200340c0a0500c1c40307030b00c0407035880000b0740c0528415400d5001802000c6d00b140c80207503486000966175030240403e00c8400002c3c400210303600e1824000c440400b0100b08180d4201007058680da4013007445c2d220100d802e4455403a80442c080b03140c3c000c2c5d40c40342d800f40392056224030b003034200945411940d000040c119001000150180b1400f01c0c480015501c0076510241c13156075403a4010b02c0c20322640c00100a0b410010111703c0038089882e0024228001c080550f078100301485401d036610030003034500764a003a000301151819540c580e4000c1d554104000e0511060003110204507201d5442503d0785c40c011060042d9001c007900c10515070f900149110b1340d020b0b42c140382585a40b910b43c40c0c1c1c4c5000a20440003107250241c400b501c80e55184044560310314a5982d0100c8600031002c13240c3c2050314109600403a0b00c8881c80c1482c00c086201 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 918761285 1250 918760035 918760111
    0x9010203030c1b06040c05030d08010e0c0a1418130b010c020f0303130824010b040312020f1f0501060206040f231f0b030a0c060807050405030312 64
    0x10440d220b00101c00640e40000d081c1c000904103024a2988020f0200225801203000705c19113100c25090034203060400d80d01c25951414030071031100401a03984102e5002d58404501c030003841d107a69506100312220080e07264240142c8001140e01c5800c0b010081e01604903007000c0715484040e4010308480d00507034004140c1d40340481c041420340c0c0094248246030b940124402400c0e240b410500b91541400300714650800700c016486178480c2c2241ea10700d0300d01864200c03903115929201c1e601d400001d60701391085010040207240210802c010140c020003010130b00d80c3c00c8400b9200708410b0300144940c0d810b200c4c2c450000c442d0030702000049403030001c100640036640046060905031040d850b424002941c01c0c544202d903000410803280500000c0c041c9039a142041d554080940442e081d4031000d581d0668a20fa102e904040c041d00006004400004200c408034100500c1d00e42c0c81c04810788241c0502d40c0802e070140030016016412148966001d8445d0107804450221441004000d01403e40c0e4001c0c0ea90f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 918762535 1250 918761285 918761287
    0x30a06050f10090501050a05040803071505060429010e1c03030c171602160905040b0c0f0a0806150a0201050901060b0406230d060e04120302180906130c090e0c09010203 74
    0x4c8074a51290b0020400c890383c1d81032492030707d55070ba00302614503072000c40c081e240001200300f0010351035080e000ba00c3d0059400c44043c04024296660540e000303415803d01855000b0400c00800b803030340a0240c0e1802907200400c81e429014100c5000c4d20f1001d000d91044000902c0d0462094045000d441c4080704003402c0c41c0707a40c4850f51900c8a1400030304040e21034806511409501e0041d40581d0354080000d0280c102008c101404e0902e400b4201c11000351191542403001c2c0b119a0f80401c00109940581059181c0b40000c0d4a0300004109a18010101c038400341100003406199217405400444c0141d50140c0200300d07035940d0720541500c6000314081c03a40043c100151000300070b0300d045030401d68859054421450840b40301d9900e4122b079560741c0700040c018041010072041c071903540a882000c0815080c00e524048071582d01c4003503250380078610b0b84900c9445022540507158800100000703110030108001e404120f0f10083c2500d1554170a444103032165100048005020400765240c144042c1c00135 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 918763785 1250 918762535 918762539
    0x101e06032d32011505011e0503271b1207080309060c1c17100506030609131505010807050f0904060b130207030905011d1e040908030a06050f1009 64
    0x100100c207005603440c070050480c402c240686030030b1085401d070b1401510010801da29080016000100e46c1c140071024013030740b21300161800c1d042002c49501040c0c440e8185607503d0ba002c14210f05102d4074180700c0d1188148910681104942a44040b82c050102d41c4440c0e0408091360356542d8800c070340280c0b5480d130002d0215280c2401c0c640c0c00350410500b51000d80c0d000c2e2080c1c460b0b50000280c000c185500007940210303079032445d1a071035050310b40141c01038040680a81c10710021803068400900740b1800b030f07005c02d00010181003c00c2440351106911421040130350a400d61b5010161200380900031a0303014040000415107401d01482c100744801411600b015507907070f00d40000a06918078080d402076500ca00c445600b0640748024070841e8442c0e1203c0e0103003400e00000608805800c0201002034220310b01c80e141540d1150312002c40c100032000c80740d54000e89100460040c1068002c014240c500c04801d01c40c2c00040760300018140e40c001d0b1303071070b0480d00c1c0c2c2d40c1c0800c80b82814985644000c1000d005007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 918765035 1250 918763785 918763823
    0x20301060e09070c062c07050a150905011b05011409160303020a022b0812010501110c090403090b04090b04050f0606070b060307030804060e03060c0c101e06032d 71
    0x189080c920703501c01c0310440d821100150800240c1c00070f000074580101f1410701c1185030034500e140103003e40c001004090b0101d810050700c0008103005940c144020f101446180c00b03494460f1080c0c0a41c00002889000310001d4000000030055881c552a4054040780f40345001c140104042181e40583c02814074100382d8090100c14481c0d00c4e02c641c9100e80e0083c1046d5014841541642040d10032110540c0d60003012880e00384110701078103c2410071045088000130b841d000200684259800c80d6035900300e45a0349001c2e1407955596016142d52100840c0001d1903200d16800985000000d0b035041c800b560720f200e90803014a0040301d04036801481402094045040340c0c1030a54040070150442d007c003600c940f40c50141e9081a0300c203070009459407202d5103c07030605003c005e411a0760a8134560030001e0036054a80c8848035110314100307040d69607500c8041d008040903c039a00b20740d151010002c4503128102405503a59500303080a41c00715034918010103041c84445001519000701028000c0c0014a030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 918766285 1250 918765035 918765041
    0x40609020f040b1e16060b2e02160b040807050603040c1208120408210105100f020a08040e0702190b0a020a0302091908070602030408031b0304030f06020301060e09070c06 75
    0x80940c822004460400100004c0301c03009240c00c1d50405c07000e441d11882c03840d02c0b005032a04900c0c0503000741181c80300031010581d0702d0b00c1c18042140c0f807a21464600c14050b002c900e8a84034003e1741c1e140a400840c0081c41c0440700c00140181c444500c1502c1009440340c040c0301940c8000d0390b00038200d04e0800400c02004034001130560101d07100309001842d0441d101807101c482032042d01c0981c0c0d070608c0000e60050460300351100c503425404402000015615000004d8003a09e0820005414000961010300c2c10178801d100140f41c20364044c11441e200d5032901644011004102c803000054411004c0c0341103504000e22024941079484038044210f59036810003000079421610045d418103809100c20000c03170ba16003c165844a810b6102104030620740050945482c099603c41401d5420810048c005403078084119020400340030021081c2d460010700c42c0703203540300e25440a403c00d081c01028408014150b001103041b103240b070391400c034010444020000442020744114020a020090076000104150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 918767535 1250 918766285 918766297
    0x80a1a0a050f010c08040b1911060f0907030b040818090c0a2604050d0e0607150e0a0b16120b031c0327060c0309050a170f04090b040609020f040b 64
    0x200d00307031484e0000c5682d050920342241d00302c0600c0300c8002c0f54841500d414001250070320480b40c07030001c04284403403038101e886000140040c1c1424661200090352100104029801141d201d64048681d00d854281001c03180c00c0209042e007910780d1a0360340d40041c41d2402d02c19004d8001d02882c1c5242010300320003035620a5018501d01084000c248900c00b0b00300c00f08140f20710890195024181421510314001c02a460035502e1600c180c0b41840b0081c0800c030078840e17040c0601000703100052050400d9200d1071034005c00d100014030168180c020405005124910202c1110080e110000080203c02040d020768011100c0c6a4059000c04210300320800c80c101281c00d810118140000c101d004685c6000700c556650700000e185113107048204080100c0b5100d1810040d02914042100d001243e865076190030081030050513003000c4000d4a00c01c03298031003c0700c408542114405540c0c5607582b0440000d4840884010722592170060b00145011b07090088559079420108500e24242c01c10299801940001e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 918768785 1250 918767535 918767537
    0x302060c070c240f050a0c0b04020406091d0105010b16030f0c080a0302040501090512030733061809031b0302010f0222080307030801030210030902040c080a1a0a050f01 74
    0x2207000060201c41405031803e0020300a050b41105a114020240c0341c8070314000948100403040185d984d503950b112107143c1e240741d0302c030001c00b0b11915a4000a8082d010580264800925041e1881c40c901440a401e6031003e007140028012a031ba01c10f4841680c3c0204a00d240c3d8174000404810002480b9041d640a03c901c00c1c140918605000d4540c1c210a4100c00e9543e404650300040c00e001c50f40c4c02025030750091000f11010821341121503034844d224050303c4401001f05241c23080d1480e01545c081c0c140c1200300200050100282110921000640254420300c02c4c00800f40c04604151070f054054a0441c41c0c054460102c09140b1186100880042c01000c1c0c08655a038242041307444c040380014000c450441c058400030a80c80300850392002c00aa000e130394280d10800c861000650840c42c041d044940440b60203900384d400040a80140c502080002d5025107008440c1b40d040c0d4105400c10301912890000701301520074000300c0130110701545216984284a10750400c42450300801d1800b40e0a01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 918770035 1250 918768785 918768803
    0x39020306150d0f0219080f010e1903050702150d20031e07050d051009051006020a03081905070f020c010c050a290106080106180e041104060b0c03030a0506010c0302060c07 75
    0x4070411200b62031710680110303400f80c210840c06402c00c3c8003400b5100d011002000640300d00b16500800444800c5a280020107100c0b001c6074030b0301503541e1091840b51324543c05102650700c00b0400d44840042c8802d014095035140e0310644440700d0325203001030302d1141c41021003d41c00143c41070140e8150150060440302006010041240c142029015040c080c0e5910101c200718141070219801c145c4034001e00c10b404e80340700202c1c100591a40080d50f49200ca07014245140384c0d03143c6500000303071400c62403142d41040f42010140624141c1c800c00303c0311240c409500340c400ca80d0b420801118003100c0028060300550007104014086100160060440c0c0f098090559902d0303040f00282a501000b40d00c54408140c0c500010441c03c2c0d0803040d16010050740c1e000e01040c85040100001d40c810010304041c229540208a98040d621a0760100c0043c03c0e2820f0090703100d0f940403180d50b580758812950303652040d0034200401d840c0c0d400b03120b11405c0b903a07140e006000c1c1030780e07003140c2e1003c9134214001c140c0d85416 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 918771285 1250 918770035 918770059
    0x31a090402030f0d11010c141909030210050a231209010e0a1b12031b03020c040f091b050a030210020a02100c0516051039020306150d0f02 61
    0x108200b40e003142031349038880d000c5e0440003030a03250840d040361a8030018013044c42c40e05441c0069807421545200c1100170140e05000e455071044036403550035000250880a000c4000c40d4040d00000500701e509030300d698000010b02c00710030300c12400605858080740240c084c4050761104050500d010b80c481113000c000104035100340d000b02d00d01000901c00780d814420420f00b4018084a50440001500002c00c80c00c0c0c4015155600500b074000c2030f5540d54100155240001c00c16100384072403080e4500041041c0842502d101a400c0205041341d0201d80031212400a8500c503840c1d0f45440c803c03240000d0060142602d03580038820000c54907440e800460007100d40350b400586c1c0e00c16140100581681d11094a0a924030340346191940104a186002d200210300304001e40d01c1701306d0741d44007408620301080130f84140c0c002411902d6030f1910b0545031001c0c818044c00c4140c08103030b680714094022000c941c0a038940803802c042d000272075100e13107801003030003190040811030748103410400900c05030003410b07540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 918772535 1250 918771285 918771313
    0x702041e0203010f1e0509090c030703030f1209020303031b160302010c0e040e060612030408370c0303050906041206050901060906120221070906090c031a09040203 72
    0x218180100c85049501100500841002442910203080546a16120450181041c10340748030648a41c074421400318000881c8039500340300012113102c1c09030403600d60540b2481c000d01001060a07518001446828444203c590302e0301848070b40c0d5801401540c50b5842e0807040200045640310b82c440e0301c6000f0007400c0e24206154400d20100d034000d50000440e2440c082000b40350b039117050701c018865818042d5808040700040307040c41d0419822a41c01c194400401001c508501a6a0166646018511201600c8105125524000d9081014220368606170a01c07181c1c400c490014007615059030300506100003401000242104000101400c3c01c1c290b96241440e908c2e071003c081200c220f501c0324180440700710240614405050440420711034182040e07050144101c44400180c0320f4414100d0101c00804d80800c5000c011601c682580c60f01d076203842c000005030241e4460301c980903250247c00f0060714824030407809000f140c50403000207007418808203c142a0041d009070385c14012074802600070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 918773785 1250 918772535 918772571
    0xb07050c0d031b0e030c0108090f03070c0503152701090f03030f0621030c020a030506070906110d0509010e0f0913020415060206220512040e1b0d02070204 68
    0x19001039a000c079048600302000f01440410888183c01d00c81e219144080964001c03440e01602c210030700c0c0a11880e541c80300300303501d0b01f4900030010302c2e00d0000250070341c24840001ca400c410b030343c4160102e951500500b2001403406000b106c400304441048010070036200c01c2d1000001d00c10030000c00214045110342c40380f90308412090400c0740440ea40d800c02d00340e01c2c2858040c2c580100b0046000b01d40a4040405d40b1042800c0f40d000242001443c0b003200d800c554039031540c100038503000300c200c8850f4901008083d16818042c010240800c43c500782c12032402100052040380405d00d0b40e80c2c281002100401917a8002400c00d510380e11801c5200c540000d0303154809014881c01c03d40d00407007220742d01401030108030788000c1d1608040a6514005014584d00002d105820030a45e4509100540300d951210300a84100000100903025032851030340304079041c1c0081c0054440181c02c40000e602c030170140040400002d15464a802001e101c0301080050650103015114000340010075242c40d84c0328685c4076 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 918775035 1250 918773785 918773803
    0x3007030209071715032d121c0209240d0e0706030e0307081b161d0106080610080c1c09030e0a06080a0f0912020a05060c0403030c0b07050c 61
    0x3000810f0a042002a03010416004400002240d80c05124000441d482d0180400444031a0f02c4803050269a00c44400500c840043c880082d50407550f05940f2400310b50340301d0400c244d150036075000055124150ba200319801080700510066600c00201015060410b0000d45014480c40070702c000c1401401d03a0180ba9510840c1e6006031104900b4003e0190071140704510020301580103108190019142c60100c032540b0205440b050402148689803070f14202680a100c8440004184c00180400c0d0301c0d02c1032031100801d6514004c030350f81c80320b10444160b20111246a07000111070003c500c142e018070700d104c5d0010001c05045103001ca040741e5040079a1000340c030741245160303039600706806d140e0b01102c4032081e40b00403103000c5021031038802d00504c9000064080001b042d511902c100c60420140e20071119568401c101d00001001c181019481b202c4000d41900c40d80211000224a0032080003110140c0b9490745842c0c0c2640343d01e864943c0c1040c8001c0148007404401c000000000c0010856100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 918776285 1250 918775035 918775037
    0x6070912200319023a080705070603051b070b040f020604090c020304032307091a04090f020306070509010f180e0f04050f0a080d02030a090605010803090906300703020907 75
    0xf460700c14407440e48001c501c07400c011a609681e088809140d198082501582000341d824641d4003810601c03268405c02100504620444800191103909a00030b80d100d9413501c3c030a1481880d4200821896102e00c2e18003d1100d540c0000080000e985040800880d0f8005014079040c1074842e10000308407a01c42d09618003592000c0303001c00c10440060b41d00c22000100002003071409088a540c241d0380c2e94a03018100480e85c4031030013078000c48105201c056902030300801c01e000c0c41e403582c1171070302450882d441c050340a4000e16000441460049044411001040c1c1d2401940c0600e40c80850f103403101060b44a54a00101d42c3c0000d0350f441c46114680540c20f032843c1c404503803c080c5070042c0b626803041070030700d000e401c000e042c400030402120a4074614041000090b0707803130b42d83c911080000d0540e0362004103054607103c00070807003000020180c400b0000a881c610202d40b914800c1241d0f2044c40c0c1000800354440d80107005681540030303524200e0314000c00449105070380b01c1d400a0f030301c0081128080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 918777535 1250 918776285 918776323
    0x16031b05030a11010e011802090405100f05070e0306090304060c0c051e2826100b1003020f041401050d050f06011d0307030b0601090b1b060709122003 66
    0x1090f258003c2c400c42c0e40000c0d00c107008000d042d51070754480389031001864000c0d1080115400045c144001032040d90681c8566070002c01c0a038080c9101c910013440161045000542c07455000515814005809401041080b008608051910408071603819410b4812501780307141c18000566a22202180c201580c081d100d0208406001c10520044502e190048225034202413036900c410005c0001c41c030b0513504000c0e000445401400c0201c1144ca0f900a0038009038422105101082c1b4440e034020b800040044901c0b070643c0c48441c108032b003607002d180c070304d0741100d0700410040194079050400800c500320181812420a86070506050803608201e641d284965100001c005c125a03002c1c040a03081c03102c446d00c2c55122410000400d6840a075808018032000700b00002c9a0303160301034020702005200300c0b501c042c3d4a4114507034004444498091083c854030440307000c1100399018145640541c0c0d8213110003961094141c03518001e8980b00e5082184c0e070301035500e082d032558405100b40703090011034070101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 918778785 1250 918777535 918777557
    0x50c09060d030c02010c11030a21030630020a0b0c120304200a260c040b15031009020708070b0115050a08060a050307180c0516031b05030a 61
    0x11002482005006034416210038042100181c1c205520741c007129028a41514101182d18040201d1039414050f03940c184100042a000c0141050150012501c14041a0170805450200380d041d25500d014804030f00d5100140002180f1010b10483c03122110560b94095299590b004141c103c982d9402c0450707105000a845070701400200b0401c1c4481c4030b00c101042c514035158507440c032202e240c0c0c505076480c6803075071079603445c180d64040c456006484907002d40f038010389040303081000c24034510010079254042d280c0002101d181c24401d06c0311944c07000d007501c08201101c0100d400b07240d00040c1001040d0021807004180c003501440505100d910648240b0b0b680d12085c01c01002084051340040c42056140082110b02c0f030380031081e5100c2e4411400c00c41c03c0d03a1901c074006118030200d604030743c0d010b1062010001c0c0c1410500181207030005070100400c503840c24054125094440d00441c1500e2145c8071074034400003441941000b40e0450150030001211010741d4440c1e0031907200c2c0d884030000034010710030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 918780035 1250 918778785 918778789
    0x5130b0c04091b110703021c020414090f0c0f09071404180e060a09150905030c01050f06011e02071a1b010f0c1e0819060914070f0e0f04020c060103050c 67
    0x8005070313103503910000300741182c13556001815070b5841d80358260300d01110154000c11515a90042d0b4406624807030040018074090101035a02d24030113003031001b140b0030007290311028100900582d00b80900502400402d079650340e0240c40da41020700c11481400303001c000003d4243c0f020007400e02080030990000c19000b40b40544130b031411001410341c4100c03515103081100010b140c481d050600f001c0c280c0d07010804c00c0e4181841c50560288030b01941083d4204001c02203c0f0003411051482000240c0710701e43c40d0418000720341c1006440300010809648022001c2c0000401d021041c030803021000203c40c0390084484100c4103111000c00105802da445841c400d845000f070340600304280100d482c0c500745411700050384100b91002c02a01c03800303008051003c13840440c0d41c2032010154040d0100d09000c00c40e80c2da10484020551001e208003d509040049011a4400c44100e10a54210750311400824204404c0001c18055a8020765001d54208400c20601c8814403005d4021402800075009074044242 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 918781285 1250 918780035 918780047
    0x5040f03090803030f0114030109080319060b0a0509040513020315070912020a0b160f1a0703050609041205390f0a150f050c190305130b0c04091b 64
    0x300c1e01982c0c000f4800c103c60011703061a1681120440300425800c0800da00209005208012000e00345010000c104105c0e200400010810408440004c12980d955140c011145010b22a04040010b1041042a5040c50070f900410f0700207980314411006da07103565000034902800e0034204403250801d4410484001d4010421100502c0e10700c1c0e0001c0000c00f240c0c00940301d0321130b41c01074500070079000c030340305030340925400d4510700c16640301811110302481800d00001d18504003c0d88140403880100285402e1f102e400b0b802e000f0708010344842c50f0758440fa0381d443d82000000613110108101800920b081d030101402c0320381c8202602d0f1410508141ea0318042c1e9415020b242e400a2960042030141ca80080016001d441d05410007107e1410b05001c030442030207004013003150001503003408240103c1500d024020203084143d800e004449848891065051b208e040310704604245141c0b8039900132400d03840500e680520740c03442440c9800e03103c0800c242110288040018a44a8942c2c10344813981c1200c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 918782535 1250 918781285 918781289
    0xf1602010f030b03030f0d0612051b010c23010906050a02251a0a06030c06051c060f051e04020c0718020301030c0512030909161202030402131e05040f0309 68
    0xb16082c014080c120021079580e00c40d05d10143e221010006500102c4c50f100d41c407800242c003105101d40542d00c0907040a541e9440010124800d412220210f0101c40d07000302c240044181c0c0c400c4441d460410001101c0300c9980c1e080d12007064654079581c80b02c001aa0307610825100e05400680140c40e40024001d00c0c5150946e00d1107417880c1e0701c00c03201040119181c200c100d0b55449441070024095520360200d04040d000c40d48c0000c000643d5020085002608200600891030401e90601e0615101c9182d28050761590311a040da8412401c000380325030300b000c0b45000c0466107280315121601c0080341c0030030201e81c02041200003940100006101c121075034080380407402c4202c0b00550441d41140c881220b17042d0b440c0304daa84540940901145030201c103200381c0701c00200c010b00b01055450102e603031056003080110040001210782e01c01c18104081d51080c0c034090340d009403803c1d130103d10744d540c0310b4014904111100840480300180c45044089800381328407075480f0300030b90f250100c114a4094034410281d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 918783785 1250 918782535 918782537
    0x1c03030213050d1a0717041a2203050c01150806060a080a031d0a030f061a04020a0e0409020f090109140a06120b0a1b020319030e03041a0f1602010f 65
    0x514080215404c4110f4074602d031204c00126510b03841e1148242d42580404160030203c0040c003040000340a10070303900312190640184100318030369906420480b4104900c0386000d01c101c9542511700801e100c3c4000e0201050800000581040000880e1588403020750181031280d100c2070800c8900e0074441c1282c2c00420b828401460752250070340d8080c02c08540030503450044000508011425a2035104182c025600480003142d003003240d0810307034054004204403403c0d61900f4011841142401d208880840d0101e5a42420840d9a601080060308080500b40e92180c240715580401d951040c8929000f044907000010701d00c44403803811070311005c0091400403010701e440010440c110002d030031841213a91200c40d004d85e666400300e0b0f64000b0b1002c2810050004400019100c00769000401401d0201d6000c015101008041c0d400b1000e460100490882c0c0350414802000681225154542d2403068502c2c034a05102468130b074080c0d03540180842c034803803540c10304880c4c080d5600100e0f2020750f8005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 918785035 1250 918783785 918783799
    0x207052d0108071202070501140903030f01050603010501021b120d020f0d03060e0a05070c05031b072301050a0c120323060321070b01030f020a09020a0206010909021c0303021305 78
    0x2c52024000c130442c008142141900092010701f00b000a600c07500b1550703441c0340412030f2410491045030362600100c80740c81c0c252001000105843c5444400e5904940e8142c2c010b00104060b041200d6000518060964008020f039040e2181c5440520891000c49110750090200c882031200031132030f103606140d004c02454500001800b20080600e099a804021003001141170740300e100701160080c0600d00050030078040419408100021000b900c11034440500842c3c1c0841e40360300d4603841c00c2034401080303461240782840e4140d655026201a0801991608200d41e90040a8503a000030500d10f90460000039584ca80380d040803116040c4005c0220000d210305400c40c0b80100100f13a980340d031302400070f4000949181614680010b001203c0382c09134080d07010055940d40c0c4c40c00340caa2003400c0340b0807031141c40340e1803000c142d00c01e55100780c070361007840c1d40d009203856403074482054000d00c0319940c143d8021055130380c1411101282071180c3c2e41d080c031950300143c1e507010580090300e160a058100900c1918 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 918786285 1250 918785035 918785041
    0xc0501330b070c0324141006140304030c0804030b0406020d0507030e0d080c07020402133b100905240307050d08090402130b03090c0d030f0305070207052d0108 70
    0x410f11504605032640701d11040601072110140001c04090b01a000d0115403d000c40450b007401003403886409001c2407048480e106446034020b42c0c90030724100110035246014400100407900c200352890000d80107540d100d10f09601e13038803100300c4107900311400d541064001550b03450240c2d41e8400e140e40200f4601e010403403440300c503000c1d1342c0794070005c01241c003002825000300d006042004210365889500030001c5542e00b49801e14224071002d51301c500340c0b484001000d048210058091440c0c50000700700d1303100b84803030302006d8940170054000c0c06242c01d14100d03600100d000040c510611f40a0399000811021030700d506583e40b00c25001c110030703140c0640c10400c0c0420540e181e4a031001c07c10b56106580e1074540c009003000c50300034007609841003d44441460000390f4082d809008601034030304442075a10500c203003418404800c22214004000824029180064500c00d0340460b800035003610541c0c000b01c0d0344200207242290301c0c9003080c901e03103464503400003001c1c854204c03840c86400a0170450500e01d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 918787535 1250 918786285 918786293
    0x60f0c070302102403060f06050d0c0b07051606030b031c090504021b2a0307120201050304020f1e01030f0e07050d0f0f08030105040f0605100c0501330b07 68
    0x14081c40c2010aa15407500c0003030007413040e0404252411802d407100c0403115a41e9051a802801e0b17200f00340300c0c1085c981000480c80f42400e103031850f4810340011700c1846440c901041340c60035500c001c009946600428110704504400454403070000d0090b40d80215002c0c020340308040c14185811414404140081d5580c3e0485402c495004200c032000c0318010313210410101581e01c4610951009010f0f40903030512100c0000500c0c41c01c40708050070841c0000c403038410b4401e25070b03220342c0f600961089025444160740150712a000031640a4805010403481c0d0b039001000c1403148210701d6103503090102040c0c080c041940d0520520340c2661100c2001e218040c4000c0490381c84118600a01d405020000804d100380400d9542808040d907201a2214602c80c4030705041065070404e000c0c181c07040d0700780004045d40425a001d48015120020100070b180510140b051319580324840b4216040d540702c180e40450740781c040c007842d800d82d500c1c02c00002401c000e03450001c4c0d40c1441608000c0c441c00382480303c54049 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 918788785 1250 918787535 918787543
    0x4050907032d0b042a1b140d020706050d0b0d1407092307050703090b16140a0320070306020c06150306010b0a030c110f01060f0b1608090105041205060f0c070302 71
    0x800d9142841c25680042d042c81145c44207448091b101e030400720440380c001001174940c0d01040010b041410b070383d07070118400002c0762511224818100050400c0c080c000d0440c0d40c0750302c080c4007044003c0100100010564841c407072000d060180c4001034005540801040d1094041e100c2e0140445580c0000c0106450756003590071030242090003001400b0442104060059803418064404801500c2c3c0310030055401184001b00305a00315426808010100011000050343d88011540754880303401284400f000d522488501940304c038a103104442000011524074802400c40c00e8401010f003c0d640f4010a04000000b0008800c902960040f001000408998401d46d80d4880b103a01e0081010511884200c1d290348141144401c02e0094459050060301e0541c400c0b4215481107084696407a0798240c0038444d801030403c89451400803612800010f503140c4020840f2000c1410403a080544034130307a103160004503120480701903002c5130901c100030a9500d8501d900070281d0145a20301190713035800130b480e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 918790035 1250 918788785 918788831
    0x6010f0e030a08031308070609211e200102120112151515110105160203070609060219050310120314031509091e0c010504050907032d0b04 61
    0x40f0840440801c00d03065400100251440e0403c1ba21074460036a0700303280004280c08601210008010303081c0300060700c6d032902c1e400508812a2685c0c407503205004001c4000e01050744103403080021845988074507001090100c941116190001600c40f044210076542003d0181c00040000702031103941000a00104541501c00b142c503080400d007400d03500b851002205158104d144144070041c5520201a40240759041a6200340000d0203180c640803003071489451020445130041e041004500d003c928650000c1305607078824017005140c2907010400e52441d4090034094000a0400414030000b00c17182e403140c0015200381e00c0c0e8880e6050307240d9030241c58108005004080280003000181024803003081c1802c03d0417024010101030f1400d000e05a481d00080d1a01d4050340e00e90390507510341c045e00010000080039044e15004c1c41c0034280b07401c0000c0344400402036001c041d16417800e00c0504015070652444260b10021080942603d07070150019903001078895030040380740c0152001031980041c0a9a2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 918791285 1250 918790035 918790043
    0x503010f02090a0b0d0b100c020102010b011707050a02160e06130e0c120c0306010932181c0c1403031302060c0a0206070c0f050901180c050702040c0806010f0e030a 72
    0x5d0703078407000091200500704801c81143d110854100044902e908030209150440c03003603008001001c1c2501c015150700030101d03a841d44040c0c2410000b1001d0707024000400d01417410f801111600c1742c450565640001040d0008903042d090401480840d040210344480000d484d40b10130701090341100c410641c3e54480319580307441100c9084103888800810300c41d00c0c6030840d001d82600c20070340c1c49815410140000b42c04462508541104c1034190845000d0b18403c04101000001c080340c0702d407040b40c00403c840600c040640e01800c1c01802480120000100c200360f8503445444041c44503007081310b4a0b5541d207106842c25003040080040e250203001240803107582c100c130090b031200d00c1ca5040c2c80c58105400e10003900f0140005004080c00f5648a00100301c49000000e801da0341d40721028000c0c000c2c028490a0888920b01c0c92102e07840400b50881c1c04641290b140240c20041ca6400090540380d02c6840707000810054028005596400000347c04008546d0a04054180011020aa4a00590401078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 918792535 1250 918791285 918791287
    0x5120a050a0204031a1503010603020108010510020304050a1e0f05060313030e061204170406020307060c020c130e010c1103071106160b0702060f060603070323010f0503010f02090a0b 80
    0x154a1560a5050700d0266030405060405c4d01000e0b030010904442c151540a440d0ba40c0c50400540e5103014014017007902e5041e901d44c80640d20700003d1000e1b0510103180035095010600c00419981c45070442c400040c44100c601300880340745550b12140741e00c180d42100c28902c113101e00c1804161100b1003102c0c0c004035400c3e1106160100340c107084030881c41c14200145e016400040b1410082ca891f801d040c002c50140c409013111400340d01d829055489070b4401c01700582c0080c80f0403000700e02940d00c8101d161540d40143e5a00704080e00000b03800d011108007030f29080d42d0340c01c02c2d00c2d1000424030440e51100c2c41414400c40c200c2c40308071701799a24001c240d4014450914100c000e40140c5031542035403000c00c1104014050380c040741c50250860b0340c04541d4140144220360020301044564a2100d00500b0003500b481c0c0740d62201401200a082c40d08641041c80000c002e5458000a002903400d00804030b842002821505210401d802c0d01c0b8407140048429005002003031031a503981507018201e4035102c1c419 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 918793785 1250 918792535 918792541
    0x702010504120f0c120903060b030f0c150d021c0e0703020306180304090c090602060912030a0c11100b0a0506040503100203060a030503070303060905010b03250c060203011502060705120a05 83
    0xc541001a8284c02403a00185034000020590000740c6601503d215141c02e014040307904d800d056079203a00101c02d05003540259000302090405a0317030941074441381d0110038680104010810140e0384800d4000d9000340181650021013001889501c01c89500000a00b11144c5035800190342c0383c001030001400000403084010300300104000b01d900400c0d01120a21400040b1000034100d02d0080c070441001d4082c1100042d10f206020178061900c9181088403419034807241d00d00402010b00400c000305100604284500e03040042209003501c401e0000040703a1000880180701580c3d03a00e9003d5030050310103200c01e006640e00822710b041742402030f180041e100d0790391400142015685a002410a0100268010034154160420000d40e03d41010500072641d030388102000a11003100c090700845c00c0c40101d00d1301842400f0341310703102ca402c0e442d248403c01c5a0b80c44110403a4401c7e4000b8600c0000c80002c0181c0a405100440d8024894103000c0d0610300b0560450458183c000d104184451303580c000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 918795035 1250 918793785 918793787
    0x321041403070f15060816150f02060705070807020d0c03200108040b060d0c0b040e06060406050a081b0c0304090e060f070e010c0c0b22051305040f2103050702010504120f 75
    0x1081c1c009007107540848000c05c80247d540c40b05407015006039600030015045c41082d0b1402030825184914440d8014242e1b5600c4040469480c3c10072042103807011020010803000d6500c0f804400455806003000e40e000c1807951624420b0a0242d44403903101d01c1881c5100c0c1c08585e003025000c1d60040e0003034107011150b51000c000883d02800c6400050500d400d100b00072410f41c00d0400903106403001120081c4090b101e9a04200c4103020358400c03480011410401c0c60392003441002c0442e0009000c000311043c0080c0c40c01441d03a20b03042041d480d070050788040380422a0388401d003d83c440c1c1c03001483c0503042c0c0d070800020300c000c2d0300f400034480d00030710040004005050b403003400854141ca400c08540c00304c0c2c80d1103441e102840da11403801007e08040540303140d18200715800d1384c0c81c200d84000300300d201070840b509020405020010002d444551207011000301141c001083c1c02d810b450010641c203418404004040c04942700544403c0c11a0316107410803000442a41c03000070004070b80c2c02d10090140c00460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 918796285 1250 918795035 918795041
    0x70f08160e04090501050c030406050114060d090c08010501060c1509230f1506010e0117190b0303070605010e0a05090601030f060f1d190812090321041403070f15 71
    0x83c00424075803134403003049200402800914050751054505004a980c0d581002075a400203c212a900c810104480e0704005c66540c4044400d03031080044451f880e540d11900741c2124403d90104020031700078842d034800c010010740380c00132001d20340f0802c01c400215034030740d4084540e03400c22200d007103185104441c121442c03c114a0702490000000c660310812004843d24180c20140c4109022800b610038031115507000302c4007e00c042025100001c803039036032284440401c003540c504081ca0b25540e850a580c01e41c9017440103258550203030743e010426526007200254900d400034078086055203400c00348900110049900d50440390080b1001c4c44091150414800801c5411902180039203804008503402c3c2c00d420049040510b40c0068801881948624044100312118002c12010f010009040b01c0b408603180242c000d01540c08407800c20302e0f0b410100e54511690864600301e44404402c12041120400500d83c0011008002c2d600340724444d03498000006079440010121030300d0f095601407610042e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 918797535 1250 918796285 918796301
    0x1104181d07060e040e2103100302180106111c030506042405011d0102101d06041109010510021c031803050903060a0504170a0c080c06070f08160e04 65
    0x20003038446441d42c504024010f07003110034030706004506042d40841c07844c201003032210042c51400a104d450030201c20b040c1150381d100034912030b100301c8a0140400940c40702e04144a407001340303170740105441d410207d02403c0d035081c24040c40340507406100401c601c28030103a00c09188001c40d050105140d203400d0002030181c62a8418162207907035202032046d1108403c2e10000440d01e007070300c400c414800e07020343d0038880880980d07680e230150b805604018cc1d0a0181d81c40f034907030021005211403030280c01c0020581070240648050b47d07020320151015540380b4000201d00c0c01400200d4100058901000c40613444603803243d2019181c903603010030140f0140c00f030f40224035a0000c440b20038030b04841514014220781c22810409009200d603a0002e808030b038a07880b882e03014171703040704008240c001903840090503580000c400c5810044295000000155800013a00c003061380c80f4007429481c91b00103001000051080c0c0103508102c0340340107008000010140c00c070058101031414180350441c01d40802d025200300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 918798785 1250 918797535 918797591
    0xe07060c142815020703120f2304060b04020a0f0801060203030f040b0a0605031c1b0803010e0a0221041406040305090d170a05130b0703021c0c050607080109110418 72
    0x5d110420150b00081c81c01c0410b82e912400c01000107204211000c0f41e452038500d1030700424020032847d00b107445290b2254018482d04020400324405030108050b60000a402c4000c03826201900140d01d4115219a01405841c8001d5040d0b00e0b00c192401c11361403000c0e0000c0d00303920183d00424001c071a1b03500100c001d0306001e400c4544250009103100300304026285008000380100c403043c1c08858407005c441d000d840d000051a829a400c203c1c1052554801405014480b0340c20403ea240e404441004124004245c044403179442c075090401001030b10f4150344040c01c980102040100194000050700e82a030400d5900340050003103072030a80d10f100896001850605004a410028194030000800f6046820464145082e9840028960501400340c0017400360300500900e00500642014000a02c0a50b1600520041d4103442d4981480025240f00300042d00e40801800601040e0080c00f6004c4a005c1c641846d040c82c04800d0382c801c2c043c1910b9910030544030680050308240001384603942c0014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 918800035 1250 918798785 918798787
    0xc17031e06010c050f2802030c0f1305040506060108010506161b030609150e0a0c3c050f03030a0806090403050714250b0d0b03010e07060c14281502 65
    0x14007440140d07540d010f482c917194900b210b40031800070b41d51b01d140000181a405001000c0e8180d40c542008a075907080b580b1a5080120040f840c81c5124080c06172501880c0140060400c0c1d0502000052070b5410503082140122001c21241d02021204000c0299154000c0c2c90981d54046100c6e0740b0324141e44a07440a0901801d229041c000d024010030f0718001c0300c0c20b10004002c001c43c844c42c6c03541c4850460402900c00c0503840f030104002d10003155107140304102e6468042c0001d2000c481c4407507030780c1102c2d66140381c50650001408117090800c3d5217039001c00e003200110b040c0688048001c1045000904041c091101d4001003020507011b0020b65091030391120404000780e0356003403d20b80c1d42c10081d9081e405040200700080d00c0e81c0c414100e003010348840030034082c03522584960350b501030300055400640544d601c2e501d16810b0340041c001e181c0a00f205079600c60301000030342401d201d11942c031035084803e0f80041035422700b00400042c404040104000822403c561542810340c1005020240c84003a030380 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 918801285 1250 918800035 918800053
    0xd0905010804380f090d09090507020319080405070b03011a07020d12020f06070906090501030b0a0f0609050a1e030b09030d060b0405100201050702061302030f0106060c17031e06010c05 81
    0xf003500c00d2207205120b01000304d400781c1d64001d405a40c41202a02c2400030600303940b400e200382c0c403c43e004190711a20fa0700441e854144214811140e0030001e031840000100c00c0414082000000d1110800400d01303850034a045506181c48650b00c12544511118040000203800c1c08544640f9800c400b15500703c1c04080003201e4140d4080d440340c206888906582c01803d0004070b41d5400b400b1700d0f03821359003281d4622003038a080400540080041c00003a540c0003104510004e401c03210001a10050030542d940c1440007031401c01402408a5150011000b02c841005200c040031144101482242d4010100441c551107c0e420b440c01c40c0305c2e03921148460f604041c1c001c5082c54084008008440c42950035038070350200364800305d088600558404005811a4020130b582030580b144c09181140001d003500d160b820300b03010050841e0a42e50128002c00e4000d00c83c0300522028034031081c03108803400503481c510301d0070070708601c1c005403551041e034060081000416603036441040c6188160740d20400f00c0d0b000300f07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 918802535 1250 918801285 918801383
    0xf0212030f27060103030305130b04080406121a010507081b0706080a0b011706040213090b0301060503030f16140a15050106030e0309090903160606080d0905010804 72
    0x2100b141c00516150030907480c5000d12005507403100d00100100c000d4a1140d0840c1e8045000c0c00004d84841e101d02c22943c0f03d1408240041c800c1c2e401284205c64040d5100d2030008064040105000310040d4140b4100002c401c2c0d070106a080340304045d0918080d0381e40c0b003061810840ba805902c960b0708032040e080b0364260f9104000900702042d40c1c0d5a0311152103640d075051010045e2080b06480718001007007024403840500041c561250800d00082000d400c00031103454100e1802d8a82c0d104682d40b68903403092009a040a00c194000b5040030340c051f510f8031344680007490440c480d1045005041001030300d103600340321054800d1030450b496030040d20554415410101d681a24805194144626120000480d81d0107446000a0000c030140590b00703000f04142003240b903074001030004030a40000c105403400c1014940704400018480e840c000740840c206550107107002481d0640405101d055031007030110741c0e0003c041c81c0c0e10551089000c0f018090b05581840103d1748440e0030080e000d90140416092 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 918803785 1250 918802535 918802561
    0x20604120915020115052e030f0c02060f0a05091203060a18021209070602070e060d022e05090a120606030203160e0c040b09010c0f210806010c03020c010f021203 71
    0x100c6005402c3e0003c4584407410402c402401f1108460b016180c08120f8403181c4002c0ca100e81446d05034200080c0c0b54903500e1648051311940b400380c1d03006810110801001c407160366a06500b0285582d02003005d8905150b0b0540d4848460411860402010000400c196280804040506015003c0600d8045448502c00c0650442c1003403a800310f4042d000280005e50001ea00c008498803a40248600d62a1113811025064050300040e08a07084118180147e100c10b400740040360b28411118948125030814601100202e080041c1084010001d0042541d05c26000c07005485000041030100791292600e20001c0c8010341c0000c0d0980205400c0c0c0c4400d1802e4149030040303550803100f580596896940243c0c2604c0b541c020f403841c031705c01031100c0c2a0315442610765512161041d10f000e440110943c94079000c074051007025544103410b0a0000890329404042c3d15004182800c00c40d1881c4155500a5113841c0c000c0b20050400c91500c980312100381c420498201c1c0304039584101d81ea02e0a11001613210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 918805035 1250 918803785 918803801
    0x1103030d0e0d17011202210309090f060a03080309031e090114030f040f0c1a0306010e04140109020f0f030a0207022716140d0603021207060206041209150201 69
    0x10600403a00c0508030540200300031180e1a041c3c00c00185144e007804011822180040e205903081480e2203000703a0100c0c0c0b4142c4001d00c1388801001540c0781c00095042028010b00140004445000c2d9001d100c0143c403941000d81c1640da0181d541a20780da68000442e285010f1790b41411085920007400d0100c010303644004184011013a0380d802c1c0d05100d01c590000441c40f090303403060078041301540020013003811003c030101014842d0583c4404680c0e07a01c0200110416401000300000c4000280007070b030340e0408040700c0071020944040c40310201c5000700900d2202e05120740490590000740350071004030148211014440c10b85482500d0b81001b0311144000e4002103003c03405a089903843c2948200040c0e42118180c0440c0140110365403421810000b2500501e002001c4c01211b986200c001003161010344154482c040000038100d2440c0108001c43c00c80035926a07442d00805010301030143d001c41d54540c400c0d040b0805201641c4281c2044034001025801040e0406290020180080d030640244103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 918806285 1250 918805035 918805061
    0x15110d0c0801060504180e15090312242b0f14151306060e0117011d030a08090a05030403051020160203100f021b0a020604121103030d 59
    0x86507a0b2500f00560b03992283d401907640643c01012242501d22440e046440180c1e050415560360302c03a91a0004082001aa2208040d03080841d500d0215000440351652140302c010704120107110341810910f071304000003034450261000c00354640c0344401c03515a08a440c003649c401d148000929040c04007100c14600341c1100c0ca014010404150643c0008000100034019485d880b815180c0c090a00c901c440312510469485468040008001e0700c10581c0038000c4c100c00003418807542410450b0303403c440d0a14641103000012440750741104000006980503564181801021900c81414040c0b8052444000030524440000c0c04000c12101250048034a08040303400c0c007400c01214142c01c118a4440c4059030707544410300c10740101d10703072200400200d2030000e816501018504070250b010b81d020060041c0400c0d80014260113201400c055040c464218000642414086036001500b01d12451090603086101401040103200c084c13001661541d900804403940d45c26150fa92001030844917103160 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 918807535 1250 918806285 918806297
    0x1a010f11120a17011d040512030f040210110601050112020d0905030a0206011a2a0a1226010504200a230712111002040e0604110f0715110d0c 62
    0x61442504105070f14180c030080c0050b440460300503852080000c40c0100183c50034403c2a03100852140b5040041d4010003603008840c06519081c014401d42880340030144003004080440c0c4032030700c1da02103846410350b40c091904a52190068540c40040d000d008071181405140603440410044000001c0140300e0403502507401c1c45ea41e40c0035040344002e40e4030005012917001c02c8007680c0603441030070b40c0d40c0d0301c030304140e92150010542003206d14110101d4011121034002009040701c6130341100c01400c04000480001d0444411303c46007108041040c81058022600c818040c0d4000700f9200480c403c0c40c01400b43c0c5034440003d400018800400740a090040300600c0090040002c203810890f1a59030700070103c01950784160501b19220216641034010501812486004001319070004100170550800c00b400541810000c10040b140f1500c1c0c40038035544108030000b5481980000c0d140f12035041a10800c00102000514000d003d07013449032203031030500180c804507400f0780340d10658181005941d0300d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 918808785 1250 918807535 918807557
    0x60316031d0102211f180f09030801050103110901020a020402251a161e030e0717061006090e060109090501090e1209130911060307021c02011a010f11120a 68
    0x5501c44080109031100303901c500c0c0c17806112405914098070040c00b284a0300080301f10103818120b0440303900520031800584240010041c540e80750084c1308025401e00107862503c1b90030f000107955840b000400030300664010a01900c200281c02d110100d004841c0740c003e0040003280340036161420080e589111201445010650040c004034007000e031302c0001d4a9051201c1e43c802c40000c0114004070900c0c1c20107464000d4220407910511081c030040548011000c80703250b01030f07880350920000601b14401c0d121400c0e420000240c0c01001d2004179503089441c024162162001243c1101c4150002820581030100018942050360700c031038814840031080e01c40111321f002800105200d48162076910004a0a0990384100d85600000e102c0d03200744401342d0000c0030b01001ca0703030300d8208443d0940943c120170141c10801e5807901c207046844007a0300c02000500d141640d45248109410511070402804001300f01d10341c1d0042c032070310020f1a05501100d0f007504040240c018580d20141030580015030f00301074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 918810035 1250 918808785 918808801
    0x9151008010c320906030901201209150601111015031104050408090f040f05040b0103140a050706110f0a06061401080c03040809180a05070905060316031d010221 71
    0x2c201c0548112008641c504140c0e44c00b0002035800103009100c041d50381e81107980843c4103a890300c0486c0c030b100c40042500c3d101503895040c131841005044400980080c812101d5198555038070b154440f03000d003400e58120300001b402900d1302c1d00742050803003c2c6140c182c105850000c50020802282c0c8104084100000d0720810700c002d60310103540003400000184043d02040ca000d0080c2045240f0140c00020007410031000c0d80f0642d0400c1d0b40580b05ca20b2805c0c010300900100442c0030020071744410080003824581c1e40c4a55540010348191010480102590307030600c4002e00207404c140160070103c800d81041e905001c0005c0020f445200700070851600a08502c3d40141030103031060b4041c1c030b40075045658544039130036968841881154003240018074109a001c8003540240600150a0002202d01d42170001800e45003a035000349115400c1131003000500c0f0f0384190b80c40c0c00e0135824540840c508010754585180c250080d002001c0300c0d40081020140003c103d2910008113200041070415511241d074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 918811285 1250 918810035 918810107
    0x150c1b01021201180905011409070503190807030c02060307031b030902060d02030a09020a0b0406080a02090609210312060a09090c0308130b07051e010509151008010c 73
    0x5070b0340040402000041104280c0340c0b800704c2e101d070408040801d0100c000d944646c01c41d02c440d59030400c070850032000d014a030382040020034080e04098000301200c404c90a911440c00d403031188000e01c20400007410f801090301c1400c3c0d0041c42c90303020b02100d40380c1c2007082d00035029002d40303100d90804041046041c0070940c1300f40625071520390041c1600b486d00d28101d9810000e984024000c510f465259540c501c0140c40302603280d001007082d0701442d40c81e5414000c0c01060300034013a0500c20803e005100c801415a90401283d4000340c04035900d070014030304c840100c142465040306825240c0008940110310040d60100c0920407201190f20a41a548031141d4400310342c000e480281c0042c0d2010000d00c009080c0794010b201404151004400c001c3e51801c400782c46a01c0070400703c589030820010500da00700f2020131101c035100f07000000e0201c3c2c03416001c000d42e00c070f0800313481d68501000070f03002c912a14501c60660000d451000700a0050340700000003c0c1c01e2456042914251442d0689103a8141380400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 918812535 1250 918811285 918811297
    0x40e091b030d0e19050307060f03140403090b031503100c09080d020a03050a0e10030905150103110f0402160c0f0b0c030a14160b01050415080c060c150c1b0102 70
    0x1e00c41d41d0355042c4240901c11030b500700188124002d442c42101190729a4208203d40c010460349e80c4450302004001d800509a56900c0d0103600700d40036203812302c80081d801c070340b008040d40c2c1c04003101c50f16582c1d100f43c107501c40000107402c1c503098007420080910307503c1e464010380074000603030310703032040d0150740e8040940e0707442401b4100130068205d0316a03100028482c400500001c20545402d00c4000180400600250100e21034100440d03610071801040000a0100429000c0f01d46181501903141d521240c000e0004440c5082c0303c2c48210101d02a95540c075415a40c140418400b0420b1441c05858040b00c066124000e801c06881c480c600043c1400861003158451881c1101842c1031500151041e2054442c44480304a075180500160480c000c08401c441915409200800110351400742400102e41e080b4240c20484a040c0740c0a120701403001400f010355250545420b9915000c2c81d800a0502108d41c1d5031340411880706c814806600305800281c03014880c030024034000501102011800c030300c41d80d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 918813785 1250 918812535 918812537
    0x2120904091e080d0b01020303360d02160902070314030702030708040e011a0c030415090e09060a060b04060206011e03050a060902031006080a14071e09060b120c030a02040e091b030d 80
    0x500b50340c801300c01d00406051100d101040036034101001206500707080c14030b011940e00c010f900dd900101c1d030100c20040e1100003458014030445c039081c45038030000c260229078503400610090000200d030b50b01d03108100301c0741e010b41c010003a00e0f111602da01c0202e14640c001e01c51400f10302c42c0d040000004d01c1e08502141c070061051401103150500d41900100c009032003032400c03030900c07001c0d1100080c020100c0c103da910882e1000007404881c6003024045003160403903000303180c010300c1c288418040960005107690540303214500000009a2941048601302c0701504028507601444042a041180d0394100c21300740c6108030300352545a64010360180842d1514421866030703030300120305c00b00402c1444c000407100030510002d84c0c1c1d0f01500c410200010742e800c140c882c001100707000030800016216200b82d03800340000c04592850942050803800743d1002c080c4c020b1000304000404600040250380c11240140790070000c080c03c1d8a8a510815181c00070101d442c890422841b01415640c503020541403000307205 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 918815035 1250 918813785 918813811
    0x1a03010c0e01080a0b030307140a0c080f1e070f0f0e07082401110105071706190e2d010e1f23030105090a050d02120904091e080d0b01020303 62
    0x2130214a20050130030074501e181c040c0401c100c404086981d044034058150500c400030b00107641c00e441c000e89506507550000d05140c01c20425854101c0020462541e40030a90001c02a100c0c90360780f8843c200b00c601d600600ca000c80705da10004884282c480c0c6101160141a9a000c1c0d40c0d480c101c041e5003005046401c03000c02c41107900081622082d20030640803048041c0340403190018090084c0d03084940603101e50000c180080d80d03590388801e01c8600d65a2208068500c0050901e071038004820441040c0109005000803000203100b404002160807210201211407d0104502003811907052000303008020280d0f030301030005410040e0f01200b9030030070012040c0b550f0700b8a02d0401218081c50044812900a0b4030f81200e0000a5600f4000c19008159031409818542643d141417450500034250140542d0000e21313010400b012001d003502e001c00010b98001c0384e200903d2a041c052507807180f02d0800914035401d42c20052001c2280600344543c607030442002110142401640e6900088640d4071304070751 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 918816285 1250 918815035 918815041
    0x3010b101716140f161407080f0307060b1503010906090f151401091706010e160f0f030f020a0e0301061a03011208040512010506040612120c080d1a03010c0e0108 71
    0x501a8000c0c048000040c05040c00c20300007500240460f07031641e405913207010311090740d5100000c081c1f08074002043d10400030015580701e211010f1f01c13070040110181840396543d82609c481d4480300c030001c40011440308040d0340e0b076840302400720081140740610610145405a2842c08126910500c418918440444105545000051140008c10780200360400c40fa1000000300e5804064000700e840f0090005001c080d0305040184a01150090084000075a80b11017070421603080071040441c0c107a98907044248155000c0281c0140c01401815034202d44000340103c10507a00c00310083c034400044009106066540b01d060b13504c0e055024103280d9650003040100080281210300d130445034490380708181426560000a8204050341c284001c0e265140c0c0104102890b05100308000341444c800000b0302280c1036100c141c101c0081003410028040c09401030001e00072400140c8035003011000c4180700d03901241001d044540c9400103680c0c040e600300842d03840c079180982818000010182e4540c0c009035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 918817535 1250 918816285 918816317
    0x10e0405100b0103060b0d0608160302130c0c0206030726070f0503040f0206030c0d06051509100e15040602011a0622090908071103070b0d090203010b101716 69
    0x4900b0712060605680e40b800042c0c5d001d484028000015040740700150140c50003c0e4242000840c007800b0300c1c5c3c0a440704041c03005a854841c14200300c040c103803001500780c1c0306150540700c2ca804a01c029501080c080700300400350768030200f040c0c5120400e804c03900c14040c4101c441070701a0000c1e04c4231b4010074085817488501610840c09140d019000f144d80c0d0318000280d4012800c241c1c02502c8405442c0000100254158039034022000140030a585040d04140c4c1c2c00d032445024022401c0300c0c0d20503002d48021441d40e5208070714100c030f1a0001001a142d201003842003c0d519849882628055400d00042a40704021544030085a0784040c04462900500145000040403400300300104100311060210302c08181e885150030003440b0f490001e5503032a42e41404440c11255002092207944090020b204031140c83e4281d07031070240c2841001c1340e85505480044d0150141d04241d5800444000d00105055440501440f1944c4540c0800304240c4aa420000071030034803c1d96000410300d1266802104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 918818785 1250 918817535 918817541
    0x607080105040b0d0c030317070f0903021c150f11130b03072115090911150c150609071d06030411090907051306030b1501170405030d05010e040510 65
    0x2441d001481180d03000301c05e94821086840f5608140c00040c1c00d4000c040e000802c0d40b4940f90040e11600b0030307020204461071300510203190b0340402401241110684200d55601840c20028198003c400c040102001000e030b4008220b45080302100f030b401d0110001401c51804121070500748000c1d4010001d5040100004580d8405040a000c005003440d071340c1741440c0f07910309040030140c40e68804903000086201c0651185141e822104110746003603180000500c1003040034a03d00400d41c4c0c2141c81c520300d040b060026000b110301d8480c0e64000da1200c00044407075180a91304c2003104454000e401d440e42c680864131802c05132808207000c2403501e0081914030f000d6019541c4184902c45c0741d00ca1000610104805000503179950055a0256030280b00074500303400402d100c80080301d410000343d440e6031613420411002030040c4d001c0d8501340c90320349a642d11400304800100358492001e003103401c1ca8a4090381d65404449140c000525020000c6504580e61014034080c0c0c3d0030400030600440c1071a422001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 918820035 1250 918818785 918818801
    0x80a0203070b1515040806070309170c160b091e0f0a030809041b0f0c1502030103080d05010602030703080a0e012c060a020906190201090c090506030c03060708010504 73
    0x1548001d2022400050a4000841c455034020322405288000300d801d025139800c0d1319104004604040c001402200780c00108554030008a150100d1842d00c1400d1000411140c54107485681c200001c0306095500001505c89003801c0e15518890250b9031350301d440c01035005085e1000c0c1d000081101c04917000c0360242081c010030030000d10302e01c60400004001400050181d20403914000c0118810809103054490580d11804010b4400031001301c8400051a401c0040c140c2414850440021787c00d001400c42c100c2005407810008540d203584038104011550040c000c01c40301c1c075040200212b02d203072000c0300b910002d40d4981c440f0380094407080244800b811140d02e900d070041d940d0f406443c844040c00341c415182d06108550b507001484445d0f4103282070107801001301284034010802c0080030f8aa281c11100047c88030201f0074044209004200c0c050f182907680500003110045010865012030b5000300d00828046089482c2a0455018151542c0007103600801140c5484010021414603801040b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 918821285 1250 918820035 918820037
    0x333181e2310050409060f050603161203030603050f010b130b060f07140a0b06010e0d020906150c06190b190b0d0e010f020a030b010207030f15020d1e11070b04080a 72
    0x40c02946940210b001c413813011038181c42c46074030740c1f116034032100a03403089941101080e00a041305003107010007540c44400c02d116202401c1e00c3c114518050520a0f403180018540c00025218052030b000c26a40c06000b102240600c5200080804000342e903c0e032040540c040c001401440c14000c14410206035a00441c20544070020040090341460905005c8500228070a026101260030210001000b5034200541280518004c047d064003517501c080903240e11030303800c685803511014209100d4120b0700070b000e100b0080b4480c040a101c0c00071500c052403a01401d40840c100204404481000407014603904082802e103100b1509003c2200320300700401020b10448030200d445091110028212140c91047c5000580c2c04200140744981c1400303601d01c8940248003c000d698150b4840024034922103500510011401201d8058420190103a07005c070300c41c2400402a40324900f034424144040d00040e0300c200c91510b01c400b600f151040b025510941d8000c03081d480c440c0da840e60740658560207084814 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 918822535 1250 918821285 918821311
    0x120b0105310b0d060906050907060806040e1c090305010c2c03071a3a0f060b0a0c031206080c0616020402071406070333181e23 56
    0x42c001d43c980360500000c4900c9900001183d50300e908000341110b4000c2c2103092260031080307080202c650710101e403a0b0800811280001d846850542140ca402e021342e07000459641c000440140c110380107500c1e0b00c2200d00902c002c0c03088807155001215200300410300c1e05545850800f03c4000e0014081c0c0169080d50080c048420703282c5c0721004c4403841c02451200300180c0d80d00087c1c110114050071080d80035481811000800c0d40d40c4554a041d45400f504100300803a9aa0f01d00d401d81410107400c030100a08600f5100c0782e0351038200714028201c1c010344200b80c000c0342c594080f09082a401c0c0c81090125408040906841502c000c01c00c1724640c0303e040724800c2031aa8007203044c00341e612840180012480b81000446401603030040c036003000c00042801080c5854080c141c003000e80c04440043c811102104410600340c03513032000d0848004a50402c0b1f20b056008402c0070200e0206500003100e919184411030801400c101c0c09400f59406142d5507001d107141c8003030345207103000c032007048541003604030b81c0003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 918823785 1250 918822535 918822551
    0xd0f02040f1104091a060405090c273307111e011e0509060f1c0203062404061107090906230610080901090606120b010531 54
    0x3103030581c0c01d1080d4002e10403500040800140b0b03c1407055801a0082036031031901c11700e0400001c1e882d4099881290701403181100000d40d038103840c104840030140c880c00c1c00038559980341490842508100c0c1468042d030204240101103803002103242082407405940b0300d600c8454800416082d4020703032412586444c0381c00c017452403651503044011150400d44034540450b020340c000102040710002500c1142401c4c0200d001d0a030354028112401d101043d145260340f111100001520392007070456584044646081482c88201603800842c0035800803039401898204070000000940c0310070105e641800410001000011300800170300210140c2c0d44e0031f840c4103d565094690036503a40c40b204982169031600304146070b18103103c03510150400c8004131801803034103001290000041c02c0006051040400c002103128500b50000f0300007640c03080042c0710b540c0d40c2d00c4c0c6e101030b00c0401020031624410a100082080c2c00e0010380b803070300303080c0d14585021560b040309428070400c100407110300c50b610349405003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 918825035 1250 918823785 918823811
    0xa0f06091e0c050307020304050f120303043c0209071e1e08040201051222050f0d0201050415050402131103150312041a07021801091103060d0f0204 65
    0x1624401500e10141c4062108070450784500301e0b405605a441840004e00500c503456a001094500b9105c0a54900c4200075a400001c2e07140b200540994440d07120000400040103c0f200b0100d00442d903002c40b00c5c1c155048106003c4800d1402c143c01840440d45240e65030142c58100071b0180c0012060404040343c1c0e00380042441820104007516010540d00c0860420300c051003002c4040b10405444d192030103040580c0001c0c4144030b03000182003100c40034400b107070321041781290340d0300b00c0086442654841c980503e4115150384565076105120300590765010051801806140d1103198081c04100b0341d403011003814801420081c0050ba04005058903010013000188190f012130101d0000f002c0d01d034a443d09495840303c140244450194210110b58541030000c1016134003902c13102c0072000898140203e480445005800001e0342c07042502404008000c0c42402260603100d4480c03042c85040c0107403150071005e01c401c2d21199000210b025640c0c0210304800c0c8401c00f4207200400c0400c030800c001300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 918826285 1250 918825035 918825041
    0x12007030b0915010b0703050a090803040602010605030f0601060c0f0302071211100906050f1804020d0b13090210050901031d01051e011406090102030415120b0d05060a0f0609 77
    0x112000201101442030a07841040841d030311490302c8000c0c6a03c0d41c100070750720050b030040040040c10303c00b001c210410224090075001d0701078a0194101c0780c0f641da5655000b07001c0c0049200709070080c081c109082424800108845049c0c4140352100d0702c100c0d046544109610610000550440c05010000700300c3c0c0381d40d0b9550304800d0340501100d04000040c0d00420122045c0700300c041c0d06100210004004840d004070640385000c440c10591078403000c0b800156421500c010034079a50040c80013038203070b0440040e0f030702040041100342c521010710004132103000203d403000c10b000ba40c00040d000108800520800017400c114006140220702a070039051f41103101d504501e540000c507512a07007007142101e01c80b01030118030012003088035219490004000202c088080a06004031000580176415074003c104440c02840f035014213a5070f4080c0d5150040c142118901188142414010700f14030610b0681c0527441400d80000c060695038882c84803c2d001080102c640382011501d4407000902959144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 918827535 1250 918826285 918826289
    0x6071209030b1e0106030903391a01050102030403050c1005042c060415170a12091809050d030f0605030316021c350c210a0e012007 58
    0x942d11011402c5007098101c00d4081c140c01005c10146030440400129510000d4481c040503a284548081d9003903403400000b83c0c24000c1c4800e2040d03954440c1e8010080520750070300d040d804484041450740d0721074004a80320701c218400078015031302070140901145004180007403850014208585041e0307495441007040c105e0940000d02a143c1d10340d07132145002c0711486aa6001da000c480800c00041c0f00c07010018850003d000e4402e050041c200e521f94603180400c881402e542e001403a01812480f0508000d11480307083c059200760b80c500700b80500600c0580e006181d50140d1010152681100d4444101d000b0b0034107451442c20341d900d5402c0080c054409000400945c0c041f5049035421100c6401407026640d040d1060b07001d42c03619030a607400890a02c0b140340c2e000b90300c4c220704880003110366001f100d650072030717080400c4254000080c0034a030b28600150084040c6445003182e01e4030303012856000e40c6030044199400c04501c0341850050a51701c1500c0c14001440c80503090f0f140c0006504145207014169 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 918828785 1250 918827535 918827551
    0xf0201062d0504061206110f0c030a140a05070b13080a030b01030513050c09070507060c0c02130c08070c140303041101120203070f0c02040209120c01120b06071209030b 74
    0x591071503803602100c41040c1002e018181c90a120540c07038140c2e01d4000c103a0b90900900719030341d219100042c004041080f01d45030354002c4001a120190319148940b02e920030032203607020030310a40d41708075403102603010f0b035034207108580716103040c00f00985400900003030080c0080741030650b10000d03c00091109000d41810b49056400094140092002400700c50300500016400c100182d200d00018000164007010004180d40000e00c030380381c555050321307140542c810050406040081d4401d0095018456a0307001f4000c44a40c00d927980314906800c22a041000103030300007040c02000800040c0100d40c0e14414501c03c014075048680e00c5203090741036070030984c1c00f110a00046d105a4080b50386c009901c140071414003004500e0742c00d200c000030f0020510f641c850000d014265907410295503455040d00d0700c0110152000345411302540300c15031107003000c1d050940401d09050b0030410720440c600c6007814540300030f8100d524080841c2c0300c40c4a00c9207810001000c0204040012000402c503405150041402c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 918830035 1250 918828785 918828839
    0x27030607030e150919150f051b0315010e01140708040504060b0f04031707020315040b100806060904170a020a1e121101060807080c0307090501060f0f020106 69
    0x580c02541004410070811055812000500c410740e44e011481100781c844d20000c031110ba0a9503c2c000d0012801c0044004040340740c900d843c90124295000144500c001c100c0245510b0038070002c02903140030030307a400045088032441d42c0c09a540a007064040603141414002c0140008030000c0020f68000300e42150034050200301044a4146802001c1c01f41046145581c02d05c81255400002401580300c0a0b00c222842004a0541010355080741c4040d074020303095070606c48000c0b82c842c0504005840442d140c40c1c0c0400040c40180c0103041e0350059401c0314010f81140c0d101c08042281c00d2001500c03e6030384d203843ea00c2d030b510448208001006020101e80140c04d41000d00d081c01c2200a000c80d0320b641c500c0c2d0030081588001003c40c248281e0a00303140c24000d81101c502c460a40c010040381c2c000305400d201d24400403c90000000c0c00c0c10521b80220216126503841c0c49010050354400c0c481c3e803012a29510305980c099020f030707913040f91f480e003203200000d213050b624000c032200c1c1d0900c2c1c0800b81c60008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 918831285 1250 918830035 918830051
    0xb0d0212090f1218100f0f08010506121518090c0a0e011806050604060309110a0b0703081e011203030e0c010801090908070c0303050909010806010302062703060703 72
    0x10040d1000d680c0072240c0005009400840024261100d0100d810f08420300d4002071344a248121001ca07216829201a0442202c21114003019207486004604900401c0d40b001c180d030301c0c461103000d40a05951010f03190714189881002c0799003031444003405a004640586a00069540f0350f820790801521074041c420b941800c200a019051100e0103a459000d003034400c1c0c2c1030000d950340583c00ca0440742c520115410b00c80c0020101c0c402095203800681d0700c5000002c002500703507496000708000900401c0c0e9400c0608020041149203403040c40b802e0740c282402d00160005c42d004541c12540324214038068540c42840003003001c1c8a0703100340c00c039804607811402c3c0d010078558180300d80512815200d00410604280c030001a0602205200c1e846541762540d8003901042840c60039501440d41c0055082e0f4465280d02c0d025000380c001165880c01401c070b40c00000b03101c0e503000a203941240e80242202d445c09418500701a000c00c0060180403004040000c0318038503840c1000007a2040d4416030340058400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 918832535 1250 918831285 918831307
    0xc0221190f0507020909030d090302010b030c040b090a11040f0b0d05070e01200a08030906041406040f17040b070f0302010e010b0117070306081209030105070503010b09190b0d02 78
    0x44201880040182204580d100719400c0021a40850b40440380000540d41c0c9842c8945148140e070b6080506e64205000301081580540083d01854422802c1e54081c41d4008280401c1f0707008041620381c00b08540c004114182c4050b40510280c0340504600b6280544802511000702c40390343c4803500c000c2000403121082c035030324480c0c1500901d181c038122441400d050002481c1c0724102c110b0139400060f5103000164620200b00380529554003d04164803440c000c3d030b5064542c04203c42c190344020240c02c00da481c0b00008103c01d407107640d004c1c2104a4480741030b1102d00c401c1019580040c0d01200811011a0120002014106e864814040200241c6052600a0950700b244802294507810003481c0006607030403c1c01c2440507000c8030000c0c0d000d681d03241011005803190b03030f202025602030404003c441c0b040c071b0380082101101c190000e00150300c524400f128035200034454025005002d0115403402e06e001d504c0302d043d09420300d0a40c00c00b1a264035400c61940e02c0100c4031040b6590000b40c0c8201c070f07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 918833785 1250 918832535 918832567
    0x110714011508030915091008040b0903040f14030c090f04151505010e0604050a03030c030f0206130212070509070903060e011808130b1306080a1505040c0221 69
    0x2141c02241d01e10005181510180d41c034080c1c0710390188509040083e0f20545506441960501040184600115481c44601408036441541d040d1001c3c100500090035409002013250f04561151035000920340c0380800c548504d021002125030701d805580290742072540c810041a00445401d08d0502c4281072901d844080f840d10341070040344450404882e5905149005143d200f22003003801c0204040c003c0c0d400080662040341c0120b40d100f4540f10000c014103601040c0d601f4101e2294680100701d441a050a0703071343d044119940100c08801006a40060034420305507454101c480044031035a0b0744510000d13484000032101800007658101040007441244d004680e6120002c06c002c10441142d080b034641d0565448001829080000403455515070740c00d00064010803035480c0054590442100c1001500968401c0900180b0300c0c0c4003060000100c1d1141c003035090300716a210740e503061808041c80041c01031f00c0000301c2940105031102d29403144034240c0007848140c0c072500642c1c1b0441007240e0000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 918835035 1250 918833785 918833801
    0x3060f15010212030a15050a030f0308070c0209060d02030f1213060503010e0703090503070b0406020913050f0f0c1e0403050d171f03050f0105180d051c11071401 71
    0x4551081050b404144003140c11260410a076400c04504a00004008084070503035500454002e0000302e23001040c8031000900d184c62a1180c1c0c3c52030000d8a86403c00c940b09107500310069400021b29010a0051410700003601d40c0520140c2518200b10001001c1801c102a1060820301d40340c002442c1600c0c034109141980147c801c6051240c1594142014443c7d487c400410305814940d80302d0b4040c0a200b410030540c1c4555905c0000300c07142e0320701842c20310041e40140002d00d010b0502e402c49042d99500d0760007036900c40c1103e0030441d08240c0e10507104520f04071000e01880b885c000104080c0840d41c503810004094030140301c47c420340ea0f528602d08103281004108401c000c01650000d0f944000c080602c813242c0014550462103c48030402041d0085a1301d20b038002440d500c94000c000d1040da4040d04284e102d40f07103400d182c466480c50860215180c000c0e0540703000000300e0411100f104010303d5001e510000350000710005200400c2119100240e0210701d05a901c80c124030150f1021900074012404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 918836285 1250 918835035 918835037
    0x90f1f090f0645030303060f1a070303051801151a0306030a1203110d0e0f010b10080417040e040b0709060912060f0203160306090b0306070f090503060f1501 69
    0x22000703c5141c481840300081c00300900a50300107401c900402201c0303070740071a1030003912480d102078580d00c0c50090300800d02c61182d5200c05132a81e10000d0325034264128240e0445110041074686851503400f1001460000c02521424003091281c045910091107034140d200d001143c107403416810f10312241902102e128004041341810001c00c0034588001c07400742c402540c840800702034002801410b60141403000080810010040b07000350b181c088503000007070340c1d86c003840503200709003840d140e02c0307090301e5203e044241c0154415010001c824415003540d40e0050042060000550003840c85450580c1700f03070b01071301d182e0707442c60705100900c001317408040c1d000b150728102030314040d1170606d01601041c0b5922800d110110750100d80c0b0300340821f07034100035011400c00c00119580c1c944030a81031401100c202041e4002890041c0100c0d41d5111407041c031140302030040042c001b070707500c40108403481c4480f115080f00300b1442d8000048c0c2c549003041110700580003400185061f103452030000054038041c0103024 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 918837535 1250 918836285 918836297
    0x706120e03090a0b0c010e010c03060617090c0f130e060f10150507060f0c1206080312010e07020708030a050d050f1605160c0b0403110d08090f1f090f06 67
    0x802c10341e50f81a841000c030303031401495585505020145a0041c6041515a0029400c01d00d0401c0680c1c5e0540c024015a0b5054907001c02c8045c01800c01c8000880454004003268084400c00c4d450741340c0301d800c1031115040245070b0480c8640f402003100c140e400d14103507079a0a50200b4180010304200d141b8040d4001001c103620084140b404d080c017913102d11111a050f040c0440003600606001490304019050745041109100e1548030701001040c031040e5040f81a1068608040030400c1480401200c0080c5141e030288100359082c51582c40030303080050100e50541c41800d8000401075010300c00390100b102c61751105038a9610020901b0141c440c003c04e24840c140001d8100800740206c03d60740c40c41d880030f92408940b10148081001c044464818002c1c000c900c44002c005411000d81000704141d03881104000c0c1c91010103001d101c03078813080020003030038840e0034001c030031303c50500302285042150b000f00015002108002078612170010961a400000e500201c2440011000c060250003492146812 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 918838785 1250 918837535 918837547
    0x40b041a270a090c030605130303050c1204140312040605010302040501050603070c0312060b0d0501140a03020307060806010507170307090e150d082b051e041b080706120e03 76
    0x1000d15020000c08005082d41d803809840180602c59200c44091544880208014144800191080402c6140840000b41000000307451031400b1320079035808115900c49030200d500d40796240c065481c0180760203201480103110001c8072005103051f250146000b4003000910f0350440c010b200a581058001030f0160b201002403000140d4071420f80c08400741c0502c4c0400401da811100130004e44400e40c8040d10440c2c01151300c1485147d546d12040c101c07054041441710543c440f106100c0781081d00c3c80701942c1a0084102048100d0003500718591203d41403410a181401d50703a240d64034400f030411070340100d01002c82001982c5410010900292a0087c4408680e00d007484005169000c182030f5103016461650324241082550800e450b1005d000e210902c0085101074a00004d41c00b420140552690510010560440c02204500c0381c105040401000304e0303032251034140702038074404110406001e10100c0003403208024014540504080c1d81c450850020b10140d21080c5c40740c13656581201c1d0800c01c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 918840035 1250 918838785 918838849
    0x6020114060d08030417031807120201080115020f070f060809010b060f090a03060f150e0613020c1f0f06090b0603011419091e051e06040b041a 63
    0x109559110b4081e036a0f0345e60b10300d440080d02e2900788181ca41c0500200a11045484c000501d03080b20803407d049a00300c0d80e88507160700701841040c4020740441d40b9100103000105071300b041d0300315107001401187c2600b6185400c036460201e5661003840c205910600902809600c001066086802207009000c10b010b25000903045100e1415040c4a2010000d10942c181d1240219a0021030300141d00304080340802c4507102c0900001038506c910320001c15070202e2850364601006010308000ba10a014049902400800a6001e0703c1b545485100d4418421140422a00620302c46a80c141c0c000c6030024502035503d081d0340c9103801c80d07010385003420109242522404c00340d0b41100c950031040503149e00c020011400203596a1062aa02c2402d0000490344484640002d100c00c01c07204003060f0045050038040007102d805032001711740e03980807020b0820312071686d480c420303000745000f8000a107001003200082c1c101c902400340c078005104000854441f0349484400c422402400c900101542408191 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 918841285 1250 918840035 918840049
    0x70e150103050f0928020a030c0806010e07020c091e13060c03020f12061809030901170f28020a0e030106080102130902030403050d060b0306120d020a030e06130e010602011406 77
    0x6050035041071640407902840c140e140e0307100035068025022101f201c0e12030900a50b8440303d401200e840c0e11802000045960790117803010f00c9084654098a940200d40c0c081100592003e4040382002003182135828048900c0014180074920341c0c0c80c04144001d00380f43c10800e40d090382e1029402d1510600c20401c250003414120303901082e24059800c810341d508000500c0740001f210441400d06002c4c0e0030002003140000c01403003404000d0b03d500c124044081100c40101404940942c840d4003a807021070400ca00254108071110300c402d10030b90314100c83ca01e00c082207030002c00410000655105180009040a02c02c0d08068490741740258581500e641040085014621a404c00b80b5030000004080c907200b0300070307507041d498050350602c101c558134a195001d0b82c000380d489510034000c20890048100700000c42910342e40030380e000b9082d6101580c0303040e80d24180b00c00300c16801500c01c0000300b8851819030096006000c10046902844d410100000d0840c0c4c8400340201c25015840c09120715592055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 918842535 1250 918841285 918841303
    0x1d0a1211030d090e370e0102030105013c05071a01150503091213060f0305040510020702031c0804030216141509040e1e030f040b0c070e150103050f09 66
    0x2010081c95120102ca05811250203034021514140b0a1045c605021105440c10503240340307540180030a031680220607080b448203200d8580071404540c1000b160b4048500d00003206000207140c00e0400d8800780c082550000c1c402d4890b03000a50005e000701c06c101e803444603081400304140041c2210b605081c904030000f00140e800703100340310010000540444080090101d504200c004090710348426046a83d0880080c1c00b640c404101580304194080e48244510380c440c58024000349400030000440d80b00952000c0410307a054015808035420031100310b1150f031410001541c0741180e510341400e0003401c0016054116581c50980602000075003e1601600700d1807908542030404107140d00d081c0716161082000c920380040c1422410341d542c07840490001c142d458116642c19034104805106510b900c14003500f121110f50601c01030040004003809130040b040c0310030860b800a5110b2001000c0101e04643c48017a9451034482030a055915009441d006540d2408248041c2009115039840700e16007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 918843785 1250 918842535 918842549
    0x902040e04032708010207030e060a17060a0b0f090306090a080d1805100b010801080c010816111207120804030f0c02041d0313060203090306071d0a1211030d09 70
    0x8103d02c20780001001c00e000004480300c4040714085950f0b80015020f50031028054011802c400e003111210300f0524100c0d828103215503104001d040280400c0b901d0032802420700c5812038040707200407551400c500003c1113004170b0a04a50344503a50300c0c003050b00c3c1c180e00400240307140d00800314940c0040ca60700d050b6400c2020f41140883c0b06c0381d9051181082d00c5215401506030702c5000c0300c0e82e13041c2c4060b900c900e201003c2a1b81f5004503a88034000b81d607a40f0211011719002075210030015031180600640031050259a1a200a130400b092030114986080059405810440001c1c2d040800c90340789aa46100c0c0070364100300d030b00ca10f490b1310301402050340004800144216400907108660322540006240b602071407100410026082c09240d40f504004500c0400700100c8001044040c000803d50343c00d444020000d01256880e11000c403041000c0300c2d0030b44000b083c2c00f0080c401942c0d1750008c40c400307414075285040f01c442c0c00342810a101850a06401e001b40c210140c0c0d9103285030300c81080000e840b60 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 918845035 1250 918843785 918843797
    0xf0b0a030c0e091c110d05090a0618120c0e061815011107060e1203280908100c08151014071209031b05061b030c010f0e070902040e0403 60
    0xf040c000d036080c19074a400d000c032191003440f40707110702d950000313207403880b4280b408101c42c0c210361000e40540e400c1c4500c00165510040d504000c1000341c1c801c28242c009000e00202c03040107255100d207900c5004520b4442207581c9801141c0c01d204007a1034044071688444103ca114030b040b840300c1c01000101e100034090b12990030031501c2c0314600ba401034680c906506012070032a54090760b14000200800070700e01201c0e200d81c50407620030741c074800008240e81034120700386110039103480307100a09207902e0201d036055000e00040380710008040ca010701000051400840300452542c48030321004000e0080180007640b41c000c14440d0a442d070f118018958400410340c00c00d00031040320750b0768845031405503010080c0000d01c0020070a0307686520005160031640303c0c24903510758110030507044400c0300300d5014460b081041800081030012840c40c01d0b00c10300303004405407440d0620307068106007075651143d07441c0641d588802480350400400c02081d00105138080c011800c0c103080c01c18600d01d40402800c0a020408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 918846285 1250 918845035 918845041
    0x6040b0c0a0c0803091201050c2a01050901020a032d230103050c040c09080c010c060f0f060311030c0609120f0319030506010f080613020c01020d0f0b0a030c0e 70
    0x442001548401e81e0001c4030041c51541e155041d0ba40c907800300e48071701d008031101903c0c542e013141c0502031580600070740c1500e03508180d01c1d441c54201c07084040303a0003051017081c1503140d445003000f07104640c001e10340c07600091b075520306208002d01a40c08048070a0b1040854a805441c000044103401004c04224080424000707201c0d1407002d0b5001072000c3c031001e0031404c60000020004005851080300c40d00b51400d10401580c0300c03041d5100f480910031441d0036002030791607240c41d42c410f0752408503040c85903d0004582d0301c1c40c00d01d40704a98080854108039651451300340280440005d403540ca20200f200144000207015000c16454001c615505000380031169103040c1c200000c1c8400010085d40078110b07034441e0380004454502c3d906008115010038038110200e01554400c2c1c540411072411901c80c07507850b03110031041c0020f0303540d04030420308056807d0000902d02882030008002c0030758100b5011074500c5001f5048811564544135580c400e502d000010030004030710090f0703075045444082c00165265 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 918847535 1250 918846285 918846307
    0x6090515040210121d03090a06081312050d09060506011103210c04030f0b0a051332010516170f011a070203160905131509030c080c010c080708010506040b 68
    0x16200d10817169520b0700082e030b20a00000001400303032400d0440d00303440c403143e55078002d45a40c40161a01c55054400440e00c00104200342040f00e82d02e4074502d407091a24071150040c00c1200c4034110b00f02d0b0b0f8192500c0a001e9150f0f030150303032140b810001c136028518050a9400d06083c5140b181201c000d0b4494040001d4000381c1c80200740c400841d04104110351a0641d885d0030011640116180c035400c5245c031012640c090341c03c040c0350054070741c403a080f0340080d140241546803080c0b40b204400340c40e07240c80b081d644020400780902405188000203400030b41101e80005440000302d5610401001021402c03c000c11000c00d86103411200c40e18502103059242010a000500c60081b010390507115207a0b01c540c0d6110702c00c0d03c50b011124050000c0026444405460022400e9a200904041400041c3d861200100d5000341d400a00c681040e5940b4262683e810710550441d41c001c0320755940d54041d4908440c1c0040340b041d4400c04d107180c0761a0540c1080300007142406507020301d01c02e100c008900c9139410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 918848785 1250 918847535 918847541
    0x5010e0d0609050705100e0607060207210e030c1c08070c08031c11070203060109020309070515030a0b0319080f0412060605041503030903110303160609051504021012 73
    0x20350840824452403502e41040c0b41d0b148102d21135240103e4031031285500007881f4040c0e43d1004a0700800007880c119940d1600c20103500701940a80f00c49003200c4800d02061030400014283c501c0320f460b01c040251401c400c160a2150444071075014513002c001c851f061405500d9070000d07a60740300792065151105400c142040201070303045081d046c0303c00603003c1c010140d00c0701d5841840021590a020130284006186660f00889a0082d0103602000060020b034540e0303000303554441c404401304c40d412a07540c8001190440c8082c0e44001d111000014803102490500520604202c1503001f00030750074074940c40003600c51250a0141c6070401c00310b0f4100305090b0f44400c59006003019080f58660301c5090a06000915151140c2407080d031600c0c0c0d290b86a451449442801c481d01a20394400c858916120041701c8008002c0c80e60340350108114069030340e1808408800c80700e00511000945600628090b440e06805840c1808103203080410040160303034224040010349401c2c907080d40384040300031940c0c2c05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 918850035 1250 918848785 918848809
    0x9040609021305190c05030f070e0d030e0f0303030705070f080417060a1b09090f0b10081803040b0304030c020406050307080a06050619060507030c060f02072a05010e 73
    0x720581c95900a62202102e400690241110499070425200404010001c1783c007120b00c40d8012680070b000144400e1990340d01d9a0b4056000d06120100b1070400c400145101d0a1440c01c4001c515985010126401c1c00615103100c80c1050340154514109a50058900d009043e0020650f0803000c2050040003404000d91b002005c256600c00300c2001a0102c054845004941c4061307040d140410075841749480c00f025512190b40c61719001c03015424046c03400054a0304c40741c12401c4907161a91f5a00944a1201040401000741d07100305c91414149100002c40c0f06001c400201c0d41c0c070500081c044c011414048981043d41410694078004a0748007040240c00607a00c1a0340c103002c2c070940010f000d1030209598600c02d03c0f52600708003903a640c000304000c0c89410051041c200d544000e041c8446805000101000350090428004012440d5511070079280788200009a00e600862820200052450307500f910b0f90102c0300001c049a950402e40c91421801d119080c10000244003410803521a00e480713041c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 918851285 1250 918850035 918850039
    0x120d0e160305010b0a0501140a05070c080a05070608010608180c040c110f070e0103021504090203010b07030f1d0411120c090a0614040320030d0e030c011701050904060902 75
    0x4811800203400c04114003148400d42d0a5401c04000045525125461005442c8142c680c200c03c0d040c07840406a5540007006a6400c1c49400c100c140041124800c0300c0c0c6c010200300700207080c3d1650328544142041c00303a501207814014601c00600c0b1145d00006030560019a8125084485044441e42850981e00115180d00246010501e05900b540685500b400540d48001c03980e1101242c2c020680d05d51031480380c3c170b20200300e4030010300042c030302a428000300c010404445424640c4172107149040b40c0c002c0c2c0c011840d60710009511010150401150b66642c0030038203010064414041030f05100c00729120031a4401c1c5c0d9140e8a138451912032105841403030040d440d03a0700e940d00e049000c201040d44081d800034400c00c0040c10000726203210f00b02d00c0c001d101d0b00b1a80c00e800c00386559280c4124038003180354015051409a081d100d5034a0400a0b040300036450340d640c1101c030070300c80700703060070141c82c1c2540e5410042c200c091080e20f1000e0744200c50440d8000e480ca203000c0d540b9410000300511482600135 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 918852535 1250 918851285 918851293
    0x90c0306021210080c03031603021c02100c0e0f131104090e060f0c0a03020a02071203170105060a140d0b0a0e1006020109030e0d0c0521010617120d0e 66
    0x5103415401c02e0340c68442e8414070041c0e00710540b60052150b071044210380d51a81940104201441c811200518010304e902c80d00450301c0c40c440c01c3c185440b035032100000401c01644400c40d044d41e4440c0c2402410b0149080307003040701221003008007142001d100c0c106075900800d040300e030f09100030139a0760140411101c1060080e464030307200c07840c0304080c060046512103e07224050101d100e0700c0c041c000c0310f4061071515003207524000d1820390585c0a50003940f0a0010b50043d0100010071060118049400900c20b503034482c5814200818038001d42c42c183c00280c01210b05220301d58489800c107a01d80a454a07001003541c4924a0f003841802400c0128013060b04400341040014071a40c0b0002c080b4010441181c102440540f81c003400c9088070710102001d030008860014116050030705501203034009004370445850161600082002c00c0d03250301f04100034800013407140d100c0319001c0c070904005d000d510402000c4d01d42c0c011861550340541c04100c0b04002d40006501ca003280d8154048454512800207032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 918853785 1250 918852535 918852547
    0xb070c151514120307030c060f06060816090510051b0f1e030f03060d0204020903010504080a020c03030903100c1107030f11041b05090f040504060507260a090c030602 73
    0x941d9550400d11840d828a40b035002221410729182103c0040301c00c20100450606042e43c80491350f100501405507855036481e1000e0410030758a01840e00034100549a40c005400d050035400a003024042d142c904000b510b46040c0920303641c41c0513210205c2e0316460040c0e100c51019540300815248844805503070300c54450710802101d40030075180140900c611a880440041c1c8440a171070303100c0c200d1164020101040041c02525041c2d07080ba035400d0026100606085540300842c0c01c44800740c40c280e480103804240e0035105503040000c0b8104400580256007404c0e00000803981e21002da04002c403c0075181c5214a0700648500484d5172140c1120342220407107036507420507081c99070301d0301c07005d0702d400d6850344d9002c600e4202405038445980d00c400e5286448082d1a104407803e40003007840541c0b140800700c00d107010344e90394003425014070301600c0f0000b0740382400040540f403400d01c40d160203000c2c9074640c40c5460000d40803103016407014070720401040020251800505080c041e03080207101c0e504c040ba41e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 918855035 1250 918853785 918853811
    0xc04050f0603071e03060c03020d0914070f05180a15090e0106050904030f030504111e0f040509030307141209010203091209030d030b04090618110d0b070c15 69
    0x1103901403801582541c0c03421361103020020742681c0c50b0f1060004884103110400018407075600c049100d8000345401810b000701107442209560003100700f0344050403400085905500d0038402c01d0020301c8190a0f90000914210108411180e140d8180303c680315041c000a00c43c040341e81160307040061701d40f0148262070b00d50058000500c41c2001590a961134050302003410b041c080402401980c042d00c41c5200d02814500490140100910449510850020403811525021094449003054500c4034070400c2c0c01000340a0f500700d080c0e43d03181c802d80c1008188007980c03502204580c1c21810511f0030120303201c01d1402d080303100d10a114100c04c0e04184401004010301041d0b002d540102090812384800a800745803040d072030f000c3c004030aa4181c101414500916001c2d0b48402d034007810242003c80e201481c1d4461204036404030032101d03074580e60a40c0383c2c000c0090a844941d0070000c110354030001e10b01542c0311540c6581c40100040c0900030501010014002c010590190030403006a0030702c00e212441d18 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 918856285 1250 918855035 918855061
    0x10209030307080a0f0207061b05120409020703030510051c0309080607030c0201150320120f010e0601170703081b0d0936180b0103060204140d05070b09030c0405 71
    0x1c1340000140040d900004030b9480820640c0440e400d560359032044080340800b035440d03542158412103240c410440d000b142a010301d80a080202a003200c0183c031074140e4100502076840081c0810000d85920505000607030700c07042d501c0048800e11001c51104500d519064803042c15503000030b80144036440401c14007540c9600b048d03011005a6000303000c0081203c1c00941180d4040c0401850b0464072500303412010131152982140440061105110501c4652130713504110b46124030000c907035101c4603850b55400d400c028207401807100c2200e000c0d07042214010151940030500000b03108400010791540941004040c044910b1050740941749940c040484c05828120070b40700c0c010b561108015012803200040c1c5090802c49140b4070008141d074116031580e4000c0140b4910920034410316140c14004c6034649080d14003840c8500341c0140e445041404a0780346501b1404600e20880d08409800d0000c0c8020401c4001c80310030f906a141c032034110f07400007410820702e66840c60f00140b902c0200040c2c1d00d0400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 918857535 1250 918856285 918856297
    0x6020d050103110102060402130b1504290c1015090219030c050a17071b05010e070911120613020a081b03010302030d0f17280209010c060e01020903030708 68
    0x20f09404844100300e001683c90b11000c6401079440341400c2c500c246001d690380c0090982500042c54807040c41c603c2c40340008940c1068000201448001403d9065212908424080e45045041c014113258021341c4003940d98031902000418035456800c1d046520b8040c03c0390320090701d03650a055498006440d0060043d10b0750088120010b42421000700c0042d002c0e208450a008842c0d495000340c8110000c0a286031502074840f00401088400ba00c65840070300301035400e0340c4e00c03031f60010034000640310120f860490f544d041141024502007e1500d03500d070075000c0f11002101c3c41a0031102d9030354040007806200c05c2d6481d8094440c000a184110241d0281002c0d12400d9074019195074610a260713120400c2c0024000250554001072614080700c1c0590f030341c2c403010f420500e01802090252103211400104c00d03141080060301402c0b80b1500c4003000112048114140d000841c14140706000007488a000b40c0c0c40508640e0355102c1070b098410080d0100c903011a80541120340d541907500d03103220b01d03a02074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 918858785 1250 918857535 918857543
    0x4050a1508060108100b03090f030c07090c170a0e010b060f0a03050f040c03021203070c030c1d0c04060333050111010501080c040203130b090f0d0203040e2206020d050103 75
    0x200000d01e698021134485020f0014001202c40844c14110030003400e07403000e0090351440c0b00b41c142c14003141c1c070708200400340c2940450181c5120ba2805242509072541600d81400344150752040404008041c2c81d0b95602c40c2135440003141c01c20b480c8240d1801010700070075180d00a040002c04922030787d00b01e0010100300006503010011552040c201c00b183ca05c00b074900510300c95044408002516041009902044001007030380e24014456644c9240307154164002c0b02c038100d045508001190031803001d0440305c0103812024510386401c4406210610031b038003420040c980e8a60a501c1c800d0140f4280c50a0800e402803079261020a4080c640c0d260743ca5480386034002403100c80b440c100540180a0302e812100880001c0180d004000200710103500f0091616161a01c1c03410311402041e080c0800502800401019040c101c0240f85800d02340140843e102042d503104000070000f00d440c0403035640d07001c0061048000700941c41303091034811017650107010340400e001049601c89042e25502c098122489 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 918860035 1250 918858785 918858797
    0xb042004060302060f070218090a020103050f060f10090513020408070512030a120e0312010519080a02061b1219031e0e0705300a0c0303050f04050a15 66
    0x1808020964940d800700940000043c0164040204120090300309a4030090111a45149560f07a203210481f040f100c07030302e1982c00382d09400e0035075805100c0d56801031565009032206240c000c000c40e150011160003140110002c00707042401d94491401c0d0005040300512181c850070001c200e90740030f504103008480d980d0185500005991510151408000c600c000c0078500701440000c0564154001105442d04180c6403c1b46440003c0148018200341340e08100030030043d41080700f4498401c200c00400f58080c013900310140311550000411840c0d0550441d070603039403941010500504400818140102c034419581d0401c1e02c1407005010705000c1c20000c0e000c0c1001c400911086081c1c0e030080001c1500000c1e0715101388602c02094001c186009071010860340c1c0542c1c1c40d40418602c0809080c20103580e5201c40400722001c0700084c8028180302d0340c1c0e00801c602841520fa003056240284002400d101001504594a4401c2c0d41034400a00008080407110f0741d441c0381d0b5500f86a05d00000400203a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 918861285 1250 918860035 918860093
    0x4061d041e0b030f030c1b151207080127111921110a0807020703150b1c12050d2715110f0a03090c0b1e030f0a020a0c0b04 54
    0x1900001ba1650106403600401c00c1280c10000d0012284401400c140c010314481e00d5008800c0940008110001e9501001000c074a050301c002010440c040c1c014041e0904a0420708922800c041000c010075800c111000503e1700e0300d01c189071760728410020904090f0300340701c80c064a10354000d000d05109070260584070040300681101001116100c1448989030b01c0107210b40d50700382d4881d80f0340359400980e07401115880ea490740c072844030042200203440003880e2140512080c500b41920b004525126550496001c901240c0d200001c5241082ca01c6080003404240313101460300a40000640300c07006620501c2590034102d40340340e003001d20003040d1100c60b40080c40c040001010704c2070001401d4494205414800301081510a6074000384c9a03504064445162341c0c0403c00c459480d00007051417042c661b5940c0309050160240d00203940c40c3c060441e9060040101403034280700743c250b0002c040d040041c0d844102c580306451400d4480ba0142c2243d03e0b01c4208000c0082c1c2c5540c01c4040c1c120481e0f0916207030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 918862535 1250 918861285 918861313
    0x11a0c15040f0b090d021005040302030909011401090b0906161a15100512070503060105130e06040e1b060d020409020d0b031903020703121704030c020f0604061d041e0b03 75
    0x40c500d00c0d0042c006a00c01007c4d12100310799603100c150494400d1046d00d18107500c03c800542c4080c000c1c4c1200b01d03500390503c1040c1c115a08500c515001b03140f010240c6080401d6003001a18a000c0e00400b0b000c0031125141050070440900e801d80d60300e002c42c09080d4054207281c80600c3d006ca82c10349015002e5610300804a1176180618182c039880d10895000034665a00e208080700c00c0d4002401c82418048107000b071500c42100741d09901c0260081454400140c0760407002c21054403100b000c0d039580d5400a828101001c0e0142120f030000d21016584d01c0d03900c207400f6183c08000c1c4101e50201560a1010920341a403042d0781e0007850700c03070070110120784800254111126405200b070100401692002d80d00304002800b806540e1080b0312642080014031148005482c84240200c03021000030320024190800c51270002060400c1600c05e03207940d07040c103085c084080c20a150701c107034403c1d00010402591500d6aa030fa04034980415110000070a824002d8241d90007030301c440418584030303005d00f4810420306 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 918863785 1250 918862535 918862543
    0x303090e010b0d0c0219030809190302061506090901031505011e050d050a06050f0a0f0b010807110a05010f140c09280b0703050703020d08011a0c15040f0b09 69
    0x1e2185000240c0c54500c1900c140c2c40107115074951304055000c0c07000d019005050b11000007013480d009840b004564500418003600342086202c0a080303490424510001103079002070f2466011150070304100c0c0780b03982c250011764203000b006800d40d4444000300000c81000b40401e00707845c42040b200024000c90b40c84074141d000c43c03001c28142c42c0402c2c0c3d4030745081029203003160f444850240103005540c0304100039129101510710440f00c41220020f0a030921031102c0841c81412608004080d041181800e0400001e203608000f50040041104914000c021810103101005100794008000c0140380000043e04001c2d0400312404402d00c410000001c8860001c00111016520000d00e280545183d03030701611152003219125011907004903001248400d06180105002c5002c0c6c0c54054803904c89240007890b1040343e0007100108071940c40104415030f03c0001561000e114410503031745480180f400540b41001a4280064104a210501060102c00103c1d955101c0c02562564241e98802d0409030359 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 918865035 1250 918863785 918863789
    0x903090a0b040602190210180e16020f0706020a02221a100806090c0c030f03070c020405150d060f0e011e230f1e0406050703060501020c0603011a041e0303090e01 71
    0x3425002c6034038010b110b40480c800748000640c48d80b00c42c84c0c59031410781072800300712050311907120503014010701c0c3e82d010008502034002000c0203214150510000039215600102d0003806400d00403000790b61046201c00405c60b40306a20002c10900b40c40444428114076a6207005003d620704804201002d40310300b030305d01c0c4650001343c4950001c1e1500c0c80415025403040501d031000d40030a11250311040225002035004a03c1e03540c03668100d81590041208403000644420448150f0b080716041c03c1d2902000e50f802e4580006001901400800064024041c107880ea240c0a519148590aa041d41c06940305001ca540c508200000c20181503101001d041c5100703111039040414001501000001c6201c66010311941c609081e40c901e003294101e4400000d643c100ea0064580c0204a912a41403141c40000d010900c01807660500d800c000c00c541b44410b00407107261044a4036016140241d140c201d41c000c01da182d03002001c1c00d51b40222030311a0140c6000c00c4000a180c40700c006460304524150b141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 918866285 1250 918865035 918865039
    0x130f0611270f042f0403050312240310050a0209180f01060201062711040303030b090c0313020607060e06130b0a2307090314010c0201050a0207050c01080903090a0b0406021902 77
    0x4003d5400382d07000004481d80d042d2070b0000450820000c00020000c0c130103040390702711455600d422410001802c074291410040c11036004000c045000f00c00340c0e0006001d003041041d0070b400003070689032940c4038006803044c44011a0481d03519100b01041010352076007680708080700f240b4040079036241c100482c01d0714000e20950b80c440004402100110545640010004080c00400142c04031030940440d00c4c3d82203a4015800709035120120301141c1000310f0040e900218490b613042c55490005040743e040c010381c842c017030702444000c2205010000a640401181c0003080e04642480c944140d19000c07c50300780004a8280c903191f008110303807110794050a04040140000412400001d460001d140c1000500da0342c100110300f04004003107440d2a01900203446010008104a1018403001e403d4807005001441c00910401600002c0381d0045105100201c0901e0185500e490714100c0034618002c01103400da0107000540e0001e07074024100e0082044603541d40a07540e5850f001146c04481d04d4140c080a5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 918867535 1250 918866285 918866321
    0x10518072d091b1701061206051c022409010f020c040e030d060b030f0a0b0307080105090102041a03090a060b060c120c0105130f0611270f04 62
    0x100c00740e040070900390400401040e0700e50111507101d29556510010354031082019a40e620030341c015080d4100d4038908a10b19091480014011914030000140140b10b060100a220080e110311004180c0040004100007802d0161140b075280d00005c00070030001d0103c1c030810703404081d0401c600d606d00c0500d0010700001e032090f0a090581c1c0040d9100c086400714201107010707200c16071035150354911481000d941040b004540700c0c4142c08042d401c41d501a001182604000d008208241e0350020145500101404011440c2c5180001003480c1c81e110340c000002550a2608001c01c0c03640550242c421101c268180c2c508805541d4007041c1a4030054510780e40310303004002c202021a000d81c221040c0b8442c040e202525025001c8034050903c100140c01031025100081d00d92960355013400b138190400c4100c0c5041030a02c82a1380c845666280740000101200e8844081d00500850b00d03003561034090008506c00c0351800f503024806a0042c442031503034814038070b186860358036081c20b104003414403546038862 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 918868785 1250 918867535 918867539
    0xc2a0605061804150f020f1804091e0b0c040b0712090f090212010906060c060e070b0706051e0c0d0b150a0908010e030f03070507110301050c07030201051807 69
    0x500030003001550007181c007400b51a554440031006910075405910b0056541c0004101c030b105840031600290001070040c44041c0450203a5812943c240d009210341e590b03003181160104d4007419024001418184915039445201e00301982e03048040d5221380304000e4140c0e100c40582e030060099015540c249a410711400002500d081e081c610310904509104a10b00e545d0418407044222b01d400401700f4540201741443e81c8560040914098000c64605210007805d10000910a00c20b0500c090b0010b6101c01004061180c107004000c0075003813503030199540360441d0403c0c0d0054171080d86c10017560808034080249542e20a04c203180030702e8101030b043c0e103018400c4003a44098050a007083c8e0344840909012000d080b4242d000300491170464690041e260301d400d001ea800c4981c4030700c95070b2030364104110071400c851003201100e500c11000e0801a450302c0c0b850400200c1424012407041c3c0540c81e26082c02240c2a900c6c2c0540082e13403103a4000e10140c3e954030100180082600540d0340039038004035003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 918870035 1250 918868785 918868793
    0x40b0105041505150d0509120f070309121a06010305280e010527030901091502160f0816030b01030209040f0f030f0e090f0f0601030902040f0c2a 64
    0x1400c0304200c40c00502c0032a07512240001e51412a43c4400c0010500c0012a104000d006001e00c55112445030040c01c0829404031f858482c0e403080d8250b5400500340007516208060150560001500482d801684078221a151825045d180300c0e04d8039498000c403100240b4290b2080c010a0300c1810384c0f112030316440380c0010b40c0382c404042040c8102c481c07545910700705d81d4009003442854481c650380d000100c40d500301c0c04003070300090b2051108484250020040c1d90000e03604503000d1004c07100a95021070504800030320072410300b00381d50301c40c0d04d52041c035000004050b030114403a0003e4076100300540da880810300c3d2102ca0807502c0340c0320003031906010f48010809454928425544503014001004c2d20061a642c2c0c04071650b0801740c102d003c21200d020301c800792a484180000c80b200161140d4881341862000200c010342c00420000104000100248ca544d06c07d07042003c074164003130028007030405001d0040740a03240c0300030b002c07002030340768554071509125041601c00c410f418030001e11031500450b11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 918871285 1250 918870035 918870041
    0x6060a091802131e15051512070e090a050a0c0302070c350a0309230d111e0f040204061e0309120215072f011b080106030e06040b010504 60
    0x100741204035036140781082e28116190000d42160200c040001782c103141c406514501701c2c0c0c2a41010740500e42d4460890030a08043c0100e414114400700440020303030784c01408845448c5030b0396241d0b40104540003444440d91258000c00d025613203155082c80804840c0714114100d0007008400350004104400802102e41e00304100807484d00b00044600300310204c0051005102d1a04a040d40070b0751010044c0c42c01d056000036010041d01e4640e224640302c1c030a815460301c00c169030101c05481810803092480402c0102d950351503441c203000d40143c07482e0b01026903c08010156096540c0160b54116100c0000d28040c4222000d0b9180b40d00c9000c103000d40b0080801c8170380b00c1607903040c00b85503540520780301146501601d05000d010300d90041440c1140907415000129001e0070080c28002418511902d0182c1030803110032105020b03060140854211007403601600c401000842d43d2711170390041c03848044d44039a003241640d40544041c0042e40100441569590f01264040c0108120308014030851810b90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 918872535 1250 918871285 918871309
    0x3080405010e0a05101b0507020f0d02040c0201061d0609180102162001030e1c021e0a02030f060c0d09210203031e040b0402010507020d0c0806060a091802 68
    0x40c401c002c0c00c0c0000d02d0480c0300c410994065124203921155500240902000004291814807103c0d90480010f480f6005003200240b00c1c8404001182840d02c510305200122a0024070030b00c203408841101a000700614081c0c510200c21107180f9920070340355102c1e41070055401400a02c095664803003506040800e0b0920b00031a550200440c000740d4803042a0440e00d58001c41c030408040303005595400c401c185886440c2e05050034440c40d039988210203e2068036039400300c3d10601018a407141d0890030217403105941c5c96158084401c19a2900000448000240c03094003145c1410491424150351803e0803a070031121804c00300110f84816100d504503184192144400d04078100100910701001d000c42d8031020016400441089022801070a9801b20441020020340307150810f0b845040d0055030040c0003906010000034454119290204040c610603007146d00d20030800d403126004d94542800361003003440307240d11220101d45107245100340e242c108909210141c0001c1e01d07030b09019183c5005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 918873785 1250 918872535 918872543
    0x1505010309020916021c030606080612070308090103090f05030909090609101d06091506060702010816051c0603110a051c020a0f0b0d0e150112061b020607030506090c07030804 77
    0xa044008456030b008041c0c1b9000389280c0c83c00b00e42c060600f03070002c2a020000340303030a225001000d541da42c1030310041601025030381c0154000395202c82c00301c01a006031407074840003407010300301001020a121021014001803902154407107001d48851241035903814066440d490641c001d03030300644050700150b1120061025101070b0080c45400603140700c0c10040100c036a065039802c10201c40240e0130940390b1075a80000210341c40c1e41081e03015000204824802059036081c024101c420358159406801902e07110369000418944528000709040c0c090300303452000f03c9650043c40034111061802400860a8072405008071207400401d0513070071840c4001c41e5040c0c0e081403000d180846e54044028100000c2e01e0300f218510b0365501c140b15082c1c215551500b80c07102a40003241c01c0b004001c1c1c020945411244051081e488410300784c01c10034000c208412101d8500845400074080c140d03004038032135200b408a62003c01c01c4c4e0b510310f414040b1102c07045a01c3c615900b02003040c0030000c5d010303050580d006805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 918875035 1250 918873785 918873793
    0x1309150e0a02160b07020309090108060c070b1906030f03020c0402030142020705010e04060b03180111130504050a09021507060617030405151206040207081c150501030902091602 78
    0xf00c0e140c40300f49800650b070000050b000007500042d182054040b0314010840c80005050910781884c00202c14020740718010400000c0300c0105410700d80c9403045811101c60550100080781c0d4902d0000810848880118094000e00500c4402441c1510940e4100c4d880101320500c0380c10800300302407250300e100c9440d0642c190082d540341011701d907a141d43d0780c40c180d03207400403c0b2040c10200050082c0c00016500c0d88160308050061000841010030340c0c0d0441d9451070680d403e0700e00c10341c01e05c0c0904280e00b040b1030300d40c00c0842c9103040517185032290411150161020082a00c503241d0200c00c1c0d8030034a0f80690460422900011010300100060a10b01c0c02610001145c940700d040103140c0140741c040a0043d6800480c05005600c3c00e0280c13501104602c801142c170f015031000710598070140c01840c080c855580402c4c1c01b130500c20403908440010050016000d450700c07210580d140201070f003d200f000954040c04001c13800c0e50282c802d1000b07030341c0c00915000a80da1240000c0a8071882010b4003411805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 918876285 1250 918875035 918875077
    0x80d0c021527010905030303130f05101401061407030f082208031b030f06150d020d050907050d051203060604080613021e010f0c06111309150e0a02 65
    0x80100742c0208912801120604030401d4000400107809900403a229030010010702c0851b204009060090943c0816070000e440020701f4103904104481030058040703424170340081131000400b181c1a042c0c0c0e106481b48000841101c0b201c0702c0500034101d0045c0400c1d85403d090300c526006142196012005440f100345812520725111003140f4404003c442c1c0c4640481400310050907000d4541500c01d0041d009411480d065802807480d980150a0758060702c20300c0e1004000c44046000c840501c4442101956660704410b103080007004110b9250180b4010084081071500e400d45c554407849403c40d001305040e662401c1649840e42c0f0107025164482020000050300380c2c1b041c0b10316445188540000c088120a07401808000e804000540d0140d410f281000500d0303a8100d410309141018a20740201c6000305490700c6001070a814410f0b10803520042682c019031128091001d0559070080800c0c01591841001c1c0c045182075030050420702c0203060001942000154007034000aa1b00716503c80340c03d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 918877535 1250 918876285 918876307
    0x318230604050a08100605010507020307091109090f040512043006090305040303080105091e060d0506010f0303170f010b0a0e060304030c050c090106120c23040807080d0c0215 77
    0x10b0a13a22030009034000c0708507003411480f41c1c881c0703100800003070803c44e240c40c0f0180d0000fa2249110300070004250b83e9a10310500020040d807e440c103040020f0500c6a207801d21004c07009556408880403221072203003d1113042858969401d45084403c00103031005c00c07000c110b070151007025200c1c1042003840241d15480c0301055040c01881d200a000b41c8545a13130b103086040c001d01800e0140c0017240203003414401e200038604c09007810900381c0891000c40d600760701c03041e000030480801600003038050301c039403400030034920400274041c02103c2c42912003820050003204034088228003160704240400e810401005403000741001429003800c20328040304d62075207081c0040c1c447d401c00e8600342c0c0054000c0e030562003001401c010281d1903010840d410245585020402030014040c038450105c180e450382501032099010f40c20000b43c4c00d40070a6114a4801c510201c10340359005881045864420000006812680460720b07007000308041d60f0301c0040811b66001d000c006011040c01d544041010802c180800f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 918878785 1250 918877535 918877549
    0x280203010608060316061211070f060204051201050402030d0e012109030f0c02030703080d06080316060b01090807050108040c0905271902101416031823060405 70
    0x81d0103162203160355410000d05040c0307407102d054000c51005141c000c0a008041c0c01101544072003050610110b0040e83c0d414203500366001e502c100402120080d20f036103040007e250058000d5074400d0b0340d90b0b89805000400503081e501c0c10398020b901908000c1ea1003101500c9414080401074060400501c140508080f801405890842505201c0e81e81e1604c5010581d01142101840d11545490714032038029030000f0b0f89a040c58800100140c00010b401306c054592504500010079104050760b803036200c1400d0519018544c207904903980d5103401709001096000d4800c04c130603140f1200082440c181400c0040d03d07540e2024105550701100c0d1100000c1220032401058891400c1007402e1181003241a541c040c107008040ca1200b1980254107802086c210700c3ca015000c4035012958071011412000d004c2d2000406150070114240c0000f82e80c294842c218a0011082d620950380c0701c80007150410b0300050000c81d0300039541450b088845da00c1c400015802c9515180340b0090a041c0342c01d9032800000c0d10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 918880035 1250 918878785 918878789
    0x170313030c060e10080a0507180b040f08030712050702011e0c020406061b0813050307060c0b070504050603070c111210060f050f090901090f0b091c0828020301 70
    0x1003040300341885200e5001c4088048004259100c00e401218821301030700c042c00003801071501c1a81d500000e00094070800405103000c010158418100e903c2e8000079205900c940070f03100300c400071580000ba200c000002211030498020389007101281d0f4180c8219515400040705034104040042d400c0c96120441c07085103000e80082d1911004100c540c41440300381d40250340110240100c90060071480f4120b080d80200c1164810b40b0203030796034095400000c00441d40c3c3c100e25014800c540d40410b84582002d80a03420314080c00c044050b07940c810400302c6940c4a2030003500d400010510105d100c142c0500518551035100b40c1003419820502c0012400d01c40e1003040a1202d544124408500184a4491600540348101c40303e0451303428000401c0039107601900860150710070308001800a0001c1d40080c036610740c440c40c4241080d0080c2000280c08105480001840c018031020035500090a0114600808103403a0b0348402d40e1846012440102c82841d090750001050350841e0700e09034170b84000c43c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 918881285 1250 918880035 918880043
    0x513020102120d0f1b0f08040203121c051f1a09010c02030c0409030201020307030c1716021f0209090115090b030606070506040c0614130b0906190305071d0a17031303 73
    0x1103000c0300d017500800d0007800700d078404c00740403008060201507100410032155042400425540e40c07000d01021603600440c00905108140c03401007802010024800e001703100610484a0000703043d1070360f02203c6848c01100b452101344504002400d100d502840340f01c01c501d0700040564031401c007004041000c0d03800310082140143d5001040011a54040c441d05c008a590361500c1321107040c90b0701c0da600340e2440c041c10030015140d1040c075120202d4800c0003050300100460700401c2484540c2038610020350406d0094501c550340550002c98900c18145407140e0038801c03540c4841000d450300c0c1018807180e10162080b50005002c22260b00030800c00c101d510b0180d40300c1c1d40300f01260751801c1c4000b04080341400d41000751001c10010b40b0074004048452800f03a4100c80700c440d950f4941c120001f241c038420162000c0014030341801078090190164000c82c490800f5840300032100c90380060000009414441e00740c0d114203405003d01180b0349402d1803040014104003201e15188400d1402c030354001680c1e200319 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 918882535 1250 918881285 918881321
    0x60108091f0b280303120b090406270305070204060e0c03180327210d1b0210020d020c03010c140706060b0408030319051509040309030813090513020102120d0f 70
    0x300b051b038000b445402e050114801004600c580d00300082072850081c0015021a842d18004101c81c04860321180746000520710814612246150240454204280a070311481c03410000284540c1c4c2c041010344540c03800c00d003883c51980e400400344011450342101d00c0261105102e981403d034030341050304600c0543c520003a02c0104161040000c811256034a540111849044015141c0800200b0ba241007540c1d05080c82e090299090705c0031101803015001e5406100110904103407500450103002c0740140e9401da4800000a105150036600342c20448000a00e42c208440c07900c20207003000e0300406106103008104241d035400c00c15103d070895040b80c4540c1d0000012712080030190b1300c0c2c51100e180790340e40030300880c949118100030500c419005580030f140d9070000070381090b02c01c550b20000f46600544540c0c44908000c2e00540000c064003980140620384400300e2004c1208403100352115505078014038000128003818901a0000340d00502481d440b041c0085107807116010b00304d10151918400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 918883785 1250 918882535 918882539
    0x405070308130801110426010b0d0b040605090c0901061d09100e090c0d0b04030e031b0f0a08031b03070507061e031a09060d0f0b060108091f0b28 64
    0x550031a0940080c0720035201c02041b082286a10720780c0003440600d80c1c80080c00c020f07454418000d0242036030120305c4e58844407103000f01d01006820100d09000c0e5000c0c8608111a94817030348002e40e078464848840394000e984100400000f84074140d400c40b0b1030f804203000b80c80c001d068400b08484000560300c0d8643c07400c00c2c0d40144005601402203992050201c3c0042c0654038005022640804400300084c04d6600040001811b260081b201c10b00102d401401715a4004141700e6098a80d611440b070280c41b800f64240641e2032440c02000d010140d0b03004901462400c5d0200b62074060800801a0001440c08280440d00104000b404840c0041c520350710b03400200c5520030400150310404c2d161101c240341c500000e0074850000ba00034600018010b407213554044e103030603000807103100c10a0001031400040d0b54600c42000444480c15000320002c0c2c0318002e081d01c3e5020050340301c0d110050f241c003641c3d4a142c154805003600d0703005446502c00c00780c4400d8150340c0c1030020319245841070314040006642c007502 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 918884892 1107 918883785 918883799
    0x1150302130e0f04060e0c01080a0207020423091504050309010305042303130e1e3c0c25020414040309090e06040f030503040507030813 60
    0x42080c607034030f0720a079030300f0003840700700e07011682c6509101300c114185800140c4220450380503102c035001903650300c241d135000350000c0700c00360790054442c03c11003020512507400002a182504569a031450300848242c50240c0b00c11700c00c0221b518400800000c101c3c00b20a071001c1d501d09103400300300c540342c5051145840003e50710b055803d4400c61f041358610701c8000010420b9284422141c01c0d03469846080c043d00d51400c8400c018400c60101c0c041012000c0320320b5550707100ca000c140307804907401e04559542111502e091000605448c1c505045954440ca80d1415803081514061601d0700031072907a022048110f0500240004005a00701011980e40ba0400c0e070008050f000000c88604e00b5040c0200070414a20441501c40d15102c01c1551050021071502d100d1a008109038103603051a6600f02c03401d41c4002c200b500c840c000c032072000c40010000401418012205400e9281850804413 = true := by decide +kernel

theorem cover : BRFrame.Cov 918705035 918884892 := by
  have h0 := BRFrame.cov_init 918705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 918705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 918705035 ≤ n) (h2 : n < 918884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
