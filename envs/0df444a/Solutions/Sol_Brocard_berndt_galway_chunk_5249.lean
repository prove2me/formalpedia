-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5249
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:14:28.690379+00:00
-- url     : https://prove2.me/submissions/badedbd6-cb6d-45b3-a47c-64e420e6b942

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 943884892 ≤ n < 944064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 943886142 1250 943884892 943884917
    0x110d02030610020316060b0117040b01030510020f0f0a1b0b0f1b031f080703060f0501060c03080109090c051302030901110307021b0d080a11010e01020708040501030207170c01090201 80
    0x130384a04c03800c4101014194000a0070000c141c0039040310201a0b0189004a8680074014401800340d100b69411075012410340010002d0110400004a40c1d1200000840c41d1240743c0400020760b1060420b03981d03030802d01144c01c00310340b800b07a0f4510031816480444c9908603041440c0c00e0204036800c8504844104064020407064074800008404459031241c4080ca161101050107020340f91400e0302c00328200e085080499507450500c1000d0045d0320030940407805030704443c000c00585405070012010440b0b11000400866404104203046a005c100d0000b034840d0541007007412241c598012640103010308025040061050740154415076030803000704900f0b010240450356510080e5203040059000000c4418007142c0021039810f5140010701200c48950260b0b40d0450a4104140d0000820303018100208a00380038014144107540700c10085190403207540d1600c906000d5405218101035000c5611010040020b49103803a6628114000f0345455031100b01d24081e00301c50208900055903049517030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 943887392 1250 943886142 943886147
    0xf0b0a03050c09150705010c03090b221e2d0803090a060204170c0d0c050127090e0d020f0d03050606090a08071802120604020f0d050c041d061f03110d02030610 70
    0x82c0c1d485a8408082c42072502c84400a031111110b61008880c07400318400d03034600088033729001c1c143c0c681e1a00d0000c510007141d4140343e804100c180114840407850002e80c0d80d5116001070500075015072040ba016160340304c03000b0303c41c0340060b070507c02400244001808034948048a00070f02d107404051048501000d10341080c4421072003030b00300c011b005092449061100750300401400c0f0760310300d4201d010002d912004940c0c01480c405a8405481c0c140e07244010b02d00c45000784100048241c1c0c40c0020326505034210030166070f5207050700c00c0d4001c060751000410001d955400407100c071968000d14034600a6107491185849188502c104480b20410b00b0354540004c2d1140280c031058801080060b04030341d9000305200295200a00206c00c8040400021100d46610b01c00d250107410b40083d0191210f040800d0340c00844030220300c4041030444079007044410764400c01c42814400d40ba010790070028803d581c040c0e0140c02e03001e194030041c2c8804620000700a20603400345114010890781c0604904201e0b80a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 943888642 1250 943887392 943887401
    0xf130507051005130308040801050603030a08070315051f0f180b0306010302070b010b031e24190b130b070b0109090221010c090f0b0a03050c09150705010c03 69
    0x4110350440601000546012540904416680d0a010f890452a080320b180e0f103141a401c2140c0a1101140a01c0100401d2080b2540050241d00a40c034080d020b0401600c0303800020442d40c00c0684504e0040c083c04492080c0c07800038000a485100c249210320390564015900e05054000035406480d50f0344051700c254641102c0402e42c05045c5042400c1054092095100400f20760505400f002a0030008403040ea00170b00900361101c403140c4a080008445880300c0945021080409500040c0540c01c2100303048015541da6001481c0d240240301000300e8030020280b9400d404c3c5901c80f800008042074410028140840d0105065140e10b446480d42810381c024204050580e403030300c0005000e24001030303201540347d6000a10210343c0303154400c46880c28101803110100c2d280d44444110b00e08903001031a942c0038065400103d16944e04054100d00c0e5230051406036020152202c020400741140e840440307118800c0038281d032040c0c0500c0700703c12038198005e440881d100e40c83c0010050712075219104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 943889892 1250 943888642 943888681
    0x50714040b1206150406170619140f04020a021b03030c06070c1a0c0a1706090c070309050a08151005030309130e0d1808010b1305250302030f 62
    0x2081401c0c08082d008034101e00800408064000008000e0462108010030141c401401c05554007481e99030030304e0400703204101c040c107024010303010180c021841e11120038040d000d940d001d00020644041640014004105c0c80904070380251001445100351039002c40d441841c5001c0d0820f04505602d803100b4182d4a100d50242a103240e00030b81c2c04280d034030303124002c510042c43c01148400e580b407907001441c104030f8005035542050504001020038515410a9102028100c06a48201a490b05c8004244038240080c100b0150120006100c010580248a4500506800381c0016880d07a118805d4669824011956603542d400010000d0950141e441e80c000c259103016016600b40388200301807280d2002c80510520a568540d94000f20845003002150b20701050b6540f8070000000c803c1d8140504212900400016418100d65a0080d00d0b8140041c4940704402400996640c0e540c2c02c880007442804e0084031000301e002602c242c404d0b4160042e5000703002200a40b00562036200155003050806503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 943891142 1250 943889892 943889909
    0xe0a060e040f020f0109170105012103140a050d150e06100e1302040315050115050f07081608040e222102100617010c051c0c0306090504050105071404 66
    0x201801420568001300b00080b041c1010794019440d0b200449288044200b0350119a5445004005090b00e10050040501d400f10301075007120181d490040040e2880052444092000180b01c80e105100710200d81103800e01000c20450a000c480b6020310300740d458030402c445030300070001050162403c01c00b0130b65a00641d46444440a0f010024800181c4a45411a0003070707900740400004541c01d1041d00404c0b41c0d80000002d0150b050841050081000e484140f0410409220f14040a440d060403241c41d03541111445403110041362140c80441c408281c01460654003140019190f0340b1846a40d001c0c0e0048640c418043c10381c00c44804001e00140340150901c42c014103419626050080f406c0101d0801344107640b210a0301d10135000984440e9809451440c10103007000b003940c003082c03140382e100c0c0c2c600d8a810781c60305546602c8100641c810b008411900c036590515056094001c0e80200024209140240041c7c07406041041c0202030846689000c02c0d289c400c2d030307001c00c1c0d21281202d08cc0c0d00c548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 943892392 1250 943891142 943891163
    0x71b0f0e0a36020607020d03020105040308090102030c0406030e07080106080a03091508040605040c0f0f0f0b18010f031e0614090405031917090109141b04020a020312010e0a060e04 79
    0xc0309a442e0081040099820420401c448400b50701e82804d4000701030300980001c5070b182490714008102500017000800d160b40b05200741303c5a41c1c03800003224111007181c9000b141c03180b0038200990030b24195600c00142c543c80c00c2000144440e000c2003074000c5a0103900c6a0f010542e88000aa49104441030103200151418000500041c01c40d4000c81e04070340148900411561501740d0301120340c250703400100d0551400641001003460100ca000b001c0c02d03008003410b05100141040e12261003818541d1414000e0080814800502c664811b81c8405100f206c4a14150107244201c001020035001d017030150341c070703041600106040804c0118082c95000d00114980180004c0910135490103414403401c000b042c0941d00e51207840030301c40ba40a107610500024004001b80340c04030700903450340c1d10718a01390004040078844201c1d6003ca071300c0906064602582d901682030f0200d0541c4140d181c0410302801a100101d0403100e8403401c070b8071500c4105800c0000310703112056002d11038000c640051654898 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 943893642 1250 943892392 943892471
    0xe0109020429070f03031b030e120c100501090b10050a120213050d080a030b150409020a141306090801090209190b0d2108060105071b0f0e0a 62
    0x314000421100c0b020010300b814100c8650750806001c1c4244820340002e03490342c8840c5008001440341c0c50718035406080030451283c02c2103590351111800c09000680c0714021aa06005810500500300d20300c3e0642010401903071104184801003081b4441240206400c1030400341e10390051003181c845104540b5200c40e0040040002400b80d0300044c0d003908400322100c00004e445c0c958039680040304d03114001d000d84440b0181802011030b6040884103104844000d0145140900034044505840040001503030380c00e0710310003d4a2105900001c4484c00000040302116400890000d00c207403000c2d544c40344c4107980c0d10a8000d0a8031082d02001c4c0d84071008101284001c080001000d002144c03075100031504040d8070001a8002c60301210548419444041c1146800d13803a1041500b2010b1742d0400c081e45040c810002041409400002001d04102100c04ea0003052a0541040200100d070728404c00d6644400e44c0e5030303541070240c0d040310308182010b03074400d0118003e024440804048070302441d00e1858 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 943894892 1250 943893642 943893689
    0xc030207050607261e03011e0506072d2a0f0504090f02031609050705030112031209020a080d030e0106060e1021050402010e010e01051812030309070e01090204 70
    0x400e130a41d0204100308401c90f0314003046020800c0880f0121201500c1398500741d43c0054031146c01140c000040d91414090085607103000c25119001e801680300d0b66100b03414004c040f031a04650039500c021450140e1700c00c0800c00500c0d445052070508401014842a1281175050b810425010300e070042d860f009018059030800e98081413041d409550203400e40c48030341d008641020102c1028186840004400f80240c0f1264000c0f04c0c1c001d441850090300c1c6601d03110500c00080341c8100003c0400c101c500050b501c010b5036401450607150010601c410483d5a80109561000d52040c0f080100c1d007007034401c1d410000e0600c1200215070268495401d040446410498044016110b550501c500750540c8540c03130b6440740c04520034140f80304000845080c140009040031054003003044c1004490000050780b44d80c00826101c6100031ba061a500650a90340011905600d0492840300d034440131040101d0000001842d50444000042081050741c0b1040b042050303110324064002440e1064203110f00242 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 943896142 1250 943894892 943894943
    0x30b09010e0735070215040309030201030b031f0b040f0e070e1b0408030a0801050306130b0912070c06030b01050c060f15180402090a1a120312070c030207050607 71
    0x409072800b035000c40c0290850b5400380e1541c10503e600194002000189a010044140d141c07203142162061440c155400030701c0f410140c040281019281d04010807180c40030044818031642d014140d980c8891651241d400030900c144026104504016441c003928100744141d481032180391014054442c10080c0c00801520040c4c901c002c010050346210314004000c001a00151450901855841440007001072401c00c068010a02c83d4000f04d007441000144d0380c0c113003405582c0c40100d02d045640ca420300642008400b40c130500700c0c020001003950400038100c1c0301c00c0a49030a0384040090340c8a500c01103409014049950341198002400324401648022a80c3d5001069100d201061043d040102e0500c90118002c40c0b410102c1009000441c6440b0504079803201c280c0e58108050b240d40254000305d0904844824025101c5a001030003003d81401282d80c1002c09504521060800e110028220f0b074144c0020740060150403004075130340c54842c0c11901900d800a400d5608000c15211025914 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 943897392 1250 943896142 943896167
    0xd0506010e15030601140901090204060815060d0c110709020403050307082206050c010f0b0f090a0b090c0d06060302030402010905190e240a0e190e0715030b09010e07 73
    0xe01008555060ba0755003003020728040c0c4400c2c041c54044c441180c0c280300110f58180c2110084c940140824404243e01c4030b03031a03902c01700482980f050303407280c040070030024411a48521002d41c2001c540502054000d070a8144084007401101c02c21170380c034202001280560302004142c1d410801c10300340460401d5010782056401d50180080b1000f001c0501070104401c1d41c42200071510200300240030300b00c2071040c4008283c0c280000c0c00925000800a42c000c120b2014261045003100045003a030141d5a201004c0b900700a040840c02d401c00145c0c004451304540040140d05041c0300c13012841c0b80c464001e482c082c0f80e0686501204c507080c1010001c0511500e80f244010102003038000a03400c40602c180780c0211800716400c00f80c3ca442c910510400e10318500e080d4040c0e000548100f0205544645050f880342c0030080d004020101e4150000c00351a81c0300d120310041c407540001041c80000f070b0055800000c40d6071410042011040c0c10b02400f800240b0503110602c0d0804002030b14680140ca807005003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 943898642 1250 943897392 943897411
    0xa03050717040506040e04020f1f11010f02030408130b090a030b04051f06080732132d0515040b031612030807020a0b010902450d0506010e 61
    0x141912400802d13000c0e00a6401607501c207902d4010701003541026220342046880c152800444c01080a110461102a0560420400000e0325022040034004c6d4880c820b020005032055681c0d050a0400b040f1580025681c56603c182d200d4002460360900002c48200040150060072064919140c0040401c0000c20a8855000c0c1360807640030304080c03842003030b02c038844860002132990234031801c585004001d03044a01b42100c07a030051070a004552051200c0505e56242180000c001500442c1e02505601500b0400078106101c801080340030380140341c50216080b41d91403880d1914192001036807070036210207002d03041c0411601010705058020681101c40a412070740c1143c000c50002000103c6544004010400d5119002c109640700b040d4540104d860310081000c91400e40320305517842c006104202540784d00080d0303407490542c1c541c841441c046a8005c102d41800d035410181402078403101488051203200941a030300c61070022400050f9541100040106a003031694006949001600010a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 943899892 1250 943898642 943898647
    0x807082805010510030c050f01020c0d03020a08030702070306050f060609010f0504050d0f05060f1e04020a03080a020c09180a0b06042703030b0102030a0804080901030615050c0f0a03050717 83
    0x7040382402582e010302110740390707074104070300e1800c1c4221820110b0300210712a10f11141c28800740da0340002c0f01d901e11601182d1043d90004103240992620480c900003d080710310200c00c00c648250003003141402c503405941c00b408540e0300d100f03100301610ba040300c41640c00300c01030003c40015481540d0b0507260f0103090504500d01525a000940101d0240c0003c40b06840c400501c44204441440840c1c1c104980e11420304090812070107415070442200c85c07200307916480f00009421b640d9140b840c00b000f160031111565540d050040025200d00125a50b240130710340a07808038810025080c0c02689403104003001e07040502c400e03510780034120f801504882d4030a03100c181800c90713820298805881100804400348441c1202d140280680700303014240c42c19908107108072880a50000e41466005038014541c075942c000050040e401014150080a503038169405101c12040d080b0004012a001c10b908592140043d021583d50380c09220400400250051010000003614000902c2c49010360b04295030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 943901142 1250 943899892 943899973
    0x409151a102313050a0f03030e12070e07030906180803150a1d06031203011a0d0f060e19110f0f120f0406180c06080c090a0f05010801080708 62
    0x41c03508003554000d40d0715010b0f40d08000e80e02d01441128000e11202c410201103615503140501905119105603000307403c090032401030041c090088101a00090050200c14104564018014005014111003031841c00c08058011800440801c0c417003a4070501e030030301d140d0b2101200314005000c80f80840e00140c600b80c02045d00c07034020104c4801c007185522010114906a010185440c081c450600c150032401c0005000001c00c0001d0100d40101e072100f03c50307a51106482040044c0324022002c500c403403402d8004161140070000d01402001c0444902402c050003a150f14112400b1864030107607650100710340d0641100e10409808481070b132021540c1820034216202c00c060b02e044901030303a10b02c2400d040100b000003d20444010701385085c1300007001c904035a24266110f0b25402800f05205240780000ca242ca150703021150758150182c4511440c070796462414110a5444c09000d0100384014000707d075221000440304103d80c51500240036115000150070442c4907075260071045a100881c010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 943902392 1250 943901142 943901207
    0x30b06030408031b0708160c0512010f0c020d171509070201050601020105011d0f060a0f0b07060509012a20030a030b0f012c0409151a10 60
    0x358480ca004140e1940c1da443c24002c00158058000d25000c0705070070a0081d800030404c21810780780c841001e101407030b40942190a0060844600d80e2045038082a0340c1520040108103402800303c90455413020320403c040300a00fa6102d42c01c00000100044410f240c1c4260340028142030f0340c10400206485801014400214138041b9084030030380c000d41e44074414000d1a5a0910443d0300500c80f00d0052903100701d0440b01003070700c1e03000031781a112101c1240c0301242040d5101c4d010480180901402c2030009a0350300e0800b021a040108103232000791812000908851040c02800040e40140210740d406d03038000e4500c0401000b45003000381c20054a40b88201d43d202500c440380a01c6856203004646a0000040080c1910031041d2070501904217010083c4141c0d03000004081d440200c100780c0101c2e410a00c08204a848801001c2c0d5481070504200c00140280c40c0c522100c900035240f000d0102810110300041c81c20fa02c0e0101d2500040c0e4808440d65052048910004480c03081140a99148182040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 943903642 1250 943902392 943902397
    0xd12180503130e0105030606060712030b0307140405011a04031e020402030a091202010c020c150712270312050702032d07080105090706050a0c081303150219030c030b06 74
    0x28070306002d10510b0500c01045455005801418110020016842d104c0003042081c042c0c2c1030000c0c15000c84100054006000313030408000d0078009000c8038050782e617809140c4001401660800e015614000000c650542250989490014062480b5141500e540e4882c0c5448425480c0080700680c0142d450006a80d203000450042345000004a62130040303052801600d541107400d6400c0d685408101c1d5400707038000c502c8000103103044540944000b8000a071050a1080300401844046409040c50840d0781020342d498001c00303012902000e401c00c0d1411015080800e02002d00001854020103040c107100c0c078000c1c96030303c1c03014044e141031088d01e03420529040c06032440d24802010079114414000e104000120040148030024060340c01d001003221b8580c5801d01a040400200155401c03149020b551040c0c0d0841d40844125951030001c001c44142c840140011241103580b500c018040c44c4040c025100d041c02e030071062490080000400390000c16009120500b4180c0365044560103a40f030101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 943904892 1250 943903642 943903657
    0x301060b0a1103040902040f050901050d050c0f060409050a0507080702120304110103060803070f052406090601110f0c030709020304080328090803150406060234260d12180503 77
    0x10041981ca027020100148124160130a40c00388070107175051008100700051700707800d8000581d06200c03114881e03c00f04c0e400388615084607001d00c1c00c0c40e06108240c81f040d800103210701080e650300410f41c0c80d20701c8101e80b200040100d64200080c01d00c049408999608989052140d050400144007035441242c142150007a004c1a210001601e12002c10303c9000d0000000410101c0d81e0480c1c4504030480c521b50002c000f4200c0f6010f0b42c3d42d04000340ea541d005200004400180400321090301042810391507440c01000c140c1350080c0504440020024070a00969025507400607440d404e503039402c110400300d010003001219200ba2121085501e1980c0e911880344401c1c058100d02d9070368503282441e042c41510450106004a140602c10000180d010604044090300d03410b480742d6840e0b103c44090841c82d07500180504d0441c0802e40040e0455590806400f11103221146000f2070700380d10111502d40020b24100c002280068581800909180e4407941900f039405540b003074500d00365101d00d482c5400294 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 943906142 1250 943904892 943904909
    0x3062d0b0a0312120b040209060f1b150403020c0405040c050409150e0a020108011509150c060c080a05090705010816020304080a0b060a09020a1707170c0d0b0301060b0a110304090204 80
    0x2c045808207006010b044410001903401f03524000b01d80700411058424020f0100605501040d81d00100810901c081103108515080768001103014014a411b210b0aa4080703001d44039124015a4600300750041d030780304507013200315a2501e500d00010711000d801c3e094000c8402c00d0342408860060300207842000c4001130000000e1858400c6813001502c1400d042e08641202070325080d0f0720b150a544201140191010302c84940000102c0c2c80c2e06482ca1210010014051401d0240d5544541c0c4e014581c240715500e440c50034843c6864400c0b440351182ca40c0d000707450000f141a00041d01c034074090082d0000b40b5440c0d1040b02d2625907100c8540f03080020803035040390300e4040003050200c03525104040f100917080d2480214903102d034502c009044800091450b0f241c0000003000602600d0141a0307004d203441d0f00000480c0140340000b60300195a100e8860015001c1c44c152002c00903050502c5003c050350048011180b41202c06030058584002c40600191188010840807401c203096002800c010066030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 943907392 1250 943906142 943906157
    0x60913140604050d020c1f0f0c0602040b0a0314040b040b100b030f16020d050319060b1204052802040522110301050f0c1204020102010605030f030403062d0b0a0312 72
    0xc03132000781414407416540d446410380c2c07000032402025145411800b00e08600388201e0300d41d00c146c002d5031001030500c006403640d0710118002480855040c003d00c91400c0b655002c210070001c4450049401c0c40a480c0038020b20a07100006000030001d020b8250400c6112000202c0240d0300c02403243c880c0d000300c6850600c0c0010304280300341c00041c03280f082d2004103240080d0070890940c0c0380081c0305010082a8881918041c1d441100c0c0e5085540a800a0200ca400c19540d4040903c000c441101083e5400c80341072181052411001459a080c3c0d370b0f0382d0f500c50300400703500c1d0b8003a0200005803c02900d4000b042202206049042000701d030075860240c4a202c07a9012500060205821540000c10b035510005d01c0c202001082011401200c50480d03110240910f01d48681c00100c0c01010590800743c1c040c4100b0b5140c045035000000600110b901c00c2390103200000c5560f04000000c4548034140c5010303612046820032203290754000702034602015142c181c00c180c1ea522000b4992041040200c08211a03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 943908642 1250 943907392 943907413
    0x50a02100e0a121719050d090b0901050f060a23030319021615050409090c050a0609230616050c060a030c120e032b02040e061806091314060405 63
    0x7280000b1410344001e802d0383e420f05a00700784805d08408000c0003441000300006405c02c0c850030366840303c0f1180d50402401103691a2a200190003008180d402a41c0c40c942180000d00c54502a5415270940d1a0003c4504501d0150444003580510704404598980000e00c0b4005070a4541d54002803403003203e6000700701c03000c01d100001118141c9070b0000d8420703402006404a003036400c803007201c0448a142d80e000481000780e0034140803804440e00642c1d4000c200c00300010309a50b01201c0e203010b43c0e1843c40e03142c400c0c0d0045000e81020540c1c403480030b50802003c3c03107510300c01c13607551545401d4140a2815103950a5060b40014035039400703400003d010960b00c104446800b07521080b004600920101c1c1005074080e0103108590324041d214a440c0511640d840e2040900214240b0425000f440301c0c3c155200ca4841d0508100114200e0b403940c05100648085400c0c002e1801809004a40103000340c1040e854102140c5440884006c090701c03000143c0100e01b9000340c0421a50380f10b980244042c0808405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 943909892 1250 943908642 943908653
    0xd060e0a0213060f0c0c0806220203250b07152409020c01060b131502190f0201050c0d090503160302060d020d0b1509011407050a02100e0a12 62
    0x14080e111061551052082c610800e14a1045800340c46180c203288000b2070400070101d1303d43e5000321008142030f1b2030f800000340a1100284050040120740306006410b003010740e0041864070504406541350f03000c000d1902c02c0100c2491405e9514040c060014400d540b07401024117254051a0708442c00080501c88031031a0307185221741c08030303581000c0180d0700354411207900d400200068040c055206500150194520200350300070307001070032100d03e50341e290950001c44144020702c1d03100700c02903802d20042c1c0724515031010510148200c424100305805285135110400850440c0c0c608a062000030030580c0118038003000421446081170391a01c1119040c9410316050504414810003860088001440141d8a0f0310039200f0f5920066030040c1c07a1404181401c020307003144d100464014041d814030042440e1140c005200000302030301c603018500f0301004440c2082c807400da00600b0700c7d0003200d5070b80c005241001c0031034044106031400b00214100c04000881c1004140e0095443c2c440000141d401c005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 943911142 1250 943909892 943909919
    0x11030c1804140a0f06050d1b0e091e1005190c0e180604090c0806040b070f09051e0a1206060b090108180304080303040c05040b040e030405040f0b0301020d06 69
    0x15094500b480512026060840c46800c060300403107081e500c4443c0d01103141890383c0f000700204001400d81400b82006e0502e80712100c200560f17550642021400400c1c64000c03420482d00542c038410042c6542d024013080d0a25000c141802c251946c000e417a100c04041d461409064000e18055080c1d1554684d80518001250800c0c0d880005100102c101d00c50995140e0540109080040300705241c65a10b41c40020000c151108004041f40743d101e001040c40c0d20002211403146c0d10480c1c0004c56612980010350b45032812052010004151403014400740c01e2211880e0300c0d80c2e40c1c10182c50040111040001d802c0319068004408000f215100c40c41400030601589004018200c12603141414040c0001d08410000300b15001d8050400c0030b1007a102030030001c440081c08140c0c10341e51a400d240c41c00405184507442600d100f00c3c24807075034100d24a80f030700c00c00202c201c0e003500440c03815141c50705000c003a180d2141059012507842050002036242800141010710603410f00050b240c2c10610307060000d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 943912392 1250 943911142 943911187
    0x51002031f08190c1205031207020606150c0118030509030c0103020403081b070806090a030f0e012c06040807030204060605030906010603110705032d0c06010506030402030111030c 79
    0x514107607410880786101141680110030241603090b2070404509211421032001d43c42000040b540da042d0034184500480544806e082201c500303445070315440c2d400c0340c0e00c03181529001e40c00710641504005a9180034004c0a55450120000c100e1a0b5003103441410110f41c0b41c0b041d00420400107410f0354526040c400400000c809080031810141540c03140184c90280180200059500c0c08a440416904000d001e00030179019044601134a0b05daa90701d6100c00c00c2c85811008600550813401d01980114001e91040c241a545c010503480d0025464500481c0d14409841e01d03281c4008500183d141c48005201900704500204011803452062104a40c0d2940c000400c000040c02440741441e0302064507811980c4a1502007001c4580710841c004c10700c20450014102c2c40002490300c41000101d20010100c859500d803604406030003d0f0080031031207040100403454100400600c42442c0c034901454010f400600000f4049107070701d04d021342c15030065402d018242e00118000c80020101c0349500c820 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 943913642 1250 943912392 943912441
    0x60703060902040b0301090b040b10030e061005010210091e0308040c0506030c0403030c0314040e0a050f07021009050f01062306090f1e15040303031505011e03020705100203 76
    0x7010700d0490391a0304c03400113000d041e20081d21804400d402c2d03230300c58100003070b030340c50080119880800000340580100303192a5211200e024000025000d0104280e07034201301d50068024181c1041c01703200318002056500001c40341c50741061942c13503000080d00703980f8003aa84a030f22514100c3c1441d00308506002d410750310041c458501001008242068001601c3c103eaa05007001102c2c513043d468150b407650b0026544103010200450000783d04041d040303426003d65011101006036441706000900e80701011101e04015a1121085022280c419030042043c240200155101c00c0c56411416095485950020542c4912072410100f0040100750300d02e40341008030b5141e031501c2d814501150810214282e094403600b01c1e0b40520b0408404184042d0740713402d0082c41603054022001c806940d82d04180004c4c0d00091801c9044106080030400300c000b80d03003050311900c8010400014041007514580d801000b00b5030280025000603100300090a8818191440984c40349070407103c0c2144504c030903035440c26 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 943914892 1250 943913642 943913647
    0x9150b040e06100b18090c1b010605150d06030f0c05010f020601060801090c0e0d0c080706090e040605040503130e01060e18220213090623060d0c0305010e060703060902 74
    0xc000720a542c840040700c02805900340c4503500005200b101403070452006810201003c00c0000f0184c0c03402c02845c1c023602a845529100840b84201da088500600605400c40c2101140d20f226000c800050003011301800070102d103260f1659510382940e250a5001c84d482004154140810741c0c000c078068480320f40720302c01816190300d8208000d00ca000b062203813512941e03036071007135840c41d1344038035078200c000c80019005045010003450b203141c0c58146481003a0300c0c0d0207100004a4114440c00c02801106c0c140c6100d070110f9255521154014000500222040e100030000142b42204500d880c60007000611940120303985071510140c14400c0c0902644e2191610340350350401c40b090514075070342202500d00540100c061850144510859600e0040c1d440120b100030344140c0c0c0d08540040006078450041400342021116003440d81180e4030100700d00d40b1100394000f40c003605110030741c1c1014a02612000706120755945507142100c0d24140c0c14031907a0007450420580300e030107020700e8005010b109421071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 943916142 1250 943914892 943914901
    0x10080d050304020d060e030c1b150702040b03190515061c0b04020303090d0804141009061b0c2301020606030a02010507080d050108070f1d0a020d09150b040e06 70
    0x9200c0d2100810081c411800c4c81c000d0703400d21000764005900c8003240801c417a0f545041108071560b4101e642058143c24201c0c0005484900388038290b0584170002480c2c0c1402e058040d801c1001070034410000315003620920102c0700b5200d848507005840103007d4000340005000c1340c25100d21071400100391600074944601507140180e90300720401c408982020211000361114400241036200720524240d0202245c1d10700340a03c441c0e04000c0080351402c04c0800030b8000c1e140c003440420300304420b001011843d54030042081c18040c101102d08920070185d03580d07842c1000d41e10392401050f580c001048005e4034140c4503d13003a11100c480034101c0c0090005180c1c5190080000e5600c08003214000d0401101040080400403d40e0541d980030419a030203022668640d00107030380c1c50245200d006903140c0001400103d0405042c040403070300902ea40d0301d044555401140e032029510090740310346500d507030b1403824002c00c8650383c03003100c007a80710803022a80541141c01c01c000d4a01c48899960103400520901 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 943917392 1250 943916142 943916147
    0x203040213050702070506030a0e1905031b0a0c060302120a110f091203030f1006110316031b080a17130609051009110111030a30060e10080d 62
    0x225800401c0c0c0004a2907aa58a008030b00742480b80e0300c050b410a0020082c05102622600300d036007a19000c0080301d48032409031051401d0001c45100c0604241c00401c130454405070302a01039001d0812402c02c540030401555100e40c4520b11036409a800240c1c045200f11407181c0d03002a141e00f00d1485031050002424652000300c8910a5902200243c040020303d1505034481c2c032400d91010030a40d05032170320b03403919064901861070304603101070713041c2c15401c00032480500500d0180c481f056030000031070504a0b0b00f13011850405c0c400805a00740300070320b000011103e0380c0700d116171075141c40b5400c4903484030308104010b080081e10074503000c00351804c00308000800032786140c00004103810140c0130800003842e05000b424400d0308030603003071005e041c41c02a006005880302c08100009003030348e441384410440c249940c0c0740c0c05907614400015070350040810740310981c01580c006101107030040c60b1002c1040280601100c18a501c540100f0006500b004081201101da80004280c042c0103052950f41d102f000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 943918642 1250 943917392 943917409
    0x1b031b140f03100c03180c080105130305090f1819050105120307110f030a03020105010515030702060601111e0a0c090c1b050a3f120f24080105010902030402 69
    0x142400e1980c030701e81d81d030380320703100b42c00c458004240d1140c01c14000c8500d05259450900a0003440c1480d070030f02d40401c0150040c1c0c156000702f00e406030b95160900e10b0203410460700c0e540340d104060f802f8403070300d001243c2c2807904074400d4010041038081180e4480005800000c1e654160f004c940318080386020500c0240010089801460b4411192201d95183c00000f403404020313583d01c0c40d0580b003065001d00c00c141e015031003541662011a5911030340502c000320000240720441e54100160040b002280c065400703008140d001840100c00c0c1e51742503072884001004076149819420b070540c00b4500030030600c001c02018101501004405111403007a006003d00013140c03000000c0300070049045000b06200040c8680004682c0c031100380140000481c84500310b00380038100e03039240c1c1710440340c1560301d0f10082c614075800c2c2c00d0035444500444d00e51a548000500c031050109900c15247d0100c0c2c2c1c03c03070b2844c02d002607170030300740c119105c8a04c1e040058642c00c560303058100c107800c1e03841082440b0169907004035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 943919892 1250 943918642 943918663
    0x12100513050f060109180e0109050d11060f0402100309030e040c02010b0a0503070b03071b0b070c11030a170c070302041404031e120f150306061418041b031b140f03 72
    0x46c0851440e103142c196a006018511028000f070081c180518040c0d075100030a42104040704048400907165403400c900003040695000750b100d1414212050301500a4021150142c000d05200162088260204007600c1d41050f0400060350f484055060714a040c403071220180c80140c004001036030400f1240c2c42c5501c03000d00310a003071200c1c014060380c40c240d50003458258164415201d1055040440f000b4104c101401c100712902c0c03040303100311081e60a0010741c01c20315940140082d043c1c50752498101c0160b81c03080036199000e000d16040031001d41c555000d011103510185003042c0180c42c250400400d85001480c40303081c040c0b0518031003449203030300907000000d440b0041c0c0001b0705a030000480500910200441000c15501560004140b1019920400031980b424070202c0307110f40c212003040b07842c4100c40201d950079841039000c174010521440300c160040d800206405c0d10310b500c0b03071644940d848028518842036010120f0070b12581c80007440210740b003401901c0309510003050030b001a4a40c5284032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 943921142 1250 943919892 943919939
    0x50702100c0212010e030307090504140106180b070f03020c0315040b130b0a0c110d020601030f02030a02090414010b010c110d030504090911040b01080c12100513050f060109 76
    0x166080c0542d560500f0003690305030101c008108a410b5a8400781d1250411541000400c49500e000a00c604042c000c41a0100180c012445a07a00740303882650100c00840500c0032000c481800401c1c446200c00007800510f00032507440c400c800c40d614000340b40c90306d903200060003500324848030b48240c410360702c6441e0003560009190600350344071601c1c1802c3d0115980007170b050108007010b0113600030740c980c4943c09002042d95541c1c0c0c22040690400c0d130300c2d10002600c00c0103074130040040011400a65181c0085071005050f11409080d540002c1e60b5100141e400341c031950180011000d18000074898840741e09020300f002500c800840d00c1c0d903031020300b0101215020f40aa64242c0003003500c200101c802400300e180c8200181c510504003200800c03107118103140a2448c01c0b0105100e50b00410289101c0c0d144612080d140c11075161036004002d02c050502401150001004595903a820b403000b80700201c02c00b40020285051403902100303040280010341446030041041c0f045c0c844241c407d040700380700c64 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 943922392 1250 943921142 943921157
    0xe040b13020306191b0c1a010f18020408011103191109060903070e0702030a1701142418180705031609080d170a06210614012405070210 60
    0x45204c0024050504e810f50310070080c8441c0c13254007500b0100d4081c0080c000d6803860390590070100f803069070800a00590103640080e040070000802100c1030649548410240941402d9642203100c0c01c0d21010708100400c1d0b0004000c0106414203103102d0355150740c40d00d8080c4282140040b00654500c54030341e00d42d00402d400070b5558150340b03040125030001c280c1d00030184050f07e81900300a441e0b40041b0780020009001d4040c8003d04200800442d06881958141d0f2410000240400420b4a1440001040345d0f5210041c40340c41280400580300002c002400c0011064644080201003080100c82055a00c0760301d040c000c05540c4501500d90020710f0203801c0049158001b001d540b803881651002d0f05901c1130702c510840d02c6510644c44039032942003058020580d1102001d1905440d600e0142049040084002d2401170445601410449002d29400104007070840080034014000740c000850240081d40c0c102220481a200341c1c00d045010b14000d400e0100c00d034000342c52004a5480d40e001c20600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 943923642 1250 943922392 943922431
    0x6070f0c032a05100b060301031703070c0c12030e09041211030d110c0105070c080d020703200c13060b0306191205011407051c0c14040e040b13020306 66
    0x1007411010928070b0101511800c500d0520700142d07204814520707000350f541440c284001a0030100c05482c10390303a014400081300c0c4d000c01a0341c05250001440c4204022a400302500401d642c83c0d00d44014003a080c04041003500c1d9801c000c1c1c15560032041890203201c00404001c04a90421a88200e07081c4c6881e0960304500c4034520301d0319500a01c482d00303400f00e180640b1456141080c5005101044ca218000d0055a0710900c0c251840000544082c080d810108264029144641e0041c040340380700b03042c86140c5018180c1d403650031207030003c500003a0f43c3c4440301b880c2c81e03450000244a4403080d200d02c10311509041c4540b0b40300500000d4401402207401d600004900c07081010907201400c0c00b0f40303150725080c7c8603080082c0a881600c0d00c680d9445611000300303044501c65800c4403c640e040c82c4842000c80c01c110070400c001d04014002100b00b00118803080312408201000340300030610240451943d0a05080c0349900303a201512034404000300900e030000689021405a0b40310801000070b0800415 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 943924892 1250 943923642 943923677
    0x60d0501021b010506120105070903081c1b091a0a03201201030605011a0a05070f0c120510060501211401091b03090b011a070c0b09010206070f0c03 65
    0x940e000c1419002c00d00044010405015400107108280484070710900e0342c009080c43c0e080700c0081c1c80384000903502071810302c045906a80100302c0e40c0d08000d000d00d13441d001a180d84045410a00094103405900d9046002e140d5020000c180034002c00040b1758601c10740403516028510030320328100240740d26000305071124004011001000220000d040c0e0340c0705400c007050040d03000c0900007110101e01d403070b00116020091404e010910794003403214610b00300105100ba5040d4111500441c0d8410f02403200100249480d08824004c10310b16249890101551504504040042011400040c070300380041000b682c0c003031407030170102900c0c0e6a583c251502040702003000d4104001c40b060040c02400c0000f5034080320b03a01120000c20f045106004480c0c00160440079564101005098245041300501001185070a2121604800c024007071a00f1425511460072508640c00008a0748004c5002c05942d41c0501180c0d1384015140b41500d004074038210040d018070700c8a00e0142c104003078400c0d1840b440d030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 943926142 1250 943924892 943924897
    0x1b0a060f0c0c09062d03080c0a060e1f110901050307050c0a1a161413091a01030605090108250b0d05040512070b010b031b0a0906170f060d050102 64
    0x16001035240310310a0f00c50030008003408007445202d41c0c400c46806400d50411450b8084101500c000000d000310510359100c809003a00a140c003418540140d0301c08a00040d00d611410700c44000000280c54451110701d610036040740c000e42c6800074281032005040391002c080b01103582000090800c00d44a071102c8100f00c8003402005402a000d204403012030052200c070184401052803001071154841e42ca01c1401b00e260900482c0d10004141c0c0f4880d100d06210b07440000c2e000c0c00585020083d00b00742d031009083d041c0c1c0c0d81d1902c8100b00107241142074049590500610014210541e8648059403500d0340d441d96440c4170200c40040e040d511902102100507482c4110000c280729076401c0e4035810044c902c03400a00c82514101e07024443c18111302548a88002034801d1150840a0880340da8a0a802c026884e40001c200c409084451440d00d008c0c400704201900e520340d8240e175501c1c8007070700780f51000d409118040030300b55401400c0800c2018840c0c3c240f0585a004005440c2c50200c1c400d140740c85ca0190 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 943927392 1250 943926142 943926167
    0x6040c090e04111c060f11090d08210604061217090103180303020c0c04110a050903030d09080c010b0301020f0a2105190f02130b0310030204090609051b0a060f 70
    0x2081c50021040651404c4062903190244030108541401841030104035414294000c2c90090140001070b0686003024103201003a01441c0251b02e840e041410104e08074800340c090810403c9048144034050400303106035406408448418908003180e52035000d01c140c2c0b010400200d0b00d400107000415070b44a80c11100d403c0c140092440049503041c50058040c4d0000c041c0340007648911093701c0d140d403606000d0814400481800e01303180204d1100c040f200d95000c21081605880100400c034062a88d620030068064007070740449845403400707d16203003515054001140310346e0050182d1342d9662145001c41e08001e900313044c580b0045502c0c50115a11700c40c9040d1500d9020300e002c1c00c1100340c902852101003200c0c003280080100a036020b80f00340481c0255290b0035904c0e0000b41060080304120300045400010b0b01e82d1494605513258002401e46030b40100c2206c0058461815a082050410040350030304c50880c620f0007107000c44d002150b200205403140d4410003071020400199240500301c6440507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943928642 1250 943927392 943927399
    0xe010e0d0905461205010e15060d140f0102040e01080a031418030f0d0306050303040b181f0201021201060509031b0f03010501030507080708030c031204170a120506040c090e0411 78
    0xf1907512410f410441c038160307209403055420030301542c04144020130f03030500030080c220341c0f003d140d10360b5801e00c010040c402a046580400134404651122810403031010041e6400380051790b9107003841d882e0180d684060344100055440040d4074000a50400702588440b034140d5951902c8000c0a088094410300b81c5200c01d800d8012266414414040410300c510050f1003610140000c41d60384c1c0905907280b08510134081800c009101d9032500c0d15020010301c1d50854010580c0c8144805030696807012050142d6401c0075070360009a1041010004000034010201e5003032032401d00c00d00e00046a140c2182200f100b0402541ea01688016945d28002002420000d03000300f0803907860b89091a0b543c08607001700111803007405d400055103100001260717040340444001d035040425108400040c0c05000e0402c459030309580552006440c0d1072000780c900200540d403004000c5001d42580000c45001404590007103090101c07002085800c10309030011129400800001a03a50341010311400210010f5550b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 943929892 1250 943928642 943928779
    0x1704021e040203070e101d10110304120b06010f020a02090a020f0f13050607020a140105070605040b06010f02010b0612060f03010c120b0406140d02040e010e0d0905 72
    0x42e0311400000e096403081e11b000742d544415181c1540c12040c0d510000c02014407030450f941a45c1800c41c3c2207500c25141d410680280c0c032020141a0460f00250820469008003c060b00c0078812584819a000142130030f1410058901c4040251a4460301030040d020301211804a5118516a41100e00c40030900300b0803a01ea50b02c0c0070725456642e024507202181c0aa44400116140c0744c08000c40d500ca9030300410110a044c42e011440030710a040880701810720009002c0d01c40415000c1c01602d2003984110412221460101d0024043d20540400c2d03004584c9050381c40155511100120b404145801d4000c1501d5555000080c80740c0041511480d09542401440345030150041041421040014001c1c040f1507100000e1104842d1180700d00440a000a100b14480e41060511221154005031000c201030011111a60a43c0c0b500d1140020f2640808280700e0070607400441c6a000c1c0004554990300c255a48403081c04116800c1c480242c482505004110001016070f0350720b08058820a0100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 943931142 1250 943929892 943929901
    0x6090117070803190e030d05122d01031a092116030c02181003020906030a020316060e0402071101030203090712080307031b080c0c0a0501051005040c1704021e040203 73
    0x1515103001804c0075000c5003944c0e0144140785030101e09064100301903520075080c1603c40301910804400601880441d00c0454600c00700040d241c5810310004d800340b40900c0d03d42d451890002d1200610b100181c0d0450400c40c14891015800308c1d013480350800e003000101a14109030003001c1c080c071517449498141c7c1e5181d00a9400c068000c1c840841e02c40c001c40f42d08510107480e00d07120f84000f604686818015800d0503041c40145030003d0119085080a42265004c0c68281d0101e440c0c1032010340c00c410407459100301002499401141c106600c1c406036025403c05060f0750720190503c1e5080d01241c1456004000a114040104441d1005055500341200c1584003402c1c09252688181c86140000e42050b1940119200d4144a071148400035568905c0540d01c0d000b031000d150300041c0d2141c1d444c0c002d03103c00e00d01182c002d00a50303000d0f00d503684080301d10078940002c0008880b4403420390401e0001048022016594072109145d2294050358011190781c2684400c40240803040d514581c0140b0220a11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 943932392 1250 943931142 943931167
    0xf01141308010c4811090601140702040507050c160f0f05220b04020f19090608011502120c0a0c0b040b1b0307121205060906090117070803 61
    0x9108444001c0c0003000700c030000200444512030f0301c00101111510144a50f4101c00ca410710400b035106900300d0000403411646003400e00c98200c0642a5108861040034900b2890300d008807a8020400f401c084a03003c0ca02d9420440074002c80d50080d101d80d0b5100300081205e400b034021507280451a5050f988130f504600c0003009515120b010308120603002c20404524142801103000956000900b0400050034005104034a0322907110101040343c1c4580c0035001944550000c2d1400c00403040006403034800030800c0f45070400c10a5201b00402c02c002c0c00401c1401e80016050f410340d122100074540100f02988264075142c031160701281e84860008001c03014042c0801c145a81905c0380c0c3c441c20f90640d9818091180b801140070700e0710005010803a600303075412019001290382c1c80c84002d0340d0a00e1101d40361055070481000141000c10001100420b64076203e218466021b00101c60803005410301300049101401c050280341d400050130f804460202030104922001064a241101d58510050310702 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 943933642 1250 943932392 943932427
    0x2606130c12051f0b0c01091b08010b0f22020c0a03030e0c09010b16020a0305030d02040f1e0b07060e060103210302030f041b081015080105040f020f0114 67
    0x304260301d207840c020503d8001c4030300200480012100114007040d040c0902c41d0783d254400700300501a0343d07071401110005000300c13030081800441000300241c0c075403070310007120b0a40710070f01c2c80c1d1442150403890300c0210b5905e6003070070341440d03016013904a07003021100f004034020700c140340501c003451244603040400c03d64140c2000144074510025a15080000414051a80c0b000c1c040e40060100a2007281c80c0b07404038030346003a481c500041000200c40c1e5280c66003800d59020410300c0725003d400160511008019401481c01070102401c0003100811041401c003600480e805040708800f000280d190070301105400050f100000802502d2044d40e403850710034403408955030841c0021460258070344c0380b0782c024400c0d06e208008031602d42180d9680e50307070b0340070300029400003018201030001e00101ea003110800100c290840c00120000f0340100340142d2402c40741e4150711800d00d03030b81413808200004680075200d0706d40c0741c0d06a4000c006090740e9030059070081a030a52030b1075190401b084c000c1040c07100044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 943934892 1250 943933642 943933667
    0x4060204051002030a08040b0705161a070f12150b18030607020708120c03040b040605070c050604030201020c01030e0c0325050306010605120a0f0c050d06062606130c 73
    0x4002d0024881440180e0b160f00910707140c83c003c00e8000700028041880c490040d81d2080c4075240c0703103107071011000c0300f5100880d00b02010703140250034005020b8a01056046281c022030a82040240c10345c46080040030200c600358001401c64941441a40002848500c00040c0c008074410f03d8852b5541040301c2103250794050114802d00c5204041580b103400841d4030420b544044010300000103146d00c410307002d42c0c02040204c1140c0300400000814009410140001d405c15940f000d585600f2810628140007842d001144190303000c000c2080142c1c0c000403140c4103d1428200400c00040c0b03482e0741805d001d5802c00160b010301520446002c2683d204180b11500e60710000b00ca007029450744107142d60342c0c4090003804080b6200700450001c0c00d0002d804141d00c200d58100214180d41240100da0a44501010880119401046814485400d800b03503902800351071a21440e1190303482c07044500c68000e000030341c5030f4050301e0003c40ca89858111a04115040221090085400541000302580f0560301d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 943936142 1250 943934892 943934899
    0x14060420040902090d0b07081008011a1c0506010b120a09051908070204140a0e120d020f0c06070c0b090f06160c050d0206090c01020703080a080705120406020405 71
    0x203020400008014400c59040003600c4141400c0506040450000f03510200b115130f40094a44100400990351820443c4a020b41d0ba4600d00241448000040c07012041e170400361a0780d061810425440080d103d46454101085580390150008003c120304407020948026206000d10400810215003a5000b460044600c1d5103000031a41e0380a00e980403192080f9005001d074010b20b0360003100e400c0c1c151440c4030140c010b04207103140c500c46900007012544103064503400500c4c1c0d03408001a1181c1c46c4034140841d156080039000c2e080e40c2d403400b0141d034442c00e01360920341580800e41c80e86481c2a0b03820b8400001d002002c58103e801e00c81c00181a0800b03003c4104c9200c51b14600107196801e01141c0d020900c07109400500307140c5c60354a03040b00301e09100308104007000fa4980d2004046203040200c540d119406801500407410500f405504104044c25143e05551129004200081a103021628400190728000c00c481d102c0060481e041d22500500c2c03880103006505100505c40140d00410440308201c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 943937392 1250 943936142 943936151
    0x60504110a0306022a370b061e0a0605030c070b0c1b12040311060d1409100908071203020c07080709050a270204020904140105100507051b03070504140604 68
    0x1e46005c0c60424002c81d02d58a98014110050390040d402d4059441c0c103010072030a64000305030f103003172141d07080491740160f03000306421007800300da81406291003120b045004480005503d00d44080341070f405481c800c0008000c40000080c2c082e4040e8410b4500d926841303188120b00c1c3c280a0b0b13086646d5008403c01d43c06001000c243d281c201c40000988280c4102d0240c0003a06092541d29005080c08a1142d0f054000104000c07600324281d00b8441c64a2454250301402c5241c204a84110314080e05000c03002c4005241c1040075000c03840380d106881c0116400030032102c0700c0030a0b43c8201c0290282d580b1741d0129128090303001ca01c554010a95405940b0740309810411542c41c403101302d00b9100c80308541030a0003101080c018242d19122003018680e400500054038004140e004642143c2d501c6100104800202d0018095803400022a081c140700c280380903400c1044640b03c240e251f4003405483c1488022035901070009032010b000304402008002c1081101e000585078403101c14804a485c50702c2240380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 943938642 1250 943937392 943937437
    0x90418110604150e130606030c0e0a05010207031502070b010f0e0f100306020d1103010902090a080328140a0f02010c0906140921030703110604030c060504110a030602 73
    0x800c0c19141118100d081e40300d1543c0841d03800380c1d104511003c0d9070b50040217a441403c0065010b01490000b400d865600060703030343c46a100148207075070303003002c0390720451101c081041a80c0c0c0c0026a6410380ba0006440e100002082c1950790007442100d01c02040c020464000094200e290501c5008450071441d004403a5551030220003030351501100e260351510440001440824a00d50140c880005480b4001980c44506160300005410036445528015000105998107007001c1403103030b0081c86a50001c2d03080c0304244411010f07400c403503c7c000d07018a001106010f0550b109000c2c00302d00600c00000d82d5959041c0d244014140c030340500d0303403030095800d0900e2000a0380c401d000746401c461040c0c0e1465545980b0700742c90881d6030300041c83c0030350100c07815200c1d02c1c036614441d00c000039040d1a08002e40d40ca100354900940740103580b6158290360303004401040082030b00042002180c84d408840043d20340d44520301955400f207801c442c5500100030b14400301c100304040d80100a0003201440c0e40d01c01c1c404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 943939892 1250 943938642 943938649
    0x60901020406020d08040609050f030c010f1103060409021f26040309060809070512070302010e03210f0f0309010603031d01120c0903080a050a17160e01020309041811 73
    0x102d00c40e42005a0018080d0f00ca090311800714150054031400c0c0c0440c40300260b4490b10716002600c0070040d51900b00080b074a15000c000d00c10800300101c0803000f8045200344c840c0d00e003800d0000804041c002d98480b00048210f507103124107c40007039400030f84219014030520f070080c5903030081902c007641070082c096210311800d054040b00c1c0c13040380d0581d81c0f0104070303040002c1180d913404041c002418605c2180d0003c58030750b8540036800200d100d1007004084007407840c0001014a6000c41002d8013a4101c1e03100510458424414503502204c80031540e552040740b06e1030208944244080704c1c5a219020050080002064000c4000ca80c00f1341d403800e107840301460390700d4401200c010508d408540c0c4110303200d8050b4010f4018804040f05400c1001c482e40e641e48031034804da0700140103a0001540000c40141a44d0004500301c0b038100280718400591400700446c1c2031400842041405000750541132040c1c0d42e00c00c1088581a1401a00038056014103203085070403002502812030380d03000340c01130980e81401c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 943941142 1250 943939892 943939897
    0x6040204052d030f0a0510060e0a020903150a050f07050a171005100c0302010c180b031b0f04060e030a1208130501050c1206010f080105040c18030c0806090102 70
    0x1c0c0001e000d0b251241c0b08500c0030031466150104891140141051052542e90031300c0340c01070445140f400703818943c4207482c1203400c14000182c8112164500913040c00540c00482c00329034000f140410040c0e4401c040c00c0040e00d00381d889400d00c842e00560100700440a07000360085402801311400c8581e00f07444020042d101d50040340d402074009007080b014203810001e088001034018486110f078410003500d89010540300303a5040d1303154020401d500052400c00d80e0910519044140d103240007a140d01034251303952a86200d43c890007541a6000c0046080640c3c808890800406a82d400c80c0e615549071905004c0394100303115010100ba221240b072181401c01296000440f68480503c1803180c0b56480103480004000c0c10341f0309207010310382c9001c001910900c0303401d020781142c02026454020f60941c501d02c0030030003485c450401640f645683c1d00d580d0085e9805065650480e404106055070150132100703000c0802d150882841100d43c00030038040540301c0003056070721690984a0980d62281c0341030903032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 943942392 1250 943941142 943941149
    0x602010b0102010b030327040e0a1a1b0715062d0e01030b040c0806040308010f06050903100c0c0c0b030403020c0118051e030a0302010506010f0c150c050702130c0806040204 76
    0x58004211108402e1340c1f1101440c0a02ca58407841040c820080c000320741101e550004000386a0311100320302d014002c0072500b4604401e01d6255680d064540000d4110200064038100300c00624040303031000070009603801041c41c809034130900300559581d4188440850607080c8151181528880c85425080700d80a0780e0b800340c4100c0070045c0c946918690311158801e400810a442c8210789c8200410b28070b405210700c41c045c5000b569000603650620003480d40200d8154000303014000100306c6610542c401003841d0005074203c000003c1c8004580000703503100c004103c1c2c002c066154070b441c007181c48100346001c0c0d0b00683c000c1c3d0846c0e01807400100156410140c0c542098500e88040c0010041c5152001c42540510420344a00c0e0140c15164007107880e246800e401100540d4464040040303950344000495100185443c0009014426481d004030350b90403150a0413086884004041a4900500072543d036281d0190010152280103085500181401c142860009074601c0104407030385807074000d03941030703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 943943642 1250 943942392 943942399
    0x302604150e041a061818010b0d14040201020a0b22050f01050109050105061801030906020f070210031b0c1e0c090506030a03080f04020d05070b0403021503010f061101090501150602010b0102010b 85
    0xd25008031211800c0c1741c06148101d9003d00c81048640343c941c060012180204941e485194030b500700f400d00c20080e6007100841015480d00c05040201507a40000e0312000f040e00701010341c5194031014400492011400556580132034102c00d040100100003841344598488100200407507620303404e1407002d8038130171311900354860700511444441d10910a80d800c104141410005180350f65513940314181d0b00aa500400403007008691a01942001d42286590040b146020410340d00b4000500b1101e0110300b41d80c1d030401124207120030070030881c0d45107049136a0f215410f9004141882c03411513080c40c040c2c064178090300e003080085040d5040c0083c0b5682040e61540301d11403650b41c2c1040355280c0010040007603900440c00010900490403d01c104030181081da03001558079821401841310b03401c154004203043d00802c000401c46008114013806c182c5800e4641104200900b03c1d049000d4054001c0c050101d52034486414400a5007098100881c4c00d1500248011000e010040e0708071403000c4680e070780 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 943944892 1250 943943642 943943647
    0x52a0106180501081c050c0c13060303120c050414010e030102070f050f0706050a050a020c0d082508040e0405100501080115080102190e0604030b01302604150e041a06 73
    0x2140c0220050310f11f0741d03141c00417580000c40034000550311003044076020b910a955010305006040d4001c144820340c4c030140000780214802501b004240b4800e5126145031015210542070340c5a1290f106100c441400600a540720b9015051180f40701030b01c3d0308112041d00c2030300da14000c2d0348004103601085504a0b10740c1d90400c00d000034103440590000e10300100f10300902808460b00e40c3d80c00e8019040300c3c0a0840300f03440750142280d284210900611046189056440000012300c140081740c041e1280300d050043c25403076905e0024540810441d240303c01c5410080046200001544120f15078422100e84e111080d0350340c42d00500700c2c4180d5a02411118841601980c0140503c080701d9401d440138191500d802c4e0749031107030071184c2ca00f030300203101d0701d000b020443c440902031848900d07818455848c031301d1034203002c0d41d50945c4140740710a1920446261080c284032061210050b10024100050385251400a00070700a15190f40205064841c0741351406461103218010003186041c0c001400561 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 943946142 1250 943944892 943944943
    0xa1d160c0f020d02030607020106090b1207030f020f06030a05061804020d03140f07150e301908160206060d02060f0d02040f0603061401052a010618050108 68
    0x40e100420aa082c1d0b00810003500720300050314200481e502c1030006500001d54a070419103144c01390b48014000c0341c401c04404402d0300d05484003003440821280d0008001e06810018070101c1c0004e0725400096600c481d0200810548051680119104801c1180e0b41c10a80714009020984064281c5001e500b2501440002000900a0043d25044108464100d0400d030150a002c006640076050440740c1c400340e0411801070f0f0841d4000e0404007150f02000c1d0614840e403c40c1004402c0d1502800303501d082d04a006001a051000115041d6407079074402040c00b015410009861424241e503000040b0012600013802c40c0d10203d1007c1c081ca0740100721020100c03240d001c00410b500301404000782200308004107040d03c4003500c020b20041100744040d100991a0101c090115482c642c0210080640602540d1103681c0c40300032500040303552200c042c5d50501c10b1001e40390141c040a1003642544c07908801040b418504d400003090f01031314170010710041ea04d582d0401e40301c0020010043d08090742c801c101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 943947392 1250 943946142 943946153
    0x13030c06030915020a020703171e07021014040302030312011809080912010f050421080c040b1c1401090b0d05030d050c0d060f06030c030b031c09050a1d160c 69
    0x10517002c0e50510440c0c0d0111340326200c100a505030182d401500c00ea002407508102c0b0314491102e002c076000e4040c43d50424005401041c10410360b2048202040220b5a050b404082800c050720055600501200e8031140f0900d81410002801c0c0071f000e841c00180748030720700340000345e000b8a00c41c0369000740070314100240d00050118030b829080e070380e01d41552903020030320303118103284512845940104144542c0d00c01c4249120100c0e40ba04008504101070b08013084204e080050448084642892a04d50f5640908a81c1c1c0340e2461004000e218580c244078140000b40107000031a8162041d040c02000301c0040182003012000d80100014482d0700180881030707180b1401c1d8003181c3d00030307040b913080740c80e000b0038504507003c071035194210103010102d440041c40541e603d4800d1000001060908100c21011040060343c1c41240302034562007002e81030404110ba510500f04000202000f42034281c8180c0c6807074407100c004000c031044503943d801c048005918820240c042c60742074035082d01d0b42980c0340000d4551 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 943948642 1250 943947392 943947397
    0xc0306050a02090603090604060518191a040507080f01020703080105040207020a080a0305120f0708060f1314190207030801060507050a0b16020606011409120f0313030c0603091502 79
    0x22030542c01d00c0f11000c1916401c00440c0702d4201c0700068179040c949850200e0413200098a40103d2080a00201600340e01c00214000035451034038070140403a06070710380802112010b00c03000c0d01605441d07050004200c2c0008c1d034502528000070a445140400244003806c03405501800f0b00010040c130010046420a540144091400038110540c190b07140d102d0b603440c0c01d00005080300012070000320081540c0c00d030300d1569001141807401c5403480c2000c80e401440c0540240080f441914046242e000c079540728069410f41902c1d10030b091040b0b402c01030a118104008940381c40041900c90588016101e181c07003160150766050b2610282a401c04000319020b0300264000c40c0c6503c03d41d40501d02185410928a00c81c0c01114081040c2c0d4450400c000e040800c0a8141030500481c5407401c2c2c40da140c00015182981c0041e01d81030a10071180380c1451800030f210b03e0900484c0400582c0c0005000b04034210710960780607610400e0a81e90b00c120440448030359100280c260300380381f030140f040f51940707400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 943949892 1250 943948642 943948651
    0x1c05090a05012d06180228090f09060303080f220b07111506100516030c02010f11031602030a0506010906090612020603070e12240c03040c030605 64
    0x49030252602596400d0844206160707203000c8241407241041c00125151182002c55001c02040c0540c62801411900c1403145414003454140c001c0360300d00503450f002580d0445000d980b00307000d0002da03003a0005400000e06000b00c4800031100c000106041c42c2c98024001140d03415500c4404076540c46244112140000d880b08142160784590021800e0301a4410000540203075000902c6082c585e0001e00b0308100314109034210340000100c801407140160705181c1c40402611102d1160040f55000c03100b5210700c20300c1e41000e0040c400024280340e400400445035030b100703032900007030241c1b19242550751010098200c030f5181e00c108048946803450580b08102e852001d02190402d060a0769074a0034006c003608a40f0009540d45010040040c113801b44900034800c0d9003c1407048441034003c5031341880000d02903428800d841c0c18a03076942d219183e100c440188108103035604810300f6401c02905001000f032000d294820000071403039081006003164000c503840811b4034240d0349103580da1409000006d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 943951142 1250 943949892 943949911
    0x1090b090328120503010e180a02190b0c0a061d060c0a1205400209091f0902010f090b07170c03040f090c0f090e0a06030609050309030d02031c05 64
    0x70000c40003d0405020304189001680b2040c0d103942c14044007100004000704030100103418441c040741215400b081146005e40c0645004691018841d110300200310141c0c044191a50006515028901d004c141413065511800342441003070000e62400c104c0b084505401c0750b240c1c200c44003080c00e00d08044020540d2400300c3c208000f0090307101220108803401100c058140509007240c2008606040c82c140c480014601c0d0b00c0d00c5440c01200062901c9480c001d0000d004520a00c0421440c4070104000c6041d081e250328a0320b0b03440440d0318150301500d00d44c90100d0110300c4016141401d18080e503038480642c0c0c900990f40382407100580700c103540880c00000c030320b03c26141049880002002840144091b03c10840c0c0ca5210300d203421110400c8401c0394813130400b04180020f20320b181c0703903112980100700d617000c54511583e41c0b40d000b0250700a240c0c0d94001803800d4944102031003000408405800d5a010803019200001c0b44030300d06a80340e2040c0300000c04c1c80105026034203d4410b055011176003140044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 943952392 1250 943951142 943951213
    0x150603020c010f0f0c0206090706050904020306030c0a06051b0a0b16170106050a020f010506010c0f150609090b0a1e180209010605030103141207021e090f0601090b0903 74
    0x1c3c0f820003c9a50003280c10b500e403034031070b00b0100c20039404010740b503084500c0034002d18005203002c10050180c050071402900c11b60300040401c40e50341d4204548903070480c000308106840350769401e020b0100d60103480492111201e1903090985c00301c020416010b0140c0045107030015582d4180540c1d86903074000801d20a00001c40188041000900c00b1240642071075164107a0b640150000a45000034a101c0f03d06075a0401041100503640102d01514180c0e101c0f1104244c24401c0c50801050107581e043e1040c40741c50050001190b526541000c00e5060060f4082d40150301c608040c4c000b07642403084141c007045000701c02204ea9810740d078015007444601c4c6a041071040119400120070400a0384240b000070004001801404840b0300800e01d03000446000f081c0c00000440448400d003d0050080e20600300120790302c12503410303e4403400b40300b14000c005030071714a00b41182440d200c2e02900c40074000f65561401043c1c040e903400444900c0c100080041c03c046108004581282c10248451202c40804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 943953642 1250 943952392 943952411
    0x11505070c0305100b0d17032706010f050103021201050f030a02090c0304031b0b04030818060a0e010f1109150405030604140615060307030b010521010302090a150603020c01 76
    0x80c45281c9000d184a5406041c14030003610000081e01c511307803007203441100500c02d41c10004401c9241155080c4401c0c041580341e80e20780203907124000d04003482039600088844a40c989000c085251416034011162803085191200c1c011000c900580e0030310705503154018018055450100b1007481e45d4200101182c40d81100c82e8089010094261540601c180000c010b100c10140c010941201544641100d064300300110703101c5284140c405007018051003564030202d00c5629141030a00f601d007000380e08a64860030200300343c10041500c5c401009080d40b030441450402910ba00480c002c40c8841c0150508091540c2e007082502030303950891042d0074208200008440c1c40a00540b0f00c0380d070054040020050134142d4250911000a05940d210714000805965503500c1c5029250448860710300041c81010010050ba014801c018110b031140c0f280700586211195034401940c1079030320985602c0340544400071440e0649000800c4140d41d49079995041c0030f41c03482036001d8080d401c603d800100d4102c3d00b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 943954892 1250 943953642 943953653
    0x9010e060412050106140301091a060319050303040b070f050a03110c01230a02120720030318011103010f0302060a020a020901171b0f19170303090709020702010801150507 75
    0x164100700e4141c0d44a50007000184110071ba030294400d030075070007804210610b03982c594110036580c007a110307d0700796980820056241000000111041a07860110b80b8645080c090341e00d420882e0100c880802e804005102c40b8414203000024003803907181e441c2081c42410381980500840401c0348003503803050000216000090103040a1500402c28120030380362501480741031040300424040186004000c03030340b030358168001001c0d840f6040345801c1c948000d60300798010100300f411110010b1071001209214400140d071000000c8107400400030010125007052403491800300b403041c11a148030140040000d82001001040b02d0b00d183c4c81650002c000e0341d07000803901503080c1c0200c0495042d042805210110812001c1d07074003188151a40200c44216000640e0001c0b0084020b0040d0303981042e1080c0400b407101400003902c881e401e0040c1841813034403030a03a42d410840b03d00c6094429180001483e070100d10071200e02c03c0c3c069540003020f81c2051200ca60608008402c081004000c01c403000c041382 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 943956142 1250 943954892 943954919
    0x1b2103021c0c02030d03021c02210412090501030504080d11040806040305090906030313300605040605011505030c0307090302132f07020f030a050f0d081b09010e0604 73
    0x1c0700d84a201009090780103240c07130704040d040780909051040010207040313a4404010f0703940912100300565540880441c1c03a41000c01c11001c40c1070540508140400c1000d142c5440c2c0032030020b6a2085c6050b0b603144011420707a5410358020303001d118200300d115829443e0703800148950307400e080245d1620b540c9070b95403464410100e8040d40002d4001c42d100d203039454041511600721404500440c10030010495160009199104140b01c40004400c4a0b4200540015080e50305903103800e0f0010590340350900704080c10086504035484c80c43e03c0300100f0303d4489100c1c034024030846650342c0d50031507507219401034143d071001c0c026505018035004000300603a92051001e0810100b07040109900c02000e01d0500d180c9420700b8810100b0b200754111848103502d04060765041d5404072403016002e0103500100e418008031410140c04d170b00132020503112000000801c00401c00d25669850031a6480041400c0341c1d40c900c07011050401c0c000c0140c10035a62080300d56415501000784500e117480d5030307140b00c4d08546 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 943957392 1250 943956142 943956193
    0xf040b12030310150807030e2104050411030f040807050a0b090313090513081804050108061b12070e0f1f0207080307050303190605040908071b210302 66
    0xa074800000c2203c9858003c88078401840d0801100c081307030702c1c59200a030810350010000020036035900c0711040003500c00c10003803d254100701c0445a100807202e407114045d41c0280103803070103039007001018400a40d80d03500710791241216121101d60703610381d0746c0e9100203a400040f080c1c0c0e90b481242d4120300031500d8000100d00902c6072100856543d1102000c00480710b05076806139107903034980010080745404030f0221142081c1e102c0350803030780e40408440d802d910619a09030103030403034a0300c000070404e030400081c1a40500b13030034001e0030060004000b044840d8852142e2509020380d4940c04226101d01440c0c80c0f554082d001490040025091004510a10310f0b4103940141e6685c2041400b4045070144030b07180152841d00d02840ca4124140c41e00b5a480c031000d001c00941e0700d0413a00022103000703603074080005414010720520890704a401c0900054001d54010388201e9042040c1d012050310003d20398084440700144000004181814000c0b01c0943e90010f4040d070081d89043d0021942010300705520 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 943958642 1250 943957392 943957429
    0x7020d14100b0f0904120522080d1b0f02041d0607051809010b0a0e030304031e1703101502011119080c0403051203040218130303051302010801050f040b 67
    0x790300d0004003c01d200c625920540101841e40512000c1141540b6005604d44a418881d68902a6401e45403205169010104810380d000d40d002c540300d603003c2007040041c0c440d603071001004800525024100f6a80314001040c5000c030f05544401410a500109241d03c000602d20302803410442c2102e041503000c6903010001381e030000f0f01c02105141c0705010f070751281080d030f00a1b01c55070400c0b4000c40d00b40304006622007070042d0058048180d035800c004960241d9808031450390f03100b090b0000320701c0c040c40d07401088541d00c501e4240c2c980c098075080c040e2031064280ea1351100410b850001001c095140b0f00c0b8030502103548510f441c04500d001c19000740708006c10f8800c001c0102052140c018500a00a04450310660b0104000c02c0843d41c001144520701c11700c0c100c52941ea480724400140050308149074001c4200345542040340c000900c0c41e64000a40c001d071000d00c825510982c88003e08203010f64003d003c11078500050050341800442c80e910081c0c0600002802800140000d1203040340301c100120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 943959892 1250 943958642 943958651
    0x90310090b0c0f0d0509070308070f050705060a0f08060105090a0b040504051506040e0717160801060504050a0909261b0105040209160311040915120807020d1410 71
    0x4209000403215407040c002c40c0818203081080c0707403843d03041c424034035020300080c0c90f4004640718040c02e100000045510441c61079448605284c685455a0101001d54007030040b0302000414bc180030085511508080d5a289054052814142d40701d8001420721030421805000d15229502c440307178954058542c10b40d00d9607c5902e4842080151130004140340440440d14510f4116070721100f00b90350564112131410401d9644840c001c540522400306c0343ca803130440c00703414040c0c030b20f0480c4070b000085591541d80d241140c1e02c40c242545c403449244682604400e0005041010200c140d01420880d0f1188016222102c608004040c1140f805000b00c402c4540015480e0015803d590300181010001402400140303066000290200d0005000030320b44c031000074140c1c4401d40710394050900e40b5401c0b66080d440c2c640f40d4034084000c6c80016889030b413201c4200c1c40420074104108800c0d1a03154066005071404e040380c1c0c01d1103407070100c01c10210f544041c0020800c1c1e00c4c0c0340c1842103662a00001c5000034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 943961142 1250 943959892 943959911
    0xc080d0e03011a0913031110050711070b03011e0803040b040807120210030c18090507170f0c07020d080d0507030f0b0112050702190f0501051b1806090310 68
    0x6007111124105481c1051a101d0f02a0702074031007442681e070001c17202d40202e100100e14181515052012400090135000710f07007400f8410351540d032005000e100d440d51400c801590310b105656540409010702c1140c03550610041024078030821003096016003000e07031500000da9a41617103140d5081034100442c0f03030602140038403111000f00306580040c0b402c503c18079103a810540114000301003210801d010992110590f000082c016070b00c0d1808801c0103140388110030368500c4824024801581d1100c005440002140460325012a105002d8030642c1c181594588a4098481156000840c100d810402c05210741010a1404020313086082c0c440f00040b41a2030301c00d42c000c04079070100c01c100806a2070016120b2159038040240045100380400004082e00c5e0a541a0301e820110380760182c002c105180b000c000c100c50882100300c41c2d8410b00080c003c41d00d1720540b4482c1d52220040510981c441807019101003601c03140d55800784a001740003070345442c5a00700406d007055009070915031182d07140c1c06e840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 943962392 1250 943961142 943961149
    0xc080a060b0d0309061817060411030d0207050f15030702100f06080d18080a030e09340306030804230609010509040b0f0d03121505010c0f0c080d0e 65
    0x610441401ca0b514440c80c581030b60060b041c0640d40c02640100f00c041d11700403e6100303a29203000e021b4620f1316030300f54032818400c01070f9603580422a0101c4c0c020030409022901820005490641c10b2029000790681d1418203041c06103103c000c0301410b0707003c00e10f04010141c81901c0d02c0194001c4420340d020380141d40c81c3c13215140c181c603140d051207501c9600e0500308012080012841410100c910300d440790103e503044518040a40541d0003144d580d025004114080580144100c200c16100380d516041a030f0310030740c50340c0e21700501d9254080746261031241c0703903000b5204200081e0200c1c0c40341400645151291030350105500b181d006802c200c41001c1e12403000009605070b80c2d2540d18111503162401a010000825a005240916005548880301003006030394080b03030b4405001e005810100c0b204044e00b0001c09140076030b10581d1010340b8141013034100303061a0540109860301a1140104078440741e540c0c2409802005042e103a0b4010342a01090968003030001403e00513882e500c0301c02e60030144c0b040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 943963642 1250 943962392 943962401
    0x908011103010e0103031d030d020d140c0a14011104030b270d050d060504111b0d020a030c06150e07180806070e180c070b010803181c0c080a06 63
    0x80420302a4203200400c103601100300b003141921303810314042e80c4a804541020001d14016440242c0c140500c00e018a203482d0700007404183c0f0121a510a004481101e0700380140b4405c0062082c0c09404c10120707540401e0701140103044511910000081c2104030003900c0c031a40c0c0013a0402c54590b2200382c01e02c54000d0001c0e07190450300c09007240c44441046182c26aa586005209416060010210701401e85e103da5038800001404060400d00045003104004100d65020559940041c031907055568584400007680c0791096440360020051218991400c0e40c02501920080318a6502d442070469050000440e81004200a111260940c1004030020308031580031415198604459a000c02c404c00700052015040035040c1840c016010381c80000c1801642d07044415052501c800090000040025005258040c06041c0400841e6220652242c8900c5180d245091102420349404003901e0034144d1800780381000104030304108110f64543c00e000c503e0b503014035103e4126800c10802c0c0308080c0039 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 943964892 1250 943963642 943963661
    0xd0e0606041406010c2d1208070f02060402040b15070309030611090f1504030c080c150a080609060a05041416210f1409011a0913060f02090907090801 66
    0x1050059440c0c200d00080000309400800740800c07507644052186d4180e10108818252803000c0c040c408042c140c10300003e400400807402e400075141c080000d0740384e403148441c2c04d11100c2503409092144c9490702004090202e195070142d102541c02090030411820500800c007071442921600010303490f40c14880200c1d203400c02550b8902c5410050440035585040d044000542c4c121501044403201d501541c40c1c90040d0742006006921410010884080014107404840350171940744000300034282d2242003501603400c3c0000850400004550300f0b1038010007080d407013000500209901603a800000707094800003101c07448074030308090a01100c1172a0f01d807003002c0c035542410820541d4a20340601c1c0242c07030508a0010f441030740d034200c110b81d020941e00107030384021302142e0b180414144072a4060003408a041e01e20300c8103580189104441c10305112080c40340481004c0450050781a0b19400d01501c00c409008800c2a420450240c090380c0f01481d1340e0182010350369100d0f0751402c010f803071400c541e0202c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 943966142 1250 943964892 943964921
    0x40c0f020c0603270a0c030309080c1f0818060a0b01081b1b011506120c02122a0106090501150e100e01020a050a06021c090510020306060d0e060604 65
    0x40150810b80900c05000c81c1d02000c1c4003031180302e10b00c5484ca05000800c0b0005065421124002060550008900c4180d503485020b41c4c40001c0102c082121000715040b440c16843d18a001c81054540102c0203e80c0c064201d02a0b81d1425071140c8031142440c00403244000070a980e124a480c8550b8420407850784100c01d0401841551504a204555400703040da2000450a0900800c50365142c01e400042582200e254230f140307100d40300c05014110081040c80810324614180910b01030394800601d1807031f460700a11345a4a40841108001540c3d440817944c5c43c050f00004070203500300c18007445028020550801e001409504214881c8405d50600403290200403c00380c0f911070b00d64808001c12032070802420718489a521003801030b414659102c1c00031b4101c0c068950090144030941d0000c1c001c003100e645009211900403010f00040304c24404c80640180c1c004c00b80e13860031440c140d00071604148014a07050408104c0280c40050340d0250081211941100e000d020303250805000381c071245400f11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 943967392 1250 943966142 943966147
    0x30c020c06250b09070312020c1f05070b010f0302180106080c03060a030206190305060420030705120c0702150f2a1006030b10030b0c0c010b040c0f020c06 68
    0x100001c42900070b8035074220b0400c00140240481e019107004010029910100c41c6040c1e160041c10103441c2c203170902c41513800c80f07441200710100510102e500c80102d47c005210103180b80703840648143c8884c40280303210504c6400c001c1d8402140380307101414001c00002c903035a0101c0e802c503c14046e1940c5d12003c20b604030700444005000301ca0f00141d00d5540302070342d9a2982e8a86c1c0d02e0ba4006003140190350b00280d0850000150a500c06881142615100045803403e000303030b071280402d100456220544240c180500c09003a1000d0341364210085822100901d040c0782000b21002800b11341c040c05660725090880c2c00030700b10b170842c01c0c94a11500c40c6c5a112102c14100f0315441d81c11040d41c82812184427003421500340003c07400340b122440c0300c005203680c07044904184140c0c40742d40c024001400241c1c3d2110b90040011950780105105e201980c0d03204169500355220445182c116420000c1c10b08140e5480740109031044c3c0b42d61141c503013021640d984110021105620180c2015800e0211a0089008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 943968642 1250 943967392 943967413
    0xf2d0a08010912210c0c080a170f151c02031c02010f02130b090a1815050a0b190219120f02060402011409150f04031203020c0a030309050c150406030c02 67
    0x802540c0400015104d011501c011055002c0b01c40c2c18425200500c01d92001c0781915071164401200b96980885620039159500c0b0050740e040c0c4103104442c184015074031806c0400c40780c10301030320700c2450840d4040d000748501d9240c1d00090919070072845050180130304c001116031259090045400c00a0321800840c6001880c0c4007005110b10180140e159008001882c0501c0c0d1b156024104c00404a0f0400340c411205101e9010700940304140d040381002800e07070790105061070200c1c8400101ca6440000f01d00d00601e0a0200c604141d01d414420b00f58060088a4403030040054074007290640b040c0171000c0844120780b0041e10b800e10904004c021503004004100050360040c094903540e0100d168130b60346454030340c000501d1401195a0410000c030b00070410010011800024005482c03141c180032030805603403401101240074034800e8560540c0301c0050000400c0c000d51100520b036000350155003180b501e440200341c07079090070800150b880c2000241003004070b515200d80c6010007150302c0074040e000103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 943969892 1250 943968642 943968677
    0xa03020102221211220609110909010911040f141f08010308032802091002030a09090209060706090c14030f060a050c040f0609050f0f2d0a08010912 65
    0x81104005001018490030214280c1c2c1d44840325501117000440e480d0f0400942c0100c401520b00c51055841c1d0ba41002001205182d9a10654180110140004002e6807804003240c4c0602104c000b00c980b640b1b02088045824074083c500e03c8064121140d803200d200f280c4505011a41c0d4054a03c0503c152078110039079601503001d02820b0443e600a6030440e101c0e142da120b0f101030b000701002450603000d0341320302c403010702d05094014090fa01411038580e601d11410070342c240e07120720412800900041c030160080c08144a940d01600c107100d000b03000300e41801c8542c0e59050807201c0301c0000351585400303003400704140703007440f80102c82290041e0b0182801404109030b00369911406003420b2009a123a00000c1c211a2180c0140c1e4001d05001e08521003030340e9900e81c05000683c031809101d008980408400c0300c2424104d0443c1003808001d030080b404e940e900000c0428103071090740c0c0444681d108000c048a26070394410200c0107454031400000c0e0841c0709180580032250803010504c2806408101c08000e40e2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 943971142 1250 943969892 943969919
    0x40509010b27060d2d180f0302190807020f060412150b0d03050d110306130209010903021e0f181b19080901050912091e030a0302010222 60
    0x4810810300c502c05020800a119030040c804d108141034a405a004d80f0300c0444514289134144000a0015690400b1440410f0f59070041002e001022501c550200051440e02c0c0180303424081c1c8143c9610916007c00311180c42503104040e14110404110401949000c0c01007030020801190f0140ca03191074a045100228040140608030034180c500c0103510b61803a8020340c00e91a0300400d0003078807151a14025016030440041040080e01d4a00d50803c51000c001c100ca008180c0108800c107581103004a55010f0f6124841341810400009400001030f15011101e074039043e44219032074401c2d24500c042c040d0584035448402d1180c81083e00e0401d848000d0700d603190f0040000748201d10741e095100c10101542c8628901030344071390561041000d005622005840c0280a40c1c4028050b039121450724030b0391051820301d9103000ba0002c2015512034a010360141542e40707501c0020510300c1c910800042d09000100000340c002d80d400041040402c0b00030385500e03211030348982594044c50f00b40960041c009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 943972392 1250 943971142 943971187
    0xc0203100b090615040f08060906070e09010e0c1306030e0d0c1713080609011515080c031506040b13060915031d030c0d0e010c110d1109090102040509010b 68
    0x22111604d6140d5514014021a4050301100f6510021075903036200c125506c0c8400c41e400d880e240104404a503032184100202041d90800514902e03044c0d09100c43e448025001414000f2040300801c102c900342d1403038142d010000c0c610342d10002400c0032916841c1d402c0c1000c2d240d070501007114403c01040040e01d044000740c1100f0400800e02c0d2108040c007014044118150040000d600c030b80401c0204160054005003083c00d200e00c070618100740d48040302d0300c84402041a100116601d00c000400e50426100510b510480480142c0c0303c018603000415015805500444000400042d0108641080041401c01414245003002955190007100c40d02c4501000c8600d0130181c40d03040660800b00d102211005c28801c000075a40d8500030102c105a4072604100740c0004194000030f00f010540c000c1c800007a500c1d8024044e07134040302c0038104006c103001a01108484501c00314014031700548412144030b100d004000300050356603003050200705c0002c605038080d000030340e020807032403031900e5a403070000202 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 943973642 1250 943972392 943972399
    0x5090105041206061e080111030402011b020f0a031a22030806010306051804060c051c090507080609030a0809010207240b090a090b221509050d0c0203100b0906 70
    0x854900c3c6400070240c03085902c4007840b40100e417071003c01c0d8076130320304440101c5200400030042c07000b84200c0900030b8001100c01a02188000c0000924444d0304d156142c980e40c80103100c4001c010118000940203d4650021385d00c81d010001d20340c40268600e1842c0b40c11820381264519415614214080e032110b92040043c100400c2030042205170740280c011901410f0002c0603204011040d0168804d5030f0f50403642a980c62341007000400b02c81d40940701715010300b0601111004c0010310980000701900c2c0004046810744100c0400041904080c410f0600583d860b001941d40c1f903c0d0b07010000c003d14000740c041d801a901c104140400600000c1c0b05031b8001e1090560101c032102103a03102e100030441c14403038680007003001d010800038a04039404500d481c0d02c101503422094030b42100714101038842000000310304602c1a0200c001c05d0302c0c2d00307003c2400410340d40c000c906114290390303550805c00c07015a074038081802080c1410443c60248440060514120010040004801c000444c40c2c400904484d00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 943974892 1250 943973642 943973669
    0x1706040504020d1203025a0a11030c060412050a020d0318060e060615090603010603020c03130305010c0809031e03060f0a0e06010917030405040c090918020406060509010504 76
    0x14450b000c0d0301a22810307401085105070160402051210b5070015142c11803031b6500710425404003013480780ea0747c400c0c4d1540710850700c0003d000ca000aa0640c1c0320b01c030040140003d11060f8869444200002c064481521024102504140c0341c4140ca1142c0c1200b100d040c803009103c00c25045500003480d05c544a0241340201d944a6424210b140040c140c00010303046504140c1a1001d08000003201801400165500107951010907004030300ca0048280700c0b42c0c49401000100892846900a481d1101107c0c0c281d0b454259180350384180e014241d8030441d166512904001c81903a0000c1602d5030018500019501d8954900160300246108501d0100401c00100c041050f9449018503010941009840880c2c2e094980c040c03030b20705007000c0b161140002c08120f4007003925034410020710301203000708005505007800c1404000103040740c660500e080000000c0006501c1c0302c18002d100cad1256480c48003540070181303801440141c861580210003840350421055105980c410202c0781182c0076035800706e1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 943976142 1250 943974892 943974923
    0x80d020d0827060a090b0604090213020703021509070e07030b0913140307030509041b0c0f020d02060301060503060f030607020a150207120203041d04080912011103071706040504020d 80
    0x21101040010604452041c0810000f44c0846a07000e0308011340070b00c074264403a42e500810031054901e040c6000b50010991200c40c3c0100f138058000e404000d02c640141c2d00340c001000010350745041304450500d6664007620040156180300f00c0c0c1c064008046180c14030a6030b1031003001c100d00320320280c00005062004041c200600010410b4079950700d240c201541c2d039a0310103040013400c03504404100c0d880796181a10b46290b014044102000301c2055460b1640300740b40c103844000e1340c2e200c0d60310282d030410104001000181c5c1d45400071400382019403501d6849041181c20b02a000100c00c0806010b0b03070060061100e01038001840000031a48011000701084002103c4406405440303001448803a20f0400c030f2409507004005001514506080b05082092100c02c6042c03803030044c1e42c094500a001c0086603264107002c00f44da070b41030103e1070000c40c00700d201740d20079819035004551003000600085c01c1c00c6807a4bc3c151541a030003107000c030341c1030210341402c3d0001446000030303200007050310700564240e9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 943977392 1250 943976142 943976191
    0x5060a0309060f0b12031303032a080301060f0c050601120f0213050f0f012102031905030901030b090f0a0506130e07030204050708070903140c04060b04080d020d08 72
    0x580340e10b03620640034440c0e076458090010141c0040d24000d4810301c29400c1c1d940b5031907800810344100e40c44224152404c207196032820788400000012007440e90780c903440c0214124500c120b0b42e51006103c1c648440c3d4962400b4001050a1651491042040800b94201020410004145065070080440300c1c981002e40c0c40c02e01b00c10080300c0030003504291040c0344e4400002e01903012501c141d16010495085076a101402054580d09015108414144140d01030548100c0c00040c924030b44050110349003100ca50082940f0f003103108508942c1907000240348185560f2500810300c859400380c40800701403d042c120300e0192040180750340541a035510004009568160b4203140b510104078081016603c14208a501c075081c1c1e00083c0c0c0036504040110301c0f010303c26004180b02d4207072644e6a01c64503045503504044071004002440451103174040b280d440d503850b84101d00c014544400b000c0d55640c90b100d0605d0604646940a41c2550880814141800c0c0c0010609a00545440c5131403016145006103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 943978642 1250 943977392 943977401
    0x50c0706050a030b120c04051312030b120f060105100525080708030a050906060d050c0f0a0b0a030204150e0d03051c0e0c010909181b170a170a0905060a03 68
    0x11503441003c85d20660988440032402d2144024169824425966403801079010400d918034018a000345444407031f421240f09500003800300000034108030f0b01100d1f1400b403a19090180104c08450f421590040100340f40113076000340c5100d0030b82000d43c14240040c0800d2100c0c2e011818140c0641712024021040000c0582110100d82c0d0014885031207080c14403403c80201405c0300d0800c001d2055030042403007450080801c005140e4040002c241140e889030511405002c0714080a40203011032101168941c200c5000d0200d040c80e5580041c0c0311841c1075400381d030340000b40d01c085052040030f00d1078600584540902c01110307501820560703a41c1005007104c00300c0c044c2c20003801142c1c500e0b0165041041d0390201e0341c2d03941c1c007500342d84400350315407540c0c0a00204e9840501c070f551a14800c04119001513400030706001802211250410049d07a650013404000c071801200080d242c02a86581c420810142106804e000035000a18208008140e025140d002e050103420f20850b0b002c102011200c0c031a411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 943979892 1250 943978642 943978661
    0x110303040b0a050a0e010302040f030201120f0204090b010e0a08150c0f0313061d03030a09110a032609031209030a02031516030b031002160b0c0a0f050c0706050a03 72
    0x409556440300c0b000103189800a060500000d0242c03031307010042e98400d00940d419604c0403030511171814590f6005580340c403c1c410f1940c2056490f8014042e40241c00d1014100820303507020f001c901c0004820004001006d1781c1c0c440ca01c1a541140b080c07007240e1f80090188010624440c0f890800d890b0210721528a0040040307113500394a000080001c100261130f404000a40319003010322000001c41c0e01086840c4410b82550100c3c0d1061001950088064000034806401241060300d0440b66001003611080742d03030425540092030016011151008296600350b1455000c0f455040c1030350540041d40383d00d0311084420104402140700314103590203000203882c03240d004003142c8040040d038043d082048001c41d01080c101c00044110115580240280080c01c4801005408065070f40c2051100030741000312010280d141141902c00060403c0940f24042c0c03016548950b2070784810301c0000c007891008621642002802d00c85413441000002d00d4100b80e0707069042082c1c885800c18002c80084c040c00c4d2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 943981142 1250 943979892 943979909
    0x1b060512040b060d121d0303160b060a0b030406060e0c13030201050703111f0b0f0a09200304050c1309020117070203090301090807020f060a140901090e0a05090616090311030304 78
    0x6081c44203d980126040000807195808815820084000c152303d901510138032010115180e480d180c00a904850b00661040f0020312030b030b0b10b8a0f1195419251a0811a01104e8455841d10288184203003013000c03540c0311046510310741c078000703000701c6146410007036110003414040081914810140601c1170316003945502000c07151800542000000368203001240007200034548500800c1d1800c01060301d030a080000f400348081c0301d02c1c3c00b5900c0000d0086c00712007100d000482007164406003101000f14000c0c1d019030000c0410110040821800100c643c3e541c68a0700c2c0b4180c11f0310b00517600324501c3c56002514015501d481e0741c07084420b80c154840c40e080d240e415442e1062032010007000c04050000d0500039112218403614440521849208451210010401d82c105203498007003c10000c01925006141060f03205940d424004170007402607401802042d00d43c000c00103454420003c6035404061000702c45a80922000068903404c010b0201a0401c103014545011350b071410003c40d0010220603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 943982392 1250 943981142 943981163
    0x130b1e0a05071a1504020f090105160b07020a0b01050306041703041b0803041a03010803071b15080906161b0303141e07050c1c1b1b060512040b060d 65
    0x2a200e00d400c08808482c0513180c00204074000710f00341403078403c0d100030314050404540f030002c11100550311a00aa440f194035001c411001800090070307040034900a000c07a80084c8400445407620b03a80d400416040310b4000e5218034100400708442d400314101480b4020f2001e0b0380c81c0c4442c00e003080c0c1c450381462031480c08408600001740710400003006000310b80e0720040c80003180303015a11742d1a503480284140724040e4010312280d40803030f001118003480c14015a19200103c0c1d56442e00d10040c0e0b40203012070020070008000c000c2c80740f205020490740881d040c4513401c0a070003a001d019041c03052882040d900814000a00c00405010741e102041003482c0404800b510302c0c0500e80541a080003000d1020390580d030501040f42d5600610940b02001e401c04040d000b1030940303c3c0030102c01a20b4031030034020400c0d071a4100c1d0b170401d1074121a400c1140a010f03203e05403e000c0092025030601c5600c0042080381c10891610310086140742546c0140d070010103e00d4948982c000104102841c603c05403002040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 943983642 1250 943982392 943982423
    0x81306050403090819021e0303070b09010204030c06181701020f071101020f07030507090504060b130b19030305030f040c05100206010503070b27011101060308130b1e0a0507 76
    0x80d250b0303811136504104444c1385045101ca0000e01407001c5800a4200800c448040816504440d4aa0486c02e003e0212030406040392101d25070707018295500505a58005414401d01c42a207000401820140c10303c0000d91203070852103141ca4082e0b2182100f0510744641a141480303007901160059072100d0300301034884040d420408007469a072660070340988035980700e0780300100000c10b0403011640c001c4050442d01d868240301c1009000014400c50380c01da40c8074000c000036a540340d51a001c2c810704500004105403401c0500501c0004009000c01000c10134200b040000c1e4800122a80710401100e001156111440c0048007903c1a030009913002400d070203400c061503400201581250000c40071504050341c0d640c14416a841010460145c8040110005102403e81206e8140e00c1c0c20600d05007080d1801c9070850f50071913486800848200b400001e9040000c030b60000004c0c040d02074501b05501c1c00c2184c2ca0801410503500d14009e01e42400483c00c04039580c000d0081c0c03204140c00006c0c1586e814070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 943984892 1250 943983642 943983647
    0x31e030d06050301110d38090f06130b0a080114160302091e0a0e0901090b010b0901020c01081306060902070209160f11031303030302120a020f070201081306050403 72
    0x484280c2a03894003070001110301d0140150910700003008a5645403841c940b4064015110303d0460700308a008001c0040240c3c50aa4406150090007200d500114118181003080d00c1350040d00c0a000601c119081c801c00d9550440c2d034048544101600040000c1c14802040c038203075160340200c0240d481c1060381e451045100c01c0d4180704100d00100c08040c16015602902240074036041c158214404d40420703d050b00300b00e07003084e6001070014008042c0ca556a010740701c51401c1181c3d0352115035100c0040100f0043c5500d071984c098103000a1450800341e0802c0001d580d101c011404030304102c5200b01184d1110718101d144110340385c2010b0309015481e216088100a0b40c4600401ca000703902480000d60150045002280056150342d00d6044140c51501c00712000c07040d8000e224070314001000b04a081035004d0489000441c482d85026845031074200805e00507241c000c01030504503004200302203070081d070282102e01c103660900300000980c4590464040d102e4a42c90b000f09000d1070002480240354 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 943986142 1250 943984892 943984897
    0x10060605131e1a3a05011406210705040303080610120203090102160c0303090e0702030403150207022d04092607050d0816080108060a0506031e03 64
    0x51000e00c404080d945010750041d803500d040091510008248090118025800300400c45079600f01e40e490074034200d2881e94a0041ca0032015942e08400b2040000c0900c0844209184003038001c1c10400696142c1482c104650361900d190f5407040f840000c4100342034100c0741c07804411840e40e024400803840c0a07400a403099115000a802168044e4000340061420700400c100c03100d06651030460884030407940310003a40000e844644655000e01101680b0320241d101c01d10983d015801c1a06405d2640c1405088864142c1101094000c088104081290004200e030101d0303034810002c12800c0400031041009008110b0001d41c42800711131840f030024101c91070f05080c07020402d180f04521407403a082000f22280304100411420304003190090308820b419032111348213a1501824076000d080d40d0b400c4d040c10032900700b0001281d00700090007858540000082075907001d90410034003075410604c0d0300340e40c1c500003400100c1c41030315840000c0154900740081d500781d40d645119814088102105c1644a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 943987392 1250 943986142 943986157
    0x3051908010906271104051009050f03060906070c0614010602010c09090e0a0615090509030417010c0c020f0111120909130309061b0804060f02010e0f06070e0310060605 74
    0x5905001c0c0c00b06411032003510640003901e0305004a00d0003800000c40c54054221103404070180203003400b001039281c42380c81c02c40c0150740d1150f8074213038a1400d003800c212401100700c01103402540040100508420b00040b8903401102e0360509107040009c80c6410000703070035032038030000848520a00000700d00707405400c0300c0381600c0305440399055240c84e28400421243d4424030840c450f4010141e100108050307501c00d074810301a01030500341d4030b40c645003103405580059070070038595400040c04001d460030940043e02d200c1103140c000e1248005a080041c00b03c0218000640700f0040c070080d00b92103030300991201c801903808006803022a07859071507208a581000444d94044c40f815000246802039265092038041d82c5500d480801da070a00780300b00c5001e414007203c601c0d610411901c002c04940b01c0d002800052049540d0001c00c8030740c4201c02425100040850303440c1d940440801000ba171000700340598420081d107028007044031404002881d1884100c80807005d680340c0840810303d15070040060504c0d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 943988642 1250 943987392 943987409
    0x10608030f12060103050f0105011d09090a0302061f0905060d150e0705010e031b0625020406240f180f170a05100b12010c030b120703110d0305190801 66
    0x2030f07685010066007618030803a4132143c100d00541c01440310358094012810240740d01e07851403400f00b070880c0200f0060740301076860f22002ea2010508604055042040d240d00006070a605184100100e9101d50680303041d00402d00d801c1e0f01c8100060507502c88210380c070107603034100822122005140c0c1e640340040500c2c1031028281d00480380d02042c10f5006240c884046c6030040c000340801948035124000c7c0100003030b48240e108504110308444583d20b050244031480d141038081d5180100303441004111422913110907103003800c0e440044070350502c0c0c0360034840070b0317069080c45104960310b8141200c007800c3c0080001c03c1030502c008003188802c01002c03400c042d6195a10401010b4040c001c103140e0710b1410a50082299120031141e40e60f101944c3c00200ba1540d025083c04081c066120b0103a0941c1e1441c110380b00080e030750b1072034264545013194452218204200140504c1411900d0380c00707241514155290042800e10f01490801d4428021922940c0d10a031050000e503005030002406040c0a00c1032628 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 943989892 1250 943988642 943988677
    0x80319141201170c030a02101103031e06010f1b02061b06090106060c0b1b0d140702010b0f01020c090c041212031b081602100216030311030103020307030f05010608030f 74
    0x190340c00005130005190100400130403040c6140c2d400c000c1c0420007108010708001d00400c40c0000494104040c60140428201c03020100040c0d100c542c01010004100711b0403c000610711a0201c0c0e040300401e07455842d030109641c402c01c101d00100700940700d1800702050f000743c4400314034000c0c040402d05c24014607481e40248a119a603041c1120b40700d040203406000724048401044190300140302e426001c80b00082001e00301001c0c0050710f01160b100b2280345400100c1c42c0700f003207801c0e5820b21a0340420034084680201c1380000c140001d5850422003200c41c00f403560319001ca820440c451050390001c10103442c0c0780891055620307215550341d40404510000c40c0c200b803001102948500404804001c199858a15503651890003007a030030a01c441c0d20f0154011120b400e11403e4a600040401c02c041072013010714000c4620b001001c5030300350441c20304042400d00060005a0b808540300c81103903004040030b00d004025050007030040085901469283c44002000c0307101c01000f0700507002000b5000014131 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 943991142 1250 943989892 943989929
    0x110f070b0c101109090702100212090f0a17090d060c09030201080a060e0f040602221e080c06130b13030b0a230a1404051015080319141201 61
    0x2c05807840252090034081d8240300e10041400c0980790746601c10054411104071001c0004410304a0f4800303a0080e12501d100010481406400c100101d00c40044100404100e00140c5581d59034078081c100803e88900d001402021595400d008000b203e42c12150400c010003820f2005031158003284022404100203200041d00c282c1280b00d8401101e001455009660750b88101c04038441034010400ca40c0079900f4401d108841025003e014000208040f60104883c100140081b01d0f50030148082030158402c1d03c1400541000b088410711420192041c40c0c55a0768249504100c2040703801c09041d0302004203030981c0901c160b05003201281d0150580c0340c926285c03920001c0030b0700c07004030140c040542102000300e00707840d0303840d003850b0700401c80341d000100e40c1c070301149281c6241c1096500b0340f01079003c1e6a06141c01c0c9204e00c01e202030340422242803140d461501e00919103900030491406001040d82c0791400c40c00e4011110300c4007200030ba0031010341d19010071200c0c14021100307008078114598110ba808 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 943992392 1250 943991142 943991173
    0xc200105072d0315030615080f1b0d05070312021501060e09040308250804050f210c030d0518010606031e0e0f07080a030e0315010501110f070b0c 64
    0xc00c00e00329111060702c40403618040d006081c034080c016003c48811400000880c1c81442844807035803d01090511961514000d18580855030340e401580303810441c2030a552015840e55000001ca0039520350141000710300b030590401a80360301c050600406511100041c0c0d60100d103007440051184c442c00d03a5640c0b141400c5a41c24102e18045400c14000b50104000c20b0155015940c040482400044076200c050aa440350b04412081315000c10354190070700003003100511400d4007010500f8000c1c00f550920010017880060f0040c402d041d04440042c8d100f940745010300484242400c20102030005062000d1205170002c0c0d807400c9035030b0319444c215000c82c905100340030760350640281c50081400300c0d00045035203000f0b0100c1c3c0d500c89018030594a24440d110824801c0c0401004c250015048820301814003401c2010284441403090300440d6402240640308002c0506617802880c16011402c0d070314129600c0c0010310510044c0328410580c0018010003000000c2035105a0541940c040080c1c810a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 943993642 1250 943992392 943992437
    0x6010812030c0703030203060a0b0a050406031805060105060315041b021020130f030605011d0f010603051302091801060b09030c060a05120a020318030910030c20010507 74
    0x142c0c038141c0302008810003280c402d8000d190441c0d002040c0a80d025901c0c5007801e8241e2048031180c0120303502103020031995030503101da02c455070010501861201046c0d0713601c54a9400501a03207100301070102c081621443c03540032120035070a0140c000c001e0200c0c0391001e0300720055403050300f10043c0701d00807840807404428045c06010b0043c1c003c030200c00d0300341851203a44070f0f0800c43d4030594030050310b2400102c001403405910011409003100043c1941013142c0705005050f0745651b13000202d442d100703000400e00150886411a1418540051607499802605135500c9581f50060f504c1107085003400641032001401d01680c604007402049041d5545074298000c2c010030a060b035040c0c000510820300c5041c1280202803010301440d10314a01464003165500b00003013a500c3e40a1940d0210411200b0802000c200d0152200d20001b141040c0b40c4800042d04035030943c003140205601c84900013840360040700240740450743d07030000302c40d5007014441c0b481c000d190450703a000000b000203604200c080c08506c403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 943994892 1250 943993642 943993651
    0x1b0309101a0d060b010c08040e09120f0a080417120a05070f021e0a050f10180503030402042f070b01050a0308040b0a14030a0e070e0709031103010603140601081203 72
    0x4680ba460b207840c0c4501c0c009100c401c1182d414040c48a00090000f15004000e1003c5c01c081c120742c08240c14401f092501d0048a0905c1d500307160380c1005078100c207081400a6a400108502d00307001241e41c1d03031422074601c010001007002114008955003056a80311070004d031280c0d000080070001503607244001c46032036949a2104000d82c1103041c1c0413040e078600e840030f180c150321500116641c0700c10070380d0341c40d1130018401c0004803079802c0105075130291101c60007403c1800d031202c02201c030000325a8640b55120300c0b000d000244a0b541c2ca42c000710007000c04060a04040c1c7c1150301507951044428070001035907010400889500e101d840c0041010326000c2501d0058a401105070341c141410881d42120a5204a02c42424051035544112245800400071845498408408203007015070104e02440c11105030080f81c03418521a00f0001c0482d070001d10a803c0740d4120f00c60710510803c50380401e0040641e038001400703031002a19003c40a8200140190480d03948608442e0018401e500c4100e09010549 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 943996142 1250 943994892 943994899
    0x904290a0b0a05090d05151006050315090601020703020405070f120501030c0b0304050120090102010e0c010206191509051006050304030c02060a11070f0f080105040c0b031b0309101a 80
    0x2000c072602d03503c1040502110800500007040800c07094841070701c0d2041ca0309211180c240c41030104002c0f00c00800306040101a1400c045040d81444022800141c0c5068401750246121b040002c1403a84200703c0c100056801800c104280e00344400020400c00c02c0c0503105010403650344a0f0b040b00d404a01c5103d040366000381e0350004040c00c3c10200391840c0d0019205540c259240ca81210510003c41120030f0030302c503c100b0312655154400c2c006400c0d03d181c0103040440f90064035a141050b41c0205086034004d0f0700103010018103400c2408030703004040620145040070b2940c60041000000c07584858044c00c01e031440c00c0c850350355503607048072184000c590060010304004264001420114050034030440d550412a0003031403006803043c074000803036120b903c00c140b14101c100204407540c0b000101405200f002400300e482c0070340729a04e070302e581d5103d150a400700003c000340e1440d104080121320001c181c0c80d03483d44c90078214003456840d4442e21011100ca841c0c103410304150742c000b910f180703003141e4041d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 943997392 1250 943996142 943996147
    0x3180d05120906210604050604052a040306020d020d061a070326070314090d09030813150203180117060d06110c0601090c0903020105030a0b04020904290a0b 69
    0x403040d441c20703420a1042c2ca030800c0050045294407140e4a02000e1207007400246000d113407426030b003000306494018280038090f614181c05d0110184001d442d68100c410003103017a1410100300e0040c0b281d0b900c0780b540040d12581c40481c0c50056000150000c0c00010b51441c4c0174800b4689030b00145040340034003540c82d6084282040303518006070060310b0380301d443c66150407510a408078181916055040131a00680043e03a42c120f54000404032840030f42d00710010784c0003405205817051003d40202c1070b078000940b440601082c0005c1c40d071603060304500603100d65981040794007807200020f59281c00c10704041d914140e80c4481010306510a20104500201036026103075551510b030240008a9401403043c1c0355644c40301e41c18419a4240030003051802c501e640142103035803401c4940c00444510308100002c100001c0c00800150303070310905480e0090000c000015080010000080081c803464120baa0418204013043c01c040c8921701001c0b900b00384c282d107100c0c0152403943c100034030b11306140220f07080c0503410b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 943998642 1250 943997392 943997413
    0x141c050a0809010f091514060a060e1215090105340c0501020f2208250503150a1a010f030902151803071505040303030c0203070b0103030203180d05 65
    0x1d80e84980c101440d0400050500b07805034500d4245d0b040b1710020340e16690302c0d000d4582c1c3d074403051190221211403601480844d0130301c000042c014400b9403080360708121001d0441407240d620302c04c1c26240351010808a5803a200001c401201c10f0004941c00031540d4030b0100015160110041071106252000c0321001d120306112195a00c85010b002011042100d1100701d031000075801d1004107842008100d0303841d1110651111a03034000e11040101d061510691410400300c0700008145807941101c1142403640b160300440e0180000e6103612041d0301d84a80c3c1c421540c11020b4105040c0110395401e0144030350142c540003000c030308014a510301e000410703188001d0980ba01c603500c540311040c07000308504411000e01c018505140c002d101209075144e4a0021864140b60070400000140b5176107030030241c80d40d940c80707000d00280520320003e0305054a50045800c001c1c070034400c0720764082e805a040d8105507101c0c10003e540750000c0a0300c5207100c800c403102e604607242c550000321000368080c0081001805 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 943999892 1250 943998642 943998647
    0x32418080327010b190513090f211106090601060809010e100b12070b071b050d0f0204061e09020a0c0203100c081b0703080c090d141c050a 61
    0x380791515182e0b61502c5070112106182444a204403041c0001c0358140d0308604100b4411036842c849000305094800030030650703d0310b066074020352055007030008400d401800d02101000d40150004c0001c01c24402400801d042c904001310103200c00c0c2d07180000d45c203210149603601d81e401e950380c82e0780d1b50201004005840c0b04010860f40310b0244000800c00c140240740003840d00b403006000c0e10b4100d4503850303680707923608044400346180c0300c00e540100b210501c0c0c007180e14020f1103485c0d4040c0400381c080c108000800703807800e0100020003000d001003010046a003002c0c0002071140c05d00b00c0c4202d04284000a0b079001c4078201807899500c01810b58100e9241907140c0740294450380c4514140841d030900d00c001350790709000800c4903008502e00400d140a60400051850000410061a064142c44ad01841110035000d4810650303160802100325151040030132082d0195882070b07544290b602d80d00e581003002e44da0604036114039500032141c4030100450f05d00d445620f804034580019100340580301c103882c07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 944001142 1250 943999892 943999897
    0x7050a0b0601120911030f07060c11010c0210050c070b03010602120d06050306010602100c030c090501080712180209130302060423010906020405120106050303030c071a0103241808 79
    0x141442c424020f60114420190703190010107454000100b0804603a90606121204401020001411455082400c0585007d094110141450f400942c00303038500d0f4082c51402414030303001017164001084e40040200a540011a80c807024041c200d03000486c40f0340741040d64140c40d0650058544540d00100b0548980c004844059886490b42d100082588062104078042c0100b81d01a00c8407510749260f24054074000510001010302d0030f06c503108101d504c040c4100039200246440c151a450b035170001c40da1002d00b0140124040c0c90035a00c0304403880400044a00c862080e41c0741c10250340c5020b4030669800501c0809405a045140003c2c00038a5080c8040707188140b8021a41288002c1240d0a013118041982150b41650000d820300140c07410b030340c0c0c600c52044004024040c850428010035102c1c007018080219031100860320034100440002580c0f091104030784a60101c1d80d41c0d00f4004030b081c600c0b034804040400344500d0200c0303000d024080e00c602d10600b1946605104600c0d902c208065 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 944002392 1250 944001142 944001151
    0x111030f090d0204020a030b010809070312030903030e06010803040f0608150904080f13030c05060a0909050a0608100b180f010e071101052e0f29070c1a07050a0b 71
    0x120b04041000040e0742e00d2000e840d000003a41c0d0005a420383d040005800c8039006028507600703510804041002512041d00560502180d10f0045400e10952400340d000e08011103141085004400012801040001c0030740100d80440d0f80c507241480e568034095075400010b858401382c807071114030a022203007000341e2a01d40003449040750b0361806006d803980b1180c6800140359000c0707203280d03110200140310030302e10300d20007602c003c4a00900d824581080070b840281184202d44207280c507800096000da486500c040001c2602d002901c1c1030400140c600c10081991050b072a12406008000401011101f004144590516510042942d0900220f214842c10040030b00040000e41c140e442c4428000380213041c0680718078074214003036035000300509501a06075080d0400f050280001000b00c0d400243c000000c58080c1750701d203103d010b18018100304550138040c070349840d00d00000c2c0e0030040003c03240710001103c401803425080c07550b001049440e144540f804c00b0300981c1c083c00010020421004c1e000c0d401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 944003642 1250 944002392 944002399
    0x1b060e06030105150c0a15050a02041404090501150e100b040315021e0c01020c0c09090d0309050f01020c0d09050a1203031505040c2d08040b130c090e0c0111030f09 72
    0x42c018a103001d240352075000c00b41110322120042240103460094044d036270300300304200801d500b05800c248101e078600c0e0400a4852007552684006000c3c00021b42c40781404070b043c070745900e1040391503829103404d0034030582c2c40900d4040001400034205a0203806c1c0e505907a4440126031075500d440c00101c010303402494403a2424050001c0d074420303442d060310041001c01c03d44800541c5a03d00c50780064203140350845203034000d0040c807040007095080800c3c1d00c803001d400c0e800e00180250032818514a00440c07207049008547c80094016000c444c00550494000d00b01c4c0c1e2200265900d0f4000e0240d201c0f250310601039681428681c940011b03000b60010801c0501c41c4400c1844140c0d11030014094074091800000403580140004020142c11038490a06048403103824130301445540000f405080c0083c0301409400c4034001040c0c2c400d13610a100d00c400e5030094104003183d0f44840301c0c10002c01001080407201d2040500005040d4003412800c2040024038001c1c50500701e02c1404480b01e5448030403103590 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 944004892 1250 944003642 944003647
    0xa0c080c0f0f03040609060b10080a1d0d1707110304060311130611070b0306060301051c08040e0709080115060e0109030b011211091902090604121b060e0603010515 72
    0x4842d90503101840c0f19a00982c0046801c403243d0174010116400614540d000e4040341c0c0c0c042c0c800e582c01501058111000180c000f078003400c0b61a5130180d411401c18100c00c64041c05000b60800c680c0104c403480034004038804100192203001c8160381040b0f4401407003040da08240000c1003940d0007607019124071105002d10603d412a2601e010786003a242d40c0003000820030010b03070203101440810001f006414800b2485140d428110006500c0780030500c01c040c85034003060443c1c1c00c0010084814842e07079520040fa15100c0d0741714070404030020741c00c0703c40e44000b80c0f036480009040c10050055601d442482c0e40c0b8000c4032070401000322071580381c0131030765810301081090010000d005495070b24024440791141e40a10001440c1c15010340c03100480052240403103c00b0700c20700c036004611401c100d030484200140d075401000b022a010b806680d00c6040d40085515083e01400161405070302c108084da1000a50140c450409468150320f421280c0e401040c288018000e5052244c0710f0440705604d54082030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 944006142 1250 944004892 944004907
    0xd061d0f192a0804030813050703080702010203070b010f06020111091e010915020f0c0105070b010605070201030f06030506090136052b0f170705031003050709090b0a0c080c0f 77
    0x5030000c44040000340021404000c104c00e2541c480c040580040c00c0983c5600c0c03100c140c0c0c85032135961a0500020f00500d5000840c00116802002180c0c1d040341c0c0444000845d41e59810300f102440114414030b8099400c08421a80800c5104100e54140030004c1219864954800c104002d4945501000d41448100c05000c00c4415081030042502001a80148110703030030041028200386070310100d40d042c0007050040000080c03645c803266054590a00d00243c4859017400124042e08111f0a0280c0b0545480008801d000c1c0125419103c2c03541100244200380d015047e00e640e4190113180544240400541038900c03014035100800520b000d2021241f141103080a41c100301c541c0300080b07801021622a8046449410a1790940040b065081c6098100302100300c202203410b0040041040040000010301c00c038080700f00d80009103030048100c60700e00740c44010540090052690035135030102da29000510b048840c0c003905002c16104d03554400c01e52561a1040c0080d0496003101d401c103041800504c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 944007392 1250 944006142 944006201
    0x301030b190f32160e060a0804030807090b0a030c2006160906120209010c060e030d0b0301050108150705070f0c1706131202030d061d0f19 61
    0x24865041c10b01001074140a1900d6a100e41201d4a91041050100341c0201ca20a403a80c8100c507800854400035500c0703074014900c201d07040542c400090340d100c1c0c4003141d21950250b0000e65503200340c1c825120f1103003a8071041419109490303e4802d82c1d044040820002e42c003184603820000c00b6050078100030307402950302c0310600e07441540c40c1d81c060903640c010410045003a588405600b8500c0383c50604030004c07030500d000209100c84226139460b40e140c00141c81c00040c1d108040b22213030990000ca080018140e034015182d203960004400c0c0b82c1550a05d001001140f506200d00f5049030300b000010300d08417605001140340450000e01c02c60600105000d804040340d00412004800d521440c40e10403010700380701c000c5815021240e4048100e03841039042006003020081400c441a811280f101c404400048080780b40d0b01c14100d40c2003039181000000a8941046034040b80c220011910181090343c5031120b030f6000400c1110400f2810808401541408841d0f82c08459804604200d01e0300c1c030f01141100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 944008642 1250 944007392 944007401
    0x905040603050f06060d0302030301062a1505010803090123040803070f0203100c2106080d020318010309020913060b121f06060215150d030f020d0807050301030b19 72
    0x1070711079401c00c02e883c0045442c10701050380c1c482012251012004026100290340340014002d0009010481e0405c0f00700b1507111244280004c940501044c2005c0c1a1416404213441d9160241e407450411001184040000c81902d07880c50060303440c0303120b0114002042140c00e1003e414402c840d05c08101c049203001c0240020021136028240c25285030740c082c030515151a204480c00c21030740d4901403d0341d05460b84a00b002400c010003408118101401801410081060f40c0c0030421600c1901c1039810055004030240c20485c1c005103560121103019001502640c0d44140001e6000801c0f03000255080c0301e03201c101d030300705009201c0051038000600124482c1d0f4a06148026180d002c0000c04003402d00181c4c02d4500074500b51000e2082c280f9140c00a944d892200030281c07a44020480082c0800c8a04510102ca464005041c00781c1c02c1c0440c14041c0018015041c014010300842042034009070117080035900a03010f9070385441c5540c0c0703142c1b14011407400191040c070506900e10b00301061002d05004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 944009892 1250 944008642 944008649
    0x40b040603050a030e09061815091f0e0405121e03040804090e010603020a12060b03070b0910020d0207050621010b210f0f090f03071a1f1509050406 65
    0x8048002003420042c10614a00041c00c0c0701b480403404100e056110740c071190741e2012030070314816400d46444015001040c8680034007a0004901c908002d5095803443c032039007021140c0503078161076903200c03022900c200302d003103402410342e03405900341400c0c0a00850040018545504002d021420980c0040f20a68010742d000d990218010609006800d40c2d8480c058640b07240c1c0000300140c0d85142e0100d10642041e1060f800c16504100c010700034840141c101c20341d080380c010240c4a002d1303265452070415400402d54580980240405c544a6a00003e18034100c0103542d001000368038035140401c4655400010080d40d810409c80c1e10221480d142a41133001c0c00105d1a183d03120508201400e03d86208411220b11b0081c03140c0078004140704504041c0d801400e1900c0e0000c480e55504201c91074009082e021940c203203c00100b6000748400c00140380290041e4050103021a103807401c0102181c1d846500c0051007801c540700c1004800038203642d41142c2c4003641442d60009a0b0380700010200c80d242c3c3d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 944011142 1250 944009892 944009903
    0xe0303130c1508060a05010201092d05100e16060e3a120c030806120718021305040b3f1e0712110105090402030c0c1b100e040b040603 59
    0x41880401c2c174103480d2076005410b0a10082114440d02d4a51502e0103611080350901e480d0601440c0f40c20700c0c0d460a0002c1d1143e04641107ca00105008038200141000303411104507010f00d01e0f038000d000d070b480b80820040f200d00d40e88140c05420303100c041001001084258030a01c45a525a200c030018a8001d810710076401c034607010080401c82e04014065030580c683c9002042170034001c100010740c0101f00180c00180c04d440014400760b00c001c100d0700e451407640201c14524440e41107412208565002002d402611040c0202c2d0b0399500d40c14082503650040e409940030b4968440042d040da411000d001d021010408880e048000020900c00d8248684505031220307040076103121144420401d091140c00f07081c4005010749132400f409c0c40c1c1503509504d070081020001c80300c0c0f603681c0d0384035505a5603103503002482107640c2c1c20403101c0303c14a5031100303401d0340030f40c010301017000c1d42525080310000d0340d800007905408e804010403174210b41004121035090792160340c8140c1c00710700780c5451284c14040c52040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 944012392 1250 944011142 944011157
    0x9180c0611100c02283e0604140d0b0c1209030414060a0c0b070305062e050c010e0f0a05070e01050d030c150e01020d0f0e0303130c15 59
    0x8041d51070410700b40c50540001c40381450180801654006071504040035200c07880c04440c2070004005502c213000d11006041c800059a05a0604580480c01c2c0303100e038480803840007181c2d4418070b26000f107552042c0840d030141040c401046440c030038080f1804e48a030003c25030f40842c00c0c0381d9a8484001002d4441c0c113141100030410004403941d2004141d00070f00c00e0790055003098501368400451082d403a6120340501c1c0080b500011640c06442000c1e0700d41c1d032180300d402e0385141c4808014001d160403100e10340310b50441d280342007074140100380c2702018810f5801400d4260b480b81c802651136901c1400305142c650758802c400500d42d50f0030b0000c041442e40ca08084c0c03440310703284e007800c81c6001c00980150940c5c001c0343d80104020350718615202049645400c4c40d00d204042404d00800e03030340c50b01407950481d9090401580003440194021700c00f20143d014100005442400d404003122140080d1100f00d510810101d5140c101c40d1801e00b03626407003107850000707040d11400401c551440f00c226100209904 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 944013642 1250 944012392 944012417
    0x6070806010f1e050a110d020c0a061b0b06030a0c08100c0f020703150e0303070e0406080102041d04240c09120b0414011d030d05010506090a09180c06 66
    0x10300110107400c0d1458611994041400f03180b904140d0701060800b800800102c42125501a41c1044401030310a416a0b5001c1940480a0740780d080d051b520600c100180d0701d01150031400f0b8011403c3c2c0d81c4410714801120071880e0b40e203040004024002c140e05115940281e400550040007076406070107003030040d0003402c03640162030044d900304861040c01d10040b402200361181d40040c81000301c0390054440308410114403501001410180c583c01e010740000020032500c80e4000c0000c090300071041c0c40c204143c0f0355480c03a4508074025406010a040d10404030300740b08080701d80387c461f0840c1c041ca0055800248000c1902c3e4845044400000d00c90b88981d80341c0070703041c0c00000c40c400420001806a41c140000d9030703401c5007468000c00c000c00201c0c100c4030205d040c000035808500c0208402010302c010b032904500080e580c2e041210a620b516003010008205400c0c00c00541d5400c01003d030a00300714030304166516015004080e42d4288101c4100280340101d046821080001c04071601c980e0085242d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 944014892 1250 944013642 944013647
    0x5060102030c160e010905130b1906060519031505130b19090c030614040e070b0307091a160b0a02160804170a121803141c090f050904030e030607080601 67
    0x8140c1c1b200806510300802c00c1045041c020a065519900486611095070340804885051082c542501d01e542d29240000c5034841d006001000c003440940c51102c0c03440100c80084041c0d40c0c41c9420003c0000050500708030504000400d008001e490348008a046000303480415180b803032440215801e25505203080014414034450061044079610f01030128900380800501c08030021340f44c0a0060740d0701d0340000c4600000740300c03000c060241e10340e600b650b034201510000c06064031303400348411a08401c41e01e50042c003c084204c95000d168170044143d021710607151500e6004000b0005c0c204540c003000b24540c158450940344a14900c42ca5441c4d8846092010035034880c00740d581c9101055000c41c4017000814110700121100000078542030041d0b95210f1006031002c040b80e40300411010700e070020784c400160085200280c602d6130b411034103d40041380c03100300d500307000034800c981c031506060500b884103050a8003e183d20070f000b8180b05200941b0340e40803c1c43d0074012100c0b500040c4296042c40700c07070341c1d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 944016142 1250 944014892 944014919
    0x60f01210201122c0318010e040e0d02010506131e0c02070807030303020a080c16060f0b061b01320a2403290a1808040906030c0608040b060405060102030c16 69
    0x160040011410a42400c1810306c01d1820140164107100c10320503540c0c00c95a50b600488034141d40a400e540722019600c0300640681402e54255101d083c1400035150b00c3d03942881400d2480d03009840a03543c25030101c54000c010148814503204501449001041e41441009103070001c510076900180d581480d800700408140300a000c500c1d00c501d0030800e07200c105185140c01900079800104c00a0311075a03108154000307060149856401c1000030a05100907480a481d08009045000003404101002c1075040324000855506000603242102508002041c201d24141e1080c2d40600c006050541d14114280e5010f146031b0008540c0303a801800e200b0843c40c8001c1213040401c00b040780310358401e02d01c86002881c0c001400440b00664800f0100764040580c50b01300c4106070050f8100d542e517500c501c0740f80041d103e58042600d0080c84900d00003111403041410600c81c80c1c100481655035101c180401c0090180500040d04601c001d00035424030311350900a00e081c03900c4214030052081c1c030f000007203200c82c1e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 944017392 1250 944016142 944016221
    0x807060212040b0712021f060504050106080402030a0807060917070c06090b1e13032f0622050a060e0906040b15030c21060102060f0121020112 63
    0x25500740b008000c00d4044030107407020280d2081700402c90481d054000c0b441c1c040d240010b104052001700900f44580c03c83c1d400441552410354080c40300380c0c2c03201c074240c91005003039800039003541c01400b800001c110301d013001d0290b8610402002c11107040036161609003005007104001c000f40b0019142d0100000d074108100145860f0030010344403464040c5c501c1850044918805802c00b5810184c4a4070986004882403404510a1520b1007522402c01194480e4413030380c014072015885030300c0d40004c0c022028016102a005210918251380b0700d103402e120100308400e09406400310b65000c186503981c240751001512160740c2d0342d5030804480042104000014007030501446c6020301c446410344554208059013054010801d90700e88640002c21810320075250002800c0182520700d0315406424660103010341026400c403142c13a2110040c000a101d000c1c42428065002ca1412001d02d0043c2803481d1082c80c014100b44846103c42501e01c01a10300080c0300c4041c4149901c03808500380075284c680c1514 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 944018642 1250 944017392 944017423
    0x4060218120c0d03050903070306061503024603051e0108060408090a032a06180905150306151207080d0309020f031507200a08160c08070602 62
    0x1044001866030792141c00d0b80ca8820b01a806118007001818000c904444004030302034121810107039281000f01c003d009078080c6503000040e01c0d0801288510a00a9402001590030002c04200550080c41041d52805401c09410143c151009401011a00c1e065500300c0030754602182c02d00e0a00060001070758801c0901007400c00b024010b102d404400181d55a00c2540f140c400390740e03420700b440004d12000142d40005c15070b0815082a161018518804810300e0006452800c14903845910a58085204860340d0a0480c3c400c42c3c10030220ac1590000c036040203141e011026201d070280701080c240603003116100c518004800d091602c0382000e807170031841d0301100d0010344020ba05014019448810032042007080546071001103003590360794407807c811b100009080b54456001c0394100e81c00c0107000c8640c84003050b102d80c05c0740b610980c005203401307040041d40003800c0300031010754503200d60fa0002510b092403464408440e00002e05142d040c0da0240803c02c008003129460103600a180410b004584c000c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 944019892 1250 944018642 944018659
    0x3060c040e060603041b03080c10050103110405060a0b041e050312190e040911040c0f050f030a060b0f07060507090e060906030a12030606090f1d09030d0504060218 72
    0x2500c06078107a080401100c54555a40b074908111109000303415a0038804607840c200042080a040010f10680205c2e01c1035650041c104458501200c0c000d1001504115004a105103580b82941c01160701801c000d10540c0484e403188100300d45900280c10007441041199103804071042450240710080401300c00500d4040b074420112041c0d4000c0030315805075250489000102140902c3e032062901c3e1028100f0051000c00741031100c0801d00948500f4001c0e494410b0b24000640f0900c41c4030030b074900584546250102c501c4c03007500c45620081840141e10783d24000840e0041e1544001d000c035098214140b51030340c40d1428100201c41c0054044414040b4a8408000201c4044222a40a075040301c0390146583e404001c41e0918199001c01409001c00ca00d840c4012501684404240c84203642c0c0d859401e510f59036403850ba0419409903105400c0d0300c400310300d04011090131a80d0312241400a50303040610220b401d1080c0e88013601c040310300310307002704010307410108911000304000d804030b80710030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 944021142 1250 944019892 944019899
    0x180e061312050d022106090408191407030203071a0105030c150c0105071808030c031801210902090c1206190812070b2401050703170a0b03060c04 64
    0x504280c000e08005100881c1210a046800e0040e81683c160100418007503654904003c01400d20819139207480f9250082c9801080090800494551056501c004114902440300c50082e038651001c3d4607a000300194410284190000c080252036040e10030340003180c1b02c402d5032622007491028000c14a5a021851004118fda507002981106140b070684040d5198400341e0045074582c8211540340751550b080809100c02035a104603445940a0040c650030702c0281c4925826440f0301c01c8a10806507580140801c040050801001101501050402d410036404c2c0e01308039030540310301811140005550310134290030740c1045c04403603070301005941d84140307011801d0226042036035005d00200d000e800300c405010352503190b0900c610081c1050364200c4900015181031b10030183e0260714111882440040030480c1c0070745041c580e00f1004040c0540d008140702d07040045500d034019003030039010402c1c20034403d10004214040180941640c1002040500060050510b0a440a094050851420007081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 944022392 1250 944021142 944021161
    0x1005090d1b081c090c0302090c0f040323060a022203030203070b060438040606023a0c02210d0c081b030c06010509060f04020a090b04180e06 62
    0x101881075120007840e0f2110480c418504002d2516050b02c1da0f854a410943c80501c604410305900300d030300c2240c4840c03160796440b0b05000c01e030060f6600351100120500052000484400300c00c501d400d1040c1041601d12580d1034060303d06101520b62003451540007030602100801c00c40c0400152000c500a02c45682c599540255a4491a00042d0444c078514001c10846d60f1142c0100700700031a182c03052684000714234030b00c0308a50b0740803100f4080b19580300305024042c00c0501440080381c425402515940c07040c540c8952800c036042815101c5400140d070080700d4981420a80b803407034207681c0d85604400316a44140118034480d420082203104211600c190000b500168201d00d075603951511458020485c508000039014440070118503140545100d076154030000082c0690046500807541c075a640c030310a10980b54000ea59403a0001c1510b0443c1c440c41c02c1540060109111500c1c206070659030b00c54154180e604550003004103a4079000c00700080c600e06d0700641000e083e41c0b034050b010600f48411300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 944023642 1250 944022392 944022437
    0xf09070509010f29040602030919080c0904030e03010603060c0e041e020c0102160503070b10030b0105060a05071703010815090c040b0d0c0f150f0c0813081005090d 72
    0x1961003180410f0500c0b850900f00e4402d51301403941c140d40580d151074a0b450080c0d10380e0400314803580036030307440c0d80e0f1000f1074030f59203c100d4100d0740300324080c03c41028508144501640020300a60a000320510707001c0450b14248140030046003d29000181d40314102d100030054044240b40c103204030b081c0890080d000c0aa03684500c1c1e0003044040043c2d0780c08039042d50354060b02031000c3e07000042c0002c002e01024404040002d00c0340c04d21942d0754040741d68a40c0410003822295000160000030048014081d609000004040000b100e061817800c2c0000340e41d030340d607072200a00003109240a001c001080010310030007441141850f408544190381c074000694558800ca41c00f60715100b0703519507442c05003544403244690a85030308002c0c0100d5040e1a200700f000040701c140320301c0d144291141c0d104120300d40314804050b0800c90b00e588059001d400c42d110780e1104c0e0418a109041000300440000c3c00309010005400560b0210b00b02181501e0302c5900e00d81040b00011000c4244101d09003c1d0340c020040d03214 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 944024892 1250 944023642 944023649
    0xe0f0106090b0702210f1002090111030418020d0b040c20010b090f0406020408030f0c120301080d0e121f0f11030c2104210509210a0203060f09070509010f 68
    0x4000a14044480740d0b8600f80c031501e5981b240e03008140350200c0b5102c941c0c0050244805c2a01d6103400c02680c50545990b83c03050348500007d0710026518418044078a0f00100200c900035000454020040d03c00902103c2141e445000410100403004103411803070b0380080d5800d54044001c1040c144011f0100d0050300004004100040b07001f0001010004c0c240c0c10350b40039009076030840e515a01c41089012460b880b0042d1401203205100141d600074241e001200c0c1a90396184c0941285480c4030825181e44611050040d8407218103645069014001c00c24000310ba08900d14900c420f14032072440c0800c42d120054403034803190070700c4025003048200a045a41003100c0418803941c0740f044080c1c403000c10842c10014040d052810741440140481c444080340300c00d4010310421510350a0240c2075a2510815201a420548148e10914010a400c00d0b07101611040b00a0b00d018007a00d07070001f4101035088591000f19403901041c03002c0400c0400c4141c0182200742c1c0c100c42c05504114a81d825210301d41b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 944026142 1250 944024892 944024929
    0x302060a1503061e060e25050d0f0b15040315020307090e180a0c051f0801140103060911070c080703050c13090c030b0a0c1809050702070e0f0106090b0702 68
    0x102c2c1404141346012090310f0706a2900c4041041c40d454a003104501070060350046003051480e15404040c203000c001c072002e40a03d54880510b0004900d84440140129032000c92a0784d54401d001c00003503c85c01203d00c1880010801c0307958039419446c00d101e05c01410043d034603590f44180204152180c004907040700351504400d0308036055452103180d11020019022a58450080c44154001c01c03120745007080c162039044421381214403800ba40e5801c1602d00c88010710001e940480100b05001200c4072003e1452010700d0b001c21140c0e02c4980810a9822140400c045c5140c0004c0078000d010905203203202900c02c1c0c8024001d000e10719221580d84514a8000c5486840c0c2c958400f80092001d0740141c20b0268014480101250307a0b013002c500440342112002c4000c0c1c1061081d040151040070002a4040840d12010f80c00c1e0920320102d009000040c201400e501c01d0740008102628000a030520800400f04850915810418020400649a03004007200314051041c800160f0300d240ea600c00f12410030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 944027392 1250 944026142 944026151
    0xe0316020d05010204031101030507080405072913050307060519051803010e151b070b070923040c1416020307050d030c1b0b120a02091206040302060a150306 69
    0x2030001495144248000800e01c0d032000034000308024002035020303241c10090324104515907035000c068400d403400326002489604142418001622600f1079040140c00b098060714448c0144181d44140380d01c04651466840301c0c020f42044185002c000b08409007001d4500f05041540c640450348880d601c1180707840502c1000700ba600d01c0c00d880c507003080040e2725000b8002d004000c020021180c036000554214104001420002505544054016401412000e401900d0040d10752654200701d0005000311081180c1000c000590f2218184000d101e000114031403107400d0707460401c00c41140c00c0d03a0099014060031058008100282009441c007007181d04800500081c5144000f03420107666400003940010300c1c200761028035510590249403540b095803000c10b00f5410440b040d01d01a00c80c80307807291b070031002c00000d45040300001c22180c100102c00c0025040407a400005401e40807401100c85017507006400708001d0550401040d0b8102411030300401080d0109001c255002c0d85602000d44110b0302ca = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 944028642 1250 944027392 944027437
    0x412050c03490207061b2118030c02040b04090b0a0c080105060f0a03092307050f100c060b0306310c0501051608030a020c060114100e1f110f010e03 65
    0x179400900c9820f0301d55200e00320040300c0d0440503110346210f00140c0081442102d180d540c0751600e03c144413180c0c49980c42504500380035901220150b0001c03404a0b041034880b43d00c84202c0e05e80b801844030507403044a0224503031030904040021981640035100070885044010840c545448007240e1100c0307071540d2601c2d910180b090081d8003074014007134000c00d01c0c803600a4003108a201140b510b000c0039500d100341c80009980d5420072a04030501108a98810103142e40002e0940c000c1c0c9160340182d01c2100003240300c141250000b410201c0031106681e5601403d2146180c840305010840f0451090081072016090030b0303158086400c146004207414020300151240350400301042107508070340c1c407408080e41d070310b4a035000d100a5009011100e200b03100791030010500c894040c05080302010080c00c24001403c1075034040784e140f65511000380c1c014080300d0040341c01d52110030541040b0400303525005103036540015014034005200aa0f0b6111341d151041c04100720b00007004036825101444814180f0411 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 944029892 1250 944028642 944028653
    0x3020d2901080105070210020c0303150a150c0209010504150302150f0c16050109030305030f060a08030a08060102060c040e04120905031902090601170412050c03490207 74
    0x85000c000c1010010440005880141500504d00c00c1c1001e60a540d0085200c100481c140e01607034168004603002840000c240f041c6201385003504031002414031440942d52030204200e049441524000078a006040800754100902410300401c0191003c000f045200e41081c0c0741d01059020003886580c4900c4100794612203030702078036148400310798441e03039551410b45080d9441ca14900019a0025030000005507580202d9403142141d40607121180740d036a400030440490640103000542c03100204002003a00541000540a41c1c0c882d0b071200302d0b260405100183c60090010702401c1008030400c02031020b0000042c6072174104c2d6100c407000c0c00c0108105410703580c21245420141d014800e4540c008540b1183c400d400c0c002d14002d44140740c0c0c0307803110b00044600590020040d20070106d41c0010400050340724802c2200c1c041e040c6403039800c5c03d1500d00d045040d544050041e007070300408107031201d001100001b030809400005903080d00c410011800c00501810080700703002d60716607001c54042e06114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 944031142 1250 944029892 944029943
    0xf0b0a0516030203370203090d08090301141e0f070f260702030a17070c030e04090209090f0114060a0e090708070e0109180b0a0b130c020102041e03020d 67
    0x60401001a20b2110340030042a2140b500c90b48140c0200e03000885c20003068004411a00d1010001c1d00d50401c5055a8558140070750161100c107130150350703e40034501c4004914208900031017a001040f540070030300480d0100d15020140c50462006804d009002443e600408666512240c9040c440c001044614040c050301054010110801031004100160709901000411420801c1e0311b55020301c0b0306c0261401203100701202c528012501d2480008040b03405900745090041c4028004a5112999070105500300340548004e101c5a00505110300c00300c800703000e0648450002c02002d94545009800220315494911030001d40c0800071001c10300d18601802030304050300300d0318211a0b0513542c80000399000c90091042c0b0311071626040080d405c860850001010194010050080e1078413401c0e060001490007800e9903500400c1018a180c1d8183d00c2c3c0180e001d4800941c00040c2c46a14080c403008015404500e0841c0102c01c8140901c0181c0c3d6107802c1303503005074004d50207901e6444400e81350810708 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 944032392 1250 944031142 944031157
    0x102010c2a021305180105220519120318020f04020702060c06040f0c12031202160221070f0f06120e100c090501090f1401030207080706060f0b0a0516030203 69
    0x10300e1005815007014041c4c0009000f02c20303200403882d120640c140b10078200d441c20f07152070304448801030341d010007440803000010400c1d009109850a061401c0c0c43e0b0340d403800c0382e003a04440d940312205a400450b40c00d80300704025035610410070b100c003440640c0060200300c801e45040b0b100d0b56001c90f2100a5460321030540300c00c0e850840c2220000d00742410883c4203403108030000c80740400030300400300c0c490a030309011048036030340354450080122140d0a4000a5080b003a9031405101d5014001e40c0903035999082c0039030720301e10030b4421407185409003d5681454215084084504030000c020858030744001e240c40200d07040342c50141e4060101c446100c0113000c1188003240540318400e00404058255071003541584013980701c516440d40d03a203005450714082803040000c12401004100b1034108258500801c950052400500d40303100c981da820500d0b00800c03000d4411580d07911090103c600c0d4044060302625001503c41c0c14042c0300c041c014524030541c0c100070b44c10b031145207411081600030419070760b02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 944033642 1250 944032392 944032399
    0x602210a0c0b04030c02031b09070e0301201c0b0d1502070606080d12180308090307082205040212041212020d0c1206240207091a010e0102010c2a02 65
    0x18203150400a040d0720410409074030074041c040b00380c003150031018624045c0c23003000327009201c45640d2500c0130764030355211050b529015506d90f4000080c40d20b0001b50203400b681c104144648680045c00e41c0b40143c0c81c1e446481070418502115140c40d40c0d241c084024196a010301c41c29840700768401558042d0098020041480b82400c20201c0e4031400440c503480181d84a5a0b654140030124489509aa00400c408443c0d01d80a08500002c00c1c1b04022190303014034a4011245443d403c2c0c0d0b200c4482e40d00032050014031505139010000d000040301700d002c008250480c0c065041a80300c3c080700e180e0010151005000d0111250380c241c000c0c2c062003000c1641c2c48000800c5481e00710700c030200005041120342c260300081d4003000b41c004001140c070448060f12800b05100c00c001c0c0342c1044610303514a905820b0802d40c0300f440b4001800350058095070702d010182132200c120641401c00007606071102d8031201415a41044c1e20500c01580c1b11104600c0413241d610381002d0095010315801801d145800c3c045d40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 944034892 1250 944033642 944033663
    0x90f04031403011710270201050f030703090209011514030603010e0a0803220503121e130209090f0c01050d0b1f09051f0e060c010c0c020a0602210a0c 66
    0xd1000045944d00f03c00880d2205990020058800c418101c07040d00c13010b48400d98005501d8448400c8503030004112500c1030500900e004c04a0324141060f4104480c444006900c8503a42c0e411802c100043c5401018104207101241c1c001a0015150352400401407182e040040b00040499030250002c0e0f054000d8042605c003041014100f851007030b4800c40c0c001000184007504036154514402d14052020341190185040c4201681d001d00d51504c081c205c0609140c00e01d01050b050414880346074054481040c0b2014003010500c140064480000d05007941d81d00403070710981a2860114920320102004d10340740d40d480640b00c065000411030515040c0e0026401043c4480f02c1e074100d810011810320540300c50f0b8041d030755101081031403001c1da10613170388000c041480c41c0c0d80c10340a141a10501200101054141290b900c016800c5503403503400c010000350019110742c02d6040443c1000054095440034110760218004084040e0710000c1d0440ca654000041d907100c16407152030305c101d0b090f0303202c0200306 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 944036142 1250 944034892 944034899
    0x40312060e4615050a0e07020c101b1502180a05030102070f0f0602071401020703110327060f0307020a2a061107270b040506090f0403140301 62
    0x4440c1905401003032240314071101c5040880901d040030071200048015540000000c402c8488064503000c00030b402c240a020b0000720303841d5039441e15039001d81945400d21406182006000780b80560301440140945220b6008251041d07120030000d202e030200300c40b81c04020346a49420300d00704100000e089446840410300341c1407151481412025120122280c41c0081e4844c4201401c0f44510303000140103005c1d1494407030009008508010300c6034003a400050410600303403521481d40160101514007039600040759010960000b0b049902030000b44021810018245840021280740081c0c50b03180044423041000c180c2d9550003103d0408036031a03085502c03420030305000b0b5555031244030100d5030310703660100d03150191500090318510203000c8040160460724244003510341051444030b402c0e45010381031020410b040c1d4800310b0f0304003690702b6109000e140c56542d00351048032290078109100d58140024400c0c00d5664101403a00403003040e003185140e072110f00d819100201c031003150414500c000320000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 944037392 1250 944036142 944036161
    0x51008030f0702210604120c051002030a0c08190209030109061b08090a0309060305191b32090109120f021e13020a0c0f0803060a0f06020303040312060e 67
    0xb070030050b03c25982d042c0c0c02c1032511010344013880e40b514115041d500450010303002c03980340f1603028080f0490341041100400c181d16842c1c242004d000c59007422030b0700003007408058103441c4a160401030711860004c419041c160740c03018010100b500b02c2884281c0208883d08203680039445445116400101042100c29490b00034034400d10401c030340800320340f180c0e0010b1440280894101405c2d68140c0c0d4034035035681008810360040c00c0281c094610704120310f00d982c60706802440b6810114039001017504280c1d1114200800820030500c018842030384000f0300100c0522010203110b10105070607070b101c0c0c41c1c80342400100c0e0440307190750010001d09401040082840042110600454001d0321101e42c03040d41080c40600450f20b2142c1603420494410746140c00c4500b540c01307002c0c1d00340c4078a40449214180e8070f41e5460640c40301030941c0c100b1030000521034a46084150384c030041080d0350b40090b00520f0690080e450307000040010b0f06210189031080607048450340510007408416004101600300359406 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 944038642 1250 944037392 944037397
    0xa0e040b090105090610051c0501020a031a04231b070b1902091804080d020f03010906050a1203050904020f0a111b0d0f050c09040510060b120109051008030f 69
    0x5140303510f00008640c1110340070407042c1c45503944581070402c152401051007620f000c4141101102d00014150400040f07085c001080080035a48c0d0200d070341c1c90440c0407400c8d200103c400d0309104a150480185880c0204210103207000c210b21a00800340d41d0304024241c0c07284c1504025501403500040c03e504002070241414024806079042c040515602c4540c00103d110340703400301740d0180c0003d0080f11000b02110b8016403162142c00be29050060b18403441e4142d070802c2d41045d9001e80f02100500142e40342d07125041c01454112100340304545805082d56a8080c40b0101504200d80010b450b8510f40352501124040d81c600a1055901c080d1f2100c02486108549442500c6004540b423284803280564000c102c10300d401132004d80c01008541c2c50f1001c0005042080340d050040e07901d416144c0d070300d14810610403030040c00a800b8040511103001d007110040c1d0042d100541c0c00340320369030400700030200450544070450700002d680d45a00c850561a05076941c8076040034400021f00c10040440c0308003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 944039892 1250 944038642 944038651
    0xf050303100b03061c02010c020406060c0201080603030f0412170a0e12010b01090521150601080a06060203030c0a0507020d2a120303020a090305160f171005060a0e040b 74
    0xd500d500c0707510b070400600c49120a5a1683d402018603d022018407040d20369482007600c141000d84000400e03501080917070340542c0c01070000c5030707001a4100c19035801c505601d030b01000450146140480071602d111a6004901641d0700305a00031180e1401c00411700c04010000d212051180e480f6100c01c00014005100130b5000c034083d035019000c2c0355076001f05001d0a030005205844251a040c103100601c2a4180494285110305c070250100c4507205205100e141817402101c0b240e00300c0d91130143c0014041000c007800b02c0600600d040810000c541c0c0c081700b41e980116000c03025540c0c0f130800c0c03c0f08551601071440040c0d400741d09103000404001401c0280144100e036507240c22035250569840241c1c180e10f512681840300202d820640000c0d1080d40200300c008a0303420001c03582c41d100d0300c40d20b140c04c20134561401ca0124447e000d20403c201c0040640090428520f40302c1000007a43c03181e51a0141d049107650155112004104599111060300c07014110110b0390781040c0c80d0031305264030030100545 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 944041142 1250 944039892 944039911
    0x111c080423090a021c09060c080f090a1707050d08011404060803030109091a09060a0b040b010c171b030405090a06030221010b0d050a110a0518130f050303 68
    0x1900103100c403040364418185101c000e2002400b5901e0389080d10295100f6540c04582c65101c07443d200c3c3c5589140b2911502e54060b030800500c5500c80701c0054025000039004000d904041c00c10131058071000604038088030b078407006511425400014045850003110710050142c082c00841e500d400b5400300c0c070030781216100710200801a8088041c0303c200c560300c1c0503040071034008000501400e1915007055807540d2040101c004c080301d03030900c20705444405480c0c4201d1900860240301203524540281d0108030300c202e408010700c0d200100041c00c00800c5c520028a4850050891411060306000b030701c503007040030959011482c0010041688944c858000c00e807103505134101242c0b5004440c82143d0070b0301e50141c0b00411508046007400b40587e81c540c1c031028503649415541d201c07501c440141181742840342e0010030206445161200c039a0780c103038040c00d014483c4c0402c05c010f955207204c501c9074a040d441185080d607499034542480740f0085928060502001c00d010101040b0002008511071000078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 944042392 1250 944041142 944041169
    0x6100501030606021510030803090718060b04050415080f0a0c08060f0c0f1c051503150a0f060515120a05070207032a0314010605030307050604111c0804 67
    0x15001942110b4560003110b0050b4458000c924103103000740d50480d04103c1c101e2103911416030b240e543d03072032603801282d00000c15080814100683e060356410040c40e036050b00b40c14440c00c0d0410340501041d014902c51280300c3c0e503c64a221314001c2001e003907030b0090906442a0b5000001c1e50400030341c0d600302400304568040d604980020458000b0a596024901c0c11017088072507280c0005071801c40c0c200e9a682406043c04001d286003040b209500803081400503000861207240a02130b0000800c2070746203560180d00b0012580c0c00301d4081080840e40300c00604000244211072130300c1607009050f5600704da60049180403441034841c1817034010b130054100391086554035036201021300050360030070707140345e400b603071050000744001103010788900c448150034020360101c01220340314170343ea0006941c0150b42e03603450944030101c0b0036400c1c0590f20242406800079890040c19680b140d503202002031002e418141903042c020001c1d5554110541074102a00c2004424801820084100d038003a12a5440b003034043e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 944043642 1250 944042392 944042399
    0x2011a09040515100e150406060216170c0301050a02131e03081e1303030f0c021c030e180610080603060a0f021c0501030c0b0403050604030c06110c0610 67
    0xd8090900c11a07000c000703040d1580248007440b041c000050643e4080c0c1079808804134801c1017043d400c2c0e110380d81044214450680398028842180c05940001c000c540010350300d01e120214028201c0211681450b8407911118442c1240d4100340840a01300e40c1542000d042c01082c5042e60054000a12481182d08440741c0e40d81e0316400000e40d40e890720701100210701007040442c180d90041e00c851071482c407800710188907c00c01c59407254052140c500c0d40d82005d55003070050580c849401003400e826810206140381003500003c0840d84c1180070440201e07400d03d6110f0801d88070f1200d115520002034aa41d845142040290310094000ca80e010301801307442102c00000c40c45240910b00505002d00900580d803981c525490180100d983c1410703d05400304801640003c107680011189032110744000b41650440c40c12408041ea03c0d03100c1071032440305110620111b200866181d800c2549030502504103503040c900340300034000860040c00a00804501040182c9010404c036100741c20304405012281d84 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 944044892 1250 944043642 944043649
    0x1140a051608040f1e05151612150909031119080f090a0302150d1b02030a180f0b0306010807020a03120b19140306101505031801050702011a 62
    0x4507128050009070450022501003600e04507081da419005000c003d202e88002c0c1c00c0d00c000c90f507001a04840c203612003404012200c148040894000150310104802c29034800340051000c800300080c2d040e410b82d00e404480701500ca080c403500040c8001001402561424140506142d0b0b80100c41e0b5098002d41168030780389803004008003492740d449440c403400d0500001500d107844d00540d040d00e401c44030411011025030780d102601f08a4003400416241d5130380320807a909056590720b55100b00500d4124030b10341e11030ba4000c0142c0f4500c0940340b0300400075059804801803102507541c40113021058200d00030a85d04002402580714140030b0b01e968480703459408080782c7d219a00b10000e00040e1a5000c01801e58100d600300e160400d0f0000d000c1800030318128a841c40c82030b6268090611945500307201d03480ca007810300025911195050889810328504411610724800003c000c41c10003000100041c0c0d090740c5004104140003a003002002a40740040d0041e0082c86100440900d00c800140c04921526 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 944046142 1250 944044892 944044921
    0x902100c020a0603020c0c03061603060f0308040501081009020c0a03111b10020c060f040e28020307050c030c101a0d060f0e0a0606060e040207032f01140a05 69
    0x607809080216040d00d80070048009402084803069a8040c0d40301e0b41850b80d0301040450b000d410502c0201400c800c4c15080501211001d6018020884204804001183d004810340d030448400782450342c01a51460062410121607130000101184013040340203c03510000781807071620f4800d483e82e542401e038602100c1c4e5a008010001c0480000302802c102c091b0424002d01d0781103200900440f0316107410000018501c4c1c2083e0380319041d078031011904100b5104003d6a203034001c0d0000040142c0450300c0c1000307110500701000c01003c2d20b600003000c548007511810407908501e5588042d40d40315800d1800346a250481207650080031401e015003005500c043d80d0230300d0301440c00203045200d41da401d070744d0f0500581755112424804a580c0c00700c1d0760504da070a00c05030b1201441001d00145003414000c01400610a0505140c0a144103000d604002504551a024a142000211001e0301414600505d079541068800740c07465007001b5508921184040d0000d00a0781c1c03043d000d00c088d650700d10311084000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 944047392 1250 944046142 944046167
    0xf020c120913111602043c0506010f03180c0303050a090e01050607140114130312051e0411060c0c0f0d0c050910050405010605190e031b0d0b0a090210 66
    0x14010000d140c0b03450545100e0042c094030203000403c900c05000c0c011800072140b18100c2d1fa00902c8044005a540480c0720008000c3d502e00348100101d0400200090080f07220301400c07410b00d9030300e01c2c00198400c0601c0050f015142c0c4104080040e2781c907454000c0503a0403075100d81c1c004c100700c12800703c0c3d80e0680c84443d5040c1da101905aa0030308c4904c0e01c84020070040284011425580c0341021141181c8100c4407601c2040c0089281000c2030082c94002c4c10541524580382c25185410103109200d1052103040380513043e58024540e5544903801c1801640e90303084242503206e1000180a0f81414011802c02e0901d0002c40b120b95950740001d046c04562070309124010680c0026006c01e1000b07107442c1c80344a0300311111403001000c1c1615071010030104c3d107080c0c2011000c00c80c0401c820340c815080300c003001100d42040c90544404007104000c00d039690380c0d05103240220404007143e1003035030301d506c801c90940c01d4006100784601e04002d16968010405140103074010401c250030488020b0259030043c400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 944048642 1250 944047392 944047421
    0x150b150d0903030204050306070e03060705030f06061c0e0607020708070e011707081b09011d070503220f0308070c120810030204020c0c0f041e0f020c120913 69
    0x91650340a040340007406112022001d25500307100102d80c2d80c4041090910401c0c1e981c0b55186110400c0e010140360000c000d0003142001820401c0043e54070965038030a07041001074070510b8440c813054405645440048110300ca1491a0081c0f42000b0000081c81a00500c0d13141c0980c0c41107070311142c000d40c803100305009507406170232508010044d00d0071b0603401c441c900c40080151a001e1707407079002017410048808807039041101d0000500c03245283c0101058018081d0a82010289000d41d0b02d2490000300141801c09211020000581c1c0015030710300c1139902a21500c0140d081e401c03d140c50745101c01121425000074100c0e00000b20382c1d9016507000a0701d00c0c0c01c0540b1452400c421081110f205070000c02038080e2200d200400001616180050b00c044500c44025011200b070755010b0200d0700c615000d00611982c20411040c61042c0543d40c1407103004010000450000030a01095005e07204c4c07030440d0020383c850316000f040d4441002001d0304520b2006c6941916120441c2d10700030030744841140290b507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 944049892 1250 944048642 944048647
    0x1b0b01033c02030c0303030405030a09210204200d021804091505060a151101050703020f0403020409080c030703200c1c1a070c032a030c0f080304150b15 67
    0x1030310800c2a10700c0e02501c0201111080e122150110381176401c00c0e94100d4990384046201c01c5482d1704991750101a00250f0603004983c80f03142c1c01041250841c400c007a005a07034652018608440f0400311084004560001940e54804015404001d40c003510740c0c21800c4e00c1d80c02e000d26462609014410041e0340218036624111502c40052008110181034607510a0b180070380040e14507080500f0020010315600d5021000030701205c1d02d82919001008039040510401c41942c4800840e0709403419650103545c0081c050038585418401031081d4900d0340102d100216168080541c468030803603da2205141080c2c046034440c06040e621340584580342c0e0b100005500000b280d018421002e503080d406030070b455010f5541c2c0700705d40700030013002d60383e200000d0342d149259010300d130300303c4da089900d4100100300000b0300603002c1c0440c0c076000c0c200c08000d0800c01001c107070005004d244025074017025008295640d0b2401c0c5807820060a9064581041d015420103008002030700d0400c00e490021400d0420061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 944051142 1250 944049892 944049983
    0x306050d03200f0a0f12090305031b010605030312011d010506270d030201060812030f011202010224042d0b0c0c0618300a1b0b0103 58
    0x2074407548040301078140d500c100080100a10030410900c2695030145461720340580480c14148103c10049420006101120204000061000044a00780d0b40300182040400c60090500d0f0301402e6a41d110783d40c07600c800b0600c22003000e20b04416a040790313600003000c00380043c221100801c1c02c00034842e2035440f507014040d6481c0580209080000020011450180081d07801c001540b0600c0c10300003940140e6442c1003c2c00207400400c844152005011241421482d0082020410f103105020304a00900b5403074940702164000c000d40001500c41d0000511031243c0c03640d12040d84082100c0c1916a60540c1c010385411510014401e102d40b20b108403580c0b009000c075110304401603000b030001c900d40708081180c041a8001403107a03502400c80c80e000e802e01d15040c60b143c507107040180c0540c000904140c038801488040b2944485c003120449551250301d42000c408299501001040ca09592003295280e1100b0042c1da1010203040c2c1e071141000008403108100d99100365000041c0003900341c2204940c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 944052392 1250 944051142 944051177
    0x1020f07030305480102070503160503040e041a0705070510090821040209060f01080103110d0c06030507020f190807050c0d0f060b010c080313060b0a0609060306050d03 74
    0x1001d81d100030401d80780354800e904400124050260013080560544134494803003010201ca00e012108040c40000c2d0305002d2280c071050740300d103d107465045400710782c001032104001043c070031303100140a94100d0a0345441c25003003881d2001c00901505c1040c00103140007406c01c60286064504e4150014001c1c04a4140e02d00610010942500251443d580074408448218400000703040001a0f0072041d4499041c00e2040c49540000545801e20418504800d1101d81c0d074001e104a044079000303e44d507914514040080344c901c00318002d014010204040005c6000c6803d50400c5018242540c00c44200165040009850703101c0094111040152154080041144c56028060703050050f403d075a00086000d0014a040e00c040c281240d1042d441d0400b03e061000078400c0c10016802800c02b07004240040d6035100051000506103400140f003d6203000c107100d1035610084081e24013600f540c030245d40b0340001501165092040900081c103040c40418281050035010041e2685074a80108003849210308 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 944053642 1250 944052392 944052397
    0x1031415010b1b19020108011208091014041508090601030507090b0310061511010c0801090507030f0c0819022503020a150b040509030a2c0a030c08010b01020f07030305 74
    0x1001c541c200c1d6183d8051038020b000341c03a40b041c1c06011003240b42901d80300240841c1c005900c024480c03505a0840404a0000070480b8028842107a030300071020b0700021b0554200762000080d2418850109004c119003041411407800b562042c1c44410a550701c400d1600e5851f1401d00006096030003104080082d074040780c1114cc41494024240ca6001c01c160302c81d18200c0300035501031201609040d180c0b1790303456045245403050a64010082c0110f8000e0a406420f4400603c03c035115140c0d190001241c852081d0f1120404492140081c45900900030009102800655441c07001011407002d503004550310784202c919481c0d01c84490500b4600e00d140c100c0104a80110a405501440b40711900041d000714080482c09207410001030001a80000d01c8102d0303000500395100c5034010031025500d41c0c2c0185480208050f80d503026001014807108008002c0c0f03402c4880345d001511050080100406130b080f501c251000030300204075005070071004a0341c4103543c00d8945065008240203101180c480c100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 944054892 1250 944053642 944053657
    0x506030c100e06041a12160f0e06040b0705070608061806100507051603050106060c03050702090a060906081507021203070503220302010f0c0e06041e0e070801031415010b 75
    0x3249051a5540318400010881e88117100a41000003840d0307a0018840020316412480b214010122903441d00406003528070b10b111501d0902c4000e0494140aa03900f404507000b0306210042c490301e40186181160303640350310380250400320f1407010010300b16003807980356111000b642881c4401c2607141c08040c024092010726480c1304101d0700b040101e02044c010030406901d8030080c41e0b031403191403450401500310f030200e0300441c04000d0070509802c0440d51000540d41c0c1240c0480d002c040f5034a40c44111001001c00398801c40780541441c0000a101002144014050006980700c22061307454410407070300c4d05e410300022811010280040b0340c0c035910440141d607021007002132a0742c26954800354000003d034400b9048005039120f00d07500380d4042407405121946072150500d40101c0031890001143ea014a002c1c00c2ca85100c4d6030f4104200c501540000001085280300c0c0007414200310030b000300f24070300901050315541d0a401041c01d00020000c1d20340300049104043c01c085034200750804d80c41d03600500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 944056142 1250 944054892 944054899
    0x106140a110a02030319111c0e03010912030902010e0604050a030b070306122a061b111011060c0306060702010807030b10050d150b07030f051b0d030506030c100e 71
    0x600c80c60068a04000030140303c2150300da02c0c0250180b1006c0200030842113410300e00e01d90000c10603001202e08841641988851600740340200703c101c3c1001c80c1c0100f4040030042d01c441c00214280110342e415502c480c01440c000c1c2c0e581d00c40e110000c1c06004e82c620540c4603181e02b0507208001000410401844241c1040d030510340828020713a16032448103511038240c41520700b00500c803000039a800c10b424211404070b0b9075241d968009494844041d1080401d0003804046801c12600e4808011003c000e4000c050300042030401c480c481458024501031000125000038443e10300407484100b039000940307106050041c107031885c154195004460b4403c01030155003d141e1504480907044d07860020010400321180d8500e034981c01030115080c02d586102040400480000405000680400048030041c0d609030034a01550008010704403624841e8500941c0c00300f48400700c9a84059010841c2e0841c8130003903030144900d880358802c258a4600b00880950300503161f08c44c803007072107000d221007041c2800c005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 944057392 1250 944056142 944056153
    0x90806010506072901151107051002031b030a02070b030112081602031f0621060e030f030a0915020301050112090302070515030a05071404033e01080106140a11 70
    0x562016020020084d107009018034440050000c051120034602c0301d0b2803249860240035052104298845d99035000e014051100008203005980c020411505010004042403800442842c02540c0300e800c0101031f0b1006010b10040090764a02d81d009607416503004000f5000e005c16265208070042d031182001007982c0302c8000c06032000d03035414009842d004480700ca990795401c9034416010110b603d02d400840d080c00420301c144d0800000349405210190340848001002500740c3c03d0307680745003e0b104181c1d501c010000700700030051a03903801c0342e4820303072094034540c003028980d0000748140d0000340a1f0358001502582020030720070300c1e0340040c815039010317005441d1956240c002082c034401070f0315400110400004240a0303a08054401c403503015000d0b261402040e040300c03540454a1043d40301c050720241d07003210046503048100c240d40b050700c03034411946129400241200c43c0859600080703640461701840c0001401da000b1100c82e030000998000c020300c1c1091540054942120580c1e4001082c41031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 944058642 1250 944057392 944057423
    0x1a13050a030305030f090d020c0d260706060f0b09061e0a0c14010b090c07051213031e050d0507050a14010e12092d0d031e09080601050607 61
    0x44000000107540240d491070341e0303403818a8102c5800080070b81003104540c064800404125408180545d191408a41b03584d60440e071400d20001e0a200b08442a2410404440401c500f0440d0001402e00b14030a400078040a60790300c00040105500c2d1080d111050303800c00c00f4000e47d02c2c4c100001e1000e1101c2c500d8440000360003d03001c0341540c00490b24880401c811003014000d104140484002c2042004000d104e901c4440c401703e004182c2c040d042c000b010402080b4542044028040030015202c41c14520f6142d2107103444010184195200079110380c3c11040401d821001c14548802e00160400300411303071184510782c103c6655014450503940740c022810310900003005242044040030b414030002c6854108811803500b00348501ca002d922101c403c001c180311070b1700c07801d4402184a0564040c00d05c4502c096000610400d08031300c0c60b80e0712180c100011010150030a2022690645411944200511030306059480b2070480c01062800d51000703004200c60b28004c002450b07218810b4401402c3c0544 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 944059892 1250 944058642 944058649
    0x27050109140c0a0504200c0a080d0c080a0c080613020c10020405040501230d140109031d0d020109030b090102070804060806030c090f0a050702010b2106070201061a1305 74
    0x1154500241c580241030280428602080c2c1d00c006041c04072000c0000382e103903820860340d00b607456440742c1c2d1226000c24041c0d201c0e00c00340318078229950480f1303c031580c0d0780c5044124801081000032441c01300d00c04001040301200305200c1d411a40055844694090302e5010410031a141200d00c4071401030f03020042d82219034401d1000500446441a0140c0c40c2c0342004204010b480050b04540d0b580c0e0080b074041104981200076200b400315050b1035080511642c0d042000031200112200300d42582003284070402c0503803105810b124180000c00c1001e04c466102c082116090004202174002200b0300003d10120f03070707141752513500300320f104000502d400107036950800d050b0030990255021688900070409107003024448080744190843d0030400c00e00e0b04109d80c00e00d95002402d0042160742d0b0360b002807080d50003584140c1d0744040040c045600c0e07004041c000c80c258503030056519503500070300c00803450346030050140c0026030340e42030010f00c0388141c018101041e43c0c00c0001010401445d5540006040c0c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 944061142 1250 944059892 944059913
    0x40e01091a01060e0307140a09180c050301062d0e090304060305010806190b010212030c04050f03030a020303070c080f1b010c1119020f0414041527050109 68
    0x240301e211111000707801601e81481c4007005030b201ca4107003c01001d13030700b2144e60045100019180b04d0100701e8208084100410f01d141021740104a00c145081c85c0300aa641c030a101400040788621030041e107c81d01d860030302d400d03a072080c425640404405040c0079401085015014402002c1c81c41680340315076203c0e4185910079064030b0241907030300001820700c84190326015203805032000340b000388080d0400294903e4040c0102d9800710000e5a5030400e4540e13a07200b800b90201d0754108803012516400c150001c500d00350300601c0756a101c2c2001030501d41c00340c14040b096551141c0340360040d40c255500d2100c15200c4242c00802100c1412042020f180d0700000c850180920703124041100c6800040f05141c00d003110306190556090040d42010003440b46400610221454502d13000c10b65040064400700700d071040c1141da5903a00908020350140c4410071001e01074807442c00b40380704041d9070407922114002c0703c2d218105030190a01340401c001c03142c030034103450742881407140000062120080d15141200d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 944062392 1250 944061142 944061161
    0x30d08060a0905160302031f090b122103040c0b0304050303180f060403030c090f0e10051503010501201501141203090d020105121009060b070818040e01 67
    0x89010090050354145540c00402610580c0810001402c2c04060798080111090341241095000400583c004541201d4100801e1a500b103410101e9200c442001c0600b0400c14141c0c010381c950100b6070341c010720018030740b1495a00d01c0078001135581100e6545400342d2000780280c82034104580f0001d5580240300c02107201e140100b0255403a42881d42e06425081c55051052005903c08000c4041c8841c0100380a03801039418140082c94400951090343d41031015406011001d03030300180080c6030200040564480e038081c0207900801030303c8038100600ca407003a00ba10482c0100900043c080c81d4001c0420000b904091116002c40e0b8608100e070a10380719510111010f480481030042050b50f80c1f00c19030061014086454444810752021160355030b000c1c0c003000c0c0f40704514113590f0324150b902032000c42e00503140310540704070700c0e00d0f00e145891407102d481c0c442c01c141549007400c00038546110a0070f940c00e440d40141307030919152a807040500410781440e002a0b200d60b581031600e007c03039024481c40180 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 944063642 1250 944062392 944062397
    0x15040e0c1201050411031305011b050706150b0d0507020a14010902040b030d120510030503030c0307020607020703020604030209040c0b04060f180e040201050705101a030f070b090f040b030d 83
    0x11030020a080c007800080603440f040c0114200184040c519138400c06803640090103c1d0030b040c1d00e82e01d605160f809013079156040741c030340210103503107600c950350050060409c280640e1051007000756200b22000031074001d20031500200c1c0c051144510200f001d0300541e810006034411603c0c40015034842d15480e01168060b80c80c980e548036101c0e001c60511740110303014500220003078220751b40481c3d8080c18944695040100322551030001031200540d111803000a1038215080340e48900e040c21101500741d10907500358000d8800e01001400303141c0b00140e404243c03580900a103080038655420711400d450003034422603102c04002404035031441c03881e000d070004083da0b43d41d642c0b0200111201400d002d441c0100410100440c01c02400a10030b0034901e82d0300b096080c60312540d40e200300e0070708604200e040c42c0c0000d0f04c5070500141d0416094100f02c40d6407951003c4050f698441c6c008680e10740d80d58000e1007a40d05a00080c0100708151500a0001c010003c000d000440c001041c103000070306002555400c90003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 944064748 1106 944063642 944063647
    0xc09033512040b090d0c060209040209031510142b0b091f02070b0601050d0b0d06050106081e162d0201050903041415040e0c 55
    0x856000610315651103120220000590070310684042d94100e541c01c0214030740040108181c01d800c182c80c0c40b81440da024565820001e9000b1027411544250b0a00000116850500101e24094824007012159189c844403802d8006042d8005100c000d02c1e44042030a6a00c5040201c1003030140c0358110342d0300155980480b100c0d41e25800004004040134424440620320004d240060110402131000f09462202c0c2054201d000d041d070064400c0b50b8140104100d54040c800804a030b400b00e0901180104000f400b00f403400c030310380c0c9049504566400040002c0d81e070100060780c1105456143d10304601650741718210748030018101a000708508068040c50740e01442c244030701901140d9514500f0301414581c0d00741e0050010140000d5402c19000502c01d06002c0121400d039502480641c0718449410103020b040913102c500389080c0c4404000c0803c0011282010501c940c20300c00fa0b0b181d = true := by decide +kernel

theorem cover : BRFrame.Cov 943884892 944064748 := by
  have h0 := BRFrame.cov_init 943884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 943884892 ≤ n) (h2 : n < 944064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
