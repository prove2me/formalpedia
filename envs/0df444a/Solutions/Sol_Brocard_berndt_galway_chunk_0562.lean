-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0562
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:27:23.307325+00:00
-- url     : https://prove2.me/submissions/88b0fbbb-1186-4130-aed1-d202e467526d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 100899280 ≤ n < 101079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 100900530 1250 100899280 100899283
    0x70906061706150f070c09140402010f120b060712090611070509070309061803090504140f1003020d0501060e0109093906020304140604030f15060b1206030f01060602 73
    0x240c0300a204000780c0d1918500c44528804442413402415415522001a414500790b00302c450b100d0869151304006840d0701143c00481d034940700c0c40c0c1c143c46401e1032140c4038208480010520308412030700c40d41c0303516000c6a0303580c1a010b000d440b031051500400c09102c082004181c442254000700c180324000380090090500803a0b5401900d40a03264001d07143c1c0c40c0d1400318081d06400c01d000d080e10b841c2000040c11800c425181200b140d00079168a00213550b660148400c82d400481040c0783c0f82100c50101368807485280c134090b00204250307405800980c0326000109202c54507c41101d00342c1d5254002c2000c08031a00410340100702d200000c120070f078032545548120f61800300024007115031001e403201140030140510401c4040782c0802980d02500e03180040c3d640e0f402401641c0c0f6940f0361940900e100e00c0c00c01c00711416258050b000fa1142812a503032400c0203031100006051254480b00c000c40c8040d0355802034846161a2801c080150a02e4001d040c00c04400020b0042c403a41440c005202e2181c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 100901780 1250 100900530 100900577
    0x503040b1305100c06050f060d020405060a03060e06180a0f11010c290a0204081507020f010f1a09101403010209100302040e011d040623040507090606 66
    0x28500d10316580c02821488032034006441d04119800349804401c00442c0b948544280c03c0306104440c01c20980c0c4070301d030742c18521a004071602a030040001da20080141081d8100304d03005200548881c00150320703a614482520348001050815178400e500704140e4018205e00210920140e03009020403100c1c9464403039012a8003900030b40490501d0f20068503c0e48243c5c2030b415031a40181c200801501500030828040000c80c4502d066007000304003092070b0080c00c1c1f08841c101c0d065030005140c110104100002d0000740142000154018900d174a50140d10a0146110300301c20207100090006030b10b0014090940c2301101c0d00e0280c1e2800003088903540c6006084426900b540552102c90103c8078002406031040b00e0485400004142c035001003107805402074403c1c6c030120021458a80e88880c6035815143c90301d080401c20b182054042004141e556014005607043c07003501d51001501030b48081c03807080381940d00321019881020100060b91035846074201034039031407604140e9000e83c03041d41030034001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 100903030 1250 100901780 100901789
    0x50303072d030501060906020705030304090e07030807060203040b070804020918030f04030c21030804020d0309050301020c0d020f03040501080412020a150207050d030501082509111804050103050304 87
    0x66a102001c91107030040d007450845001203648144003807200300100034210030b01c1110045540780c013010600d24000b02da040142e550190041d0b00306481c1c2400d4001511642c00501c90234025046d01201162402c001008601d009640250303490610340740c440a104402401c1c1420000f200c02800016a2054682d5802c000441406003a2440c04000c0340d0a41c801d0701c01680392a5000a000010804240c15600840c0c5c503500c4a45600b4505105001500d428500b0040c0064000000900186048a940d00495010340341111740a034403000801d089901c540c0c41860958003121596103100d07810040e400d4003103a4840690300b05445c1c00006031004002810081040750894031010301507108002040352150003030507003150000900350080080d4030800d0195a540100c034901e01c1480c0c02409138604841c5011b005010f440700903410840360400850780c5100c81c002041e00040d40d40c49500420420007128a0b00640d107000c01c20b0100c00e07600241c0b107840e0142e41810010030101d00302000f0b503011107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 100904280 1250 100903030 100903037
    0x506010c0b0903040b07030c11120304061b1e110406080a0204020306060d0525020a1707031101051e090a020a150203090d0b0604140f01050d0305130b070b0c0705030307 74
    0x10303151107041900f0b601071034010040841c070101e203113000d05902184129510f40181c40c4a41d48055007018000e844064a18406250340200310030400b09106000c1d40790050140400d9105600c030075a0b41005458192000c1c50480101c18a41d100703015150402d40c01c80c010458041003000d20b818100d41d1a1000d01d903020744916404400955940c6401d412100000e6450344100102e00d84054100b54100d6904841200c810600d05615245400000c006114941050121360f030030040584006165100d04421000c1000400c4240404402401020702820018011920103400c003480c4914110000380100c40caa801a1002c00c05030711400c2900e001d642d01c0c902100b5050725081420381c0380d4451841c04540002141100d00e087c0041c1445150160404803000d00600400101140840c801030fa03200e0403501912004101c00d00e0300c4030241e076069100f4200603051110400c403400c09135032240c0c418495490005400e0040260b4041d0302e55100c141020394a041c5451074946640d01e000081070712060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 100905530 1250 100904280 100904303
    0x50c06070f0804080304210206030f0c07170915120c070309170307031106040b0c09030708010203010b03180304080c09061203030a0902040b1806090a020c0708030901120506010c 78
    0x2800326440c070007401d090b040801a540c42e6500c01d0220f0352a0b01c2032140c031140500028005589036840f003150303200f0b15001095141140c80c3c076544885444005800c3c0704140408114810015007890f65425441c940450321a44408411082c820382114820020400c40c0c0d041220820b410a06800d041d040880088101d484a02a00e000d40b101e8403950002e503804002c0703100c64035603280004010120302c0e100390364004c91041100039480d0740325015039004010b0101840040d400d0100b54020300a6004000e00b2109295640c606150072a0f0082c1c100c00315200c03001042009200400c10440c00b0502d102c4001c0d45010b2a10411649541e0ba07042c0580c030540b11900440c980e0b0f03882c0a55100d000c210ba00c180d940d40d050080c1e005004040e2000300b2405641801c544400d60b14050345001c11b200060040f4a1103659903a04212207804010001460302d80e080c840e2842c00d0804119100281580c18011540d070752041002620240607842500010381c104010400280d80c8040814a0141e105030540c0a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 100906780 1250 100905530 100905533
    0x6080705060c031b2103041a01140d080f070b0405070b0703080c0306040204150203090a0e06030a020402071a040b0405070f180216060f061a0301032301060f0603020a030e0a050c0607 80
    0x242178110203400340d9139411240d840118080c460003140924410f480c00a41e114052002a420100900c904c504100c00c410103138000707081410b880c40140e0311420216103000083d08200800303403c02c00003990004242010042040340801c25480501a00c00300d56043c050295001030003000001c1c00201190340c044081545621140c0656029081e180040000f00410480096507a08181c5880d407191229000008280f5000e00d661f600410028001d01441c2d0000e4003400007079400044101c91f201c480002e485890991804a82c1c0a684107080d2031015003442d0802c107241523480c2e042000b41d580000403c000070724110030b2034030740c1d10300001e0050380314504008800e01000102e00081d1540e4109101c1c1c032808081a84101c094410b80010203030400c044801c51b004901007404014040a0742900789283c481080d0700c080d401080901c0049049030f01c401c0c1800c0800300c6540040d000c03e4000c034880100c503816000f1040c1ba04c61542c01081203800c1603c1d080e5480c400040401d02a01c00003d0f407c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 100908030 1250 100906780 100906783
    0xa1505090a060f02061008060c0a0905060d0b01021c09060c14060f060312090a030b1b0703123b0c0301050c0c0c03070e0103060b0409021306080705060c031b 69
    0x24031221000344111451940d40001602040c071072031a41e80180150030002e1a44120340c8110410f0b07600000090040344e03203840070741d551503004007860010b01030098030015981e40c0c0e1000810f1001032909000c20000c030300c10000b82c6040c00e031032108411119004e1841003056448445802150880e10b052000c1d4110303400c0c0417003021a0340a210700345004040400c030400f0000e600700b501031803094089510b041809000070225000da000101d82c440040c100401c00b0444050300d080d04030361710020142c031081c40e007000315009601c50003089010602d142e40240c0d0068213441101c2d00342640c05100902d0300c00c02c0042d011103421900a0548400142d180010140000c00c0707400e01480b0301070020080c904040d0030b07000e946d801a2011503a644140501c541250174041083e10441c2c61406c11100725074210b40e14407010700f580d402925000340e42c03208504050b0361858180d1041080e08000007a51a04004d00e103400c0031125000710303002d00c60400ca0103814450001c00c81d00f0981100054940c82c201300d0070ba0301d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 100909280 1250 100908030 100908037
    0x1030512070f0812070f030c05040b030402010302120103030206040c0e010e182d06011703070807050a020618090105040501050319050a0c0602030a0f0e06040e0417030c0d0501080c0a1505 82
    0x1d0504040804c4000300800c4c0500481d0080c11140c0b00d030070702c030840004101d094520384d091940c000741f02480100310a61600002d10f8100d40305040150410084207000d00c0301d00f034264000e0700140c2c00f4030240004e200c21003201c000500100c100b40e036241c3d030404498540782880903004a8840c6229400e01d0b2070440c00380045003140f10b204142d1000307844041c1305141c002c660340100505038040e4800004140030ba0302c40c02e4a641e540580610b0610209441c1c0305101d80041800380c4040c01030401c000010b94461000740055841808000c0b220505401030200704441600700500981c500001070040c1c2e0740015405c403141d82001051954000c003844c041e420903140c0780c001001141c1d00e510104003984c0120203850b190b031080d690500d1381504610201c41460310019010f4120800b04402d005c0e080070380c04c031540e0250188000d008012811800c00c40b5503802200d0784030207040003043c0801da04030140109401010900010101211441c00150303014a40c1d00c100880000c06641007000c5a0044066 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 100910530 1250 100909280 100909283
    0xf0405100c05070b04060e040204032a030510050712150504091e030503061c15051807080c0f03010504020a090209151c05061002060103031d04020409020a03110301030512070f 77
    0x241c43e0029a5540301803401c0d0030074080e800202e12040311003e003074100340c8281c400700d0340c1080d00844400d034214102c2a4100c20010001c0b52402c09000110101b42c0c208141117804407007000020711850400b070010011800d441c16994884c2c289600240c41340300c0c46000f01306998007100d0000784207045280c402e00303e044d22500d110710741902a08803401c0c1034000e009944286015203001001a00000341100d02c4840a50b00030040b030800310070741c0e5602c2e06941c0301035448100c0f0054180744034074200001c0c0c90803100c3e50081c58158440d01c43c6006604004a2141300c1c000260000d02c858200ba600140c20074506000f000107040d4042a8142c05580d11074083c4080001034540b99901d134200c8001105111703d01507890442800d1001240e1103080c60840c008050111358045c2040741d080d56021a94210030840c0c2c400c8c0c0030b6118803244410360f2184010f00c020442c07100d00680e0b65461900107401d031500c0c8140c03480600818130040021880106141080e0700180c040288d4a07109864110740d0407180500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 100911780 1250 100910530 100910533
    0x20c120709150504050c040b04061202160c0504061502070306020a091203030b0f100e010807030e030d090606050109080304030303020a090b16020f220506030f150114060f0405100c05 80
    0x48049003034080782e500040d210306540130302155403011411500c602c0b0b24841c5040900c010042008860701c00d100b0008001c00f921805032916010700021402200048401d403111407403000c0421251429214550003410112582e03c1c05840c0300c035019485003d24440a810341e03400144c0586414400e020103405010540e49640c0c030340c50130f810002e00815800d030403c0d000d00780c130780b0800c841703450a0700d07090048034400d81c1c841e00264000001141c0400e4040c090400340350b11440039851081062014080c140140440018401e0070b038200401500d102e60300090503c10a50000d000710b403001320071602540c1c0c0605002d684c41449500403641c0314034030f030700010b6170103000700d2400d05a0395044c0b0140c44c6207000301da02208400c2031004020f0100e2421035042e01c0600b007064115600d07826500080d51107903004040d00c0b01011524032140c141782c1ca5a8022000140920061020001c12603480c8680e8000b52a0f90b0306180407010a00c045100b140070740f500c03490400e030030f500d1028800d400321568070f41d1060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 100913030 1250 100911780 100911791
    0x1f0506032a0d0f11070206090406090c0e0f09090c09150d060e010e0d080a0e030904020a02151006050f030a020c10020a0f03090b04020d02030f010203131203050403020c120709 77
    0x4001c5400c540081d0390b019000c5080403040080354035580501c0111070081c1c18042d00e800c2d0313264204034881d031004041c0f80d0800e8541a000504540c1840313805a108515102c10a08003510002c10107000303041e40701688100101c07400e105188000154601055006a44407400d58a84004090925030b102072250b6011000c80142801c0001a402c11100880e907030300213100100082c0c0e4410345039007d01040d80001125000001c1a01ca03203a040610030013009020f403403508844c18049800d84e400404000b000d40e02180d9031034130703850701c1018081d840800c59081c014500d0601100410501c544280c0441c03440000c40402c1c112041641110504c48101045491080101185d24060f4100c05002408180da091028144600070300905140b158072407400250b9035240d50800a442e941c10009136014847e0f07811140c1d207041d0910080d40035480e00c4401d21035245551504603814070300c0403d0807007051304000a000009800050301c240091003112601a0114409886460050240e020103000340c14074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 100914280 1250 100913030 100913101
    0x106090b1c053409080105060f1e0a0e1b0301060203030a1d0a050a0b090109080f072415050f060304111309080405030d020d0507030302090103140a0509061f050603 72
    0x580c8081c60401654480316a03580c1d03201221402c8807011a88180c00501581c01a1480d161030b2030342c510100300c9141c01000d031341090340100c0c080b400e140d001033301e60100800c240240403c0480c40b0400039802c90410a26540c10060029100c3c0800790080c1d045544507000104001c5070a00043ca4400500040fa1016078190901541c0d4000d407407010343c0d0089809002c907086003418000c000c03140b6008a5610300e0029441d91920300d940c818002500c162003200045890b9a880f02d48e0104404450040407804288100e5800490f110300c0d84a94451420301c9018109a16900d0541e030744141c01c172206045016413040421004003601c864424003510b415021020032280c0d801a0042d182d094007102c14028201500b640d9404040180c600850802d11521000910940040c048101c0614010407000030f0044104440c40d01500c01d00350761a185c404004041600700846030340040901844030300144124040d4100741d400b40102801000000005030050b000c40e000d141c8201e007940410b100509a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 100915530 1250 100914280 100914361
    0x10031e080309030d050609061011030405060307090e07030213050603060102100e030703090b03010506040b0a050c070611011406090a02070611070f0b0f0403020304060c140f03030106090b1c05 84
    0x4000c07602c4c1000e15000103d5150300341000f03254030030500900400f10541200405a40b924460300500600303100030000455182c07030f0030001d103001d40070540b540d8058904080f0442c040d000001c0c42c0c4000c040c8103009244009072407052003c12200300b0b0f40d001c0d540e6164400100d00700081c1c100310800035410400900d100400c000003c6c84800d000c0d9a42a00307454a451240b11184006c0c400c82d648460148800d00c1520340030b800505001a01c4e08140d4940307521b00c1d85850400b4420b52102010801940760361007941400e000ba09010b811000d132140f2545456000210045005442a15030035030120702082080f405030f0040340440301d019092901c8110310b2800580240540074101c40c545140720100c2c41340c100d441d0043d0300403a415006141450b00786901181c11000d044c800784c3d0207107c00f010024040c0d106010720090200c3ca031010b10350700d604006024040c014507034800010301100304480440742c0a0074203100040d01a4840128850726014118128142c150002c044e500b80c1c2000b002818140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 100916780 1250 100915530 100915537
    0x706061e0603020c0307020906030f0a05150703020a0c110d0f060c090e0f1f030f0302011b0507020f04151512140105090708040510060803030103020a0e10031e08030903 74
    0x90401000d003105841e55811070030b0380101c031395200d2150300a214400c01407515140990b8460805800c03500e00002c1c50305241d00d04070341e00b001510b0726082010050040c504510b00194088000d00f01075140010f160380c01404618584005007140c460072a000c085a0f0310049669030003900010800c848944500380350000300280441803000c65030307915000a440a24440c0f8074480d406482c2c40480344da0703a211702440220341e100b510f030034403056010b030203c0015401c03500522403c2c000c2d03000181d00c0c40d00009803a07140402c07003400801d12000303020b06001130f59001403011310860181e0700800d07110b0101c00500368800041d0414040b142c1c020700780030022680300c586c89503c038481207401d012884485d1400e03041c8400a0080c071780c0020036000015012401400d890b03801501c55011600000e5400342e40104131210f80e009400c25030030000041003545860407882000c0e0030707094503421403810040d181d5000c603801d501c00100b0525814401511400c0d1501010ba05150070401c0786a032880c2a00401ea1a5071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 100918030 1250 100916780 100916819
    0x3090509070206060d080306030a02090403020c0102070803040b0f0c2107050c0409080702010309020d060501080f2401211505040b0a09020f01050c0f0d050a020f150103021302070606 80
    0x146800c000407030071480000c400b400b400c400f410480280c400c40d140c11400c3d82c001040c0ba6018446d160340640140c4030240c3d158481d6020364040c01c1c00f40ea03010002401c060442e4003040351a40240414080480b5180481d5a1011682c0041e665499006a61810400504003400c003075420f4201c0c00905101c601c00a010f014410003c0e284031180c0c4404110407240c81c031901802240d824400c0c0790042d40039034001c40c1003074001840f441c505581c0e55504000d6800c243c014001da600801701c18200301808111101c00c0c1368420061005c80702c9600451103c444c0d051103041c96000303035610040e043c3c0c04fd98185400d100d130032055000c0e032080c1500d0848040c1005a03012034810040300c0002d2000b0140f03200b0150172650007850241442c1ca00b0300111282c1c3c00c1140003000c1c038020945225202c601c10171640d102c02c101c98440316165111749101909107104003540788015004402484207410300705100c6410750b030f0b04442c40110000010000c3e0006d004080300207069034a0608081340e980940078a0301201c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 100919280 1250 100918030 100918039
    0x30206030f01030b10080d050a1205270307050a12110d090f08010b0a0302090604060803030901090209061f14071202070801060504020703080414030c030d0c02010f0b030a030c0311010207030905 85
    0x1515004450070440c500c501c03c85140d60030502c00a441135210300b000748002c9c81585802004001210004d03003c41f0f9069a40d09200d401408550988900e58520165400170b4600954100030103900e0307503034a81003400c42c01848a480c158141044a0007134540141d400600700c201c5100c10101100a0105840c5002e0701e900c110007810000342d25a41400382c103030003100190551020502d1507013807000d60040a004142e10a407100408240e0386403c0011b14400c4c0d11840021485013910700510041940150005009485c0d0500b070418a00750102d00c0a030780c6900b454061581514039003503d0142c0140745004200488210030103488503070001c0c00c8416600b55a00030031203940d0350320400040f8810410010086403058001070041400303a414410186902425039281c41360031807009007507500c820101111180e40310700703d0040e40c0c0d09210f060a0045a07007410007034600200002903503082c6501c0c0040c01c000300904d10b2001c05110301c4403080b0b404480c00c020764a41d40c803031174050049107641c002e0078000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 100920530 1250 100919280 100919303
    0x140619090e0f011d15031005010e0f250519030507020d0207080705121c08040c05040501030f080702010306050406060906170f010510020c060a0503010321120b030106030206030f0103 80
    0x42c1084600c03481e048944410400d0b12003641400c0100010310014502c1c0c26820b103860b94413505440030300c4203d00d15410704070002203035810550a690f49500143c45403030b80441c0c00007005510a4008500404e083e4802060407001108040841e0103103e01c041000c680580a03c01402c0c0c1c5805800480c020401d603029501d00c012482000c0f82d44030300c0c1e03104100c9a640055820011070500d002c0107182050140161081c243c1c1030480e032007a8494a4540500145010742040140503d0201c41805440120b400b4000e9514680b40c501c000740f201c030805068210001050700440e030295100000414001c4c0c810b100f80780d510391300502100b925100719400320302104810030400c01184aa5803040314100c522810503401c0030b0a1101407040c030410b480540c450703000d12400965404001d400b0720034a6580b815900e40c10351810000039a2540801601d40c4000040400d03441d030020003240c01c88902c1d82001490b05200320010b03002d0b000540c406504110f001047c841c149204e020b0b5135042e24010401001c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 100921780 1250 100920530 100920541
    0x40902040b1b010e0c15190504080609030703080601050306040906050f07032f1b1609111801080606130e0601030b031b0402070827010809010c0801140619090e 70
    0x99489640b01c40b402038000c5100c1e03411700d2901c0540351840d40e1288044070b04140740003540d0b14110340e0142e501408150085801c009002c01000b031180d10140c00c2c0f018504007101070750302819a00003d807240e4140000400054450b8480d90b1003560400c1c3c00250600440c2440340da00104904141d0b0740000090030b01250714404035048400200c1e00c91500360305840007201c000e00c90400e070005039908400038175031300c214070140004020644995200c01c004100b85441d0421180440314200680711040340c080c860004603100f4820702c0828542d084c02c1281807075a0740400500300d0701c100c0d0f03c03901880440d20004905070a05e031402c03600c92a001e890402c040006401010754038000c1c8c500d42d43c8030940c01520800c090810b90040c2c0b582078456401c040c00c01e850016117002c040c0da590f4070b5a00984076001001a1903a1000340c55400142d00802001240220319004004004c140600071960030701c42041031140e212182203500300c0e2000303c102450403d44c101c0040c040240c80c4110100784281401188 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 100923030 1250 100921780 100921783
    0x10306050705040b09060a02010e06010e1e07021b01030e0f0601030b060409120c151113061107030215042d0806071713020306070908060c03100e0408040902040b1b 72
    0xc003510b03514051340382000640001c120385584000d400108554030342c81c14001c05d020401c5854081c021400600c0c1c000d10300a5410040780c1829540c500c0200c03030260a02074010380200301c0700401011150241c540e1071a0a0059000d00040640052944500c01c07840440c1400440e28905076031040146841c19180e003001c0000f0383c1c1c4150700c044c0c5211040c1441e07038942c074005d00b084020313a0711070030442114241d001c800104488900000e0640e1260010310b200302009010030350360140000d0705200f4060100c0e50b04007503440185008c000d0051382010340100b40c40c902c0c01c003650010241c003103611102c0b10b840c80d0b20a0075401107041c0c189880748440340c0443c1e02070020924501c502c201d5511003035040b0301648200b840c0e01c400307001c0c01c0b40c04140c00b01c000c002d40c038140b00f2244074034469281d19001614000c24039180100040130440c0303c41050050010703800003c030740541100c80300600c054103a00c507818142d440380309a5002b0200d480c800640003540603e190040c1041200c014501e88543c0745082815 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 100924280 1250 100923030 100923037
    0xd0608030f03010b0d060e040f02101106060607020d0b0c0408150603030d1109100206090d090b04051210020d0b040605010c030c02040f090203030d050103060c020a0302120a1412010306050705 84
    0xc0c41c00441c1400140b101e4030703c00b0090500c124458001040080d62030215141d200020780307040d035052034040c2040c401d500745108060214581740c5000410761010701c02103511040094030413841010001115000d541e00c448071602c3d0550020f0b010304540c00c041600306980c0d0701912400f40c0c0d50007901069060b46403011000c0f489110064040d5103000032400d59080200011010390301c4400c42071149039038942f01c4100c600308114154000f8405814107606140c50302411220f09001c1285280040c8190800b80c82a40c00f1244181c40c1c9401c0d014544401d01d0420741c04101e60b80c402c51000c101c141c2680410b410440003488140c1e000c01c410f640314001101c175800c8092020380424020880c90b00142000e501210904119001c001100d01c455400070307081d680503880c107008443e25072006006210082c4180043d2420600062446012941e03000e5224102a03130160100c1d0004110701401c1405001d501151114044040355280c080604802c84480280000e60b4824a40800104c01a000742c046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 100925530 1250 100924280 100924297
    0x5060309030d09080c060a05010f080a0302030d0b032505210606010c02031903030b03060a0501150c020f210f0609030d09020f040617060603120406030b1503070201020d060803 77
    0x80c51602d203107400484090501e038403084549080410119580880a00882c2e0040c4140000030595526006095401100c10341003210b01d9008640010000780e0008200c8400c800c0100012494040b40000242016030141c400c10018099040650f40c201c80141d0980c1602c0702201c4910b62010020300e100c501108017248010603502440c0810403a6000b10510360095200908803411283c0f50101090ba143c44001c04601007034584100c6110740c40e0900070590b202d16011401c00075585405c440010100c105418002442081c01204080d515143c840d2540700d4030180042c40240c0d204d14080740000703032201114105020b00641c00c035924002044103409110404020750400c0804851640101150202240d00c00350481200e100e07500c03180035200081035804480c01c00440c0448019080401c011300b070620980166038100c1722a0911002c2c9c80581d50b8030325000074088181408180c1e00c890b4524065070348035021040107a00c560540040010500070f0100748803095a45011560b2409501d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 100926780 1250 100925530 100925533
    0x81203010501091221020706090504050705090d14060c0304060f06080c060a0306090f0212010f0f12080c010f0b0a0e06090a020c070f03060605150310091d030c1605060309 75
    0x10401a49140d80041214135000b4502d500110b40d04d103e03695401401e01d51800701603008110304219594201300c2c80802044156800e019a01e0400c1000700b00348103421441b40309810516111052080203a03162002c441e46908a42481c1806615083c043d001103a013142c03101e04165140005002c4e50041204031411080102000c0740c01804000f40354229464101c2095500c41001501031300074020114a550904401030381d0b42244404440203860580007a0241d08220030200021004c914001d400c403100c0703500300140e007101450650883d121300407186140e982441403408481945a005110761001100c1c90000143c0e90007240030381040c1203801c164000351610016032a0403c980050412039460f0301951341e0f403a00e03a007017011101d8640d0001d450495444206200c2414001402045c0003803000080341140b80c00050382a0000c40d9000d4014000c0d110513001c02d0b04a402c0d00e501141000180c2541d40784c002c8002c00c00c2d075500b038942c0c02070a01c4021040000e03460811800720f90040c52840d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 100928030 1250 100926780 100926797
    0x60b04021c051515040801051e0a0f110a09050307050a06021f0905060c0415030501150e060f0705010f1a030615030c10020d030c0f0c110604030501060b04081203010501 74
    0x22003070040500030840301a820300034404402595684650780384101e00300610a071104e081030142c0e07085901c0203107010420700f4100307803541950a10300311140c0d0091003201d020481e01802d0441e40e018142e000201e8210313110102e42d504055810041c0300b41036400a6044941c078954500c100030200f0001e1160202582107840f81d0b180d4a010301100b801030516260300401c00c102d041d5659450710500312518a5042400700d410300240348000e520604c0840315103000e0107694107114080c02d00381ca42c1d00484046c0142c4110504603a00d4180642d040c0c0384022200c0c0f601e40d8401c0c00d009000e000d4001200101d540340418032030b10002c9108210f04404005801080260343c1c0040d60748030b1445e01c0c00841ea01d445012170145541c0e07200c1a21010054040d4003074500d640005002405030b821400d92601030160004007100299400a100c00803145c00c845441d007150042404070343c1522444c5c1019015508000340070929450100c020800c41c0c10b0841210030300303241c10100041502003805402e0009207140f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 100929280 1250 100928030 100928077
    0x213020a050d05040206070507030b240913030207090c05120105060301060917030906180306070e15160c0312021005060f09040809030709060609050d080a03020c15010603020304060b0402 82
    0x180e103d10b51051020303100d00d24110040c1c54091500850741c2c002c4482e9014101009a2010000c00001005003d007030303905124501540080c0c21a0402008801040390900c601d105052081002c0b000802014204020444544000615a0b80701684000314582e40800001d09800c050085134125447c81d0b0b0341d0b2225905200c040010043c503502040c4e542e2000780301684160f940e0380002c0844105400250a240c2029030600d81000001401401841039a50364041030b91150101c40b002e60300035030318082e41c84242207808050141903640151041541203000300802c03000c40c0b40360454840b19000c1341d8910b1041000802915011a0303510381140c0000c020302154200100c190760018460103000d03003000c034104042441d081070380e849240c035507869039010072055802c80ca820000d4001900c607400350810945415240707209640c80c25080550010f95000450310500c426a00c2d0030321060446010359542ca4020041c0d041540c09442c420f180210034001841c091003100d000e0007981030110400b1828 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 100930530 1250 100929280 100929307
    0x60b0306061905041a09120627010608150708010b0301080a030e01050f21130b1602030405031204090615080402042a020a0b06060c060c070c030804120213020a05 71
    0x81582c0d2406101c028400411a12004180c543e001c5c00094060703a240c24052080200544858071342080c240c01001c21301c50364580d4403070a0062500101070f0b0502d918820545540103244d2544519414020343c1000b2050b6403182400c140504000d90315014140d8a882d030005082c0710038400c0100c0c51740b00d42245c4002038000c85000f41003040504025042001c0002d00880b02d0380040358080580d000000c401101c51802c5135440e0b0090420914071580400c156603618030303c0c6001e4a0a10500e5050742c014250b5031007001210040e100140036507070b06495804810781590002c2c0101c45080d07003007070344c089002d003412189051026280c0d5184969600c0d20b8013803100400300c12000480da10f4504045480c0300003210001d031130300902c90b130091940c1411405e00070180030010388503078070801c01004100c0c280c110010744160040d0541010b04c1d50348682e0720306009440c407641e01c02000789502260015544032030124940d5000d00944800d010b452108014004a00c41c01d08807002040091103200008542c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 100931780 1250 100930530 100930567
    0xa23040f110a030321021303080c0106050418120519050307140a0f0219020d0210021906061410050f070f0203060901021b01050f04030e011209080c01060b030606 71
    0x1a0262404403185880803a10b82c4081e03802c01e8011840310344040d500300c00c2400524451060f00e810450414240c4004144e018440e031101034044040400c04840c401021340c80300c3d00900c2c00610401119500c10903c140e4881100c50070703941000003003001100e0b540500101c1b00f41180410400b540040c009034142c0e02c9410240c400406c011401301500003034010301d401800d1500c40e98407241504508076000134a40041d0412a420844480d80080f00507111444000c1000798112650800343c1c0b07224030101e00d40009402d0b1609003460900d0480d060040540c4050140d0394040500342144e641d44013413002501502508000089041041c48600601100a050032600c1851108251501c54001a18084c42a184c402041c2d500080706081c0008008000f0341c0019000020320007403030f001e40d24610760f4000801c00740601005d940142140e0f0710918502000750f0b810502041440780c1e6048c54007086d0840714803c00a5840d265012502c45907031000d40340724140003400d051401c580c0310140005082c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 100933030 1250 100931780 100931783
    0x18030a0809150106020f010c052503050f070f0309050f091b0706020415021603080403020d060209180f0705040e01150c0804080109050c040b09070e0f0303120a23040f 73
    0x42c1c070004201c89600c00010600920150303004101d9150410640e500b101d00020080040c040d0810506406800866410070904054800504510550b0405a980780320700204080300540c0002d075075041003035044040180314041e90300c15110a4a503014816068880515194490072020015109824008089400c2003003a4441030400c10303655552410703078120343c0005010f003142c00152000240d040110f002c1c9011424100039801d85146c95107500c51056000203400746000c00c00007000e020242d011554a0a030152018428000d5200c0070074212000340c0b140c4965560034401b081920b403041f000c0e6410b441409121a6142c0d180001c82d0403000c04c00c0b56020300707020416411b840410701a2014000a0450b400045080c51051400b5814501c5502c14280b269203041c0712200c0c0c0b51101c2c854140c0c0442d0303e060400c448401140011107040000003425810700c40010510016142080024040c650a0109200144045044410000340c4a0144203074000610015001c240030054280b0702d40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 100934280 1250 100933030 100933033
    0x1804060608030d0b031506091f1503020304020102070e10060302071e0b04031106041101050d110301080307030e18040f0c030b0f01080d020705010806040b13050a0506030618030a0809 80
    0x45580d01c060600b035400c1081c07040340140d5550740c98089400c3c02d000915003c1c5210980107003515040001a6040501424243c0e07501c407104403000d8050807200c1070002600b80d06c51949460341406c08010040d41c02203c0881c0140203441c030005208480d4190540200c01a4520440c240d080c0f0f02c0440003034105100c15110300302c00100c000010ba4000c400048a1030003002c5040c40382c585030802500440920441101d207910500802c4040340e070401c0d104a042d4800d29161744d07168000d02c5454054840246c000104040c00000003590310400002000340e54032039158411200c3e110410028040d503042502c0402205120001d03000411800c20321409600c0f07921898503150b181e441e003203e0540103c0703845c0012034406005101e40c250070000c1c00700504541c8020424a802d0800091000c0e101600380f0340200c0c0c580090f112655581400d03500948841d280030401880d256165401400007a50054040d005890128103600445010342e12041d144500441c540b594601040b0f038116801880d842c0e45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 100935530 1250 100934280 100934291
    0x50403020a03080909010b0a021e1f0606030b0105120402060f070f0804062a020108091011040519060507020913050d0809010b0f030709090611030403120c090302180406 74
    0x1640c8400c85003010b180600249a1104a00c9050081d00311060304a400120010311448003480c3e4009034600c5001e001c0c9842c0d40c80303000104240fa1502d0421082422400c00305c1890800000c12540003504850444c0c0d07062120154030b000540b007a01c030b0340c2c0994541048440004015013020340003001d00408101072030b403410460788c88049070501182d03800c45004900041c200420341d445100324099003440c0120820000032200e80c10300099407004001c3c10b2020040010f80302800074000d138202d000030320300c0610039002c8040f0050f1596200340034007803043c4120721080e40754001901342d0100352001516000c0c5002011f800304181c4800044c491078458580c0301c080c100045d001d00c01c0c05240c8406031584100c9041c1100c1d03041c2520703d25801503001e10182c1401040d00c1c2d03400a00714007182d104610000300502182448805404030345410014884000284810154000001414140c00070341c20001103072161400c07924002c1c5840065030002031005400c00c10700071140c940f50081e100c1c40c400500c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 100936780 1250 100935530 100935533
    0x1020c0312030105030709180b0c0904021803070609060203031801090c120b1812030a14070f1d0a090c03060513060e010f06080420150705011811010f050403 69
    0x24251803141e151000789400320040110b42070421141000d866090030510070201c2d209291011fa85120801504855440021a001078000800c441c401c080250041d9518140000c00c408404000d00f00c80d40648138001c0b00080030351280000e1001d5502a5003c0d40ca5a114070020440ba14034090b00f4241e99584c50142030001a00246084010f102d0002070000c4070041d4200319041440c01014428601c05690004c0542c90007c5042110395030494001a01c1e40c541925800007060150682d03150100c0e0f4a0611186542200058442c481680e40707010710b01500e450070702e0f0012900d1407410703000743c039140040c0140d00683d00f240050320078501d00041c180307030b9801c00211300550700e00c40615a950f5601e014000000c025030074a024000d000d180c0030b03080e450310030005e0080758010009041200741c140d03031040b1021000d07102268140000c01e11040e03005540c13013034801640034403422102c540c41c10118440d0100140041010b964010403e0403980c400400155a10146540d0880070024100030200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 100938030 1250 100936780 100936783
    0x40c0e0106030c0206180d0c030e0303040b0702030f0115050d033006080c0307050103021c06140103060801051501050a02100501140a050102072304061518050f0a090b01020c03 77
    0x14001c001c50380c0d011411030301550010b8200880a004060003109210401072008000517803000300002e203140090201680e400c04a5880090224883d4103010000d800aa14070340f2030044c002c1c140c000c800762380d0707010401c0001e01d0803103011074141c1e1601d10710f00c40d0030482c42c9030659603074a20b24002e00380030040c16400b610504500d0720490102040f882c4500d9411980c105500c40c40002d0301e0410001e08200d184100000e1b6141503500c280e904040c2c001500d80e54605880c2e03494a000792029505021064035800c86144455170440322070700191030b00c03000140b48a0b05010320383c0200d060f100c9824000c00b031000110344e10303480207034454154030075100100304004a51023054024010040d140808644100420000d0011503000300d0455004101c103102c41c039140320540a03264091019000048100000714015150300d44c00401e0104002245a0840d500145881c0700e86040d0080d103042207889a007004038103624201c0d0990050f8111006104501d403d0b03200030440c9205004035004140c2140009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 100939280 1250 100938030 100938059
    0xa11040e0109030207081023060a1e03060b091611070f03081c02090604060315030f0b040506010f0b0702210a030507050706020c0d06090323090a09050403020d08040c 73
    0x46005a01c44e40d420801b42200b80001d4404011140f014400d4441c00491036011045000c00703200700d2104400441c1c941d50328034001900030300b0f40c0141c001c1c009402e031080720540f003403510060716801c0c10200d02c41090b29004116512030b54400088041c3e40786026411100c02c030500b4608000c0e840b40300300100b401d8545d12043d1000b103103d40e400d01c0d40c802c0c040b149030b042c00168600100c0340d180140000402e5139100310076202959024500080d1401400c03d501603202170580c0060407007608184580240866104038520450140c011181c03142da03030351340820b400e10007442981440d0300c0c1441003900511f064101e40000b003011004180a003100303a060341d030905c046400101c001c5007001401d941000f5051040000418031800901540c40e02d001c0891003026103c00700500c0b90780d80b040c1d800d08050043d080d00b079100d050303203880380304004c01001c00702402d51003c00528451804d0303240001d02410580925131086501d5030262000003100311043d030319100054003c81e8118540d001c017042c082e0001025 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 100940530 1250 100939280 100939283
    0x303090902070c2114030403020a0302011101020721030c020f0717070e0a0b030d02011401150512180708062208190503010302090105101d0109080f0307120804050a11040e0109 77
    0x10038409142490021045500c5d0207107040079400078041000503a595020142c1102d4080c204410080c0b0041c2c203240c0240304421009019000760300441c1040481400724011260458504004402000e0f40a0ba6115001d002d40201c552082c181440401080c0c2d0720a1079000c00d4104031940d454480c00d5081c00c9c040c0440c0e000e0325056450446001514003040545021a0a80000c0000c982c42000c41d22401c07005000301c004003055104c00ca010b45208404580310030100900040d05400c02e544490202e20710208184021720403075501060001002c2503090054a0140002c4080e02e001080b10341d01c0b80701c0d594260b4a05c001842031421140540a101d000100e880e0b48065481d815481003106076001a00404e01907090a03041c907241540112010094240c111200281000c0340310040300c82ca400c90300000c3c03960040c9041591b51042c000040e0480d41d11070020211100c0800800b00d4820b54101c0e0701800c1903108103caa00414013184500103c0c100180002c685003086110303150a44840500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 100941780 1250 100940530 100940579
    0x1060f0c0b04080d06151202070206040806160329100c170304021302040803070f0c0b040b0301090e0d020304060c060605040504050303150103050c070204050903070b010e07080603070303090902070c 87
    0x82d5082d11303203100d1090001614605250210504401c2d030300924928031030000f20807540d4001101030565541e002550004d2040320121600c0303241c81c21b0700540b01900310811101080c100481050a421000c8100c841c800c40004030554103e80d10040080070341031200c0c0401445595181c0340045134800300904185c44000e184556241032502c18004022200203d082c2d50610502052041c0a00070040725040c0f038024640c0582400141007800034240070f94030a441404002400090101900d8007460403034840403030401042c110703540b203640c845049024880c010b0b0070800040c42801d0140300180d410174017035040090310076180d1300400d084400070384080d20654004020411070151710b001650701a01d00307103030070f028908000c401f070070550040d154028803030380d00e5000140307412400700140d03141150480812000c95070b40d40184c0000d1142600e1442c00923800b00e000900794140055290102d0b98956681c040641c5801d2801000b908004000c03100d4400c02c9800054900b02d20658402e003021510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 100943030 1250 100941780 100941787
    0x1914070f0618050915030f010606030f20030c030405120a0c060b01140f09032803080907050a03080c10090803090c0a12021002030705070f061b050601060f0c0b0408 72
    0x2200504001040c100c40b50b4036007840b0300280803036210750b100300344c00904030403072840500240d1000a041c0181140b5002d4258a400e4001807450b602d40c100c0001c0f0607054034200036800200d2a080030810440b02c403440c03a90010804a180b000c4501d00441d4094002d1064a50b408110a503400e0310781d000f920092b0004161001031006d11209208490050310709007014011025100003104050140c825040318508000c2040304203510180110150740f01300c018000b214407460b021031000d040a0b000241e000501030000100040c0c0000780c40020703a80003c1184c08040d00d50b42d10391607658031440c0b00e580e06018001c0c20006256803030080000c498460596a602c030b281541c0780601e040c0c026080103100320244441040750202c05000002d44980503a010b58600d943c1c440141d1031441051801891071040c280d0000d81c090400d0410400e45000390341d0340780c201d084042e481c5104d070000e110161190300120010884280540c440c0080402c0c1420400030b030b50001d455054014504640c25195040d000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 100944280 1250 100943030 100943039
    0x20a05070803030a0c0206100603020d0b060d020403060b01020604050a0b0406060312120b04061202092e080d14030f06151b01050702010905030418090b0403110f06091914070f 77
    0x1170081010384e89651000308018545081040c01203501e0b4400d4100b41a4006a0007040402a812203401ea50f03019082560b500a0400010020b501c14403007035411604d440c2c2081699840403c4007801103422500400d4072a015403601c2d0700742030024204840c0385564070700000003d42d042d0010b003401d06094a03125085101100c0a9040e10600716445114519100080c407010f0300c8001a081c602d60103070780100541c1d4800e0198040f294103c0100003800000d105001c2400040c0d1002c4401e481800c401d4580100d9980001e40b110800f41d0000300c10030000307000254048008109213a41b00740c0c0108015080d45450f0517109603980105c0d8808140da00001c505040c2500c00d024290f0008003d00c0200450643d54885075102c1c0181c2c06410103840c4045850100e800d03c40d0415840e070741d004940c44443c2d041500c0d02600c404020b9241002c0c4d4000d244112209500104100b84100c08030070180c150000210a81c0d011060aa0800c85903400a6002ea0700002c0080215201800c4204190006c180c00c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 100945530 1250 100944280 100944301
    0x60f020709110d02030c090418050d0806130c0905130209040e070303200708011406090f0c0415051308010e070b0301290912070504060504060b031501020a0507080303 73
    0x101e40000d03030464140041022010010001ca070002d146900005071030781c403030340c07a10350031449584012503001d414441d64089002c02c0d0038040d40340f588100211038240c200b10710255801007040304e04543c00451148124101e000d039400c50158000345141c54a00c8076203881c00651000c01c45160345180c154041000203071414244a209840300408000b03000f080d21356940286400801c3c0d881541289816031044164141048111f018020280003441440c1c0c501004080d032150403a4100e1058142d040860b0541c80c61f1805103004141290368545000c0c03d202e0000e40008281c0c0b1503a0411504101b6401e1018100402c0c1d0090311407000041018165640268074100d040d030003011480708100300410075128030290380e6500130f50400b1003001e12103445d540166503000d030403e01d580000742c0f07450113640d924021550400341c0d00101e0f0200500741c2c68006120848040b800390000c2640c08201148a8904850040f0011174051046982c9002c040da14a414900d0a80c441c8070154408402c4c40805083c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 100946780 1250 100945530 100945543
    0x50c0c0406080c121e0d031a100503060303070f0f1106121b09040903090503010c1b061d16090f020703020d0c081b030301050307050a0605030a1113060f02 68
    0x20445060108600340480652500d4401018611855920060149101d03040c40540701090000e50780d5424404090400c5403520b00365825400001d1a24440383e030840515014070030141000307088032900b05e1904105803915440035000d1a414170040c88650f0014404001102038140f1a02c0f05c0706070f0b640325150110414000d888118481c000910080780b8064513590a86c2d03000100340c0d1070000c0076210340560102c51242045264115041c60a440b0078507070480715080c11a181980200001192000c044400c0006540c00d112180700094000c400304056400103403500d42c5030341000130450b9040341c51520380048614882101500804100b054054a124104003681b60030015403900c515554005e440346030101c01c0a050080180d40c900a00c0980419a02080b09203103d103c02c0ba6031607920659260001d02c555840b9105402000c121800c04800d140100c541649550b815034403000b034041c01410412541035a105c00c05e010300910050480c480b04003c1185490788409107030150310086c24081e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 100948030 1250 100946780 100946803
    0x7140f120702060f0a11040b210106020705030a03050c01020405100f08010f0e060108090a080307031a120c060a03090606030c0311030606090112020a031a091e070306020903010e010606050c 83
    0x100a6020000c115649101150f40100507080c001ba043d0b00000d0000c9540c080c540101500304808140211100e4140d2150000d0050065420001d07070ba03500412a51a03082e4040c050305600702c07004910010380600007500c0500385900000d800c01c1d89800109640402c500c80709400a14440000104541c000310b415015081c00148000420b082c0240500c140c42d003e41003904000c0380c1e01c0010000303031041c408010300c40c1d8400303001c0d41c1c1c134144008000d02a1031222485c07401c01004211800c90307840c10380c0d554050f41d0136060150020710b40c200c04118061704000c1c0c04201b4545c075045401d000464600c40e0002840c0714680c13103031045055081c01e00000070b40b60a924081d5000c002480101d0341d074195a03604490b01341c4015491010188007081100441c0ea2004143c3c280101180c1d11200100007024420715400702103a16a11041851005070811070411950300d40021b04203001041046d001041c1c840d0024001050024020340400d01311011940100d0005201007103015440c1414040d4820f4003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 100949280 1250 100948030 100948033
    0x91b180901151509030206160606090204061b05060703090c0305101424040506060c010906060815070f1803080316030e2404061e05040303060905090c0907140f120702 73
    0x43d10380c002030468209030101912485002c60000c84101c20b40159281c4981c0c8928144001e42d500da03802c0000c0e400c103025160128100713a00024000b04007030000c008142e0400010019a02d40b010298010b01d0149410b844401d1106000310120b00c040100c0361105014200029184681ca44104078a600191941c2050800c4c004498080d0840b102194002c0310111800500e40c0c541c0b4000039201e00c0340c0c80a440c003030f500304a000c5040c48001e90100d812503000d4015100402102001c0307071060102100c80e440899401c030000142e0b107100c3c04803003d408941d9030381c2c105419103d440ba11841e8104940c030711b07000c1b81c01d07180c190440765141c06111400345400005200e40414188c0f09644494803039840000181010700103018040c07590401a40c2c030b0041d001080c201030030904000301408085a00f070300031900b4040d00240000b403030710485104441c1d0002030691040041c0400151001c0513283c602042540c0410500850311b40c0c0041902c000117003103a45d9100c3c500c2ca4002c20701c400042480065 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 100950530 1250 100949280 100949309
    0x10080118030f1101020d06030b010302090a06120b060102010f06031103070501050c3406050301090e030301060c03030c0207150903030809010c05191205040f0515091b18090115 77
    0x40e400601c501c52000850030100f54981001248a00900551508168007070070703c2c00000500c00f0b12403210341601e00a45064036150394231081c0b10b003515100c0c82002d036a1000e0540280202e10620485500200140300128207078401e0310f0300c6400d0790016041620b11803080e8040180d076150401c0000c00a240a003407a81c28089040350540d1200074040c40320f1901c1140c0d4000960300c0465034003501407124505402072805480f002d0042a0b174100b4000c030305407540f514030350381d030000400800d40f81229240c0e91124000c46043e9021005494070010403020352203090700105900410025800240030340743d440c9210a031441c240104400c070f020340341d02034591409840054481e4000c1c119a040302103542e8038080e01c00b141600721001d02001e01405101407074001031000f00001600c1101c0028028030071a04280003071855040d105c1d80c181c401d0b803101d50104c84066560040d00800581c900002440000700020340d03070405210030303011200d8001c0c50355500c502e2015000041441c101400504050300300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 100951780 1250 100950530 100950533
    0x100507080a090c0b0301080d02070602070e070f0516062003090c0f031507030915151806051201090302070e0c0301060c061d010c0f030c050301121a10080118 69
    0x8120005000301032801c0d1640d8505041c4003450440400510305024001e903203687d01c40300030351580d500003d5070b40103011341d0340006070f030707a03c0014030405403503c102d0040d00c261035862064603801001d401c645c0c03e04c0014840345098490916803070702054010100402c0020120203001001c12007222411341250040c4284070b10700c0000666010360110075100b40801c0c441c504002860f1001085c21030803403088400c20082c0141e8035401100340390f44584c601400001c010384010040e1149105d102104011268041112010304424079070241e4400000150181d240c3c00415100580c0030090800c40c1c0d100c0c1109800c16604001c2d8100070035030a500c0403190708110040300c0c0d1510040c403440040244940b684070905c031481d48110035801142c0c3c6500305140c00c81d00c0071806002c0c01418400420300c0d904c1c00d40351507030080c01040700810349951100d20310f07801c02041816010598009484085047ca0b1015003041d00030301c06030042c0f920030a1002d2080c0f03404025400e583d021445808002e6600c1c100a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 100953030 1250 100951780 100951787
    0x80105070c1505040204090f060c0210090308060f060f040305030918070f03050901180f05010c080c0a1d0405010617070201110f0a0c0b0a09140f07050904032303010503100507 77
    0x2c5005070000e40400c0320b885074000100070740042c050103001080c8072a001c03020019662b1195200403516020384007114420030200b0100c03454080c0290220f965600011202d00d041c00303211f5200140207029900705900401c003081c4680117604125a9540005004400352500c2201003800301e041903440308542c0b9040364000c100c0418040c4070410300d81c503000800c18600080d0000c00a03440c001812214079031150a144c481007042440a8590b94070344120074880310f1040400902c00c0d20080401d52400d080000b0882e0910b610200e004028090703054041c407159994001d40c1e00802d11503690f4034050052a000780c5030b6020186c84181568902500705d07401c80680410b44054825410615031036009001080d05c01c02e200a0005103883c54210410522407040e0348943c0c00c060180040c03480142180a0b19640c4000c2d1052102840e80700c0501008185003507141543e004d4071a281c9840310903079040440c0304000003640c1c90311603441e001c07006002d2401c007080ba10800e5800c6640a00c1103040500025 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 100954280 1250 100953030 100953053
    0xe0c030703080f0403021306050405060102011a10020f01050c0c39030c0916030e0601032310050709051c0b01090513080d050609090607021b010c0219080105070c 71
    0x40400b2400725401d64a45104002c1d10000c41d0044c0080f801030386595181c1c0000c00860180030f110314600000305d101540305203d542c2d94100ba40b0fa0800c003201c01c40b42001907032401c83e110350301144100d007145840d0060030700170b080c00b4214074540d9644564244070360034202200c0c0042c203204409900c07080705504110540001d070032075220607060b45040c00d8030007007400c0040141149030000404800d0000c5201806003101d8005903030740d41004580c2e0445002070b20b46000f03100250047c40c03a15031002e10302c03045d0441c0001580031a8100c861100d000301c8007034152101154000040b9031920002c0245080c070100d40c0151b6001c40035002240061a901c03100000b4042c000d200c0c04903030750400100e00117010240e190b0b803a5040000c054a903550040c15401910045030040e0094207100d000c940d55a03c00501c5502a00c143e8000e020080104078000510413080e810490402c903045c204000940c0302c00c40c91004c030740c400c0d10454100e50300700b10740c0d5803d554001d4612400c0105a001d09408102d441005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 100955530 1250 100954280 100954283
    0xf06092e09051005030f222402070c050405070e10020c01120605010c060c03060807030c0f08030301030510090611030903071b12020909010605060316080604050f040b070903120f02010e0c030703 85
    0x19001034542c0d80e007144040c1507c542e44405007018444d1842031150841d074803084c000b0f1039001c01005280c40c1c07500b94164010000014110028000140400e00e06504242d074089100c2c41c10315440e2040c240002c081c840300800c0b5801580080309825195640820904900151500c091080d0307854500000c03c50b955401d4080c0c2595070300c0c01908120343c0b083c3c01500c014422001110440c544070708154540d1401841190075195031020b0000349248040162412290040c021344504000d0100b0f80001d4400004100d698580e1142c1c2014032040b400c000d98064a103090049d03440340381394600300f00000040c1c9128206c22052820400103144c0781c1300d40541c0194180d41e48466610391508040c007609480d0440c940c0300c240802001007511162040500202300c540d18034050341c07510421302013110700c00e46d00100000740150008000c100541100354000042c4d2904240d069584c2d11140c83d0384510320642d0000420840c3c0b41003145a090141c0046411044060700b00e454003000000d6030b50900d03100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 100956780 1250 100955530 100955551
    0x7081303020709050c041409040203031e09040c1110060302060904200304030c0b0f01050607140a1202010506040b090c1801230301061b020f06092e0905100503 70
    0x8824041600c00c2c440300c1c005040c5800d082c421410044401d0103107070401d001d1540c40c102d000b03010250910f0003c000900175034028020398582003a03540c0720b1613410640d004901007044200607201254485d44580c1800b0901582d0752503082d44408403d03400c01950b000b20801581c00c046082c00940c2c1d0300003c071550032008407400a9540a100070ba800c0f412803940741c40c2c6408401008020174160400c00003250144612055001c80d540c07110381090500b0203000e0150400c0080c40711400042c460032014070114820001c4410490803583c0340300c1e0030000e0304010300041c1d44500a008280c103180c001d000241d43c04a4040e20249007100b50f01e1100e0081c8882283d403440e070410b11851607400349140c03e4520295105034090540140c01504440d8003c0c030884001840070050818501f0300c0d01c0041881e21360041500c0002c40d5403c00301b00003501b1801806a00505803000c840c5c0c10390020400e80c69104010055030b120241000d405840020503510443c0200359207181084e40c554420b04880d4008030000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 100958030 1250 100956780 100956811
    0xa050303150d052d010513050d0504080604060908090603070c0b060301020a0c2306100609050409080712030b0402160506090312040f0305090a090e070b0901090909060e0a08120703050708 82
    0x1340d40e40400c2d00c07501c0a45040d17520301014880b40c00009400d440115001e007040758190700d08458203d600e44918415561503400c55404900002c806400c403610541c012400e203410010081c000235030f2907000307841301400b0543e081941e204102d100e810390ba600400450085040c15180100a404d45030b1b000c0009280e1034000c003c071440141d02c5100c11000c550b00800b04d800514110901c0740700020b45004001c0841e00b240c10001d803d01d09402261800307070340450081d0904006549007071650342c00702e130000d05040d12400c219031203460702d10161005c000c0250b00c500070a0321500f0811300b0000080d000d07010a40081090320300c800d11a100f45030b0496030025500b001840c042c1401c039224080c1d1000070f94032001904000805d80d0603a040009240c9640c000d550a0555440c5003603402d00c43d00d00c8007408141000300c100800f20903648a20380303281c05401d01080250141c4c280c1f074104100388030211018880400c603803188800c80c002442c7c1c08801d0341401c00c240e042c60036001e000e01070001c00310215a010321 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 100959280 1250 100958030 100958083
    0x513020f0a030602030103140606040b0109030b04060b041b030e0615090903090607030e180105150c0a060e0601030b01090603051c02100507020706110331080a050303150d05 76
    0x1c1d008400458010b1411512544c492601c05890215000110198403482c000300300b0030f1901c8e10450000c40c40503166050b82524650b244020b00340c00034015101c8070340d00d00d407a540c5500d4070700405a41d80c21042c000680151256005012034900c03c0c012080c1d544170303800b00040c2410318403024800010440384002c0659035100c2e040e14610945010a402090104104040641040e103a01107a41d00310764004010250303d62229009400340b003001e07806001c540b410007404070302400918165904805942d4540003d480b1201951040d402100c1c2581c000c000400c10310042ea55541e01404014400384421859500c400760f982408a0701e20300b07882c0b1400f4051004034020403400d2032a00040c901030240349881c480280d100c54a51042c0800729140703943c0c1e2588800040211150340001110403018890150001e52903881d50f20b88101c07904940c1d00c80071610341c40400501400341d21400c011507a80c500380040c421544100c025043c018000c90200a0008102040e0040121010701000652035403d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 100960530 1250 100959280 100959289
    0xb0c0307060f020d05010e04050a23071203110304030c06180302130b04050106020c031b0604080303010b0a180302030c09100b040f0801110a0c12021606020309130513020f 75
    0x303100c001440640740c00306440c12a04140c01a104100411008100580ea038801c440c03104401220002c1c01c58100e0090000081c00c61a9127408a024210110042c00c1941d01d03504d2501403d40c0240040344541d9011004241c0c5c0007030700208074a24034002e18281031542d901e1180e0200a80120400c0c0000e10303440076110307868070b40c2c044011600282040d4000d02403122104c0204000c1a06500440c200b800108002c4c0c000512040d128001030001c007003140d1042200306445040b407441a60000b41044000303003040c803c00c042c40c040c051b0590034541d56442d00030060300d031650712220540302c0c0b0400101000076a401080c2c03900784801c15914001541d03540512146010720642003901c0700b038804200812071000420007070041d50000030013005000000320040240303006280c1c91a00090440c112180041c0c1d0821a00b01d115203140121041d0342e19181c080da0b4170410315005000140c0c40441c4a40c50f84c50300b14803075082c41c0b109040400c41400d1a09454812200744680a4062180603490480d01d454 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 100961780 1250 100960530 100960537
    0x301060c110d030302070312051902070206040e1e0702060c0a0f03060308040f030302061503030a0c0f02061801020607031a040b0a05040507020a170a0e0d140106080d0207081203010b0c03 82
    0x18000c00b0820302c030100307150190080d00b0101e410380010780801c007903404c80d501504c030320341c0514250512659406e01c0d141045010b0b41c4010303000c0360041d40030300c80050b500103800720003030080714942011101d0203c2e07150743d400300d40740040c00d620856118606103c2c83da10030764216920b49040d031404245a0612810a9010744000d5100400500000400043c180140c0e500441581d120350309490030741d10341491000c0c1c01e07050444240d0b4150420492014802d00076881c20314820300c2403440c2c03540b00800c2d8000070800d8110000403a0030794101c011410711513038184402540244541000c202c3e480090b521085500c0390328882038000c50390780410541c50340e5180d0080c0010100104203001c41d150240c0025180d62408000300ca011075500e51520b4900c02c2401620a42e117071550b6200c004d108080700300807174009103072410744020060300d0481e03014a02c2030041c9000390070420000c00d8502c2040740001c0c41e09509900c0410150024214803d00c40c000c0000c0303904407003024491b107840d40c03180f003e076506611 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 100963030 1250 100961780 100961813
    0x3080306060d140c0a03060b03010803090f13050103050d030608031809060f120709060b0c0303070f09030f0b0105010f0c1a0a02040f08012307080703110408030a080f0601090b0301060c 81
    0x1d480104003c2e0003c130040042041e040f480d0350901c4019030310000c0b0b0b8a2404207000340c0085400911240c150303810179050000c40160010006400c2110ba00606801c40e5420b80080c0d8450b007012403030080042c0c041c092a0000d0000c1070003507152840951b107528480d203680e02100e1261000d54003180a907902c00100211001e0018602000011a130b4051a51155540701340b5803254203000d80084c0014110003540c40341c01022005c0d51075569589011200080404030f10000d0180410001c800b045e000180c141e00c6511901d048080d03541000005400c0e0041c0034032610800c0900b861603000646c11408001c050403c2102d105541e49811104401038040c07900202114440c1ca0b00001e0034000c150410782404109089502401d500350004816464084506101107542d070001314540c18425880600e6403281521080d007400e440c1d1954906552181855400080300c501c10302484203006012150003100909010340c070549012240307111130005116580601001c400c2c3c8400388440c0012010408 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 100964280 1250 100963030 100963061
    0x60d060c0201110a03051008030a0f030e030f07030210140108070e04140d08010e060a0308091c120314011203140c0316030801080d210c0306030501020301030b04021003020403080306060d 82
    0x1c81410300024006d02e07080359481c407413814a04002034840d8000c001c8440e01c0b101d5544010b05d0a610040c142c2c00381c400322441200302e101c200025180c81c59200058800c9500c241d0150070b1000220b20304000341c03031284250390321110060b0f00400095030001a007002325111440860410b0744c903400c0c0000c100a6201e0000303094001c51940c585035650014074141650050140b05110762180c409000105500b40402042d1074400c0018007620301d4011411242051820844040740c2d100b5a6410b42d6001c54500b00c0d0b0119854540c890311001c14103c0380ba000d0251030f00381c4803140b49a510000c250300500c240403134010400003a19501080c0510403181201c03203466040030b0702c03401407400030f10381d80c000d20910182d406020304900c40c0511407040910b09000c02200d4100000207108000b000f003181601c0c100505039170f8000000010020300181d0300850040c3c0f841500c82c600390040c400281c81c4082a5000c15104100c2880000e108030145c0380c0102c0300307454040c1c403000068502401414100c40c40c0002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 100965530 1250 100964280 100964287
    0x103110c060123090601030921020c041a0307050f06070b090304050111010b0a060f0306180c0915050a120b041407090f060207121a0709060e09060d060c020111 70
    0x429400042290482e1083c0b490041c40040541060b100080b200d4400d0b64011100d0000c5082584260003030a11b240c02942c40c40b290300640012074212507500300001002d42c0210400011350700d414070800320307000500403061180030b200c00700190300e0303103280c1c0140d030701c103443e590310860701d5403250401d43c1c5e280b43e802141062282005500d4541c0c070b800502c24540041c8411010070a554418013a003c50000c02400d100c0143e400c1c0082500c03c040c0e140040c030708155540034001844200d405142000785c5011074002000a02c82e4401010b030b0016801210034100c40c40d407100382c4140c0c0202280e0000f034082c40c010014100003403900c0003900488180503403290520360240201c0d8002c25845001d40d4a07a02c88110255a40b548250b15059522a01d000360300f00391030030890f070344615030001e161922031001c03503840300702c0c0c0d080e403400c1d02c0c0c0c050711407038000340740680280704564100c6010b00314100220f5014506280113000591035030102400140744540316104107030028002d4000e0328281001000c040e85 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 100966780 1250 100965530 100965547
    0x5030403060608012a110118060b1c05070605030a20090108180705042a0503070908010605130905070305031b0106090204061403100506030c030a0f050105130b010311 73
    0x20b0019402030011552070100c940601c448042c5030341610400da02001c401e0241c3c10f45d425070b04900b074030307140e01800e54a90100c0200303450301d0109100c61612400000890500000a024242280e002030081c040581411200440c0c000660b1104941152400540c0c030355680340308001030546010846540c00d8140d5408603084021001741404502c00e0740d4481c1c01b03549d101c1c15120704560605641c040c0d0b4110110901c8241040e8201e442100402d0303603114843d42c1c00c1d0052450407919076018900298010081c4448690702030341c1c00008000c03801c004d105090400000a50004607000d241c05502d07664001401041401d122038001107802205a0703071980740c1000d800d44003072501c03400c0c410346518001020400003082c1c03083e101503400d5075603401f640710888880d1061a034000f4008007011741401d04005017998038a001140700e601d080065035220b040481c4510259203040c40e00c0410a41000014040d40d1a036080480000340f4181d408110ba142480041c0e0003445084500e06907143e00088141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 100968030 1250 100966780 100966793
    0x6050301140f10050f2a060a05160e19080303160908070b16060903120b040b0d0b0c0909040606050f0303040308030c090604080105040c080705030a0c0b1605030403 72
    0x18101c5114114118004034484108188031074950145580484100083c244542c4544050041144030741442c1d444d2004038260103000e10021012955013480c4951901c07070401040c020680c012082e43d40c24002c0d42801c00501c07900e24201200b044c01c10101766801040e607540c2105800d210320040000002c01619241602c1c0c580e4003c503800c0320058051411030780c45034071402111084030300b41000b400819041802960503580020540c422090340800d1000110700c5c18480c0010551007502c0d04100c501981618005841d0702c0860303544034030300c2c216001010f500c0700b840c8840c0d0607a1200d00c0060302d07901c1c8010301c01c06000300c5000715000300c030313a20401c0100100d507070000041e208221044410300744207008041e40c0e4429400300410300c24040c00800c440c0f40c0d041b0042c0000d248001d1099082a4441ea4500d0840e4030840e015104885004000c000f9034105014040103000180c0c0941607003901600c0d112107080d814403c0c039a01c1a000500380c140c15001501c14000c2c9a480001d42e9070316942e90030201c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 100969280 1250 100968030 100968037
    0x20d020c0d0f180b0c010b09090304030b010b0906030610030608120310090213090902030307080a0519030e030f070f050a050a03020106060c03120c020c06040b0d11131502160605 78
    0x40c4003084142c0345621400e4003ca4140e0101d92030310110411160030190f003190b19400070304815010390340310b082e4080709641c0c14a00c0e501c070f00b03101c8004540311499420a584c1421060b40220440c1c002003280301031a80741c0e041126170281d02aa10200c49c45c01d515421401482d0720750007444039016a003084028245a00000c0d4020300d02080c0c8009000e840d0300c0c20340228416400e4180311911020400c2040d00440d070480281d443c001000d681c10408107031500603030340d032046c079400000500001d40501441c010b0181d03101e017092705140400003008000e5a41e562803044e0700069041d5140440c10008100d9403294416400340d1090540301034410301e190066580503840c00480140d4203168012070b030316110b01c000303400160301755a400c5900b00001544000505510442c20114000c5100c1c030202c0703444000c000d00003000500e010740d41d43e0008111010850f040d500400248550030814000034421248490084d10414800e05509012409083e0310301450038007882480c3d81c614000180700b1b034100014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 100970530 1250 100969280 100969303
    0x503030709030203150628080102040b030402130608060a0b03161418070905090a0b030a0818030703020a15050d0c08150f0123090301060806010602010b0607150c03020d020c 76
    0x460b115542e80650340307801c5d140b080f910b081e00105d804609003031082040c0400924006a0400000d8241d1624005800d9a00a82201120800c000284400c5003044c2c541b1000304401001d08102843c10440d8940d242c0c0c9002d04045161b68984041c82d4050303605015000c40a1400052458110f40d2010a000010344108909110320808401c14024a0200040c02e00c204915500d540d10390b81010b0410085070009051013000a41d6800c03040c109803401c111002019000e44c00c015215a001d204410b041d09100703044034061381140c8020801030711150b0220b01a2882124001c8941c4c1409504a42a000d0140401141070400c034440c00525001081640100c81034070440e4010040c2100b03100d0b00c80164070485001442880f480031440d00415070318500c01b42c1054255251100300340c006800e454498022510396000340004208550302449001e0a451003905c0d1541403c0c42c3c0d44402c044a040c1900407600305495481058185200b80c0c111854200002411034440d036042001651b2111000711 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 100971780 1250 100970530 100970533
    0x20310050f09090a020d0303061d01030203010e031305060f0f030f0103110409020d0605060103110703020708010c0801060203040909020a1a0a081f0302010c0503040e010e070905010906120203130503030709030203 93
    0x20940442c1007402606101d0110030004044420490f428449411500c0074260101503548101055a8010f5041520308101d599401361495040d40101400c44822111080300380e801000f5514070310301140c84040881d0012074a880e252100789050646510072620001c40ba030707030000f040103440da2808615a05076405411800c02c1401100240800ca910f500c1010358448002580c60300000d9850704465803080042c50701044d0b0b09a0350642a803c0d8008176422000760f0041030040c8010384003403003128168041860210350700d515040c000303134891060740903c5001545031504602036440e050b00c0c000080114402250110a2640000407140c1102c2d800400107019900884d0307225040080c02e01c1040c041e559220141d07895a401950500d260010448179030006000000b00c62030f801490754000d10000b91141d00924210600401d400225040181440040c0206005044d400300511500c00c031100c00069503511401c0e8074080d02245000000c000b848000100005198880106400c880c401d40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 100973030 1250 100971780 100971799
    0x7030b1602070f05011d0301060e131e02010813170f040602060a060b033603040e010605040308030708070e03010908131406070b180d03050615030411010807021002031005 75
    0x2050000600d032248504c40c001240841d10811168413040c1416007107400030000164aa40c0d007440710540039084074019180100c0603103a0080c889040c2901c0c01c0105072290207104c21459a0000e06a00c801400c0303503d805810080000c104441c0c0041c1021080c04034100d56200ca01440350b01c1802d9116008180042c0181000305050490b240680f409540300b51140c00c0c15076940d0694480c14004c40c090788095400c403240c0d00304690100c64008801040b03070700040c0d81c0e65400d00c000030b480741e070341a8401e9080000800080012900b15801d480c1c01100900d88044a0b88540c6000c94201000c40100d982c5546004090030404c41548001c2aa10f001c404100c41040d65035030241c1c0f070b03e03039400c480c490300030904000b1900010106003034154004480049900d840c0128a011032070102001250000320780e07940103000482c0b4007403004480c05a221600c2500d50715041e23540e54215242c402c0d44505005241010410316802400b0f0b400300c2c1218400d04641740e1070300e80c00d91880b500b002d103d424000e0f0f403141c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 100974280 1250 100973030 100973039
    0x9050112121704020f0109031704050901060f0c060b0d080336100203040206071a0601020601090203040305091e0d03051b01090507030b070314010e07031104150c0507030b160207 78
    0x10350302050411100b060440c003958440c1c0920184000740009070b0304101c1e07104400b10014202d128401c02e2100400c050303986580c144010b00c80c142070107070400e0303040c4095074a24a40c2d995024003e03140542e8007a10121f007103118000402d02c19603100c00020072289001c0100314a8620a41c2011951541c1c0108681d50000c4c6500d02c901c40c0d0072040f100301142e040510080740c6130020303030019604607102400161a02105466400031485480c101e5107104c20b01405100842d81d04015250150044007421495420070f983c014001c1c4c4a100d82c1a805410341c0b40303040901030800351103142c070130300c0140c98a01d0401031850001c010f640154125004254048120b00c0050700522074200032a07402401020304c01e0840d2620565080024400e104054842194203030711400700854900814503d245a0520300706140050155041500d8004224000b030004001040c5070600c540c03032284143c100304d503080590341441c9051801d55007014003c01c07008001d101403241000140229191a80e0035200d515484 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 100975530 1250 100974280 100974287
    0x10602010504210c242f0a0903060c02010b03060a0b090c0702091b0c01020403060603050c0d02100c050307140f1002040b032410030c030b09040506130c0905011212 72
    0x2181c003d000083c00c0881c1140c0080c03c403800078660000141c642004481c180304100302a40c2010004c11480c009002d031040710300d0382200010420200e620a05414900b07090b0004054800c10b100c064030702c44c2c6440c01c81020074000c0d030043caa01200941560040c5c40d04401ca00e01a0458500060280c012240000c07130b803680c100c041e00e0788a43c4c02010341400313884801415466207256003020a90070030412502060000c240700400045125040201fa80b80c40c42c101a030500940181c42406514a007181000695030040085031541050508200028803070408034694050210003d00420368103244010620f0009071803d42000600e0456420002c80c520200a03806103101d100030010052000c15070b5242031002d01042c5940c654a881642d0f00072034001007003840c1403140c0e440800d5071810f182d00aa41e00d8010f80c003400f0001d840741960303820a5500d107580c1c2d110080460525000081005007002680400700d0300600810109005658494454942d101b003c0002103401221154162940710701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 100976780 1250 100975530 100975583
    0x30e0d02030f03130c0803190801061e031a0406080c10050a020a1e0506190b01030b060702040c140c150601080f16090801020a030204090c020f120702060909010602010504 75
    0x1c1d900b18600716256020002c41810905a00b20350b03007045004081021402080900340c2d04d643c0da0f0b217909440c10140c07405018510180c10080412000d0900448010600040c0c09460186440c00184407400720315140c0222008982c8107511504080300050440070000c0e0301c540c031540484007120810744000003a40d0911650b03034800c0c05a00320441550114071311124074a020b21074402401000d026a540c1c49003480412110009980345162500000d072140d4851140c03121400c0c2030400c2414400b50006403d40110b4200078031844d00d81015101031441900c1024002010055043d06e0340501215691605600d4620600001c9401c0c001800707503128140d42d5004000d101c51000c83ca841d01c108001111000c00c5101050004c446400611039500344000c19900029560041e1551f040c0309446080c0d58146030720000315401103050211050f03010440191403445031910a03514015480032403094010307500c1c6160700c094544d0000602c96019008944502d2080250440907040940001c2e00c2c0705 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 100978030 1250 100976780 100976797
    0x90c0426150f01030f020604030605130b060f03070e100b0703020a03020c0f060423060c0a0b06041b0503190f0b01030f06081e01061a190306050306130602130303030e0d0203 76
    0x10020b03401080440d280103141d001d0180050006850f050b1a5100e8001b500d41c25520303640c1020680d183d803000d2141c070111064101400b00c42d2400400009000039590b496640100c180c12400701c0046046490708a2100c402011140301c0c091b150b14990030040d450708182903040d40503024800c04000c1e945080440302a112070010812420507041520b4811500c3c5000403001100c00c0c10290f10056590309800b500c1210050402030641810511307055020306005042d56000b0741c07d00b410ba44500103281e200c03569501e803510f000c41e2603031744580d05200740d040105c1034820114500003451003251099000341902c12400c0c0c07414420444000406000c407001440341000c103803c15514100f25585d6800d880b22889020000400e06544a41840e4040d44209959008040000031504110304000800070b000030b1540c00c0c10000e0510b40380109403100340040c140c0b041d800081c555102000007590558480c00c0c0080030644005440e40b50140c001c1c052183c4a402500c210104240c00a100108440800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 100979280 1250 100978030 100978051
    0xe060a0b010207091a190614030f01030f030915030c03060b190e060d0f0617150415110d090c050607020d020f0406031a060103062102090c042615 64
    0x20b91515403040000c1c25464171041e1017100010011000e0f42d00c1119024842c0d0980c0078402803e0b24000025024865105c00404280420310400000700c1040c071403d41100d401c02c3c03070b8025106d12868202c0701401d1540001d0410082031000d0080d0643c907a12011415a442d20102301c200c0e15004c100d4414003920012410703442e0925602ca9089104000300136103510041c000038240a95440030000b030703c61400032982c86075602d01003000901403a21079030540400003400360044081942407440720301c00040c80507001c84481c0c0720310281c3c0400e0b41e00c00409000940680d6071510800300308000030307000b89241560340c0d102c02580032403d490010110f030406940241440c10220480e400d2042440300610b0803035109035645400004075a084000c1030100244e0fa400c80e40900d00b80740050111801ca8100044007440d2203500e20001e10300113150309141350103e1301c040490303603030020140c81b40c401c1303801800365100c078100704c00745c80110b5542c0b1945201c1d0381000d0302d6041103416008481c03180e00702c6188400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 100980530 1250 100979280 100979293
    0x5030906190e0714100c08030a050c0702040507020a0201080903040602190f02060c15010f05060306010e030c0a120507080f0303040f030c020d080c10050f070f0c050a0302010e060a0b0102 82
    0x200418110340141044403240102d40032608142c4a420118650300251080794078039640059882c0c22460a1100c00c6a1304041c004140580ca901005000080c000d01800c0c3c1c0c0d90000c1042941c01c282070742d14150303009000f8005842c00c0b540094403818901030480c0410030010202d598540b0203c282c1e030a07185154010710744100c00a550448188420400366000496003600c0c402580300d440c01481070131f030180010003102d480890a44100c40051344240380d4505043c1041c072281c0c0d11030701200d8005009207070501000c014900041d06000700045481d0781700d890103000052441040c0383d054441d034007032001d0303070060381d0b0754001103850309a060312601d41074200b00000f90000b000d107001c0c50003690103413034544e0143d44603501061141004050a6030310301000324903802640004c00014900c15010f20f801d000c641000000114035840103072507a42400b001e401050b098034850880c038010150401d08407aa0450705060183c02400c0944084009000300c9002039114580ca000795800c040040c2d000307100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 100981780 1250 100980530 100980541
    0x30507081911040306110301051c03020d120b0a030308010501020c04021201030b0714040f03021e030c090a020c0709020c06060a030b01050904030509030f010b0a080a0b010e040c0509040f03080705030906 89
    0x10003201000302400b00d024403000c40454414030035030b08611030b0001600c0d5a541840c2c00c0061001c0130004030030030003007600405030010b9400720b10000c0014003400d003503800c5100001208060714400550030b4020416403000800c0c10f50200c0e84034101c50307013a001c0d02c0400c07550b00c05100580c4102a40301107140380342c1300104000b90408407e5030b0311240a203803072085041c1c0004c4454507584030707038022040010003500c14015031070881045200f0011007030030101d002c228800880e07100d10104021030b2240c1c140c1c00c0010030010840e01101c1c0d1951052007946c00c00307501c0314001002504241500c100c82d1245100044090800031000015070341c10040d1501c03185e10342000c005050388000c008a040010030f0004280b0754030100b1000c5030504003040003041003a00300c02440303000b110301d610000c0903610403041c160114800c081da09041da100b01008508940e250700300281d00e811560321040c1c0001d4200300b000203212440c0c4071102c070b041c841d50700d92009071a514011184c6000a56a88146400c010b0101e031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 100983030 1250 100981780 100981831
    0xf0a0e06030309030601060903030906050a080f0615040612240b0702010309060c08191802040f1104060512160e0405040302010b0307080d02010506100918020906160303050708 77
    0x5900038802811280b0700000c000109003015400c3c1d0041002c102c0c030320300c140205500700304000c002d0302240c0b030702a003400c41d0140000e1400a018103c0100c11000300301045040c2c42c0c0c2c018400103034845a102c5079440b0359605004003408100c44006015a1500840056950105182402d002460300081c11201d041c0b00241c40550321494040b8103255598114000081b224002d1841151a40e10392a1680c5010303510307464440c150f122130341d09062510001002d5201031040c0d5010300c64059a0001d012500112460010207400d1340c00c80101901040c0002d91640c094010301c0d19803803c00300da04031910749204800112000440740408103462284965031401c140d804036a1040c006d10010903141700b4040403078141070312500042c0e05500030404546810350240100c5801042c241c0780d0b031845506001c1c00906800d410b00442c0d90824002c1100d829049803a0141d500c00e04004081503521b500d9144003003400012800201d010030b0601d0000790b4030501440b0030900c07603c50034200758030b850400700442 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 100984280 1250 100983030 100983059
    0xc050304030f11011404060b040e0715050408100207031701080c040f140c0c1501080c0402030408040b1801030f020313171e0c06060307030c03031404080313140f0a 72
    0x14410040c0c0100e43e8142c1210034000c001a0f5000c044084540d800e0a0402109584506074041e000b41e06104c0e43c2c89560314005045e80031240366941e11011014048070465840c4142e5208000f14450b050001d0b50500301a03004141c13080c880c0d102c42c02c0b03400c888905030325150300921503603030715801000c0d400c102d030705058201012244150f200040d2070462102ca0744200242503c840700100c601045000149000b00110301d0a040308194000041d0714000c13101d031342c0300c0540d414140595000720102d020003d2081c2614003800f0b4114610f0b4031880c0700e0114010701510b080e58640000c1c00c081480038210400d00c202c07409400000d550050540c0d00382c0b03c0d03501000415940f40c1d50100d04200445180c0c03030341400540700f840558041c0e5030321000403010303515190703014002500c26000000b080001501c0c510216040720b501d82414000c001c40d2120340b115602480d0311420060000040580c0540d0100355004180c8540c91145074200c4005030500491645840e000d80c0c000151000910030858020140c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 100985530 1250 100984280 100984307
    0xf01030803011503020c0307030201060504050c0f0409090c080d050d0f05010e0a090215120910060627030b010305010c08090c10080a0b1809100504023f030a0801090c05030403 77
    0x2500d0a00104901b600d90341c8047c1082d00140d6583c8020321003454540a030039000f0490501c0c2c5c0b0304188524985003849e1042e4410258201d03500d011501c2080310190720440203240240540305030121900c400360a03075201c0720544048a02d040d042800000c12442080d058910005c3c100c02070f0758822500d90000c040d880c806a91100b12900001c0000070900d0081c078004000082c515414201542485e2514450420a080e268102001840b80390b0380514424403c0ca10084002e00700c5000a000c6c9d0039022407604040c010417003542c00070040c40b5054000f41c40c603000d82e07078030320040c1c4d91011449516070b4104036503a54000310001305100b80324030880d040c0d504441c1c1001c000622480d0040090368440b51090414492044101000f85071101403001c03044042114501b4081ca00e0942d0010300d07540f40144c0e0304181110b0002d1004c2800c42c10360003100da1071440d0651020383d1240100f403695248c000e01014800120000000f1604040500442d0030303020654603143d096495641d400d8070700c040441d08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 100986780 1250 100985530 100985537
    0x40e06010806041103090705031e0c09180d051903050c030a020a05130f0f1512020721030b100203041802030c0d0f0507031d070605030612100b03060f010308030115 72
    0x1840c2140d900400114015071b000070040c441d0300c0c0340400749420300b101d000d11075040b945803590300d1001080101c0c2d600080441241c82002c0c50707071f4020b20040b01c0d440030220b00d6028461402480340858000d4002c0000100303102c81480e80350040c200440942d10308459450b00484244013052a0150980151005540b0341c01e001d420084070140c109070076140c503480040d824000c0d0300c0400080c3c1c0d502080002501c20194031201e4008152800781c000c0d20703440f207880b401030750014280e010312188608907903541b00c41c5083d40203aa10341d1140140034002d81c1d500380c1c2c815041c040780d46000303d000104035011110707002e442000240e584200070700207400007419000c101d03004208086200020b48a0030a07100d042c80000030f458103008900504880c3c0c54070003481c0440061280046410001134103170101c5102d4601983c0d0b035954a4040303061619005030030101481070b10300d20340032601150058441c4480c15401c6540719a5041844800c0b60f00a02c0040c00c0c401e800c000512105103070301410308042c60300d401c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 100988030 1250 100986780 100986791
    0x7050603090c09101502030c0616031b0806030105070903020904060c0912062a0516050c1503060301111c0506010e0a08010b0f0f100509041d070614040e0601080604 72
    0x2010598030503003104c0300b0f20301c905490320600c04006041d400f075501400302d1000750b0611100540056a030300e0040c08104500000744130040005120760031031488644135107450b0790241e021902c041d01030401950814441c0d424071001031481403003070131900100c80d00201201c680340c407551624030003080307901111000c00c9020040407403205009200340080c00d10800001400c402484107200040007181c8290110f04081c0c0b202042c000c1c0d000d0240c44c8035031014529804407140520f00149040781e030442c40758126900707110411107007540c0c0000c0d61054070305030300038000f40701203e1440342c041c89202c5050005c8004012005c050711001d40c80290300c0441810510304c08400180001d4807404654449080c47e911143d1092090400300340303144031341c401901c6407020300e1141c000181c1c449092101c100200304010682c1e4a4644e0303a07070084000720707a2168180b11203502000121b07031038500741c2c01890007054032540c00d1488040395004440864841010303c102c11b403170b10b030011505808041e040d913034069241c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 100989280 1250 100988030 100988053
    0x6080a020f03130c3c0812040501020c04060e0f09070504090b0403030c08040c06110a02060d0b0114040e06121c021606030e2805060109020319020c0705060309 70
    0x410055001e00c003160651540510a0324180d441e00c0c6164021804811740c551140c0d2010386504400e20456511062a0030395008007585000e500409503c91003c1f44106c0070034180d46c1c0441e5004105480c5d00381c0c203a5481701c4149091006440992049440c01d01e064000103c09c40086904240c01c41c0b4014242c412490751200020151000117101366040d030380081c00c0c002051f4140c41031810f00b04d69418050118070f080e4130303801b070001c08034130408081c0300e400004003c0381941880301541103540181110b85600c00001900c000b0007440d0207080c04182100c40c40100c8565a800782e400301d4640304000c00d07265071000c0c2402000d601030881d0065a20032440c1c1001075900c0081000003040325075004200d4225054450608000d85500400601d482e1503038983c030703024010a00c6001a0741c0040c100402c1200003c01d0030314091481d101030329502941c40040354600064000714080d039242c00010785100320702e210440482c0f00f15007440b549907004110801c59802d1443c003035940b060f502000e480004814 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 100990530 1250 100989280 100989307
    0xa030e03120a1d030a030f0c110d0305061809060a0b09010803160c03150c02100c09150c0804180507030c230d150305010f020915131701090c080c0a06080a02 69
    0x104800082507c9100025044075944180c003040e10807454001051480c01c00525106c10020148900709922000051400d441e400300000c2035070345070b502d0b1002c1e0303290440009489601c15180183e8036401c003441d0007443c0c5001c0b03030102c0c145e48010f006185403a2050100c00041031384400101c076211480c00000000c24803400d042c20159000e2100030030714410000c0c009080c43c0e02c0c8040817070454a0003444010a82d0f002007400151030012009403054491414243c0711540d02a10040528500250104c2e99030010070640c5084030402c0700030701107511030703a1007a030a460070524003c002402e01100f005014280d440c60700250031008001e02e1030202400d00d8401030b194001804017141d1030f81d40c4c0820030040c09104c0d000e20000c0030302007141841c20b2540014007413013070600600c1034400086101d507840c961184041c0c0081045001d0208400010b400f5140602810181510068600c0000040c1150003040001400400500940a141c2822801d903407608000d022444059424030500307069682 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 100991780 1250 100990530 100990537
    0x806060f03191d0c042c0709020307051e121504060305010c020102181504030210050d1b0e03010501030b1f0b0307051b0f03090d0312110a030e03120a1d03 68
    0x660700240c1011103041015a240002076035420b40103600d044225256a0005464006e0b5030a14034a0850620301c83c640c5189040c12a1300715000d014400402e101c0441c1d013080c01001c1041c1c08003030701005610141406003c1d0b015204034894108a10030015030f20020202c610801410001c0c00064156140d480303050844002110010250394001100744c908008801c11401802085507a2000c000e9484007030f417a03e00480c40024018005c40c110501030f4bc2c0100c041d01e81c1d4800743c6508102d6a40c102c44001111254154031102084184041e00290704041c01000e058035040580ca241980b03e403860310310741c1c3d41c1d48c814161520a0010011031a41c0e41d0100440c000c00b0a80d503003030b46035124100c0e0541803c4071500f10310b906074071103a03036001d0ba0741001c03050364054001190403010503001414283c51045040005c00c07499403901c0920302809100301c0c0508144069a602040750038809440642c0e40e1180d071203200b0000034044001340c0b907404280c01c541040d00c60307a101103005040210342c0c1840d41c8c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 100993030 1250 100991780 100991801
    0x3090607020316030b0a0b06090a06030203130b04060c03290f010509030a08121806040b060604090518010c02010605030a020f030a0c06050702010e010314191b020f0705010806060f0319 81
    0x1031005100b01800140a03801c7c41040c21900d0515004110002909040d814840c40d0103058000c4005412000d0844c0b221000903044a00e2115034038152034000000e04640b900003003ca8030b0580b103405c0c185d03107a00302c41306600c0d164030803101400020f00030402e0540444400e14100002040000c075143c80038441c0c8055540300700400d6480302c021039010402c01c41c0040c1448040d40000c08142c18100300011050f80058111954071510340310035002c00da03240b05540000c03c84500f040180f05481c000304010382c00c008854802040b000c5480c0b0401c0382680c1c041d1203010351507130012401001610741060441c5800ca0020112541c08010f46d6412070403e16551050001c13410116011013076581003020b000c90513009203002c0115030390303207034548510322005032000203003c24440c101c1000551503402801000c00307841030001f8102007400002d60320581c14103102101c1c040c400d000102c035405400781c2e9008940c02407406050240400c003010080c0c200401908021142ca000c40010008900c21400c292 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 100994280 1250 100993030 100993043
    0x30e031204180e01060801090f060e0606090a0b0103090210050d06060905030a0b0901090209040c0611030f25020303030a0603140105070918140421140f0a050c060a14090f0309060702031603 83
    0x9030810b041c0f0008440c80d11442f0b20068001a081140c940d803880919588000b80f42d100003101428007004074000d2441b42c0000307421005c0b07440007405c0140c0080c0070f084500d04c401400e00150f529984101c3d080712041c03080682650140c1c00d600000b0703109948859119840000006101400360005000c0d80b800740d03821749040081c80d0b402c2c09410b500103007606035210014029440d190115400c1c0034544a080304441da48201d246202e01450340341c41d1503240a40e00201180c0e02c0f03051003082c0700014038103403008a400d0b0085203a58200624103004440c031580c0e40d030702d03501d07043c5140401503100e040d40c0d01c2228250555800e140424022021500b602441c05080d140040341c90500d000c540e01003031080c05205020581c02c004260300814130860f465075004e84001a110081c2e10b2080d2904c0c000c440740d00c81d03180910000c00c00c03440050780c007030762000c04420301d4006c0e03544480010544507a2030300c00d14003494004101c2010030b814144014030030244050704856468030301809000c031464058008498a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 100995530 1250 100994280 100994303
    0x19030804080f0a0b06010c02030a020a0b19090f0308030c0d0903020705011202130501050a0207090f0507140a050403021e0402070b07090f05031e0c030a030e031204180e0106080109 79
    0x340700d400c000180041e440c42d0018511650f85856060a0304002080c045c104280010b520046407018005800000c0d4050500c0503020780310401002160014803490170b00b0041d0284490406108418038000c0300c2a078802c1054490458640100700d42c0014900300701040d0070044801103800b00d201d2100a1070080c0e0240c1489402c00000404465518680203039050041c032000203142180c0c0d040008855090074030540d50300382400280c3c240109548503d02151034082469030740c6030340c1e4100d144151b0007903072000f508029004082c036842c02101c02603800650240024001030421105280c0291006019403d01d48420b100040581c2d100303c0f803c8640b401011306221840760040c0d0002c01030716480b00035410540c00c0c0300210355516802680d0124412441d001030304c03c03540c00d014003e02c0400180c156560283c841c1405000301505d81032040c020b101e05041d5411a0604000355800c4c1c5004030002140c035100900d42c00c0180200b46010990380d56100300c0000c02c040c0c00d1003120101481581018039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 100996780 1250 100995530 100995539
    0x30a0f181202010501051e1e0a060c1b0f060c08070b0106050a03050901020a0c030c080c19120f050702060a02070810060305100219050309160603020403060b01020106060203090f19030804 82
    0x255001a44407034042e00743c0a59079203442828450000d890300003a48c40d81e20041d29510090007014826410a40141c20305002146081c0d01070104c5d040e540c05456909a0000c901844844c1e80185104d0f140c41c0700300e030244c140a071901c100c2441c1201c50040c02c0d110304103842600e521a9484003030b80183c010442c0003c0450410f41c05020341303a1f0006101e4000c5040c01c11034400900010204d100c01010040250208000c0010210a031032281144108982d0a01a040075041080d240e5450580d0400102e081506c615480303081800075405141c0d0f02d0030f040045603800d200c026040201080258000e6003800b01d81070a04015107411000d4000c40440d0291850400a0406c00c0500d03c02404030700400420020b906d02d040200ca12074402c0c5001eaa680d900c041c1c10034184078203019500004c1c09500e0000981d10b1781900036105480c0240010450001440016800c88425200b01000341e0030500c004120b614218401d089054400b8000c10b050700e2041e503100110078581e810449140002003420310 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 100998030 1250 100996780 100996783
    0xb0408010c090311010e040f1104030201080c0c0d0c030c0b09031803010203060d030c021c0602090a061b03080703110409090b010f060507080d060506030907080c0d08030a0f181202 79
    0xa50280c4281002c0c1c2c1001e0030741e21580d82c882d42d0416031314140120420084401d403125404256200c403110802c220420704110b00403d5a4094801a40090020008a09069100e40485045600300c0c0000c01c406554040203840a2030000c100758180200e482081d80401e10380c180d03c074450700d103c3c0040d690706c1e801581c1d00c500e20000c4040140c080c0c0c1c41401046003907200d215a100155425040240824819100183e00080d056121103400520300301d07221300700441900504180541210081e20494540400300c0b80300314040720314680c0101814591006c02d020740d802607006400b5103404203a440c0030351860540d0742d00c036500551607203507100b41850600801a941da400b600c0803082c4149614a4210010514040d030000580480c00004040e035042085501500041c007010301200e40360326006203102c0e16480c0301d11070741455006100104680346009945824503692101549083d9118011043c0c01018194062410140d44041100c0078400d028101810580b290154400f40015420b00a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 100999280 1250 100998030 100998041
    0x60d1503020a0f08071404061706012301020a03030906180503030f0f01060801170309041109030106060f021b0d080f030405010b040c05090607020d060630050c09040309030204060b040801 82
    0x241030b2108021428011600081070ba00102d81111486041da0046c840c00a0010540343d40f0016800c04000f821035080c007408107059040701c42900700052460510419a211845211a05401a0020032900300000c1c001d5007d45000c90150000281e5146a0304481c810580d04130003d90305584040104041c560654000c00c0d070080e505610601594035081c000b070800740c0180a0400151801002000300c090100182c5640c1d04004109100090196043c0c00700c9500527441240254246040811341074003c0c16001c2021a01b6401802d40c407041013032805551500440c1e6980c8200d8081a000110b42c510f00038001f1707009031301d10703866403400c0500d00642140e8002d43c10501135400c1034006400309400200b51341040c00e083d5145a5920203d1000421204102100030030052030301380049038000c240d94150400b1040c0e580300e6200c44804400c4078580c88030b0300000074101c0d800640368001c0380c200b0400c2d031030f00310780b090900c80e03059038491340001c0a8566580000e8201c040c04034003040310303035001d0285 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 101000530 1250 100999280 100999289
    0x7030e09101802071101050c0f030313030e090c04060e03010e031216020a1101030c020f06010f050a0801020403020603061014120609011d0a111b01020a030c0503130b0402060d1503020a 81
    0x214134102c00c40d90340f0340f44000100b1a10703050013008244444c1d10700050000c848003070606029269a480c068140d141040000302c2c0c250002442d120030280b450514000b031340d0003032860b0310310320342810b1412000310340c42c501186000e500365480308070b5070380d801e142003003d4200950040c0081003a441e02d0181c00b1081c2013680303104030456000c044000d01042b00700c80c5d00e0f1a102c2d82807a000c60700301c0d10020180d181450940c0103100ca80704180002030300854214000090703500c12941e0300c07000c03a99a04e0007400c0c2d008a000c040c2d0f101c4420800b049081ca40300281e050480030605000180300440480d04850307410010340f035035425480401304825894160441e40c05015120f2410b2484580c01c00900300c0d040004100c11422582c440788d5071500702c0208150384070840203031006a08009480b5420b8084d400065400c000f003400e008036000341500403001d50b031003181d41040700814900f140d111f0f158031031000390060ba002081001a04281180307402003207510044080c69240d540c1c69881800800c0c949540b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 101001780 1250 101000530 101000579
    0x3010e0117071a0304030c0f0b06010207270e0f030708120a0905063912010f0305150a02040306020c01050402031e2a030a030f020105060103020a1407030e0910 70
    0x148000c1100f403508644080e0000c0d07203162250781e185070a41d62050560f102030000c0c483e070b41281c07040207040341c10325118810130703800d940030380ea03480710b00201da403c10a00e1482551501c03500e240300491076a00241d01b0551040c11600310944503807601e400c69011f01c4091341e6208000525980503582000181c4c0c012903046030800a55056803120307601c421000c0c1070403804203402006807480e8100901442e00340d40b5510710f24017085407c10071031000c83c2d004a808011440501c400000e011980c1580c2c0d070300301e84c1c01a0213841e240c00c3c1501380191210006000c95203c1d81d00b488080040b9a103440544150311111b000043d581c2841e004244c039083c0c030710004a080005200c890800c44401180f41410690740200d200d0481c403c05140b031610480c0344000f56094800c0342d21140506520035400486c100c1d6035002081592120710044090344229141840802c1c1011508400140048000c1070420702900d8038500f00a0035000081041c6404d60307148030030b2544204184903440049417a903086080181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 101003030 1250 101001780 101001793
    0xf2715010903020a0e1506040b1216080c0f040f06030902120c0604120201090b0304030903020a06090308030c03191d011104050a14010c0503070302060708010509070905090a06030803010e0117 84
    0x2d000030500042401a48070044010003c03400c1099035004030200c110700140410f803109e844420000302a00003000728061050700101165008034881041a90f192031980c800585549802e52800c0540c4165070340070102d801000005403200808401c00702034849030741c0104510100740100a90141d4441c81c100c01c68000d5060000c0b0f030780c0c9581c1260101c610310200a4034003842400103880d8520355174003a00003c04000308100c10164804000816a442140e20f29003071070700c80350b040783c49900d00e0000411203142000450088c15020f40615400610301000903484001c0614103016100c0c076407061041e8031480103001c204024280114585e1741d00004a01c1d0400d8640740002c2c211144a1003200d4044032001800c00742e50340f0440b640301c0c40d1a0480e046070707680c07052890001d54901007200c5e0440002d004000214052600c40341c100d020301c0e5982c1d103002d1820708103c100211400050802142140e03907680000020700d0390310240d802020100d800005a41c5031074443c85c2c0c207449035903003a0500c0e041309 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 101004280 1250 101003030 101003033
    0x20105060d060b0402070222051303020c1306031a090c040905030d090215030f01080706080610030e0309040914010f021306050d060504020c0c030d02030c0c0f2715010903 75
    0x7030030000c141500310038080382c0340c104100850000d20034410083c2d00000c1700ca17044209440071108802a6580f2444204086c1c0c0d04c54084621101440c20002d0068009151b03070000c500e480202c00c1d080e0b00e0840c0e000a502e035503d42d1000d42e842e09850500d18181c103d0401c121321a8030503c4181c4c0c100006407410b00100c83d40765202601d070320442d6141340c1680e507100000310541d02c42c0b45030543c820008404c0d5558074102606058120309091040058034401c0b40c038040f504d603100e046000d00861001c2c00e280404208400c0580c040c00000084035040d100a1120345e42ca03a4540c020134503c9ca0294a01101c040c08102146003904c507030503e0b550b0598010403044003199024031050f001c440551030607a40381c1c0b1414404001500c50b0354407065200b03001284810701503a011840342d4800314110200e4102c0c1010a4041e40c690045080c080c800f9000405100b0751410585844100c118000300120310848201c0380780d0342c0310b5030150039420a2441100400882c0d004001d800103407000d0074240130000e140795 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 101005530 1250 101004280 101004289
    0x1406031b0f06071e050a12020102070201051204030c170a02120301032f06070602040603150b04050402090f0301060602010e07080106030b13030e0916140909042d0c06090602010506 79
    0x318109406500001843c0081c024070040e810400c91482d41c3c0c021030f064031802c0c40c50351103180500c1965201000c2d072014010038014030031075607030795030607102e041c02c08820350f040b01c0903020010700590610520f50f01c0d5000240140203070107503082c9584119900d030341041c0070007407038040d0700305048500050800c010310204021003811880c140c000200104820450140e09094030154550203412400c00b040c2941044025006002561250b039010442030000065003c40c8111520902c04050020030060106090a030010b042d020806404c03600c0750300a242c086070841c1d07107990041006035504c14580007100014402c0c1c6000b030140600911466040d5100d8000e448030203008040c0c41c05802c610074007014014880188280d034001e210b51251f2520f44c80003020301005018a000041001012001c890b80356401d8070565074014091104030390391642c40d10109501c02c48503060008507144180b20040d403522a60b040079106401c010007143c81d124001c5c2400019800210075039040c102005120b444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 101006780 1250 101005530 101005549
    0x90c0102030403051c090e0f1605130902030a090b0a05010609061d0910030b040c0501090501020d051602010903020a240302070b1603020408160f0b0f03011211041406031b 75
    0x10025800000111904400d5400030619400070010152087c200071900400b9101c0520800d415003807030380d0100451701c1c00c48091007104140c403030341c07500d40348140039100d0b581d8055644080c2d240e500141801503a02e4440c005101114104903060700c3e140107002056010140d10000e004a04002c2e01600c599100024001081c0386080d00407150b03440019108148a00194021508403000d40d03e503081504080c9070803916801518049000000006a927501c0095418540c580994070181003003030056944940117414101a41007220451010016030341d40020f501c01002e03111040322840d007403002007000f9a040c030710241c030615105200306004580640c1d401030740100d1300340c0c080700c0c4071200001c20380023801140c108188500c0780b4070204032541040100681900d00900300603444695452811085224170800c0c04085601840100b00044004c0f0300030381034501c070703070000103216081c4000702d402c1f505600094410f407241d40041c0301980c02c2c03e0007080f0030151114900b60101000700041084440e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 101008030 1250 101006780 101006803
    0x2010203190f0212070c051605240f0a020d090e0c030604180c060c0c08010504080a050f040b0a0302070209100515160b011d0a05060a03030302220b03090c010203040305 74
    0x1501c4021a0450403100e0b4111160400180c090013043d0402c0c1c1c100801c001080a000c96281c0300c0d00c0042d5032171410380d10204046034401401e000000d0050001c440000070200071484a02d4018003051001400c20720103004904250342c000c0c001034050f000001c26200296201c03090f1842554240f0003041d010400703c82d4010003c0ea40405e0980741c54582044940e07414401400b1200980c001180e02076202c43c183c0c2c8a00d000d40c20520882d5280c1e0703203081c01c03114191070080c0102c100b0460a903540c0d0250000c2c0812207103400300c4505065980314401d155070301062030700c00001da0015002c02140f600da101c00303030440d040d24500c1f04094101400700303868014a4490030f2400c8400300350340b40030000030908503178400d510401c3c0e110596500c0a0302112100388820302c8001814000000310120000e1007228820705004004485003451070320250002d611651155040f1050490220859501845050028041000e1480d82c91034071042d01030034840000c1540d81150420041000441d40c0054034907840d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 101009280 1250 101008030 101008081
    0x20712030c020d0f0b01080c030d020328050705070f0906140a050112020c010e030c0d02030711010503060111010e0c010f0302180f030a1203020a1b0510050405011d010f0b0102010203 80
    0x1543d6400c11104a19010074001c100406010002c200200c0c0071500c214000c005400701c1d40b00c0e00c00e03504144e869005001917001106001074000c50041c1e0a00e01000900c600d50034590700e402100d03140c803030404015811141d000801407030204403052540c414400141032541021181c007003407500041001e00b2600c0360341d040101d080443d100c0c0e102c1c5981124034040707084000f004040807401c0030707d84075000706210005038007400d00b464000302e0012040301e5140303a01428241c900407510006407041c2e08064a114104014a2424950301000344981030340369241c0002040c0100d017003400101200a00701c0c0c0401014010b0114a170480d542c0080c04191010132a41064000303094000720f442d02c3c01e0fa43c4041c11169500716440741d8a5010341c002c0010070400e6a071030a111098210381d032004000d8140003003180d8003c8012234000e040540c400c0d608544544004504a1820380f9082c1c002c0440038104002c40e50f48803a12180031800d8880c016000b10280002c3d070a41c9041100c003040c2c00b614400f180d056 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 101010530 1250 101009280 101009299
    0xc18090c0a030b030c1c0515010b0403080a020a1a090c0303040605161118180d08040b0603150705120f07020304031e061103041a060f010f031104080d020712030c02 72
    0x1203503014404c2e40d10f16100540300d1032003822040c1c6c0a03203030700120000540c4c16009112070ba000e006680c2d5180d43c11380c5c3e001280703a40f038145160b440001551140c2a42000c40c01071503404400103d8039040203014090443e84404181002500350f400c0c800070301240e9101e03034001c0108005603500b2800342c50101480c1283c2a1803400740382031035070419031081c0016500c1203c1107051840c5011135150700780a80909117000b4020088462401da035140d8901420005c035644000180004140c00c0b071030707035101e034014059603180b00b00a45441d0701040f0680c0e440b00420b9002c202a25560141e484284d0310002c1ca29180c01d6034102601c0294980c0b10301e0101514192075503500346840540c0d0220041040d5001004002c00420340429441c1d6030019202240d0b10301c82001c10004001003180d182e801140c00418003109020803d006442e52080c80945038140341c1c0302c03a0100000e2103220f000c0c00081507850b0103030180c480e000b14002e007414203a4000140010800003d5804240e02480008000c0c0d4166854140e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 101011780 1250 101010530 101010551
    0x90a0c08060103140117032215020a0b1902090d061e02031003080703140a030504020a2301050c010b040204090b1207031101081015090e10060819020702090c18090c0a03 74
    0x40d80b00f234806c0440c010b00580f030a406c8400c00c05502d441180c40c80112440016903a0404136103a02d248000640218020400314504011010680c0c100e0784064000601e003c90701804160150725400090340c00640c1d80055000c0c00000190f071001d00d0003074000440c518901200000305e000003900015221780d0002ca030030802c0600446032a1202c1024200e0191a280294001400703084125400ca003d0b4021100024080501c4100300010310035648511581b0b6074960011912a000903455568030b640701c92140ca25070310360b44000c00c0a0032104038049407950b503000500076451440c07690601c85a118030350400100d9a18560510101e4091030140f0694481d44070f418803c407100d801480b030a0034a1001d001c000398102421070111080e08003050020740d02c411680c00c2210b0944110303c0440c2c81500000c201c14080200d10640c0c21402c6801401c00360580c0205030b04c1321045504601b44840081c8461030a01020241d448144040750350424030b161580320350400c1e0190710009000c1c0750325009102d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 101013030 1250 101011780 101011783
    0x5120115110703210c1101080402010912050606090c040302060301090510030b0108030a090b03090c04020f0403050106060507060e19060c170901021803030a020a02130902090a0c08060103140117 85
    0x7151805420219101c4035240e081c400340131040000311036100d01d6560202d41142e40038444014000d500401040306518146005440b00301c00204100d0403c02c0c2c8030400326001c004641d0322046240a5002403100740f17400c0090004a00010307051400c01c030011b00c170400040ea5a0001c881c15100050004034244c1c9800f80d0305044801c441c0c00040c00c4581c004004600d150001001e8461011613603142000b02d0740d1404644500d00c02510f48404d10f8004ca41281d00600f042d400600010680040c0b0510b0240c1d65100d01d42114490f401c03813400610300184c0c55062000c00d0080f03042400036480502101c01e401150825a980b0342a4010b200c0c54840c4104c1880c107008070780516510034882020000c0d45040c01145000b5801803820701c030000445041042141800000d444403c946c640082c10322aa0715000c00011446044440c0f18070342d01c03000e0600c0141c0798001d00382e0060700c060001240c4801030000240802900402c0c880c1003604e09180c0000f154100b03038a00c0d0445100c0f0020703145000190320100d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 101014280 1250 101013030 101013047
    0x270203071503020c0d0f1e14130f090606021c12090203031303030f0f140301030f170408030d0b03031201091509020c0c030606030607050d0209011b030908060705120115 74
    0x40b040d004105148080a42201c0546e04d2042c8699406544969802e00045400086c5030080005404e036510b48107082040302c02445c00d05007040003a22050b9480340100d10303500440d0004400151206420032150f80c040100100d20702040021920722143d0480c003c0400c468030b50074a0740191100d20107815502c007442155421222114503040c0c0e2501c0b802d0142200019406e0341000408090b451039038148241e480101120781080d1152460b46540c650042c0c483c4801402d0b04d088045120103401e0307148041c0103100030314194003e036859202c11510b04080b101440f1170503001c0d0704200301801e01f031130010102074159000c28400181e145001d0040000c141ea481e08514241c9100049010382c0740000940401071707030411021503805560b410149512140141c8040020031818040c1c00e000b0020303a00600303030310384040c03606406c000180c055030315214101c0e40c42580410743c010401d001d1003109018040d0301050b5410054980724265130860910f40c01440b81d2244810401d1950b40300a01ca030414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 101015530 1250 101014280 101014297
    0x115080a150c120e07060e18040209040201020106120f0203010f0e0d031d011a1e030d0804050a150905060106050906090402091504150908010c09060f020f010c0327020307150302 78
    0xb04200c07034003c0001a9514020300a000103e0722000607c1e545180c2101a401000403403c030010f03698445900784007070020013400c100e0640d504d40c0030101d515490882d0301c450381030103061178100030b442c640140742c01c40e02d80d580381801d010700b0500f507128000c0300002c440c0d0684420b4640040c4801c0c80744e40001015040e003021301d882c0c1d401e2030140f082c48070100412400030300c000c49140e01c12150b0030428400701442c080006030984c003d03a604201c000c0c040d0381394660040c0100c0070b50b07a006000743c1e50012800c000301c1440e600c240e03079038205900744807040002e2405070103941069860500c2c504002202d41c000d52032450300c40d903000500100c1d1600c0f601960030030070000901290321541c41d115003140040c00310f0021000034241d0b40340059045c1c0140101341d030381c0d201c039154071460030f007400c8046034410f0b001c004402c154460342c1503070141c03640d00348035a90b200a02c99a00240c0444418100f04104801e0451911721480010b040e03801b598002c1540e108840301c4030000314650040c0d0301f0580190060356107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 101016780 1250 101015530 101015567
    0x601020106031211100b21010f02030a0e060f042a0807030302030a020d090320061215010905060712180305030f0913050f0408030c070203010e0115080a150c 69
    0x4959a0103801121200d040359140080c0e906004c0205d15031000c0319942441d5962102c1c61160800c68200f8a00c1b49907984c0c0c1003070b0700100c2c41a0b01400a103090b80d0040c3c4010300780701d61701c2003001000c003003d100c00d94100302c0303d907044001401d164030740d03400102c008900c110145006540c10041c01c1c4e45e0101400051032014251000c02d603072420065120380101440708007501035003d01030403c46c4a49030060a607a4042c2d4040c1c0c5504281041103a00c602c80c5032416000101002000109000c11900e1485a000280151407803c2c002000401c1c4908070790009005030b01c01c0c401e5000040380001000d42e003401918201200500c61803440200403120761001c0c1c0b4a00002032078000100245004041c400c406079060040901504006402c507035046809010300800c0101040004100030000d540220103101d00c941803040d1a0002403c50b0050300175181c8607036403030891402c4806613200700e9000301040c00140c14022071a8442a074640c10102c80780030302c3d41e5141e0614100900407044980803005141 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 101018030 1250 101016780 101016803
    0x2418050304051203040e01030303020f120a0f150b0d0b0a0510050301030302010b15071103031308030910020105091b1507030203030a060f0f0308030a0f05040803040b0907140108060102010603 84
    0x240991254401e0140c5800f824403040000707044000003003181c1c1210002505401c4a0380307142c80c101c0007900944c04001141c4020042c06030039031400f1414500407428100c0c0019100c1103c40c2c0d040486070708405234150042403070b1041111a10400030385a91412500d03010800125800014501c107035290010b0b580030802210081101c1c1d40000a54140c80c840d400030800d580200e0200300007500415a80c00302c1c0380080080900080c0d081000e4603650034050100e0b0700f8154055210540620700b41c002044d55030020503d00340070b2034480380d1020056001d000800c20350030314032007198403001d03103980600786424038041c6030200d13465000312014001c41c142c0341d00362500d1092074000d4490344103484120040d41408400305200d0038184a14003119100c1070b40c86103451440d0b5540d0040c1c0c000404021a4681d52444161000c4450180c3c902c114401d51500365a440c00e03140c4103c0021001d0300c5880242c0c020703002403080c0c42d00c1070900d0920a10900b40044903980c0d42c00100e01400c144c0e0802010310f100d09 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 101019280 1250 101018030 101018033
    0xd0605010803120708060a0603020a02010f1b023307020703050105040b0702061005060d1509060f030c06080f070806031f05070210140606030c04030606060e04060b072418 75
    0x300241000d0108100045103c0e104c00364221584141550000e50040d4081410820507000b03500918003140d0500020440f03041042188040361081901055507900080821a110b64180580c84844020700d008270419110300800784034171202c460315480c0e400d076004003280c5100d0080222100942d0312070003d01c0580f45c103140c0158281000c1c7c9001d4007510801e801b01d881404007207400000d5402c05031600d4104400c00040e000074100c14020340c0d041e240d0b181d2020605440034000c0c0000740120b0301448072160318500d0300550441c890fa100300100100300041c0074507000109003194000495143c986455215003001a0a11144021508042076a801c00c2c5559031040e0301710318440c100c0c40d0241c50f4442051310040058491364240d04508504890019039907140560141d5004440352142c2800d00740c40355115011124650881d20100300e4120011040d40707824000c11004d0140000301c141804400d030b0700c085106100f0119880d80e1044484c0c1810041c160754080c2a50703500d101d0501004c84001e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 101020530 1250 101019280 101019283
    0x112140403051c0f1406030d080a051b0408030c0d1107060e0f04090b071b030e1905090108010b030709060302031902060f0a0905040b0103050f07140d110d0c1e0e0d06050108 76
    0x5d840b501e800c00107074000170424a0301080008600c001c80d152a1450342e94146140000c2400030002c00388103001070761440b00c1804090240c0f0107840d01c90001e40e075441025822616000544210078100203241d0300340303070788610089400c0f0120342c00c6061122421542c01300044165071514036941c0c1203032414901200307001e01c0003030450203183d03991a0f02e011001041203038400c41c24034510290224801180314036a03401c2500c000611905c1d0094200210b03134039840000c40c1400c003a03020600f41c0e034485e000c8690364982402130800402c4401c1c4200070440c616804262510343c60304003112011180701c03a20381951281d03001c072000901c05c150503a940d06081000038001022a018031405285800c0c0b40200c0c03540644259400f841d01d1915036541652040d0089031204023044403218840c4e030501002c0c0001501d4052000d8540b045102c150700c600e5404106001c0f266084020700411106203400c48591003501c4d00f410780d0f1003551800b0810201d9040100300341001d2501e00401e1980b43c500002800c0c0300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 101021780 1250 101020530 101020541
    0xe040609020a29030c04150c050c0307150e03161503050a0b0a0308030c19090302090709030803070e010c0b0f04031b020603062701030b060112140403051c0f 69
    0x1088641ca440e058941c144a18400c0c5940e1a090542c1c181d00f40952244018401440d800707003038a603099103025150302c5110680d0702c6171111388012039400c20312001040b1007403148843e05101540240a100e181004104003800f02e1400e4005100018080000584013400302d40c1c2440d04900c6030b0031120b41c1c1c65000302c460075035040700301001034504008505550a01d00a4074030801004000c0035038181551a0042e4640c8040c6c500d0741c103481c0420218000e00302004408030800204e40740c03000c0d8585940188464850018031701c10801c00481000d01c00143c0c5002a80d41184c100d29184804442140040c3c860791203504000c1e0901150320708000c4080c4c200d83d030712442075210350340d0440b1800342901d036220300300039032000203611010070320019086003803105103004590380402900b60002c0500000300e55034042a001510035a40b6002080459600030f40000204440070108011032010307582c2c15207503207001410080401200085458002001081045061184210420140001c450380d100200f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 101023030 1250 101021780 101021783
    0xf0215040b16080408090907090e09010f0b0d050d140909090318060a0801151205040c030b06010504050307030803060109030519030e2b08042706050f031f060e040609 73
    0x4918a4100b09490303c9598424007950340103801c41c0c1010000420400014001007880781004220b040c00034282461131f6803036000e12201800060b4110f504500601611018802c15001d00c0010140310700040d400100102050f4030b6281a044030541103050800c0c920800ba421680300248100303000522401000405500c0103d502c540f280aa480c01800710b18054540381002040d07403030004001d1425030302410000c000c050710b00161100d513240400c004445e4180c80c10303152a14000b00910400600d4000e43d50001030900302103007018034000009030358403110b0100500c004004030200300759034013407a4501c010710707405826180702d003923005012410714851110642c002110558a4111405d065006c084040142c1c10f405901219910704040d51250440084440d00003c0000261840742801c00164242900c41c12a688190207042d400540c0e50503048144110021111000306940000b201e100d18403960031444009403041052400802d00341d4803003d005030140b000c0000b001169488280c009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 101024280 1250 101023030 101023051
    0x613090302150105030f07030308070c081204020109050a12020607060b060408160608010b0406030b130204060504050414010501050a08040516061e020105071b020a0f0b0702150a0f0f0215040b 84
    0x90b0713600c0d003c150361964440f0f40c190b80398110000074000319104003492540607569081024009184d55240d4074030354003840d1b000c00f503416803205000856074801c16640040404440c02400d040c10054103c02c40c00b4040002881844002085003c221880e040401030070300041100380c44d16600e84802d511000842e05940708030103c000c01007180d07801000f0642c1039448285925007064249103043d0010308801c126581d0100e004c000752801c9040a00080024120942d9482c1c1c0340e80c9484240010b5400340801c000040e40f0840c010300c002c0e40c0c840d00b81d406e8036045107005880e0b500c45040c45401c1c0018110403482840b550b040114443c1c6e00703c6c9860011907510b9051b400502250b040881c203e0b54241e80d40c4000070042180030407a031821811000c9143d0008000703445490b900d0740301c0309440a15901000e101180402c15600390305d040019207000c02c001d5a20315140c5200464020079041444241c0c42c140000f2041540c8110710810140604401160100c029402c0a007006200d1050444818011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 101025530 1250 101024280 101024323
    0x10303080f0c0904091b0303120b0f0d06020919090b18090a150e01050f07030b10050f0d061716060c0309090203151003020901180605030604050613090302 68
    0x380d0410700c40901c1240c0031004141040034071410800a4500100c05a41c0c03081c0746034a0a00200c0403d000800a500c01d44804290020050f00402910400d8003da03101d20f05441400000703031618042e0302005035001c14010307a2408030100203140000001244020414010000709185080b1390055000c1c0c1c0085404a6680c0d8003000c1c4100c40e6001101d1180a58000c1030072000002c003c5642d030502203040340c50124000c6d0b036a21026085401c01c6030400802e40c40001030200c0d103901032040344413a41058840c0710307140a81c0c00c2c0252440c4110302444200090019044000541d5075002130098031181a948141c1c900207501c0326552130313080b01caa400c0c1d059a000d00060803070052605411281c3c1c55101c01c005a844d10003960001d400080000e50240030100e0b000c10305654500100c181c240e02c40e100180c45010039000102040c51805e0740c081a00b60b82c180c00d10207542c20405607940101e0480700072883c0e55500d008141c0310a03942c0018540c04d400c0c0000c0c00c08258020907085d17a070388407840d0101310 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 101026780 1250 101025530 101025541
    0xc07050d020f010b0a15081803072405010b03130c030b0406051b03060d060b0402070c060203030103050d02030301120f060b0301020a0302090306060d0b040b0901060b040b0403030e090603030d090c0e0f01030308 92
    0x50303041c480c41066410f004507036145542d03d015448050b40803008c1e60000400450b5200520304640c00000c0c1194400ca070105c8030201d081101c0d03245250b080203000100159810500040448c1c07001422041e546c0f4005880d0008010051000741c015550160b110b100302d080500e42030010384416901109402442069440b490142c90256449110001d10022803074040391600f100402c00314030745641080e000c10180d40490244035241004000940c02181d907903142d03003000d40c1007211142d201d608540080004009414200a2001e444e54000c22490111345803440e002005001c0d1b045402e801d94004070b58140c00f117426034041c000c2c241c1e051302500e000c1d0742c8080411000c2000b20100070003490102020401280450740010b82c4801c03107000010300c00c1c0d22403182c00c4250f0003e0340181c2c3c2c0e030400090244201035225180012090081e036040b8000d040420000c0d480e4050300081c03007111a030340c800d88002d000040c0d2036900207008a040512071400c201e942000500c4c404d01042d808152844007140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 101028030 1250 101026780 101026789
    0x1e0405040e010e0304092a08011503020c0a03080604020c010f0510050102010917030c0f070813170a08030c0d0906020d0c0504030c0b09010903080d0905010b0105160b0c07050d020f010b 81
    0xe084540ca0f401443c5082d0400d40003c00403d0284240d80040722242c1ea4501c0e00000071090001e408461348801c1a10340c03520400c01c00c500030030002c0c00c4c08c06005110142e00c1354000100d41da4420f9240c14100761541d289400700340280034010086000d5030802d112404003c2a036030040e0301034003c1280703481903140c640c030059007030303c06450000308020180d4007071811030018078020b103820082034003810b450301c0c03801030101e18140c204050aa45018001680e01c00c070f2807420b00048001d02c2c949008080e040b0a800c0d800c0e4440100b004080d29010000001440201d04441120900e603501a0100700a00d003604041d0025006508a5180240b40103a40007840303024001391401c990703010a50b25180f5083c4005041160003842643d4180241000048001410340019000c0319814180005200307260b400c106003942c011840702030500c8000c002d4910a030703203c01c0b818444150032040070a4a07449039000c40b065032142e41009000390090171010502d086c0e020800c11103000080c002030054204610400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 101029280 1250 101028030 101028041
    0xf010212030a0b0a0e040b010f0905040305030f0c090a0b040509011e14030309040c17220803041103070807060207091a1c080d090213090c030f081e0405040e01 70
    0x11103900c0c00900c00189154450b40003000e520710013401e00d00b600f40c2e82c4c0c042d03402c0c801c0d0700340c40449100c00c1c44801840040003400703a10004003c091414000c506141d1009003d5100152016401c3c0200c1000a400000ba600448030150300140c810101e507543c442c40c140c003a4016000b89481408400300008120480d410314460091000b11a400400e1902034000b4050604000140d0507001c01e000c4812641e84611941e0322103012601c03502042d82c5085514441c03010028520110f2002100b5071400c450b02c140e11804000364011800c1e6a240c5490806140580c6411300f0540e01d44a1840302007055040411030702d0480b10b1039000ca80220340c13203000c0401513982c20b210502d8401e005010807091454241260600c0d0b0a0802d00c070403100400c0e844822455000080f03101d001500c4040490031801c15500701010307038080040411500c1c1856442e0000c8180c180700c064480300307420504000b03002101040300c00301b40c214511910301d074406114003421904130f44107a600c0f079407400515041a44042c001c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 101030530 1250 101029280 101029303
    0x3030306031f0f0c0c060b01080f0601031d0d020c0a0e070503040602070312060f06090e1504020c07080303130b01060203160318090212010302040513050a030c140604060b0f0102 78
    0x380901c00040351802031600704503040d98002d40d80720755121250b450030b440b544039805031556400600f00340d02e04040043e907401c0042141000200700410602507480090b00e5000142445c010680c89003000b6038460039025010380414038050b0084c9820b403030f82c001030680815881503d180c3c072081e0703648440c2d01d50759204807071050105d0303030420014001808a03802406600d2090400d4031b804c01111015104981071170300700d880c00ca40d036124180051a04150342200410400241d11b00c60f14015492080f2a1115200140070780d030003041c4c6582c0f2070b0003480303800d0280c0680b20481e51645008101c1d40c0c0780218408040c0c070f160b003d001c00031482c18408003c0b1400152100d50080c80c40c0700564048031065002d86074003604c4561258045040c10b503500080030f070400c1041c002c0c0e1183d41940101310031190098800001d041c400c101d0314000a60208224003070b01c1e0141000d038051381c0d003800c0500c424100465400082e00a180c1000f040006651204810317030350541e00032070814144401640e4030f80800e000e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 101031780 1250 101030530 101030533
    0x60108011208090927100516140d02090d0b10060507120f2a0b06040603050d030c02031b0619050601090306090510050c0309011a09041101090803040b180303030603 72
    0x40ca42550810074221500117040e03000b0603200c2d001d03151042908045191060400c0c0d046020340d400c1c801c16a018051b0000e207090307203040044d00d2960016000c8030070b050403a030600c000807134008040c8465a042d41d02444002d807a0011001d07203454a2a102c0000b01c940181441c50114082a26403145081d07174041d69114000708419070380c016051b6120100b024202d07017040310034055142184201c80c9a49866031360b0380d43c00711840d02e1902d44050307a440000d1189006070711700301080010510005841038500c09500340042c0c0038041540480c2103100b04070021801500c1110256031000d40007031000d208003003450403141c42c0c14104515009a46054460500040000100344082002c81c1c0c0900d4015102c0c400f01d411101c03400b2184800c4d40c0701100d909122090200030005c86070b03000e00511122910000310b00052203031000018021000143c805080c01e00f440b00d900d14981d004880c090040e088003011039850382d548030b110910341c1c0d000104a65807044000398042290800005590290304020b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 101033030 1250 101031780 101031787
    0x4030206030126190204050603010b01050f07050705030d1d010e010806040e0f0a03050702091503151f0306020901033209030d15172d030f0d05060108011208 69
    0x998582c04a03e462014070079900980b11856281d040c10420380c6220511012909440401070040200b00c5000618044c000e074146803003890a41c0e480002c0355006480644041c0e00c030260b9081092406003950040c0c0e4040c400c070841302c0307500d9030004100e00c00301203504580c2c004e0b510301c50011942c003c14251040c5c082482400415554039158005541d030280303007001c9840c014101a128ad00c0c00e94416000e174041100045d01505604220303000303990020b400020000d55202d01d9002c2030707560b07a440992941100d0030f1004110607400c140c8204000b000640c118041098803410403400a5100080185c0030a141270f480040f41002d06c0004548064115101d20403903507d40e9202078482c000030480e903400e001c100900c80c00b84403140305040c110b90751092400000c03030600d2580031030b41c180502ca070040c0758000205800042c504003404040c00c42d030119020101003011001510318010240500b41d082d10100740c00c82400000d80c005441810241e95111040e683c0740c02f00b82d200640c942e005400e890081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 101034280 1250 101033030 101033039
    0x3020c1318031b0807080306090610020c04050a06120302010f0c0f020c040203070903021903020f04050603031b0709020c0c0a0906030206040b0a120e0a12020316020121020a0503100b040302060301 86
    0x404505240019000c41001d03d00400d40c1d80d845a6845400103d42586c800b00502815003812031f680c42d40312500f500c40c5010360f1843c01000c0c1d40c91011a01c040c0c4600c0c2c4500000d2000c86d10350300000c0007496440d04250b580021440c000c0c0c0a00307200600710080525008100c050140f040c90801ca06070348030340103043d540b1142c80c1803101a60005010005002c400f040c00070050300d80408400d00c629002011084660541c03041000e05174010100724411070904040c84090358021046070020b43c400924000200030202c9001d0421545900c0718a00c18804122510070000c04140c5c0f5000389012100d40d503050392925801c0782202d02a00029402c060140002e000b800304c02c8006200305006e908042c0c1c10040c49203419426140120145e0350b035500440051010801040c0403015000c556002550600310703445c10804105041d030002074100f0252800140519206400c0c3c0795004c0c4140200b5560f514440314082c241d81e10136600072614000050002405005000c10780d0f003580e40c000c020342d2569191 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 101035530 1250 101034280 101034287
    0x10b010305060a1511161806050307030309171c050408010b03030f07080f1c0b040b0d05032b05010807170607090e0415060602160504020301050a0312170403020c131803 74
    0xd0380400c0308070b48144000e00311040b005e50540b00081c122106040c01540080d070800c03059408ca640300e14002d0307014a00074000a504441d0b810159200244411040402046c00b5440c0010003031304841c20030038514a83c09c6d01c9510000a2041c1d4600300c00038419404c101c1c080c55a24411520800b9500c54103102110000c0c0090b0001c1100003103c0340322074189440800c01142440b200c03142c41c03004582d240d04a000d40d08040c01039042502c8103d074010111071994484544034800c4400b0b0f0100c2c0000c00b0940e00c0501550703c2180382c0111060f000300403139a120100656a50314031b02550410004070400550f21490000f461032289006656840c05140340600301040c55102a00442d0000100e90b0945010401c0c0d12894000707240d41c0e4001c0044641b12202d140d0000700b19000741d405680100014801511212440b90803258010850607150340b2038081140c2c0d6420011a142c0100581030030707c42456030000700116051011201502500034150082d0308580f00300c0700e4004003203882e0a080000c00e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 101036780 1250 101035530 101035547
    0x11712090907080601020a1e03030f0b130c02150412110609030403031d060307020c130207030c0f030c0203120306041a0f0d0c0b0a050c010b0306040f06020904021b010b010305060a15 80
    0x6040c01203075495a060b03692300911451403100e070b030a02810707800d201d0b0071300d035250007018594200c0c840104000704c03e21011840d66941062202e98094440c084c1c1082c0600c00c1003446600b050307441900140303050625005001c00b11034040b031000034150b00154441680049400d40c00303148104001c3d4030740303880c5a50950300b02110244486070702e4a01d90b680d40c955100c0c9801140708407010341c007404011141008202e90710841da01c1091a182c4140824800070350084410f0003025000303070140c0818125440c003110002d0071188002d400d409030340300c216030050010f40914040c503012901804400441d18500b086071292805995014401c01c0b150455030502c0d031018820a40a20992042252a0640000c00703a00c020740c0d00001420010303014070382080a200f42d075801803084000d48454100b07500d6041e4125102c032001b8280319400149030700d50380e0340c0c1c3d4100d03241c9580a5891070846e5500b10006402403030704904040c0468189400117001d45006022002070300c55844a070b4600f62441c5000300c42010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 101038030 1250 101036780 101036791
    0x908100c1b05120c0105060103060b090307030b090c031f0614060d05060d02060c070501110d0906050f04050405010b0a0815011d0105070b010b0918130f030e040501171209090708 78
    0x2500306102007043c894008015244100001081c0c0c0d0512000050403140c2a91000c664510184840c0d18140d0b00802c2e1102100d402a4201505469940b0703c94203004001420984c1407207411510710701e2020442d5500c9500240f00b0702000b40e03c2c0c0e18014070320100120317110a54840000c01c103808070320400d03501c00b03a000368004d0042e80441081c1d60109480b40c4c8441d801b404140d0000320100510742c0c0c4401200d06204045010f082d0340c0e001801c02401e28803450040d1001d00402007800c0310660300520650f40141001030041c4902d50399280400d18580c0140210320000700224001510803900255258130124103a4403043c1e100031801000c4281c446030711030b40c3d04001003005120046050ba18000740a0501c0d01c06050340c03407241c0c0f010000c2c1101d0f05080541c0c024855000c2203100c6a0000b0580c880381d80201c0e105402c8012464222440c00a10003407030f600914207000070a100d07180f100070904200c1c10004840301e48050701504030701c5000d0324660f02e601210394000920070030f10851880f40c010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 101039280 1250 101038030 101038033
    0x103051216150209120609010b03011b2001060303080f090307050c040b0d0203060a1a0108151504150207080d030e06010513060b03070c020f0a080d0f050c07060908100c1b05 76
    0x132040500041c9030002501100b0f806030301800c14000d402400388900c403a070b070341c0450081290303c900002c1940c3c1c10800428110921540000071210000c001401c1103000703045000801ca81a203c2c60081c03c841d4040d1024400c4036801c0e40006d40f920f00020494022681002c010442140c0075010000500b131400c00d0540c005d070054800c64010784080140e240180084080802c100603070aa02117010021a01507038104140c003000d1200000307507100300d111201d00c1641c0320f9003403030240d4226040310b00c980e91042290154641041010744d40c0800c0d1682a110210705852019402c03d8084050f00c0d0325000d0210369400c8103004002500c0e00c0804400e0700310103660702080c0f0b140d80700b0b02803001d81c1080b104040820703600507581086282c46210f2581d030440032112071400c00d003010401951000070321807003014004000c42101e00103000381c081d603202488a508654903141c40380001020b0002c941b0901d2894428100c0352a440c2c0c0c41409461f48598296484080740c0440f030409e500d0300319403d00b054609 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 101040530 1250 101039280 101039287
    0x6040504020d020309120708070b13020d060c080702070f090504021f09030614010e01030803070207031b1a030c09010f0e040f020309060601080c0a0f0216090501030512161502 77
    0x240c0e111800900b1080c40c50300320058492920070780042c14003940103040c2905220400000b80021408000d03070380702c0c0d900300d080103840307030383d580c048026507805200080d5101c030500409804210780e0740c00120560640d0354070303c16162608036059940707020030301801c40e102003000c805020000c45075100e0b80d4030a0008040d6421515004a00c820042e004813001001490ba0001070040c840c0e0350041d141242c1346030a00c8100742d07140540340003480c0c1c1d040c000148040c1d0000b0100c1c07089842000b0344800355400403001c940800240238a046485120300c42e0406061004014419050524042d81d103c1d1090811203841d001a11004454603200440304100b03119000d2245d03042d684032413140e4808807815803001a0b6030b040c000310381803805c40010301c9581040214003c1008207041b0f501540c040a900341001c900746103a40d001a41890614511424000040c1c040010740007450b800150489000b0025141e03244103950742640144214442d104050440c20200344c00156411542c0c0580301c40441d00505 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 101041780 1250 101040530 101040539
    0x203070f030606051f050403031d130c1404050f10020f010507020615030d020c09061305190c080106020319050c010e0a0201020c03032113050a06050a0501140105030a0b0604 76
    0xd0034111600151819681c80c40140b185040010811040118410032010440071105004000c2e1045000040c00c012000d0000d046c100314080005104800003070591900307c5d04018140003c0000c81601400103c1041580d40c04500ca0421501900d174050805100c51000101340402c982c0c0c1125910118412004281d581c00020700c15640110740c0c55000c0c081c00c0c1011041d2003070042c2e0056070b081c0b0030b070080000010190b0300014210341440040e28480407541e1401d000030030a50412403481c4050b42047d003000406a100c0700020801403002008000d1001c0d0850101c42250f4240204009644100700000d403201c0c16a141161074111803500b14034259110610f613003982e402c3e1540b5003c90740450110700866806010101c00000705a0040d4148107000c0fa00319200005001d1400c0c2c0c4503a880c010900d64035001c040c0b01c200d250031078101c800485040c500540140f00c126040040d8618180021800b017180100000e02904c05a5803182542c03940c4071580006c10300b2841c181e0380647d04200015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 101043030 1250 101041780 101041799
    0x5010f0f0308090612010608040b0708010815071101090506040b150904030c05011d06070908160306150504090b01030510050c0f0306190b0d0609020c0a0b091006030602030105030c0d1509020307 85
    0x50283c80140c0d45e50000781064032b842411208040d1502007441402c0d401840400800585200c1c6200e009210341019103641340181c41c81602a030140500d0350030081d0401c280400060045e00861091942244c03a6a580c000c1e0b01d07078640c600c0b0700c6a40c0050303820041030100b03108507640d105980c042c42c00069014036407030300030007026000700b9080003d4103c2010009101c0d082100c45008104035005003070040303103081191050507150701000301000ea03078024004031016030081003c06484003400800070b03103400d804c2822918809203c212001e100c0c41d50301401c800c2d82402864000c2101034159424028052101841a000140300c0d54001c8861000642d45a51020000e4024604500c05580d6400c3c00748501054400315000040a94010040500c1030480040c0b98503c69403c2100c070b51070368940c1e05d502401d040b41d001040305103d00b840c10210078841954011030481e04100c0440b901010201c09100c5c05c02e04091000d01070103a085c016840c690306a0304505451840101520725443d214105103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 101044280 1250 101043030 101043067
    0x613050603130b1f1514040902031009060302300607050307020d030b0603060105070804080102030109020d0c1b110402121008010b0909060420031b030105010f0f03080906 75
    0x101a0b4411416440062200302d0041e607400c49006003510050031070b010310100311410a4418010004145540f4007041072250144011002d2400445035442e41e1f80d880702c00103500280c601d03001e603440c0280009100e4100c1d1042d80f08480d4058014030201e81e01d141000c050707029400e40582a03074083d0340a10507000080c08205d2189105445103503e070308044400a2034034021481c0c031003d240c80d000090401c1d603102c00a83c0d030303c402c2c24603010f0769580c070520302074030300740070315030100d0140e600100002c10301e8126a00035088240051000b000240c03494401190f00403c4048000032502400d41900c001c41c0c44011060700f1508041d1026141c0402551f038510100d0040322002c2e240c51700c40380d00307004046082c084c0c52508281198440f00c03600705042c1c4141c40d404050801071048405d070705840b042002046210b0b1100600401b500c001104500c1d040c1d50b200d07143e00c0454860b51918002154038504691024151605c124881544034250340d01c030700301a884614500e511071410f000d026030449079600c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 101045530 1250 101044280 101044291
    0x15050d0e0a0b01050a0302090402040e011d06060306070e010806042f03011701022104030903080403080c0d02070b16021903080a02150705030601080709030501020f12060301060b090613050603 84
    0x8215080030350900814040040e04101d12170043d01c6010000740c0d40c1c0410701034115404803800105014060340e4680100360940f2200d043c0c031a551001072441101040c1c851080030282c0581d8147d640347c1c1c00448031045496201408503d034540410349508040c3e014030b03100c040180c260752601c10b01d50010652a000c0ea0407200c82c09030000014000c0c42e03410018038452607030210017036050590381003e05140300202100c01c0386505403c00000c0c1898455542c6a00840e00000f003140c0d1507031130b4204041e41c0e0b0b0181c8040042c901c24200c0c00e04a4900c00100401104c0b400026181044c0c14191414160030050030103a920a0b1002100c41001000f40b40c6003008510403c522036440c200b40c00068200f044002081c41d0528400bc20800055004011264489000d1800c030b1010340d10914182c494166503003001c9d040d5840482c90400105031500205001c03545c05441012641e11300c0d0806003600d2160082c0800900240b050501500b0448041c251008456407010303030180e101d0300032074215001140d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 101046780 1250 101045530 101045533
    0xa05010f1d0307260d0c0e040b1002190311030a050c10050609010b0703031b02060603070b13092c0c150306031203090109210908030705060115050d0e 66
    0x41070800841d034400e00190000407009103041c01c0698442001c1503a9030318802040e070030480300d0400070041c84c80032138034010802c80c801c101c51102d40c840184042d01d00440c440c06145050355a07c168901000fa1101c048030940c000c010042d444030100f03091621038503003202800f0500f00e440500d003100744043c012911290b41c849444078000b0454a1900c001d4118a02669140200740030b025107414503010305603400081007135960501807408600a24429940d41c07400c5840c088503a854643c0498920f0060f0300840485025907203c1c0b411060b40d110311910f0807440b030b4501d0000c00401e5115001040c01340c07004200307600300060880d070001c1c04460034030410900b03810442098615142401501c5081202045468114078202010a944083e0051007840301c10000c400a07004280c00d40040b00305c154004400040c2c948100f422000e4096082409c0c40401c21041001c26094000025101082d800c14014001c43e40303411804503e200d801c40c3d0600802c6400c201110b1040c046005c0c108040f40c1210 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 101048030 1250 101046780 101046791
    0x1050103050a0c061403070c0c0308130302040c020c030322050a080a060c080103031d060906130801050702010203040f0f11090106110f0d090b030a090b16080a05040c030b0402030a05010f 82
    0xb5100506984903084030f4244845c03180303c2d802c60320b10345003500da1181c1c003402d02005248039402c1181c0040000c0d803008082c40000505103400c01d0040545108691095605000c0500901c00c00e0341c40c1d210b402d0055415510603c5100190851f071442c0d03061011030721203135003840b5407540c3c04a203030034000d50441d407001d40c41841420304014403803148240084047c50850150350440c0e8005040e0160300100c0c401d114901d0104500d5941c0f03204c00c0ba60440d03001040301da0303901341001c0c04e40c1c107125061180b07000a52030b14000500450040c001c072442541c3c4195103e41c2c140079076480c1581191b260704256108102d1a4510040782c0f52041018003800c52901e07440e0240385146500d0b841d00c0d104001c1e81441c1d801401000705102c0c0c2010842046e00c0c1c0034508183c40307540d54201c41300201440c4001408040e201000d004001200030101440c00102d40c1d00c10360650744281c40348041d01c0e41594020004142e41e00c00300302181401c0fa2164009200806446900100780c68181c02e48100800305007205a944 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 101049280 1250 101048030 101048033
    0x1b060b0a0605120a15090f1e0e060a06030c05060a11010203130b18060a110d060b0a0906030501030f0201080a0b1206070906080103081e070803040804030212060f0117030c01050103050a 81
    0x140d0303c2ca58403821a440a101d000400e0180c6640300c420b901c154031043d40c6a0350907064144868100b080c200d04501440c2d407218124981040c040e18060912994a000c1c40001c2442105503003e41c81c2a41d070080d80040840d8038210511040b0b603c440d03900300030048a51900e5003642000e0000b50b0040c8948115400fa00704141094641c02c0000ba01030541c2242201d4132006c030480c085403140c1d01041c0424009600f070a01420031000340714240c02c030300120303103052804030b5000c40000c054000642d055486100c06521101700754200d49080c0006400c0011000d500f60040d803080101641c03014200c980880d800000038045211841e01803100e0341c0c40e07007141c82000350043d440f103180c40c02403461349400030255156072641040c0e0310500c00b04000c801d06c51080c112400b4101022a0352595010349065941d00d030608050000741c100303000c12846850000c9030f00800300000541c2d140284208080381caaaa40781243c8800d04980603401120680414403200030105d8080c4034060007180904c000d00b0002005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 101050530 1250 101049280 101049307
    0x3081204060e061306020a111501090513050309060d02160507060f0e0f1c02030f0102040503100c0816090b0a0815030d080c0a0207030b01090b12030a1b060b0a0605 72
    0x4072070544169400b40007080200c2c0200c071380c1c0001150f002080181d80d6500748008550040101900607801e120383c001203118401c0c8880700604079008001c04000584035180c00d80307898000b00d40301501c25071090190071140c0c40c04100604a91003460801886c00c25001c01050440c54505001d44c2c0a4000030010000981c022104a2400c25281350200360321400f400010901101d03501c01034060b07000f002d0000006043c2c8803031001481e400400b2600044100c0342e0040c081e6225006060103404ac02040d915032005901554110007141e031030344d41e5540d0300c2c0c0b0fa0303040c52007102c1045402040320444c00000c03828a803000800b25241169114551440c0640d44120718200d0b4001c064025031003441e540440ba6845074140d500142800ca0580c0d4508038000c089190112541020300500e0f20310000007a403603d554042d0000b80001c1d144910080354081640d92a07010301ea0301c00e00440d032030380100b2174401c0300d404041c8080c61052b040001c541c240e00700460350000064224102041c7d00080ca1003c0c0c814 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 101051780 1250 101050530 101050541
    0x512041b050103060f090e0109050303240d080304110d082101050a0b0301050105070f02132c07060f050c010c0804022b02040b0103020714030415080609071103040308120406 76
    0x1c003802d00303100e1603280c410392035042c41003841000c0340c0f19a134403200503010000f900141603050300901100d07201c0c104101998008655a0f40f801500b43c0c044001d000d103810319650301500d95801012003420f41e51661101d82d07901c00000d4620f07901071540b0302c402c000290110003915042c242c1c060880c031002a07040841843c8441131b00a00e1142c5a10802000303120165001c80381503c5081c64202e880c2d010510300f0320000c00441da4021750051003441c40038100016588403002d0500c1d00071403000110340c0720141e8070250b0001d03602807403160000078040c840b050003125103180400c0b1514005140c03181d0040c0d002d00b19440b003e400000110b074074007030000750318010740400040703000647c6480c101c02007601c1c1d07460a0300001c403009003c1c0c1c0c0c49035a40842680285d0680303903c59080b0545078601c207605541c1b03a40341e6001c8d00442070b2000480070022092445211400e2048901911070b004030707219124180e482034400c801c042c88070b100810011000030040b4000e0085a2080220340800e42814a405000d650 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 101053030 1250 101051780 101051789
    0xe180109061d04080702010e3c010c0c05010305060105040305100e071d01090507030204050303070501060e07170c07050a120e03120903060708060319050c041d030301030803070512041b 81
    0xc2440080c40b003c50100c071304a0302140d90900b01020050841d10101d0541c42c050800d0b43c01c0303600c04888884600050800304145800288071242c4580e0038600155200c5403001d002070011402e0100500c03007035000b64801500500d050404d541084c0e920344c0d42614050501d00003001c41c0d03803030f000c121882d00010050480074080310b4101c1044a480c0300d000a80c7e4000c148264801f00d5103c1c00841e403040c7c0617a04032800b4100203400c2c0d03a521072950401c14041c0185104100c0780040c42d8001622080c414640780000102d41e80c0d040c02d907516049003006040d0000802036945004ea212a0800542c0c5c8031403105001915850718402814001c04240c10800710540112903440304202c0c2c2242640c020032625030054003800e11501548450b400b0a00e440444a0046907080701e18070501d0a1000c001410b410b5000216028003490140840194418030603c03902e002950003400140002203008014545c00a810300d0a41d01380410001042c88480d001d5400351064900b0054500c624181c04080c0c0c4042d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 101054280 1250 101053030 101053079
    0x503010507051c0c0912030c05060109110405240406170f01030309050909010f020409090204060b0c0a230a080403060509010c08060402070311011401180507020d0e18010906 76
    0xc0e08a0000b0744000c41007590009603a44d54412005600380902e030500081e0041e072001700001e01c2c061501500040000d1000d07030322403103075000000b02d000e00d0b4020321880c4043d80010702c0c140743c500030038050b16880780c29904a0951408414280c0c002c003080140000f040d051b43e030204104140518141c024074050302025040144000500100fa080580c1c00211102600c0c850b905035182c4030309900522060f0351006815000140c0081c14440c50342201003064001c0f241040a96a40c8a0010300c920940e1000416a089a2807801c0030500030f41055900003400400581c7c0901d000400c00d09003040b022007128074400201c0e0a0040c00000d1080d6035102e0714000081003039051544024006000c003c004a00c1703650001964003c05115105040d44600258024425101004c4112050b00002d00034a00c02254000000480d0801801107502070007064010f41801b4007695411070f07032008040300c002d4001e02021900c60510425082e404c2c000d2540803030005185040c41c00c04030f108000720301d003076415 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 101055530 1250 101054280 101054287
    0x61d1006020f06040b061305010807080106120b0f13061e05070302030714030613020301090507030c0f051c1e09050c0f06030a090c05060a020106060f0311031501110f07050301050705 80
    0x45080000f9940d402540000c9280c04999071417000540f2a60b442180024940c00c01000141400c000650704058400d0300c8000d02400d51580824403d2040040f40642603500700c03004200f45000046ca99500418800755090219507180c0740c200030390751740f001c0100303400060040080340d80000d41b003503a4000c112032805500d181807540d401002c5107070320f1601031031602e00040418030603a00e040c1d0700c0510f612010029500c03503039980710102c0107000884001001c20b05010304800320b05e100d0301d00c110707400d03035240c442c903048c1407a10341070100b02120f4082401c113030b55440b050280c00c0310b044080c803102e24070440e002065036402844d110381032103208080c060280f1070b40c0c19805041e80c2c490043d41e6201c21000400a030324801c0741482e150318241c51b4000780e00070360001000c0d50f10316410742003201a1001500c6100710640114411021139150b001d01c2118000c0500c0420800703035000ba030321400500c0502d000070700c01c80c260345418100007420321884045d5111507810466030900303000d141c1e0301c1a03007414242e04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 101056780 1250 101055530 101055553
    0x8130609050a150e01020f0703050c030d0207150c08040504020c030304030e040c020a03050c070e010308070b091504141f02180901051503040302070b0301060302030702210f0904061d100602 83
    0xa004014100003090108913010300485900c01c201d482d54190425040f5850031307130359042880d00c42340f84450440c00707401910440f14030b042c00050804100d4458500c0d50311506421201142d9140150004a40c1c000082200145955823800980409080c41c0d019560f01c5c1058940a00806503030040c060140382040070303038200303103402040d001d140c3c036058101941c2e100112100d985c10865a40c00c210040c01d1140300100a00003140003901c1194841c10340c0c508903896800405070340c0c0c14402c0c1e0485c1d20306100c50008001403d80541d64146040c03810448604102c00c01d0604e0111040e0134682c00b03040e0f1302140003038040003134044c400074201007602e01c403c81d54184030114011440807074080d100e0050004c045000c040c401c20841e001081003030112900d0b940c4400c1d005020b58000c0e20140010320500d210020b508080300800c4480341c400c8a0881d00d81030446112482a42050050b140e1107580d444000607100c030219103600803110860f103240030520b03100d0000420520240c01240455028500400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 101058030 1250 101056780 101056799
    0x30b030a021c060b04062411071701090b0f09011a060a080606070501050f040212010c0c03120212151002190b04020d08070b04020103050903090105040b03090a08130609050a 76
    0x25082d00c40c40322002c030100024241580913101c5035003074613041407a0140006941d000c4090410356101c19450007043c4440d0207800f190b100b1800ba4007550aa00400c07800c100c034502d03440c62180240700c82c02c00460342001c035803600e07104201c0032285160305a900c1007c02041d04028490b0031000150f2901c402000416080410002c0c000d80e25110709110400004c102242d0390b400070784d2000b071780c0100207000900e8014204640e140b0166400c9004e01c0006e4040c0300c00300f2040c02040440c000c2a0b895095045964031704903215043c0850402c0003030780c00c00014103000002c0350040e02c135002c03690900c1d0101040c00306000e8500a0f2010000c03c40d04402e200405400c000e23a640380b4029003181d242c0b1416180c40c00054494101920010030303400000032441c01704203503e440f0f58401e50003600c04000c0c503900c511400761a407240c2e011003800580308020a00840c0402c00180d0740184240003211460a9560b0b14810302e94001c040017070498080700c1c81080030b141d01c54410000741905862a000041c500ba9924 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 101059280 1250 101058030 101058049
    0x60902040f05061c0b06090915040302101401060e1302040801140402030f03040609090c14041805090606010f1b020a240311040306020d0f0203100810050906060d0c0306021306030b030a02 82
    0xc034414040343c4089501c6000400202c9400c41c102c1c10941309c00d060501d0003942d02c4403542c140703160f42e5003810000900e0b078003a4500d9604070ba2164403406400300001c4108100030340340b000c1d0100c50550074000441e20880c00d110300003814560b1116aa00c1f8100390040520b0f2040013001a29191300801c01401041d80c8450400126017203404081080000c1500550381e02001d225100c0b0001004a03000881b0f0002c3d516280c0c4a40c0b00c00810051a08c48014807a2540390440d0300302d0200313414151041031107211f400c0244108031110b40030b03100559943e0014a804030743d40e02c5204614489003a603100b04541083c0d44c0c0a10711035007801c102e40c15050846c00164090f07071001900d13440d0f010681590850b06904800682145602c00f15501c2c40c0c8682e001501ca41d15000d0640c41f846030001d4814000240e1050301e00503051100100140d03070f036110810a444050140480d402800100000300003111b0f40054514880d905143d8803010342050710041c122400700038441c0c4254803040300b020260703c0310400c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 101060530 1250 101059280 101059291
    0x60304030e090c1c0209011701080d050f190f1205040302060a050c090d0302010606030c0e132f040e061903080903010207051b0901121509060902040f05061c0b 70
    0x10794180ea83c40c1c203828100c1e0b0084066550701445420588950300c4050340c001c0004003000d0321640302c01d1950181e0410008824054803d00f0313844840c1b03210510380200080d204403145810b0680c9022644d0b00c124402c4c041c45400c00d0041000d2088056075580c11104d5503c203000d014904200380d19080e10025a907641c050840d2899070b82d500003041442c07521b1001c9410100011f010750038420300616000f0f0080c4450b00c9004000791404014050341c0d03110340340014080d04d00801c46400904203421820050140700b10652941d003e01041c1a0703860580103025200e22244e800c01a11a440c00b9541407240d80000c028612640b000d07040a0008944210880c040d42c3d00480299241c624840110380240301d040d5000e0440d10441c6c01c1c4041c10000d100d074806031290b00395041c100c0c5903600e00b407010b40c0b074240c04002041c030219101c034401d40c2c03402640030300c3d1458040d00b0081019070f0141c0103c0e08403103101d0041400d003600d560412581d41420900b920014101c0104620007150030380303806400888c05840c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 101061780 1250 101060530 101060539
    0xd0507050d022e020709140c090a03020d0f0b0105060c0307030e040e07081605010302190810030b130302070608130f02060c030c060109050c180103051819050606060304030e 76
    0x44640643d141c694070501da8042c054001d81009103066114182c15074140d6201006124003100420340003d507004582e62015641440c41c116110081c83d00f040780c0011085503040100740c070001015940b010180800c071402485240380103203460038800c04400c01600841e02900d0100310004078003c000044854250b05481c107141c0070508200058060a00d4800035801442036440110b011100861400c582032600c0c900000c6007a034490041d420790040721088200756841710802d0207624010008290f00401c001c09103e4a19269910300c2c540c25020342d400d003a084c4000d40c42c0e404160301040f0281c09440c040c1440000ca2034101c11038016621034003001031541450400140854848d40103072403e010390fa42c1940e031114515403050713544820900c94015014102400f107051550103030100d5030001610110642d03119410001500a000b01401034035074240310035901d4540034030601c00c602591070b211007411032500060400070700e07240c00a027416108150070418440001e0304001203400c0381d14145c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 101063030 1250 101061780 101061799
    0xb03040807140723030609010c0801060f0e0301020703030e06060f060d0f0912030203041208270f0f060105010306090e0606010c0203100e0705010f0513140609031213050d050705 78
    0x24000c3c104070300380d03000c1c107100c00c0c01000800207001c0903c50408106002c0e0304898090b507a4900407070130382c0e030502c158001180c0c3d60401440864824003400d00c00500504102e09600d039090046402c9038007074082034000039a00d03d5000c041c4001845404d42145084031240b4202c2140000913440384a1009188080c2d80d690f20359043ca43c1d404d80012200355040540100e0325100080302402070361048500b115104407030208405224007070444a406180d80e90444980c0c195120701d07440c0702c45151043e646080c42007840d0940c649408010f510442d48040340034044d503501d4280050103444158020494460412900d10b94a2400044169000100346003e003144002c5002090422800c3da46940e2082d05044903980499000102c00b4121a8207aa400d0500713480c10400f111103001d2461161044040c020303040050369120789400314081c00081501c0c3c900412000060b142030300552000e0507002000c28076000040c0a00d010300d00819013643e0358003001d900381e034031181c440300a402020321440008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 101064280 1250 101063030 101063063
    0x1140307080711160f09180b040f11120a030f02030f07080a050403021302030103051902030a0f051e0f10200307050f040603050411030f070e1b03010e0109060b03040807 74
    0x200000f00c018107001c004201d03919259017030901c0b01002401044007030f5080055900070099040c8440c02226040ba030a1507407600c55a4a447d07522204079020343c1c8900d150021a00a60f4410308204a80c0000500600c81300c40342d0318024201300645c07440802036404c1440314070070311800d44080300c0e19030b94000c022035500d1070000380a8030180115080030390003400c41007008055124580c001c0d81600c2c0214100d0300c06046400500528100ba100003c1d010340200f80e125000488074452113240c01c5c070800c01d45003250001c6840801c006003440052030320750b0040c458401c10460900003014400818901032003403001c01c98400701407040100350510800740000c0000d14191040060303c1e415241c003441c00390f58946e1030000901409058400785d801d0040c0c900540424600001e159188450850242040314544218402900001440c07002d404011040d041c541103030750801035002e0300d9005803504165052034002c4045030b0040c2c1003121020000c0041c40b01040f4081c0c19101890341c020480d03070744e0301c101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 101065530 1250 101064280 101064283
    0x10201200705070e09151003020105070f02040b090a02040501090509040c0b1303060603080405130e0d030b0402130305060907081f0b030a020a09021b0604110402070201021c09030201140307080711 86
    0x1035100400b00088103050290f041702c0031911583ca90480102c060403a225100d10b000fa0b0f900910009001c1403041000c60001040c1c4042c14031400d000500002d8100c02c1034000c079070030030f03411940d1030307210340e8002000d100750360f0401781140150405440c0c1610394509071707950f030210702c2c0d990182455409002c950380080c61009040c0c2d0300550307070025081c0055030340d030b25100907030380c0007805004d20440602007041d000010510a1601c4900c040300140101440b00400754014003400d85240d400540800041903a0035190300c0301380055200344001c10443c90085111804c0c10038507040504603410000d208000400e03d5180a00010301c040000140b08035810006803900c90304c884000e411000c21400000d00710240d6015115603540001288108041211610303124071040b40c0007040a0a104070b000403030705260b0302604441784180121001e00c0b01410030010544015a9002d0001d58290380510441d41e00580010001c0d981415403425414102c401425407031004180c04204010f40c080300005480 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 101066780 1250 101065530 101065543
    0xb030a080a050301030b010501050304030c020103020a090b0705060601090e150907170405100b010306030807080f040b1303030f0305041e1b23030607020d05031b0f09040b010201200705 81
    0x5200511558407104010007a089820910090360701040b03480000074154065011644610380c540d07160101c0d4682030380158000d4000107500f00c2000369915000c90100c000e40300521101d80140010403052401d80c000400a1050390002c04c05e03201040e061000404a20340b0201c100d81c0300306d45000155a41c401c040b04ea1104d440625a03083c1c5400080c04140000401d5480355a11820710071301a01d4220001541954560f101c010b000c00c0742000901c1c0810300910103000400780c6080c40c1d81c42d007561406050780541100e5140e0740c4a4142420400805400940080d440c882c01e00301402180350948a030811807425540d040d01010960703080c0401c0044035009841030900407100f9840c01501c4541c1e0005484900d0242c44101e9035552400b1246d1500040080c030030003ca0707005000c01c03404002e08071880e070000740c2404506072452001001c981441c3d000b03030403440035102c20280c441c0381c010100025524039801c103506591600e441c401c0d00548030806100b0245c1d1071600913a4440741450114648103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 101068030 1250 101066780 101066783
    0xa170c041803030c050c120c011d0709050609190e010b0402180906040501080c010c080d0c030f050612070b0f070b1806090c060a0311070b1008160b0d0b030a 69
    0x1403500c2081d075601000d4614091000c2c2c040e50707040084151441050354280b150128a94442d4008281500f104664100a005140745040045000c8003000c0c4120440518080c0d00c10381a0021701092003400203c1c4202e650144003241c3c9034840381440d40e0700c00b2154061202041005840d1004021104000d40037203990350809402199035802c5e4001c0959402c64500710b061042c64100c0120700140f420f405024184e4542d44068a00f0003101d00043d21501d01c0920f04a40045003031106946480c01303407240320411480343d04e0100e903416071800c0c0442102e1b0001c2495204c0e0440c2c029040020100083c44c00079504191201a581c88a0704e40c65601d03801801c00052400324030030100304044070300300d120303000700c4003c0000c44d0329640355070710003589505a4888071030b00801c3c10711500c20018440d4102d2601349001544091800340c140c0c407a4a04002c0480e4181c0d001058040100b061500c10000d03080001d45038881c007002203051010140e40c0303104610008101c9911000d8150079560140148900d0a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 101069280 1250 101068030 101068039
    0x1050d12022104050a17060112021f0503072c011d130207020405070203250204020705010e0a0507060e01050403060504110a091a090403020d120608031b06010b090a170c 74
    0x1520b821081c1d0985a00c0741c000c1c5402400940000200148880ea614a48441200c003815091b0300300800c13051642c1c141c045c00c0c1e90160404a1000c5903c003558082d1040c110156685079886c40c0a500c00f4003162210f0071408152140083c10075400b140103c0a0030f8100c0013441d0441130403940681c030200e002d950043c0e00da0301c144403108203c101a40c036401803e100c0d00c00c0e01c0500c000d07502c006041e40c90b8044c80c2e0310b0441180510381501441c844054190710041d2000348010300341440c0e41c8465013115080703000b00210754040f046501c2071180410804000306840d10301f688040c24403400090040c015440300404ca19181c001080400c007100300310b400244e001074006450340b566106034001901f508058504c2a0f0403036404006035080c4406014400c58042d0024a2030700f204003011990443c0035041900001e90707030940414112002d00050442060840c503030f0f4285081081040c0c20130406034070440803002c3c2004201840d4440c4500c1070122954008254441018826003d013420350030610950f01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 101070530 1250 101069280 101069323
    0x111010c0c0203070e130b04020102100c0215100819020604030b041b0e060901120309091b0305090c0102070302100903020414160906020303270a0302030309060f01050d1202 76
    0x1803035101003400d4506000302c0c110b441c0c050785c0e015803850f403500503038407200d99504442d0080c0208000001480c2c0052043c4100c03025180f8641c13492040318407450401006030407108610211020212510750000325000c1c40407031042c50f040c05c0d04d6450b4985400c0c00c01d12141c0841c41e605556a0ba070540d001142c020080803850301e003070714045010343c03d421000c090080f12013070040b9201c4115003000d4462200902020503603420401e0381d8002d500503c100300c0812600b080003103100d1003103000d1030383d92040b01c00500c11301b02c02c403001c05400e540004003c41c08a03400002c510740160390000b81034040340d4060320200e50024407170303004441c03824071a080030750890b00700400c0141070b550004115208035101070301725200d8024054100c805141d184139001c0168018000305004080c00301e2200310961012000c10400011241039505040110900783d015030000b004207c41140b0074494240d016801162041d010b41c10040000c05450034100003034072900083c1001801c442c001c0002807040c4103245100741c0d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 101071780 1250 101070530 101070551
    0x280f0303050316020102040317030406150b0a0323150607060e0304031707031d0303070c09050a050906040c150e1f030e0c010c08031e070305100b0412060506011101 72
    0x50754803d41c0c0308418a4a010101c0c540503106200380d40986e07611100031031042046600610700c5400190050780e4459440000d031803584020100d180041c8005054507489002c512005400c0341d4407080b91710b40c003114500c10b903461105843d01e03440d4007080c6042d40003110b0070241d010030382c80d000368000240514a41042a0141100000a4401c0741d21400c2c49070b20403a460619110540146c21009001c00c010701902c11108465135101050101c0250481381000d04540358080250440d520001a06a40d0700c1480404002030041e40d1b40240c54070001c1c0043c0c1010707944c003001180c1e5403180345042d2185100c84d080e0785108140c10344084200a040848801c0e849100e01d00c0d088000301040302103413030000c0c02c04003c60080b540c5c1680882c161500c24180c1429151011f04c0d51006100411707078904800701c010000c4d40b20600c103010303440302e03540000d1614120b40c00e1002031400d9084601c1900f811300c030811170101844441011154070a2010420391941401030312807680681c05811107508041c2e081e41c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 101073030 1250 101071780 101071787
    0x518090c0702091807090204061706010201240311030718020a0201020904140906010807150e030106050301090f1101050304020913060912021f06050105160f0807060507030b030c280f0303 82
    0x8113500d02c030304203a5070070594405c0c0f42401c034071030341c0701c0e010216040c044400c1040a0002455170300c003006000100702882898060032250b003000303c2c0590a0702c030b150303018000d000080c56001e40c042010350050602d03a040c9207244586009904640c04a59000070b041590f0501c06c0d0190355503041c0140082c00080709041064441000071108072a143c440e290000071200340010701031085800c1008821441400e081c8115004007a5140c040d0305592207038400150f0391002d124003a10b40b0700480c1245480442d41c87c10102c030070914100c440c10020288184405a9107000c0542d40160f00340e0722401c00709501d4680400a0300d00702d030340035069440920400c0001074002c510200c60b030b110140003800d20302c0d1100c0d1010403206540126400220284100d109028504a06109043c016540c00c0700025041d03039441c203107a00510007103404944500138001010740500815140c000c089002e4401ca00f10b10300812454400c500c0600300000501d9800e40c42c82d00d130b00d2003400c05030841c1c05c6100600c0e0340300d04024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 101074280 1250 101073030 101073061
    0x1e0304060c081302010f050a0201110f07050709090b0a0b1c080306040c0305040b04080708041e0509130f120903151508120706021b100c02010b010518090c070209 71
    0x1d070003103840c920003c2c200b807014602c004942c550586581c0e145005840013206d481e084400000155075842c03400520030034150300a80382c0b015203a4003442d030380e9205141403410000140c4c44100c01a0a00d01d406000035520120142c1c044022200000c9868240000581002e04036160a4402811901701418014844000c6101e40c030309845c04c3c41601c821060807003c4601c200c0e00030f03024440844c0030800045201d00208416801901100d060a88483c586c5140c607200741200d84180d41c00517000c01560070303d441c0d0740c4e0f80003c1e05d00d15644011300c00d480b464400c6a10b0040200034002d1f518590001e180200c07448005035404c011f000c400c00d02c05070540360041c04a80107401c9110042c107000036501c08000344650b00103403130543e10b07400c001c500e0341d0740b1000c0d40004076540c440c0002202c0c42201d070b0070304200c0300101040c0b42c000840c50181c200c0c800385c2190012203040c1d0401408111000ca81c07500110801c0710f40b03806844452950756954401c030000c1c010140c0c0294060310140a000c110014122070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 101075530 1250 101074280 101074301
    0xa0309080a08040c0515191e080109060e010b070f051011040320010f0806040b130c0e0a0f14060d02040f0305010506010810050915030f011a04060608010302061e030406 74
    0x38203204c0d0703194030400c80603000d814000441120b0030484913286500c001101c00c480d500f00e081001c514400c94490044450809141100144102d00100300710045030040078010000100102d1041d410000e8105184c03141e040050040c451948240c003c0050400024804140c404001c210b42075403100900700710f9010f03100594025043d412146002c01e5250b0406062060585a8900a00c2c25071015144080d004016651041c1d4a041c0e00341c042d200e1034402c1440700d00205001407881000c542c003810141c2e1805c0c0c414010480c02100341304019001c200841030f80c2c040061400782a9080c0c00041181c42906282c0b1140350000c10005035032078401018906580c820402400203944040c01110100d400706c40030200503880050800c100d003070101242d030b00425000a80010601c4030004a850154000c0b95801d40d623648a0040c1003610002000724003c00302110188541d80c6000402031000c003040c00068441c590000e03403038038840c0c0080ca03080c084031400d10b210303500e81ca42800c0050080111004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 101076780 1250 101075530 101075543
    0x615020714010203040e0c0c01050408030a0c020109020907180801020403050703030f02060606040308160605070f020c0904050a03110f0a080405010801090b03071712191103040b0f0a0309080a0804 86
    0x1c510480c600c000107005403010b0303000f1400c2620301036040b1449040a098540540804c00c8880c1f220802801210700c40c50046174050f98a0500c0003146040ba00829555000c5914081801307005a071080d02442c1c0040c02c51800b00d00502d000304c1400648141903108418640c80082d00008000c000308100c4200c0b0300a8690303409450900c4400d986650b81204c5030380d40190101310903c00584482c0260810101f074000840d0030342c201d552150222401580c00c172000c82c0e040303103071164910741c1040a0110100265080b03007650400e50748240e80d0340003512005041c803041e040d428489000411504400b072103484110344039400f080c104944264840d004903400200032500101e50f5144074040c1c80140070002c0c00400200d8503001b0000c038201101402a0340c00c0c047c0e8101944042102c001902400c60340001a6030003c04d440d5018210b40000d000412203030f08144401c0149038a008182e5400307920700c50102d42c0e03070340400408900900701c8103001400388101244d2507000c13550111501d44a02d10558 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 101078030 1250 101076780 101076793
    0x912051b07080715021f021c090c0e0a02280201090503031303021504050d080c1608040f140a09090804120302061014100e0d0b010308030916030c0b0304020d06061502 73
    0x4102c1e202c9030311410041b00c90081e1195a5100c100aa0050003400411686103050300030b10103005041ea4070607c015a2080c1a1035070900104600034842030f040103100034214078180d40f103280e00742da401203d44034001c1c1c1d01c114030100803024003c0d00180340462b0300800303490303072031405000301c000b004001c607015001442202c490440260110001d14041c9400900a0040400c01c1d042125440030040c0350001e540d9060000c0d0b140d001c0c011100e0b405203440345d94119140c170705210710b07001048400c5d440080150f640d500440c43e2502c5443c000420f440241502049081f01410450307050310441d0700840c0c011300003e1f1000145a030200b88580102021005d041500d5640d071100c00c2c1242c85803050070742c400005195090103502032640e025940c5c2001e03183c1c1100c0d004030b8a9841107140241d200751900c3c0800800c00c0820316052040c06100c0c120000500c041500399114880d86200f00d00807000704046c000040307019540c1d10f01c001c040c107680c400307418840c6c241c07500820038010003080d116001522846 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 101079136 1106 101078030 101078069
    0x405010e06130506090c0f091005030a0b01031b03030f0509010306080f010606090f0e0103020405040302340503150606030402120d02010c0e040912051b070807 70
    0x940701148042d50a0900300e0070020010052640c5800c010080c048540e2400d140740e042c0101503d90032640e59a001414100102e00e03002180e0501c40d407090300b810404ca000805059901c2240c09a019084424086444010601000700824049100313200158410303c050807090205150100e49c003aa50f4007043d041a0350580c22054a1351142403d00502c1d40007014400103101c0210000000d41c0703040612110300b013060200a00c40d50b1680081801c1c0351013080001d040703400f501d50001050060004105051080650b40940690203103000144c5103004104035441c208600c000806c6070b41d4030401c209147e8030092040f070b0b00141c03055a0440c1c00b801000b1040410080d074000140c48900e007007001d044030702005030340752003242801400707030000d1502e10325000205082d00780f09441e466041c00d540d0003144d40c0b80c00340c01c2501c2001000140b110300011f40604440101e00c2520740d51241 = true := by decide +kernel

theorem cover : BRFrame.Cov 100899280 101079136 := by
  have h0 := BRFrame.cov_init 100899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 100899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 100899280 ≤ n) (h2 : n < 101079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
