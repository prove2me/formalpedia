-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1283
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:09:29.284782+00:00
-- url     : https://prove2.me/submissions/469c4cc0-2bdd-4967-aee8-519789f6ee85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 230575539 ≤ n < 230755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 230576789 1250 230575539 230575559
    0x3070201031a0a06120b030703080a02070503061504020d090515010f0611060a0209011110021806070210030906021626120f070c0812060f0a080a020f0a03050607021f06 74
    0x41c0c030100e082c601031001100003010f01030700c00221b8084d014081c2400000c01c0000c9a0302401c14802d490302070b14042d030780310f001f419910001118083c1e9140403241078ac0265082990041461a20075007000c0745101403511817500e0405e41c00d013103d00f00e03ca036074010403050341c00d41ea40b00c001d0400d40c603003410350307a46607180680d80d01c0000e001c48154590000f203500480e030141e00b04140e81c5130003106481c80418100ca107400203401680c070035140c2c24070710500e08001740b41000c08c88448a50007405030480502640c8101d0042c42200700031940107908000e6940075507103a592081c81c02d4441d040b072800c1050944000c011414100c0101d007030044080c8103102c07452011041c4664000002110f14000e070b81c0326242101c4e420400200608203003400112a03130b42d04050216540300c0e5805840d190f0304900a0b40034004c071800c03e40700c0c42141e600011403140c010701d4965610001401d0050070303844200c3d22501e8960811000f92031030070169000d00c11305140e602e500c450740d41d8036540302d0340308010091424440715 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 230578039 1250 230576789 230576809
    0x50408072312090d0b09030c07050301180f0302010b04050a0e1005091903140403030f02010b010f021f02040803040801061a0a08010501270e071106090a06111b03070201031a 76
    0x90010382d001c24082d840e9280c2c0400c00d203425403c9031003100d00b4184642d60944030340c01256503242e00c1c00f03003d001090504050103010b41c0c5410900b000c3c800009251640c41080c0241c40c001c4045540302e04030311540713a80740d009043c0110800c00340012404000b4400901d80042c00c54134807034282c01d07c001c2002030300b0007003040d02d80004d01ca01d058001b48070742d24040356103040b0624141c100356804100481456808150038100613001d40003008461010030064448083c030f07544150044c2c2c00310320440b03100e1006a00114101003000e0006d07003015242e03501142550840c4c1c03c0704000740c0d510b4104128540c2038020709550700b40300003050342c07a00d0310814000308400070500a280c14840c031803030040c0800405640d402c41c010300c400d00203a9401c2c0c44000f020703a050000e0350fa00c00006d500103100e401e82c00d030214a0038003606d602c400500b00c0c001c1c0c69903420f01030080708080f010001420710180c0c00c00c440128140800b4152840515644e04280c4000340841c0c1c0b10300b10f0314110490100a185990721802200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 230579289 1250 230578039 230578063
    0x180306190518060408030103020405010e04150e01091a060a0e160819020d0b0909030a0e100302190207031a010302030c2b0c0e07020303070f050c010f0504080723 71
    0x20400c0d55600c40540e00d90b401403403151229200d008100000e0000d000051810b0341d100f10780a001c5640c0e9940880d409003000d0710080d1109861100c900c8401c19207900004040842e000081078054507a181ca02c482446021200c3e61020020100801841d1250451014222500100c803031420001941f40c00c240c03c0c07440d05401d0100035404100070311241c40e80c01310341c05482c0d041513650300f41a0031084068403c0001f043d02801d00300020901c1c10304013005454008640c3c1e40c0c0d0a2040e140700080003400c8151038a41c0080c180d0810002f50201045c00385c4c0500f407010780e002032003c142fa6141c850244503244684d5562030380c0240041c00165808580648420001c03240480780e880040e02010b8015100b903081c0102c462083c540c081042582d05940d000c8861095214446071303640380781a0b032030707100448616000035040b021880402d1300600280c400440100000500a845188904115101170350152040c05010649100300040c0382508440d085485841e10318507017500a41603661792903240d803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 230580539 1250 230579289 230579291
    0x30b090c0613090b060405060c100e19030c08071a0f0604230432100204120b0408120705090f0307060509040b0402070c32030a060e0313030818030619 66
    0x3013807580d0790318415280608001040261f6548280107010b0303603000000101e4000c0350416210150592010584000e51860070f802c900440c0043d030b408691040282c0300c21555103105018000106002c008012040180d00382180f04030b0800b03d4a0320b91001004003554480c50808d050b0901100035903c050301e0310048074911b1000c80d1a58a070440c0c040326270708200080e000c0c210303026031880d05421600443c0d440d410b07410b035111206010100401e900c643c3c01960f003081c0c110888c400c005540d40586c281d00a0040e20f41700e0500724100c40382c006041040e5685000528003180309141c500c1d1612888501c01d10407002072008514018020b0304900401c0a070320320840d6102106045911141c0403907881d55070000420583e1a211103c1901d40d104c0c000c200f03550b54508003150144080c00e50003003000490014002c2170b02199941c1c0e0100541035084036984a80810301c04108401480d18000300130750301c642c0c0400d80b10042c580080704400c03c611040740c401d070b001c4414001451111583e002d8440b0394580 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 230581789 1250 230580539 230580551
    0x60924091216050f060109110403050d0e060d02040e0f07031406040b041805030a030506030708071e150906021006050604030602071a04060501080712031b110a030b090c061309 77
    0x88031045240d4101a03c1c41c0140c40d041102c80c039012841c1c5041e55140c41e0200071442c0c0140b5004001d000b14080140540d000d820040700c180e0140000b01000400286041d20300014000b81c102030b43c1041e400958030400e000180083c00080c010025072008592030704112065850032840f21060025000c103009603a00c8410b10040c1c0c50302d4010030b120440c0b017410340500d0303841482c2c1035650303602c40148500042c0c50400490958500403501e20200c50038900100b001900701041e039500c0c0e01103000d0000c101c40100c54005050045a280640781501d1502c0780c110300ca00c0d07c600a82003298582581c61003503d400014409a41c2d258280c0342903039008080145c03230309960314104c10a01444c80d1181048113030541000208200c0c0c0d08441d05807a040c1c82513a1072107945020203a22400d43c414000c1c0402c500c9142c0c008002461b84544603124010750050010701d148102051801c03203903030015030311203041c107040045025040045140000050714401e1900540c051001d1001189001d103201080e1902 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 230583039 1250 230581789 230581807
    0x3120606040902040b03010f12080d0b040204090905030909060105190e041d06091203130201050c2803020118020a032303370e060703110609240912 65
    0x10050760098000c00a0466455032107610405480d0800d104191301000b030b80708080703040c0c007540201c511120782c00114581045c60140f201d4001d8041088040d82240c0d00340070010702002ca5005690030980140003840e42d841c0c03880d051000394403004000c0790612000b080409182c4007055807920700e48040e4980b941d03c030410b1800150107400c00f20840b040c00f410b112a45080014041511405880c0e81400ca42429180d00950480c42c0404c0703490b65900e9040c5a035031005940900300a104612140099900000d00c10220300c2807606070181d240000c501c84006c0c0301c10542c0900c14062800031402c184210065a075000a01590207400010001c481d40c81b000d0034102d21503080c448e2445824002c0d241c980c502c203c0c04031200d5241c1d05240003031181c504003184004044448094480a16948100d003211484040c40825404600c0c12010086440d0725400700540901007940a40c40c0c0d00c0141c0440402d1a4000e215290400c0988801d070f6504070074000200c80000c0c030b600c3d1212034000c010382c644048e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 230584289 1250 230583039 230583049
    0x3050a050f060105180d210c030e01050d0b0301061e0e040f0f05100606050304020a0b0a090902090d05010617060c04060203030403080411130c080901110d1a0613030510020903031206 80
    0x99008560026580040c0008001f12408650103c19a0f048020102440c51004a4408800500c044c0c0807855032040d010965128400400c550440d200000c100302c0340710004a070860380c85500c10398034030501440c80102204040e19400003044440d2041d88541080c0d1180a5910044040200311a001020040c10440f09220b05880750b054042e003040840c0d03a42d1030282a940c0215801c03407040d4104d00001c07880d0941081600c401c04180c2c0d896928940c1455070040c000e60000b41240d81c00041c10700180005142402060003820018020a0340300700000040c500e804c401900d891401c480038001440659400015207601507054585003449403079500b807032130880c9141040d1941022419682045d05a40e54028801500c1e040c0d94030040c0781d0b60044e0b00d508840043c051029a05001c121001c0b004200d0b41210f11203041c1281c1d0b1050301d902e0580003510b158882c510300744211848202c108240a0240802070100700450402c1d8944196000029140d100d01109601d00310700110214000d5290 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 230585539 1250 230584289 230584327
    0xa020715091502030a0e010c051902310c090303080a020d0615050c0c03070f0e090f061008061012060207050705060309010902091602060403050a03020c0304030f020103050a050f060105 81
    0x4002d0010540c18840400a44036400000e00c0c0002c259011200b224a5104230b5401c0c02040e0804d0141820701400e082e41030f403892880d00282e0f441390301116519250070440149520030101402e119414050040030402038408020900c0700307000e00f0600c10008640c000c042c40741d00020b80c4d000141e84803005002180207090907040030180420084164541d51307000f00082600e00882d200312200341c0b0b007a00030155207001da801076185044a00c00d04010244951108130381050141041c2c844100301c002090f450100102c0c1c894000d00d50805040103035010520105401101c0180d111114a0402c100704038a00e07801640103041c1940050b0340070a1007408d00070300000d0407005010542d40e003815072107140603100310312081c0e2081d40d9003408103400c0c1c0352410a081101007160007030100ca5890751402d4400c1d802807187c42050513020401c01181400a200500c069849480d1210002c00c00d40001001c4410080070300031810318100500c400c1d0040b03c80141d500041c246072640d610500252403d4000310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 230586789 1250 230585539 230585549
    0x10819080d0c030204140a060906050a03060e040b060a08011104030206160b070e030d030603020d1202071203200a050a15060504050a0c020d0810050d02180403030509120a02071509 79
    0x1c0751190b0008181d6051300100b0440e60580c00e8842c95020200401201070312602c16100400c070344c14801c00c11140180082c00d1240c1c0b803400c0005109560303200705041e42800326400c8907511119820000c80d071404d00da000016140c0b04000300203800320710304149254401c0b0b000c06481031101050b0099100d00945a83d841d46601414200643c1800301000c2c2403030781940700e070034403a0046038180a0352500c60321a880880c1e800811b040c11855444e00d44460100171841c0c490114054a040800c2e030900c030a00b04103945200c0c0c2c0c0c1e900b0340d10500c5801054905c01059102c07441c1d4201d0356480010810025501102503045001508400101d0a008004140300e51045410a0500041103000e600036480b0043c191150b030281d0720010620f40d011240204110b848103c03084171450103000600301943c1015880344050301c0043c01c0300148601c42c400c070000311000c0700000d460301c1c108501c0d10414441e0840b080d18040455080100e540c2c00030b500c0d4100f45c000c00050700d0350201590b210707610410031980100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 230588039 1250 230586789 230586791
    0xa0819061d0402030d0507150203040c2105060609010315051911070b0609042301021e070c0b04050604030303050c07120206160804120302030414010606020a0218010819080d 76
    0x301c4501c40250400200722820381c864024400040d0460b401101100c2c0115070054402d41c02450400b4000025000608140c03400d6201200100350300c907000d05682c88140c8400702507036507001c1a203419454100024160b50082c0401401000091130019000484036080300d00895640d0302c800207032100e2160446400c505c14142228a4031428408004001c0d003802000a440c85955407400c0c02052081594020115252000700c1100e40c81c00380c407501c903807443c1c1000161070403407442c000d0140d204400c180394280303e07000200b80081101038140c1000074110190b80909240c80e060000394607001d0351001405041e02c4d0400508012620300442c1c4442c1e81c0080380701102c5009910095035200100c1c1d41c4544000000c06850006018a4241d1300c1540c3c401000000181c210404070044c0d00043c00c101e482c0080c0c441c41e0000080c0a000305005094103900403ea440d11500405c660f088084240c0b0041c81c03880310040c0111540800c8491a218042c6841c030448a018540380081c1e00c03880034824202 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 230589289 1250 230588039 230588069
    0x3021f030f1b030608070503061605090d0309050f01090501020303180f030c011d01050103080712121121090304060c0321020901030509011e0c03020403080426030a081906 75
    0xc5a81000c0e01c080250b0705a03410072020352260f04141c1d1324130187c01980e0341684176400003240005104801c2d107101c0c09900d41360381070010349004201030030041030301240416403084042c00542001c140030b490501007444c1c01401c9a2414001035107900c400390010b013040d0741d80c0320146a112800c1000c4403001101c40100c0365607642d40506e90340200707280442815040d160b4400b41d580004140541d5060300d0700b0500a03854440ca80e82c0b1040c404001c04204004d010b07000d0302181c0603504912038162034211041002e03648511103400034046185040c1c0350ba8086825006211480000005490a540c02c50a08881003811800c0a45e020304600c0781069100f500e214840000c070109402401d00788000fa20280090740304e0b03c01e1242030361403400c0003401c8948121703803c410030305481c1c01000302207030035040c01843d281c3c90740c41e1000315500580020498460322443e0101042403101c1c04100040308a0280d4200034020710001c21919002c0c18054a40000040c011888681d0341d01510090904500302c60030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 230590539 1250 230589289 230589311
    0x51b030c090a0b030f1b0d15090903030f0f02040b040902031e04120f08060907030c0302040909050601030c05040203091915020a0809072309100b0406050d110403021f030f 75
    0x40e500c00c9417802401c0b803401c0d0200740c2e02a0324007801704a10052400880c14150054800d4005240c0d412521221489082c1e0000d4075502d43c0c8507042c00580203030340200f084c03220305a0320b00a4500704480c143c00d90748108000c021048103c400d9a0645640744805a625228140d6480c440c1400c1d41c4001c1140d00c00d14144801c00045600c170b41c1c00c10400fa11810480540d402c82555144811103805411041e00c0c1c0021301070f148a40e00100040c591410014180f58981d698902100d118040c101c4150f4880001030060110250010009000c2142d040d491458070705001500d8110405480306180000e40300b039401c00424010701c1c405990401011034a80e846144001c2800c0000e542600d21170103105404a0107a500c0ba03075141c141034207403455541c064000011302207a040d000340903403808510310304040791042510f0020401440c0750340e500d80c0c0707852801c1d010100311911081719400c615010402000140c8498062800003007810680040390040711900743c3c00303800c117111500e1942e890241d171009 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 230591789 1250 230590539 230590559
    0x10b0604120c060f050304060e0a050313030b01050306060a030f1109150906030d09050d0c0b030406020306100e1c030302070209090303090f0606150304081b0a031101051b030c090a 79
    0x2918014064200b81d41e9030341d00b040d150940c40300c10710000600e0410008000c1911504400700c6102c1240840310f940c440354030b650742180c01c855000e840c010010a008c000b40840107044c140034206c1140030b00300c10301313000c0c00188020209120082c00c503407088000c1c0003400440c00c40342c641040c002d01030703441c91311780300702c000800c100183c1102d40f007408141c0200b441da082c002400803450300c0c90b4640d075214608180410000100c0d4035800c032081290b41c000420160620b20165000ea0300c101da0258481c2054000c0000384c1d090140d0100c10000c0782c0c2d1715003050342e858801e00301c2c80800c0d07007009603111a810304044000e88a16a4065041100c040a20040038800802948100c914100b6102400252071902e0b858860a464040e4000c04000c0c5035400e285404d0015504036115841c81c6107414a074050641c0e440b10b403a80e00000c160007284d10801415000710301e0613005d0280746e000308007516041d00700c0780700c854660398510903440001c4001050021884221070142c0001403440c0d500c2550740070100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 230593039 1250 230591789 230591819
    0xe010e1f12171c020310080f071d1b0d06050301090b010f1211091816030314030f18030912010203040c081203130809090924010f05010e03010b0604 65
    0x1110200001c00385000e0265a4043e104144081d40c0c1100c0455480100003002c0e4001030f03d040c0020051203800207101314204182040c0c80342000240008078605007a030078078001c4030810055481d2451003004819031200c1d6401807035108048883d0745801042800c0402410700303811490301507103090886002c1c0000c1c1050a0304886281d0011280c0035140d5100c8224a142140020800040300c4034003800b9140030342c2c3e019401642103092100d510900303c4554070342030301820b0314030210b08400410300901d0f9000f4100300c03c4100f8980ea06285060001d10400c02990041040d0050802240100c503080d209004581ca51394004086811103e04846110300070b50054031708465440520100103004d51010464200f00004031404e50704642d00c2c2d68446100c1c010709501142d0708201005100c0c540d540d400d603243e004085800040c0100e80034064400c2500e44003c0d900200344240300300400c207544e20f14074070300c0c240d40c828a030100c07801e00d887c0d01007405440c01c0d0281aa0082c00468003003001d4042d10049 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 230594289 1250 230593039 230593043
    0x50d020c01091a04050c03030c0706030915110a0201052503090f06050c0c0f070806160c0b07050903060f040b01140303070b0124080106080c0c0a020a0b0a03150e010e1f12 75
    0x18480d0704903501c0c20150f80327105c0c644041e2160f030041d09003007020034003a501c10050303a4007440744000d880b16003013460301c2107030340344c0c00b01c00340a50020810762012942442503039489690101846041f1000c482d0000c8000580740e070441c10161145801c2e010450202104000281d01c800300f40950300b41409000640e4003c1c00c8101c52b14818150355003e250310000303110007122403444c0909020389410900600b0424915600814080c0c034a4561f00001e03d00b850f0f940c49007149617140b1303442d07010803810141000707406404140f403400100180404910a43c000c0d904403a0408202040001800c0201e0b0a6014095001e05100124000050010202c1420780501c4001035603080310801c21802c2503903091001e00885000409010010b412080c0d9a401030080e8080101103c1d1031141c194000f440c02c10417500300c0c5082050210300800c00e9600340c000e0840c1500e001c00310309195803d00e5540d50880805201c0e5840041d8070401082800c1444a540d601000740c01c00c45403034485e200c0ba040d146070007103c503007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 230595539 1250 230594289 230594293
    0xf01140d05160812040510031805030403050a062a0807020c0a0905160c150c0314270c01050f03040303021605060105100504061b050309031005040c0f0501050d020c01091a0405 77
    0x4d07103080007140031501074800003800c45400070f44d040822001088942d41c02070040d4403140b2441c000c14000c0000c0d000541c811001811100d425107004801c0e08d11041c0300941d860400c0e0081856045156561030403001c16107009000340d59000c2c000c0745000c0c0f180c0d00e1070303400c401c2d0b81201040c0d00c4506d80005110304481101c0200c0d952440302d040b00c41072041b60004e4143c01c81d00e104c00480c080d0b1030300205080000c034039022500c2601c0382c45d407500211040e140c40c611142007400b24a4070b000342c00b02c1034107001208005407145520405c00a415032242d900668a000340c000002001c05000c1d40c1542d141c080d090b80c0c2c80c01c140c141803400b03694801003801070324825148030305046049442a002c03102602c50b01d0799900403460f0740030301c818034400c181441180d05020a02031054161030801803101d040f0b001000c08940ca04140c10100661544c9400803a10f5210380841030003a03981210417554124100e14005070385210b010344481c01070010710401000701108021150381c40101c402107500903030003041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 230596789 1250 230595539 230595553
    0x61e23070c0308060310020c01270206161a150f10050409181a0702120711010c0311190c05030a080a120b041107021306050109090908040e01080304030b07080f01140d051608 76
    0x80c2c42c1202b2a078020000c0d4000c0f020000c80550501d01d01249654502c65454000d4071031500800e542409421941031994204121413803600e03251500342c2d03501041007607071440340071a00d803080103019208500582c28500d07103441b8000b0001e81a2140f205402e50080c480c1000c0101c0300c034490300740c40b8054640394014402e02001d0700144038500300b107400003580000081042c1c0e60190055401d0540f0305e0058050040700c07510340100c0c1100b4804039101050220500fa092855441d1080c150072440d04054041d44c003a6061070001486881168180401da091405620302104e1010300500200006150441e061800108905d10760030041e0501c1741c400c075a450032904420342900c00721f8555126440c00a980441c003042455040d90041c20960f0041408520780741e264030b0304400156003a40510307080c0c0d0000070200140902603041c0c80d08003029140042d958100010307010441362040c042c0002041050321014040e41e076400341010b000e40d01c5420380300500700e10032800c1d00380502e510482150303000b880 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 230598039 1250 230596789 230596841
    0xf14070b0f160203010e0109030f180b0f09120109060203010303120209030604020906060d050c07120207080a02130e1608070602010c1b061e23070c0308060310020c01 73
    0x1005540d415040d40441c0e60824407400420401c40710b00352002d81e015542d0350502040b072542806400040da0081d11030380c6030046c41e10802454a16851030500f04151840f009210403032144044450803c04030015940758058080020146450701c1d0182041d98a040c0c105d00c01c0044980196040303030302035100c0d42000a1100a02c400b644940b101c0103501d5044400094011314041d070080d0f4000c0c80181009091542032820f40c81192000e9404440715500850000100300c9480c0c80c0080c044101e20240180341d10f8202d4482d40c0c0d007902d0390002d118461071624074a15244592000035152141c10844409406008101d03125004902a07548140500d48000c55031600501444c1c12070b80d210ba413601a03410160108035285202000200e42942c4c86400328200b81903032601d82140300d01c0b4007000040c4030100c109401038421a115055011103c09410401c1c030341d0300301c03d405071a0f6405041c0721603690749440000342042d00102c1301410040c80441e0a110348141540402d0f014125240c3c288400380200c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 230599289 1250 230598039 230598059
    0xd020601140409030f0f23180604030209070f1806050a0e040612060b0d081209010e06100510020c1017010803040b04032402030f06090f060a0b160f1407 67
    0x354030103000319001d170544058403031040c01001040c1700320b8a810344040800c54203000c1d4203804014060016203011030300a508503c018000f041c4d000041b10110714081c07566001c150507807801007140e014800c0440f5031541c41c03401407101a004043c0204826405505c07400c002d881904007804420000300440c040d9003c5090a115407820744801200c43c101d07032000b56481c18003a11000f0403441e009124451190001050900688003849519040d5a0f50740f820716035481c210344501d002c1140c41c0e07001005000d5459089042030080e10015030f591b9003a0b10440c48264a0480d80c400096001114241e0322184654030054042207200b1f624082d24160340d0310300b0010781da80103e02684d00b01c0321041100300002002007441d03c641846030881c054102403e1607100303040740c204880c11003a83c1c1000080007038601d8008165544800f50b1038480405041c4000490107518940c00b60301c06140c80042e1201c0b24001c0001540c0403113600080155216032145055592810500a140c0c4144a02c10000c210400340d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 230600539 1250 230599289 230599301
    0x2040303080906073204050604090506120303010f0e041b0305030d0c1d040b010c0b0109020d0c0804111c021207030506010602030f0a0c0609140c0f04020901051603020c030d0206011404 81
    0x1c0c00c4441050000511010900c2491106031017000108110004007900c580028000901c03071440005060b00d0901e0138048884540742101403280c10400041c49103106d0006e03070000b941ca070345000050035542c6250044210140002c6140e007090340e41d20000400c0000402004511209003050088071100002982e62846c0015010380e010325011200303c460500c0d0b486030300109414584800c1814444c1c45040407120203802aa8100e6000030301c09200d0705445c042c054400ea00c44ca000601e47c541070300da01ca818074400e000c552040070035042e02204280101c201d05019a002070480c848405142c04a0b591501a0f11048070b250103003000000c7c3c01c600106c00d941102c881c600e0340314608041d03510210751405200b41c04aa22030b6903805d42001280c0701c403440c0000c0361080740003041203440b514100100058643c940610541c0100700140f001c3e64000250782e154602c4010308c500380c0541c1c6c6020380c00d025603001d082d50140314225101261950024000341200c0500d4a5111581184020b100c1681e030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 230601789 1250 230600539 230600567
    0x1803030b120c100c0803181203130311010608011a030d0c152703020c01030e0303060d1e060510060e06071709011103040807030308010906080d0c060e010204030308090607 75
    0xb00e141000075041103100612410700d02d25001420340d0320381d41d6882c070070740040c3c8a111841561505041c89190200601c4007000c2d40c10001034103503c0d1429011403003680e802e10003810840c0c0032041e45010f603001d40007030740036100400081c011807642400700920846581489d81c481e01c80c5002500c0741d18010005030034842d0304080c0c40b40c940b21000395a0340281810001070307508039021685401031074200213801002c2c10300c25805000040e8907100010140c8111021903101600104107202c1c059a80c00a4109603075803062070350200c0b00302078014000000144402400240c10002000009d941c24410307607080c1d0303c0c2a00c400e803804003d41c0610034070340500702d002084481c0001506c0020b84503a0003408060700145030014a60401d80039185c11608907610810b10707a03004000500805400448071400341071041000c00c4454030b00307424641d40d0300c003100a600511002e07401045c00e011840e04a031030305000c550000c0d0750b5076a0700d04d801000954101d80b00482c42c0144000b1541c4a4410200996051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 230603039 1250 230601789 230601793
    0x50303270406050f01110a0501060b070506070905011b0303090b0f041505041109151908010e0c03150c130f03020907050c0d030b0102100f0e0106080f0706081005041803030b12 77
    0x9003401521b016580c07000f072503568403d8110315030000384240a06000380c4032054034280c5540480c600680b8000c00541007000788a0204014402664000c0e4965070003081c039488003051440c103040a9000701005032001e82092641410071220598408049020700d100314200d124141601c4440c004450042d40e00801c3d211550804600c113280465005801c41040c82c40303090f0fa00c401c10300103681040311200140700046015401c2209000038030810070903600000203407206a50b1000069210088075914040510f803540208110540c41e8007601c0b440b00c00e82403d8841c1980b10940f084022006110407840303402800001011a485102034034600250032000b0300c207841d080c0100750003500205491904502c42c60b540701e61046845c0c014401d000c10440c000103111100001a00c0c2501c2e00e903008603140b5070000003200d08882c03001822070121900e40c6001320480c0c60700441c2d064520841c0d40850ba100307086c0081d0040d890a0000b4503d01940700c1d4900f001100d014105201c04003810101b521115 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 230604289 1250 230603039 230603059
    0x1b0c0106080708120d1109031504060605101b030e270a06050619020118060218060708030a110403080a120617030d0e030c19140318061305030327040605 67
    0x410807a0440018011601d8006d82452480d5001c0b0b8544520201180c0d1800344001c00d00c0144031440c45040060242659180444603a0380c0d0b0107806007008113264083c407042d41c10707000c061502c20305110035100f500802c00340c078141810306800000104940d940070207141400c0030540790305031489150121100a800341c1d0601086418400340000c2212000040d55282c03d4102943c02034491003c1d1494841c4000580725051082d00e40504540c211000d4094402000300c100410400001e481e8443d549100103d01c011080400c0b10f1940115440200b00035000318070910610f800c0142d81490400456041000b00d984041c25400108030310010740a9400c208030005644035160072035405a8281c1084a140440c5165910718180b900740700a503c402482c60480c08002d90401c652400c54041001141045400004c0c0401204218190303407042c20000744411207143c55080c0030f4002c01c0d00600340e9865000c0c444900c64000c40c03070031201884016540807200c2074034040c821801510740262007090343c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 230605539 1250 230604289 230604307
    0x30a0f1a070e1201060816030605010e1302060a03090503070c080c0a0513020d060b040b04080706021203010909111905042a14042102010f03140705031b0c010608070812 74
    0x482d0f060000d8000103035403521030219160328108031001c000301000e40c1e61040c061560504404881c010b80000350144801804d000302c154003030311103000280c1c045918a80d41c981d66603055004000b03200c030091170750001184400c00c0c440d62130303c907004441001c3e003922003906a01d402c00030182d0340fa00540d580048440e000c0e000d201c501c0d60160442080701c0c0000500561101c41c0c8103600e0b001039018000a050005060203400c2c414011080101128001003140442c4400f09000310f0105002d0100401c1d9640c00c8401403042c18401c10311960000303000d2030520710000c0d480c00168800c0c0e00980740240e08190140c2505002d181d030441c0000ca07160500300360541490130448002104040680c0e90400c02c0c00003160704900070240c2001c1c850341041c41844070b406880050813a640e01000300381410b11700030304464a9000300c460755a0114240c07030f100b503603070742c442c0d84010101e02c11004a25501c070340070071603066044056100c0d0702034510042c11100150354500d1103941e540c21140e000070031402c0038030003501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 230606789 1250 230605539 230605549
    0xe0d08030709050901080109020a0b030f04080a030906020c100506010c0309090b030c03031801080c0c06041101030e0a0c03050c030601061e020703150b1809071202030c030a0f1a070e 80
    0x1d04200c862915451065484001030420f203400e0b00522403a035520340002c002c6140000d00400180041455603082d4984101e4801c0704050060015241c0d140015100c09030034443e91040705002da0005c001c41d06c40d00c2a098003541e81400c890f800d40725514000204010b903000350007403002c4603815503035150007904001c0c1300405080d1100c1b82e02d82520030344034649101d070b5081c070280003810410248202802c030040001802c141c0080c000143c5104200805000140007084842c2c1c0f094001610103405201c04004030700800c00380d130008155018411051080050103069201143d00500884000c0800801015203401080c4901c202280302040307145070308001608011903c3e030290061b40c603896980e40711440141b00301c01800718410740d521030008007468882218401b210341d4001078000d5117004022140e84501c2400341a07100031189911104542e0304020524a020b0094241c4003150030a00e0102010081504c0032610b0710000d04414104000f10140d040c03050100d6943d0b40d01010303404c0700b402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 230608039 1250 230606789 230606791
    0xd110405130e1e0303150405160302030721061d0610080c0702090406060513090b2202030703050309090a091a04030c050d0207081005041203020c15010e06040c0e0d0803 74
    0x72414003070707241d00301d6400f641410040a0303124400c018598070324109400c40150007401d482e50744031b02c0c944030511102204401c0211030301800c50800580c0c0b501c07a1071080d034000c882c00c80064940075a41c0d009150f00555034102c5022a944580d0040310001c40740c58111000d4421207100760024690a400c0d80d009114010a58005110411032482c0c03143c0d54000c507140b035038101e0b0151807441e02e03041d0800090404036030901e21860200c40800a4442c01d80d905844084041d145000881425a04200c0812850010000700d540281142d0010b0b0b901c0c81c0981d100e4016100c0395111300107000001e034528042c1e00070541c3c2e15a102c502c103c5440f460102c0c070522010080c0c41a020400c50420800014204010403021041c4a40082c0302081c50322100500d05520b000d1100203a9044c2010f010004400d80319030b201140c058207004d030b22011590b076194580140e0000301c1e240f014040e4000100f059900c070455000c0d04095509000560381d000043e1042d6841d5489960050103018016022900c2a4051 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 230609289 1250 230608039 230608061
    0x3309051e190f020909070804020102120c01020c070906090507080906010b0307110a03031509020406050301141518041b051e09120f010e120a0e06040902030c0d11040513 74
    0x5440355440303840740344111890121040d00003a80010343c0c4106281c01a5050790140c4c092918030054940360740000d4a800091081a46804012800c0350071070400f034060380e81d20341d1404112041c9a55034014007000d000580b0444600a140a0100302054800e405003813007000305c5002006941d1030000100b105500060500e400c0114001c2204080042440000191802a54040340222b0413101071050610300f58000b0100c2d0348100810042c40c2c0d008416241180c51811440c201e6001c080702080884800d4107048505160001c0c101810141002c6810140c81040e40c0800c07011415010500407900c05100420100318244425260010b0208583c200b0701e5070218554100011203000c1041e00c1324540c0340c4c0c0001d4100040c070000c804024803c0c0b80c400c03103009000300980e1480c0740c0c00802d0fa1242c0e403050390401000760800301003603c41004480c020440d8440031503903484e105400200b203030455455060301604184400410744180f0041d0380640c1d00c028030344111100c030606001c1c01440c0d04150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 230610539 1250 230609289 230609311
    0x406151812052d2104030f1208070201020a050f07030c0c061112040e040209041a0f04020f01021605040b0d06050403050a23030a0f3309051e 62
    0x228401c0d00c907009038030440e071191000b000d80c1c0c0c4080d0f081c18202c142c4801910042608204011590000060904690044410800a0846101c00103081c1e0300c02e58001a141d03500c1c02d400b00040048054a8051107002541ca401164540c00c1e000c0b803e07403141da00421300051007800b41c0c00c1c4c056841c60061506512030b080044428181d81c0d20321129240315440500820141c006040080f5420b10103c03110300c0800501526007410500b68085100300540068010b0202d00002020041c071110101400c01c1c0308100c424080c5403119440e01030700e40c116001c9000d144c0204440545500000703440941556001540201e1030518042c40000c01d01e40d0300040c5e025000d200301101240302c500c181f0713000d13500aa8505503150030240000d844c1e0400103c0c541c1120300401b401141ca6015401070b280c00102040d4045090607428291034043d100741d0460030b040c0300005c0054400c407002e85c1803452410302e400f0ba1440c0b1141c0c0da2030740d60044980888030b0f00b107691000d01c07000b010003c41e031280542c45108a05 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 230611789 1250 230610539 230610587
    0x31e120906040902030619080705150403020a092c0a0c06030903120f1d010603021f0207030602130522060603020f0f0904141311090106020a2d20040615 67
    0x10001d80a141664402304090700895014421400c0003201c0c00300c6000707180801c510b05440c690200b400d8801a20a0340345a075a100407541e0000ca46081c105e07070704a50749141c0d104c100c54910200b0748400000f20201d45000d662400054010f000340907a103051900351321200646150600c001000d8059907c400644a40d100c2601800580501c101034003010b4038400052014114418000c0ca04207583d10f80c1d040725949184595103e0f4001802010303268080704c0581c50791400000c0303580328606c5e50030260b4807141281e1280301140d60586180018103d07003205120b001d0703854409030201d1055540c54000d0a50070440a24400d1400d402002c4a00000d071002400c00020764400c0d4107980141c481009152403501c0340002e00c20300c1003107000d506100b20f4800c00d06514001c0041d58684184070300034a00c00211011001d14001c41702d2030415101c0380c4048415000c054031f0404000002e510364081c4401090808018500742807080d1000c0e508040070546c040c0341d41c49000d4441c041c803076454401600c5082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 230613039 1250 230611789 230611819
    0x2607080912041421030403110f04050a051f051005131d04061406010806011b0b0115081003020d080c070b0d0b120a08090f010e031e1209060409020306 66
    0x14000b0700040c00100641001282c85030104002ea44d0352800d0044a004104100216150080b0459040340d9100c0e0070503440f400058007183c8001281c003902e640c0a4901820032100740080d400549c4201c0030b044441003c000d40c584038842c60009401142d4200750543e8200c0d07051800f5100802456200705c40c40440140e40d4034030310007080b9100214402c1c50342d45000f40300c10412103020390050030480182c96001740c6481c000080c840200180100d0410412400190042000c46010b8218641046a40c1495a1290a040080c0724104401000a0824400500d00c003900d00d100c6816650700910310400c00005896910450708801c100741d06501400d000042d001c50104000c109554007404d003c11803d500000b0046681200504004075400c02c02c1201c002415510460b04c04080c1142c10705000490000100d0b210005120042c0e098810a0380413619202e650202c80310702c03c0e07182c04841c0c200c1e40010407078200e0b000c2c2415103034211100388000d00080620390061980880f02034070907101c3c0d810030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 230614289 1250 230613039 230613073
    0x9020f1603020106031b060e10031503080301060e0d08030403030b06040807080d0306060206060a05040e0f03031f270b04110a0801060906021b040504030302131526070809 75
    0xd03801200940e54a50f02001000505120155680c01c803100046c0d6862601d80c0c042c000d82c00315610340e84500380c071042102d0114000d41c040b0030b20a5210300315a80c119201d1030b020030254401e00440d80440e6512400242c5803400100c59000306900001da542140c2326542c0903000382c0145440700c1d6102e1002c0c0004201d00c041008000020884600203103061350450700050216003c40d00301d541190003039010405170352160070390780302228000d0310006158150310b510303039040202d1741902e175085000001c1444440d4405e81502145010004148410160760717070400707200e0000e5450422403c481840e051080e41c0c0050340005002880500040391468a80305034050640c0401606000b2452100043c09034950002841001d418640014001d1100c4404003118003000001d00b54429034642002034201071080e0142c69000700d900500340d406540b940c104603411000c001484000862200380c00300400c81120b0f407030b00c00d11480c10804a0503114030404851401c40200f942c0514420300031015519121 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 230615539 1250 230614289 230614327
    0x50304092d02070b0a020301080604020d0213020a0c150b031e0307140607111b060304060605060a0c0b070309031418090703151a0406110109150b0913050709020f 71
    0x3100c1c00040c0d843d402441c008142d0b06021300b2881c0b0542c03040c030043c402c83c080060086d410179011908140c548055100150310408012509070940b030004c90814025034102c4503044050384503412030700d504200c021072042181d081c4032082d07601d0380c0310325003180c0c40001c4050860300350784074042a03034500310700e9884064400400902e0709101d513005108000344e03da0b01c4042500d50046071f0024000d11707000580c0442c811650010240c3c42031000001241c100034555200c1e00080c080505155110024a40040c00c00104c400b0159102105400001e4a1512901c500c00300e06605840340b840c4c1d81c20f444200803003a000030213400c10802040160704500d41c0d800c2100c512407021503030013140c0864030101c00010b4409552200701c0d820808072001804030700013400d40d016030b403140c9001405107105c08445800750017451006000070700801a2041103c0340c1d90014240d803c8161140304583d280e0344000c40d0490003416016100780c201020034000812182c008111503010b20b043d69042a1240c0b01c5030503c010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 230616789 1250 230615539 230615621
    0x30403120806040e25120302070501120b03030703051b011e0f06080d082a0712050711040b0103021201080303040c051c0609080d02070b0106020609070305030409 71
    0xa4a600c1444919500044542d800788090382c0030300c080701e00d5540950f600d0860701945150207220380b00c50403080e0b1a240c0c03801c008286940130000c28190600b4065151403150260f00d000a1101550390904119800303404420000a0001c0d8540071042c0c6081368590000800e00005a91107140c40350500c500740503242042c0301d41c0042d0b1102c03d005052020843d80340e0341d5005009030603c00b0400c468040030607519001039a034240480c1540d510f40c0c03008070442e42540b200c20840403070340305514040d60540140c001c082c03103960060000d1814280c02da5542c00b445200a0a1541b00030200f42281020303000b02d00e000e80e06040140c2003280c10901202140c0007600113901e25400402000180702c8c0307040c500c40003003c051b02c1800359040801192801417510311006000c0c6629407200c00c0c1003002c14030442d0750701600c40f18115180c1200d450503100200c0203220b072100520a510205030742d5000071807039800310703980303d00154a020700e03140941c806899154001e4100145103034a9200892a00d010017409031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 230618039 1250 230616789 230616803
    0xc07020406092406020a0203060406090212030d020d06051225210203060703020307050f03071b1208010e1311031c090608070c0b070809010b040c18090e03160302030408030403 77
    0x403003d00c034091000c0240e00100456011880440241e100850696007103a00400085100041400070412118034a00c82503c1c500c0001800a020303001507005d002d880a1408040c480582c1e61010441074907414018802a5080402c01807018080019141c6510b402040e100ba560f40c3d0704d00220806407444403822aa881c0c803c80d0b85c0301149018081141c1c010141d0030118214141b205000340345005100c20341c02590400000300301c030f042c010700c1452044c03181070003641c071003035002c1c94207000c040108040c41700842d04e48000841c2c50004607040b54403454400034140d01003000c075190114508503003002c0325010b00801070444883c1d88018440310410101d6110b03240c035586030070002080004010410303001c0100c121480c600042244a600e07400440b40d00e010042d64403211089070040100c0c00d4590340c0b05161440701941680c02c40c04050b1240500000308a102d0b07a2440000309a8002910480403a0420041052400010030301e030b071103080c003a10450741880d03214802c41303207142c1c01a08243c81310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 230619289 1250 230618039 230618081
    0x91205040609080d0503070f05121005030d02060f0c092403010f06020f0d030b012607090e090303040f0320030d060b180402090d08040e09010e06010e0c0702040609 72
    0x20350b410603030301c500800035040101070900604500034020b00015107440304014201511001c20303441102507075201d200f00d040158680c140f1181c0700000203c6031285a000380a05140c03c07240c9400494180c2c411030b0480c4100c0751070f50316510305c0000d42d0b110074901c95000310081e0201c1c42d4804d0386c17101c0d0300c0888020380c1003d40d01c2d4100241c1e080c080d1410390040b000c45d40040418200c5441c003084030844119141404214007100c100140c0c0c01c26500080702d0100d441552013114000d00c6101102c0c0100707429220300703c039030751141005210100111001700e900e07801040880d0006403109141111203020f460121101c0c00e0b800918641400004000305070756101080f02c04085c907180c03040d000145500760007189007111040d501c0403141c40c1c0d0b56003580700755804600e40c13005403030b14285000059882603d00e640c079900c0d503000c048010f4003039412400075072030304180c420710280c0061218166503251024286c1ea54580c0c0200300c45034000001203801c00d4030342800140300000ca00608001c0e236642c014274140c0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 230620539 1250 230619289 230619299
    0x1e0e010c030617030904020703170406091202010b011d060f03041209050607150b0613030b040b0f01030213050705090a120209060102060114040207050102070c03031205090303100e0a09120504 84
    0x180c4425810000c5001c2e60f0b1a14403500d008008201c2e24004001c2e20096103d80c500d08041d2542d000701d8044840a8914204200812419610000240b841340d00040f41d130030306184040303080f41c40602c0c2d03060120700d02e1341c61141104040f9a0002d41d481004285078500100b40001c52825001507030b003210300b91550b0210741101c0c3d4001074883c01500058981700c1c18441d0365204c046000080c015503540c0c072a80c44441140319203030141100c01044076160341072005680c0e490b0106c0c4145084409682804644011400c030f911500f0002d41203d8008011061820210511200402003c0c00d8842809400c000131061511201c10401c000c0c22200d03880e0004031054014009040030041045045400c2903006100c8040c411400742c1e5840400ea07001600c4103598a0000c1c02032117114400303000d4503006400001010361042464105006022042c005038843c0e105c00781e1b0b20f000c1681d0b07a080b29001000180140110302c0c811583c411400f000200b51514262180500e2800301201e00300082c80000381400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 230621789 1250 230620539 230620541
    0x90c150904060e0a0e030901080412091517010e07170c0d0911010f020c0102072615010f090902030a030305040813090501090b030601030b180a05060a0518010b03101e0e010c03 77
    0x501800000145147c002e222000825811b4001c000400c44680e402c3c030041c4951191001c00050014000306800c0c0da00d0058000d0481e00103074038000d42d41090a030006c81c02c1c80141c200c5a00481e465216061030762161007440f03449000080000d03000c81d000344008824401c181c02142d0700035014040501c03000d1084400104a00c180302c1c0900d081d03603c1680c2072520b41e40d000074000c088812418610781100f110f9004002c4041100c2110010791203050013003440c8030b1441030818100e0b040c0d0341220035410303503414200040da001110b010b94540c1200e51288042402500403d900c0307440380b07084130314001c42171804012081150f04070b544100d503994010b00c03d0900f01d118851105a045004020135859136440482e410001050603560000c45590305850800803c07688030701d140c0c840c0a0f144a450b02040201c024903044601c00780f011184104008507500c180300f901148030b0054050084148107082c000081c1094910881044200e0112688020842e104040d070101d984000440c202c07000b450300034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 230623039 1250 230621789 230621801
    0x70807140d200315040c110313092a050a05071407031205040806060d1b03240228050c0123090106081b030a060e060a050f090c150904060e0a 62
    0x1919807034082080c0160482c13001301288401030b0850300814a190500011181c41000c4040e442a42c440441c0c19400000030703641c42001ea40300c2403c2008400d40b0030000604044040c0f007420509001c0c1c0407868042881000201414101828803d02c2c01c5801c1d51052260b4002803a0a10a500020014810409207107500780401d603080c50400c2c107160820704039a4640f0700180c2000d10a421140d059020450341e0b00d1003049110344200c440a01c259a410718410081300501100f8a40791a048036186503000341c400c3c0c0c1c0701b214a480c400440020145441020700e00444801d03824000e051100701c802c003100b4060303040c1e0000300961660510302ca4a4402000030b80180ca0040300da410210140700700c030310025260380c54940500008010040d03100101c1d003801e49031403016041d907003041c00b502070038000012000d00405100008000541d2409100070300e43c036060350008000d4020001080451a002042003d0600c15143c3c15142c5820f40000400703d40040d4042200900d59608000c0180c4880c4203c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 230624289 1250 230623039 230623091
    0x80408150a0507050901030b0301060914010e07050f0409051806010603020a020c04180803040c05030601060906020c01030c0f0c0218070918051003030c05010b10020132070807140d 79
    0x1c0c0030303e0400810140150148600ba40c1c10140e540700c40003500e54003504890024080b2510402c02c4801901c00886490000d020307800c560305041002c00d2007a40304900f154403001034030b0682d504080c14000a6006400302800b814001c40d10480489009802804114000c100e1502c0050788d5034514070001e070604981e01081c40c4103600c1d00c2012503503500054016549207034031010071580d0b0768072454024001e0003541c0151781c06205050000c00c1070303500f103184403040e81e03038a800b243d20054081c0011416203030b5501240b40007803c20f0001000040c0188804008184010500c00844507001c2513031050880c111000000165005005c20110150160010310038035106400c0c481880d0402c14200c0294941c4002800c216aa20031070041c420298013800107440c0045c241c0c0d00340075010000034042c00c560740c01c1345403036400000940e0003988120302c0380d100b841c641180404c00d640c58003002d032a40e01d00200504140603d03064151000b4100c000140000c030017224001401e0082c1501c043c820307404445034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 230625539 1250 230624289 230624291
    0x1e0c01050f0301030b070210020708130e1005090703090602220e01081b0a05030102030a1a060a1413080d050409050a0b030606040c02120f1b0c0915010c080408150a 72
    0x2151800700510200c0381036030b401c54404a0903440741c8404a10380340c80c0000e0112068408200ca008000e50280149442188506010000b40d1503c20f0a02c1d0410140d460f41d00b4800150380c100300504002038801d502c01e60b5414002400100c3e0745a59041c2d0344041c2d05035030491046180e03030004410082808003e0322511803605995030410700344c156100ba5072044178051900c0004001c0d046c1e0386444111b13016041c0a4029516802c10441c0701e005084412000d21510340e01240ea0420384c203158040c2c40307203048140c4e83c0350f0301d1000d40000e8092562149040e186003084001022418120401c00700c10301516035991300740d94a151120180407103001410001000b41000d4883c8290b603030002d070407030b0070000883e0009202d10f020901640b418418456410301d0282c003090100d100035814014008841002c2010107480004000d00b64440323128811b120350001d18580801c0d90294106034907030280784181803040558000f40c42e00c2885412950080a4a41c0000c0c8400c40504d901400c10b5000500240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 230626789 1250 230625539 230625547
    0x702060624070210050309010b06250f020301060b030906070216140d0c0f05031005040506010b030a0906020316030c09031101030e03120108070302031b0d1e02031e0c0105 75
    0x400103107040d0103446103040701c6461140100c00a40e000c0100c071056030b0300403c008012007803220003500d69001100c0c8000306528000024019041c80000c80e100c400c804501500c0c038808070b580302d002000642c41e0a40c1c0780c14040e0080001030720309104100142c0303424032555490f40f60a400c014680800140201c0454000303400c1110b001f01155420420385451580c0940c4100b814008500814070741040981034848071480041c23031000300380e40300c01910010b40a5802c0b002d011310051003615403c0e24000c00940c00174004012944048001e59000610107001007500c3e082a140c0100381d070001e644045040d8a141c1000201c1601807180700307500c028a003014480d01c3e20750b84400a1082100c80c8250605860b0407100c00c1088080c07044600780040447d00c00001e584071898550f8030303e04c0d03000490083c81241e0703015101c5001e012a10048090081103000074034170555a400148009004030030303525000c500c090700145e40034003001040c0c940c1849a18003000c01c001c5001d2500c0c8030529414103000c0c01700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 230628039 1250 230626789 230626801
    0x30c0306140709080601060f11100e0f06040b150d060f060e150d02060c03220e0c0408030403030c0602120f1005040b1f14030a02030411010e06070308060a0f120209070206 75
    0x5c02d0244c111340150038140c040e005070403400d8655882c02200c0040b07034029202d00c403802c1d10007580000e00c14078840040b141002420030050fa500c06041d90050071042400c4006400e01c811000441c80100c40034002c100f020055507a4903050311800c41050070f26517283c00c000d00000c0b400c813400941c006c950540d041e4001e542e03440402d0219080c110040e002d40400682003074a108100120360580401004540314408040170f50b0030750489030300600c0d001359803020102d030340d40d81c025082e50240e492110196141c60724513a01902e18608031482121101c0e024081070301180600300101d0711800c0804010581841e0641481d032500881d40c20042c400c03442c2035031210b569198000020490720000051032140c003040e50060301c94070605804d40514007000000c00540da50690061402607105242d05524035000f140150343c0b14207400703203198200c0b00900c810b1011038070481465801c1500901a030100c15260542c1001d810519001000c0f8001d0080240045080200c0402d5000c1c0c40c910207007034a8203082d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 230629289 1250 230628039 230628043
    0x10503040b06120f1f02032e0306060905060102070b04080d0507020f09010605070b060901030f062a0f0212030c0405060a0e090708040605090c0619020304030c030614070908 76
    0x1900c064040200795001a0b642c2c1c6825402084024140c01282c0400704800102c51380e541303404c0100b101c10201240c242880e08054002d480c0210896034008800d18504948100018803080030a441c00d104654000003040a600c100ca01512183c000405d451501d440060720706000c50384158182401040708014100300801c000080e0031140c03400c0b941e0340700366000141048944404842d40301841e4000010b903960024000c040d118821f0500c002e0540e9040c0802c094408240300241544d880b8201803c001a040e500803548000f0302c200e000600842407a10503d401109000a000b00d51407076003101d481038040110164012044408525614001d800e03540030340036a00c1510300402e0701254000881e40136185031142c0c1ca10241403600303540742840008100200c01d450a0301c3c02480c210200750300f01004683c19990b504040c1c6036918103040081c800400421180d141411800280b1003c8001000740c0b4040004600520b004104501070401140741c07d08098158000d2100340d000c100010000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 230630539 1250 230629289 230629291
    0x70b010e060d05030a05070501060503010e03030402150c0d08060301090507060806190506040302010f0c05160f1d0408161401020d0e0607091e0504020d0501060e0607150c09031a0108100902010503 86
    0x51078a5a1145624030341035024000ac1e420440d0f055003070a480c426804000005540301c2c0f8000c84544411100512240c91580f02c0d80c0322030a00d0f074102001c4492454014013225801c44030190000481140c0358540501b0040716410410000c2d90403402e1008501c1e101d10381840899a09400110381480c14000803d1031107a44002414404245e0990307100902541e09082243d410006480c0b9800d11600c209091220900580e0b10340a5030140c040303010702c1b000d0f100c038110700d0401000501645464988032465001104070102039090349020000180700f0112515480c40701d100007680b41d0485500800559401d003403135010550101d01001700442d44003100da0201c40e402a5002c0041030784000c40814680e154101d55001400080c4407507420b01140e0269049030080d946002d0000b40c5102000302a12401030f02030034010200b10403440b424000c0d401a0548520b905107078411036581d5442c039500e002c1020865000c0c25020340100803102050296150340c0c961a0000c0145400c1c2d0b500181181c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 230631789 1250 230630539 230630557
    0x6080f060301091401060609090603050c0d0501020904022704050f010303080703020d11070606081f02030c040e0405031803030301050a1707081605040b0f061c11070b010e060d0503 79
    0x6211004109251820341c80401c890703801c5211309003080c1c100600540604800d102d104c0000c1c00545000411b07000c070703110301010f6a41c89005042003c4004041212461220500b5500b5550030442a40d103942c0d1840140034484d040b001c1e0030240300c0300480e010510810306050b81d00890503c0100202803c8071044641501d90505010800d5114807004400a00a000146000034030f8689031480100382400a4500f85104840510216407640308964441c1880c03ea58030b0b00c02c5403108040f00d80d00881d00a194007031000d60080d81820b95541080d40458130a80d0161282c1d04002541440c103441e09044041140c810f03070086240d5450940810905c102d58800d800d01055011a100c841c0384040c4890802421300800300d0310b03400c01c0e04c0c400720459003091080c01d02c07452a104403160103040200000b56030020040032241480300e502c0c2e0110b01c04280c0c10b20240e43c9a614040f0b024002290307806020401e0007640342e1800396040440ca170f9104100034000c140715500342d000ea04000f600000440b10940 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 230633039 1250 230631789 230631811
    0xf0306050d0b0106080903120c0702101713050c0904030302030108210306040b030f0607080711160e040c090509061009021204110a030f21140d150806070f030c090608 73
    0x80c0eaa21b006c941940500c0c1c048440500480c01480040411400a82002070080320440c2480905200544540403080480061519108001040b20070711f2010f00c04503c1c0030b40c06903000c440e0b4010008606070350860302100400c3d804401805040310170402002d40d5061100c1403c0c40d0b00404076040d2040c000184021320484d2641581c02c02510203105414402c80c082d03046483c40d04010034050401c1c80100c0340700340002d016030b00d1030320b45000006018001e40c030203862a2400307d0511601c04038141e0024002d81d100c44550000040d40c801d14441c0c0c030711038407441020380b42908000210f00d68502040e800b5842050046c405119041111410b49400541c4030004021102c84240800c620701190741c4050a02001544544288070880541d43d40c0c22041e04035034241d0108441d400e84190b50701224a400440003407140320344109141d404107002c5041e5280c0340030842d40d1200110728000b0110364103c0020741c0940c110700003d07018002c05051005508201c591181003420040c1407035401095000f00d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 230634289 1250 230633039 230633041
    0x18140f03043c050f120a030f0e030c18070203040b0304060609060609030b0f06040e03071b0e071205060d12030207060b06041d06120105090d1b1509051c0f0306050d0b010608 76
    0x1d551511400c9174145a010180e03a403061040c20f01030030944220a0700e002003041142240d00514000c11046004400103203e42c44813005c803542c0c800347d458002c0001055100030807012409400c51005036100b03500c240004611541850007030402d940c03803035100005110f40742406000140c0942c01301035000310001c055400d1a51600002000f070040560507a9950000040e004240000404500c441026a4030042c0c22555505160141840e00300d8840000502480700031039030361082d8001c40d41101004040e000005034648904042d1000c0d07101c81c201095001a8440400265000e0340e00d0991007203900700c2c102440e00c0010125004910400343c690f0480d1300000301c140da01e0f0000030341c200c0f034918001c0205280c000f10803039680c5c2c82204240c0128448800200301c4081c0b10030710880c4560700c0940752040c0c07203003030f9003040241c010080225000e000d242c8034a10b050140d4031500310b5a2080d0303a6410340c1d5040d420006822240c42b07401050041404005100c0030404210306075044500500e801519 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 230635539 1250 230634289 230634319
    0xf010b060406210617060f0105060a080a1e06060e030105010f05040f021c09030908010509031204020303070b07050306010f020109020d0201080403051308070302010e030118140f03043c05 82
    0x41840382c407403c00c1561801e0f8000c43e207114105a03080500c000c5800703e030b6241e2601040c8170010f034004d104081d03005a0070003581c0e0203130b071094101c00e400502e0407101003100302c00b0038203018070042160008945035030703103000401903a42c0c000e03145c50b80c4041c00e400800c00c03941840d029000c2c5040034000c1d40d0003240c4803007242640c16500c0c3d04848000410b212a68407040c802286070000c0c29101c0400e0300041e10380803021900d020184690350003010850011842d0286e40094215a40320080c800e9a01d408103102042c00f265050020034821085584d0380e07a9070380707061800074140040300000c00045a140ca02448010f0300d607030922001e040d809082c10320b400c1e903582c602200c151041400980585410020000b04c00d207001900c8010760b03100342c80e0202c540807444180360880c0d0014141041040d5013a1201c80844ca5004016031f0700c81c05a8181c80f0080c485810252450b4083d40c0300100402d8210a0042c1600d00401990fa081c803140f90004000c0c1c0440160745032003451401028441e1210880c010340c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 230636789 1250 230635539 230635577
    0x30522081305120c091e0115031404030e090127050c0702060c031905070f0224130e090a05060c090a030c0e061206100306020d0b090c040303020f010b060406 69
    0x900000309500f001c04403945440703480700018001c6a003c1c0e0340d00004902001c4940d0469061101c5007080744220760300e03200c0268182c150509440d0181651f8402c0c1c01c00302a0114012403003240640c40700b01c0d94660400c18485144016841100140b003070041030007141c2520581480c0581c6c040d5070204540c2c07100354032481f06104101d0300070b61000b4000b03145c000c004008000f80c100c085441201a5a400e2003010550340c42c031403804020110a001034042c801890718550301c01d103a00c0040074241010040001c0320740039501003d0141c500c0c2e0321055080101d90a0342080b00d900c108500c02510300a64070750342c0c02e955104040c002d80016a0301140e600316517150000071a00a6800c00140c105881d690481c0449900040e2030403405001c0030070209090540002c3c3c00c0740507540d00400500c00a10715202e0302c009412194a2150907600d41903020000c3e5122134119009440d00e450560b0b40364039501c0c002c0d1400e0456116405543d0504008502d00d079030f440292011900d03181443c500403095005060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 230638039 1250 230636789 230636827
    0x3120a020709050108030319020d0b060301090b030c06090109060c110d06291507230606090a14040f05031c15060302070507050409140a0b060103052208 67
    0x1001500498a01102540051980210b5403a0541002240d8860b41082d849110480e00400c0000c40104000110b203110382c0100f4505100c508000380200c0c0032400515198002c1e4001c0e0318031603c482c0001c01614050000031055982104c000340340099110029110400e288034000030702030901a1007040c002c800c1101d44281c24004d1059078080650f251001c010000048005141d1503000380c01c048070310401d2400803042c0c00040039102c0d6076400c540503042c541d0145130202c40410b2000c3c4071000740390b60007a0000c0a118081c014015502d045020702c002540001d03e91948942411a03009150094014194200da00003062200d29210390801703c0c9184030300203140d240e00800102010b8450900e9000c03401c91507070209011700072580c80408405902031040058015000398108128525041c0d00c01c03142a480340d44629422045800c1450030048041d0041e50340807c450104100c969051242e240e00500460703400801c81c0524074802081480c1b050010400000040c804038a104200105 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 230639289 1250 230638039 230638063
    0x2010c0b040605040c06020309090a020c070b1204050d0c08030a020306010c020612010e06181501021c020a1b060e01200123010f08121c0507030e0f010e030a050903 72
    0x2241090500c2c0c60100010001202c060754902000030011030480d1003c41150003600c0e00a003444865280ca20085000f5807116208000301d2007080c100107001d002460140c00e03940b0301c0c032000013410300c2d1074104241030280403d5903508000c00f1217500f0000031140819260051070900d40182c40b44e803900c005945028841102950000c804207002240c402d481c3d03107060581c0d0030200300700c1080d1141c1c41884956110740030103444a00d03100c0000350400c00301d194503445a070814412111350b40c4e803802e08424280202200500107030803601031a02032112207010030345a883c031454007540c50f43c03034448020002e90303800141034100004441a82d0300446031508100d03094094000800030b07802c00c0501860300c41128440e0f948440f1448000003440c0407654614012605158080c1004084101c48030700ca940c40b11000d110003e141031080c2e0054115441111701c58455078070009141442c044149240401060008006038148280300140000c04015030780c0344035507428250703110f1000c0000030b4104070142c0a6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 230640539 1250 230639289 230639303
    0x309100207051e0f0d02010b010f0804080403020d0c0602060709060e040203100b0f070308160212030907030618061a0616061107030305070f0c05032704060306020a020d1d0d02010c 79
    0x808803e443d030103c0c4160301542c3c88021100a50390004c401c2e800e81c1c5404000d0780c0410301400100320524020507840754050301c21182e840c601601d950010b20030000240302030b40c070388042c10001e21119404200094102c4101c0c10081036071442e081e002071141c02e640b14054001c54001c00850049161f8800e80c00280c18024421a190135182d80c010f20650414081a000502c0990105081c0c81801190f103079880000d5024100f910548181c9543c00c1e03101074514070342440b400000201281d03842c42a100690354110481c07890303d11a040102c2910612203080016403400c813403100065640e4400c4030ba9417841503c40264070405030a049004010100714880c40e1a000520141016032541c0154400d0015466010b1000c6107628120303a00c0200300e0b03004013503600030003106040c0d0391102c0c1081c19429070300200035002051000420151140fa034400c03105c081d004140d07241d40c0340c1c0503c404c3c81c0c07501052410300724241c8010095007102c0780f0300d00500d000f42c10400501e0250f900c590228201030b40c11800d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 230641789 1250 230640539 230640583
    0xa1409030d0201020903010f020c0a03260901230f0114030f0a0c17060907030b060f0409050c15090307050607080915040305010f0b06030a1a0a0b04090b06030910020705 74
    0x40c1c0603003c0e5110144241c465443d081c218005d060b064402e95140e640c0000051800d688169400e6420608002204c64044944201a24011455800648103404a80001c02c0e402c40c01d441c0920542c014000442d88401d86400304440e00301940700c803030304407003e20008030142e000150101e0304041010804a01500a07152900d00788000f00d90305504a8100c1d07650840c4640c0020052a22510282d92010064000c0c400c00c20208001d4403c4980107a4014600c0301c5443c02d040002701284c4181c4400c42d886c0d0003001d059070503803078500c1c4480c8080c284e560340c851410003404000b03515072800707004041c03299101003407810038424004103840000700081e14140010b0b030140007202417600180700840da0380d0300f020801d000e6585640030340c1d846640c0207001a4155140c003009031019121202c00080805016100010165601d43c03000e80213010301c050540c1d4607410113001c802640c05c08100c0d00e000b000e003003040c80a145000200200c0c002d91021006843d4011841c0c03803814401d0050801d511244040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 230643039 1250 230641789 230641813
    0x8042310020319090c0311010e100c02120606011704050123090c010203160209092e05090106030f12050c0102030115020c0a05061c021902010e060f010b0a140903 71
    0xd03000b1801103220302e040aa4a2443c1441002540c62420004020b003a0000c400c0000801000d1000c07055241410302d507140a05000204000440d408100000560310170a22025420481200a00c40703c0800c06000c1510b0080d002a00f41201482c4d05001400d11100103000c0c09030a500280d071041071500e2025001d44211400b2030021000d03501c8600c68003a01c1c0480d030a541c000411583c0c2d0240400002c103c0c1c034096001c01459141c001c2c5280118065070605190003102660925079881c15050780c6000c083c00180b81c0e8040300e4008000107130030383c074024090001c02c9403001d13800c40346984800540c0006c524044210340f0b5014468907140703150700100011074050b801138081c0c1070819059088034043e6500303404120202c1020f00c622500044100054003d500700c0c8005502d00031407a140252401920070134070500101e50036408c10041c0d546007181e441500c0d0500070950003c8000c1200364055041c040c182d51103114061a402c00d0059408801001c0c094683c203451440800400f6210040440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 230644289 1250 230643039 230643041
    0xa0507020301091208090a11220f061a070203250312050d050a020901080a110c0303040b01030b012c360d0302070804030609020312070501060509070c020108042310 72
    0x51308001d40800d6802c0f00140010b840042d51151550300420744054034401d9000740a4401c119604030700c0c095111010745001000c041c0200035251109100018000e4a40000c0e172000508401188500318010400c81015035000110002003503000780d84880c842c0c3c070201c0001941e51843c1d000504032064082007152041d00311024103203041184c1c0c0140410381c1d9004103a8120302c02d100005012030182008240c20640c0c0340c1c0b00c020410361418040380350542080d403a6140d07070011030703040310014403000051080004441c8440d005150b101841a50b00310312054140030305030b22420f0950201c10800004030100746ca0034a4002c0d9a10301240c03c4015039107882c840b441e50710f040b20100c0c0b4030700c0344628440c40c0c544248211504650130400c100d05017421503943e840035050540c02664507104980c500d0481060381001000701d1442000002400c62615003032110b500e5008002c0c000b4421a450307a240540d07004902140d0095215551007001103810308503402003c031200c2803450901c1a865400041003213 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 230645539 1250 230644289 230644313
    0x7030506090a0b031b04021b0c0411120c030c040b07050f010e0d140c030c01020417060106030c090b070c171b1f1202091e01030b180106050a050702030109 68
    0x60700d030599190740b035007049000c0e0740600c10125050360040380f4221012280415a40100c1d000030f00151a28441890f0f10403c049208110200c50304402591280741c80c4c6889108000d0911916490400c40221011880f03910020252a04650b00100255034000110f084801400504902c291140350b942400f60b0303a100c01031002003aa601e08040072414000029145c1111030650341c1b49094540c492102005542081681e00300f20700c018080d88001070003e0000d48003424607004403101c01036032200550704c5e0413010382c0828145851b150700c940c01c0680c461140410b4070396005041e1360342c1b501450014404400380c0c0c848010ba0351040d80c0804c410001003403807144514404c4011621400030801c00840b2454041c080d0224041407502072413441c091900c1c2c445c0c9841c0610014204055400411011008011807a01010b41484814060343e00f520813103a04035002e5610108140b2040942c4640c40b07018001c14040c441c010845038117244c0b00703604a548041d070240003484139408524015007c50380b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 230646789 1250 230645539 230645551
    0xe0a05010e0f01150c02011b03020604020a0605180d020609040906021305040b030d180803031303030e01051512030d0f050423030301150c1b06030b060405030c040507090509070305 79
    0x1601c80803400c9903940d4202d580c1a80d20840300da40b00381d000308000340e400e100f030580201c1c14081090140b29031117119203d0900054001d07009411103140c18030400840645540041c0107110090201440841e82c001c030741e040611040c0c0701c00c0104045400028507600034151401d50080c1040325a038200100d07500a80f0f0965100440302d6500b0380c8800403c815600d4003086207400d0b92000780030f50a410302c620b904000d0691082d154121a640740d103036550550713008940310400d582400302041c0c20164144104070100c19498000c01c2170b41000c205d1181c19406410b403241c030421700f040780c05540480034000c50b0404002e0040401c44010301202200c058203081300c043d2100f4914101040140d0340740d5414901491500300034618603807c0103291781c110300e030011445003007008401402001815690203260040344051340400c24901e00f0388018140c031403000410b0300504003448200640d0314005030040c041038040710301066996628004071840354065010700e034000c0460003403104107034141d880f15010302 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 230648039 1250 230646789 230646809
    0x30819051018060b0f0313050a0807150501120f03020309041d0c1801030f11040903030b03010e031c0509033106080c07080705010b3714190e0a0501 65
    0x9945400d81422100140f044c00980d480410004038008114002190f1040000c0403021300ca041a488881c80c00d41840306c00c5a424500250310b4043c00701c0c220a038407d06d150510b003800070350b050800e0900c80d00d0340428000c1c491780401d081c000825000303109503221448003500c00c00151031640e803e9083c4c01d03056030040056018230280310411f420890324a4600410070246601181d00c0c2d80c0ea0b501d03034408102c2d0f06a42c02200c0350740c100980ea88900a0b508411300940c0c010a00e03030480b0080508690340d04c1e100c0320003644104100910b000c1c0001e45010701c4180306034001510351b904015603007544102500c1d0b081001046a142c0d24004041d103290411300201480c1080d01601c50009450011081c3c0e2101d0041c1c40c1400700c240020113180045c0303a010700c5800040303050005040401c2d43c0c00c440c1c03603180e10107c3c004c21542c0222010802109000382034540e02e4a030a0380b40c41482005d1041c18442c0701e000e8081c2c0760380c94040324101c1c981c000003001425410f200701c0c509413a4a6005010a00441c2044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 230649289 1250 230648039 230648069
    0xa080117031c020712031a0901030203060c070501060e0703020c0d08010602100b180f0a0b061201090b12060109060e060402091e040e0708010c031103070207030308190510 75
    0x2411000202600011540025442d1042888102c446051200d03800c480d200e408002680006110b0448488a00c10a40703001c60761641200c3c4032014807801640250003104500010805664002900b40d002420404c41540d106c685092141c05400c140c0c02c0345031200303410801e02070450b074154024010701304004160f452500705068101c902c0a02840344400507800760303420b9940b100c0284d1042c501e5050040030b500c40308820004d40124694200c0b8400d070010081010000115014024a102c040b0116811464241d10b408195000b00c010b000f00f6070169528080e0040584452851a41c1c11028100b00c0d03003a980d43c0c003c220003034116401215184214000492241d003002e0080d150141d0006001c1c0c4401c0c1c100120540f5017000010b006944991512103864400c1c509000703c001400d1404004140c0320940e10001d03041d1081050f041000d28410030811140341c1d4041a06800c2d01e506240004850b142c4040c0c00c2d03103180c1c10392203242507107207820300f4490580c0e0340901c41c9003243c0c1c49850501034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 230650539 1250 230649289 230649299
    0x603110f0d03080106120605030d180b04050d110301110d05090c01090501020307110105040f0807091d06010e040807061d0c010504150c0c0305063d05011817030a0801 73
    0x100a011000300403c1d00d2100601a0a018505010b802420b803040080c1c015039400009250001c01110480840c48030f15441c1d980b40700f08a04103025000d03c110b00ca25191904010440703401c2c20840c003500304059a106070609a4003901300d50042c0702e090b4070850316590a03020b03500040c1b00c2500e808510b4460f04031003070700950041030010700703c80058001d9400c2051a4441c0d08401244801c403604108003000302154081100d60403001920544004001c0c0d0f900780580d4008490113014049100006030000c0c0c4030003400080c1c068192000714171100380648a9290814940c06204e0004000b203040912640d4150803c40780201c4c01e401c1c01e0220f0f4442c0d0384034001969981f06601960b2500b20554802c0e408442c0101e52141c01d943c4981c54041c01c290381c0f5100c01d8140070341568404810f140c18a002c20381800c8801c0145c1801e00c00003500c44400000d0301c0e480c0084603684c07180c10f0601030800e40c0c10040c000181e10807801040718400c6c0b0744111a5034400cdc141c882d4030145115020940740000450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 230651789 1250 230650539 230650549
    0x6050c0c030a0f12020c060c0d08130807170403080f0a030507080c03071103120c09150a080a1116060204050102010f0b090606090d05070e01061b050a03210603110f 72
    0x10b8050300402c5006852101c3c0d1100003000d039100f0040010b510551054040380e803641030040074500f401e140905181505400000c0451601414201d1151a1501c0d10b00c046060783d0110303665558021100d403c2044a281d072000a405117a00142141e000803031000c015078000c0005003100000d540d000c0210399a03240c01598080000c1c0d032212030b11a000d1002801c3c81e0b018144c010191408001164140b81b42006000d0200d1021500f86000c880041905003460a00300c42c40c11103080e24403001403e05035026030040c2010742c0105007568541c2c40b244102c1c0580c3d090000c84901c10100640040f03a51400d013000e0010313501c944101d900540c40c000100114502c80d00c68040840070007402c4e0030380b5031504401c011083c0c20110b07402da03200c880840000d00095042040c20018040001c0302c0015605d4110081d050854103200708030b40310715400c090302c0005e030042030003018107505051441c3c00ea030b034001094000d10841c18003c034010b4070f0030b0000300510103034040e000c400810480340041c1c0340c1c0c62075052003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 230653039 1250 230651789 230651803
    0x6010512010312021f0204030501050105030d08071d0616031b0203100c110703110907110312040809030d0c020a08010c09090504030527090a060614070501060e0106050c0c03 76
    0x4949035280801031002030541c4406910f007400b544110b540030f0080d00c908018141420540048040e40091b0410400c40c0a0060310b00404048001e0030800a103400d01800700b1400600310001c0102041c1d1414509144541503108090060950780c0c030f0341c1883c1295072240c02180c4c2c050700440c41d24540060100701c00c2074450040b40d0301801405005002507c07040261178090a44024442c5840ca001c0040404000c0c0d00e0003035000300390824820840c0c1c1f0034400244006071a8004014030000005498200002258140e1100e0200c40002e55901d0030412428001e0710b0300b140c2d250080e90160f0b0412a070000564400900840c0d400801960711002e0900301c0b6034074a019004160815803c101c2c0282e1640010350140c02401c1c4149448100e02410207039003165081140441c4401200741d11b10b0624194070fa40c45952050200810350a184c009403070007908102002403030a0000344a020803200f900984020150401652415611480301415980241ea05001c1030301c5114080f1050b860001090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 230654289 1250 230653039 230653057
    0x11a0405010602031e0417100b0f010f21060801062103170a060503030a0518010e011b0309080f010506011202040506030109020f0c0616020c0102070e13051905010212060105 76
    0x46141c018000d0781107900d240d60303101d895900178003403000003030021403549440e02140e41c01c2c000d00ba60a80151101742145c8401e42420f01400c15078000074010790304240c00741c0e100000e030f0800300c505c4400205003500700600d480180810506001000541080540040c016940103560242c01c0400741500701c0e91800d2404005400902a01c0d0b59031104a00883c8054100d50b4405020a1641d12030700031a00e540d000310841c6c4005040000c030190701890300c5902c100840f07030901e450202e2150000c0000c2c0400150a451942800c81490110400d40158804002880c185041d034020a1598802900138401120711074007245d4691118040c680c110700c222400e85100412050459007400801c10007900006100b1100140c00c000c50091050104189440788900e4525450410100d0760b009040c46180541241550b02c4000d05010f000da54040056110003051007441c0070000c0d60401502c1e04405105950781602c0d41c080c641e0600106400401125110031020040c54465400469041c401c280700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 230655539 1250 230654289 230654293
    0x5070203070e10150e040506010c0b040209070c0204141f0308041211030307060501050f0604140f01021501120203012901030e07150513090204030302060c0d1b02011a0405010602 78
    0x20300881c06503103103560300808443c89461a0548404d075a44a06600c2c0341c0707100c0461101540c00c91145803e0047d964001380a00c3c000403d02020781c1e8010003000c02500c02440340c0843d800040c40c0a119034401e40106800400c18030030b03100c0f0012100b100c22400d968004255500c41c460b49040a0b1401c100c90440c2d921022403485c1c0f0303141c20040c11424102d0202220140d020295044160b03404102501d0142e000780400565549000200003400c60b4500609029000c1030004200360101d95034010810402900c8400c2064142c0300100d040c02d2240d00e406400c3c86c050000414129503104401d800b50f0710940003000100030b907018101c0e1354140014040e003020485c48401c002548680c205568080b2545d045034803040d140e00c0000c10a48425201d035000610104004880d1840741920074000c01460b02d08501e0182581c40082d04c51100401c3c0c455203440c0010040e0300c3c85216030041c51800381c05040c020f0b00b400720700e100078041c140b142c00c121800400c00a2071210781c581441914125040b80d00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 230656789 1250 230655539 230655553
    0x3020702090a090f0f1505011401210b03030406110105221e0602030c0913022d0c010504060f0c0f051603051c090b070e010e041a150307090605070203 66
    0x708000340600340d0081342c90100d1021107800140d5a0340380e09a4140c85402d504610002e45000e201c2100c5059005441080c075810040b03100d40d0300134441d000d50740940c1181e101e01d003000500030000382c0a4480015018440040c0c001803040e80405141c1c1d020b10400020320079500d07801d1a9180c0c400548072210702e4481d120710210300080300307600c5c001e6505c41c034000e0881c0e90400903250401285c00031148001000c20000c0d60500c58604440403901c400d0356010b00310b09082c4005460240201c469540440c2420000c1114a6081c50001660004c201d180700911082c0380c1031504d40041c111030b954500d0720320b003014038552100740160091040028a69109424401d01d12000200141c45032400d5083c0300c1d003002245c00a1003020340d10815030100079000708503c0142e03d098900000b00a000c00b082181001011365170341e0b482800c0e00100803003150007007407480c110001c9003155087c810980d94842c1a101c60307903145502031000345100c1c0d08a030710380c01112559900161030328801e0510082d850b401c006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 230658039 1250 230656789 230656801
    0x607090f06110f060106020105070e0a15031d0303040807060b0f010f03050a29010906091512060819020306060303090315281b03020901020d030c022103090c010302070209 75
    0x3120182c0051010110b03400325451004072403c01900707800420050b5103032810000c4890b00000d142008580c159044c1c2c002500d0102440040029241d0a60030142c075440d012901451700c084000d0461030141c15280c2d03e00b01854100c1c115881f25104582071405c00000c02164a4002d02010398405e040e1201a001440c02c01c086008001c028040503d09549090301c44111548002442a80d907541d1a180c7d4040c203000b00140c40c03030f800350780841c00b0080200c0d0144081001c842440800c1d00a40c2041e00da0740c0701d205150f0380640f00b280c2005560380f02c0c0d042d4211080d110804482c0c2d40354000d81c10340d02a901d81d482455280d118040342c860305540703c00c3d5001070152003220702c2548418443c91020f000040e12510a00b00c94102c1e0928007001c1d201c0310000c2008100b007003213139604039584c1421450011941d0020392101401001541495640c1d100c8007505070007071210004001c2d082c2030010031800940c44030045038005031000b96580c49840000030340c9501a100700d40c1c00e50b80080024402e0340e901 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 230659289 1250 230658039 230658047
    0x30f040201180605071a091c0302190804030f110d080c0706050903030703290d11060a030c030608010207080f070804080111030105041503170d06180e0607090f06 71
    0x1800403810000d031415200c401c00741c4070000c20060f0590b035403669598005402d2000c03600d11020341440e018001c6401b03008401c0000286024000201c11807104c03219005801a0001d026003068200c42c1003e45500750903c079806480c8605c154802c0d00c421001300341303080341220300382c24180344018940d00a08102c01110700031400c80c0e601c10712440302c840c82e144a03660b0f110141c1ea02030b104003500740d201005010030541c060180311004030445035070140d01c190001220b142454000009409441c12000103000e0000001424000007409004990783d01e1415070020020003000503030100003494102e0100d101a418000c0702c1c8081c0e0070500050601c15001d030603500b1613101c40d50440d03d8103020480021288000c0c05006e015403030b541141030f22585098188800c2e141c1c44c0e00409000141c1400a01c00141d460214450128190214544640001e002000140b4040c0c000c010707000d20700c150700e190710521500010407040034401076541c1c0c1e4a5501d41560865503e000c0d1b540c1341d0010301d2080c000f8a00c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 230660539 1250 230659289 230659291
    0x3020304090f020d02070f15020306010806010305040812010e0a0e0304050609010f05220f090e1c0c0f15060e0118020f070f0606060906050c03030103110d050d02011b050f030f 77
    0x4600c2e00515142965409400b264800b14089074031003030317040c0700768240b201c0d4250003072404589010030341c5075150401c0001c2980d400203014605066442012034140041e05007900d1940d014000000707540c0d6180c224661224000700c4820060500703101c8580000d02d804000d6504a40000d440d4900740f003c800015603c6d5080d254584c1c007040300c18012189503082c43e40d0a078010705458806035900c03504102c010b5003c000580c0204214a06080d0011014400004ca4201c04c1482890841d1121400314003115181d4103102d0141418181509500c18000b4218101e0300e0156034100402c5a10399814100b14070ba0303402d1040700b240006003c0303800c0b590070f056001000d161a40e581d04038600b039215a54000c074025145006d031102d503501d4405000244d04282c0120150195042403400c000e121071505550b071105010080c6034100d4420140c2060301c5110b603400da182d80c8142035410f0b09200d10002402001d4600110300080c0400d0321005110303000700b04840c3c10f450040c0303602d8a1a952400c1614141c80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 230661789 1250 230660539 230660561
    0xc070b010b07061512021504050102060f220602030609070e010f05030916061d041118030c0303120f070905010c0803090709110909060603130b0c19030506120106030302030409 77
    0x501c882c00880300c802040c1c090307070180c4400741c0d14008007002401030003445100070007403501f0228200001e1015a800041c41c1b9441907290b4a0003d9550300d030070f8803241e500c0d40071000052036a01514124200a419009144034400c04e8071002c1142d0307035801e000c070341c400300903040c45021502c0c07014840305e4284174000940d4850859001c0341d00400e00640202000c04095121709c0019a0070304510601020b40041e049400c80c04503000d2080d140604d541a405214800f403074081a0811500d1041d262401d02c0104120000101900d13103a0041c03903003100451000b00c1d2a41c01d65000c142c0012a843d0042d00b4540c10b841b0103030340307022544440e0740d079801c1c143e4000340c800101c038800c603e4000340140a13070048049895850440e03a03100c0c0045410f01451880141480d0711800060041090100c844110984925002884030301e1544840a50b11440c0c400c401c548800501c4482d543c0c2c101c282c141d04400c1c050710b000d6520b60012404900d03514201c54003800028016002003204211a6400f5004643c102d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 230663039 1250 230661789 230661791
    0x70f020304051c02010f02011e0b0d20030709050702030a05030405150115020706050301080c0f1302030408072d06050c09030a060e190b0429090609060c070b010b0706 73
    0x80c0e194400200101a03409076192076441c041003d00455901c5009800ea500550000340200e0039442100d140c840d4042c005d02044c5a5100d40c02400e95840600d0502040d400c440c00310a0070b4040002404032448410b683c17806881448000600382006110f50740c8155102d5010754101581c941049884d60b2018205a0b1030341b04111401240e030006160a034004c04070b811121322a0400d2410203410817603903034003100900c80180b00412240b000031580d2001d01808030b07583c8076154500c3c800507490030558111307628110720200400040103036002c01081d5542c0500e40350094080000c0144420b9241100440022100354502c04000f40250b0000381d00000b40114880c00c1010030750200c1c0c54a400c00405854064440c01c0c40000340c542484029070f00c1040c00c0c12076501d40e01603152001c1101000e40028685041400c200c900c1c21600700e0102c03e8112402145a0309040c01c0350941c0d0348440a84090505004040c04140d040441c6030403121001c4d4414208a90750386002c1200b50140c111031070a440c42 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 230664289 1250 230663039 230663047
    0x206040209040f12030c020f0d081303050f0304080d05062b06060909050610050a0b0f0a020120031e0603100504060b19030510090b280c0c03120506010503070f0203 72
    0x70540410b01c4a4044d4665002031400e0008070001d2406001c0e240c940381c50f4102e03c21102c40360742c0c44011130341d0150031058020412881d0385811a503602c9492200100c405001c018001000745505c010030358682458020302064840302c0400600710003169900c90150110720040304a03540005c03564004601445000441542c0d42d03d03c20b00340c0340d1014045882e900500d00300040d0207004a80e80300a00401d40d40d00c0106800c2100b400030a100c3d6080300c0107081c101040540507607100b5001700c4090a0301d0b0060b05d94641c07101c201001c640c0c1041d0364030341e000c903107024500b84c103443d10a0130341e40715110086c001d00011526910a4006140240083d0b48498403004452015102c1d80140850410300c4400000d04d1851400d019081c04e0700203c4402d405401c1000c0040800c0000f078040da04000d4208614021409042d04035000d013090000b50001ca604040040c40c0041d041445180202d0203074a810301ea140c0130380c1c1200120390007258240e010981c1400030031002485a01250488800d6004907490 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 230665539 1250 230664289 230664293
    0xe0703181e06050c03040201020c13091e030e01110c060c190b1e0f0a050c0c0d0302090a050105070203030304060c110109080405130b0a0302190f1e080d0206040209040f 74
    0x1035050a2a4008515604599101000364500c1425071015813140b90f1400d6090540c0001d480341b4444c20000d100d00c7d000086880500751b6580100700c09a03001c2c801074408010b0801592010740040419004560840e142001650181c0740305032844441c2070107000152207a20400c082034000a909503804d12440c03910359000e81c0b842d20801803190090701100e01034501101d0300404041e180c1e26030050260100240240814482c11840d0000842800880c01e0307a246083c0d04668010700c4110500c078410008000e0003a90140d00038071564805480051009890344015a240d02c14910002e405901c00c10003d008156650b2004001252038540506503c04408420b0700703441030360380f0136100b50500281c100298134103a0380e1220141001003050201c0200c10001500415551001a008500c04034a6580604a1795001c0000d4090060800c18072502c80b4018192003540348100302000c030f032110b004502c50354001501802c00c01035500030301040d5196424450b0782203004c0d004881342c410384102c00d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 230666789 1250 230665539 230665553
    0x30405040608030c0c1012270c05040b010c1a090a120905030607091d070509030709140c04181a060a050a0e0f060405010e030703120c1a010e070318 65
    0x82400b14019510707100c4100c42d9a003070041c001d0000e403044040d2000322803101e4110061f45455502d12000040303c1c16a000c20341c00f051544030324109840428031085040090300b2446405459040e20100144000c60005545112003544050300ca04103c482da81d030505500640d070341e4803182450544000010a5503144829070700100d1402c04100c007400d0600907410100f294960102140c40c00350481407410418000c0344082c840d0103003034405c607000080d420310b02520850700119800b81c21038a580e82c2d20079480e40140b100c1d4600c40507004080f070111b41241d10a900b40c1d81690b0350252045118000041001c0061525030400a4008561655220269180006441221101d8544c3e99480b400090010050704180c0c1c1550310500d4913001100aa4a8040aa4003500e00a0a15404c0c911007071000900d84103055000411250b0303003040d03081c10710b0b91002c40551400e106d0b01149107400c001c0191140130810900444074500c2030440000d11041c420b4006101d00341d0030748050040c00506455500b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 230668039 1250 230666789 230666801
    0x16020a08060f0412050901050f0d09140a02130c0509100207080102070b0f07020706080a020f0706150501180501022805010c260f01032d03030b040c0206040506010608070203040504 79
    0x1030b07020020001008240440c0e203c103840c00102624240740780540f44400a00303140205010f4502d10304000c9105c00d5189001e5008078011500609940c2c0341e210b141c4600d5a59550012049018080d418000741c45040300b40602480c0719802c0d180e0740e0810000c030050000c0c45110441842c21032040200000b0003000070310003007107030368050164088540741a24080110070005042602198080041004081d602c840c0a64101c2c4141c840982c0d940e20051401006000c0d41c18054072007850002202d5500034420150402c681080c0c0b00d9281e1680d806810703407040c2e0081d114003800758000c090500320300d040e80070a0071380142c260241324860b0103440d101e440c21546400c03c542c01103169020110005801e00a20418124501d0050304140c5002540c62905107018030000341884064500a070300b074403841020301080c25041083e1030303480c649070070010f0180c08441004c3e03014615061a0b5407041b0310100b00c50b485240c0010007040aa40781450481d00744200408040860100340408a21a5a68000c0c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 230669289 1250 230668039 230668051
    0x306040510031202280302060c0c160902040905060607110f04020d0513260409050c041e060e0a080a0210050c0a0c0815070c08070f0f1a01091116020a0806 68
    0x4068182c00d0304100101e00304905c1c0d4100343d0156046800340003982c0010000e0348000003010b280d888a2001c07406502e0544401201070840d5000c0c003003c940f803001c3d58003820455013050001d105036290702d03041c44114401d2020140440d68154a42e40c83c3d814481160461000007410051416070651012000c13603005848062402c1c4a283e503100c20b214500080180340e10070200300c5110304101c100b0003d164882d900c80c03003950320784440000b81e5000108041e80e00904140d400003d031640d0003080c13a000255140980c03008a0500c41d134403e06c50405030304c0d05c4203544d030f981e0040c85018956000c020703c84082c11501c0e020000308004030000180c0501102810900c90000c6a111506100009042c123242c25106042c50340000c00b00080d003030344401e41c100f000d0b40150079181d9541d29814082600980301d04040c218019040341141009440e0071408078007803088020760b0b16070340c0360009038080e82c45540140da2045018440c44600b10802c1d0629004644020404192070303030fa50200505168085400b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 230670539 1250 230669289 230669293
    0xc0307030c0315030b040804030503210a0213090510150906080c0a0c02061b0303070c060c020d0504090b030f0f0109031706010210091115040810050c0306040510031202 74
    0x9110455805000c0c5040d00000e905007404406014050700c90001d500c0e110150400e00d145000c5000d2101003000c850165800c20141c0384e0310120300401034407020200025024a40d458800541c1049451003034501d07030310300d0340004c5c1115071501400001030200070304080c1c592034480000250340c1d6001e861440121406459041c0c0007490f120000e00704090003031069400000070000c605003603070700803c0d5481c132550440c0d038181c903281c90341c241d00220520512001c005100020038401d07019000410f0511481c8034072801d0188000082007262552001e8004402041c0203020a10881030310740c0080080030300290454107000215040d0303c3c81d0414418404200e41d658840b0103003810b80c1f00c000740a41d224000d0340c090306820b124000035070300c03080e424200c0d5000382d0743c4605404215507880c001913041c8004081e620340c0d05160203246d0a50b44584216155445880310304000e200540c0038040c0324055404a041c10756030b4030b4041c0405071500900c41400b4051032600840011600918484016405d82c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 230671789 1250 230670539 230670541
    0x903010f0b01021b0603070c030c0503030108011a030307032a080d0b040e0f06070f030207051c09060905010509061809040f06060f1809030905180405010f0e0a03030e1002030c03 78
    0x380c1004e244144025040e0b60b614515440340d111401140d070070210b40d15000c3d481f0042401d044070306c0300d0b640c00024140e000c008000600c40005400c90301500c410311005118203004c1d8810540e681c40740b1480200428110070741c1c0c0d1810403680e10841145540c41c0f01c000c0d00005941d03100c8215901c1642e0212000340e4a4100c5400c83c2850303c6540c0d88a0442c0e00101080401e19042d07030340d14003004144104000c03c5000111141b48280c05540300c02c2d6000c800c45105505214940c2d090307241c91040c0c00000340b900000000c0051088624204541d8103840d070328034040ca14414051140c1c000030b60030f0b24000107544d554681c2d44660102d50700c40d5000f1149142840c0a501c0c1c6801541d0340d59102c00303001c1c511030405025094801c6002040d2890182c00054110482c0c9815101e0440f16404241d020621192414050008088140c41280301c0c1e0020011502250009411164414580c01d441d601040e0124002800307a40021038007030b02038049607048e4a08201c1942664412918442c80311000305c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 230673039 1250 230671789 230671811
    0xc0a0c2a03051015030b04060f02130603090506220b1e0106050d0b030d050d020d0b0405011203030501080f0d0f1713050f150c0a050c0307140d050901081501050903010f 74
    0x122a02010100640303502c004c030313071864982d0f5a4010014001525941d07030b0f11710b08131403c0829411154514040070350865801d665000180c010b000080b0b040c0c0301e0740100b0340015500c030b2008a040d42084000c1c50303002c40c1c0480c207031034030050640c0c024a1403507004410a0819407a184102016008280d0340d82d81aa03600109103240d030a842c4a404081d0180c0d0205d204000c8080c0c02c00241d502e000005400141c440044081c0000a40a2480c025070848c0c60100003082800007029001c00e040e02945003441666a202d100996501c03441080f02c4072030b040380403000c0a051141b860724030b03120003510302090070103035102014403070070001d8942e245140c034401e0b68030b030030414140445010303600c2e880040d001a1000075069000b0700001031800d034910704005501c120f01400341050b83c0c54900e09204030383e00d500c0036103040441c2100130071268200703105011000c4031081c816802c43c6c442c9241a03403178403a140c0325104a101e9240000c0c9a00c0e0600100348412016030718244aa000340032650f58010a03803421007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 230674289 1250 230673039 230673041
    0x112060801150b040f091806090303051b071703040f0b0126060601080c0a020f030304060b0a080607050901030507030e100f0b06090f060c2d01050c0a0c2a030510 71
    0x69801118010404c1c482082200c1e54400650100c070b21641010038020074903141d0401d2104001c2c0010101450440c0d1310040c903074140e20662080c4d8419a6400c1c50740c52500d0342105500030300800a061003034201a100303084600d800519040792054401c0c2e01840029510340e8094207098100d840307003440744555100180324503041d80c403481c0d0314071001e04410b06016000a0039090003c0c10000c00c00000100a8191482081209600403240742038135100d0074140b40c03140140c280d0a901c0d40c8260744d44500820702110224515014003410740340d880c036090f000801580645401400242416a666501c0308071031014424252007141714903002820036400040042225099084113024403070901c014002c0c0c4e15881801701e40707003000310b6909494a09201c0403c0c40d001e04103160503040c40a104078010040603d041800000d4a0807009100715903c05003400c001c0d0040c9200000080c07200403c04d40469040f034200c2400c14024050f215880780707400c074139442410250b0720441d502e6001d00d4a0200c2c217111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 230675539 1250 230674289 230674331
    0xe1e010504062d030b010e091c0206060d050f030a0306170102091c1b0803030403030f0506031002030c0c0d050706140f01090519020c0f010b03060c120c0702040f020d0f060305030f090112060801 85
    0x1100d2700140300301c0c07102000a5031170740004c1c4000d00942d00c1042420078040c00308407180d41e601c481400c881d9595820600200a88014403940c0000c00c038820410309450818000e5541c0d0140c050503141d618403480c50340b02d511a0901c40305650420b038603080451982c5036880550040d10204004581e0781c107007460000c0445040c0c10810803080e02d08024442c681c4e40100b10013684501204016840e500d652034101114440c00d023008060703202c3c41814020041d0032002034005113005080810148070b8890101815420803078000d4568580d14006100d262420f0740070b40d4218000503240c20090504514540403a4401c91202c0344a60025051018002c0c0c01d000d441031010085c2d024040e036082003501c01b5610301409210940c3d00d0564400a84100f5000d01590350f01034004000f0311984c05e00010300d4000354080d044c0020a5030402d0a01d00f81c0c80224081e01c401c8950210042d4601980031082e249103411041d44541080020302031022101d1850041c000589580000018080c080c0300405035203000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 230676789 1250 230675539 230675563
    0x60e040803180a0b070c02010215010303080f0a1103061002011b0909111c0207021c0f17070f03030509010209040504060501080c0d05060106180e1e010504062d030b010e09 75
    0x1100514000004a1580005800082501b0603054051507440141d042c40b0640c10040d2100b040e44000100707140c2d100042500030700f20030307035034510940b01d00c5208404e490202c419004510002c10115540d400c01031400344981c819440000780b1800c8030a4826614441c03000343c100040c2c000001440052210712a104544002009180c0f401da15030903031400c0c030b111218600d100d4980c0481c0030425500c03041c40c1312140e8003584039854445a4146040700309807030f86d032006403000c0e419240174684d207078000320443c3d034000e8002500b07214084e03107aa000c0380607144c000c1281c0400d540900c80b80d181511980101b40c040c3d8801c1501145660501506610307001055050718800c0c0b080d5444c2c0408a030700402c0d01410360302c0354600010848401042182c0403000b41c0e04c9154030a40100400c60b0381404400200807959942440c41010b0340d0314010003041c2c5015001d5248113241c00080d04051071500141c0c40340d5885810701a40b42e00359070303465008420074240d2061118a440204200e0038240034000742071100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 230678039 1250 230676789 230676793
    0x3032701090b010b070206040503060702010507090e01030203060f09011803030603050f06060616020109050d030302090f092701060308130807060302160b180d0e090610020c06070303060e04080318 86
    0x107516104034042e810711400900f03460001d0b00100707541f540300c00c444c0508030140489415003840b140c02030003410216100c000123804042c01085802403001d085048a070001e00404003915a4096060368010250603008190342e1303802030358000030411500d10b0303c0342e000e910009803291035810702500f440131007128080aa00620308000080d90740f8800d4501c440c40016610340318104610040e603101050340c202b42c1d80400d40e017200408045d8150001d006005055035904501c0f0794075400e000080790182e07000d009500d0400c00c0000c40010000681909400c40c10000c11303666501c7d100c6414070b80c41440c07c20020845920203004583c010800c000040109140851601100604603801e43d11b03041c40003080d6018600104a61b826110b0140a8843c1d21105841500c2e14040c2d02400c4480d0708040e6074082c50310304000803040d180210072418010301540140039100c000c02c04014841e40500d4040b000d05a99100203e02d15a80352a41840795110701006580c13410002e0300f5004081c5280300741d444603 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 230679289 1250 230678039 230678051
    0x121731030b0f0106021905011104030b06100903030e04150308030705040f06020a021503041a16021b0d110109090515010306050d03020706080a090515010e090d17100803032701 77
    0x19400190441c1a244180906e404550a890b1040c09489044503807180d916000c81c01006112a01c80124001e050407a400c00141d1306182041d50114440e100c080d020480c00d0540440c142402d4004440c151a02d08222005e241c4035a40e400e116001076651000080e000300d014040c403d04140f404000d0500c50000309203042d50f9a000594a049184a03840ea0316404008641000000790051040d0b601b0040395514514140e22030004207140000c04800621507011071414031414622107204800d00a05280b0f181001615803845400103101024100001c8150010b0347c0320f101d106150040402110814071141e6001c0010155100b6030441751140345514030048c0002d4000031950121072440c10040e0540e6100f0000320006c000e8a10054a180100c00b401121580c880b0066816296502d40511706512a00301e520303902d0f078003269440041401000b4100b15002180125540000014014903907a43c40d08403950440e002a143c49051813070034411481c1c0045075081a41210303262034020040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 230680539 1250 230679289 230679299
    0x1816030c031b05130302030111092b02060d020418090c0605090a030f020d0203100606170f070e010509130f0c050c1218131a0103110409180c1d01121731030b0f01 71
    0x2f9060030301038000d12800300022001101d07145501624020301d4a12010709001100300c810801600802d2011200f40024410200f00d8902900070343d10030510140c00807428a0465588208060300141e00782c4e80000040907050046c0d0b0100401c0104081170203005c14440e260150280c030520307100d280d40e941240058100809411311030981c940c0400c0b545080502c80c002c020051724181b0600810607044101801c0d10311034000c01d600800030402400a00f00011031408904850034052a580d0b009560440322590703581d581210042e150f4088443c1305410030340c159000186602a0300d054240c02542c444517044440d40403a140321030b1200003820144130400803041c2d410792902c80c5000300c0742c00b00d07516030580701e400c0740302c2c400045050341c4141c0302c00700b158403103003040345a9440e036923000c0c402c010740c50011880441d03c040c40d00c5015480b03051410403440c0d2840c041920b8210304000c0000d00e0a1311800e940110001e0316048000904103e103421150450600c803007034940052550031444808001000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 230681789 1250 230680539 230680609
    0x9060e0d140a210804030e01050723070311030d0f0c0606180603200603070318060c020f061e01150c050109210318111816030c031b0513030203011109 66
    0x30341c7c40d4007480d1969881ca0349250074020601244051022203400440d900184400024001d065034001d5505208141c2400c04040d6113640c82030401c00047c90b00300344007501030300884028014600c20f600100b501500c035600400500c01e12404218000d0301c0d090704000740b0041c01c02d004c450403800458000c03806440404030b0074030b1001601d42d8080650380c03203c503401124000c1c00440c103960301440c142301c60003501c40020743e1216040c02503001802000b001c65681c0c180090b0425000000c12481e00c0c007a031070407010072440c5068100080510074440e2030341c800148284181c0e401a4401c12109600707505881980200014600301403003854a401c4000e10400d405000e10540716a12040765540c001c030320400708408031001440c0e542e580d03112209201c80540b450654000e0818641d801f044900b0361a1005c03401c2e540c0040044500400302458880241d12560090007040c91015080401c6940c0c1d034042801c562a24801c81c200103000300f020b600c60b2030b24200b240d0746041010002114032445400f550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 230683039 1250 230681789 230681807
    0x8010b090d08030a090503030c0921100b0105040312030608071706061201020f0a03050601020d03050705030f06030f0d0305040218041a06190e061009060e0d140a21080403 75
    0xa03000500100002e144c60b15a5005401c03010341c4801900d0b00ca042004d01a5029000b42008500c2161447e0b0202d0048600151218032040840700400c80c03002c101c0c94080080421b6184a0f042200401010021440b100da0020020384d441d58002007151a02c528a82070081c40d030031003a000d2002c1405902680c03000507115420410071070311420415019290300d40203200d6454110b0303400d64003145200403182c26901840c8202000e800784d1344010a1900100d084900480702407020500034400325400d20901e021084c1e00200203012a6803003000203a501e440d028680d0030f00c000007901c2d00c04101c01c505000d400e40e81c20284410040c889400c00c2d50b0b90411890500c0e140040891503c00080c01c01d0b503806000828031403502d2852201c180d1a6904c1c250300c10001c4a07198058107004000c80003541c0b2130042c0404036200c1c5d6884400c106001e41c02c102800481079419911681c90340c02205000105102d110300030751203004014003000c800d8042c502101e062107291000e110280d020800401d030441055 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 230684289 1250 230683039 230683043
    0x15171506030d050f0904060e070311070201050a18090f020901031b020d08040609020405070c110a14060a090b0d051e0f010302060309030d0f02090f031204030b0405210a08010b090d 79
    0x107184c031200095210302c09809000840e0390300609106000980450050545000e5041560107000c10016081c84490720b200b2250b0081c00070300200320a84280e0f1042c00c03041000c045588600c1c40880e60385d120720003507803d070311024680558005900c032000e60300740c86258068100c55441e40ea440c21030440c00380d19165070341c08400a1054031000a401c110582e40311b026200c0c0c0c010010401405e1a880060504804007401c0b42c0106000b07201d5042494000b0b0468215072201e1023100e600e204000901c41c2e40d8000e01c84800602c90303000c0000c1100640500640b489908032000050366240c41c0e41c08074203040940c40061042c00900d0184182d0707608003080035041d00c0d01a1b8083d40d80c1d4648007013071490b43c480c10010185413450101c1032070582d046500100000c007412200d205e10ba01401080646030035140d000400c50b004100300800000304500c01c032075031090081c400e41d840801440044500c40e0000404c1e074842c40300000c0d1101c010354110001d2809802c1070002d60741440303d28008514204240040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 230685539 1250 230684289 230684297
    0x102010b150f1303051b040b240a140324010801030503030105040c3b0a0f0306180b07050a080703051603091110110106051002060a09020415171506030d 67
    0x41815140c3c850000300000b5070b44901156080c00b0501c0d10711400c020f001e00e04501c501c0c141104501c039440c180050012107941c5a8a0390240445000078001d02e5211840306002e00c41c00b0010f05103d41040c4c4003543c03003107490402e610344101100c07500c07544106070360000a0500080c00014000300d107002080d6815200c090740d0006003007442100580d440c0040d07900d0100e032507292071142484004c2d45400e0316500454901d140c0140303109582042039801c040e000d0181030f2482c1c0c6108002140aa81018000100e1091000c07401c22a5032900188610111340000210304005019140940d1260000c1e0340001c507032401704040d04021300d044502c500b85500440400d81c0b24030000060103482c00c00d000c2c141d43d0080c61211001c0800b18007801000c0d041c61715850319460101e00185a0904400101c0c480500358090aa1a41d40c404054002d0480c000103076086070740e07014ac0541c05504620700304050442a40d81c80b14180704162458608030500c036059600d150002c081c090030b6100003070364400010705804c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 230686789 1250 230685539 230685547
    0x120323090709020d0c0206010f0b0703082706010e0f01030b160908101a06160219080604060b031c020601062712030f0f091202010509030a0302010501050102010b150f 73
    0x2039440d19240c1c003508840c00d014400522182010030710762008209100c6602611650782e62925604122162403082c1c1205410030040d01c0c000a11400ca0194801d00c0e011401c424140340061507141e0410358038101d0390b141c2c400300043c028400950310595000d500a140c69060351b066907034982d01080040c28900480c4010f64030719400c0c03809049a00042d084401c111004e400007400c81402404007400210342030b00085900751858100302080311550741c101203102c2102192a03081c03120f0309038a429042103001c115400890009020311000d405640100300118401c07855900f01810500c6402183d4038034020381c0f8044402940103d00541110400c0c04d000180400e090060f2080340c42c1041c1800340208810b5020a0015600003880c900501a07594400300c500910f10a441441c001d00e4580089410050104030701e08065850120040c0f041c034283c1e0030640c020022929103804d116080300545d440b02e0040c005543d092151134000c500481d04414000310700b20a82405101c1c003421740c888100005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 230688039 1250 230686789 230686801
    0x130209010203070b04062705030a05090d0b0114090105030d0f030b06091906020d050a02071406160303060513140f2212090605030106053103060504120323 68
    0x102c20b07159a240c01c021300002c540340511b0b08000030240c2d80030740038052010328884401c5202c3c40342101c0900e54810021840d10b40d92139000e588940003c40d4582e84030b1101c0340322000240c85211114020b05003504103a4181d10040e040000103c41604858082d80c400c60b0708110091380210508541c40650600040401c85140071601300e02c00d45001c5608036100300015035600e00c0c1c40c1b0862040f01e8403642920900050f001c030031149840340002140043e4014802485902854180242481001000d55140100100c51142c0c8410541d4068020940e205d0003003095041021141340c42c1c13143d081303080000e41b005814403800707901c003d0440c410302003510000600ca0720003800c0c08083d4001e40c0b03000780e1f29688070b41341054041c1044003040000a0300d002d1f00003401c0e030041d42500d040e114039450300390a00c06980c081c4038441422240341951505c59811400c042445900c854000c0c2d8080d51012810349010b0900406240300d24505408240c500400300400356004400c034070031600a02c1a07042503445013 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 230689289 1250 230688039 230688043
    0x3102702120318040b010302091f020102190e031203071407020303120f070f090302091f0e090d14040b0702190503100e0c010e1e0a0305010204030812010e01051302090102 75
    0x844070825944000540d404861110320f100d400380b4401110b042c4450384102e0700440a9020b1207011940002c05240201048400c04c0344c01c04070400d40344001410880d1031400b280010202010030008a4079803914412107050500c02c2c200104111503d080c0345040042005151200d025010381c079580011404000f1950240304070340070148501300c02c03030060a0121550a5040e030075075181002c941e252401d2a989070065000300304803038004001e0380c855684c913150302020540b1640300034946800400c002c541090544d602038060103149c4010500040d1525001c0c003840240000c11003251024402042110b030b00400312214990f058960600941008103112541749280d0411307540360240003540261690254010440640d0080894404c140b01e1001074984c18801d10110380c0140141e00c2c6e003511952013002c03200d02000041d0001904541d40c3d114282207800a800031640750710001141da59007000c000180e4050030754034410032706552518001482100d4004101d08845070003181c0c0e940c0aa0003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 230690539 1250 230689289 230689309
    0x1009110f1909020909090d1722030504050316080307140708060f0415050603060c0903070302190306060506030106090311011403090705010f03020c032a0a0b0603102702 74
    0x5081c09595a490b450028060b400c074002040c02901c0f8440007428554002a04034031041003620341e08003500d11010810140c0f14000c2c4154215042e014403031180700c2d0440341c40c1d1101402980c9054440d405c140c2018100148190b100c01d05070100d400a000c0440c0110891b200c481c0d00246a240c0351030541c05040c10180183d024218900902c0108904880e042c0c10103803150340716001011000c205080e200045460650780580c169000c0d4000070700b0101000000c0095a03001000c503224940c1e66800103075005501d80714110300707500e00301e070070010071800d80140c002920b001c803015401c640c100500284012120310010f042001c034003859400c164042e074028803120b1418400c155492800307621242e620a950302c2114009892864110310319442842038400307111240f00614034001a62000340028040c2c0e1601d0044401c0e002c0800540e400c0400c080341c4558420a02c042c45071900f48101420034903001600d1040c03c0c1880c40c211908070a422111030b401580107074855624000340041680114 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 230691789 1250 230690539 230690569
    0xe0c2206030c17071a121503031803150403080712021606090209010905070e041e1b030b010503010f06031814030d051506070305030a090c06090302031009110f 70
    0x26071000100d401d520307000c40c1e03c50882003201102c80540c1e0703920203680302d01c04a54020540c01010312002c00120740e00f0401d41d030080c41710100c00715a950200002420f550103000155680ba001d0204118281828401e20003030300d1101408014900e412b40f006400100001c2c541c1042103891500d103605241e50b54181d43c03118402000d11a07015900d441c0a20003800f075618264030416142d80001070846250041307600c14002c03980c980c54007480d0001030001400d005090b0010030318400c8603130030001d091441900c0520a0400d0a100390081e41140682200d02c0080d4040c10000200018480c0c00c00d0b208622003200c07590320700010311084000b840344030555003000040000c89903032102104084000042c01c1c4492041d0300c00c116a86400350205d8041d801d440b48160403003014080e14010900480c083c41e8041c9024101145111540d50b403103c099030745410050110700302c85c0c424404d40c00c0400c4001c2c11103140c40300030460700100381c9680c400740850205842c800c400e1441da445044d203c101250729804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 230693039 1250 230691789 230691803
    0x1050714010e12120a1509110903030706050115020102030403080708041103060405030406021501080d180b0408150112031e0c230d020a030c060b010e0d050606040e0c220603 76
    0x1d14152003440513a103c3c005590070840003401003488140c2c0e41c40f68100415280c110000076074500940c40000d0603c250348050035030014401b8060549042c00208a8507104040003d401e40c1006040480340e0402c000c040700b1607206004010009800482e11904071443c0d0929541955a030703e4613120409581400d150540180ca080c0010004004081c005a50083d025504035841070303041003450104c00d104604550388544010103c090240000381d642c10024010504c0c0203803901c6a01c100f560066100d10142da2098002c01a5240e02e01501d60150001960f20000c00c01203480081014055228481d44c0148662007940d82d01d018090030524158408524444900d02554071741c4414649656002d0381d01800303080b2203e80b032003c140036540c2649a140e1a02180250304e0b070400034040c0c10142c1703060007100741440c400c0d555815410110240304200420703040c5003850510090703072007800b0b40151a038440102c075141a65408500c04090140a080304075103a8a1840f04020300415800903101c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 230694289 1250 230693039 230693053
    0xf04020d090b0f0109230705090d0309050f010c150e19030302030a0c0f02030a0320040b03060a090e070308070515040506040b071d04020307091e05040f020901050714010e 75
    0x401e100c0c442e1481180481c140c07064a030790790304882003560204101c0e0514442c1c804440d9001c040c208801c2600030249140090810700c1200110310806410ba00580101d90891420801e174508045c0466003200e003803914101c000318550700e02c2c1011607066014550244c0307030301180310f030301004004024104040c0c7c001d0309030080e0715080142c0298403d40e582c1c80e42ca414414400000c502030722800d0020b4403254000d42c6004695081200144810740b156440e242411421a2810301c03e040900003501860302490754900b880c00800050403039030b40c404a03906092025a010350400450704504030303504110001ea85030002d00d00142810f149040d420074125600c0b0602042c0708000a50354400c0b4454044010300392148a000c0c0d480c0d01c007501b50080300c2d6000500c07007246410a41c01443d00000c01d414451401c0b510313014155402444120004004840c1c50420010391405000d10190000c1190b0308518000800340020503030310070044098212044030903000c08410095001e11411100407064543c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 230695539 1250 230694289 230694293
    0xa05120f030a0c020a0f08060403110f030403320d0c020d020604081608031603030c0c050a0303020c010b01031808091801060e12061501110109080c03030105150f07020f04020d09 78
    0x3c5944104140e003d83c201840c04200071301c1401c1760b5015950130100030541c03581c1e155400c803148a43d241921035180203084019000207410030140c0050344c41110600102c0b0300c540c019840c500007643d075103203081c0b1030180f040203848404625445988283d18010799030b441980080384091210800007908003000040003d40c40300045000d15440d004210011201a40c840d0003031f540780103d22131006001081c0a0b1940046c0c029441500310b05a00e00300740d0b101e0403140e110349041184100c016008690009a1340080c0e031820f104440e4910400d08042103114000341903080c80c0c0b800610028440c0000140200702030f951925814040411292200c48070360b11303200024051000140041d000742d150341c0410440d4040450300304d1044400c0d400040048408100440e02c5116117500e1103199583c5940300b00c00306080c2001000e01d002c1c498010f540c0d0794901000d112030f50a00e0f00c0300b0314521805200e5840501d080038101c0c1c0010b0b80494900e5900e00070940050000c0c41032882030108070b441c0c928a002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 230696789 1250 230695539 230695547
    0x8010e2a0a0906050708031302120f06040501150e0406020a140f1c020c0607080421090f080303070f0302070201021e0604020406092d0b04110304150b0a05120f030a 72
    0x1800d5005556400c80c070b1642ca00c2e040d01c2074018582d0090040e036060001070310360ba000201d450303c00e40c001804803080c01c107030700c01650801040207002d0030070340c2010007000140103003400b45e14102c03070510a801e03203540c1c50000740900e010300140c0028849070300000c0340c1018a1050051600031100d01e462195030314a02c5558044031341c80036120f000d02d802c8001c50b09102c0d2180f4800d13500c8110000d406418956540f04046500e4600240b08a031240014502d44510703404040345220b1000c2aa1950389485080c020520628885a400350301c599100f081040000c0340e01030016501004c2c1c3d070a0258540b0b80e07500c0180d00b0620101c440003c00c18010340090305500c0009411800381d4000ea50410100740c880383c2000c00d40d40711803040521501c0c03500d08010800c0b540301c01080b000034241d0002600010301000a02503428080521020203004424482032060451504861000c54041000f5010351140402c10314403082c071a142c4100c40c40c5c1560008038006015a50031410010107a0f542c2d00c0c000040a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 230698039 1250 230696789 230696797
    0x3010e070e010617060a030305030709030c08010f050903030403021c090e15190501080c070f06110702090c0c1b13050106180801140a05060d05010903120b040b0108010e2a 75
    0xd00000c0440c00c805000c0d60b45030721014010300c1d02034074011406c0d0454400744d5056102405240801030705400001c0880c0700a1603140c06824200004038052401140507010f540780a13040305c0e0300d60410802d00c800642c0000304001b20114000c00c401200c580000c098039540b1160b8040c940744500c600c1044000000001107140c410400c40c4c15003810f40300c030358800344a642540101341c0845d5524001c1005600c01c2c1010344413a174400e404c0500990072699807281624080c4000340300c4a00c0100c0e0719001c6140c286090356002488820107418811151389141e40d401202c5101e009001c0b4001102a09440385a10038040c180200c0081c40b01e540c3d40c034402410348001c2c40034220300020b00b21000c200d540040c0130ba1008482f44501031082911100d0780c0c0310040a024010704e070f000b00c2c0520940001182070041e441207034041c1c0c0717681c0702220031140010282c454804103203100e135140603100f0307180740c1c0c01c68821415503090f070101d020341d9500c1c4c0d005080311020030000000740e00180c28040789031102143c024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 230699289 1250 230698039 230698049
    0x1020309070e13030909050c070203030705150106051303080307050c0303090f061e0a0c020304030b070810050d1e020406051c02330c011103012402030915030603010e070e01 76
    0x70906a80c1e000c06660f4a824958402000592049000c000e5601650013040d0414070040b50303e03103400031941c00685541c0c02090110769580007840c0040140d01520081801403040341441840c006019800058040003800020980d000c0800418001e503c03540a40341620541401c69940c5c3c00d0920030541d44401c3c0301801400c2c3d202c1c1000140003e160b0144d03242e00440440a25900c985a500a92000c0e14607001c2850440c401408000301160416038587d000d001c054a80b20641c1c2018003045aa200480d007129014000c8c8001c240001003e40d101501b030740c03100303031282d02000710f60748005005000039510842d44641051481c49010344a00c0c00c80e07c0f0b00d0320031564a0414042c40c82d2a0580c84080034110154001c00c1481920078449000244120301c0f0180c00080c0000002945c110103400a0308128a0100411014843c001007465050043d04050004505002c80607000030740741301036442c00c90202000480440c0140d00c0941060002c180110180c98886850b6100014203010074850 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 230700539 1250 230699289 230699309
    0xc0503070602030c0c010b0f030a2604060f020105130308040210090b0a020c01120e0604080706060305011503110a050a05190906060c0302101107021e0301090503091e0d0f02120102030907 82
    0x49040d044c07910300ea030300010803005009030403280815243c11480bc4412042d1041482d0071035981d8103054000e90007031001d01050b81b0380d004981c8000c14002d0846500a09640b40c0006165501d00420b03000b406841e40304d1380c111641242d0201507801128130341c5941c0e01095150402003188080d0603000f05503041c141100380d030340c4281d81c103c1c2a40d0000b80c0e6640c0342111b0154006002241c00300d059007008250030390145501103580d07641c3c0d5685070308644600d010b40800a40c03401c014400c001c42003442400d140c0044881418036410b004c0059000b000d40c1c4100c501c26040c6000c04142c43c138400f585500100721000701007101c10360310b072006003428004c0502180103014449280404401c2c500c40e692004a806078100d00341020343c1c1c00d0080640401100406500428402c80c078169000d0050007030307140c480c01c00b42d03454480b4a014405032150203408071211010300d00d000c020f642c5a4100039400c2130341100c2002058111030020500300c0d11442844807440d400042000324044000400c1c90850704030800d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 230701789 1250 230700539 230700551
    0xa0b010c0f080c03070f03030903091d06010809010b120309042a0f05190e09150303031b0f04091506090e041203060b1b1b030307030c0503070602030c0c01 68
    0x1100c103000e0003400145201d0200003007002064002e800f41400c201c1c1c200071603240000d030741c8801c0350303418110a0460010744c80b4a5124101540710441800a15121403010042d40704281c0c00701da40c10004100030704108150b0b00041c0ba458094011400c8a20050014880d00030509015500c9920414109000b503040064101c0450700c84031941c40600840e14905030000702c1120304035510361300c200700d802c1000b506000b40d0980f581c3c03c6c189000f42e8040c50f03c5100d15910601d05004050700028400c403103001417007550b1582c50720040100c9034428900000507003401c01d03091295041d402100305024001202040100320f203411030740b04414001e0021a5610056135901781103070300c03041c6c602488454003400c5020800240803a130394000070304010b04010901545030140c40c00079400450100450304c150000428180c08103022a003c0c3e0245070812440512030040400d9591042c26001410001c2d10507130b5609000c3c09009450314150f1051080d0340d01d00703041170900701540202d8900566546000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 230703039 1250 230701789 230701811
    0x10121a040b010e0604120f02090a090303050c041d0604060902130807051c061802130212100e1f05060d1a10140d0b03010207060903020d090f0b1c0f050a 67
    0x20140003a4010007400c80307117000e003070407094801c191810004640190031640280c0059450100f06d40c41040003900001c1d018a03241402010b44a020342010303800c0604000a00c1200303002c0c20000d11405200d01c5140090301d43d800414000d04282c4e100d00a117a01c081490228030316882c1d819001c6070901030441c1c031065251004c006240792642d0012036410790360805600051032a4019844490410240880c1d004050b0041038100080f14030b2884503036400181407002e04070382084281c0103801d5091008081d030801c0098001548068a04000360303002079920400030340c0810300b40d009404042c00e0741e51180b40008081000c0d0494000ca030380001810301c003556203414110000b00c0d0b0203203542d850070402440c0480c3c05140703034031005c1055010f07915040154102c0d00c003400180a007d101d00000200e181d0ba9003002410007405844800c00c00400140c100300b407600c1030900030103030b4810440300c2d0340e11420580302200c04a60f0407900300e001403d0035891440c001455210521403a182107051080780415 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 230704289 1250 230703039 230703047
    0x3020a06080c0324040f2003010506030403030e031b07051002010e1f140114090708150907090512011a0103151208091c02030c011b0210121a040b01 65
    0x125030303580c60007006100242410700c0303400c0d1030114084480c002601300c0b810803010030207440e840c0b50a0a0b1180e1140c030700640c00c3c40c02c0d801c5501d40c40c0c21070140744e045505103000903280b4440900301804040d16904440300701c1070184202c1f00d1502c1443c0f00c5003000441c07a051641c40701900e1041a2040c840c40f070440b1802d41c01802203400c0210b280014007012102d41203460001c641021b24291181d80e1000c0c55440c81d840c1100150103004507518401050185504101c0509401840e820400c0b00e04000d03c001101144401980703280100d0b4000289d54544004685000580e80701c1c0350302061100e642c54040c2410f601c503010300300700741c080e00c55081202d02c0117400f501c0c960304ea1203c81801c1142e082101000c1c0391303124000385101c0d041c000d1401c94460001242114440e548031520407003214805c00318501001190343d0160700f800d1003004181801d2000038481c40403200a8041c0c0d1140809200c600c1c400d13125400103010b40e42c1e0402c583c0000181038100f0442040b5060b02540c80d24002500942c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 230705539 1250 230704289 230704291
    0xc01080105010f20030a05070c06050a0f050d1103010b1b01060501050906030a020d06030305040603060e04380a020703020f06060306011a1903020304030221090f21060103020a0608 79
    0x410f8440c2e000b284407668045951880380780c0c540000e40043c000c021a101001d0005040f4403405550f095251590b0b170078008100340e1307035511050038004100102c1071b4094001c60408106034550810386c0e02c850303914a6000c081c1c40029240b415144001001150601000c4054204003034446400140e01100f0800c46003201c00c94000c09001c0341c0188030f000340781e181000055500186441c405402d1040d000c1c095001e03524942c0080f80801c0010506012096241c0300c2d1038020180e945084113a0300701900e4545514141d91010400d01040c0b80e45e8120302e42455200b501c100390745008110301813070111042d10094000c4102100107010b190366070108158006413a034044c0e000280a41016441c06460707a01d810b01c283c13076070003c211040c418210506c144e0b45250080300c080d030314007680e00e1406280081c18441c64610708080040890f8403c200304840f40e00f0342d480540e09803203111a00c8442d000040420721000c1020000e03c9249545911001000c150746049a2007603501c8103040c7d0b12590262121b844c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 230706789 1250 230705539 230705549
    0xe0301060b09060d02041a3c070206131815030503090d050a08030921070f060e0703062307050307020303070e0f0306070f0e03150613060e010e07020c010801 69
    0x101400b01009a00c1d10700d00606000100c0e0200502d01540c5d0340311000340900c050101c035082003001c42c107250481d05c484d417518400000f01c07000f02581406160b5007550b1221400c01d200c1c4c218804a13004046443d03100840d00c24071903580d480c0b0b040e595a060381c502c000b6241e0000000083c00c004083d407010b007007039180c00156035001e8003443c28010711005100110300408002e80c2e0700c0c030440300c4000216000f44011400742e00243d01408c401c40000301141050711a100d00c40400ca103040102c03d0106442015202c0c115610610102c0c03101030480c2103030725180703280d0005082d591401c00030f103120031590702124500d942122940003541d0f4440005549a000885142d80940c20800018040324443c01c018020050010310614601d541040468079046044030420003103006074031b050b000d640d041080c100f07140c0c201702c004040d80b1200301461034130014041d00d0140148080a440002d44045800c0030300600180266440b803903a50754150107500c8001c1d01d06d10052700843c1c40030500b035403192403e503050315 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 230708039 1250 230706789 230706809
    0x1c022802030906120622020c210d05070915020307020a1a030a0207050a06141b040f210212030a090506090901140d1b1a0703021203090f07060c030e030106 68
    0x80211030113843e07031030300400c400d038080c0a200c00d064848182c81407041000e41d0301000144c6900710340791400d01d8042002d2108600751403414811203144e202004841c01856040b201040c00e44520b4410345c1d1081d80e0f81c0205208103d84186d880754290f0002c00f40460724000c031015101c441c0c2da4046190010946800543c105400300005101c000040c0c000b414158400e400300c610514031511083c040340c13030700108500b501040006005100306801448180030030750110040c5054a4450064034580c40791181700d581000600f406032141000c000950301241c1c0203403e100b13075081c1300c2c02c0c1329881791b11262008010481280001c50301d414141c00781c0e4118000039062100f10703424811504100394440310342c694080c400303110000000d117852031180541103800b10076007031075801c10b506007d04591001c2c1103080010188641008240d0001d5054007011021450642d02e8407640140d03400c0440c4100000754a20840400081d9143d0281010580314020f541d18082c90007160304140c02d07107190340326600441e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 230709289 1250 230708039 230708047
    0x1094103030c0c030f0304140f010c12150f151103090109090b0d0f080a020c0402070c15020f0f03030105120a1119120c090b010816051c022802030906 66
    0x1140c030840140103c00010f012203090034100179100000e9441140c0442d42c0c0f08085c0a02c408211040210000014440009010351038042c24000c000c181410707900c00d030040d1943c00c0002414030031100d1201401480d500c03801311540707075400d24039082c00c1c1200c408000744800111050a40d408820381e00d1100050b92114081c0d0324140700c0c0d101034103040443c00c0c1d00241440c04400080c0c1404e14524060b4841d90095895812003e8064102150301c25030328081e900402400001885030b44588080da1545544e140961200a0781240350600024427440345208004602c00c0d00d84000000c0c604031402243c9a02492140d07000c0300c0c0e00c508100d02c004081d440d500d030460102e4608491210040151400724503030240d075075072079240024035502e01580e030f40b03107801e9050010420a000e4205540070a0800c82554100106030103482c594030550b480c1041004500311441c0303405944404e031400500241035459a00e01d0300c2600d605080c4200400704aa104081d4102c1907002006407a02c0c003100400c3c041c00c3c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 230710539 1250 230709289 230709301
    0x250b0a051009020313030206010b04061b0303110310030b07050f0d0c0e04181203060b0703230c010c0e010815040209060c01020301030f0611190509030109410303 71
    0x10384000741c1103072010455003030007207141c401620185104040003102400413003540d040c040e04188060b00300e5012650b082105000143e0059604040201000c8190700b4030242c9007800c40007465007a4000070390303800000034003030b0074420f021140080d2405825a08840d07102c009041d0307607a105040030404180400d02002e4101010380c0d1110164a401d170420f80d0010b1082c00010f8100d444400c10010744011050030081800f84150703240750480102d0078208417882c14924440b1803801840ca000701003108990540460410010740e500d214100103403000e4540510400f014040d0194200c1940018007405c1c4100480d23114075403c130702600940040040011110003030002030361240220075004a000c011203088060248011402980500311400c9040001d01e0903000341c8299418034101c944062005a44508494401c80c90030391706403c11070f0f50381c040400030a000d409a40380c0604015100c4204200e21801ea0001d510000344c003e243c01401040c100040f0904c003020006048540d10600c00228 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 230711789 1250 230710539 230710541
    0x110609100336110a0636120b06041401090e073309050604050108060f040903031b080103050a020d050718090618020f0405060409050304080102250b0a 66
    0x501c01a549400441d0301040c41003601a0a5001000d04002c40c0a15446050000541d0040c80445040300d0b021006454071a00805640d160b407a44140c040d00340155100c0020107100722800240929040350b01207560700100c0c0c03c003183c5d440b4161150150400000e0041c03a080c0f00701000580144583e403c82d03400c02d040c020081520a04514851140000c04600050025042c410350000355010710124490b456030780c41c54201e400a85002d00c02c0805040c80141d1344c0205441c1a01c40c2807905c100284e80348000991101c8092000507040352030078294509159064200d0b42074810048049540c110401508a40700442440050180c0e08100071400041c03508141c8650124003c0044506060320b850010354965120101c40420030b035669650030402400303000743c0302c0c100d86194a403d407445080d0085850030726041e05407407046540c1c1d0300085550b90b0381d501030140981c00c20202c907107858440b1000d900170340c4441c51304014501011010001c1c1c80e00c5820501a80c1d904c203280504c0c603120001100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 230713039 1250 230711789 230711801
    0x3120807022b030e0a110a0b0c12090103020f070303090204050619090908130e040519031d0102030c10140c0304020a06030207060f0e0c01030c090b0a0e0a030c030803041106091003 79
    0x201901c951051140c200108071584203540a000c4500c2d411b014281000a0040c161781b10f001c00c07070010301c604580b40701c0100c0c0450342092641d01f902c0d0b8404425004034000d11510300c0c034812400e00410500140f41d4198044c0c0384082c0700303507810845a02c0c1c2c00204018911048010349007845264000d201d901303113507044881c0540c0302d00e400504010741340040300608a07040d000902c051924004100c188102080440c4400a40709042d030036400040e100105040000c030281c2030039a4182e24600c2e0280d108004030b5144038111410303112900f5800c06418060449002401c1e0001d502c400460701c0070306d0500481e401164003d026581040c41e013001940650020700c400d0b109996a0481d42851040d82d0141c401c08091410245c419003100c60000f4045480d0030391101e08228454506000c40c440e05001c403840917899042080405049000060720103246400041c00d06c01d07410700020401182001950140f4400c4103090780007100b410070710505016920b10300f54480d810000414109010394054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 230714289 1250 230713039 230713123
    0x807060603021c060b04051509100b031005030c15160602090301020301180c09060e010e0a03050f061015020c011d04090b07090e0402030a0b090709060312080702 71
    0x21401a03920b400242d943c08440d03005486480709210b2940402c06148250001c4e2102210304010600b4105c88250200c00f94407091400f9000e42400f190311020700b41c5200000388424000140c3e00d20f0856544400f01c0024400c1c50b000348102d020003c0e451406414800c2c00c0042614000c0c1031001c130240c0501c1c610841f0f402940e19a0b820030008603d92001c2c0000d40c040c0c00c1c03040c01c40d640034008150380d1044850000e903800c1089090f003018040540d22032610b414500b0b007441c1c4040175009900006103050001e610080007849411401400c1c1c0c075010030701030711819a8800710004d4554172849607640c0c0c1c40040700c01005800403900300383c9a41c060851145002d40c0324142106506203a004282112180c0c0070588000c0542020001c00903070000315600600021250003510b410150b0109a540080c6840108102550300018002d06000c000110041810300400c1c00829603900700101c00c032031a6842d81c0001503015000569043c000a00300300011a02040142c2461042c141e19807803c0440d001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 230715539 1250 230714289 230714291
    0x3b0312030a0b010c060e0106051806030606060f091f0e100509040c050d0905070e010503010e03030c03150a030309290712050903070609090e0106050603040f021809030d140c07080706 80
    0x90130012410902c220399070742c441e1400014000d4140010420f01c211981c2824405d040c000c0704001b203588000c681241c00401c241e0309142c5a01c0c2c4401200c80601030618aa42c102000b42000c1040480c0d09556103101d95050329400041c1514a00340280052002c2414010403020072041c112404c080e40814002c02d100d24000f4140407056501c402581c0c1036200c160f071658080c0c0030600218030030700d900a00415046000f0841d02d132001401c591203000062641c4100c010120019580c06d80c07060f0b0349010a0002426071806503124580600603003424001c0b0100508901803074020409100c1c100207842d1400501a41800c0d92560f4900c000c000c10a0242c04100341481100350b961402c20614001e00015201c80303207181e00300403504044820098901e03030240e0400500b0401c0f0b8581008607074103d038021420845000080c00407902c0700300c00d000c15244071000c003010004865404005046010740c0c0a000340140740711035144110040b002c1e074022102050405c22400000c850200a000302c0d48034102c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 230716789 1250 230715539 230715557
    0x30a0308150406060e12010b010c0314040b1605190b060d14060c0c0f010b060f0706020906180907020c010e1002010b120106080f0a080306103b0312030a0b01 69
    0x41820340b0030701d44c404004540d100c00130071094502203150308440d03a0a40c0081040f03a4804c0e000800ca2014003501030140308a00841d903076800e2805085501034110000ba01e903650000d10b031040b020f16103e040c00d540f5809691058504038900c0200c01c070900b0741100641c5000e8680c8400c000b00016100c034200c038841d0a0103039020030448103208880c030a0408812207626803000b4070710715080000c1c8441c01c0b10283d2418510661950b80d01e02a030b44a1510303c080e8548400052504800a100305441e0743c0d4403100c00b00351602c8010719102c00413203080c03007070f03507105117540315010143d98500c5041c0381e1601081d20004007482c1030034450880244008a072001049201100e4042010400104252001c80e51101d0083c440c0c208200005400c07201d980c0000c00c500040d585a1000d1404007600c00c0c0c2c0709400f03e46100e00782c02c0c42280b5243c00c0381030050445c4190004510901c9486141d400b45800d00300d210b18280c240c610700420040f45140e61081030703518550390804844002c00d2040c0704241881103104c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 230718039 1250 230716789 230716831
    0x7110706050c010b0d23060f011203050706090b070306080a020a1701150b0c15090a120e0306130c0510020a080c0a0b0903070c0f030305070b040203010b04020f0310050906030a0308 79
    0x40130100f21030140010001e003028441030340e000714503c12210480c2c7d5000720140100003a100240c24110344088691406409191408440d02e1041040c00345c41117081810050900014060007805500541c8007000320b00d5442105540f110880707031001e50b003c04072010800c16000c041c8101d0705841d016000005001621000f80d8142c4071030364000c00c1c040e240c0030441c2c009044042140840a11850101c40400d140000c000c603a1900c0c540d000410004000c0d0b080229a4003802c015068074070014241c582502c0c0c0400b000b440740a82401c21344400350080d0b40001d041c00d00c582c001240701c140c0e41c0505440715040e2501189944115550005840b880c02102c02140020450030f0207402c0540c042d60391100b25050010b01c0004039001030b102600c0150701000001d40020441d1026544603811030800e50741c0c0d00001f401001010314054209000147c250f00741d4121400031480307040c100c1032071a405611242400300c0844100c401c81d401d070740203c6562011070300505c14640c1c410980045052102541 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 230719289 1250 230718039 230718049
    0x28120b1203070311100e0601121b121a070c080c03040308030f070807020c0604090f150b130905061513120303020706050f0f0c13171507110706050c010b 67
    0x100e10300783c0001d40c0801c2c1c004040c2c007040c4420036014a43c81e405020040780480c00d01c0e110340040c8034280c100648490740c403041005646940303015441e003510607001c3c982d5404980c441000301d0034044410f0340900b60b8040d035421075004841e01454091780d5041e41c1070a281c0e01d0418a0340410925665403000344000000601440b00440c45440819845159810003c1006d06942c202400b100155000f203080801582c4844041c0c0d800c58400c844081080e110804c606402041d000045a80d000300c48400811400711140080c221032418100800c0c481f0356403200d02c4101c40003503810650228540010390000c0340100e01800020040084028000d50340787c481d0b846040341c03190110080398000c141d820038840a480b030300d94403407204036802d1450b2404459001050400810f1507042c90340100d00a2020012001d07203001400b02c0d80900c0c0882107000700540c1da10000d00100ca660171020100280c0024402c0c11004180030304c5800602c00a81003d40603540d6820000451400e50750390544030110303a680c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 230720539 1250 230719289 230719297
    0xa0c09210807051e07030503071203020904050103120908010e0616050f030a050118050411060c010e160905070203040b040504020f210708070e130e0f0d02010228120b1203 75
    0x40f4000a00803241c413100040c031007001d551144402a041403404002080001c0219a081c1d580502d840c2000351089400f5002400f402030410b81243c508000441048002c800c4142580e0858545554259690000398240c0e81c40c41551062a00400086205080880308001e204141030504500342100741d2000c00c280d80040f90a05641c0362514010040c28018040042030210b040c2d034103101a03e00b90301d4071500606400c0301a800740c1c0000540a174045429401482a180f4031419511020324034034050103a554240100d0343c1c0e5034680404103a640303000104441c11144030501c0c0314101407038242008020340080484040542080280080705c0c4403c01d50030300300072001201100c0c0d030306000c00000c04101000b0302a0051102d10003441d16030b96230300e80e21690014031204011405048500041e0304200c00c044107040320344540c1500007402d0750190081c0c652180300400d0130b0381c40300c0035509042c00011b11452010105041a041507a03620081d00100b40300b4030050501002c0074651440039140d548 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 230721789 1250 230720539 230720543
    0x504031208010f0e040308150f0a0608060a0e07120504060b060c010c0e10140c03120903030103060c090e04060c11031309060b12132a0e0a0c09210807 66
    0x42900043c4203a00c11100e2010180c07a01050003a010320b8940e60203009503401400c03200020140754a2454240d880c95084960b001001d410040e001d40d079008050150041039074240d00c04c403100140401c08002d4040458802c2d1140e0742c40c2204c022120002c24000c0c1000b80064580343d403188905199600e90708003c0105000350000058981d400840003000c00c4160510b4030311034800f007421002c20503400407690000d11804000c00da640c2583c03192051440c403d40282c000c08181c03a508000111030040080d6040784c0c06050188150300c03031154200c03054511030050f202824119404640842d00943c0301c40460a102c0c02d00c8050518110400780c5560000300d10102c0d602103542050164003070b18000c1e200140380480d8001d042801810305480e004030010014100781c40384010030010700c601102203101400c00707903a500307041d00880c8a51700c825000d2800f6a83d483e000380004519808614440c1c5800030049a4800d620107041850540b4404110340b19014840d4004561034046040c440080c02194 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 230723039 1250 230721789 230721797
    0xc070b0103030e040510060807031812050403140303040818010c0b1801140606161b030609020a081606081915050901050a0602150a060e0f06190303020c1005040312 72
    0x2c048801c1001317880340104052100b044880d4200301080e040601e007500b0100e10704000c1928402240103030303c007050401001c0c060303400a00e8180c1c5884e400c54010310a49001e01444030f09104400078181e81c07448207560050402d0820021444070010540812881d440d05240140204289407030301000d404065592002024102d00d0607100040c0134410b45c3c6a850141643d40c2991420342e0003d2901d025000058507495003d00d0a01c08229001785c0310302c1044134040e08851056100e00b00302000f403076500d00c200e00403c01d102002c16080800a03a80303c000c904121641d840c01d0800d01b01700d400320405081c0000514074402d07030300e8205219001e864944034800441d61406032030710042014100040e404a40038070822030043c002c0e590702107001c40c0c1000034644d0a2180e519040e140b800101415130203c11050301c0fa00030f109440d00c441c4170441c001c44084841403548004c6120741c7c99000c215110003005030340a44900d00c01400c0c0210140000010b0f400e1803818142d40b41c9a43c041050806404d00001e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 230724289 1250 230723039 230723057
    0x90d08210708091b0d0c12030c02010201050106080c1c0f110903011104050307170a1e0b01140a03060902040e01020a0f08070503040305040b0d0e0d02010605011d010c0b0c070b010303 80
    0x80c5034480501da5100300306000400d001101c802d100b484484d803440c8614040c04a41500e40c0901000f80040300041011410b0403800e8801414001c0040d22154000c81c0194201000020f10074400d1010500410011501d00e24110805800b0409181003603a07255045842e801e200da0380c0f1070350780301d4401601c1c0106002665075101204141c2100c0c128070b414600600c0a000038489a10000303100e0003034500c21307028200c0c90400800f20707a140041480000700300a1050413401c039022004100c0c001c26030310905c8035940036607c3e0403207000030070030007111581c11052901c000c00100e001908041203050019000040c850100c0748a41d0036640f1048482c00441c0e20020190070681c0d00110160b03214450b840c0036411400c195a004106120f68440e5154403200071401408000041c0c0c40040c00300700c44030407102d044914060181c060a00380c81242d01082c0024011020316600d10030103040f14405030345000c1d43e6203441d034174412280000b600000c5005018450500050014102a80070b540652030344010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 230725539 1250 230724289 230724301
    0x5040f061a1204120c080703050a030f062412060e06030d0509010e04090219091d01020c0706030207080706110d0c020d0c080a11030d02091206010803090d0821 70
    0x70345400035051011022003000300c060300c0d20b4030012054115520007210307070301000544021604c401c4580f8010b000040005291401c15400500038103031684a42c81c01d00c4101d4100700300b07e088130000d1043d07860403200c001101000600b2040d002500e03001d00e0400da084011500d19800403203c90f40c03c20901b1051803001d0140c585400c01c1507042c1e65a40f031501601e0300d009540001d00007250725003218015038540401900f15520f1454850304482c00402320070001360b45480e0744000d0040391590340070440c40900441420101802115960f00c800d40040c19498a8840e04400035031003c0e1064585031024003c03500000c940e80118200ba00380c008101d07448040081200c2c003210300c0c600098040d50b20800d01c4c03003400c54000305000329464001c4181a1191461881640c17204800320030080240030001e0707000b11483c0d41d603010708256a402c0d500c4404220440d401540c3d01d940c28043d4008a50003488240741601c0e0950000e89041c1c801d8511b14105215103004c407208420000411540440d500b0030040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 230726789 1250 230725539 230725559
    0x21303110a0b071110030e010f05060f03070518090a0c030c05010207170a030e010203160303060806090601080718090210080f091605190f081e070513020a0905040f06 73
    0x80c0042c0340c156860521595145141d50040d448028000c041c4d40461040a80c0281e2148150030020002070003900c150100c03400007458201d502c5d901c603030500420204a03040001d404015a040a84841030460b407480003d20318580003800c0115622454405800050240319488000e5114210f425a0ba604050000e07003800200c1d00031140c0d0803d03544007036811080c00100200600c1c0c06050040484150381c00403811407103011844041b1301c03460540e800815138141c3c055021222410155041c0351600305403161580002e00c1043c084d81d000c00400d0101801207600290f100043c2880021a001c1a0340444c4115804200400c00700d81c02004000d9240120410039a0150554019103841b07411a0b811408440341800750300c0c0240d034282c003000c413a021410402c0d000ba0001d2030381d44074042d80d10740c2420340e40c0c5c14100d4030355482e20180c0902c194a01c40007581c44c040d114000c0a03c8017803081c104243c402504030305200000c105031070500040c1274944e03100303030f42c03440c04804800f282d06410b0103281380c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 230728039 1250 230726789 230726809
    0x5040224030f1303090528080318270c190509130b0603070e130509010902030d020f060c030604140703060812090a050f061333020a030302030a02130311 67
    0x9462056203038103901c0040e03400410581a1942107c3c0d0244414401004100415594104451203485c900000c10810000405000c2803080110403180d6158040107100d8001c4010250440c40340000ba80005681c661501903540040d000f15949e040c445018214882e080408843c45c0104000144000c61414081150008403510501c02d100e0781c600364001c039400303100c014804002c000102174092069501d07030f06528030305000004140a00d08005030294028200e01104a10a20490071101c207040e002081494004203070801410039941c0d901100b8090b54801846290b100341c1e00d41e004c01c00407484180c00c0b4041e15041e540012058184101141740452109a440000c034041c4500030441d0b031821504801d030340d02911186041000c55011034403502a04800d1443c104505002044651030341d15080c400c2c0d00a418040c90b4581489105846201c0000003503005800c54900c20b000320340a5002590070a81c4202d0040c5410028800912034410359042215103181101c0b249005291000c421 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 230729289 1250 230728039 230728051
    0xf0f0201170622060f0e1e0f1b07050a0b07080a0212010b0703181401080a05010506192003030402180108100908040b07030c0605070813030305040224030f 68
    0x4600c2e082c0703400081d0108030540c0d680d07185503076070303122108000000c0e402590080c01041002415103840d0703517100b540b0140032070f44150100700c1c041001000e043c6000704203014494815410759183c80701e03464110b40070a88000304089400801208000800030000200814080c010010041c101460020030982001d4030507008140103000822118a841400700c0c1120340d40070700d45940707010300d1034213941920303c55507024014134603c540040d40349c00d5030044c09080074090fa5045400d988900c51042100c0c804c0c0522904558180510302c0c03040c080d00b505074070301c3d00c035803c1051040580b207002c14041009e0070680e94882c0c1001c0203010441c2040080300c0c4a820541c1745400e5658108140c240d0303541c241880390409180c07605c1e4008280040501250f0281624680141d614142418040e049400100080760498a000d00080c0514031965807540200255022642103a201d13880440207400040d00c1642d109042c40303180c0351240254000307200f0904890b40000c1d200d24116184241c02171008100b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 230730539 1250 230729289 230729327
    0x40309050907120b0a0509010e0a110a08070c02010c0605090a1403090f100504180515191a04090e060f10030201050a0503150d061e0b0d020603070c0f0f0201 69
    0x500c4141d0350001419104043c100d003000414056400005820503035940c800c0f9040420034001060741d46e51104528404e00314004244516400c032030b207164040c07094906d128000740c01d11011520b501d21404840313011600514029561090136200d0504541c400e60346902c42d07902081c4d4071800c1201504c01844d100074640f000d5410700c000d4001013490011040442c4d84104950b031114100a4001c1050310003400d5407506008240e4061000705000707040039607007500300314084480a803440c5480c0011001003070b10106003802d50b91800340e24029506a0701441c03804104d085c0400300b500304030b500c02d07142c0000c040d01c0148124146000f0050a440c4081d00761022543c8416082c80981d0b00030044408010b1549011541d0341c0d0390680c40d20b0200840c9000c164440c078004c07031110a20031990018000022035400c0700e401c60383c0801002c002c03603801040e0f568000d0540c6445d40054075003440030b140c1c001c010741006101c0c80d41c1990b4800d00c1c003168910485041c600d8071841015945e112420310b80752100515 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 230731789 1250 230730539 230730541
    0x1a150307030b04021206060703051b0105040c050d030e011b17131205070e10030b1816050a03020d02030f061311010905130e0c0607030c052509050405070f0e0403090509 74
    0x101056401400031b1003240a41c9001400c00100362040c0101da01c0d119401c400c941d55040c42042c2e0034082c107030941d0181c803207280950011607103107420441d00c03a106034503031140c081d41c0c0300d40401034900038020319100650a40002c0c000000c03a010b415225103810840001560310481c52070b0010138200d042e0001076203d13000c1800701c00021400508041512807c00c12409107170380380203090410341569000140040c1e200304c1480480300003102c0226000408100351422040186d031802030482003481940d0303000390f5100c1e0400140c148130340d800701031a002a040d40c0c11400030742819803400c3e100766074204041c0d0381000590180300c11903100d000000004d280c420145854200010850034048041c0c550480e5204041e50089400b000301c86419180075001d43e844105600b40500300089034072050ba094001c0d05401000c024603000080341c0c0802d002a003c8000b400c16640f01d00030304006000721201d1041060101d0381a84501070034009000c1c011405003103261502d002045004213602580c0101244c00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 230733039 1250 230731789 230731807
    0x1051602070e1b071101120c091707090507081905131b0e16030e0105010509160315090b030c0405040c0b07030302040314010603050d0509090106031a150307030b0402 73
    0x1103042402c603100c00aa5141d5516491401076036a0036070030046401100004000013000300343c500420010030f00340c031400e485a01000c0c0c2d11050fa50704200b00030010342d1429090102c2c10341034000103d20042c14080b10341e00c0351a10702c000e003100e5040d90008045654041000b803000ca041c840314015000d801c1d0700b40194100b00400750403078030b0305c0c000040112001c02a0302000300a2031000e03400a10b0349082900c40340c1000c02403042038101c0f800c3c5d9500060700300041d0210740c1c00140212412544090319440b407554410282d080800809000340d410191a1010002803800c1300c0e01c408090540544c0010340711415004040c0390580b076140072805103082908004c04212001904000c540c011583c1c140d44035403d107000c600a1040740c0000f0254502c15075404046c030015400982524401d104a60310006480425505406060910b80d80030802c4801800094801d4200544030000d014551925061440005003e0900780c0d031200c0840001208102042b545070240c80b069400544003140740080302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 230734289 1250 230733039 230733043
    0x7060c0b0c0307030902040609050105040b0d12030b01020f060403020c10080f1b0d060b040905091504031209050a03110d03020c10020a0c0b16030b100206040f0c090e06010801051602 80
    0x204030440941c00403000940003400390b00004045030307008004001840d04d440c44000281001e0091500072490007400b4080350a080c81c164032580c0d00101da4000c0903001c038404502521803043c4490440c00f0b402c40030400f078003041103d0340c02544a90064148003845506100240900407068000c00c1644024051103480000c0c82d2030b0003820504141600d80710348400701070300d0301c0b51201130002c0d01d15007100000c68200c118040c205490001100b400b0030340750b01701466514a15001d00d99032110b61400440c1c0040d00540d104441c0040c00500811040c0603900e40605052031100d090700031441011241d040707002c09004802400900c0d050444c1004004000c1c15a10740292803071301004c03640000d01c83ca6032030207025014032a60b440180500c640c50800c3e201c981e010100c620795400309081c052664803515192070009100580780c5c0c02000f49550320385480c402c10b1034034003042c0e071800542343c0c001c17507924002d01812021140f030b030000300900d515101407103007151001820359a000d12843c4a900c090303540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 230735539 1250 230734289 230734291
    0xe01080f06100201021308060118060810051b0d1a12031b0c0303210c03060d023309011808030406050f0d18030305100b1b030f040f030507060c0b 64
    0x2030b81c0b0368014108819050b8024410110451003408000400040e0980000765481c140e80b1444000364140c3c000c10384640c190b038820b001d109419007050b500b044040b01c50380e201e00d9000c1c9a8800c08883c0c0070b41c80d085414954051560003030240e032140d440c0702540304044840d882d0351200759030a000ba41c0002c0079050300ca0080107903c200940c0500089c0800c0241040032404008004069a5032100781d603e042c1e0361752541505100b0344281030000180c8c0020030409a0703115600103400c7c030b40000513a81c2000300c05100410801d4507092240d8400007030042c0d620300c1c828000131034000c2c00c1c0e40d52194000134088a00740001900c4a42e000141444108008070a44048406505000f600d030741070060004020300030340700300e9807042c0c0c42e0503800e6440c0403101d540521240d01a440c2005151280f0120401804035030094690301c0604201009040186400650620000806032420035000380246038031944039a00810001c007141c02e091040c00b0080c0118001402d40d03081c90034a042a55940800c1508 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 230736789 1250 230735539 230735551
    0x30b030c01121104051e15040e04080f130e060a122001110a030503010e0105092a0418020409060e1311010905120d090f030201020c09060d0218070e01080f 68
    0x40ca070020300c0c11550f941d41c1034501a101c001d01c80510132100c9040c20381403074026196644100c4030b1f070709050a15501c40086a00740d850b880f00c0d0890799922603d80020ba81d00850961007240307010881c050a0600e058103201c0075102c09200b40c180b80c1021400c001c40c01c9007581020f0162012001000001901d0744220401085038401071055500b80304c00584440c0281d40d4031040d503004481685040550042c003c40c142d0b03000b02c401c50710b01d0b41c0360402e20141c900b00b00d0f500301520181c0c0c18002c007842c006641d840c21a52a448202d480c05441782042400080121161035025402243c04d001d960030030300039140074000700542103403280744c00700043c40081d901080c0030702208009020400103034400e1038104007610002c1d00d00303c3e0914070440d8103a82d0b0307030140c1c214500141e142c80010480700004030701c07070045070340580c0204024140c90b400c00c81e1051028104c0e66100c00d41680300b42c01a224000003800110641d4440e60aa14080c80e000e4079194110700c46c64100101d4104004400d0201c2001d00d410075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 230738039 1250 230736789 230736791
    0x30304030b0a0b120a06050a1407030e070504020a09150212040e0601020705040504110a140102120c19080703030605152505160515031b0c1c080106030b030c0112 71
    0x1e103407000e00c0402007030301d1414660843d2041d0742c507000304c010000c0c1100c0314030b00c510700810041c0d17960700e010780c12070709614180a014002c0601064003540319420048582d403040701507070501940c500008089030b100a40344000718584000802903540040403010803110503001610300213140c60321208a6105600585403d10311180c0480c040d40d00c02c1140801401c0c014008000750304081c10f11803510078202208a214203100000424101c2c01090720401c000c01c1038000741407401e50320b440440700e0381041141d0326003413003022200c29501c04085031842c6840d02558038155240000e0800030150b0b9019005180100c60840300032003260200c40855003030380e40d42508030170324200c2002204003080d07000c070024282d40b10300c104051240031940c00280480d01c088800c02d0040300c54403d0078826000131290344a000d4031001a16108000300b60003812025505019241c610900180c52500080103240500024002100600403141c0502c074401150408070001c210811080c00000c009110b512a1a0003031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 230739289 1250 230738039 230738041
    0x60503060621040804081905030d0e0109050607050301060f030209102a060507110f03040909020105040b040602010516020a020f010e040f09080306010305060612070804080708031005040e0c030304030b 88
    0x98612a49000002180a03824442030f007414203001c440c81e00203025000241c05101d1414403075211040030000460350080146042aa000038171100400c00460003c4255403076445190003d5014040390303209065584035030707890394103209004000c5c8060a9694042c50300c10400701050f680d91029040c0380035541c0c50820042806503183c041c54200311540c0c01181c0c4211003a81040050f25002644110f80981c0d400a0804841640070354a050110801c08560030410080c8a016003540242840d6801810b0181c5042d5444100109a500542c0320200607550303581031055104100d80141500000c41c4010100008240c0000c1c0600100002e014103000041007c04140e41711038021812207110080200031014040c10300181551080320500c1c0001d142c100010114984001622810001500008121b903200201680c0c0c4450142040d281440103020800000e6415002188074515001001c8661450823060105030384400d00710a0881c1c1200300280155200001a1821250000110711075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 230740539 1250 230739289 230739307
    0xe01090b070b15030a060c020f0a0308150a0513050103060605060c25080f03090a0603051603020d0b06160c06030c0e04110d1b1e0504060c11090924010605030606 71
    0x42032030f0301165054080d80d5082e01c00c0c0a1154081030710826513400351884940455415600c8000c1800700034040746502c000315440f0160600607120110000c0d003500748040d110310006115401d0b18403020500b40d1508014002c02030580142e42c01402c0544500d8100084054102c1d11a040d8000300022620700500d962106000d1034080030082601509580070034049000a40d00e030707400104001d000d00080c08000401c0c900c24441e083c808d20981c5107904600354130010450180d4030899894540395100c003603203406950341400401300e403606142501d58103989403600010440322035200b40280b500d011b44c40100700b504001c0225189000300c0f40042c0024520083c09494020311004140c00c0740342044010261400c00828181e01101c0d8031212543e070018074209500d00520700001000400600c42000700600071018800303c1751161110000510f95500419090b88003210b1440860f4405080b503e0503070404401c446040740140c142e10550340c10240e02038101c1c4006020309004d05000110049 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 230741789 1250 230740539 230740561
    0x603060d03081302060301060f0e060c150703091a0412080c09100c061a01021006030201050d05070512070519050301030f080c0a0501020c071a0702011709070504020d09030e01090b070b 81
    0x3e030507a0003810300d6200c2d61144030041107040d5030041000469006011031010340362041c159045080d00030000d200c1044652412603035081c026141d8030605846040b641d00080001100c0ca04d900781c140002029442c250502031060241011a00141720b01141441000c00145080320301d910000e540c14100050403a00c106c50640c00303032102802141c40c00300c0000e07180c05503508660b10750400741c1c205e030307090202074150310205e0310903201c001e0214600300503843d011003a64004540c405a50701b006070610f84514045080d0b407000704c0311400040d400041c60a045050b01c83d01c46c0e0100090700d0960f00319810347d0342c0c81c000000101c0020b42030365800325961484540400990302e02503032000003903440d481d010000356900e0400303014001201034120081c0d2120451074065903036036a0165100c0b12100d00507440040c2980e0f014015121030f015070070340410f05031241c0c001000c4906030808000343c0c2c5056400c00a00c1c03000740c81d060034104010310104004601c48e6109442c145504042e00744455210515104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 230743039 1250 230741789 230741821
    0x20304020d0224030a0b0a1508190603080703030605100c0206160f050318030c010c0503090111010b0a0e010302040612030212160b010602030304120207080d120209040513060b0603060d0308 83
    0x20070004400002c218030140d894120f1a840d1074251200540940c07560010b0023100340322101d090010700d0b80d0b400600641c500842001d00050301d4800000e1164403a100c1480301d81c00fa04007640480e446101c100038a04164000480c1e0031500d1a14002001050340001c91520822041e110b1540c41080c6030000d01a201d4044000d0660010480c0e0782c58501544031400c0c0358040e00381c24805d000304080f540d40380d4000c03005243c402e54040c014602e405100c0300107403050701e03441c2e034030112642d600c1c601c0300c0b502d4541e5441321024002080c0c0380801589144108402d03102103800c040d1098000a003a0000a900080c1c02080c400ba80002c01d900e03603480e24113000065210380c0b0701a001d04840b0000103040398002c0002d501031402003205010249403003800341c1c0e032641648560650765202100a4200d80d2180820742c0154500b80c0340945000e1211000800ba0b81050300e0a0110011418143d0100109445040740d03011059032201c0c11454500d00150350b0200c4200d001d03045c0710f000760000303c4c500d0340c1034015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 230744289 1250 230743039 230743099
    0xc02071e03031d060c06100518040b040f02032e020702060423180901050907051509030a0c1e08070b070b0c1b1b1504060c0c0905040809040c03020304020d02 69
    0x2640745d40c69030401e00d9441d0303002c2c0c0d540d0080e07898420000c40d60382000c91060300d0b8032701c0c0c019007071030a03448580da1304018000003441540c1c0756030702c2c01d9aa001030b9410b021000f00d16440301181c01340d121604020b611307071640c1c074040c03319414810800c0d10016140d140c217881c04c60758001110142400700d601141041030703024485950040c0c14085048240f645404424044d10342d40d4001c0201d980c604141d030365200018014a07600182c07003030501d491403a100008041d0300b10060161802080c50b6034451170402d6594103c007800d0b0b21030655603c1001600c00100004010744001400a1407070b20b410100a0322405601500070340760400040e0281101000f25650307044042510101d060302501d900da11a07840101c14203001440340e10708170152500c55100b1490004c0030b4504d5281600e000e1040e5070b01540e51000701c404c40e940242c00604440c4a100d0548514060101c0b655940200c1c410082183c02c011403000a144c4103009000c050b80b40c1440310508503a0580f021342c007500c1055020b0741c040b1a20105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 230745539 1250 230744289 230744299
    0xf0e0c07050f060417160b15030105040501060303230a05070c080a030e040f02070b060904030c2001120507020d030905070b0d0905010b0f09240d03030c02071e03031d 73
    0x1607040b400d000241e01449903010344030315041c0c0e0f510fa1140b01414803c00401c46803010b4000140c0020602c0001c6403604000d00c500f44450014982000c1783c2515030071107090350584d40d00c220130001c0c5500101d11303840c10038070080101c6490842840e8041c103805000765010402034003103104130070003e404e180200503111190446008080034940103020408110340c5d0381c000c60034008050751120042c0280c80c00c0c503a004c4038047c0d145d0b450806100304010003c0c403c3c2c00304441c2c03000b080042082201300700808090071803070176046121400050000004d4002000c2002d15080401c0790b040e43c08980111500c07101e141c0801c040340c03141065841c26905070480380381030400151208a41030715a114401151041c0003e00003200f140c4104124030040001c2643c000540340300242245a000c0c010118481484413a00341c1d6901500100340048040c40303007200800c0c1c1e56480d01d20b9641c0c04100680041015079100d0301010b1960307034560f1400c00c4500c4001d080c0082d501e00a0342c090890011840050742c0502 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 230746789 1250 230745539 230745553
    0xd0f140705030c0115080a030e0a09060b03091501031a04020409080a0207080115031a0c0403050a03080604050901050108120a02120316080a02030c03010302060903031209010608070602070f0e0c0705 87
    0x1000e03510b03a44401030b0520690f1074048003070f8081180405444c00c0f0b8641901809140300c240d101611019000b5042c00c0e800040c085000c03a9400c2d1500c156005010030000c100c2e2a0b25100002a190070440058000810745807001007001610007180320300c8903002180b10380d64a48a61020030301030b02d60a680141540400b003a809002a40020340740c0480d1851002131188051041326160b5194240c0000342c05604450044040c040000b009560000320702154035103030540e240c035080e0605070000003c800081c4420140a451b1406009440e004020540204115454404903558821213018404206440811403201c16402480345e44000e81200851954a25000c0801180045002c01a00c0440c200b00003280c2201100e00c240c912500e41e40502c0c614607400c40d000c00c03103550828005554103200c200003a00e085003641082c40e000358170f100000301d83c145c18410003508003001c903004007003107610110003084260641c1003540203c0d80f08203c1c0951039240c01d41080c00c9446250301c0646140310f01d00c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 230748039 1250 230746789 230746793
    0x61b01060305160b03220203030f0f0403060506031c0f021501030b0717070f0513050d0b01051003090206031504060f080307051005070c171b0109020405180d0f1407 72
    0x7003040f4901010040c1c042c0203403a110740e0400f68500041e240c01c020741c02918040041d0381c44d100321300d0010030300090459042104802646050b54010640503883d41c1000c1402c00400a880c000e4681000048001c0c1440040c003004000206901d11060704c104050b20302c1000020b030091011a80707580c4108940f500642e10790401264403481500e6038000901e050080703601005d42405058080e8603c1d98801280784103a01080701c0c4c0d138215540c44440a0940e00d00010744e079540f4140c15184c90300c561400c0c205580740008020011001b40c40314000e041c180030f101401a074940341280d6100700c000010030140c810501c04603006180346d400040c04400086004a45004000054160700d0300c110110784008000c4001d0a080d100242c420002007208030300004002509810380300e0b003007114500210704101c00c140301500c07111340c1014140301c90307556020030000b0743c01c060145940c03210000c40026801c2c1060311000360b0b500240c40740c0c0e108000950092404031445104825480303e00c1c40c4245450350924 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 230749289 1250 230748039 230748043
    0x11060a0915030507090e061807120605090105060909100302032b03183c0209010506030609160c080304030509031c091406090d031e0809060402061b01060305 69
    0x2401514100d1003604020141e2611034010349200b1601c0b1740e01c0c64819880c01d8040f02c03260300c0c041c0050742c0c09494031808141620410300e81910441d40d90b520b001d02001100710354000c50b070182c1c1000c1c0c09100d290006206e141c0717507081103400c0508151144155680ca142d500b0f00e041c170301034100a50500442440310004043c5400d0b03924060080d0310300031088a00e688003038040382d4038201c80307000310340e40c600b000c2000c104420810580c03884480c10205003007400c1d034840b00008180e26510ba48031448001c1403070650802580c01800741c901031700d0182c0303142402000200194001084100300318465400301076200e01c92107000b03035440e9001e50160344070b08007443c014007160004080d0500a20801c1160902c01510040407079101c14103464212946d402d1000010301485420140c07508102c0400190355191076003001088610302aa035040a4200c44403040340d0f03034003024140c8004124410081c0203071078002080da10340141d412a20030b65107051449444242501c13800300141c03254600b201c00002d200300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 230750539 1250 230749289 230749307
    0x8010504020a121110031404050d0f08090703080a0c0b010b0304060b0121020d0e0609060702010e03040609120c0b07120e060703050d1808040b13090b060d0911060a 72
    0x2080780c000d41e120762140030f00140c1d400b00d840d0150598035402c0303c00100381066060640d200c0124900460305010306c90b8034001100060b24101c503154080101200b00c0382d80030922407110344040c41c1a958608007030910035503400b80b900000d410b205000800030755260007481d0754060b241d80704003000348035a50b450600891344c0003150255046810480342c81040c0d8820040907404000703200b0140056603400441d04001d4100615840301d041c2d9038804101d040750200441c0b40f08440300c2d40280341c1881c10b010300a084d030380c000049801c168018001440203e8020504030141c03400105940e0010280b42032491144c1c0c840da0000c3c55820000800205100d03100340403115031201c030349914800d40701d01828860b02d44039440c40a00010018080c074188000b070f54000c02038600d0110319034280110703a41c540a04507805035100d04540b07a80041c1c00da07110403101071010300510102504001f204240300c0480c840b4400e144206a020783e8030401c004c204201d1010806103131401030f10040d00c4290303c8402509541c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 230751789 1250 230750539 230750543
    0x906080106050609130b1311091206070c1b092408122502030609030a030b01090b030a0b150a09090609020702031f0905190209060307030c060509010c0b0108010504 72
    0x4200880407441d4101001203d10b00c050290803030103041c10758440d0800030303c0706c400c2059102c80400901d40c02a0411b0044a03506044109a140d9968140040000394008045000440c1e000b4004014403590440b4100308550303048007194680d03e4020750280c2d88540c0c42d0308100180307850602046210303d450040402d813406100344420b507158030342807490f54030011041141005507081008540f00070502c050a818070400e83c5116030001d070283d0000381000001c85000f5901d90000c50b00ca282c0c1c0c0d9040c0510340c2501028204010403070309014200ca610700c00107082c0503020340c880c90100c401d0707240c90801040045011200e40e4640404000043c4a4809842009501820118041010a458401c031070369503038003c00918021840510040e0103d840c007802500d0b007945c9124180101e0801d00400050100070702840990341c032544100516580c0c050f00301c43c0a40d002690502c002214594110b003595041d040850311804944012294800c01a5004048030107420001421180541046005034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 230753039 1250 230751789 230751791
    0x2070506190c0212160c0503010204060809100c02150403210c030e03040b0a08061809010902040501080616030e0c0a030506010801061707030204020304030c02030d0f032403080307030e0709060801 86
    0x3216a01040342e50300007420104104c08000c2051607003105807243c0080350b80c0d210f071480c0030140313644d08002402c90b00b0a0f4410004030f22403004102c84410180308105040c64459810050740c1040c00000703550764400708680501060500100301814011301ca50034003c2003001c103d05240f40c810340c50001414003061740c2404241040400c24001d280482510113682d58052800d040c12507180c0101c8030650064255604113000318610445155240f003038078401c0c22401c1c00800e00b40400d206000c1181e105a20820f015004202886080014403400c0b14410205280101d424820030b08414100210b202480da404000c0800c00402c01c000881c1c03140c101c03894100208942c43d91071418124480c4c4050007005107410a035800d2005150503400f544c0c0281c02440d0054039032078241d010902d0705202010803408200d2049400300c2480c0d15019141c0000c0356400c9606800d403030404070b42001011400024a5090040b0004070480d1099012140340c10705c06c0c04941100d40e44142e05030003007045004da91055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 230754289 1250 230753039 230753051
    0x1e030d021c0e010e0c0102010606140a05040e04200a0b120603120c2107030c12090b0a02010e072c0c0c0307140c04152106150e13020907050705010207050619 69
    0x1d1b40c018803409045445684450810020402d00060140c0c00107500c3c0003480414440850000400d000d01c0d407040e8420381c81d402043d0704c82c04000007103c00140440b4483c4030b090b4000d200c00c0d9054002c2c0c442d460b461100f550300380c2d01e400300000d080c40303101a9000d000c0880854080030a01c030004502100a54485e04400002280c02c1e0402aa01c43c51f43c2c054045000c0c150b0000000d01c0f04030070700c41c0907901d0f86040c03914991106400e8003168400b8140400507912400042c034000800d000d4003005100201e05560050000c50100c110a40350320700000c01c42d800e000001741d400d0120001c444d101c902a0080e01d95840462810070400401c41c0f15a0010303100340010001e4600380b0748a003040c00200c90035148045460034011640800c1c041c0ca101140d81d0204031040d00151280c0104500c0300040c1c0752204029007080c41d00142c00343d0042c0070280c1c8010b012411005a1500020310307400c40304502d8865503800d500c0c10891b019210707040008016215400400c01017545105404420b4501c40d5024468 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 230755395 1106 230754289 230754313
    0x207120b071805010e0105180402031f0e0601090302040b010c21030b0402070803010302042c06040b06031c1209060204171e030d021c0e010e 62
    0x403186080c407607031641040840303140c0b04215101001d0030b03250000091140d558110020f040c0b1400148070040880c1615a0f00814180500155900e0078659103040001c8030030000c00c3c006404012002c506440e4082606000d50700c141e44441020f8203580800004107140fa04890512080c7c1c4c3c00d92002400c3e40001e0895203d21440403013912821402c0541a03c81320240c041c840c5204000c0c4000190090040d20b06594040d01c00258680c280500c1d1000d07024405084621200c0c56442803c0d0000001481032141c0e200e105500110744401080c10790b5080520710103c910120350342940515849094400001c4800500100b40440d05496041c200da015411140b0442c2e002030081500401c100144541b50a80700206031460074084515612801a03203c0c90301038540002e507460031340c01107900d880814643c2d00410022805440d134164000c0041143d102c1c51401a1042418 = true := by decide +kernel

theorem cover : BRFrame.Cov 230575539 230755395 := by
  have h0 := BRFrame.cov_init 230575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 230575539 ≤ n) (h2 : n < 230755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
