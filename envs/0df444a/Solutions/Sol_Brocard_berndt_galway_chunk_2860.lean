-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2860
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:57:58.508241+00:00
-- url     : https://prove2.me/submissions/b303382e-f795-41b3-83e1-b61a99bacaaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 514208633 ≤ n < 514388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 514209883 1250 514208633 514208641
    0x1b0504030609150203150a140a03260c06011e0b07060509160915050a03030f0c0206210a1a060708070203031612110d050301290301090e150f0f 63
    0xf49005a10544110365015502c90034500058188150102d400a00c160810305c2c00041d80c149411441d2481840141303020702e01ca246071110040c04d41c080000c0560000444e40168031039501c40301820342216290020540c80d0305000c8501c0d20004c00e00442090209521004c101001030203048030441644010081007548914181d140340540c00100241c510400348004183c143c1e00361700c040818202028001000c0c1d0340d0b070003440034904007800042c00103184c0d44001041540102c0790000240e201614807480c00d0440124a0312400c0c0c800e5140c04c0e1440701d2020702904210034010394001c0c0850700c00c41c2c55030008000029909101ea80d80c0241801c001081402c01c1d0b580038400d640d42051490102c2a2411042c60009000141c0605400109a40640c410301c01d030000220040c0d0006917450780e500c1c503402c00c8030340c0c4001d075603010711401c2d41d00112a8040c04035103008080e40c001d1008000100320420380c44842420710885070001e0f5a0180f43d10300300081e2880445d000d680200c4134405915903521 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 514211133 1250 514209883 514209893
    0x10605060316030c0e09090109021e030c10020a0219080c0f0105040618081212070201060f0302060304084503060403030b1203041512050402010801090c050412060207061b0504030609 80
    0x17034032101c1c59800308009080120722a410b41102000c280700b11000105030003e80a01410a070f41c0400c85501540200c4250055062202d0610003400701401100d05c011080e500245180007241d08604040400850402c1341460400c000c03000141c0464150f940030781000b0000f46140500d10643d01001040314404a686144102070740c0a001c80d681515448020854240c02507885011100c200b9100c03040050360061061081005480e46400004d043c645103800308403454201078800e4403202d4042118150a000c4240c1490404500c00d030b400350513440b00c00b94030000c0c117030f06280c00d400450310860703003409030f680407854035800b69050a000816a00c1140440c401c04001e14801d00c05100009021408000b01c070040e441203040b5640f1000a42d80100523201591425100240072890fa4401844280b5854102614142483c030f0709509003680d030702e070303e11000c20080c00075140903900142c158284030b9640110f804c00340850301c0d1000e0b41410208020314600ca00c0c4005040103683d2046001008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 514212383 1250 514211133 514211147
    0xa1e0f232101030515100303050307030f050906040b1003050c100215010902091309031d03010e07060c0507080606030307060f090803072d1403040c0308040611010605060316030c 78
    0xc1c52601c5524240c4041e1640c0c054116007800180d6503407040c03070382c1c0c14140e96021034118400c0300904402c060052540e0742c140c6060300060304401c1815181d501c404140b80c66071103080e214001c814014011802d0606081014000c0501202002801c1e95400e0012850010700240615004e03561091062242c1800301c0c10929810b07240051220100000650404150013810f201e4008030b41c0614005810701d054170480c3c03041f00d4010041114000c1072000c6c2d0b00b01e0350300c0180c0f40a01500204055520507001800c001d0107400c8071022a11000001c000e01508000c0d1801509034400149018106000001d0341c9001e407150041c840b503240c1140040341355007600096075040d400b03c903181e140d0502203005050b5118000c031806104600e02c0c43e030010000d100c2c0c180d111040540c0c03100040da020100792880c29500c001c100303840584c15990300000142078140244005e01c1181c0d100c48800850800b03840c2515241d42c000b9218503c21b0040c00110110648884061052400d00262284802e80c00ba1250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 514213633 1250 514212383 514212397
    0x611210405030102030c0408010501150c0201030906060e0a0f050903070c171c0e0117060901180b1206040c0801050108060a1a03060403050c1011030406050c0d020a1e0f23 75
    0x554008018028900341b148040c2c010340b02d07000000c1c802a070f201d203800035204140341d02400000b91510344140265000341d00c41c04640340940c40128400d51208210320813400b06503505d0603050750340e5183d2451111144501780e0070000d80d0002e1460400e05889a000a4140b40200c0107400280c0c109020785403c100703c1146528510074260500700d202d40c401404030f4840f00425404201c50b00c8031225540103001c2224032600004280c12a180d0904207110f80c0c1e002c402c5014101c0796034036a200b1160b95940c400f41d841410b070560040c2050314041c6898a02528554812402d50b8100f00051010791f4001c950241c0c131803c04100011021900c0344210202c0130b06541a6425000e05000e100500da0310070008d01d1240c4451007181c00207083c407403403e0121a051081480e894109001060000391541c1046422040501c1020f00f0061129107410490b4841222540410440c1c1c0000d0221a5525000c10000341c0300d0811110b1044030700e0010b0010160001401c5040c0d400104bc0400c80a00e0401e940c86 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 514214883 1250 514213633 514213639
    0x150308090325090c0c060515010e040504051c090e0103051605120c0d0201121b0807020309031f06051305010f050103060b031503071a1c0501050307120812150a0611210405 75
    0x2550600000c80381d5007003235158081e400503400f60540c840e02d0a090080c0c81c041e40d0300c6401405041042c1014500100f510400c0e0010818909800240800110081800303940500c0240c6000c41410000c0f50310003495611645c0500e182c082c1c44440e00e00081000902c4010683e490340c848801440100e039103801140616001c3d5103442d8842c151030015001914000c40c1c146c544141d030351a10711013a030b80ca000313840ea803e07855030003000c0c80200500c033703031802d800301c0b620300800824020744900c00185e04044017084c3c0407801e40d5803001000458501c0c40d001009240a090070400d941c02d00008600358840184003c104030b960b481e0102c0e0329101044030800410707000a142c016000504417081c0c1d075a1010300c0755080241c948401c02200e001c10b114103030480e50006c1c001c0030308500c0d00200c80080030100000b65000034081c84a89088038204228501c201c034240140030103035007048100490803120360040c9080240f2801910b4035600e0000780749512144084000b10f12008500105010b403046030000ca070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 514216133 1250 514214883 514214891
    0x615050d1413110f1e19061d040501210219080102090f040e0c2101020d0c020d0e010509120f0d03020316021501090f150308090325090c0c06 62
    0x10b9084a01000c28502d01d120341600c00b50301001e0400c03c1035500460050940c040f0045014240101403411204c051820180200004144039142c0b01c050000d180c1c0028042003805150302c02003c1c4804400c0e68002d03080310b0800c915410000d035920900304903180c081c603410051282c9829541d60207101514040b00e43c000441710781d01c0b81c01442c041e4005412950082c00c03400c0d841052840c00303008840e0b820b07003620024032000c65048100700a103105440c00d0000251840c20306400d4103c203000416010100340700115203401d04031802454544210f50040802200d0181e040103603a00a00b181d0f01450111568804d42c00f14110044c10044503c0c00a0f04900c10045102c9085800d0340103584910411502241120020642a600c1d10350064102884503040c00040c040390116500548080c20607000026545210031186c8801568940081d110808007007102d1081c3d20f02001880b0310094204810201e040002160300702c00b003218050300c200c8a803140700c04200305103e40b51242d85150040003c0c8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 514217383 1250 514216133 514216141
    0x609260609070512010212150109210209070e010c150e030711090601050a0e01030504210c060b06040302010c0b07140d142d090f0706020c10030615050d14 68
    0x10b60342c001030f1048500440e034101030040004010304c01e031104611031514032280341e03072030600d41480906080c4200d4140300d0850381c08124410142c07600204c07803211484442ea00855401009044c42c4010080c0c02000241c1c042111140da0203d0741d040b80b1688007003c01d8054109144038070141c000c0500f20801407001007009424031081c41c10000c5140000d841841d540d40302d007401108c0c5071065541d01d0010a01c0300c1c541c1c14441d44a40e0080e80d01c640200800c4040341c0c101050381c0051601804002c0001300c1c280741410070b020140c49805030210044400f9031402d80745d580040d0803c0105007018200381e0518000416441c0510b440710030103566400f00d1a070b2880340c904c14800810841011030900120100041c03078500d00300000c009080311017031898400f04030f024821141c03000d00600c001c500b0300030303062030301e003084030400045000c0c2c4155000762403c030725420144240410004c03a04010541040d0040240151003500407220802d141b230700c039944030080741030310010b8110040d040c60028900720401c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 514218633 1250 514217383 514217401
    0x6120b0414012c01060506030f040807020409081902190f1b1203030507020102030f0a02070323040311030328050c030f071217060f0111060109061e06092606 69
    0x1c0f00d41e151800003c10842501810440d08a51040c09502e82080c800c001142402000401040d80584070704081c9140c051300345d0116003615001c403011a0703010000310707020040c0300081200940c3c0403070750310042c0180e121040003480c68041000340070b02a500403064000900c00b101d9151484003031011140640d8560300c49402c0c4a400032003c007600000d20b1704002c80c2c41248103001701c0c0d0180380012105449070300c65030f02810013588402c1c1e00303c0500101d41003840c0c1003d0000e43c40004003024a00503034860349542040c0b43c82101440d010b5120340c20420030380d1800011705101c028020181407041d034054000c8101510f8520450503541800e02c4040b561504840e80580104009481400742c0c00d899828000c0c107951410000f0302462803e0844000a407180c20034980350200380005140004846000c00180e82c00c00a00380c001c41c00103521854140840003008680b0410f040c0b039681d5200f122072034075900500071400b90040c5034800251040143c1c841c101450710316002c0030000c050b24010b003446032407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 514219883 1250 514218633 514218671
    0xf030804030203060f10050f190e060a050d211115070e0409020a05041a06070c2103020705091b0a031d030c0303221203020306011206120b041401 64
    0x12440f0b8821000001c040c802103900c924001e066450350f0311502d0f0300f484204240c480c035030030740b25801c0020703502c04c002d8040b00381d1050740c001d100b044480c0540381001c6062104014084e0071280c01511100640030000b01c00d900302c0203102540d400500d400a552400403222034201901a50581c404c8000c0004008807801815008905540b245091403204600f40003d0b10724002e00654404924081040f003420681c1014400212010240500490200000764150446d03041640c0d04503020900b80995420340702160040d00c51200c080701c5803070710380d54020750b110500c0c040c443c056200e54010903400000010303a03690250076520020348030401400018010030b4a04918034480c07016501e1070301c4e9114013004886040305000050740c0b859030380d440c0c0f2081808103510a00c0b130030448011214045040e00004214644069902503545d09110340014407042c40d0b2010b9041c5603190840030040451480c03000d406190348491420066529814641c2c0c20700f00f00d060001280d400d048110000b4107819138 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 514221133 1250 514219883 514219889
    0x7030501150501090e1803090a0909050d050304150f020d0f02070506010b160320030a050301060f080610231306110616050d020705100204030b0a05091905070f030804 73
    0x20511010340e940d03100450343c0504c1807040411044041000c10241c1d03c804c42c0303681001151000700ca2a00d514140840c048084036031040040640d00d030350300d03801c011040c811201000044c1c50a00e04500300f980384c4a1025110b03e190998030740e6900d0340984c403402da9805842c400310303007201c04105005500c1940006540080c00031104c9005500000c03504200715415900c074116450700541a10403246d0302503401c80c401d81c1055054640000c412002c4090410044c80b605900340d07945512545403002c00740200e20104508000d010417501040401d0729428081007940e142031810b0013011000700380d0f0200c4006110b4031541c81c1c0c1800a007511340b26a02000c018101d46c0303195143c4085c01662540203441e11415a8804428111440984106445100900120740e41c076100180303001807aa0701c0b00e1400da00c0324480041c958000c1010001e0100b0001c0c1e00394054401d401c14840b902e03003000c84a03103c07601c50140b40001900019007030b05010040002102501c240840810755940b6814001e6890700544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 514222383 1250 514221133 514221161
    0xa120509010501030b06040b010e19030312110a050304030e040e0d261302150418050109020c0c010f1202030a050126060f06220917040317090d0507030501 68
    0x400850300200d814442e850481c1e403c1049801203403180030030000a0485005414104520b03c03208001079030f00c00d240091003040340440a11042d15610f00070344600180b01c0c40481c003d00e040001105040c040048a842c261030745880b83d41c0340e840340b5041c3c0d9420241c2951320342292070f00101500315500001c070394140c100942c86805034418030044074400c1c1000c092101750280c070b40201082103407840600081d410340c802002c02e02400c00380c3d10018420703080b41d4007420111611000035581c092051141d1409024512000d519202c010b50110b0f60368000a0401410485902e420018181c460014001c84d4500000e040d50b40707003007503040000901001e010300c0e500140e00035501500540c0480d049000f0380c00e402d001d07200c00d555800714400c11160042207141c004500e1103515455621710104c0130710041c5215000180d00030503080c000c028140001c041c0ba0b040d001048180b0100d9480031001c41464102d00649545118010214442102041009005e4420b8071400300800c4810b42204402e2034250b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 514223633 1250 514222383 514222391
    0xc0306010b0a090e10150c060506060309030307080903040f0f080c010e09010603051918030e09010f14040b040e03041e03020105040605031003200117090303010b07030903080a12 78
    0x41d005400c010300c5001800340c003003400c4820400184103100000c95100c02c4241d402109a0395170054151150640d20503807001038070f0010003400300406481110b400c005d095405904520304000407513524407001d0100804c1c010524000703074503110b0400498001c1e059182d035080c00c090f40e030703024951030503903038000e02d600c4e4001c60007114802d5100f20504c3c5c03581e000042c0400c440c0d0b480c00005400034600508100c40a02c0d20307040300c0c0d070b07440354600410001c20744d40501ca07204000603040c010040140465214464111880100400810800359a095440c40c0e008038400440360030001d0001c08410b805590894146a501503441e880407000c3d004030391480c9068403c05402544801c043e460074000280802d4052109200952084015550001d450b01c5500c213600d441340c980c0031052003009075034031517100741d600c21401550707010461a4002d56101c4480441c0c0c1805050b15840c2d00050203030300703190600418007909151081e070544c001076800801d050b036030f03a016810092114002c0c2d83c91400042c10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 514224883 1250 514223633 514223639
    0x1a04020304080a050f120c0c0606010f1e180303081815070c080c060103140f0a0f0210090b0301060914030a0201020a060e100e0a0c1203080424020c0c030601 69
    0x106008032885181d110311000d00e4403407450b809441c00d4004201d400403601090011880d00310704804141d0180340042d01c03142d1074048040320680b030b11100071b05c031078100030314141d410340c426401000e1100240007032102074440d50800c00c42226004c03000a5a10b0a410b40a00b001051603004800c003401000b0405203990301500005100b6035032190383e05916840359203030000440440c403030040480745e170b48100191072901c008034051515082e420382040d01c0c0007119030000d600b0382404000c0580d00c0e18901024040f4580c040d10b9000c0440c4196a01134001c030000c0038140b040038031a58502000e846c1d03d415803526940c50f00e80041901c0b410380180d036000b5000300c0b88903000e4900010400c10141d0f05034028400140d00fa92001c02604110210503401e1003016280e0801d1003281c014016a2003011008020130b500c03a09000c1035085d2070381d0000118000180c410f002190b0301c444601e5000b60401c04883c0200020400091348020250400403d41c2c0b0205407a292400d01003400070800d9022800c40b002079032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 514226133 1250 514224883 514224889
    0x130f0806010806010b130302130c0e15090609061b0c0f01031e0f020d0903020604020a0b0403030c1106040518040606090b0109051509030717010f020313020f221a 71
    0x54203000b8a0140d901800040044440c048001c0c48105481c90740c2c4141d044d41d9501107000a5200b55801d45c0c0142c540c03405c0c905456004560381400e0707004440b03000030185880071300314451140c1e2a9550181c01c0000c0c041d801501c03520308503074112a03d0000481c0c600c0350291240c0d280c0f01951045032044800134800007596119008040d041c0101e040082d80d003180c0059500010032a40e51340010a40e000c0c445911400d903948203035040c550294020f820541b400b841004002003107a080700141c01c000f4882800801c0c3e0003007100000790341c0082034040b500c244500282d11406654001030344065444080d8030b4080080844601842c07080c182805150313107410f20541035980901056000680c2d0f54030401044c9040304a41e450312903c1091a40f500c002200801c0c140303a616000801101242c051559500b2003d00c00c51b51a540c3c5100114118106209166200045404040d21031032107424124241d5032440a90301c294000c2c8043e0740a8a201e10003400098044107042c102e038103980c0720704500138bc2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 514227383 1250 514226133 514226143
    0x1b0316020c0f1e0a08030d0e071d0f040c0f030f12080f061309080c0d0909110a0302030606120115020c1927022b0c0c0605060303070206130f08 63
    0x3804226150003940f501c0004003c00e1190b164041d02600d0300113844c04041c802008419031600c80031507901e56513001d0920307107050f6622041c0803000c03c1c07084040d245d01c8a181c098100c401030001000c1c9071101c3c10b00c41d03c0700361250007900c0d61218100d4000104001e01ca0380004452048000444a807140401a15550002c80d030501460440900140c22490440040c041c6044002c000098407103030f41c0c945c201160000b52841d200d95100d613203491407940d000303500c090003001001001e00401c500300c03002003164007803661110241500031012501a54800040d640445d222181414182d070356110802c5501e00000b030140e000d4090320b0b0b103010250030426061601c405003200e07130300140da1500c43c000c80d110050707290403034504070140440d448a80300350005001948409140c620a042c00051030700075098189590703441c1030300d01400900c00542010b014284207410000009082d604e1201090542c0308a0314000d500202c0001e201c0048a8591804001c1d22200324203002c1103503d510340581c0d11 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 514228633 1250 514227383 514227409
    0x6030b0a091226040c05210d050307030605030d0f0e0406051e030102120712050708071d012f0f01020327150c03090114071202031b0316020c 62
    0x9101c2c81ca0080c203046020304110b9410302a0034803440324800c0c100c4004100241c054604031103581c44003004000c2c40ca086801c03048500c0210490000a00e0070a0070303a40d07110325001d40a028800040000355109009a10050041101900361038024810a00c02450040500c0c000da010480080c2c1c11041814a131283c402650005400344920111780c4040400000c9504945d950540d000c01000000c10b00810074103004035040e03100c0310100b00355401030348241c0700c00505140c03c0100c058100251b19900070b4083c078a030305201e041c2c0c650141c00c400040f83c05500c441e114062031480d451814034281e200020450365440c450742610041401d4548080c280d01c02a41c0b40c5894030225030b03418403407000300c1f42000c0000ba5954110780c0c0021220041040c80b090440d609a1000008420020104802e0103440c45001450415014502e040200030b40b05510003c03c00812660100c0000c21030290314210b003e0b4032403000c00054903450035090040a4144081861005002c0d030320030100541098081c840070307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 514229883 1250 514228633 514228643
    0xc0201140a0c022a0301140108010c0c03080718090e0c1c0c0302090a0f050a05070e040b030d050c031308030702030f0106060e0d051524010804320f0106030b0a09 71
    0xc038142d510042ca10a1300c0250a10186851a101d40b00310b03650700744115031004551110316600b640c900044070b4210740350303800408107100354203040310b0000b41c0c0710805d643e1240450601c0200150078043c40d08010816820080d8810b01d040c60810148100007602e8481751030845612380070004250080110b08600540200708100c044014401407400c6c228003580412400c900240301e10040780004159036050780e440f6040c0303641d0b000780304040380c2c0a81101c0c580c210070b0302e080c00b099004d4008241d40707a21004605c01004004644100c6040040c4200c8801885114266100d1610f84088503103a601c03014080303100c3c1c443d1001590703160304180660000c484007600c0b002c2c02814003c040c0050405081da045800d80078a00c0045410022191a0703070080c8118031138150a11001191035066107428960203043c82260b504104c009946034460036104401000e805a5140c080300c2404a10448901017513924002e250702c0030001841584400300f100e0140c0301504140c0c079212218411514543c202520b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 514231133 1250 514229883 514229893
    0x10080c06070c0605031b0d0b0a080c010815041d060106032a14070506040b0609070203072d0c0b0c0d0e1e0123040302120111030121060c0201140a0c02 66
    0x6028020005181e20001941c82d0107000e81c6c00e075a003855550b015a40344100180d890201166905081c9040006400d42500800a840384480040c2030000014440280056002e0a01c1040c3c0c5a68100a805480030356140000403454902c0c1c945a200034012100041e260515180c000b50f501c007041c428000318818240860702c504c0c001101c40c03001c1038044282100c4100070110000740d041000501c9180103407174000701424800d0421002c240007420410443d8014812140810300c448122030200704155044040300b03000900c0703901e94a0241c0c030007030050818624002115001c0000506988100500fa00d464190b08030040d00e0601101d071465130013110040c9410320b200540a4010f514400c1418000d82e003c54108480b800c040510072403814160000c6802c00c01c41c2426200e43c040c0300c00d11802031100c0008800104818001482920190301c0e560322950b8100d4030704d00506d603005801c844240b01c4460740c01000fa02800c03503402041541c054000c00501c0e94096841041c1482c02d080e40600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 514232383 1250 514231133 514231139
    0x212060105100c03020109080a08100503010e07090902031c02030a0207060306030b0a1a0a06020a050606092511060708010311030616030209040e03041502060f13080706020c0610080c06070c 83
    0xb1410f01c1c00001c1101035640e00e80c68900403403d5040940b2941803556031307020a82c641001a604001c1d49544518042d80c10503002c1900d83ea4041000002e894038980c0000d80c82825000181c40c01021a448019819510b071104080c1c03039000c0010000c075603658007202d140c5a600c2400f2411244613100c0034048a144402103850070403941c00109461190050321611940c401000440c8840740b030303006402692040003141c04004051000c00c8e800142164051540c3c40d107034241d00390005200e00b1302e43e4840c8000750603801c028000c1d180910320501100450741c603482d12000141002d4428001952000e41100d100c10282c54006109031003147c404a181c0700c0e01007a0b0400768065000044000c1d0701584900f001c40503146e007040500018026032031b0b40e01c0394149000010741040310240081c96503202c004100910414498440314000e5400742003135603903041600341080240a480c180c00030300d0143d6130500260326042d1002c2d40c10380b2107240580b81d503e5412002c108807403244103001401c0d50a244c40070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 514233633 1250 514232383 514232387
    0x2011b02060d0207021206090c10090e041101020a05060a021b0318010f17041506060807050708160b090105060a1d0612160303092301051206040b0a0e0103021206010510 74
    0x11303281d07841c400b0b4a01e003c0410b203c4491804c02400312824030681c0c0c80403454020625006900b64240740590506086c034030705120442c44d08610092014010701e040c0300281480340d00c01c100440bc942d0f0000c058502ca800c00c094000040e512040382800b00e06030222104d180c464000c421103507030081c0d411580b80d08105400c01580c01c4450b600410f814013200c03445002030124040f04692003180f04d0720140076004416044482126582d0300000200324013070041003002c94100d0100c800103074004040d161108510399490170341d01800040100350455680500c081510150802405001c003114402000303078468501c0462800ca42d40b144000858000104803e400c14044040d0b01c1881d0000b500c5854009017040034400016510840014450810401c01001c0e00c01400313580c0e035201d0f04504070f42c00c0c9200000346540212a10644268842400704e8580d40d555031188090f0000030b0900501251780f07211038104003001344000d0f40140c100140030755060a0124055058510042994004078031903101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 514234883 1250 514233633 514233637
    0x3061e030d120f2315033f09040e031309020904060302040c020303070207050306070c0b25030b0906062d09180402030c0d0503040612020d0212010302011b02060d02 72
    0x4848809940d03040e040c82140100e003c0c4c44843c4c010f5804500320b10488800b0307104200801402e0300100d440c0c80d20b00c403400b07583c0402c0001c850074902e8113094844010460502151552020728201d146e8248282440e15100002401e46181d04071010800400181d1800380c813440703500b42d180100300d11030206000e0f090071540a825040800341c00001d40c1030716540440d0840d900203140a0140c2d00102c00c201d002c40c0d0400070744001e0441074000d01078a0034210006021b012001c00014920100b640015462002c031103c860076010345a01d003030a0303062850501500500141102074026240140028618180035080307408850010882401170346100342e1000b1094280c01c1c40000c030510800800e0385d41d94806101b050365110000b1110818140b903c105841c044011101303a003d1030604018002040001c070541d01241c2040c00c05061000003040000c0003446503100c16078074503201140b042e40e04140700503464141c900c00e032a941c2c50002d00207604603061010f0380c0c0c005d601150030084140700c4101500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 514236133 1250 514234883 514234907
    0x70806060d0503071a0420030a020103020702181602010b06181504030f0834021e09011d060307240c080c010f110702030a140f0d030203061e030d 64
    0x10f90b0306214882e65900d03981c010390407a4480900c03189080c0400d0040440002c0a09400742c0a188410642800400c0d00c9101118020341030541c086418030954481e141c1c43d40249003c8110b1000030b00c2c0c941100c00111003002205001503181030f0341d0306d010f0304001048413000b07840f0280001400d44210100800b03603100070141141084103001c00000144403e5174000e040340b10315801902c59640c2400c8103c150704400094003c84801c52a00180f07004604481562540560321035010041d0f4064000c518100d00700c2c0140c01509160001a116081002079040d096680c41d80640302e494403010582e1b0340303149026401052909003861070762810440c5003c40040420300b05182540016110510320f074101040380708280c1d4558282e51503040c920710071f1070618140c0c02d241504242e00b50700801d544a014000c0100908401d000081c09060104a01c000d800c0c0540c007202c42301c408042c8020007940041d650203000750503012807442030908840e0381200c3c446026000380001001c01c1011100100c90700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 514237383 1250 514236133 514236143
    0x5060d0507031107140d0c020105030f0603070513020d05060108010b25020d0b0601180b0a0806030f06070215010602060103081614060a0b01120504050c10022b030509070806060d 78
    0x10107810f1a01d4121006000707068068907144070107000382c0290340d04051911502004200c61500c0240040c1c1c1c011055030307000328450b5009000c0390307103c0c030100e07281200c3c9800040d40030842002d40740000c40721f03030000c3c45600b4006a090000703454000064421060a00034400102c1c81408803680002c11700c0c3c0720301620000c2059640400c6104c0d000b1500c90386030050700380e482c120f81100f0440c0558004c8a641100611002c40740c14481c07420300d41401130300507801c01c58200300d03e01c804902143e0341013001028140c000004d8400d10306021001954400d00d0405159030107900b0306c000541103001148150489801c0241075240c802080c81108400c00b103600102c1d01d080c6628800791400e0000c00000780b040b1703251800006c412143c0c00014080384102c000c10b4041d03508150030000042d0022070b000d4070803c001c1c0c4a424110401c814103908103800903800c44c0742c03100808038007116500142d54440c05504030f83c90801051305c60090503621001d2a00070f081140d402640071a086007041d101d440c226600034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 514238633 1250 514237383 514237391
    0x90f0b01170901060e1003030f02070b0d0905070b0d05100b0a020c090c161410020f0d1d03190806090906180f0f06090c18010b0d180b0a1505060d050703 67
    0xe41e2170340c2c2c1040d00a4918003180ba01450050081603040300c445500682d050000340840c0746013050000182c804c904240b0401522003010340300f0840100b000c2005001b55003480c5898105181d00c180081c4400c0b10032184441102c040016403c840c0d1007140c180c0079180d4040d03c0e0100c034050a00c42c42c901c0c0900058030076501044820000c0705c0c0031825440f000d00c901824004028260b4440f441c1100030f420301d201c054410000c0880b204d0b0010215824400720b5139012410302c0092804030030408480c3c030b800c1281c0c000000e0284010030040580721000340b550325600740c140c48071018405400e000310f900500551228001c502c070b00d0b00700c0302442c4c0d8201d490b004540004a01d0102241019141440054968081c50900508250038413070010a40f80c01d64001d8605100b10243d807041e0b103010f00c00c00b400c0740d1000850940c0401c854000b04082c0000682c65022910246000907070f0100440b10f40c0c100030300d05201d442c084051460000111040105414104006002c20b4401004042c018000340340d81c1e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 514239883 1250 514238633 514238639
    0x120309180f0c03100e13021203121f0f09050a0c09080307140309030712050609030a0906030b060708071a100b0912160b1c02030601080112050f16090f0b0117090106 72
    0x41e941000d1b210311900c20030010107101d42e10510403050141e135007241440d0002d00400d5442401000102d5000414081c142001c3c5108a4005e41079503071a00f0138a051540c3e50008100a03800b60406805075001030301c01c0060601c501000c541c490007030300411480d60800c03c01030000c5550003100428852640e01500d2400c6410750000f480c000341340d403001c1d00c818440111181070210034041c1c07650041141c00510710b8824a030000522107182030045505040c0d84d040152415220300d42600c0000d544101c02316911b10319130819134080c901c18245d03202200042d2001803924541c05031070000300e664900e050b40c1802203e04c00c12424007818218800d41e4840c0c10008140c8680c007007403500c006c1c0302c0a400e0702d0381c40d0390440e80ba0700c00346540c2604264190041061042c1660311041032811221503694140f26030b4010300c0c02e1410842d001310211110307c244030f000c800000e11003c01001320f890410f002c0115280c032081501c141c800f446000e03400710f0490170281c00e4120b0040510b40d48a4060000010341d152 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 514241133 1250 514239883 514239899
    0x30b0a09230a090203011a0d030f11060c03010e16090b160b0403030e060c0705071a0706140604060e040b040816120f09090b151305120309180f0c0310 66
    0x1c0031120003060580740d1100381c0c1035007000e210700200303400b1226001c6c1c100150312002c9a01030104a030000c01708048103030340401191041800704082c145090581d13005041c1400a92410341082c0500803202d0501c4010aa00c031207e0103c1601034000c0e03482e2910b00519051401c400b0303400001e02d03500080b00700c002d61000035124610551265100380c41c00034003d222601020b14000e801810345800c2e4404109d0040819800100401210025011740c1c0f4060700011100c0100d020f1100020411410306150b044221500d44d50705105800c1500c0801001d40d0b1544030701c2100f02d09840142003803028a0108002c50094001070501065010707841071110101d0351003250482100c5c04810019000741241c0e1035a81d4402015002000868414894015007000207140303401c9080e82000c00c04000508484c403501c4101401d0020940104000402c1516a410b5038413640200410b0b03105200660b58080000ca01228a81c01418141d21b0340e100d903034949031030b00c07038581c400743c0035180c0411540c40003c0e07448 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 514242383 1250 514241133 514241201
    0x903070807080607080105061602060d180b0f0901110d0b030f030307020706090b0c0c130b10050405130c051c02041503090b010911180d0506010f03030f030b0a09 71
    0x5002c2c004064070b1401c80001400000180c210501c240010400440342c0020b0701c2002c2186501100c8031030380c0301c0e510b901200003080d91600d109100300d1500b0740002880280c0c240a0b00c40d01e481c8520b03034456950502013034201c450795a88a402000c2c14490007003000d465034002e00c41c1c104042c0454a0508840c1c1c1060f140d601700b2541c2c030300103074004441071100d6944140194011b15082d03002c50705219180c40000e80341c4964500d0309018040d1031102c01d40715801901300d038a5a0b400a040550380c107002480080c0301d039100d40100350090380e11481210310b4200740d105545441c0d149079101403e04184042c29101d1480d1303207400b4078685400380030102d103140e5201d140490480d1140c80016040701030389060030040c001640540314091415902c2d040c1440c451046a89208500303107140c0c2000c80354000980700408011000d0598441c4400103c0c6802e02c074001c80d800d89020b912204140340504030114280c400c080002030700403e01c143c00b000320342c603290000c031803007003030002d8034134003000b502a14003501 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 514243633 1250 514242383 514242389
    0x1a04030b100f090c1e0e09010f060206060f10211e14010303020c040b0a03060c020610080f070314190c05010f0c0b01290c0705040c02150c0903070807 66
    0x1c0310388020704100c007142120800c401090410418010003001c6540580b05460550320020b02d4880c01c075034094964820304400364803450080910000f941c4032017020702c00b5146401400094840c0304041031980c542400c50001002e402864a98030368224007048414040c0c1e81f4035070511101e0300201c041a114030f8040c07826042c00b107010281303140c4548000c620503030b04048c1060705917007030220050010982c049080000c0740d10650300800c0c0401703a2008140c500055510140403145420400d5201582c0401d00501070340042c071405502648a164454549907940b05001b0700d80e00105042000401c00318800c2440710034034042d10318200341181d01c5280c2c0300789500d00f201d1403e0708880c20b1200f50b8024040101f404400d25140d09074440c990340b890b40000040c0100e603250102580c07446048154850680d903550014500207489000c0c0700306090f43d401082c05400c3c812070402c800e24084520000e400c0c03400041c400c110108580354032001c00321b954481926150180079904e0080b4001c0c408008400c02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 514244883 1250 514243633 514243651
    0x4061a042d150e0613051513141906051e0c0615130c020601120c0b0f1c051504051b0c071503381f030501080102131a04030b 55
    0x2c050400d802840101900720303040c071904051002d50009050005110140c84095980c0c1e0700428000240f544140070300000b1407540e42c12400c0c0410308214012148000b007006583c103a805641080c15040080e010b401880b00141c814007440d45110800c02007450610111009546001d003592605401d045048a010360410118160341d66641007034100700e408042c0300da1040140c0d1103600002910b4000c1841000d001c040b0500300c640c1030041400f54507004001d4200b03d41d58401040705085610f42003506050807186012030301450746102805814441e07603003440240c8040c030140003080014240a0000c20342000011188408100c03210014202c3c0900c01c1e00605106140501415983c000924448201400e010810b0003030240c07140384158a418024100c2c81c6403d0406446a854602d4071800d6846a11507036642d645101080201043e4040d41c4d030180002c0e070301d901790030b401d034403030081034250001d070a54041100d070030743c02c02002014469140841c41d0664940368581c505000307950340c401c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 514246133 1250 514244883 514244909
    0x10903062a050301051804141e0106080a02010c1b05041109090109180201050a140403060606030513150207080702090c090a15050f0904020c010f050604061a042d 71
    0x700c80c142105001c801c0744a2807034518075543c140000710b05d4070074418074415171001e4001e020070708015042018170900c0e1409400c44c4c004050f54030709455101140e1003a40e013194685400410143d4001c41c2000180e80c040e11840d040a03070b141d456604e6201d1743c4099581182d02414049900d0383d450007072012406070148440d1f1a01d5021003041410341d03069008140c1245021007541041e14051a0003250980900f0019181c00b1040010b84d81d41154446080d40210006000301c00c01807654001c005481c66079070104030665440151700314281c400b40010306403542d541101c00d10401c00d500100911380c402c125490a1078003560224801c0c4500369240300c0300d220013050402c0c3c0781c200391401c00000e055203040e4481c040c1c02c601e400f51076449501c2c3c000042c0c102c001203219098882c2e404552800e000c10b0002c2000904022040b00109010307103440c0d100341d082020009050800d00700751422900e201030024549454200800790710305010050150100e1443c0c030001c10005000036180040000d01450f032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 514247383 1250 514246133 514246181
    0x2010f0c12110405031b1807020313060513051504030b0c030411061e031506030a05010f0504060f12030c14060403020c10021504020f03010c0e0f01050403021e01090306 74
    0x102030b2028a01000c50030030040c001081640d0340080e02020b0240303031600c0b030508103070f0020104003900f0103160320340b118008940c14000c080340d00100812800b803440001d0341c0c116845180407aa684100d14a02d11300b0500d0160a02042c41c2944c0c04d25100844200c150b80b4003a03030ba0f03980d16090300b411200045008004002c1009110040c0b441c51000001107418501e06802606000c5d80c0c5020604080b5030b04074040002450400303044482c000d2000014402910707450320001c4c41015100900134035809078442c0d1000603160609009460640c0c400703040080000d07044c50f5040c10700520300001581000b564085134008904000c0d80201500501c01c040c003010f2825060180c50441e424200310301541c0700c2c0201e03004450b804541c11401c6202c0c81c4c0110130a0300c0307c0c0009200b115041002660552a00f50003003205500b081452100318016148503510481400064440b0b00540c4006908505801079418200c0d2003e07072424500c0c001410b000040c240c070780d00ca44049440a0b280b10021a003045005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 514248633 1250 514247383 514247417
    0x302060123010e13151e0f06050301060e0f151b0106181a10020a03030e070e010e13080c03070309080d050f0d020f042309010b041403010209030d080f0709230102010f0c 74
    0x706c0302070f02190080460003803502600500500c014828801081002402d02d01660b8030900a80f0100c8002030050b100c4011941c0c0e005a248e00008002040000201481e0400741060040381c1c22214180081015480481c0d200c0300503042e892400d03448001e03a14204000e03540c4450a515114443ea0300170101c2e070510345000342c00c030f613a40469030342c072070b480500200401e0389201c8465064903100400f44071030361a600b40400a0645518004110f0140840e000c90202800070140541a010750340c0c0d139003126591000b494039400d98405501c000b404c20840400035070450780081c509142042c00051405821140c0c3e00e0094000d900400c05855020100d881100307515100c11320711010480d0110129458004655020310980c82501103545103510b5407021036034203606403074155030b001c4d090303440040384107000410880048036034040f015a00c20200e4103070b500c203040d11004e0b10000a1030720700c00c1d410b6902104096a010107141c0c115921062200d15001c280c0c007407044001819116a500c4908a0240c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 514249883 1250 514248633 514248689
    0x50904110c060f0603070b0c03090409030e0a0603110d05071e0804060509010515090901020706060e0a06081f0504080c0a030f02010c0c02090609130804030302060123010e1315 77
    0x14050f02d2502c01440401e40e004540d03a011202e500c1480d950340c0c000d0000b264210300030540650340c000d1804d0b854109241d0011000318058030205c0b400003942d51240415400c80e0340180100564440c1405005410301c0707564000358100f4640d003031891880710b12010b914400c3c49101c02843c0011900c01c1800100443c1c2e0241c2070304103400000034480c92030100346000410803e110018841d030740e10008200d07900000c0d411507000582100c7c0504c4280e0320b0311214bd00450060703500342d503030170303c1c1a17000a020840460101d894803010a0601c101440f03400e15500540000740c0280c41803081004005e012440810440489078401c1e1655005440c80c0140a821110083ca0040900004446060050b03031506105580110110303132203185a00c0e01007025180f803030061401050b101c00000d0100901d500001c2c068100c03207082d04101e52420a080c8921029074030b0f010310300e0129400343c0035182c16142100140c1c610849070a0b000451408049200000c0c0c0caa40e4005000600703000c80000c40d0b07004d0510 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 514251133 1250 514249883 514249891
    0x10f0c0e0108190e0106090b10030507050f090f0d140c0f13181a040b010b180d020f041a0108090703031b03090f0e07080a05090715050904110c06 64
    0x400d4089580024000380c845031008103075190b00181e0009142024406501280c0203404030f90007003260540740d9504500414140810780e100d03038055810380d0806442401004c0c420185550340500b03040e0705820701c54668109008030b582c401004e0300408000d0311400c00c1240c07001d0158480c90116800040502c0c00c6c400b070303030010074082c0c910340c100704968bd06c0740c00040e01c3c00c143c40c401c001114030340090900c1c000032590320020140d0102c4980180c1030358030310300c2140c01039000300d0002103039980c0c500a284880c0310300f425002c4041c001740704050b107924294054040c00750000d005242051501da000404407403c08107002c0c0c5121810f001c1400c1d81d40e21000300b0380c0c8004850000c01105084d038801401e8100a0341d00100c81140500c0c844d405c052040c496107004001940c00c401603151900b4500000e100100c41000010303103540c0c00500380c0748041c01031900402800000e8280395042c484030b0b0780c150200d20588001d2000801c1410020b8440d0321500343c10480c180780c203a0322041450106800c1c4a0090 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 514252383 1250 514251133 514251137
    0x30d05040212120f130b0d05090d08010f06082a0c0d0e0d0212150c030613140103030e0402040f080604480305010c0c1112031e1605010f0c 61
    0x2da00c040c1441c070704101311404061000d4406032109022006080d841d00d8a4208000e03070b000c0402d03946a50402504090b01440031002a200c201c0c130540d00464550909102e8800c1c064680402005118025411180c100810f60100c6903407588204644403441d030310018516509400003001b20035045d0610a00c40c0180503882c041c040719440c0d4000401c21405d101019100303a01c40864448110300410120b4142b18040300d130400030b03107040d103149902c0b500201c4499002c0e841c5040c102014244900c0b40c0980c4e59610714080c14586d086440441c5c800010203109034005508200100d2681c0b00003504d01c0080c583e1000a00c002d10f440e24041c0303000c14896070382001c40e4000800901a075940030b03180b40b4210303801c1b45016640d10305041a080c00828107500c051700359403a00f81501e4149a01209a07228180608540c809900e101c8041c402a41c0340c00516401503001805021140020400d884811040c030900e13003030808058030310b001031020410a040b28140e55030201d03408001828040c80d10000418 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 514253633 1250 514252383 514252393
    0x19030f0902010e040f09050d02070602120405030a17041e090f060b04060c1e050a02091b0426070e152b0203100e030702150a0207170f030d05040212 65
    0x540c0c0060140e00f09a81811301c940e4503a20300c50024a8a03030f215206650b008400c5401c1a50002e0010b920344005028007130040c02422101088c070701c84282110210b035000b50003081c00300000d40310202c0c4106c00c2407160700d04400070040001d8241800c0642e55022101220038204a0700e4103091100310794081d0b0b514414103060810810640e0307088030070313902180e0141c2000740c0c698129207400030b40c2440940c0c2404026545010b424103000c400100002a0f51003590a006943ca0318541c0b410101600500c0101c0004100024090021413181031407000502c82039200784034100c03090980c04c15010790412890341082c1c00820240c85004290012010420303511881d09070396070960040e03c4108412a9502c0c0401040a2421510204180b05031800043c07810420041c00043c00c1c0d840740d00041d01a8070a1080a803140c1244600c50b088550020543e001411124504401c1c000034080d10504105036024910070604100300a20050448400d2a2000110382c40e0a1040146a4280c2c0450002039400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 514254883 1250 514253633 514253651
    0x90708100b010c02010c0c05060304080901081b0315011e020609060c070201050405060f160501020a02010f020309070501080711011107031707080708060d020301180605060d08030c0a120219030f 85
    0x480403c034041a0286448940e5050604001c98181516440745070030400002c00c00052204000150420100c00d07030380d00c6075640790440c86844030111040c848403c0002080462520002e504224074009018101017041c403123000b02d1010031003011400355000d40c00503010882404802d02c96141c3c0481e11402e11400d1500300d40008009014501856000d41e40004406162040c4030068034800c01490680d003010840c1498240d02175000710400c60090341c02d01a01450700c15045c004d407885100b2020041100ca403411004445641c4040d00300010300202c0403080900e81020701884d620001e04891711950741c880c501d0000c028008002110244941100c2440300c40c590220b0a650400c084e0b01d00001e19071031b0701c80050314080f04860000d52649c81e00e492041946181c135850740700140220020841d680e01c11003408000c2201c188010284c1d20204001880c0007901000707130804c40ca4624207040e52080807584802242d0120075111149440d02410500d071036450b000d14119400128014002126 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 514256133 1250 514254883 514254887
    0xa1e080303090c04060e1009110d1e0b040605090a020706180b06090703021801111c20030306030d12090c1403120a0c02040f0905121902061302010309020117090708100b01 75
    0x1f00f107000d494042911028150360110a14043d60420580758804004039468011071a03002c14a850700283c00504210115900e46481d21a031000c84d840030b49982d01e00d07030743c3c08241c000a6101c0f01c2c085690300d41d10070394004000c411110781028548914207100f4103040050401105800c010700bc03c08041c0100201c03d521101002000d000034020300702101036886140d4160f0900d8410084c801c14184144030801d05107038041000840c0f602c0301d04080ca0001c036402e102d103890384400c48001d9010762009400c03460552180314020035440305900c000400514568803058210f5140d4460a1080c9103540344500c14075081c01039454005c506d05140e85401e1a0b00c1001c2c009015211f8080d02c5650349100481e08050940c0045000560200980f0340111002441801c0c64200b400344422501c42060307001d038503500008010b40120034160301c3c11450b20361580110054045090101d04104405a04000c1c0f43c41e9019000e02491141c0301404041d0300342416940340c508258054440a410001000c00c541d03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 514257383 1250 514256133 514256161
    0x10b032202150c0102040f0506120105190305010f090b0f0610050912030301062114010e06030a020307081f0b10140c0d1e0e0a1e080303090c04060e 65
    0x10901421544440c00a0000900344040201c2040b00000c000032030803444001940280195000444991486a1a10f013400450301030680900c250010b80c10050155140100c40300c403561640000300d5070896141e84c0d80300c0c25603080780c844500c0710b515071a210f420454045189548071940c40404811494070100160b03060a4440d41c80c418000002170410076522403122000c1c6055298084035500c1d69501001404500e9031030500d0035041c40710740c540f103e040c281d00880344400a185003030b094590800c0c0001e040740101400321945486005407103401a14148070b40d034001d11007000038102c5001211030600c14641071000710040c90707180c0601500c0303a0f56006100055a80d203403800030075a10354000da009007071041015a115502c107052411107203d601c0710203a0784250052011609505147c4010303144a503e030f103130003a444081c0031004c2c0900194100700f6000072006042190005a03035015403411a030040d40c003200290000c082a0489049c14003c0e5402000e8140c2c00410300d00c0e00300504842e403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 514258633 1250 514257383 514257421
    0x3f210e03120a020114010314150f0610120f0b19050d0f062003071403010602061f05060409090606120302061614030106051e03070203090402221508010b03 68
    0x4032804a0203042c8980300b5030240041e0703544090b4407543c41d6100d00b0074030b4040c1005550500c00d442081d56841d00c890744221844c0c0140c2074140c0d2200036841c0c4104102e086100442c502c810020205005695080c0900680310301e0b860000000805036020024030030060544208402c007040c07903160401c0302ea115a0100040da98000743c2001840000d8902103010704008100070ba00290b00302d140ca603000043d10020341c040e01c801d49a404403000d0713400400c682800301f44549030260300424009200ba00305d0f640c1e004103031240e0541a0f000d503602c2c1e10000c0c3c0c0d01d8020b0703002141302d036070384a00403020020036200c0c0c1c01c064200300c1d6410084441eaa0f4000f5643c4d0402461625074002c031414565143c0e000320000c3c1608828005103d89030360b141c03d0000c0c9150040320020741c08441410641c403040034242c3c11a4056400c80e400340d0b01e004250001d10020307600c50360144a9803210401562402012071206001034061400102602115420000c108580c1070b00010810038007081031204081c03c000041c210 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 514259883 1250 514258633 514258663
    0x1602030d050a020405090108030409150e0106050703170109020705010f050105150c030408100b010e0907020d031e0e0d080903040e0a0902060d0f050106030e03043f210e03 75
    0x5942c5a482c500041e00583e4000f0b03402081040000c595844040080c00c16070b841d41d88100900701100c401e90b90394501d148592900411451b0051120520800040c80c0306402030600002d02c20001c96403040c0a042640085800c560104130b032410405c0a00582c0005160b00c4414811941082c5c0000d0201da03c01004106c0300000040b990304a8074103005650040130f04c01c0c10b4070a84400f45a060014000c20b030001800900404403003282e034949844a64058000c3d03500170401d200500300300303400501421401d250811069040c00480b2201d0340a00b406a00f0f550303001d006513440704640139100e40000303800c949441d041404184203d41541e81840c0e48081e103a6008600c1602034000314032140701d03000918803a9070501c1100c0d00d4408558000b641200c006660400020303c201d410b250300da0095001e102c0d0003c012840d000c444520000b24601d141c281822046444d40203000b4031400c01c0903005e0115008015482101100c031314500258069100c28101210007100030000a502e40240d0304804039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 514261133 1250 514259883 514259891
    0x3050709030b0901090b09030a140c010e1e070e0c0d0f0e010f0b101103161b06090303080c0406120903020c0d0501090204110909150d08211602030d 65
    0x5108201150007581c0000e411421400c180040d180a8a00d400080c1c40e038030510404a10301c40c00010032100d1340000e40c1c0d20030b19654100c3c034465855501405101c019592914001e801072903062194a86050301c0140d6880c52840c4801030904200265202c082c5145940f81001a00700100084910250016000040a10301121400e00030078030441d14000701d601c0d180b00c02a504000740d02400789180d04031a549840807102d507041b0b444031040e51000340950028032044a240450711006110181f0a081c505901c100901ea0380002d595554480c0c1d000400c04030040060503004100540c112042040d450715060806030081d142c8400bd81061009940c2c2d100103100b4103109200445101c0f0700141100c020a40c1400e0842c082e201c0d80310141c2c030a51034400303070300b103108000800c541c070b103000217003c2a20a81c1c43c035411010b6038070100441074000312800421030005a040c80201481c4544101c0e050095064505082c0c1040380182202e03400c2d40c1c050904034100d030f00042610000c4402d01c030081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 514262383 1250 514261133 514261141
    0x2070e15030703060f05090f010c090b07021c03080406150302150a090f140418110d06060b0d021b0a03020715110d050406020d050304150e0309090907050a0602030f09010305 76
    0x391411401e94006482c462074245e02440b4901280c20550080c42100103c1d083c81031110900c46c00c0b00d210914850108001d40d9003048809100c10140500c0e45c0001c0580d1942c80c401c03800c620003110706100840c0000d400a04100030030500d4815043c0401090182280a07415940407900c84900c480b25290240d2022a161200c0b03845280c41c0c5000c1d20071104420701d4070356102e421100a0040140103441541852981c1d20444640711200c01000d820000c49080541c6020a10409545296064903040c1c0c44660201e41980c2450041280000d041401079442041c1c600c0808070070070300b0284001c1030b04a241540d01180d0300190080c1070f40c4104464462a194010081d52503030309185170303055a4094091444d5001e50840080d1040f1803180d000e0b11903000b80c1000c100c07500d21084078014403070700d41003010011002c0315500c00c0320815a030008aa00d00040080001c0c0c0c445c80403510b101156000200901075420603540c2080180700e01c0c00118107242c1440c0c3c1d07658150103103040c0d00d410142d41e04001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 514263633 1250 514262383 514262389
    0x303070f0308060307060806030a02220204180c0206060d1101030e07090606020613080412020607080c01051503011a10020a1a06010f05090609040f1b0e0405060102070e15 75
    0x11221a60322001021504005203005001501c0c2110964441d000310000001c0310390060443c50b102c0c100c0100500f41c0d4052503420001111456854201c04d02c003182c2c401c96a0440c64801400030b004c400c3c0801a064403c1d01c018825580304581200454000d80c0c10f2103410b03103406080c064000d03400111046c1c1600385400490041644e07072440000c910401d040015080c0e0150701200540f42c007a400c2d2040c658542420348406410110000c0c450141000200708445d4641500c20946200034441403826070301ea12200d402d900241c4071000c081c1d5680d000e1000c0c00e40d00c010340c1201080e00391300034000e980c01411044054035014034090b009d40d07500512259458800e102d0220340070350040c201303504141c42da0f41078586000115021404280100312402c07501d0b0047c01500d0503000014161450b0004a00034400582082100e1a00d500d0300d9450000c0c500d03250700c42c1c881290415550300358180c02c10300100030680c0d002400b03a0b070540d0400a820701020841d1b58140f94481210044562003000c01804 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 514264883 1250 514263633 514263637
    0x714040f1a010c050c0607030e1e06070305030c04090203160e0a061b170f04030b010609151d1005070b01050a08030403080a0c12210c02061b120106080402090109090c030803060303 79
    0x1741d40c8031000103040420142c02400704a01040c0583d0240d024902014001c01190345460900798000014000b8000082c03240d402150300c10349452001f410070f07036101c0814085e82c1040e2400400d070326501c031900164030f506c048031020801041701c084011a00d8100d01404840d500c0718080564500e50a600d41484071000100c11130100400720075595042c00050322250341c100d404103c0d07000203500000161b2500c40e4180e802a1032022000c5407109079124415101e4080b190300010300b1854000540c28540d4400c00e504407046c00715115144d4918151400d0414140160001ea00c1107291030811300040c00c000080e50181d03a40300703101a0303607510949030070307aa02004100d0040c55002c01e000121505903010845658000d80040b0300000d4100008244003030300d5034922040300507482000010405a80d00380c2d450010130840b1045032501d04682c581c0004140260081d80202c2c00e000240011410b1240b80130f40141300401d0208240195a071b280703806400c05100c090412030010000c103000b41e4003481 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 514266133 1250 514264883 514264903
    0x11e05060304030507050607170f07020a0c0e070e030a0809010c020303160f020405062d06070b0a020301051f02060c07020a0b03090a02010e0a0f0b070c03050714040f1a010c05 77
    0xc1096201d1901c0c2c580105190305ca0f01044a83d80145004569502d001e40a10003045014542c0208030f039844400403d001c1f10b0092004045108038045003020800700d420180140a0a10780d80959151100700601a01b0003545000d0095010311220b6002c6944003096491102091901e0f40e44120b4600000e8550301400648410410140030003108000c0041003200c0058070a55013400750f40d0300c0400304014030f00e4140b014084003000440f4850300070700c018211240240c1c000c080c2414065181c5503803001c044115a40140c8540c000014441c3e85003003c09a0819050110142d0130840100802074594030080c0c54145041d00200f0503508554030243d480b40900260008540c407484d040300113507900c02401c1020b07404034003400750300300316802c01d920040c0644035654020003125140c0310801c010b40c0c0c4100003d550381d000c40900480010300c01d22410004240c52030b424800c1c21074041c20881100c0c6083c00c1c1d10040c918011084114410307018000e01076900908180442c0c00c80303403c0050400361300803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 514267383 1250 514266133 514266139
    0x9090c031f140108070911030c0d0b0103020c030703090e060901060909050a1d0a170306100507140f060f0606040e0105010f020f1f0f1812020c0406030b0a050f0708011e05 75
    0x200101310008001000c804460711458288044290307005010b19500c026100f1a035150000c00c404000c0d10f030f4a800c010340c0c0000c1850010f01e48a002100c260031500001c100700c0c00103a4503c1d040112949041e01590802021101c1402c59403601d84003500f07500c00c2d841400703850b80c0c80b2000202d40c0c2100380d001e2055404074440034504511300e41c0a058541e1400c0e10100d4090701410401d00e00b003150081941e1159001600340ca1801011360010744403904407213012103c0c0e4840106502c0034440900900001089100041c0302908052080b00c2400a0080c107050040c00c1c24041041104146086581156420300b810506020207100890810448602c0660381d03200d55030f0103e00480c903200c00b002da998109002080311440c285851016602c2c0807081821211900310301e08007048040c2600e10ba40340c41401111000381c04803010409866482c1e00a90303080d8036080030480e04407030700e0284642c000002c0201c10000c0c9001400941344000c18091004a041e100001d072911800800c10040500402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 514268633 1250 514267383 514267421
    0xe060d061107061d0a081b10020c07051008071e051e09040c0e100e12193e0a09020d091205040e0c03100504020304060b09090c031f 58
    0x2d42020005009004d000080c0c80c52000081d42d40c82002082040c400ba80c090071080c9445000e040d5090800e50601d541021802505044801040a48020302c044082c04015060b03c510700f5040248984541610000707010480d82001950341d0f00031071341c40c00c038209003080c02c440160750f40080b101c1d03004000d000c10f04a10032481e552250040b0201a0082c4d400458051101c641e40070021507411590316031150b0800d41c4031506810080c05403010b510500800303000503074079012a252061070704c13200f034410403403200000c41e20f91309122200d8080c02894a464803022002e02c83d950500300407000c0c40e0040d02d02c1070341180b1000c1c01d65031900c0d603901c01444c4441c0c0031354982c015611f55500500c403081003107810320903404084250318010801d860450342180c4840b20681d8896005c80110b500040540c0080900c0c42004030f204d590f544095809035000d101c1c002032000d107200c148040ca07400600795449036488483e025511359000901c1d54840300e004a001801e000c50081140b02608800031064594004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 514269883 1250 514268633 514268647
    0x60224040311150a05150d140c1e10030e0a0b07050c030403050106050a06020708071712031326091c0f03171506090d02030703021c15060e060d0611 65
    0xc88035444c0603046403141045a5103403040c00c040482c0ba0b00c5c10854004041c042d08101280740c503240d800c4500c1035442a600c032100b140740020120307881000004101104c141e480c041a00f402c080b842d280e01024141002400d01c914403031079882140120042c0300c1040600021901481041620600444c82c02207903101e940701d1a00030301a00950007240c0c02944003960025a140c8000b171210b0442d60a500a000c209041211840c02031010751029001c0348200b10700310007882e5807800150b11400700050208041e580d640f07010000c0450080040100c0105100e03400481010b00044503c000f04c11113943d01110f81b04032103681d0712800e034030028148229231b0300900241504804286079a40f940045030080382d403008017100b00580c403001c40d580c1004081c040b00700b26040000d60203e406c0d0008084422996507980003c149c0b4490080c00521240580341481c1000000b1001c202049000101803100f14180200c00304000d10090446206000c0c0304030f54001c3c0039665100e8029004691301569035114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 514271133 1250 514269883 514269913
    0xd0206180a05120f0105061c031112030403080603010c2c0d051c1b051203250203090301060803070f1707050106060e0901120201080c13091e06060224040311 69
    0x909408299550b501b0680001c00300d21380a55003c19a4201c8940300c0b40c0c402954404135650505502c0801e441e1059104144031001610061445a4840e5807a801545008002c2c1801c2d00c101100359424000c07c1210550581040c0c15000d05803138040c9100c0300441011000111507140c8400042d1550144408020031008003142c5040540c54903202d00050304407080072280443e144440c05049508511608041c088480e4004d68200c3d83e020401030122140d20080040110030030112009644000343c102c18904003030003040c00501c0c030b84000c2e605204050301c0314061404040c8005100054110310380c10000c20340800da410307450b00b02008005254650801810304400c40c203035540301b013846000001d172040d059102142c0071541131391510304549a250459000e40c1041d5003580390340440f00e4000c650f801040c441c44808040c0000c18aa1038660900704104441c6030b84c0004046401a051032012003000c164803000700d0410f03602c2000b442d038840c14112000e000c508207501c298015001c0b4030030b8000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 514272383 1250 514271133 514271143
    0x18210212072603041113021b062a0412080c07080a06060504090206120624070b0109020f0f07020307050907050c1b0d03031d06090703030e0d0206180a0512 68
    0xb000b02c0780070b0030340001d03400c034107902e900044400801610281c041103907981010009605004410706000d410407418641101c2200700e24000881103501440410040400e20068080c0e840f4442c40d4141d28060281022455031145000d001c078124581c803440d00c00c000008040fa442c00341c001c0181e90400f0744801c1d00d00e48800364450161082030500c03401181d01d02c0d09118140b001a40100b100d443c1c4800c45080d000502c03401092030754081c010300c000c260941c24082d400c501408540d01c0741070b5178040c0703843e243c0800c02d0b06030060b00f4464418841140c00c084088115552069402e80c201c1d202e41140c40002d182500640129400800c02d00070b00c042e140c0c0110142000807001c1013601c03843c005222503011071326a09150558442401640e0502080c0698010b13840310000914900c1070b410b010320040c1c680f5409490a0341503034130080040003070590001224182c80c104848016014400c0d4002030014025920380d45603504d40c18012030910b81c1c402d5500e400810300507000d140240803410a480d01c0f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 514273633 1250 514272383 514272413
    0xa231207030b1f0c0c090e03090102101503030809070906090203040201020c0102010b090c090d0b01150215160827010e07050904020a030b04050a051b041821021207 72
    0x82402c0000207050303407420070440d4811800c81003d10b011031250450864250b481c0940a03a0000034080000c10412031901541c0322104011000310b54840240000a1a007a800071036034408500c3c0215612040b0726084001c81120340500d00702805031900700740b003401c2840e90351254014915080000034407084a40103144070b54001d07002d881c041d640000c0164240da101c6007801d40e004c00c0140003c0c109413145000381c41e01010180c6100f10350000e0f96500030100c142a0071400802c182d0351a4848000e5040184280c40d152a01c221010750a01210000070ba032981c404440034800040d00185100c0c5940607a800301d1550741807204e01079004107004a0003450039400c05022406501b201003070130704101803101d01030f0758040c0200c5052031440c1c4410201c0030018000320341034010a6594008682c040000b881300049485410700312080a00030001111301c004001101d032401d18240030003140f01074030214462400090000203a90241c40b040b4104800c0344180c004248001c2003800c00e000a1081190340 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 514274883 1250 514273633 514273637
    0x705010605010f020f0d1d0613030c0510090605300406050114010c0f06090f030512060f030c0405070e030312010806070503040c171009050303040c090506060a231207 73
    0x1000c81080c1d004c0342c442080004022a030b42c8155031400342e944c0b049142100518a03803156411400700180084c4040d8000214608403d418240500c18001403c80110040030200c51580b02c0905101c4c0c040c20f414102c0c855070703050180201c0c0b886103c03000c0024450320a41c80c154030054105290300d5841040005070380c10303105e45141000208070401c40101840700c03400140c4801071300d108c0070368031242050b0310024100c0b2a00c0c0c540c0c0103e4002052a9000c130704035403107a118203840341076540321502e0100d0020300071449440111141c078225180812010341c203403020b03a0081217076941c1d060160f4160210350181038241c0300001e84208c0da05818600581a00c03000020b0300d001351240e01040300e40e80802e80380036059501d0070100f040418030b1001c112010303251001c26141c04840303a101510407115010425212071700700100300070070890042c2c010f1015101f007180800280c02c14102240c0d207406141c0c003110500000f40d200e15400003000140c51b1183d4080c00d403582d03030b580780940c80f620f841c4419140c0c440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 514276133 1250 514274883 514274897
    0xb040e0901050c16080706150806070f0c08071b05060a200d170901110f0405040506030d140d0906020c0c120d0c080f0c07090c0f18090902060f070501060501 69
    0x501c0310b0f03c0714101e4410300c0122409440042c6140c503459216400001708031030303855444c60b4000c0040c219003c0f001c02414000f000e8002d5241000016103100000c1034218100a6595580b400203503411090342c10f400c1e0091030010b01076602014030300d54240c60ba080039500c0344000c610441d281c0d0384488000c51152001c00c00071303c042d54101a4903a039200842400011511100381800c015031420102a400140b24001191002c1c14100c09540c0c1e60040800040d0b54100190500142c02c15004035034101310309600074502c03806028802444001c18403011402c004000921501d645940d42008100c560800000c540c1c904120048a07500c80c82d890006028407040300d8038101462020030700d050881c1c0c0940700d081c074028041d9640052a405072a1142400c4c0050144100882c0b04000d004094122a24002000b40510101030840c00000a4240800143c041000310200c00c03850b4001c03c4030032049001c00d1440903840001c04501580380040ca82c000042a01002d0002c150031840071904280c0700c100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 514277383 1250 514276133 514276141
    0x151d040b0a1e12020a0b09010207090e060a05090f0d0f02030d050a090501180308070e21011401050609030307020603061c0c0f14030a0b04140703050610060504050112150b040e090105 80
    0x1070f040d0300e5510060340c070020400c4100255803904006003641d4505105858805495140b40c404130340783d203801c0d0107a0782c1c00b413003c10110608520a1503040700e001c20080030a0280100107543d200c6a10f40b5030b20800601c1c0b5504102d0b02c1c002c00984a101002080500440c6051440318000b4a000c15041d540366080a01c0b401403541c40314000c0c00780c0c640580e0385c0c19150ba00c403541581c07000300b012802500807050180128215101c0e0103281600020680003140d030302e154600c000300b098410707003089224a02c10000f004559800004548a01394166441d645940d5510300107a8800c3c0051a0003245030218000c141c10403182403254000d0b104504a03009070652203a00200c0541d020418142d003690003501488045040c4407a600da0051140cad5480342202d103064030381c41c1449500d5100716007903440350050108214190003500d0103043c0914002d030803d4a0600000c1a003031120311046040c07a80d801080d03504002c0da20200024080f00621240c0e43d56807034050002e1048226101c48407035183c10041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 514278633 1250 514277383 514277399
    0x60b0f0c07060314070819020a020c04291933050a080408090f1c0b060306040503030103080a12020f0403060b0a030809040c050d05040309030c151d040b0a1e 69
    0xc2c0c1c10040c02c405660306a4171010701383c850740c0c80031704020081c0783c0038801000908813600040c4072104003a409440790912900503c025a01c03041140745050b4030156a03c42e5040507030314109010310045075070400742c0840c4070400c1c403030710381641004d80c4005d040b5001000044908400b034046000541c0c0c200103107601b105040b038581c010a003d25001038000008600070442100c00303041c1ca00002010211080c18100004500c401000103030880d401c1d45074400302c00d0280801c40f0075400171041c1c0c050041840c1c17907070b035a503101e110501000702a800b01060041c2c0c458414512449698240310046554a045800c00d001c140c1091004550b807500b8040c00310060709111040804072988006003034203240f011020000a8100c407854201001402e10000088075a9809071a016078001d80307941e5803031821070078600354941d200c0d0002c3c400710881030b115840d000d07805003500140d581c480d800d0011024048000401414105c4041540040020004120060b01ca015901c09886803211600569980e00e10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 514279883 1250 514278633 514278641
    0x6060a050408011401030b010905190b040b131e0608030702060a020a0c091407050a0c060b2e0e0607032a08070c08071205030d020f1605010504020f0103021912060b0f0c070603 77
    0x40c221445807812f040309902251038005552102005001085821a08020601ea0303980ea5800402094540d0716141040c441c01d40841c099501d10b01c01030000c0c038102151035035244645000240600800190710510520070720150b001541e00ca900d00039030036a5a1180d4001e8001502d02004010103000421582d50040c0100d842e03912450300c1e490f8504a668560750000c083c60702c4002e8102458410740c8516002812000d1010490b0b462400e0251034070001c024040c1140a0300e983c0109001c100405c00310b1703080b0700515a26952442289106401c124900541c0c1c420341c2c0d00100315040c04111401002030a04151080d24110002c65070780f03681d241c1d240d0100750500100500340f40c0040103030711700d01d00700d9400401d024500d40c1407041c60401903d4071002c210f0a011020303034945c0d6448051108524104001000718982440d080d82080580108940002000b41002c1c0610005c06001c10880046410100041c401603000e1a210748000d0035008296210038449030060203000b2020a2550191003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 514281133 1250 514279883 514279891
    0x3041e02090f150d030201020d050606091309020a03060e0c0f03030f0a14070f0c08010b0d020f1c0204020c010614040204080c0112060308030112111806060a050408011401030b010905 80
    0x2116604640b1401184024002d000d0300ca41d1154a40207a4021191540c1030026840c03403195000594030404100c0c80800c546001c0c000300d10074001003040c040950342d440b0301c03680804589038000441c42118030000352010b00551000f003081d401c0404400705a080420b95480c1c070b081c15144800e414078102d0806d5203a10420354008032200041c0106907142e841241410400c3e074902008612f0036100b034841e424880030058080f40c242c4203158040c07046050030f009000090000f6605034001c65400d90000720a000c2407000e41c4d0040091300c8507030880396000807641e0441c4d03401600c03c55035200c51280440c042c029501545100074100400152141854400c0700c0032210104c000e000101654401140d040c00701400300c1402940700c11002c0003007040c030301c000c50080503458072040344594189072140d00c141444607602d200b82c040f151140d50b22821446029401031048600d640d403101c1c0c402341520310b401182c02c190706079841e100e00c0106c0c410062580d28183e03802458101456aa10070111095a504071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 514282383 1250 514281133 514281139
    0x4050f0103050403080c1b1507020d02010605010903020d030309060504060f1a0303041e09020d0c0306290a110f070501140309070303350a0e0102090d1515030803041e02 74
    0x10b40060142500d50000e0000c0c00450045204c10903c90066545000c100c41b00700c1323401c0d15551044c00046a010003070080710310b070140000c1c4a4a40740c04000b038540311742d030703c8081d003d04500e0b41018109886540605205980418204200e0134103060a00c0101506034008100500d0500306c035886001c482201600c803000140114905410248103104420300b828003a0181c040441011641c040c65001828000e203400340300244c84035150100a050315556480011400e030100c005550f08007440000d0001031000104080e42c90f980d20004541d0140c110f0300f8005140508a10b00b2248800818070004498099a40c05100b10050040e41218030041d6071500d040da11074002000064041c03405400060b088070b000c801c1c05490317100c203c1d240f10710303516904107121407400030002e94120300d100307000c1c03204c102c2da00850512000d4400314003031591448002d441c103880881c1e041400c0c0f80e190040d10300110416005c00301c1e130340d60f894082d1240c3c105860807220011691401d503050f10040e07013212030302c0e5001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 514283633 1250 514282383 514282397
    0x507120c03020d0305120a0b240a1d04090c0e0a060f0e1308071b360605100906030e030f040611010603140d090905010503030703050d0e060c04050f0103050403 70
    0x507400c03c25454000b1400f202484001c4c04030315070145200c54814800e00c16600d002c10020644404c01c00c036003040500c4404c60b039404d080000d41c4c41005034150780d98420715003800c0341c40000e035040c100240c00203004019402030034008642d0410502401075811101c91240c0680691202e54000c001e4417042c0c010a0841840400c0410190384100205504100301840121240a45885020301c95002c0e120a4030000c013201d1083d005102c0105a40c2d008045806d84044080c0118040b990800050441c0c84404007911901e041c5074065940b01400074030f13004014030405a80444080c1c008201807007800046441e00b1200c0700c00c24008411101e8180c0c01c00080c520702801c20380e06550300d900ca142d250203d91f50321000400002c0c8181c9a001d80b5041d46c2c0002d11645035170541c020901140390b04805a13a80c2000010000e6440000540d07040303e0385800d0464540181103906002418100c581140707a2003204207014080c40c45000520903108180c6601c954001c80c00b00540075030380305490040c001000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 514284883 1250 514283633 514283639
    0x27060605030303010333020d0212060d050c0409110409060606020609070b0901200109081923032e0611060415022101080d031503030c2409030c0507120c 67
    0x100000500f06e03150315a248000210182c040000c0341c2103021604000d5600180130281c40004402041c0e00080444840d0940c04403607640300d4540d443d0500381e60140d51500e11403010013030b0b9114540110340c0003a104003c4000c0605054019296502c0b0f010050300a600225209900c045003502c1130324110300d041840d040f507010044400000d84408000910f850016104c1100401c0c011030983e940224080386d11001484407041c807075100d01b00d241040c0b0043d907160f19101d002100d4a02005415a6441e5859503901c41c0d50810030058400c0740307540c0d040610709100c41c60403400c2d03046041e18481d82d034815900d041c49038400c0e0b803000180e6014000e220342540c04074919126800a200600803141080c0c90701084800300c140c9a0070070303040803405410004c0c0c4000d102c1e40c148141007520407250544c909461031030314060000c80703a450024000000702082c00508941c0f50320300d840c4200310050300308600d99147c100209400da0744d5004540c24052950300156900e5405100b0260507000100307001c03010304d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 514286133 1250 514284883 514284923
    0xa0f05070b0c0a090b1c0c03021204060b01180914010b03070509042d1a03120304030c0c030b0108030a023030012c070509010201270606050303030103 66
    0x810500f02c1c04202c014040030454100a00250115216524a4031401d005610120b4280e41c0d007d0380b5001091720500001c0404d071000418250000d401480001e801102d03a00120bd01a02d4103a036004041c900d0400056607a409601c0001000d10000c46182280d07281c1404101c11303c405d542d404001a800d00540a079454150301c605803005001c0303642038000c020069040c04e01c040000d400c000a40e0f40312481c8280701441d0f41c040b00000011000750000c00c1040401c500c95020191000e0108400450000c0801c14440401400395805c4000c0c82c07002c0da55000003680c1e07a07011100c0d94005000d00a000070000d03800040c6100b81603c880c0101828410110ba0640315030007011417910000d03900e89001303010481080311060262102c455520040d810800d4003141041040990024005080482e4540640159045812494926109944032802c100403809042d9081c4928005014194442814240e0103000500c0c18810b03601444110b640d0400c0646a01003440003030201080c80c14000d100c54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 514287383 1250 514286133 514286137
    0xd050916140a18060509100506190e03150a0b0901030308010501050c010f020406030e1e030405010c0f061109040614030303130311070303020a110f0f04110408120a0f05070b0c 77
    0x400c05422120810740d142107107942011802a42c01500f560384a05005ca41440e080060380061017040025120340b401001c2250f42c403401c0e00715100d07004200c40c4800d406229141103058020b00804030b544441400c00c80c000521401d48140d51100d1400700032203110b05000c3c1481d1304880c1c068032a00e125038a442c5c01501d031584200a501100c2d541c5600548074404140f01501c0900595a0000343c10018603001a117449038100c80e0004d10132140000c20010100001181c0545a00b0301c2c0120103c040c9d480c0048501c034140300300511207410040900705c911305240140c400d20004480c02d02603103a0f81d12070300540c442c25000032a010380040001890402e03001101c24a603602c00d14101403040611240181420200c0e0412801070304444c031132005104251542e00702004040b0b0380e65111180c1c00300000c0d66000100316441c0190384412000340d124801c0c200380d50050a0410660b074030b414412805681300d03072100c08807002103800c2c0405480014400c509849116500002c4040f00352606034203605e00f5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 514288633 1250 514287383 514287419
    0x703140109080301120b0718121401020307030903180509130330050a050112111f120f050714160c09020307080c0a1407020d08030103080d050916 64
    0x29640740c6100760000baa400b0000c42c024040b828041c0c2210030702d0b00e850034003801c020f04080100810100c0c00c4035034111140400003110041c0b440012000914034000510b2070710000040c02652000c010000120b4264000c000f1052281d503848107540186c880d586402c0c017142c0940c1d0f40180c84080003d00307a00e03d00751101c403214007a0a145003500042c0e596030b94801c81c45045010f52200c0038480203507189650140a800c2540240c00340407542c10402d00e40d80d80c80070385801802c0c0c030415012083c660748940084500ca00011520341d01615540c04d0007610700d0803200c40030f2008030320f4013000d08034404c4c01c0c1c42a140107410641e079520201000300ca070003000d9001030300b450b40110356104541c0e00040501e15204001c1620031405a12843c1001e4043d2000303400401d030307540010b407c0081841560380045002c100d2035502582d02d444110f84d0020510804e111071000b00b4a103400000401031217200c030003a00c00284051400d012503030b01d50f0100c540325441d6807005a502c0301050002e00c004542800b101e150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 514289883 1250 514288633 514288673
    0x30b0423180d02100f0902010804030e15030901021804050709061202040f2409030302061b160606030512070804050f0f041d151308090d080a020607120e0703 69
    0x101101240d080c10042140b003141c026034000d1414103032000c898003408448060300321041007804e4030b58001800c8088010001010004010320180282d5162501140400c1000724565142d1416101480c001d51048640711802240c001c15501035113854020144961041d43e0303620001031401c0c0c000d42c1c0d02c003801c050100040340c0a000105441c14546c408400400e1210000d15000b0070405407000400413030405401046111402403001c260001201034111036888500300c4100c00c101201d50540c010302000c03200c40b03a070300400002441031541141054034000e038152051000050100c007424440c100009081400900c0100203920f01482420803010300580310400350419040000c048644c000c1c00420036000c40301004100784410400c9010441440da101215410f081c000780da80c890507030000910000002a10100e1602e6010480f4030031980028010380f280d86502d80070f03480b60002c0309c1c0280020a103603a0198511814041c00740c070b100852000e0040d69044d0348400c001f00a440440c0d000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 514291133 1250 514289883 514289911
    0x8031602150a08040c081b0f04090f0f0210020d08040221030d0e060c040b0304110d080403150c03020a0c12091805100b07030813020114030115030b0423 67
    0x7016070107840003440c041e0310540d40c64042e80750910b032204011456401c00072442c3d10000c0b030030800049222184066101c00c9500709014859180054050020140d00a04500b1801c40a02c2006041103510411074403c8806001e82d1070942c504076079926151030300c40300080b5040080350241c280211001100718115031800140158001000c2c51035006100919084c0d88c3c9100440008030140f010541100700c074503940c2d01d09854100e001d1a58000684050320203102981d001c03400b540c5002104010541c460800b03512a40c1d03030f0821515102d86400b80c0ca0314a41464600302070306100348212408804280c5403d200541781e034a4181c0c0703141d003511840b0188581d602001c2881058a003000c19102c03010301c00800c3c1450705d0b61001d050341003250305c58002e001050100000207038100400b290300401d03600110001902600040368040044030304640c1e4201c0000010400c801140588408401c05071400e00250304608248011140c88100b18450b03a045006d1010691804008140e00700c00c138040b080e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 514292383 1250 514291133 514291159
    0xf130b0916050f060a1d03060c0304030201060608040c09050a140a0608010b03061e09010207080a0908010e070b03190e030a02031201090501120204020901210506031608031602 77
    0x184016016660640280d000700c003000001030000040c003024103801d8030042c6010080340d0205040d4012050060706104001901070072030550000c2428009030b004040381c4681c10020400c00d0030794020345094005508119000c195540603400c03450140b40e000c04041d1000d80341504110041c5005821010030702c6d10380c40b0080b88803001d4910540551404040000c803e03242454072030071610028034850003500030200700020700741420176258442400e064a8445076035022030700d071b00a102d090f100400b00704020510029441d4072000c4801601c0400008014807010025820356440e864498a083c5a00420000350540c078280c2d00350104078540000490410051803405085420017030b450380060340081503098815460611440c010b00d2807603000c000c1d80d410300e40c25404041c50004040e0180b41c000848410741e0740300d012a0620302d0460b441c00012102c81240c104007800742680c2c40b0741700e8454011202400c11521000b2004c44500a0095245c18104c08160300040d100c90f8041ea4007010040d07140c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 514293633 1250 514292383 514292393
    0x204082d070e0711010b0f0402130305160e01080a110f04090c030f0b070906050a26130501060605090105040504050601050910110706320f0406120e150f13 68
    0x241002c1c26500d000304410f8541540000c01c01c100404c40c120150f0f05100c920b65007030700c8480d0114504001514096550080944411080c090b0b55000604a10411190781614000040030000f91104500011460b0340d03070706280707a0703108110f02d80502000c9090141091600e41044908595040030b00701140c502c0311910741460516496209a03144c5440c130302204c0c200004292450360004030360074402080c1e13041c000005c180e80507420004c0140301d00c2d01c0d2030000b541074001a010400341c10b1400b83c2d086140c01e54410310580562642101c2960800c034020410500800030744503500e1040c1d41d45400c0c9071a1108100c054180501840c0c144481003080c01c115854051f20360760b2405c1240c507002083c062040c2e425207044a00e600400402c14000c90860044c21744100259002d08650a0b0f16a683c1d20344038100c040e4842d100ca5024100c800182c0020481c1e0014110b401c84961814200311290700040c4150b00c4a4150306150031a0062200140800c000c691003207800c0115a211119a51403d5441e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 514294883 1250 514293633 514293643
    0xc040903030516080f010320061c050c040b0904050c0c01090b090d1407140f0304170705040e1905030705062503090308130f08040e070908010204082d 66
    0x1a00001d0301c0b44100011514030b20100c0440001e58074140b580e51800d80c54a22a071101808000c001c80824010909101035120f406030016100500007591445500380c86001003940025078074406042c00300103200303174040d08181d80450b80104003c0b4584210001080000c2c00010a40212081c0901401c1e146410074465010902d2140944601a00300800d0143c81c100d801c100701010041c40240805038803803400152400d550303000801e0140285000240b170f041c403841c0c0000e05001c0c48041400104c031240b0f51105242e00ea1018250b034000ca45a206000075141800d41e01041c5038003950300034580c0724280e446120034500410980341855000e650b49410060161000c060074103a0482c4010610010002c7c0c20b416085402c0c2000f580102c1d503000ba060130b50003804450094180145d54052060002c90b00d058507501554280d6202e460b450035074440901a512140003451504011680a070148210340076280580c0042c401002140704038000c190350140b54407403926510200b60340e1322008000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 514296133 1250 514294883 514294901
    0x114010b04030b01091e05042108010603060e06060909040213090f020f03030304031d0102030906030901150807181e140402190f0b0318070e0103210219050c04 70
    0x1001581c507032440c1402c400000b01030708903802e21413505955446985d2112210703502c41c02d0790300e0049130725030317032820104808011209100110114440d00400141d8070a007254141d031400e850800181d5241c10f001d00100038100d448581181081100d11014500360484617405480100001380c0e1000381e0b52803038250b441d40300c0c0443d2810740300c4190703008510b005415419040e1050740198114030305920003c1072007450895035448400d41c5843c0c04200c0c3d100b40111800090041e0241d83c0d203041c202c0010f4000c00503120711610002807440c000c90340307000100f0004c04a44c00c5040300c54151500c0c0c2d020000a1403106958801e81d00e91415800350003200d40a100030903425002c10f5001881e081c018440c8411001418040c1c50240c20020b202c1450380081040a54580c82d032440e0300ca070344440414103008400300f60707081c0c1407290400008400b070308074200506a900c00c111072103091040c2107081f9000100c10003a800560060160000014180c07032142141500034000c642c10104660007040841ea0341704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 514297383 1250 514296133 514296149
    0x60b030a1101020111030f0f040305043201090305030f03102c0604053d0e10050a0b0a180504150f051005090d05010f0c0801030303050703050114060c011401 69
    0x1410001c076640e028440c1e88003001d40880c110303256160886081c000300000405241103c04e0420100e02414412025600030740203c1000e0400315124448d0454046110a03000890398820032280c1c20715482100d84c1c20072603500000030340c1080c2d80301104d1041508018480350514003001000150444110140b61010512110503d85181c241c010340c64032900041c0034034041c9041400303101354142071113401c1a0207a2801c420703140b07612480301f009070911151034001141285122011074204021700385180950b8003000e1108925640b032080c48000c4ca203070301c1100c2a6100601c11003140e03902400004581c1030025540030383c01500e070000501161400500314a82c50300d41102480704403802ca00c0080078101c21100d010703920320f812200914074403584001901480340003040100b0007009400c00c0d0749521100401380300700c00e5105030007040550244415000207042c0000300e240139010b441024161644241000f45070be46031400d1054551040c4040c1c1c8540d0b503500b00260107d40e03c0d007500b40c044d090340 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 514298633 1250 514297383 514297403
    0x20c0d0804080c120c0103090206210105030d1b0f050c0a150f020c090601050a12050a05150906030d050903150c040f0e0f06011d060d0b01112107060b030a 68
    0x5030a182c14000000b05006010800480710b18030700000d036a00c000e845c2481c0c08a0b4001c103910100d6014000c141c01c000212480010104042100060381030694400358100e07900d0316045001222508035120100d42134140400d039080100d4400c07100d024a031801501203036580c85030000412190300c42c5a00103000780d030343c01300031580450380010348207a00ca10720704c010300b48200e800d0000b0b40f1810f000350095050110002e03102c1d0b455405150031025000340340e00100414a460000d14000d00f0040300d200000c00d00560202c0b42516110520034040c0d04050b00610860726501001d139820341c4814491985071007010880b211340600200a10710440400760080d46a40c54a4a80e045580b8250800b00d507030883d0b072040154129555507001d910000074a02140580070050300c4400750b13078095105c4c030303040600080c008061401c203400c81c0a03654401ea845010401c4a4511a6210550414404015180c1a1101078800d50a80c0500000c5000385800a031038421207001a240660b820411981076000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 514299883 1250 514298633 514298639
    0x60305151014090c090a0b0a0905040506090c0a12021303060b120a051506010302070b040b0f06240d24080d050405091314060a020705100c140703020c0d0804 69
    0x340e09403401095054454004055164000341d98810020100b03141381c000842c00020700c1c2c2d80e05840c440101300150869075550310740d1400820301c00345400780300d014906142c0401c1c01410201c0b08244030301000c4102a08040712b46034203d03030034082c01c801b44c5003094090102c0e00c10414007110784d1000714440c4100260a502d50418000b4403180c580e44020a034200c1c44800c03010840104164003051900024590240e0300d032030060f0003d0003070040c05488030303079850100310800142c0c0346c2042c020308605052000540e14202044660a5080002c851714a22515407291080701240980b00300034a00c0004140190382c41c80c081d64040c0c024801c0c10700020000300411011000f48006a041449032905515290a050208529240103004003000c800c1200e0b60109000320f855005036034400c0c00003a100d1609040381000080d411000090741c60380108822400c41a0741881280c80390f0102c0e84400302c061044503020301c00c68116500a41c00d50203034240e013028907501c02c4250030710207125200302510b99007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 514301133 1250 514299883 514299901
    0x150606090f2d03011b09050910032906151e120405010501051e0f09040f0c06050a2c011b05100207030306150905060c120313050111040311040c0306030515 68
    0x1030348141003011171000c02c008070300082e400f2030540c050f224144e900e8140350f100c01c1c2107844503906030341c030103003008042e02d08200d610390b1202c0c40b6144288500c49602080d403100380410100d49810850104140320400c5403d180d80100304403141440d04200c0200e0505503450000c0e018031500b160110340596542c00140401d1614407105c01c002d5450120088a14012101003000c004410003400c1c03240c0210300c000350410482140d050151030340403140041c0c05580b020090320913003000004102180c130081510b00c4c01d40701143c1320240c03007140042c90410840342c0c03001911100c0e0304076000c2080341e010f01444008140c041014103024044203100507500c20950400034100c3e42c15402107505003045001141e049580288148182e0740100d0b281035981009101842c90561a0354207803092240100c108041c4103200c0080581550290f80240300c0c110910701030444912903800028200b140501c4e96607094107203940b20086c60500781c14000307240c80e121b407519460b2003020145401c1404000f410060703020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 514302383 1250 514301133 514301141
    0x601030c0e010f14040b1002070503120a021b0f090c0702090a050705030a1e060806090f03040e04120314042108070f0539150606090f2d0301 62
    0x5110010074a541d410f016001010859901c5412441c15a004090705a42d60366400054805c400030005001d40f004420007948940341441014400d014690468120054803012a51581c0480c0e002c0c2c10b040360040021000c0c05070301001c01d5040a034184c820121915000301907406401d0b9040c2c0079898036503e10400204280051402039403c1c20308061010240c0c0120540741c01c44883c03980820301404203060000000c220b101c1c04000d280c108280029020b00100c0d6250060b1210401e48104500c0c50651a92303030721440c0314406114201000040108490345d00c244100003182c54081284100304a81c43c49a02007a100ac0d160441207080b402100740401c20302d40c0d181141420a0079032850007183c041c002d48000c10800081c00f00c0062019100c8482030055035020b841d20100d0060304030b81c1c4d824001c415980b99960b018910a9041d01c60041990a040f94803400e0300901880c5400c29142c240602e004c64050f042c0d030415200c00c2c4801118078070b1440035100300000b000816038110070340101400c0d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 514303633 1250 514302383 514302389
    0x1c1d09011d100b09010804261c022a01020f03010f06020f06010e01140301090c06021c0809030304150f09150b0f06070b040309171b06030708040b071206080601030c 72
    0x142c069400b04101442020042d201c0d08502400c028002c0d0741c850404182c883c80d0b6254042d11840e260f1a0510301c607175420090010143d4440420300c1040740c1040072401c0740306038081e07074000032602200b883d03a00c0780c40c11400e021a19080001760800701032240802e225007080c0c211400e29260100c0520407158100500712049030800002e140315450b113006040150010b01415802c0a0004000107417500c007500280103690f070014640090750350302d050003074a0710414103d2f20b103040081c0d04d210803050711800d45107000d6141100510303d103440d0f59403a0740d50444951150308940741c85612022a21100b840303000b22241c060746114044002401d4a0f208031040c11481c944924160b0420310a981c030746000750b45030943c1c0311420426680b56401d003900d9444982c0c0c04441c6a0b61100360700399080d540803c0b40c03404404050744010b82076200104100041c00700b100c9520001c2c61401c0060b000c07a0003089950340000f000e0500180c1e14035055034140a0b5005600700515650190004004208411102e2001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 514304883 1250 514303633 514303651
    0x31e150403081b03040b1906180203010e091c0e0406050409030e0a150801050d0305120c071106030c190315060206041203060803160314031510021c1d09011d 69
    0x1544c9401da0300ca0f06c0700031025049424a06904c0f4004012108a034070000c06000c0c00c2c0e840c040c2119140703225078003035031003400783c4072610a109000c0b50504200044410b41c0e080304002282002c482514115009450b0284480d0b10944910001500307840d10310404889501903516184030003980020b100d0402a168089602070307a40314041c03241582d016480314191070084030306503060030f528201203d180c05070310054034110b6042c105001042444000500c0280d200c1d0384008084007510040104500044514034007401041042090f410389050303042c1081021401c0c0003629056024081000c000c60390003050259200c0c0062000b8040b401207440528825403400f03100150a010741207840e40141d090742c00c2c204022100d0001014042d0f126142c903104980c0da021707142c4c90001c80c2c410100c0c0304e411800b4091178000c01c1c500c0f91a4408160000420a450001011061004001c40c1c5c410110300a450000d666207000c1a02079880c40351070350080440700318506502c0461410340c8000c1c403024080c071103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 514306133 1250 514304883 514304887
    0x9060a11011a0a030b040204020705060112050c0609090a02030402220209040b041a121f0209040506030a03051e190201140106020a0210110a050a080a0914031e150403081b 75
    0x180b03543c4000541d0b0640340d1000d51200d07652610710125020b4000d45000a10301d005450000c84c0c8035000c0f10110a8690255080b1109045520140320b694483c4541c102d40010802c400a00c84d25540c0c1c0046400c141301070020f101c0081c629801c1c041da034a0008a13440c602ea0005101c240610380780c090302c840c881c000c8508110508540e500c1801380442014010b01840001510082c200f4041c010804e5a100e080507405c0004c4440b98014003e6201000580c0301e2480d0101003001410f000844518032a0703d51582854610f4610700c000d4218080c5800c803618040404c4464151203901446060b20000d680000c40c0341044c1d8000181048416048102190b00c01640307000560b4a401c690341e4030055a08001c02e000034134191550034404001d00240c414403a03809071808200032940140400405951b0f400c0c0642e0301c4a404451103410030510035030650000340d80c0102c4c2050103c4c8124104044011506030480f82e10b51414221400c0310250301082e03030311007080380c003504080d61800907152240c0258 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 514307383 1250 514306133 514306181
    0x203060a0b03010807150c050f0a0b1e04021203040b13030501061d0a1802121c020313090510120b0f011203021b131e0b01090305100c0509060a1101 65
    0x40d038a48081c802c1c10309079803004405a640c02d019415036081f071500070041d1050002242141c07680c41d52520070840d602d0b54408009a8401c5e04000121058170000c10b40c07840584603074082010704400800c1410341400704000001c0d04103010b0004000d000c2e03001c0c000e01e10191460803c0c13230845000d80c1c002c480700659808070360004084000742c0795000c1c03041c0d60300103038080240100d0008400c61042c025000b5001490306070f8800c0002a410300c9903889001c1404101c225000e040340c690080700c02c4403241c804d242c007007440b010390320303800050707005483c0d401c440510b40e80c5800100004007001001e40c0d1000382501841003141c40c40180502510742c03040842c18100c180d543c000d6a8540b4000314100180141c044034030151b1340c3ca6802d0743e500c4049030382845583c400c40000e1200a622805004650b031510003040c2c101d501070031411048903080409000380c070002d040e54401810000f0080f40070480304001c2003c0507074451004d001100c00c1036440b4406080301000d81401c50701242441903071081400c07244 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 514308633 1250 514307383 514307399
    0x1608030703080c120c0705060a113007090f080c0a031514160e030a0812070e0406120302100e03031303020a02040c0215070f051803030904050a0203060a0b0301 70
    0x850420354945002c0c1c0c0940d0b15051030440038003805841450f2200207500307100010844601030000f8502803016585141c890110102c2101c690321b4452041c0f500500007845180031956000d0324051500003051007441241080400310402115901c01041c4014030a11040c1c1c0340310051030181c200c000003000c090510200190f135802452000415040030000c2560040d413140c0c02444404c000d03e1000d403082e01b001c414140112a50600b501c1c0011401d2201d40542d14000400c40e081a80221916281c03a080806494560b50010100c0342444250322000c400c5860301c0c0710b410002c0041e45000341040020b40380083c1042d10340e5482000042c2440b40d84a10441e0100869030050b11411180600941c0d6103070503800c0588a010196000340f4000389406913940120700100a2210f02d000c1694640d2075440c181c511074448003064002071070038807604c03924a40340d046400942c48000c0c21241008000c00024041e103500711140245c4c180c001c8144189410034070450005040d020310745509540c184909 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 514309883 1250 514308633 514308637
    0x1b08010303020706080c1614120912032503110708010204030c140f01050327030c060106110a020103150314010b031002040303080a05060a1a0711010c02010c15020c070608010503160803 81
    0x6082100c9030b02800c0c01f000c0100d070015500c0150400020703070f04005e01c210035180f4160401000103020382420003004520035008000c4864060f000c40c28805503c0712184121a1303150072500881c00e000101640301441001001807500601020001590f105e00758a000c101a0700f0990006c42420302081d081042c6507120100a01340800c00c3c0790040d00c95a034810300c0c030001941c14a56486142c01c00e440c0c04104240480106403840b2442c044855590360341c4012142c2e180c108040c1c4040f600491080c0006600c02c0c2c0100644407810308019210688940f507035594400802800012a03650b050048018241880704001848010354114105850342e100900f0300e07900244441e4032141e841001034496540d8000b0302e0050000d80308528010a851000a00c0c0e961250400f5201c0da1507204441020b980300341034810580d9030617520329940701141e0361a0003c0309102286500040d800f4004001000c40800000c801440c140e9240c84043d490f0005140c2010044100c02c1c583d03480c00c0c80b003400b0160000003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 514311133 1250 514309883 514309897
    0x50f010b150316030b04020c07300f030207030209090a140705010215060a031707170f07020f182403010606050415030b0d0c0e0f1512011b08010303020706080c 70
    0x24107600c0c098080f0004800400e602c4d80415485480030032501ca1003000051805c0680e400c181803860075005004001c4080e00240714484801c22000c1c10440009400300b00e41e4403628840d0040ba02070a8072507001030001a01141d40d4a0b640d4458a004002c0c811401c040440003481000a016000e080c000000e440e6051441c05684492804000c2a10b98903100c1a0b1001503400440e20400d080c0c032a20000c0295100740390540b1854861146000d90a9140c1d0490307070104540c03142107103868925400d008200e005241c0d0294040041d1140d8807032081540782e00c500c1001200240c0f15803904e034094000c82c0c114400000c41c0240c2c9449001c0c8001500301c400c480507208083c100203925141040b044015100050b015038014109035400c0003000803084c0241c0c20b88a4014801031141c1d1002c20304101160200c4405180d07400b00480714116060410b40d07030002102840010441c02003001d022185145608000c0c1d0015a2410040042c540d0501540d0041c03c42e80c9004441c60412446585960140d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 514312383 1250 514311133 514311151
    0x1903021302120a0615032a080f160c1502073822150c3b0f0d0204090b04060b030601231f0216060903020310020f16050f010b1503 57
    0x2c1f00d29201c40c00400584a1051002e221400c0c0c117140c20000501c03101d01510702c282c103845075801007003d0b0320a006030000781300c203541e4038441c0303004080e100e00c0da01c13031a031441154900b0350811000f004206075003c030900081900e803001d0f52404018100403100811101c0b18070360801140240a10003000722001c0d00c1c2c2d400c03009190040c002c82c0d41001558100800b00ca07c11f110f261100c004203d54000d180c0002e411061508400820710300004c0d01440d0142c1005040485042d2103c8512450044c0c80d0507824075001c0d11610258909601103402c5620100702a00c9035114902000200030541c0500010030109501400655243c4411400056500c040c08a2402d0700140c0524113234403102c0324802d02d60391044000d0003c80c060f00000e500e510426064250a00c40034001003001030042d45604100c950240081c030b1602210140a40250441c40030100400e104100350f00341c42211640f040705c0c15000304090310b080b0b92451242070840e0b100b01d03001130051401242c0706004026181c262644010350b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 514313633 1250 514312383 514312391
    0x1130071104090804051e031c020a0320010905060603070b16080c01270c1a0912010b1017010504051b030403121b1d0604051903021302120a061503 64
    0x10f864440343d00e001d1604416001101c00044030400442445112029101607064902c404c2000e11880320065a06140c1d5000d40c1c800744425002a1007417035011103402e010400f0642c0100a00d0149003521798540f41a2020b0f4481801d100883c54280f101318010103072100c0080c0b518241380381081a182110300c0142c00500701044040160000f9000303d40e038205a01490881c03800315800d80d1444c0e030801c0c4020b942003020b00d413012824a03802440107800380310411107139052031050001c000c4d070321054100d64441c1e5500d49140d1001d81e100c50406244108041c2c0322583c000304110119403518a0580c892441141030200380102c00449045001c1b84c1d42c07094040603526074403801c0c2540c01d0184540382c01c1c4160314060090042245140c03002c40d40d03405565451400f48107441030306100802c038848056002038100400c02080c0307030901c0d40304401090354221507a126507136000201020308485002113550703000210541d440d1860b04801e0740c403181000c81049000c1c241100c7c01110201c1e050003606141c1c0d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 514314883 1250 514313633 514313651
    0x405070605160c030b0a0c030c0206180708060901060e0c07030507030c080c0f1b041401051903050f0102091219060b04021314010905120a0f031130071104 68
    0x28054081030300b5002610040c515584c0d24000a810001711080c440e40303442e25481c1040c00340b1074040d41003403190640c000c1400b52910750301c501811070705900001e414410014002070444040c00820320506440c00001000707441d0081c0c0c080348075401003650b100000108400000030745c1010640781d41c4e0350140340c00c840d40540303850440c03c03520a61220324050b20030200b8048140c0c070005218000030126840d00300046102c0014082034408042a0a005c1081c15005100c02c1c1004001840c4404500380f140060035580d403901f03030502003084038840c180d940008590420f4100507a03032002907100e07440201800c000182c0c0c080e4004c840400e0040c01c0c651070301916121a07803640c05503032601d405003408a0025550364100c0816942d00c129181c042440c00c040042c05207052680306610b00d00407001303480001b4050f9520740e0806a550700803014002c1100003000640402c00401e00c003143c0040b40440680c2c04401115184150046a0080006e017003055000140f40d034013095140d20b100395004103203649 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 514316133 1250 514314883 514314907
    0x6051213081602040b0607080318030f040e091c0e040b0a1806030b010b041203050304060f09150f020c0d1803050a0b16080103020616060905030307020d0905090405070605 75
    0x2403480290041c240030a101070800d81250100754420301c2100c08001160703445c2c0034000a4042c00c800034084800c01d00024090508184e02521060a50b00960b0320344841140e61a1181c3c000750440764503024140108801118100541c201c948044101103407241e07042319004000b00c100b030251070301445e16118180c03c00d031111405c2d900a0410b488244406d10f4403480d00784000d16a0744010348102c00c00c41c00020b03d620007841102c05888001146140c0002079071010b0303c072540080c00c1242c0079682c0d035403c8034600040c3d11070950000d2051044040d82030203d01c060054482c805d55000b0020310402841000b020009200481c0320454202058040010071400c0400c2d0f4a9520241c01c0c2d02031204444200311091000c00d1040301280d4140305010b1a1000403610300009000084d003200040103001d01800e2540500c41409108540110702c210a5590b0700e0f0a6400642c0c2c0d010150b070203e01200b201a0304860500c010300029280d01e200d501d403544450b40c0d1000588241414402c0010342c09107018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 514317383 1250 514316133 514316161
    0xf0b06040240062f070605031003050a0b01150e0a050d03031b02010b0a080a02010e0607021201060b18091306050415020408030a0305010e25020c0904060203060f030304060512 77
    0x30b944042e2038030b0350741c0e44903000341032220540c002281035559800010381c40b040d811420040b402e20300c0300414000c0c3c2051000d032140c0c1e101034440f604004c5004000400900100070104615110300c10050351545840034607544000d80166082c02d100d0700f03190382c030602d49509184008403841200c103a030a401803800d0a80041a003500304001c0c0c003824010000301c00780c054200c5c0280c1001554414000c660b1020700544852404a0082c006640f00b01410311914040c0e000d0881540005c00c5490405002450070342100d24680c8901c0360002d0119080c0d0040901902c100c2420009507000c3c0024600540200c0e0020131083c402000c40d130780c2c0c50100d01841122554500340c400e012004550b5039840303200080d40c9421034641d041c00282080000b240a0301510003a6000d00c401c540b00403020110410814035440c001d05400c001c5204620700740200c2da0b298100c440c003c03400f83c000107940e17040c0f075824050002480c0352000d0103603004200400041d640541281d881d0302c410b0030090f1403520703441c440e09225 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 514318633 1250 514317383 514317487
    0x60605120a0513021804051e060a2a0e010809120d05040c1d01240c0f051c05030a0b0d021e010e0d03020105070e03010b060d0207021c0f0b060402 64
    0x210b00c000c5d80c0b00c0d6840c080b0008540c061400388088490340d10740200999040d52002d0214001904a00003040402c2c0081c0c202c845280c100f2500000031900e03680d40c5600b14454040c5a00008000c6580302e41c5c02e5811003415604020b40c64040c00541990010820781885010304030328826a80b5000a018032509c100794070003038421107503103025140c020427148418000078011119a0680003100071a45058140d06103542119501d405e211007030340f5118115080304024080c0d07443e0141e0f0003607003500c1b2140300345890405451780b140d035120300f8459000800c0702c8c140300045000d00c1002e0f03004000342e552030301440745840050681d1100000e00c4001280c14100c0300d000c03141c006520201c80c20800d901074010310700c00c2c0c4c440da4400040640341402c250980d05010348080c0c2120b82004120341c0d90201d80c00070401540041c1201403c51542ca00c0066224105a01541d43c880202017500400003040042078000074102d90560500c42401c1c45601d80781c100251158041c00000001e07070744485256410654 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 514319883 1250 514318633 514318639
    0x172d06130612110a1a04060e03011a060702030106090c02011e020f030118060f12051603020a0612141003120c0209060d050c040906020a2a080309070305100c03060605120a051302 78
    0x5c080b4901e41c141c0c140f604140905000704158000d241000e00303051096607040c1420000c003014001e9450b003404156404184d0998043d500c440f07000c10f050001d40162203070726170360390b00005240c8141b0384000300c80c0b0040100c006045004003c5c01c3c198801307440589040d070b07400f14400c07820742c8040700d02c0100601d581c1e80444400040f0b0b0344001409041d4981c040784560140003540c100c40d0040d01110a0f55880e4000258440428442070140c240303d08164034200390070010000c0c1e030450305030380018029803c841c5ca20314003d00090030b20401c01d81c82180300c00703c15103041c03010248040c1d500050b1105c2005080074015444003a04009000301000000c010440c0504204410222414800c010f588000304844c007242c480d40c8034820801d0303110f0b0340b500d45c2c1060900076000b0465655405c2c1d156400500b881015111700c02c00440460701c148561f4003500082d400000e0030000b403080190544051764044000d201042c41a218420080b517200b5900000c01503000505555420703842807851124500070350 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 514321133 1250 514319883 514319909
    0xd090f0902220807032a06030e1501030b09150c09060d0b061206030c06070201020307020904020f101701050109030519030203130905040b060907172d06130612110a 72
    0x15030000b01060a0056038021001c1c201003009100722a41c842a1003146c06c02c80150407002002407911a51101401141600643d010301d12110781c0c0c880103030380a80040d54190050400e01021190401062460340200c00d4840c155180c029940b0915014003070a030707402600300040c0c0741c101c0c4c08903520440032001d000b40926100c0358180200d04401404881140c000d1040040d048074500e0036109035008140d059004624003c0c1c00d0303080c01882c0ca40544101c2c2c2000c0c2401300747d80e140d903802087c1e006a1009a4440b01c0309000d0440141d41100107034885814090391500a2001c01c0c00440c1c0702c071600f08010b09002d941051490120b1461050803880b5140d807949010200380300806400c024041c6020f6240600181c13600301c10400c03110016100f40b404280421440300e80142e4448800c3c0d07101c5e8642110240d103146102024210007400d04c18448500c2c0802e0400500d890441d440500350181d0400130022107007003440d895040d15012801820350032081e0440901a2f40d1115000094160070746121 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 514322383 1250 514321133 514321139
    0x17070f0608090727020912010c05180d0309271811040204063002030a0203010303030e2a040b0a0e0907210b2508010501020d090f090222 60
    0x281010300a542c503201c58012010009031252404031071103920f01034600000114040920400025442052615045914100030220a24081c803648040e016075854582d900c225043c0c1c006403200c80030794614451082c0300c041d540469409011807007a6042900340d46160041c00210f05480d06104c04400c1205041c103140c4000c11a9010010402c24492034081c034a0800d01d80400085c4c2c081d5018030b8000480215411450095881c4103d80e8070b58000c0d00b6a46001e410000c807070613640115282c0a0450300040104201681442a00943d0b10b806000d4801c805032403890b041944e070181249180306c1400c00307846480b603941d80d11804040100070280213900da500c1215110060080768065514015a80000345090801000411003d800c806074200e2120300d564400c001c04015101c28100e1550345000c80c040d4204c210756440c900059198480a0340c03500000902d00b032014a0310104100e80342004000c0c2c280500d80540a6401402c00540c40d80c14500c90a0120b005a080c04844c20604413000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 514323633 1250 514322383 514322387
    0x1506060a031b120f0e0a1b0e0703060311030109050c011112030405010e0c0102030c0c150f070516051207150507080304150c09050105031f08030a0201020d2417070f06 73
    0x90703035200200c000600501e404481300d0070841d043c0030911040c50300308940180c00581141c96160320103a4180381001e450ba129500e04494240451700000804d80d949000c2c42484000b0214498080088000f400001a5a903c2c00c2c0c61b55030349072070107061000000a0716020700301482030f03030695514507929a03124541820030502074030410700c024025001c2d034100c010322540701108031822032400c40020000d894200051161130842c01ca0206512030061220b80380c8800c40c1001020714600600007001c03542110240d07100e2900d00d0743d001c113201d4106018011317403c001c0031602c00201c480a00038a80c8190b41d0f88425180d81c810144001d21500c0000200010050503160101c2c07403041d901400c00007221403a2040c0ca000c2018025103020510a1000402400e0006c40844004076900460946155503600840c51034100a0390800581d4011130020010b02c068411040e100d03800c8015803103045846200c0107001182c038000c0300800603039028145241e40d001c001e860b00420f000d001d14000365541e1180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 514324883 1250 514323633 514323647
    0x1020c0f060a051003022805040e0309030607031503080714030307090306060e040305071e05031309050a061401120b0907030504050f28020315010905010e01081506060a031b 76
    0x40b042d0040d10700030200d00c4000e202d41c505400c0d2913003d0909818251602d4076803101d000c10350300a0b0102110064041415103403409200c040d040e00134000e5440d00702c10300800d810300c01e0042a4070101498202d43c0e0486100d07100c00320040340e4110042590b07801c03540c10448484640300c1100f02c0c86100c008144030070142d210303c0400469000d098200006912030403007082d800f0003130783d0240001c1d0f42400710340301244544843d650160550070805404003099078034035085402c4440c41e5002002401c104101088050040340d43c03091340c03588104046820080c1030b90f42800c3e420001810404007024000812045520807120000c00801ca03a059107030440b4003c0280a00700c1742111305000b800c00100541100240c5112141200060501410f81382503000e13950058810302640d0512542d00c0440c485481c043d038942c041c0050000214442d8148000c1010304107040c0d00508440e407121603013441d038000c81403105030400000c443c0e140d0344031444502200034118840c00000c0c01400d042c007900c10740e500a48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 514326133 1250 514324883 514324891
    0x10c0c030c2303060f150907050d06050d021e0d080304060501031707230c090f0912190807200114070e0307031e05060f040303380301020c0f06 63
    0x403401c80803070142040c0b044008040c107801034060780035030045954601c61040e099800031006540d01620020f280c00513511010a030b40c5100850ba00040d1642201d8460184a014145c1942d10050f0003075180d0200d80d40b170f585d01d000510992440880c0803003d0752402c50a21060383c101448175100c2c1014181750000300000e110841c2c0c42d03543c0141d1015001e0008085e20240340d00b00e01400d0400c40700e081c405003610000b1000b44403d00070310360b03034011035510000c00c3c5c1c0c010003d0310061803280c0784c801ea144e03240441e000b2003005284000e00c00706080212407440002c002c842440c0c00c0c00242c440170020340e00d000035200c0072206254040c0700c8030f4003000f0541c07007800481803e1264000c55182c1c0c0f0b00c00e80e09203402000507601500981070910114004c840035400703454668280c6042c011080e125642000826680c20b5040132400050206040c0c0c1402558075104200d2980104110900c1c80340516400c120003503076068600214002071035400303505a0707540c007182c9000e46840404000640340c8640b400c131 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 514327383 1250 514326133 514326149
    0x30605090a0b130c02070803070b090c03030301081209010e0a2405031e04150501081b0102030a080a0506040e0d02010c0909150303051c061805070e0109050f010c0c030c 74
    0x40010341070803040d0180707a2031101c001e059040101c5400d48000041c20007141418290300c0751000000310032070200002c00030140104078221144c01d04c60b80345030414802c01c4510b88030b5441800140002c100100341c2281001e02d103889960703141081001614504250904164080c80444000600d801c6500801c000c030b00a848a05403280002030040d80c0501007030703590400a041c05558000482400009990460302801d90006000c0d07481031038505803802604003000b15008405220361503d8031340008148078009002460401661b50ba004020170001000d41400e6511075000c15400d4541e0307409000c540c030a00c01501d00c900e51524000e8042c00a00701c005001529003140092034032124402c00713903d03003400d43c0c54148841c55500d048a4540001075140a00342c1c24809030403100c3c0c6503100348402042a0303008180004001d101d080c00300c40000740500b050082003c04812280c0e444068581920001c03a1060489025007004030380306a1030046c0140b5035a01010f0110600c02c14400d0803048403106 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 514328633 1250 514327383 514327399
    0x1d0a110f0c150708180610050f0409060221180604020f010c0203010501030501060f061e0c1703092802090403050a09090212060406320f101d030f15090c0d03030605 72
    0x444106c3d9100d4003195810040000e804051010346400306460741c046000420124000386e04e074461800702d030310000c0c1c0020a07415841100301400001e50006511100d0f050340c880c0301362441c2ca5100d031a92030041c0000d100d0071a00d500b000460380640c2804211a40280003003081e50384038a41702d030003041036020798042c40e50640313000511b9901c038025041d0015160030b060090091140340c02d40e5540b000c03080444880030201c004034407142c0a07501030b510800710360004021380400b40189060241005401b030b00720001c0900c100340907864520900d50096072624002d6980c00220314200d50054154210481641c000101201c003100200701c1d00b4050002203404211640d51900100700c0e06480301c1096007810f000b0345445501544c107101c01074080c5c201519610070f1403400400541150720708181d1601040c500d416240d103c1000c0058041100400e40c0101400030302035030080d599180210508160140b094001851902d0a100244004d04050120920300d030b41c3d490044c0c040d1209000f0300d070040103a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 514329883 1250 514328633 514328671
    0x6111903060f0512070306020f160c05040f05010806060d02031608010510121703071b0302030304150b0a05120a0b10030b3102040603020a1d0a110f0c150708 69
    0x70407070150254504d03000902549145680380c0f00690400c0300c014105810501051201c02c0141106003402031140e14100c0d041820502080b0403652284200c5082e180340000500c20307010000b912907048001140c030388441d050f42e4800285040e1000c0c414104c0980400000a0510030541085024101c002600b1000390b407582070310460070740d80c241f000e40400c1c0071040d80d81d86202110020341e0040c00030315120058015065a0803035400c1c11740001c0b00164400030410040c465081165211a51941410303ca207071a10000031340c03410828080c1a200c0c1000c25030140c2e80500400c11100b542e07500800002961030a1009940204690303c03003501d5003034403100055001941c0c041005c0841e040409541c000680c610f00e0903203001c1e140001281c10681e11030003c070150b40c44a80c0d0000a03c010448407000b041010102c0c140c0c141d02074a081200b50412688103c0211401c084d10405400800a5074a403016003250324540140c0c49502d0700801004414041c2840e4007141d024454601011180500d0760 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 514331133 1250 514329883 514329889
    0x106080c0d05070e0c070c0b0307030b03070506031506040f061e050c1507171005011205040807020f0a0308030f15010f080402040507020f070b09092206111903060f05 73
    0xd040e01e801070031904a20400d01ca9078080d4110300743c10026198a29040c41785a580f02044522941c04c035003070a01000c010480701581c14040c1002144099018101c0540380a000c00d00038003026014403006400e0340c54043c40c0c1c0c3c0b142000e64000f84001d492508481355244006000c41c2406c00c5240000105401072200040c003501c216000781c240f100c01040501c04041c68020081c102811000070460701c10844000000341581c02030007210350200d050201c0785030030000f4102251440c902d010481c04c00b41008045401c42c01516032030b0303405840108807441c2140025014403a641c00041c1010000300c2406041d0a101c18114440d030492010181245601c90041d030717880c0007403400100020842c038001001402d00e50401c03a0092070b00d0040b6800c0085044000e414018a5004036803034041c08100610146004080700f43c010070281b54000c1c00f50b02c1003200d40b0900240035405841561900c0081040442c5207040750700c0703550401a0f04229543d00780004001d85194414105240a00302000c50340d45 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 514332383 1250 514331133 514331149
    0x60c0315080307060c0c0501050708010e18060118060e0a0501050405150d1202010608011d100b012309090109050f0105010807020307030c05070518010807060201091a190204080106080c 81
    0x110810700441c1456002e6903000302901802d80c0c610704001010000400003103007400ba560150150740c80745c8403258100008001c108400030300c02c06162b00e040b001000040804074005064031511b80000d040d906080c00300001500095100c2003510550408100c1700c0321941c1e000c2c034180d0718110383c20b1002d500e803200c8114003016280102d503403188101c0329a00000d1078110111500500900001c202d00f5035441400c5e0860715801980714440080d0945500062000d101d1b003d00d00380400300c20454500341e040028514064141c2d012868444e40000c00044c000040503205111001012089650703107904031200a4841580c030a010f172044d4100100340d40d03000701f003010700c1800a58020b6040040030345040303034540e1000c58182c1d1280030340b240200300d90300c64000380702d070002d030802c210041545008485850282c00b54040300c1103914009001000585210030304400d0f07080100c4001b00c5031150312602e4200d2040c1141004020320000740001d40e800103400440880790366000b40d542000340403045c05680 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 514333633 1250 514332383 514332389
    0x51617060a170607081612200c0c04051305190c0816051801060503071b051203040c061106280515040c09050612071202072010021225060c0315 63
    0xc640d00c7c0003d40d20456241d8446203800c404501046080154800072115030781c002d101030200354102e940c2410082c24a4003d054002e40900f1303e048220358192160f64031114400f581207500f07081d03c1014414400c4050701c0402034003d10003955244003100720750014261591240c140100b503448400b5640d900312021103812640035488003031442e61141c0003222200d400202400c0444003038806800400c40400600340084400c03143c00b5135a041c6810001c655001c0ca074042404c01c44080e456904041c40424ec45030400c60842102200c0410302d0100d4681001c010015801145890208001d80c0c1015804007000c010682c2c1c100040b510a10080759107118138064203400c100204030001c0e1068007110400d5002400d0b18102c507003004c000c140c2c042a640584810b132050780e0b0300006824005200c100d490524002101c1003025010b03408000f17522420b81d0811104420004234401c40c50344441c9074001180b441d00d0402a80c15030061800c5c000500c1d03004501d600103031900008840d00144c0d000a507081d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 514334883 1250 514333633 514333637
    0x10b07030f180f120303110412020105030604140f04170f191103040f080d03090f020405090c18180c0109031401020f030406050703051617060a1706070816 68
    0xc007505980301981c69049007040da05950110342e000061020329480d840d030251091101c0c41c4c40c0300d8880d040007004c2c0c0e02e51300222a089181040200000d045d0040000392482e030a09040e0b840750f981000043c01450300800e04014140c40c5402c0110b0340c00c495600c18801e0f44030310000180c801f004c414242090007000d80140c44940100403c1c00e00502c6503808031142d03041840c001e030301d03e0000000b190030340d0880e40c010121017002c000d050000d00414407034542820914541001745400c56200c101080780146000390085a8840218085000900840070780300c1e805006407821504a4044241240c02140d8107620052a8918404d100e880480e442a010328141e403800c400506513218039035000f0403d48000480e6608014041140140f080610710a42c080d140010f04c40c40e000300b010b019102e0040044485649190203c0c07209038001c0c12540d004000303100e01c50003c0e0f54480129800b044950050741b81240403544071710a01200141c0c061180c446540c85140548407a50f000003c40b034070603d8400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 514336133 1250 514334883 514334897
    0xf060303051b06011a0d1d0d090e041e05070512031b0109080a1202160807060509060c0f0a0201020909040f020a140a090b010302070f0b090d08100e060d0507060801030308010b0703 79
    0x5d0500300c1c1e41c0141413808503404000541500f1404044000c008241800390142c200000d8036110303079004000000144a4080c2d001e03001d00e46130796903a8030041c1c0800042201c00104100b0824040100000000b4000103481c50714100000c0302d042d0f40d03d4001c103201c0c1541c4a601d00b0500201e6106014592005a10425041c03d2040c0c2c00f0003510011103c00d41c00c2903e69003807064440d8032694040c0d28005a02480e1040d80e1401541442019202c00918030001503104105005a800501007200c0740b6140c000c2c0c1140e111010040308901a2056011071580040b2010620051001e03d96028400a00c212001c40d03041d030352450040c54001c03100e01c2e5290301403038220040050051a40141640c3c000500d00140341c43c1c0d80d9038a0108151410a058030310b03a43c120200050a101000b261400c00320509060303032107180402858400c501c050299218003800c65010503100c1d11038190f0702d020783c0e50040c25101e00c5c90311240002c00703d031024070080c0c0004810000000c0c0700046402107505164050365540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 514337383 1250 514336133 514336169
    0x21e0f0a0b071106151003050702070b09060405060f03090106050a03030806040b1809150108071a09010e0901030f0201020c040b03061b0c1e070602030a051204060f060303051b0601 79
    0x84000c00d00404032800c3c810004a11901c03500c0c18070840780b10b060000c048070001c01044040c003d24012880c4240300b410703d02003c0c000310030780000384842201c0a5003149070340e945803100890464007440d808223401c40d4001c5150721658210801071845000e5800003005130640d282d04200c0707083c00300e00c0060049080c11000c900d5504140d08a4000c1ca00044c1200031881a0321111002c500c034111507001640e0800080710591003026071001e1f0042a00c0001005450304100745402c840d44501d8004161001c0010315501a0340110301078100a1002012900360b5030b0340341403e08000c0c0c1812012401801100403103004d516103407090440c54000900109820f42d50b2030000f0444841c44195403d003410309208810542004006070210182c510205403591211344000b9850120070750001c42c290b410a0200d078102c0c65018003592142c0c0360503210315a07261900d04249009100300018030b800b840c1405004418550000001e0101340210a90340249042c9425410349403c0c0070700403050b00030120005a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 514338633 1250 514337383 514337393
    0x140a053016140108070c0f06060509070c03030c1107261e070510080f06011e030f0501050a0302011715040903081f0312050c100f050601020f06011a071109010303021e0f0a 75
    0x51f8056102d5040065140e460702c0000e08048001c645070302c00584800d09003010540d05010b280104605400d00d8010f00d400310b0351268540b03006001d2500100302500058000d051605154000c2204410568000c41100d451110b228079900307050401501c200034000640342048414165003200a40d2810040d44606001c080c1411001d41504c2c10420f0350701c1130175260000c800e4400b4400f02c59840000c0d0512032401824103542059202c00c0c4500300042c0108050b0741c03c03010744844485030b5140941b542c1e442800d8541c10094000c03207240c00502d400454030400da0440000c81c06100400700c40a9416151032014201c0000e03030200810119110b800303991140c0c001c074003030107600151100b9030341140000c0480000700d5460300c504100d45602e400501c81c0958045c00400001b001000290101e0343c1000d81625039481d511250641d00b00d400110380c41840310520740c00280000041c204d00c03065949040007581c691072071112070300058035024654000040090064158110040a440707a406140c440b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 514339883 1250 514338633 514338653
    0x120c0312070312050c03011805090a020108091608010203040b01090207031e0c06110d0501150e21061005030d0c0c0909030302090a0906140a053016140108070c 70
    0xb1000d0210511001d508042207001d4580300340e505850154a03585003030b1529095940080000071080d01c3c14060203051000030509102544d0207007070640329034036040e81052a00001d0340301e20707402075850040816030b03a0064000303500072401001103500300d9072604c0760300080380314400c802000303e4a104100107060516850301580d2241c9410049510725240c0c40e180d080d20855040692040c00c005550010001107101d00c602401c01c1c44802020510342d000064002e00754044403520690400307030200040c0104010000d00380306550b0544a0a080a5200030711114160203a544a80a10030250804038881c0c100f0018450300b00741e01117820740c075081100b001001850700650407d5000c01016110307031111036109005050700c00001401900e800c0c002c0484c0407502110134402c1e0f044e54410445641c5000b0000c6503085240d0300c168418145510245040240c4000348407540652003200c0c100c0b0460a02c260101c03605013260b9054035480c200110bd00030b03001c90b6060040307203c22003103001062003942 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 514341133 1250 514339883 514339897
    0xe010f0809030d0608030c060112031d0406090f0e061b070b0c250b130803060609030a0210020705010207080109050601060804032109031701062102070f050705120c0312 74
    0xc0c2c0340b40c1002041c50009039600c6030441c803c1c540c800a100e440494003005198014503403410310705510f0a40b0340c0c0040110700d0020526060f500c0381110b05096640b030b07503c082d006009000c010090004c80c03c10000180800c90030f100800d004000c0003803291050300742c0400c2100046c00416207480e44c680c1ea008001c100103000003003a64070034040e885a200c0321403402e2800d038210a41041d105141441d01582c07440c80101000c0d9021019414400007170001001e8030b800c84002c4580581b01e40c200d2000c01c1c501303401c1c000c0c0650b010100300c0345102200d401080300070580b00d00382d098803010340c1c0740c0144038240c5002090040c2180e01401c010070602e07108642d0680c00ca480f034034000c02c1c00160b4183c01810746440200403100e0030355960243c0100742c0c1007800c03054410201d0303030818400e61400501411034070800c005020b400e880d00030000c000d4101039040b0391010358001c43c1c21101400900305290307210074500681d40180000071514942c1e4100181c3c511103040d0003001448000c0a04040c11f00c0307908040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 514342383 1250 514341133 514341151
    0xa06020d18030807031e180308030c0d09060608071e1712040905070806010c0c031e150e01050c121314030a1d0114030a0b0d05120d0c0e010f08 63
    0x1c4804000907000100078410740b4001d0307a503401c1e5543d03800c1261096246840c03a11007480402229101d01440203400e003022607820a407010b48a940c0c12100748003902c40c0c2c01c5c408490506d0070716a1010000c0d203600540c261403280045a0b0501e46442c0e1302c21000d003074003420404411101c04100108491905800c002c031840d40e050702e180071203031709038004280c2050300503c25081c0c68004000b40c0580c000c5c1d0a5511034024038020721000c1894441d690300c840ca601016210301041c05008603513003100c10f08245817551000001501c40c00448014005003400e2071484819400c1c40046080041c1c1e40b8241c4a180b190b01114080c0c0351a5080980c1010440890440b41101948641420610180041e041007101030310b9903003c01001980c0c05061001e6950b189041c00344400d051103030302458406480d8014201540040c900b8440c13400100c50032065031f002000c6100d40c0da0301d5044002070314040c2c0510800080180718a008200082c2d86180c0035012141c0040c080440413869148030b200304a401041c55 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 514343633 1250 514342383 514342427
    0x60f030411060714160b0307121107080418050105031203130c080c091609140402190f08010b090906042f040602160f030212120a03090605060a06020d 66
    0x35004103040b60064003090ba0030804013801580ca1074020301119603004000c01c1c0703020901e4103082042c103050201400560410100303800d00640103003d030344842c010b00011f0a00c036440b16103900c1e10b203002c0d60103405084000ca001d0104060400c0c01c40c083d540c181c940040c0540071000604087c8060740d04001c04a110300b00c2c41405000100e94100314440c0074100d4403014120302084a0144451a42e014000700d440503040b07110340854991201404083e101c0018034001070065100016001e40038040c50000021901c0c244910501e402c08074040e0032440548818105030303610041103c80d406000c004642000f0b05500044603403a182e40070800802c00c040c8034800e07003880070191031400c05160f05c91028110000030207110164041103a00c070480050185140881e040451704042c52002d0700c0002c3c042c005048100b41000d00c24048019020020200261140040303440180504030022041da00d4526201c041000d509109841c40c0c151001600184800726682e541103811010b441c210110000107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 514344883 1250 514343633 514343663
    0x3191407032d020a180c080601050a0e030304090e1507050a0f03021b060c1b0a0f0b070c060c080a0c03150b0d0b0d08030601031d0d0815040c1808010b060f0304 70
    0x28400401301a12250120014456580c480c030821144100300d018244690841044040c1ea03124040b0b0366011400e2920000c0441c62201280c50b5020742d4201a80f0f481c1040511552600006100c8006002e030203042c81c0700ea155537a050380e40d403040284e03000c0080c501c9078011a140c0d00136002400d040d0402d01908030340c17500d2894613504001c0d0036551003000300c41c00030700c04680000420a411500c0c1d07021000d8050f00d401a90b951600000d003000082419880f2000036803890b0260000d03a003d90f0700110107000001107050020a546000c0ba18100542e1402048000091007886480400c00c1c912042202a50405c00854801d4008041ca5000141ca07003500c146d90303441e58180701c0c16151140305031316140c2c00c09200250a44648400340003080e500780131202c0016800280d40000000e090600300c0d001e44604110307000c5060307840045c60704281412000002d4551118081024403000e2420381b085a4030340008030300ba0340f4016540f07588141c0901c40301c00d44103080c00055400c144250b41300005115 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 514346133 1250 514344883 514344889
    0x80d02030c090d2105090d0b0601020f030d050403021009030f0e030f0a060207020f0d0201050f07050106050a0305031b2a040209090709031406010e0c090f03191407032d02 75
    0x2030f000d900700c1c0c466040c4801300a40505103030b1352941500c9641082401d004081c00840c48181c607020300689803500c008042581079000380f00340144a03101600743c0c1c1d900c01990421001414013900c0c1180180300d0804550654006071048036905581a40c0c2d284c1300d4143c0710303c201c41c07816203403000a5044c0a170122000e0a40d008000c155000ea00c281c40150f220003071070042000f0440380001141c01980352800100060f0381c01400c035454604d032650f0481e1030b0041401d0403401820b1b25000b0540240840d40c0100c24484000040d00d2103064002c01e9444554030100c000e07481da88040c943c110952030481ca1b02c115002100c103c0c205528000d04010300344a58100041d9211005840e445c02241c0300c94014010304c000d02d8110044880000000d00c01940b41541850b40c3c160014040d242824001c40e500040d507480c02c2c401c40c1c1e10319008045940d900110080c02c2c0c2e5010410000f00d4940c2c103603805c1c1c803941d8000071031100103c9400040c035100368032825000701d0380350210000c0c420a542c0e044c545400165 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 514347383 1250 514346133 514346149
    0x26010501061701090603050a0b070c080a0801090c09061b031116230102060c0f0705011b030c02120703030c02071e09050f0f011503021b0c180103080d02030c09 70
    0xc50341c0d0ba0303075054002c1d21101c003611a07001030704003040c0c80381404014008140009903000016502c110012820360f0382071802c0b200300c4403e103002001c5070800200040c551350720449060581d40d200100300441702c00b010069599004c50701c0380c6000b04141a00301010703401401c0004012500a041c10390020b0030303007048242001d09501c40d207030350198140d00c1807040040c904159030400e40c442d0745001c04032000500103035545100410300340e029040081c0c00c107442018003082d21251a40140203100c050650030824400404031a00d88000030b20380708011a04510014041000c0d925251345203103807800700d03141140940346956140d01948100003002072104c511000302414000d510090209807800c00101c441540c0c0044e140b4140e401c4603000f4400d80b405a520058110780406010544000407020158083c2c0a00c510030130f0507000341100b0030240b680c045010f00504004481c1c074800b0541d02e940c025003400082c0405090690300340100c0c880305140d41d0045400c210940601d070304102000000034100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 514348633 1250 514347383 514347389
    0x80a151403031b15060108070215040c090e0c121b121c08061306150f090b040308090a05010215040b13080c0307200310021606090803190207080426010501 68
    0x280d10040c0c4031801c01a01d0a51543c005c0c00134a400959410618402541e600d40c81d01441d818506c150041410045281d02800040c1141442480f803281a50714558488030039102880c010030200364280c08109021805442413141c031704000302c00507103480500c1240340d099003820f1268403401421080003800401d1519207503a1990701c8000c249040c005100740e81070210200508141814000e21030b10b401401c0a2410b40e1031880c0500c0c490361001d604492003400ca90222855420026011045c000300d10010188001d041d602c131280c1d00e96032001280d403188040d00c80d400b4082201c0c0402d002440340e040702034100b48501c1c80740c144512075071581c288690003280c000703d10794400141d08080103a44801c0200c80714030080b500c070844e4108400300c0d44900400051031906a40081c001d60000d80f00103c446401c0d40111041080e0070300c500e4444207692040c1d4003c001c00640c0b550740071038105640200d86856034081c80031070a0503d803024003944840906c1140e131180d00c0f10380300c001c000702007445900c0c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 514349883 1250 514348633 514348687
    0x50709090e151509160212161b0e01090c0e09010f0320030d08040201080a050405060a090312020301090902010206130309050d11090a06150e031209031c0e01080a15140303 75
    0x3003100c030a84084d1802947d0307004000548018001008503014140b610488280c1200070203c40301132011500d0b00c1181180c20135a401003071403001083c0c4043c1903001d008180081e4403910a0302e0030b07543c1081f201d12003d00c00c0e1101c951058005100007002e41c4401114840d1803011000e10f2040d500c00281844040c031006400107007000104803e56a005030500d03000709032103500704942d04107a100c558482d071008210742d00305038030b807900c8400b054441c5178117001e800741d503190454481d6121801e0304041c014410040c1c2c014801c034404074905141c1310740584540303940754990640091078041804070327507801d244043c0d0b00d003411180381080030785074002068440c041c0c140e130000e10142004c03500d040740c1405040c0c513020004074100c4074003d070310b0006c1e2071081c500c80c48c20b6060719016000c001a00d400d903818582c2d5804a070780800314488680140c440000d00c03900740c82c0c02881c0d80d00c0103000300c11914680c00005541200c01c001300140d0301032912001c4100f038007509a07860841040c0152090010118600b00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 514351133 1250 514349883 514349911
    0x60602011e0203040507140f030a050a05010c05040609030f020604051809010e0d020c1e100903051506010c060917040324020306061e09040f050709090e151509 70
    0x44855419541c0098501c030340034045085081a4a440350b840006009440020140c040c54148070390f1019444242c0c900010100c98107444140340503901c41100400449030f43d0700f0154000803180c094002c0d18169a45a0345600181e85992241c0e07020988515060340c0140c010080814a2748401c6841008081e5a00f1601801c0c10000d1085085803003008085010b6009184902c803002e6000c688034009110440d034200c0b54540c0040762001c6203580c01102d65000080141400c0444d0b00303c40058100c03030142c01900c180c1a020311401c80403080c2100c0c910700040c6a00442000a6100d912080405001d140c0501035008040003c82c00b65025810aa0746420380750400500603041c42442ca40d50040c6000560850070000085800d0340248a240c00d10903e8a041c0600d21007a1482070702c00c481c80003001480114520481140101810348401001622801c0040360302c240d507004110b44031840000074106914440001030000380050608683d6103c0300d8845243c1c2d584400303185003d40b6030790383d4240c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 514352383 1250 514351133 514351151
    0xf04050a0f08120c0a2a02040b040b0a080607170403080f0702072c091207081804020d020306010305060102070b1c090c03060c0f09030f0b04110d03020606030d030204030c0b090a0906060201 83
    0x3c0c048403520008011083c20a06e213050a11048030411000554113580104d103614051001074084c0c81102c1080e500460f11013000900d9483c0042c6141c040c540300d8486035801160074002d80c000b080100c801601107096100030030024005045007913485030345441680c10071501c42500300c8a4030781e400c0700903e110340c91102414a401e800c48016400c10b842100a10408565001c100c945000300440501040008034180200401c6080601180742004008550382e02c40c5151800c02900259815400246044001031081d400001e600b002d4504402d8410704045081103010300d942000340e0450f8009858501e0100000c0300c088d10342014510440003c1851900040001e000802c005600001c2202c0170030100302140700150201b512a030802083c030519035071402c01c031104c20713820032440390131000c034841d00000e069003c549180140300c00c4081c0c0e00154440c4108500381d020b2408094000c00310300700e041000100c000000c0c07501181c05040142c0082c1d40b008940104c0d006030b802100581d44508182c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 514353633 1250 514352383 514352387
    0x702040606050310090e0c0d050f06040f06050c0c0a0602090d0c0b0d0c09060504060302070c0b220603020c06010e150a03080307080709030f0609020105040f080c03060f04050a0f08120c0a 82
    0x50018241700704005c0520600a6544400740a18640200c4c0307000d80e94406e02c90184000f10b5480182c000719507c50600c3d00d440000d40076110001c0d606c0c14609000300e0f00300079443c0212019944072000402c04504282c40b800c0003540151011540b0000e80442c0f03c001540c038006000080022040c030300d443d088005001410788441c580300e00d04000d0100c000348401038001003a0f405560240c640113032212214940500c2200007a0000c96400c400070901c0d030028401d8002d090f903040d40d0401e940940c0c5980710000d4050b4060061280300c203400c0b810040c40001141c3c00e000d940085502e080c42006076041022881c1030000f038005a0f440c08000003001007036500301c60b619400882d42e01c0c1075004a859500e071030144009040d0f008051581715805403041d684210f083d00c0140a441c40902e0303944d607036000075603540c01c007065034280030b801050005001450911000c910841d0400060140c0345510350300d02003214060101164514820f01980c00d43c54032098004c1d115130f0786035912a517117030b0f106080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 514354883 1250 514353633 514353661
    0x60319060212060f01050d05090106090504140706030203060109030f110d29061e0d05010213140909030910030e0330070f0509030106051804021f0503130807020406060503 75
    0x383d9000d0741c40d00111031004c1c1d078400704607400480128000255a215100014054102e0b940300c0704041c3e0414003803005001c02031032024840100c9070210b41040307075110425800da00044076000c1c041208004100302160031500c1034019070f8400c3d442c0030f031b002c81007100203215000d42c40001d07603025540d0500c100c0290503071020041c0d1908051004406403508800081c80c0d102d000030203d074000d074441803140054032102001c4900e5607121009648810601491408600307003441580200014020500300e42d007865640c00f8010058080594602400313070051050103180d580202e01056a00c401c65045001d0600c050002d018402c00c002450000f51941880c00000c80d903805846410000140680503400281d21490035101c0d0601c19250044c440000b0300500d5240d0050760000010761041c40c003501d01d1036115200d140300701c4039554111700c0c001d504d4083e04c160341c00038004101e08101060340f6460101200030020320450480d0300c2c0c40c000d9408902075586a40c01080401d0340403060210301002c1c800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 514356133 1250 514354883 514354891
    0x2150a031b0c0f02010c03110a0b0709050607110609010909021204020f03010e0a02040e03070f050304050301200412021309050c15090a05120f0706111b0108060405060319060212 78
    0x3822142d0300c011a00c540310304840c1030b400281400b4101c0140802c141c01a4010998040840300f6038001d03031014103248c4140b0900b00c071940001128a14045001d10740b03207050b181c203d90001840e8501021010503c810795100040c2203041c80000400040c10100c40d000800368203110b080f00c1040d9003018414030100c18480400b092003a4104802c0c3c80c001d00300090540e80c020b40449000c59244800c8040c00c0c01c0d481901c8020f0700d840000f0a40b0030511038000010702c1201c105400800590511684491801a41408140003404200000c1203c0d50400e07914815043c0020070a80488034103540c0f09007280d074001402c031410380000f20724a40c20b02e00404a00c017140c103013021907881c2c00c02a000041c1c504400303015451190894000305d4009100030070240300d0184400003220001515808007614019000720341201910815044000d010011031504074a8481070b11500101d451701400c00010f0040140b074150144a0240b205202a44c482c1400301454000c1c1001a0307600200c0c0c2e145005404014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 514357383 1250 514356133 514356137
    0x150902040e1623043507030c03060e030d0905010e1209060d020f1b160801020a09060305042d0b0901020702060f070501240602100b0303090d02150a031b 67
    0x282c240d03035000d50480115000006a00b06141e040e000c400c01000240c0125044030481541000b200b2000611400282e075201c440c400101e0903180490410342e941e94550300001302000000001040000c1d680c1d04a21042d681a1080d203042c0704800030588102e4030010410380e5503a445107207069036900e06000016401d00116080e41c6401299008a002031081203108503140d9800540c16a004003403100340c0d03580400c0c4031502001d002003241002d82c3c03042040c00c01c2144c80c1c19604005200c010501c2158403615030354a0f0312211501c1d2503002c0c0c0040400600641d07030042d00c1400064201e800800701d0b503176006903030844101c80c500340c1411a4002001409040301c0d07071041110b9805a41ca032030a842d18040c0c00c00c2003d68408541c6491070241480d200300c0c07001c0c8604100700030390f0704c0e80c1a17001c0026900c45a08480411510000800075185106901038054008108040c0f440c00d11000c07075580e40340050260b6400d50000301001401d81e220b802100e0020307a4901d12201c3e00d55600c50020042c0d0032034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 514358633 1250 514357383 514357411
    0xc03071806020712030c0b0f09060a05060d061e1b140702090423070e0610020105151c080d09020f0a08250b030906040201030501080d0804080a03150902040e 69
    0x400300203503aa202034058000040510b0760700c1c0c41091b20603580c00070059481032100c203503400c01c038a030f401c1d0304242903440c41e10900400001400c02c500b1842250720819000b40110103585540d161503004140c40404019500c1008518148840711801900d0520304170030350b0b4a40000d40c07100000c181201341da40c00c0041c00410031042c00581d6802c052582c2040c2c0201ca000721200b0a143c00180000c00070798402d4050191180000d183c8100c5180c1d030340325a50580749900c1130302060070228200e40003103804a4031218640c1e0503e00e2414001d1005410704003001c8404241c100b02d48035014030750400f000009446845016400440c18107410303411030f0403000c6e40e40400e82400c0010340c98441c4100046030940209035440354140c820801400d80060200c00c0c502c80d56401c3c2844601c0d164813007220300b0390210703003040000141000c000a464000c5140c0da80e0301d2099865558403940a82e000c0600d03078080680302d8458031180010b88807018020140020010394607468407550540d59540248001003400403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 514359883 1250 514358633 514358639
    0x30806010e21010b1c0203010b0d0b0a0c0212071b0e070f0c03020313080604020f060f090411120f0403030f05060120120a030f060f1d090708060c030718 67
    0x1d00440310040c612070090780000c07400c0002e80600501c41058400e40c07101c440000c07042c883c0d88010b441c110b028000c0d0001d1200000c41c500b40040791072a914002d1496182000194001886910020000c0780c07038419901101250151000b1603081b080090b0b50f00e15620088260807407085048400800060106805a2804038000342070105600c1000090140a54500003003510a10440e030440c004409413000030764071000405e44d2a02c003124201e014240155035891149840f10a40300c0d500c040c2c181030740c03070281020144005050b0303034110b2054042d400d1004242d1102050f6462f03100c1c6400e0211041e42d4540303810002d0076501c0000c55408914075050038885140d903c20b40c0c40303401d20584446031240d2085100d0751440c040c2e1281e20302c103013000c001c540586c03034590540169500840006041c81010707150181c0d50512100391046a841c400c2950850000c60014041141e10000d110306a880c01590f0f0071545003041011560340c0034040b400020421441d40180e4111303031454007080780c000d030903003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 514361133 1250 514359883 514359889
    0x1803090605030a150f0e01150c020910030602030f062706040f0e01050a020a0210020405010905010f120e030307200307020114160f0b010602060f191107060605121203240d0b0103030806010e 83
    0x2105140181c02f41c414000041c40c40801c0c10108c100860340710004650f2031030302030100e0000000a0314031724030440354107030007a8044421450303403420f000340c05281c54440c4c2c80301010000101540c3c0d00340c1418581382d81404409000a1140520a8907100d102503600c040780800241407200044c1e0305444070f44103220500540c1d9109100340250303582804c010240d449070140a940b01030216040308840d90074035001c00340c8145d021001d5401505103485100c4150b005800d00164102c0790038409030303aa8801c0c400030015601c29083c82014440d40c0306802c6c03030b00301c7c480c14451076429103c000b81d441410201084081104448915004085500c050049030401412440e241c010103024110142c404c0c12441c0d4052541ea40700b04500c08000310265507404103445c29038060051482803d209680614004880309404600c0c55181c0340029407039032031540c0700140d0341001d05180c070f40d44078000c1151300110050345898010399000c0e80034080c040c41c5507143d0b00d001490150001c003954100070350060705240c40c2d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 514362383 1250 514361133 514361147
    0x501170c090103180f03122007020f0d030315170c010e010306091d07090b031c0c0b011202040509010c020c21070303050d1803090605030a150f0e0115 66
    0x100300c0300c680c1a41c80c405940102c020b49003401c00780921840f0801a80c0070426440d6111100301c0c440d49074902001c2d44244504220b503000d01b00440701d0704c459944803174800d00080091036407600c010010401030f031030040031400c04001c221044012075918601c4502d4200384034803040090120003c4100303018040c1d004c454907000700343d84041c14410401040d61941e030198000c000070f040a12003c21207541c100c07402c50120f04001c46106500d000f60800425816000d00500c01c3c02c41c0c0281c01483c241044001e50103000411460079010803034442000c4001512103c085402840c46000c0010480d4103801000105e44014040c1621a80352a03070361410543c0200300340c041d500c0212500c820000f1441e003181e4400040d040201c84030f005100f000700400d504080a0700340000070080400050814001c7d505030045101c03806004196084810001c03240b0800003940d00c03032840b03100400d10002201c6440242c82454000c1440c4294144043c460340208101060040c0880c00105030283d00f1000090120 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514363633 1250 514362383 514362391
    0x71d010e060d0f0203151203180607030207081006140a290f040620060f010b070302100906020a0224060f1f05070201110c01020d05181503070207050117 67
    0x203898007142c41085488150300c4206400d000c0f00056540f803400320359002e4070114000103180700d060700341070800c080d91000003510400c0360395412112903904402c04000040e04090703022402c520a800c00414590018052020340d800c400c86c02042d15801d00c407070b0000880442d54110300507050260100080710700c0c104d600381c80c0420380501003507101681500c1c9000d4400c843d401216000000b0700025142e90200507200d074600040700c518000d03140e00c0d6034a40c07920400d44504160035421001481460101d2000b400e005100340100c1d5204030140c1d40c1101500c1d4175043c19590641e0202d1510180740d01802410710240c24540d001e14581d004c10504000294007412075406100108505102500c84074130300190303c11958600064039284200041250380426000c0f07001490f00d4403424100305000178a1030003140305802502000d01200411101d40d0440c0705156132000c82130101e118242c4600b04000b00d8500d02e040c02c00c0d581e140c0a040a0f161060300c2d44030340d040104850012154031703100352010b600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 514364883 1250 514363633 514363639
    0x40905061821030a0501150807080606070501090f0b010b1e07050a050328050403020108040b04021f0206180f0a0308072001020c011a0d0f050f0f06071d010e 69
    0x409401c40d040074901500d4460581041c08072410481e03041c48000c01a5100304038501c020701940c1e072a521103075000d00440410350041a00200403600250003000c0b40c0390710003c050301c514149540c3d80c603654291100c1d45021f592546001c00e0340310610080102c41400340c042028954540102c8007800c1c4101110740343c05aa1200000c158002001b6003800402d0641e504001101e4a95031010003030585508940c1d14034003043c40e500b90032414140188250f0301200c0d0142c450b01c3c10341e41e0700e03181c01c0d4108600801c00c9038880b107240c410481c1110064843e088000056000341058940441c40c030b12002c800c0302c1440c80075413000d01d82011410001680122899141ca4a80400d88980c101038075a20070040c0300d00c0020264024a00000005501078016882c1000081c006c16503450880707400e071510f0484503a003100c0b241c0f11800108904071030500440f88100304880860b0030603200701d8105161101001626000705052100003035000c030b100c43c003c1122803030030703600401107030000703040e0f00040260140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 514366133 1250 514364883 514364911
    0x3051b0d060f0b032e05040f060315092003062d0a0218040b0a0b0a090e07080105031c0c0b06120a061b181a0c150106090504090506 58
    0x2030540d8a0700440000c103030340030362078450300e4640220300e02c2c9410480c0e04101284580c45d18441c90302201d840d9080208100064452440c1024180405804009113000d4440e0712104000009913540c03403400291003802900050081a0b443d00c86551000c0d910b001410410340c00040380d0310764020404a4100081040346405040403220032907002614604c0243c58103074480c100410024190010150340180c80c446150282410003000101c610041e0310640000001c403042c49841003a600070072110030a0300308000400d903075210290a210085a5a40c0001ca046004001c02d04040128581118074076100a110b5020b900004140390905403010706500400008585151108940780c0c18000030343c0244c8800c400a0306010001e000c60340c0303091500000c0402524103142c0f04407441c1944071801034001048520701140d0302e99140d5000c1c074440c1090b004000005255604005146034501a40444c1d00b083d803500300098242c01081e8001d80c059410641d03228001030022a007a035104000300e030154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 514367383 1250 514366133 514366147
    0x20c031b0a050706120c0516020f180103110f0a060e191203110f0304050a0306020702041d07050112180308041e03020f0c10090b091c03170703051b 65
    0x94907104129801038401d010749180420040da0140908800c0c03c1c10103401e000c0313460701c0d603801c03142c9110344603402c0c0b1400ca800b40208010b2504114001c0070100040000a821a909140c0b0368416402c0e4030445a9800c5040b2000150a01e044481c000c0c620448800f4810761800c0b002400e000c0b91103d985206101c500ea10903d424000c85c1c25502410710b0340744000401e5100e2070090300b2855a8040d40b07200c0e03c246d0302c1d10102c0280c0001103c065500250203550079a255689040281d000200120f07801501c42c1002e02c0c40c10281e0a070300d110040c800000f402143d10344400034060b18940e8a56022050903c20413040103145022040141a032510308182c0d20740d61403d060030842040d1030500c60758012980e511081c10342c006141014180b01905442d126400181081708007a608401d01000c90303400c10040211894a20190203403050140900c0c00c0e114000c1896a500141c103003044010906181004801900f819465648200182810452424201d00300d41c801440040243c509240010303c007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 514368633 1250 514367383 514367437
    0x80a05060613080607021005070f0c050304080129010516020f032503030e060c120a020705150316030501051c050102220503160b0a05180a080d03060504020c03 70
    0x100c0c85000c140480d0104151541e0041340c80390002d50303c1000601c5448281d00d8007466610556008400c20340300c26400000841d425a03451041d41801e8035103000900001503d10f600780101d01200d40c0c019000ca142c02d60217030808414441c10a1050304012043c40b01203166039400301281d01c550303011541c12140b200e0310400649004100c40e880000300c103032510000205504101c03c4010789110381c0381c020844030f06906005480c0680089004594003003c0d41009481c2e48c140103103141d41c4207205a0700440d884601190b1034120b100d4520180d504000104521002e07076514901000341540b5080c0095450a00003405c0000b071a80d032500b82e26504840601007010940c1141c100c0c0c0c400ca49850002c1070100301141d856102845114003901540300464009114004281d080c1c07040c0000c41410306015034822a0745800083d20340c1c8a2034020156480103a03900e0721040e004205104c000c29900e004a41c0080503030701300354001c0e80101d00500543e02c07000c4010066030b03d00d00720485c004150304131003032203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 514369883 1250 514368633 514368637
    0x203240d021801080c03030906070618140303154e01020408060115050414120f1f0903020c040908071502040602010c050a2715080615030106080a050606 67
    0x40250300044584406804105500c4003e0480c0e242d4015910050540e9040c0740d164490400c029900800400483c8002041076001495501c140700302280308000310354030220400304018810380d150380b003c03040082000d001442e60480200a0303540340d070524800702948413008900750451001d50310a4400d800680740c031500448010542c1c0400d034019010741c1503458002c9d4018015180b0a0280070300108000750100402c1201da81c0c15900d01c2d141625041031003401c0c11200403590750100c000b08005540000c10028603030036962100280070f03840c10a00d180020907903803116a1096a080c070320350801086c0c021664400c000030a03940441c9100d100e10f820074141c4201880204513440c8102e0054040c142da60141c0700740c5101d0b800030005040040c4003901c03940101010b02000481e41a51060200da0942052040ea500d1016402200d919007100841c0d04865800380350010700e2040c01c0010510b010644961311840302c80f4001c0c43d55041120080045800400003070105480d6008684283ca0b9441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 514371133 1250 514369883 514369909
    0x50717100c210f051605030a09020d080a020f0c03061e10030204060b070302070603060513020901030e191704030c12030516030c060e0c210106030606030809030f01020324 75
    0x340345034000003003140000c002c1144140c1500f2103072500e0000351000c81203400507450f01ca0a515403a045a5420841c03102401100108070381111100c40007500007213494000d810b041032550045c0401030074400e4200c0ca810001e078107080c86039020405200c10034051100ca0b04101c0b9823040e2108540c2d4505d805000e00c090264002904240350040005100c15108080c101851082e801c0d111a103607200c400700c003521400d01403594008400301d00510082070036402071003290418140450704c00f56060243c1d090140517100d0f00280102002c8180400009a42c24001c0820f039400c0e40d401c1a0454540301c1301001035000741005603054020a80030305000710140d9070f04031040f103800c180504032890002e000722a0350342e00f120308504100c08501c0029010514004c902070180203007041105c000d035089402c1440c40c2c501c40d419569a6008008a101801820301442c05002000d9687c005101031600d0100b182c030307120000b41d2051080c464441984050006d00404941b042d5515400f40d0001a1026030141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 514372383 1250 514371133 514371167
    0x8061e0604151407050304050405041b03120906051207030c020a050601031b050102032d0d02030c09010e010c051b2701080c01110c130b1c050717100c 66
    0xc03400080744100550ba5504039149550b418880c8031050015003414010610001c181d80c000b8002804581000d070320090b40540120310403180c52034000d0140004c1a13541d041500c0c1c500c4801e60310420582c00103402001040c1c0392400519105030074000801c1c6a4015000c08101034861000020312442040f1400c1b0040c0c000d010380e43c0340c2d6900d14100d2284185400d98a00d200d60b80000001c1541c0048142d55118410016810000c04c0c8240e502c0f95018004008055900007407200060340349051001e90301c0754494450346c1d5560f00d54000090028003100e6070312810009107803c003000046005c80c4e0102501a1400b0340100c0412000001d4205518481d591000345403000503450200c10201202e0b040b10103080545102d8900c180045920412a0f203450180c0c3e8400b070b9140320340381040800080a101085c500040110359000040e002e079501e140206c80c3d499900d205c0e0307003d00c002844450000e101a503200005007468816490703c4c0c1d42402c482110542e0307100c3c01a070126028600a140802d500b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 514373633 1250 514372383 514372387
    0x40308030402062709010b12280617100b0a0b181008181605060f0c030c070608150f060901020a140a410c060403030519020601050108061e06 62
    0x408201c582003508130b041c4102c181c03000005009a444049075a108424036030303070b07040340d4850500d030012103407402a00707101041c030002c0d0b038058803070701d2180354080c1292000d00040380c000102c01d01d151000b6000c10304801072821848144036560b50300c0c4801100d041e50a82c07600c03560700ca102c01c0703850f400c1c030003aa81d04606404000580c1c540d01a00c4284030345202e6000d03c140c2d81c100f00f03820390f58410050342140c40703998101007401549840c0c0064035003090311032102e0389400b204c21015421a0414070131640564407a21050150315085081030390301a0b241c0030300c10a046401c10020760828044900c10340203400005a04103240d20900c0815013141d0041d401601d08104c00c8030055a40d007107808195842c40b010390305ea0b1081819a10165500d01c0301d407900500307610b4070321280800c1440d28511118a8032600400030b4440d150380e40a84000c3d4042e44440c0d0f02da0b40c0c00200085030409c21090002190404070040c080c50b82c000d42010b80084098801c031114203002011030a030b0840c007100003071b401030b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 514374883 1250 514373633 514373677
    0x403030605180117060603060112020303071202030405100e01051213120f0201140412200105240301020703090e0c0f040e180f0715141c0b0d0804030803040206 70
    0x141d1003070241284d6195404011041034003551584071001500d94650540104004101114905110b82e040031300045c1a6445c007041030fa281c00145048079044405a0070204003044146041d400100d43e86a050901d6203010310100c0000f4064813444c0c6910380c101c9186c80201304801c41131400e501d640c0d98401c565801200000e800a054040b4405a150043d0b00b80152606281000142140682c1d800944604940080003055504586004102040c90040d0148400d40da409001e42805801c000c0841031041110340740174200602a01461400baa00400c01c2c140000d6000002d46e0803500f0801d000e42d8a5250280044903030702c15611131400d1703010f0103e40804d81c0040da1010501501d2148010702c201c103000b244440c2c035000c0d0b201041a4a4002d000100150300c00c03100d1201015103549040ba19030491007045030400d0308000c0e1212503003400440419041c180e20b125046041b10100d0351030070004800e0351107881900c181d0000400762040800441d08545611050366902d0420b01d02003490a04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 514376133 1250 514374883 514374919
    0x106030507050c030c01150f0b0306060c0c06040608090601050a030503030a05060a17060a1508100207060f0e0607020d020712030507080906031e0c190513030b01080d030525080403030605 82
    0x116038147c094500d4a01e64001031120250140741c01211481d003200c40c01c65071785804001031a0045a1400c1460041048840271503403a0b1004101034a425120300d04981020740d203641c0b41c150142c01c454016003007940e041c80410000801d80360b1291807048085a07075940c10300801e0717091400390311841070f101c621280a5250000818500d22559403044204481c151602d08a03940b8a018130544d101c036081919400d442d000745400400285010304404520000642d003030800b26000e010f5010072540040c0144010581d043c8400c032107654240c8010025242800e459100440c03643c034000b4103000b800520b060400c4050001d0710400d03000181a03d0301c030320f014001c055041100a00010400550300e0002c0c80344100d05094518042c08408980b829802008003501c050340040310300c0c0e0505801d8880000003a10b1a100349010b0011100600b0b2503c0303108002a003a22000741009500c510f001403c0b103450b04581c3c401c00c1d0a426a0300e800300c0c40c0e8844d402c00307400030a80303900600e0300046501e041510300a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 514377383 1250 514376133 514376141
    0x406050a0305090c010e01080703020906040e0601030f06060f210e0d1806050306090603100e010b03070522051902540402040504180c05060408060106030507050c030c01 74
    0x4449071802c0c051075644040840c0c03240f00e001003090100700414601c200070b501ca5140703594446054100103141c40189000542241c01c194481218030b41c540c000c00140e541d1500aa42c0c000400800c00e0010ba41480c4018000345000c900c0682008036840d1300c0c1d0315544815030402140e2801c82401c101c0c05803040c5940f51151802820440850304966026110840d00890881111031a607101e5085890f544100004d10310007900440e450b12840c011008509120310a0034020401c20000042c10f8801200303240c20b200c950380c045c1d4481c1c0c01c0c004080103031000036600308010040c10200080e042d5162004400541446d0540d641010300c0803507101407400c80f6124a1a00c1008001c40d1544240f41510104400110039410810aa00200003401c281c3c01c00d8a807d0724040010805410503444ea40400c0854010039000820f070a81e4088400900c507440507103e0103020f054586c2440c0604040c1d03010f9071188184541d0003015600c00014414a01c0f4800351040b2502c00d02c00e481c1d481c201100c00501030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 514378633 1250 514377383 514377397
    0x81c57031815180816141801120204020c120703172502070506070b0f0901020c19050109020a170105010803031b131e03051b2d06040605 60
    0x201c0c011a9511070000048440078044509118001101051029040f80d403c0c48002e0340401452846001080e0b03000d00740240400c1c180b500265068040c030b045982e5071841680c45800b400b80c0041401010301c0c125015030b95042d10781340001d60807007980c948040f40003071085000c035030058010301c40d8010080410000402405000c1d0b0782d44030b58004070b000480b007081400d03035100303818106910003403a006401a2111070001383d135006a80220380e6903404208203521070074040b200716040c0820010070000006031503401c110104021410300b0590b45c0300955400000c04001b800c0c18141420701e0801800b504031502090780500340719000b1756114032840b0b2003000701724004565401c0c800080f40f02c480001c00e4034801c2e403446102030030f003019484602c0ca1340d600107070807400138070035a0034081a200024222a180c807490301203110161451400d1590801c508117840510201e20140071050341e0703403404018008044420490710180081100c0018961900e044080d008200401d0002c0c0c501d030010b002e80b82c0703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 514379883 1250 514378633 514378637
    0x70608011a040e0f0414010509010c18120201080a1104090c020105060102010905030f0a0e03160302100302030415180b070e01020d09080325050304081c5703 69
    0x1400030268981c0705020300e020354400c0c8071858001485032400c0c1950150024001c6242c041340c51013004809003921030860b034402c0c068ad1141c03000400c01e540103000f45510a406400c01d403840c1e00381040705c80d6508801e00044d04018000000c2884840198032500a41c1410b040315a9216a21410a0050800741000d0f0015501e020005030f550350041c041ca103001903010000c0e62a1400c601e0400318141c04c114503082c1007041003103411045840412030040e006240d1910001003928600c10006410108901130301014010b10921002038071502d00c0c038214065400002c01c50070248445c12001c00700303015000d80103001c0e41303080c030450b1504001001c0319107100f1703801c1d602035000c0b400040c1d81d8081144204025175108000301e014501421507412044144a41d4803409403d494481610b15003040d000004070350080035030080104044060300b03020b01658200090710705112003070308900030420982c0c0d0341c2140305031044459101e036103c441c0148080c0080f0031040300004281c4040030b03910041c01200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 514381133 1250 514379883 514379909
    0x106030606090803030402090604110c06040c0512070b040603091e11030606010c080f090a052116140405060a050a0807090e0a021f050f04031a010906050d060213030507060801 77
    0x43d0601c0200843c2e119980240524025884641c02d100003010483d200780340010b000c3c401c0c40700a410034090030303004038021807240f00d4440c02c04080240e07510413100c0c64143c591110008000300340c001000d60b02144c06034200007a41e940581000d40d000808441c414042d0a0306514030740030804a80e244006407003040d801c0b1181c6580b0000103482942101b807000d4032205060112021290030750004105070000940700d560140d07910702c0441c950700004941145070940c201103d501e1210104011496801d40500400c2d0075480d00c600314086a8240c40054090b0307444c0c43c0098010740718200b0100003003c000c3d09800380e07a40d07605400d07a2200d2442c02080003103401c143c1d0f08004030350001154281076070000c0c40c0c0e09a40044d960542071900d281109001440700c10300c45e2208004405010300b00440c004ca8000311080710100c0e0b010381049051700503c09080c45c00710144843d40355009002c0b038440d0f00210060340c1e4003580440030000c1400e907000410b54410458041072840c0d2005003541218060a840742c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 514382383 1250 514381133 514381139
    0x200a110a0501090302040b0d140a0303200423060a0e030f03041d190203071d010206070f050903160929030307030f05092d04230403090e010603060609 66
    0x58218014441d031400924240e00500240c40e00f60b00c4609030301c000600000e081d00c0c0694424450f0355108850103242d41100341c41806141c1c2600400d020f441304545014000d00c50302c003e0403102d02072400392806401181c841e0141c504610240000e807e0f40c002c05c1a074540021b074a00900583ca901c071440e0080c05000744e07099042e00d0010a881c240c0d019404407090121640300c100c00d200350024884217070340200c50717a083d00cae41255200460140342207075616040c3c003110303d008500b06622950352034115030000382000301c4103601c08103614845000c0d180c09541ca41210001a2500361030800d4104200510640010300350300e03a81c172140880359040402000c0d0710054000c618014207100e103403909904200300c9640041c0c40b0740d446240b0302004d41400c504141c4200041609103002c4002d9201c480c49031921400792407a50075020188050032101400511401000c00301e02d25100ea124040250040020400301402180d001e001f621581031801c91035a5541401400380c94184224000700f44404404 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 514383633 1250 514382383 514382389
    0xb0a02210c091908060c160f080706052a0c0a0812010e0106020607020c1003090b040b0723090910151d010518150405060408031b06070807050703200a11 67
    0x28030840c4d000300c0150905950b154441007a59000314907505070034031180b41040000b01007444d906ca8050140060948500c0c01e403501104481c406443e50640c03504082199002c4503000d0403074196058221440e80d126030507400d45a14121401c5070040105a0204a0030208202c005c0303680c1c1211200b550703a402d96640c400041e88c80301d50555a00005030481203240c005410200c0c82402030165078940003c1d030116544900c004000243c0d002c8903203640e87e01c240802a07034000c2400040f45000d0742c0d06072840c0d8000020440341c0c41500c40260080c070351a40010b40320400c8045020003450b1894500c0b071b001d4182e000080504d002440d0560ba05800000d071004194410300568400450400155001b100c0e61001c03c50030701013009801c1c0103a8401c000102c0d150311240080d10007400080700960325054034480c90a2403002011440d81e01b54007000400c0f50782980300c2d903a150011400d0810a582c3c0c800d81c00c0842c2e5019001403440d841c000c1c0803865484000001484555850050500064502441c010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 514384883 1250 514383633 514383679
    0x50a120b0714040b0f0405090901020705151005130b0316061409090f1008070b0705070b070b010611030919050f030f10020c1606051201120b0a02210c09 67
    0x30301c5800b01020b02081c041d83e030400004241c000c1c031040425040550780c0c4000740121000f02d41d01001d9940203e08c1204210040104003600490f441000c80c5502d0311076207405070410319104188c410865206100502d61885d404048045009401d58400c038000348102c0341034924a20540300001c4481d281500d1545583c0203072980346000510009058888222008a6101c090714198000340d404c0e90001d01c40104201c440000d10f00000b10b2a03c60509017001da04184e4981c0c8248aa10700412142c80010581486503042d5542410590b00e0300d1400c001e200d1450140010482c0c100354229009021036600004030030441d54129041d2005410100c18192a0003850802000e240c0c003211290300100003a03000b074090000c80c00101c41d250280300b0301c2c0e1000400241c0c0000003140c0003f43c40c45140615041c1a40540000b1890529452042d524a000290000c2c16a80c110b40d000c00d5100700580c1203858901440c076600a100c1203420f190070050490341c001c5223000d1042070003409102c011070220704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 514386133 1250 514384883 514384907
    0x608060a0902040803030a0f0e16061d0d0314211819060e0a0203100605030f030c0a1b0503030310090b011112030a02040f0905010501020d0302120a0b0604050a120b07 73
    0x4c080d605540714400c035007014100c065a40010991100b400d4820142c1c108450000c40d5030030550200414500803000d000154100301c0b24a660302c1d00e070200103058850801e1840e1702d5926141c0542c52480303262032540341d40100484800c1280d450442a40c40601050b492030080004220740d2018903005221159102040000c40d07800030b002910f00804152103500030200c0c8500e0b03500742c9031107100d10343c0060700307103c0e81e1800c4078041a42c80000b030016090401c4a0040c84004800035403811425400803540c54489090003000140d01c001c900d0594845088501e0040070040c00b00c0b912800d0074800740355500ac0d140583d450036854102e0500c036941c1300d0b14003040f0705001c0c080a4800d05110700c1c80640c03254001051084070603020000082c0384280000344000a041c21040001c1e0b55040000080c28000c40d1001101010300601100c0e05066a90f105550024440d0308005414080711000c40d1060159078402c42c4d201c868102c2c0020085c200c0e00f175072000103201e58009401950b41010a41d4400b420038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 514387383 1250 514386133 514386149
    0x41e14010c090e0612251403060c04030b0a091e060510050a0e04020d050706020f0706050f0f18120a060b060f030105130f09030909230c0d14010608060a090204 70
    0x200100e12103042c00c2c1712001030405414150b514034a20181c0741415480c850340482031200c0c001d441005221140f03482a540300d1001c60103425203041130340c00c03404140918003016040e1000350010850b040c0641d4051212503502503180001d2159030b004286040c0d440900c00e59055082c200004c0392a00c00c000804290340d4001d201041c12424001c2e290b07491600103000701e030804c5e601241c24011840420082d0000c02856004140f0f003c083e0344107a040c60425440f10302442828844504400e281100f5180190b070314485460312071250441c0a08100b182014440c1c001e00514a00d4501010202c1d43c1c00b0054040c03a424004c1004810501400f8491103405001c4514240010b10031803070500d0200f5400644413002165103007401c0032920490f129000e0860228602280400c0340b94881d000e52840013281310864007a02c842414072450b20788004040407030110300000c2d9221039040940c40100188640b81600300306e5a12104068070f01c217005d03035440d8442c0c004006e000070316480e40c0c000c99080c1c03000305c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 514388489 1106 514387383 514387409
    0x601020d0305040206040905150d0c05030f0a0f1113050709050915010f08070c050f033615070204180308160512041e14010c09 56
    0x44803080003810706180401000d655600f0607501101c003c03201c0480c103a0ba035803075611900000b48441a6100c09828819401e010940b04124182c0d0015002c40e00b1200000140540e1012108401025009044c00350300c0000d0181105c0200d619014141d0f08041c003000500030b05481c3e0403180c0c1d0300000c1c00801c0402051a10030106a0004000f4026584072150100001c14049400c042c0c6414000d448002c1945684113019401315590132505460105011485440e101c1d407005007092055030000d0a41036131074205000300389460074020b481c50702c0c1c052403400b0710156004420070908024807d101190140c1c5941c0107181c00203507000001c0700b5102842c84c4c0a01074a00140c418224280140c500850309038104007103e00c00b40184840084030780d982d01d0003400340140e0800310f0b14404c0111051500300f05c100400100c5404840b0000d2081d080c0c0c410b001c0b0354200d03040c800d031203008481c = true := by decide +kernel

theorem cover : BRFrame.Cov 514208633 514388489 := by
  have h0 := BRFrame.cov_init 514208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 514208633 ≤ n) (h2 : n < 514388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
