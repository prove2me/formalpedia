-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4412
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:32:08.445954+00:00
-- url     : https://prove2.me/submissions/baf4a129-2dd7-47c6-82fb-e1683a361190

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 793345323 ≤ n < 793525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 793346573 1250 793345323 793345327
    0x51c020a0620061e0f01060e04091a010b0a030f0e0d0804080d0c0c0209010e091f02091504090c050c0c0d02010e03061f080304030f06051509040b060a0902 68
    0x540d9844046600322286070418050192070703a030141840705610302d004400e500a0908011000845001c2d4160111420040c3c2919070b80d5000c80318003086086c003500700003508120b01d46145081681c40509090300030050301201c03441c842020f03030700054241c100004014003c80c85810301c079094043e02e41c02e9448640c0500c00c0550051180c1c0d80d034020b120b242000c100034000480c0912080504443e01c03490511307000d0142039801040540000c00f0103000324041c10f1030301c1c00060b640c0c0c190381c16503014011550203403c248440c0c201e400c440f44c1203080b9001c1c44503420408180e06607117070b07407403403211000c0c03100d8503038a40d882c0400441c00c13141c4e241112820701c01708102c0107119040c04128002100c0d400c6034071a8034900b041c0012503084560011241d0148604424810f0311180804044403120a100e44841115101c0903403a8070782c00b80c0e2100420150360030448500040980e0441135122084501141100641c5800103024040682c1c081d6055040780d4207101c010305008003c0c0019210110040d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 793347823 1250 793346573 793346629
    0x7021e01060b030417040f06020102120601080702190203240103140102030f01120f0f06021306030605103903020609010605061206031c0e030115080a081c0606080105 73
    0x1082c9444004d200810103190305050304038803c01c200c1501d019090030358030303081c0e0640c498001034000c0d8031019400101040310740001d19103610a17030302d03180305020580c090012402128850340460311401c0040303906000d00e900c50760584060540104640ea0a81003e4030954074500f4103043c0c2070807191100c908d07640100104984500d80c280f0440c1100c0029408021000380d41c2041c00c19082d03070000042c0b203030386481c00c15020b00c4030300d03005003002480c80560b030541d5641e20441501190030030311130a90451120100d1100d5a40100300e182241d0345c0c0d010f80d1250550100148002066941d9009562030544c615150141941000441d5001850000820185013044000785042c0a0300640128038450300c0001401501c05119500c00306e030f4455030092044c980180c02408100b001c40400d0701940c030702600101c5a030983e003103120407600c0f000c01401410426468080541d0302c00f1800034241d90360700c1c80c1d0f1604000c1521a08000349081c1d1342e014030b2941030008001010b42081c901c40c102c000e450f0000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 793349073 1250 793347823 793347839
    0xa140d080c040807170c04090c0512011a0d0507030b01060c03110610030f030201091a0a1a090f100b12040317090d050d1d010905010507050c0c011b050607021e0106 72
    0x81405d684036416015051108040b01c01d24203022400515045414007941000300070398401200c0a9a208440f06a200800348070500d082f105500541158052107281001e620b041040107000c6550040080e2003d0903100d0b142d4502e420350030b90010300019842c119a000380b590001460070445c2c030a0340604028240300c00b189501401501015001c010f110584204042c000d521410b01da5600081500003403503040d2041601304412200365125500b800100022600014880c0040d484020304104664032042c80007e1403c0c80101060f03924405498040782252400002c0c06070351f0000808000c0e540790614000f8900140ea03010207000064500c00d0229014022030f40c400ca15036240391068550611101c00400b401d0030a00710a02d01008110700c0c40c2c0900107402100c001800354009100549a00e074007105d41e882070b20909211508000302c0792000d584035a00f1101d1240c09200e0705c5480e0590364640500300714050326000c02507030207030f06440c4012100020a1040e804050001c00400d490190f079 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 793350323 1250 793349073 793349083
    0x51018050d0e060d0c03060513021e25060504030219030c0204111b03070c14011e09170604050c0f010f110a050703080310090b0a03080c0a140d080c0408 67
    0x4101d06101c00e42d450684607403100d070140e07220b80b0a0000103001085c10700c0006001842180500c0340100c000c408030f0b0000544034021508003180d900c081070842808600c01900c60340202d0104c1000c10100c0300c4d081e0709a1650004500001e000d1070000a00d070800c1c1c5000fa103480b588280c010000c1c0303104260800070981154030748010540659007c50401016a070500040c0f05284000800d50100c550705040e80c0f2000000e4904188a010440521611120140030302c1c540c20085a0008072551030a0140b00c0e90012051181801c504010341115104ea140d22202e030707680169100b0030f5204604010920100300500303189024180c4101800004881c0000c040c058964180420320034119000081240208940302c0141c1e0060242c442c4203840c2e141c0020550310a49188904240c01c98000c030b448282c0d4400c50025120007407074854200d140d913035a1800c5030001000c0305501c1c080c81d05031704007240f40c00d094940768241c51005007485192041020305090006000c0e00c403141400d01081c00595000a4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 793351573 1250 793350323 793350343
    0x10f090b0f130203040f12090503070f0b041e03020303120a0b09040b070c02011710060807050f090d05010207150527280f080a0806030d141308010905101805 69
    0xb02c05660f990381c9042540703607240885001030070300400041c85100298814102c1050310320440c1521800c0f07a5071840304010b400700b0b015181281000300002c1001c6480080040900121005c0180003140d80303030002401c0d50000c4a1400c2d0419848080218a0505200304013030280c2c112450251401d15403210304203d0402003882d028800841c04001c1135a0103051889000c00002d411000c42c0d150064904114544911450000c1500b401c08202a1800bc00554800b000901201810038003541c0801005034040107040e00e40d5542007045001050182d00303034281e915403101010a150038610900e0301240078030451003c04c80c0721644c072070300007034008940322290b00e03030408040503041c0045951455103080c1600040c42d80440103004000c01c4032410280c030810041e916081190760f40c10080c15121074080c8400f60000da80c0c200c25003641e503e0364020703108a03a81c131640c0d0454651070308112421100c06410544c0c0c2075003c07500142c03180c2c01d24081c0c5020000c80949000b080001542c6043da1184086 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 793352823 1250 793351573 793351609
    0x7050a080d060b0c15010f1203080705040e0901090b01061b06050a0b100c03080714031b0c070311040b0d02130c0e090a0b100518060d1103010f090b0f 66
    0x3801911802650010300140c2203107480c0f180e841030341200d507582d9510760120005024000200000c0e59401d0304c01e01c10101d440110007040321001d0780c0e80071507002800900510904c0700030320000c240c40c040c0c0e952140c070038000c04d00006180e0b0854205044540350580c040003c100c015400d80e09180030325816180e90681c80040462561200185c5030007401240d1a1550801914600784040a0f4014203144105009888061a07510b070070100702c814102c8000361050303131a010800b050303e080b20035043d512195030401c905800c0c01c4c400e01125040580c41e80c810b6854140100d54588940307000c2c805d42016843c02c0b901250402465800304120740860001c0e60105550b030074003011150b000e80d201150500f0001c15408481ca001030b204802880100e061501070440d2144180e40140203400f26602c6040200418029407902003c00030030386d1040c4010500c1546410206403500504000b0318060114030034414401814a05180104c0e242c07038100522404040c0c107114095120b002c50444c40510034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 793354073 1250 793352823 793352827
    0xc0c1e0706050f0f0f030a0f050601050711010908060901060e0c180d030e0a0e090606010206101e051522030210080408090a03120e030a050616110f030712020307050a08 74
    0x8910b03000d5030144030f07644c843c803a0001408030344002e5440000c52192a904c20100400c44005500348100c035800c5403254089001001040d0214072180c0d031080c8d00d00c0d01450310f01544d40c4c50304c5005080460585014009a46654040c03000c3c22007490340320f0344070b611400f081342407038141850300d074000305886180307801121004410000d00d8070032000366a903010060030054146659000900b00c0307070f80c111a448414021000421150741c40031071440e0080c00601e41200e011400d141d410032025420702c0241015030f400762400120b42d19050b42943c0302c401c40b1101d090300c8034080c840040395141c00786160103220700098010b02c01681d4445001e83c040c1e41e1450a406155540c0ca0052218410160400c0d40306604503000420004441401c4030ba16004e59680c52442981c2c0c4249640c521400c040200f0942100c0002020003090202801d116030381494281c464824542c5040e0801c841810241d1041e000000c0701030910140043e94865403d00b07100862502845480303003901c1c1c2d0f06206c8014004440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 793355323 1250 793354073 793354087
    0x1b14180417070312060b07170c01140408030921030a0203060103020f070c0807060c0c210218073b03030f0c03040905010515032d0c0c1e070605 63
    0x5200d8480603001d81801403951032445040c05010308242c0b20b1204641400c004012500c03c031100f0503100196440813204448410490355513086411110f00c41e007541d1f5076661900c4064881c030350110300072400f0b0462941d07203062545145040180441c20105d00c069160003210540108100302c2c1c0d8444218200180ca0b5200c801c0101d000c2d00c9100c0352031510071300c08103075041800040c60031401240c6184044546581e42c2d490103903580c04845c10013070090310004104200100c0003894000901c00381c0c2e0200a162095940046c10501010700380801e0030b10400100290b554000154880c0c841c0003485000300c03210740d40d101c0f034258443c3c1c2c54112079654101d540840360b603c0800070ba0b1032003070b100650180c1741c0b8800c4409a549130814405e1184803800c2800004031030a107000304058105020491502e140d95110315240c8100fa000490000e140245210505141d903c40e40342e80500405541c40e50760307500d80085549484840008030100c2d42d0b0480018038446030008110007150040c0c00c1542c3c5a940e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 793356573 1250 793355323 793355333
    0x30316050a0206120a0c0914040e0a020402041d1e06010e010c020907050d0f020f0910052502010f09050306011502071d07020f0c100503060303161b141804 68
    0x1001000940019002c6030382030205134000c84a070300c54480c5c01c00c1042240d11903d001c544e41c0c1401e108403404035840e81d5541416061036004140007850b07484c05c981022103960b002c40c080343d00c84d40c4440981c104050829404a1000c42c051750010482c0c00d03440323075000e4540201a20394002410203810300070350001e007070078a90248202142058001f0003054107440c00e07210150860b4072441d0b502c0c5101c0c7c90628590802c0b20903200b5249007601c2d04187c2424042c91130148240110100584024850700348100342e120300503036611070007640350f020031150702103c1c510000d03000301d4074080750b0014013100c06014055070310000b854a044a21b4110a152411070b400d03420b030304160190700101614030700c0b0207019510a061040d03690140d9616402c9406004c803105c00f0030f0304ca0002c110740c00ea00411113166040c03214842c001a41c1c0200c030080c2500e241240524000691501c20740f02190030929241000c1d00321410f003e5070304010106642260803126074030f000030701410385090480784112040740220301848 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 793357823 1250 793356573 793356583
    0x10b0a03090f0c06090f0305100e0a170d0c050304121b0624121109180d02160b0408030301030f06141f0b0c10090302210c07050103060503031605 64
    0x9a00302d44884044255410310f92819400c501038040840e2000100192800d0300c0c5c69124200d0380c010700504580c2000268050280901c90003c5803184141143c1d0f0000c5038140c0c03281c1a4803000104030341e5550180d408101c05881078910040248030041c02040040303031110b642c82c141c5002e985011902400c071944001c000005800019100c68a030481c001e680d035841c0606200740d0700d892402ca0828651303c0f000300286c82e0522200409141e0790300c030b18041a08012807450341218140703040d1011100301700c1d16107242c200c01140c0031005911146601102413080030002004d052200741c15450203081811842d640d10040c8030040007040181207220622a6603409007429034460004e51102c2d04195103019041e03410550702ca5642d400d0b01c0c0b400501c100007201200e04101000000d0070640d00c0020444000b003c0c400c8080d0258050f00b002000303951468981c0c80d01031200c803e01d85440300c1804031010703d080400c1c1c108034181450024240000d607000026130300c204058640300031541071586007a034105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 793359073 1250 793357823 793357841
    0x60105090909070f0e01140f0d1b05060c010c0e0109140603041109010b031816030b1b0c070915292701030e0d2c090405030717040b03010b0a03 63
    0x25441032031000c0f86140c68175492a04a400700710150503202035104c00c100c3d0070591004002da01c94440d00d001000144044041c8555201141054001d2561000402da1540c0189a031003820b944d5920090191904644c504145e140c082c603207691030b5030030000c4170050101060b01c0345118500c040002070401041e520b405514100c05440c0d003105507510a4035802d039420603101140c01d8002c48960800388140080d5200704032840c9000c000c145469900c03201c101210182c884010704260140c00203050b0609001030504c0d2014000a00c6014a41800001180d822401554844a9600080080140044500340b070941405901c02d030303842241c40070181900ca0380483c0000c2d00007861000c0791880c241e10341a90f45103020b89040c480c0000000d6950b445503110000c00f00850007001e1181d0419005408641c1440e0243d441e40f244468040d00064942c0703021a0102d0320396000090200801c4003080340480410f001040b01401c1500b0940c1a1036640414000d20300c2c1c0840121341c030ba2038184a60015481 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 793360323 1250 793359073 793359089
    0x1f290403060e1606030e0303040b07110a0b060f03030f0904110408010516080604091212020d0509250e0610050405131d0f060406020c07050303160b0105010806010509090907 76
    0x34110b00c0c0b4091a26038064580031203061010380c2000070014083e00030f50102d211124051461541c803a540e65998000203081c050401c030031400302903908501001001c2c2840c0c021000e01003540703172010400c031180450030709490280d0000c0c011100c51403616800d40300c11980407100481d00ca01140703540811800f690b40000004d609000c180180201d021b000803044200d25a80c096a540d1000144030950f01d0402c8001e041c400c10309500054184102110600e001180c40e0252600700c00100001c2540c90669035a03266030032000400c3c4104140780f0340448100d0710868440c00341443d2a88030b5405010051165000e000b80040e20285244030314215400380c000103010b8551701c02c6200141c5c0c01443d02050303486d045011044110551480000c240203440485c100500c41c1d0f940b55503d0802a420250100d1034920a10700d0100c0c0c966424000b90111002d00340790341d48290103d04005144a1040c1c0c051810301920a007402030760313680700307048800d180004d50f084031040e1140f03141d01d07180030100d40c05200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 793361573 1250 793360323 793360331
    0x16020f09041520030a0b01180b03160305072016060216060534080403080a0801060e01080403230307020a0204050f061c03090306141f29040306 63
    0x8220030303024121014840d10b0401c1040c1c4124000000140508002c050b00c1000c00b8000580385070459001820a50b030b040c03404401501c42e4600300d00b119003031508040c80c40000842000362550001c084294442c1c5986000e20650074127120186c4004c0b40c9050248152480c900c1e074812600003004840b140890b028058131069a0307682c1c0c004e4a4440350341c01e00b4515400640300003003552040d41a64040100c0c084200c01d019450707103007032090405900b0046089151080c4c2c19010680c181e01030b000a60180c0511651a01103110084c030b080c40c1600084113201d84100c000c1d09599012002550065160900303004400500d0100c0d80c500d5520300f0031610381c0d1f500004101c410740c0c1c08540d03680c1003482610280803036184c04681104050301154015080304881490340032556540300c040f5600b50090902012071900d80c0c848109840444054006444910b002d10000c4010301040380f0511010b0042c459246d030400092001207911800c0410302514074881c0c0c0e802030b0a00d44102d03801513901000c204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 793362823 1250 793361573 793361581
    0x2071802160b2d07121506051309020403230a080f0306060c0703030e04150e0622050a021201120308060907031d01151a07030309330f0e0316020f09 65
    0x1108000703084440c10001200603a000003d580c203406401215404121b072400c1c402c0c1000380c21209500400d50001c1441100c80c000148410540300400155000e102c1c11051800d001010365280500e0b0400c0350110386c0484503402c080b69601c000d9942501200c00081c1c0e9a8541800280c0e030740c050341c43c08100314020030f0000820942c01a01c4031903546810342e818001c20182400e440e01130382c0305102d00c4d41701c0641000014000e1034842c4000c070b011a002071808070101010300080c801c80f48100d60103116144d0000da117809803070201500300c5c01801f8418031194a101c0300e5030000c100280250000b03001c4ca54580105038214083e070440c082400300c54135070801c0c02078900e00d51406400c0c0c80c42c291403006c2c00c44c400422941581030198081001c05000b0303910344510b41c0d90440050206003400d4032080503400104c2d5071114401c1c2c10101080243c2117801e00160382c0e03502142103640115100190389d10b0b280700481d07500c1c2d011081c1c4802d800e041c0c0d510340a541d080d00204442034142c2c0d400aa1200d1540104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 793364073 1250 793362823 793362901
    0x405090c041d0114030307020f10031413060b090610120b0d060524060403081e0309031306032304050c0405070801033806040f0c02071802160b 63
    0xb6049a0705140c104070104040d40525440c1c3c41041e1019410540b00440f05a0509201988440644040c5000100c0400c42c0c00403d0022606590071807281030401d150380c0a211840c0900b181d01103040f1004415820314400080c0961503045141c01444050034481401e40317965442088d0040c0081c0503d070801c9410b02c5c0520062200700d607141e52580900111011600c1c0002856100b0303000584031510380b81c2561148080e540140380300350b00b0022142001c2e03d04161076009140102112002592292140b101e0280800100d4019504051500515000107030b42d40e5034040c881009000f005046803a1401e00c1414801d99400158100341048244030ba41130740304804030f0480307000d102032110a544084034100200400301c1201c17802c031030346a8140c1c49004010503007a0414002800041e21106140d076210076902d40201400140e040000100803040f0b1107404e403030fa0300354040c0f011854010540400303c41e5403000c0ca0050301c981540720024180800b0100000192007210f0f80d01028a030004801c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 793365323 1250 793364073 793364129
    0x2011e02030702120a020a2d030812151011011103041119050108160c05060a05011d0405070b0a090b040b09011e022e0e010c0206070f02030405090c04 66
    0x40b40104e4141d50300e4141854081149410300d680103000052052411825480218234404590030541031241810030069002240c2c60085200e950004e4444c07130a6100200041d1000b4903a5001c1840c2e00d20481640c1d961821101e403070141030070f00d0200c0710b24114046005054000c83c14101e0003000061000344100d502c41c2c2c0c02840d0048440c003071809540307030220328074a99601c0307440d0104030640f002c207407044140102204c1c0c101e141c0c9052036200316141c440b50714106d829695451034a07507450050240e4040010700c6000710080b2140082c5d05e01f000c0d07407820f55880880c8500940010041144406d5a04c81c11594004280010145494079111081d84116500121040c4e000c10740410b80b4054502506071740003c03020641e00501a0710480718030b15031528007548021241c0b005440310040c1044098811124002540e07400003a6551006401034503246016001c0ca06008681c0106911158000103d50548006072024034140c2c941c00c40b901014011604074a220a15082100d0008403690f24 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 793366573 1250 793365323 793365337
    0x12071202070c0b07170a020a06091103030703170109090203100f150603020c07050d1a0c0408010c02030c01050903030108060117100e03030f0a2c0f0a0b070f0807090e0402011e0203 79
    0x410014510301703071105400c40c400c4a65113009a008011400041501030740f040c0001409444800f0001c1c070320a0000e815548a2041100424100c41c0c00d00f14161a0046260140109410070400311070107800081d51074220f12402d8003501e499000e280c94152080e00080050741305401180040c0781c0301e44014010b5000940000494030584100107058a414451600c0a6401c0414046d6029011507031007000c070f50080406d15005030410002642400c24410001042c030b4540c051034855204440c0207095480c0500103e01c1c5901c04d00041c0100391011400c00c0c1180c0e44d12565140c26000d10000c941442680800641c15a10b44285400c0381c41021000b5841840d054001c8030780c603681c9030b07900000c550b0116603106985003a6000d40340003c520841022403001000222254091340181491800104600407a6040181011302c02020380021800d100c0083c1414540b05070316105000514248452081c03d0314400b00e00702040959014035030000100b0080081406040d44001d00a503890380030380 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 793367823 1250 793366573 793366583
    0xb0612061801030b0f0c030c0f0904060b1c230f1012120f11030a030b0307051f09060e0915060c010e1f0213120206220e09010212071202070c0b07 64
    0x50001419946c141d81220702c100d0103141c14600704040204800c940d50403001d10240c003d03503150004248034107540041d0034503c80090181d4202001c03c100c20003a0789409030500c092001c21400707440300724104040940d005e026250200311550320034052060581c1d881d807256180505240c0950288011201410b11810281e2541c4022a140c0030f000c9032a401d504150580d10f03001400102441c610907046280c00f55001411509415102c81c002100b94801d00c0c1183c0c2e00c231107140f590301055600600000024005400c0a2a5404030240481d90340e11004103890703814111401044200ea566205660f04000010000c000c021105100c82d80d840c9650030018800704100c0b2280b40700d042180c000c40d5003410b108103205c03051600d0503207680c840044001d4102d0340300e0001d106002014003280c0802142c0443d4864070340c1c02611717103128890304000c084c0c19846264010842c0c4518600030340e80382e5400030041e1910302100b90101010348003e01885000508030328400c100060401c002c60082c20032203001d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 793369073 1250 793367823 793367851
    0xd150c0e01020f0d110f120702010f051303021306031505040201020f0f3a09030209013002011209062007031e02071205031c0b0612061801030b 63
    0x90016a5209003c15000c0e00300d0b8843c2c007400d00981d00c11684405950307120000c0300c420301e5400da101c03810403880c400c16038045580803481c1c0080d5a8440d078091070084031401e00c64507001c0410512404030145000c040d000b02402e0b1080c4c050414a580b00400558222018007000e002c00c11002015040685050340140b19403190000035943c0400e5124401000c0c0e0028080d40c3e01c800b0070019511400307103084145808590f51a1a2480302c201c04002203841995400089800d602c1000007007030042e0802c507005028240006540e03003005e010307100c3c8002365011000a034101440125600403403900507415590604814408004c100d810007240780c5407a11220704805181e0004804034004d0350000f40004d13800400100c82c042012007078010f00089441921001c0c0c1d04e0310000082c0010076a0b0448282d030000409000120800146840213000140203018012042e80006e105010382c1d003640d119012604085940e6990301411030340d80048040d0105810360796030070306036445c101c21140c00300d88940c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 793370323 1250 793369073 793369097
    0x112b0b09121b0115080d1106061005031003200102060a11030429010b12060109030804090b01031d1c09030c030f08120f09070509060603070c020d150c 66
    0x218040d4246501d550810b414a80c1200d0044540c5600311000103032035503034501043c00380b0303440d181503000b0b000028000d050380d601c5034000520b02101504c20300030a800810500c145569045044400034a062514035203d4890142a0350013041940c03004191078000d1060004040032000e030401c402c0c00907000d807111a80c0d102c2c7c480083d240d1492130702d0560b02c0c00b00000b40003d14080c1100100b206e0710380340a1080103080080c1d14000c982a0441124081c02044100000200c030381e0444d0700c52000e1800c80030385851581c0f016060b00ce00c1c021031120326126100c80d245644aa4030100484213850043c1e44503040040c1c1181d02c60689a0184e0f09082c0101c42d03820815000c0e106c0c501c200c0758040410b00c5038510303640364550750452820b4211003450040020b80c00b40541e1000a50080070b642050344030504251503054a03003e000e40c40a0701400c0070904001d242d075a10001e0702e0340402c0c1e0b03050060046034144001408200f4045005141414a0001903800d4030542d02c06ea0030048180c0b0b0740010101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 793371573 1250 793370323 793370341
    0x525080103020d020603040510051f14031c21020c010b060c070b1e120609090f0c12010915050a1d060a1521050d0302030105090103112b0b 61
    0x2424003001e034112510041c0d000c01030038014001d5a2040c0580c054840030890748052300203441e01034410300e00300c56402418094040b0b00f1050b1800070310510400e4100d25400368003003500d464442a10b142b003e211840203841060103150318140e41e1031000034000c451441c00050038003c0d004800002001e42ca81403e01d030090a1002c101c980d01d0f003a05009106503450700320380c05001d41c0480d800e080c80741d221082140b80d400322000030b4050b2480c032a40100c4149841c034103000b01c90100a0412211f60b100b4200c0c5450800081201c40c000202901c138a900416141035182c094052003000030610b4241c45901400500d40798422805502d0300e800510102815007202006003400405103040398100e0400f00d040c41c41d0550250030000030703040c891451130f41d441c0403524904907000d1a07040010141400d400800c882800720384070b22200c038281103045504000103c3d540c40014003008080301050b07110450305a4850000380b04001e441350f5440f09482c58034803e84150ba1400da030031103802c5001d4000c036170005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 793372823 1250 793371573 793371587
    0x70f08010606090b0c120403050c01082203110f060106080702060a0c0e060d06030c23061e03090106090f1d0705010e040b0609030102070b190b01080105010309060f0525 74
    0x300300c1c0e65452031075401e01088011a61140160030446d2040003403400c401d012400181c40210302a0001d000b031020503000250801c5401082d03a05032003e220103940c201c6140c100c0d1100e14580500e40403010050340400e840c030700100d11103020610b21400c400024156844030005200b460301d81e082d100d071a22100034050903070303c2c0c400c00307000480d024140151490a0242c09080303185011000807425a54940300c00044404642010312819642c8540c0c1120f8041d106010000791410340d5442c3c038000354050818401d0301301d400b6003401d60800101040d0582c0382500030384094540722100300103100350b640e0030300c0c000c0110951074042842401411619880086809011214180c541164034483e640130403008084e001082c3c0e80c40181070181c50a1910300f440503022061058180c440f19080174160200581c200440c403010540c1020603892440c2d80c01038101c2d045440038240440c60908a1901d40090300b0954028414103207002c04004424404588418030980c0100303440950100c3c13004200e400c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 793374073 1250 793372823 793372829
    0x313170c0601060806131505040c090f05010c1b081b0315010b0c01060e0114120303130b10030f0b060a09061419080604030e0405070503040201020a150b030a05070f080106 75
    0x6078200c04010490381e4010343c0d01680c4144014401c03d030f811812001201110b00c11424804034850115062000341081c3c4540303521038460b41402d00503903140c60016449601103001e07990401c0803c100c17101c20046103a82565810001001140150342c039400007130740c4c41c8500e04801c0e90400d12044009000c2c02c0202e42192000d0203034140c600d5036803c00000c902d030b0380d0011102d00c0b150b40d80e5820018410047c00c010a0190442072040440d90541d1410403032840d0300115000c150740c000b0400d001c800c005504103039020a61101c00154a0f50716501c18090001117070b840a410780020800a400704810b80e04040c6c80b50100325446218103890f00234501c22a03e0a004600c40d590180205002600d000000b00218510100103980c1c1c00d070b03c030310b0928200201a107049021602c03051170105079107031600800d5841449450407606615094000075554001c400c0007510140c5604521710010380c46070481c091485010302160988002860701c10307526017541c8278111040181d840c0103d00801d044c0661012 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 793375323 1250 793374073 793374097
    0xb04090e280f030e1207231008100b030c120c090f0d151b020f030a09050d0f0203011e0501050904030507080f0409150303120c05030c0904020c03031317 67
    0x350108a03902d211490000380c2054040c445615040c003501ea41d241c0c1e6040618840c6406041081d14106022203c44c0c848440d820800c1030142406e25540c54a0720700d80c1c50300e0068607000486442c0c54520a894081d0741d005040c034200300004001c0415290402400305498541201002d99515841d84615011340c0f0f040503800386401c1030104180ca0f001d0080c241c40390148918680c82104002d19104480c10003428013200110303c40555140c540600086041240d0300000c1c0d0700e410440071000b00710881c68090303248183e0400d00c0314003d03c210907080c082d01c0313513014000308040950810b01012441c50b5095501c0c0c1e8034200f0001189906100ca40240169410f17119142008416a40d00c903094002da04908031000c4c05210011380455240106080081940480151641141001040000b13902c0c4a000110704110740b61000c6a4800100c2e41d0007042842e610f0380340c6d010400060064852861b115105110110034068030600d00d074a02e04541c4c1c8500125800022441e00c071480500411100b404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 793376573 1250 793375323 793375393
    0x305180a0617070c0b06040c18090b0a0e010303050a1101091a01180e15060d0b0c040911031014060702180609100b2508070b1005030c130e070b04090e 66
    0x4028103107504101041001c030300b0700d649c1c400303e0010303030304140050395226441c0a520381880c10128100541484080c12681d00c82400230740c11a14040d016214007a0346108001c0107000200c0c40110a47c0590156a400084981740300e90b41d000f0110480c6082c0981c58440d07114221000c401e07445031051441402071140581001946c0001c80621024001d0115403c5403d0000100000b404900107e106600f41107401d9115810000c2d203a04642c401e0200b040ba4503010003e11082c0d50240520030111b40d802500c3c81043d00d10314011171810b020b6180000c0d0040c0e01a1158000d4261800c491449075500380c03902d2043d0307600e601003010030300581d2182011840e8200200e82249054020208003030104552440d80da1000390303204206580464001e0743c043d044881880041d01d120b0000070024002100100203012881d80061056200d0812044c5001e5035000320300b120405c01e01c01301d0000c0800da50242c2e100d69076040304101410f0115110400c5024151030205951200000c2550b40034041904403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 793377823 1250 793376573 793376581
    0x2190909020a1d180a022532100209030f010204050a031e0f030216091b03150b220b0f04050d0201030e0d05090a050a03050a0305180a0617070c0b 64
    0x1079020b0b86440d6410740c0051014001809080d2680d41190280008060040c4e8452040c91050986040480c0c000180f070404540c1e0380100e00d01218001c1d07018001508c541c0003608040381800035565480c41001036010342c05102011441c181d002d00300240007035066400d490440340e1207608078440c600500b6405400f0402c1270001c42c0c0443c465034101070b043d90b501801340006031664503169401810880059124802000000c18100c5030300d00106030480003401902103031500640c0d006051000030080540d02e1080682000743c0300e0301d0788020000040c81558407118070742c4a030441d40192008015108004800080c01900300c0c0480d002041c40e14507060501c0d041c04100142c541c00240d080e81010b07195245070b5481c040600007800280c50607242c0c4c030343c0d5190102c10320240032525441240310f030345101e80c2000801da0114a0501551f85480c0150fa079040880510340c88055141c84190440109032001c034040d03411007002c604814945101c0a02030750359000440d91412131110090240010030081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 793379073 1250 793377823 793377857
    0x1e0302071502032a06040c05040f0c0e06092701051801060e0d02120718060603060302030318010c080a09031406090d031104090212071707020c100c0602190909020a 72
    0x50042c0040c0402c803004d20b289104055403620700306403410740d040c21003414100081d29052007084100e0b0b40d1a0414482000214000380c980411110800d00401c40010360300e909503140c0240320344a078040a401508040d010301320080d540070900945004000010300050800d092441c068100c85035956a456000d19660a0008241400d0300c00c0b1f030031030000c43c02a0703c12001441401c000d48003400410b8100304402050030f095506590000c414107140030002d1003d40c50100c01c442142c0e20280c0c102500103002001220007003541c02019080d08404203900c4520340c0d0102c0d460702164013740700e03100301c4451640e0b0140c03184025125507119a20840440398054041c0e040070381c1c1545007140840c101f03652504510b00b682d1114645d900c4c1c1e541e1007010003240c10381219134842c009900d80e950028074600440007950740c00568880c10711a0960241c220300300f6200c0c3c040d0103900c0c0c0d84000e066455000e20744058861141c0160420042080200c001c1803483c0c8500c21f8a9a4002598400d40b42d10311001d90 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 793380323 1250 793379073 793379107
    0x5090a0b04152102130f0e010c050a170603030f030901090b060f0d0204050c0d1d10090312320a0b0306070f0305090a12020607121505100c1e030207150203 68
    0x1089030044240f045c164010080c900c500304038124452004207002010b80d86060845d501c0030180781c01e000c401d00002d10f0840c2d11201007581100391000314030311516001c000a00c1c5028510440010507400410080710700019007049046078460000c480464482a04004650001c610000d40280d1006000c2e8058a4076402c01900042c480c0c0c8043c0c5400c10621242c1e05540082e0351182c04545105100d0040e40410000600c580100000c10864018140c2d0700401a0328514410181c0d59103415110310302c491601d081802409409003141d00b0a415000d80300141a01125070464503803a01420017880c2c00d0203e03216200c1d0016654805401c100203406400618001c2c15110040c41280d013604000764070640203159070051600280407034a44054001c050040e48100c54030081d0070710b0b41280c801f010700c03d080401e848044030146106507207060210385591820700041c1400c0070419480c4000c68803811110031842c002ea0a0718009a16408140f618a441c5500c40e40168010001c0c2d881104035010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 793381573 1250 793380323 793380389
    0x503070302090d060513030909050f010308070302152503050108030d0e0109050d02011e06030c03020f01051215012601031b030c1805071112030c0405090a0b0415 71
    0x240010f50221515601c048034011078209840d03803540d202100c01d060b0007101d90300081c0407052041c0003030303e01075011410b030401c180301c010510310011a6070300070140280a021046021159203501c245440c2031403510343d00d60030b058003200107058880032844511900a00c0c1c16103104000541c42c00e000080540020b0030b200329942c42c01e540c3d458080d00010014850300e810b4040701d40c00401c0702c901c000020400500d400303040d081d020345065030810020341000084021240c04a0308207a4a6443d42c0059455115400706403034580300f9041080100d15030b440e89109039010a91751202500d09400342c046115a102002d280e24800c403000420000c0d011401820203030819140c07903401540e0b01d03034421200080680040c403036044000300c9100c01c80c0f020301c602a402415480d0070400030b0440100c1c1502c81c5040f820001c1c0b09140000010718a08564040718020f0002810039046481d011609400074000304000c81d1183d0f041070307500c00c0c10380c1580a1200c15650b8071009000d210131100d071400440070030701c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 793382823 1250 793381573 793381579
    0x10c0c14150c1b01021c030c2115050d1502181002030a0315032411040905040501060b0702060f03060f060d2a09291303030e03010c050307030209 64
    0x300c00030340707941650024000d1904140010b21001e00c0611502414402d100b550030304550140d8480c030990300420544d0644a04942800500201030490440f2094070342140d000d1b205984000041c1a0781b1964403213020070310b404d010090016101c0b800c10000d8404040e014108402a0504440726115a4010b0070384507a810111920400c540002c0b0308481084850040503810100341c1e000503a804d8090306500002050008510506540d81c40e61015070840d0a0b0400c800f00c105464051040e680c04026503000c22101c140e100c0755665405401742800700e8040f0303115402d00c03000007002c0c441d031004d64500c01d50003410300c0d0030f2044820005249070001031050380d00c20307122151010f0a464200003401c11101c02040030a0121311214030a0b00c00d0761001d411070310804a4a03d495100b544106042c044c0c3d080950300c0400a490020f1a051042c0104510705941c107000680500c0024201402c0044038480c0e00c60010f648203100800d8201d03064013240c034000c5141000010641d501c60b074001e0250803401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 793384073 1250 793382823 793382839
    0x111030403050a0b1b0f180102013e09031f021c05040b31080904020d05070f020f0c040b0117040303020c15060d170d0513020a05010c0c14 61
    0x9841d0302d483c0c11a640001e541c0b0300b050200b406100850a04034030b014042c04040701d0319291600d100011a845030322501003051000981000b0180c0c403e401c010440903c440c40045103180f1189000c00e00100c0010f005007400600013600c032038a00729425249a001c0040c050302075060350105408003e150f156000704850b508115031034000007400310403806841550800285481d00e0302d080c122070400a0202d108946100c44070b85d0803008050818110080c070841d550702488100d10307200c0b80703500032031408603801030000c906c00d403034480315500032445501e035556460313107034881e0108c1a81c44001240d504605500700340952441401c0a8010b8061072030189071503601d00007001c00c000703075008050303c003280000c0d0000303943c0f030010100300032040d9910700703c60f0415582d0403d640000c402c40c2d00302100808030201d000c11480301e01450b00594400c0c1c1207500c02407200c0e150003c444041c039840702c0002ca10480d115040400c0e154030070180c0308005c0754032500d000040390a08202d090030400340140c45600c110b030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 793385323 1250 793384073 793384079
    0x1a0703180b04050108071b150b03011803080c040305100c0e03030a0804030807030b090402040e0a02090a050115110c012318041d0a030309020607020901060c02010201060e070c0201110304 82
    0x6040900c4010008a580c06488034100000146101d802600080401068511108003c1c0ba0760070f40c5040300d43d0240c0e0009400c0b40d0408000041c1c4241c400003035165107410040c0f0066420104c00307003a503a10035507908401d03603616002058070703024602000d01036510460302402c880d051a1701040098825052101c4090030110019286d07510845400000414013020b0004064100d0042d9402040900b010700095a055003c01c210a80040c0701038803a5890f11031181402d2818480141103a4014003004014034181034a41c000c0c0000307100c1c0c45c2080d21040d000c100c01d0b034401c1c00ca8850b000301070000380520b07201c41001112101001d001012058014010401c52a13503844020104181040034001ca0144000c0070001201d05030341c10108020a00070140c0807010740810150200340c0d041c200000d22000340c2c00800c61901916030001d420085c410008035030a6006008403069034801d134020f05c100e50311410780240d00041602c00340301061800061900640c01401950f00c0b106101003140d003082e035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 793386573 1250 793385323 793385357
    0x3090c0f24050406051e070b09030318010b06030402281712090a03030c0614010b04170c0f12150c030711070602060c1b07030602090310061a0703 64
    0x65254055010301901c04010740064040c0305003540e09a0450410a06040c90441c0c041c0013441000c08040304c40307000820b401c079105815402d40d017205030420000c4404c0d15040002e56520b500546039903075491070982d4141c4405005006050403a200600040e055407155428488510310440352980b03561081e00c1110030b07104180700c0b4130000f8441c05801c60f00744a80a042e0900b4000d4500312410020010800118641c4032901f1650803242c0c18070b050084c00c185401e000c1f00400303403240324001003003545000140614000e000b410a2340e9801c0800c041c5c018038070903016962819030102c41d40290044480c10300d00d2600c1e080300203452103080150340a6400c1c041d4080d604580031100c03181100307404230a10040a0307105484000014402e0010600d060030008040d41e5204000c000080001002500488601c10050200c446513504011a1003003a260319040000e0340100708180d02074402c40142904505981c0540c40841c0d40740c85207009036084080313803a5604ea100400650900c901039069241c645 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 793387823 1250 793386573 793386599
    0xc020d0605060f060906041e030602070b0a0506011d060a1404030b10080303011805131e02040f11070f05010219020606031c02031801270e0f041203090c 67
    0x140314603400503951030b0003410440d6650940c4000342c09050305101c0c12030b45840e90700c00c8805484400740c00c01e50740c802c82840b0041c05c2c416600003d08080c008105401004001d1003114081c0c41b01c070406210652740c1d2030045482d8080700388195000640d9504140484c180f0303400500c900e400c0d501e40100030040c03c0542e80090341c030650086411008a108110584420300012406003001c28007440c5107524020130800c400201c01641d00e00584d4600200c1c0b40300011000d14004107500010310300c00250300c5400034161514007002a4040d0b0b0130000b1f4262020074500c9031b9820815192030103410007120b030301c9900ca0f883c0303941001c45082d9402c00c070035103010071403c1a1a140717107102d40c0140312a207050002d050402140c10341d1584045a0700c602002103507000702c180c1c1c806901042950400790702030750049616040d80b921382020143d40780308054a60707900d0540d0f070b400c0d40c0e1411004a07003912481074034803403400700f118080c0110f09680f2100c0481c1d482500708501391409015000911500e41c5101642c032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 793389073 1250 793387823 793387849
    0x60f04060b07050c04090c090c1e080a0c09080316060b0303031006031107020f010c030306030b0a0905010e060105010509090406020d05070e030c03060c03011205100207051e060118020a0c02 83
    0x21180030842c80304210080100c4024a0b0f0261400c4c40b07101080d030f07948000f050490041901e1a51a0011701152a11032070b4040d0041c80c0e87c0d440d541200344000c1c4003070a181e4003600c5e402e40300c904003070795a034445025403820411186000001d61400050032030700301000c4081d4108448158031030b8210786441c0e80807c0598041c401c03403160b00e0516882c050000d804c80d00d51000c1440d510704140310f00750140e0344280815812035001c2c03c02c0c03c420034a900d01240282080c0d04020310300d001810900c0301801c443d5000d820424400e81c001c201d01d08554030f0181e5560b4091094038001001004420074034100b69549981091040e20098103042d007680895069440c11505940081d1000c40e03884c045180401031412081021b6002e058070b0f04040500b40a00d2005018100c0072001c40d150076010802e00f003001503030070250114115122a035618185440e15011003c82d24642c0480d10380c40d04400300030401c1d03412642308800b68080c4068180140e00a5048640041d007800411500000940c4174101032a4007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 793390323 1250 793389073 793389089
    0x1a0709180e07050414011d10050d02030c1201060819080306100c060f020909130c030605091e0a05070b120106030b04020405031e073014030412120c021305060f0406 72
    0x40c030b41c10801020901f0340740d0742241c0c0c21103400506200306100858450300541e101682c580e1020800c038000300f850450030a81003504590007403c403107081c40040d84410161014202038400ba000160810300c0740d030300360100c042c01c482c10800c00310b820740c98041d1341c1d004451f2036420070816066140c0c032560700b12060446016512a00017500f00113038600b8981d856480070401c01520391741c0c0340d41d0310384405903070745404020f00e0320b079031100403c500540c00c101107a409060b030000780b0305a003241c00403613482c0c042c1c44000300c0722407154000104003502804140d42c015551040740a0b1284e19007c0110058084404800d8100e503003004003044640307081c0a80346a0364580394010b010412000b9036185002059400440201c047c1c101a11110307582968114809008030300020600c00c403420108100741d880e00a4001600c00010f0005005c0b410f01d5519210600407028807012100c416010f6405581d8580700039400032710000d80d5220b81c6603561200e27410650250841e1200d503520004a0210b0759603404c4849 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 793391573 1250 793390323 793390361
    0x40902031b18071706180a0f0612050109060c051207050913051f050f0d0206130806130b06190e0411060c0708070b1602091803071a0709180e070504 65
    0x101e004130032290f00d801050654215070710b4840f584000018100240102c00600c2d10740ca1441242095a0040f00181a07030301169072408401e850402d008000c03a040031503041d82010301c40e0250600420554502103501c200d020120f03611080120340c540d104c0382203070758440141c141095108600784034480c8640136001181c0062514041500110781c3e0b02e0303001ca031290894840e000c1c0c140e1a214410b003107299045c0c0707100c0e4880c400403c4020b1130050030740000c100c6108603c10020b4005a102c543c220303960090016a501d03032912003e1000e0b0300310542e5503903844409a00c040042c04202151682d1260089004186079100c2c0da000420301e034402c0d407081006a009000600c00c641c01403000100a0100a488614044504078441c80c00a40c4003806845040c0140001e4202000c10b40c10001e03903010341d03003500e94803890361900101b41c50000000b41481e0107000006a083c0e1701807a00e46003900c03c40c8003d002c0102c925003e450240202100b5404207008100e80000c49032a280507a4500000e9180225 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 793392823 1250 793391573 793391597
    0x20909120403030c0b09120d0c1b0b011815210c0608090d0e0f04021608040b19020607020c190b0301122a090b0a0b1215040902031b1807 60
    0x41700d101000790400c4156008640000c850600c0d01d4207d039001d00c4094004910f2441d4a001555102d032410756082c3d07444440080b10003040041480c2505844400082c1a43c01000d41b840c10308448258030700e500c02c00d0043d0b40500c43c015004044070100352541c0c0f010391003c80170b0740e5100602c29482e405080031607020b00500c10307540e5042c0042d0146a0042c038045080b0184900007039400c110505041c1d003d20342c005648036007111004910029035420200f142d40c0c42d540c5040000350782c0e02850107007092030b42d40755182c82c0340f03407001c00c006019084a900600280705000200000d4202c0135030526020fa0340703107100003140194640510f00805403010ba40a040c403203400d103502049190004119103503101c1080e62450b10420808800f512100080007415041c440081004c0c4202a042071030003110200f10045032510001042c2d11406103e1101c0e1040100f05040c00103031b40001400940c10380115880720030a020020047c0440140100400641d898440c108015041c0558607080098a40c548031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 793394073 1250 793392823 793392833
    0x10903020106091b02061b0c19060c030e031c18440c0316050a02010f021603020d0f0f030c11100909022206050901080c070f020909120403030c 63
    0x2007141c1828080700f608004ca5440d00080d2038100c0140780c089040100f90101c40c040c4888401c0e10010003400040301d060049400009403201e00e000310440d042804c01400d03496144c800c0c01401e44403044a8011420b12400184556804078000481d44032a69141d003041d0049041c20900c01c00d26020300c5c422040501d078803460501c1c44900c12160208a003032035407a24640b24070700310354101d00405a13030410b0b03d0f030802d1140981103200354a518110f41d15180640c01c140000800d104142c50b2003600c0e40d0803044400101a600d40030041d080001484c05000200701500740041200781c00c0703204941d8501c801c489681c0310054441029001d800003894a00000c04001da060070050700810100d80e40c054203510040000c0500f802c5009910980d5004a8600007100c00003400c0540d940380701141140148d01d4120085c9036411000403a80094a0304011a25001c0003808407100c141e0415a0f61612103050740038003e54120140c003840403407040c10240d00c900c0b1980c0d805080590f2203030f502d001400a80e070410b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 793395323 1250 793394073 793394081
    0x130903110f030909040303061a09030120030a09020102010608190203060106020309030a060e2e140115081906030b010f05091905150405010e0708012403020d060801090302010609 78
    0xc90809a44007081c110150103000081c0e07144030104680400c0c255582d03103822000703015190710070340e01e006040c0c604c5c09560117007801822655100f40c00070440c3e0040d94003d1190107600307013900c002035141040820521030194101005050041c000400d055079070f0000c091410701200074000094000c05d1413001145024003240303004000c140700541c10b00203a03000080e1078140d0102c0c010111681c4081c040d1190609102d2141c1c282c40c0c48213548000034044d9000041428400002e07049a4070308406070845000500e102c03410f8880860b00c05082d201030003c01d42e800380e00a050194802c090040301d0000f2000e6000d42d0700507500c039152100142d4035120160b16440c81c0703500014441c0d42d40e842080220704403400c06043c9074000b4107000c2030b20748894490038840e10f0003000113500141014008199031802c441c4041c000c801d230742c0d0340c020320740ea0740d8002c501c450920500d08c906011440328400282842a0050b00c042801c107000081c007196510b45035401c4405010003240540d4507118104139101242c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 793396573 1250 793395323 793395347
    0x3030711032104060f0c080405240a090c0f09150b0304081e160807021813030f02010609141918060e0c03070f0e0709060f0c02010e130903 61
    0x207604008034480791504003840000b81c400c81d021240002014010f06070407080c060070010b00704010303250070340600900390003045078183e80601c1816108400d06075101014071501d1825107207901c1d1503d800d080c9001512000c0c4d4241d0301e1101c5148003040b8100d0085485000b0720800c0310005204407061803083c55070360150704c0448810300500c1008081403e1504442100ca441c02c21140c20391044181a891030203010a2444031740d071044040d1003000100070040182e10300071036020307111107401101c3d00314000f0b04540031541034588184d02c0c400207004080350b50314151240008954a03032034080d0101103d2481030510780c0c00c0b800341c09010100f00a98101a606492101e080c07000d4200414411840c1c0c1700035100402090741d07034100146460090201c400203400090039600140c1e80c0e415003950000c020300860034000c05003800300341b07520300420450088403510b84030b94501d00d080c050103480b2907810386026410300500e10081e8a4542d00c20f41d020240300e1f01500001400030003403e00400c058a204 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 793397823 1250 793396573 793396607
    0x403031a0607030509030f03130e100605090d11090c18040b0604171f140106030e060a0e03070b0424060e04170c03040b0d0b01230f0c0708030307 64
    0x240c551000c1c0d20740e207040354021505410f1599482480002180c034185a43c1c4200b525408049022003004289051440484401c008140b2035625000d40110070f800d031074460040490010440d264440c00d0050125003202c0c0200340c091841c0302d0000101d040004100e0b441440080f0006040028884c10400010510b50a840800a8804410116409100300c0c02548141d90480c0c0490307200c0901040400c01c0806012407584c000140030401d00d026004ca4062200f040000c03800118403184684105180103900300c0051400d0386845005100501200c42c000032140006c110600100f8a0021154081d601c01c2c0d0061014880b4401c1440d4040140a40c0c4100746060040411807142c0d001c50b219000340c3c0003034080390121281c40d10380d0707800d100f81b0101c1d59a5010226000401c41c0161004d40860b10113210309018180c0c00307c1c01100c3c0d42456100e11417000302c800003a801c1031b120790005401c900e500200402d28194201c1d030803c1c42d0480c076500c88001680b0000c10881040da0080020591305540 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 793399073 1250 793397823 793397861
    0x30a0515010801030222091b0501021b0915042901020c0307030602030604090c030303060e0114061806160b04140d020d0c1506030615082406040e070806040303 70
    0xc800003069402c06100180c42082c07072802412901c0d100320180c444000a880041200300c0c1507107040c140b12110443c1000c1c1c2c80ca0307004000100707035002041504941e68468180c038001d5104804001c034050002d409080c000700071151035503007620350340320300d400c0500c210244501c2041030387e03c0c00344d1b902c4140c01c1990464008540a40725501d001a00c201541e40c42180580c4a5891102103002407160401c05080544a10400000d054150303020303030141c0355800400b4031140c0e218040d00071500c3d5032512554000300c08009400c180551261017200c9848010149841e0075070940b107031200700419030800da4841e6548402e000c104501c0149516403842030700301410740091114006500c40981840c0d940600080111500070000c0b50380903190611684001000480e441e03050850080c01d0011180300c003009200808158035a0004440803841070321080c200302810085456100f0b114041c1c00c16421580b19084041244014800f00c009444181c000b00080d103400c2c00c0c01401c0d100c0a1208080e94889 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 793400323 1250 793399073 793399111
    0x8040b060a081917040e070207210807110405090c0a051c23032a0a02061603090b030106080f07050309060423010608030d060605180f0a080f03030a05 66
    0xc80c0b0303c0c00c1205a1082035201140da030414807020340e081035031048103c00009000c128168000041c0d80603458907403c4540d66070712510b400c074000900322190404521241c491b140010780b040001d00900344070741c50030118440b010300820207a40094803150090340000c01e12264a00784801d494004040450300c0404d141070003020b828107100c10362405001c6d031180c030143c90317034980d50741d482030202000500c116a0384244014942c0c3d415001d150b91240d03201c020700f4003441314010004510f400d03d030300100180c0c5416400030307d41c05184004c11040701444031060f00001c103600f5202c043d42c000c00054880620301c4c940300460210502d002880107050010501c14440d9921000400316401340d030040b40b4211444100c40103403000004103141d10300380c2d03080030804201d000000c000780810554208003404088c1d1100826540b90151504805602c0d6001410140c2ca16020300400d01901000c0d000c0506a51a04601800c00c0c107000e20038003d6034400401d000400107148070380caa012980d6181810b103550 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 793401573 1250 793400323 793400339
    0x1e0405011115060f030f0a060207020103060e160807030906020d0204080c09091b0d0b0711060601050f030a090f0c12021504081c0201020c0d0c050607090b0a030c0e0402040608040b060a 81
    0x21003d40760a01500030041000c00646042203002d011407083c03801c5506d074940d83d1070201c01a5018000c100c2c00242044000202000782c410503601403112030380d1001c00c40151840032220084014036040c20540c954040380003164040c402418411464000076a03520305140e403075880d059102609900505907401042860000071a074400311080525444c0042889400040c10400001501605216403030301032000c020340100d450040648400c003600d14540c2c40c1030055a00e4014803ca0540741e1750100005111030a00b0b5000f503c000740700303180d0f5007070514983c1c4030400109060b0308207142c10180c1814480c190300e058180c3c00c61904030100300d24034080c213100c02c06480e107e9012002c51a101072640c0d110b082c9000790142d485d07541301c1c40300b01e030381d0b2404e142402032460010302002d595a008140c0451030040c850031002050303450001c10389107048042071088000700f0b40751468004001c2c1e5580718101e10782d5280001d0004080c6552034113580c1c102414195507415000d4241485071026180410000c0c0d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 793402823 1250 793401573 793401613
    0x406050718030b2e03150b22050f06010c0b0408070803070f2d0c030e12030414042a02070803181309020f21100c0f02060603030904020f1e04050111 65
    0x2613005403021b400b0b20705085010b014003a0400410307445400e040c040016120801282c0000b0300c1179410510007529040c001718045c00040d07c0c1d035800241c1d0070b4035802c049010b14241030382040c0704090b50f078940002030301c42e204150801e880d601c0c001500e480c0b007090b44030341c42480c2c04038420001902080e079040028402c0000302455084c401408052165541030500420141c0d14101c03015220b0015024074105880c0c59900a0281b98203407910498072119134100707440f400c0a01080c4840d4826082c1c2030764030501c5104046103440085114541000c50101e400384050f011401d0144100718540710321a04108035800c60b90420b101d0a03182482c03190160351084c0c460b64290f14140c40c1c00c600c100318030f4a101d1603405228950342807482001c45e4501c0205103544150600040c3c1d66805080181041040b6140d81d010769038194954014005201145020780c000c2ca00340f00c41d0b90420f8a8281c07196080f500030b4001c45040180780c171004c20f003040f003541c02120920004000501904400e007e20403c40890 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 793404073 1250 793402823 793402829
    0xc090e0112120201090203070f1802040b0d110c030408150a0e0d200a260a05040b0d0209091005010210060e16090506121b0301030b0406050718030b2e 66
    0x402140602c801641c002c2d4000041143c01400b41c40ba42901c49940212980840c407550304040f9034001040380340320691090f501642c425001d90303490201000c00c4040a010030f0100003c4402c0100040e4058507400c20041c002081200c0142c4030600d00c20200e0a0344820060800088900303103540d040c100180841d954a02e2211402c5c40f0680048240b9003503243c2001d81c0302c4040d10700c2150300400a0041640c041740040e01c2c801c0082641090704800142e045c05181c5070400880c0d0140424000003140744007620103441071110040c02c00c0060320008240800982c0c4c40904c9205070703c0c05001c19613040c42144c0b4916003404043c0441490f081c015500000001c01c1c0003c4000c0c00402100d940d071040480e8001404028000b40d2210b00180240185420035034254000d00100d06d66060101c0001c0f0560341201e41228002425030784646a0b00045e080c0248001d081040c80f040c150300300b2482c004010013441c01380e501c2d0080c5242140c20b540d100c60401c407500e01802c2c8480b184a40c00b070340000f045400c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 793405323 1250 793404073 793404083
    0x3070e0411010309030e06120603190302060408030c09300115140d050d0f1101061404051f1202040b0f06070201050f1e0702030105151f020703080d0c090e0112 70
    0x1309405410111744680201a10030360282c00000d5641c868144005114080d410032402d81b0000c0f0400e58141c0c07800046181d00901682120340007a0104000901450340308015400c00ca1600440000023808640c07041c40d000c850042c40d07049880041e8940411400c9088cc0600070030030140d01505134021482076114458074600740709005041c61300c8108000c41d4903588402112040344c4c1c045005082c083c10140003e0000f884011a01400c9a0502600085400505907018a9002907041c80701070040180741500c640d41a03404504007400c5242490006c0003050200c440b2800300e44100710540f604035503500e100d070881004030b2141e5035802040b1a111070303090900c107660710701607400b40e981401403000840040b90318440c118110b6086030002c1541620840c001c101680c0c0d10181a0012000004401d400443d440d480440f0f03100c00507410003500c010fa00413502c0d416901d5448000582c03200c1a0181c1140d1108503206180781c202100d40d02400300310400c0a04c0f581000480b4819074040040036013 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 793406573 1250 793405323 793405331
    0x103021c03140409060608130804060c030c050d09090b06030f0a09030210090c030312050907030312090b01140907090812070303060e040b040c061107180b091503070e04110103 77
    0x10580100c078409219006418503d0300e40381c1d90490f40000704814800c0c01e01140982002980c0840c00b0083c5005069102807101e0410381480c204a944d403403021b8046080c041110710042c041481000704880d10449507556154940c00e01c243c00c03042d6010001094054070007407052015125509440350b501c0307104032a0000d820b405a080c1203103071041043c0d0f5002220304c0d0004900c1401800d0312404c3c1540d010752902642c0e450181e920034100c4408031aa98000d400c07222007440003902c51855480c1d01007045c4408241500a80c541144452083c1c0c8085803804106000c820217003041c000c101d502100c3c0e820b02080342450440c5840c1c0716001c0d420360300030000c1c2c00a410820180030380c1c07010024240c283c41d40314051030b0501e4a08029081a0f400780c41c4042c0003000062954800c07400c41e42500c0c4040d0241040b80e142c0081c5030030010f10740e42030b0182642c4900300101c260301c076601c1241c490400c06145a445403480c0c0140350500c5a2904202d840c00d28000070000400c2c11128052034900f020b1038006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 793407823 1250 793406573 793406629
    0x50a0605041b0e0f0607080406110c0d110108040c1505190905010804030e04090f031808010e19140303190b010302130302061c0e07050f03070806180f07180b09010302 73
    0x91918800d61b02c0080c89044045401303d21f1641c000481218920000100c40d4002001d0040158944030301c4070003010340110041e841d01552060000e103400c1442101d64103c0f00740c0356030b420520030361401c2c2d41c0300001c4d0300414108030641001e01e01c0d210385c40c0b8a0038220822410400000c0080900810141c1446041340440480361607075481001a19001a10046c10340754601d0010007081442c00100003035280a640441c000b4010f2140361020703041c00c0000c090492049040c41c03411307000b809040e56032031440f00e402c4104040c140b00840c442c1e41414011405041001d03050400c403100c42040b60b040600c14826544440c1614110b10140c9070111402615184903013000000e243c10800300e402e01c1d90800500c0041808005521001d40300b0445600854075400000c2c56504c107401d04ca128041d03449940400c51104000441280740c1760400261401e49c00f0710382c1c00510340b148952002c1001c0e010b1108800800c54144101042082c08861450155166400150348807c0c490700164030100600448 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 793409073 1250 793407823 793407829
    0x50d0b0106050c070306090f1103010605010207090b011710060f1e11010e3910230a020303010609080d1425050705030f03210c0904050a0605041b0e0f 66
    0x9500855201c075087c0b10000c1a482e150f26024202070085401e41d6017440d079580c0c1881d06014403400d4a8043c1d00a11215241c00e04580140c114070314914140721007503000003080500c00d903c592040807021020807902e032800c4070040c144945c080100b420014a0301d840c1c1c01501406503c8031040b0b925103481101403c918091034014900c02c00ca114091041d0610280342e04c2d9440c1e03c0c0c40880300c06602201d405680f002c01250a06c0700c0310030140e8403061a200f5541d03c0c030300503840ba0072408107410082c6411202c81c0d01d450050340c409604000035074000710040110590141082001e08004805090001c1d0702d40c01c05810301400580c00c40041001048007102145442c04c083c00f40c10003c003202c4083d10890420700d454018038002d00e030182c01803140d50911200c000040701c81c1c01100b84804014106808c210700a40e04015001c2c1d0300303400c1c0070850607600350b0b5a80200d5000d0b01c05c0800011301503240104000c100c41e04010704020007101105d282c1112508501c0080185405607071004001e1002c0b000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 793410323 1250 793409073 793409083
    0x5030115200609060402031b22060e0108030910170621120409050708041a0403020c06030a0c030b010e060d020f040306060303050c01060f0e01090e011d0d0801050d0b0106050c 77
    0x8a1266485200704015003d1400110035006500a506888559a950300f60b2850035290200072504100203501440746032007503140b502909440c0a03c005081d07070311600e0403429840c0c281d00c1000349500c0402c00c0411480d00c10886003001d001c40c14080d01e1201800f4088002803801030605100d944059100035a5200c814240c402041400d130684010b251503856080d555000f500031000154505000251018000c2e1180c60040750481703e000300034003285203e140042d60051080781180244a0300160704d8540300d002c1c40c011a0901d40c086842c1c1c5480100500303c2d0b0f80f2030403050401c065490303259842e464110440c0c160341d18411016070340c1c1c0800d84104d20584225030004180919091000092661003806400c49080040c000d200303240d075407800c100e01d00046018442400a00c1c400401010204c0d5019500d01850b100010031449120301180c813403d0641c500c6440300d60006030205155660040c0c14601404e01201d0304100316a181e2240740201d181401a00300317001c00001c02406003801005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 793411573 1250 793410323 793410377
    0x3020d0b09071205221e050706030515040c271205061605090a0b030910150602120708090f010216060e010905060c3007060501060f05030115 62
    0x8aa40c1a007020a40103005505a01e841d0f0f44044c503290209030511402c442102401800e00f01000481c2d56580711a80801c0c5214a114000e82203505400d000030403d000c010001c2487e034a000441c0c1c60b1040d20003904680342c07a03802e4401ca10703000cc41a251900b02102142032003a0b47e446500c2014407071203a1014041d03d400084842a0118068003041400075259104030031120b031440c1c079580740c40c0c07080c0c940f030040044003507105220700e100344801402c0c500516404a4820112800d0010040480003100c0b0003440d140d0750140c1c0c115013409810380420180303c130307250384080552801c180d9440d106424041c2d900d85074460203001c0d4003801c05a20070444582c442c0f00c00f0b010030712587e41c5d038000035045214000c1000c4c0400c0c4858400211031038100700780d030081a910000362095070641d004031035220950100c01c02c21186450358010b414802c0c0f401401c402c0f4800d0b440081c15504101c800707002e014900c030b22001085001c00060100540034001d504000f200c90800340042c0f00304601444041c41014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 793412823 1250 793411573 793411579
    0x2211e01080a020a0503060415020a0509130603140309150307110615091303020a060506010516080706150b040e0a020d0c0c0b06010503091b030a290f01030b0703020d0b 74
    0x4400401c01c50300214415010070710840d030102d612991403050544440d02140e000e041c60301c01c80032001290b0f0070382d0005c150032441842c2c06468030303150200141051500c105c40d01031a0781d88990902c10420705400748107131444034100650803d0074140010700041c0c0103050b080c04000e000305c041600342c0c0c081c400d09079141c8005c2003a03d01c4c920305550308040700c04441b00028071a04450f00456504039043d001d25020541590241014064944854025000c050612810030004000c164031a6600c419140c000c81e00c1a10016a541601d041006c00d48111121400150020301810420240030901f220200c401c244c000960554070404290000c0c050f03050480c9840b8140481111010b40c0f04841c10b20300303481280010460345a240044401c5e003c100c2d420304039507000c2500040d00c0c00e1041d4003910b48da1002822901001000c0c0d0310401440d17105a191b50405da0300c03115048603400500107440c0d001920705100745075589943c40f142454035003d480b00040c954000750b00c89240c0455000001c102d0700203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 793414073 1250 793412823 793412881
    0x31a01082e060f230d020619090510093201110106091505040507110303012d06021507140319140c0408100506090f0c070c080102040311040221 63
    0x70100750301100c04c022115564091a411101454a00840c140402540140c0702e0703420702c042e200710f0402500800005505000030f6800000d110740d118107001002400e5a039500312040d190400b5000e502c442030030b802082207141c1418500d19000b03400c040e0103040003407030016005d0786401400303801000303c1d420500450781807411126400060328203040c120b440580d0104103c1d562140101c81044002110810680003003004001803070307045e04051050820460903002d215003030b101d07042d202d5a055012502681100b40044400441109202d03404241307410120f87c0b0440d0409000b4582c40010b050381200c200002c5020b42c0a1980e500114406900c01060020340c14407489440303182e0018400c19000e44200c0000f02003420060140c2c5010b000060100132554030f074501c2e41c40301030070010200b02d8420303401d101c2d1030042100c0c0071021005242040c0010b9441d400c0d4140005180f0311140c8050096004101c0080300b110301c0c0e2400900400d420349040c0079900c5111000481d40601d0911038000003407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 793415323 1250 793414073 793414079
    0xc0c090501080c1302092817010603050111041203050f0d020a08040507090b1c08130e06030c010807080609060103020904060620150708100f031a01082e060f 69
    0x1801c80c1000c40210b5030300740c90601400c0c16005900c10301e010f0f5500408505400398001a001000d030303081c0c2d907c0080e52040581c6691315030104000e00c2581c1e00603130b0744401080040c01070078814089030340c9100828918050070254203007407250320244020104000003c0000301e43c3c045d0030a43e0402000303564255038070a00d01d0f03c010203c01c0152800e0342d250140325030020720181c26110b02060b590340980118100340520141e0039061114260079a920907040000c0d10301c2d019254100c130042c5c51556074062060a043c01858035204005011905000000050020058000356469401001222415102d40d10a00101c02902030078200070342182c104600410102e401c003800c66150b86a5540100a4003041540e05544c0d641064000c22100d0442d03001c10702892150548940c041450440c8941850f59a0655080f00f94180c0c01510b0341401d40c034a40391451003810702c80740103000010083c8125a410247c4042038801414683c00000030023554003070104c07441d008500104108070f581000155 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 793416573 1250 793415323 793415339
    0x2061e04030e0d05010c14160b06061b0601211a071e030204060e06071e0c0e0403030501030203010c090501090512011d06090f0a0804060c0f020307030302030c010b1c030c0c090501 79
    0x1140386d1884001c6010046400f402e6030940e003d9503400d02940d072140c0900d20454540904103c00907214981110081107016903244070400914060414040104501e6240081d5010311040e141901e241508624142d1804100e2101c90080300c0300d4201d280700a81c0d1200002038500000c550f14064480700d4a2402003481a01a03001c0e0044030065141c0d5007500c5070407810003996204d10700f4002d040007001c2603040442c0880741c3c041c00c00309101d050b108000036190382010030040d42c100d0381180080c2d1940010710440c10300b07003c0c0c484189810b041036428181002e00182034203c080c01518001d2441046d800b041003001d400c000e814030011002019135200c021b03240c1b5282d541c101d40394040e901c183e5080081e90745000540316003458003d5000c43c04e00341081001c40d00d0018120047c0c0d8a00e90701d400000141c0c0d800d1019400444c0729400659075029608140c07429248100b1020f1301c0b505007150119015005102e198a500f64903260000001c3d000c1d20b001c0c0c520116a400400d031030340ca004000b04000f1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 793417823 1250 793416573 793416581
    0x309120216060206010509010b03283207140918060f2e09081b01110106050a05060c0a0c2706050d11010201020f0a030b1002061e04030e0d0501 63
    0x1d504806458807803034031000140d903144400c1c03003180e80014000f4010041620780a0107160415480e1074001c0305400c18071910294007040c0951684010354400e80400c0030111049414050001d02c041009000d0b11b00b0001c1c8103403400100203006004020020412070203e107021a2100b40d40100115407100103150500131507401102d0103802001c24003554602482d10104005030005000c0318001801411041c0a918280f03458034a002d0005900d004102d82e5414800e0004140140c2c030b0218010030001c0004000c0e200e41110501540d1401c0d000b444203444200c16030b010b54409660309556114141440351414500c0240039000001005e408a0a1341c0121319424001104c01d02a000000000150704102c0d41c080c411994400807450200c0c0002d9500f01c8018480700050000500700903046a61148990201084800103030380e46421805500e002c4080d02800754062000742002d10b05042d040800c002c40e10400140d07401054001002c2503c0340c29800f04a4101500c0c80d0307107070038181c600903001e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793419073 1250 793417823 793417843
    0x52a0c01050705030907060e1f020f10020901230d0e07090506040b0117101a090310150314030c010c050d0b040c0207180b060304050706091509140103091202 69
    0x55400d000204803401d03c641c09582c024078410000e0f000032442d01d00c094030500158540940c0107107821141d10080030001030041070003055600030700b0002e5038800116061041d10704004601a00c14004200181d912500118610400c0701c90016100561031028115000380040c040c4080d04001c03401c071035031101107403101c11905a90802c0c860b0703031102010001500c803000d11590024071000c001045c008455101d041d0040e14241c2d402da640c2e41c451880101c1c02d2140e2003e03400241c1c0c009920b03001c2c1c0c102000b4100200c91610070070001120b040080c480710307141130300c0090950b100e0490040070a4000f4001c8030000c2c91520020490750070307440c0001e000c0c1e4114842a1030340c645010030b81325050825000d22100411580d01500c000750610410100b040e200034580641180d03a02c1020181e0385034800107501480c0a070300181000d0b40361003030007000444c00340c0064012500c00b0404021300f82e04084042c0644001510b1001c40340700d158012001080c0c1d03c070000d44201441118080829004a2091703c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 793420323 1250 793419073 793419097
    0x9010f0809061303030b1207050a0504050f01062d0e0f0301050702150a0902040915050714070809180a09060608070e0a0c020c0310020d0b0f0d06052a 66
    0x221009020103440800007101c440744240c100c4000a41c2082014185004031071282c20002100380c00440410a07001c04031025110b26400000305100078070700148071030004d010480701444203241850185c88821750611820007444690280e4809815020070000c44005060041c103806520502000300201d0300d0300d68181c015140e05842009a04044c022244034079040e400900c440ca015034103000702d401e4000c00011a0907074a81003003005a40f00d00074000310b60701400300d10210702d1040b40301000310f40c000340a0a06104150b4038044035440c14500340c9000341d0b000004940c856281d00007003098020301c0701141a0052804040003070040c402c2d40b01c10607860080f1000c105043c0c03154042c69070b48040d80200440306800b40c002035101c0e0419041604042c2c410300c16038200c542d595010a1900d084a019040c1d042e4000c60180203061183c4030b1002003242c01c0fa21f800484018202040085103411800381c202600d07400000c80e45101c1040305400e0182a802003030314410010030811f120f1f0460169840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 793421573 1250 793420323 793420337
    0x605010e010f05011b02120f0a1104050609010b090103061d07021006060e090c0904020714061b03060915120a0c0f0e1f0b27010216090c03060305030f0901 68
    0xb807040c01d0b80071004143d450684840002c05218000c462100c221054201d070312024440010003d4803050090740d150b004084000d1500c5030703007860322480782038642240c40d020380e240c8401c011484d50340400e83d40c1103c8440d0030403036a0b0140800100e0161030326422800950300003903122041d00f0041c04c8014070400f0680e090768510704448240b0010b4039400d03c40c4200288076001c5007202890a081002e80200a1000c840d2410450b4004201a6001124244c3e001716014610038a0b100041c0300440e8000d51140000003e60510040078440d400050f0071140140c004500082a0181c180d43c20340d0401001022003514103504802a85d40f0f54000400b1134011400d4000040d00c10030f881c080340162011451101a195078410300781076180c2118054a01d180f8402a002032607a20714001401d1110007141d80c1c4042212034801050030f0f401d01306400d81158090020541c004a0325800c00003580c030440e402144401c41d0850071070150045400107026400002140d8054606940050901d08400c0e00c0f108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 793422823 1250 793421573 793421579
    0x507120c0b060306151917150906040f12020c0415150801051003090503070f06020409110703080402040b0328030801060f0f391515031103030c03070605010e01 70
    0x541c4480c4143e0359005819078102000c01c240c6800280440051b88442c400c1c2005590381030b410070410500a01c0c0200c030f820803004070f10070071009107032641d004078505d000f010282040ea90701b401c0000c2e80c40000c5e00100c1401d5500c0b80e00c0e0320034021031030744220040c000c0c4a84048070743d420740c01c030100c0d00c21800d044030020001d9408030f002d000480d0481e9002414086010307030511043c0c010f0a641030044446e4001001000000b81c00b18800b42c0c50769008810041c0c07141d0a0084480444030402c040703250340381c8203025140000b588440c2c079503809541550003244981143c00071914001c103201d1055000800192020b031011000e02c84803410034081d07911a030543e40c2c1c0d00401e81e015840c036544070001410300011080c0d0b0314020081a80700004070b0809000c6460400f03601410891280783d10070038845c4035060841408056140780c02d5081c2038000800c54a428a00c10041909961100400c0c2d080081003242c0e041c1d070f0a1040c1c0340c0882411060b02e94541c160701e0500001c11090043c802d040c0c0e2500c0000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 793424073 1250 793422823 793422829
    0x2060906091b0f1f1e030e03071b090905010f1b09121b1d070f050d091a1303030c0221031008030a0f030b19150507120c0b06 55
    0xb603100800c1c800030308010382e07104105124804181180c095001264032000121400400562580100941e5941181010b80d0b50800e0088919000d9090030142007600350a8849008000c44002d88c1d4000305002016204c03110f00b5400021030f5005c0000301c0d02e0024a9001c0c410306410400c641008040c1c100441c40d801d0f0078000c5000c80341c440c100c0000300c89030706c1404890200c505c0307ca0018000c000400880c0f180101020072550f080d0421680d20161000405411003098a4160028180e0400e0005450310120007042030150072402000680c03203241010501c0301c40c40c2014010a65152400c0300303861f048603000d9215411480c101d001a280000c030924043c4041030005800000004000c80c5001480012200c1d8001400340300078482c40500c00202008100018880c0c0304140e00c4060101070714860160444d1540d40c8a14050840c000010540140d0050701e041592600131101c00b11111000301211039005020000b080c0a0106000e00c003056004402c1e0030394940300b2000e02c0c155a40704024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 793425323 1250 793424073 793424083
    0x90606121502030f07050a030906110a02100c1b060603060f0b0306090601051f11151807030507060311070f05060609130b04060b0d06141008210d020706020a0206090609 74
    0x744c2c06020010002007901c0c0da20400c01040794002500d400701c0c0300100c948404040b50b5620014540746400040c81400254051041c0c04070749001300e10401024140700d90141132400450240d0101c110111a0001080829404940a9034000b4010403074034001046a038006c00e40040e1803440381c4a101e0006252000001d00b10341a075102801c1142850401040c8003049010100034600740441c100c0c0380b0103540801c016074550080090064449410158404049050100c2000e01150440a001e0021901c00a86001207030b41701d103000100c103070b0002070000150041520003080088040d091000384480020f2240c0030f03080c101c9030400a03881e030305003a4405030130390a00203084003c2000040d003c900c2c1503101e8421580c0c040c040c42400a40303940d0720f50840300c0d4042c40c0c4070b0f414901c174113200058080302c43c5000030f0542c8800901e80c01c6202c10410005128106800e6004c0400042080f440c14254043e2803907150300a10954032a002c50074040e454000417151074605118810001d607802c00d000030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 793426573 1250 793425323 793425331
    0x110a0908031c02071505190e19171c150b07031b02010509041503110f03060f060406030c06030b01030c1e110102070506010305061501020d200109060612150203 70
    0x4100034080b48001020700107508a0681990b42117903d18180e0080c070174030b02903948101c03401c00128440064408500b001c4481201e15014980c0c025050f00744070b01030b0b051400700c0d0603030844041030004204801d0122544100141d18064036044c0b050800100450f03000300c03c18440c02040403017601d86640d44109580695007020b0001850540c80e00c1d8800c580c1505140c40e1401031400d9460700c4444000300d401c4e9030b410f40c0182034444030420100700b4004681d9001c01d0304102250181d000040c0d0500003035031b075080500346d103400811120210300583da80d60302400c021648a001441c1035583e80201800400041c4940c0b808039041c80b0f189070001d0710440030000c6d0320305089050316000c0420803084a41c09a80344010000c1e41d0701b0082d0901040007040f615000754030070070040c102403900c0381b074542c406032007150010b041d94444040c8140480c1c000b01400c8200e00c2d007900c1c0340c01c03002580c0800c41c054002410003502c0c0307625064001c50840d86c01c00010700307224002c51005e07000440c265801c1c0100d2000721 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 793427823 1250 793426573 793426597
    0x2030f070330050901051602031e010e0606031e250312080907060e060d150303020708030a050a0305070c0b04061a1206061c05030a08010515090d1b09110a090803 71
    0x25484c120360154001c1c121442c1c420341041c0101c0d4240e40464500408003200510300c41c1d40c0103e0441c00a424000c5d2980ca108103005484a420001c01080d07942d0b0001018205840e90b070410070701000000c02142a00308143c110350500002c400d91140d580040d09d0000303450000b40106802030391070144901c03034081e402980080003458946441103c02180c0307103d150303500030340410a90244198030302441c6846440280c006903080d241d4a4064039000d1258081101501b060104d9010300b6000003d403580090f40e414003081d242e8440c4c02c1282c055500240080400684900748007e202050703110705843c1c0f101011040d4410000001c001c075242e0f90300708056895003c00f0010700113052501510040072606801400e05401ea550341c80e0441e001103414000040d908001000070307244c071900d14000c01018161007440d081232840828031b080095100900350000c840300000c42e0f008503501100007010051010050305d5604403020710503a002220307602c005049100c01190035a030110444021454036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 793429073 1250 793427823 793427827
    0x1060f0e0f180a0f0f020c15071b02010c02030109110418240902030f0d08153007062f0316050a020603010b030a111806030402030f07033005 62
    0x1d8074081d8100c0000604440043d92a280d40c11038084107401005c1d24180138070000750b1a158800d041c54038107071810f802503090070000814000f4803078000d995002c030740145d1100c0300c03035280f01400141d0b13102914120081d050342c6441a441d0034005400f451981042048405004015200d150003e1148013510085c09a524a030200c1c0419849641c00d1012110100d4000c51740d520142c001070304280c14042d8010700d070380021142e00c8005900803245540040c4182500311241400c1c00403800310311318110801140c02c80885000004161480030580102c241804c070386880740c503044001e005404403016807544245d6541020101c02c2400c00040c04121403800841c14503001060208214141c0070080d01d060044408001c0540c03242401176010f811624216a601d040c6140d203401110080040142c4840b030a21002414108403c2c01c03503038140c030844080d520303500c483c00003e04010040384500e0aa02c202c540010800420003041c01007841082c8600030041e480114000d000401d0204100c005201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 793430323 1250 793429073 793429099
    0x712020102042d0e18010e0304030c0b0705100f020a0207050f09042307030c210b07030c0504090509010903020d020a022419120b06070206090603180601060f0e0f 71
    0x2a501824188202c0380140c019541d520b80091340d2403001078071484089001a00a262074000034041c050204600708002c5141c54556141d500c0000031354024240d500720001100f20a00000b004480030a0b042c1303400030010000844041c00c003d521510020b0094041c5000c0043e05240455000010103400780c28840190b44070b59402408894003860f10381c0466180381c8490491508104040103140304020351081d5509158001009020241c2804032908500582100140c2040e1250303030420900e060100b20b40150746826030799800b6076004404c04514100070040240815004040e082d80250241e44003c054503004070307212220b4020183d08800703d01c8444109a00c030720a800078425803161450f0520190801c1030302640308a1403090000b60f030800c11089200158804d4030320840003160300f40d00d07120300e03030340480c07481d018101c62148500c0e00400020801d5042c4504030003d40e9000041d00c10540e103401001e0302e41c1003054200c01c0015990490404d050502120410744c09600520101882407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 793431573 1250 793430323 793430369
    0x71418030601080c031216110a031a040b01080c031b012102041d0f010501081e07020706120905061303140304050d03050a0b010c06050c1303030e03010e0102090d030e0105041a071202010204 83
    0x40c80c8e130141900306466840c0040400d0700000000f4401407025480c2041c2d04040c1480c004401d810380000c10150441c0c0748a0806590004511428054140042034a025032000507100c01d041003e000202ca850f8000085009680354002c005580c414100c2d0001078650f04401c03e80408200c4445954004600051041d98021400c01c0d5200115400c0b0410000c040d014000c920801a1410009a40702050602c42181c105481e40244540d1840400c030306106034454556902000c0c150900880c038185038001803510503203031425040f1555004641d03900345441c1c80c6990711080048440000d1030700001c2454400c0d103011307000306408140d40c0c0880007110380d1203a0f030003400c0192040c1c080c0b402c02c2240e07d83d1440020310800c011802030311504820103041c4240360944090410b40300d0541d10400404416a0302c610709480c3c4a23415140c1280c03e0b0150b400180c038584100e0700208540d081c41090340100b281000014a5401e00c2903915966842c07850b10183e00703034021406040c50310407600300e8083c0c00c04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 793432823 1250 793431573 793431593
    0xd0c030903110301020d0e0c24070b100b07050304080610051e01030608011a360403020703080d0c020c0409080319090b07020102031e071418030601080c031216 70
    0x240b0001c00061600d03542901c101c080301d80c9003000c000315070040d001c80d10700c515266000300f9503c030703115402e11402840182014018400e900c0024500b4100c040400c0640400301d0f0004050103100040a5548179070741030490345d0f070704544030300c042910074800082c4514614030102421030310f01504103951540d00c02d942035041d10240c41001d0416035a0ba1000074440c000b40261918007071070700031800d0740b03400810038002914881140351940ea1401c207492803600c000c1000d10000ca03d40c00c0080d1040b500c851034228200560b80d4006001088007149030001c40c240e99100b0000080c0d1a001c50b01e802050368180001c1d00c0c0d01a40c064190501480041c003400541030070f00c0c044000020380004d081204d6510319200020548204006030340c003000b040b022000d074941c0c0e001c0d0341c04440d10004151034230714001014000101d01840c016403001c21007041106001c54510000400101580c490b9a100c011003950b82440f4a4698070a00c105016645002c1d1f01c0c0c4120713480018201030b00302018600d0740b900d804403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 793434073 1250 793432823 793432853
    0x51b09070e01050903010f0b0301061403071412030414090f1e06060909241918061203082523040503121c050c0d050a0615050c0d0c030903 61
    0x4040e003013201d601c0641d400e100b240b041d0101e004002540c01c070000c0c241400c554498000d4042d01010121441c200d82e00007131480222041c2850b6140002400d0003ca00315032121000040d841c807020a02080144050070030342944207081e9945405643c0d010200034040d1010303501c2c1e0010010350b461000324050080e000030f50200014110781c2c1750840400c04a00400c40481e419424216050310990004801c1d2020701240e481c125121640103042c40c061041301c0d01244a107000003d03018041740c44600d416001040184018800712440840c20705000d80311140c1102c41c2400220300c1640301d40b18400f4400306852516172503880c0307225031500c1c04481d1690007243c040301009001c1404001001d0f0380400c50802d10b1040d81440b15190303218005601e05409455445806540c204400c1041c8404c00c44141c48102a40140106880d1a45040e040003004d464001c440402074442404d203c094000d0003c1c000c01422008994103c01003100444101c1140c1e0402030000d102000d040001c1a00c2e04844041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 793435323 1250 793434073 793434077
    0x118110909070c111e03010b040b0105030a0209180405030d05070908071e091b02010c0e1c060b1f0813021011070803041203110105060109090e0304030803070c051b09070e01 76
    0x140c002d102e000201030013401c00405d02c2108011500702c50a04080c02070122200003918140b1a10341103100180103800010589003049a000c68034200e40d6071410401c070361925508402120a00309414841d840e13610400342041178a003030401203815070348240c3c51042154051005000c41a041010714001c00341e821444544aa085203400300e0031400c1231150707401513070307101050803109492800040d080d00c0002c401c1c8410f100a15909540c107031076602d541d01c54000c0c030300205e1765000c0440ca031010081c01c00400454100040708414828019009036a240c3c100040c1c59450080d0350b020004040a10281c4009400210034140452050b0240426032508183c120a4502c0f807611020310f1841c541080e0300200208411307429038001e242d042000f21000301c41280092140c2d02c1e00e800040c01e10b185612a56484940d144803241075084140240c9005e10361186030b0035580d04103104010a600c0411105541d9030017204da01411305000d240c11103000c182d0183c07585c1c0c0c00750344881003540d40301c400d001c02c641 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 793436573 1250 793435323 793435343
    0x6110a0f0f2c0f09040b07142101052d0402030901150602010605010909061409220302330c18090f0105090c0403170d060509090604060b030304180902010c0b0118110909070c 76
    0x9c0300c6c8945040025000c0d00c005030a86003585808104a00308a8242010401000420790034200341c407c1e0000d098181c80c240c0340940e07261a042e80c51801403125094400c04c9900078580883c1c22941074019208494090f82c038048800d44856034a003c40d41c1d1446007880d5044454000f440798145040d0090b44241d900724851a030b0072145170241c404e0400000101d0040e0020900617510180f00741010a600d070314010000b00400811403001e156807000780aa42096901203825405504030404010a904010305259100d0521851540202c1c100703005403442460440001624088108c060b00d003100e4002c403502c2e00c0c24014100c108010381c010031307010350142d40303500d000f1a0720345554004600038801da40c0108100c0c50036083c40000c842c502580c5c948641c204101c10801840c2000c040d411380401c0a500081003c01440161908403101c1401016208403100005015503683c000c182d000c0245201804541032100264042e480707900a40703544040f0060100c0e02c06842500c10443e16889013000c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 793437823 1250 793436573 793436587
    0x121b100f021023010f030b24090a06091103061e01120209031612020f0306161116030f03120c0503010b2a030706110a0f0f2c0f09040b0714 61
    0x550f800100340c010001e45021000d003001000705003118035901501d0600350704d506158a583c2c6401c00540351744000d00c9803a052011851480e20b80d4400d500800d450f12040000c2c1420b610000c250390001c5840d18815407a180000c40c0e0118643c210884000050355070750740400d40b482003140250403259007650540b18074001003080c100c0c51041c860103041040e00e0360f010052a0b10400808072078810841d40603802000030b0041409070f140b4004002000d40c208903420640040d0381e249010903020141c0c1c409000100d000040c0400d480d0020025130081e9502801107809030400d6042d00d0007500c5600001d0406c04c0100019512039002c1c0108112144000c140c210400e00034800b01040120300300e00607000041e0500411400307115040480044110090804d03c545402810b04000c00740000148070001e1000c0f840203101e00e01d910f0240812904803000c000111004203e0442805200c60007030650091103010b0b13240944001d4030840d4402e0342002c280da514101202c456000390030281200710240410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 793439073 1250 793437823 793437881
    0x8190606150c020f0f240705070b040303020f0613060c03020d0908300703020c1519050106030207020307060311070f051005010b12060d02121b100f0210 67
    0x100340d014406554296000b000c5004201002c1e244c240c1c082c1c030907212100030700386075191039103a24040710b03000071413510079000e40305540d02074410303107030000c0039802201804200201070402400583c0e000383d00b00c4904076512070f031050340c9100a94084100881300111000040c000b600b007580b4418161401605141c0305006043c103850104030300b10303581c003800300310400c0342c1d118050707540c8031500c12151040315035118640803064410040c10744e404040d000902410700010400c040d00c3c001c0381c050707030f48142490113007100d80c0e408050402040b0507600305800010304c28806d000b41d0b01003070b40090203002c0c03043c5010800d070000c15280401d500640020f00040004c1482404000705445c01800681802c6411142d0340c2c045400580025407200341c18050b000f08110b20318103a0782c2c03004007034840f006514450700006400c487c284a4050319803140c01c9202d4880980000b403450781d194241d6550450340c00c844001e81c1c1d8003801401400c01640504000c48100340140c0004034051511029050046100560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 793440323 1250 793439073 793439099
    0x907031e060e0601030302241f0f090b091e07110f0f0109120c03091a0f1803060615070b0a0b0a1d1e01060e0f0a15120608190606 57
    0x90b251504041e004000b4035805211411183d10b4429a114a000c64102c1d010a0040064281440352940800307031645049080c0408003e0010882108980c5a60b14802d00c0508650246da5004e4105d0f40e0104542000380c0c418114480094107150009680788981204c41c4040c00f01c40f00070a21984418951081c0244280c5c14015204000031600c10714509001203541040c0750184204204480c0030b1001c241e0249082081d41e810705a00c1100300301c10030003800140640c4081141000300000c6007500340d041c0f07420401072404180c0985480d07a80b02c50130071610f22034244031000d0b0302000300404c20005010368042c0b548080124000589405403101240c440141c60f040310003020003490340010310f0542c1000d2154024040ea0b22103d1041c1c002203440580e01062294100340710003514041d409a0b960749107419070350406420011a15600d2010b004c00c10032545010004c2030509003038131942244d034060f170001d5030b468100801101e01c03013a4441100000d201000d50314113950342004102d00c07010b21a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 793441573 1250 793440323 793440341
    0x90f06061d010b0903070b0c0309130f050603012d0621170405010906140d050411041404050c10050c010903030204060306090903120c0e030a060c03140907031e06 71
    0x75055030341e1000c0c10304180d103090040c0c2000660300c9003485503540d40e80d80024640180c0f8144101903494000703103288a842c502071945200d501614140604805e500258400b824140402d1000d100c41e45402c0185400c03101e070311000040030340300010280070318003c2c1c1060070100108a10006a4240e03210482c0c03041c542031101801620000715140340030300010459250072600c005929901d01494400040d01c1020381d885180306003d5080800c00c0c0e490300e004c045d0f460050508600380124035003442c01101500b0507003100c0d88920b10380006020100d21408a403032144d0340c0003005041d08400c030400c0098211286006004205042103c4504001d00b8014036401d40d10a8034096182c500303064001e030940392a5001400303a00d06d011142c2c004607920910030a403103110a2800168481c1d040000c641003502480050740500c01d100e8050100f00c015441085400c603d0f50b01042200703240c400071160242d0541300705101e03a004c04000d0000c1800b01400301041c1084110345a11440b40d6914007003610b032010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 793442823 1250 793441573 793441589
    0x1142505030903061f03261b011505090c0c0111070c0509010501050c031b10022b0b130c02011524050f1824070c1409040204090f0606 59
    0x2c034001c00a410100020350708400c0090300071003045581c19060940182620000d4020300790382c10300c07240401c000301c40388001c10b04007003031a565121005894036020800c48164200744d86403241110121a0b40c0d1351010a0b250010100407654aa6840d03100454000c00014066950b0300c0404401501c00400184101849100c034003641601d00810410714200580c08281840f0040007a900002004012141101c8000d2490415494086c0f10305141252095400021910000d48541568240e60011f543c8038254113118858000a840450507100004030b0250084402d10380381c07844580b076800c103451001c5188000a4840c0112107681018680355010150380f813403085940400c801070320000c0a90703164500303142d49001c14940c00b9081d6441916424007003104c201d40c00301c519944240003940340d200c8400300c0800d184610440c9441c0c41e8015501140c05110050000a01007000f03c0e2280c4100700041c407050030341e03940390240703c00b410074410201e9506007102c01890011b2150b20501000d41924 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 793444073 1250 793442823 793442827
    0xa1809022122080c0705090c1e0a17090114100e061806010e0105130f060f020a080901030b011e020718060812130b1207120b0114250503 60
    0x460039601e01000150000704802c48181119903281c940c0340c5440c1200b60300a032882d603601204400181408456040a03a10140a5090204110600001e442c0350f40c043c0702002c800c000340000e251a584903004103103012448504a034590700c0fa501aa590b400301c03100c0004603103a41da19000f108491000c1b2801180c85448090603c0040d5003d602c1d40c0c0e200c0000d9641e5050240c502e00c8a04034074400030505030400115000d00180d0364402c0302565002060200714491050726506c0342140d08481d40111000107440c801c814614178400038007030322500d810030300c3d8a103085c00081c0110b002e0600051590b05018116180715401082c171400e5032203409c59940030f04145800d000e10054540843c140030b400e014241001807012480c08070f040004034003150140c039590308801e00307603802445184d40240000b84010030748002c2004c40c5080d443c880c500360b0785c5141c04480201d200c14100c62120b01401d0004421005400c0d130a03000000a00c40313068420a260100510f041b14080841540c0c40211200c0e080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 793445323 1250 793444073 793444117
    0x5210903100f1a032e23010801090b19110c0304080607140a1b12020a051b06160f08070b040215031e090c060d150f03021807030227090f06060a180902 66
    0x6d40c0100902625040e002805131030500d4440308030310600548009075945064900f40c5581140d903000c60200c00301c0026440e116031518141d81d07100d4000f071282d0100c9000e0715002802c0684078100940d000c40c81d000c049410308181400413680d440d44000e41d40c04441c007220b070300c03404140201030300340c0c079191aa4010000004503142a905211185c0440c25049407075400319420366072003400740c40b004600c000100880c80c5090400c600e601078444800380c0070300e03400074901060011290006114600a5944101c500a041075200f607070320007203900c120801100c0c01e8403c00b60301039810131038008a41ca012140c0706030000001400c40c0d4804070b1300c0c505107139650003402503c42100140c0b0b4020084458a10f0300d06285801044645841e082c00004a00304400010003d6001358141c070313600c1210a00441d025400c4201c0b05081410340d034045841a502c03040001c810900c9200c0040c851a8050285130801c4000c5d181503e80c140d41d2030480c8084444001d010400e640c5074406003048844042c104038031804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 793446573 1250 793445323 793445381
    0x7020d141c05090f060d0b0409080a0e0919090309090c020705040608010207020102030307050a05040801020403120201050f280f050907030c0608010305210903100f1a032e 75
    0x1c0c030300d84180481030003996000c0d0384400045081c12030a8904a50710807001a008005102a40c1d02541c840c0c42c005404090111030000b800e200c0555490b407206005100041280785202194440f400c0160700c454005500b100b9040f85c4c030704500c02e013030003180346881b51284001c2d85d2000c00650010781c0101d504000c549080d014034001000210000c40c5441e4091700000c0d01d91000401100a0100006808100a00c01c0c0100c80c01880c49500854942d0380b2850901801d010746640c1c0401582800081f5041000d802d0495004040480c0d10060741d020047c01701101c0d003511120140c4456a820303692503034a4441c00391503c01e00a00d006071039803d00f18680882010115006075040104c0080188002100000c080c640c60881c9843e1082001426406615134407030100455014018150700704480007094021a4494480120502c0280d40e02401c4da0350750308091070b01d103078943d108907103c01d00403080e001084940b010514401104c00e299040710b60a50302c0000c0b58040301c6e0600300c11210511 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 793447823 1250 793446573 793446613
    0xd02070203150604061a070305030613020a020d0e040510140d020d14061602030d0f06120c1a09150a020f0d0c02031608030d24060e0f0a06120207020d14 67
    0x2003440048540324224401c00c640b21b81c020a5001014401c00001145050303550080c0c15000903030960007556500e002e068001e40b00e005840718800480c1c4003604640041c07034075006451041300c0c1c050709050311a00d03000046003041d00c10303004150800910342185026880d0000c1c1c08034000c2c01190005042c20902c078040340792000040c460080d10020f00313a00400c040d4040100c1c0d0340c00030b17004c40108221081038118030082940d85e0001e440d8001d0291000100442c00f01c41d00110360a00102000018510101c00041e100d0602c181e45d0054031241c10007603411000c409403840f025a40b0447d000284040a210300c1c00d880c001d00c8001080984180104519081185564210388801c0351407405203003284d0260381c0d0154400c6443e800384c56240040c550900c2c000d0558500c010720140b002d0301550f418014002c81484610140034110101220705181040b2070301e0720444800796140d900200318010904020342001c682241d000390343c090540007152040140c04c0380b100c04080500700d802019100c2039110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 793449073 1250 793447823 793447829
    0x1509080d0f050f0109180b090705220b12070501032003040302071403281b060905010201060e06030613080915120a05060319050102040e010603090201020d0801030b0c0d0207020315060406 82
    0xc00e040400001070306105080351b0240552144105d21103888410001c2c0c03e001d102c0e00000d400034460340c00c680b403414000d9035100d10b02d0a001000c02210a03003078140f182c50700002200030141d40c080013041007070703502c03d1b400100382440001c4110444019442150810352081d90240d005038001c000c140310b40d42000c0b019880c4550f0490040000070003049048240306c24000ba00c0310031384441084101401030419490300001c441c1d40142c2101902e4003009007003810203009081c0190701e4000003085080c0b0400440d801182d00400414450361405000340e40c80d00443c3c3e003180c5900d028850840341d5100c1000307081f1102102011261a04039200c00c425490303034000d000a004500741400d0000e40c0e10007090303800784441e144d000402091078a0a00304d001e03205030340c000300300c90a00800005d0307465416849009032610036401ea40c0503072aa8501264110f03400e010150070b02c0c1d4040d0200f1441c030150801040b083c0c2d5580c1000d410001c2c1600000d05084690300e2941000319403400f0811207161620902c005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 793450323 1250 793449073 793449089
    0x171516051e07120e0a03060209190f0f1a040b0702120708061510090b0904060e0c0910080907050d0f0618020f0d03020c0409020406030c18060506071509080d0f050f01 73
    0xb80502c5000081d00941c17031840040c05580c0d000035001055250300c1002c0280e500c417403403410a540d070f40340380704841340015104a05101d202254003044862441c1c0310520480b42c249060b5003000d060a150800c0380c0e00c1203030126400410707007030462909481802031100520320303500907000a24241440f000f4400150620390b11415040d28001d880a80020542080d900b041080603166691200810000c041b142c0280030711907800c40030080a81510f4008283e8541e050783c0c40941c11140100a84500704180c948501c03507041b250041c401402c0c08a00010035901801400710000e050791922011a2a41000a88829610200c10081d42014111590481001c1c1d84100804c04a41c03002500c0321890300709180715503101c046900a5683c0d982104010310340001810b01c070581e0b01c0c8144040d480c0c4000b83c5404460a10720001201d00d130442c10303291a60740008105d040e045c0022288401401c04010442d5080ba003481201200f40d80c42c07080c0d50409090076000a6282000d0705030b4120b1003030503444101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 793451573 1250 793450323 793450337
    0x3030c0a050f0105070f1e11012c0304050121060b041401030617030904180506070819050c120a1118011b0c05060f0f07060204171516051e0712 63
    0x19032988000714542816400035444c140000d000002c8504c03100481620559602b8102d00c2640402c0e504009115001c2d408113078034010031401601c50301ca001d5441001d000c43e0f42c3c058081510a00300f01c02c010701a681c80000140e44d92618400d0f450341c1c0054000b11840180744400185558141c0301d1100645030b1400361002841c1c030030031171079920310a80c031110303004a8030317050400c00846044420340121980407050780c02601d81000003c2c581c000c22601001c0d0170742480c80441100b44039201d054041c580c400302662038102d2207459004c8440740a408245119a110550105000700740007610820361500c1c0c81a0740e10f55071400040001110440000c1d000840707520303480014504007902c00490308240c40740c40e00ca16202002c1d250034021074400e03a4104200207482001c0103c42e42c010720541e000015040315101d0810350381603031784031003160380300c008654030012401c10400c41c0e0040a40c0c1c0150300d07182d4a00030b0300e180300086801c0c600d4000088403802090003410083c4a0052410040040ca484c1c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 793452823 1250 793451573 793451597
    0x80703060b0910050c0d020102030717070e01200604080309012d0b0a0305070b04230d110f061308120c0a020d03030b060318120c1b03030c0a050f010507 67
    0x1c2540705486619200c0c120010440c16014050340581d11600d40803c140c40c44504024030180c083d502c100c800300d000030410a00c400c1c42c000071001c451700030b25196481c00c040214500c0150307800506d01001192210000036299900d803020041ca603c200c3c07061803850f80303a00b0315800c00e5081d105500c2280080c9041c040c01c69441d441092135000d10005020303808213140704080701207000c84840d40c0019119010740329000c80c82c101440010007c89520320481c80c03a424011038101d4550540d10603c03507001880003042400b1400603284032076050070081c00380c0c500000c043d0002d001039011200840c409410041d0030840140180b00c01180340c1c45c60b0312400e181104003403829440d07480e040300083c07151072410f4070385040c94441da000090808000d080140e5038148880e50041d240c2000103110310078031230244585070101104050780c550040040c01000c41c0040010107a450040708049590940310030302007961001c204001406440740600c2c0035107070070015515500c0c25610010311038001c3c01a10341e015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 793454073 1250 793452823 793452839
    0x7051f09020f0d021203030a05090c0d050c040b1201020d0e1c0f1107050d1b050a0f09050604020c0d180b0901121a04020a0e031b060a080a0905010204090c08070306 72
    0x11104450085803007403a410b0f00c900c0021003505881c151010141300100030030120421035030286009441c3c020848000000748410401c030900040750040140d041001900e01c5400c00703030400020188002c040f502034503248003060f42242c1002c4c080c0300816494a0300d004242d0014840001800c40011403411f000031002c0001d07000030443d80c17000013000140a03032245070b0041884400701900e0028403035240400582040301e03036400d00310a09883c44480340f07400a03e81c584088818201d03400b01c6d42c4c44140c0d5240000c500f00130700e002000d9641107502000500ca500c8400d000a04407803403a511030071b0001c504404400100d02c420f1308540c010400030446400c0907178100055070ba0441c468240800c0544a00d42600308038001c10a0b02508180045403208031990001084004450306500b116404260344208410141c62480010f42203501040b40d0319640d4400c800d00c0d0750001c0000404105400d40355034060032a48180d00961400d81d452056009980d441100030341c1008241c682030104500304850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 793455323 1250 793454073 793454089
    0x9060e060c120c09030d05030702010e0c03120c121b12030606070807020319031101110721052701030b0d0515060a1d060405100308030c0a050c010207051f0902 70
    0x81c0ba804030704080d000070b44009644003260203002010702503e170301c40800c0b6406806a0015180c5001550070308840d12503e40c0d00059444070020000d0041085031184000c0010036400040300620b58040c0b40c1d041000c001c44840240320306241d12640c001b0408101c0360b0326042100c02d42d10560440010000d110282c1d07181c00940b41000e41154000d590b030908c902c0000e280c00000700706d000140071030164407000d040e0031401503602e1150303000003403210304000c6401c2da62510071010300034074184117800280c2120f00c500002a08030030407030402d0703442e2048403060100d190140441d4605c014881100c03265003940e0501852010354030035242000202c400307644240e00c800e0060a43c2610307050603000a000350303642407a59001132142d900c0601200a0304015005890012610180540d0070700c1c01265014444656101c00c80f80c02c00b00060131511000319181682e440b1041d5082040001d100320190b80c0f00c288000c1240ca40b103100280854a1320070220141a00d0400c5090512440d1840c1c02d0050780701e40103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 793456573 1250 793455323 793455337
    0x30604030c0303050a0e0a0b18010608060a0e0114010f0801181122090606030c0605040803030403051e0d14010905010503070e090a0b0403022b050906030402011101050a09060e060c 79
    0x280800c99585010b04100107107860003010511f4030405503d4001e004004640c0c0d03020307200b00c002046400c240e0b814843e087c1c81591240007090f50025002840d403003003550001070380090000012682c010f82400c080014582a08000c0c0d0680440100f005811002d100d20004000082e2003007007044030366210210403590900c0d2060265125924100501d100c100c105441c00d402840304100454007400c29600034041170108448420400d5008a0080c5c041c0b0256001c4881e854020b52440e500c607602104c55411102d4111030712a08541d1100070388900c840a8080e80c5000320300028035040080b81d034a492801a80129002c500e0400180040c0c0c80c049503520a1312400b0101c501c1d0303911294803092500464040203044900700100340810540c4c00701d155010401c5008091040712050690420745000ca5215600842c070200411181401e14501455000780141818101c0d1101440700c9800c1d56000c4401c0300c0c641c3e98510b4031034100000740c4a4940030b03981d00001890181790422401c3d0040c440c0e40c0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 793457823 1250 793456573 793456577
    0x1050723220f0348030b01090e0c010926100f0b03060912040312020a050105042f0607020d0c090204080109150209180a0212011203030b030604030c03 66
    0x4032000300d01d41903485614000c10040c40d0110701076990120012200c0a0700013261452480010030b0303001442210320090354211194a071a444a804d1028418002c040c10350381c00800418030b000020034400b90606000300800480400d084046020040c184070b4155141e5061080c0307820207118040d40c801c07014100d0750034a000450245003030540907241460680da0b15258500f0800810500d440307503009440c603180150121900b83d01d03032001e4103481e040c0380e16004040e10406c0c00100046444401d001444120790300660745c02c2001e94403041cbc2940c40403201528160300c1c94412255080302440889221226400194007284170600000c2c040c1c800c003040a485015180c8615003800281c041a500900811508540e9a90345001d0b20f40689000c840079140b508010b048140c2c40c800f80c0c000c275140d035480281031b1000031388007003601c0d10f035000003801000f8955800d2103007280c6040c49a56840c040e00501501c0001c400141c540141600d501c0003316011750001d01c140300c0040d4220340d607004050303814 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 793459073 1250 793457823 793457827
    0xc0813080c07050301020f040905061507170f0c07051009031709120a030f09050618101202130509011e211a04150b010c0f0c0906061101050723 63
    0x10124070761800c1c001d90816581544002070f440c3c803240a600c010b0084500c000710070b014981c2c1d69420401c01a50b90344010484440c00c02807a0005906e100000b07200c0c255402e41707030b4200103103d0440b941581003c0110f0310a540b2105c0e0500807440c1c0050f00520349005490414019070842d0368007824115003421039221480302140c1c03114aaa540f1080103c9074003424200c45808041e4100106800310700d68400000ca81070700004544e0b403c02d181124040c40b1078074244450251301c40240581489030200c0c0d00c0801c02021044084040180000c04007036461102c0c00308039134141010844141d006a004600188000d0540070064030b000c0d03100710444500407200c0b0490301e4007500e41c0b043c08900f0302c00145410815110b09188802c8070b00e40a000b907005059402d810000c1c005070400b01e455800d21280451141450a4009580080d80754a00e0b4880c5010b00d02186d41c4d039445000b550900d82100e07011a048690110036640e0034400c890780802185452108603084c0503040002c03107003601c00a0480240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 793460323 1250 793459073 793459087
    0xa0f0f0b1503040f050d0c1203090222060302060408011d010c0f1b08040b0c010513051c090b03041115160206031e01060f020705060310120c080f0a03030c081308 71
    0x880c41101c1d4840c0d0017205407208030845c2800240301ca001c3e0001111001c0e0390000c0303030098912078480c0c50b803c0e0b980a0b203c410491449015468261507091341c1941440d2540d20210050302c4a00181000f0110000042008501c414009041c0c4030f0204090b0744030b078074107002e030314501741d0010b44c00d0265080743c01d109042c016803018141b120701e07200c5000f034110a4005000070b81407039800000d1503140341d007000030846900c82d030042801ea000d034000060026030181446140740c401c2c3d00c50700960312410781450741c450381d070b00c005504103604102d90907030b481701c068a00d003036007410035414080c10342c920150301c06e02d03190b00f49018980300c000610000c1d000e4030307021001403005241310354a00032528101c10105183e6a480c44000d12103400e1074078180040c004e030480040d0a080c80025640511500c1c0c102030401342c01d0500244200a03c028160b5401101c4003000600c04020301041c8915548400030741401d200314140601a902c1d4040c0001c100114141000801152050700540b4282d04c4004550340d001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 793461573 1250 793460323 793460333
    0x190b0c0708070b0c0301060806060702180a06090f02030402030c0a0b03040b060409060218030c0114040504050a0623040615020a032d2001022d04030b0a0f0f0b150304 73
    0xb4201d00030000c58001060001140180d0003a6040716119540c400e8941d40d00707018480d0a0040d4603000b500150180754032034142d00e45556040d4403082c0518002040f503a18009001a0349003000441c0c01c0690000030302003036003400d000c41d40300d810003a00e4954495243c4450000c941c07100920262031a400503000c5030096030307950030907042a03410600179925100304001841500961441080c4288501c14070b0012030750040700c03a00000780001d400541414034100510015010091404000070368588020504160b203400b000365052111131504540c1014409000c11200c9035080410100440e0500d803d50300d40c0007550510340c56040c9005030042c0c000b40c400403030321100309590300314010b08090703402d800d50390080034120b6003c412010680151240001c0e01c0c00c0344904600821500e0103010f000000c2100f04200f031204810b0f0694080ca480d989403a0b1000c0c1e01002e40d0000016a21005130b441c00c60f207540107251510b9001041002107045c84000070f0071120550413070700720708a404000101444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 793462823 1250 793461573 793461577
    0xb040b03100f080f010507020c061b0f070312020708070f1203110304060c17070b070c08070602040b030105030f072108091e0a1208030a050c0d0e030c190b0c0708 71
    0x1071202e940060450321007503816100c4074000c009403103d600e400e001410325480010003110080010700081e1415165104d003040041206110324100e10440e040d070380d55070000300700660086000348200348084902c41c00003070501040d544a0f0b4900d40c400b10003404003095540e4140200e411807040c3e90340300ca080780746c281d40c107020403003240712103000120b000990385070000d500c0c1e02810f02c070b41e2002140303078250098142c050040d5403010b404180030f90006642c10380981010400c4500555415040501650303400d0141c1c0d00c15044588103100120041100c0d00381080f500481c0d0304100c014007038041c148100301d01c0c143c2d0398400c445040c280390300f0301030300f4040b14204031040e00030b000d007907452001c02915000418800c0040564001c801c610400034011350b140043c42185940100c1141ca543c803600c56000140c030b00509401092102000384182c00300aa100b000300748664080036603210005031803694240349518642070800b001e4003d203140060500d0328805d511203858562940c0b0b456603810005840c4c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 793464073 1250 793462823 793462829
    0x3060a0c03150303020d020c0901080316050313030c030c0909120503070c0b091510030503030a02090f03010e0d0f0f1e0212161106180d14100e160b040b0310 69
    0x42c0818004000d1542c00b04102c200000e803a000c03140c4100f490001d00c03000a20901c9202e019420602070741301071300d20b0300c8500341080e406541142d00307048030090710002d0b02c415079008840344070b1884000c00c100201c00c00c5000c028081c034031042000c0740e86601c4401013000814000004c0000c0007000410325030140b0b031042601a0811407101180c0b0b480040107a8440c0e200b000e014421102d030300001c1a9003181c01901d0142c0381c5c00b40c061411602c90104840294200305032560303002400d00101e0016841c24881e13030031482c00281c018840d101c6070340c0e00508030340c2c03e40351517a08002030b003103101803c42d1f0000d000400b62100135680300b030180c11a0070220b083c1080c0415040900a000442d40c0040900d46000340d001c1d40100c3c43e401d00c192405042200c144034100c19191030300c0f44114a050946898000841c00074081c07041d480407031003c8403209041c070022440b44d90802d9070340d00803015a55001c12070744601c2c0c1e42e045043c0c0e41d85820203400c01118059880380f1981c06400100045881c07043ea540c0c4402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 793465323 1250 793464073 793464101
    0x30f04150c080f1b0403030c02040902060703020a140c010c0206091225080d080a0b0d020405190609140112140a0c08060a0b06180a080d051308070503060a0c03 70
    0x30741001c2810052031040152100001d8160140114610750408046201018026049075180503d1650140d44140420000b030f0780c020307582d925400160311060001c0060620a0703020708107003d294070704007801600c00e4070841002c0e40680001406030340c204c050044103640440d826902c1c0c0300514001800181c4029051090b0700580c40201c1e40035065040d12510301c2004c3c01503025054807440ea65a54000c483d801d480020ba2210100d40c10161603070001001e940c01501007101c0200a80110301543d40a0300c5d800004032038030500518a0110713106440190403050010b1029440c041c20400c5890b00c1801007000001c103281302002048840c0b00300010b2003d00343c055aa580403142030000d030200140c42150031501403400003d1080565102c1d10007048801070181c0d041c80b450705407202200421030440c1d0f800c20dc01100200d07902404020108161006968055a41d4400d4550032a890345981c0005140e601c04481404590780120f6071540c401c0c03074002c0009060040d250204c015017980168218 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 793466573 1250 793465323 793465331
    0x61406090c0c0102131508010e0907060503090c0d150605030316080901020a1a0613020c0a12030f05040803041101020303090604030318120906021902011e02031c0e0706030c05030f0415 81
    0x800c403198486c1801d0420042d2078000310340ea685c185484a641c0f0881d000c21041d000743e8424044580564061130300411103e080320944401040030502e000e0f5900c405a8a186410b989444820900d01410018017000d901850070203a41d4015501000d0b58120000c107905408034200340f8a901c01c0095150954208004d4604450079080031140500292070450003010b0741416130103a99940d00844415200720301c024490041681c5030700e40b5205c001c46001080546405410703810049500440e4042c50041101070f5680c24985040101c4000d01045ca40c10340d0024000c0100d5081d01280c025449034042c01d0201d680c0c07107070030324807084541c501c0301c000c07d0941c1d8a29403403c4203070b002c0b0034070044d943d4640807918807008a1b070b000d0741c1000259038002d000070320001c03520ac075090724103445044280440c01224107041d08080703100e03000c00803000c580c0d029595807407140c003000c0800c1000000412090070200881050b03580000d090b403000504e000c803181389250200d01005941e0703103082141074501000308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 793467823 1250 793466573 793466579
    0x80d021203070e100c110105070f021908010c021b0a06020d0311040f080f06060a0503100207050102040906290a120c11010e0d0917063c0103061406090c0c010213 71
    0x28017000d095001c01d40340c05200600c1044103500520889864503002003800b1440081a8204210041503001e9075103070f00d0000c200091101d03424000d6a03209140368001d000040c030b0407202c044d00e030024948170901c16000d4040400c0b41940108100d00019420316011070691592900500140304543c0039264140c0b100c2c00001e0880f40118280e61004854425117903951030f02c904012a007003d5015803681038105681101c50103181c0e50040940d00d11032030002d07040580d40c00c1004215003c50780324042c4060035003048045880441416603045110b4040c1504040c10100c00501c11840c00f22000d410a6840151000d11030140c2c140d6188600720030024050590300317120964403002c0441214022070a414400703d905185008160302110a10307008024554411459007400b510044090396502454030a202c1092101600a601002d4086d00501d82e549145000401c130390300c60705c00a42c080c490400b2701c44655548640c8940100100d01066224100c400c00323540244107400000000d00d201c90000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 793469073 1250 793467823 793467827
    0xe010509071115060910030c06050714070b0901110601120f02040209040c090906060507080306061317160512070b03090c2205250804080403080a0315080d021203070e10 74
    0xf40d4425030702a01c40c2c04243e181c840c6c05c0d1548113514000180301e52400c3c0004d104940c800e81c007138000c0700d02451400f000701012000c44e80c1044d59540191007868400188881380c0c0d600140005080074a1000038641585003100c6600c0c000007484c17000b0907406503141d0f481c05569541e0156890701a009004215040a400028040c200340b481a558032904024000034207501803c160380003540c106030681d1031a941c2c10208401d43d4800140100030101e103010201d031440c0c500040b1824001160300408980244001000c000760075580542e00c5545101c40c0c00d0705140c0003049150440e95114400343d1a5124038120030b0509240b0319460750404408612000b40c0b0f481d190002003c4040403804002940340c01550b0402d601c0c1e88030740a0710070180e0f4058041e070740d407142c2e41c40c5601074081c0c075400d810540c80ea0f075203022030f51040722032000003a11072054a0f2039840e400400d600400703280b0014000140c44405c06501c40c079001480c03500210300400000c40d5203014800380c03244201d0080125250364011180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 793470323 1250 793469073 793469113
    0x912080c15040501060602072d0b03010602150a0c02032a1f0501050405240d080a0c03081503100e010617100c0c021813060606030c080f010e0105090711 67
    0x4280d50703d608282001600074000f2842009449890391840940304450212003803d12a027005030301101410480001c01442c10300146000c0e0a0726030103040ca110701203c0c03031700303040c02c0c007600420040385891080089981c00004440300e00b44c840c8004650144a030b180103001d01c01c0500e18400c203000e50700100c0c0280c0060501c039111003035022010001c0340d0325801844110340301101d45101100e4801103100081d00d000c05504c41e1010000c8c804402003200b944d0b0042142c00619900f000b140c0403801620816400c1550507501c003644001c00030800560340c00180e40c560b02080d201424981e254504003100c4001e401050240c1003141d01910035000d400c02c80d6a4400e02c01601c071602a1400c401c070410644146483c90440f50020000b08903d007000001d107009043c0900f40c0310004004003c018001b4030f45000d403030002c203001e880024a4542e4008007500e030041c0203005003807244070301c80180101110f0003c8217041d201c098401d0300d003e0f0b6502605680c48448865044800d204442ca259401c14580c80303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 793471573 1250 793470323 793470331
    0x607020d02100b0102030406051303020607060207140a080d02130503070f03050d0305160f2c1003090f11061204080306041b0e1009033f0912080c15 65
    0x1c01c40e000401e8403990380c0e0440d800120f000d80143c10400c01080a503219501030440641607180c41540c2e1a925800140143d0200390126500c0d5004558441485040704003042c08448040207015800410768940c1c030030b485040303e5042c049a0204042e00561140c0b2700c004060a009022580100d03255200f00800141c94803003214580704003000c1e454070302d101e8040daa0044070304109101da41c40310483e0075591000c645110408202d201b41e0881300b4881c036034050351403008800c003c030b50200f0340c040f050005481340d110128041c5810a0b00c0000002c98203800f050b04e25400a440000b41c4100740d0006100344251004103c83d00000d0090100340150000214020401141d00308006410002c211107003d9481c55200042900c1c0e4104920b03505110203802d40e0b00d001c92030180035040d1241d484095481e2403191040d154001c00200304540e0320421003282c248407200d145041c6170000d0b60030041c52050180903515904100c000c4030b1003049041800c3c0e40b03452146809a0300c2030440c0c0f0203c0110410111 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 793472823 1250 793471573 793471577
    0x30f0227030616211b091514071e0203060a0c03051b37030b100c05060c0a12020c0c0a0e0c0f03040f02060f0304110a23120607020d 58
    0x18020407000d01c2c829901006030003c6485640f10b07aa80284d007000800140300184841c161500803c00d210320003a89400084a415215040020300b84401ca4803091800e01c105810f014110f10100012402c50060790107560f405615540c40c08010500c1011041c3c161000039003500c1804240000b024260300303c84c01c600134030b54080007507646003c0c4140e0b003003c10500c030810242c0c04110722110405040c440403031803514540304400c990b8881100507202942c5144107400282c1e988401a00c514202c0032448154156240c51000104d49844160701e41c1006400c5140d000300c0041d44411a60268098501c0524114011034031001409000d607150b00119103010322685400201080f50322010748060b020702d5201106a0521a6842c180c00f103030f910141060303400d4104003d1040c01a82c8180007803516004080b4040c0d2242060319181641407014170f4001d11803500480c1c107105070a02c550301824503501180c3c20400110304039011410300b4401c0d000880d2280108030401070078a1300000d180c002c42c09aa = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 793474073 1250 793472823 793472833
    0x706050906010b09010c0314030a1d0102090a152705040f11032e260109030503070309060e0a2d0f030c0c0b030f041a1006030f022703 59
    0xd84441e444020074081c101c1001000e02c01c99005501c00c030300c00360000340b0a081880c001504403040e10701d40c1d0400c49010640d151110f4050454030100c03400362410800010083d0700303142c4c501d0001101103c850042540600e112100804210710540202d840821000308283d65440b45115044d003400150040d0740c0102c0c20210b17000c81940c141d1080c3d81500354446d068904640394a0003815410ba92a4090355010300c120341c84809018031007034038a0007820307502a2003030680140c980da0400c14001306401010750340f4060810020036004000c0300c1d801643d41c540000e00c800b41d0310f041001480c2c1d01005841504c202c0c119039082107a0b05c035540003910036a820351810a0102e022980a4101c202c00080048003200d6040c0b0001c1e01561003008628441c14140b0081601c0d80c2d650b40c0107400403541c4003030103d10700e000e0006111200030b84141c0d6010120030302c0e0040c0f81040e404101c040440c41030004040d66018002c02031045a41a5a40d410707000c505c181c0c405a1250307040e010034007104e158606c01e01035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 793475323 1250 793474073 793474081
    0x8040b0c0312072309240301080f070f03030806121b0f040e03160819022508190c050a0f1a04030b19020702150d111606020f041a070605 60
    0xa100b101c3c0c014244c00c121a050640c120000280726000044078035000402c140071501c00005008400c485820b039250040e403658904081c0a1401d00c416200d403140b600080070501001840c50084070940750035050203401038580b840842c0304414000c8981104c3d014101002d262000540c580704200c1c6403c03204510301e4000807040004a500e01c1042004940c420459241d511001580e0409164080d4a106081074008040100403a0322500300200503000010b03450307131203102c5444200320822050503105045050003045542e803100e803556502000c078005601420401e101c41d904010f014080c1c02410700c503954640c0342907209030500a0180e644036086190a0500348281a101102d4214101400644408007905c1103610281002044240c0070070203540507031181440302c1c00b1440304064559445829151620803610a800441446c00c000c001120014880c035500504854101c400160707591011602100300b0b118036842510700c0d5407800903d40480c01404040e0503054003942052050b956 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 793476573 1250 793475323 793475327
    0xa1d010e09070210050f070c150207021f03060801050f010302010c020307091508060a0905030304080a05041203050316020d02120913050c1b030c1002031f080c0f0f10080408040b0c031207 82
    0x50200e42c01380c000b0360341e42090300101c0c4102c01440c010340c102c03127001860300700e2980200301c2450306900b0001d034500e1400e41803170141e5810300c564401051800c00070449800c0050310034054190620020b4100100301e4818815560f060140c90300030040e05d00c00b000182c45020301c07000b203801148680d0440d401480f0010380649094010f0440042d441000b1314516600c550b0f880505411500000082140622000c0750100701d14171040700084c0643ca925841c2d10740044e40d8550003081c01100b10854211141407501142c001600b020244225082c40d92107134a0701d000310b07081c10340f048a05040c05040205100081259200420340101a07c625085000c14040050b0362441409038003840c1c0d034440c0011030200c83c80342d4007642d040b0580001701015400031038031140c0300b08826088003040d5000403171070380018a8002c28003c0c10440036207200d501a004a00000c0c40d1203074100440042c841e124002070b0400c8108800c66020304400002e40d41c940702c004800f16600d811211038003006e1030101c00802e50b028 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 793477823 1250 793476573 793476601
    0x306061b06021605070609030b070e09010501030f090602070b040b0c1e090117190501050301060b1603051306080708072a140d0e090109020a1d010e0907021005 70
    0x3003a10204100e03208a140e560000070340c003241d08103500483c0510440d000540a00c01c8034000c00042e6990b240c09070071402c111082c540c2c05001c40b000d20400354a1000380f0740b142c00006044480034200000d034a00f02034800c1003e005005001800940f0006543d8104810108158052406103800714820360300c007203d4a51910581c1d0400a401e10411011101092100c00400c8000c2c81071401c521101e091038081d1800c40000d980c200307035036200c20950303503280b09c1c480c412180144011002402100c3c40c0c814241c0c0e1b18401c2110303e0b11166490114441450700a03401c64032022005c00e04522030783d0752500c000700398403400d031a00400628a18049054284036143e202c0780e00c1140c00481d08078038201200300030610150302d402c540c040d00d84103003c2c10b9500d041c04001c00c03402d0302c1e403940c2c6c1943c00014200300700303580140c001040151061141921055204020803845004005052074000714400140c407444074015100d40d107c400c0310f041006240c3d000c161252148159502806030341c8401210072014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 793479073 1250 793477823 793477847
    0x22a070e190c0c060227061305010e181006030507080f010e040510020d0e01110c1203100f15120c0203032a18120309011e0e031c030606 60
    0x51111000e104000c1545940180c2e0920a141400031000c2c00c0c40e9949001d98005d0240030642d101071580b590214180103801750b95429044481d14a0064440ca000e030100c5e100d0b0281c20304102a41083d00c2850311150b54030180790700b500c4101c0b071503440d00040d0348440b00e40c079004020000e070403c00413604003802092010301404072842d040140741e0801d0b180d070500c030700001c2083e12140704070403c107104c00301144018108400380388404900c502c24a130f050b6086d035081000d510000541009411805100401d12000c07004003a54074541d00d8841220ba00a00780d0660485211529110000187c8100b003200c105807014468588015202460f040b500458140b02c401101507001000010080c107845520899419000d0510440c0f11808910414064020342c15800c00801400503400072480c0030a00900f056403004001d5180c100341000007843c22034a459102c8021040c9a60034611500400d890300d00d01070060102d0b404030b590342d08406426844441a0004a03180404c0800c3e020b01c5030360750701c0d40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 793480323 1250 793479073 793479091
    0x1302031b030a150608010f061e030506010c150b01110105040c14010909180c0f1802090a0510080103110a051c020301150305030409150302010c0b0604022a070e 70
    0x1000290400c00c00c2940000d000c0052aa525510f500341d0046503041d64000d0b00075070342c1e160b040398100241c61038a94135941118040c40f82da0b041c280c40400403c0c0115500c80c00c075140102c2e00e5282c5030016078507190388483c0106505295000074116101075404018045030907a030720000081700c07941050890f00c05550141c400c075842e050900c6015450340310000c4218040c5401e140550755520740c1c801701c2d0480d00c0d20441d0038100c01c185005020603125414094030141e00d0700c03d189481c00c0d0484004906c441442c000042d00412072440965515282c50000d040282489e40c098200800040943d0400d000485403580d15510203051400c1a10741401600c001900c80e54040074110003014034241e8100c022a4135640300c1004111655441e00480d0081d40708100841c1c4541c00e00f4900310035500a1400c100444c0c040880410150b070f80b05241e8800b494100f021421152110000708020f8481e01c600c4030300d650844805600101410700300101d4100007141510140b43c2c80e2006801055800da50200ca = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 793481573 1250 793480323 793480351
    0xb0108040308150a030803040b06010f081302040617062a07140106050d080c060105030c090105010513091e0b0406060c0b220303050421090603020a02071d0402130203 73
    0x38002c11038a03400c030005803045491a40d610700001c01016080e041141c10f00f50120900040003024401c10303800c0b80c42400d04120f0744801c01c0c0001d08450005203814900f00042020030150b40303ea5115901030044200003e1a03141c000c0791003a03442c5c070103907503445144102c42e010b4021140d44404010300c69102d8a0214688101038841c8001e1480310110a0070329542c40d00006201d0b0307204803251079240d105082268440001509040c1004016403040d4083d8105120404403661035020b01c07419106e00b401e1090f00c46c8000d01000503119000e40080410501c0d000300c4084103e9078098400f03c0910850060200310001d00a11082d9002c510030a00850f416119507400108802c008641c8a0840000b060014940f229003030a005214001500482ea4800511080c01000029035034100d682000c0a40703840c140701c00040c00c08105108040805501260701c240482c1300340000001030441d00700e9500f42c0c681c2964040312555017075404070302c22042c00380a4820700003503000340c038032600381011400d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 793482823 1250 793481573 793481581
    0x1e0903050309042403050a0c08061902071112070503121201090c02030f070b2508070f090b07080a02010b03061306020d06170106031202010209092a0301140102100b0108 74
    0x103c050507201c41c4c010401d1100a09070a8034001c440c04820045004030300034265400300741081d6113440040d4000d0001ea8004108110788081c01070448410780d00d0b541401a5546246d041121503c0074000322654042e4800104503202d000001b0300c4003d54004a0585c2c441c103c02c3e00001d00c0c0752240d1001d4040c4d6801203401000100900e074406100710100e40141c0380740001c80d50811449a2110700200c131140c001b0001d10503a03a0242d4842c8503109491300309210304050000029204210090070b0408100f04004030207407071072003128044000c18618000751380b102034516000b0407540110340c0c071200540c40e080b5020818940000c1e000d0203215242e1403226400715644420380a0340c011039451342056196100000c40d80901d9000b0450903450341b0000880c00d0075450320018120848401d24116801440342180075a20034009680108842100c4015802e03c05031880420034040041200c0d03e101000008201100715102002d00b44241e003a2140400c100c80b40e0011036031f82c00d541500140e4488002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 793484073 1250 793482823 793482829
    0x32903060c09060f0a0c0c06051602130e070608042a061d09011205010b10120515040e0d0e100c0b0907181e05060d08030a090f031e0903050309 63
    0x20b000b0050082d080034904000e0003034401899015103905800211800000002d101a03000418003418807480d01500d4900d44001c0b210703003081910300103441806082000c05607103080340d000f0403004240e841a40d4400f5034503030016007054012034040c0c038005851041003440c40500e01e4080030030f80c08041096416405c00104a400010310642107800170403010121259903941040c04d802403040101c4036942543c40e2030481e09560700c41c0c0566010700c00000228072607541040c40340000081c24040000c0b1940d8003143c250400b078083c44100d40140c501028000b05000206601410300c0780341c0c0390405402c0c00501030001d004145170f00c41d0006074002c907205000401c0d148055402034426011104c545032036200304505902000d00f0148040d980e1011640400e04451a8540c20205183e04002c0f620b401c2c000b086140d405944020440c3c200080050700200c440c0d40040f07042c64010740c012407003484610b0041c0900700140340345134654044c1071405950920a48214041c2c07503014002e1340c1000713100824 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 793485323 1250 793484073 793484077
    0x60403050706140403020301091211010501140402070203030909041a1e13020d0b1801150b07032105090c0406090209030a0311070e0a0b0a081203010311060405060a032903060c 77
    0x501c1d4000300200130003c09654240102603540340144442001080714480150543d4410b11411216034180310040081c110002038203004060162400f583d12a00c501c0000e082d40b1070007107100d501491131f1062100340500c1c3c10f05090700300d45401031003681d9260307a507643e580d00000100708910119400001001008141d461419561000c3d1240aa0401e20742e90b812010b030302282d44d203080708118840c0883c01c140034011100100c040344850900f89082031008011403055a5010781408101074942c0f800140148210b10780e490200f20400a40c1030004030180c4504000000c2da2240c1d0034040c0120f0003101500c22a607000d07030001c000300480d80b079542c0c0585181c0010900b0603550302400d88002822210320b40c100303100d0b039214500018800512030400091039030310f030811300d007983c81020102c8500742038408a0f815250070030890072403102102d00242c0d907486540c12464205c6030106a160026030590040c030b02c0103000343c80300d40b15107181040218164650121242c0c0c564018404580c1022583e00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 793486573 1250 793485323 793485347
    0x50f041205480105090c04090b010302060a020319030207020112180f03110d0309510f021e030606092404081f020301180c2c0f060403050706 62
    0x358102c80762900801101094824400b1141075035143c00c10002d03402010300c03401c50311000c1205c04000500d8079850301224a041404001e00030100003501d00811802042594010f000d1040d41020804a04200074041e4001070012030118800b0000c401012030a80200c10190400c40581c054412442d141d000c01e91003c07140640032f000c3c100c58101d44910041c0001444210551008184848a450495400c20803020922443e183c007071214200c4850312240d041801c0a00145002400540004900d4180411502908140c5803200010034040203802601181e002e00c400e082c2864847c03401e10754107200494030141e2112007040300345514a071812a8008500d694001400c141103100d0703100810350f210b60000b80d0a60b01030016500c41010071a40c1e00001d94030240c6c15415545003180b9502d0030340f032089100162944501015507581e201d0360200c80b280d0754805240d8178142e0142069a805503215200c1d900900c100c0b03100d1886818510212001c481c0d00c04c009100131480c11a007114440e41c481 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 793487823 1250 793486573 793486657
    0xb0609120706020115211403040f1d0c220e0a0603030813080904020c0c0a0902250b0117031903020d06080c0a050405190c0e0405061002060c0a12050f041205 69
    0x1f15002031190400c060805806440d0000a201e810a203c500310184021048042c1d40e20680801c001d183e000d02c2680c164a542601c016190444100f25081c11785854000c2551500f5a4080003000701c0d154004108aa0181d182d000e005d80700c004500000b58072000000e49401c004015200003800c15500500c24450010140c600441c1100000b8243c211a94007407a019070700800e5407a040c2d03030454408044109032010b20005558980e0b10a44031f0881442010112040d041a90f0103d040138411a0240a034482c010100e0300b00010000d80250000c003010641186001da010030641c1d0000b030749030071803c0000e00511440d482c0c58100000350400410503070214002d00a17070841d071001401005108840c03520388486116160040c0f00c212a0b0003000d541c071911240190360b034070340c2c1c021a0b9031b13400900100560f5a120342901060310300c02c0701d4a0104140a250404202048900e05109402103100342070b240c07280c040ea284112014055400b141d01b081580d00300d03c0045107034100d01406132003140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 793489073 1250 793487823 793487843
    0xf060412020a03210b330403030e04051003050625020a02010c120216080303220b070f030b0307230604030b0712090210020115170a060b060912070602011521 69
    0x540081908000c0703130410003091100300106d01701c03201609914000401307074949100e41403d1540c2c030b00a01403503084841d80e019903039440101d603442030111510344c0910340250880740300c2d040c400080c404100780d601c1a030009003001e1800401e0070348044ec0d11180c02d90140d586020b1110a0385a0603683c03a45000c0d40e0040d417040040f01040314260140f00340040040c100950340b289080356851107443d002100400c44100050b40b000b002800380144a0740050203898020f010100d02081500140ba880c00816818450940d0014050700103407000c0071400049420362a2050241c0b051108030701483c04001d145052000000d003855104103419440300100d450b0200d0300691680110380c040c01032003581c10040c0d4581d0b882010340c0c400054040001c1c101100c0c001240007207003018a8039030640f1100102856102e901c041d42c1591104280d03401058004c240f0800d90305211010b982e039400e244030b018050350821a03d1308100c0421240a82203e08003885030716403081d450340585a00c03812007011a01c000e40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 793490323 1250 793489073 793489091
    0x60c03030b1f1110020301180911040615020705040b030c101b140c0f010e04110705011103190207051209030a05070f0906082d0a050f060412020a0321 66
    0x450501d05202d08140c6601c0e040c59400c1c5446030800b00e0050261500d10700403c0108040001c91312540d15030a00f5040c0001d1b03a01d403e24203810840da111001c2503010b410050041250b0910740c001c03189007291170f0216400310380d070368091002f0795a00a400552640151046501c00d0408260a51050103549800c148005143d02100c0c00c00b0b401d500c0540c5c0280011131075030b03a600710400c1808811a4100c40415224800e800028800d402e00c4504600994540d449180300e01004402c2c2e802c120b50010081c031642c071280183c120b150b04100c0d150002c0300921440039a06075442d20071511181c2c0c225000e0003880481c402e4024080d40203507050b0b0340601c17400e07000070f010035403e1010700c001c2e21108003039554040ca010420002c2c0d4a0340d0b0071040480d0020401503800b06003034406207410342d10201410329810040320f001d9081154a000142581c05202d02100303950f200840e15620607803142c41c0640800f502040201d80d0303400f04035002004902d140c0d03c480d0f140f0289401c1c1b8000da8180e000085074070f41c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 793491573 1250 793490323 793490359
    0x1050618150a091a031006030f022503020705010c050d0806060f16051e0712031b0507030b0c030433061806150503150301091703100f060c03030b 64
    0x80310325142c40000325005420302019580b0361260754407241c100d03a19401e50030491181d515900c00d510500c07062640d14050981a03480341d4064811465036108000c0e861030300640a00b208105021342200107000b15840455650300850107160000d80003001002683d60031a001c0d1840c11000e03090350307400034051100059006140d0003c10303203544035114104012a042c40d143c0c1c603188803075400c0720200001a08514215000151690458602201003130150a0a0609441c3c5c0450503450070b83c200a030000326030a1040001e807032012203208402403080b5940d411029055400140c5004044e480382c40e4402c10141c0340c030490103d910600c3d01704102e404540c1d41450003110b03000c1c0d000502044c40807805100b80c02c25445035800504869007203840071420480c1c01844e51000070044240c610ba0721001c10115107003580302e84109980040112600550740300c41c6030040e0411180005201420780300460802e4200d030340390302200c006840e0a41c01c14129a0150301500340c00081c0c40d0082919111204491 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 793492823 1250 793491573 793491577
    0x6120902040e0109050d02032d070b010305070f05010201020f040e041a070e03062a0d09080f180d050c0f03010f110a0f030e0c0d06020d0510090f050105061815 70
    0x2c01a070000600041d031483e0040c10011401400d20079900240507220b0400b410801100d0b07191880c0c400d500782903556103078a140078010458041e00c200310000010003004000110310080d100014070080559603030320012401c0c1e11400001032600e04052108010030b140d00c0140c282c115100c1da00d0444c843c0c444105a00030307141e00311801c40c000348403c1e140781c445085c280041c5802c6007208901400c0c0340601107240e02c0ca03001c210842d40b0f0400000035904040c0406602001c441c90340070296980d00e048034030210210360014040d040d001c0081d0300ca6481c40d4038021401088490744003020300072210400c002c1050f541941c9d90361542654844010003c0c906240c0300d1a08100a90a14184c44000240713000708200050001c80c1c0c20b140c0f50241880807110001036050001c071044840042c81a4280b41c054064002d0b11408130301d490415042c0403c49000b010190169000d902c070802210010b89010000c0c1c4000303101e901e070051410804d8074201c103c4004081c20000000c1c020005164101d41000c3c01a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 793494073 1250 793492823 793492841
    0x90121020301050414241c1a090105040c06030b0406030605010e070801120c1406071a07021014150102070e0106080609010506040315200f130f08070612090204 70
    0x495030020052116203020310a101d40240c0411075000189011a2150305400c0e002c2e800103001c0c40300c007440c580e0617030741d04800082d04401c90209000c40b48680c580310011100303850400c0e0100840360300047c0c0c540703414807da900c40c607040a0712219042c604081030b002001983c1180303403c1a10f44c200407010400c503000d82402440c0700e560032001454034190042000d01c040c0c00040c1440701c1403d00e0004184417841c8102680e000704c03002180721405500084152040d03480007494000d0040d402c54014817181b0750369110703009903000e992201c0400705e0120111005d5107110003410008201103040c0021920240e01200c5040c011924196102c00b00724501042c00d03841100003550080820402d81040d4050724010071081d105103062600f556511440140c00300503d1007a0341e034440f40414461545002c2c1480c41590789034081c0d40e03400404e00703c203056100e2a00c0f144a10003014002440c203100b48004011280c2c1000641065030601a00b01c80300064590070501041e03c0d0440640581d070755100300400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 793495323 1250 793494073 793494137
    0x110a0302060a050903090907050f0403020904050a05010b040509070b030901140f0106120c080406021c020a050d06231002010609020a121802240f03040b07020f0a0f080901 75
    0x4500e480e4a102e0261100200106001d070070038040440c071500d80d0f075840c42e002200d80c01d02c0368035440d5000c609621380c041c0354400b03503000b41c5040a10041c0b141c080f4807090464080d5000344016540f100a001c01d0329000c0e01e4185159000d141c040140e96480781c080c6400500000020403642400c03000912800c00984402d1300401c0350a0040103401c1d0403403210f0b1360345640003a051007098151800503000c0207000b80040d048680004800c814031a4a44a4400d4100049801c43d110400400014000c2c2c2061041c1e1003140c0c030b4000c1c04258982081c086410010342080140b1036400504244a0010040710310201550340f030f40740c00b1800000500240c48602001c0c1da030a1303035808031484800196111710b1003401008030701c1d025500158a0f615031151414004017403950070120600c1e55648607108004540780f411102106110820404030b90050248903d9401c962410300c402d00741c96211280e80d20004c043c407d9062104000404004c0a00079040c0b05041c42765240000355400300e0465849154018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 793496573 1250 793495323 793495333
    0x4062106150311070c15180303022a10020c12030c030301090b0109090606050702130c2003041208070b07021b190b1c0f0c0909020c07050a0e0403031d060a090201110a0302 75
    0xc5450f900087c02d0170780711088000982840c0c916140652100d01444220700f104070400c201d4030300c80090000b580001c510252a07241c00c92042800207483d0603c1c43c0d8550b104000004c5c14031014800041502d407007000880140d8556464a0351780d500800c41140f029040c071074216030010300c9040500c2039400400150703c94603540c8159104000901e4400d0041c00c000a2030060f4001c3d00660200543c05001030200c0d000d001d4242e03900b8000c0c9503005a601103880071104000200802c810f1801400010f48192900d074881e456494081e030711006000300c0b1b880ba880b142210514107203850000085003001035002d00c1c549948650340041c0380d031300008070f55401c5040142ca803140e23604288140c00303c0b208480c20803c00340a00e03c000170894071061244415040d000b180c4e9448095040c440b41004200c000c2011450302c0d03607a500040142012507040d03002c00e2030148454021000c40120314510030480001d41400e40e140c10040008000303204059040000c00405408104810020342e02c016002e500180 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 793497823 1250 793496573 793496609
    0x405011b0b04030806010315060504090c02010c08070e0604050d051b010212090111031b160801150e1009231b0421050304062106150311070c 62
    0x50300e0000c060229900190041800c040828020312045030026411326090441d42c0721540104c0140ca8054054020303c200b8480008405800000410480b800030500380003450311414240d003220081d04481e4041483c05000401c01c900c640d0021500e581e00a110720704054490002c03810001d01040300f180d007030f401200c02d241c081c0003000c800181d41034244010300100700b4000c900b9429009609049041c05400072400802c110103005131100d82d804210619800c820341d50030a071b540e00006c4030540080621079004250f0381d03418000c4400c0002005440340d40b45103082e00e0035030004402007907220542c66040020518100d5400317601c0000c0c0c1080c1c000030a800d205910311754040c4000d0561030303c295100e5501c4982d03580301c006540450341c1c0201d0241d9002d602c140c0e1181c200610b44001025401700160115086421109000c030144021404100450080804804903001d03409000c10050303a610038140e0182c0b2942003102120421204a400d1042c0c99441e1410030180b6041004c200203140626 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 793499073 1250 793497823 793497827
    0x1200304150e0406051c03030914161409041202030d05011e0f4a0a050901020a0c060e011e0231030b060117071206080304061202220605040501 63
    0xd11070b0181c02c540c200011440c0100080b01402c115890f03c0000011480c407209040c046d50040b2070f20380c0c00103030382d05c05010040030031070b1a9100c00204542c006a005800702d2a240581c218040004020f440c1c2a010f444545848880c0d400d02d03c107490440c442040519040340c0c680c01064001d2116034440864103030b1a200841c14445141c22908038400c1e640c00c10400c00755030a14440007040c8800b801c2c82c5800090280312128030301906a5503000007400c02c604040581982c28030b10410b0120710410854443d042c44030700781d00c40e44600000041d000b005280214041da40614441786000b0000600c01140e0b4681288048940c401e0b4103003a5804680c002c9030b001d0003084a082c05200c6090391039150071001c1083c190b190140806841921001c1c00200c15134014181140c061218641c0b039103003481d004000604c0036031405201100039007400000500a0300001c240c800f59030301c03038503150040400302107044001d400c100801141c3c412009000411501c00c01031140160038995512581c2c0c50600d400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 793500323 1250 793499073 793499087
    0x18030516030c060c0510020c0114010b21010302031515041e0c090e0118020d02030a0219050901052706041502060f01031a180f0d140304030203090120030415 69
    0x80138080044042c1000840200d21500c4580e1a80740041c0c50f061041070050040c001c0300c0e0000c20004007040086256402807014180c1440d500c52155003183c84d408074082419420311009405a009254040b19240170342415544050f07a0001d46200940c6000002c1c203131107045041501a8081440340344918606004010b0040114107100c4001880d240344681354020512402c0060000401107001c095265011910044407a520a54403409c1c1442002d000354401c0368111420340052411513000c074000d0080e92040714050311040c1c00c00c25156203113502900140404641031740a400107070010703540c04000e0000713030880d410402c80c000a0070700c0117441c00401909205c44501c900004000140740400f6000d0f40001c0c9504090b429203405016404010380b41d17480341d41a0041c1001485502130000301514401002da4a122040342c400303c2080381440196005401600100710985c00d80d401a42a41754100c0c03907011042c040300318010180e0450304141c0001c82c4c00002c40c40c108482aa000c22 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 793501573 1250 793500323 793500329
    0x7020a0e07170c12010f08070b070305070f0606050915010f110f2425030b0303130b0307140c03090409170f0a20150601030e0613022106010618030516030c 68
    0x6c1c406c03800c90410a259179140884c1c0300c0e201854100082030410148908103490312141d11072072038481c0824500c1c00748003400301801143c4c043e80ea42d20000e07805042c5500015081101038603020400b41c1070400484103035500030500da0309881988050807280c40104480302c66a4400a50070440205e131804a250300c04024014a901c2d1408099403908500c80700044982d0641c80c0c180010140480e130007090440c02111120200004200400500c181107103004621410440ea1429440c5600c0170070000140520502c00d2400d0b4020f01400410381004e80c0040c9910303026600303600d66070b0580403440003070b58806005580345c640081460418103421000c551401c8020403144810700041d001003e650304200021000c0c0001420003090325a400303175125421b180d05007019959076240c20824008008162481240a5a00b101e0740f6043e00c00c0c94207020758641d1101010341a16485d090003100c904003000300c940c18500b20310f2400000a28200f06218280b42403201d0116000c1c61070900d00008540383c0c0c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 793502823 1250 793501573 793501589
    0x60b01030605090103082a01020a021011040b0316020304030807051005012408060619170703021608091f0234050409110603040b150607020a0e07170c1201 68
    0x18014000602c03c0030644e0303000709203065104401c1c40440d40e00c407d4a10078000c2e0303000035440041c8285005601250490040006550601000c03803808900742d19803140d8031032025101c4d028408600100c540b052802d14100491040303d0406841e5110b61507142d100b1b94007241c0d00d900404040311001076600810b8010021030340600445091740100c0c0c00c6191015950354100050300c000a2401d82c4c40b0700580f02d440110304954028080c0b0824003a0170384034400440031002c0319103000a44040c0c0301f4000c80d6005541b078000084003da01ea41e898140b6080002415400454410152030b0741410401c240d005120740d60090001e99804000114100c0c1d02810b513807408802202440d08100e50b2100074400c4950940c2c2c0081d220340c1d541408080001ea55204c9079201d080041800180b00f04807901500501041041000301410f000410255208240000b5040307114050100004903045151951000c82418500c0486001d030429120625048072002940342c008120b014522401a0180c0e014090310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 793504073 1250 793502823 793502839
    0x1f140112050c03070b0d0209190605040305011d1e0316060501091d0304060f090909032d080105090403110706121109030c220c022415120f0604060b01030605 69
    0x508602ca031841120201c20340c6e0340e00000d80140c952208441001180901c4021072051925200b001f81503903c90300c025159503081200800601486084001c0c074241c0c2c0c0c10040007600040c0c03e0600e0354900c0c0c0c070022001800184640400f80b140c400c1c4003c0c0c081e120f2000001c0303560601402d00e088a80340c01d050740c003040c154658001254070000c11601030303a110781000324103c960b10400302c0f5008002e400c0402c0542c10411480304243d0800c200c0c00001d2800001c0c061a013444074140014103406c00140000500c0c0c1030010442400c21452047c1c1040c001e240c00038030940c00d001c60f11b03d0486654444000514410752143c902c4200d8850501e0240200900c140307040c10310310000740ea038001d048000748684030441030003684285450203490070806c0c2a070140400428800e010f501c2c0c001c49480707001e003803291194080400e041c0c00c03050b80c41340d414644441c030700c0303242102440b206003580b200400e4140700d0ba88520b1682d40c010012944654403d03640401c145c14180001070980d80ba60740054012044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 793505323 1250 793504073 793504079
    0xb0403080a09090902011202030c041208190206070c1211241302090103022b030e030d09060f0f020f160914040305040608090c10020309030610081f140112050c0307 72
    0x207c40140e84068040312409602d984500e10006c0b04c0b8800c0751711510b10700140305440c600300304841010f0000b01007400d0351049080b400b035500b0784e194803040f51040d000a803005c005c000004e4240400011460700c91400800310413544036081c0c40c115041444c0c00002440c501c5480c1010000142107a000080c0d54006c5001c0c0b0081d800704100090600009114400403240c004100300012001507400000c4100807450001c07078140506030400f18101e0b130340203000707036404c0925a500440c4003c0c2141c00079070354441004201b079030071240583c0c40c020503000c40c010640d550300509020040301c202280c48001c0b40c00711743d2510300786a00300d401c0c41551081000a80c0b0800c00031a4010094030111221802e01394044c0c0e481080d26820802000c4003558000c2c00015000c408660001c0035003080311080e021641c1c00d480d08071403240c00003802c0c400d0050039803001a107031482c1c0000295100740c80404882c0803962074209413210f105120260050500308142c1c2c0140410702004121400400009401600210341 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 793506573 1250 793505323 793505327
    0x209010509060c01150b0319020703120c0207080619050109060312080414060a09030e042c01020409050901020c12030f0a02031e010905091506030303010509100b0403080a0909090201 80
    0x5914040c0b4840c0c400812201582c410a4000a4080000440d441041a02c510344070301a5081551003007000003445403c849078240d14800ca0355110b415444851100500864060282c944c60300ca0b603086001c0c030703000020310607401c201f10307400360350b141105051443c003c0380003004175001640000015410240d003080030650400e004070407006a403419040980da80d081403505a04109002c2426120f500704200748103050758080c1c082d0354441d54880030140c0c0240208000d603030403c3d042c1000c0850b401d018420100c814440d0342c1520100000243c201035030340340040200c40e4101c03002d03910b50b50002403040c00c0100c05e10400b800d0030140e40615043d8241002041d42100004282020055000021804040681e584650342650440d108441581c403449610050001955285154881c03c04617020814081e005d1901c82d41c400743c011410750303182c80200070b0940d8000c0c200c08a409440238000c120480090020000786000e50500ca45e20810050020f02150003644510f00c014030703050b031580044c3c1e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 793507823 1250 793506573 793506577
    0xf091203050a0c05030408030301150c0c060302160f06200f0d150503101d03072a050d080304120527120a0c0f05060c0d110a08040305030706060902090105 68
    0x6800d86040381e11003081e9402625600386400c0081c24030300c4046070006c0c03030280c000029816204010343c1c6110f4145543d0f801e036880b882da1840140814003012050000e2807003070380503101c051103402440c8000b8100751614040801c5094043d25500e172900d00c0c1b407903001c0130400c1c48404014485030a51070800001140d01071070085054035075005403a500381d90781480d0843c101e400074000080a542038140342004410040485003003034002c0005080220500300404801e6030300450700451213103210988a5140088030b102c1c0c3c004011642104c0c1004111038680d8000c03503828512601e210b59407400c0505042090642481d0001c0070000100f1030703203090b03a10141181642100000f42c1d0000c0b550920b0000b00c000e0b03542284070859110340400d010500240301c21640445003101c09050710940c80304244541440341810301c10031a40007c3c1c103a071040b48540c038464980130b54134007661640b00660b03442e51000c1d4401da000384c680d0340c0041030940501c00c0c5841440000c000f4240114a444072120000e0824 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 793509073 1250 793507823 793507859
    0x17090901030605090a02060a05120c0405030a02040213080307030f0305150d0201210e010b0f030106030201080402010c080403020d0b06030c010801030b01050d0516080a0b0a05070c2d060c0f09 84
    0x180f5103030070210382414000c0006854165000b0311190311621450801440f0783c100400c855105d410860200301d82c10311400c200e070140d44010700904960b14964003030201035400401c1000c140d41c40c03a040091595424000391420500c04d079101300d1511140c144c01001d60f4006801440c42c1500d0000000d0240e850841d016042c541c21300308910050102c20759074a40c02c3c0b600c0791818905c2e08003600200c00364010345c071503000030740308440360603031060306405140c2214014080240419540c0000c5070156014006140403244a0055031380f8040d06ca9005c0303010b1070541d810803104101141d09004030340c0380a021f4a29942001e1070401400d40c9581c540707003804c0c90180308441c060b124140c0320209000c000d01c06070f001d0ae02804103405041303a942c41c0741d640e100380ca09015074180081e1000314074507101c0380c01010b01851845d9103000e40d4070000c1d2508038071003030010404000e0300e2511038a85a00e2403550342000003117001e03003c001000450200701804c40c09480421408022403020244442d801030712140c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 793510323 1250 793509073 793509083
    0x801150e060310050901020723071703030a110c1f05060f030a110109081608010608030a050703030c0e0d0f0501200d090203011d0706031104260304170105041709090103 74
    0x1245c80d07000c4924021f1143d42c4000c3c180300243c1035610741e20b2501c051802880c0c100b842c00c40300159580da104842e203111940704050039400030030108990300c1d100c3e0070504c203016510000925012500c643c840c5400d07110001e5203841c1c0034101404101300e02d18495254042020f440d0300080c3c0035550002500c6480c800c900508005606803e411030346d105498450152080790202d5103040c4040c9681600491948030701f00d055030820001180307004011040d00c00d09401e54442501300b9074140d07400c0d005030001c1001d050070485444606110b42d601c418940c003120b400717200007a020306046e0620f0390a48115400e000e950304810485440340c410348500b10303545000d10100004144405100080c054000f008400401202c0300517040100c20340821403400b220a6600c040204d4200109140c40a028274450f060304141f40b0480c2603130807140c82c0c080c150003030310300f2003924074047d25035440d4500c034058a040c1203086e039980c80c04c0000b0404407020300b244c19000041490708101461002903072000c414000101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 793511573 1250 793510323 793510331
    0x1a040303050901121508061605161e08120709080f03070f150504080c01060f0f060804063c0203010e22120f0216030503042d0801150e060310 62
    0x10703185141d50300a980c5044400e00112101c3e86e1698891707900d601c11f440f1203c0801c0301340321a0a0882c0644122002c00036400340310100508203441d80c48816140749800301112855144080015100c400182140c00f16800c005c0186e040c440f4006001e1030741d5810400340c6600c2011050078040c000802d40c1c203001d40c000200c0e42d6081d80c0707140901a1140040301c030844103082405101c104030860b400b50203200c2200008024490351900914602143c03486081516085d01e0802c2c0513861083d82c541d64403d0080030003007115003d0904039105461030748410144000c032054801100b0b500c105c0c4900e110740880e80154155410310ba4955070058000d4840990300041410130001c0110f15168070f0217282c0c0dc000320740c408005400780542843d18010107040180a00c103298811700b418071458a00b81c94100e00190b0419090004024111900340320200603801c4030292100c0c03003420b0080c14409410045d00200722008460019800c2c03000340e802401c0c1601408041151030b4800050510118a007404041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 793512823 1250 793511573 793511597
    0x91103010507021b03010b030f0d2705100203070f080a0908010b100302130e0c030a290405070c020901081b100e010f090308121914010e060102031c061a040303050901 73
    0x61b004007072600a030342e01801010507101880c040810000c1600b00603446522130803c1c4c04002c60b520362410b41c13030100106901c1d0740c00d104a0500b40c01c40031a00c4060f00440b031031b1221985410601401c1075404440c0004000317000d401207a488030342c1070002e2071504000d0203030610803400280c0c404001d80d1490201070707021400800a88801d101c0b18020550091440c0450604408401c019401140c01142d05402d0051203020700c00301d00d101014124095500316003006140b001c0001030100a0521010010b10800300c0e0003680da1905440d008040700e04c01004d03562b10b00e45200c0540403500c922188600301100c5102051a001400c840d00c082003483c180da000d90040b1000c1d1180301c01a04068070890005c01e02c0d0620f40d40780041c0d14058038900d00020701c103051703d13108013081e9201d0420340082488040010022440d0144242d0703003008050050303a0403d5086404a040c0d1204101c043d001141c50b024100b0201d60301ea50307560361000650060614207815a1005011441030009031410020490042 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 793514073 1250 793512823 793512829
    0x150408070b0a0c1b06020c221a1005070507051c060207030302040b030103231f0207060e060c03011502030405090712060510030e010f270302030d050a091103010507021b 74
    0x25003009544240d102820380e1044c0d449141c0e0000c1400b400c00540709154000d042490000030a0b034007201007889030048c0110241810015005d001c802e010540001c1c0b6507502ca56448036081501c1481c1035881c192580001c2c2491407410500e03a000038042d09d180155404201c50032891240f59072f800001c0543d6520079072408400030b04ca01d03072044e00f1040000c4008010000000911111a07044464240138211a10b03d19034a51811044a00362070b070b004034540700c00c192036070003810205d0b01429000038080c0514046a0501104441c1c441c9050750010040c07101c0c0e401c002d00031541008a03c000d505160805002c20590040540840107114004880c0400341c400364004002030072001e0504140d41c035404a0140140620551482181d401c200f9200050f840754410080804041c496000c40c150710030850003100d074010942a021400100700110b048980740c003449000f030040400000701000c0da810110030110b02d81034054480d9040400f8040c00d03d60000d007000c11410903400700e1099202c84400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 793515323 1250 793514073 793514087
    0x70203090916030c02120301060c080403150605101403042315151504050103050405070e09060103020a090e060f06010c17090a0605160b1308070f02150408070b0a 71
    0x40254030024400030484200d0b00c8045080816145440c180048415840e00307a0302c4100788442012004024001080001d1051101049081c090b4880034582a200d441e20b9803001c0c0121110350301540c03604020010703401c0a9240846460742c61400c200b2003210b0940404880c44003a0000d00054030044802031030a50500c0580c01e400d581100300c60764144001d95405c0c0d407500444084401381407021045030f1b80d041c802d40d10500c8e940810002ca10309418000190014280908261128440c244000c10b0000101d0055409128403900500540d859407040020276089a044071001609110008940c00800902c0b90f1308040e80d0400d00c140d503514400101c503091046400506141c2a90585810300050140180800f440540795804040d490740001e075483c0c42011043e011000c4980c10310b1001c110041c074000e400161007203a4082c002069103c0c410150030005081d0340418601003400c1c114608450442140c02100100c107013094686001c0e20303207a629902c1070b090704800000310085261f01c5445 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 793516573 1250 793515323 793515337
    0xe04080d110d090f140c0d08031f03140c0609060316050c03160218070c06050a1803030b0108071d0105030a0e01090c081002031b0a03091203090201030b06120708070203 74
    0x22080001c61004d0800d0080d0701c0543c2c6040d100c0301c807041c040c40d607514804a10241d884001030610030341ca0320f0543c0e464006510041c2245480ca0b603800a4000c4e100c00000d034040194010710b03440d520000e005c0103035428103542c484617511a601c100000481b43d2290015294402580c941c156903a91199505540e5407058803503010080c00300040304111540080e4240e03421500a80752000048a00c080d0b40483c0342d006c0c1d903104041481c0c100f0500010701641c1001c4d9200300d00001c04100c2845100c0001d07000040224100c020a8450700f5400d06035030b00121b1640d0043d6185004440c1400c445d900104044406074003e040140001c0040d14034910b41c0c100b490030010480003008201828144450340502501036400b19000d40311074103180303070290f00949002d01c3e4420340541501e00e5034a103030280c91384049103d42c00e0640729203c00c004a08101041c07080c0c1007440c4c0b40411942c0f1203200050480350b145042070302c56030b400e0040c1041003c0042c50705910605504090581e80c443c1d0318142d1031401806 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 793517823 1250 793516573 793516597
    0x81b0f04060e1e0112020d02065e05010507060209120f1903020c12100603081822181203091118071b06020d060503070e04080d11 57
    0x2d03050000c0c0c1441d42041c000340e2801143c6100700703a42c0340d410000d0a00300706080a58407200c140b6048001d03160040080085440300030070201c00f003914030401010b03400210650303029020318916200901029041c42c116890990720507810351415012004a02e031320a000f014100400030426070300f006070039411200034880003080d1070f0a01c82c0c05200c1c0c994442c00507020030354601460615040c000c5c28003089507419070341900548040f070381100c140050030212600404030b0780700d96601c03440c44002da4401c110181d40101c0c1e000390b966002181c00034282c07842d0b85902b401400245d0080280204c840e44049008040110100f0780d94a000050315a85841d540060704010f554460050140e0705a0b11802d0200d1054210f28485800401044519044112084203414240c000548018841c1c011a13805099103094443c9600c030903161a801c0760001003030086240d540320740c14003591504010501c001c20319492951a1454150f44552150041014035a001500c0c1e240155498440e10b06480200e0301034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 793519073 1250 793517823 793517849
    0x30c061e06090b040b1c060c17041101021c050d0b041b0503010e2409090f0a050601080c030601061409041b05030f010905131e0501050405030a0207081b0f0406 70
    0x102d41000c002c008901d0018411403404160343d509061002e0b58212030205600302851800050b10707100054243c5180a070101302d070144d80407042205240c0c41d01e004a00500c541002303405a00006440e203a00d81030500054103070b05481c00302c0d0503441011501150b10100c000701d0704642e00070214019000c03d0320007800803c0c0f8403c007400640d5104018504990545018003020b856501e405031504000d0300020207804811398003940c0d21b00782601c030360781c06c259044100c5e401c4110340d1040f1410074404042c01c48441d000100100040b030301c100080510848110054582549003800250850080019001301004085002c6141313546940c0081000a100c070070590540c0b0701040000d1007540101c4540b5038851100300023044150f0a031050603c41ca540800d500c1c074404560f01c4094030300c00c42c880b003074848480c403d280c1c40008100380a80d1380038921520055490307055414010381410101e0f0407401d480d500ac030251031120010300302c160642040640755183d58091841c041405002c0c3d03500000950750358 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 793520323 1250 793519073 793519079
    0x27092e0308030415200702060a090e0a02040e0615120403020a0210030b0102060a14010b0904060b0d050f070309030c1515060905120a0510020c0f0d022404030c061e06 73
    0x10384c20702c0c0f81550900480821032025221a07400c507158800d030488100700c40510051005041a20003410070300080d050102486994041d1011810350440e14a401320b50081000c0207050020900190007010850710144280b201d156507a155004403440808030709142e001150500d0300901c800c8000503009080c4000400100304041d014100501d0704500503c034000c00241444241d20900b12102075411000d012a481c000502030b054100d488069071086d900c120000f0b500c51040000c00d584aa0f001c0c02050303500d844c81180e1015080106088141400d1900d55400240c1c420403035810700398040c0c0a04110440d04491030003e042c0e800440003804501080800c0e410303000041c076821204125002ea0520070b00200c865120416220f004000e64400b10181069001a4010f002c0e11020101115a51504144414a0182c0391040e00c800360b00035080c0300115120a4001d1035801c01806241485400c107990b00030005160810040c0c610fa41ea80300c00c00c40450400f01600740103081d440c00b4401c01e61 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 793521573 1250 793520323 793520333
    0x2f092b03081e090a0305030601021609140705040e06130f0504111009060e1e0303041d0c0703021b06040816050a09060b04091a040227092e03080304 65
    0x6000d076002c500c0d09584501c01002910380351800d52007404008003902e142d0800341c4e41900c0503000a06624190700620102104420840c01ca84c4e00903d601d610100e6a4041649000402c450240803031003000070800081c07142c1110182c0e490b0708803000b610902d10714038002501d000100300303040606060030b06140600040c0004000c059402100c1201c1c1107482c00081c00042e20b5501d5540b14420229100710000d100602e80841044002000d01d100280c04000701400a070443d4000e07046900a17588540084856815200420798000c0d01142450314000716520060359410b10000f40d002002c415030042c1031561550000c0c1c4004010724421204054801120400109824001c8130302952107858005501d40183c0200c0045422200b4214034280c140f21b1a0400740c00084008460250704489a802a0704c4520041035820b00b08401d0a80420210781c080200c8044100300510411000d82800030034280304c4841e1210300064540700c11074940700300309c002d0081d08030351010b084030b20040b08100902c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 793522823 1250 793521573 793521587
    0x7060b0405151518010c020d050d02030408060c0a0903110d060c020f1005013c0b0d1803082a0301060201140a0504030f03020706020c0d032f092b03 65
    0x810440d40050f40120040d0002c51070b01074000c4100000c010396000214550088068135406030000d0400c80180b625a220309203040707004101000140d00c005030410010400340002e41e0810b80c003109503454440510f8009100392418007010308040721600204ca06660742820101400781c0c4004240720800c1c91820183d1102d07100d02028065004100f10011090707564407a55042e6030301000d60004582010300280092040104003121400d42c01c4541a0049004003151000f424041c0441c0e981d0ba25299005017500c000040c0c20b000710008118600000c0d400c6850a54041c0b003d0051800c0c17210754504540c2201c0c2001c030710031201c0308000000301e8420741c10740000701072030214803000d24961104641142120b504440280004117503400a101044c0710b034000b0075005015007000b5050480301e032051410660301407030b100c0c042951000c241c00a00003001e02d50509040c15421245035000c80703280c804840c4644a04144509003042042041640c1c2c1c412080c881d007450003444c0c3d071501803031501034801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 793524073 1250 793522823 793522861
    0xa0209070e061c1e050103080a0813060e1c0302030907060525060b1816080a0e16060809030a080c090109030506010f080613111912030c11010203031b07060b0405 71
    0x4c2c0e02800b4640020345004582c103c035440364506140040921007110340400c068161405403610983c084082416409604541d0343e541000c2c0c1000c1310690400c0c4840c240501500701414014400c0261510000c150b200c00c840007400d20b2030381c64880d05407400c08814401001131980361042001d809000d290b601c40e0019540542b00c0600020882c8161a90003004130b82021100030000301081e4518420800b0a420942d40070b004540c6100241d0841d0402c429800300002402c1d89a038100180c540c801900f90f046124100510b14111205000400540e00145120354900002800f40c4680e44540050f000961b040303070a0f0303122561100c0c0e107075505c03903141c3c4102c030f51900c20000031545460b41c00030142190f6034004030b0320710002a030b0400d0248045016284508c01d0b1084440002c0c0c4080c0c840c4259010f5100e5500c06520003554a00712440a0400881e2030442d030041c4100070510b200e1400c4070706801c11003c03080e6143c5a451800e1070181c80a41d50417034015042400388600d803540b400a080b04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 793525179 1106 793524073 793524101
    0x110a05091c060203190c1b0203070f0b0a09051008040f0c180c18030221210702010f030b01120216140604140a0209070e061c 55
    0x541c0480c0c4025294079400208202004203540b2000d0040002204e0410801c141c81400400610b89003c5a06c00d00c01d014a80c0401d40d60104858401013428898490800d41c88850000480c0c000711002008140783d0701c400306051811019000c20810355545038107442d6074946a11841124040d010f80e04800481c8005c60031429281d074070000080700203c003143d0403c461100400e40b2641c94011100164a20401e00041e03850741418916010880811103440200c80b0700033f0f003040002100b092031841c1980744501d0900b000c0010706513850007600c8003000c41540b08030a500f5030f01d801c10247d000440b0038459041a0f65558080c0c820290541d5401800d00416070b148194a0300100c1c546172154800d000b00420042a00000881c214518002d020494250f5000c105160382c060a44000c1c0001d20320742131426120401502c01e088100303000c14800f0980c1c001c1010042420701010b40c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 793345323 793525179 := by
  have h0 := BRFrame.cov_init 793345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 793345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 793345323 ≤ n) (h2 : n < 793525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
