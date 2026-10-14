-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3651
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:11.938+00:00
-- url     : https://prove2.me/submissions/77cbd1c0-6a2c-47ee-8cee-8803f53f651d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 656474820 ≤ n < 656654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 656476070 1250 656474820 656474837
    0x180f0102060114040f02040305010b1002151617040c03020301050703200c0c060f040303030b010903080a0e0a05060406110d03020403080319141302120105160509040609020703020d030f0b0d03 84
    0x3c0090020500565251040390010600009000303040d0b1080c1e0b0044400e552582c0d070003a01010032070320740c000344130720359040802000030030800210f19094601d8010300b4140a0304105420310991402d040072903080710b05a244c2032041c41141400c1c0561504480142014451484400c072990342d8002c0b154000007542c5d60104005000500c2002807080c0e08038003401460382d0381a4281c500e01298894001a808a814122803040d207522440801040fa0b400406103420a03050f41c5088420f05003010344954464400c40000c145652001c0090006041681b00c0040e841c0c2e0f039980e141d0610301407203104814544140401c20204090b02c0c1100d510110390307000890080c2c3d00d18844801440d0b4408100040342d01c45041001000304078010a030007030b0084440520029250f1000c03400e03540d08403850900050004080e80b81913010300003130f00d048031004001148446e03d40d10000d0498100a8003900180d0100304d00781401c4c3c0c0c00d84100c580d10a4010424841015080c021071800307030f82d03110014200580d84 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 656477320 1250 656476070 656476109
    0xb0a0c08090411030109050609040209150a0b040b0706150501050f0d06030b0a05190e030915040317121006051c0e0601030506071b020a0e0603070306060605180f01020601 75
    0x1241281c41c6039000901c100800c41c1c0c0c885075038189800900608905e18545400f0504511300301c03e065110f00d50042030704c0794580c1c0307006024008400c02c20b00d40780c00400c2c41c0c0340401c480b5044400791001c0d02c0031440c4103484022504040040d00c030510f18182134010007030014005071742e03c03000300d030040d2070126102981c2c0c00300c400b180c0c00180010750018100c95401d400344584c0c0d15040e00302502074400d20201c0050340c03016800440c1183c00401052000d80c0c003c0040f5102414040c1e900a29400919520b505081e500e4640c101d641043d0010045980c00010304c2000030200850826000700000b02841c00301c5081040180061050701d0580000390f20034111840764040542000900440b848240d802a5030750f031402d02e40e1030505851000200703544003640d80d4560035a552520f0415002032060840d54541541c2001441014000380d07054060b01d000400403540c80e000e000000c082503510ba650740c3c1d0006600d0740f443c41001034018454080344803441c0c440e0381d0000e400f505445103044520b4900d01c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 656478570 1250 656477320 656477333
    0x906040c050418021c05060a14030109020d06050717040b0103031b210e0105071a04051e0d020c090106170702210306040b0411030a05040302280c0f0b0a0c 68
    0xd80d44403c00440c82c01c20307081c001036056005080e00417800200d01ca00e40c0030400f001c4003520f004580352500070040000810107140345040c22916008040d0000407058800d402103a0b140300070040540d035654a60081c0310b41c03181e1054030345080e42022594442a8245580e440c948514184009003c0140c0c2e810301e0543c21350700c1c405141c4019440152001441700c05551107402c007401e0785021000c00c0c1008081111540a0800c0712901036008030320700702384d411810440481c507002410640741c904c100c19810ba0f051001c44c41380000c02620100034002a0800c0030024900206001c0c9540500d014400406c08145c00c00c1680802858000000c1c00a50300d80c0800c0380b030014500444409960044e048018442d0a94015802100240c0301401504080d00c09e01080e00d1490b81c10a5122400b040000e04031072107a8401500b0a02c248182c0e00310500e0b030009541e2145900207410b45a250701d000c481c00304043c0c2207009000700210700030b400c1000d00e801c078480581e024148804052106840f0140100410b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 656479820 1250 656478570 656478577
    0x60a0f120f03180905040c06050c0a021309020a080a05101413030e0402030705040608010812030f04080c07030b0115030903021216080301090905240411031c022a0906040c05 76
    0x803040c450b115420b51301c1035040701810003903c05841c0400310440106000784a0011107100c481020300030080658160702340440c507011802031689165a402c5e0010043e0303103031100d050040c6480c07801804040d400d0f051260800c41d001c904508e0083c42c003c0d102c00c6404815400a80c0140c0c880004903100c60241000e035654401103000310742c460700c00810880004c0c2c00c03102800039103c041c1c0d40d800860381c94442c555500d20600d000d01134035003000c0c03002400c0c204810303104584c414854008070342040c0e02209518075141c1250012226654034100500c030305501c50341c01c264070f5041840c050180000507100a5260240c1c0d03418117486601c00500d05913040002e82030201d240380d0160741030350350703680d108121b40c024510100221018010010142140441d18036040300c0b0b403030340341010911707074403250b98903210009541802a01400384209080e0b009801440e401e40e542000d030041d000184010340c2c108081180042021070f8040d164100102d40d0300c0d00a41c10b58803d006840000d08842c8081041e280d81c003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 656481070 1250 656479820 656479847
    0x1406060f2101090e191e0606080325020a0e360607021605060d1107110a0f03081c1503150c08060d020432060a0f120f03 53
    0x30340085644581c181014034032412520403c0301040f03012200d020b03054880a14019488244070210500404246c4003610102203851070052a074a215060342c0b803005803141d55111000c0340c7c001092400d158281e405403820003001c1050340481c2d0141c0d940c009480382d40540120a501c81c1220005400e4100c1e0300c000d080e48012034555024403010410169082ea0703035461480209020f490b0102d2a80c1d0300004d000e2041d039101c0509004014284800e200340d40d042400c40501076a21080b090b051620b488008046150040d8031018900e20101d05110906c1125444041c030a5900307001080418660300546900f03c000811680c141e0800101d02400b84c410801c180f00381a01925000041080580444280303d054000030300c060800f11034140c03600f0a0490b907654000810844400042c0ba050b072105862001d00401d120601624002181410a0f004000101074a480007400039500d000c0e05007600401121032808403541c181032080d4440b4600e0b16000b011030001e01d032801c040500440c0f01040c0f01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 656482320 1250 656481070 656481097
    0x30b1f0c020a05120705040b0d12080402130515090115050d0b04021909090b0904020a05121c090302030c0603060303040e15030d121a100f03020d02030405010c0809011406060f 77
    0x501124040d2a580103100c1c95201f0b42c030b0900050f00605002c0071420300070b600021070100b0040482e009030b84500b80144200e911102600c100840d4681521441e80640c0628080c80c1d128080304d01800000d41c01030300400d0340a0000b01031080c03020350001c1150001c01e505440807503140030700c40100e000b901601210301110414104132803100c9034404000c90840702c28110500070300030b038071007482000c04040e90040d421580554040c40305003481102500c000d4264812079980700054000c0e501c00030341c549a400000340464008009619003005200300000c800c031120340c51405c00e240001c2d07480c4141d2044110009400c4005640520442c03203803549450003038162003c003408108020064280c01c0c038154a158640ae50300384c041a1690b41c0550761880c00303000c075010200009020358210761031701c45200405d038003017110b4095040c40340061809544120008504102111000760035110300030403121032a0f1600d2110f80440d030418018a4100d0425600709503a44261940340d00207110704040c0b040103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 656483570 1250 656482320 656482339
    0x5251808070e160e0f0f010c02041a0102100212130305040801050423060915131a040201140315060d02160c0320011d01020717060106030b1f0c020a05 66
    0xa0181d90211902ca8441650243c0290492007401e40707080190300701d0b158020a101d1407080d200c0c2464110196608414144502ca15141d5800181900e51600100d02c100c4007254101c1181e5804201104480440c850300398101881e400740c001076403070001d0100c0c4900c11540c01c40e07820b050281040385c1c0a020b00000a00c400c0c5410b040415184120300400c045a85070121041c103850b80106000e401030560902401c0c440c030015204480b1610083c00d90011585036044020024103c1c10448400d94000145e0042c545000e00001d465000d2010841010820800820042c0a1200740035520400d088030b020380c90312480042040240105095041200300c0c44680e0418402d5070a45181103d110b0101c030103030f0765200e9030066034112030340c0d8615001c10346c190341090301040c207120b4841c9050010f1040313132810399a90501940079540e43d24000d8080d04640010701c440c0c0e40c513003d64001001c0a42e000c00407088200c1201002d4543c100328001000b01c030300403000840d920140f4800090100809000c203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 656484820 1250 656483570 656483579
    0xa0f0e0f1c0c050a0b0702060c120a0506040b040c08091501120b070c0606261204060e03150c0a0201060602070b0904050702100e07051e010512040c081509010525180807 74
    0x200380020b1b0740000140c4140d90005031034284500480d1f2143e16114203440c003a03250384440740050071015194a520035210040320f0b625490714071603601c1c1c1c4000c5594000f0182000b60f0b4046c00c0c00a03600c2030301c0103d602c40c0e00502141182c0c42e101c2280950040d10b0201e242d81d2024101c44080700c2c10345c010074440c241200001c0131210603021b040404412608a01c002d00c3c008449562481214105000e20000b80030400080d400350303100c0031482c0c0000e0290380f01050f000703006000d1590115240b030289000071800d809100c1d03091003203501500e10703400102003c03406c00340010b0090041d0110319101c0e503203542c0066200d40c424800103440600c00101031020700505800a6128034003806458000e801c03284078440d000b01e8803400c2d81c5601c10181c641c21310f028018800b9840142d00100140d9410090000008092108004c42600d005d4680183c0c151400c1a1660500799070b4013800860b1500d00c00c0f11540c03d107502c0079105d22075080b424280114541580c030540010f1880a501206141c02034141c0041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 656486070 1250 656484820 656484833
    0xe010212041202060403021c1b0302150109021303060e0a1704080f0c0a0909050a0b0109090b0903030402010807050d060807150305010b07030e04091106030a0f0e0f1c0c050a 76
    0x5000310b20550702c4041d101c4010714126500c21048901600607070121030192006198044075610a20285c60a16191500e079080342c2070314503030700400b10011f81c4561311464101200030000f40c05440d22070b40070361500c482a881c6100c100310b1804045c10980e942e22240c0d6502200300980301c0c104c0d521580c03070b030789011600550100903081407081c2c04080c021442c0003c440940459001c42c5840c00416400d00b0b9420845036900620000100329414030a01d0038200120740403545140c0288882c0c840031071000d41d10f01d04800c41038005400c0381d401d9841031044c400107030707080300c50380341d000c1001c2c40d0603030321419811003940103041290720100443c011000045441d00303103402c00f0b102005154034180440d999400303881e8194400c5050141c0000c41c50504c441c02813405030400d040840c0100e582c0f4080060071800136000f917205a504010b0260f45056000c0c0400c80350185100b41c0310810301814004494018907500d130f0000045500b031102c11482c2400950340610314000856030000304071800140f00d40b45c10f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 656487320 1250 656486070 656486107
    0x30402041a10021c032a020f161d010506090906031903080f06030a0b040b0705041a0705010608060106091701060e070210140601051b010b04020c070905060405040f02130e0102 77
    0x4100c020050904604120300900482990782d0049542c6036403400c103031450406c0400307100c0a0104500030f0300e11118124000f08145400200040110315000b032a06528100c695007003240105001c10550040006030303034403020741d498900e056030809110b58512001a04150040b80d00042c3c014250034840c05241c0e11124261050611400e203000c0c68543d181055500c0819603002400f41c1d5001000138000390041001d6604692181010b03428aa11074546070500703400b85180b441c001001103104014041c090007000c0080c403482018002a5060038401094070b81c86020b104940c01c208401d13445052001d42c880e0009201060001c03645041000c0000e4482c038160a481c5446c505110703071800002640d0740ea150042c40140c40e85494201564000c0d0200c44940d1000705181d5a281c501c05132030b031201c0c00208134010780740380035041d41e90030442e40608641e40603203035500403442c00f070130080041e8035044510805074040341c1c0080210b41c203414000252000d420b820000d940045140c02d40c0c0f070340c1a41d61 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 656488570 1250 656487320 656487343
    0x5040903033201350f060106080717100501140408160503060f0c300903040620150903070f0f03030612020a0302010f050d060b030108071703030402041a1002 69
    0x300304407a680c64290264081220a120792819200c165044c0b1500b960022080b00340e800300159081441501c0c81c09040503802d9000202252804040002e130035807004022603201000030700440c1a017800c0285c806000102d0042505018604c00014000f00c1b908060360020901201241d500c0400b60f85080d6040d506840f4050191240c0b00c04240e0320980304d07401501c00e640c40383d4064140001896440920912060003452100c15040c0b07240307201c500c605000748202d20701f4005698a0f8545940205074003403d00c0c60381000400b045171015000d1020231900400c0224910b81122626203a80ca00c0c114440c100004244c881000700c0c0703008200340c0d810703e1664180241c03000c100381a9100e5088070082d03407100009601490031032052005600410b8446205c0314180307801703070078860b070341081c50308070f40e4a5040146401c0c00031004200c044010401140507011a500035244090102881a030302d01001c0c000902c10743d110540d5406007011100c802c150400c000380780341c0914416003406034442d02440c98 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 656489820 1250 656488570 656488661
    0xb04140f180724090320060d1b020c0f0108130c050310090c0e043507080c070501050a0923130504052802040902030c06070b1005010212040504090303 66
    0x9070f4010003401141c0501c00c4a0304034035a600032402003004c061242d810160541e41c080818000c0030f44582e00c600ca04c031205000c6003020446800e0408010303140a807980c075542d04c074a400112000c00c50340e011845070b0f00482041034403102c140203468009000d5031280c00603074051040100c0008804000d42084003124042d5407280e440783e40316248810f81c1c08041b507002c0c14000703080b0071096000454442c600e40f0407411001590352140c10310215402c0754004142a40c2e2044045900c0e40e0800007840002c0c0200400d003449890f1214040303020300448114031420948141241402e038028450a1030b20101400003400c607000901c0c28402c0d000105800e850946040c403440c1044c0700d03500c600c803d0030000664440c402c011103c03010f070708002c09000b154104a070140500041320155403504c2c0c018100c8c1c10311074070300c100c02d07460020000440c101e81070703000c6da04661040020f16a016a07590403241990001c0c4e40205107490f090038150054440c503000b00c14185103a52100648844001508000b403036040c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 656491070 1250 656489820 656489879
    0x90402121e10050d110a080d0908011a10050703020a05030a120e0604020102120a030f02040e2a120601170f07020c19050d0311120306040b04140f1807 66
    0x485400d88485401400e402101200000c1c000ca0040f10340b14071652001084850700329101c08019023446460003500000c240d0411080c081001d0038000d2400609412409010840e8000c00041d030650035951040280700000450a00341842400700000b2103400904070795a03a03c098400901d503120219001100d245049101100008041810380c000c41d0140e0081a03241c41c14500d814880e40540c8050003450b546503402e00708e08010f80040c2004110380300035440146005081203850701c139880d299040c20b500611030f0740c8003071351044240c803107004c6484070200c19540c8000041e00d21403541340304e28034401c1c0780d101000961784594640c9889606c841d4240ca900c45c08560a010158901c001421800c40405405001c2428404c1030241d845010346400442078510142042c100310306d01c807030307551600000400c100f0241018050781307202c198240e400300001e49440540110302080907007400802000100480e141c09102d102100c06030380d601c42611011075580d0b4541e01d800b0b180030504441300003101d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 656492320 1250 656491070 656491081
    0xa0f0f020c03070303080a0b0901030503040503013608071406010923010306020c0106051002010204030303050c0705030a11030c0f0c030d02070b0a050306060403173c090402121e 78
    0x714100307207607520180003411a1400d6960580f5480c80c01040c003041070340d440010911640c0d031081000d0086001c1c00166a0312070800d0181421744104400e240383c00c1000300441207016000700c0c1c0c4654001310315681035440f44041c2c078025813144540c180141104c201c000c1003510008000c100e1170f048a01804c400c2155000d0b200d403443d140307040340d01e8088500414030010008507170b04e030700201020201d41d400050a0768a9500189110107007040c1300c1c006039404078007071003010b8140c4140d036084614400c4841c10008159070b219601c0c40341d83c10b0781e002c0010200b0600c10307074a001c2066070b1800402030140c0d0003c1040090090f40c0b88281c84d00340c0d00c42e210788205020b41c1030011036224182e40a10380c03020b07d8030020480580303460380041c2c103841e000f031001c00000003c1145032864500019003000c0c800d0f81e44000c21482505c590380c00c00c0c48001c40444045034002304005000303945661740c003201010707142c142010000300240946800340c041880c2210400192801c0c10119100c814540c0d5038070b03603240e00d51 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 656493570 1250 656492320 656492323
    0x90f0105011d090a051f060504020306060711012003070b010e0709030b0705071209171f110705030408070314010605010807051b0f061509060a0506030c040b0a0f0f02 73
    0x2c2c4105010301c1411103441c03441040d05000d003548102c0380e00440e4442000c6680b05441d000303e00302d001890209400c261001c40700a0300400000b8501101c0035810b41c01c0070310014a451080c1d503001046148030198052403030b4015a5480491007400c2c0100d040d860031020310395100e51001c68125104002d4800108081202c81c18840c01043c01d0f40c0c609003003038210740d60044680700141105041c0442800740000061900b266080e9010300359071900421b924002000708692004c0d0b9185000350031245920801820003803400059882c0d24602180a807000b40704850140b06621002d4214040010041864440082e0404c201c0b485018090782081c91814242e00300e800601989000480700310208601c00e01c039401a008100820f03a604c4420700d1503803650b42c41c0c0f0707892240d22450b0781c001c14100001980d241d42c1099062000391a011070790720780391000404500860250510075903001c0013060581e084c1c40c0c161009000c2c00c4800568900d030700c00c00585201d0756001040002001038040c140c039240f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 656494820 1250 656493570 656493581
    0x120f21030105090601020a050f0a0c150f03150305010213030c050114040920030403094b030c0605030604050a0603051b01110a0b06040c0519030e07030c0e090f01 71
    0x1400420142141d003454200014143c000c1c000074118841c49a80b81c02040050041001c11282180207110b50002842c1c070090364200c41d031107280012400c440d8004100e0300200c0340a149440c0b4035000480c501541c801e1035030b0419a82000e0455031010403401d41100c001036000c419a0701a408843d903095a901c01111b01410705110781464541c103105c05c2001d0180c0f80c000180b00c208600d8820544102c0c2c0c4188595600100d80540c00689c0c05001081010400106124440c04070764021740c034130840802d42540004000c10700500240c60300660842e1320710907110710001d0341e40204801c580c0e6540c0c0b00003d01c15081a83e09911507403402002c20f0103400c082c0300303000c00c40382e112015000b9000000031441c899525400c805060103130030004403030559000c0c460b5480c241c0c4a0200d045640c1080d07c00d000884400320401e4080c01000c208801c080403405000c1c41d281d241501d004038140100c034911a003051880d51004041d0381841102090604a107049075124541289c01c82e03200c3c50a01a61600782d03036 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 656496070 1250 656494820 656494873
    0x6080c03010b01120f0b1c020916020304030b150d03020d020c0604050906040b0d0203101d0a0b391c2f1b060402090f070504090e0c120f 60
    0x409500e03100135661029088074030341094080300065200b5501d0041010501c1c00b549001c00d4080b44140e4000318903108045a41000ca89a00280c82c214101030196803840b6902001d04500c52a90028425521004180801480203880141e8043c0b917890040d40d20300c03134010b80c50058000c00d8203042c610704241c0b003034800f280c1c0010020440c070313251501030000604160300942c3d08840300b041c0e440d02580b0200b243c9094003840c1c1e0360014030444008880180c245001c20455180c3d00025801c40100b043c1703108090301700c401d0715203404892403003211030307c202c450400d070841515550202c1e54100003c072001400820640001107013060401070f2070711044800012101c0c40c0e502007041c4010308409400811201005802c0c4541c5c41c203a4551003492032680c00704c40c0d058095114008020840c00c0915400c0e80100c0054106001c5081c03950000c2d020b80540d014170550f5035a0390380502261003003000b951112072405408641c000c00c00c0d400c40380d200c1c100c12107041564454040310500a0407551101c04065 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 656497320 1250 656496070 656496077
    0x71e021806012f010920040207050607030b061c0b0109060c03080a0209040902131d030a0504120c2105060714220b0a050903150105102307050106080c03010b01 70
    0x2e1a2024103900c41a04106105200b0344540c1c807010144209100c0e8001640c003e4900038150000b880e0080301d001540c40181f80164010b000c4000004d100213580340e0004807a0401040032000e80c000b0650700d018000d28200b0340180b4036840349441c14035a1055226040a07078810300d00d252101801e41d0310b01c040d0200240080c209200242c980a8264040d000d01d15000700b0200b0030319016000200c07181ca44450304599645d03241c030460070403101d401e40702c10141941009182840707417060015100c0d01441c46000041c0100880c00f008001b1040803000c040e0801e1103054100260129402c3c4900144442c11103161246002040d1500d0003034004c41c89580701d8400b03030b42c505070b203001585d034465141e049002e07039848159074049800328884020344104140c640d40c69440329401c0d01090326103501d44094042102c2daa200500ca9034035450800f01c044032150504c1c5114108500c458075900704858880a423100001c502441004010340140040380c2d020021241c0111a030b1041600702c0d922801400e010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 656498570 1250 656497320 656497337
    0x70c03020c010305061f05041424030709090c030209091f0302010c0501020c030408160902030c1b07091b08090f1e120a030207050d091a070206071e02180601 69
    0x720362207600b0855100e41c0c05000c540c44d0342042000c0a0b80b00b03d8154140020940214041c40590429110b10034180001c803a9000d28040f4510340030341c02d011600003c1f28243e8000700089420380101d00c080d00a041c1c501c030402115988004c010000d40107000058072420424000c00c88000c9401720f5003001e03108088030310f40c4a51641c1d00654408287c000c045600e55000c1c400e90003003c10030f0003d0001400c001c3c018008010850390200c40071219500190040d500c18000d10010030402c20944084191151696084a1001d071010741761400586c02107500ca82004400c0d514410f80c8016140307101c100d5141c010194498400c0f0985902090304120b1180d84080800141d40c4800100c500f08a8180410b480a800c554100c013050740e4840984400840d4000801703e080110400c0040c4002c0014075058081c45e040c0541400c8070b20034908040000c141c0869600c0a540d00c1904440c102a800030b107074140ca99103030222000d0350003101c00c1a40701d801c091484440c0341c0f05000c203552040d81c05940301901d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 656499820 1250 656498570 656498593
    0xc0e03030301090c1e021e01091a070c240b041b0c0206120106230313120e031605151603080a06080a05010f0e01230403051c0212070c0302 61
    0x501310b6814410800010201c40400c1d0340010084883e0249160302504445420a10701a0703a0301c40b0180107140d1381e161080a401003000341c002d45511029601b1452001e4481c10001c41d03102400e00b0780901014407c9094203004640d400c8890303c4400040b07414045003589004010446101d5a04112103d00501140d02c84070700c1a004c07203001d28070080c580d82c1015118417805041035002d800c440041a0002031403540c8280c40901c00940240d000141841c41c070b413a0781c0310b5001a030441030003030140039070040c404050b80c010740c124111a413020381148c42a5407850810b900b001000d01c40e09006242411141c028041860100d80b0040d0b100240d40c1144003030b036502111103400082034050038030f0751600007140d0100b0500c5603940c12070144001181006840200004903440304110340e29aa1420300c48004d40d100707810f01244040b2500c4244c00c2140d40307a00381a00c5a110b007030490024002c460100031000603840c0c1c068a0301126050040340c2d16966003106540070184046c000d0702587c0b2a81c1c2164 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 656501070 1250 656499820 656499839
    0x22125020103021207050a02100e25080f03070c080106030201020d0c0c1d0402090105010306050a120602040504050108150606092d10020d0305060303040323010902030304030309090c0e03030301 85
    0x8200610601d801481d0982c158400d03c4440e00607560740700006c4001072030300c280a604015144161074080d100300014036201c4c00e01641d5400c1c0c4001c0302c41e140d40c0c04500285190a00c10808000c0003110140e5401116040040307850750b102d40c1084643c201e803c00c011624800500c40d240541758180c0060901c100d04100a0b41c6004000f841103400c0d00d070020002c2502105418100203e038540307807a41c0301a04041c410825807910582260b0304051412100300510703682c00c20b0307901c01c690f40341c1c13480903000000e03041110191081c2c0c0c202d80d41060801000103840d000000305102000300820880445403100004c01c0624400d90621540c41582c0804004140c1415100003030401c1703000a40c4d038200c0c4003080c040390422685180000140c0c014881c8801e115815000d81035001c4002ca0141d86031508650320b801041c04403d4103000d5031412051591000002548080710058000b81101d413629900c1c50f004200446900500c40ca032406d21480362221030249031400f0310b0034401009141980e00381010003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 656502320 1250 656501070 656501137
    0x290409091a1501081003212615130606050a0207082d190309050307052403101215060b07170c1e07080106150519120c0221 54
    0x1c03a817401c08200040061103800c2c800313111036005d42e4028a0303400030500c003500c42c800700d4142d640303400700181c400b100c440d03550403010354020145408080705500500110713007501070102c2d010b601a840c06202056058220b8040e100c0c0ba64a1340c03c03686010b8580c0d41254580541003041c4c801034401410303e4003401c40c00401424144c00346c008880e441902c644005074040014503081d0040703003100d54280003608050000802911b01610b40800c3d007a81a210442000702800440e0a11100840400c003030700c4400c02103c00601e800140807034110a9420108003c00714185001d000d54500f08001074842558800c1d134054503045282c04042080600b8a0200d030b0344810301d01842030041d22410720700c0340e038251440500780100c40d004080f5242844ae1150031284190031100c10a0402003008400b5940041118500300450041000c0082260b200751410152014515205030a001210241da50300080e00780003000152880140400703030a13910b018034440c0511210800f400060040304148426445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 656503570 1250 656502320 656502331
    0x604140904030314180d030b1c0204060b07030f030513120c03050409110c011a31020c06160801120816020a06080109051b04290409091a150108 63
    0x10a10304200309062944213003c5680c1c081c10181d022021175150000c21030340000c0a410300b02041020f10100009003081c924060103808040c03d042c51000310344803504040b0041020380512a15480b442c58094444a0403d441d040024501800210307005043d03100312141c0c54000250401c84107600d40210b03400a0002001d5050110130030001800d510341c3d114019441d05503003615915142068030050130b4078a42220403500d604004182c481559814804989444900749001d0500c800082d2104d480110480035042540c404211540800000710b181c5100d07201459041000c00b00b40003095031045001c0c0295403201c1c00700182c141c00076211030028107010080844410107520302d680020300c2360b155904030000140c100b0004016051060003820381080003800c10210010b501150781116005512030060b204800b000b410000e051110085246030100780d02e4150341c0c544698441c0e0150601800131035501c003601103100d01044003150901d00078200030b0004c021182001c0011250140046d08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 656504820 1250 656503570 656503577
    0x1b0b070c111e09090c0102061f030f0609060e0105010312050a09031e03140412030302070602070b10050a080a0c143609010c0c29090a02030c060414090403 68
    0x40703080107555095114042003400c1299004441203031000e014500c1c1014240b074085500c2205040c90503a000700d03241c0d078040304001450039401c51180416100c4402a80040d0400c21050718007000c2c41440d80015585500800c0184100050b0151890072a2003d20003d0801c0410700e948018540c882c000508203040580fa001ea000c5803681c85150000010400c0b4640056a804d0198105034110401803500900c60700b62606052901803418403614011070020101355000400c101000b10f43e50550350240d812145072002454542500800000c0034015075125004089c2c0005600c5800203406d480c03a6400643c0c0791308545400410480c0012540170340e90310411044003150603d0304a10b2529007003009480e060249060350420050040e00074147c00030303e9040030b060120054010f40300900c116400501c0407600c00c842c00c040350320074007450519041180d1a6060011403030000582007c1140200c0950388000c030900d0800c02d19100e0f1b48070303070f02c030302d80c0d40c40076603c2c2514050888a5205000c0d05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 656506070 1250 656504820 656504843
    0x5090901020f0f0d060e10150504080a03030f0b0a0f030809040204051008010603150608072001060305010608060a09050601060f030b120105041203020a1d040b03030301030507061b0b070c 82
    0x80b405032a07040151040e03104a80820b00b003140248600403080213001c0c4014904c401e0a01500c400c4110380320740201000259045810b8052a200c0c5080303034010b2080d04150380200b0803a03c1c2c0203002c3c2503012460003001c0c0c1400060459490140c0a980c11210402c04400c003180c911355034a42e403608803802440d4801d60030700c80011507844000c514104001a6a2144440c1d8100782001d41100c4219030201502009104240040c90304000140c0d04107a03681440800d030614040440d8000c00b03045410005035003040e00000800005400c40740981d0890400e607002ca55031440045c0031103016074005840d550020300100880381c080c040307166140805d843c001c140200c2c0d9501040140c1c2c62115000c1c2c00340e555100700000c0c00260030540c40f034040c46240640ca05540b00100a000516410b034040301d000c4032084142c600d0350b40d58030084010002800317a071b07225030707607820003036120b2606105080c082000c00089840f00341800307850301e640c19809423202e946515194000c8030501000705003140c0c80480c50 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 656507320 1250 656506070 656506087
    0xc08091f020d050403081e0c09090604110c01021305091308180a0e0411011826120c070605190c0201210509010c170726070e18100509090102 62
    0x6008644c030960003504c640c1003a051030810540081d408004c2808912410020300500d4085031040701c40328681203802c61059181d4200117002817034086443e560503040010051690001074024002d008003085074082c02550310402d0100c4010b0480b01000701461042e1100300080c10140904608083c03003403144140c0209001141189419400007030a00f591041008108001d0382c1803000199005e2805416071070044100010028860040300c2130900e004c000100e01c40452250003685440d01e00c200c0350041d084c1c00c401402d0354820907521083d401420408540f4030300940031607074823031a20741c2004481403260342d0484540062280072030401c01c2000e02e05806121014107001501c039610300001d41800c19031411800c4a030800d01c001c0c00d11000915a039280f1040c001c0a982c172104508041e00c100c03088081c03c0500f010500e1200440b1100072041c0a065507100c0c01c03d000984080d01d91805001f40d0728151007401c44100e0302080c801c5000c1d4014011802c00c0300c030140c7c10034020000503041880342d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 656508570 1250 656507320 656507347
    0x106080405100507051213020d2612090f0a054804060f080c040515030312070801050406030816140703081c0504020d06020903071a0d0c08091f02 64
    0x560311390002a40110340a44036002408100703402c009500c101c8004050203034080360401d02a000003070500313201042c40d4116404c0000a125801916401e441c1d80c0d110079415060001c4000c0d1079105040c4501422191203407030011700d00c084a078103c0001c1c003484000f40d58000b6164400816006c030606141c040c141c04841c0c064494034400500c4000445034034041060004490055000d184140c2c48a04101f081000100303a034003044c00207941c0894141d981044500161042e41d1015426110004603800c83d44464611a40140915900d002a990740e800400c02651601c3c040a40440001c01446100d1811280e003074510500c25200e0026048200c4015070801402f948140c40200002490303020008220400d54854100d402c0304100e1814a40c010601c150011107008145130780c000303800803060360104200d6004007400700d9401c0545821440840070b98101d9400b2001090030645281c103000c0c000c8000724401c8035084003d0003402d120035080d41d80c3c0340500300901035a80c1c0c01c000b1410100ca1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 656509820 1250 656508570 656508581
    0x102150408091c29010f0504020c210310150f0e0109050907050d180f030c08120703020a030b040b150a030e060702030c0f070501020c090411040e0c0307091103010608040510 76
    0x143c07980b10031a002e950766526512480e04d05100041141c90014007888100d141c1405c1580c0c03041d54010384030051b0300140788c608110715000c440110719811011040b5a4070f074000b90b100d02c2090002d42c0d03901e907441c032103014040c82c001d54240118070400e124a4165103d80e112801009051501e010744a940300d01080e020b2034180c070f60b00300141000030746400328002c900800e180c82564140bc00c0e0004150f031650403407044201c400404000250b8020002e01c104402a00d00b0311002780a04081c0b41803144001e0005d42c0002110b201003820080c02c10000d1a140c03046403031840012b450540400c485003840102544410a1102410340d0384100c000d8007001044803911031041500156902c86a9001003403800c00b0401e0301010319480811f00380400c5c0d9000c5452084205d094820b201d0b680c60b907141c50031001c0403000017a030b08145007111140311403000180120720390405800b900c440b9501c0702e40d94010743c1c1b40440280880b41c41000104915842041d40030352080c010401e48580303c800400d00f8040e141c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 656511070 1250 656509820 656509823
    0x103020904150f0b040506040905250305040b0c03310c0909110603010b0412020a05030d0305040627120306030512090a170a020d0201051909030606050102150408091c 73
    0x401c42d580034400340307895140745005000c40e0303a43c8900340303450080010008d21580c0aa0707401c241e2980c0c0400c0311000d25420500d84032a2510074980c05101c5140f000f00100320032a01030f10364250f01404a4400101c100c101c0f8003031081050400d1240403141c5140f07800054502002c030303010a9614643d40855005100076000d49900400410202c40e90f041441620301003c40140c482d5a0800c01084142c21060031601150030084130ba18144c0b8241c0002400f050307003a403286425001e100944141703e5455031001d4481e038032610342081400300c03108442000c031310f544d0521030b1305020320041240402c80c040d00b800c0455809140103d000d548942c4c4040c02c00c602130380c01d601144000300318032940e8604500e001014040e4943d165030340d0454201c01035a50365100720082d0003080c1d0411110203591040d008c03940d10030090312291400c05484030340202650210b100036540700c0e280c100046031035072010440c2c0714520104901e90303c0700d48803911011010391111a4090b800180e16482d030003c80d0382c41c0745030341d41203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 656512320 1250 656511070 656511101
    0xa1409040e070e06040b0102060a11040b040b0901030c030c1b140a05030d0b09041a100308180f060408060f130519150501080d1103120c041806030c140103020904 71
    0x952414061080d030f49806004144641d040044464040e640020041c0e40000307840004110345112104d2007400748510340103070364a8000040c011600103000d00003030207c80c1c400e90341041000035003038044007240e15040c1d600c0000741d480d08807c0e120102001c10390350014043c40f001101070302c0809040d8074004080004446680010071154141c03003151041001102c0140c4481c4200d2803d51796a172802c0c4a030300d115000c0d05030302d507010031403035200c0302400805941d0000a107546c030081c82c40c00b2101d00c031003540e50611038071400d02800315070b042140c241c400b120920401001c86032689201c01d0007043c401001001c143c1b00c2128014085801000415070001c169803a00c860303012a4100f036172403040c0030f0015404050a01300100440c440024085129640515224090f451354520446c02c602c5240c0321064281500000d1105402080005000321039800e441605180039001070b00091701c005100140103820103d03020407807000e819000c43c80c22481450700502d003c84140c00a000c0300c03110040207400c0c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 656513570 1250 656512320 656512333
    0xd2304080a111509100807170403080603210901210c0512010801090c06030203070c020a031a0708070e011412180708031206100306082a150a1409040e 66
    0x181c00c00065002d10b40c01c2112020b4641a520350220ba0412041c0e140d05d02040045000128124400c4100d060594541c0481c1203541c1850300b001040074405607502d030710901902540359112548008411000c1204000e060f0400c40d0050042d1010080422440c02d03003c020541c0310244021841444801c0c1029202c3c151260310901c2d41c4010110140c1100c5800d070b240c0480540424506800d000403521680f80c0540d0f0303a038540004071041003034900002d401c00279600c80841046a045004002c040d02c980e0403240d140d40304030b0101c5980000b50b9070280814144130001c2c0107948541180300d585801054598680040b0100511241404980911000881107040c442c51401440300c10300609002c00298104031204400706160403018044501c10003c444a2030f040500980141005081c0310054a08080d940c0341a1104070351a515003826002ca610044c0141e0b143c11059070f424401d410104a0600e00120300c192204035502d598100824070a000c02070310780e034690103044400003030080a82130 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 656514820 1250 656513570 656513603
    0xa14031c02031c1b050a0c151b17060603041a04171804060e01080705010e130c05070507051c14011119140304110d0c090c050301080606030d2304080a 66
    0x6400130f6185078040000402000c042a40e102c0058601c150300004e5003003040041e200048020201080310200c003000070500b150040340c00c6000c10307200000410780c07046903a0340e00b800c1003540d2104030f030300034150b1140c0b4890a07001260109066841031040300303800016035000c031210170681c000354104e040209620003a02801d0425000b010028408011002c149505100701d03191140e5460080328100071640213103003c20b9031350502e250b010040f0104100041038083c0d00080c4541d0102c802542c01c1d10420304001018140321209180078000b0440c035400c508103a69030101d40c03240340504c02415640b038045405115141c1c20050040800c80e41e0303034008914440401515901620f000d0010b040418030820000c6030026408980101c01100c222800c09218a09203011558903000010f1140c5882c1501a0f469000401035050303c2105044a2890341d03000101a51441c2c80445500083d80c604007080040400301c41164010b50425201402d003a11044120320306110b5542c150380840e041241d880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 656516070 1250 656514820 656514851
    0x105270c27100305010303021c12051005180601141b150912030114060a0c08030a0902090a090f1b0308070506010f0f080309010c0303180b060a14031c02031c 69
    0x402c00e12506003400b8030340c51600c02079212080403906201581541e01d00c80c3c84184602a0f9420034408114104a21f0030910300007500398115000b420702410204925188d25604d600d2010b10800c416500c0100c4240c031040300003851380000440d030682403d01c0e41115035004007403008c5050b101c40c4800000c850310b0076504103882c00f01c1c1d0fa049040c04510030001403000d10722400c0030071441842034400700d03520200c0301001c5800410400f005003c0e02004000d102002a09400a0702524005c40c2c01c102d058841e041c084045400741d0000034685d4400e05040e8001650341250391004000c0000c070324103032a50b2511036043d03a5100c240201d45503085000180040111070800078060306049908010440c204540c1c65600c0c40340d0203240e4144110440d000040500c40e410460b610f03100380380c0c000b00650342442d182004140503140c131803003550650f0000c100c01920701c21040c03c904000f401458401d403914507105d64501c041c0144811400b00300b0491190921621100e00143d00705607001130300d99132004442 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 656517320 1250 656516070 656516089
    0x120303050f10030f0212031c0501051008060d0605041514060913080703211b090b0a0e060c0c030607020a0b150109060503090a021908060105270c27 65
    0x603101c010b10b03000e1000c541c20785485440654150350741c10000407146152450340c007a031681c0400c0c21008182010b032048154111a04175074040e82c5880b081c1503030f003000f9540c60508071840c5400424100700000820b5154121b02d40060150105c2022001300c510f0090030344012241e800101036070b0b402405440d0900450095001c0d4141000c1c801042d203990300d65030a4440e8001c040d042150160362010405041c1030001c0c024451014200241a50032904003004a41d07080d00e0004a86d550a00041e001c80010440705100020380d2000122240003041103140c1d0403401d40c20000b446544452041358408000c110f0180280d5002403800c45450700d060b04c528800107000718402e00d400c885104413660002c0425003980d03000c1c00e00d56226a9009556860084051030280d0b102090804500009400041000546003400144d03100c9a803603e0178400d203c0340869128000c0742010444512210341050005d40050003170027014a044500b0407604210020000f45010581406001c01c4051038031100c3c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 656518570 1250 656517320 656517331
    0xb1209030c030a0c03030f090b1e01080706230f0c070b040302030a030c0201030e0a031806030504020d0204200708040f171e0703020303040f0807122a120303050f 71
    0x840c81c245201e4462502c0e400707415a80380500488803007038410180250465068034504c600d04000002d0142007403009804107a942820150744180d5005003000b04021841c10b0f40c0d18580148511840c0c500100d5440b0a002c4000c0d60049540d4889a4a00701c0384000701802100300c401941c5030390190000c5410f0a0b041d41c007100080f08104010801038401068040340560141441c1c8201d014900059010301890004010607001d440013100425400205034000c4011807103408003960313160141501120400d81d4042c3d406408600300c00010716040e0001d1a1b00b1001c400d462040c80245404010190072030a030840742c0c001c01140a00240b41c00da00c41100030103003001c14440041092688a403500341522030704c0c2d01c0c1c20745181c40e09001000bc00c04d40d0019940079048130b82d03403031340c8404414041c0114040d08003e03000703c240000e05044840c47e0815159008008c07400b500780314a0040500c0f9505c50604c0989400e0070720300040aa0b02c85502c40000d50203501c011034030340340c181040c448144000b080c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 656519820 1250 656518570 656518573
    0x140717090406122607050307030309110102010b13020304140d0e030607030506012c190815071e0219030201050a0506090c0f180d030207061202030103030f05180a0b1209 74
    0x2d80e58040380118507000703186107500107a514102d003040c19010704c40c8104500680903120005001003019810351044011900a243d200201c88010004a0a0790354680d19207901c1070700301c100d0300102a100ea00039600a44502c3c030103d1790140401070542000303c440d41d050b0109078252f5440041c0e041c00d1080543c04a02c6240070801031a200c00084c00000b1340d03591448449004c0504030003a00e40d01c046801c0c04400c000e01e080103070911800c1882403010790340210383c0341d4001c12520b10b02c40c000d40421a030140c00c4944a80c0110400c940c3c6449408202c01070005c11407107981c4c0c40c404419400003e240d5a64080e60001c1071610b05004010709603500601514090f035216003c03c81803058041c103561890810305070184e50b91946050440510b0388583c080c5900c0340d0007000c01401c041c0c001070850110380040d00c0d507115142203000100b00300e00003444040c010482e0440c0528000d84600024440b40d5103143e01d40e68010664400b1641d46003443d080b03031580a40005041c1c81030040510410b074071515600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 656521070 1250 656519820 656519849
    0xe04030207090c02190602090a0803030a09020a23060d110304080414120c01050c1e010c27090c20030c1608030a03050c0705010903020c04110903070501140717090406 73
    0x92004500300e117000d01070101d550105a110311551903482600042c01507404984d128104941c6c404001c000e0050100e10403101e506000403990031008000c13502109a060024004000c40d06206895103c081c4c179811140d030b00c0c4820000061948040d600480c092048240c0f918140400d240c0700080d801d442500c03507004000340c14104030700003519510040c07081c60105e8807080c0c0c8103071442c90302401c0136680e0501036400c20406006c800c158480104841d0070760752200f034404618070400ca100041e081301080040020000d000c0e407103042e00302d4144001c0c1031410340d07d07511600107000100c058601031060140c10005048490307260410449203186002d41086c03003010b1400d1203081c1e580c490241001305041c3c580300052803a1000c102560449500a0000d000b50000b03464001e480d21283e41e06180710341d1410305c01000f041c02c5501030300c20301c21000c3c00a168980c184001914030102c0d11040b08200b1004005200028941c503400011034000041c0081d03c45828004100a03a515600418621084c14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 656522320 1250 656521070 656521093
    0x304020f031c1d060f1e041d04080f0c0d1812060c0306031505090d051903050613152108040b0c120307121b0c030302090a0e04030207090c02 62
    0x894001c0e40c0c1040d541050420780d922800d840400443c0c00083c15803200b0045007030401025400d000340801010135811008803e500303c0049013a008900514440040d014148084104e500c0790090f0040d0040d40c01d50300b0034001000d0283c03950300455140310b06401480306d0902640e08000740100304c0e070360144080300490901c151341c010314400040c00f03400c103525991948403050081d0303c004040c5030008001001400301c0c144210180c0300555002e81c1d68401d401840701e181c1e02c158140da01c800b40007401800550b0314030f4000c9000c1e0001505495200b800048001d502840510030710b04000603918031450280d00d440d29862400001040c99000c120554006d84c1c0054000402c480a075030059030900d8079054460480e030300c0d04200f1b4143d01405075000007403101043e0070096010a0510005080c040c0415110200d6203401070517010310b0218803030f0402c4500081c029005040d4020018241d2042295078142d40740d40b40c40c1c260341c1500941c024a5044c420030318140508640d90025000030a10202c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 656523570 1250 656522320 656522353
    0x108030703030f0b12030a0807020706050d0e010f0f09050601090e19050f03040f150306060504180213170f030a080c2a0d02070608010308031506120c0304020f03 71
    0x1000c40007002c041e0b644020f15001800c0da8028154101d02601d25070000f0450381d1500e607030781c1c0464611004600b5200005030b183d8400594442075a01c940d0b1214108400c1d024401e02400c4001b11029865403a9142c078440107895108404401e410200013069000c1e035801d0280c14404183c01016200342003841c9005030160001c0e410710000a483d13941640c231881420064101040403000c0c042600000034005141c94803041450262030800f529000e09025080302601295194130407080442d1040c07000b0055042005c4403101d600f58051809860304d800701c1c51040544140d03420188a8185038020903400c0075040001c240101301700c80065103081c5140c1f00c05801c1e08401040682912000241c045040030500c0310f980c0340240f50704030f010003860741260340d035250114010b02d500103204202000070518850740d0294101c2c0e0f080700b207091550b240d50107240d9004802d1845c040d082801008580080107812400c540f16080840d8404e480e82800d104104c603407d550701a0700c1c0301f90701401c3e020440404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 656524820 1250 656523570 656523577
    0xa030606080c391605010c0309061209150905060106300b0910050f1008010902090d0503030709060e04060b0d0e0c03070f03060e03030f160e091806070503010803 71
    0x1c0384116492400d4402d1940000c0b0300650b5941c20442030f500243c029030a4000502070303524422001440d465944401c011078000d007440c480500044c5544204010950040030300201c10801454040f030569456124070b50100d50380300300c0c094102e540350703075080074001c0600819001d0196458400c0325a607003c194480b002810756071406034144450468150001079074440c6d130304242c1c060600f600e14a007403030141c6000c41d280c1c400e45010726801155a04645000d80360451408025155104541d091508120081d00989281500000c0c071103414000700b8400c0000d07603c40c2056982e407401090030302c540205041c00019519000d10700b0600d0038440ca880344070a84a188066400003d204008000d0940c07a2492240c1100c0c2c15001e00b5201003010200c0014010540740142002d000e09000020b000703a90744402c56820380450600c80100e0340c2c40303440b031010b40103030910b81c40e00d80700e0400404c00084c614030040ea444c40c1003501c180e40f05108950700b4040395034070001c1420070908541c54100b0583c0c4a10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 656526070 1250 656524820 656524837
    0xc0905061503070c0b040b06030d0206060112110f120106090b04050f0402031b36030a0f03050d141807060e01030b041107030804020909060405030405090a0b030a05030a030606080c 79
    0x24404030000f080544070b244880d901c250400403822490a09040200341c21a083d02c00038024007810b9800211031380001075003801181c040e912182220981c13000c4500501d58100c4001c80644100811780c1071014083c081e25403500c6540d280c4c443c0c0d526108000c3c111651030f5002d8194204180310810865440e4615082e0300034040e01c001d40c2d2644d5410550301d00000084420304101008501056903026000001e031408542074103201c103484003860b0b103844071000600c90310b5040e449a03843c680003030404a0381350041c40c864148981030400540c401d10540c0c0e850841070305050480020090201a00c65841c590a030400d4054001c0b142085401000240030100460505850b00e11b15003d80e101e5a1000c2c0302c081c0054035503501c1e01858a0000c01d0400d055034140d00c07071502c04010664044000c203e103400345a11100451030246410103110310300c1c1e0001e003090099580c90b155040103850503c10258003902c01c801860b0344034185003020301203502ca60001000c008280c010842d40c0c6400808407401d51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 656527320 1250 656526070 656526109
    0x5060f120f130b0720070602012a0c050a302609100e010b01081f060c032a2105040b180d151a06031302010306051c0c090506 55
    0x360b07610101990819444242007a030800781c07041079025400e0100e180c0341607583c0f81d4020301c5404c0744207080f009240b000300d031110041c0c0c1da66508451010f000f041e12f000911311503815900f008030355881c1c01c105058402c244515001105503007030303400c440685400100f1b408a0801e41001c0c404e1000c0d2041144007000034903d500b480e5800f00f24120003c2003041c0c0010304a4a09008014043e40340d14080e00d680100d1902188140d804210a032509001ca442000c09541c491145107190440440d081e0101410540030f002003041c01844003c0c0100c482d04540c911900c00750303410b4490349820054500e04420b802405203000c541c0000709940311007210700311107141c1ca6031a1994828240300601c51040a40e880d0f00c404003070004000c01010440d90403120681071710400004070450198414400c50107102548084104005440d600a40c0318825006d0b0040c50000303052602c403008181c541c0f0661840b0468040c10703c030b050080150b00031f0030350040d04500c90300f44503d0a0481c0404c2d01a901030a99403003d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 656528570 1250 656527320 656527343
    0x2060d150b0f0d0b0f1012050919030c020103110d091401020a0c112b03021203040c050409060e010507020c19080d0c03030e060109270c090e010605060f120f13 70
    0x40759105070144905080c010b206c12800e01e040c1c0d00141c15030749020b0311011200c0c20000064a64000403848140499940c070307803050040030a40d800c0383d2090640508a0504d69140d0b40a1601c0341c03600302400b180321a152001520f0800780c10503a6404a0b6146220030582c0100901e41e44c8650003240d00b069a03a010000c0700c51035100b8000111403a60700000c800d038121401c1400106082e40400001906001c2c0e000e403041001207840030030300e41c0700450b0003404400440c4001c02007801d02d640b000700700d64040c10300010201030f014210303401c1d50000d480c0382006a01c1401c603040c040c07516000a840c3d0081b0f51070601155450714680548500240e41c03c40140b1908181e4481450b0081c0c006c6664a0400425a5101d41e1141072a000400c07810340705280741c4162002c446000411400e10326603072030300075110015032883c20703004001030b00034002800d019540721a0005015210f080c040c0102c83c84c40c144254840f100d00035a0043e1000c01800002d481d00700105008500070700540003481c1d6a00040c0103410b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 656529820 1250 656528570 656528591
    0xf050c0f0c0c102105040519110414010f050301020304021003091509080307031109010c110f06030f1e04151802030f0d02070609030203151302060d150b0f0d 69
    0x10a03800c840d0b51608640d1151081c60401da0141048280c0300358903200c024042200300c1e06408a400485008000790b210070441600940002c2c821001540b040c40c625640040400105094035250b0011200d05081080140503141c140280000580410703030007142036250030703000202d06821800d00d82051603a192044014000640c4030040f9442d81d0540901421489150a58090740b00300d40290000745482c400700691107490341100c60f5103505968403411517415840e00c00000007046030f500d601c185542c071180c45945032200614401c0109a0342d220180c644032400b02c03189100304418084561051040000060b2800044a05504000380c002602035005140d0b40c00d0484105001c0d601d4481c40003a036841000028840301d103ca00765098403440c9a40c0d40b0240c0c0c0503682d5000081d4141c0015400280c04001c0d12901035100b0441c1499034442c42c490713004102c9541c000545600c49030384641d103041c04650001c05540041c442d0514452901c0245281d040090080c00642e51100d42c0b0b5001007070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 656531070 1250 656529820 656529823
    0x90c050d080702030706020c032b0e011e111b0d0305070206072a080c0120030d05090708300a11060a020c01060b070c03030f0c05070f090f050c0f0c 65
    0x8280300d9003d030440d85c5a5031030700c80c0a5503c42031034910b10702c40d110300810440c0b44d000e900b520480e500050807842c1281c2e0000c48054580103844403140303040000440e140c0c3d01408650003480d00004482d100c0001032004d080c0b00c2030609001024001e01d00300864103074a400d03150070204814040c3c05141041d2aa65a4800240c2038800c004001e040100440c2015000075842140c841e02d52102ca032601189694411000752201e81c420415408104a0002c90001881c910743d059200120030040d00d140205021a1030b0071100c040d242c403083c3d41c2c040304051103180002c1080d500c8444c000101103904507554505890a071420034155450f03084082205181c1700c1c05102403a411604220940c2d40c54a0103174200c1e002034201c5241d903807a542c2804800140d00010340111820a504580c0070000c0500350340b030540e100710070070030b1030010401e001a600c00851000d010041c090903000000152242c85c03d4611410b40d80304a403600c00d400d103081c1c00c2c0b010285106088510000c1202409a00d809100c07070b030f0302d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 656532320 1250 656531070 656531077
    0x60f0507050115061808030f370809010213090902190612060512060703051003050d030507120515040c02031e03160c0b06090411060c010f0609090c050d08 68
    0x508070740c01d0101c1da00c0002d020340c07550400e0b0754845d0348240b04c61081101d00580840c2511034200a5002000313550088003aa900809143c01c0c590207560300e030044a4900c055032080c6464510658050b40c1c0590f500660120071280c02201010081d410008135840c1c000c250342c00c074410070304510f50740c1c0c46413011515084c502130200190791030042407030303940c83c800980321458402c1c519844a00d0041d02050f02e19007011701100e145510001082c01c0c1d51064800c1d401801c02a01c12800c1d6065820700000191003044030402103039140c0e40c0881c030783c14030700b201901e18100100d2a1030914106810001910415403500e5071561040701c01184224401209a04501c1400000024500004428104070032810300030340c0540c006510201c2680008402110500740140e00280001803440c00304501d441d001c0b803c650841c1c0a520b18102e14484100014510b0b031041c000501543d444400300c116800c094880c80c401025140e8050000c902107980b1130310190824003440313100c1c3c6e041140c0082441042001d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 656533570 1250 656532320 656532323
    0x6060a0f141203030a0f0608010e03180d0f050f07150210150b04030c05120a1703190507020a0308090f1005130c0b070c06090b1b0f06011d060303070c060f0507 70
    0x5813580c07800c1c50000316001d4070303605181004160525900148207441403040d0648209000003950600c000740754143c100c0503444c262141d1205a20600002040a150420140300e1160700107001d468070802801d82003e00d80c0e440900f040d2901c0d201a140541c0104844055414120000a600c045801a41000d64450300861b42911021030003004220009031000243e030070842c0c0c801d440f000e06600301d41d41c6820150005144032407000c4828542038000d0003075500300d4144040340035505d03501c11012003201c008171103800040e0310503148241415003014500d500540b2101c0907200b0512807101d000d54900c42e08102101041e40d035000100400032181d40e41401c41d51111040c1401070307940c42c505e00f8903040340c0c9040d961140c1e400c04c00204980114004130446244440e150b040001189401c105107040890441441c0504c0b6405841c4680c02e214081c081c01110761759140e100310b40030341045c2c5541c004000e10b000c0d500c10410503011070004c21003d400c84d201480c0100300641c1c035a03011281405035040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 656534820 1250 656533570 656533573
    0xc0b07020703020108090309010c030c050c061612230a09050310021b0102030105010e0409112119110f1305160f180b09011407080c06060a0f1412 64
    0x1842002680030600c082224001d98514a468465035081134603486490070361030120b20101e900174000ba00511000b0101030180d07060303440701161180482c0c41540004450005402040741c9102003004000c100d1390000458542021500241c200303998502101c9030700b00b0488680440c901607818480c2100c900502000f0301503a000e8049407280d8000380d000040d801d0070a2244c040640d0500c501403007075070304a40059403031010703404118003032000420160106948001088160b0006502d5515180042031150249104901200d941343c0d8240214070145010241c1c10b400c08002107818901c0924404104450000040003d100040c903607522940c40704140c0342c01d10301000600f9080b100b20081c1d43c2020740b90114006402ca03011548441e000d00c0c503076428405202c0a1044503214809070103808011306041000b068502e420340390075003182404451124000607030000010040c0308a80c0c100c0e9084e0b94120343c00d4103000101c0d040d42050700490f103014501d042801e501355243d01c1c0c0452010071810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 656536070 1250 656534820 656534843
    0x60f040506190e0306072c0303130303030513080d050705120901021314060711040b03031c0f05040b040b04060213060c020108010602120a050c070503011104090506031605100c 77
    0x1049000c0e420700c0b00c0407050206000c040c1510507801c0118040d132040c4102d60704c41c0e8001c0c00118400710140c00c20340100c40325082265101c1c40700d031400c0005102800c0d0380c200e4286118513601d4010f040c2c0c1c0e002001d241c0251400758068000a001c1c2d0187c81140c03030908004242a034641d0f40450b82030040320b80ca504042441d070700748150500103600400c0c1d0444502d140d401d100d0703119404e050300190981c13803042d00000c5c1008244007040c40d030458050b4104008101040200c00e510000c1e241da00468500e200071031710220264450603203071007103003042c2001c84002e000501d030a403601655180c00400280c411030101c0005000c2101590443d0007140c96055600c1029480b4070008044000c2100124049090300c80041081341c00001c0c603840c1e0005a05105180040c820011130721900510107040281c403400102103102e41d0700303015030790386044036861043d142d0b46042c044001307644000e0842c0340240c10041d0303000c100c3c1170f0780260807007590011749103040040c1005c20200c1e910200341c240940700c0c0c22900d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 656537320 1250 656536070 656536087
    0x181b060c07030b041e020616140607120e010917031005090109020a12110301050415090603061b050702030607031109181f0e070c0206070506091c020615060f040506 72
    0x20048107018502502080b4000a009001c0000381029054042d41c0a2010301103840548108c0d658410068821001700398004503482d5001d03d018020f40314000800c1041d2504c000c0c0e410349200e038803541e000c03032030084c4a405080d480d807651070340500c0d298061460001000506601381007115000601d8060200c218540c1d65241510082d00310046041c00100082105280700e2802e000e0714018040c5505400d07c0d691030841007100a2040050341c4d41c4070030b201d1000049020140c0324120007180910404100d8481c10107619090700c1414416006000040c00f4031000350b20700165a640c08815800c2c002030548a86034081801c0c06005174540d0b004a0003107039941034545080902e8001c0c5000c0030440d0101081c910500700c020694042d4101a441c01800540e866110300b850300e00c2240090070107807822145490b101c0c2481000c886140165000e26103c0b04140c0040c0d82108061040348041e0205007400c5100300b02a818001c0043d1085801041c0100b000c1c2c100001ca0340140401003446556180c034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 656538570 1250 656537320 656537333
    0x10303030c0e220c0c050f07081216080306150d0b040c14070204020322030f080c0a0203030a05100504020d2408120c01230906181b060c0703 62
    0x1c400d20480000c01070800035605080c11409641d901546032408020b003d02c504006006042c84003091040041c0369020321302041c4248001d20081e02010050810076041ca2501c52500500701c00000003d5010010f603103800301031807141402a0380c08a0722680c0da0700c8482c00100900560050030302c0344100000c07001c1c0300302d0255105941c11981070341d0911101c0c9030a00151008a2140c0048054040420000703006103070a40c01154004200d0300312260350208401d00208101d61020308401084402d003500c90899041a4140c2d40081203080341c0d40707800180d8000030b48030700020300b108106c607403540c0119000c1c0b80e40c0c1200b003000d400c0c050411500c8064000400015111003001c14420b6000c40d5800a04181e54030314071300c140d525050042440b50b40e080b401018542c03024200a946542e90034400c031004503d07484004040d0750280702072215003812241c446c20541d01a2401c112000b01d007161500210000c29035840241d02d80111024600500000c0b0340240b240851544542c05414030200070440c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 656539820 1250 656538570 656538581
    0x80102070b090c1003090c0b1201080c040b1e0a030b070e040b120a120306030c030c0801051821071a09071a040512010906091103010e010b061603051201030303 70
    0x707406454110b4a4282aa64036002c84111242c0c0200c080d403500d00c0d4860081d0000d00e40240708805a500c00b0740d81d51071b0001e440e000842e442d0390395480d401c010056004e0400907003002501c22101045245c0d00322001075000700c0311900c3c011030b40594000c41d4030140c0c0d50603110300056030003031103040c840c0c5086207008240c0c1c4541c070032052080d482d1040d5440c00d81040744812103003601c01d40c000c1c032801c90140c441554031785101f0204420103840c0d14020001900030f0f00084000c40c840c0c4012102a0b040100d41030a540d001401d405000b141c8400302c004003080050301c00d800b414a0750000340ca907405a461100f05104084d0081c1511142c2541d581c3c8030070030454150b100b0350216085c7c0d00d80544032001203e0384600310345088099070041c0401e0102d40b90008000300b100500100014201d11213603188002d84098030000c1e50310003c5458440c240e810203016440c481c4000d18020080c500000d0001450340c0120603181c0150503880e8401d00400d4041c3c07044440d116816220002c01d9070b03591400a01130113 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 656541070 1250 656539820 656539823
    0x1920030105120a02090a2a08061005090a03021e030601030c080f1b130618090308060406030b0f041b1509091a401406010507031b0c08010207 62
    0x24851035001c8541d42c03011600c8282c1c00e9004011801545510903000c002e024410a1035040c1d2200e801502c06010ba00e10700c2d2050000c1a072201c0f20246030010070040c8071104107a45405001003000710b0b00300c2d503549480d1001030702d90484010641e8034451100840b454000d4812607014402c1c00004800d201c00496403408882186084030003911241c481c4030384a0b1030715100b49120b483c2c400700101c094130b005d0140c40c3d40b09004107000100d0b00e03900d010002f244450101c900d01e8859803840200c082c16440b0f500f469226106440905c0000c0c40c50b51061010500100b41d84400a400004a0100300580d604100e590f00070a000d00100c54a82d4a1f40c24113030350f00da41400c0810415800002c1c03240190244451110076000111240422a02400002030a9071052140011003011003100c000c0345010361501094481d09030000a003000351150211b64100d1001d5503001014000c00140783e07448401c85403c2c9a262800c2203011440da1282c66008a032248002c0110042480c04145154154054540385 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 656542320 1250 656541070 656541079
    0x2010b0a030b0108011b0c03031e090615050f010e010305060607050102030106050a0e030d17340909180f0503090904060b010314040305031305030912010b15040501081920030105 78
    0x80705240d496400d4204046c00520120b068a000316003c640a03071320040e501030700d19a0b101409404060020102e03a81c1543c00c4480d11342d1414408411803540034003c01400c0180c40c113541d80030348a0700182008a03111501d504258580001403003d0703ca80c002c3c2d07420694800025526940c68040280c0f607500100c0b0f451000545000e06000545800200c51510501584480000c3d041c03040d0300401048008041510b00c00c00480d1004100f0f8001080500c440690101501d00e200c018200500c841d02c50342c40b100105042201440484080750303d4840300c25445805070001c119a0701d40300e811030103103049681d400011a8200420311881c2d07048152507030b03002d0341c0c10006c0e50000c215208800400f030f80d010700001c8081c00040d6501c203680c070b0441505402401260708181f60440090050886802448040d94481403096a24288540c0e02c03100003220410180c28281000002044654001d08000c113008004804085045040d800017076641c05444400c14a5110915960400e500078030803107009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 656543570 1250 656542320 656542331
    0xa080c01080723030901020702120105160212220f1d01080f0606010f02010603020d08040e07020609030f0a032903060a18060c021212070801122102010b0a030b010801 73
    0x416104950a1614004810b020520b80c0910203103030f80c06400040000352590b43c00c100d00405661341103407401c00007120758000304862800e404000030b44045039109000359401501d004100c921070000356200c20100018440c6041c0c0010a0309440c2c0520758402d40d007000e41040003040e081d01c8068502a60584000c540c0c1d501e0340d07601e503066918400080342e03901d83d40051010402961007100802d1100c1518400841c1c0c1603201c2d0001010300354001c000321400500060200300c0d441400030456800a0240040d056a02d81040050703120b1044280142d04460b0000d10082068025071000070040c0414404c0f0135240e001071000401b029000e00c607144644184c0b000143c80d61294028005091441d100d820301d1104035650b2032018091150006055000380c0003015181203004c80581441c1446207610034440c181408090404001130b0020707249522041048004241200c0c19004034500d0a045440c0d00c0c1d6101c5d508034010003504002c2c55000220b0400042804200c0704918166100c0702c000701310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 656544820 1250 656543570 656543581
    0xa05010605090105121b0c0a0b0a060602061b0415020f070b180411041a0307080a05010b0313051501080115051c020d14030313060e0705032503020a080c0108 69
    0x88a010300b02d0740307a00007441040480e05061008810325004142c0d40d00800b80f48141c1840c081281d0401c520a0205610125080090081e91013580360021482d030000c0000c1c2c0d0601400039162100100100c05201e50011603140440e60700c401c48001b401850704d0020000c01d42c001c0251140d4400901e81601e210714500410070a0410080b100202c40c44032000242c0c40207a014080602031361058100021414070000a8070048000d14030f030705d0481d140030389951345003404001e80031103070240c100190a4070f040010700c2844410001c81e03403c001580513014240c0342a00d00780b40782041607480615001e8206c000041c0300001500a654103411019145c01029225001d120030232118500000301b06801c5080407025041c440d120380c074100d009418024064480c071000310301d503510640c0d80061100459407202c051001e948510300588030508003400c000c618090001e03640c1c0055002d4081c41d05005100b40800644e8000110001c1d0307800b171f00090b0829030b186a844c2c0c40c1c0708003480c0b403070118030700000081c4e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 656546070 1250 656544820 656544827
    0x6050307211b080c04050d14070f050910060207092f040504110306030706030b0117042303160602180d0c08010e0d021b130e010507120e03040e0411060a080a050106 72
    0xd00ca03001c030710440ea040611b490104030005420b01c0081d50080c02000604500c0d403000d01800f0060001c07c0c908106044c03400051120105000348041805081c0020500c442640405c40c2c03012036003140d0000ca00d03415036100c10071400912a804c031030480d10b0300c1c0c01f019400d05000b002d002107540440b1f04101c2c409900d1202e0810f448101c400d00e82c507402400003400200c0c080c0e88034011014042c9001c001c081d404601d00ca01d415820344081d5200284461030a80300f45500726000d40004500e4055800c08407000041403990900100042a00390081500c0d24100381d400ca50b80e041410040001e452600b603802c0980c6480700c03e00030003040d5400c0c901280700c1c0d0900000d4418030705045034018450304050f41c05120b80e40409044da143e00440d204200807030b848490088656045900000140b142008007001c1d00b80044901070709c082c541850b20420b2030308000f000b640c003110050741c1060303c42e40d624505410314a116580341d035030201001c00d462802583c03200f400791068107801c2d4200b0103030340c0ba420142c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 656547320 1250 656546070 656546087
    0x1020f01060509160519050d0b0402070f03080402030f0703080711010f0507290108011a150904091403030c0d0b09060901030303021b0f0f010609050903030106050307211b 75
    0x540240050011410710f2900d60340038102d160145c0740c524200b5194020301c0040e84000702c0b000000440109282107018001d2040303410445007107a0031858a602c0d9070b0303500c01410701326001400707124804001500355207040c0074000300340c0104025121b4181e00c0345020442c94001d03032010740301000079982c0c3d41001d50040301c0380c007010030031901c42034202107003503441c180360b200c41c464002e4043d107400d000b00246c09a900140b40c0070342141300000c10400d680f2000c564a07201c0c410f1070703e4480d49040b0681c110540e0b102c1c0c22200c101c1130607203021810154a080401e07101c072a1643d84070940c4400003c00000c100401c003d03060070200718400303025540d003480130001c154400303550b41a400300204004200290103903000386240c4e0408a420740c43c0444010410b03081082c0781c0b60130105a04902010720320340c2d40030710502c0e01a00c1840820455410301ca01003d035240014059881401800800300341e005004461400500039800c0c583e543d100b281181c004081c1170720302502d100440d10701e40044049401043d94 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 656548570 1250 656547320 656547329
    0x3170c2205060909090c0d0b0403020f120d020d0e06040c050a06090e0a021819080114010b07030e0112060902090111030306181e250c0b1f0e09010b01020f0106 70
    0x20b2030404403102c04009140d8400b0385901c03400c0c03150000341192074880100b107180d0a8080d000c41c507034034039141c10040e04050400607201003507001024003a000310002020307201520f0410000603111040c40180c078004000c058088081c500c2250304000821200321301c25403c1c0c85083e81c6883c40315a60321003c2c0c8100006009030380310300b0f8a02c00040c1038035540b903020f041c142c0c0102c220170415071030704d0010996441d0720604100103000c85420901ca100b00034000c4661441084003903604c0340d03140c40080e038005c0c000e2000080c100910350305010703090f03845030540c001003030400c0100700025a0b075000200700940c4804d541c503002c11480300d4410100040881030780e105120281c4401c29800030019500c42d00305008002c1c03040c49044501a040d94995222118480c01ca0303d8108110508020303801c0d048110450400700420541480100005401d5034544c1d41001402c9000350f0a01c01005408038241c8464000c2900900d0030380030400302c4801500150405042a02510349500726445100d0990325203004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 656549820 1250 656548570 656548579
    0xe0f03070b10050d03080610020a0215071b120303110f0d090519030c1b05012c130f050604020f07030507060225052a0d03170c2205 58
    0x4001c5401140e0055105222000307407107106450f080042c160590a020a03070000d1948410040c507070030171002c141c6070751080b8001000740e4002036002402c2101007000b4400b0480d004640c10042203103d11038500001c3c1441001c6080c0381d01d42204c42007200d500c10003038000138100103103518440c50050844401c1e10111551030700d442c1e150780a00f0b001d40f440c5002120307240b2035160007407040d1240c2e25140000354070a95541c20030f07103450700301801c92002c80c0003008000304c00300c001002940c0c5c0100c3d141051500002499050940f40c00441203000d0610481d0380d0009500c2c49905400003165100d641607400c1c2031410002629a1400e200c01c80c0561110407a02410070080301c0d001c40d0180010b080e0951007042c2c050315010b0b1090413020070812050790152010b0340c1800b0442003010601c1028088004a0145062103000c00404031a941802d203115020b803619000c420709052180749403103c2c0041440095126061290030300003241d21041900d00d1500050000b40707401856007105008940c40100f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 656551070 1250 656549820 656549827
    0xe2103010f030f0c030203010f06090b04020315010f030b060301181d10020702031207082109070501030b030f0d0519110a020922060c080a02091e041119030e0f03 71
    0x1543c0b080c0c2011030100c00d940d00103c8000001c01a40e00340502510524040d00100f0020b191040350350a62b1151901d41d0711813401030080000c400103482c68072152100910700414a1100b044094000700304024035184c010400000200710010f07119400042c03034074441d05c100412a0035a041078540f01c002d04400141e500010003041d41d1611540261000d98001001e030307910a06c0c02040d107069039108520440d40b403040070901c0084106038201042b400c40c651104d500742481d10900d8035855903224000c8605060343e4a1030182640c500300321203100d1200703400031500c10300a101c4000d0030781d80000c2c3d102e1002d280b882d0310680780c1a206049800442d0462700040c002429684d0070810a050000e20206d481c51003800e07101a01c180700c030400d241a90184034006940000380500a10700200100301100107801046001c1058581c03028009000c400740083d1800e501070003000502410780004050b2907400d01284e80c4102c62400c60300c2801c0c008541d1010084a0f6a4403001922041001c0e038101d040d030001d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 656552320 1250 656551070 656551073
    0x15083408010e2e180b01180315091e150e07060801030b0c0f0a050a121e0504140d0206061009080601090c0519020c01230a0c02130e2103010f03 63
    0x702c041c1140f0310800610040d03488440e00c2850784d00b20303000f402d4a81d488102003501c07540c0118040c0d07480703640302c52002d18850031038075a0100c04101022046415686140241c123100381c00a000400d800d80d038076420002001d07030070a18501c50311000500e035a14580090002415030010f1940111402e43c1c58031081030b803840d10341c0600188010700c03058041c1020000e00e0740d4a0b480c1c03001841c1c640b007940c40b0b05445420a09008101c040c001c102030324640d00d010309069002801180300c515000c41071002203a1940c031407400c01c440507914414a07544d441101500010310f07402180252050600b03440c6070181b04454041101c2290452240101f02e800c4200140030030581394100c4030394100782e821311910b800d405603016110400181103890040c0c1100005224960340301026a0594401d0200c0803165011499421181d200b124001e006100c0407a001c5821921006e80580748420148010040e0065070a402e07521112a0903000011600e00001c2d03550804811094a061740c012510510001e404c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 656553570 1250 656552320 656552371
    0x60c0c10051f0b04061e05040b0306190906030302010b03010203040c26030708180d03050406050703030e01020c010203061809120901050c07080f0708030415083408010e 74
    0x16204545010004a60391a84a21800018001c100d0004000da5403864048002c0031000060880c0d000108000d02d11b601d403a600105517419525640102070f521303244c410000b502202c42034828403c40e400300d0030014211700d255100c502182c0c000d07002402480a544101802c0b4481110002c012021889080c003000101c5119010718404042e0032035140b465103004c507451a040840c0803642a5000901044285282d03082075107005001d80304030800f031000b56000750141c055030084504200300401c5c0d42081c140b194001c0009004118000c41d034030540d10949a01079842190381d58081d135080030021080c0080d04030340318810705140c0040c048803000c1100454550f03105035019410040207103c0765203e01c0041c00044000c000750300080c1024000030022500705181a4000906a041844100030303160400e020070070122500d00d0320805580d40e03c048a00040c20340c07004010f0424614002c0e284101c914802c002071040c8a8807490101d03aa44c80400114020803201000b0700f854010b805d844010301c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 656554820 1250 656553570 656553581
    0x503010c022a030a05030c060402041b12053103090506040305030306061809090c1504080c0d0309170709050121030315091418070b16080f0f0903060c0c10 68
    0x100107055a40044c0e0944070903141d034000a40d2001c2d035400a000f8841103107060300c03901100480c01201000d44801d140d001806180d42c03041c0c009034454803000041c1856203500e0705204400e240306440e40301c950509205c0049105ca08202301d01255003480d001c0b407145000e800b60b0301280d074490001d51841d543c0c1c500740320083d084802c1e40b401d005d051614036000f55440404581c481d180c60001810022005e4040004611014590a09005040209010760350011036110424601558a24007030492450229407072059540040141c3c03011200e000b00b0b0a20209004045039614a801d120a0340c0b9280b01d006040c08800075444410862264100068000c3c0c009154031425032040003095903413003544130305503107095814242c0380109004111003005603860f5084074a8842c001025243e041840c1c18000b4420303990014007200e801d0800000300200d900071911204100078480f81c40d05442c0303101d60301c0c5800c013100700c600c44d0059000242c241c0c007e50b0161210a00020001c0c40f16142451002c4020301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 656556070 1250 656554820 656554903
    0x160e061303080a080a020f0403170c0708060a0e0118020d0f02060319051326041508061c0201080c0c0c04090f050601060309080a110c03070f0503010c02 67
    0x124203120114100010250050007103020ba0700081e80c4051900000340005401031001016602c148160890503070710b081034505403a48410805000151216003520900844a10404500c60000042200807001c5081d038000c0700d000000388101c00e1091200b0f400c2e03c2142c1070254240000c0364003000945440408006480c2c0241507a81440780c2c80c0d000b14030250f0003110740390700e4441000e8a850040806105240d40b04001829a04860100b070b81c7c1c07402100c181035011a8001411602604911520011100200010fa40703055006260300005021058200c030a40c0c49840001404810500c0c10b60320112002d138142c0d140da4650b501c582501d00d642e00f2241140d0513621454449502d00d03100e9110307805100380600310754180104d1a00d4641d181c0481600b11030200b40c01c00a03080e0000f0000c02c140c07805112607050080300d00e82131980e403130324000010200c2d55041c45107030000a40d03011410750300c0080d18415802400081c0700300354240d0341c50300c02c3d14150f021039400b5544121062080c4d001c109200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 656557320 1250 656556070 656556079
    0xb0402040902360d2d050106061d09062701080c0f030d020d05030a020903030409090212030703080408070206070f0f030216050109150e0a1d010e0f0612160b120609160e 74
    0x4a601c00080010b13204017202111540e643c0d000c20302003c1d420142040986c05a080d0411001a55801140c030185004e0f04ca43c2c080c1182d4442810001079040c0c44198040d02d015200350590f03900c40004d5940e900e010803650094210020410040c20301044030703000d007440c0382c0003002d05032020f02d8102c880c0c0e84020945800e075542400480c149640034001031005054014002c40c0452050041043c000c85640c403a0099602c10402d0000180e001355a00f45d01c180c1091170341b52100124004200d440c840d08100404500405004000f08110301d00d070010454000d5084401d010400c00c80c54045009a010b0607022942d400340801c00900e00b5880c2094025903850168030740c03100100440c40103d01c58000340c0048000241c080129032210b801c0a0042034404c8200f401c034205051000e000d150042d2005004038200908a0302c5c014080000c1e105420104241a90280d9a10f007005a6a004070000201c10746240c408100d40c0c0c07074801c5241d400390300034003905691b00600c0c102c00c0c1c40c41c2100380c4c24260407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 656558570 1250 656557320 656557373
    0x1b010e010e1002030d0c0207090e0a030f050a2102190906020a0f022b1b0303051209070f06120b030c0303031303030b130606300b0402040902360d 64
    0x81286c0580c0512401680051808038200104042a6030790f511504189602010201c40800c1d440401c0780544003590a01659a002c500c1003201c0d203651284d900360500690403540da03548034540c0e0091040b0119840c042e043e042c1041c104079807600040c403c42006901107400c0001140e1641d004503011031008122500c104a40c042c03200c102125102d401c0270f00b40c490503018080c0501c002e645002c0003a4046503488560551b41d0140450203905620009242084001246100c04000e0740c1c0c090520310f01c46012007a5035210040c90b840c080030201c80302c41c2c10204207a00c24100064040c18081f002009142555548400140050312060080c4c1c20141c40f491000903541f91018591494440d040011992500304000a05000703164001207044107031015031014042e808841401c604001e255011402c41c0116000030003901440c2c1001c03c40e07070f200190707114076642420700a6944051005442c2a10450340c101540c90381120090290040c1d0240842c030002074035020f10021002ca000740c108403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 656559820 1250 656558570 656558587
    0x1d0301060e0f0a0219030509031b070f081902040c20030405010f0206060904060209040603080f04031205040b030c0d0e0d11100e0a060c140c1b010e010e100203 70
    0x352101640203055a602500c10b1110341076004404550000300104194034103290309201c0c1070860b165002e0174041660b00c0b004104042c81c24001c403001c10042c071400203400c03070381c180500740c4540e400d01c64070f039000040d0700000603000e801044451325078954080211203058142c081c800074048034007812040000480d07080d4000500241c40c0c800400e0450004c58643d41000001346c41850441642030a65001c101044865070303883ca4095030195001d84056282e001200203e00506959003000341002c0300802e0100720555118040c0c811240160b64014081540c2c25056a4074411070086007181e54041000a40a60740c0c8401004152100c4100040314203d250500b4201014100c0910004140c0c0440000c20002000305a04410782400200300702002401100d5580c5000080100407540b0341107d09401c0f8082e080d50460008492103445c0c1e101040d8441b55151251481560001e2480744a0b42049500c0340c0114440d400b0182c41d90f01076808030604001001d180480341004603c000c000102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 656561070 1250 656559820 656559823
    0x1603061d060705040e0c03041e080409181a01030c030b1506030109140105041b1202040e0702160801020306010509090603100f0204030c05060703450602061f05011d03 73
    0x911418041d80c4040e101c2d4100031074820405c0b0302a01c0804e501c4024014030000c5010020301e800d01034800c200703840c0040b4281c174254013a8002d581c09081801e1900d40c0c0d007c5264842c1d10140161441030803000c1d503005104152040f010403e000c00b4200e1559803030103000255220300840e800c00c0c040f001400100c0640307000142103910980142445a4858600c40c003040c100c0350340e02d07014040844052003844084030180b003843e40c03251503440c100904205109000411981241c2c09400d02050041c80c0d4584064065913071520fa01c0140e0407041c018400080c029018800e990003148140e440c5494083d9010800038103c9000d85000e9142c0222315407002c0707014035841002e41c1d0100461005da103a0346581000214054158002409404c00300103142c0003d038070007421921a01e019403161412000807003d024012001c0301c0400c000011084081103484890400c002210a070380e080300e4942e544c0c64410b071050719400c82054810007500b8800c0c0103541c050101d90303503250440c40300803440641d0440000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 656562320 1250 656561070 656561083
    0xb030105100c0501050132060322021005031b0a0903121b210903020d08220306051909021003051e0c0406090608040519030c02030319080105031603061d 67
    0x43c072032a1806040311020603144114800341f0014a08031005414418000c90414400107102d80d925850011030241c50f5494803442e08600b0390064154042214040f2024003564420b40d20850344d840c2901c0002c2c45072449504940c40c41c40c1a6440e04682407441d5100b82c0100708460303500080c410700200e03c40841a28450182c48140200807070800100c0c0090390301015405040c828081100c040c10078000341c1c582e40030042c0010b90203403a4940d21481500101001c41c0110305010b10145c03000000001d000480d0410fa000f1039110030f21011860481c5418802c907118248000d410040c1c41088494050090303100c6a4440741c00000b449881030b0f994084d1031302001c00c64078418007600104082c420f4551000000000c0d01c414200407074a428141c46880d0b42c0c040a019060b0511179041049040511071900382e0811613024045949078440700090700602205940d90740005240c0070b000003418a0001040550207030001c003d000100d0a54940402400d8004100f0a80e07040c03031222030b100045d042182 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 656563570 1250 656562320 656562329
    0x140a0207060e06090a050d110a0b07111e011409060a020a05060a290105071410050c19030e01060b0a0c1707020a090e0f061602160b030105100c05010501 67
    0x40e041041c2040030207003849000103000341c0a01c405102c2c100382511080d0308001074800446501040c4401403616840203d43c4e05211b40d0001e501000004408003104064102c5905c01e0500e05c8510440d00207000c0d004c1401000c0d500000064108034a15501407078682e02d80324200001039180c10b459201040103035011062a80060388030312a40d80902405106454100c000300c2d000303015111022180d10462000b0004d420b0911311007088002090b80030781704940017150303c4201c06140c031294014064460204000c110000b40c03d2800081a00700c50004488008900d4002001d2400e01e5100440040c4862840205c8a40da104008115201c1c4038015182180c1256140c5aa0509901d0404111594503038401602441440920700595840342e120b01910a0700c840081d41480550b10035107070900448030001c2c103020300c405210804411a8080344079801c19002c484400400d00b031a181c0500541c1708035a49641c05000501280c030309141c415803118440e1522000746da009442d02c0d82110801e81c1f0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 656564820 1250 656563570 656563573
    0x20301060b09090a02090306061309050601090207060e0109150906140f07110102090f0d030c1430041208040b0309010b01090603090302070504180503070f02010e03030c0c060307140a02 81
    0x9018034980b4100d0310140c2d00c411340c94030642c204401c0b0408241c0d0741e20064111803007000c0b11084623045014a45c070280c1c10035004000c40d103a07542e5031300d824402540500d0040e42c134142420100c1c0d4210405000d42e03914551b0140a141c2c054036031003030381002054030150844503141c8405560307110600f21034005004040d9419080301c1c03401c1884010300040703132001503154281d005101c0c41c459030351036050103903d144041d40c400c1c1c9011814507080340d10b03031400c0d4401080d1650b14418003070445400505200d0005900c05407500d514250054103010f212086096809880200010301c0040d041803403d0481a101d04021401c242c0c487d1120301042c1c204030b0308003849a5684e00c1d45070096130f10158031001000e00b41030800a0250300c2d02c0007501c81a45002c0d89006a031961442079a59080400120802d900042903940b10801c2d840c04c0d4401510210040e40010314070340b03021400f45000b20491740b81707a5040d03000345010101c100901c0b000b500f00500c50014400c0321214042c2c3c41d11404024000a440d130750 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 656566070 1250 656564820 656564827
    0x30304061b08070801090f060e090a02032a06250b06040c08130308060f04021206031005060619170106030902030715121a0406030b01030b06180f070c020301060b 71
    0x9600700c0c6440540d4090000704a091014003e02d82d8100c0700c007a041d40c01a0002040044800c22803002030899540318010301c517942410082000320128261790201e02c02c80541c0d00390035042207140304102d151103000c104030302d200203940d00320b02e00400108218500403600e00381804501d0b404004150748410180e8200c4e0101d010030466203480c0c443d107a410003031414080d00074144401204c1c05111001002010f100c0711001180540c0d50b01c0c0c0090960a01c010015903032058007200c0000c00c102c051f180e5902034810b200c1b0460740c1c83c0302ea00401d4407806010340200c0c00c0c80e4000740c03540700c0440c091080078107000100c80a20b20040d106052940a0401d0351400f217031081152050501d04121070348045d40400d40e9018082c1b2580d80040300544c0020354a0011601c0300035030076603c062030003040c0c5065020f440c00c4d100204004170840d145040b42d000e140d00c0d4109a4400c82805052085c44202c0c6250404c10350014501e090020701c55a085a0b443c506003d290001d903004c03908540154100d803c0844011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 656567320 1250 656566070 656566091
    0x91504060c0b090a0f141509010207030e060c0c0d030516140c0f011e0212070605070f0c0302101a040501170d05090306060607150609020301060e030d0207210503030406 74
    0x404002e4200c220f5400510b8646040e844680341d0010b8038500070804400103504407585041048078202c0900c09580714011402c14a07039160007540a0b80b0100e0100d99020840d07209480d2401c152031903101c90801074039164103548100b11502c4020030088090160a1050b0009002e869018445140c802e901d003c902c90707400280c062520000c002040d01c100740c50b800445103071341d003c1051901c440e0720f111040c00a00b0003441c141e0418120078000d90042d900400e0110a000742904101e01880c030b0340c1c8410681d0b0140010840b140d5200ba4005401f503400745c60b854100060950099440003070140780c9a1a00310180c0020b0107130341d8284d00c0f0031070584a508030915455420701504841d00c1140c10800e15195100000c0b079102c20009040c5403081c0404203611017071001d01c0c000542c20b2840d00c2010001d40d92074000b080c000f90003c0c0150400107802ca1107040c0da604000851001020494000300f0180e031500c21013b045003480305940701101d5507400000c00044081010310701461240c45c0214414040c07 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 656568570 1250 656567320 656567333
    0x91b0d1b030e010b130209010504090e15010b04150e0f0316060806190e06060906070302010e100524032e0b040c0c06020705030412030f03060b030c0a05091504060c 72
    0x41e0040c040c2c0e076450881d2000c1c940c0e9951718104000460040e01607100c05182c00143c4d80c5004d99406907a81f641401891501c2c5240812100c0c0c1440500c1024000e9980302c4a956580340694010000049038000750ac05104c1e0054694030b16003500280514610410440883d0410320045a004090307900354805109841e08000d00350f91280c410354a4a0582421122984c1c401e042d1f4820300030130441400109455465240480300b607101d005d0802a80c0707015504d402802800456803072003d0f40641501415242d0a45c011903010740e5181c10440941d0142012102d5800d18001071564503104d60720080701c4040800c24000d06441405031000c40c0200000c000d0004c0d40d0f0100f01c50b5204a15040d050b426403500152400079003908070a00584980032440c08502d144a2500440d500b1208400c00c401010b501255010300710f0016902803020941c6d0300c0c1401701d1804162035030b4244142c1800700500d001c0c8a0005041e80260007484e15401c0e007810726283c60350307a00c07581150300090336580702d034000e0002 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 656569820 1250 656568570 656568581
    0x203210c0f0d12050a0f02190e01020a030801060f0210061d01050f10050307050409050f071106070906050901031b030209030d0c0503070b0406141f060e091b0d1b03 72
    0x300014000034002c0b900000c00300350341c5141c0210441c1c0d0701c40c00704500824640c130202141c0b03140c60003155036400c145440c008414440700a140090480d8500345111b520101d20989041e90545600340164207021055695540c600122130840c41969520075140d130ba94003c10004190414900070b04038129081d041291205801182c029440e98050b0742030f580301c1d130401c005071341030b00d14200b5100d440e807050031241031146038404a041d9003407509100d00c95440000c0c03580202110b8554513a200d40f48483d40307865080450703000c40070400c2800100311650044000307018011781450002032040c104c140038440000c41ea440040001da020914103018241005095104e9072103003840d00f4428996030303546a59101e0310600a100c1580d030008501001601d0304145170001e010056054a03241107909201001c20031040104440740124002480da405140c40400840016012400c240d80c1e21488003400c0b020000169405541003064220b0085248680f00c528820b0700503007081703000514001010b990 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 656571070 1250 656569820 656569843
    0x23006040c15050f13090b190b030603010b060414090f09070911070b1608010f03020607060908040305070803030a1103130f1e0303140c04030312090203210c 69
    0x601290602000c41c0c41c40c03020100710703590070301d06040305601010111402d00911407014aa02c4021030703100805211421240c0980e460b00c0c3c02044a00b85030420010302c00c201a01001c2e462521074003e000c0c502080c4010340d44480f014001083d400c1c0048046621a882544054241d0911200604851518000454002503002c00c1e410150408110b00c54032140c00388203540919649500004203048a8419500e41940041c04e103c03003803418800281c40050300700c500d40c002801401c008504113142c00407507010340e1340203400c41d41006120354503580140071115007038400110a00000000842c10400c4e403002e0318816000d5034903414042145400c2d9410042d051040240a00030040c845088000d11207016420034155103109070a41865100c6401069a50740502c10f132a606000341a0142c0004600110b071a80006135a03441c949071600341d016a0200030300091031107007515103c01e03450b007040e0066400103065450383c5100c081c20140007600395445120107030012a00d20035040042c410b02c1c8603072 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 656572320 1250 656571070 656571073
    0x40204060b0918040507120803060f01020111120c040f0b0a030e030403030804030c1a090d1b08070b09010b1011060702011406120f1b030601061b080a0302070230 71
    0x42c0034000060030081001c0359003054646500d00240c280001048240b00800245c2c889030f043d0701d0903042034050343c0c3c412100c441c0503003020b40d00240b2070351051203558180320f104111142480034030880c008215030090800f8000e4141844003190150010314800f00401882c0c500d5569040141005420360f055184084030f107070018881000800c0c0c11440d00d580c000d6042c40d00141011700c620341406001c0b9201d040c140511400c4e01000f9910000040c072511032201ca4480384990b40721450264443d50341168000d22441c01848050009020702e0701258001c03240d074001048540301103007c00c0c8950040d040070000905c0e17042c45c00b548440c00703004049d000b130320510084c000183c03901c0b44446078070806065136004210040b80007040b940d0610101c000000048266003002c81200c15038102071142c0c87d10325200f805501c0c000100603004000074003000820700300103501203005885040d0280c01560700042819002c011210040c0e9036040501c6030b4a03020a03003468460101380700c918600540c0c50016005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 656573570 1250 656572320 656572327
    0x3305041a09030606040b0409060c0801080f121e25020a0e090a0809270103051e071a07020402031009050903120402120106030b0915150609040b0118030803040204060b 73
    0x60307280410f03801d901120566011564020900105005291140c0701800a91800401c0d4141c4d540c401c100d40e04035510401102d210885d85a800c0b510742102403944110360004124940c40c070f0204a0840a107415000105402c01c0d002180c1c59a25000c1c61440c0c010607034107010014111301d428480036000d807508000c1b041441c1f034114869961848042d0b4003510503080810440c0031a51030240d5100c500c1400d2440703050724030600c0ea00481041c0203000072100750081800c1c91008225072100e00ca400c0749210010165a4903100401c1582c0c10190303041103c0d45c404214103c0547c0740da00085004494040c006105940b0340b91500c01169405441c0750b0b299041006180d50b6886181c1102d1b800680440c1c2c0005030040140d101ca00601c3e80e580300410300f071107841c02c200b008403002c200c08021002400c1c0350b0241d41d03a040c2403021140480740905500041c01e100030503544c2080d910084841c4018108120306990544507500b240105078012114aa80003040008600340740c02184024886410520308 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 656574820 1250 656573570 656573587
    0x50a020a2309030a030c020f0301090b01030f060615080702150106020a14010e060108030d140105011b03032403050712030c0f0f0f0b160804030206013305041a 70
    0x9292403030208003290740c06034041c080506444001c544081c20001d0455500500504d0040c0c03190720002d0040c0c0c400c00741d03200041e08500b01030107040b003a254031040ea40c1503607003141e0340d02c20900003140c41540e94035622040461001d0899044803100321042c0c1300d0a48030b03d00900c00034136201c81d0282e00c0102c01032000040004940018219100a03803188441004403c000c0420380184100c640482c0f891042c1000000c40010200c005c00c501c81c5018424440e54106105030040c010083c070509000903040300108580c130154020200d1068820300d07003c00c0100044003054507151a103134882040c221008010001c1000810000004000e4000021401c0d00261030243c051485018041c1040710f0f039400800c1001403c40701d1902541e4020520442c0061a003408090080100c1c4c28082900e42d4013103004429000e1440b451145078143d005140d00c3e0f09000a158029800d42d8610038000081d294507a42c40f562150325000c030054a0b40c5807502e5070f280c44584600c407080d101400d074520104000610 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 656576070 1250 656574820 656574827
    0x10524030a030219020d1205040f23010c06020724062306071b0f0f08150601050c0705090f07031401080d080c040314010c020601080f070e09031303030306050301050a020a 75
    0x84e4590055040c801c0034034107800401c003407041c20380005011070343e564100c24480d60040050815510001c044060a68681d07803c500f03181140004500d0421001d0f4201c000c541c0b054110b400c04a11038140907007069055517070980b40401ca81c00800520308446824110300b40799203d910001c0c03801c0d800140c0c0109010803801c00c0120305189560203100b00040400501510480f030303010300b9269040204950b40c1d240045214060580a842c07410000d02e640001d07040400a0700885c501d48043c5080500e448500040d202a800030003040054001c199000a0594132000001c0c460750540d840642c403498030f481c0080c03c8070015200855022000e0b0018001c40f1000a1030451341c00701070070f01c1c81c11503c0300912200c16000381d910080c80000c49000380c222803241900907480301200b40d0211200c80e40c9031450340b600d44080565101d1650b201160800103051b82ca40f41030f070042c0c84030b420f60745094007202d510b0482604542094001c0b9407144020030080c1005d203e910b1f8420a070030301c114100030300b088004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 656577320 1250 656576070 656576083
    0x30b010215040b040221070513111b010b060406030203180f030a030c140f07140c2803021507201302090a15020d0207090b060a08130203010524030a0302 67
    0xf4140e0300e02000003504640791a070800c1c0c0c100d5100d060103003a03121b0b1110030035a510600c0c0545401000180b201d41502d8400c1d000b00c030601c00b00c04c8034641c01c10a5401903003443d541c820703205045039904c59410f4510b90321401d0081026084527036016039a8a405000309002c5c440b0f21000700035651080c154009120404002d6800c0d0203801d2a022845078200c0504941298460310b842c5507a510000704002d608501c0c000400d21948075040803c2ea02c91030044140c0c6541800b140c26811207000d91050354826a10304614200c00346000e2800c000f00d45076000303e0030025840c110b603141010009114010710004465204d15105131180c601024001100425402084160800030007900401c116010381d68100d00304016149d034680c0704040d59040c06000790349500d030b00000405070050306c40114008030039014a18120801074207851514043e440102d8513010000e01c0c201040740d0007103403400141d0702805200d00618000510f000700c015180d010566602c4a0300d181e0780309900a0401200081e00403844 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 656578570 1250 656577320 656577323
    0x140c18010b1218011e0c090f090b030313122d1103010e062d01051503190618050f07320d1401320103060305010f060303030b01021504 59
    0xb0760030107840301074111070704504014420000c4c0d400c1800120120f900c400200e5a0701455100612580001d502c090b00c6520302c034014100d00b040541402e002c40310f0107400a003401c80303000e02203a00d001c1110f0003070581040c0e160017696507203180094000070300c604038a222100e0107030301c42140d10032281144070720384950042c00018040742080d104a0000e03170302075201806440000b030641e0083e03c0c0400d11803200b509407011210151000c0d010503602910310344a2035040c0c54002d003111214200c4000b503039180ba08014081d0340c0c1050001401b6144040c3e500400008003250b11800724040f041701c0b030074006c0c3c48004040c0d000c904240f5041102d6298000080700c80300c100404850282003840882c200c0d00da0b6028034914800d0b10006012016010030ba002c0e00e5a03010041c18869107980362402d01c001d504c00340b00c1080c002c92840f40304000c3c80d0b50b224034650303400005050001d0041d80d81e644140c03e4829880c480204a69910010001d050f010300070745500003000d102404441506c480f07002c03543d0001820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 656579820 1250 656578570 656578597
    0x7050f071502040f0605130302092203020c10020a0507050411040803040303020c0a060e06220503031204021801050310020901050d110a090506160f080c0303010e01031103010c1d0d140c18010b 84
    0x100e01403203020743d45030444148400d2075074013151b030bc7c2c10041c0d03a94040720b144502440891680c409420b1001c1451f41e4503c1d484000707403003080c0c5060308100c054520340c81c413216060820080020464402c000800065200360040c1c2240e40d8103c040001c1340316241c1c000801d00000c020042015500c99080360488907800d440341286a00b06091080d403200190007158040c84001038140d20f100303025100c284200d10880b88880802c1d03617074501440c200760030300c83d5a40584c0f255116064010054000d080014010324089060411590164080e110004c0c00e141d080301000404140185d4010500b03009008140c41c03007482c1880601002d51044c44644000c0c01c2c41c010303000c4050401c40010120781d41718054004903034903961a2090041c1001c42807204481d404141c032580e84140c2010300a030300d00002662180300c0d04244010514281600080409500055980009000400240d1140c4100e8120802061201c0350fa0b420b005122005046094041c04803c00401600300c00c00112140c90005c020f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 656581070 1250 656579820 656579839
    0x5091c0c03120c090503010e0109050d1b021003052e140a031a07081e010e0603032106030c0114040b090a0807030303051e070807050f071502040f0605130302 69
    0x3022034400e20750152034460907051481c881a6984d01c09102070948204400800c104915000c48030b0072142200c1d070041c03442d003200d000c0000da9801060703041d4820051000c2c4d510341603503035800107096070189000c44000c04d0341c0d5020302205030401809e91140045511640600e084034821441401c10707244101041c07088038540d0241142c685070071102c000c6601101640f01c0840d4072a80000100d0201c0d20040090000800035170b0021306141081d40396000c0718141140b59003090900d0f03402210062409400d0720003041100c003030075070700001d5642000b4401c0c07440d041170406004250805411043d0b15040294000219510141ca542180d0403110403444081e542c113080c1022483c1c85070a41e000f112140542c0c0400403d141e016004144506000c181c4501d00c41400309840040c44000d940b103c0004980314002070041c1c5c0600b0050042e440c40c200414100300040d03803802d441d2500b08030301d07520351034000c94100080c18030009040007a187c0340c1403403030410001c4140b0840c0b0214a20002e803055034801c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 656582320 1250 656581070 656581073
    0xe0115031a1f05041a0a03140c07060b0a0819060c170a020a0201060807061d01050c0604020904020f04021b0c03031c051005040c080f090303131709040c110105091c0c 73
    0x201d003210020f040408082440c820a68a41c0007140c100301c021b03401003800c01c1d00b502500315856000d21703c64007585860310700b0219151141c900809403580c000d500501c0d1a03001081014013040031060320b108080410103407102914001081c0c4500340010410700c809032103492115251035844650000110500684600034510120302500456010000c603004140004c2507481d4014552400e000355480e042d00c0d1034051000447d5035200741c40150880e500900d02150051070400d240d5908580000d02004501000000180c121780c0f00c3c0e5410300e40f10402c4d5203080c4004106105421400d44210007441c00c02000b52100700600206241d0b1a190f81d5450002035100c400340f42456002e0700c0b024100308a044241103000d09609010707a0079040030011200001d800d40750000803603100b08400190f80361184540e50303800f448100c44031b000e07600f80c001c2400b8406442d1628455881400895a55030034107610068100c0e00f1610090030096160f003040c103482c40031003058100c100325001300740b0304031988036602e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 656583570 1250 656582320 656582327
    0x2010507060902060f040806150a030b07030603140a020306090a0812040c0b0a031d1605010c080909090705091303020a02010f0201150f060e011e05130e0115031a1f 72
    0x9510b0080d4014008103d41007040407040251080e69070482c21503641d0703150b007142e5040100c1c210030b00960007541102d09100007a02c8003405a0003c81904000c01d11940325680c03445621000f10b80e082c040d44c0500d00a00a614041010a800c0491107000e0441d812003501d0b200400e2040d40351034000d030900740e030102e410811034003219001041a5402a82c9a15600c50014094814418442e05400056a0640c081c4902083c036100451080340c10710155450a00195040301920000741e95100c002c3c458038515845035170110b4400d1200c8400340205038203080c10840c0d000c0c0003074101010702d24503007917410020ba00090f2844090760242091000c4540c0c4140890140000e902207212031382c07091400180e4024400c0405064880e035071030302e00184841e100110b40940841d02e84c500074000c1c0d400d0a125441c01a00107201e03a8800d055a44003080c1c5504d42120308842c207a11007200c40a000101400302039040c81408910f0100407080c18032915002c001070703101003462801c0441c04140b155141200c070301 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 656584820 1250 656583570 656583581
    0x170d0e0a0329100303031425030b03030706020901230d18021201091202150a020c15100e100e18011805070329130302010f0f0b0f0103050903070201050706 68
    0x348100142d00c80d1600002421140f00c441c401180400c0c10080502071351040006014401d0881c0a1610194044182480c0100b11384400140515648110038903868a091009200d001e0058401588e183e003113034001042c540c540240c2c081041d0581d0003042c00314030030500b220742ca40c01210004c2075070752000f501d2000020b04090020740c04004850301d0059000f045d040403050f82e020300d0400c83e844103000d4044c5e8807425074011091000603158006001080140e01800c40785141030116074823142821070b50b201898050300c2c0141c1c40d1840c07000c00c0040101a100b0954008509501c1c0e20f4114a4007040c01c01010011308850124590103515800748882548a42082c1403d001ca03100c100c9818105103854070034600058880030000c0b05940c1128081c0100907003545142c0c0d071444000d0380c0300c1803030300c8403158020000c40855488403c06940340140713001d9424210103219000500b020081e04001695040d0700c00c0c42d06250824080001d0030401006840b611902820101d544102d10b14050b8001c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 656586070 1250 656584820 656584883
    0x3041b150e0f180417030601020705010c05030403060207140c150d020a030e01020a03020d051501090b0d140114041a0307091d031b060f040206090103020a030f06170d0e0a03 76
    0xd0f041d10ba80c07880c1c4840000250145002e84076120b00c8100320802c2d0300c400d2000b1903403240581d016050403c0f00d54031401000c0006d50003501500e080c90f4882e9070b114266400312038161051000441c4820b42618140300685a4240840b14400b1001c50703c1010f6040303018801601e8000c0e58082010365501e40260419030305d01000800866031200c0c40400500290800c0442c001038038500800240711004490b44038141030016100c400c9030a190601c05565a0303c040c44100402d81c075141e0501d92500103810550203002e414200c1d0010300820781c280130440c1c0c421b4481c00207221031400103030003d03140420040b00360303043c169002c02d0310019594915000c41d110100380595200004a170040c0b0180e00b01000b80300d05503201a11410713160142d0f07100c200b00b401e40740a035101c0340070031006050350b01903402005044401c3c10081610001c00c90180102c448640c040300190b0b80d1105007420040c07041c402c1d410100d4803410301c0c2042c1207007000441d500e6121804010700c072005904524542500c061003034079449 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 656587320 1250 656586070 656586079
    0x6050c070c0602010e0d0905030a0204051b030720030a08061e0a29040f091805010c0c0201031d030d020d02041203110105060a030503270d050303041b150e0f 69
    0x10b079a444024000d024200300540f0fa07006d000d00410b0143d100c0c1c8955000c81d00e004004201c1900c0329001c00004040c0500380c11080c02c22034800904100b00030010b18030441d0243c9503010403d0215068030b4031254901c402c3d0030035030003c200407125517030805a1950402c001b9a440d080350104000409040c10452051580c080480540000d401c00036a014031009010450304044040d550700844007540240c1c081c0540404c00c044040c0410022603002181e61840381604a400140f9501c035182116114030742800000c0140c0c00403000e5580501900d0409980d00410b00604c10300100071940324010b4020202d40c41d40c0000d02c01700941c00d150180c8014180b21880f0000d80c948603d4090704521214007401d65a508000c00150540b6003240768034200da400001541c9440d0941c04c0c080c156040c4a00d0101380c0000070004010140c0756201ba490034144a08008c60f0f42e0308103424100e1030075002c13030b00c0382c1c501c41c041d0f400600610411180321440c84465041170001030b80c01130001207440801c6601d49400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 656588570 1250 656587320 656587343
    0x1a090118050a06091b090204240f0e04090c03060b1806010e0d05071502030406090801051e04051606020a1109060105070f050c04090305180102010603080921121b06060d06050c07 78
    0x1c0d00e816500810882d6280085009c890180e070424895983c1c1c06000d2401140c1100013040c03009004103001d03c50310400500c00a895041380d0366180041034607030001d4a525035100700c0c4001605240741ced4041d100040b440d6000c202d00c1c1030070000344002403841c4030900030118400d5860800800300f010401400150814194108110400942d00c0d00b0a100381e20010341e0501000400ba0818400c2e21700400c1c0720314210104508107400070a03040005042103c85214200c1400c00e507000c507100c0b1344003030705140e80500311000141c104034041c0c3c240c0080061142054505012060f03820200b00d415607a488015a690a440e0b410450b040c40000608140c00904208850f4205076204000700203104062800c81040c2c8104001242214403501000304480001c11000d00d56280842d1088101c801003241400302011810405c0c1c14500c6c0203003c01142c03540461012101c001462000e1013090200000305030a2501c00d001920b00341520318040c02e4070b03549201050121190300704a8000d99004040c0014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 656589820 1250 656588570 656588579
    0xb04051b1606061509061404050607051e060a0e0f0d03090309080a03181d07050f13090911032e0b06031006030b03031c05060103091a090118050a06091b 67
    0x100c10464070303030300042c2c0c5e40c2c0002c6030490194a414076011200000b41d420182170200b0300505070310805040e6514811305840081c4041039005051190502c40098840d40c1000500002910003905500c2d519402404031003110020004212442060354900450410b0803801c0a41c0c010285412510141c0541418007040c036401c9042c5009464211200601142d070795580b070301070300404510460009050401080400b441071014115842100100c107184c2004010074440c008940d0307114070040383d101c04556003071144035070803107285075401d03009007003154075a0041070619030400c55400c50800c071005011f01d0b0f0040d80e900645c49010094240c6030303a0b0800c3c0c00218401c9200d40725140019040c105104031508002c81a1408402c10007444d000b08940090800c024000c010869410940d0f40d03d09000407034104d841000002d102400c051003d814100791940c01c0d42d40d01d02c03c0d0303004415000640b200042e800503030240c0706500b051000815504e6480e0400c504aa89010708841146404003c81d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 656591070 1250 656589820 656589839
    0xc17130303091806080a02010e040204090e0f0706030207051011070c06030b041505030c130b100f0e060405010507020402090f3c18070e040207080307030b04051b160606 74
    0x4141c03407000c1d408001e03900380b6042c0c0f0310a443d0343d4043e0580c1604005010b10065015036001014064024409801c2546901031441110800c00c004e1240f03511114452611610600052016041502d0709615110641d10b44580e60b0b102950100c0c1420f80e9042060800c00c06603007950780f01544640707011a0190354410060240c81e41381613041c13089151400c03289101810802c6242210005005410ba485c8100304101d40b0504140800e22a540c541c080400b240d03480d000b0300c0e0962007242d152040889080c8c200200b4403101d200415028040402007400b90340c2c0c00000b07541080354120b8000d60340702d0403840814414905200a036800c002a1142c0d030740b524019904280c0402c80d51002c0782c9100b40c044101101030400a1a0250000401d01c1c0440c03c3e0312002c010a0350003a0036003000462042400701050490340708070015030304244080180414180e06000340040003500302c60600071801c0400001c00740080c00000a4030120000408101060494480300e001c541c20003010007540da6991240c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 656592320 1250 656591070 656591087
    0x302030a0807020108091b0409111207030c06020312010302130207061509140105100309021f081605030925050d0c05030c030a0c031b03060510060207090c0c17130303 73
    0x3c90101c3d01c1000042c0c0f40c2c100002e0040301200344054501c02c10707400c210601006202920054400c0800e030f4445950689078803d81070500002c00c80140840e40c61330502401003401500070a0031500100701c0f80d800700941074801c0341502d404448102d201c41c2c010b45090000d22074041c00600d10360800103190f110589051903031045401d404002e0102040d034020f2010841000d00489902400401c015800c403481f82d03001c0ca48103480031f080c15800306155420340c900c1c6030084000e4070001d1110b204102c1d44e111181d2030071221400905101d801e6082c07440700140c0399541c00d140844003d540409110001100d0368420000b8003003c1c20b0050307085080d041c9000d4000980c01007901078414905c404d1500c0c10006400c8106c580c0044098403500e055584e100d0301c81a051060a4100c110510f022021480c03502c42c07a40076114000050400c02e02d80034000c0d0030181d03582d001003c040c0c9881c1090001d00d402102e071000740c41d800700e010402c011568039099003074003400054076517040c0740180100c101900400785 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 656593570 1250 656592320 656592323
    0x91d06011103040602101808070f1518260d0e0c151e190f08060f2202040801180b0a15030303020304052521030504051002070302030a0807 61
    0x1807003400961031082560340c1c4114403d400c0140d118102c9060005125400307540c601028111448949019440d09500d5405c104130680725105041c1a010800070100540884050b0140703050021910400d885440c05420200180c15051191007658028003002d4100d801500341040954035040c00d005070100034082c0000d001c02e90f106204e001c0b0514a011442e1244010050710307080d10340b5040c02c001c449501d8411704120401d03a400c1c0f0008425481a402c201070b50704042d900c009817640c03c440c008200c1a405402140290090012068652610301e40c102415031141c511002c4051440721440080c8a594003e101c503510b441b054100c06581c400600e0b200c2801404600415101c02c4890030446000710900742d00ca80c0441c80070400240290080c1da841401203094511a26000d44007040d100240c0450100310021590244280440c80030865200d40000200000105403a5406020ba21440c080c1d82e01c0b0b030749080000700d161f51003000b080e40a07585c041d003520000551840d005250740c2100382c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 656594820 1250 656593570 656593577
    0x3210d1506051e0c2d0102040e0402130b130903020a0803040302030309071a0901030515300c030703030c050a050d020105061c0b0609062b0302010b0a0f0b0a091d0601 73
    0x3c4150300901d4042e5140511401d024008420076480301c0f03410726000718400007000c1007001d01488102c90a2000e880140801440c10f046440c0910400c1a07551803208843c00c440e140105418054640084010041c61b9124001460b600c050070241e2624401d600003c288002c00803c00003010390201c09140107005040440741502c0d02c55008150041e09007085020510040c040461b81e90300ca0703002036030440005e0300050f0a40107240c010a9001c4801c62041c0fa00e2400d44251400c54607079844451408038034000a4640d1110040c0040e4403540e03140b06c068200560740510700b05210080c0041022160b00504444561610340c1000e8043c1400325242c034414600601403030700c1c5907500b0041003100e03a8012410071190ba5144200800c401019100c07540001001a180c0da0782c20300b4078684149000009000031280040385002802e5600443c080d40c0103001c24041004102810b1840c2e0050f18901b40340ea40e100c2001c1081200e000d2601d5010141220040c5a80701c0242146006a802080280d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 656596070 1250 656594820 656594857
    0x20f0c030c0a05062a0304060b061b06010b0a0c060902040b060d050f010f080d1409030a050601031511070807050c13050f07020601140d0f0f030504060e03210d150605 73
    0xb038040103141540c0002c4141e00305800d17017038410b8021903c0259032042c450100060104500300200da005d4000340544282d11903071001c08103440108100303070360060929961a515020714203600803c43e915002000b000203841c1c01d00d142c119a21038000100d43c9074090034264030b800303800f00110003900082e00e078552203030407800000c81c00c81c4c04030403150180c6d804000200421000b0035000c17588201d01c18443c459030b00040c411059541c0e41404008000c43c0510000c115070f50540c10b250b240c80e542c84002c0e0200d5481c00e500003d01c484443d06840140da001085c05c1e854200c5d03810b096080a0f541300f002030b4891030001a1101c0f125140d4803150144400f00307203030100d554840000307a940383c0c1c082c01500e144180c8172201028600e05002c0040741b0611075142022030344603a56811104c0c4003030282c210080340b000314080c01580d905c10a400d5010204400800c0c101d42080c0c1482c640080407003440e070507004001600071144249401c00805850303400c1000701c2d01c81e520b980091483d0440c1600d900d5001c41075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 656597320 1250 656596070 656596081
    0x1e0f0906050616031806090f091a28030c030b0906061309170409021903021207030506010e0d050303060319020f060310090612140303070f03020f0c030c0a0506 70
    0x184a04000d4580c042c1500d4640880e4a00843c610b01c0400d2080f002c003d940c541920703031000c1c0351061400610a640720448a00d040c60201d0038001e80d02e800c1000030625000c9100500b981d925965144804261a40007180b07501c1d510089981400d90f07545032026070020780000070403094105050481e400b4064000c919100d004050381c0343c42050b10321951200940c14003124404035a4443c03aa55803049d406004050350500c0c00c0d140b59000750340b00e25200da5002c58504040c85803056a080003015a280440c40c1c404100c194242c5050f0252440f020599070710b000031120790044548038900d100c02056041d40380304c0c600c1c21a6407984120f5200740203004e24203800d00f04103004410401429402408501603203186021300c100760704005c04155209a04a0300001c800f511071090201030031000051485140460811402c50050b100f4858280d910410810401a0b800b038100c800402c041e14025a540103600c14004041c062500715108070700000405040c2d001001841f0001a440380d010b403002075952 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 656598570 1250 656597320 656597339
    0x120c1404090c0308180415080601050102070305071401050c0f0604022103121509070908070609060f0309060e030c0c12030702030a140a0c08030306040f0c020a1b1e0f 73
    0x75440000d1400c0358004042c00000c100f40083d0058170040700105080d2481600010207490811b042d0b1516929003003806c1c42000c40030311050740504401c3c0000c1c500140f541d5105545c0362014488d80303c100148060f01d01180e0310400440d088004040e007103d10b03082d070724044503840381c00a0f90200d10908d1443d000d15000c02c99808216000e081c00b5025500f4001a80f6144000304001407561201902c9001583c003590364800760140070348c400b80d80b2440d100c0d04161201c0d04d0880705070061403d02402241c1000070395405042900100d0503494042101207643c9480c03009481d10b450403005900000c1000c00001c1d40000f803015880c0401c56030702e4088004040310689911940c100690180c100f0400100821808140c0d040402c1c80360044130443d52a540300c006400500da040308145030800010b1000c145414058032850f81e00c0040100660341500308041e542d00b5500ca4020413101491004461200e041003000c0c000300b62030032a50014036900440c0544a031310b90f014180d140f82c260300011940081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 656599820 1250 656598570 656598581
    0x6050a0207090509030a032301120b0108120403020103090f050d030e0606060c0d05130914040506090714121011040f0e010b04030f020301021911070603150519120c1404 74
    0x1c00c0405945406da082204802170240c2c0080071480e0400540c800443c001800d80c514024000d010380254595041c0c40c0150354010103030300202c010380c400c3c2c2082d40f21032070450440b0200ca509080000d8160420728000003402c2c05003002800300d0140350308500d603540d0075801100c6400c520b001610990703030380c0400704180c1d8003c114800c2c03000d42c03081c490f10b02d2207401400101100d414200c903144909680320045070070380d0b0760101c3e10314031441d07114180004c2180c100200c98000c00ca98000d020001c1c10018510303040304080d20818800c580040d900c1100d43c3c8140218940a46141c1c828000031000074101a1154020f20030b444041c0c0e801c0e04002055a680c4031004e069480820000f441c00d4612340b1220407000401000380c1e4113543c20010039402841c2104e210300079035031644600c0240021040c801303041000c5a0310010626003840072004010700d1000e40340c400d0362802c441c4888c1c0320400c100407142001454001d0030007010785601c0e1400340302c083d00398142111044802040303058004c00030701040d00e5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 656601070 1250 656599820 656599831
    0x513051804060213090606050403061a0f040507120608060405060f07050316030608060415060807050306060d060204050939070f080f070b090708062707030c06050a02070905 76
    0x86032601180004400360000c1c4100c004000202c036000792506040b00448040707500c0032010803400070f001c20421406009144c04480c02c2c0c50600040030094000c95114a10404038030f101d20342d41d100007060381b401100120301842145004000c10750302d824000340d55850544d01036600b031041c3d500190200b09091641c0d8807501150766100d0541e1200003c0340c180704003004542e03003410344600010484060800c0b0052103075004218500225445010708012035005400401c9141c001c401c00303020b0380c2c074005000d6801c04020740d50209241a01d0600000038086d54100b554441c6048041c043c280c503100b10036003c00040030400305001000351402c2e42d05400e008100c0c1a001101b44500c80100d401c0d5144001100d014132803051601003020040d0145621880e0100c8500c441c42c0c1c24402c010008000403000341044070010409801c2c05121008103404428580c240403031010030b89100d07010705100d5030300156440344049a01907103e450181694101d04007810040c0702c0c0c01000a0503502038040c01d4002c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 656602320 1250 656601070 656601109
    0xd0216171c0b03101a01030f0e0312060d0816031404030b0705030703240303020c0a031a1312030506100f080106050a02011415030607081e150907051305 67
    0x141d0000c424031002c2c1944488099140c052100c50a01c0d00d02280200716100000c80303104604094440d00240840c0c80c1e1390202c1104600d0400c2c40702450500004991250a0321402545d0f9680d408002880407964480000c00c91180820464404c020218540d20b039140300352103030704514141101c1e011440c0960300c0054040c4407600d010400c8030340540c0056801c03542d60710340454200318841c10424020301031710300c0113201e50300d90808100b0315506010024450750119406000c440c69078450303407103040d0048400300d00c490001000c100031030100100100079650024059101c0d0310060009030007000704685060284142140c141d04003407042c401025600c609032242012a400c0050888558200311011429036507200400032821203840b184900c145414018000799452101c01c0c141000e80c06044001400032250901c680c03c98000001c220003000c43c7c184414582c0e4954214480c005088011070700280c502082c801d005034003a00602d40c0030014000515020303625418844040c0700390001c41241d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 656603570 1250 656602320 656602357
    0x60810050d060905160513060b0d111c0507030b0301140c03062710060813021302040506070c2105280206030915060409120e03030d021617 61
    0x6858801e1504450901402c000515a400e55407035a00d40608643c1d1950090303614001040140707049010242001000310091100314589443c3e08021700860607a00d11142d02e031340c0c6441c826216034054668404022030003555640d00c0000310f8008101c113903a510002030030080c003803e031070034140121a44003118103081c0d50651303156007081044d6040500709550220010030960320920b4034038255041c0070f032a5684d10007982407920b4440000041d603404201072014000400080b9810700a800d101140c05607500017800c01c400c09248000d1144d40c100981c0b000b40428403005000d01ea107480700594518035036401d01541204086940900b0403903004160354030140f501c1c110300c0a0700561044000c0d0000d11032054111740d5000500e160811038130030010f41e01c85010a045840c00030001500b040e010396041241d000582c072220540713440d1500a8003448038442103803181c0e4a040040742c041c003401d082c0c21500c543c42030600c01940d004480e410f84048916658040e40030f0441411a080707901c0a003010303003a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 656604820 1250 656603570 656603579
    0x16200303040b04020a080708010212070206040519080f1207020115150c260a1209021005071103030c1b100926161d3601090b04020109060810 62
    0x1905070010804c903001507480400140041d400c01c2480c01030b1081074009601c80324400e815a9066400070300d40000c542c451014030010413400301c0c0320907070080030f0040c0d4081e050071420f00303200d1031003a007441e4514142c00051401302c0c400d0101401c1e000784520750007400f4a198205107900448402d0050b4480040d8400402040314010604e2682092042180f201d03101e00d0180c40e003000750039102c2010550440007914004959009801811416030024104004e1400e030f0081600e00c40c0c2008a442801780009003c418803103081e41e04502600c00800712980c801d00006000d4a6216090b0707400d1022101403289030480c60080c01c2c1e40e000c50241d540d0310081c07514065020680700c1c0315602607440c203a01a4844d06c4c10100a201da18040d030208010200d0711803401801000c26682c81c040d03804602104810f0010002803280000300c2c10007a1079030103407014003c40000e0b0f0400ca00c00f03a9002a90300e88a1140d0822011070801c91046000b42c8800840c2d0341d81e58010341d91032100712000d40d0f10034a144820b10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 656606070 1250 656604820 656604833
    0x51005060c070b0a02010501051306030c06200607200118020409020a12110f04290a0e0a0509060601110a03030c17040c030b01050d0308040f031103031620030304 71
    0xc000700c1c00100d030402640c81d0b0302045a64010581300f40143d4644d0014000e40c01c1c02d02c954044c01504004c10080303a45151200808428540148003c01141f01e41030048840c200c24003200b1043c94905440040c10002c0c00600b18000c07901c41010440e0f021a8950f000b03200600c90031030030409008843d8240c040350741c01c2000a00441c5822640724a0415011419640862114407a00d22510304000d001e00e9080802186088034200780d4810303030804820000c0c4021a207440700d0014110040c81400400840018201354007580095864001c40d070200010107819803c0075000d545500701f59805500c1354401114441022015100558090081440043d1003684401c2e181d0300b1900d0900280904080448407450b82076505a482810449050080c05903009109005040450b04124201015540a025200000c0002c4c0200854006903000d00d03024130065aa991806000d4030341c3c6c0e161000030b409201c000e41c00e6078000600701064858400ca00070f0806440d04010038021421a500c507034032003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 656607320 1250 656606070 656606077
    0x12170703051506131208190203091c110405040203011d101401060f05071e11030105010e190515100f0e060405010518041b02010204060e1c0807050f0307030f0e030105100506 76
    0x8445138141000021010b1f03403041205560f9001710f901940c0c1c0c40328244100050700034060065881c180003051404002003e91030301019042051320045040d58640c0000b030f0042115109a08e10780c01c21010418075240041841c03002001074480400c11040700c01404191603d0034098080401d0a0042c11001c281c00349005d89003942c41111040703506101034001c0d106980300760008942c940900d41c40000c85141c01c0c041d440c09000d41c80c151501a18008056542c180100041d07440459503d002203800d102e0782884200e4245409400c62200c000c1c4800010311480319012040300180704411161602c1c6001c900300c0d8110340059550354100b4080b0482005401006c003031480d402640d5206041c11040c15011303400304945070b5000162203070f207011006401481c5c038400b4284510030055100002c0400c504c1840a6a60008600782c0c8403082c03480c10901d400c103640104e100b20b1001040c95801c01d40c2c0a0203030708900442da980d50300c040d0300a0301454280c0d601905e6150190203401414041810601c015 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 656608570 1250 656607320 656607323
    0xe0a020a090513090609140d230a110703140d0f0c0602091f020601061103070206161a010b18030604051c02100204081e0f0703121707030515061312 65
    0x6130a00142c1c0e881c8100c5001510131144819070401a0f200d2001c1440b0301d888107802130402d90030311741c103851180c400840d002c00e60a40e81e0402180c0c0c010880d201c0c098030145040020100c4078080c0e200d0404c0c045014044130400094400c080c150326880344030f4401102c0883c00b0342ca50ba900c1d2641a40c814000c0e4008846664001b080213546100f5600015641c1c100380c14160050001d5505241c001080706101c1d128215480c0d008004440050300d44504541c050014003026000301805890300c1a00c410030b00307541c1c0d20090465800426140c0030400200100300c0e80054125141000f0001c1c161a01001c40c0d01070001c0e084003100d0b04030b880c2c5241c40400034220a1040e505180c40e131001e5141280c00a030010812a030000448080c01400d00612041a0810000a0a04a03050803045a0300d500300e010040c140b003840300c00550f0301801070382c015103646200b0741e8204140c80d010300010b000b420f003203840000316824900d030001141800401c4440301c110095090708160300303150300da14003500324507030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 656609820 1250 656608570 656608609
    0xe2b0c17091318020108091914030c07031406101412101103010306050f0103050303040311070b07050a0302060a0b0d030302091c12020d26070905040203100e0a020a0905 74
    0x29620114107540304007010b103d00056034101811490000601c44180181900203d40c0301e0808d8041554268104070740c11a8451110440280e02c110180c1c01c50155003000c40c80c5100d824030110030402d040b94948610544101101c4540d950484402c045404601c211058002c0c0030000c00780380d040480d000c01020180408950041d034085103071004884005205451544002c0010f204000e00d40c054543c100c000c2542d42011941140c4400b80c9a10020780018244560312900c1003044400b84468001003820b03032842e5407540480d040040d1241c6064a00302d0045c0104000504820341c0e41c0f04182c40604081c1c0001c2c1c9071210750342c0c01d500950100c030b2820b030300401e0280c0d080c3d2200300310902d0304401c92207814072141c040890b0f04044d152130070314150003042c809003020f00c0c40c007000d1140c2c0c51012510141540145500d070f000e02030340d0412355034020701d8100c1d000000b003295010460000c50200e036040181860036940d1415160704a02400ca100400100d14500803c22032826208843c1c00045210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 656611070 1250 656609820 656609839
    0x90f0c05032d071d04111209010608030a091707262505120f0d030c05130303080106090b09030c0402210112030e03010b0f060d0e2b0c1709 61
    0x241c461000340480e400b100041e2821070480e044091084d5203010500c044c3d0b0f003404280901e003041a128026250341e024a40705d59000100104401d41208001b065010b0503203941e0070160320002c040200902071148030020720513110804c0000000d4030700440f580001244402c1100220030780b28918000c41c51000d500c0f41c1d2040300088915403060340450413182034110022480d140074008480003000300c0354010381040010f1680200003142840204400d454000752007201c9000c11303160380c000d800006903400b000942c08000c040d00248002e060301ca054a6000c0c3c00340c1e82e045860090b10408021a8158001804514890819401800e40e603061643e0712004010920711500c40280309a000e049040d43e40708803c410704d0f800c10050002d88406600a000342c418081c0030651400400704824010840060722404540c421380c071141c028160396091740c2c0044002c11071070117601940e40400c6850054003420b00e1050740507005003841c3c81da000c9940502c654909403865516008001c500d81c2011341030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 656612320 1250 656611070 656611141
    0xc1b0d0c170c09090109020315070509060904061701060501080121080315030d0c0605070903051b2b1101030c0f050a0c0804081509010e030d021308060c04090f0c0503 73
    0xb860701348076030050000016a4540c5004140c9040500b51030303424002c1450082c0039029602208031500031606076071242d600c2d0150701c04900280045c0d402480c0380420781d00e15003107020b419000002250300981c0c030380300c0998907402402d05981802c00f00b40941c0b8081d50b2500d002489000140d5402505c2c0326070405c140d0f5242d00401d051802d41e036841070005004000320400c00c031041c03054036000b01e031601d000905c403030441d603500f651901001c81e440e030002d01c9101c20b00904d9030342d280c0258001e081101e0310b800c94100300309440103280a68500322220103551080c500d183d4480d100700c80d071041a590f61120000b512400648056012003000c1040028240442c001300f540710000f4401024800010013842030480503c0384101c030007600c4054164142002c1c9201e0140c000103503501e1450030a401a42c07004102c108204080da0b55003d00900d010346c00400190f0704418024104440d07840302e0500620f849041c0410844c0c14030050200810814004074008100c2040c20170101c4084a11203545034080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 656613570 1250 656612320 656612329
    0xc020a0f050f0d1101060f050d030804050c040f1505101b0302031611040516090915050405040506091203040506012c090f010c050906090f030307080c1b0d0c170c 71
    0x290420040401c1d442e0342c8030144e500e02485400018807100c040801c0c603d04280c00200b0104607140b0281c10080302d2400320b803e0210034000d10359a84001001045080c0703d001c00720300a4142ca036007881b104d04141e81c000a550624030b008560f02c1d05260f442c0105101d50b80c2d45800036040c241d07400c3c0c04510048c03000c0101d8802d83c3c0c410f400308a0281c200a41602076820400c41951401000007060301c0130040e868030071903004030382c100c151200307060049007100320758107803c1d8282201c0d0300059120b42004140818440c02046045c0101e40e104156001c5103c881c0c80b522540c13100340c90040c920342c449001045814412180b01d59a9400707442940003d400c3c0100503240140300340c60003990341c0c00070700651a0602091242c4559107900e801d0490038010b41000184c02406552240c5000d14544103c40480342d030180201c46c595640054080d0701c5695030840d05644440c0302315100042100c89031903650310b103001485107586a80c00481200c0381d0b0304025200e4406008204111060b20072410715401e590b99 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 656614820 1250 656613570 656613583
    0x5030d090f021e0a031104022a06070503010e15060d230618060f060c100902130e030304030c02042d140601080703020f0d0501120c090c020a0f050f 65
    0x50030707024441442a004000200032107102e24103002682400c50800350311514401d2003140d130010f020880950101010170040d00c1500d111401584204c000d52910310b86c12103090b00d41041101c1154011b07914282d05a41910081c091050120010800100b0700c4070140c14800858202805c05401c01881d078441c882541c0c9220404064006103856008641d9502041c01e503001d0822141000d0804501c0388145040300c0190203031380a509105c100c1041c1d91509002c80d600c450094040724011400003200c50014002ca2108074424908684280d010031014020102034040480103546075481da0b65080d601e0701c040c0c06089810030340ba40c07201c01c1c030220a038441c10307420600f10036210a401c00300c1f11104101c40c8620381454081d105070b4148001e99078003000307881c0d018580e8200103a503415402c0c84007907103000790082c410200e801c04001145400c60003c8110404d0310894a0058031900c68080100ba02c3d5200e0020740140d01c03002a41c0c0200d500f1100f81007a9034015016a031601d40040d201500b00744 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 656616070 1250 656614820 656614823
    0x111201030b15100903020114090d1a0606071220120405042405101806030905010c020c0312090a0518070f0801030b0a050a2a02010b090f0f0405030d09 66
    0x62200e401c10242c0c8080c100c0c0c810401d0401c851500c603402d280e070405000420107000c041d042003003413001691040e4680301151007001b40104042100c3d5001d18004500460316046c0c0c0c107012030028007064940c10510259054194080010103520045c900300b2505030018880c2c102030344414010b10355111200b44015120011640310141d60b8034103040500003a55040100c0b2000da00400083c4100070344644951400d4034411283c007400800c3d141c908a5407003402002c8010380901c0880c1c00529650150b00c0030b84518172510007444440170b02c2905980307a850002c007064041d004540340b440036151b41c0c80145034800c001071580620f29242d1001c11007403500160590542240f902c00e002c05141c00003140940700d801031030020440e60540d55034212000014080180b0103498001040d4000d28582204a030f0900c2524803c40107540700301d28003203100b001c0c0b032418059482c00c0008115401c00c2c06580d846809882502d0905071103031150300d041143c0c02003058070140800c0c020346041518900034480c0e5079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 656617320 1250 656616070 656616083
    0x20a02040f0203090712051c050f0a170108030a080a0f0f0e03040303110a030c0b060f1816031107120c1520072316030305120c0405060d11120103 64
    0x240b134035002162400c502504031550040c00091741c0c0c00041c0c8001500803840000c90100d0002081c0004140ca0700d000e4640d8140da540b1002c1000007105038402520120a80002c50418150b41c0e43d242660701c0c2d2050014440010b205900014a10b079a50b802c612452a111700d0000741c4030851442601c1160074500e6440031a4100003400c2040c1544443d41c1c800d035040321406002d4003003803903030050240c83c8500c000414907407807840000e000c0c1c1d407100e4544212142c01750640d43c15207840360030001d9901c01101d241a000c00c0780740080060f2403081c440c1012900300759920600c1c0c0724641e1503011a080f0051688010028403550205c000340318144038040d0044500c40100714003200012000009a644140814400c02402580c0105588000c0f5101003c201c41d5070092501c603400000e41030150712055030040400e000d10000030541e01100030250200c1c4d124039003d4640b01d4441d4009203200301c0c4a4580d0000c814412000c1d42035442d84588a40040d400c900c1307191500460300c506c480e0200740d01c1075506 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 656618570 1250 656617320 656617327
    0x6030712151e1d1006080a0f06090b01030f03030c080114150f0f0406030f0506330a0c02010201050105090f010b0307180314061005060d2c0606011725020a02040f02 72
    0x740c090402c2030482000101c0d0083c070a0034205102560380701031f02400a030140c50200b11b070b401400040c0e401940040c1c0c000c1c0250400c4d42e12410b2104071500760803c2180080e19001035200c10501c00d0360228140c1d404400c0010300304e41110204441c0840c405240c0307041160411441e40907600d40001044034845d160045903d0354908a4040e04031041412440885810001001041d95a030407a0030100c00c2c500701320341d204032048500e5018051070318496603d00c00700010019605500003a002114034400d0303000780f14a070780791410701c5003403107050700c4061007081707c070005100203501c6002440d400010341c0381c0400d04007089080c0030580d41c100e51059880105018004040d02020700c41e02d54803c000c0700c0a0003407940b500b0003080e80c0e40303c1d40b03c0300344000d50340e0301810140140c0c1030f07000780c01d17182541c103240341603014100525180e19054485030301103202d5044190000700c0340804148684a4080c01c01c41c58010710381641000408400884210b0103407032045001a595441801100d0805085c01a03d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 656619820 1250 656618570 656618621
    0x6091302160203061f151806030b0a140d0b22111003020306030d110f0709050603010c0f0c03050d0b090403080a0b0a0b0f0d0212090606030712151e 65
    0x10b050b80039000b1802d00140e0300740c041e8030241c8111010101d50083d501246e1000c082001142c2d103818240804601e403404100000c1c100d40d241c4c00c507100600c01125001d20040d03880c090500110000c1e8142500300008a00001c08a040c40102c1644030101080c99444029440c1841c83c6010000000303c40c0380c00c0200720f5000da42048030000e0180001403d086155092501c0003d580b12918101e4108204201507900089002408a0410b400c0e186080f10403958a44808002070041114820301940ca080040b030b0146118044040405a0035102c00f49114881c0d1070440741540400b4000b08142d49810301680c25440e00c18030035204e1406565468047e0034542c070000c0c1542d00882809108002200d02070084003103480443d50115080c0064540d207800c5030207248083e00801e0901180c01884000b006200722022841c548030307035030032400d0300e10340c42d2103000c0c0390200102ea000141101d0f5002c1010b12560700d241c5e0009130800e0a1100c040000e03504010004280d0305d0451004101e02040d00301c001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 656621070 1250 656619820 656619823
    0x506090105040515090615060d14041e0233031806070e1011010b0622091a04020c0c0319020a050a0e07270b0a1803020f06091302160203 60
    0x18444d8001c40c80d00460390030881401c0d07aa07100e024258842c000d004d100510980d603111003c031a0440d020303040074080c0d000084100880c0101c129416685a50a0031b201800b03108201840c40ca80e40d0300401e42401031100030101406070044402c812449803510400c0d0050036507d4015510840f19030828560482d50312075401c1c107146014200605120401005110359510780301c00c52131190b128038203204246482161a03014041d11071000d40c0101000840040340b60f06400031600354601c0016800d0070542d10300f81c0208803200350050703000003031a20001c2410340c07038250010030700d882d8604200c40300040514006424044004070015179000c09161440443c1003000c20540100000c6071031004240c0761500210044030014400ba0800c07140c0c0c4652401318002d000c4100200ca62082c2124030240c660441c0012a4800b08401e0040390b090020b10900c0031103000410103817a4091301c2140c0026404040c80015001241d01552021443c90307203404490341b520180920301c0b6981c2040c0100d404900506 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 656622320 1250 656621070 656621083
    0x220503011118150d090302010204031407030320060a1802090a1a010918091703010621090c090b01020111070501020d06050303030f040b060f0d110906180c0f040305060901050405 78
    0x20740035040e80f00c5403070402d5000d02e05448040d01c0704500480c034041d06243c124028804e680005000451100105600c0100003e0401c00d5a02c02d40308da01480142011002d46142d0601c11b188159100100003001d8224981000b0b86840f0b461382c0a13503151400792300040300003c04540340d405440e500c01d6140c00142c3c1e9025502e00e034a80a00b0850069400c0591317203034244840c0080c00e43c9141d2540c4a507410080a91a0302100d90811030580f9103a58440100510b038629420910780c641004102e07141d4000443c3c420303000300a0380404001041440d01d03140794090903c08003001c0c1136541c2c2e02c00300215003124030024000b542c4102c00060340c1e01d0800d99500100c030625088240241c2c814001c00495180101440da0060f401201a080a5580d10700248401000e075121035000001018110104000da100e00d01000070229051070b6a03595039010f010340d4065942c01e002035002058081440700550100504020040000c0c1907d070540340d4481c05d1500f841070b81d003020b16a44d140d00308400e100090009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 656623570 1250 656622320 656622367
    0xd020a110a030305220b070317071b0204050a021c0204050907020705060d150513050f0c210a0b0303070b0f0a0b0f0108090c0306091b1002032205030111 67
    0x40908840c00e42c1c07801441401401c3d407408841d1004c541c082d81380c02494600717100401d03090350000d07501c04803498004c16442480c908420400c1840c0c1c0407030f0609004008600f099091000c1032160b43c0415003c000c080c1801a2404030016820401c52030015130104c07aa562013009000c0150f50749151030240a204040100b80707200b15003040074184115507e80f4104c6542d0940c41901203600b002c207200416580c0400e52006501c4511382d25241c610340301a0f0401407091383e0a50242003140d07071381f821160952044881c0040b90203070307810f410300050110700c00c199008000c1e100e0000f0381031160000b0900e180c1c421000cd030340840502080105602e41034001a80c0a4001001400210141008502a01700b114442414002004000717810b8444c100402d0303200d49001011182d01c0e040500b112915110003466490f404440400403001906103a0b107402c80080c03456000b07514010b40c030b400401d01c2050051418044c3c10811100040b665024001c0b08001e070581c1814503a502810650303003d80301c0010f2a13 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 656624820 1250 656623570 656623579
    0x30e04060f170f120a1404150e040e0a1101180b04120b0108010e03040506030402010215042001050702090109050c280e03011406011209020409050a020f0d050c1c050d020a11 76
    0x4002601a000130103603031440c08541401005a403150f580241329006030b07004920082e2414045003030050303001680c58002030003513804012040400e210305440e001e507014040e1209440d24000140d551099621401180c48030100442c9292940881d0606078810b07400840d035000e80340021800c1c401100300190040c510600208080011b1794180d40e22405036100703181c407554002c80000e0035a4000c0c0000026109031800001c1c0c145064070703148492049910250b40b25a6015940f0201c0e5400f07882200c80854004020f08003d07840c2c1800c0c036014000003001003610040a000315151801c01c801d08004041404c0310300a0442d10540000300191144070301a0305c26810400405200c500191a03141c201e4801e18101e00c8100f82c0030b40c1e000142c4038051000390080d251150b05400c8c4400400e00840040c800c440c2500102d040784200b00c0108145240a00140c100d800140018508100036074519100391080c440201c0d52900c4503070416402840d46009604614019010850a0030050741c50701d00131038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 656626070 1250 656624820 656624833
    0xc100e0712080d0605120a11100e0d140609030901020d14030a0f0b060f0909060a03120509010e3102040602030d05040f0b040f030306050418030e04060f170f 69
    0x81d101c0309802480141c25003000040188592016030090400303000301900300c41001c15901c00490340c2e1314002e00700344c514500803550709005151403112500428107c2c0c2e9101070b054010420404240c201550841c2d43c0c0202070180c004d807060a10600c0d00c0340b000c10b4003a6847c2c006440002e4288030f0842125020408601b28607411030b0914400d4903089441003000203230101d02c031a0020002c1841980441c2d10010108050965501d181e000b03041507803007602c10100d20b49a05080c05800091408010495500030801c032403010b10400140c40c21000500d05000740342c040e4000320b84030805440b0040449d101c600100d201054101c604494428207d0301c00718501031400c2c200079141e005002c01200c91a46440126040c00b90301260302c3d4101e0340003035143d06141003c0c500860b41c40d40c0003600710301007400d0200010381440c00c0d100e47d1217510062146815030201e1590222680301a04200984c065680c0b039002c42c00c05411032442d0007403d036000f0351082840f551041649842c40c1860284819800305 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 656627320 1250 656626070 656626079
    0x1050d0905190b09030412030c03020f0f0a0515090a141908030105030607021516020a0611130906080c0907211e0203060d080309030705010f060f140901030b0612030c100e07 76
    0x303050240c038230380500d0000c491500903e8100e0816804c001c8101003446070364003e4001d00000301e0329003480f9200e20100d400c0b80340610806441d4140490314628141c01100d0803c0c042442a003268403812441d00980e81500e1021204042c904800c220554420402000522550800b000341c1500b1500c40d000810340c0304114205903510a4005041222140202c01150310305402003003408030342e982c00302050000c4c05440d0b22075121a00040c411094405000c2e40c00217116441e44103000c290342e04030f4040c10300c02d0780d2070040c0102d040d00031301340c10104900032541e40811802800c0d0000490b24010000c1035030401e4540300364404240c1c91030070b0121841002802a507a403084114a001a07101020303613280c2c1e880100150640c083d100010380294201402c1c90405803c0b54003031825240c00310010150640c4401d40c2000d080250139035250069004001440803c082030f111030780c000c0c0002d01d5101d42e401d0354455141107411160351401d41d907000e44821500003c8601074614141c030307400c000f081181d140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 656628570 1250 656627320 656627339
    0x70501020406080f100915120807020102060105060c0d0e0d0f0506060a090212060409080708070303141305100902030c04090309030b0609071b020303090d05060a050a061401050d0905190b090304 85
    0x8034810b03d40304070f54410680c00ca464441c80507c0091220b50742800003010701e414420103d0b848004224014011600046268601801510010f03944a03000b000000c80c2020b080d100101c0310031038035500c1400c4039035a00005101c41c2c03c1c924894840d1001c1c10f07a43c00c11038180482c02d540c6800c03a08140c1c2c0140801c290981441d94595440b40d0100d501040c19915418018054450401d01801c942c400050f44010b140c0c00d41c01104081c41c1703c0d078001b2640e58810b0821071807402072540c010070079000804000700d01d1056401c05442140018103548202002c200098229554000103c0c0440c40100e010001e2014211260f42c0c1b100c801d4494070302d1443c0165004101041016019025840c07924023035003551010820384004000281c4040050203c0f800e00c50b944201c207d8601200d075042a0001d4044c0101d40140012030304020481c1d04120281401925290044517480d90003954865994000c40c00c200002200d103507120f16405aa44a2402c00d84681c44005040c519154810001040402c44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 656629820 1250 656628570 656628601
    0xf030201021207090b3c2d040306242607140607031b0c0306051602060c0a020a05030429030402030307020d050312090607030b030c06030a1d03070501020406080f 71
    0x441e00380722043d01c044003003000b0943c400941c8654441c06038042d00104100b4080200014032604d216010300d182540301890b00c40d11187c64808051805120400c00510036400034820440282e03644076032000303144401c1e148034480f0b91005030b50415096000c503111014a0050301e00103480d002400350a403d0104500102203031321005405a9000030b9820189882a000f40c0200b5040044011101119003041592078441d0b0200380c03900d52400000c0741450b8007103078410324001c41503005444075642c2ca0220980c20780002080c0340c03d5020304602031000031020b01c000c0010300941c0038040c40b402e0b12902500000340e80100c1081c01c50100300300b070001694002080e100740d182c3c1103e110202014900d4010f00b9801042d40702c800340030103c002e0040414010814a00c59015550f042045803a4003003011794406c1b2450000da0400f008001090682c0031603003008101c500c40d03607481042541c8850802d407642c0c0c8214001d0301e09960104081c440b10f070f03000800c0313500411059075007122418002c2145141c0b05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 656631070 1250 656629820 656629837
    0x306050f090f060303040b0a02011e0203100e0726090c010815040b06040302040c02060a0506040c0806100c0b01060c12080c1b0c030a030c020f01051c0b04090f030201021207090b 78
    0x4070407000a1044e0340070004c40d8040c000c1c24417440e0700d44418503c060301800c10f6600c116401d08000203603007078481c0d05200303a900c10b4040142444010342752042c00154218003410200410020000095840c2e203035201442d4842e40d1404804110300d0704c0c0c0340d041d04041c00c0002d0103040142550a002040a14005111581008650000d100004607000407510300c50b5600094115060106090b20260042119881064a14024040c0795141c4040004a400d030840b40404592080302203406030034000142e986074011410964034456494031901c5c1490400d900c24030000f0f1a0b48280c0c000c01c100c00d1604121544981812446403c00c1103001c8100e0045012907011a12280b0112104041c20030044051200141c19284040d003d13060040c058800860203034041d00040fa111a941e5124800311094140050141807420301d4940002000d01165100c417680940c5231409900880c5141c28400700f26403287d000144d48040b201c130b1210920000518260601c5a444030030445803441c802103d4006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 656632320 1250 656631070 656631091
    0xc0f260a030801060e010903061112010503030f04030f0206121003050d08070804080c070b2a120301030f0807020907170604050103112112070201270e040206070b07030b010306050f09 80
    0x40c841700c0c012107d03116a40e102608003410000b1b03000803540d19030700400b40c1036507003401614541c0e00c510915690307100d01c50189084034003c2100308041070003070042000082c401440d061420030b4100b125041c4050a6804032040aa13004080041100c10009801e80c61640d0038041000e181000e4050203607200104050300803800069040840f04080c468031000d040c46c44059500c1d2070350076080014099501804c100940302828803041882c00005000d800640c2c2c010b025480c41c2c1c01d6540d8a104184950002c4585c0a0180840b80041e0f83d1a07101034800d202c03581d603080328404945030b500c081000223000280507510b4a030051011403243c5400a507101001c0c0c5030321541c1c2c00900294980c012100c03214100a014a48012185c18044001028400c0c000d0341d81c00d00c21307200c0408000d500400d130b811030400c182900800b00708240058180540c41b5000401146c24141c0a8840b5075681c10700702c5078080040d41c0d0344000070700c80d038140c410300001c2c2600b0340b58500e101d105600482c64415003d0040e1707908 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 656633570 1250 656632320 656632337
    0x50901090203090319111504120c170d09020a05040c02150709050909030307230d11090301050f0907270f0e122701020a020103090c0f260a03080106 65
    0x10b210b42001121200781d04032401a20320043d100001b02103907107030380703045120b8001c00040c0d92001c80c8400c0114004d54002c02d4900b400c0e1a0210f0581c1d003d4100c1d48d00700c502401c0c0080017441c4a001c18050004082054404101420a84104900e4281ea60409807007246080070f80921181e000802803010f84541c0e0300d001e11612900300c180c407d0340080d072115074001c0d903c4040007030510011020f03501490076a00c40e0f0f02c6001c8504000b100111105901e0112410180207800c4040915000003928010f80c4446a1410030000082400c0d14000c407074000000625000b8000c1d00c4100300092401040840c41d0300804040c8201c5088a01400c82171030110107032144400d0012410b1580282d000e007902d0300849051920000210104d0f80200c1001064410041800d20a100107031550215450b0140c0c0903120500307032980154020703d01d4100507900036414040110391a18a10204000740c2403c02d002e01000880c140041400d1988c0c904030002034002c0f14400c00002e0700030900a042d640c041c1040d03039a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 656634820 1250 656633570 656633581
    0xc09040305090303040b09040e01051b0d0225030e120318180106111504080403081c06180f02040f0302090714070807030e0a0b25060c27050901090203 66
    0x900d4042d2050aa41c140070025000035203452036401098006000d03141400141c648080705400c03500c044130402c1404c41040d41d030400c1c0c1c4071100010500c19580620042c1000c602c68903c2910300510300341c0361078006103540154149504120741c140c0b40c2c0030407905603511342d0b1098409622030003007003002200b0314100e68002e04030750f49000c20a04040000c10540bc031135070350307840e00030000c0c0480e04040ca15801801c1055030304916242c80280b085820010f100d14052035980c071042654045040c081c05242c6600c01102e000210b4010180203100e840c400300008801c03080c007141101c0c0d4003000207508a2040104200e4150b0604458044039011502d090007581c1d403070b6040d10601801c2141c00e201460010715102046074070304c080c010580c000d82c1c94a1410703101c0000d2210081c101d00820003c050706000c3d20820707080000d103030810340c141d040351803903981d1710f6079900400ea802d01075281c00420b260580d00094042801c40b200c1041c6810241642c1952420010426100c4113000f031405083c0c0020001d00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 656636070 1250 656634820 656634827
    0x90201020703052e0902010f080a020d090809031615030b0112020304031e21050720060405061f0302060703090e10051e0102100b03070513050105010206010510020c090403 75
    0x458100098a40e526411002c0d030130b41809040039800e06031000c0c03c0c0505101c0843c491000490750685841004c2d06144009541540d00142040e65032a0208011145034450340103603945544206107058498039418200b41c2802c080321045003070494200310800207203615950845c4044200d0a001408004d0400100d6500d80c4103e0500e15850001080c441059800110007080340884c1d0079001e20000500c01c01c87e0368581d104c1d01c440c90005810912070000c00385510598028040b410315104900000b294141c91003c2c803e890411500401c0800c0b06101040c000c030741d0f2004114800220049030358a59401c482124003000c2c0c01004042000b00415000c0c5c503035400900141400394800c0c3c030302a00600421001402818000e00f4403e001c50100241329401c18180c0341d05030090001c2c2c2015500300001019100019a032620410700300040640f5010540c10808070840d4020440d58105000a0324041c01a0300c202c0c0154001c201c0801e40c00d6022a02c401d28a008440320703106900c0e03500b0100d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 656637320 1250 656636070 656636083
    0xa0b04020103021e04080705060304021008150a06080901060f03051906060b070f0201030e061902030402060d140403021203040201090b0a032c06010b04030803130515040b04110904080405010309020102 88
    0x40080b00c80c0050754030f07844810340043c104569042c6c044606558940c400d01c141800241d5009400c2110903c40340d01050254469a0381301e6079241300010340000000004e010241203621003804140340e0018845030000038054030014065840000341c5007843c542d104c541d52030151026919001440000c6420002580c10920062005c20344036621400d050900b042400c0c8403030700883c00701349084145240580d0101340a445104050310104001000132142d40217580010000c0741d00040c1040904c1d03818030540b0400361880c01c1440c80c2c03c805d203010701c2c0c040d05c0e140c0f5049104021040138400c2000607a8000d80040945d015009569202c1c40c00400a8014102c43d02103019101103e004003101d50022190342c440c614051012940c1a036601c4c10401c14a200b10300018115050410018a4801e80060041e00d2a8460380445503c411b40d415101d420103020b81d41200d40b9020003061100340084818000441c1e0001c6550308000e051507a25000c1d603100340d200d40c90605844000081c19a070090080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 656638570 1250 656637320 656637337
    0x15030d0f0905031c080702070f0909111917120a0302070203011e0e120f07110d140d030b0103050f040b09030d061509080f07090b06070f031707030c020a0b0402010302 73
    0x8640c0c06101da44004645000c4900d2013200003080c110004070000c1c40024188221214100100384444c1040e0f1814058800703400150741015849480040503110310403000707880c1c203488210b40d0b4801d0404240087c0c2c0300420300c1604040d0300c00d038000110711180000300c404080c100c0c00e005941e402284042800752064088240035075800c594100341440154201c00307210484c8a0903183d84d003110f400e0022007801071040300702d1041424050700002a081d10688149000000c1040d02003d00c0c0c0c1c0d8803804200710007140d0790b4850b0040040c110b49640c040c01800040542400e040c411803402d2081010712000050014002ea000b050200f09000700c10f00884a600301e840700140030b003580790503146803060a801102000581d07918000280b100001c40c1440524075410007414181d840c011345100a050320203403187d40084204041c4d000070703502d0144044054401d840f0400c856110f91030350070020030005c2c000400e16013030410b4400c00d1980454a920302d150300c060307848020b40322400100d0003801078070325 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 656639820 1250 656638570 656638573
    0xa0804110d06140601020d080415020c0303010801020a180302011e09080a030c050706140a080601051903090c0f150507080723100207110139060515030d0f090503 71
    0x4450040c00016002a05003e0ba1070743c8800d180d0f11050012641c6016495a64000820310380110740000c0c5401c4940b04440c41c0c1302409400c040b420400c081c20f681c0700780e0000c0080ea50004410000b40e4001c2c54203010603680100250071145160006010f010942540c0006044203441999045000b80300741c0000d0100d4008a0303026029514001e0215500d2500c10355142c031445000045041c813984001120180b21602c103400c1401c1e4450650b20100054106030600c1818003500014005c6148010040301482c1c1d40894076440a040900c03400351707181c01c42010701503a00410b0010500c0c440c1540c0200403940342841d0781d0302140c200340b1294040c141d03000b4022032000c00150300c5815100000f461850011081d41d003611320001a0714101d20811302e004004d13408055507070900e50700031595000b060700f40d010a5420170200d00d0400c10f0f445101d40014416002200402040c800316100f055070240180060000342e01b80403001036074075400c0100350003c00c00c1c401c03203841510388210307501d0004100180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 656641070 1250 656639820 656639839
    0xb09151605070f03020303160c0503030d051509060a140402041703040812030f0f1806010b0a09060309020306160512070203030a2a12021b060702160b0a080411 70
    0x840440d285000094140c556204103039021420900c084030050407640d00a00452400384640c40150f5a00c6012038181c0d44001161400141920184018420511903c40028041c80c0541c400700810b0103001809001e410312a041124507108c0e02500c1041ea14003070007181660100b0000074002e8481e0b600107140b42c00101031500003108001024000f51150756080e601c0610b1a40010340090000303c4a0845110b0000701203464403144840261300001d920991085254040004916037074003a4060355001ea800585860b017a85e0160031400581210701e0180b064420940000340e540781d010b071100d006e429150f41d600d076801c1e0084044400798407104444540500d40b192000e03490b40c008540c0c640c4410304002c6001070060342e4100f8400315154440c82c0c0462020a81011525054880c880380e00c583e82c20800d140d10400c0e41c81c00e0041005407a030040644c0d290100c1c0081c10178946640382c0541d2000c0c0c41d01442070710038130070546040911901c2c0c034500d03a59540c200000d10a01080507540c0000303515 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 656642320 1250 656641070 656641087
    0x30d12020d1b030e030304030c0b070302090603180d090e0a0f24030302070b0f1b0f070e0103020a0f030506010b0c0703060e0606040b030705100c0515011203020d0e0105040b0915 78
    0x40c42c11569403800f40c4041094071114a1026101e1104640080010b41e02224290006140158241e0403911619006081001b0000451055401540c41f014825141c410b141d00b0f0050070403910b40d00303260610302000402e01d8071400380e0445001400b010015500e5642c524020318a40e8824003860308040c40707401645944172848220481280400d4005004040d000b040f0080030404642e121440b0004c03161030800e116010840a4035640740320b100038051030030140351140007000344502801d00e20707007900182e51441c4100402001d03135074007120074020000000c0011400c04a20b0074112917895806c1d43c2e070f495070300740c0007800c3c50f00540004007102e10340b034150a800c000004080780300d800103503001c00151500d14201550381102c2e02c07505038400c800030318503c10f40d481080107201040c4207004480a08280001050032401d0076000a13100820110000e0140355041101551016084c105010440070040c0020081d202d41e015042048000050003c500c0c0c4400c1c0340303140c00010f0f4a1b402e0b80c9900340b8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 656643570 1250 656642320 656642351
    0xc0f030f09010804061515090602030708070b10181e0e0a0f082b0b0f0f010e0a21030f0305010f170f07060315051c0b10120b04150506030d12020d 64
    0xc01f075004000031440c11300802d9682c000422680f0f0302e6007000302141400600e94580c0300ca0840107000c10440c5c42050000550745400c84a0550304655400001c00c4401076072000c2c00c524500a84222180760400805410610010031414002d84e0008541032722121541403241051140807500301d810f8481640e2105012484c100c2d8031100e003010030b410b200204d812000c00c0b40343d50881d10011391140036092600001d42c0280c403502e044250180206040c0340e40e81081803186031410f0400c102710202544520105a03000d048131480420394103007008994100b181c1074414040501421803170304008640080c0c02c94040091074a48130a4208aa0b03610380c80b090001c010b01200c003070003139503007070100f802244034030b0301402710100c402800b440401d4443c15600c031000185001743c040015840298000314094982540114180380221085c847c00d042c54a00040200701004030450260718002c00d004141e0f40c0400c0c1d0040281c181c1c41c2c81850b1840107030114000748500c40f40d118500d032506030100c1c030203580c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 656644820 1250 656643570 656643599
    0x60f06091f0e01111501090203100815060108070c050a03120906051e070c031407020d1401150b071e052409060a05070503011818080c0f030f090108040615 68
    0x20700381ea40d040c008000504e500d80c1d0f00d1046101075241a090b00041c011034030140e021303591002c1007181c02040d06070744103003807401c0400d8039001252144855080007404c0d60058034180d00030240b4035101c050903010f03449982e200d40324124002d003040a880c108004808054000c1320045422610070401402e0080440c41417a4070b4100071503c4038850000518200d010742c910b00704060701521409808a03006602190b164815082203034040c1c44102c40101250444400f4014010200000900b0061782c0350b0580b0603402d294410042c115007008520b0003e01c10001c00d1311051080c0d40c2503070100072075150040c1010180a9086201c244000c0b40c0302c514000100142d029000f0344003034840d19100c004016003900c00850f85403010480c2080100700d4041e09024402a14840341800a468108040424450300034000180c50009c8045110100300c5000e000581540c84030000651401c1c2c1c00a1514440d4065508041c2c1400380c03050000d000d01010b0703040026482c0e96076190805160300c40310103030700621 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 656646070 1250 656644820 656644847
    0x7081006030f02040e1311091905090a0f0b09012a050a0306170706080f0f04080f0d1109011e1b0203190f03090e010f090c02030d0f021b06060f06091f 66
    0x7c1c10281d40344a80d051400f4070500403040004c42c6a8202040b0884102404000e03141c0d060740d118011811010a181160781e016540c0b0804484100341401c1c0621425120440561500e00c10b4100205001c5c4081800c0c01941041c0c904000b9243c6124034400e40080486a0010514010360108a29100740c023092010030368038991030300784290301c078001040425a001c03140c1ca2a443c130414085070100e10900082c0009000500d10646071508903ca00000d0320b00607070320000c501c24042501c0d0003940c1c10603000743d0502d0080701002d10720205584001d001410080810812541803141c110543d2030900800e03035880407a01c048c910a1701c5500c0c000292041802003580020007442e00861003a94105101e4101c1c0d000740d0864170614101180d0708003d169020100065210402c00c0100c1c11440d4001e80c5021111100d005848490100d408d60340c845141c9031030000d07904040c003044890b607a41c00d40c11181c00300507280035480744201d0300410800b544d01036100c2c0c101e801150500401d036034800031450422 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 656647320 1250 656646070 656646083
    0x150e070314010c0503091002220e040209090616030b06070f0f060b09010305120904020c1501030c06020129010c0f210c020d030c1e030203040e07081006030f02040e13 73
    0x16085840c04031082d0005039003001b2250007008526110b5075280d0068a4580340c400e80300400b8242842c4580b00300951507000700d030806400300c01c210542c40c08003c0030b54030203443c0c5d014003500e14000e00f21840c80c0076081c0c5d24005050b070b00c50402c03000b070702c965082c2d4800301d42c0000e40100c1000d07a81403901a241010904403805405c03c40c55075964180001f00314100c0703a10100502404406000510a5030801d115003504a40e0074031420201c2441085582500100110315104039419418008180700281d0411400c0d6818108118000441410344001d04510707482c9003c0d942003008012100da941840c009403180500c858003030140500c0b105244150061410000305040e25024151825044507001039880a81d061070100800d014003283d03648540309803080008210482d44056030342060302015401a80003180a11580c80c0d12000c2940003e507a0178079081916100c00074000116503401800d041540711a080490341c5000c5d01070382c024044070f68101b05280b800308003030750001107010702c2611034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 656648570 1250 656647320 656647331
    0xb0c0d030207080d05041e0b06120c0a05010806030a14030a0f0c11060702040e0d21060806130804050907030f050703060303081314030325090f03150e07031401 70
    0xa64020701c01c55204903400900281040b0700e0440003001420014000d50f14180c44428296040342650382c20140d80d449642c40fa412030501500340071b009981c401d10b5114640c80205101e00c10713a9446041700845d002403070070000329601c41011a0501c070341280700602d500e8004d040041c0000000c0080c0014020681c0c0b4150881d5241d80700319090045103c000c0c1c0801c010540340150f5007844001030103164000391020903512020a142443d24100e100d4400c0081d07040d4031448050b440700d100802c2509282401841a03c0c01d0101054650501414884540e00041e1141d000c000150041e2030040000614984003464400005400b5080341f200142c09103140000107403d4a0180c482c000680e60107684109445d07652140c2c0d1015002c1150080d900c01c0b040300740c0306402c600104003d51103980b4403082e05614141b00d00300303041e0705851703008020144643d030701d4140210300c14940d48002300d130f030405288180310f070025052600410000e84600540d0262000200c10301048407100c0c5031109038040200328 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 656649820 1250 656648570 656648593
    0xa0f0902060a0c031229040e15100806040206180a030f0305040f090c020709020906040515040509060105030f07050307110a0302010c020f1f020f13090c020d030225030e0a0b0c 77
    0xc641e040c0406d2101802d440090400b543c0380714035940b6410101420000c3d19085c0324610602d0303e02c0d00070304050000303120001c1214401050b04244002d01c2c8a40042c1650300341507000515501030514180b8080c164025031140d140d40d0042072800131a041980c1d081c00001e40e0800901c1c030b50080c0203110b4013a11200d400509000c26101d40b041c0c100700c1d07070f0203001c405c4c0c109a212400f81d0302200c5681d6002d84103001c0401d056940480144601c10b051b0302c02c2d43e07034524060500100403001410181480740510400400f0400c11a00390380c00301c1c0d28505903a4079500d600c030903100300e02d85940c81d14452143c080ba40040640543c840c59601e01d042e021503101d0b0100c60b001d555110100901d2401d204045080c030b0245c50501d8000d403000d1404c400b040340c00d1035446414000d040c00300d9407040369415143d401c0c250000c0d4060042c010a0030701c5280035450b150004020104000a0700007040c041007034200b80e41c050612424000b605800c004024001d40c1d5962496404240c03c1040c10401304d004202044d103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 656651070 1250 656649820 656649857
    0x20d150e16060c0f020103231e16080c070c08030702030606030c010507022215061d060301050d020301090b090304080601050612041203020408010c050423090a0f0902060a0c03 77
    0xd04a618030b5072a040c415207070703030b54a0513a0201c03500304a0505031250242205822496842903411346030300401c40503864440c000c9a00c141d044020505500905020b10848500010310804540c1107420b01d10070b16261080c004006204404001d00390001c481004540910040004c11302c00380210221005600c41d2001c160f16409801c00f940d0104208102680040c00c0290750704043c0c079404c42d0303a07060303e0140d50041c0c002d940c2ca26260040340540301c0e506202207a08080801c8403e210049441440420f020208205201c103021b503e120f2694210390400f1035800350042d1100301d9220a8a02003030410802d030b6030782c81c0c2080c056416140100b500100766824094240d401d8045550114121138a55403203d160514010f00d903d0304246d000c10012502c00d00c00d0291711003040380307651140c0d511b500e05114400c0030380d12003000740c01c40000c0c140e08100303980d2121150f582201d01e07c400051105a00d248101c01484500d4009400c10740200d65461030f0368000520440300d601a032a44030800300c041a581 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 656652320 1250 656651070 656651113
    0xe06100e01030c1101091103100b10030911280b070f0311070f3002030a150b040e1b0105070302030301090507140706062108030c07020d150e 62
    0x1800030303100c1055903a0340d42c841e030801c810031909814020141030011101509498a0410641c0d04ea02010100c086908041040708120150018200071101c42440020507809034420303803c04047d120b801c003000f0701c001b8041036070000340010400501510300c201ca90840c400a2114010804962503000400444603421141c0740c61380400301d1902d2402641c0d0a0315090801903118019109068000c41d038108501015000b070100203441c0c40040010f410304a4620904401c1d00041c4000e900104006840000b00140c100d50302610420000c001c0d235448000810915803055400380c20f090108502100119622a4140c000c06140118110020055400c0d102e41200200140d004000400104106901c4281c1000c1189400c1d41400310003600c1141d180c018100c02da030340a076210010440c0721040345132403000d200441c1c01d0031381d115070540741c050b01e45c00000d244040d40f540025440c011960f943c0907d405c000d5010101d0070a042c400301200d402801c502e0307107181e03591280d1665441d68074000c1081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 656653570 1250 656652320 656652349
    0x51f08030c19080702060703020c1f020d03111c0902040b010c1e020a0302090f06040e06010b0d022a030403030207061805040207031715030709021801180315060e06 72
    0x1410480722116000c0c402c0d040007041611114001d000307a1005a450341e008111860080d4000c04803c19003000b00034804201641000c000e48041c1c802d000c02a40100d0411020855410700052070f90401520b40d02c1440303050304c015218002006007542c0c252042c0e002c800e07214000d0302c2c00c001c5040100c00649801070044006031581c602c2240c1003c0140300041c1d152807440c4040c1205040c03d076a035012070045042903680721810140f400030081039090034803600251f07001c0c400007062a5450200c3c2e00d1018490f10002c0340550b030f00007450022031031044107803428201c0200da40d2004906517210041d241d4019001c01c600501030403100081d0684244e07400203608501c000c072040c0c0307580f034902040000d602041c3e04500f40f1544111480d030107440400850721505000c3e5241c40f180b08288101424038415030004100c3c9481400b41d4a810191000e603101c40070400e0170319443d41c0f0f01460040100080710390000b0510710704000e40c200b040301a074100b4811120618802d41301c0342c88140c00c201105150541c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 656654676 1106 656653570 656653573
    0x90105271504030e09070239030307030306170109080f0a1209081b1b10020f03030103080a0e0420091519140406091a0409051f08030c 59
    0x801540f000f0b10740702400402128a48582c0e0b445000d00129102023004a4842d40c40e8042c0c0440c00762440780141100d468415614005010304100c0c02080c506000d00107110340e10940500640c041f40f903100100a0815503010000b003540e80144501e00100300c103010a43d101c5400521403004044c1c010003490b581c40325010aa42c6052980441c0b00700c00d540309400380001590f100104c0d9401d0001100e42215440700c414040f03142004514828619000c0003000000700003113400201020710076503e611400d400c0074010441180c100707591007424101e1406c4405a00c18003400204000c050040287d80400905840300300e507908441c54018129500008a080c42600400201d4200c602192010315041c01d01c20001e009480f18483c00366881840c0003000748568007441500d000c3c1003150801c010350318042d014816407038402244401c12026100000c0340040001c421103c45401240 = true := by decide +kernel

theorem cover : BRFrame.Cov 656474820 656654676 := by
  have h0 := BRFrame.cov_init 656474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 656474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 656474820 ≤ n) (h2 : n < 656654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
