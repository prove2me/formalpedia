-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5313
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:27:17.039598+00:00
-- url     : https://prove2.me/submissions/7e4f98dd-ead9-46dd-95e4-b0570ffd8b15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 955395683 ≤ n < 955575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 955396933 1250 955395683 955395703
    0xa140a0b0a24080f010f140f0d03020606211005180604060c0e04050103031d011b080306090606160f020102150c09040501080105070509010c1514040b130f0221 70
    0x910b41c1c0c50840600300070403100c802460000c4085500004002c0d1051303103003c0c141914410801c0314041019100452121408450026440305007142c0ca1000d154020070214002c1e0410366260b0091180d070100c030f00700000c490b4032600903544050401d072072a40441d484203812900d81456003c0c91454840181d1078543d0984081c1d03444c1e13540720800c2038070746c2e04800080d125020a540c02d01040d89103032000f901070703019060300c41d07000381c0300c010072000316881000c9103100c1c036440398590b0b05030003c03504100b840c1c4d420840d1990f00801d004030110300c0c0c0d85061410f40707002c120408041c040c82c91040d03a80110382004c048040f4194030079000c03641c12040309180200c5c800c0c100203005540b92081b9404103c10b440c810780c000800750740350100303100201c1e6224003160343c542d4003070801030b461601624042c0c807080800802540c1c4185403112000c08122920140d500441c0030325401090741e1620341104912142c0c0c558010300b40007281c0c0d44900107040600704040b0351040c004907020480260440315045c0202e0a07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 955398183 1250 955396933 955396979
    0x20405041e0c080709060e01090530031608130f030b0601020c1e0d0213060806090f0d0c060902130603030f27290f0702090a140a0b0a 59
    0x210304491034400034400c42e40d104003245800f803241d04101002400603042405000100280072045c0c1e58140d0040d0b103410300400c0042c10030b0110160b210384050507544003c0040b20350008896001e0700c2c00303500100f41c956259420240c3c03d4010443d07034404a042d40030030202802d03960318450000b0075401c5445600d00850040080c208103203445c100080c00d00c140c0801d010310580c010144810252a9014510019081914002c111703000310b00004508000c443c2224414904004021400705000f08140340540030075011540214410f1034856100d0442e511180001500305240c0000700d0041d40100d80d07080d0019044041e107410b0300c803504042d142c094006801140c841301c1c0103841143c0c04007200c0045086a200803c0180901c03989038034600c0c0b144210059a00f070380b000100c00d03901c010f82800c100395041e40b4190341c42c111480114116001a90142c1c407403810340c40054418001c82c0038401a0688458460450341d0710301800400401c4981c4802d03820150090012900b0386503d081025042c0f011 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 955399433 1250 955398183 955398221
    0x120e01050601081320040f06121b141903051c081302010c060c02280210050f0306120708030f030a0c0504050d0b091f020d0f0e0a140102040504 63
    0x8a8005012040003400612601000c2002078000c545800401e40e400b800381700049507a068084006806440351a040320392061915000141c1d07110703080042c9015922a401c0401c603441940c00c8a001c1d009544250250862012090300031031402610340e0b2131100d070201080400301d0700c80c3c0301d05290240d004101c54244e0010785031040b000b40c1144803241d1280c1868003880b18031000341d000030308100740d0480040c0304544500034480418000d102d01d007542780d5071803e4000700040e407025401c0c484092405c1a401811a14a0040d4072485401110f402001e541d800300d01e2340e1500801d100054411040200b00341c0030340c071400304001000380006c050480c219a48140c80c2d041c404145400c40d5260b60301b280c2444000c0000300500d40303610b070214510725080000203680b035071120f01c214207001c3c10004968940f14410103020003c50180d0290a10288e11841008a94000d80111040781c00002c00205903912002e440000078441ca05a82c03040c04107180050301b0190b0383c0c030100701031b220402d40e4034044e4600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 955400683 1250 955399433 955399441
    0x91104060503011806050c070b040c061701060f08130602030a020405010908030c07030201110f1e0f0114011e051017070306050109051005160c050a12020a060807120e0105 75
    0xe0094101818007240201300000e40c105000c82d4003200800000c2210381c440c00001c8128103401c003a200116000481c583d040d00e01858a0411a0054001c0d5000303d1038a11060b041c1c48650361119068400b01e8035040c1c2240b410480940d5040b0f8002c145840b20303108514001c0000300180095409100180005600c2e2800e120000d441c40c0083c0d00140c919900c1440359107142c80000840c40102c03902030809000341c982c8141010f0030105103082c01c4000e4405c0d403c2c02c44943d18030b880d03d9040e58048030143e40740001490216400e842c012f03a201c89420005400502c501c25001c2c004041180000400000d05070307503007000c51341c40c03004032010b88003003016003540440100c1c00f00c13085030340112103180402010342401c0c00070b071104002c0d000b0140110426030b541c2d0000c0340203504075548010102802d100032181850103028042c0b5900a80e0700404201c03070006201d03034540ea0002c05680d0b0080201c14a0760a08408990f003a100400030000c00070081ba00070300282c400d10450410502140010450303140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 955401933 1250 955400683 955400689
    0xc07082b0e07050f0d05030904050c190f141201060513031b0303020d08100b070206041e0807060203040605120417130e0c0c1c120e0307020301050a021c0905100911 72
    0x502000c00390203000170b0b114400001d003000c412910502c1013114002201e485800800042e4041c401141408021300c1d020009a150001c141c143d00d0001552884441000110707036006500441c5500c140c440d041400500407180140c001c1c00910b402e100071070701050341d03e81302d01c2e907818040d1640384014140c0c50010700a1540c18442040d648829081200341c9081520404a007101c0501c0368071030384400802c0e03a000310358810040f2002001040300e42c80786444950400f42208800e03125142c4503200d10307140040c040740013100b51012a9140d842c1c50341458603003802d50240706070080048810b003031201c1d1840030159009014240b4000502802c9420234104019250300304030140000321080300c20b00c107801505000003010045042132030680d80d4203810000091329007021034441c2d451701504240d00c50000303580000107800d8042c000c900030f000b1501c6003800c1508034401c078030003c10300402e0f60040384031107003082d04004440c602ca8811030b0040503049030518102c0d80a00ea00b101c01c0b040500042407245 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 955403183 1250 955401933 955401949
    0x20d11010e060a05091c0b0f091501080d0e01091206110d020304031d150307050a02070b0a020c010336080405041a0909060708071b060f02120c07082b0e0705 69
    0x1540100c0c90040d8106c40d910381d0310500320010010740030285c0314400103400080901211508102c5040c9030b511030b585a02d80700f03440e910100c602c08001920030301151800d621484005049031044e00b10b1000c501a81d4407048050709140f48803003900101045804920001480103520890080e500d030440c60300c9541c1078007648028058000c1c405e003000e031410200840381e60116608402c0c541032084d6075142140701603052412039442000f0050001c2591500190041041c03c15244242da00b003103032041c480300098200d82161900c0c06c0b05081c844822059522808a140459000c0d07480d50b407d080d56030000070141c80301c00030b011580f115074003641001070401d0303c3d8040c1c204020102400c9a8901030070300501070000100128100310710014a014292600d6070001c1d80582c20800078401818111500006175022003c0d01400124000000307180000150547d81004d90100049182034580251088090340d81100b819a44505070305030b49045080d403040340050402e2b00c6c050101d243c80e140801c0a01c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 955404433 1250 955403183 955403209
    0x30c021801180531021f030608070f0b0a021908090f030307020334090903091205070b0a031e1401090e03030a090c120602030609060607020d11010e060a0509 69
    0x100b400c05060101580d40a80e40001196200003141808844148071034112611800040d4200903120a07401180c0c106c116445144005034406001071561407001c0c0b0703541e181798403030f6241c900c2c00080d0511235010140020b04000019104a881d60605284030000d00d0207206411100c0c0d080009130a2002d013400c03696403d821504130f025604110b00b0b500442e0f2a0b05168406038006c4120b0900490310181090704052103441c0c40d0b0120030110384824030000140014036080c0c01092103102c0c00200e40f040070480340c69850740072018120251900e0407542058101d8020102030503180c0c411102007841c03558040d034500380603900118545041c0000c01410340411713044640c00030f0924401d44800000002140d81001c00345c4400074035420113040500c4145040e402a000d01a503614084041c0080c1c1d4005d03502900d4201d41d0f66a03030b51520310401205108489000350051545023026001c2180241c078610032001c10b0400a00680b160000100700741d02c068402d9000c00e0000c11807106900f85003840303a2030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 955405683 1250 955404433 955404479
    0x3020403140604050111090918030c120c060105030601032102032809050103063203030a090e0105010f0804030e0310060f030507050a081509030c1b100914040207030c021801 76
    0x2070047c202c1f005c20050b202c010301001e40422203203c591668141041210890510343d000d55841d850700c0640003072554400d124800c1148909000455a880c0101b202d0341201d520098010401120b042660151903c40d41c80e041940014025446d404c4604843d81c0c0c20040c40001030390004050f0030018042059540050341018548001030089420b071481d0154110a040006042c038560b840d25100350041412515405010100d20414801d400c61044c8098440303560428880d40c0c1c03204011a01c5c1c8038200c5907400092603020229021a00a40d40320052140240c169500060385240e5001a65180c0d44805848588102c04100707202060102030041c09003200e425180c145042000c507035610488012865014000c40450b403280d1040044581e800d401c0c90a680c0340d01400380c2207203484070891080034080d05401c3c90050034640721b44c4091040c0c0e004c2d46c882c106030900342401d000003900685012010b00ca41c00301c08002583e02d4101428a000001400d1011907041100507880e082d0f4800c40491 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 955406933 1250 955405683 955405687
    0x2030607090b030601030b03010b1008010f1a0f032208181203250b0f0601030e01050f0f090312041b0609061403070504031514070c2103020403140604050111 69
    0x80100081403c0f640c104800f440c011840071070050009004003a8040344a0780b10b82410203c950303064100c1d2446040320000150207104c0d41d650000f074001d09004104000040300f003081420700418010340a180c108841c10007042d080c8009410b23a60580800f80d4096881c0a00402c95615a0028a030100f60300401038410160000d805203d440e502d00403052210388030380b250310f0409a01c050301030034014001c3d00200c4000c100c2c100a84e40c1a0350031001d40f00d040c0082e0a222510100e508140120b43c0140e0f000c3e58002c00366038446030b0102240781d02402e44011408200300710401d6203245042640a50700802c01c4409159140c0d4a001c02c1d441558800310078458000380030421960843c50701d10b4030080d0010341036900d0740c2d00002101c031403155800040c60204c2102140300c003610540c0c05071140110a00c6807010030744402d0001e41c1c210807003450040c0b00001043c603400741e895181c9107085103107034203040c0942446e4803030340c130544158840e44080704903903c0f00c1d04020512000340961041280c00060082c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 955408183 1250 955406933 955406939
    0x60406080f061812030103140c1005031609080a110a270e0705130b010e060f0405060904021605061009060303171003050d0918060e130f050d0c0203060709 68
    0x2a00c4007801020400c214546120f025201e143c2400007058103100b484405170f0307135a104e141c4103003c030030f070030701e203041140b1500507900ba20b428000310380d0501e0a03042c2c8a05081d0340d070305114600303c0c00005488000b007042d44c180001e4100c0f41000003480d110720400040c000780388010203002c000d98003644010a507142400b510f401d08014201440f007140c1c2409000f040d01c050320300519280001c5030b40b14542150803645e40c5e075220801030381b044030420b10980e54000d030b01d00351744200b281c82d0041b8590f552800300c0c100010000d5140182c01040180f4001d4005820401c42c01d04020904c4e00c1c02da402c2c2e42e150400810002c81041c10100640030b8036058004101c8581517850003820060400c01d4401d26100340c90100703041f401c1ca10003a40045038488119507000b441b54200074140d03095885580a8488100b42150300c041640c000c003400e96040328a00441d5581e1540c1c401c801035100d42c0c0c1500c8101c0d42101d43c8011946c1403128070016400e0b07880e4580000814410305241a10041400f0104a0700d14014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 955409433 1250 955408183 955408213
    0xd0206040f1d012d0302150c010f060f0504150909080a02060a110915120c09010f030608060a0209011e1d010309030e10050c01050a0504020a050916080411120606040608 74
    0x1c2d504e640c2c4890b84107040500d820700300f0200e118540c00c082e501420b8100315402c1e00c52160000d2080541080080c080032948046030340a8078010b000705400720289400900680c201940143d59011141102071070882d9110540d00031141c0c04982510007410004003803201076010000950003803200c0d1800c012120300c85045451500902c04003034410310b40c009030f4000402c50402942c3c12244c10480341c4803107060508110750940d0001c0007050114600301d00d82104203000e40310b403004070b54088010b0151031755040c454000940c848201c070781c140b2140d0b24994100380d02001c0c1c0c4003440d0403103848030000c004400c07285011509640303502504150900444000103a8041c003441c2d5080e1090ba1408010710b41e40c00191194010080b40c900030b58a01010008001003135082640518003e4070445c001507114001e014866000700e40280350902020409045a4490700385d00d0340c001d0003200d0341e890b4010310030005011460105401340d51a8000002e001d0340340f0302482075074010700c0040c004156130b11b141901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 955410683 1250 955409433 955409459
    0x10e0c03130804080d080a270b1f080607090f1d040321090c0602030301080718020f0a02031c06050a0e10030203070e01030302100b1309020d0206040f1d01 68
    0x7040100703a200e001e00008000b07607241030710041c000890a80d00518070504008042e036001b2900d00b041241070007225141c1081a2080300219500c0410f811491103180d00c9107070030200060400200401003a6043e050b641d6211010400303000000f01500490411020040070303400c2e65007084600c0201000100311a041000c8a54035400d003203200307040c0607512030a080c2e03025902d58035500030b80505000b040d4003060003940190b030114400d500ca205010340350280dc0703035640024003801504c0d1388410014001c0301101c0d4238007546844040c402600c0e100882c120244a074000030341c20703c0968004035141f17a4826004042e60419183c01c030f800c20120303142a00103195000c051007900e080d489204045100c0c00f001082410203035030044c0803284100c1d6a0740420804500074441540140504a50404d0100984c060060b541c00c0041918038801c2c000c62010008143c8890100d9001c19100140700058803000c02401c014440050134001d600c0c90484441c421140c240c40c4007104c0c0111400602c000701d04080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 955411933 1250 955410683 955410691
    0x2042726040e0a0b2e121a040501080303090601030314071502250b0c090402160f02090a152601060b041a070503030c0705070306111c0b090f0705130306090308010e0c03 74
    0x400540318a41c042c41c2034582d1b44004d030766001018280303030340d46003001c00a442002c034510302a00c0c1003000d6039075202034584a0000b515030314041d0f041403004001103442442d45004a0322a84800d918224851f81e40d00141c0c5200c51410401580214880160580440c112400340e00b1400354404420000d0340c602c1030300480180b40760101d90300420801002e807161340c140d5018861140c498486003d440c2450135015843d4003089105156075400659550703240d0250420090840a041c0800e50034420415007440100200b1024449a00583c00c03a2010900984000b80200c100ca91f40e92400c0c80d10400440344151054940d1301020003810000a5000080340e900c00021200d19444108519005040121a90001c2e22550030034043d080d900303910100914410b00705105140440340c03442c0c4200e0580b480848a194080e4941000a41134440201140d40c481120302c2c241e41360105640d440d12201c940d0760410b0f03074500e60362030143d070130150042010790152007682c00c140b83c1807070401980c0c0c0083c84018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 955413183 1250 955411933 955411999
    0xa0f140316050a0c1401141b0915070b0723071505060f030d03020904061205060414030405190503010e0309090a020a1b0b0402042726040e0a0b 63
    0x1c810643c58030031900000e0060388600c010314003801d0510818081c0c4240b520840e07208111102045064411054554680b03407a00003050809803128108040250142c134140d0f24600100220703000203505001d198810210750b200c495032019921409076070080107400b15600030000b0060715000c1641c002e004500804031190120303142d40c410010035000d214030154250184150301541c0c02058164020b044611001da6080000c0d981c0c4100e00f01d80c2094240c1c1c003600940081e404a4080b032201204c458407005c44408032031905607550081039400025050354088829910750901091a083c060b4040801c0002c00071030621041c01c0010381c500c0b101604480b145a40001c441e1101401400030001d0360036450b001400e101c040381054240f22b203084a080388290325180030203035030a45452100c0e0b07040c00d81382c0411440c010703ea0b9a07521100390f19104501d401030b10612110b4000c0c41600203002034002c46d0181c0342941048003000060350040c5052b80d124940b11294100350070024001401001514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 955414433 1250 955413183 955413187
    0x1911090f0303040f08030a0f0c15090318090605040f020c0601180e01020d050105040c08040c050105250303090210020c0607020603190920031f150b0a0f14031605 71
    0x1800010b0b1451003941d0180c1032040000c60002040000030020f04002e0500341c895400c8030244000c2215400c0f0780104c010441c81000214803014401e96000ca208a4401e040240e0082c813030141c150b0750301016134803d20055440351824040c0341018083c404000240d0705040d420722080d103403941c0d203940d01400381c0b00210043c1c10b0303425145045500100c00b424071040085513564583d40114020346070900030b050059041034921071078a4445d0380303a0703482144c01c07102d02c208070780c2080011030f0036500c254010030411540018120200c4440b0700810f0081d8869280000d00d04100d1040c0206041c4864000065402064a041300c41e01d4040880f170754294100d859035034940e29102a14203a111800d034140000c1e00d0b001283d006c00500b1010480552038285100407a2a549810555141c1c03078400c5404001d0005081080400d5240e0007000070850039001926043d51940030b60741880d003140f101e0800140181d10341c12400350f00610944004480652a14950326003040e45204100410300c000c0100080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 955415683 1250 955414433 955414459
    0x3020105160f0c03020f1f0f0513080a11060315060702130c08010806100f0311040e03070303090c0e0c03180f10050103060c050a0903030c050307020603010b03191109 73
    0x80e1407980380d1075407008002c4140d50b503c0c280300c030001840d8003040f4020400100000000d140040803070245c0d42401d80340c045500031602c0211900d0218030b6100081c481c050003d201441068096103001d07004000c014401c210240c1072042c40740850710200c40c011030b000c0052210780d040e0911040ca0005080e9052135444400e40701141102c050340b13181985051400701100981e0741e212307440c54104e03206503084070391589519a080c041417900748900c4084040340c034020800540c240704141c000f08801880040c0c205280256142980e00040046001a903038a08603000c000d02e81180801400041c1f00a1080b0310b442c2014501c10301c0090040041c40d55030500900c1301c1941088107110f0010309030151f59629280301c20710809414203002c101e03102810a0780ca41000d900c1001950680a001d95034040340c249140c40035901e0f44440c200580e054001001284050784414006600070001c420300c0c261781e072800d9030580821840c0341d54201a441e040041c90011045c406003601c2c0502001c82d400380304045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 955416933 1250 955415683 955415707
    0x3201315120204080c10050c150a0e0708070911190309060605060d020a0909050408071b0509040c0608242110060302120c09150d020d0c080d0806090103020105 70
    0x14641e00c250003042d000103008a8a124046441d00c001031007529800714003c041401030340c0c9401410300809071a4418006d0103481d1508a4a20b0741101c003038840007a4503422039040c0b81c14080b00d038002e0b41142d40404010041911a441000300341d5079640006801d0058070380620745111660340d8404201600c0b00307040d0302032065a60210707001348801407480d0350300d0a100c40280040c1d0401d10700c00c404190780c00c2d00058004024081e03e88a9548108858508811030741c0750f0000034a91b030031003a140c0c41c6503103000c5010340303030b085640d80101d015100f1001e4641c9024802090318000521200c10103425036461a5403120400c2c4080c40a54107c86100040d400044041e051813800304d030468040c814580307844601c0110350302000580307000fa141d28140c030b41d40010003941e0b940e41c52450b41e04000d0701400a0341003021306818940680005010103008007075500024011050900d007541c0181c441001041480f404000e203604e14001820104030030b11303281c000944a200c0511010b414803c0004562600074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 955418183 1250 955416933 955416947
    0x2205060f041e03030b191a0f16050715030b0d15020c16150c11010309030c05030a03050906010f0803300f0406060501050f030a0c1b0303201315 63
    0x110b8001a02c031030340a0030002e0217407803c2241c2c2e501070f07100c2c242a06402080c40f035030360080e580c103c50b203404414035803103000300c0350b90102c0001803002c81c092001c1000c1c1803a40403040003140c0200000c0c614107040215426401d02c2c83c0101d10249880c0008850007900d44c044c05102c1c40360013607482000c0c0c0a00204601c060311401000100c540618645809440b040329442403e580714100c9082c5c1c0e1090040050390078176500407029010186c4030004050701e601c25000781000b54841d00d0011403101c81541e5203032664110400400120341c88404020140e10104106030040c81043c0e0030044140c42d00030002d48900c141c002020050000c0140281801c009030125002c411130355183d4803040c0380512200120f002c00f43c5040f12007070b0402c040050b00b58860000da40707074014a2b075190352031902c41050000003070076014440d0060000d10702102424640c408007020806009031800300d40300080d400a45041c0801200078030b2070500510040d180e141d4240c0b2403009480c40c1510841800c40680002da03200c0c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 955419433 1250 955418183 955418213
    0x8061620031b1c020d051e0702040603030e01080901150b0310080604140f03070b0105310b04050c07032a0c0f0e06150d02071103152205060f04 63
    0x300214058032070711400b000070b4500c03903111540301e02c03400b8114000003207880f400c0c840c0c1400001001030010210300c400100817050304000b8010320a280c0803003540480d040d600d541d0300680c086086c0c2d079025100c80d40c001c9a403540c066400d50080246501c55450b8150400303442c0200410184040700003903020018031682d5001d44a00411142c241c6050714050355a0710080da002038150040300c007140e070445c00000a98809030360082207602180e00b010140170554040b5040420618080c0303d0750b94400d6040c00a04000345d400050115012030040144810b945018181c106000b00030400c52001c254840940c880c4401c0c11003075410008465600d482c16607550308000b6215030781c0344200180380000d0b10407040c122030300c0d035000049036030315013040180f010600c0c01185041c803000c2140703030050710455004101e01c901c1518528820004400400c0c42c14000c2c5480400035119001400080c00d0007032200c605084840c01c0780000b07000c007036803000c1d12800054045040700c00c6a601280420019603510081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 955420683 1250 955419433 955419457
    0x105040f0b271012020936090307060504050f0303010803030103111002120f0f120a05061516150507020d0807020304030804120f02030601080102040806162003 70
    0x816140d1030107486903400880c200c440d8803007103490b40b408801058801091540000c004983c0070328014010340d40c50590320800140a075080007001800d41d200700ca40c40c02c603484441c0043c110b12904852855401904842c1d000d5455005c04002e45041c1c00021034075066030103140030819480700d02c1e002e0b103081c81000c0e01509a01000c80041418074000000d0341c1240c1c05841501c1000141d44c046c0400a403030356103200c1c0142c20161050069880e10b50040c500404881405403601c8410313000c03070605802100c2403c400c091310701705000d000c0705d0501425402c650210781c201440c502e4000d61045510901881380380c0245030305590018820741451b581000b0300c080b50305000616003000c1c0251910700c40d00110000c01c0c100f10200308028400025281649c0e8401c514a180604018064401404603034080341e1008072500083e0042e242030010b07030700034103080c0c0000d038031141403511180c2400d200800d030151007a020300141c0d00440d480b0300248405402012203648440d4411841c0d81544514006a81 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 955421933 1250 955420683 955420709
    0x8090607051c0507021c032709090c0816060914010210050f090d0f0212030606090406030b100e0c070201050c0f011b09090207111002150c0702120a0818010504 70
    0x92a15004402818040c0c401c58101d02240300d40311b1420030107402140c1c0540029108400f100c050614000a0030b003950320b001d0b06400310395541e11010b041d21a00030044a424034200c1082100350750400c0240035804150440d003412604201004000030241d203d182040b0366040200c04859000748119013081c40091014070075032400410034400f045007070b100811740d0711403501c400002500c80d5039065040e40d050f074041d054205034590308000641001d0700155005200300701c070101c950366900c2024015072049a600c44540b5246000b506083c4071907002c8031600d040c690804c1035243c2d40204442e07000340d09081c12030300c1b4160000c5852414009024000183d8600300495120342c0d582d0313100b4800d0b80341981c0c40c175810a4543c0e030a981070307004800004007c2400003020500a29041c0d17200180380d9224411103110080502c1740302001003003501ca00a00c400006080815810012940040040094010705540040f540c5000051194030000a00300c42170304d2107409144e04c42c90842e0003d1a1460f00d0007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 955423183 1250 955421933 955421983
    0xd0c05090c070b1e150a1212090801020a090501030903170c0331062d0c201b010c0c0e01062c151b01091407030809060705 54
    0x140e0903480b0318801c1c0c1e8003040d06000120039070340860040c0c902d020b0765403910302103890f001a9007950107984c1c000268001304150010403084199000c0c101081e0040340c444048140703030900036151107600c1c1c12080e4140d004003d005d01503a04800c1c1e0604860003841c0000d15840d20b4141201c1802a480705890005819018820407002200c055030050350540e1042501a04140e4480071451000ba010750307201041100c0b0b0004119664010b1108000c04000e0300c00000c04400c00d00d058100280c3c900c180e0594904551448650103017042050646c810001c00044400c188000d42e14900f00b500d8040800b0202c118840c141d1192040445840d8850b440403101c5448041104000c2000d003d01e00c002111005210000642e10381d512240030447e6048915078000c031418081044084400c100c81e0080c200240c109181c00c0355038501c4650304c8040009100071503844c1c8640f10b9070082c10140d61541c4008810703c041034990f03044a0141000310790f00c540d640315914020382442d21410440240b8a5140404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 955424433 1250 955423183 955423201
    0x4060b0303032403010207030c080703050f03040f050c09060102031c0b04020f180f180a3e180d0c0e16080108030406080f090724020f0102040509060d0c0509 69
    0x302c0810540c010343d40c41d081d142c0300c092500300d009211000d0002a100c16801002c108070000400750316001c6c0c0740141c41c0138004800245298000d8908540d03050039075181200b44079084c0001000d00504030f403642800d042810000755640103460342500091903090302d0751800e810075070026010440251056444d1701d4503042c1d030021500071a1400056481009169200c4d141c00d440b0004034010042c141d044020303001084c10388408005105610103275580304c61441e9150910800c821075020503021020001044410344000140303130314403005500040c07001c00d444441450035000000c03c1030301d038131030300d681ca41c02c1c0009011030341c0c0e00c42d58008802c030060111510401c04445034110080c1c5910466981e11031045550703201d80d1013034200054404d00819031151408282d1500607005038211401d550325901521142c1e40700c40c003000e5040c0e000d80080c40702250113005642035039003080c00840c14146807038003040e070701c01c1c0c0101603903c2504002d40050411007810311400c003604000e03000c14280d1034500346c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 955425683 1250 955424433 955424461
    0x3081213050d020106090b1009590c0414031c0320090306070305181b01021e0a0f1403030c04050f040b0307030602030c041706071b0b0f04060b030303 66
    0xa90707a222403c04c805e141483c20010104104100d2541c0d4a84c0d0107842d00424540380140410f0b0603080c0c40c0307404010108540110100d21001c2b045480130040b6640d00d1a1081080d43d00c1220044040000c4003004992600b803002d40302150704001461141c07000b0b040001c0c0c00e040f81c1902002c19441c40071000d4a034a6495070144601c100035000c9001c00c00308280345401c0c01d00400018035816400308001a060328800e40101e5088400c1c481580b894000d2035074018100594076200990514041c9402d070031569041101024000d100c504404030004640000e0761100c48881000d4602c80c01c07885100c04208a158114040d41e040b81c0c140c80d101c2c10510001c031a2a80944141c901c540000d46041c4c0c1d00707241502c11601c203880000c004250700391951396900f000e50001800a4100c0c4001c0c0400207d03140c0060700019a140310401a100d40e2610b40c1c0c9c041c000c1e490040036500124180001100001c3c080e0242ca5040421038102c0300d070300e075030b28039108020707000c0b8108040e05408003005201d0500310040c1c03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 955426933 1250 955425683 955425689
    0x403060e0c09061c150905030c01091101051606180b01120b07050c031902071a070c0e0412030902040f0606020616081003081e03040f0c0f03081213050d020106 70
    0x72515400d40f241c40403c1891410455000c0d01d40c6880714440700010744058402d07180c00c180d140007103031008060300c449045030440d070124486070351034203601e104001d82501c840070348030004d0812134103000308888481002104140014015591480100e08110a521108070255800b41d466120ba686888a8206c4000400d20444251a4582c04203d4090040003619110186403005504040036210811001d100b4100000d0940c0100310022400304d002007464070203031a1038ac16959560100785804880c20300d240d070150203130409840500c07001500340b04500340031449518001c1140d10190001500400071420310140a500d04200010f0380744e000300741c1d10b10400f0342454202103560203000c01d403900e81040b6411401004064000e00001d103680b405041c00d041072160001c6c0440a506c61718105510540301a40c00028030050003003089088039108014106a4102c60803203445c540d500081801052aa091051424400190058905111008020340140480303001c00c0c0c7c613080290080c00240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 955428183 1250 955426933 955426939
    0x3020607081e07082205040c0302090a05030102090a051306090203180115080d0c2919090206030c0705010905010f0f0f0618151802210601080f0603030403060e0c 71
    0x3120080d10900e202c01583c24864000440918001c00104018400003042030101c1890907601c901003269110f6100721000401c60341c40041e81d528032202005942109544940d1080c0e004008a102948278065000c049070015104000e1608804001e00098000d9400c000f100a1000c002c20020803070b2030b120003010282c0c840081096000c0c0a040c640300c0c04081c00b606446a100c43c15001c14036204030078400780113015007050580c8160484074280824a003e04150611861506203c03603034080810360510803540d96070030465135400d640407846a0200a105500081c3c0124a5074140103007900100d0145038840001c10124188214080080c200030030480720a51034541542c150000521801c015942c2c1035025905240548030400098050581c0028529103441400600390200403030301400c41e01040c001507162050848022420010038140e17012090f05c00040c4020f598004000a41002941026100540d80c08011900e18441c503400240014500980089071000124840391680012 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 955429433 1250 955428183 955428217
    0x30301062a030f02030f0403060911030d080f1909050a200105181f05040302030d092403110a030506030f061b0a090e040305190f0203071b0302060708 66
    0x9038084108401000507119501800050500046401039202520142c910310440c1c1c50201170104070030150b0800d034011103909446540220420054011068400a00b90f0007000c91240c034450040070131030003070903400c44c0701d003a02c010880050882c284041d007015210000c0c05804010315042d031740c6d8018690f00b5685001520100320303103a0103807004800e601105943d09402c021140304030030208a40c001c0129404940401510b2008906c0c8422500b070030156114162154503600515080030b41480c0130030100550322106002c41c04106203215803141c0c0005030503160900f070110580091188100b443e517880d0300400d00d005541c2d131641106100f0310b010741c15203000c2e404122500c0d80e00c00040e160f504200c178481c4001004c1e000c001025100321403513132a18a0138030b503442d200750044003400d44080c3e0024000041c0b0000c586820b0724801d949590624003401420400d0800a40b02d024250000300031003011a205081c4208103104403000d150010a219036440040c9000031450b40202c1c14a00242e0f41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 955430683 1250 955429433 955429457
    0x8031308070501050409050a0209030d021b01020c1c14061501020f0d020d1812060b010f0c0c050105070c050307091401080304031709011e021b0307030c0b030603030d09030203030106 80
    0x41048000c0b94010307103406041a080c543c0b40f1003d0f000040120300c00c2d55003486204619607040110400e001e90325000341003095820b6600103a2411030040d01e50640d0300c18030207180241c541c0703030440c3d0000003c2c0d242580508018078126108030902107215280380b080e84140508142403010364004071600360219038503400c0c000a540e4441c42013500003405600400042108980261119015851032980d8496542d455503130544003904580390960720f10766203070f10206031540c01800030145010726061280d040c1d40d00d41e55000301e08841d0f0180b241088004640b0030100541d64a00e00082c0100809450000e5113586200000f403945041380d03080704040700000103d03035001204490a0301e800c9002d40c004000380000c080196030140030221304114400006051800c503440b12100c1c3d0078440c1d8044d012803130750750000030507000c9540c0c0e100d403003078010000800004418501c05400c03647c0b492030542e141d558410010303003540161074000e110b9500b4020030004040c0d000c002035040e03c203140c54000c0c00c1d000c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 955431933 1250 955430683 955430699
    0xc0105250b090c011e2708032a0a030f030608150603071d0a0911091906080c06030a0f0b0d0b0108070e0412030504080904090c0e1503071a070c080313 66
    0x550006283c080800302c218101841c40b440d440c1d400e0981a40a01561071b0204601a16034001e55100e0b078020340000c00c40315030420b00b42251140308000310400e08501410890801e44400700c1d90360003424040ba40c41440c0f0081e001e41c00000040c610349040d00c5c842c0c40c10780340001c1115400c5840901c0b0740039200d00450300a8440410720700c2c13403084222090940e55600c800078010640308000385c4000203081d544901c84da42e607034101481070302c615940080f10f04031103800e042514580d03000320510b80c02c01c09520803651955000d49504c10400000401c260001d02d000c2c2006000b82151150071801c5c21221703109103c6405822030480e00b820040f20881c5036152500d02400c10196001070101d42410741c0940c22903c43c0c0c004070340150213045a5454010510000f404640d4070040071518420144010090107850162140d440004061000002c020030701c00203407103c201d4002c038105035000081d0540d41d01000c105940c0c0c0380340d010040e4402c49456049803542d0f900074450114800c000300c840824149 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 955433183 1250 955431933 955431947
    0x30e330714070317090d020c2704020619170708010b04030609030e0415091406010e091530070308191103120f10080c0105250b090c01 59
    0x80c25503210040703188880411107440d482490140d082100980c00c0c44601204c0070805400b5161030700080c80d4110b044400a0308003190415664400c0d04003803800ca81590b411444000c9800b5801407015043d6181d00c0010040d010b0f000c062581c1101c00c95002518a030070100c1c120644900041e40c0f1850358407094100e404940900a081c50600d017840100005143e680050000c07a108e41010600500203d02041c1181c100494100c00307080c865500b04809200e0b072198044003826244190001d06d400000607025242d0103068501590400b000140c01440148003500758502c02400b403012002004183c5880d0300310b0245030000e41e48000c00d120501304000680c5011280c0c030283e100e0900074010050841030302150468001c2c0420129140d1418000b4001896005000b00303c906032070514015042c0040c00c01050303410481d41240040c80002400100301c2c800c510309180596540b0307240d503a004601c0c181c030700c103001c2d400c10300015070380400007407809083c0300d07070040b03030032030700c1710072240c00112198 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 955434433 1250 955433183 955433191
    0x302120303130201030209040219050d0c020615010c0213090303060f0501050c0a02010516020a1205010b01210209011419030c0c020604090e0a0c030308101401051801030e33 76
    0x2c0620112a000154044d40180c904420010001810a10050100d801c030000c3d244402000400c0050410700c98a12441a481e9440d5030748000c1056207003282040744582103403001c260610000340100011580e410328500e4181802c40801d205800c0e41e8900a00a0b20140c010981403e03502140401e895101e041034070300d4503405000828075003c8540042d00c640e80150b0b82402c84400041204002d61078120754240100317107070040c1c2d0200103003500300142182c0030402081d0400c41d40c86420f503113030201d2440480200b1240180103070b44440100058400d410100c204141483c80030070b070b85908480802844011042684041c00b031000d40e41021900050000d6000f5800381c4140021301c0303216545d0b030000c0e01c440a00022030301c075845d079910f8424100c0191381c0300b10009440701e01048114101039110b0401020003108000b844482d000002c1c026005410380854205103038910110507a00c13a030041e05540400505440c904000c003103c82111150101d01681290340e104030724416281091002c1d842 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 955435683 1250 955434433 955434451
    0x260312041217070804020f06120a06060f02061f090c0e010306080d050f0d06030b041b0b090603010e1314241608090109060501060903120c0b19060e040c0302120303 72
    0xa1551000070941301300c08064000d9800c000091000705681d120040240482030561003841e82500d440721001050740e407241c01c54003c00c400364400702103d0b9000502c0c41d420590090311103c4807180021350b410b61a41551100c40d420703007002c5d002c1901d103410134950f010740d5800381d80501005484a048503681c4c9004050000001d03010031400c0c82c03c0c059580a80201ea14200e000718200ba030369203950260000641d03043e200c0148048130481c01e01088040d03440240501042542846214400615280014402d00c02045140030020f10a40c40d41d1000c4031402c2d0313101c0416010351441da014607541701c868080c520000c0c00003845000c02006482d000754861412450890305c80515036008a0b170140018268506035034039802c00c100003407100d0081034083c0c801070355000f80407031075403c1150f45465110046018011030685400222f840d8080283c1d1001007503044044001441000b640140700d01c0e40429540c5501000380000c01ca03054440c0f008881c001c48482c0d0180c50103110b01c68032440305031400c0f10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 955436933 1250 955435683 955435727
    0xc011d07061202040801020301030c080f0f06360304090f051003021c060f0b0103060e040f120e130b010e1f031509150302010305070203132603120412 66
    0x240500c03442d400e258148200c400503040c0340d80c404210b030982e003007a0021201420380d04001d00100c0c80c100f0080c0c00d444c10078401414050000021f194a421340070304600f1681010843c010040300d084500d070501004100c3d0008003601c804000c46480350072034026102400d0400b8900c54a01c103203402064050100008449905450341e03082055518018040c07200200c444102c0c2d03804075006220361070240c2c1640c3c0001c2003a94a100005080310701c030f600031407501400542408003040c05901005a519488008000b025100c40c07005d841c4003080b091001e80c00940f02d40034010004103504003610701d0100380c841585000c445800c200031180c030001c440c003040040d0048000003510941016000c560800344801d500307915054003e0690f039011241080c140032050341007045580c948a482d91210103031000e54144400c0d0240b603040c4c00801c1c0329910180b858200d000c200d00b00320000c280e01c503891a00c00c45c0d6170756618901a440240d000c585c00d07038150f114031074030001d9107010390801444c2c01c0003104424 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 955438183 1250 955436933 955436939
    0x111090603041b0f140114090d15020f0409140103050a121e020105190608190203011407020f070812030c030709050a27140708070e04050c0c011d07 65
    0x1010580008105072459031208203480484488000703564003402c66203030184c0f01103040244881c5400d00b003825681c1040120004181c29280300002c0d5008040100c4185c0d003042a2800c046403814103a040c4a9101744c40000e03002c204e15038900090084800148050014034101102040300c14000d110180c0150409050180001d40549000210b908036080051440707003440502401c6400c0c0720140000351b9074520901c202244003207003008401c0f01010b805d104c0541441c6400f40c50315074021407418583c1001c07064508558003034010742014210114920044d10382100c001b5070354101c0d00c0344400d290081c048081600c460100d00b400c03034040100d0703025145031185401c08503036a01c01000c003c1081880c0c00042120381d9502c025100500709082e610003c2004180c902e8500d14500d01c201114502e080b0b20350100c800407500c000e601405a05100010b035481c110180d5000300000c00590b40145000d04120f010b0503984041d0040c41c1641c00200440e0941000e6520354103c02c8141014940c041c1c00e00f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 955439433 1250 955438183 955438189
    0x4181a06091009030b0f250e010c021507081c0e0a14031b010204082401031115030108061801020703140d020f040e0105030c030604121209230d02011109 67
    0x70b41950812460100800c1399a500da80c00e40400c140c035084503050000003400107520085018010084149001c485600d00114018003040183c6c18202c0c14080702c20740701801c0d5aa14400801d0031005041c2040c1e40c1c08a51030028515413040040940030400062045603486c80da11034003030360000110080186030010b4607480c544522480f2203507c4d0384030400c0313002041c00c00043e203841c48066160000d83c6450804c0355072410461a9070750102015031002c07006c00442418500103044139008515800180c0d40b110100c0d0003803411392110702032540000b000003443c15000a400c1d126207d00310303032801050842d01289082c0d200300140540000c010ba40c1502c01440350310010550407a09003030051505030005040502e079005944086d1004441301c0040110741800c1c840f128441e10118050001c034a070669034407141c13460329003005040100004d60210903d085522109031176401c2000e100c400c061101c8800808100a41214103d0003640781c7e120030a40140951035a0f181d140322624282103204040c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 955440683 1250 955439433 955439449
    0x403080f040302030d09060e0d051b0406080307030903020301060e0402030d0e12010f20191805060d0921021b0a15080108011109060a0309110604181a0609 68
    0x4031404408200400801607504003e110321140c0951100c12500d8904480500780030503401c003d602a40c00d48d000800006d0000c03441640e45174440804214486800d404580140025040200a031200049200078942c0021030306040324401c40080c0306035038035414140c04003217043d980290160300803011003034941c0c05641040e112240107802c044c10507140c14040341c02e54030301340761800065030342d44201d400683c0020f8020149140b04c0000783c2c90a105030071030000e51102818100c0c1004500f020b8814116a12404100100344c01001180c550300080c45c00002010300200440308581070022044e82d807080d1018500014410350080c0040300000202c608541d662080310300d40c03054032502c02207241c244805100801c01d14980d1000055814080c0075802c40d46042c00d0f12a086909000e82d200b070b0b035252130031103100e00b00d0392a0108401c0e040e46015111400c00b010384645c440320118010400b00003540c040d484186201301d0510001c900903400d101200c00040c0c665030012008c128800301c81c107200c18 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 955441933 1250 955440683 955440697
    0x9060309011512142d0313180b040915021318061707050901260f03090414090703081309020d02072109031203060b03040c051212040308 60
    0x4000315030040e00400191401c61650071a09004040020943c1403242000301218114003c1005100480c040d40e03011244a4031030780e441c1d40e050100724030b044520f071060080e00c030350b4051003405e14982c44e120401c000c4840885003a00d070752607240c4091814145024010006c0705d5422550008036400c2c1c008000340030b0340c40640e84102e8241d101c01e0008502064410030301002e5018400044e0aa00341117a031181410101e81c0180680e000b018140720503510310005a0444041c60940c4c690058613600494071080402e00702c01a6000782560f0042c0640c0c00301c000c11111004450411164170203c00054100700c1c04d5490000d00d6005640500c0010010b00040000038021204100865955000c0e50140d074040c41c840c0d0032080d0041421010020034072010040100070340a00c143c0340e1410704000344800305610020f000007149a4000b981c050199002d800a000c3d01e1a406079a45454185410240780a100e440e000340010f00c40f002080c00c0229910003031500020503140351600c2d40d10f49401c5a04004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 955443183 1250 955441933 955441951
    0x41217040b0a0513020a0e0907050a15030519050403020c030c0324040228050f04050601050a0f030612050705031204050a0b1c0f0e16210c26010f020a05090603 70
    0x2082c0140c6d4442900b00000c0443c4040c030900c6240450f00142441210340c000740c0160501c0c0c0040c40a440c00140c0d0050103441d502c1c0004144d81c99801c4182038422140540c01000e203003309001c2803582c08240380c1c0b4100000d404a41445030300070b0a040daa0f110000040788400080c290884c00300000480c40307034000f80000c003035602302c0681d41080d4121070f2816044440c6e4448600c42040300b410081c0c2c404e840d8060881d0204518a48040064803e1007403490324810040300b1810150542c2c000d40c40705001d0701c0403086208100120789400c41c2c0e17840ba01e014007842442502460200d8505040c00c032000c0e03c901914410045140c0140f00400d5007000491080c210800c01c03c440c1114140d224900c1070607880400440c0065400208034100b810a44c6000c001030000788050000318012190203400701303d4580407010904190030000e007a1242c42c1c0202080102d03014414400040d4007207501c6030240f04030020008211a0300148080f8401c003108600450410301000b01c0c0c501e4403901840c0d101800c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 955444433 1250 955443183 955443211
    0x20c1201140c0a0f0c050f240601030207030c0605041419060e0601050102121c020a202a04090b0112030801090519050a0e12040807061809050405030c0105041217040b0a05 75
    0x4800828180001903c07018000002500014031503090323a0202c40d0080300a0030110310308440d544008141c450022000380443d0345a6003c9020060200009440324071a0f02c240d8800600182484000600c0354a0503a81c8034103200f050390507100007003440350481d40141c004005180300c000d140c0c000c5030400c500460300301050211300012444140020110a41c0540d200004d850700703035106c441d410043c000c40c98081d0740f200c0000c03400c02400c407031162502c014100044442c09042c0c00018007410043d14000e180740e82050002840c050b003000c002070301c80d1080e00c400f500c1d6a03c0c0e0101d2000c855040720032043c0c4000f402c000b180080c0b0305503c070030b8028008640108001d240380c0421031501150000c190240107002404021034041441028050101c525260780c03603c0d00c15000e1310f0000b071b20f4010325282c00d035103d0104040040c10030842c4c040d0356000c4001e10007403038282080c0106154150034800410b508a0000562403000f440951046a1241140e030007500d840700c511004101c020603400403a001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 955445683 1250 955444433 955444453
    0xa0b06190e070f020a110103150305030c0d08010e070e0933010f050c1c0306031a0f071407061d120712020a02150901020c1201140c0a0f0c05 62
    0x48403006005410440d00caa1980d0601440051218032283c00c1074085400c210040c1001421070140d80c1505207003440e020505205c069580707103500c07100da0f10041084c0300010f00ba0310100c0d40820000810b85894540e24581d1703036035203401124444c0440788200001c1d107a100c04601843c00b0198603400442180c0c1048005800100c440300c503520090010445c0790026044004546c1d0200c01c110310381d0308030b15003503080200c400c07000d683e40c050135200c2040150070003d01519141c0300e03600400013950060720040c0c448030142c030000007204050f076001e100c001605000680d60350103928002c85440144103518a0b000041e02c4513001000130b014a2103c031004c1800c2095041c108000e846403c951410050341d803900c443c03a100c0c4281d100074805405542061a40c3c1d00940e80702600c03954a030064a08031030362684002c00407400c0c2515010750396840203110303200d1444102c0562201058581e200e8810b806900c0721a910f0140380106920b203000202040c1d407000d031031403144c080441118030030070440c0c04c1018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 955446933 1250 955445683 955445719
    0x3032607030209100906022107080a0c150c05030402040f060b0a03020a020c03010515010c0615120b13020f060a030920031e0715020c0a27020301080a0b06 68
    0x6846210001e500850300060a2902c01200c1000441c1d504111080c1c5140c000c01075192000000301c0a405100315042e12003107041e4604450f0311a0380680c0d250f0380ca5040703d8019040f14811013042c0c524000540010505030581d1040c80004181c1e03447d102d056a40355404c00010b8010040b4a550b02a112034001501000400c050100095103880c0540c0380c0c04e42d000d0080c5840c5801021034820780c1040c0600802c41034281c00b51041900c00e2805c0020740c9507a0030700703002600b810f10b00b9a00b2038018142c00181044514003000440f03100708003020454840108003003181d040354001a510082d60540045145060303401031440c9461800c005c124004035403254040901c2c60250b41c1c0c0e004180f408100310500d000d0000d05444002040d142074490400c50b1029550b01c407502950190400992150a1f0580200069401c2e400c004040260b100d0302c1d8500700402030194103100c0c5801400c10440b1011006600a4134140d51102c002030803101c1da1616403410f03408025000c20340068004454a0480d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 955448183 1250 955446933 955447007
    0x312040f0210020d030e07150e0319032f060712090213020702041512030e180a38060906161103210703080912040e010509060a0b040303 60
    0x100c40380c01a0818000504014041d1050080aa501da81001c10148009848c04c4584888201c043c60f01c4d0500c40840310102e46012540d0484044406902101e2010594022102c1c030040f8101707080403e081c0105103e0071480c00c4d40e0304a015907070300f0640c00694114428203c0350062265002c0215503486a500864144a40c50700400b10160300042c0c0d01d4150f0406002d0680300901c00c03050700c2ea455103845851201606880c200404119800010012070395501140c10360f1899103680c040f44500301112404005c02c1545500001100c0103400149481310440d07204080014007000c40c55075003643c07400c0140d146c0c0815900341e0300c8a0306100765094040c0007082a0006e0344208248a01103100c1380406281c01d104400d4540c501200c40349200a030319542040d80c0e40341d9814201071070651129041c00b810400c107001a94002c4601080024a070341c50403500c281240c009031442c0c0710580303803e0f062100000c1e0700e00407a51141801c0100300000b034810100e814500710f500000001c61101c500018a4003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 955449433 1250 955448183 955448209
    0x30f02070b13060f060b0d151d13080307020105041a0105033304030f080a1a090402120303090307061a03060c0a091d010612271e0b10080105090312040f02 68
    0x1b80e0101d10200c45000500c038090070300b00e1220700c88195503d0923810308000b0007040c20354095100c0400205200a03a1a110203104130707031056003592245400d0030003e008120848041d200c000c800900714a84561074052385050f180068050700b550143c3c07941e00004100d5a002080c2040e0280c0001a10300c000380b004a405140702e555000040c03c00310100070041c80e0050b104042140c82c2500c80c07411f000d4051014104100143d800e6169545c03203000284c0c02e28a184580e800d2400000100036030303404003100600803984594030400a14040764915050b0b05840c6038101c1c0c16611250100d082c0c2c441180291000d0042858400b60458903540c88020501070702144100324241c1200521425422055501450201c00401c010340c03901c2c0949070100345200026100300342600b400d40b07001d000d1103a55a09021060078050f000400c9503203000309041404a40100c0c08914400003c10100ca06000b400e0040302c0000c003d40c02e040000250340d8400d503000e8021665060001003004c0140c6441c651030540d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 955450683 1250 955449433 955449449
    0xb21060f09011b032d0203190908070609020d150c03050105031b06090d08040b030117060f071805030105100e0c130312170103060b01030f02070b13060f06 68
    0x450800004803490120060820241079062a4240c03085400c1c402c84988103010038580441c014141c0040810307000500071241500006824400b10205055001140a04140b25070081c0151064201e90201d9490344001402c10070304003d50800318080d504542803c0c0c7c0020b0145448802035640d500701b406040d4500c9040740e031107119001580750188031303a90041000b40e024003030341d2181032040f8406d500540e20782c52140b1404a07200c0c00a44952228590103644002820b640703a4a482d494002034200b40b1410014180c4a65200c071f0003080450150700a107580c0c00803480940301c218081c2d40b802c126044446a20814100028050741c003405060b0040700c0100320079040b0781c14414241d030080d00080c11000c00e51070400c032100840516018002c01c40e600304220415842540200303c0b0b281082c580d000752610b2503040013100b0b00019034800007000e00d098a0070415407003a10008001e034010488042c05a90b655400155802503103202c01e401c942c8207040000d2070303203540d400b80e00071281d80f9040208 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 955451933 1250 955450683 955450693
    0x209042003030a0e100e03031207050904111306091212030b130b010206151318060c1106060d02061b010b030d0e12070f18021303060f1802010f030b21 66
    0x80609280282d1424480181b600407045060a00865502d1280e031641140c0b6003241400103034280c3c480c1c420781c0e20307a000082040c49400d0350200004002d401040e40e14680000c0c5480005000380100240403c80d02c661110240c0d41503103403543d2000024003d070840074507481e594062415a103c0b5100e1003000d910280004500340f500b07000a2500500400241c2810b501c4002c45155aa03202101c50740b0240514000c5080d0318121101e4030542c1e00244010109070030700109850040d0002445a210507100048464a540d0001080710301c0c0303103640b00a500460104440f07c100d000700c0e0a440741c803d08440001c10701d0b4000102180c41e0009481d848000128002c0d00100c2c03a1901c00c0d180103806410030001e01d04a07090039007001c801ca11501c02d00c5114010f0390b4400c0145841c1d03030142c40d001020040104101540d80c104600986403a030740713000d140b51810504000b180714001d00382c2c503103d8042c1e50700340c080513030750005070b0003030171140001c0364416104030010500101c1a40901c0000c046080903203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 955453183 1250 955451933 955451957
    0x92805101706060319062c0d030507120504030c0b01140a0605090303030604200705100b030f06150a03020432070212090d05010f0c12090209042003030a 67
    0x14030039102001c09980390840b9081c0859641c00080d420001000038000c0c510240d0340386044401012101d07512483c030350074190f240392840d543c5040b41050448a001b55055655200300460840d40b0489060300410040101c200a010841d07101c590700a101c2d0800ea371002c10799844075024490260b1003d1000004215880c5242c205001100c00030700007800c00314204552080000e8503030000509144c004c5940741507408014217040f442051100e02e0002c080e07034a014500b0803544a018402d4006900f42c01c01c80c0c100c51a0500240c441444800f40010303200c00d4407250394500c0030784503880c151a444403124a0210240c1d5403481051205408030111011200361010905070740300d5101210729240400c0c1c401c0000940c0c0100382c5400106140440f03941e101c80ea44001391118024100c090665840c001c107000d00742030740d64005880c0100781d4542102d10032414a0303401c26a013074114000c0d04140240003250000d0b035070301c400e250361a580c1800703c0c40740030f66000464619084807002500141114540c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 955454433 1250 955453183 955453199
    0x304050c0f0d1e050c1203090415081e0309040c030f050606040b030415020f120613020406090902090d08070b1f050d0b09070f080a05120909280510 65
    0x81403200c0c0142c0740810407400b6903d61000e00038024074031a540b0070f8414543c00820406000c0440c081000400c0500d280b080303000c0c055034a81240c04030307a0156240501d404245054864140c048036541c500500c81c04920401112005403050380d021018882400301c540c0d241d407540200050080182d40008800d21203a00da0029110041c1c55a40100c1c4108024130500040d1421644d02a8103d040303544070441c184c2c5010000c1c820000224060f10303003c40d0600034119101a03040c0a40002c03038000b0f08500078000c041007284110301c02e0071302042030f880b410829149940c020f0840c0c40c20040c007920204069845943d403d034003017101150b50401d540e0400c00f4011010031541400c00002c00c5103402c950800e400320703250f042d032020040c10301c0c100f020009000f110200060170152020000280c44295a0340000d80d031546101e2045400340141c146d1842040304000c20740d10303010401440100345841c0c3c455507254a074040000204000c0301c5440c81c000c08003942c003806000b551102240607031a4905044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 955455683 1250 955454433 955454449
    0x1f17010b0301030503190c0b0a02040e06040b0a060311040321020615060304030c020402070c030b06011103090312031312050a030e03030601020d27140f0a120305030c0f0304050c 78
    0x1054a031242031006101061002080c0d1391100c40e0141c13401d00c40811500203035460b45001f4401040b0101c1b0500b04041450340f0b80181048400404003010180c41d00c5041005448c00602060381021401c01c007089040d100350880a40e50803401d030030910f01501e90300d440540780d40002090300c1490039100100c61003941000300540c000030041401c02c0101070f82000800d01d100c0507101a040155a10a42c0250740c1c1d5581164440355100c020310340d06954070b241c1204020030840340729000c6403000041042150011049408000d40140a03065603081c03048000035640014111480a01044a800000034140400181d40d00d49a40f11180c03100785001000701a2040c0d083c29001035042401440201c1e40c00290315100044c560914a40301c0600c041e120039400f00180701000102c0c40340700c000600024800001840381d005481084901e40c1c0303041801002400c0388180d1032003001c802c1420011a00c254091604500d20714441494058a118060801e0b002907505541a41201508180318503000304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 955456933 1250 955455683 955455689
    0x5070305240703150b0a180b21040321150b18040b01030b0a09021b030a051611040c0503060301150602030901050903150c13210602091f1701 62
    0x207040803110104400d00300c10440142229082c0b684460043c413002282c0c0811070054401212150380b2540507400040070445050004940c80c81ca0250114030180300c80100c40c00241d0300f0340074541c080380000301c064840000510540400c4010030340f40b0000125442880c02e04404540e022842c01d50407014404800c29945c030010a01c1d8081056124452500403650b40c505802c40b0000b8111b205000140c020300003162b50307030340c0c801c40440340403031081060340c00f600d104008106204075641002e503e4030381e0380c8580b11901010400c188890008074410740d503008510307441180a0844200041c0106003501c515416a5020850100800c4080d081c02d220300d92260b40341601c10740e2084c2c503225019440340f260080980c1000400148103100d40c40400ca0100450000380403805240341c1615404001c1d081800c10b00c030140500c2c0c40c00201d411800001440b4034196000f20001d40200e55502c00080d07008a1040317410513207120245d08d2040401c0409640024a030300ca0861007414103945010a00c2c05070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 955458183 1250 955456933 955456963
    0x30c04090b031f0b010e0a0f090f14061c0c0e010305060646060f020d050a020c22050405011a010c0c0302090c0c060c1b06070c021012020705070305 65
    0xf040201000140c0e1000d251001d010001a0860940c001207406880080c07901e5008a0300f2180010307002071a05507442140d10982c41001407513000032000f01540c03054250700340e0102c110800302c1c0a9107000b07590140d03613003408907100d1150003495886c1c01c0510075542c0400ca2100d8088010014000c0030700c0f0241c0e01040444421940101c103c3c80c0c1d26645400c48103c12081c034805007014048400103103800b0021000c2d1483d07101c01560380000800401c0b5840c541401030051010112425010307100351030b001c4485402401d80e60307940b242400034034500d03c10445069950442d818540c82580e200e210f00841c0200000304001c0e00015920f4050f51003140b40c1410000001e181101007000c2c0007043d005c2d03950403280e00c04507840302e081d81000c034003462000200c24001d840600048846c4030f801458030f600414034918001034545805078507080e04844140c04a049446600c006180405142d45406c0b0182841c454408000502c6400c81e008824100d4182e0b02640042c0140501009051840c130071030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 955459433 1250 955458183 955458193
    0x301050901060e130b03100e1e030f04060309060b1f11070308030a0b040e0f0a0b0f0115140c030d0b13020f1921021207020309030c061c02030c04090b03 67
    0x9022902c4503a00004d80b8074030950360110309503550760030300002e0b0b1303268084202070200d40d10f0443e88680f100c0b020303542074481d00340c80051402800008015500b811160300701e010b0420703290400c147c001c4c1071242c600729100b85e910001c211599032680107000c094003d0005666400752501c401030080e070080f481034102035024420810004550204172988225951804149540d040c400315020300b1807814220301900a44000710381070400050718215a60040c070742d80d41a40c0b60004070000e400000e0103411030340140d00c40810f8056028000e88411540305040b09440c01c4280ca15060642d004084100e03e090b0300c40c0031f181124644440103050310b0000300070451400e0000300707030310030079119035840c00b907001c425007029159003402201c1c20f085190001502d80380c138802108950300250300800c0d0740c5030a60a15400300320828400025200700031406001001d10210701c508202c282d4100c0700402c0d411400540854241c0a10380c000f4601428051040d00d1311281070901541c1926400da011502036489 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 955460683 1250 955459433 955459457
    0xf02010605060702150405040c12181703070908030328060e0708150301020a111e190804090603080408070b091302160506190c080402030318190b030105090106 70
    0x944000c941880b13504440d000f80b507440d0099604524025584880d500c203103004001c44400da0003000001e028124928100034529100901118003074281002410b00004141202e490080304401107401541e103050080115a81e02052460365204503400c0c0030007140b00c100004030b0f00d40584000c084a1490354113001950824041c0501ca580c014103001c104007001020846900704030341508940100035000755a51042e02c0806012254681c4034a801c6224440c440f40104080549108004030a5030281020ba0303140c0542030840e8581a07820b03140420104000500040c02c0d00c502d5008521a50000e621b0f00e140001c03846c2880c03450340c0145032020303041003400d046035900d107154026000340381d4005880d00d00b01180822202d00600008086114110034400030702607104d140c0c190011080740c00d014400000004450f444802c1d500207415601c24050550300188030702007000c5602020b0729030008602103144602c4d0ba91a10382c484065020000014051800d105035210302508160409000e20f00c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 955461933 1250 955460683 955460689
    0x10906140102070b1602060f0708040302090f06030a0b0c0912061e280b04140907080706080c0a180f23030a020d020f0d0605010f050f03150709030807120f02010605 72
    0x801d9801034410651003a010004559610007588c0500718450780361030704c0d20240c0c508005150b00c2400168450300c00d02d000107260410b86009248a1b00001c0d0252580d1406031351801d180f05009003038084040e4080c003040296484064801c00e0440801e4001c280b14100802002c140280081017644407107a10f404101100040344202d1010340da51404200320055036680d0780e0001e091520000d540b041c14100d00f2140d21296a42c1c0c40d0248036a6802c0d108125920030566903190b02e14400c02010400420008840918840151007029a9405e080410241f000c20702080904150440d0719010f680c0c200500520524810503090485800541c686000f18840002c0d41c1d070007642802403042c000f9034030103c1103440e101b40d00d18100e20081c0665404880d6440c0140c0904401d0003921601000040c002829203001052449946800350103804840b24040810104a00041c40d8505101489000000142c1080e00800c2200d01855400100f142d8901700102000020907900c1300b16810803000b403361359 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 955463183 1250 955461933 955461937
    0x206041203021e0309030409022a06090a020f041103011e05010e0a092a03020a0806030601030b041e080a0f0e090907090b040615020109051011030c0d02090405010906140102070b 78
    0x103030341e0021113441e81e44000d106865440385d500b221181a001058006600c08140d5800001846800401034092201b034465035840b1400c44486041e980701c981c140c009814000c581c401014405030012030360701500500c0d071740168000e070700c444c0c40c031200d00401c13142d040c8000740300b4400341100b442d0204501015000184581c104e40c042c82e11810b03547c800510841004d20140c29000002491244088202c0e01000d40290401004040410300f4030300040d080c0c2c90045440303416641d104032503011984964035106602580404941c600c00305032090a004902076001402002003641d842e004078103811900107180080a0a41705d00808070304c014004074131400300b41582034441c6002c0002e00c03c0080000035019102950041c0b240018800344210002e506401c240300b164003800817501180e400810680c2100d10710140c0f04082c0c2e1050004c1814800c000c1c0040961150003100981880c0c0010700150803540701381e003c1d01c0c1041c1d4500040094500b410a107101c3c14030240068000b0620f0304000b00528 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 955464433 1250 955463183 955463227
    0x1080c1e0c030706092916030902010504030b010f091b020604060f14040b010608090d140a2c01030f020702010e0d0311030c0102030a11090102030a0f030e0d020604120302 75
    0x400d001050716040080100240e07640250486420300003801c0c4c03800d1a8588004c0f0700103000326040310b14007a00039500d4848046000342c0010b00b803031350a08100c5800b02d004285140049040103010071002021404400321603010f45001400c2840d224500307901c0b007085034104201a003010f0910847d0050701900803030b103035030b0154004201048106408654800400801900750029401d4106010501941418280c180c3d0510b8951445c10748481045941c2c0c0c00100303800500050a50b0760191003904640c014003030324103150504103081d01da024442450555414040c4109486042106040c0d60b45402405440880e4400440c5000c10b035800007000c040c6c0c131032807290042500388007110400d841600e5610784030b6005c1c0b050fa034580c5a411070260103513106458171154142016000b031070028024040328103500381600194a031156094066030304069039072501c02819541c80654600c918140001d0a10481c10307405494140b804c1d19101004010307159004081510502c08801c00405203a444101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 955465683 1250 955464433 955464487
    0x905130e03072a0e09011a130c03110403140606010815090402030c041107110307381309110f072316180504030207050f0a120308010501080c 62
    0x462031074182c5452543e41c6600c01a101a0a6010002000e640740b07150907000c3d84a0600038868008140489100c00e04001e500e50f5006851000000511030f40b0b0b0310000f200c4200e42004164610303070782d648030a05c0d0016070007a00c2202074440c202c446900300b0312059034012401d08020381c260810300350308003429409800250250b80070030085010f43da400c004180620b000204240808214410b1000300d5130040c4d50101d40402e002e00c800a6641740115a01007030342c0f803000041c4142c0c500a80091640d1100c01c0450301c801e400024031072360910019008040c20022a442c0b10946464004007400711941c03002c0d0700440c14000d02c00043c0c80c810010443c2c0c54030790000601001b2a0041020b4000741030003019208007445000746d10380c400603c4143c1c010856400c0f44000d4403504183c440740c400e98104590040050300080c2d0281301d103107400484d0360b1111602801180310247c59900e20181301c8813903a02035001c543d42100405ca6980d100940d035034411020107040781400745a00c60140d00e1840c08503e510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 955466933 1250 955465683 955465703
    0xf020f031606062d080307031d0f0d1223090d081b01150b12040b1008060c090f011110051e3c010b0c0703120905130e0307 54
    0x2041c0100c1c1d4022030054004603a510420f00e01211000c01d030800c2c100307900700414510010003c5c0c8032a010082d070b50f1007038140e1a00b080c0a887c0f401b486a07041801248141e00400401c1d9502003074596880141340540b0a10000d0404003c1810140402140300007100b0100c9211307044215403003c81c1e0a580100105503003181032103045151250107401041641100c14007032458154211105410105401845c8500054016110340b0003040a1282c040070440403080d0b03401180000b03604440305588100305402400640381c4a10055003070440989086040712808140d103502ca1800c48180000000c090a000320b1010302c41640e940c032009554002503046035200c1c00074001c40d80807402044841c0c6811213800d01c80c0f408460741010344841107403844490313001610100504200d01c00079604040850444482c50f8030304903980c00103500c0202c102803580151200000050b0498502c103100034203d84555070068100300902c42c0305a4002d0358008a941000300c1c2d4001c5400100451750240d4004c17500716 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 955468183 1250 955466933 955466977
    0x300c0501050a0c1202031b190318030e150c100614030c1503070e0a080a1b1202060f09191820090102072309060301050c042102030a0c05010f020f03 65
    0x1c0324250031f1403040d80340103000100002c000c901510b024500d41400d4804100048074145548103681e202c481c0280402c040c40c251074401e103400280c0040c038001c0880d00320320b04006180d0150402d01c54070300680380581c448206110344003080e03c0090704148241c004054085201d8001121400740d10842412500c001001c561058402c0c06800042a4050b100541150340c0d5506142d586d09001401d650a00d40140421403151240d4001000c8810380c4121540442141d000c0244590110350203d544540c03c01038442203407503600b6080301040351509150485482e0003000c46107203002401e181d105601d080c80f044060401150703100301700c242003081e10b900c1c1d4103480d0040c4d282100e65040381401182d210801118115244621040c2c2a030648910b100c40d2515030a0509845c01910303507000140040c4402c0c0014403d085c401c00c0d0301e204542c500702e0302900640121782425000d2a0580e03d10b031a210080c00a075030000d2601c845060b0a10050070540364020171581c40380140c5140c0a10490040702074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 955469433 1250 955468183 955468201
    0x507060c170313150b19030b150a060e0103230403020706020606063414071d070c021906020327150d060305030f0405010f0203070f300c0501050a0c120203 68
    0x1490400c48051b220b400c0010042c03408410100c4644011204001c1072400240f0400390385164400000001e807140c200c4600b003d40c00c3e10329074040c1100c1410195a0341c10642d4200015202d150f0311070b0080c040c0d000d1070402d424021704081c02c03900858103542c481301c24051103440b4002241d0685e00e852281800145200780320f404c0301c810b200340d10b26056003003140761030905c848201903070f000c4183e0b141110600d90b80c0352800c5020401c00381c014444030380480000351080c1c1c02103001203031082c0300802d5109191064840c44410b5030b102d404c880010307440854280c01050701210002c864151500c00301c164124050000303000740c0c01aa40901070310401182031012060390b900542c015603800030a41c3d403035698a40e00d110841d005031140d17a001940104034900d4003400482218042c03604110090038440c510744070088001c1e4810502d500b402040006600d4102c490901c0e0a55814290f603400880c804609040c2d09451000d03110070092860400c115100d1a0440e82c85881d54041c1140580c80703545c1c048074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 955470683 1250 955469433 955469441
    0x513110d11031c03061205031c0e1605130e100b033405120d030908040f09050403120204080c09060d0209040302070305100b2b0507060c17031315 64
    0x341d0b415214450b516190b0f19501c52152a0500c3c007660100301141e81d540010f0b20078040c0340d00191031600208030459034080000b107005547c261003203021460300c3e041c0c140f5900d04500d18000d14980c80c03450106000618007841c0d417048014882e82c00303000d20004140655195540c1c03140c40d9200b2681c45098484031b4406005401b5100034400c0904e001341c0c2c10145000080d00b440014040111101e078003c68180341c295000010306000d032000b8600c030407861005900604591000380c17002402800000380c041c880d0b40320007000d05038188000c40e4505042c034016100c2002c0c0340c0b191f142c1c0e0f80140401d001c0154001030413102100b0460340d80720181c17a87d00225100144200c0c0182d0401030513010001415000a1807900b213a1103074003102e00c00341c2c02ea090343c000c4030340310030b00300b03a00007880c4000c5800e8108070150b01e158000c460310181d03039000065551500c4c06000d54040404540704059080903c201e0f9a1850380188000c00704501d14909030408800240c440314000b014100340b00b40e2000003803070b03030741c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 955471933 1250 955470683 955470713
    0x4060e040911042306060c0a0b04170a030e1615180e0405030403120c020f06030a020c01060801150608060603010902030405030712021507020a030207030b090f1b0102010513110d 78
    0x2004074114280d1450042e0310031035401c00301400c1340004102241010012158a403000c80090a6044141d035035940381c3c090050015105200c0e081461551413030500c00400428003107880000307610140a5009041c4140085040d050080422080110310071b503200000070f081345458084001d820144c03004500c3c610316007203640302d039115034104020000d00000a000f500e00610746030701c1486d030500b8125400041c850000b500445130004000382c1e810200c002d141c010070990409420014078080d09421180282d00c40120b50303444056944e072440f4102c090348040c01c5245020440c620b80440820303c1880b06201d04910154004001001d105045c030907074528a500c00d81c9451403051442001b55105071480391446250812804500420300015164442c1541038010701034481ca9a1101021310320010b003066918000c80055480c414401e106100d0345010b158117108280e55000002421250300810640c01c114070360000707c02151410345240c41c4044c0841d102818101c06280200c0d0840340c41c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 955473183 1250 955471933 955471939
    0xa06141c0303021b0a06060501140f0a0503060d0b090a020a0506130509220318091e0905010204080d08011a0429130e060f1017041119030303060b04060e040911 70
    0x400380d4003080b840d600030004030b58090f0b035020340f2ba0b010003103035030110300c1a80801069400d080120210702c6002e07002540c0e100b0001000312100c1c2025444002102138100d0390b00c42c0a4005c40350ba03004603c0d100c6240c1c40940ba00b502c80d00d0400d10b0405141d000224503005140c42a00d4150001e048001071800340154040c00e00042c011190480c0340161961181c81e01c40916100501c901081e4140d181c03255420220001c080c0071506440c95008078020014424251a595000c01011031fa07510108200c0c108100e040c1d446c14420361400c0840303603882030b60803000301c04d8242c20001006141c0d0714200744030b00c000400504461003603010344002c26a1240c1c401c03680703c1042c602ca00141c898201401c040c4141820b86014000403020f0741001401088850080b004c171b01c4a4400e14141c03186d14031055400761190074560081015003000034040d5024104991407188090014005c050385401000010501040e00f241454180440603008084070110035010359600c50006050046e203024403100d1710320103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 955474433 1250 955473183 955473193
    0x30306030a1b120b09011112060d020a05030d050a030b0904050d261014010207031e1a010b090a081b011d040c091403060105060d0c090e0a06141c0303021b 68
    0x280c6005200e00004a07500d0405c2e518000c441514900070b00c044a018a03518a82c0c00c2c3c066490342d0070072034410301c1c041c816a0440400000818152400c003d8415585060748816456040c103820040c1030301c0c500c0f080d00740a554000103110003d02d002520101c00c1080342004240c510072039000da1821403d548403501107035188002d2020300402e40e1030301d600342c5424070070515a1100090059a48900d07500c401009a03420386a0420199641c003d0440654880c900b02100b01d024404101c4410b4001e0308142c0d00c1c0500020009454038001642800500891001d4060030003c1c030400d192500159058505121090b458030b58030394410701c540b8540000c014001c020b540e4004000401c100224001c100000d513205032644810b1a001031543d041300d8000b0582c0380f1700030800380d0510181c11204131400912000c540040750001d481c0c041c10b889402403000000c4c1e001e01c2e080b00040311644401009001e201c0342045c1c071500b41008000c5c007601d1030b09410b0250395125562030981d541c001e004040010ba0281c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 955475683 1250 955474433 955474469
    0x10b0d11012a0c0e07030e0c090606090405160e0d0305040509190e0d020105070201202503050309070603050103080d091b0801090506010509060618030111030c030a0e030306030a1b 79
    0x446445405072084121101300a50700c2003070650032038091001000903070b441142c00d000b5074030340000203951041d0007502c05801c01c48074401140c140c03002603411410040c2c1e4800e0f0300b07844a80c005c9a4030201c0c0d0048841c6001d80346d0f10303180902284554050b0a000f81d025030005003000402c031941d0503d686000c10204080410704550719100e036881e00c50075005500782004900304c180305000d2050605000245423110703159024081c103256002c08207901c102d03203500d0142a841074111802383c200b9030180c1c1f45d003507603490110349981c2015110740044041c10710307000040c400b0a40c250155a5031780d80310b0f07900007080280380c01d2462403002c04a0a1215544408002280d007100640014214912500446400340d0b204c504100c0c02180440d20a40c11010a00010b54a003003c252000502e450190000821485950000519074000c80d045a030046002003442445c5505100301304c040d001d800c001c1c60079410041c1c00a40c403915034100141182d19103c5000482021a242c54001003c0c1d03503080380c800d510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 955476933 1250 955475683 955475693
    0x20a0819140a0b04110c07180e0322050315012115151415030a0e0610050310061802180910030b1f0b0a1101110903010b0d11012a 57
    0x540301e05080c0c0510300303254a01782400e68035030a031046000d441e030190a00c5400d010300e00c1d82009848000d0700314551100d0303508001000a00003840d8468043c60400c04100c403482210036001c10551006000364400c01545c42d03400748000205041d50300c005000c0c240405039951030001510110806480c42c03000c0d1400d481c00f0906540280b007096449200005407035039500c910040b032603440300f840d40c100d009400c6020162550f5001554002d1030108001003040811500e90b00c0c203841110080e15800c1700c800180500d00e400c125405d2501c03240b10040c003601d030401c4040710442c201e516580403425004145250f108008000340b55818a001e013940700c162400f500b83c048a0616440182c0d5070200c402d000c03c1808031034061100e51005c18030001480203191011005042d0f0003031400d40d0400030007030f801c02440c100a0181041c40b0303100100d0709071611041c1c0100b5003100c8d8254070300340c401c1555000e400300180801c031440740c00410074244800c00300c10319010103e080b912040e0300c00380c83d0029660402041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 955478183 1250 955476933 955476941
    0xc07080904021b0d0305100f050315060102070911090111061003020f0a0801020d1505030d0e090a1112070e03010204031a13020604030602041d090307020d0203070b0c07090f020a0819140a 82
    0x700501c7c5001c1c50700c1e507822000480c06214005c45070150081d48416001605549805030805030610444904036514581c010031100b4049201250352800903c0c6015584d20920000302c8580d0000a801a0b091810701036802d01c9452100074001c201480140740319a5443c10030342d0043c4401d0300255603450840c20402e000300070050142500300100b50f4046000d08001849800840e007584503035540c6640002081081c0b00001c101183c29920341c0020781c00b8500c2400540385407411301c04840c400c0d084c4540b000c0e180824441409000b0380c0305000410110341104481d100b806614096200c482c2c9983c2100148030840007000f0f500702e5000580007081262550040c02250702c141c0240c25038100200c000c0800c41c0041e10485000e43c0f06101c0c45001d46080346100c3d0307440b44010308480301d26a840400b050b0640254640c2c4da455000240100a88080c0340214640a00c031654114584200d500c40640380180c05022407010102540720091811460780c400d981d0301d40000a58081850300c3d00c0e401000d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 955479433 1250 955478183 955478191
    0xe0105060a090c090905060a090c050702030f1906091103070305070806060114030c0d09150e07080f07030b07032301031104090c06030c0314041103060c07080904021b0d0305 76
    0x7244080e500145110380d07803080020324440d50f5149403203103180030b0101c0f010745070184c04658400e456050018040c42c0911036207200340155180c09494201a00405023010800760760b51242e5001300d007505d244035100b80d00400855600000c0010300c0c5c062420080c2d030b10041450703020b070544905c500100078010b0002c0c0450441e407017541141e07184d50750350004484001d500480312990762003c1c07021441d032441c558041c0c480c4802040001407402c10311746070130b10b041d04619556240d00c0e030f494281c0040d07000b06201c9035018002a400070a140d80710320f4921980d602c1548409040d000c842d2012940072442500300b490b003107008d07003030f0000c01503500100050f000e01e00b0701c01241d00d04035240b40b15407503040074051100340a8120b070603200781c80c1c81d1090070741c0640a08100081015510290030910020306a0007900603030203118248800084a030500d03250800185c200110f21500340712000000d071054046400003881620050b840c3c800d07d104419403485030505c1e0006a000d0001d5006145905601292003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 955480683 1250 955479433 955479439
    0x12050705060108030f07140319110705030304030b040b1b030106091502010c0f030b031e0705010801300305040e04030e0306070309030c0b28060303080c2104150e010506 74
    0x1142e42da0b065a00d40e64850052209410760f030500a400c0802c0f002902e210410752000f058034585110450030003c010321040c0c000c008a8004004020990010032920380981020f4008603d0503086803950420290001c01c0200000048000030304a481250541d12545642c24041c581300e58403124090b018900340e0080e65a56001d00c003000c90050310501600d00c56240940b5800c40704507044408402030302c004894a44c141c82451850000d000030f000752500860a6034014000c5035003000001421a10113034008100041d004090500007001c410180d46080100041d007442c2c0b102900e4103944034000c82d03004122040b0117000700400d0540110681e880c5d41c0044040d946160b0700d804081c2d080783e0004002400044480c40c041c0001202d1907000c0d6004890b425440c804c11003a60500c40202c00340484050003542c43c0c180c01c104158100903103980104a07148030f541445205080b81c00b403c07401030018002c00e51048042ba05000000701242008900040140001145c01c521035000e40810340304940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 955481933 1250 955480683 955480693
    0x403030504020316120b150303180a0e04081b120a0324060507080f040302030f0a0303140105150d0e0303070c030e060408150a0b04140a1a030303010b0c0a12050705 72
    0x520003003184d498801d960342c0c96100b04801065440d108840e450042c01208000048910521569001c102408403e40404090000a00d480041c04001d001c80c1c0c0c804001c2c180041c00784400030702c03a01d05440000d81c3c001c1035018107050790315042d884e00f825081001d485100008002034410351540001c5030305041c01440c46a24485121400005001c501c41d000001d00184000400180140c004140c9130201116140c203068994000a0a050203080300c1451940480c5050701056090b000d608a03d855103507002d0b0543d032601022940c035143c02c101d401000c2400091000322515594090282d4141810441e600c900c0c200780301501c40e82d4400c03c158040b441d000320420705890030300c045805036207a143c06003240e84903c1c0000070144c1c0b030141130300340d09684407103ca2450340c840d482588117484d140798450b1010304011100a00f107603035141d841172031810400b81c0030803c1d131400401c41e41101c04c80100c8a54803a024803100341490b8100c44003c0c0482804542c0d4440c59a12a02524400703000b40c00f03841c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 955483183 1250 955481933 955481953
    0xa060305041a070f031d0f030403030908030a053115030b0301050405030409090201120507030507030b010c0c031721011e080705060a0c060510030c080a0b1902040e04030305040203 79
    0xb90b40c00710125582000030340318501d0001030078881c0d001040039441c000111808502c0082c80a420003409008051050b40045000c005242c0d10005120007400040065441c0a4881c00c00500350702c20030321000c1c10180d0020120344903e58210048242041607070444940944a5140070b82001040280c400041d040514661040c581841803500403030340300005515261800e0a5070029105045099041c46421030703604584514a008042c8505120b503400500f619110402804580d4818000b038100070f4850040d000142d002d080000c10303290080c20312000e034040000c100001c1c5c41142f5034659894020341881c03030b40e2040d1240c042e050703800a0250741c0f03d44c0c044840c010441c000c58030800300316506c40541001681020802480e031051705180090144400b13844040c00c0d50816511101c502c2a132150800038800002c0408010300081809030041c2820741c1c40b00c1c8a4003002510720143c820b5010307203407c2040900e5044500400c00c501401ca01480e207814080c0003848101c1d0164000e0064038900 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 955484433 1250 955483183 955483223
    0x62115092a03142406030c03040303050106050a020a030806030f19060609090b0c2206020f10290f090106020618010b060409020c0f011104051f0f0f0207050a06030504 73
    0x1840c401d000c00c10f1201c0d0b540740311000002105001c1c203001d4640d90028400603070349500000394031a49021000c0d070358905041c9002012514164401020024140000c1c02031503800f00c0c00d502100d400d89400c500940360f090001c6d040c80b940c0704c0b212085110768540c40442003022810403581900038403080001640d02e8000300c0948500d0301000304803030b480304009611070140d80050492200040c180d0744040380105540580512203801040240c1d102c001181d10701d150800800e4000c40d0a100c2c1401080000d40302c80310241640301400b031140c1000310305540e05498584800742c0c0c10300028408212565900d202a40303414099801100306520121400d10344441406040d0000d540649070f04c1c03806141050390002508640316000082c040c03a00c2494a0101c01d008551030000070140c0725586074070b00303020413913401004421150304000403800b07043e40682144128164120a0400301180d8801c8038040741084100e4004036031000f0740140102e980d41d410b03449684907900c03c0780311501404100d014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 955485683 1250 955484433 955484441
    0x611070806040c0b0309100906050f0a0902011d01140a03020c0d0f0219020f03011a01020f060f0f070915050706060b030603071a130314010501062115092a03 69
    0x101034800345901c481040304c03040b10b1000750703400810700003500c0c0031440c000b00d51815907a8008041e01d12540780c6050007901c0b18604541a04080440700410080c266603002802240c040f0b2000039460951903000c24a81e40621848225020710031411617a606500e0800b4000f9042100030b000d2520508481c01c0710907010300e004649520054008154501c2c140d040d828445480d800202c2e00702c10881e041c0110b07620709018801d120300d40750f40400700c02c198060009142102d51001120180d102109100101400403c83c075007120007a5140741c140e07560100c043c2e5408550750300c45103d03031008100d1070a1156100024011440c030914060103105c0c0e0301c0400c0c0e0700a00045d508541d02d900800400c02445121802c0307813042c50b08506210b82072010b444e0b444401029241e00c10b560003d08442807145030b450030311a02d07001d0112070505030100024413860030103101d40c8840c14220f055549280a103101d82c406001c0d0028030700c0550910400d40c50f041c91307520b6041c00c0e400403940d115811a01c040724900070b0007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 955486933 1250 955485683 955485691
    0x309080a1505061318170405090a0b0607020d0c1a0f0d05151206040b01050a121707060e03070b2a13350706050703050a180611070806 59
    0x1201c07201ca1006031801c80108809031039154421240d03500c9003681c00603401141603800494050320113050f0f01d410301c1d0300b60078920144030840c1c0038208018405075403003408ea150803072440f07903000800012880110712648140b65000c1d6200c1c9559002c181000440102c603400e4940003078418400399180e00c0c1c04d00340303800f80300c1c5c0c81d901801080c03090490980b541e921141d40100c822000350f002c4001d21020845031402d03681c1c8c2c01010f0b002a000c200501200303108560051400391100b0142d01c0c0b03041218121a03502c900000c014415070390903120a442604141c40556030031040c00c000d0444484c1500782d407584030300c400315034140c03441000a0010034100e61039610010711541090580070508401d2689a0004034019424040c1c5000402c0d10100200c14500c590090300303103c0798007686000501d820070b5425050400c40c0c3d01c40309052140c654010305903500f0741e6040c103216445101104059030224520801a907100b100c0120000780103500c0412000011818020b03114a1900c6009541c0c4801d400c032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 955488183 1250 955486933 955486943
    0x30e0907080f0717160306080d1b080906040609060e0405070207060c0f1e021504120602070807150b010f09081203040813060c14010c090b03060105090d0f0309080a 72
    0x3000900700b100d60440d1558410750794a402a0200406a9420860801901d00840400400306031020154052040318003801c041070050400c02039a10006010290a90203080510040b540a2003040741140944590140050500e074445440b00001056020b10740f02c0c141c0080d2040c040083c4505191040d140190711590217022a01d0800005032101030b030020044408806804400c0301160b0111109014203000c284001000c40031801042055003101007550150070042004110100c0740b03022a00d01c03254046005601e60300e141c00c00407078600407050702420941d80110300894140c501d0784072500380c1c07a090303d8108801d00c0b820000c64101506015186803507109070240340004034000701959005101d00600c514054559a0000807207441d03a100350085007000b0950b00801c08018003031010104004020002c4010200001b00054014490f0119507040040800c903280d200c0e00403070b02c3c0000040c00c58082381c3d0b11072401c0e2208142107001500041d084100210f06801d000c41c070302c20019040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 955489433 1250 955488183 955488197
    0x60c0b06010c0b01030b1305030309160e012706033302042105011803050309060c09102007170c060306090a0c0318080a0207140a060507110a12030e0907 67
    0x5503031b0580f440701c024242d00481c00b0703201c05040000d1004c00086100340b00b82c8000e080c00e85591314035040c025115400050340803002000501900c4142441c0030942c03c2d14a50102e880380c415080074000f403000e5040500b41d094641c2d0091481c81100d50300401040700020b101c0c40301c68150260f40100d00481c0115180108405000603040c8801c5402400344d500031b0000241829200d42c3d2375404484400080b00440d40200820001102c1400b01d03941c4000d6080c055454507a0900003d8891110a1200003e0110f5004a5001070044600c2c000040c00214100c0e01c1c12600e806003040d0010b4403090380703001031043c586000c1590404409603070181d40d000d490701e601e9444007200c01010f010040c01c4482055500c110207400311080342c125010103400740f03245c10341d555003940c40203081c003a094201101e0001301c0390918005407900c4c003451003219107500d4034a48071000d40c60040d90184982000b143d02c41a100d00115022160175807a01016200c1c1d21110082050f0000b0b02c104d40e8011039541c4046001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 955490683 1250 955489433 955489439
    0x605281409010b030d032012072a0803040c0b0a050d0b030f0705090411030d0f2303060409050102040f03050304180606080411010c0b0a0b0312030105100315030606060c0b06010c0b01 80
    0x7940218181c50030014150081051451010700c1f0754008900140c0b4404202c002d100301260000056400c00c00201d6251104074000403480d20590131100004244c00c100000207400c1c8400e0041c0d2501402e15100d00d641c1e070313440443c001001a00b007a0340382c078541440e06880030384520780010103c0c40c2501c1a0003910f4000c0c9400104090306034002c000f0744100c041c10101540701d40d07050009003207400c07041d140d00ea00f4080401c802084020304950301c801018074840c403828074945c2e010980ba80a24111400b088840c0f0724500309019011780c3d440304c1c1d158034401c0b001104102c0c0c0803010b0030a070342c0004c8241c440d00884102100a59405203d03040c08901440041030100d00c3d0240124801103042c1001c4400751025515030084a9040311070818031aa10aa40c08562809000c682d86811020f081307141554107001c001444c42c41d801c2c4a07541456601d00340300c1c94905180c11480021900481c0800626a0340c10020f0040a02410b044400750600c0000070540e6020340d800482180d005a000d8045a003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 955491933 1250 955490683 955490687
    0x106140a3b0106050d06050303030f04060b01030209030f0319080106090303031d030d090c06090305100506040b090f19050c0702010e03030d02070f02090705160605281409010b030d 79
    0x80d042491070041840140380d06400c4415109802400d142e56001d58a10281d081c02080b5000707600302c98440c0c0c2003003050001080d810107106400a420110000d1000c01c6480140c1c002c2c421030744543d0305030080308801e070f02e103030b80104c0580343d0310300d4a02d1544038284003a813044030904001d0007803a010884100003400802d200354054030020504201c8040c2010309020b107149942c2024032044251901c9074031130f4040005e9010145e00030141230401c940d03054116500e1b01c2c0c81d45800480d1007400c5a0b0344002983c255550b40183d07040c03407400346c047d0f030050a03c0c2074202400070040fa072101510014412494a0540d2441014810f50145182900700283d42d80111102000c40c44400e80c035110900105c20110700a1004040035407003100000c5090600780705020100d0304c005c05140c103101d030502c134030741c1c5660b48a01c1021029901040c0007500365909114107800118a40c041c00086030010680c5900c203e56600845981001095801c2c0c19601c90380c2d003909035046038402607003581019141e01490340c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 955493183 1250 955491933 955491989
    0x30f030e0a0b0c0d0f09050f01030b040f0e03071a130b1009060b12012306130321080f010515090d120314010905040503120403050712020106140a 64
    0x1190080858510740c0e60303110240e035150031485005030507401c81882484040e4103c0703181005000e1318100316564900d400b00044008002e8030100d810b05840d01020b00642d546e5502c440459503c40b01304226240207142d00316602d41042c030b011508090310ba01c0c02032004090905191042d1705080000c400449165100341c4c8100c4084c040c0a40307600d8a84005c1628910303801002c01400300401e51036120141640701000800041c0d0290340080039032041c441010300c00710507000d0b462000340d030074a5542242503e5511748488a074005030855810281428034248003500d150044005070f03443c05004c1e102c2c00f603080000742e028031600d41c4c4002000c41d8685800c001130060110b0200080c030700c2c0a80e03c2e0907103030070b0440d00810700c64a002907a940c600300802d00780003c5050150642c803c0400071403415903101c650700c2c4294500f15504850200009003014401c0040300d0865034403511124182d200c102011307028103128054101400e41400b0502917500746442d141d42283c03e10726075041090000d0750040461 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 955494433 1250 955493183 955493207
    0x203070b010906151b0b04050f0d0e0303070221060c040302122e15030f0c0608070e01080c071b08060c1329040305070501080705040311300303090c0604030f03 70
    0x30106140c0b005c0104102e144054400d5008001403d9204601c00e44282070089071080c00301409404800d02480c2e841c004151000c140e815110309004800c3d84e9540000e10300c0c001900381e50382c8680d0302000108000e65015100712031080c0d0748102c882c03204090710780c0c8442c008a01082c0d144070781141a914500c46c5005c403080646101c00000f0712a0254417650b00c106000d03041a04d0303003074011440600300407544e0782c0200204090b00e407100d030318144048000c008a841c000034904101c0c5010108107580904004c03144650b03404054001c0c0e000680042000508803480790385244e018440005030905a54400c0f901c0780c5103500200b00e2070a0520030901040460040c1c90002c5088d031581c0d44000c484000300900203180a800107186e81803401c00014443d007130040c103100400c2001d01007040040c5001820200c0550102d800821024010002076003000c1e0242011180001001600f51251004401580520096800c4d604c021061809000e204d1003244801441c2e14502c1042c000030138420900034050f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 955495683 1250 955494433 955494467
    0xc020d14091e04020c010e0706091512061212030501050604050105120a0e12180307030b01060e03010b13021806070f020d060e0105270a051c050c0601060203070b01090615 75
    0x40861800040343c120380200e10406450f80d03660711002018101041110002c01440c0360801200342400c801c2140324071000100c500781b00b040c0c036450103001000d4001d100501001341c030289031414103040a40902d030030741120f603002c1380c5004004101414480c04a07026240306869103480c00000800c0783c100e82100400d041600741e683c103180409904240b101540038804887c40c5030315031380148003078400490303455581d0380701364882c0e0320810026480e030f0003641c1107803170a007410460b40c200710000c6800340492aa07501e81c003004940f14680d5040f0706038080d100003000d44004c12a003540400600c80d13103128681000d40340061802d066001890020903040b20b2078450740000c10703c2d603017191000c2d082d600c00f036602c08801d00440004124031300d5507000d515040c1d10718500a054150445c0c498540f503c1d007001c0f5200e8640d262103000c803c0f190103001161100502030089412542e52468025240e4002e0b090880d0000c808000014800c940d40c000d00090740c60006030b100f80488541c10a444e40b000b1400380101c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 955496933 1250 955495683 955495729
    0xb0306010f0c060903031b110a0b130f0b09010606020307020d0b0702100906061706070903020f0f06072a030506010909151d0f0712110a0e0a0c020d1409 67
    0x40c401d01404494a205e0744003c182900310702220710303c030b9145400c41002c000d802d0303a503a0000b810000c0c00308000d5420034414401c82e1a101d189281e161302d20807010340900002c45001003041045c2c20124805e842800007000307030940700c600890b22413044a1020b503000148140c0742d0081138488600540240310350044900d44003401c000042990b80740841a180e06a5402c420019140c0303440703c1100c0381d111500981420703c1d08450107032003081310b4040603005104848c2075406d261226091080d04950040002e42c40d4101ea25002e460102c6030750947d01c000c030181c0305119040c03603c010310200392a80b20300948200c5e03003010100c6009104291080c1c0c1d00039a1000c00b80403011041c45080c4655100400180b2035000100650303142542124807039100c0d920102d0200b01412619440e407031565800f80c1080300640303859000074034602040e040024130502510a2061305281c542c0045100301d40da80956420100c01441690f03070085080094101c104100030014032850130881010b1500701d5400e00c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 955498183 1250 955496933 955496957
    0x1090f0b0d0213060504050f0405070c0b0601050f0c0105060a050607051e0109080a0806030d090f0b0306211e0703030801091e050a061d100b030c070615090e070b0306010f 75
    0x1140c0d00d035580f0084c0420ba0000301031040d42040f0301c00b00f8400e6401d80f01480f00e070800c20001881c0340002800580404c04910124205a10600840741205240c40350a5100c05846a18500900c0c05842107442003040400000749402c240d400c0d101d5582d0042c028040103006d0f042c0404145003682544d030b03840d540c0d50a1138400078142c5e6000d42160140341e80c54060902d03050040c946000540e02101c0305100e4500d504110301c60119401c4000e5601020f5004c1d100d4540e0b1012401c14000c18800e14425103548030716420141d00082c0410f0704e05115040c1d5040e8840821010362100a107020140004103c48014840c040480e007040205680c1c000300c019202c200d04240b03004481c4141c5031400c00d80c0e215081008500c50302210b401c0c041c42e01c0c0c01c007210b103410b220840c0d0340341080c24401c07458405001b1000030030491080c01075a540319004041030040103c40c1d80c40c1016030b000741c0942000f072864048803216640000645005980c00d883c140c51560b11107400654181c2d041e0030075070081203a01c4078030f5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 955499433 1250 955498183 955498207
    0x30e03040e0f090a0c0b090d061b0f140405100c0506010b03061905030a060b13150e0901020a1d0303070c12061803020349050601090f0b0d02 62
    0x24401011544007a4800341441c110b04191084054407049140d80040304203070125821221040c11144c00000c0c56076222007042c00b00d403031005080c00240500f0316103410001881d481410003a800c0d2a9551095600b980c10241a94426a4007a4030f00501206002c203010509142801354100301c043d09200c030800d2555511585022002d07003082c441004080244001c3c0d04144000c10758808000a10001103400c00000c00c1d80c2d4455594040e20f201d40b0b94251455603107030240943c42c0e6101c0500d003401341c04040c0152400040e200c0c8500d01d203100540c000111020010300c01e90b61442040d9583d000b1202022051035030041080a45039410700040004100042d140c00c0490010902125840080c7c44981000320456100301e19183d10f00d10b043c00148001707607020003240e0b0040440690b921400c00c0c0c00505c441c440c50200e10405050021500ca0b110b0a128003c810400d05900c10003440303150b880200448602160b0310404003107400d0408280480e850341400381803080e4a1300300040c03c1c1500341c501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 955500683 1250 955499433 955499437
    0x2030705041203120b1c12090315200903060a0b031204061107080d0210020a211401270f151215020a080423062d0601050f0a030e03 58
    0x70450100f41420000d004010417401a14074000044441400c41043c030a0000341c0d040d28424010141e01c0000c81c000c90903070185a0440c055600403031072001651070042140300800d10081501d903010b1704000246c080904120481d00902006005080161103194402c40503052111803150325004030300c00212034458444c0900300810b1591b90300300501c08070031391080c200152600072080c01c2e00000765544c5002e80000b00c43c030340f01c030f0a4600140e4a240710481107a1002d00041c0d039001818030a91009284c40311504008866090a070031186144d03038401446600b00c01c0e1074000d0480000f954100f05500340c069000c0d03c0409496a404609604001094142c1e820540c11405020f02c00f01ca00c00e0a01462031071320103400581c0f2004625203910100c0280c04680000c00c010301164900f0301142071241c89549240d0101c1500046a41c170b410881070300001d48107010302503480ca1001102d004451804201818041d103010b8441916021002d56500419446180d038102416281d0b007200f5040300302080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 955501933 1250 955500683 955500719
    0x33f0910140c091e090c071e1115041806090f0b0307061409060a0f12140c0304020415230306040c120516030308070905031c211803020105100303080103060203070504 73
    0x11b140e07290303032516040b660f409400f0070758a10765810103c85400249144003480b8440340483d000c0760fa0480d0405513081600c500d0b000381c00c0b11404442194100c01441c0c21020aa6604100a000c0b5480b00c001d142e084505941e000c0368140c1c040c0c0e104100340fa0080106420055a185c81c540c030b0000c2100100d0f42a80c0011003000c0026508241c50011039840382829414110800080c0810b90300f112074000c1150010380707560506800000403c046503190342c0182100762000108442e1a41c1d41c10701e46680507059401c3c40035a554400201d01245000b150080c4150740c06000b0b000d07158201a07402064803c046411205486100781e0507042c1c0070303217071b14186c011440707584c9036045845d100d5001441040c01d5841107000e640001e20b1440c082c481c84d8000300c0385134000e150100184480100451903412045440001585004143c80c60400803a030307a401180d000b034000740015128014408070345462440040c0004c5c1d2035000600c0014175039001160010000e107801400c0540300d407408540d07040700d04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 955503183 1250 955501933 955501951
    0xa18030506070f081003020603270c0306070f02030f031305030301090f0f020703020c0409031206031b14090403052d120702033f0910140c091e09 64
    0x10070082c1d82c0d00008078a1200824034004110707092240c2c101800c1043d40c000284180c2c00480059040d058690500306480d8001d00020242d18107002402d464826584006000c4d0060f80001540b050168238207803c5c00c5c407241e00a5191403a10001d0071070700d8002401c20220801e00c078901d0380c0466009c00195000c3d01e4024400035498102200340000c98840c2c00c115030f0031718011f001c3c400200350042190081071070f041d58042403681d402c0c902103c8800f04264032040c1e59150880c0442400307204400c9222040c4440203d20002d030311121180c0d11030300e0240f9619440400180001d001a200c0c1c000b61006a0b20520114401d040c24000224034130284082c2d0041d010010941c0b409070b03407200d00c04540000c19070024600e0810042040d006078002c450300b00b00d10541c1c600350300c10320b201d404454452a020400d6040b41c00e0801401141d2616a0529a0300c8000c0c10001c21041002011200d503018203135036684246050070340030a1007003010b0a00c030b18000b550441c40750030f103131900e5210b80640b0901c0c0b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 955504433 1250 955503183 955503193
    0xf030a020f011b0c03030c111006090b04090506071b21030f05010305120c03040b030103120f0f0f1214070e0a0e0402060414030708150610230a180305 66
    0x3010381c60860340080202d41d192004540540700c5980c00a84601c0c000e505442c02240031511010155911402941c0340034062003004220300171100d89500480988140d210103203c0c1c1050402080140c1703201d280c02174080c0d007240f408115841d015074681c01d19035070403008000c00765045850b1814000910743c0000002441c1000c1c8008203540b41c0303d90b40303c0c0e070b9421100308055411529040e9035009580740c044540c0fa00054005150307041001034a0003410303520b004035504e607100e180c0000c5a41c4004140070126840180300386e40e0900507040c0f0425501244d440001495040800311900c070070390042180220781d100c20540707005082c81511440340039242c5a005400d40340d10f040c0508a00990301440f40c1001140c140030045e070b40c0d501240d00704c17481418000300c076411000001c3e082216a600c60001445400c4d148000118041145031281c0d40840d400c58908200d000d0690b10000c1c1940c50000004a9103401b0301706d400d000018004170300c1c5502c0c1c4102c6100201c80414024607030b90b0402d0300c0c15804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 955505683 1250 955504433 955504453
    0x8070f060810060f050405061c0506030a0f150b0d051e0c03060a020d140a05101d07081008100203040605072604022407020307060203090109170f030a02 67
    0x9121a4a0014189840c01c240c01e4a00325048401c154090b0254900b000303005040c00151038803900c00e440c0948402000369641c0c44010394048003012415aa41a40500b0701d00010305903e40400c02c0072102e90001000495012103a44c2c0b511041d4800501512559407407815a140741c89078440a104244140010030499a0314115103140c900b031403420443c560701400d403060b810b4070f01060b441d07003191380301c0000758a9100058401e405090902c065502503c1041c081252101c0b960300041d00520030810394041c582c0d15100e030303040108070704070030380070803001c10000f003800c00784501c00351580405600310301803120341c64201450810307a0829114085075000b00502c01800610b11540da00042c4600b4444110308400c240d0580322003095100078406078040300010155150752082000d411007038503400d5400050500662515001076105030f00903c511200402c22038000070845452050503100d502c2d6151824042e800c00b04c80c5c141c0d601c04503004003450143d44101c10000b5004e8103030030350050301900701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 955506933 1250 955505683 955505699
    0x503030420030d05030907030b101d060105030601111c27060905210d0c26160309051203071a06060a030b0402130305010204060f0c38010807 62
    0x1e2038925101644001c80581c19a030000b545a40c4a2814101a40c0302c2c0c0e00c40c3c031a14180f82990740003130051101c81007004170a01900c031481040e10085000481408086a06000d4004007180c00d140441d10401c081a455805012150a2960030700c0c111054125041c643e82c203070564008582003c100603c94000c407441030a8400d48a40c400c40403ca5440d610b81a03006000d00741c9445014003400742d0034010f0300646809484050b80d00c5841c800c660144503810310041030310a10803402e940e0b0414481c05401c001e03450040f084103141e00e42002d50308250700e84000011869050a0881c00c2c030040540020307850b1102c41c0f4180600880380003550700c0305480d0030701c0e04c00d031300d0144414a810341100003000455610201a1107107a82c0f01c2c41e002407400c07055800b050091040b0b040c0300c0741c44240321800004105054004009540a582d55108070141040c010788400c9030b641001031050240c20540e40381c0740000c40303060703c5040c003000640103002c0c24100120000304c030a801c0404c4c0f03a005860207101e140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 955508183 1250 955506933 955506953
    0x5090402061e0a0e2209020310050403080708090316080903010b040f06080106170303150d0f0b0711010c0c021c080409020c210d0e030c0d05090a150f0f03061205030304 74
    0xc0010364071165441c1d1403558919407440c02200160305c0b82d60b035048400541d1001c0050400300c0d80c3c0c0c0030080006050606005c1e0080f071003200d801000450280c0055601c440c00b03c00d58074489408c0c0d07500c41a058680d40e85c038045030040000590550759036040424aa0b42d103000d01a6080407661340091001c0c14108002d00703540458000c3c3e00d254444424000320030000004486d480719010803113411480e41e505c0020814000e280b8046c2044000f11000010300410141850080714191a1072807640c0700703050183d0994000000354000320b00306542100c05814105c3e4024801e8212030032800200c00159078490f900d81090300043c41059020454501c1c1d03c3d800c121101100c503018881515507920403031000903a2040e80340c04c1302d0342512080a41c49900c010015100b0281d02c250603210749000760140201035400580c6003a02c202c40715000003a00402c1803800c506544170584d29202c03c01c1169000f41c51183c09820610200b40d501e64002550034001a4180c02c0503101d80c02940d070700c1c101420020501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 955509433 1250 955508183 955508207
    0x140d020d170d2901170408070516080303090c010e030703060905010612150b011d101403090a05060606090105040b161b18151211040c03060501020f1605090402061e0a 73
    0x1c1704038000540480c00c41c500040b607005e603020490654480312454000c1c00e14050f01445400e0304012040170034200c00c040044d43c4500482002c6400b0008002c0c01156015270744500250150030286007800031608503000342a40709d000313000100d40140c0d10405e40910f81465201690802180c0c2651110380d044d03402a40c80c164000d290007846822270078a41c01c4a10b24180209220b4110300c03061100d0b19003c1c3c54500d00a041c175260306130b121b2511518451703c03a40070480803202406040300244091809000750b80700024181d41d52810142013009545c1168401d048a002181201c001240040e0b10001414500040781d00c0d005081c1e4a008482c008038120500c14091442c1003059144054001202c1c000c1101e040b0b0382080c591480354100200c095000b0000c094206050403900705689030540c114008440c0300703a00300e60a03404822482512040c0c410005c03801002d40550410061030600001a002030000b880ca034944026044046100811620345a0f400c032008900d0000c074036000211001c0c0d03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 955510683 1250 955509433 955509437
    0xe01120207393501050a02040504140114060307020f07060f08072c0a0b04090e061e0406050411060d050105010f020703080f1602090709140d020d170d2901 68
    0x20345801c186a030807081091001e0f00b0a20b9102d03840211100210103840100d010071071000300868100301e45520301035030060280034043d6082c00d00201c1030b40030491250341203a102c070200c6485c4001c0c1400304034040d0f001902080c2184039903216440d02680602800300241001c3c2c032141c803650f0207124040d0030310030000c2412081c004400c1240c001500e46030145102c4180803a02d110795801d0352800204140083e03005440988408600418401c8480e442655030045000484d29a5968101c0d03061802c82c48620000c4c0e4802460701140011740e040e0081600306219805140c0c2982d01c110115030a900f014400c182066210300c01040742c0e58005c103403403020341070b54405000c0c640d046480340129440340304c070b0181103003100150781c4640c100c45418645030541d00820b07074007450800820042405050b07000e2000801103d0800060500d48060b4010310700c0e078081c00301c002440c0c0f00d8490007484089140c030244280b400700b1140224800510440800341d146294002001c0076281c2c140c0d06240c007000020381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 955511933 1250 955510683 955510793
    0x60a02063903191b180b0c01090209010b03101202010e0607050303071d180603070923010b0421150e0a0302060f01030b130c03060c030209130c0e01120207 68
    0x90908202c44c00740c0c0d03654000b070521903000702c00003121301130580c80c50340078000003440468003010072203046d0000b01e90940222400000350b40c03907220203a201d22080d5428019202545420059a600c00400100c1130340141408103600810700080365855000005c00c0303545810000400c00c0240d04148402100e0100c031047c0350a103280c4801188581c01c4015103011350f80c03072100000d0300c6039400f004420301403c000070060094030186011490004852521000206410400172590001e60029141181c074002481c4c0b100504010308921a106160000e55498940b10304141c0400d00034040c2001c40c604000003000e46038043c0c180281025000b030f040301d00e111aa0b40040000c070702044503960700b10340c03882440001c560891521070380000b480da00c010411814a0307200b820300d0781c0641c041c1c18080000d848030003021460741c440f001101d508108201c080b60940007040c2007035210b03020031482c0c0205807000503d001555240d00c0c2c4080003c40003006011505540e0540d4100340700c0202c22401c1203000110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 955513183 1250 955511933 955511951
    0x4031e0203060a1a060403230d0e0d03030f2405010503090604240e030307091e0e0606090d05010b120304080a0b1e07080a0605060a0206390319 63
    0x41c0e199078010380f0220320662a060034855074080604c2d086142d00b0003c0190390b4581d0f0700d00e010085600711850841d2150141c2c560809040004124903007000d0a40d500c030210360342d11a04204104000e45020346c1010740e1540c129131890039510410314108240050003600e200030840030b040f0207409401a5041205c2071050089000c000140d0356001603010b286280d407524015803200e030b060101c030342c1a1405410301c55540003d040100040d80140d14554881c038105803074034000c03030100c1a60860818020102041040b9405403c003010340c22100041013145002d011100280e81c40044440a444a95448100f02010310b000c501c00d00d041000c0e400079504041c50419160340390081100e003d4015584040025001c040d0004406510004400c90010600305450020082007084890a800703501d4402c000c10f15140150a4417891840da500030076099903076100c41d0380c0b507070f02c0e124031400e03066010b42d46049000030b4040000c5210340348500e016101e00c4d00302d01507411440c030742c000141c07000d241050038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 955514433 1250 955513183 955513189
    0x11090904061512170f0c03030a0b010807091215150b0c16030f060b130c020d02100501230a0807030825020f09100509010f03020103110306010806010c080c0102070804031e02 76
    0x520306030300c44c81011621540c92140706001d6200d5803c5000c01d44c0800400c00c003100700f859001c804001c03401e0b81c4000d070558510b00305403100e80c41e41c085c520b080e0094a11180001c0c045040d121108800c01c040486d07114254104c4036008090b5802c030340400e00010a4031500310070f0400600a100000c2c0400d400e12030301e19190841d81c00c26100e0094240b07922450b03041841c2d220300c1d905101100400d0400c11210343c2003c0000c0d21541c18100d0b40006000b4003016800c02003650098038103a803080146c000b07640403810880b03540c500c00403500a400005040002032801400d02c2100d0085001d410a5640e4101d400612552418508007400c02400c00013180009600c0350380604864000c251078800554a0b9901401c0c0443c60507404a46e201c0d1000c000440c54009030101f1b041264400e881c00d0105200003c414010303808209c0704640014850b80014455610520001ea4000d000d060128036110300c1d00030b4582640d02c00c43c403da8040c04006420001c0000f5445c0759124a1500b054900e00c90001d0341c00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 955515683 1250 955514433 955514453
    0x60e0301051b0310180b0405090d05041502070e0c040608070c050c0d06090506070f170f04110a03061b090617010504020c0712050a020909120d11090904061512 70
    0x808024448048001400c0b076006001310700181500319025032610204a40c0c400140c03030007841c000d01850401002c0341c1021000500100c401d8002e480b240e041c40c1c11304d00c4409081d44070b0182c14046100d00320002030800e41101401e4050511825070781d698904011000c0c0035140701030005800c20802d5450b4002050010404040c0c40b2421256401a0387c2c850030510050a00880090150301500003400030598125214001c0745007591200398200b1054a01054204400c527035445811070400c000070700044008101050150009000914058032611150103d50a803400b6a510418440305107a0703042d0400909030080c0100c0c90200744004142c00a20700118041c4503240c0a01d40101e00c4480303c004c188a100c02070102c049046001c890542045544e6a0a8000580c0981e00341e001203200800041403141c06107032458030040c505a10b8484600041c0900741003900e14070018070800d001540c984c24950f01941c020180814200c11122482c00e078605998000c80c2420b0303604000100048401c21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 955516933 1250 955515683 955515721
    0x409060207061b210902180105011d0d0f0f0f12080f04051c02012318060402030706180302040c050a02010e03160f0c03060203191401060c060f140a06060e030105 71
    0x44141300e010314000382034000d407480307190096010000c0c210714283c28488406460488100341d0b40c0100c1d015011809101c2694402800c0c4d41064001444101041c190010000018403d800195801c3c3c965115448003c100800869404020388803c0640c140c0c0100e801740c0000f030401c1e6020722410281d480d00d580701e00011aa0780d0510030011051540d03130007940848080b080ca804112820940c2c0c2245454000084900d507041103640341c0c00c3c60803000b0000321984542d07405401072000b24103005040e100740500f080c40403018001100003000580740d07405241503d81c11600c880348c44941181c1c0282c02d50b003510b07407601180d46c002e11495611511405000030102c0d00b00001c020310461500307100c010418141c2010340101d000005126094108484440a00ea070390031042050180800061030b103841d080c45003038001107a105586001c160760358498968052104d034005421480b81207500410769040310b0707804015680d65000c02109800800d1916000c204900070001481c1406101d00c0ca0740e2204 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 955518183 1250 955516933 955516967
    0x150c0412050a0206030711070f06080c03100b040e0609130308011a040f061e0824031c030518120a20012c160302090703020403020409060207061b 64
    0xc0045014410240031000000350041d000503a24540240c0c00b6000c03214000d101d0080c2c0c0701b980701c00a100c50490f00000d040d034049548102e01c03500d51803038500e4607800c060440420006c0100000400809480080c0000e00f28102e403407400e46069010442080001482006120b001080d19400658440041411340320707026242d1400908801d00080c40d80500d410801011103900ca022a9980d049180c8010030600701c940e240840c103840f00200d0702a030042d50003a09806070350b9030800e405400d4039050010000d000d01220024100445003201491280c4855800300303665109000702c00c0a10301e4000501c1c1521802003582414016207800f840c4a035100c500100040100711031006401466200e55124060000380010b2180803500100c56112540541003c00c0d004c451241e07001010400043c1c0a00903242d0481442c81d58003400382c0c80c00020284410942d0801012005a4440c4112446103008090040e205c218a2a004d81100c1c554105410031000141c07400c00e0450340000c1d1600c6a0040c8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 955519433 1250 955518183 955518209
    0x90603230619090b041407080f0d2a0f0303112104052a1009060804140c0301020f04180b0d1103010b0a0603021801140d05091e0d02150c04 61
    0x90200c02c0000c051aa03801813401d1002400e00050190350301c1c1c0b8060000500d0160f901c038076650405035640b807107843d5a000668200903055980180141100c0001c58812407506003800c2031500c0c180720300340503480d049900054403520a0281980742c070880406400d110101803420b4441101c5280d04c0341800921403111440708002810820180050740041d0134030700342c44158085c3c002e080301d04c6221701d441c0d10b070080341c072640b00050385031107000c0500450309540c60b0040c450b282e54944041040c288601c05525100307050003030b8021f0b03e00740300400d900c4040100454840d41046440002202e080070800109401c1182d600d845694264440c200280d2041c0e404260107060f9010030701400140002c5a030010046070001400c607010340081c50200304010b800c50603007080c2001941c3c10b4200d00701c2c07207581c10300522203500e01110070b038040b58000c1c3c698011103485024040401c20403074a040050790303451308280c8148010f1501004800b00d0b070441c40f410f051580c41d00d042c010529000d02d11420303a1031000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 955520683 1250 955519433 955519471
    0x4020901140f070807240504031403040c170c03010b18180120090f01020a03050d0c020708102405090a0f02091e01090b090303030705031b040906032306 67
    0xb81c02c0031505480c0c0d200d2000307511050b450070720b021030000410070081c20801c440d40050344a28144149803003030364103484500003171150400003200b54100030301c1280c2c100c61408001c40c0e4404801c2c0303d545108203000080c450220f1800505082d9281030300c0301c1d8062050345020800380b000311040c280c0d10503a01d00d444c24002c03010402541c090401c0e00324400074818002400803040c8404401403140541c2520074240d006c41a400481e6604c125101c06030020307505101490056000f50000c3c40c08098610450310082d403101c40c2c25041505038050000380715611604002d020a58110070315681c0c15444070b00070450301e04400301707a820000918105a081d034442e04240c160941d41e06441c0c03150030141040032000c441134034007090341c400c410856000c0b44c0e0190000070a003c6d40b00c116010000c0150103941035480d00b500544031500041c0c1541e803d411700203c0742440c1003d01000c0c0c0000d04611a01107059031450400501282e02c001103030030301060008050300340368400242d8075004881c006000c440181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 955521933 1250 955520683 955520707
    0x2070b0a0302070f1a1503211804150801151505090105070816140f15040c030b090114060d021008100b0c1f020a0207060e0d0b0a0f0b0402090114 64
    0x4545008003428803852004403000d45d000d00136072041454070905003a00868501301560741c0800c0a03034000c03140d0b030000c1401e880c50030744c0302070446c2c108818a050112107c140c0010150703142481c2c6030758080c40301601048060400d01409081d15040001c1101c0d4a04007240200e2a0940d10b1140c018000c001a2101b4140d22442c2140c080359000610980c90300c0b50b6034005043d12181c41000c2e00c500071014100d070718140001c240140d6085000005103d50324036045181034a800080080da81544011400030108030303214600e034031400d090f000018050120300b03070b001407504025012900807607402c402d500c01a240c00c4402440382c0f095081c1a0340c29900c1407481140400c80c0d40016000d002c001c143c200b800040051442881407410140c24408160000014124020005000b00582c000075040084c1c41c0660503244404401074a001d848100c20340780c120020006440d500e101558920708112200c20f06d100b40389404804031000d41c6000380c1d0100007402c07060079955940500c000040e0400d20383d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 955523183 1250 955521933 955521953
    0x52a03040906121103120703030e0a020a0611100504150504060f021809090127140115050108100302010801150e0d0c03031218030806010203090414061002070b0a030207 74
    0x564510902c611521059198512220120700700c440381030b001c0f0020598503021070031103120740c404070b004e60400c1181e0720110007600440c050008d49000e414050340150319002a80c0c00500059118482074070b1806030030500e0600d0460b103100c00b4138900ba09000c00181842084e00c0030705180c1501107510345680c18400000e100050302d26100c140700280c6010310841ca400504d1941004613000344036995600195401d0303c0a10101c040b4901050410980110141e0f4283d003085001d80b07102c180c0340010419075400c48041123225691000c10384000c00081da03001c0d43c9507500c0501c00301a0400d440c590740c0082e18041307040c06078114030f1040c07001044189109074104100640009d101480419860608402c2030b00306020540004407000801d210501860207844034210500c0700d440e448010b1510100c0c1e01c008050105070440c0410001c400c0d5594030741c05242e035034010060304c01c10701d03090040404c0388c4030101e81140030664000d007204005000c98038065070110070040c00d015135280310300d14100c5180c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 955524433 1250 955523183 955523189
    0xf030405100c020f0706171f030602030c0301051509100f0c02211507050a03090602210604060602191e080d0c02060c090d0f11030307110907052a0304 66
    0x324039151001d1240c50303002801c00e01320100c81d01a984116200c0074101c807180c4041e4003841c0581030f1000402c0400c000090541d404c800c0000120141c02c0d104d68801c01070b0307071095030786511140c40170005005500c0e103000c440307941001c1084418034014071440411110358400113108244a424001c400c0b115000328030030000e08e07a0091403040003402c030001040c0c0302103a448442429228079116400c0c2035210241241c040c0d941c986419040c043c0b01d20086002d80740c1480c0840f5203503001e00c208001c03504003600c5200c0200c000c881c040000d00d4094180421a103555002c1e500315404406501106145400780806003900411030103c402c18480c2550854001030b5002041840c00041d0f40c40c0070441c50340012a1000954242e440d039031030305204040305015034034045d5404007540e101c00b4005400f403110659035a200e03002d0001c9030f4240d000000d0464004601c151141e101c0d035210300c0500d1511581300c41e4450b0f218208a0b0801500e001074450781c02441115440541380005103c8080c43d04100303035001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 955525683 1250 955524433 955524463
    0x61205012106180311060a090302070e07020313060e03120307050d1a120a060501120309060509130e0304050f15090904150c110c010305041203021b0102070b0105090901110f030405 79
    0x2660385286401010000e40f405c01710b1050064a010802103000e500941c100c0b0307901503008040c00c40c20801100c07058100a021101948010481028035840b012034010042515895100c02429034500b8117080424124041c40c0c200300070020040526002070503202c0d4880341100010301e1000d01c001d0780040144030700721142e0004000d0600c0ca011040001d0a8034010721690302071045998030b180001817080f120707200801180000381d003407020394030420280070076642c0101011143d003042051001256051549849176410003c2e00b80420b0400b0392000c04200b00a0340c4003180081c0591b0410b682d8002c1405007481144484089000e002190a2528000c03c0b90700382000120fa50b4807000d002e00922314951070700c030301810280302800d40c007a1150324401e5800501e04442c00c000000c0881c000d5000c0d0041d040c4026110f0480f03d40300c03900344042c1100c80d22950082140b035041c0400c1150700c49000b04608190303810700340403d410f1100c0b034054854200215045a0316510b651900c1800c016016000d000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 955526933 1250 955525683 955525721
    0x1141206040b01030c090605030d0309050c0d030906092c041b08010903030c050c1020030f06150c0c0609060904020d2403030212091503010e01061205012106 69
    0x4280040040c81c18102c92040000d0102241c0e01c1d40000700741c884034891181e25070001c3d2b1119040300c2c060340080402074030983c16078891004c41c0300051480c69129000758002010110140125600071a8a80181118259403000d1744003207014180680c07881e1003034a4848031082c3c003290410691407010504a607101d4262240c0a0b250b40342c00d070080c00f55107030550000b400d03c1e00c0940954001c500300d922190080010300710441490081202518034103040480c80328401c4007800b20240748401450240042c10030340b054504040042007a00b4020310790070400c0d00300400c86e9407521400029940b5001c50241c0d0745c107442d40741803c0010000e0040314000307a0450300009980c0e0b03030546140d0201d0034605075541da0030421041c002c0880981e000303d002c003d003d40d101c000d0080c0040d020341c0103001444c400412a12a82d1a451110091600203074403e1680a142d00e00602009405c03071041e00442001400803c0207625011101201401c0b000c2c8120241c032043c100da409011aa81004020000c000c1c9004 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 955528183 1250 955526933 955526941
    0x90117120f040803042c131101090812030402030f0c0303071101051c050406200901080a090807030f021203041e0c03020a0b0901031a030319030603021f0201050a0605010801141206 79
    0x1a510f12848048000c0c10000319490422506d4a01280592030011034040c9a06440e80c641072422090344003d4103011100390001000348040140c0c89210310103440c919101c2c20641b0501d4904103c0510000084d0003440c5002c18584001041d100b1040e0800b200000c506840c400581d1140719103400001500e13110101242042416080140034074030401c3d0800c50149201040021040d0202c3d0742d59015104000c0e004166110341041a00305074008800108407031569200c0c1c9d1140e2000e68200e0110b0030401180708542d405109070340e00c00900b900c110303195143c1a41c52842d03010300070341d0704000180e4150116080c05550790780a0050366016151a048580703072212801c00c0c0e001885c2040c000f80c186858550b07800603807a0f2010340580042c5c002d60401e014030000c40110201040c070340c000c0590f103401c00005a07481c54182640c030180f4120340100a1081c401c0242036441c02401c4188040c1006010072160740d00407011811188540c0743c1c40d00d40183c2c00c0001d2071050004007291024440c26040c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 955529433 1250 955528183 955528199
    0x1120e160303020f0703081c0209180f280c0c05151506160f0f2f060a020d0503060a030537110f04020405040e010506090117120f04080304 61
    0x140c10340707000380c00711811250f0080e801580e64106000080c91030b0000e001d400424000032000600e400034200c409403d0601110124681d0102002c0340e442030b000341d07814006110592100160000c0140080800f840c1d42050010314454021501a140326511951100c08074400c0103018045c0d0303401804d90300600304c5045c10004408040c0c070359138050040c405c3c000e02c151810300119100c140c0c1032050001c4444480c2c68000038101c030b00200f034500b1b0071508461000540707030920596254410030300801c407500e10381d0000106024070000d824001c020408c000c00d0f0164002400447d80c50842c54980d6407a030b01c1c08081200c002c45076000038941c0c031806514880d03600da521038043d00d4036aa0311030300c400581485c040e00c1c8560000c610191070b01070b440180c2122410905504501c002000c0c0c000b40c0b03456502c60202e8112210004500000d0355500248a1545440381ca1039004221a843d440042e49a007103405496411800700d0740d142c8580010900c6c400060b01c0d060310010014001566200d985e0f400f60 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 955530683 1250 955529433 955529473
    0xf090f120d02010c09031a070c0210030204060909020405033d0b030c040516030f02040e01091415030c280f0e1b0f090102011b0908011104060e01120e 66
    0x765400341d400c01030700300c0c0c21a1180304181c04680d0002042c0c1417a403c070341d0718604022000b07040c510420a080402e075015031240d40c824810040d49640041c1d03a240346c4200109000002d81010044a0040000b00025580014804443c924442448494680c0c02c00001c1100d01e0031107100c41d6180c0c40e4840b5280b00c00f80c950203041100e030142d06880c1540004000c100858404845d891030000c0c3d0b41030300c4501c441c8aa488440300d0009900010b02c0e098550604400420091380001941a290417690010040170002c07107405c0b1800b42c030030004010950000a03100c00001015500070400501034000c006030070482c0e952003d80450310754041c151034800c080000034060049034040c0b502c482c08134408041702c01c100c0749405210086582000800312581d101075214080030360442d0b4850b800490684440074a81c0d948041070744408940518000302c0c1e41c01d541841c811102e540030140420045540c05c00420b00c5c030000f00f407030410712254031a40100020241c603682240544540341401400c4410b10007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 955531933 1250 955530683 955530703
    0x90102150a0f050604020748290f0d15080309011d0d0f061e060906050f09010504020c0a060504200d0210111509011b050406050f090f12 60
    0x240503c1503550b10424082a407088440003449480095482c148a100740c11b400e0686803803a04032050b82c0280c80c0400d4401ea00704041e03001e617980e00120304100e03521121a00411110441c0b81034180c181e40a40041914012004424075207440044c0c0c000c01c0b0343c4240d120030504a01501000040c503264107501d0b60385d801c0300e030300d941c045440039a0030b00c040c2c00c025501545440009210844c1c3c4281d035500c8002c0c0812079081294040d8a51007141032181601120113140710007101d0000d4000c0c600301034001079411035408a401400f822807480300c141c407840c01030380c150f0350705490151b41d68040300202d03803610800103805803c0070301c2c180030320041002e481900510b5075900018003c0300c5002000b00000c11a0049000798801d0340306044504e09070082c18415031010b11481500c428a5116151180420080301d158103181d5540c115200f241103480d4415414006600d0480d08040c203040c00607050b0310540401228980010403a5909582c4d145400c01c3d03800c2010301131000d184111001903542c2c0032140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 955533183 1250 955531933 955531961
    0x90102070b04080f01290d060b03010203091b041103011202010207181a100c1b1e08100e07120203240f07020f0a1103150f04120c030f0302090102150a 66
    0x3e07010820500f10280103501480c6c00c0d988000d40c548064100f002016060a00b250841c0d00d4640030784495a003072024500c201e06020240c4013101c43e1012108030b051007005098402d0b4070349403070f84940c0303000b28042e40c3c1500c00c43c50300c044200005000503850204282d228800e80c0103c02d5159004186603000200590b540c140d901000c1c900301820410007402c090b0000000611081190700880c2241c4441100d4801c002040e1100a4441c900804038542e83e0366107402e510703681e04040103c0d44081107014510f100c00340d002c0080394000700980303444032480d101d6003007889426140341065580522410340702611400203800071079140b13100c1c100e6004007111682030000341000040d6000b40041203144088031171078094001c4203056500d040d001c0b00ca042c6600d8043c415540700c2c20070380301504000c900910180f14280200d10701881c26500303135210f01171954108843c1d4106480001c2d00308240140151a906002d41c407001c082004074501400703e0142c031100386c94030f400c3c05098411544101c0002c22070b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 955534433 1250 955533183 955533191
    0x9021513092003040807030c120201140c030919140615040b04090b07030e03041502151f060c050316140c0409020d060e2a100c03090605090102070b04080f01 69
    0x1111855059031120000c00000b5070030400500080c40484c001c2007403500c281400a030140d11502d4101c0300c080000e100c0c0000d030395906c0a40010030b186400751a071001700c4210315032462501501580c0c80b002201c17800d031030320041c5500000070001c451503200803540007102150954074007502d44007100744c6001c0210740203500c0c1c607120010a0400c0d0141d410300c10b03004800442a6150684110b00406203000b0145c0540010703c8041911503d080d200d5590030115401458100c540e40d88401d0184d4025080150000050b01d0f20a40443e0b50b80c0260211740c1641031144030075200e428060306600c1001040d035803a2109100d2a030400c151040543c0c2c0c171410a0702100c4074070700780c1e03000d0204464901030301941c4048007030800030010b000da810002c8800c10101c1602d0318400340402140b0340d15a10800344580800c0c0444100c0141484100c2e4114810709107421418072116403405044809107005240400c8800100350741164020011a030040c07958002c240d0340c0da5920154a500c401d05044194095420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 955535683 1250 955534433 955534451
    0xa1b0c050f12060105191205160b0301031a04030903240f1533120506011b02090403030b131a06030709120606030b04080c070b0309030901030902151309 67
    0x420303544054110700102c010700d40ba0742000d0400c0600c110141840007000203c8001040c0c0c14404120600103900c56801088036180c40d9550500c55550b540242c2800c4d28140010004588600c0c90501600d803903002081050300c6034102110b1003885504041e08100090900b83c0d19044040e90800103201c0740d1100308440080c20f1090001c2e242500700007410b40c41c10440074024070011200b01c1031502c52008007110400d41195115003030700c000c81d1400000c41c1c803a600c01001d5140a0103020352000003464180c440038404e1020705d08000c020600680516010000a020540640c1c0310382c902e039000500019400103407140d0306010300444501825403100ca6814105241003400540f4003030380d480d440710116181014515422041441c8050751550784850002010482191510b4012130203406255580e592084413680390101d158403000c1050410010004401d0b404816502c00704403d10740400c4585c3e0900004070700c0c079010f483e8400501d0f00000c81d445a1000e08000b41c04940c1902800c0c448041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 955536933 1250 955535683 955535689
    0x804030e03190201200f0706020106050108010510080a0e070b070323040e070e060a0e09071d12030d1d060c210606130f060e040605030706050a1b0c050f 67
    0x20342c900c0a442424100b0300c0c0015070081c0e6605d00324581006400342100391a01445180c0170b21a4400ca40d180c1100d03809101455085c01100b003d0002030070690b0155143c1000305070301c8001c00203140100320080010603d40182c0340c1144881d0008942140e80c03031520b80080c07044a0f80117003021408038848a50200840c00a019401903040e2600c120900b818904040030200e200002d11010810031070010500b49941c60034060141036100c0c0c0c0d0390581c804281c0c1d003403201d07039040a44402c05024071a604038040f1075400c0c584080340d410990340d13150190f40320940d01d851800380142d4542e105003000d48800034810700020414201241408464942d00c820a5483d440d01c201e904c00c03224414151100a6620180c21000360000d101412141c034120076030401c10714504441d0026408650055010400540c0c0300305540003003030301180d0400c10039240500080c0c0d81c900500c1100144140424a03a40b16805080701400c3c600e000c50024641001c58a40040c205e0300c3c6000e40d9102e980e04401c0c03810141 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 955538183 1250 955536933 955536943
    0x305030d1401030b1302180108060103060606030b0310150b0f07060612030503062704060603060c1d121f23070c230d120c050a09060f0309060c0804030e03 68
    0xd420290301c1e101c1781c03030f07502507585450a094003da80041d1845480f400c0c911001440b01d000705a124003070701e415411032a1080941349140d019104250800505c0c0840350790102e4001c400c403014504c00100c0c04007550440c0b00003205940200c3c0c5101000c02d0a84c41c040003840100a1503114003c100542d0391610901144800344d00f0300500019030500000300309040c07100b0104003054005880302c0d11400c0c4031505c1c100c8410111412101240c07550700400400080740100000ca80c01d070305001400ca02001c240e0441100d8000c40144100910503800244400c03e10a0740341c1900403000020742c04142102c0400500080e0601201300003045581e003401c1c0e84020203031401040070741c0e0f40f003140c8981c82d156100344540740d07030300044036001310a1080b00320041000b27284480407041d240c0d004811403452102046404256102c4c09200303040020010160344045c0745010395440781840c15036145441c1e005c5002307001c800c400800031403420b24a61075030760300244458031880c882e941c0d00503041c40c40401d040d164 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 955539433 1250 955538183 955538189
    0xf030406050d0e03040e090a0b0109110d050c040504091a0a0209060d09030909150806010e04020a210609030c020f0f240d0906060614030103030210021b06010305030d1401 75
    0x16400b84040850120a40c1011101c80e20500849003820349901d03c010000405440c0c01e241d0740d2002012800f04100c00c50400c4c01007100400c10400b4151900c1e0200c068031170302c550b2201e01030360360000030540d44451040d940988009001000114814500540c200700003100b40d03441e12941d14001508415107000712646080c0c0900041e04000740a0300d40d0028001c60302c3e040f4280080360102044006451240d205040103d07030004900d28a4184010700300001a084055804080020040542c0b503008041c411548603841d401068008041c00004a55440400800e00c3c0d007080564001d155000b043d48005d030340210b4488003500310b808200074100e10101c50140d0016843e800d03a51802c00c00030a2024000e00d0700034807070314041108899a085800301c80048801580d00c40050103a0b07584a00e40c1d081011369040f04524550654501950340c0380641c5e480b0016980001c1c4c501807904051200f02020f50322501154020350b103901e4055200e42221902441252611001040440009001a040f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 955540683 1250 955539433 955539437
    0x5090a0902012c0a32270a0b040e151b0408031209060415020a0201090605182514130207030201140915060607300f0503090c13061e080f030406 63
    0x10400445500000c2180c011482961000c45170ba0807071b1144101c60015031100a0101c03540303000e840c040110303030b0850f142c0c05030f001e000e0792411003264144000003c100c000c00f00303001407070340b22a590f0031620014587c030308551010740000801c001400c045c0010180c84518032040d00c0c039444c1c2d503e02050b10754a440441d40900f900f4890043e09175081c003113034002d2902c0d4410748000b19501209846010035600f00b0b03200a408034040c61031100d0000014884804d4000c000181e41102c4c40c500700c09956101c001d401886002ea40000b00d608041c0d0700c81440200b0723401821402e40d1100c0550401070700810781103580100001410001a2070050003050b000700c2504020f01e182042e0705c440c03092090503004810105c0714a03034501004155440f40741000c0b0040c0e444075410350391118655100521004400b0320017000e012060090118184021614000113902a640841e100da03c4c124098041c10a0f9070042d00302c90700c1c910703d903170728903103003040300015940d150003154814018a501c450b80d074880e80c0b02e2000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 955541933 1250 955540683 955540739
    0x3010c0e060d240b0d0615143f010b0c070b090a0f290403120807270609080601140105070317070f031505090a0902012c0a 54
    0x19040260f0f00078a40c24010b41e444915211410014005075541604409514000407956001c5804503000d4100504240c01c1181c0107100b4499018214004d8a014102c1c1c4210206d14111008086890744450844200c11075006004900d401c40248048041101c40d1040351350011400003941e41c215407a402c3d041c0010308078546043c80c410b040ba0070180b0340d25071003400102e00007401c543d1102c424024200b28108500e1030382000c2032445141c14940300b41c4454400500c020000f1a094548005820030241000d0401e40e89020303046907690b504080d00140075004c0d258450b540100154001c081d150151120716606440300d030400e5598909229985d01c0724100e0030301034001c0d48242c000c0c1c840d0610034185800070705034568844110380c0c801c50f07650b00001c882c0c0c218000007980c1400341040d0f0b00218480a0340752814540800d001a400400c00240f4a880d00c5100046920400d0042007a0f40c1c001c06041101c124407070000b0f51284130f880200c1c4aa140440086140c00b0380258a07400b110600000c44 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 955543183 1250 955541933 955541947
    0x807020405010f030b072f010615050a0f030b150319060906050a060e0904020f0d05061f0501031a010305072303011e06080f07030608031209012723120903010c0e06 72
    0x44030383ca6003113010f0304095485903800200c52072140152b81d2010010344901d40c46140d4039a0042490410003a00340030503091210000302d540f0f41417076008106010040e001d40d20b40d250540c1d0b400c0861301404110a01e4942500040d500d0a01e600980c1601c000b12780190034565074800c2246c0b42020390100c164050a107030041801403a00b4854241c00890103000346c0f5481502d5259107007456412600200a5811810412000002c0903850030213071800742020882c2d410700307031080c00b0304050381d4103c0b0f8141035691000c42c207824060000803200020240031140d06031721140b03002180307810030302c1000d6400300c0607402d524000d0a0b202040c000d45a55945022807990345004103020300c0c030301802da44141556070601040700305082c1b00401d894400c042c902140b030300b071214001f0b0840380b0f20030340640c0c2a034603941c03e2400300e11541e058607640c0703070403104e0440700c2d5600c60420700603030b44803915038001032041d141109260300340c64001d04111103084000300305020014006542c81d23400d0180b1203030301c21010801c00f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 955544433 1250 955543183 955543247
    0x41e090c02010b012703051c0801060c031d010e1302090901050f060d11190804051213180e0303010612050a0b0a0501031d0f030c0609010e0a02010c0807020405010f030b07 75
    0x29401c00031710340c0a0007064170395035204d503410b0600701c940c02c100808001d2a03540c00c242e044000c00340140041e10340200003202a07240180302c40755030282d0122511030400c00b459507a11440d0009040b03040181b0344010401402c0924000f0f5208619050040c440c040000495241c0642101000c000c09007185d46000c0c41a201c2c18002c3c5900c0c543d1306001402031041000b96220411000c16076802610340000a06190411629251000032400d0040704200180780c042075111182c0c800303c810703406015180c601d0b07520b12040501209186000d00d84004000011860350048220318450b103a07003420009038541d18282c80940b003900e0b6019401188010042040d54800d6000c04003580d02c6000050602400313284150500c00c090f03d416606500225951815420621800750131101000007000001c030704041c001d4640c28512406030600c5402c0c000e003001d10140b9011074901c654010030030092580c5031100c0c40c0c0d041809000541d8503e4107000020940e41c0031300c0342d02d001c0458030020b94111800e01d0f051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 955545683 1250 955544433 955544477
    0x110a0c051003060306020403060218031b190503010c0e1203040b07030f05210a110403050a2604060504140913150e0a0510050601141608041e090c02010b01 68
    0x785001c2590f5200b0000104800d8406000611300c96480075030f8078203071320b4000c169402540400b40d20035000901480280c1d8402d01103141b500300180d40348003103164090203803005420b099014a806508000d290005141e0200400c1101c20b4110392a42c2081244c0c2031032035403800f640c094110088400c1000c030300400d010312900d004040305440c0103850000a07122255001700c4400900d80034480c10403e100c086c8015000307103015410007140b0b050800e8034545503a40d0710720300b04001500f00b01000500c041d5511030750311010a0041340d072100702c1e6202c2d036800c401040c69001c0d106040c1d280001745401e20142c544040c07000d008015240304103141104036181c00c3c45d9040b2029072040300580d2040d038511443d900f444a4580d25004001030818111481040d80c15200d0043c0b14604114bc81c00e204003242083c3c07404d88441d01f40086480c0c2c1001c48514007000c103880b03030340c02c440da8007044225400c541c1d410000300d020603580356050500100380004011fa0984290b101203e003c9030701649084075800740c60341 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 955546933 1250 955545683 955545709
    0x10303080103110609040c020a020f040b0303041202041805070e06060418050c160b010e01091b0f090302120a020a0905190b0604030b07110601080c010f081b0a050a110a0c05 76
    0x2c02485d00c1c0071880002c08452183c091400560007103411036055260080d00b441c1b0705602075606001c2e20540200194882c401c60103400ca0520f002c0d0700207025074456038443d108100c4040105031004401c1c2c00d2055075804184104150b41407040c000480c40c0c1816419281181c2051201061031402c5040030700103018014a0364900540c184101e061440e0b501c0300080c1c8603405081d4100c0c0550409240e02801c1c40141c000c18005414402c7c0c440c081c51005030620400c8000303182250041600e0300e41101d15807400d074006580561200d014401031840030441d070f02034500c00c8502101075503441444c00180d0303108943c0bd070b01c01421541018102a400d400240140c5001031001f40740c10344a541d60345c2e0040301600c0b40c00006200a10503441d12a08100180c0500841d4000b080101114000200512690303c408001c00c28400003207003400102440103081c9080c1d0384d224135221080d940c8020044c0c0c1241c450900000c1904c407609891400c046200101503800698160440d401d110900c030000b84984 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 955548183 1250 955546933 955546939
    0x1409060409170301060e0f0307050108130c030c030b18010b010212090111120304050712020d080d0f0903111608060115050d060807030201080a14060f04021606020a030c020601030308010311 83
    0xb65000641d048450000d6010b40481e03100d11000d4902d1009014001c0c07026112a8061b81c01280700344416a0441070b1640d110184034440c00c40605189007042c000102a0f00062079509569000700c104001c04514600c18800300751303108080c2001140f5603007624145069580542c014160760f0b600020301800400c0c02c54010b04109021100d20f0620a140c00c50243e401e169451001c8188000c010701400303c80c000b04452002c44c440c5039115000502c07850010700000f05214400625060460740a41107160401d0a080c41005494241d04024020001003480003001c0d000e94210404070301c0498908101341c2e000e80000b000961309107003a20702042007220100d402c3c41810f00505031144014011403000e000c24401a1010b1469880007610058014042e100c0180c10b04066001c00c1c1d5a016141c0c0d48102c0c00c0340e01001e03084115003c02c00030303c120a030072012054525821010320415070010007802e24642e90420100c034420b0300498232a0403c0c08001d000407113000040022032013030981a00220001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 955549433 1250 955548183 955548203
    0x160221030408150c0a0203090405040c08030a031a0d03021509071707030201170c0706150b070b010e13030203030703151706090601050103020307200a0221071409060409 74
    0x1891200d00d507400c1588403070081e9210303818403650000380b1001240c101000e54001c90920901020181d206d00030200580d025647c0c800c000b0381449a044031381801000b40b403041e241d5516030f650300100540f0800204a1b003031304001d1030444180c2044103542142542603030282801c602401503045032060003401004485c4031301d01012810f0002d0303000d4070104560f9580202030040c41c51001508441c103078641500308074588001c2103100829003049440c1c55a02c40b0700002c595440740030015500c0003a420000c140038002c283c1000b084190311105050b9902400005000c1c2d4500f1591030940b1010034000700182c009101046140303000f41c1020f421f80d1654400d1440050300c1c0c0c14a4855114100481c8080350301ca042800443c036418010240900401e10b015403035481c25020260603107100000748801900000450b0003040e10030303c4030740b92075a401480b03d00710308000ba6104d0f0101d00c003a6103104440c0205800000c3c4904c46030a080c04d08107011304850110f965082c10031004000900054a041800b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 955550683 1250 955549433 955549489
    0x50d020405040606050406021203160f020f0609031b0c060a12140c0304110d050601061206080706111009021f23040f0512070b0913020703090510051602 67
    0x160f0240f080500295170360075840e2840d00c1002450600103616042190a040051000740343e802032054410740002c0c03c01500044403114228641040d0a000f44601c0c0158010310401c0d00012008142204103a4480c04c4c5141400a00700d4880c0d02036240d455018201f00118041e29000b886c042c0081e02d01c1c10300c0000c0c002001089542540700807070f442d040403c000000c020400069004500303413500c0903103000d0522800f0350341c0c1c580d54510601400c3d0a014440007001a0540c040e002071000d403d904094440321556039501500e4100c01700b41e000c4076030240030080620f9030500c3c404c4041c140d070010880f5205c090407804030200c4844210b000300801000800d6841c1e104030070b203400b075002c5074203441c450b07551460300350300454550740c80d0003141c450b480c0e41401d0001040c0000700320382590001c041455a1b45000c1c8005584144191411153b0a00128000c0c0616400c0020601155003c0e81da8131060090903000311400d118003004400f0750185a000c000c0942800c100400b80e07164074440046054072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 955551933 1250 955550683 955550689
    0x90d03150e040c170c011716031e1d120309060106030917071a0a020c0c060c0106030209040b19020c1b19030602190e01090324020d0b0f0f0a06050d020405 68
    0x6444c200c002c5055224240c50419543d1082e2810040d44c1400b80303440490a01c58480002c0365005100718003010f03211400101254070742c5825000342a001b40742004610b0000e803060342a19030107011803603e8000e80741e11221040c04001100d104130264000742a01e80e080c40d40a5000344040c1006481103a0054500c120a07604000100380e01070044884002c3c0c060b1000c10300840010081994500b580140b140724402e1070300181c2921010001c0f20166250149601c005004105560000c0e52101a150a01040c04030441c0443d0140c05a40c1d0101c4042540102600692082c180341c0845a0310801034100d400172007090042d4107200090440d036600c01203503098032204025400584d020742e400201f0a10640003045d55618103030709400e0044417036003d0320000c0c00b40e0a0a100181400340345016064070b0b20301c401d03440c9940c0070066008544034100720301008020310310421850300940f001e40c80741030b9520700110a00c581510003042161940e05001c1d080718203800c20711401c0a03560302400082403940d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 955553183 1250 955551933 955551959
    0x30c06020c011b0216030f110918010605040606051606060806090c04140103031e0203040803030c0c060714180301021b0c01090902130303050c03130e090d03150e040c 73
    0x9110400400c03c100061003100038100c500400c030080d98007400c0d0708140c041d501c01c1280c04030303a01314003152540c1c12242403103044000605121035011485404101843c081c80ca407001c0012800f0380208082074031001408222001c5018500100d0024000711030092644154400c2551040c00e020a01a60721400030345005010348107004a83c0081c0384042c800c0c01c140c480e26490b007074900d440306003552440c0c501401c2c82400b031801d44d0240c58000c114800040c006c00441e4000e143c1c0d517040301d58a1408860700c264641020501c1c1203240140d0001c6443c50344512030010200b030411004501d4946080414440d010a00510075003554092200b001202400103030301090741c1c0d00e01d02900c4440c180740001458101660056101c02e0f1040c45080030000c88280450140c0f03916017003403513540e41c0007402d803407542c0510440800d408101e460041100250080302c240203180500841b6a8100c9460307059054039050703044030722201c0491404014405081c00443d41040c000d0b048180c44c82c1e1101c190041c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 955554433 1250 955553183 955553197
    0x3110c0a09090204150b1e1801050705330603210c0a053406020a020415170c091e060f0d080403030302250809010f050c030a090302090f04050a0f030c0602 68
    0x8440105000c40c01c1d01d15000584840042240c87c075203800002d0300202d40304001c135942581000f801090640030420100901c0003082d8005001240e0000c5100340f00e6003170f18218100b00e04c640c001c14003180c06408e000915060b0072100801440d0b506403c81004c4203903410421080c00c0d98403541c00c1400100381d080c4803110b490010300000ca01d0228410a00746100300800f80c00d0303d2074480d030344001c01240d0b501040b4405411360443c4c0208103204811000c03003100301c0130780058184c1209040a03d84803400003400a150601c10703100540c07140da803250101c031818540303403030190100044000100e141c078008002104030640248200c4401c03400d5203650010350800e400c00c40129500060440560008100d140c00e820040007100c2c0d02da11103a41d8002c1e06014510149046c00a10580032228602400503290303490f101604403034542255070702c0208900c0051000303038058101940818402c41c3d03641e24051155070020002e002da95944ea80352180000101e10640400160030f0407407000580c00e000030981c1c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 955555683 1250 955554433 955554449
    0x31107090e160e06130507090b0c030a02060a1104030803060d0f080a030b03030f0409050901060302031c0801050d0b04020607030203070c15020c01110c1908030406090303110c0a0909020415 83
    0x800500c010300640015582d0300103544640500c3e080001c80d6a602158025a0340743c054017003042c0c0c84038072040e10035412a070000051020003040c9241c0200002014003241c0c0c90a40c2282c055072100440740b0304035107400c2105103190108000a0020031007400c01540c0084001e083c40040400ea80c03603064601c0c0221400311280c40c130001d05248907071743c5400341c842d1440048001d1071811100000200c0c1612580c411407405036203a600180740c4031820f502c100000d54014041d10840408040c24280b001d15811015021460300c000116003802c00d221b0308004142d004442d981c00b03032030395008c109694100600440443c032041240340e000403801c4082d500185011079811140300041d00000c0c0c01c001d280540c0e02e0400c144010b994200700c0001405100e0317010151401001020744081e2510007100c0303078000344064400080d0000721583e216030500b08880c0640d540b0f41031109884185a200c02c644810765510050320b0406204c02c0c1210ba010006c0c16100602c0082c4040c0c45540141d015030031a480000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 955556933 1250 955555683 955555693
    0x9120f07140a14030a060f18080a0f030e0a140a0c031a0106030504030e091506130f061806050d060503150402040e210a26010315020307020307031107090e 68
    0x1402d00151031405007440804151021001c600480e903a82400310019003c26182c3c050601800300e1a44000301c54141d44142403091a041e003000100d5901c00c40c080350010300c1099181d07881c00c1c07080c0b10f41a00d060442d406002030098a807265040b0080304c0c0710040c480e0040c541c880d030008690308520b9008601c01c5030f449a0000b081d40d0b41e544c107540e050380190305060900d410400000d030b0122250040d81000c41c1c4a0020b9120b00d07402400e0050035020158020400050f0a1101c8980401240c121a0041007401410703482c0d00c011940d03003c1040e41e8010b15910001c0502460b4040c00c0603001801d066000082c090381d80341d0003c0d2410300d0300e094400d0405080c4080c041941401d02a0b900840c084400030080b00d10200344074145a001500003440b0800d0103d40720840034440d038082c0300c0c60b0f180b90203008090080b80414001c00314003071000b219000f60f03d8410b1070038541d95000f030307a01c00c900755006141040300d50b8900340e512124400071102c0b83d02503820080b801015074810384981c980100000c003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 955558183 1250 955556933 955556969
    0x61107050a1209140d0302031b0c040b15030a050c0d020d02120109020f07020906034e091306050604260a0c0501050f04090903050325020309120f07 65
    0x60340c02480d0380d0b0503008001243c0e105001101c101c41101d00c19001c213030740d4402d0302c0603203060880c294011720385002035003804e02c0d804a109050005401c4602d4604507820048000c2030300c100513500401c0d00310982880e1040c0001180c01d401c1e54001c42e404504000c83d41c0c600060071a03c042207038480410000c4640d80401d080c4207075082c504506014011201e82149400c451100581460003010320092041a41d400003c440b61003d00614240c481410b0b2541c84103c0440a240c00c00040c1c00c100910008190708900803281c10400c440c9400549258282e19000014003801041c41201c4003041095866600020300c0c0c0e2281002070000b4241c9049107900520000a0000c1502d001800154554001c0035140042049801002d00310f03070017400c0c06551410f41e019100c5c41d5000316403042d0f1b056883c0c4081d1300d0925412500841c8561518085007100031044031094001c407203440340b00001640207100c80615400c040c0021074240e840107080b00c449140142c4200d2401f90b254100d4104401c60702440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 955559433 1250 955558183 955558193
    0xb070f111207060e0f07050d050312091e0a080915070b0c03070207080304050f01081905040302030702012a3905010207051f030f0e032704090804050409061107050a 72
    0x103d003140944c0018140d6100d40c0704805070b403010f49005061007800591502010854200126216800052a10841441e142031817940341d8030125030040c24040c1d0b544d0115902100072465030030303036075100304c40e2420107800c0f009100651142d1412281c09150800800c40460003804400c0d1003509004c190541d05c0c90034140013030030a105a841140b181c0c0c0288002d0041da035558800c01c841010038600b1142d00d50765014001c2c0d41c501c4100e41001802d02d014240403d1603804030060248500030380300c082801d12040786138494001d003a41800007012039401860b0004052a040d01360003d40305003417000410080b02041c800007c030b481c0388030300160004020071955805100131801040111440c2c1d90284c4000440900c0c00f0503030700090109035440d001c500b00c0071455409090f14100d00c10440342c55085007203e80c2580100c0c60507003401d95400080e04646440c03e801020b41141e8000e18883c140f5203400d09005c0985548441160015224000714140c41c412202034054540200d009014107030a078200303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 955560683 1250 955559433 955559441
    0x60d0b0405010c0912020a030b060103060f0e0108061803070f030e0a0e0f0717011203140a030b01030e01050601021b120d050417160b1c0501140406120b070f11120706 73
    0x16045c0c15030b0101003002680d5241e601d20202c0741c0101c002207007a628500101d00914140c1c114484211412902041c1016200c038060b0603514820210785807a203d1444802c0d03040c0b0081300412a40d4410131404001807a07001e82c1010a9120b810450031102c0c0220014803800c01e02c1d00000c0c0040c0c0e858007044030a44011041e030b5000649801c0c03140104c0c240340310a008415050250100c40a00c5c8141d0004162041110000c81d14840902d542c590584c0f2600402030303c08402424000303402c003201c00c0f004280600c6081d004143c140c000340080d541c0904e106109c03030b4006034015800482c581400607480c03014070401074004444c0d40c0d042c0c0d42c0c906003d0f61100c6500041d00c10b004540c800d1359844210341d103008620003900c2e04201042d4445074030300205103030301d031780310b140d40554504010001441c2284000200c680c2e0004403024459503890301c40c184c6000d41d802c0c0002e01200b01010100d03802c240140b40c40742e186401131500788044d070700d24100280781140c8181c000c0400440060713401c00b8800d40d881 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 955561933 1250 955560683 955560689
    0x4150b09040f1a010f09120803071e0918111b060a02070218090a14010c030b1210020c10050c0a030516020604031d0a0f1a040b040905060d0b0405010c09 67
    0x500f0480407900091010031a041c0e0040369042c844c0e402480020300d405103901d103004146c0169401a0382155142540c075a8100340c4d0108041307a01c52104c1501103407440d5030b00404002c10f6071503181281c0b405083c502e40342d896880d00e00c420380c0e440e81c2015024020394010a043c0e40d51060b080c501c14034010840349001001010856401e00c10712000c030050b134604a045003404050400f0007003070b4a0300702e04c00d810160400d03c010105c8007800e516101000c01074100074401c81032a00d04110080000051150210082d00a0308994200d05002d8081054a501501400745e218003121854551201c442c1e04444c010340f1071584c015004507a00072140c1d894000c81c0d900503110402c80d8000d52504001a54501c40640001c1c148180020f54046080c010302d08170040c1e9900a0041101541d9050046c0d8059068000c44110424100801c5102c1c3e0b603680464003180c51a40741d00d49414542480d400081002804090307003d030b80e6040c00c1011560034001a0b001d0f5008600000300d80000310030280c42c2c0d50085e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 955563183 1250 955561933 955561961
    0x12060a060507150c03140a05070809030f090d06150e0118090305090f03030c0a0f261c0b09010923060114070501111b07052d04150b0904 60
    0x2001c4000f500110355803400c642500e801090349026110150040c04513030213890025141e01080005080b00c0b40c0200d8051070075a29101296202d03440810744038411800c0c2003902e01000c10035480c0c2d038104100b07203c1c038040c01020f00141c48111110000003081d19a03002d020081d0744000103000c80c030181841c1c01110302d200c140c1080380044954020388503010b00c86c007642c4030b901500011005a18180116403e922030842a207050281c0d03844e0a004801404509803a54070303001681c0c2c1000350308000c2e451164402d03d0380c25801c124400031101ca1800300c2a445001054445036092059140c402c03230a80608801c020110f501d0285d50207401d16481405416500c059920050018503600805000c0e0345001c0c01c1a003507614620741c00c00d917014069407100b8011607440000e940447c00114580b400743d0b038880c002542c82c00d6907103501704520100a141004c80b0f07481c0401d00000111156400001b000801410110750310051034100c0304100369980c4804100c3d080002c1c9031042d4500341c420700400c82c900f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 955564433 1250 955563183 955563187
    0x29100807030f020603130c270b09011809060f091a01051c1106040305010b210c0621070518030a0f021009080d0201060f120215030705090612060a0605 66
    0x5512800030841c8807442c003a00460000001c100f89007170b4407600312025504410f650540713640d245a41c0c4c5140040314914044c02c5c0c2d007029111101010380c0220305102034000c00785161030b402c041050500300101002654402d585414500c00242c250042c038000c1080714100091020103810f10400c004911001c01d05191010303001403000ba0b440307500d20094589015006046030f1580c0c64866145003003039645641c0204082000010400b054000004144041c0d4906512008030100281c174842c2281c0d0801d00354100300b0000c11207003070410190131400c0e4407040e8940040e0500c2e0b0b030212810810380720a0001040040c50084280100320502d401007415801041c0301c07201c2d61245c0000c1d9000a4000748190001c1000c0a00300d4400c40762400a045040262000c0c202c800201a00800151182c0c10f10b8012044000694100100d02100015000380540481030b0003400103030502d504c0200007500740705062110302d515844007805020301005184403d070080c02d04c80204501c1c81030660100b4208031381 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 955565683 1250 955564433 955564439
    0x11401050a0f0f0201060b16140601080d080a0f05040c051908100903230c06010b07020105030403080a0615050705070902030705160c0314061608061c29100807 70
    0x300070400948100b00303241002e202e0640c07035000c034003505860303025200c91300c40802d01d086404260010802c016200c0e4900201340d00c500c0204d151100000d10450b0302a80080c906614a503009540c003d41c46034074101c0000384848492402c0c070407074001f540c00350f0740d0141d00d800901080c28449003109074064107124030703814a41340040460741c034040210340348040e640741c0000508150203100300c140d4a05404c41000d4449a010003950200e81169070700318460f00c101d02c000500d640d103041c2102d451b03980682d42d091840c1d440c1e0720180d484d0714001e0401e96195a95850000c2d507691601b5990034004c200d655070725034036041810010701d03100b52034000001492041092101954204085840b0071258101c85222680141440e0071a21600d91000d00000010812011040c00118a8500c1156000d00350f1400c41c084c140e080740d8008080b602540c00610b02d03d94451500142d001180c0b0082c402d0503c0c08054218082c00f80110b40c4414001001804220a0018113404c14000001070141c80c0c0082c0b106502e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 955566933 1250 955565683 955565687
    0x22a12032221081609060e01030b0d020402030a0b040e070b0403170c01052502060403091e1703070203190f03110a0c0824090a080a020307120305011401050a 69
    0x1405840a440d10007481d00c4108000c6a012000d0b540c503140d07001c2c1c000302101c00c24081d0124604a40305291031042c07901000782c613030140c07100400750740040e80d54010390b14211700103400400e074481c0071710350100352111740000598841c00150711980300a4000b04070500038206110941c0d6000b195801030b40c002900900c66041c20405440440b90000140003958540c403100045a200c1c05481039400d50822007005212041081c00c0a203100d034503c4554001142400101c0e2954010380300140040c10451080100d4000b180d20045040341110300c0050b5207903205c44010035000c0b500000c00180c0c2001c2403031801e51905105003040801c07000302210001007690b44080d0300d101100c1c40101804920501c0b4101090100000311000707610001001d0580c2d207030380300c542d41c404a41d103001c10820004a101d500340054407090340e0050803c0e00090411090301e03a6a02c0003a040303030908400b14030084c0f00f10310106100e00c0c1c0310000d401d079a4400049030350424120842010850706c1d410305104040140050a43d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 955568183 1250 955566933 955566961
    0x16090c1b02091f120c030b010603140106350f01290d060521070b0703020c0d0201050717030702010c08040b070e03070b0403060515010201140a0c03022a1203 69
    0x42d0740c1c0308480b601482da112481512401901300c00894181c45514100b003007480d055400030340740035000c80c0c10142c2c0e070b41c8001c034280c1d0a011342050b40c9440c00801040080e00030641044030004400800002c80704206100f8000814000418100f80500c004d20066040742d0031500e01411109500d43e01079101c406009240320401ca00c00003ca400018101c0042401580040c010300401089148602c100318220304100311500751140ca40d000301c010015480c0101d5040301c4e00300340d0680180003e5451142082000110100142d0602c00304002040004888640b551384041d0700000454032401c040200030700f1142c00550352020b10444d6814007001c1160007007201ea2000712841e103480c5007140356001c80c1c10241e240e03000148014010030302004022007900040d01c01c110b20300860380d4410b40315004909031303441d240707124407111030000200d9503400141e00248540b80c3c00703003005440c1400c41e0300d4814490f244105003201550304c0c1048000810010f200c0203140407207101001d425420041070001d246 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 955569433 1250 955568183 955568191
    0x5090f090c040e1b040909050d020f120f0415090303020d021207060c030e12090f0319140c0d0609020906040603020907050c190b06120d050d0b0316090c1b0209 70
    0x40c1c00700000942030352004c0e0541e007a00f9528904542c680381e40760f24082c0942070307801007181d05005140c5800021480001c1c019100c910000007455909258080c1d201e040d80002e01c8a54440000c00011907182c41e4400e4940c2403000c02e6446030788013171450038000d0901085c060810110f401080036000302041c0c0310140c0308199040140001c02101e01d02042d4018807041a5400d181d00030380a60001614200015140103402500c16101a036800000c240d1107107500072010314100c180070310340307000703c3c0c0b04c0c1c60040c041882644c2110028801300d00010741c030300300500b41102c4203130712800301e6402c50502d14140c2c2d4022034103881c1884940d0541d4005010128000e192804110300403803240300c561010041c0d03c8401a614603642c109101c58200b1170760130071040352950f000d2208110703155155240045c0f00c0741040119035800b030910b2011798910002c3d200100106505106d00320816419440c040c071004c00828580200056910031508050540540300800003041880e6440c0b0740056181c0100c21944 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 955570683 1250 955569433 955569449
    0x2f040b0405061b0a03091802190f0c08032d060d02060f040e04060f05010b030903030621030a111006050102060406090f0f0503030f060a030f140f0d05090f090c04 71
    0xb5001000b003041d903003201c40b8000010f00e03c030340d1183e40c0c01e0540182040064030f00c411508144601d0940c44034041c1e108101510500c3c2e20390828a1008a02c50401c17000305ca0101d02e03109420425648a0380890740041e13900d00b060001c10500904c01281e00d4038120000402e1006446181c80c0c540700003800015480e0019000383d2002a149603450303201821140640015181c42295003841d0400030010a8200c40280c0d402e40f4240021590103561410b603480750348040020340ca1540c0305810300c03a08840c600700e98114184115a00d1408250510142c071b11031031603948501802e40c2c0309030344030300d0302c10b00d01c20014001d440c045080c0700e90f076804603402e54003907007011011800910380c0c03a280500b91156135001c0c005594050003c3d0404c80080000c6014071000d410141c2d86e510703010104882c1c010700c4d00c0010312140c810341d1543c00091401c20021704040400c0255a954409294448e08020b03102245000280c00003c40303041c1c600c0c0c0544551a81071083d6003047e00c1d450326020440882c81a801500c403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 955571933 1250 955570683 955570687
    0x81e07051b071203020f0f06040803011e090e011a0f011205130f051501091404020d020f040f14010b120f0a0b0d0b07120c0914030a062f040b040506 65
    0x50340740400c104400c014072a148003141030103040d0038001c0d141c0540d2038413800a4003420562074943c981c0005e016000d0350300302404624507441c210042c00d0700e0072519014000c0c40d00c22440000c0082c007511070100c0d00445280046500301050140390340319280804854032032240c001c00d844544c0da00c0340c0500d40455544d040042c203a103920310300e402d18040003080184801030190f00701c4200100480c4003c00c4001e468100740c80f07a62594201c2055811100d900c401800e0864005805890070140440da0a4005085010f51800302c101140c203072082841d03810030070380c3c503020a500225200b0606500411295484a0600c010982040c14012000d070180301013001440108100d022242c1c4105c1c407141300109082401c02c00351420450b00c85003268404040380a00720061184030182c041c801c9648a181d03a6801e03000e007013103160070180106440c1d99401d4481c490003a8000f81d1b05100d9907503a40101c59101c614406950000000c8401c062160a01500288401c00070041c041c000d41e03055070003c58a043d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 955573183 1250 955571933 955571977
    0x60a150c020117090a030f08090a0303090204020909010e16032306030f0a110a090912050f04081501050405060307080604020f15130f0801061404051302030706081e0705 74
    0x354101d001d5150110860841800d0100344c00e80000c0111a05200352070b03c00240c04500c40030348040d0012216404943c1010440307000007440b80d4040104a0300c0240014103052409011400446090f00041c03003000c146024880d0482d4405903100c400c8009103801c0c0000300d545076480c038121394100e03084c20351401d5640100d54580c0c0c082c05490f040d810403000701c44191455003400921050030407040c0f4080c2e500304d44046521180c03030046e424211740002c1c80300000000c02804484507800085229a143c100344804503107802c05100d94480d6091b0741907a40295414281044100c0c1c402409007407007684a040108881c00000c1801c0394010740455a6941c10900701000c9000b4125008a802e400c800c001404001c5100d4003d4010a80d50420810791406842d0140d2500703d441c0b43c003c41e4410800c00503800c40514140e040700350f0102e1923a180e86030580050f800309160440030340181000c240d5240c204144162011109803200032042002c6880342404d00002c0c0042c810760380e2104038040259021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 955574433 1250 955573183 955573187
    0x40b04230d03030515060301050306160908070f08010b01050c060118141f0e150f0303210708060411070f03020a02092e0501051902070302040507080f060a150c0201 72
    0x40c0d4421040a01166006181482c0c0140241001c0f180c00410185152020440d030a0000649040c3c40c406030013404182c6a040c00602001d100c0303400300c01007011102010500c00f070140300c9400140b4000c42828202420001c00c01e080d200c50598181c10403806000d0048000300011700a8110b40400a0025100003581034010103480d502c0da501c5000e0311090107001d00042ca0f21500540a44580c00c0900c4144d2144204107028a09941c5405420b100301d4030008035282c05201c008034054002d013141e1511480b0340b05100c10781310400c15a440218900100300c825500507640c203a000b401158208450003088240fa0440d000d914805442c250b82c6989202c2018001c0101c45000c6030005c160016610308490b19402c2c8641c0360a004042c05841d045c107040200403500100180e0344140c49090400025800c0c400000c0580f42c4488114428201c1c00005600c0d80c0c440c05d40207044035526008280b61015481c0151880500440d002d040005000c10448194003882000103182e4607100064440318001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 955575539 1106 955574433 955574489
    0x82d12011706151c020a060e240f0f27040c0302090a051009030c0b07021e0d1b09020c01050906010608151306180c090b040b04 56
    0x9103064907040001c844866000280d40e2090b0081303400003110035030031b5803042d004544141e00d40441d60400380d84140300305a1006d2107080408140c00841402d1041cac00014101030000718260910082100031500720f584003081c03c42070700c402d140310b4807034900701e40c0342c8a881246000001c2807010700a00940e46100c2c40101060500c0345080e06201810031610301c07690401200040c00300001340900d00040240c00c8007142a070b01d840052050084105480410f5031400101c03506441c981c2c0d4411000d0000180d0044951420841e00a2801e0340a810740d01300e08a45400860084065041544560b100300540d00459070031b640d8070001a6420721094075038002201d81509551003a00b801c0c441c0c010000d05d8000001002642c0741001a110044140256951070705c80d040841c03001d42c014000300c0641303440040c0700e00d001e2070b04001400d14415885808088609000303125503240d0b01a42c = true := by decide +kernel

theorem cover : BRFrame.Cov 955395683 955575539 := by
  have h0 := BRFrame.cov_init 955395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 955395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 955395683 ≤ n) (h2 : n < 955575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
