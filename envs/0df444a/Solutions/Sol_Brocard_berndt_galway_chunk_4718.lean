-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4718
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:30:49.693998+00:00
-- url     : https://prove2.me/submissions/8ed57db0-1c5f-464d-b293-31a467451568

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 848381294 ≤ n < 848561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 848382544 1250 848381294 848381321
    0xf1701050c031918082503050f0c030d090c0f060f02031207020a024f1d0f032a1b03071805090c01020d140d0e0f0a030201 54
    0x40a00c2000c030014400c881d0f024006509404851403110030103802080c100007100c24043c10040d4440c100402d0b00000c2101d04a00004804200c04900341c905103089001c10080119904002c0400c0400c1ea00c00078112038100b500c2528280b1003420502c0054915a2500310340b62980101c06100242148200030054259403822201c03a627289240a9907a1140c002800701b25071548001a40307446c400c124002183d94087c0081071100000624a130103280101000011a8066451010300ea0000b05205542c0b5002400b41c02c0002021140580100102d103101c02d0b918641d200d40001440040100c80c1d03040802800540d44c40c0e11807084603000268404020304c003000c410f42601503a0000045210303c035000004000e820000400010786040856480210750700740d031500200900172540d0149206011820640e00140e8501004a84400354601604040307080424549030040688024091607140c003d00051500801900c06113810150301c0081b185e0784c44955039404140c0d0a0259040d0036481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 848383794 1250 848382544 848382551
    0x7090e10020c0a05061608011806031e0308130201170736091a010e1306120209070807021b010c0f0f060e0102031909050a0f0326010b0306010c02010e09010f1701 71
    0x6c5160080a011040c801c05400200185e51181e581205611a42c0107591003480340410015004900c4100110f00c0c80607808500458005008401075158003609198143d55010513801c07510041900810046c00d484200224050290400d480416038070045c1c0c0c0410b40c0c010102c2c00008801001d440f000d800c615203d50822032218025902640c8039141c2072400d00f0980c800b10a014003140d041c050a00f4544078403414210b001841805003610f801c02c80b4004e40c0e83d004941c0e2640340507200c40005035501d000607400320019206400b00055015182d110500d0b00202a078802d44a050800096030030581fa040704241c04c42d01000100e00c560400899003400943c1185080b00c900b03103020301b40f26050781340aa10b404102040010078000d1a0a01c1c0d801070812a0b60f6205050082141d120300400c1c1440c40b84281400c0514041c3d2071000d030494416040300c514598038240111101c0c104030504074180032207054856159656900c4150203014610f5501c41054982a03140c040c2c849030942d041d607503925 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 848385044 1250 848383794 848383831
    0x706020d05070807030c1b050111010c090501230f030108100b0102030a0e06070b04050102090111010501080703020d1a07180b090906040b0a03050619061707090e10020c0a0506 77
    0x100041642c500c1e94025103015111030240c102510585002c03403004140003001c416107480d041d0b040707041400344d40003a600d00000314100c01115088403160091040481c500c0c20040006600c16140c1e00e0302c070801d40c41200c0400c40301045207030080e0402c40109400b4000400103110300c50042150307507405030300380d0300501c03004180d500040c0d280d00c18899210704010120410001d152140e0701114142ca81c040e8210300d051805d0f0514078000e4011000300c0e4002440740101ca5907122050140c681030340c00c0e1342c001c3c090031407541e0308100a4518400044a00b4901400f51065204038003d034103100380d207107856856144420481e9041c11080e1078002d85040756083c413034a4280d44410150720b41c4000140d400080c0306810000042d8a142c1640c00201140300310410000445a0a0480320100c84441024010103803181080505641503006550095000c584100a140c040360410000444000c1c1543e0403044084150401e980c0015000100390b844031401d44100901040504d9021100c1ca0a100c0e1042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 848386294 1250 848385044 848385047
    0xc0d141806072a1b05040506010503040c0501080a0b06031305061b091306031401021312080d050411030a0803010503070e0c0304060b030705042a1b02120f15090706020d 74
    0x5501a4000f40710482d40690001c400c9100320000100d07642011003001004544075800795030081d24054035001d1818040807601d254010710550b40641e1303001846200540c107080044a00001c0140141050b0b6110580c440c038540fa02c00c02540500c103504180340220304542003070b40c80d2020240058659104418045419246070800e07240fa0300030803a107000ca140c02c0c0d41c4038240907000703e8101030300c000c41c0300c0119011180154010b0441d10301c0a070044180c030791303602c10001050100e018040d0005804022580490b9041c2d40040d504c18441c000e800d44248040010900c1c010038104103ea01100010051085180410a00d00140240b041c0e400217840c14005400c074501016100428503912440c0508840c1e609202d000068078024000308000c503903884c5d5800416580d0001c0c0e150b802c0321608003044040c0301e070314400201c1d0101200000d80180c0c1e50b09001d075602e082c040580c000c0c0070715032581c00c15003818005030245445281580c20141000750b070943c14803686a226000750741c0710038054607080303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 848387544 1250 848386294 848386307
    0x1020d020606101d040509031207020d080a2c010603050111091f1e03020301140d0507181103040614090a11010305040302030c0616030605091e0c0d14180607 69
    0x1c80680c5072108484030511428840c411342d208206500c14148020860120000400b07800103e0b24200c442d0400c0d100e510040e82c50342040128400056020f8001070021600354000b120003e00360399242c7d003c031003201c3c1c41c00800d1201900c1d8100b10794480c502002442000d00881625041160100349420305101c0001d6440d0240c044150b00d03d080314000c0d4844500a010381d1007031400251102c441d11112040080007507009026481c904000202804003c0c1000c950719017000354020020031840b03003400601d200750030700030420018094032034618101c03714131800610b004610428010034085000d480b070280000c4000e01e850840e500211105020518801250304002001e017000103440d101c0d42404c9044ac400c100d060581c0c0e1248070180015415a0400005030074aa0380d020081d141c0c84d8410058120300035100003880c03040540000100c00d076024901900f1850104840e841c0c8440e6000b4041950605500d115a0b40c0d0003c003080040010100d54041d8004010050012442c2030072015100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 848388794 1250 848387544 848387569
    0x7061a0d111810060f0c061a09010608040302070e19060f0617040503031b09031903030507140d020a030b090429091009030201060b0d0203011a21060310050f0601020d020606 76
    0x4000d0050860460345d40546864031255412280a00001310b005d01d11255642d85d901d40d20780140c0003107000003820380c403800340b2a010340e0740740c0e014220541c6460301410810f03030050301d220341142e0f0046014040e043d452050000903c0c0c51044862024641000a41888940741c580303081408030104000000f003001c811070707500081045806d00d000d03107208240003443c052400100d42502c1030009109028401052a12501e0303c82d030b50a11196507900402c480b0407482001e5490070080c04d0080c51007038006500a0920441c4a01d800269a8540c40000c0c040071000e0398251040308000405084c0c2500c0801c0c03940c103070f5401461100d418106241e42540c2d0703c1071582c21002166a40000c001018400e401401c0202a2000550340b80d0116601c1c1c90000c3d4800e1040d51390b00041a01042000c0c2510410350700201440e610189596003801665000c40c20010310781035050143c280d24218403d031501c41d540c020101c0c05100c00082c0703088000645803180d0000c0741400d6511071801c0000d40d69132f49214101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 848390044 1250 848388794 848388797
    0x60e0f04021303150609020703030e010c03150e040812070521040f030320030711070f0510051c110c0607090b0d0c0320030402100804050307061a0d11181006 69
    0x40082c10f404c1c0820082a407a001012000c0c0000b4101d82456410b400036030185400c500204104111050190700b21000042d02e0070240038809000c100310f0f0036201405070300602441d0420329000c40c452010a040c4d40458502000ca41c0c04540b2a00180c014190f550003562030001d804000d040907219a01070744010b0200604068803001e0140d0f0b81c0b03110701480700070840c030344003030f5526810100009418009c00800e500c00340d22410750002050444035015804423800a4140850080703000b0040b14281c0c09812880202041c01074080149260344c41190320300d44030035001580351141c0c0c08078182010070140800041040900c805c1c40303141c0c0c00704200d80308104006000120342ca60110241d0240c038007610440101c00c0000e01d01d6488294920043d0310032442110489248001280251045042603401822075131040c0216000540c0c2940f1a00c441e81c4214501c48641142d0400038000000c1c50b032044600c04c20520040001c0e040c41c1030b005008604c255442e800707918001c00342e0314074840310744120350 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 848391294 1250 848390044 848390063
    0x60609120f12050405150f040302010c030203070c0602031225050c07050303071401201801090b030a060f150e09101706070813051e0c0406060e0f04021303 68
    0x20420706020760921154004440d0302d20090300540508240c0003441110300651205041540e460403140407901c64a0324104010704150951700116803900c10039130210f0035884108101e101184140180b500100030b41d60055955410038800c11100b040050001600c110072258140f040891028001141c0c039898980142c990a020307a5407403400c40076a014503090b000005140007407081c8043c02807105041705000340642400c0404555107940540015122100b0510000800174030000c80b014200764149032016925440b16000f43c1c055005403166a0025500e07082004602c40b040030f0700d4010b003030003620503200030001d403405042c00e40c402d6000c42c0314450180000381454440c10310000945244070366021900310380c02c241c55942c201030f60141c003c10000c0000842c00c50800300035a081581c410040c003c0b070300898009550707040103044039030540d0148030a194400c0d00c8510500004010030b54034022150004018007903800240d48409004070b00421489005038010f11070001200e52103038030030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 848392544 1250 848391294 848391329
    0x7052b110709020c0105271b0f04050a050601030c080c041206021603021e01050411060a020a0b0c13080a240b030111210f1605120f0910060609 63
    0x160030a0400d8010b880154400f10300032a10110551103d803041801805410300d01c42e0316501813500c41e14a0100c20a80e5002d00d091000e92100340b2242624a000640100c10011142002500b9241c007100c0c1d0b02e010301da0b100100725281d1b070716004580c0c0042181c280760b45541800c0304100c000f0311490182042d5588a420304e803007004016812542844c0486058407038401d003604d402915802e00150b605846408140c00361410101846503500071603219903142d5003910500207010154000c075440b8001d43c000c0983c3c00340816603103480c19105064002c040f81e5201e4140c40d5640f111299a009242e43d9844281400000f6208800e803074039241500341c428000039280d080500140c81c0c4481039036055401d290f6040340301e10381203000c4c2040312101d90302840040b480390f0101c02a0f0310300f00c0780704550110000100b10b41a07003083d04480001500e1400d186000360a01c140e60001c0d0068402c1d01e0f0590040c000c03c00ca00c0021710617020740261090742840458607110b0010300b09140e41c001d01d0700001026120 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 848393794 1250 848392544 848392577
    0xa1422050c030d090e0f010f05041d1608160b070303091e0302100b01030519050606071e0b0121060b06190807022e0c0c150207052b 58
    0x40030741980010110b600040300a00e0051014110f8880c00d0070b201c40840106440d00429220326050302c0c00c4041251000f440c003c00c12001d40075130903002c9025100b9803000c0a003c1c0051180b01510744160040c04062450031070200d242902e5500d00c440f4482d00e42d88180124441e40b005c880e1000d0305840c002c00d42c8001e41c2850003415140020740b101d03c00e00710f40404c0800d038020039103840140a64000f008008554401501030303403801c80744066040003800c000440e100c00341d400701e900303d0000b0b041142401187e59414107000c0d00c4610149190048003c50000c00000405103400b510010011a0480c600040e84140c0ac80c0c0d1034000900590720360480502c6621030300c2c19150301d000d031544803815106401e00041c1001c0760503070310030380180202c40719600505044144400d0700b0710b0003200c1542d408002c40314000180321100c01c034410801460189070114581040215401940102c016a600d0092518900e01118418100c40e10a4000c4400c60440706201d0064160012030030080700c1445803000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 848395044 1250 848393794 848393803
    0xa0b0c1c0614030a0b010306110c0d0215071718122101060302070f140c130e1b030a060b0307050604180c0c1e0f0804060e120703050309060d020c06040b0a142205 71
    0x161030480cbc8a55000458596400561088104001c0c0d48055250700c0d071070412610056149030044003002c1c5040802c48114914030341c05078510286064480d20700700d40400b00390303a5100c500300410020910a48a006022540300240142070f541411843c00c1c0031030355075000000c484c14010b444440b0029010000304000e01020301c00e08002480695240c0c840e07807421000b4200042201400e204006001000c4103544000f0700c0300c403c00a00401c210440c5035a11400b07080c00c440039030b8050003100e000141d952680c4000d0000740c01201107142d0642c0e00d80d011601207406d43d4005200b0410440c0c0b05002040491400ba90319000741400130ac44041242001c003c11152544000d05007800010300043e0540d00011120b0500c0c0c080747c0c2c88cc544000c1c1e2a09a54460803400058080d4004004d0849103150200c001c00c20b41c09944c20141c00d04403040d05007410b00c842181c080d03503c0140c02c81000301074880c5100b004e0b160440b4034120030450505403070250a81d050b0f41885081c00300d0982400d81030110410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 848396294 1250 848395044 848395057
    0x261f05060a030603050c100518010c05030a020d0807020604031704020409140c040606050c100903090305010501030813050303120106030c090806090304080f0a03020a0b0c1c0614030a0b01030611 85
    0x20451907680c120554020010400381c0b00544140c05400d246910030305d050040141d80c08165076406051004401ca090141a80d09101d50705200d185440040080c030140b000c0c0c0082c804503009000c208051b6200a80a0780004000ba000c5410601c100300000e50401400d810322f440d501705a2506540d03504c0810000c00030b83c5030142013040d201c581c05501480c00030303002c900d8007401d40d0b0030302070300d40d4589054400f40950020101360741c105000252100b00143e21281038103003e840c0c00480d050352034035000d086030b03000c3e00103466144000501c84407141b21a640507000b4142178001b03521340620040900c0e00042c040c02020100b40e101d004018040b4450504e02000e8000740040d2505810841d031443d07940d910034802e0b545a03005103903c0d002140c07030204a0b810b0154060b0050403548181ea43d6401d45050000d00ca204c102000388209211030005000c00360103903140754000543c403820003c0e01c601c99041d10700200e01c29885407508800040c0109562811a503002c500421080f0f00b41d45101241e00a15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 848397544 1250 848396294 848396299
    0x60e100b03220c06110706090504020c011404030306030303060f061211041703030910110403060209301c090603050903090d0804090f091703090f120a261f05 69
    0x54406009001018503a42d0131a0242e8580b4401c002d11100160307100c1705203100d41c10200e501c280c001c000a0800b43c00410303c1141c0710000040e145111448886080c205407030079130000b617a0b40000d1041542611130000540285107000c82c000d894000c00410013154a04284c1d0059250b483c00c200103a418001d42c4c028018111900400461082031a6a41d40040340c000b80c80d4425009604205c807841d116241a00107c4403625142c181162241d80281d03101c408000e4020180804044000160110420f0904000400c001034040100d4802d40707030150200e40404010160b00e20184816004441c1404480c407034100403e082d03a40030361050850003105103154104840b01c400d03c08002c0c40100170b000343c80c8080000c0211142c4803403501c4c02ca6002d90300c010003c007d103464246403040107102030355220a02c4801c0f1641000010501410204c5060014a82d010081100801a0b4100750310301c81c8855500304050140311503200c4003944813005090341d01c0200f01c2078440426900c0180073b040c01b50401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 848398794 1250 848397544 848397601
    0x6060703260901020a030f061214070b1209010b01141815030408040e0106110303010303080c1306030615030209150a0207030816031e08010b0f0715020c01060e100b03 73
    0x2e1030810b4041c1d4821480040007a24103191342440c2909882428255039200e043c3d080e0300c1c0c00643e260b8144030011a0159120320a81100080342da42420003001c80841c012401140d9007000000da43c00c1d0b98410302558107002e1001d41042e10410a4030960315280d580190120382400c0e00700105400340280c0340c2c10004c4240c0081000207014500004000b2158000c1040000d40c1c5c3e074040c1140c0c0d0440e4070940201c950000c000400110744140880c54002d68502801c03454608400d40140410342e16a0220000c40e4690001300044945004075010b240000e0505610f0404aa8002042044d41d48203900756040081243d14101d8420001107010b1a80400160382e5260140910080400009001c400095110201c912690006d40c03030b110313005010303440e4a0007c0e401c12011040c00d410407070080c02c80c2c00040c040c13800400c40300124080d41541018005aa49031a160f84c6425200c513600b0880e0241130090500a801711041500412502c1c035801e0aa00c0b034a91200380e82081c801102480c00303201c003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 848400044 1250 848398794 848398801
    0x4110112020c280302070e100503030d050f011208040e07030b0a420f02240f0f0603060f0406020d0509030a03140621010902030327090606070326 64
    0x41c005803114038000f000911403481007406040a216181d100c80c0100182c1010108124980002650303d8101c000f0410305200eaa440d0000f20b0328540103044040100e585900901c1a51034100d00c40a0142c14a64000c14071b41080d500c40900605c1588910328051001000080e0503910aa00441c02410010f041e459101ea84a81c980008015420401c00e021450b510103110100b540550311604071484003d08001c402c01c0e0010388041449040f01030941c01480c40f880b144140f92100818100d45500c80302c14241492030b040081d880004241640d911a28001c0c89a00d6a0010b84c2e44d034085000e0f01c42c88010364451403c00040c0c000c0308030f044c860b541440103210700400d021024011700200d0f580c00b00304c1a01e039004c510005c640140c0e0380ba608480c02941c0703004a4485010950300c41c3c00c0d040300200d6501d0865020918550100340d207800f01241264001c500341280c042c00c1c035600030003151560180c4c00d040700010303140e00c5550b0006050065a1341d44140da400e400d1007205202c00c082054802514 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 848401294 1250 848400044 848400067
    0xc010f021201320f130c110f07030b01180f09080408060f15190b0414030d030207050d030203150d06020318070b0d0e1f0f1a090411011202 61
    0x203010b00c18416008010312040d801e0021a46195104954801031045280c80f0134007505280607144d9035082810030f030110795000c0e6030b0b00481c0c0303d40d0700c00c0c2d5401840c204000310309400c02181160030f43d61a0403581c01000841c00700712406046d00c81404008441c2e00200e082e00f002407900d01100c50005040000403030a10000c10060401c4a03104000c0e50700d00e40c1c0345986110f8107181116051a882007540710f409603418040780085110350800f2000889545503c060700003508140e0003052902151076211846060503c403500b8044c81a0400713506140003651440d484202c078000440030540d020002603007415940900564020024103904246200d604000c0043d51044410025034510741240c540080c80000e0500704641022040070700b411a0303040100054458018900d0f900d115505041c00200c11706456880d80548031000040c60125282d810401d0310f83c4601102401d80c400f0b43c0c1d45010340c80340c100700c950003980a2410101ca689001c010f0701d03038154000500d16801e101007180c13003e20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 848402544 1250 848401294 848401327
    0x3061406010914180604020f030406091205070c061809020c070f050a03030c140102040806070804050607030614101119110f180901093e030a02060c010f02 68
    0x4003000c0e42c54001c002d0b00c0d40b100b15450301030308180d29008040034012551001c0303035290300c0e90001d0000388007615000d28903002c0751087d0401e65003075902d00e41d20f20440041042488030111889428140340c2d04108603612480380c1c02c842031140c101484046c8a0340100d65110f2800b06002d0603081c04c2c1103444050a02440ea60f40c00310303015041204140202c04100c501d03018203000122541540c44966906070ba54914182d400401c2d000b1441e503400b80720100b40b03024203020303051160a496481c1c42e00d034600743c01d2003403424101826800515207044028400905880c0980040c12400d940000c03810150307600450342c003c1d0306401e400d51401099080420041e00868110071203001c0d410200e00e41030030350104090000d449a00c240d0041226a1030303106260301072102607100d02c40000010f20707004140c5130384401d070803000c2c070113402004065511224034185141d08090010040100e49440624102003641c0e000c5202c00a40b0507040454004101042500008040b640040c000d545a02c0141c82036080e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 848403794 1250 848402544 848402551
    0x8010320060c0d0e03120f090a120803090d0f0801030828051e030f1b04090207060f1802060a2d0c03080a090305040e130f050c0a0b0715020f04030614 66
    0x140710b054004c0c440d140000d15a80304244048041d07103001c09159908642e54004c4180307d8001d4509900000e021040700300310f100e42800340c80302556a00c1c00d241000d0070710f1010f00e004804e00c00b1a0400049543e48500102c8c1502e034410503040c0d580c5102500076507800103e40d801540c246100ca4040c0710654020082c00f400103c0341d03144070f179130f000e01c40890019001c12101600d412049800003040840410044500105100703426860207031501d0214050340c1c01610203813140d903112807000041c01c42502c240b4202c04142c14107410004541d0740001c980d40f00c0c100180040020781c40d000c03100c1134400300400201d1202c10745001c0034048600c6015010420755001a00451418800109507400c0b9000c0c0501d501d40c1a5622807030503003002000320140b403001e040b440d503203a041c4403000c001a050001c46404c0300d020340c008040c0d00208404201124200c0c0d002041c0111040c04040e00082000040c488019100c0306c0241c0c980105c208210814000c950025220700c1c1024810745400010680ca1b500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 848405044 1250 848403794 848403797
    0x61211120f1605030a150b0604080a0308191e0b012705012d050a1e0c020f03030f0f0a1119051926300a0c08010320060c0d 54
    0x603903540c0e0f034081503160151300001425038400c100300c0004c555a81c1c3d00c883c154540045c072a42c2440e0f200e4000501d8081006000c4011070300010a0001e00904811800b0f143e8041450a10080140109510a801807198001941901d44880c451280e000704031130001c1c114844803020014840c0e13100040380202c1841a0b5010829500c0038030150f80c294020030404010b901a0901e041d600e07203c0c201c800340d100400c00010400009041013104061459082c4181002c1d1754503102c40015004005a003400c40304514420381c01002480700242c01d210648130000c0540451a86594020740260f84050105243d0398031401003000c5009044050442200024018000c0b204e409290780c540c051801650f000140c5403090320010403404242410700b403160418416842411b00c0b00f00079044280e02c5e1892521045500602c204a01c180c40c0810020b901c007880b10001c0c441503000c0c0f10b0182c091041800040c020500034590041c01c8040410144840f00b0054205599180000c918a49030b0b07040b42041c50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 848406294 1250 848405044 848405083
    0x510030f0b0901150c0317091b06160213090602160b06100c0206070302010b04060906140303030403050318031204061b020610091a030d1809061211120f 67
    0x4040e00b01005281d050700c12210040c16580303440a0f0549030000c80000442c200008950000c40224688081d43d004401010003803600040003072281094501207071885020706001d20002215202d120003082c411a01683c082e00500f414211403000b5200294010b4041800006d4040c0241c0b85020010111030180070841603d031034000412081d0307054136003502c0009900036980005032174035400030502e540c41b80c000000c00d000e03030300003080503aa00c550001100e0341d9102d00400c000a62007000e100c01d140110059403079440c1c250340103465408081d040050003182c58a0748a040c0e1010070441d480c00d11000104151841d0619150300580920001c0c00488403944460790040313800010024041c03d4502c070304280707490030041c0f00700092074074405040402402480f0300d00c03192030a101c0c608882146070b9504a01070602c0c0b1290303401002c40e5100240207803903c2001c1120800400600c9240b0350300004200344410420001341d4402c21704000036081d4068105d0001e400c0400103006810142490b5444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 848407544 1250 848406294 848406311
    0x1b0f0105010608242110090c051201020405240705030304081306020105040b06100201153c053006010609120f0210110d020313051c0f0201090510030f 66
    0x8204e0340444c040075500000c0d1011001680084111210030700d101850480c1c4240f54054110703403d5540c0c801e029140800c40348006e00440c2403501d000807400c601c20000b03510300f618000100301560001400f000128001d14406000b2400290464203000d80040440340c40e810582001c51240e440072211a01c1c420303040c2c1c0c0008007a40107001c2ca602ca650800c002c440f4554855080c002c0703803102c4a10002c06c40d580e4070211047d241029036084064104203c411001856607036013420b01e08032011481d2020544c5810059815508400c0c60742a2002a02d4030980c0c036a03698403e5412402d1a540326841c85208240002e5490700001c03400c0c1210718550346c40350850396a4183d80c18055034007202800309003200365490090f060066200d118074041c0c0c644040400c00701007580c0d0504060622020040e0000600d480d8200071151408001d0582200c00410003151100025600c07444984014042c95818441506580c01400034800070b0001030007011000c85008030090050140b101801c0035149031054030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 848408794 1250 848407544 848407591
    0x201021818040312060b07200306090d1103040b190e040513020f03150c0a030c0203130e1503010c0c020316030803010302150705030d060e0a0e031b0f0105010608 71
    0xa2114004081c110011039129510100c9081103818072210701180c940c480005c0d0503048500404019000c0c4600d40030b00c14910202030040c400160500d07201b40c1c801018050301d20f41c08243c04003a107901c4e0524805801c604081103003940102c1d0b00402a5010200300c6030900140e0780011901d40d08940c2c0c4031886c3c0d02d1404200800ca900503a117222505410840400c010300b00000749280100e1700070101d0b6040d490308c149860034144100d507000d0007690b000c07a18400d01c3e50107008a40d08200746001030f50038125001546144062030344181000480040c000c1348044000348403000c0c4002c40580203004c100720808004d8a1040340f032100b28001e20686c10041001c0b070350740750741e0015280d2001d00d9500e56482c0d6001c00000c4010a01d00180d0200c042200354005a400c000401c0c00c01e503d140b011a20a10340141d0100c88000140941740d00390500c10265040c200100450740720079042038414400b41c3c195100c0c1803a20141d4990100700350302c1c0400104046030840c0c2018446c040400d054202e04000180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 848410044 1250 848408794 848408809
    0xb0d030e040c1d040c030e06040321020a050d051e01060503102c040c0f08010b012a1209030b090f06060111070504180b0708150102070806062e02010218 67
    0xc5440c40b031043c24a0040307602d130a800001c0944c3c0340c1d241c0800c070440400c140300d003883d4003a07808501084840d00c3d55452255210040704491900c0542182000c4a070600a0000d221700c1c1000060b4541c1c40c00007801d107a082500030b04034020b040615100c15038481002410307590044d503820700009100c80c00000d01180c005200c00703401021170000c2040c8400045088462840507004692444051602085620a0a10352001449010008618044200d0015005600858081a20290014603546031007a0340708918140c0341e110061000b590000c4000300c41c0c0080d181c00007800c800c0c2c0041402254400000c0c0b20504064800a070341c9070f515a00c0065070943d200120700701d42900003020410061500c0e40c04860700811800000580840b146d0310035880000880d04100070451260920440c60510240c91100000a0004005d21400c0c44001039881500904180c0310300001e031842d004004007002d00c1c140c200b02d81e40c80604038100d0202d001c0d000c3d400690135100103960303285c8040e809240021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 848411294 1250 848410044 848410067
    0x9010c02030706092102010615032c120a02030702100f0c03030c0c1505040c0e0105060414130501080703050d090b0a1101090b0703062603031602010b0d030e040c 71
    0x20001c51500306150f031244003400d0702200a5074550107403664003204010070007401000d40c10f50750000a4032802c06c41c10191155419141ca01014a85400780001a2110902c5c4450141c5a0384c980340400201c98910b16045030310540c2c41c5580c1003c549000c01c15000809849110f03c02c1b03840901266005204407900a0862400c80004140b280c00701d002c02c0c000e501880308246140340c403204001d0180c4840700300d03070311405c1c0c010000390781c0740d0400050001ca041100701510000c40030414652401d40043e103240202d0040072070654400b10000030650f51548280c00170001d1000c18004d941c0c6d1510a25103801c860310040c3c520380502c9007440c911910540c22602581c9109181c1230030005881400c445003203040400ba1590340d82c5200c20008501441c071628441c030b80654000c04d00b40c0c14241d81750a500e81880600c000402454420005035901206a0b0b6111484201e9521480c17581030f0108c0c0034000c18280700750040d000c3c2c0041c0c01031542c0111400b0070305401755000e1100003c00e10341101e4058070b49 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 848412544 1250 848411294 848411297
    0xc090207080307050304110a0609030b0f0606040b0c03131707060201150303030c05090925030615030b2121090a150215092104060905091306020a0e010809010c 70
    0x1000082c0f0032500880141d50054045c444642c0341e101c18070045242d0503401c0d0008000302c2c1d0f1394001042003001003010280d000b041c0039401280d40c18041c02007001c9024a00608009010120b6068520103081081c0c82c0d048480440b1280ac3c01e40d00c106251f68001045181c90807405003480100d400c4c0d005018140010321805c06091940d46140c42c00c83c000d00346c8464200401c0020014648a0354440e51854081c8220015112640446a8140001a440c140d0740c109050906a0070000e4602c0701203803501c41000c0b2304000c41d400c5243c1c00022458400b51a00019202c1040d03e10700c0300c81ca000900a00ca081080e406140d00503410048441c01d0203500c140350b83c85420b5000901c02840b400d128109940780500407107402518a44d019203110b00120341c0c1039950392040e0302001d1a400c041c04042c941d61b01c3c05c07100d0341c5410b0812800070310090950259500502c40c10740810a400165101100116000041151a640040710044c486000c041d2500c0c0056501030100f00640f4041c442d4248100d1503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 848413794 1250 848412544 848412547
    0xc03010921091a0d06030f121b0203030f031f03060519060b1903110a11070e0106080708060a0b07050a0204050a06080307060e160b0c011113140a09020a0c0c09020708 73
    0x40380c06640741e4058004c0c1540c0e5a2110400000580701c502000f0040e8440c24036070a580d442c030b08004089200000c10320160403401c07030039000035850106c125030b0768281080d240c0d540ca43e03810000b520600000d8207000390310b00440c0000810b01c00a907000d07602820211301682c2c4080030b911808000e0316a14029070411071020800c029213610034155202d454151824003082e61401000554105c2d08441d45050220355552003052008405118074005000c1180700c107905035040420042c0542c20007041d0f501444402404500c2c42e03500c541010b80100302c0c00d80321543e0780c0020b18120f515000c5007030041740564144400319200718000d0103000c0c00d40b1003010003103040000c0768543c00090920800300c1303d007500035182c0d00e040c0801241041030280c442d5294160355081d098006900b111401c00e01039882030f2052140001e0001c00004e840203c4040f43e6000303400a40c4080080c2603542e85034018079810b031002030740d60001c03900816030400f450700030301044800c207540d419100c080e8400c01000a254075030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 848415044 1250 848413794 848413829
    0x50a111206030109080c010b0901050603091e03190306091505060f130302190602061e34030b2704030503090a06020a02100506040b210c0301092109 65
    0xe8142030540c0218010008503842a0360384415120381d0003080945240d9459449070a0507081c10109280100b5054031010300c2c41c079040020544500ca00e02d0182d40c902140d80380d81021600070400d40742000440d50481e460f6145009020340204010b1243d031820b103003820201500204542134000031140040c15032460000252002d10382a4889203d500d800c42d0f98a60100150b25040c044000c00c40d81c4a68541115050040c06072400c00020050503041d840080a2030901842440c50380d0003100302043d101800c6d20719150020320301c0d41440d00c1e070365410b0b00d4401e00580543c15008180031079070540c1e084500000c59030822460022888040c030040c26031501040c0042e1240008540c007084801c16a80072130101d81d1100e05980c4034180c00c200592042070030300c2d500c1c0080d04c00c01d904880100c1d410051017202c8404550780080440c21601858075020755542e0740c110074032074032640f148003e008204850a0785002825825101050f00b1161648001071000034010601c00c816034103812240b184508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 848416294 1250 848415044 848415067
    0x503030307020d120609020f030603073003050c060411010917070e130f0f020a09022802241603020a1209080d02070f0b07080112020d0f020a1701050a11 67
    0x1303c044103600c02c641d41d101c400081e50fa95610241c41c00783c40300b0260320b60740c2c207144040528200064000700594000399001c20802c0c1c2903101c812071903284612085903000b8003820701741c8190251844d4a5220301403541000100701000c1c081c20f03940075007600c1d94416180c0b1028440c075502d41541c66148150700104052241005901c101c980c05000c0603075000103030fa440d68420740c128940c0101140d00c1c48484043c1400c500e40b0110304000703070882080c00c50401c5800e03590545607070300c00707282001420403810310410300c14400e2140c1c4540e01036000c4511982e056042c2c0744000013204850f030050590403214035038000d912900840d41300040035550108900c0c03d00c03400310010051903000311002c82c0708001c0ca544001640c0081c1c10301601400451030413800c2400c0c02203003458000c02840030002d03800c006019207078070746102852050f01a600322000d503040f440c1c089030060700402c020b940505203410001c0c22142000c40f00e00085075403402403109484a240220580380701a00c3d0309003000007403010b0380b242d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 848417544 1250 848416294 848416307
    0x2e0e030c010c08040305011d0111090604060507020103060b0c0d1205010503070b0d090b1024020717012a110a0302060c0d020d0912030e06100308070507090c02070e010503030307020d 80
    0x242c3c02444850725183e81d81da00c090843c1d01c8251408050b9280c25003d00000800384907180301000c1900503140b91980c80c1c0001841c0d441240a09820701c00042503072001e591203503000101034440980c010359680000c9404030360701c0002070a0840019040329040c030a008490054504954016000b000a141043c82411032a001001e0180079107941d0311844012070000d944943c011000c07141c010340200d04100d03500c1c68416441b542c0e0340291917000d00c3c3d02140d66001031210101c07506582d24848403040701a107540076000c0361048081c118243d085510040381d01038000310203509140c45240f06a946215103d03151071011780e0240260700414000b070070056011004040139080c04d0b10042c502400b44400c2d100b01d4100381c406452660307550200b07a11090b0148075091468448400408592030b00c00502c01105640e800700600001c40070038071004100081000300c026040262041c8803940f0712950096075194075102d44202910624000901c0341000300459024035400e60290188100c440c00070f4030312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 848418794 1250 848417544 848417567
    0x160605090a050a0b01140301090b0a0b01020c031209010315030305030406020702280e10210c031e06050a09020117181e0c040b1f0207052e0e030c01 65
    0x1c0c040c865204000800a000d400d03070442c40394040e00880c1d4140241c2140890f0a0f0780c0c200e0090785800ca013038010a80183c0800d520804607030000c19000c00610040381441c0100c4100307a098840d0482c0c1c18400c07400311002e402d20100c00eaa040202020b002c91034a40c0c4516880058085001000440e0100c1c5054001b0142e95001906203420081c0811205041542024a0010b001c10501003844108041e40701d440e001804401e00e0381019040c01c4002d10964504a541c2403410085d954041c10400c0e2020114001c54100c1c0001c05490110000e9406501750301c00c003207500d00d15140000384a002d0318410300103029010b80d115105035980040030040340001411300507240045d80490580d40d4800c10211401c1070741100c2503c80c119201c032125150082c9142d80511950924011003e81d40b0b586080b0380000304007000e070103000035101034281d00f0018160451900b042e0104c817000040440384d108180c0c01c1404000020900e800e554040300e240e000c6100d056456003101c4424451507100d0b007d15080e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 848420044 1250 848418794 848418811
    0x3011a0702011b11060f0705120a0f0e031203090706020c1806010c02030a050706020a03021605060a080408040803030411010f031e0f0216060c1b120f0e040606030f0b06160605 77
    0x1070145608005070582c6c03c140520384600b031000030301e00100302d828040341a15040c1494040d060114201c40a02490380d06130039001005644040543ca0380d4007048620050010840305036075900f40360b4041a2204428081c030030140c030840400b1219414440c0c8070101d014009010b42407640c941c00c0c0111200070441d01c081ea0325110300560000402c4040c0185401092581c000b070840d400c140c94040d04003100c5000c0c900080a55103401c120b5610748030101c4089003501d141c940310750369982c84c0c41950307800341d504000e505c0e10001c02003000300b00c0280a000780810098854509204203010124103548100d83c00c820203460040084644c0741c03d54006030480b0142500242c2000303ea104611181c0300d003203030292011038658408843c06504800d100c0180080c42e03414031717250f030001d4540804a110b4a2107080400c0f600f0b1210710500c9100314040b6460140061092280c0340d920100100907000c006840003045290814491407850150708460300710302d0007400300c81c9500c0b40e61a807400a0070000c10000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 848421294 1250 848420044 848420063
    0x161d09090f01050a2903060c0f121f090b0307260307081308060108061504061509080c0102010b0a090c05040b040b0406020615010c2a03050303011a0702011b 69
    0xc1d0400c1c0541c0b485008a00790000e4981000b02a8243c20708001200201042149104603680c3d2030124941b40d0001c1d003122100d546402440d480d014510680071502c0072030b00340c1414081c2c03840035241c941185240040e0b9140c011500c8032400802c40708009040c50741035008500822500304090402c004980403c00b500e02800071441000b400e40e417054a00700e94040001851000314040050f00c5006400c0c0d040041203158101010945d6864014040c2c100482011400b440d00c0d07504d40c2c21090107001c2400b42141089810309000c0c2c64800f007800344a040d40600c00c5006d00f81d510511810100010062540c10301519050154009141c0c44823164204030013004045004400c4d0b0008100030000429910358036841c1c104001d041282c0179109a00c0c003841190411400c2c0e90140f01c030b5142d1600108078407603088400e10b07000040030522034036058074600c5007000401c4c42804030207541213a080e0079840c840654800306145040c03041e0782e802408150840200000e14441d006182c105911861035603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 848422544 1250 848421294 848421313
    0xf090f060201020d1406090a02070203010b0607050a03030605031b060304080903030f04031704030c0905190507030b03120307020a0b0a020d1401150915111014161d0909 74
    0x1810850a29086040542e400103062000ca40d0588528484255036203048100790416100040fa24000503120701e4005801044000956400b980603010090004091907a101c910346051911101f0705542903000c00e01e070401c00641e504010821000408481600d100c8080d0070a0800c1200d030000340042e0307451141030095249548081000f842000c1d031342e10000d80c40b20700e51b181c029401c4004101d0700788004010300003000080c101180c048240c48031105c0200d0340d40e481078183c0b20951448000300944600305400e001442d40c0503071144840c444140d050303d00007540707111503102c288000c0c1c0b85030300181d119200c050085240051003507048116030f1000351a01b00000034240580d00e1010005005800c0380c2d00400c10504400c1001c119071245052403501d892504403800c000008107220b420034440502c0f010702e81d42401b170106810b248854401003083c158107103a5400401c6080724a52043d034958040300c000c0f41e004a2041403010940000c01c459035030300c40706201050300c0c0a80b41910301c1c8650b080b030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 848423794 1250 848422544 848422559
    0x1090212031308030901050307140712081005040501232205011409060d081606050a0903030e060c070f020117090c150a0903170909010905040302150114010f09 70
    0x115128540110015a00c030381c440340d00c02e280100c040e030041046a00403c49440c2698002050742c1d03105049080000f83c2c07003680d50350081c140c4592000141001002c4e00207010464012001c1070091041c00d80d01e0005503110380a1000300e540a0161014009007021007001402a150780059440c1d40500000001c45240710703070202d800420400c0340411519000184490811030000743e0758440215030f00032450034600041000350801c920051b0070f40c0000544024117420440aa941d4a980001c04010b0ba02e000c1c900c0c10001c00c80044110002030514050141c04075000800b0f034000d0022040c02c601d040001d40c0d907150700d009610000c03418001540440c00a003004040b581d8811080940549240c402c490200200811005007030110150103006480741c007940240c03144161303540b14040340940e50f030f01c800c404000d004024086522040c010004500d86143c0c1c2c0005009504ca50200d80c808400e800840050304004d009083c204a01c030310340f00c0d002c0c2d80701d4800b2200340c100740d041451403941c56540c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 848425044 1250 848423794 848423809
    0x609030111040e150925020309060d0209040b090103210909050f0a0608030a090608090f070303020a1b320907090611030a1e030b040603030e011101050105030d0c05010902 75
    0x12040c0480350b10010003042500c12220079058680850758a0b80b1890800044691000a03400c409881401b028507000000d00800496640887c0280070b25212052800c11002a500c0b680425000e1030505d01421020b084c1020400d050f81d500524100c0240050081e2000d40981d041d0210f04000203d2400a03887c031040c4149401403803c104150318130f1820000358003d4074000e50101c20140d204000340650203502904c0b210503078030740d40340680703107600c3e2006e5076480e09001c42c800341283d01810f0400010941c00095103040355109610042c0340340d204c00e196040e8064076110b0300c4030703400100e60300b0000e003c0902daa40c0c615030309240c013061585c842c15001c07500c0c1480456044c1c021600c00340007445519000744d008840600307480300035407804400c090b00500d0351b040301e605580c1e03402c20b5034021605103000c5c0d00601c80c60389010380200240e079580e0138020b150b00c0180c62207a0105100000c01c061240d01030107224181c9402600405a42c19a00f4007100d510200d44010b5545542e217210480c0180d07034421 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 848426294 1250 848425044 848425049
    0x20f0c0f010507054b0c010c020a05030303010618060513060e01051c06050343030f031e02033901060b03041703010f050105070606030b0a0912030b0f060903011104 72
    0x41310074024046201c183c1c010300c41c1401480c11a5200301005e9828060300150590300c1c0c6001313103820358040040b0f00c0403420240881e04119814000400040303142e50740117402c02201d4481d000000c0019607600411345041c07280071400150800f00c10001d0050b1401032550f12800e04040c5086443c2c007034150398800c01e036900302d81300080c0d860715110200128501045180741914554441d09400354001d10290f44451080300c0c80c0d4080c9000080b8861002c0000c02910015500031101c4429a40390345001031401c00007038590118500d00002c0794071407920000540d540c4818101272004055141a040140240c4000312100d0704001c0c0030300754034012007e0142100419061080a407241040d00d0500f48111080d9a14881c1c01410f100402c040e4039a541d01d001210000c1c24a00d0390382d1424201040031300b0440e0800f074180401c030418050b1703904080c2d201e400003034010b003030840d942d501c9140110150f90080320700a50145102e400c03120f4900d070034401081c00d40d000030300000340726060200e00c103d40c0d005076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 848427544 1250 848426294 848426353
    0x4090b01230d111207020a050105070e061c02071703010302180402060318010204150c0b070c0203150402150703080f0612120f070c03150f11030429090d020f0c0f01050705 75
    0x25038201040000901070590001c1030b07402e2880170518240043740c400d024020180003215044071010b821700c24240c1c12500640d4000e412142000114000100d142e8000e20049000d0095400c1c0c1c0b00301400c0c550300c220700583d4001e005a1071900c0700030f400d1516281d08204006195401c000c0015021604200311810a92039110320788c00c1c0c890750400f83c40f0508000c18050900c05500c44081c010390340401d1030007041c4c2e402156402252101d001103402c0340c029002410103031a000403c40c0501d5002803082e1b110340c45010402884e603850a003030100400c4250451a0180c0c010710500042c858603074040c0100c40a02c410440c20f21502e5180c0300821586030b07000f0781d10010b0300040d0340500c40f111b01642c5940c1d82c0c40314090101c1e00d0302c000c0e0132502e1722008101814500d0b14541c20043c0146454000b51101100304410b922420726506074cd86401000044c83c015100b6081c000310b008201003101c04d0b4607000148141c00010350100192041d42c0a00c004840c14090401600c031461111107408200742d911 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 848428794 1250 848427544 848427553
    0x51602041b120e01092118090212070201090203030d0b06070c03060b03100b01050307050a0509210d020c1f0c0501020301090207020a06020c130f020d0204090b01230d11120702 77
    0x1482c1e0701da0885030000b0764007007103034144907178100411040f088002c101405001c1d408803010421000b1608062210011090355040f0b0800180c2501150003500e4018540c89050110392542c01069088030340300b0f071000350140c00a0103061030080c000c0d400100c003054003901c101c0c6003408550355000000002d03041100c80603502c14034100307603003020401c2d045040c3da13181007002000d0042c0000b0f085800b004080b40e0820a0008203440094491819942c003618083c000c00040049100004038407003425009580510074051800000b620019a400c0b00c441c000d410a141e084008104091801050314640103000c0b000b44c4080c001502440158002e1211010050300e421191041141c021943d610100455001c001c0d141c0e059500da500003956000a001b00250100310223074400003070f00402110180091000c2070000e043d00d550b030001d10300000240d0310304031003001c0c01c80c6640d080a0400c0c07402c0100d0205011034160441590700c071703640c0075803c14041400c00310011064186144100e40082c0140c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 848430044 1250 848428794 848428817
    0x25050606030a03020a0b0709080a030c030e01030207082a0f0a030e0603070807030f0b060715110301060f050304020a171f05072a0605010e01031e03051602041b 70
    0x6102180c0c21100071006001d98441d940c40003035480075070f80b00c05000e170880400811001c0e4041c411500089c4060b805880801c2060308025000c1200b8070b0042e80400d0200c81122210340c400e10846030000e0703000c08050b0511450782d0140d00c146440320340824603c140d5440d010f01d0968100320920030010010010700101e465480d00501441c400302900d8000c21052045c03050307490b0001e0345590700c14414980068101d09502808000d01001e0b10a5500310b400003909005101c2902d82e1031412048005080c001c092550012101c2d41c8024400d01000a01c038084184138544107400940c1c100340028005840c0c65210404218000c0c0c2c0e40364001c1c40c590007100041c200d02d1100321400d203c0b180c3c01204000f5440c007840c002c0c0510040c1c0b00ca02412455100c060455540d040100c07040054200b0f00410007980c481d92410079201d800e00055424030503805032004070004000c0d08240742c0e540341d80c4240c20006589000e0f00760b003c284a0899121341c840e00d0682031518400a50119030b281951490503075031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 848431294 1250 848430044 848430053
    0x30204050f160525050c0a0f06030605060f070b191109090907030c0506130305030a0302040611060408070b0603010e011103100509090309090c25020103050901050f04140325 76
    0x1407a02012014401c00b441303001c0d01c003902c401031980d905500c00d54840f201a180d25050f030405031101401c0b036005c648058041191b180f9210701e00c065030b21507102080130382e40702c208000c440e019480c030021039404100b101a0000c0c3c100551160000c0002c01c50b90041070350031064a065911040c0c075144900c1c40031421822030b150440c0c8458210400c0703005480d0081c21500c441e612060301d4084d450086800140003102e03082c400400c040116000001c2d65121480d2247c0200a540680304500014120f0107d40c2003070100492000d0049601464a030710b0f080e01982e56400b0003030010700c0560304d55030f641c0307500d804200c00303000d690b808050502076103549250014604000c0004c035000f00c0d0003048810200140303070800004071951004120790900c0156600c2c9a00341c0c030f52203800c003817029031094000740c1c1e194069078020a240c001d100741c07018001941e8145200e802c1703800440f180c2d1213450140d00402c0c04100014019000500020141c2c0c1c50704810045540d104554000c04a0403984004801814070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 848432544 1250 848431294 848431321
    0x60c080a0b04090c0306021602121b12061b0d020a0207260601141207060c050123040f0501020d1509050109020403020303030f0720010c020706020607120207020406030204050f 77
    0x101c104580803c05072800d0f489200480c0e05500009000c180e0001d0617609007180d00d80c1401e25203500408003d20142c8001100307487e03c501c00028540e500d000308800608d031824140c0c940b00b404901c40204499a6905000d0104207008540c07031200394800c11503445a40305600049c07840722417540041c45107529140300d00c0540d90840b032806195050202100082c1c0c030f4041103070780c1140e5000c07101c1400014200e0025104103883e409000c50792045010000d010740d000280c034045280244000c00100c46032441d07141d101480d4030300e030200c01458000010000b43c5451041c00005000b180011b0810002412010480e000341c17555490088149004202580041c003078075001d0080b1040550a145c030b1680400d6403808041c09074081d08002d0f1001442a900c07034490100c0003803c0190650108840d580120300a00301c000c103c50050044031004a182c900005a81d40103580030b9444104450126104800941049808a91040c2c50340720001c0541c2e11400f4142c0121504c0040c2c07901e508002c2500d187d00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 848433794 1250 848432544 848432561
    0x11130507020c12120a0503150307031208070c0c060f12060b0d0b031b0607110303030c0a0f0908060105010525080405130c090e04020d0f0804080c1c080a0c060c080a 72
    0x1c903840b410b04e00c05100d2591098a1011929062a0b80c490320351420701c02824a840000c1341c0c051040c21000802d05c0018090307901d20301a640c80b4052540c0714071800711507a40b004031024040c907100e08000c11283d807280700002540b800928207148800b40201818003600d081c0d611100c00003501058041006900d4400c101d40c1d038404030001d102d01c04413407460410042c8040c22052084101048003403d01038202c43c40e9089a030020246c075543c1ca09100005155080069203100140b49404600180303805045c0b00000d40b05110300802440e842c10004480781d50110281c1c140807000d40140c1d41c4003944a48011901c14072505034140c40d20f0900d4103005142d100c4166007111030b4101120a0181c0e600880c65805541101d40c0000e0165154008036180070781c00304005000101401c0c01c242805491000352041c3e446103010b40d0026070001d41045081d5801040c070806020b0134580400000d403a580003000c452a039402c01c0301113003403581ca8480c112074054640c64041404a8100841a0784034480e030b058 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 848435044 1250 848433794 848433829
    0x10509091e5b050108070314010203040203060c1312050a020301141303030f02040b030f1005010e061606090b01060203030915070e09060a1a0d0e01020309030711130507020c 76
    0x240d620807071070002c0c0034503407003201d034680c050010481180d006800c40a452000038052083c0b080d03503903404101e43d0f250315a01c01070700e8051080c002c0748480304060007101c1c02a42c000b0300400003502c03960040d40a5074007200300002405038001c0009541d040c0e00d201c44151034080d402138985003c003401894203540b45001c075807400c5d4620008100704820244200d06d926a05444c3c001145644000d18030001d1246404c94440204007000304103081e0724400d8010301c1000d210b609050602d41e100c006403285400c41600681c403031340a21003001d42d0070002c814072004500541011429419644803483c0280082e00410010381000041145a200c00c01071100c0c0d4000da6078084007a4503200300014158401c400002d8410b03404000032450691392513800c04040e11100d41c881810548440400185510019614940b0707410070501c43c05003641071094902ca0303203188000c1c42c500703005603940105182c201440550301c0740203000000902c0741c69206952082200350010404200100b0400c2440500010700c0d94 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 848436294 1250 848435044 848435113
    0x2040e090d020d0e06250611031005060702240c0610030b270f030924160f051005091903050a050a050405040207050c011209020603010509091e 63
    0x460741540040c20101c01c06162510180c44000c00002480900c6590584850b1164400240e41c2001075504940589845003000304180a44415151860300007201d00401c1c10b254001c04012504100f0014241e1520040c110748070104010900c41c6210b800402c80e13440407102060303208220804100194002c5034a0080a55940c51907130380c80b58031030b80107107042e1000c0c240c0e603110410610903485440c1441a007509950700c07a036030403000660f01c1d0880f22101d882441100a5441c0b20b44c280840c0d80c02000c90301d1107091501d090401840a9061400f80498034614220703080008940c00f17200030303d0214105440818141030040d0018500100340040100c800c0c01140c804000130307042821141c4c804614140241c0300d041111040d13a00d40515482240c009000240c1c2d0420000302289001c85108241c0340d041200f44040321080482c0d810410081d00240c007040103014a01e00452000c2d8030800b0042201c0c40d401c4e44091800c3e400791000001e08460b0300a64140940160b400240304900880c100c121 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 848437544 1250 848436294 848436313
    0x702151e01120311010e0c33070c0b0a0c02100e010804020909010608070e0a06060f050d09020f060706060501021b0901090b06072a0906060804030810051302040e09 72
    0x5030000c95041c0b2801468500780c07241a41003500581202222024000080098084d608000b6440d881c042284900c41c1701440130407010307914084601c15a001080c01980429a00800000325580c4000010741d009602d403480010001e2101d0000c10300030060341d40c1d0036003198091040c03020340003081c82c007442400b00c410b030541d101e42d070321148142e43b003501204c1ca0300301601c80d0442c0703600400c1e113904040034500654101042c4055a802240c0c01441c541c4020083c1ca651150222507280c102c6400100240041051050303003010ba4014201ca1b6000a09003034808a01c8000114264000e1030100c500c0c58681000300100c1da01071014407151440300004000041d184000201c050405004009580341d58001c02001620740300c041c4c800c1c965005405a0f20000f01152440c241d510079001c80c014203680000c08200300320140260350444400c1c0d1981c0c030503912035560940361980000c001c2004041d9440340084c0540c0c80b06d0346044940812070f40180c0d61810400051540c0c640140207010385d5201c040803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 848438794 1250 848437544 848437591
    0x180606030212060d140a0f050c090402030709230106110106050f061e070b240105191229040b0d080f0c030904020a09080c120601090b0f0306070215 65
    0xb4562218040b6650740c840d802c14500f20007809549030795410540303c0c00c4611070400c05d0048803490000d0061044581e02060007040203c048003c43d40250140c0100c2070800990000d0b810414201d100c41440d41d0004044164024190303109a124500244405807050f4100d07030288104e2025002c20b0b2016002c41c1e1000340030a0580c842d04902c0078506945184065550781384a060342c02e0103500040380304071800c05400d0b200e62800110000c5104001e10400c4184640c0075008450b4490908148034508000961007911746180304d090130002c080d02d41e5040240210709840075032203440310b0041d03c550014a84144012120044040e5000f0580080d185000c501800107540c41c480503203401c141d81300f5610701c0650450190648054102d0700200300c21559540011a00090760180c60450340c400c1c124a0401614014415205c44240c10610051101d0038254120140041d40070b00321070210301c942c40229107014801ca40460042c0c0011014640d01c50b001c5035155040800041c1c031115141d0103509 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 848440044 1250 848438794 848438827
    0x22b0f0b090d082212030501051003020301120f0516030b150102011e090519060203060906030c130e030705061e060a030c090f0e030a020109051606020c0d0206131806060302 76
    0x8034445180d40f20404104404c010392260400c194003201ca404010740c01500600a0034007030003881d01c10b001c0a0189004c461007482624103c070300b40303d01020303500200d0b11010b00c1010788207016070b05030140104900380c00d135049044c0c000542c81200249854038000c01401050000500c901d411a41440300b00680c0324641e03041040c501016510001d5881003d00d0603518110040381e541400f110b0914000d000d014130369014520405003a0b4560f4113aa80700da0816443d0030b0324010140d4000f126007021007400d0707200c7c0c1c0078420b40032120007143e103810441e8550901c1c2501c02c8900c0d076401d140c000344401c01200541e071140d80101d0142ca410500c2400d565a0782c01c0c41d402030244c03010312a81c0c0c10204040e00d0b0075800446000c080e074020f507942d414024200a01030240d2070340170380d420710580340403503a00791032030b60300e04200c42079603001e802024490710812000500d841c10990344520240b02403036200c01e644072110b000304240c1000028203690040403d040e506154409414544180a82054140d6009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 848441294 1250 848440044 848440051
    0x5190606111f0b0909150106171504112a070b0409020c0c100e0a0e090c060306030f0102210714040b0c070f09150b16022b0f0b090d08 59
    0x460841c2c1c0d9642072a4010081803110003080d80300c1c100c3c80620a2144020540c0018690705607a0544183e80b903c2d4186c0d8601c2c211080c260101c12034000150215155449002402e00010004140300c000600400798540180da801c185104030072810904501040c02101e04008400d00a810302910340058200b180c0624402c0c1c4000a80002c1c24044909043c00304110961000388402c00103078032031000401e01066600414000c0000120110b10b107005440c0142c0b00d00e1100d4003c06040f42818140803154002074603098042c400c8043c001c112180a0000c0c01500f0030030388003601c40003889628a109020083d01c80014070041c12755410b11104060125000e4403840300c8642d59480d6104086450100e26a00c1541d420384c42c444080b4a04034150007004922070a003110700c1d49280c485407500a54480e020401e01a0001d901d02140141031801454654480a2007034075500802c0c00c806003119440d00104a03018001084030b08100005219115003043c1c2c0c0c10b00902e034000005001400010026 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 848442544 1250 848441294 848441323
    0x1b0f170303063303091614060706092907030e0a020f0619200111120705041e03021e030a080306041508010c230703140403060519060611 60
    0x31882d03514a0203c60300b20610035100301c002c0e08000a40c9068014a6001a01c072414240220401c00c0540700c1ba00c2065410b9810700e8000c2010040c107081040383d150f0207030b18100c4070640c0741d0003440c0c007061105500038141c604a0200291004450b40f005001d820018201801c3c1841c2c01c030303010781c0c0c900d0004201101d20b60550320718864465900c00100035000d40c92007251800c41c000c0c0040441c60380141c141da68103240c01c000022007650242d01500380d41420441045103103007485142c0c06034820141c282e0b0407068a0a15a00d07068031031030390110700440d0309061405004039850030011400c100382584405901030140780201541200000e4881c4070320a005040303c00044003040c919622030344074a1a0482c2c0c3c0d542045040c0d80e841016018002021141c1c0c042111000b203c03c65403004d4030015841103403040c50700d141c08525a01900d000c1500c0000760b1034108240004070000c1e0351071207283d000b400085448444400c6505400d0141c416a41103241005500e2518100d0074a0019042e5441c4c40312 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 848443794 1250 848442544 848442559
    0x5060f0f0121060e0a1b031502220b120708130f08210603100225110d061401090c020a03260f040b0907051005161b0f17030306 56
    0x2156158092210310b4400f034086490031110b68010f0600040e01c40140b0710480c0c0d10f10003040b04264894416132540300140a0094600001005180b642d00504204804035a001c0d10060403c081c00c44a424942050041000c009900e03400b09000f2400300c0d901c29140d03e4080f00701d1070b0202041611098a1030010140700c480c8500300f08200d80d0105541d45560000c00c42550403210078500803030320400b0340313a46010780070708000b104500d1803500840e2008403402c202c0e041900540100c440950003406001d5074560043e007546801035540c980389035a87c5004201c0030540c2e400031403040d001c0490680c00442070b2881e0140004031942c020826101d01c54050500d410b95802c00381142042031894142080000c0c900780400504c0c2c42c110007071034090f6001307640f403c1d02d0380e4409034925034801c40741c06929840301c00035104404a61085004180c2440c2505400035010303a6659080010300030302c2c110110301c440701c40c001e0040c28a0b030002074000b00001d030925050038074021005600c0e4400544080d0040e8407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 848445044 1250 848443794 848443829
    0x515010f0902030c18131514030d091a0403050a0804060806180c07030905030601030f17040e01031217070f021908030a200304120e0306150402130905010306060305060f0f01 76
    0x120b0020f03081c804952200203010b405003d10020a82c41ca060080c232030110003120070102d9030304000034600c14040741a220b84c1541801c1040c8a100300c0740080e44043e00050400000c000210140a0045842d100b144d6158585080c00806040c51308014005e03402110104488203240441840c125002414500302030f075160704c5820115120302c501e81200c1e8142c4140400007041140718031964000300d004035100d05250303a401001070a144541d00c01c8a050103982c4006002051104171804100b10340d905184004a4110303100d03007070303002040f580c3c900400c03184400f40d50982d0b0184804000c2d916000c13603142902c1c19564441405010145c00c5141c12640c230340411242d0014503d24600803219000c80c2034491a0525181d101d007099208a000028120401c8000a0a000aa082c0079141c031800c0c01c0c044c0010b41091100a4006145600060102c0d46000942e91114441c0901a5026031008a503260440c01c1051402074054400307120903408100300008000c2990885054888070465401e5810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 848446294 1250 848445044 848445049
    0x1020a08010509280b010e040212010801180c05060a201f154101030f05040f2a03030c050124170106050a0b0702120c0609010305040c030515010f0902030c18 69
    0x1fa0410101e400c548002204120103800d880104e0480740b03c00000e1110b210361488030300c56180710b40001855007620704010300c154541000540f07180c0ca05440d14180e280003001201c2640d101600004210390000100a000702c00c0c0b0000305d0b180031070310f09414000101e15040300c1000b10203504c070b0302c002490200100308141102c00044404109421401b09004400e200070b22206000a1902d5012070700d80a0800f103022a43c1c0a120301c20750f0884041c0c0c000300450707110f003500c44141400841480655240c041d0701c00c2411402c4001a500964a88440601c1c6140460864100c046142814440e80452059081d4840751031740a4503003888084052028500105000d170030300380c00440d804051214085994902040504515802104c10a09210007a0001d41c0c44801043da00d9411400800150800d5400b0360840c5812a100d071b1280a04599240c0f45c03182480c178172a058120411020004000d1400400140f8014201d1034000314554281100800403034810301030101c88500c6401c07228103451f03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 848447544 1250 848446294 848446307
    0x23040e0c041212020712120507030e040606021b0901050d0212010219050d1d06011214010903030504021306050f01033909060513030611070501020a08010509280b01 72
    0x90046400da0b2882c03942520308064003540501c5644014410b000000481c0311aa65103a6441c5070028540002800c0880c0c0482d080d038030801c801d03018001e805030465100d494910510700202178960280c07140d2800f5500c111003100c9080211032103003a00b0070042c0300660303c10035002003443d411140f20400c1c0022042c0300303001e4003800742403502d040c0c02c13070840340e42c8290441d00a0640000d285000c01051103000071000500900a6148003207502410042c803070341e017041d54201c02c100c0c01150b46082d0516030148460a681c07600b2801c40c002a203403004d010450030500070b0490600d80c00603050001a0030540480c0c1d4010086000d10304154890f424100c03083d40020801103030004020b40c1c21081ea4145510781905004c80724100000b810950000845900ca041583e4a414881c0f001031070791403454584d44040c00c02244903440e00e207404c021010004000744020b140c0e42d003842d00c1fa07a42c29850602000048080284003500c00086800a144c03882d0701c41d00c0c0d8440703d07101c2c044001408030000c001221031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 848448794 1250 848447544 848447549
    0x308090f060c032b2301060804050c060f04050604120303050c070302150717071814150d0b03070909060b090c0313231509010b0604030605060d06090b0723040e0c04 72
    0x13803070701c1c04560001c0050503803e41030010010f00e40440003642d841c002181c5850701102c000d40b03507401c45179452001703140400080112500e404009418581c803140056500d40c8186c0c040d10f46440e001494104168240c094140c0c03201d00e01400317500b04201600c010b5192032150f100c039500c042e01032000071002400f860750104002421524501c0301c0ca032a1101405120340f0080002403800103410001e060720843d0001020020098081d404c040901110121250403180308500c203c0e84400001d40713580c07420841e10300140180d4501050350310480c104542150003c0d001c07280904081d0003041184480c031000c60350804030310320181401e0318450502c030000100c1c043d002d400024103440d1148120500040014089030840b01480c3c69407143d03005a403c8900340c034420740e0000380034002040415200c1d40026440100905925002d8080f580c1d50012100059003c80c2c81d020150144448103901243c1d007a01e000243c0c020b01d00340014100202100c0c000ca104114140c0000000a01c0c0d00c880102940e00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 848450044 1250 848448794 848448877
    0x308071b14060f090d0806040905010c08011e030804060804050705090901021215031207030e131a010207060e0f01032702030d080403090b0d150308090f060c03 70
    0x10400051425041c0900c0d4298126841d20421020840d0850500b49441c01201284010201c40ca40501c003550030020041010f540180c1c1c91808001059081c003810001c1b204980d124900c1c2d40c10042d68068101c4105241c0884808a42080c00007a100340200d0307050324800d0605211039922440c3c01890541260000d9400841c0e00050108140b01500504800140754000aa4558401021040d041510b401c1c3c1723507040e4403044250141105500080c500c1380d0007403400c51230020300c2c40d000c1100e01e803505500210159031546100200311000c030880c02141d07400d02c060201d0300e00d40940281290800d0408511800e080c2416503807580c0294480800400d80b560441c034152500d4010030b810240401c01a0f01a000e802c0710148558450300c01c4910440e49030301d030401c15505160010f101030300f00d21058481142d903400c4048419034441c041000862040050b1a0745078095070030302c42081c00306140300d8042c0c00d00307114542c3c1004010080e2054941c000c0000c20401a00f80708089020995100030b58 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 848451294 1250 848450044 848450087
    0xf060303030501050a0909120e032a01092103120e061504062c0a06034b0803070c1e030e0d0201020a060b150a0206090d03020a020a030807 61
    0x400d9050342025048440840d12515543d0f5a20070405c1a03c100c000d00400c1c0340003e2106044c05c50182065420880002d02200c8140303481407036042850083d0202032504034407040da14080b96910450500c0541841b000010188a00504907004a14004402000d0014101b440c9442d555243e00c00b1800240c0201180c640c0d0416200911000306a040322902440c00c1541c00718403034443c3c126181c1082440d8401c00d02c09510100000842100603202c0004542c644a0000100e58910b81c40e0b6030b003055141a400c0081f9403141650030710f00701c0111203800b1103181c000b0042c28a8644024540c1c4640000c40bd654941e5402d03012030300c40210302e10040500080c10946c9100640d07a000100c01203101c1e07151802c060041c0700402c400344160300c1009006900104400b000204070b60007410f1054000b40c01e900800400d9a1945003d40001c52003d0059000d0010000310201c20400c6501d02100c50074110300e02020b40500039160400c862001c2c00703120001c00890b0b6201c5c0300700e6081c2040c424040c0e522 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 848452544 1250 848451294 848451299
    0x50c070e010f060804030203070605100b120a0f05010f0b0c0102120c120a020f090d06060314010e060f0c0a050a11010f1a182409150a0803030c0307030e010f06 70
    0x500360300100380a80e00c00380520450206880c0e0089466a00450305034004504048040c1d0b2800c0280030000c02645541024640c0002d90110310000341146504040506034140f900040c16001c49181c101c8074540b440c2800c00411608243e9001c100940780c2d090350b01030340c6141a450141c0a4400c0310015001d006002c0100500c00020360007401e03176107642c01244901601c800441c00c003640610301d80400b0b5010204010402803506103a5107c1d00d62007403a000c60781d66034a131250b80030304410741c440d45541d9440c0e0b0710354034907210103002060b031041364203620f081030b410030a020318128010000500184080007500c9803981d4003e41ca461100c0c03040800a201d444500c031a283c0180c441034007204204401080b403d0740da4544154040070520300104c0040a9948145c1c918031190764110005610846903283c9041703903115481071512034020107090151003030b5010240814001d80c0e501207541c2d034105009105a2049410480390480d010f07260204002298020444c01050440941980e080c03610000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 848453794 1250 848452544 848452559
    0xe0d030509121f0b0d141e03090901090b032401080f0a08030f06120a050703060b04020315060307090e0a0501060206010e13022b03111c02030405151e19111903050c07 73
    0x47c2c9040c00c019504800034400c00d075001b9602e0180f101c80c503521841417001802103100e44e501400039030320010215200d511052049540e41000e000e81352001c0102c140040c410000104500d00c5a00d01707803401400c0340f0000b629114001c0c0809420a0351040324580815403030341d550f01041c1d24410b190015124021207034035025030b0350040c0d48811a04d49040008061a5140610980381301c1e080c02000c0764030180e464020807811358001083c3c0018001010b5010456030416000c0d030b88203040121b000030b4154145103010345001c00507030041200c51030580402c04003203000740c0381076006a8160303440800004104148801e03501d000d000c0052004680b0100c805060780036061080082158054451005030381910505080c0d0b42000d03000035900402c02000709003010943c9402e0720f00700303107001c3e810300c41254290181b8004d4101d2500d03440e6000700d000340c0080803d407060101035000d414003a100c0c456583c68951105907202244020301d4a83c406003007031501400803110000344041c01d0f82e48651720380aa = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 848455044 1250 848453794 848453803
    0xd0b06031602010b270a0e0a0c030b0c03040f080705240402100e03120c030d1104090b0a120308190606020a0c171c0e0d030509121f0b0d14 61
    0x1d100015070910028224608001d441046400c144135030200004055100004030800040c0c0407003125613540e80e480a11801c2409018039031783c40395007541030103495030411a034002009844000800c60400600000495624004035410b501005940c0c0f01d8180c0e0034810b00380004114045448403803e07007000d80e6042490829449240308407000040044900e80860344148903080340f81e0540c0c0300100042d00001400043c0580401420449140281500c124410f075480800049460726001c64140700c1140c050050003030005050314143d40c03503441c00100c0030b0003040006024091101c00e0000c00c1c0143d1400d44000f2200304807250903c061030b40e03901d00030f5032814202015241380984517400b00c2d002c10910760740b000b0b1444640090452a100002a0180822210300f010600c5151080d404150710342e078480d45c107a94029214652a203401c1002c0c483e000f0030002d80750304180c0111a600c16090030488482045400b1103000060408807240800c0c5c00c90101603010303100840c41d100c3c030b401080c030016 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 848456294 1250 848455044 848455081
    0x150207060f060602032212030203040812070203030702090601030b09091c08160e120105090d0f020a0b0a0b120604050609012301050d062c070506041a0d0b0603 70
    0x25010480810403541c01c0c4101e902c24011040180c00070403841c200541b512041c2d01e175003110b6030085030031195242c1a01c0342a0441c0c075002c4000d41c0001c10100209c280c00e010359071806100c01106842c140e030907800280c0300e1203107250091081f4a20000310342c43d0391081d0b0020096040c0901180b0340c17030400041c40740d90f5a11034810302c03105141121007440750b036104006241c000c14404129418440400600f0344100f62000300c02a0486240c00d14040146401d010f42401228420040c1c2003506805400819294500c60400107552146c00400001402c40301301946c000032204001401c2039041c00003d4801c1d4141e807001106124400921052000220b030090051000d40020404c800d5811800c10090482a003601240c2c80740c00c00400070b80c01c103540c411031240d04c50200001d0803540542c4408806c4009070080c410200b4101e110b103088402044840c0c043c10007251290300b028903204041d203c440c000b0f1004d0100010104107100090029080000d4a00300208119100d28040f05010124203620 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 848457544 1250 848456294 848456303
    0xc1206141501120b0607120c060c0504050105030f0712020a030b0a0509040c060f02030f041211190512070b220b03040218090703060c0507140c09160c150207 69
    0x2001066a141c00c5442141d074514041c0c589201002e041c10596008000035130381190484002c11040b000114500d400c0c1c108049140c841074042ca0740e5090030f03011035960011a400307010040000b40460303070b04041a690301c4814a0500c50703540c1c0c1c0342001150071000b40104d0941290001c50404102a0940c00591003544103581e00ca1140c3e0380c03881004502e00c01518050000150030900303004151240c80c05402c46060350046910340042d260b4041e00586c4258809040900003074440801c110307a03403052010000c41150030400b5501c01000001c055582c504c40e00b44514a42c3e4510754043c1020301040300207240c0e040d4040d855854051120032000da0800302c3d00e00020f44007101090421040054034000e5402904c0b524000c182e00000712910707100a0f00c07103c0f07144218400040003411034011548580360940d10292640200d00c2c0c690210540d2140b080000e420804c40c0780107686600404642c0005038500141c424107042e0400c0d6070048500c0740c00b6210f1040c05c4039469440003a90020118944103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 848458794 1250 848457544 848457581
    0x1d0711030d091104060f180b090a0e1e030301060c1b09020c07060f0e2e091401090e0403080403050c07060e0f03062e050a0e06120a0b0606070c1206 65
    0x700702c04c0004441107800382ca18201104002840101400d00c0030000c2a5481200081c0298448001610358001184daa0710002c1d107540d0709088016061010340c501680948105010050001502d9101c2c041405510200701c41241d118081c4030ba800b140c1e8011503041c01e080c6810b180c84620b214082d5000700d1043c90680b207010000601c0074441d0941d161401d9150b070382c080d100c06658080010003182e0340100f5141110920200302c18000054500c00102d42546420211515100f84c904e14152852801814025620410026211102c0b1200c1d8040d505180c180410b90b182e14040d20725000c2e414070140c0c10b100e01c040108206402071010707500c58008940079100c0c0080c1c4010907983d10780844004008011884410000303100380342e0041200494a11609030098450011814031041c680c007001c121020101030000604055601c81c0200e42e101c00179180450941d1110350120b0005495107020791000503885003481948040c01d0050314003540340840c030304450300344103003d00321101d80410a00f22 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 848460044 1250 848458794 848458823
    0xd0207051e030403080a03111c0c0507020312030703090b0906040c050a14090907082d030703050f07020303090918070906050d2004110c060a061d0711030d09 69
    0x1c0d032a508404810100461070103085544441d4950000d803482001d041c0c4601c0e00e40100d0401c00c001c3c001c4800032601501c40b8124a409003000e440d5070700740c08414407004004080241c0c0300030419185440450352840c1e40c0e41c65058044009050518014240d94808000c1c0301d028440400c581d8001c03405240b000300703126191820481c41d286288612407010304400c0d09000903007407203059641d019075241c00f070760481c0f5540d401e03003820210819040b108910107403600c44182440002e0f0b0000a07a1703014011070a00382507680244c0701d403207000a00c00c403085000c40c0038011560100200c514070000034001d5202402c1c2071001c0026290186050101c9000d034000100c0c40842d240f1920086820003031540c0150025038079411815581c5210001e0101a60905082c007500d40e4001c045d10340c02d425854a50320507005001d1340c00c00101401c2800414140801003110b103c90780f5841c10096801c1c0208056a11200340c259502049000461041d02020079401c075101d0f85507200c0b20280f402030010b0b120244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 848461294 1250 848460044 848460073
    0x7020604090e0304240f0c11221a01050313060f1e0b1206060f0103020f0c0706021501060206011404020d06090e07060905060d0905100905010b040608030a1e140d020705 74
    0x140045c807400140745011032058984200c0484241c2400340e002280060400c10200e80407168900003d40c3c1031140070080941241d01c3c4c8181d04001024202e04900e0ba18058002419031001600b500c0c406150300100317105001030740d4400c040d13141000a00304603545032a01d04049500c0c1310718070104070300d29000001d08107003030540c010320440d4800705c041e0000c2e0340e9503030400c900c0100040301035041540c240601d81c07582c005140146600480000248900c2c1e02d0032100a01d00107000c2100f450392005070004224142d00040d01d94151100c0d0040340c04150b0b42000458007c0c0922079500e050141444070016015045902c500005040c00b41075518050310f541c01556048600d100d0346801801c104100c2501444640c03102c80072520650544e507064880d0203115041c0c882c00758059405955844040f0358520345882200024942d050145081c1841088090400003103041d4074010300760f080342400c911600c9818502c840c0c000c3d0f2360b0000d4031801581100b0b002504090800c442c20302c0b0b990000c00004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 848462544 1250 848461294 848461349
    0x3151e06141204060c0c0501180227130201031103130201110a0309051003020405030a1a0f0c07030e030705190801270f020102010b090109020a0e0604061407020604090e0304 76
    0x1800440700b50341d5841d250395000003030074009802810000c0c030384d100d07100003a4207024140d0a041c20032508840e1041500400a9082506040c41e54400200010440c40e441e05031407250f0001942d403404481409a0006031b028190240340c001c10303000c001040100820203043c007000320300d000780e86e520424560035403125a0394910b044041c0200f0155141000a40742603840e100b405c540919016041583d5100401d1a085084000311400c400d00244818002001441c0540c02005080241e8a60400c0500084c441c800c03044098200900321411400304d442c1001008020440a0203441d00c506c0e01d203011241d2179500340208031040d42048200810000306686400c0c084880e074881c101940c105940c4e0b21941c0042400c101d0642d503c5100b00c68003903481d0b0180b103008018028000d680c41880d80d00c003c02044503a9843c0d4859030040c00240722855100403016402c410301081c95640c0d0480e400000c1040c01590f014440c50303030500803520400980400a0421556a0321400c800c08404222082c001d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 848463794 1250 848462544 848462557
    0x50a060614180901080a0308060105070308010e130b09010902040e0d0e060d090c0621141b0903071203090602012706021b06010614030606070303151e0614 68
    0x5003081c010785001140306001003a00c0c82003000303025012801e440100315025801d030b101034100d82105a07040d080c5074108103450780c00003092900d10702d041c80d20750300940a0b42040c010541c0c1c00d12980005511451900308140c000c0e908441c000941c0e28041c51118080d00345400102d01440c1851181081440700162003640c104158554800e154058414401d16811410100c082d094642c0d4814001c54015107a1801400403952201192a0f010908241d0201c1d46038940100034640b80203284001d54070074105420455102a038040504007a40100d00781c01061107069240c000c5020002d0140cad0b005c40c1c1c001c4020301c02d84580100320754502c0c0980c01c80c0c1c28520115919607041413450ba014003001c51499080340b01d9900103003010f50480c12611540c0340c4540400083d8020801031001e0342d00906081c060300c07440002c5514620300240801c22502410f04020305060b03c404042c042187d19405203070180c000011030b0f8480c41d2200344411000c40340f134400c54004c40e4061039958006040e0754201d924 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 848465044 1250 848463794 848463797
    0x2011d090a02211513060f0603050402130e0c0a0b070512090109030512031605160609080706051003020909031608090d0f05030711040c05071205041208120a02090a0603110d061503050a0606 83
    0x40785180030015002b90000400072644450701c004024051400da00c10140c0b02c1d2000801805419882030a1010036001904050300d101c506100c2c100003e1000128480848030102074140c48806070401a074a040140d04014880d0040c81510703e00700410341e0156120754001070200000c83c4c10340400392a94494940810582044210a0000b0172020b801803484107100d0016103203404219240e0004840f41901c1201031844007003030400651901907105d80d04210050003952038401000461500401d00074030081011001040119040da103071708644a0140d045010040100118074080d526988440c50444400741e102c4105030302030610744542d1800170086d40794545454003a8440040c980401218442000010440400c1d0f05251100761a00c042c072482080762100741d2480744400c2d14000420b400161703072042c4595100d69070341213191800c82d401800c0004060750f0b2038210022a1041684c60300d001400c0100005684082c04031000b00f8040680e0304102c5034841404130700590b0103d1040c0e80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 848466294 1250 848465044 848465069
    0x260f06090108150c0714101125021302040605313302100e030f04030210110303180c01020f120d15090902011d090a0221151306 56
    0xb0032080307689100c0e40c118200188460400c0c165580f0900b101c40c4d1b2440760406500030950034401103103680a03910348020f00380005402c2c01a200c42618000d0a035a034018106940c00e0b01d25400e5484000e070528118190703110079981c498442034080c00c02e5109800c0420311044000e00741c02c1c140100d480640304a00c070441304004562510f0001030981481518281803441c4101e0f100403132250340b40042c0106a0250041d10380280b0b440c841c8412504000702c6080c2540040040e000e10005400840c0d081d6036048070451411354500b00d04490600301e03c03c0126851000100b802240ca01c0b0a8030501000303041000c407150712080e03c00481c0c648018002c210362541c4000d01c4013007650701d28406001c0c10741d5031810019403200d442101c500300c54699440f1489969407140e0b40d01c195681704401c0690000d2010001781ca40702140b010542070310000700b80b850740580c0400c415082d4900340b55407117519030030000d6032071080c2440131000c42814091b007032a034130465443c510008850001e0040038110307240400d541 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 848467544 1250 848466294 848466313
    0x90c0901092d0311031605090718031a040b071b02041805070b1b0a150c0c0206190f0f05090913150609050c09031903260f06090108 58
    0xc241041c0b42c2422600341c8642d50071001c5612402201c080025800741c039007558645401c80a050070a1100d4480b6009000901000d00c0107440e1800001d81040071441d0150485805c58040c002e0810f65410044c00f031504c11a003940c034040d080510a006501440b500f10658071250f01c142d6030188a00c0c0d42c5180382100b640d0720400361805038049128180880c0042c60450020350311241044a07d40080c401c818000c2600b008090b80c0440b0001c0b03182088005010041c030549a6030310060710030114040d46034981c070904c00140c0c030900c400a88150301800c00b40d00e56504494180c640242030a01720002002c1010910f20507124176032560f101940d0761181481c0a41c05018040881c0f4010507a00b4007920318040d580c0010081030f48018080c60000700042c42908000e00304055800c0030302103030a0544148021042c554003c0340010340801c000041e03070b003098003c0c038041e603440098192100c500350b8034136a417040440c0800c43d1944117088203801440559100020400400405e00420680b6031062081 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 848468794 1250 848467544 848467559
    0x307050909061512010e1f09020a17070b18120106180902030708160e0f01060906110c1e0109051509150706050a0603051009050c040b06040b030408030402090c090109 73
    0x15000f59201c05070001c0c981010b180c900600b501d00010400c070050f408035951400740b0032900e1020102c0300e203a8005200c1006a500012043c3d02540214201c010004041c0740c00705004100c801c00030044030f8000c03925000030002050041620b00003942c0a00b540e1100310360b0400d410300c2102c0c240c3e503030102684043e0310414907070b100610a1310300498061003a107001007001c040c10400e40340081d0342c10507000240c5042c2100e210b0b0403c00034003621520b0005200603c502d0360060000c80507034882e0f142200101c511484800c3c40c1800151102d90401c0280318011004c503c10543c0030145070003a2564500c41d552002400b1108a40d4042d2810710101800f601084c1d1900984806040000c00314482c18000340d61503550490700c0c191045012559a0b100030010410300f0b11007003a404000d24000c00c91080c00c4c0d01c58948500c010348074203200f00d540d02201788443e9258401d40b0050a199044079849140c203180c04180350b80190b034241e100b03503481c000250482d05218119500031074180d45c2c03460654601801d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 848470044 1250 848468794 848468821
    0x9010c0504060c150204091508060403050702010f0314091c05030114010302131802120105011817070b03041209080d021002090f10080114042007030917030702030705090906 76
    0x8607103484c044142e000c800e550704d001900107403900085c0002c5192080702c810004121650003114190015400c20001c07980010076501c03400d40a080c1602d014a1f4101d0807030045c4822a041c50500716880107001e000000010552030183c0d4003011384080c3c442c444801e0740c40b8007003440740981e8a030780d0a400d07000551190700038000796400c00c2c040c40049a1940030b0146142100c82c00d0402c00c40c1c1c042144007101740a01d030b201d40140301c2802c0116801c0d43d118500740c04d08149005200c3d00850780b13004044240e81c1004003600030000200256204d0419140202e201c2441480842c0059440000841c400c03601182c60428020a50010a810040d100902c1c0c0a50004e03035005600c01200c04105d9183e46440c2c003290a003881d240d1300d44c4051341c1040e86280d41000b44540250090346030071411091204030002375507280d0740c1c02d440551100c1c01490300311490007403500044203480060006604044001024104c4ac0744220191200d03184ca0324140300020038121070111403584040e0129003070b5102c544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 848471294 1250 848470044 848470067
    0x30305070219150f020c0307061b03110d0506030c0607080c010c1e0815040e01020a080c13030609080f040e10050414010b0d06211a131217040b0106030509010c050406 73
    0x100541006031b139420301415034001140c00e844035500c42c280c22040e5110131003291104c0060381010001c03401280f02110f207902401c408980855621800300e85c0c9907a04001040d14142c008200c0c554a80b8145412541c80d0402c0d01c1d0201c0d00d60900e034400d034969000e5540200303601c6441004c001904000c490464103001c0241242c0d94000d5150b0245400e40c8490041016000a410000d6624140264004d000c540010010808204c050011201440e001031002c1c0499810000104400d030303c50818640911481c48110000d03400001e0008030f01061034003140c402c200024642c12102c0d0f60b04140416a45010041c22142c0c409400500030200300c400501280304072414001074040d2030700561121624820b800c0380320381009024032403c00c4642c40e580d00200011444498503070801d10745021041424120080c01d21102000000c1c03070510900f1160000c2c0200c50170b00500d81445e051252032060203000d4080000e08010005100300c005000b00c00c040c01c1c20b69240342c07030540307011012102501e094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 848472544 1250 848471294 848471321
    0x3030106020d0f0315060f021917090f0901030606081b100c03110708060a060501030e06060105070f0506070c0201030c0e211204090518160605030a1803030507021915 73
    0x5005c180e0200e40e0a08001d03000c0c00454850b400d14201c0c0d1800640b800c154980003592820740c10448170000b622503401030f10f00084c0300c0e0b4603030b0301c45101200242c00c00058010181c0c00c008000c0000041c00915000038040f55520000d5030742c0320004802d40c003041d590301c0c4034880c0c1240425407401c501030300c104000c60041e03019250684c0a13800c02c0652904100895100c02a56400170303051209240c154881ea00060400342020041c0c0391408072566122a03004280c0c1e0305009000c20000d052007081c50310380140542c4082910090710b4010b1014041112a110030780c0040c1c6015a0b20803614041e00c1580e0110308000e2500f030480c130b00360300700744800800120b0228240c000c132214013028100386c40140c406031900100210301458103041e40034000c2c1100800900c0350344042202c848400c4071241d50020755030140b80083d5240c7c3e0f0410104054403034514a100407005814264092507816407006000b01103d60a40752401001445900c69840c0a0380142003503001941c0700c00c200c81540e0215600e40b001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 848473794 1250 848472544 848472551
    0x8090406050402070c03110102070503061603020c030a020105040c0506030c070f030e180103050f0303190b04090b040317011e1e0806010807090c050307091205010902040221010803030106020d0f03 86
    0x164000b00c0c003a40c00c2100c080310641c0d814030040c401c200340140d410f00150000c0c03006100080c50100000d035a0200a0b00840203604c2042c00980403911907012101d03445203280440f6654801c603e0000d0082804171015a4003500c44100406c3c0ca16242080380d02805090046034241a5242c03101d00044052241c00c030140a58008035403159181e2080340c003109042030703c20f8000c940c5117040040c1060045182400320b0342041007004100c003448580a15200c4152000040c4507800c00d0101d0300820f146d1001074551400d400070041019441034801c1140780c4011403401d1180d0741c4074a14214201c051100c4010040051024800951042400c00c5d1030407080c2407008a440e034401c2500e0401c07d084c0c004100300d401c038803420300603410b00c2c1c01a032192544038a0454035515042d6001042c4501a00454081c0c8140038610700c2480030075040141e0154001300115550003403655a50740f07202d8400200404030f1448000084c1c80c0d4008810b0301d040720001d030043c003a03030404480102e1b8040901034424041c1681c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 848475044 1250 848473794 848473799
    0x5060907120c350a0209010e070206040f140a151a09191409010b0102161a0a02012a030b04050c030f0606040b040b09010e091e101a070b0705041208090406 68
    0x1c0c9001201d003000001c0f0054503035031185005000745000c058121403c080e1201c418008016400514584e22982280320f8059920711ba203400f500c08920100c5547c038510900140f54203001c5800c64048841c07407c04000c01c0b030680c08920161039401d42c000070030745c04694030000803905001b8114130700c5080700300e84c00002c0e50410b6404003080018162030201450395281c092040950f0100560307111420007100250000d40781ca03448012202d4076551001000790301082448c5031038001d4001600c841543d200c0a800140000c100d80300070140001d548d40000e00786a4011107604180c81030a000d514500c101070300c0d5948002400700c0c1e80070040c001130381001c8204800240c0c141d107000544084c29410080665502824000500c0103082d503100e907100e0100c100a0103144907001c5110410003c51801490243c0d41e45020000f14040c503901c07103980010f13800500406034041c0701c020000184545c03044132080e00c03007400c12102400369000f07a840e958207118400300440e1003480905901d000040001c1011364 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 848476294 1250 848475044 848475119
    0x20304031a011d19110d0905010e07170601050402070206190f081509360a170a08012d1d071e050d1805060907120c 51
    0x55103810348100704071000014050026150f02500390456282c1d003444080c1001070003075580802d01403d00440951380c864503089000c540094912092001d0800c000c000c04c40c2c140540a090106a202003502a11a0100d019041e400b0711307045404046004000c16800c20741840b00a5100d4007003a81d1201007400764484558002c1c41c8120b100d07200b580c1e8492003064600020341402405000c0381b040011441e03400304251550107820b6484010607429403940311040d010703600c3c01c0d4480342010350980b4194203984942040050200007943c8034900d41c4140c00c2d121110700080740240f9240b032002030f40403001081010124502ca0154840c0c6206d08035003414840a010250005580125840c500845002a003c0b990140650740460740c0d08080c0d049010314841d0400d81c1ea1581401c809001c00801c20301040c0d0742c41c0e880307030900440c0c0c248480c00c40d01d00350070715994070801200c2c1a41d452003540d034003040c0d020f0305e194880c9116a1200c4000403030342c14040080711051501da0f1002c1d00d280d040d201d040a14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 848477544 1250 848476294 848476313
    0x90c010c05030909100807050f0913030314010f060e040203010503120703170f160f050a03150905180d020a05070306050405030d0f06080c0901050d0f02060f0307080f09060702100c02030403 83
    0x407171100c08000d100307a2901c1c1001d400d051b119804244200310310094a10191514100c2c9940440c040202070400001490103500a041c0001c52103118408040080355000007107880000ba102039807160340c034008001042200340d110034003469803d43c0042070703400030b2401c510340035042c45446400d00000d20b200030340c0000401002182c81e45411009001403002203911040c01c96101511841c00581307074901c0c518090702920602040d5010180e40d00d0700c00640480410b1940d0240c141441c044c080c038280403a615440018081c240082c81c02801080e00c0894000584040805e5011020f0034000e0301d55192800100801441507816010402034141a0105441000f840d942e0f0310034002040c80c140380a041c503182001c0f420038081c18059005214a030780b100046101980d10058091126207035202080703550003880744203c448440801070007070513500309011500c2254401c4003640941d8601c110156207182c03d540c0940941c01100444500c11115080f00600b2034080c0100d0340703880d95076039604100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 848478794 1250 848477544 848477551
    0x609110408030417031c14060423070513080303010e0603060906010317190804201f0c020a0303030b03011506080f04060b10120e060c0d0b0f04020c0d0f020105090c010c05030909 78
    0xd0b03581f44062000410300801c66000030041d182045410340010540313041e104074820070050071000340f0003c4c01d524410707012a091050f0780180d0000a80e0703180c3d1070715a250028020f583c0722420341000034080381030001b4007500c5010000010725059203107444903603450054041c480d242080c1000004d03880420f88c5840d051078000ca07542c20500749420306000d4080b886a0740d000c80c4c14040308168404603a50b1000e0800e605401c1c2c0d4a400041c164180291651240c2ea20000d410001c00940041410340681c0000f0800c0c6c4150300900c015400400602541e0015000f40c1c00480c81610204e052800440101d95101c0d2041c000010072107094000211691804c408410000359400804004000f81e8054884c1e00d280100c0100500d06005e64001e406000d00320203880a1035440c590407109541d58000300c3c1034514040c000310b584505000460792112207600007500031402c58400b421095205205452069071041e0240c01010008401154078280f000c1c001d650522040c000d206450340e5071010a0b00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 848480044 1250 848478794 848478847
    0x60d0b04021611120f0a0308060613170706050703050a110705030f1e0c01091211040f021209060114240d0b0307060f0c0b0c07060c0201060911040803041703 69
    0x2008000101004165215401c010704c1c44c0e0410a41c2100b0304200003003464165034141095000c0d0340d500400b00e16140903001d0044e4140381d000700d00041d0158603819000d4103450b81e405642400d0340320501a2414800c28100030001001003080c040014454000070300c80011000988002c0b83d031300d0340028500300000ca4200c40c01d800803031002400142101c08803005c0d5901d20058101d1802e4800060428440d610800c0c80135980e111841040080c401d0048844c00d200410400c55a448010f050009411945144100300111004200c08000021310315040340c80c100388000c8521403820510194034080d03403c85141251411701c61500034907100c0a098408a0184c00040c4074a00c0c0b02018130741043c0c0c0d03100b0401d00c40e038040c80c400c0030f9078071803810301040c0e4100c1c24000882d110701c01c240d580d612859030090110751a20444682d01603042d0080c10407601d8400c000d004070542184083c00521640c4104078540e441080100b00300c2120382c52041c800d45240c41942d0400d00721a01d4003002c208041c09051 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 848481294 1250 848480044 848480063
    0x40905060903181801450606030e0a0312060812070c05090408030a1503140106300204090f0b0c09100c020603130c0b070317090c060d0b040216 63
    0x84030600d0410241e82103c000b1121050f5050300703846031284200060040100c41c00c04078200100101e40308966085e85a0150907403000c48405101c202d010341c0820484d41d850600f0080c0015075070f0700c42d00803a40d103078484070701410312006a81c3e400e440524584009444403a01c4042c0004c10001c2404621010749a152010ba980c04c064503100d00d1170f030740c030340c100d40d204822500c24040031500101c283c0354400384d44600001c0c00300070200400780d166002e5100400c50702980650998260046d0002070480d02c0003000c03207a4803092013010291580c011104103112440074110000540b4182c1c00648695000c0c2c1da40038004221900c0340d42089108591024404034001001e08482c1040c207009000c10202d460480d00c03e40c001e50005041d8030000d45806036619020141500f44000d040340c403002000c45030b0703016981e06080d00d0054001580b01c82c0844805640c0340004003105004a01c00364102c100070310745840d0202e46120600207103040c04406401c00d5090001c8140560619202e0300c2440c020308004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 848482544 1250 848481294 848481307
    0xe100224011403031204030c02030a080313050f070b0706051b0f130602010c05040b07030e09070201150506032839030902030309060a1713050708030304050615040905060903 76
    0x2d03080c0c01c0e001010703000313030f100f04454550304112400e0f9a40040e03040c0361100b0b0641e924000203240150956003c0c0a5503c000140300d0b40101080080b40d41c14403c601ba1003c2c000e480e29070300e444815922465069000401c880c00020300309900456014040310300c0000c1080801c0541c1e1015004032101001d035000000707a96650b644070650f20303001041284001d000c6603d0300038000300140030301d10581d00d103420041840810035004160381c49960f1800b40144d402440c10380070080c06440910500180705589040105260420204a034803c00901d0640c0a08014140e620400e000c91810000100c035a1002d110309860302074078640c000798a52119500742c209640044100102150010705d0505142c1078401d0010788004c0261071030b202d01210b00944072010f0b03110a0380e00708118402160200c19083c1008100b103000040e0100280c004c03402c45031401e0b202c400345a640d00c4152805000c581c403900c00103044500744100c0c02d801c107078080e102050a565669903d0b140043c00d0b10300b400ca41e003000c80e05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 848483794 1250 848482544 848482559
    0x8070305060c0306033715060602151314070e041a06010903060f020405040204120309381204111c03080114150a080114010903030e10022401 62
    0x1240e411002d4004024510706042000954500e40003a10307403030326110501d450035100b611325000c04e9820219450461440100d1401101c4068000155008203103840d00215409100054101c425000b10741ea094054a4191406140d0032032014211b40307a402982546100c2c1c502400428000c144085100201d8200307841c1000c0f00080484100c14544811800c01400d681d0141d101411641c2080c000541e0b00e0f410340c9030101070311507500315070740003800000d000800980c0d0a500407100c602a42e255100700d03441c2c800b0080c0c40801c800780070940c007440e800d03000d60b00703480c0200308058010008422807419014041224450000310340a81c1e00e451142042501400d00d60011003044405140e6440c0c1c0c03440542d0050b04111043c05075030701c0d502c0c10704034000c440c0d141e8840052076420115400713511425030381d030300600c51030090261000014641003401107a5001d0040e007400d5a61540b01c55601401d58028070043c1070481a40307034114400c40e18009051a0540740381c0881040585480040d0340c1001c40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 848485044 1250 848483794 848483803
    0xc01060b0d0e0106051c022418030c01020a03080a020a030f092303040515030604060906180b040203011a07050c0a0620030708090d0602040b1c0b030c090a020f070c08070305 76
    0x81a0702422010b0344034040b9038910f110418406a04590f5003450007141c860f440c8544031008148d625003a00010b8620180010100405084100310210361000d031441d401280ca516203540c00070b001c04c0c05880400c0780c4244603005803d0390b07401c030310300003c64951300c4041e0b070f0580311525000e48070440b0a80a6100c0340d40e00c09180003060507244011440c0030303d032002040d150791081d0340c03100394031002001003161980c8071380101009100d81ba03c24000700d92141d50007015005180242e6503000d1900314000c07850b040c28000d1b24121500000000b040e940410400c00c00383d84100012a0280942c03107180180d81d07a00b04551000d04900e540e401c15043d09540301c4214001550710001c0e144d881031200600044624044a01480c41038413007040344090351030611f020f400343d6080303401e01500104600341c04e6034080011008840c1808003e00808002e4004c0c1034440109032401a088161440014154095078000307115480c1001c204c0d514007101350301d500d041100d80340c20000300c5400035042002400310410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 848486294 1250 848485044 848485049
    0x6080c0103090b063001020a23070f02030c0d150b031207020411070503070515160804061d0a05033105010c08071505010504060b04080307080c01060b0d0e0106 70
    0x800b0807003840d481c2c481e188140401081c80c3d105040804280c0401c403084801d44280d00141e000c01c00b040900c0103c17840c040d40010025200188504c0306016246441140c04103110400c100b00602c0c4c0344641e21076020b08484079038186d81512444102c00025241d10702c2e003200c524085c0510310749101c1c0318510309007562101d004803031080e409254900b040e07a44032070407507525a1f41210700003600c1c0c80f840142e42c12030040e140b01900500020a020003803100100c7e00c0c2404242c2220014484e55039901e085c6445038040e180240010180d40000d400a4450b0b40481c0c01d000c0304d042e4004082c40505243c40c0340504280303044032150008500080d0000010410300000001d10440c094880c254651212200c81705100b002d0406c0f0381d052034038013031221071011601d41d940c1100e1080c10700c3c80300c1c0313002c0d00282a00f0f100f003074052407408100040213140e02040e98292a54034001c2d5141810310b49a05105812030f1401603203655031003400242d860765220090842500c02400481d40d040b00304082c1c0d08560103503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 848487544 1250 848486294 848486297
    0xa06180e010f110301050d020406080d020a050105011d1503280c0e0f0c03040206120106030905060709060203120c0c06040b0a05090c0d020d1b0807030215040b0703140903070906080c01 81
    0x5103001e400700300035006485c1980e8003592100185070036400001e018105d40d40c004d416600800c2141001a1341c081854a48a8000c100034003150340d903450390f00d0003040040d40c4000c8111901002c508111036184c0b0900c5815402002c5810408159100300c004980d0ba54004450703004401e5041d00300b161480140c0010880c40000a21601e02069401000000104003501550001000804540c0d5001c203640450400e80004032a075a10748038041d008220703560701035806219031000541c3c1d80e846104060217554459001d10301780481040240da8011010f48103003403198050007422600300b4100003861080d0300400017050300341485140d40c01215000b030040b00094008040300c02250b1070365007042c06007507410780d000c42480689051000d10640d9182d83c503039980528020010b11038100141400c1568021104008400030b00f00a8851522039442030f40c6101030107001420100340248019a50740d01164170340c51625904400107401c1030032035004400a9580c07076009001c1c003481003103f0703440300704c0a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 848488794 1250 848487544 848487551
    0xf090204080a0b04061107081206040b130c170c270102030a0c030c0b07110c090f061908060f07110d080402190b04090e1515090a06180e010f 62
    0x5008825880301c004140180800148101050070007007180c3c03004082c030708101c0035182c54407d00d1a11541c25444a210400b44801c83d00101398039280500c511100004002c11044945140014031005841d00c81869020300c11080c03155400c0f0391010309178500c1103950341c401e60358417100d115194013003100320040e0040c0007007180c04071a0780da6000804c480240c00e0398100f04003052440d1801701c0c0d580041500080c0200b1040f000d01c64690b800259002e418881e030000d4030703071031140c0e0f20a0211039081120354494031201e100214101d418803841341407910b200c040324082c045441d0340e101440c01005440c80d1500c2c007800c00411600301d43c003c0c507600411807003401500302004420350081c208000a44081d10460850161140340030002c0312000091150025481e1590354514144000b080328100e0708615000d5800c1504240381e19070a0075110ba5541060f0b00e030b60600c03030f4041c080052001018a00241c0e65042d0210340014210000794404902000109581e00c0d0100c0345825245070565002c00c4505 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 848490044 1250 848488794 848488799
    0x1b02150a0b220f1b050a18030204020c0604060c0507051506360a02040e0708101a0706150513020307092310110c0d17030415150b09090601020a0c06090f090204 70
    0x50000844590806c00e00e080e000c13284078901c3c540d10303840351584000d5020380b000801e000840da0114859108a001e62002c012014140209940501c07030f54100501300e400604044070500c1c0f9880d101600460041c14450f41c2c403075810607000e400344106c0030000d0703092a405d803c0001441009900c2c1c0c0e1040c507698081d42041e142c02e0701320381031160103000b032004d0105d03e2000032110340c4042403a000602c0070170700e0b6800c021301500b407860b0964004001a20b4180c10104e41501503d13450040804540000d0312070101c0031904c9800e40025040540544100001e0742400140401c91841035941800c00000c50f0b032403d20030f00e003084040710102d5029410300c8490040d20200c0c03003000c100070308100350a84040003181c000303280c0040000c0704540d012018682c04414001440f490b4400c4d0941d00d500b52a0400448030300d150016100c03a12442011007810303003000500590309010035015008001801140e01340c404da6a6004c0c8070210035000440050759084080004030700e1691008002c04819004502d040d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 848491294 1250 848490044 848490047
    0x1062117190c030c061a1e06030c03040f050303040606050117161b1a16110a02042706020a02070509092d010c031b02150a0b220f1b 58
    0x510801e41c0050001c4101101d050500600814a2040e0701c200200851084040b0380110100052102c07401007442c00020800300307a184800d20b40c500001081542913907200b1041003c96072000b4000ca40005008204100241e0200b01850081d80b103040040307101ea0500000402103546556421001140742050000705010b035403451036024950325004107040040f10185c00251480c01c001000c0054118151014059405071540261947ca000500da502c40c1041203400995201e0f2800030383e004442d03244014903050340a96000340c0c00164046d60914402014240d9001e000720645009400041c410405541031095001410084031800d02900300982429130390100e0078034120007948030903040c2c42498015858189807003070340f0f0300910280340c0180c0018041c241280320303d803942418031030003d41da50000c54040d10040d080140d030b00550740c7d00042c40018200c94010342d03811803d41c8001d5a00900c0700545400075906012022840c035002510050889070103203030343d01c891903000b00c5000d41c40f17 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 848492544 1250 848491294 848491327
    0x213030204051b040f1a040b04270911040e1204030204090c080a1202010c080702030901030c030b040c0e0a0603020301060807030c03140a0c030b060903030d090501062117 75
    0x898050380e00040a41c0ca0322461407011a0744540005008008a40060103007000412881542d6851680c104070001c82c500f90100c0e400340340240380780800f0070310040c44111040c07461000b020508a020301541d401c0d2040450403544e0043c001e42e80003514103c01196400c1c00d008240d00744504000030034200740002d00c10701c0b0714003440c00001d2103142c80354222030504c040c401020015050143c19615074540d1803600201c1c40151850100c059400c154641e043c050081100324031a00d02c2d034020b5480c1c5404100114018007440c3c8140c0705055507000d0040c601d482e50b10804425540c540c13134440b021010001001281c54180d440b1204060042006000d40d41d88906480e420050906012800340903504041e800360025080f00642210790300100191600982c2040c04c91b000c503910304010807040c005c02d00a81e446103900664059008118107411590907510045c11540110000201c081d10303882d141c0c000003441980d1200381500f81c04070070107000390400316040300c05a80100f14038040100d074851144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 848493794 1250 848492544 848492549
    0x20705010f06061d0915100f030b0402090a03080702030a060c12060e1b070f1e0317060303041806210b0c160809040e0604050303150a0509040b06031c051207030213 72
    0x81c0310090101d01704052070b40e6820000c500007003440d2003c7e485104001c041c8030074002010002801c10f1207000142c2854402c2b41c1c91900040c04420401d42151501401980725075000c80c1c00d445072190160104003144501081c0008643d6400002d403c826182e00030f0314550f0700300690368030712401440012207103d42420724140c0d42c000c3e807545400003810000340d40342d032251014100d600e87e00841008881846800c0c200035200b501da2140300703004400c440340003104c102c81194041d481000180010508101249000c0a4958010492581f10039190f0050a1120301c41c204070710b8040b0408003006210302e4045e0b4005440002e250826102c5003c80d0001c004505011f0041400000c08580030345a0fa0406100146442d0440381030b4102441d02c256650300c211111140c94101c00f0807100c9500d0a00c1d50300b800c8410003001004030b074403581c540c0140c1502c083c107a02d078184a010501c05002c3c4e80e1000c40c0c01d850070305490b60754a0341e43c05c01e031003242d4000080c1907004040c410003405402040d495000800e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 848495044 1250 848493794 848493799
    0x50a080304060e030f06010f06080114030a2d0b0f07050f090607060b09040c1719060f0b030f1006151e0203090d111008091905030409020705010f06061d 67
    0x803603c41c0c960200e0b04010207000d5049660040c07500100344458044841c4007100d540c2c0ea5451241d80c1c0e5000c2c42a4000e11950760f16505420000c0601c011451264400450f8044100c842ca07004040c40421301c3d078011040421154004910200010030900300401c5506c4009c604000c0e1501030000d55446041c404c1d4501144980008103c00082c0700c10b40d80640608070010300703141607500b800e007001ca4501810344501034240a0410300c1804902010842c203140183e086224a41501203941c0c80380a4040b9030710300b04003a1764a004080c1a0f99040100448200080f000b5002003103411000d0f4040d40d1a681001c14070000625070004003030350100d0400c2152691010584035191034520172170540c1b09034403095030f11000d00b800510611007080c0d600c13401d000302202e00201c18100514207a400303500441e00034149420203c01007180c0801c0014540c20b01d4801c4083c0d03031400c0d466405120490704000c5003995140e6480e511122010424450a8094000b81c03c1c024000c0c110200d40004206602c0c40190 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 848496294 1250 848495044 848495057
    0x7060207060513090e1609020a141803010912080906060d03050304031403010603020c100902091609030510020d0c180b0a0207050a0803130902160204020a0c140601050a050a08030406 80
    0x2101048400b0400018025610040c01a005c1507480786030f94000c1c60001100d100000d43c00003a4070f855520840710210248d07101c81620b44040c003104a1140c21a0900031011030400b24490050f03a420300c1b483702400d10580406084c0141588020400170009001c00c215501c00c1d400e001056a40140b0340c4041030b03042c0340c41543ea54403842c0450b0312040311060450711000110020a40f6a00342d00508211642e500c210340e00b81004050300c0c0103413648480c010b500144540b001c50400c90805900d480c2c2d103000c07403c01e580f000f5902d503501032074448004140e40315141d01040c00ca0f018000d41c010b41c4003e4a0b5460803603445128080c00d0412000f16105442e000400025a010f07002c0c000e002d000000e083c02091103084661740d11280383c0704d41c0311b070342c026515100241000c960000c003031081d211780e00d004888199a05000b60b080c04000d50020210009001ca801080400144e02840f4005020f00440241016516200c00e2000c07070038441e0015071082c02031032000d00500c2000000c0d9400c80d105481c280c2e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 848497544 1250 848496294 848496307
    0x61e030510020a1b0506090f070f12020303130e10050f150307020a170a08010b030702070621051306050a020f070b040c0506040b0306030c0f102001020a03140702070602070605 77
    0x1a1000c0b66103561548101c44006131350707414010041417030f611880c0c1e01c2c0c1c2510a96501c2440e11a10340d43c0500544200c00d85142003840003043c003540c0351800d80d1018003228078010b600c0840e031407499450b07400312050a01c030b0010040600c0c04200030074004c0c0300070358000009010300000994821900300510041071000320015542a00c00c0100c4004c1e150040035500c0880c030301c2550302c0400d5020742d81c0000420840000080c046c59040204c070300c00c4910750301424450b420050126115040d07819108603840201082d5050a41c251003203d0240340b803404860243c00c6603250100980300b00600030b000e09841440f0a400c0076004004441c1a01c0e031000030059036580d00c5c038020401030a83c0d0019a008000403502244203202c483c01540603280c110100e6881d58261800c11640c0595030f03281c190031400c080200c41400d4010307222101640b022080007210381459004440c00c9030000d00103000082e440f02028030010902503071441d0040520720150400704c0c00c0041c0a55120042d2050804000001850 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 848498794 1250 848497544 848497547
    0x303031801111c06151b030504050a06031b080c071401110c1005010f030f120e04110a23030711030708040905181f020d140a061e030510020a 62
    0x185000c0d01c1c41c0c40700c0ba2298102101120115121100f0456042c5405004901ca020382c030741c102c2410701196903407400700c1b0800460540e05072280380100d041c01024800815180d8828a21901801103907800080b9203e80c2d003000100742a4041c00642841100d100b80f142000d0150220749100d0b800c10924680d28101074052401405801c081320034030f0313101003001c00300c2c0c040c04207145100d2442c40302d0a20030b69032203016241c0c0400f514070004100300e02403070340f2400080d520b0081d104038500b43e040406401e00351102007000e070340480091040b8000b0000d4042701c001c0c1c2001c0c0c401c20b072580051118501c00000000b5942c2480702508400502c0025149469821820800c03191220381c00b000300d0b0b07102caa6801608000d031000741d520007d20144607032401c03481c00002404c0380d5000c142e6011054a41c11b01e1304524001d43c0183d0f11040e0581c0c41c1c8600c000002a1900154002c58440f04002a9180780050302c4001154014800600c002014000c001281000980780200c40e00004010382e91102c0100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 848500044 1250 848498794 848498801
    0xb1f0b091f0804020307090506060a08040f0f05101811011b0c0e0f0702030a2c04090b090d05040303090902130e0406050403180302010225380304020303031801 70
    0x18009000d40c03079415000125900800e07441c0110302c264101e031500ca031141841c0c81624400c842d5a60800420312510440b10704c91401c60340c0250151400c280680e0301034480b1410355806050030307101030b8440c0114400e0300d440c0748101c102100917914841542e0744a980c1d0040904030300000350741001407c680781001c49258ac01d005a125500180c4401310a6603044454a0074104880340440c990465002444860012040314107441240ea074140c10441490420300e200d1150111280354048a11710061081e11640712b0035a007140907950311607051411141700e619140c400418002008000d1100f000000e030080c40e0081518140717540581c8817507400c00140b0348128294050003001d900c8030f00b40700030300000354012070045000360360b440c40f55010b1036054104010b1602c0000d0041e400b10038168040c801604400200e0b1100082074190039903540d01e011003810603c103d43c241032020003c14020f1140300510f9407616584000301508610301034001a03101d0000422005452440724817210a4000070760 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 848501294 1250 848500044 848500069
    0xf090721021306150905010f051804090302070504020f0309010b061608031f0b030f10050a030b04050a080703080906060405070e040c020a0209010f0501170405070b160f0b040b1f0b09 80
    0xc5200f40581440513005100740c05c64894640807405610124101910600c00c640c074190803204240c1200c1c0210090000030f0003c007074160210f000310240403480390340c0c038001001030f91010b031003540d00c03420100469401c4800c60f8103020b201d4601008100b01300307158103400c4906075401c0740e0741c06d13102d0b03071280180c541d030594100803940940300420f804140e8106034805180034041240089649558000c070100b0b5034042c13030140d81c0d03201000140c1000082ca0f8000700ca0f40c00380c0320304203a4490303865903500c138105c1d500f042c681200450429401c00c40701560400c00c4940c0940b0031a0140300504003003102400740008000c405001d40c1d00c1310050301a03d07000300000d054203603000e040c4c801c843d80d403402031850207009800759078002020300c41d00808a503000216580030b15001005444141d251804081269000600306120702024000c1e03607020443c40c41050900074018061144185403602c0c00e8200000020080e00340c0c81c000300e11403001019603040d10340503030382d4000a080e514459174002030010403280 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 848502544 1250 848501294 848501309
    0x270c030709050d0332096904180b09060106030c030e0303070e0112020307030f0b042f1216020c030f0607080417030f090721021306 58
    0x78043d0f0405610480000c442001801803841c01c2070b00c018240c0340c04204000c403c002c0641032000c4082440d000c07641c10320308000e03081e4900344816100108100130b45c1100001040305a9010041c04070000d004601c021480d0175500f03540700760880900600c500c011400c0540c00ba0303549442010b51800e0400d0340030754040c0c1040401445150400764a650b904090082c0c1000900f0001c860304080d01074098007440008c40400395003180d0346e90500b140c644003041912070422410346100c6242000520042d0b00955444e03070089081000b003000401500c56000380341e030041c0d00c2c1c0401e0241400701c41e4480c407902042c0d80204815900286800d00d40c900404d0411251142e110040c400e0002051820044080e080e800f030322820342d0000b0803d500c606910307141d007069030400c2c00041d036001d200e901041e80c0316226040c00995151041c007030103617540048441c0c0c000c3c80c0d03210061140154081000c6801402c0d4400c00100c0102e2441c50032400118505000303005601105220040030721903007207080070b441e22 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 848503794 1250 848502544 848502559
    0x809060424090f050a0c0807030c18060315020c0624010305040201020313080c0a060801030b07050f0708040602031c0c02030405060c010603062a020304050a26030307030209270c03070905 82
    0x324102103440d000c628008071005c01c3c0c9010000f41f0304401003214400c580c0c0042214100c04e02d4800e1205000344030400b0343d0f801c140d4849000c4002141180c6410350000d4048005890702e6004034035501e001c1e00a0b0a070001890503495104c13030420445007400e503080c000c2c0383c0440c07103455520060f49140194405000f04071100e0801182034000061101c03441041250050806951000183e0b05100c00f8080506000c4c1c45800217200c250141d00148140c0e0f402130303841c6d49880590740343c1007802e4100f41c01c08030050b000010303804035220020202c140030340000841001401c00b045406956842207100d140d000340383c0401d4249103a04203502040007150481030900c807840d1340725540c8006200c5561900782c02c41c41c1c5214500c0040c03000090f1002d40b1005040c0c11034032824450b100c546d0362060054010810051100328244030b01c00c1c40518080c042c151000345c0c40d140c0000811030241f4144001d80701da013080620001141c0030032451507800c000304068480d074984542d1011240c1d0741744e0750080d070b412122 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 848505044 1250 848503794 848503823
    0x305010e0c06490506040e0d0f020f01020f120711250506070803090607020d0c23100e01060b160f05030417030d060510080612030c010f0903080906042409 68
    0x101d01c514604591200404c002940d1071900b08011200032014401150740040c203000e81c80b50003589500304401c4140100d449030100c0510081c00e903030142c020500c0b5003d01003416040d0907040482d1a801440d1fa09002c1c1039000503900c00b565404802680601c40340c5d002d81303001040d801c082442c10250001034101d940c0c0726581d0912164952040d00d01030342900c44e00c4002000240b0108100e01011225a0b400c1e44181d0a6102c43c00301d15100701448811500d003024540003000d007041820342c0a8180040426080d00b00c903440c0d400c49203039500100c89888108154500c402c603800306a820300e03511540c4d1258520403400c00301e01c4d6020b9600310036144c00403025078140c007440c0040074143c1e0001d450030901a203500c41051002001104141101280c40d42c4085002c5191030071190f02d1503506202140d0610310611900342c01d507a00c002c001d190031540c61a2010074991300152007680508440020412401c1c03c0d0b42e803e441c00e20100074100e051809003203406000c007854100d81c064903004007031104140c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 848506294 1250 848505044 848505157
    0x1e03090209180a0b18192303090114091908060c071a090c0618090c16060b040b03070f030b0a05060d0f0206161b0f05061204020301090b100305010e0c06 67
    0x801640140c3d044078800c20500f87c0c1c5264510188008810383d4051400e01030343d0801500c504506482001070b401c028442900586c031284c1c02100e207406c0c60082da400302890040800e040501c05042810790310001c020302c0e004242e88a1802c04a0400101c02d011560703542c10040c3d0038281e18440150f40310200040d002c0a10340e00401c00449d01030211800710498594610090031b034800c0304103034054100510090b00c00703d4080e9204400744140940045820030802c80081d04203603a0750401c030b04115650f50140244072103103850950000341c103e000c000d1400e0443c00941407034190039001f403030303062052010000c41d114041500d9485100076400094400c076850000c68000d820b040c3c2715407000c40c40710002480700c60000203e0840c1c0c000350100c0e240ca6045e9410303200000008106a0b0550749650f00000000c505030401489640501c0040c0316507811450a1801d5802404032212640e01260491000d540c07600201ca0b4110f0800111003403410040fa50000742e18000e2610800c4807520318414045107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 848507544 1250 848506294 848506333
    0xc0c170d02010b100e0405060f270606042d0305100209010f030501030305030105060f070b010b191d01030509100e0d180f0b03071e03090209180a0b18 66
    0x10080d03900280705041c80d0405001049551000c0a000605070b1403245c045400d195000c150004800380903a19180d50400c085042c114408451242c461074502d5002021213000020039000a421140b2a107800e2030565103da901040b45100850140ca0300e59020030104a48803400085034000252015000701501c910000d42020030341c540400d401441d807000c0503200f403080a05995168803010705590810f014491a50002c11035905060000c00081c0b0120b040065014020003250000b00e13034441a554400b1080f840c6100c00d8001d10183d05103c0010001c41e4080215054080ca8001030580d42c480700c2500e00601c0034107080c80940742c110310b015451382c00310761000668002d442c0c4501c40300e03414074840c0071a1164030403000d0650700c144003808100c40500085402200c940b502641c2c010015004c10240d0507489803900200e55a01c082008601703194902c5a070104002d4011010b20007070089080d2103c440036001018803c1d000b0004040411104911007410801c00481c0d400a92865907807221 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 848508794 1250 848507544 848507563
    0x4051c1e020a05060c060c0c010204050d0b18030a0c0204090204060e1006090b0405030316020646021b0316080a11090c0406030903090306020c060f010b0c030702010c0c17 75
    0x100b204180218003414000c04481200e18004000c0450340d4506803104810b030048038040034555020040001c00ba034604010001450151250940b9401c042c091801c05501c2003c03880c0658005000d0321035034681216030400c150b50141c8010030340c80c40602c0050018515604810301e690342c3d480601003002820f035150341c15180c8549440d0421358583c1e41020640c003a0380f0686515a108004840b103400082441e010064405001c0070300b490000f00100142000d923280b16401030303800c61102054400c115800460700d552403044e423040c03440e0805000f03440b00d10394a5002011035619100710265141003010f182c07007200e0990782010301078803420026210068a00182d442102c45410f040c072500d071458000c0d001c0d01109182034545454000e040c0d010b0110404240d080c171580c00b41c0007011507038030b0005200310031030fa002501080c502075900700500881a00921081c41051007000244600001100d480c9902405d00380744103401d13441c2850400c940c3e03402c014400c14800d013002001c120001044880d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 848510044 1250 848508794 848508799
    0x7032702090705040f030206130801060b0309071e170705030316060b0a060c02090403020709021c140f241201090c0b0a050a110c04090c050a140604051c1e02 69
    0x1496103441c6030880f49405039000314528841c01407010001443c20300024400d9442203030110a071a0741c1c0e0343d00c20342142c45952064181550000801016840034045034000d401003200c905c1e1124000c0c404165001030382d0141076025800d4aa106d109008100301e50401000001c0880e86d03604c00d81d6007254500076031361104440050138039400c49031a162519441c01513803201d6507105008400c58003000b03510382c4060401da0950150741e1001c10503050b507000070001407181e15440c0c01c1e46035010440204880c510010b9040001c0e880c024031079038840900c1c0b01c50700007510000c01080007101402c0003904c1c0c40c81010840d4410300180f00c1d10144a01900150304040c02a284002a590785d041440344e1441150070210005008016210429000b250101c00741142441154000e100000c0800d0441c0c0000106843c81c1d0300c50542003085140444681c400782402d010f00d06520034009022640a00460091038402c040400c00c07124007013a201c0000130442d80204e8017503521500c0b21000341e01800c01e803000381e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 848511294 1250 848510044 848510059
    0x2206020a030b1c0318030b010b0a080f090a0311120403060e01110403030c120c320109021507061103010e010305060a110a08060a15050c06070c021807032702 69
    0x15140703003181c61032120f8020070070b02c030080402c20303a03049038802441003100700c00311804540800403034460810386000e4161080690340d21221800041c1000000521200b6001101410003596402c003007080d01c2115414203080505824240005081c426152409000c11001040000c00d00540c0d0f00070071029003070400200b00586d100c40384040b0501c12400040c1c041502c030b040100002e0204440360b04001d825181168074048140d40d9204540c103e05121020001689821101000c641100a103424001c000811107080f05034046070399184d40c0903800e80a140041240001d20005402c410003120009942a95139a1902c1003001140c074280001e032480d21030000050050003c9201c3c0d00302c2e03094101039850070940400d400310342d0603a00405a03600070601880c00107244001c50b585407201c0700540c403000e4030350300d03040115840c040c4011302d44020040c154606802503198208a030b4658a05c114410501c0e54400b9015005043c030030b40482d0025000c0e010304c1280c1015500c0310304400e0300c206d1307540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 848512544 1250 848511294 848511311
    0xe0c0f0406080a0821070c11041e0e0f031c0e030f19030e0d090303030e0a0309150513030303050106080f041707020d140a0318030b010501082206020a03 67
    0x401121494000e00c010795000e0b21481020440e10405400500c0c0042c210302c030b0420801d070445d0310b840d030240c5400000c54045042501007040300d0f441612040410b9608103d484508552442a13542c01d081d0407010b81c0c0d41d114001071b000c20034408500b070400c9031402c4039650302147e00d202280c0c4a5004030041c02c1441d02241000c2d0210100c100e80d049400c1c44010760400042c602c90041e0004007003941801d05941d050080102c01c0140807416210500ea201c4038121451070402a0940341e80c0380b0b51a14030b07000041c1107000240c001400b6070039107216a4200703096010060301075505209032010030034800c108410010402d40d07d0b03042103041e220595070781140380c1c4a204d000d034000901918001c0c40382c4054150350a021298001800065000504032020100113031242d040040c8002c1882ca0540c010011400074941c1156001102002681c22204000d01c3c584405101c0403040c000c0c607040140c0b11001c508000003862210f40d00d000319600c510000032413840c10400039400307002940007003030501018 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 848513794 1250 848512544 848512549
    0x180506010503100501061d01020f012d1118150301090218010503040201020c040c0e15090307061b0b07140d050f0106110703020d0204150e0717150909100e0c0f 70
    0x444d0b0485241e5242d04660002d040da09001603600754205038118820780b0344003040200240500c09403c2d150f04048110082e515100d03891361810400f03030141e601d04041c030080344400341504031211107403e8082c644402c41c1c108006032103444400c80c8100620004000400c0103441380e402080444500d03045038103001d594400545490108032400390240e04940303000425401c0c290000d031101d02c211324145e001d400c555400035000c0101009911041c040204500346242000c100301c9014251901b44121012a00003180c0705084002c480140f8030368600c004a20043d01519131200c1c90b904003041c0a45411a00080c034009180448500c05403044041c00003401e207010b4280324030025040405010740d20300b181c09019448080c5401244c003d95213121424040b030702c020301d82e8050701304aa4485000e00f851f100080c0b807448a4038501000341060802e01080e0b080c0b43c4e44201c89d00e0300560310b048103580c400c150719017811748a0f44140314603800d0801c3d8403040c004c082081017000388122209410b80304240306 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 848515044 1250 848513794 848513801
    0x708090a091e18020d060b10090503060c0f0d0911120114070503060337050706030621060e1203090706260606030c04050409080715050c1c18050601050310 68
    0x782410740f0b00071810700341c000d420400440245a8081d0702c010514280190100381d20741d10550f10000000e08002061001d894240402c40c0c1110b401180749040154000c4458480e21414021a0490380d41c0d0401d8410414109480203a129005004604810289400a020340410520303104004c44090020308101d000b00d042e24040d000150060003510704406403494414040750f04800c2600340c2000082c1d4110b442c016100d01503100b1005468040c2c5064409002d8455a4100d200410b42a1200700721b80e580c1c101703c030740750281c000d0300108200800d035802d281060100f00d0118504e610000c02c00c080d210317000540804a600302d640c0c0200055003d800c51084c034110030043c55100001c2404280741c1e14101002c0d580084140003075078500390341d90000504a03981c4020403606a0000b007800301c280100c0341c004080340c580308841030040d0316007455040200e104130507400706000300c10704102241c0f01c1e59500c12942880d0503407001c1c450070042d08020b82d8034082486070307074440d105a001200d10b03c8024007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 848516294 1250 848515044 848515061
    0x180b0a06120c200d020f03090d03050904140108071706100e0402060f03090c04051623040506130806090a0c0e07050d05070e1021020708090a091e 64
    0x280e4525558101d44800300191142145140401030105002d050444085504048411102c00200550200014042c1c01c02455022203c480d8006202252481d1104105801c42342d906103801a07554030309000003401001140703031100c4071404420021030380301700c001380a0040d100041071200380490b64a265943e185012039926054140d0540100100d19501c01e20340d400c03a100422150070701c5ca030348e20b6103100d0b5002101c011a05c1e6000320016200d40c1014400d60741c0100e0b2642d81c24254605041e00941042000300303007032085825901c488164100d524080e9000352400910195880f20300440e016800c040a004a502e00d005150108100c200001140c1e01c4080e840307600001e81501e0403030403e40c072600007401e1701c1c1800b100b00801c0750114514841d16200b250305464099440c13004030306106e03400101c03000d0f400921014103c1d00f4810b944a41d0004002c49401c00d026a8441652a000c0c10038055584802c2d0410200c04000c500d1004c81c1d00405541c40d14920180ca1804080700342005803000342c3d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 848517544 1250 848516294 848516297
    0xc05190609030816150501060305010608060102060f06040f2f0c19110d0b090d03020408150910020313110901032d021e0915010206010b13050307180b0a06 68
    0x601040011080006002d114041141c0c0c040c00300103a131076066040c01071501741160310742d80f040140072464042c80380d0340c05841e0600c4c0141c254a49040040d5490304003134100004000c035003001a9550360765405c001c01407180c1d0b14050021261100403440320b0000700d001010700b0380224480c5640f04001809541450103c80000e02d4a8510f842040480102e250400c0e42c200c4900c00c0b203040e550321103810042c07003144142103c08051800320030180c180a05001d0400c10940100404c10100340d001400d2921008080c9000c0c01e00d4aa000020b803038410940c0d106041a0700110800011001d51742c98121024068007803030455940541c10422515403d0000900740074000b001010203600200d500309c44400509401d042c912042e400103016050f54129000031400840120813960412070200d41d0402c1c40700345c401408070b000c100007075103d00050041610030780c004035030245c002100c208544000c0c207000d030940d0245130715504c05000b803003d400080800541002c51490803804d0600002c4103c8603103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 848518794 1250 848517544 848517557
    0xa030207050f0f1c050d02040323060601081602030403050d0315060201021c110c060f01050f0406030209060609150a030218100903140a05030f0c163f0c051906 70
    0xf92106150080c182d004a1307410031a0510106e82c1ca80000e00c000c101650240c202404464000c0c0315a2003006410341a1100c0c640202003807102a0340c02c0103200360403101c0001001c0b10204150300492543c086e551016025100317810021003001c1c1c050703100303c5140c00c004207108403403519131105030300342e1080841d40b144016241480c0c55107c2ca466208a1440d80134854991038100b040c41c10601d004410340b111944a00c4240c01013005252075028001c02072003d1700c0034000285190000740a4510040c2034500031140050300c409117549559a81e600c450242003242d448416004005000790040d150701c403002040303040d420801d40b80c5490003d06074200b43e07a0381c190460465441084080440d40c100d034640c4074902a04001803418005048450054070255803a440043c115030301d403010300f040303082d4858040d61007403010207a00190b807010074810030310b01801041510050b00603000c2500080b490100010300850030001c0c2d03900302e8822184111240260281ca00030f448460320214031940b004a00c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 848520044 1250 848518794 848518813
    0x16080603030304050a060c050f130905010501110604020d14030c0c030613150c0203040812130504110409050c07020a060806043b0712080319111c0b03030a030207050f0f 74
    0x2251f08500700289032454201e0800d6001c802600050300030401307800c010807941d0005e00c041c400c24424503004100920700911042e22051040b071700c4010281c0064000d5007101c00101c1071203104000d07034031070205840131641d8441803000103036190015004028464011000800ca44030b0081c40000c025581154811500b103c0d607821010040443d20780c103006501050200290410043c01580c0883c1c440b0755169607070705141c10070300742d004c105500014070603450907c00b011016803003415607081d20000507000800340c4801c41d948003140184c0c000254000f030001d0020508507031002401e4040e4806a0f41844030010003005540803000700480700ca070100f0a198104241c901810181080c0c11414095601c1503441d503e2400c0e00d800c080c081550032000000c280044034a44000c2140c00884c4040c040044098080904882d442811251001c1c003d807008100340c40d5110703034001340ca0244014110f9640381607910028000e508004002d4480d0b008202210115010100707078041c4206403840a0101c00c0b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 848521294 1250 848520044 848520053
    0x11031b150f1005100c060f0b03160807032d030f17041e060e1506010f0203040b030105400b0405010f061116060c1203020702012c0916080603030304050a 67
    0x482404003001700036048010a0114039135220780307035030a000d050000c079503400702c542454038214500b44080981c000e08001044440400300b1780800380c0307911003500a18014203460804003c802100d0b00c00714207100214140425030001a600b00c500003580720400700e2184003032007006142049034080d180b20030326030049000030ba48480381002244902c9000410103003400c11585880625403081445032002400e2100640c2c220a00c000b00c4022032006600d000d0428554554500061244074081c42c1026031040114014070200c00408040340310316014451f07405080412520842c0e81c0f001310524298004980c2d00745809200d040e03c0000c88040c9815182c44011502c1354010001002103010b0035041c80b0f2204e10a030f00700c00050005640e0311001c0c076424108143c4102c007039203000051610400c407590060343c0000b020410440380602c030984c201e02042c681041041039041b6990b2040c844c80c108140f00b121500684412866591256030956038182450f640e44000d40740500141c0c405030350100001c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 848522544 1250 848521294 848521309
    0x2242205070b07150216230f0a0308060901270b03030a0c0c08010c05160201180e010801060e01081b22020301080c01020a0f1e020a0612050a1b11031b150f1005 70
    0x4000f4840040f8a44845c50100703023489921150044140c000b4000391051550000700c1540101044500000d9545440c41e0380c0c4036a003000c0e03c4d500700002d208400c1219185240d000585191005d03094a55503541c107000180380042012040760403281c2c80c08041481c2038140b20310300845103662940e91410f80c0f04c20101c40024101d0000301e04201704814410204a4401100d80040440c070380c3d581c00550510380200c0c01d40c1c103283c115450b02200e80c40100a00000012190301c031000c5442c044000c3c0940d40041035507603d1000c4429507003683c590040080340402c0d8001c0d41251100000c1c0c4135071f90135207030049880305007170000030b13185046600f90032020600f00c1801e50304d04144046840c9005100394045170300d05c0840c0d803048001c5003110302c07910f0700c0f951140035080d480b0140e400c003004514900d04c40c0d44021500711800c001084240c42d185a481501042100c03991410150300304088014008200d54803882c0390032070380e100386001c03021030701010842000314060700c0360340d04050a8a06000c24003011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 848523794 1250 848522544 848522573
    0x204020d110721031808070c1e060e0f030c01080c0702041805190210140f0f0a3b0319060b0102242205070b07150216 52
    0x1450380d6448100424080c8400902c4950310a4495203112001e03401441c00050300b00240d10280741c2044d480c400300076101c03c1c51070303075160344074109584846207800d004d00e4902d0190000e403000c12046074141e45448020412004031403050b55046c1c030349203000b4240b00451040c9246950158403110301d0010541c065480241d1001c1002c2d20b070340c100300c2c49400050503140ca495030080c2e440ba08d0514141803000c203012035001202004070340700100071240d02217036102d00003120f00320070800040800391a008682c0c080340c05100104810503103514501103104030540c0a0903149010442c4c100150b42481102c2c568004a81003680750101a00000d035600014005080d040e0380c0c0c580501c501032080406181c1c5d20580081c000c80000890761401c500280c6000c50b0344030100311552038216541c001808403013099511042c0d17854545019260a407070040d8404114200601502500c0004941d200e0040c02a040c401d008e4038208a1003e6111000e400301d114202d0301884c00380c0c4030802c000c0882c0c0c1a9141408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 848525044 1250 848523794 848523817
    0x50402091c060204051c030e0103020901050c070f09060e07080103060b0d050a0c150207030b240a1d0109050402061e0d0204080a060b030609030a0c03090b030108030306030d02010216020402 83
    0x20040046445218840c0515022610b040e40032405002a04100201b003041c0388009a6a03c0014800c3c2c0340541241c0d0508001410103130001042e84841c0d110307800381e03000e44440344c040314000394030303140c0c070900e2f40e4520b010300ba0b115032070110300091081200f20031070f014146030340754104140d096885420190010321041c0b600940c403040c500300099010461040d60a0080c3c032212400350500a0103502613070000c01c07100443d4441103041c00071821a50180f80c00550071010706825072038880c5c1c004e4030940000581c3d40c0c01501044002071082001c00d864201c0201c445010480d41e0b00c0340000320407290140c401a402050610400c10710403520310080380981080001d80781080040c2000c2c1e03050343e00c186c21590940d0080b030100c100b082014042c00d42d000100318007071f01c4a80741078004031b9a00e00038040240300300000d4100002c2850f0003800e2240243c8407908074141d803582c552114560301d41c0240d440300c1c0644100ba0a22422620610940d0300450121100100907440c0d80c08100c00707500011071440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 848526294 1250 848525044 848525059
    0x91b2d02011401170d02010614061c060e0a05010e01060804020d060f02181e0d0210030902190303020c0a06050406140903070303080714040f0e130b0403020606030d09080705040209 79
    0x100b0003040940302c50090141d240d41c2c003900c01c8486811420182c02101c0c1c401075a0419900340102c0c46c0200840040700c1050352016141c00c0962541d190740c410380301c0840f0308140707010000b017000000b800205100341c86124003403040ea660340e415124494000d00c29000051000d20115005190011100c0e0b000d80c050403000c1b400b042130300d00050403a44581c5500c50b002c10b18584044c0740d41881c814207001c0c07011b10300854103d01e900f080031964400b00030714001e10602d0550781c20b400050007640216141070b00606148a107219101c00b103a48902e032400150050b1169213030740e12941c5014121081628040e5030356a08081c9400c0040c0c03207840016518014140084c0420b007a40d44080000744015030080d510010581840ca0b0068003010545807421220b00d4200310521511003940c2c500004c4901d0980c00300c00968038450304040580100800400445142c42404140340e400140e09008034011802c0d5111015090700948403034401c4e101c1d0f040190442c00c010005407030241c1c05006241405400380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 848527544 1250 848526294 848526311
    0x10c03030f060f060306080c0303031602030c0a061a030a12031a03060a0617030a0c030c0602040504050a0e012304020d02011b06200f07060c18091b2d0201 68
    0x1070a445894000396181d81c8503160410180da814080d41d00146401406823014525810100e038403844010000c40d0282c07100305007661000e00c01c03c201c41490030b0000950712449140c1c81c02e03102400491442c06680240a4208655858080b492405240e1701154425000034600d605074068504810313043c101844101d6254559102408040c0c482c2c0c082500000d20035082c13108030141a0100d80c01c0541d182d20078007240b01c50903000069084000d80604100f49640c1031483c1000280c0b0440c1c00c0150014101003d2005080e0103800110500c0c14180c002d1000d1501c1040000c640a1140d080505c0380221304082405410005c0681e848980189081da82240f9a0703003401c00010031f408000c4400e603a4400310780405040c0201d84840c5203041c0f40310076143c070104000d544a40c1c0074102c03029010a42d620356940d0440e0044040380000803d1407a00d9500c150303695107041c010b0006440d0301c60b0a0003840e4401d07118071310602081100c80a014140301a5694004609460034141581e0106565072100309 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 848528794 1250 848527544 848527571
    0x30106170a060911192f030d020d0b010f08070c1e022d06030103080706020309070320090c091f030b0307030b04021f1d0105040b0f041d010506030105010c0303 70
    0x418207000c14944003641d4584408119800d81084081d80304200481c0350b03c1110199501095000728581c0380b9091b881c1c186c2d1034407816056208240c07600070041c2c07002415100448440e0080c0c3c60f0b01c10700340c076801d00d01c1d44030500540703078090100d0301d402c0002e8031058401c0000e030304480403c2c80040c0303040c102c00070310426074042000e400000b941982c09460580d06441076a83d007015840340c400c0c041d510075083d945035503500e17000f6001d0408010507151700440002d044600c100201c000075900b00a5240c2100600c60900840003140c0801c10b005c0e0310000001104082c1e24400c883c900b210140030b40c03070207140340b09040c0459a010b400340020140c54001c802e40c55601040070b0300285018200c079a0103400c092041003c1107140c88081034840d40180355103030149400003001404113440d43e414044a458550040b11180309a07000112007180c0800d5240c41e00c1c04041c0a002603030f03480c100d1140c0180c0308001090303a0300c13002d100c0d05912803030810060106510590aa0005a01c42c1c2400b181c49140941e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 848530044 1250 848528794 848528801
    0x503181606030e101a360a06060c0215030712020d1a010e01080114030c04050108010e060105181605040504020721050a09030f30020d05030106170a0609 67
    0x440390000782c407541c1c08110f40c0024081c010100c691820b0402c84c4170300100003d0f40072100054203520400e00c210b290150512401401c0303d0352a510340490310a003070200f80b4a800c0c1ca40680e02022410b140c034201040d2180116101109160010100030303101950b2045525a40e10007000b05040207560b4850034a20381039030010303103410105401d0104070804450246817805804645c1141003020581e000c82483c0d0300890514191401e41c40c4401c0301081050120340350403402c0301515005807a003800007030392070b5041d480000d102802800b640c805990380c00c01c02c0344903600c42000420b2556001c001ca07900c507442000702d400d08200c506219007400e56a000090482c2c0040790244d0350f071805800710280c56941e0305800a45240b10341460f6091220400c0000c25001c040d001c028400d021140e4a207041c0003028103000e00a1204200801d44010508481d40c1c1140d6200c000070090320a010031074204500600c1901e06841d8141c0e5a112113003c4421010f0160350058011690150343d68004100c2510300d01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 848531294 1250 848530044 848530049
    0xc12070e030d031e150b0a0e0909030702030d12092001300906090503130f050103051e270c010e0a0e07112b030f0c05031816 55
    0x1194804900395200625003003000280ca518105494140420b01c0c2c08500ba08405000e050b6100011303414080ea81c40c0b0422624036081001e5030013000c10300d84001684000c00c0040b802090301c98148a40b682e200c40e690f00e01414100070750607046180000c012900c903400c9030282d0381d0010000300d021030b81511010803074205400c002c0c0f01c80e00346150074034595030850008080e00d0b500710102030260217403000003843d4803580e00d08c241840e6110b05002c010f0240f19000280d07119003110540baa02c50300030010005e0004944030b803404850218000150030f60280c801c1511071201204020003044400c0e07174201e100800244850b8a050002c074102400b1102d0a9450a18882d108010302c1403903039102c0090301e58003154145c580b080b07441000a0204854641140b40c2180316401c2c000c1c0c100345001c8869017403103d01d0104003609101f18205000c0c0d40104442c2d81e0000460f9202003010542198a2006a413240b44051020030820808205a41c1c0302510710780c1120162420355401c0303040060100a0840315a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 848532544 1250 848531294 848531297
    0x703050337050a0b030705030705060f0f120f01080a0807032609010501140d0203030d1e020d021c0c020d260c030105030715090b03040f02060d330504050c1207 70
    0x79010404843e590744140b51600c00100d0090400354a001c0c00640c8c0c41d0f9107401014058240850285900040c003410f9820410314615000c1e142c0302d07080320784401c01078100c402800d07002105000041e091000305100310803039000459140342c04040d031410383da40000c000030394030310700c400c00481801500d0010041c3c0c09400300c1c100201740307549804113050201c212805244c0c810100c42d0880d03030060b80c1c00012102950b12000340820781880e203c0c118a485c4808500b5804454000100c0d01200807a56008000000744910003400c00c040e003144181c101e0b408010a0070250303118903280380c2e525014400c0500c0c0940d0501c102158081c110007001d003074640541e201c5182c0706001c0018403039482d05001000284c51003c204850002010000501a04092081c03010046000000c00d0a001021907001002d0350054411030703032100801e4a580007803008050200760154191409401c5a00c204288141071074109054404181041e040000815001c1d1118240720f404000c3e48440807500143e90b803085915 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 848533794 1250 848532544 848532551
    0xc0b070c0503160302030601050324150a03060605030607140a030b0303090a060c0c060c05070605130b07050307060b061e03060f12030418050f01031101230702040b060703050337 78
    0x71343c07040c0b500d41f1006801c4284030382c02101c541d0841d50343d0b1041c0d00d4103000d031901000b00c40d62241686081e00c0700020300420b8000301110400f01c2840071980064080300d0381501107900503581c022040303450500700c940f01c0300c0040e01048500040c2d440b0760050b5196480040540e8902402007001416026807a403101c0b010501c0400401c0c00d0012007807403040104290308200789101655035030240c50381c0c403602a54040c8900450b2061803160f400e207603000600040180303250b581d409810000d540c1c3d00442000c80ea10b60510700c085170340f401c16205480815842c10805007110128044991254000030001d03a00258290790082c5030b83d0707440401130042d4602e28040c5550340c1c01e05c14402ea013000e5004a8000050400c428450f8030001d541c0b8090449401004050014554400407103526205640d145143c001040c10b00e8901307008000181003641c8200d9040020101c5041400100c1c0a5090040c02107802400001e0300000c81c601d44403810b40c1d41c04c4c12854945040e180c105085506a1809580360b0b81e07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 848535044 1250 848533794 848533799
    0x20904230a0510180222020d24050105030615090301050f0105100813231606030b120d0e0d0b0901020703110f06160e1509100801030c0b070c050316 65
    0x80c4040002c84080740801d2010220582100825201c9620001e01911991b002000101c05001150f414200040002c0d9a58030001d00c0c0c0c407029000c41d8030444c00e021107190b15005116400310031801143d0060316903908590b28502049581510303001202c089000c100500e1308656001c0c8907440c400c4103444048c00c0554141000e01004403003541e5944140720150041c403500c0e10035072150030100350340300107807221101c035422009031440300c2e040007920284a4086e18a07951100c1000c04070035901f0a9404000102c401e401b004280b448030100d410315600500300c031032441407141c00038001c0741c50090044000c88240381d1380d482c2c40c4482280e0452050354040f030184105903220076440e205505150052041c151640280e6494103400380bc450f1082003140c00c090394203402100c80c01c100900c000c001242e940c2070b08a041400b940103c1845104892858003c03240b2401007104a060300e800045941070305040818035840c82d80601d401b56054003080c000014190b804100140c0c20400c080d00000740d051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 848536294 1250 848535044 848535053
    0x1140405010c141801120c08091614060711090f0a060b18010807090f06180f06090b0d0b15070b1b0d020904060e010b0c16030f020904230a 61
    0x205454124403c01610400903410700441405640b40d00c8860840070019501820050fa00203841c89407604620b4101040560001e03004407915101d1031920094a0502e040170700441446805409120401e00c040c451040060a00f50054105513102d94070000359440010b0004902140c103d0707010a20100500401019043c070380910401001c4422600340bc0000035500c0103030304020307580300318108071550300000c502c02e21440c011801014500c2c0c0c07194085480d051300030100380081d075001e14201ea03903c0c000500744101030b04c00030844041e0303911783c02c41a040c081d41c2505c1e5844200c58940c81510785d0781c15015565194442a40c0704500c00c4c1d072503030b42c82c06403400c400d2140c40100b0a0000013003c101c0b00740d07042d0303850341186c41d5107001802c016070b2141018000b500800b41600309a00381440a4000f040807401c00006144091240c0101c0d11a000b0300c20b040c0c418806240030050015041d1044440181000c07410290068031a0360b0818008100190302e491110300c2c0c0a03841d079190f101c03231090008d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 848537544 1250 848536294 848536301
    0x40207140d03021c020d0f020c07061806140a0c0b0a0603050c0f0f19030512030609280903200304140324060d050307030504090e030306130c110114040501 68
    0xd080c0e07003415400c000d10303001c03000000041c02038504c1c0c9850700040d071002c1719a0f055115032a050304000c021510f070140e40010f295601d0140c001d04002c2440d105c84184880040d082160450340b0707030fa03100d01c0c01c2002840d80100e0b0380c004003001d00c03e0000b0708110000050301d40950600c907440c00c400c00a0018a1400c2652800b1030f5100d025014054100a2a44548484c50910441103041d103404620305050003500340c0c0152035601c0030381240141e003a07a000380644c1d40020750040030111003451007030300c1c0c0324900c0f40e080d845d48400300c652400003880d01d100e021035a0402d540850090414810540401400000c2141c1c0450660741581000409004550300c2d1944d1410b06d00082d07005268000420700406200c0c80c200601384015401540000c64550300c0e10401046070b5407020a913600c500e82031030017400300e4000340185584c0d070b4180210750f00280e0300082541d2180000400b000600094076002c01c00034142e2802d52000c11914800d07040c03003400f0900074040883c0145204518600c3d1500301603084 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 848538794 1250 848537544 848537563
    0x60b0628170f220c080c0a0e0702070509070c14060a060803040e0a0e0307080a0816030902010c0f170c0604060510081e100501080f010b0f060714070504020714 70
    0xc50416002c0c0442181195456980141080c1c00c040480704000c90301410f011280d080241500b60036080410060400b04d004000c07003c043d41c85001d0113482c2e5403000a14041143c46a00690013800200300c1860700e40b201c01e4200c08a802c06000041007910341ca48841058040b40e02c1550140040c00b20203c0d20340706a40041c00500091810300e4101110075910f41806080003070100c0e143d14000310002001c6c400c8680c5a40d0040e5865036501116101900c04442101c161405521524078140558001c0c080e000e016a8169585c00c2404001d41c1c2d10061100f41c25403c1d50591050342e6002e00d00300190f00106403001ca00d0300140700f01e1401c1d107845000d81d40002c1c540003401c14402000c2001ca1030018011240c6108102402c0000c3d1445079000c0c90300c0d800304d9068a041d4208400000d20b0000802c00a11400d0204000d1125860b070b0000e0240c481034101c07030f41e82c000c4000c0140101040200541c4c8060808040c1981d101969400000e42660003448083e0369100540210182c03080d8104a600712 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 848540044 1250 848538794 848538827
    0x1209061005010509030106080f1b06030c04050d14070801020d050a090209010302130b0a0f080c03010c05190302040801050903120f040f0b0702030d090308060f0f03030403060b0628 79
    0x40a142a400103a0195818410141030010220b501010344c0e40079000b200c013426266080358480908400f20740e640d680c1d20120400f5544401040c0e280c181082c0003140d02c0303070410f5211545400d00d810103210003002c4c58a0141c44400d203110300e100a40400b0f0109000400c4028005a262003412000c42c08441c8068486096940b40a2006005880306100941120780407141400314044040001000c2c1c50258042548020078620100b10142c40016500c1501e003000101e0749098400c8043c5030884508188a1000c81d0050082042c00c440500280000040a28015007010356420f10035085d40c4c002e40d14420103801c081800020708040b001070642c01003521801000505050311a10014100d41c0c0010302044948400945564002c100701c500c0301c250b02404214020fa1414024484a4242c40103072242c0ca12103602552480e10003841a540d06005000c1c40c50f0074510f90342c0700020083c0c1d50300907411480c203004041802e64000c3c0100c040c250050f9032440d1801200400030700c01d03002449600c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 848541294 1250 848540044 848540053
    0x12010b031506030906060904030507060c050310061704081c320c37020a120c0c090c1835101508100b030f0d080708071e051209 56
    0x4144c03000042c846410890a9802c0d1402e601c450404035058031071813601070304181c144024000c42940c4840190302c45d10a40d101c40d419961500011a65448004030007880d1034000d0380814081800030004104400302c1c0809881d0300741d00003211000b50f481030f01081800460b94800c0382c1201d260003c0587c040e00958204643e070b8502852001609d00400f81980c01586410704040419848149040810052801100410707160344000964500c0e00e40000c0354410b2101c103590046d43e000b0007140403500c2c1e01c00f00f41c010003410944500010702d0324200c0340741041002c0c8102e04104000302c02800180842a4942030300140280b0100d60780d00c03046019a02c4100c104107902583d01c000320340308501100c00040070481d180c03e00c0500581e4200c135042103036140152096103100c00c2d640c0d4481141c0c1002030701559159400124551744802480c51141e003c80c1114002070303080da10540c40142c0c045000d0815555540c541240c0c0155200080c540760089100015001e106003074100895920000032402031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 848542544 1250 848541294 848541301
    0x6050310050d0c0e0901180819021920090702150603060f04120903021005040915060f0503070302040902040b0706050a06050609040c0507050f010603030f02070b19020312010b03150603 81
    0x100c1e2680e80f0f44202150341204001080c103800003174005401445004400d5802842d050402d50016400001884c2100380a020440c40d010f002060110314400201810900401d2a80312110b042500300540b001c1407524141c1d0640c5503440e80c01c07003030040460364020011411034030503042c904030000e40311074800c4d4007810812040864551a040e4025071260144405a0740c90300180ca170355032107400095203d01c10209103400180d01c500500212144003a041c40410440100d103426194103014080006840e0484500c42c0b034002c2000315004155854010300d4243c0d6881002c1c100c0c5c00c00c1d04500306002000030740c05d051104070702550303400548000003045840e1030800000c040d442031035180d900880d124401440341c28004c1068488560301700059070780c211008483c0358024481400704a0115090754807001070b403840060060151152000b2046c5000b142c90016000c0b4070b14055503900310311040060440b40801c0786a41c500818070107908075120301301100800c0c103407010031030035030701400041c403c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 848543794 1250 848542544 848542553
    0xe06091503070302550509040b0709031e0309150210110d0e0a02100c12080c0f0d1509090201021203060a1a07030e09010e04032706050310050d 63
    0x198040fa039048546034002d0140f41003079032004070411240401210342c80b0720441c4d50481c500c000b0007110110b0303c021400c64140c890001d40e400e00e41c01150340003916840001c00048500083c29080030003800c14854803660303a80e43c00106440920409071070f41c0241c80c0c1100b016042801c0d1005488001c01d01c000010705904001d550343c42044c50301c0d46d01b40c0ca48a44680e030070411006c0340c0922014100c103210704c102498076540d84120081040b070050741038041401a251081c100920b0035a8810340c10b80e00100c400354100c03142c507005041c1c2d200c0d00340100240000c1c940d000c0020221242a1a00490380c1c1c0314154002030f6000013a0b03c40c002c1d4508000f0841e0050b07a001c0f440544030300c1440075050700c0e40c0318280030460b103035103917006064101895041c074400c4614050140c01030070f00c00d0340c03421080f5803500c09019400e00700b0b10500300c0050700c00c3e01040010380251040c2c0e10f11002d0503000303100394401070a0719203220040c0c1d021201241340041448298513a140f18000500019516589080c110742d86 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 848545044 1250 848543794 848543803
    0x1101030f06080d030c1e02010e07050d0206042c13030f02062809020402040602100f060f060503092a010801080f06070c030207051003020d1b1e0e0301060e06091503 72
    0x1d40f60308056540c0d440d20401401340704419212517403e810b043c00c4450303905001c0e000b4007030098404054800d00c0b8000500b490170340d40c8801000d07400f03054241003620b0003903081000403613004da285074041314104500070b4a02031103800f072051000903901090070929003009030040d0a00d0750f507101150400c5003040004919178400d0302006e038050084802200300e01c00d001c8020145c00200940c1300b03000103000134a1603800203066a49400740401004a09004802c1c8001c0b85c90500c50108102c030814810004240680082c5501015000582d040030b0340100118140405044002a03043c19240c1c401c051940d0200100d0b0240010200420a42c60100409969841d00410301c104018100102c0300401d031090204000515015101d2015001c0e0100d005c0c010f074200020000c402460a528074405200b14410324400b481241c0b0741143c1e480002070b100700b40140110000040c0001c0c0805035250f43c42c24464800245110041100303241040c000700510210041c28901d40100c82c4400010f09a40124 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 848546294 1250 848545044 848545063
    0x10030b060d24110a0c0c17121c0f0c09060309050604020d051c051b0c0d0803060a120b0105030c030303090c060714030a080103211709030c030301031101030f0608 71
    0x7242040700503221400070001d007001e00d400c90112040030500001c1c60b0b401c00c81200c0b0700703803046295045031600c8080510400340c102250f119032344d000004c1c00b0f00103178800e00104460031806480c1204c0144050074070040c0e91202c030f5110002a51600d01505150f0f000401d00e02601c5d40b490184840c19145e2a041e41d42d040140c0301a104414041c801d2040107001c20101c0c50a6004c1480c0e50351610f02d8000203030007600b12480340e00001c06601d4070f006807010040307640c0c190400300904039030100c5400d0b114020150401851180c110b008030f0030100d2000c403c40f042c1001d1a104072248240e0b507040500703240c180481e109100d40258414414007003070306804564101420010390f01c10b038840702f00e4103101c1101000d4411100b643d010003e440300d41e41ea0b11050540c142c0e0700801c00c14103241c400070704204030400048601c10000c0c0301907800300e14007803c9901850700004031404403401c01150031860303411680700f80d2003211316001211111000c5d5816025040081043c4101040703c9440e1840c00798585050344c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 848547544 1250 848546294 848546333
    0x2415061e121d06040501090501051608070f0e040e060603120405090a0203040303150305010b0907110c010e0604170a11041407030b0301200a080a0218062110030b060d 73
    0x212031200b00c01601c0c1a0310079048008804070b8409041a0030903600800001500355a95400c2000042e00001c020010441023603075a66104400e41c0e0314101154401e0354a002d0200b0000800e55228880d0f6650280849400956010317210a00740b06041514288103038404030071410061004218030b81d9803030034040c0e2010703900c240035a603543e982c46e044008041c02c0840c0a0002443c40010081c820b0540c0100070400b01655503c49907281d4801c15908005d200b21500480d5100c0c9050307032255441004480300581000e81201d00342a2600c40382050003030362040c0c4035080e60082c0354030340600c0000140244407403001d65040141c035000c100d088050060041040c1c0501d503c46a0902c242d840c00d52140ba101100446171802000b40960000c00547c403003907150001a406401240c81e0500354801c84040c00c0c8455000c9a0220b0010180046900084e50007000070701043e0244650002c40b0040c01d01c50310f40002110b50450952500308415400074000c0e502580004400f64000f456807102c01440040a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 848548794 1250 848547544 848547551
    0x302030a11030f030112020907021b0f030c120f0607050702010804032001110414040203160c02030a05030a0905011e081801180b04061b0203072415061e12 68
    0x1d842e185214450390030205110000001802d50155644000664401c981e44444c40e00c0341c00040f1b0b943d865404c400c00b802c0c0d001c150303640014944119005070240c809810b54490700d4200d000030303494064290b4690400e802000c1450100351043c80b0295001415040c0b0a042c1a00794000030400107006000409002c4000c0c28024403c546181d45401d956640000f4444641c2504040b02d05800138824202480134070180d1408920f024001c1d41d01c00e80c1c1100d030380110240092001c448001846c01c09030b07014094120307018042007050004101c482035545501462a243c0f038001040b105203481c10301201080052140c910551050300250009011881000541240b413106c0d4010301ca42c15108940d0101c008500f420001e2455005220b140036402c00c021400b0302140d54211b07074002d03085250060308100560400503641c0e8a100c000440d032120581383c1d00095041c2c1d0070480710b2860081c00204c5d0502c0041014552011404803076000550f00208035201c03211000c4e100202070582101d01ca602c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 848550044 1250 848548794 848548817
    0xc0b150103180c180e0606060304021807080108070f0303050d11130905011d0601020601060f030612050f39040e0706052101050906041a1012060906030302030a 70
    0x1180d00075100b02a90075800c1480b400356440c08101d4000b1621441c10300a981148003140641d05100d51002841d05c50081c0000d43d41e19001c003c0d20f0ba0005000301d070310510010781040440d40072060241b1035000d9841e06955541002045440d00d05c9503071121065540d128000c1c00000c1e0b0000035203580d20302076a004503070040c00c10000461070184900c0d10441240300c2c24001391000498009904840b1020100300d1507420600603017518031b90450300c0a0140c0c0c4140010050b0710300c81c204501030440c7c0e03841c0c005003407505e0b086076610141012909645070382c0007041d4036680c0ca200b44103086003156004d0340341c500b1414910310b1604541015281d80c4600269008035030007a2299003142300c484c2000c0c3c040c6c0700030796255880038003075403ca01004c40303200e400114041c540009040c0da0b58162000182030b040c1e0750361200f0400015100840c144480700e02420203d104607200c01e6402c6a440c0321a88078881c4007403400c1021021546503900205c0880c1c103145082011035001300072034800c9891442c00040c4881d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 848551294 1250 848550044 848550047
    0x1c0c091a0112150513020901090f03020a0b0d0b040207030305150907020c010507021828050c0717090a14040b09010b0405010302031f03030201020d1a1810090516020d0c0b1501 77
    0x6203d40e005541003213a00040d000781c03030003980c000c2401c140e09072503810005480c1c4141200c0320321103000c000c1d04804028411701040341000060864000c0d168000300e00e0340445008a800ea812041c0124080380c2c0b50004c3c4024408002c040906802c0140c9201c0154507200400942e298401c22001c0c1c14010005031ba503065440d0b80381c440810410040c1c564005040c01d52900060448180b403541030080d4034010b45145007075601440340650a180c0303186043c05083e841c3c000c100804400e10b030150000c100090012512109000402405200184003c241545e410f00c803e48110b1100c2510926210b40140525080b5800780c07029580300b843c2c01a16903840294240803081900c00280c0400b034614400003c065054000342103000080d0014056140d07446c0b0004141d200c960100d5500040c9042510405100d484071560300c591150303210f50205a882c04c650b011168141c940c0700c581e00c19461a1113446404103c9144410003600d07000c0c0b100e250645400b440074101174061a10285914290810b6a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 848552544 1250 848551294 848551331
    0x603090c03070f0e090604030e060f0c0a1506080102270604032a14010507031d041a04050603030702130b0a05101101060602061303050304021c0c091a0112 68
    0x140c4080c08075145607854181031400030702d141c402c001800b41c40c070000550407a008034407180126070648071100d22a2040342040a15004201c044a200006020040b450501080f10414540c0911640c0203010302c0543c41c0c02c2501e50740d801c0850b02d60300401c00005249800300c2c0b0700102e24180b8503d6904d4084000000320f6174800d950025003586444040b0800c0500700408441d01c01081480c1000782c241d5880365299484102c0c103007103010410034041c0c3c80c08030f8090382c1280c0c0c0030641d400c00403104514140024045404003403040d15440e00d0081c05040c0340c205441900c1e04817108070021800c025482c0d00040790000d80541c0d100380280c40b4903c00b0100c1d00c030120342ea005080000c26080d201d01070b45200500903c018503080f0919800c0100000350030b0300224a00303000701c910b150484008074640c2c9054540d0b43c030182049800ca000011000b035025a40141c1c008150b201c0c0410042591402c004042902e01100040f0142015101c00b10282c4e0703000300820000040110b130105901d84100d8420080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 848553794 1250 848552544 848552563
    0xb0a09060501172a010e04110d061d040b070c0c0312031a150912151812130e0a0e010f05073b0d05070e1e0402030705060309 55
    0x14280000401d00e0303007503c0c44480010411004681c241d80310803a503190494003141c4a0084c5a036852002c410301e500c1842c0e0568441e6020b00003048104c2c10203d072036081c1e40440340700a91150340d8001849400001d41c0004140e903005900380d2000d08240d10b825811400260010003070080044030b0340c1c1040160403481c0010360b0000009000310b0b88510015002d42000c501d1802c0194404091844c0c07440d0040a69464034440ca00c0182840100b10078070601c03549108454845116a000701c0071000464110584640361040002c02c4011012080520301640400f901c20b0000d8103114088003002d41d07018090490303410240b85440d90b200d48402200911000404581a500380055407240d040d654116501070143ca0382d4840c0645880007116014028800b803000a0040556030000b4281c217281350304400380d00c014411000c500060303850314545069948800524280c5104124408443c04180c103100c1c5048101940689080c0d030001c0c2d221045402040d21500c004008110094420004200ea = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 848555044 1250 848553794 848553803
    0x323010602010b010801090504030c03200604081306022808090603102402120703110f0703030306051f08040602040902040e01080d1b060504030210290604120b0a09 72
    0x145584a1a000340602007203400303240480c0520b000002d000501e8424107200356059600d143c0001100e541c119083c18039150880034400d84000341402004080c0b2610307000f0351203224130956404154416400c10030f015400541590002040e1005210741043c0860315907102500403522010a85800c01840c003491050a0b000790700842080b0743c2000c4600c4000985034814003250884210104031203803000c04a074a2001600a50300c8030840380300c0000500000d51103410026104c034407803484581b405201004449a81d07100070020030500d5054803590014140a84210308107100c90003001000c0c11006039010b00300807516000405101d402d40c16503001d060061825941c0d0303070380c03100d1480d031448080c0a0458a4050303500508820340c01403512440300d074040200501c0900154480fa4020680104150f056010305d44035040072901c184120940030002d240a03e4074141c1d0a1891940346030391094150041008001c2032001d02407003070b0340040840d405888524996a0088441e000c0e1602500040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 848556294 1250 848555044 848555111
    0x1503050a0f08071a090115060f110709090807110a0e07111203010b0406090b0702090412032a0215010e190204050310141005060f16050a050f070503061603 68
    0x7026006070304d0154040e8158100900014140300f14030000c1c04014801d280114502684140302503000711042c1464500c4001038852081da40c3c1004c400307603420000308948100d030001b000303410051490741c440320312031043d1a10012641008550041d09030701801c0b42040c4103415241c141e00000800c440358190301240e40031912942d580b848040c0c81d8000c0d005a6000c581d82c0c200110b5581c05241c00e455030103400a040038400e446940b201140300c81465846000c145c0c9409038143d40d2010409915501c0108040c00c21290310320f000d00a060080c0c1d4070400c2c825120007801013103d0005925010b80180600c40205100a2441c00d240001d00c1954030090300360164965505079440340717038015400c02c05541c0c0008801d13900c04030394441c003000a0041e180d018106104070080e91420b100038203030504800201c1d2a0030852501c0e03d900e840c0c40540200c0b4181c0c0a0800d2109691041c4050390082400f50010042c6060805000714108030907100038040503030303800e50a8407880c070f06117081c140c440f10b030015003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 848557544 1250 848556294 848556323
    0xc1703011818020a06080a1112071103040e01030b0a050106020f150a0603150504050c0306130b060f130f1b200307170a1814130b12101503050a0f0807 66
    0x5052001d0842e0001d4019141001e409014412001120145c00408501c1c20380760750f50038400cbd501d5802031608501c140c4020720010a08044c210840c03400f0398041c1c182c0d2052881c05906800503101c050f000401190030100f4200c0e56090000f80702da03901d14100c140947c04c0c0ea2120442001011030303a0020700000d48030920810440c4071a4000f030300450040d01030307518000e62101410707566075064030300c0703582015000d80b883c000c10f100d1100c0380c2c2c01c0301c0010b103152803c0c5c001ca000681c40130301c040303d4500b13803990350000c88031490a40d2048810302802c1180c0340324003d410440c0980700e50356008491420110301107102410f60b906004407009594040700e03501c1c22480d0b40d110410280c010400000124000a00c8a80001020500a006c89280c429030003805c0d208041405411156610120702c51a2a407080703115a50310300030035909080c80c1c00000c0c08006c8050407498142c07050f441841d81c00c0707280041e09101048000c909040d2164014121001d400f02c3c0745813a440e140702c4c2410292010401e031807503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 848558794 1250 848557544 848557547
    0x411030c03190b06010806130e151f060228060209030d0c0c05060f0d24090f141b070516031406250e01020f0106060c1703011818020a06 60
    0x110980c2c0d0340030b00440d02c4683d032002c1c01521046e006a88540d8455648018032510217030a8129201601d1003038251071184445110100c0080d03401d903020b40300891102c0480000080403440c0c8002412244000c0c0f003180800910100c40300200461035003010b12542d003d50500505404440c0f44d600c1c0642142c0030348694510080c8120840c500407944500c44100001e0a4580f00d41960603500c80941c099141100d080711250081101400d0190044045105003071000c007038100d0200100342550012401d40c0302c88500c501140d80c0e0703100d40b2060044600c00d012008040d80c401104500015404503512034007818100c1c9008490132052480484000020081100b00e2003240c0c081d0000104031800c42d01c1d4185a5100794004c0c0d00c00324404c00b100400042810b200d040e54190100041c01a254115248a078031401c2d92181d4010f4008209554500401c00c10300d4407a618000200e001342604550410403554401d410800f551400d071512019090070400c0c1c121100a9495801044550f415958050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 848560044 1250 848558794 848558833
    0x1508010506041202300610182f0316081b13170d03060b0304030e01080c0913060e01050d030806010c06140f0a0c02010209010e150c030a020a02270411030c03 69
    0x182d01d5100d008101c003141d0844c010210f81c0d0103071106101020380440389846000010700c5c000e00340111260860381007003101049403100102c03224468275002e942c1d203082100e07100ba04c04801d0113601000800c00030480c075031919140111a00c0c035505000790303aa5041c610807080342c0d4041d41182c160410076251354a0203c80008130720700400d8154074180a0aa5204000c10590004942c06004540740c0115a64650310030f0282643c00f18a8078041400c1c06000f1004c5103444c05011504070b40b1a40d11340090040100040d4158014000ac94002407801701075078005081510140c03071b160601c50100c2e0380300d0401040e90818040300252101c1d8551603d0480c8010380e8039401900d001517550b180c03040c540d04c12403060007100d440140c1a124440070102ea0001e000903002c0c200140007454105101180c031006040c0000c05010b2038580c02800c5840f071900410060101000081c540058250741e01210143c1e040445c0381d0183e0001c40c43d01d469040c0c840402e0034214050300d031039818090200315410241c03959a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 848561151 1107 848560044 848560129
    0x80304020907020f12030a0e0d0203040b1804020a02030901031109060913021204030206042f1e060a031a060304170c0c09010b041508010506041202 65
    0x132052070300b001200f69044040b0140041444030030702c913500900300c4562885000c0d21200e489594041c0d902e02c01ca1040f603801c1c1c1004030701c049110960b4500c2d0504505c002d0001d569588202000a40705c3c2d20040d54a03020903c2c04020b692920008426900303c00e0b8054021440c102c0d11404010207140b00101c942c0c03409408005161700c01c4641d000050040d44030381c0040070030f0b040500d000d98680481f03034034030410112803101c52020f400041c034449501080607100d0703000b10401d80b00c42c6040c00ca0a145400d0304484005880c01d01180d0590020039020010f8105403030980709401044800d00c070548018100030300c101113411711140310b01e0080c1002d07a1850201c944602155012031039030380d0247c0c0304503c01900441c0c100111580e543e440c18215a9614228200d58140b40000f8a82d010781c1c0141034a10940381c0041046481d20b01004521a0415942080d42e540c1c0540010b45240840e = true := by decide +kernel

theorem cover : BRFrame.Cov 848381294 848561151 := by
  have h0 := BRFrame.cov_init 848381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 848381294 ≤ n) (h2 : n < 848561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
