-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0364
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:26:10.665095+00:00
-- url     : https://prove2.me/submissions/b9208652-0622-4e48-ac38-442016262dd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 65287772 ≤ n < 65467628 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 65289022 1250 65287772 65287793
    0x100c1113020a08041e1703040519080403020f100509090c04051309060b01050c1002090a030c03030201050f100b070215070803100f09050c09010e0a17010209130207032f060103 77
    0x500501c42c0c801c5d01074400c100e01c4c8400905040251810404000030001120000021900140f20342c0032201940e410000c81c460074410104180c0d1003400c040340c100107506003c4d0000d41d4075070046945281e0b2424002024101c1c2c069490404d00401c903e40015075880159400c40d8050140100428a10748401d44804040c08250074111079403800c10f45000e1041d40640c054801c00005540034081803400038180f070000350406000305500002c2b000c0c0001c08244419034aa000e1030090780085038515102c03071424420351001e042d4a1081c100304008000848200307090322a9558119100b00f604008080750200d980120100546248030010922200c100c1029415086880c100351008403e9919045001160001c643d03a0041901c00c00c1440000d620502c48c0009102c002080c0c2daa034243c6540c0d40485000c1403516009540c2e40c00904032602e4600340600d4140720b80d41c0b100a601c1c094465900800c104910390106010000c0c10031811810710034422401c15994014040396110341e0759080c9000103a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 65290272 1250 65289022 65289031
    0x60a09050f010501120201081513090308071806031802060d0b010801080a0f02040b011e080601030b06070c051504080d03020301090c18060e060705030f04030c05100c1113020a08 78
    0x144190100e07500300c0001030195a040f1990440d824400c542103400643e42004000d15000c03010600c0c4e001e40e00b5a40d20004928005641160300042c0c00b00c15140c0034044440c0940f90b5070503c00403080d0310b02805244010344064600c07525000c01e4440032002603942c002030303002c0000d50060307010800024005d4107600c0030103031400c02d03a00e00041e666180c50702071310345050f940040c4c4100701c1e100740c1c54054105600070390180c0b14185032150051640918034030010096880e40b00000b401d002c00d2010075071f810300900040480880b12145803044582d5880c2c2c6001042c03087da0300502d181c0e10701c000100406400e40340100250000d588542d00700c02070083c002e5000b401808445840d104072511844c2c803e076500e50020842c880d00c03614182c00c0c40c10540302000c0703021907d64450070400c81100020320078030281031031645806047d40c0341c40c11858121580c02c3e450300183c1c054158400c1c0c021480d0f5100c841001d489800c03941c1402818402c0d0003048181c5c10b415802c080d443d0000580c120131981c8202154402c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 65291522 1250 65290272 65290283
    0x60c33010e040308010302060307090b0a03050423060a111c060305070b04030816081306020604110d03020607030213050607050a02010315060203070602090a030c0f0806090d05030a0b01090305060a09 87
    0x50380c0320000201d06000964001d400210810014001410200000d5811095504102c02c6190341c0750050320040c1d125210050000fa250360910041052090729920b001e0702eaa00b42600d0301c01c540400541d030f900020308c0d0b41c105c01d484807521400c20880c0421244152109007011000c001404148000f904d006e00c03041312144608540018080d14034401c1d2002c0d40d5100900510b015259004071001e44000e07002924002c404101c44080541f03c0d100078001008160042c11140ca010305000e5000342600581d130380101c0b00b00380d2090009602144841d840301080c2401600c61071413015140307d44016030000381d00204000780a40c1030003000500d442020380700350e07003e20030701c0541d051480404120740724010140e401406035000103500c0750043c14030350710090b10000502d40d07242c0326168020703807e0344a03158980407223009103c40c05052107501d0340309641c40c006100500580354002c1091100915501840c8c5e1390f8490500d25a1045a010380155000720440705030303042002c80d42d0002c1000d13a004648 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 65292772 1250 65291522 65291623
    0x29090606041503060c120204080703050c060f030f0711100203011e03050c0d110405040305040812130303112407020d09030c0314101e062102060c 64
    0x600d072501d4001c25800c100b40c1450301c020701d480e540d01c81000e031107240b000a09100c180080c8000703803400c61019100401d0054001d0076002e03d14100300307003003c1480703102c44d000b4181000104a901200d230101da0b000448005055015070b69161304442e00395040c00032030150b000d08441d00301410400d8002d141614001144144000c0d515400184903155910000b8000d40210862468030319085501481260184001e804070340b002e42c002804456040314200c000c21808101031141076030800400031604a018002072400075050003113440301c8502d02c8002d080011003076451403040018840d40200c048200d13050403000040700c01c41c00307801e1800c0f10004018450991140d070780912800d600d5048036048070413104802d046460300f407062942d140b0b030a0022710030000100844103a2740315000a161240b03072003541c00300d418182c240641d8050380c030070782e24101e0700c58001d0300d8103180c1e940084059604560099860310000502ca0800e004905a50851003260b288107a42c00a4541800c80130100c40f0261103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 65294022 1250 65292772 65292781
    0x17030f2116120b0a030f05030a03060b130909030e06070609021201140118060f080c0117150424061106090d120903020309060708070606060207080a0f290906 69
    0x20034440001141100041c41401d140b035180320035500400030010003802180c605522516282d955a00302401110036600010b0840b0070580d0511400000d0301e25144050302d0280404a01e030440c5c0e20030700805400f40d41d01c016010806010301e403012000d10020b003900341c60b62010305080c00208804001030340682e109500750345c040308042c410003440d0700c051410010700d80d00308480e08890100015005c1403140d41d400000c2070030200b40d00038400a040f000c0090050740060000106000081e0600050704800b4005002c022101031858500708442503070300090f50b54941d4a800c0700d00b070910b16220400a04032001061160f0302002050002030f4220840b07549844002ca40c0e66a00c0d0070003404400100d441511480c401700e031f900300c005554028411681445c1090000802c0b0380d10040c021964181e00146540800c0b01ca4001c0f080208540c2c005061a02d140c5500d440d00c801801d2002001e603e50014110104005540d40e400840c045441c1c160440c00460400503080d40141d8421400d44107000000c0d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 65295272 1250 65294022 65294041
    0x1205060102032a070b0c0a0f11040203040c060207080a0f03232106090f0103021309050312040614060f12030403060501030803060102190201020309120309040504050d0e01030605060417030f21 84
    0x2500741000c03860040c1f10686a40d100c13210f4254090004484201009140301410390ba140080c500071070186118049140c50f004020f8034044103a40172180b960007545410000c00d18810108003c10b4050504010704a0f00e01c8031492141c48040340f21400760707004900096401d64072a40c540102a1410111440d80c45d10801c012510034200d911140724003000c8010300c0181011070030848e2079034100300e001c203000008d56196815500316a09880110580c1c2c0100014400280140300c456414401014941e08004010076054400790641500030350010705005001d100420440b40190740000e010030255850b450402c0d11035105582c01c5006200c0c248221240403030700c0207100015641600210301c2c00b001da40510030000f0032105542c003140001c4c0104213039616280102440b0394812000f41100062011b400b819481180c14010f04151401d4020f000540304c41e0100d40541e0030204200a801313541b281d1113880d40c4141e0051010702c4602140803070104000d5444c1c9032009043c1e954450b019910314015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 65296522 1250 65295272 65295277
    0x1020d05091309020d08030702060f0c0315010509120a0f17030702030d0c1106040c081006080303062803080403061a010206061201060b0a26071205060102032a070b 72
    0x141d01c00c8020350024018140c03503100f407a569202511442542c1c1064032100900c0c0c0003280c507840560400c0f03040040f0402040b1007290b0211030360000500f1401d00c0740c00800c9142e06240403905104000401c1d034420750300c0350000100c1c0c944450440d00c1d6800189001984003c09220480348800880035003600038070303800b0660f80305205a074021402c01c15a0407000c00a04002000a402d0090fa180c0000340e198041c03144601c00c0e0b00407412201400c2c82d000300b43d417420542d00c3c1c981d04034a151078014010100701100320313038001d5004c60340100c05008120305141c2c00801c20081c26801e20601c800041002100f00103003040300d0040404005a1241c6800c1c807101081e650074003070050304494002000f518142c0031042224810000000e92292103820041c003a90210960381c0c08500264480d8401080070010080410100e082c078800318100000090140468074603030018480d103510010300c443e4420415502c416a00030003000100500b10280408550404070100d00c80c0038454012035103240d02800c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 65297772 1250 65296522 65296537
    0x50103020f1603120606020607120506010905240c0d030c1803060f0609020307020f07080c03030313050c09010303030b03101a0d02010908120405120606010c06020a020c040903090501020d05 83
    0x70316860120150070701c1181c0304485030b0440c20700415421030381d00300c0307040c3c8203030700140003184c005040d107041400024050004114403140030724109002c000036a41d10500202c01c581003609d20084c1222070f086507030720442004007240c0900e000800d40070b103a2000065500c00d07140980c1c5041000c0c400e9914101c5114151407034185d0b4010010800b00300143c955885035541c03a01c00302000804079240c0b181001039a105803000710060b800140350403078082040c40703d040104940002842e0303202c0d15002003a124000101401545c1f184641c90405000c001d104495200320700a0000c4a0303036850307244c098014071079803085038028401c000350b84442072103612616101186180c6480d00000c4010200a034150200b24200d041019050340020845020000700c0100164042c1043d00c2d82d0038001806107800000c1a00c9240c2d030f0142040c840f0326600440708a500a800040243e07039072141c0c5106034640070001c0b2040b074120745065548410300d5840140c10040c2c0d8001d0317091b00c84040001d401140c141c040d000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 65299022 1250 65297772 65297797
    0x41407061d010512070302030a1107110103270c0e01060e030c061602030615040c1409060304020109080607020607030f0c090b0a171e0a050c0a0809030c030d020d0605010302 76
    0x40e8606040c50407a0212011090145082807400722654440c0700710303c5098031860b002c00e4000c020312076228100d02504240c119051806410180c0c00e868101c540a00307040b640d8180b550b0b6420784200228072004039a0700769011407290b0059015454840c08000d070b188502e81d42802894004200070b44102503040919030300038000c0c228820100c0402c0b0b104e502200050000c0608500240b00503101030181501c074408044c03c940c5c045184009000070340740c81000c2001000791802c0d542480c00a8030040d86e80400b82503880540f030b6a1684016103482482d608940c809203e07003410001c03915030004080b03101d440150703802c1c07107450811407400d03098030380389200c10011540d1200c0030b01055001e8000782200050320319000c858002521008044c4200548950f000900401441038011941452440e00715801d060304000d5840c1c800503c000340d00a134003803801080100070100d202044d0802c140c0e440100f1440c00e681c0d681004071007240095004e481c0301c101c2241130800c000b4041d0b020b442610394400441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 65300272 1250 65299022 65299037
    0x8040308062d0a080d030501050a0602030a0c11040b0d080901120b0a0504050a020f0f0406021612080705070810021b030301050108040b0a090f0b040605060f030d0f0c050105040b04140706 82
    0xa003402d880380910302029604242c51480024909904004064040d401e98070f00182c254144414050540190782260040d90300c2000fa207201076500c400d000c0c5101d07800000300c41500303581c0300000b006840400800c0d54402e0041170340c60244020a0000c0a0504090f00d40f0810000107003c1c0038260744840c0705c034551002400c282000141090b07040320742c1c0f05824075070042c584100c40b40b403003e49800c1001101117040c1d01240c240300c4c041e010058042c1d00d8000c4e0380d90040f442d103444004020851411130043c040200425820200b000030040c04000c0c1c04020f040d6031159034100c2c0c1e01c0000b50002540091031000c0c554202c0031411003c800c9038140c89040c3c0d02d46960b907595031542c2d0f00304c060140c850914a03580e80d94200c0811030140310200741c0c0344a00188a01402c01d420454162100030740343c14800c4150043c0c3c0306056030009007070004d0b04154103000810100d008010ba8071450000d4001c1d0865081408103c1080f0140810301e206a101d498101d801c1114844645c0c0d48119a004850128504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 65301522 1250 65300272 65300329
    0x1404050c0306060a05070b09030301051201140402040209190b0d060909020907030917032401031802090a0b130905060912040303140c0a0c15050c150a060302100804030806 75
    0x103100030aa11404d505103507182400310394640b0310303440e000c03220152141c0000c0018040c902e45660b4030410851604000c1c86100c11086a14800300b0010b48000e1103a42c0c0096080c100e0340b08c0c07524119050f102403081c0c02c6070039992403c050b01584043c1100c0980740c642440032500e03204520504030115000303007038104c041d540c0003016001411014010768201034141044916414034800079031090035416840b0060090154007800101c0b08004400e045c541018080c040c0090602c44003400e04e03804482100e0fa0717448050a100083c003143c0006600001a2000c400c5d1420351038004140441c451406c036004d5035103040600e62940c4001c80000d0303500100b00402c0000c640f046041e400c048101003501454001039211040c0b83c000794150440b00d40514680c1005840018100c0b8082410706041c038134501132104020503101c0134040c0090041b1401d000205d00920030a038010b40107541e020304010960a16140090507080c400c4400f00c0c0020b900200182c45420b0114420040f1a902c00741e22014214 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 65302772 1250 65301522 65301529
    0x50402090a03050d03090317010302030c040903050f0403060608061605120415050f060108100f0303120b03010207030206040b0739080d06050a0503030703021504060b0d0b011404050c0306 82
    0x80c0303504940c45081c0441c04004198103000c1c11840c0d5a03151000a04090140340180c40c440019034960086018203004001680b0080b807550103002e001c54002452213498642544e8a008214001010300b20100b0040304000d04d9030321800a99a87c1411074845940b07490281002d90800c2c030040002900a2151480360110010626040742c81650b0032081d00064402c0501101c204480c035040303200ca0007041c0031039940c002000c0c60300b1488586149801030300385030f03180400302601d210080400005824644103942580d1140e050030000400a5541c0e021030308009540e46800c1d98181c80c0a00c8180100b04c1080c059451402400d0003510701e10251294010310f440007010201e102c1c9138611070000c0322400141848020094400301070400a2010b0500c2c09009a030003a5030411402a80204112808250009105c0580c8a144508505141e4943c5820800303011000089900702158034040010403401020082c140c0b0b0164150202072a000e40400080c0c40782560100c503504c0c801c10200b040c508 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 65304022 1250 65302772 65302777
    0x50901051c0906020711043b03040602061b041406070302011e1a06030609010e07050712080105010e190608100302090f072c0628020a14011401050402 66
    0x2503959112026040c01c41c05808140e45140c070080300c01c0d81d03000441c0340400000800c8280090400d4500b007103d0301900e000070b00900c294003511019414143d0fa02505e0300303000d040460001101d40700342d9454236962a0040d60300d0b201940e8010180007400d0250300507007a0181950103c138a000041c0150480300404d100e0300b944aa03005038215501c801c805050151521003e4113000b92086001038405481d0b1a400d507125a10048144540341c20020f02500396500e90400b815149801e040c80540e441e0003074240c990f445207803802050b040c04003560141a40c0c001507120b04855081c0c031032540c103240032020080c1c8140b100c00b240d040c44ca030b0104148000d0b031140c2c075056400101024101e55194036500004d0002d02c0440301c0480c80c2002c1c40401a0303aa44c4841c03140031800b920008102950116851000e0035000405410b0040d040840e141c0c0b071079402201030400ca0119012254040c0b44007542c000e40b59a134200c0142d400c112030340100000844144103112045802520856040c1d00301820480a90b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 65305272 1250 65304022 65304037
    0x6060819090312021309050604060b07060b0109051804020103050c1204030e010e03010f020403110105030903070605090102120a0e0c01021b06070c0b0f0d050603070f03060203040f0507141e0105090105 88
    0x30210000f40080c0300c6100800e0a07201c4c000c8410512490040c030318040e20b400419803030045051903410090b1100c0c0d07106032561140c0c402c0c8046240801003004030b40c400010703800643d01c00c0d08281c070124030b1401103003064003c82c002c1c0d0b018407056540440d1003146200ba0003c0c0d0364000611400900400d124065035440304a0503d007000c00c029440e4000380c00e5566181420802e260b001408004000008400c0f0800507003c3c00c000e1700f1440d08000c02a02c0c1d00400d00c01501045e03c440000d20303401400e41c11100b4444a0404170000750400404070001004852800742c070398860311352502c5481d0300004011003101003249076800e080a210090119982024004641000741d0700004204400702c200a4440d000c040da0a09442c4c3ca01ca04d01c0c0425554041c0585000e50031101050000144049004003580e4000d8005a500e03200e40c60019100d120012002d4201d000d8001c002ca014580100b1068aa103000c407409200310802178090010140d915041e070340402c03c10003401416500620251104 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 65306522 1250 65305272 65305277
    0x30302071b08030a08060f01200a06050a0c120b0603010510090801060305060906070c0510050c160302071e0815090a05070e04060e03070201020a0b150310050901060608190903 77
    0x107045500900a000e80240d00a00c1c001d400201d40b00e00d00680c0003003c0e542c40794040f9040e41ca50040140080d1084000c05042c50303480c2565500d60b0610602000880340e21340c0d1006040256107011462100103003005541d03d00003d110224160441080c1d0280c20790f01c00e03004008603c2d5910300410810220b2202004d81d00344000c04100080c00e1800b80300e510015405180a0103039443c03c02c0d002c604000c00246810300b840205801d400118030300260f00c02034240b15450000d40b94491210f203103c517005070070480c0c1040220000d20f074101a80828044101c461454541007014000503411001c5000c50155090603031162403a5505452220151270300006080240c4100105c1c5407034082c1421950b42149055082401c00d11040289920403d1044c4030301b10041c43c201852a070000351558840c0300007501081001e404500c4102401444a00c1c8080c0103044950001a620001000d0442241c0d40401d03035180003c00585140644606840b659000c03124803190024403600c01d004000c1d030a01a002c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 65307772 1250 65306522 65306543
    0x8030a050d0b1909150e0f0105010e0d051005060109260c0d0f02040c05191d0d03120b060f0705070f0e010e01030f050102040f180c02010e030405041e15170105060d03030207 76
    0x2480418111b100740581d10f001140782d51503050030005081800310040c400c2c080c5216a018001190001c1603d01c12810600b070082440d03140d081c0100d40300c03106c03038110030401c0c2e211040c2140d0052408040b640c100f00680140c0381000c2d0f80b0f0040201c0e001100d40301a128500c0f21306c80c2c50052070264030107201d50650303060072400c0842e4015000b00d0300c0f86032400c40340820301c0310000c0c00001c0604100b04008c2c81084401d0f40684050340e41c002e001194840e5140c403101c3d01d8440e0104150781b58400c1c2d88181365045002c584400090400b55680c48403841210302d81d1802e10b10209500f0f14142140d8140d0b250b81c08900d0b0300d40d103513969000810404050648441d5404d10010072100c004524900c001c000300796041d2407204042181804941d542c204040c1503a1400e80075507000c0e40040140c0f0202c8004460005a0081c0040c84503048110030f10340c180d02a01d8401200000c40c2010305600907907400768001c081220079074942e81d080702d606450a0707500052504940000034405d4000305600b81c8200e01122 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 65309022 1250 65307772 65307779
    0x405060406090603050604031e09170705030633010c15060b1603030c02011a0d0c0e010909120206070507020909010f0507020c030d08011a1308030a050d0b190915 71
    0x10103c9482d6001100c1c00c0c0c1008051000b89544941c02410b20300000305020640801381c02c02420ba2905031240e0b503001c243c00740301c100908206004900041501605840f00c0b49080c3c2c0e5403109040141e0f608400e80d4a0480c200149401e081011100348a8180c4448814181940300c418a5100c0700011055050301d0740303004100040480017410000c41301045051030303004c1c035150140c10344c0d003904084000c580c5441319003580b801c2a4612220341c4601075907407810910381d43c100840c03a41c0e00c54020014200c846400040c00b500f00b5408141c800d4042c0080742d44101c0d80f45000c076220304003130f01d04000242081c0f00340005407030441303c0590070941060000401c05c00b000720400548030200c0e16000940c000015044407800c1c148079509481069241c0b407090366042012089044134000010140390300c000c22002d00000d036460b0354801500a51040f00e44541c130300c41c0020455405007001455882c200415100365050500c1400042c04400706405010703810a01010f00602e01d004520a0400f140a07000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 65310272 1250 65309022 65309039
    0x7080f030301090b03100f27111302091f0908030a0509060906040806131104060308070b0405031e0717040503061801110418050c0705030f0d0605100c050106060905010e0405060406 79
    0x180c000802003901062501102c94070f02591400384882314a0308250030950000904c80700a0411144012a0007641a0103004820780c028024551002d40103044803101c0d6018500301599100c0305a520350390140fa241d10b61401a44a00420080401054043c0400c0000b0326000e4084e002c080405000c06062940d92030741146810342c1644c040d800a11504900b00600000d010100c41d40700701982c003030050030b145945a94541c41111b5014180c1148080404c0401c20188121006004040007040700c0c440c840e140d070344c100d9100c0e42085a4030702c0c000100082441e0385005850469500501511084e030702c0b848240c1801c1c0004915005070b550351780e10348050002d5a000f41c805028085413502d080204035004074126100034042c4003052006101480004a000088808010050410a031a40f42a030030003c058a10f98000305c2d40401e000250170f01481d407003018036022070301420081c0101030340c03100d05031002c010500501d4000340d40c07140300e0300340390900d0380115800000292000030029a10b0042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 65311522 1250 65310272 65310281
    0x506090a030f0f080703050909150d03030b0604030209040311060609040308010b07030909050c09030106050a030c05130e030406050a020c0f0319030e12070302010809010213090506120a0c060207080f030301090b0310 94
    0x700c0108a0100350b2300c0e110f0a01d0500790703a00c600350f84007103058104141c000910b8601007803401000c140e103805010800c0c1e200c0909841c011940980b049030030742040c0ca4080c000c0c04000c02d034420342c0d10070480042c0240c602513980032300490701074541c054170f6401e240d07040d12b02c0d0f03001c01019000c0c440500030000e007076220b03803240718810705a048043e40c650400c0e008050968070346500107880340c0c000e09030501c08240710007000e000302c0e10304527240c07141c002c1000d49070005800c140942d60064000800d0016840340c01c0380c01049020741c1c40c0c1c01d40f101c2c410108108501201030200300760301580054043e0116071220590500342034080c2c10102070145511000030703200401e040e41d241c5140c225002c20001c55800418254200b0388240017503043c08482a02d1820401851061440540c0c403100404c0550703c40c5041e02041d00003030b8080d140744102038108151045103600c5440014480d10100080b000c01c041140c03480300001202841c5507910f0b12001c20080c1050a00d400d50601a01c8a04150b50f55036108 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 65312772 1250 65311522 65311537
    0x50306010c0b091c05030910020a1205040f031103031504052e0608010b040e04060c09050303071b0602030c03030406090c080607030504060609020316140f130905010506090a030f0f08 80
    0x5002441d605134116079694848401d00040c00301c10b02c20f0080008002c182132984031902407006841c1d082c0a403049440c9844610980b62083c50311f0144401d1010340030700b00340b01c1400b0f9100c85240c00315070505c0c00c0d680d210071075131143d41b49040860f00c04549400d400464119204e41c0c401343e003041d8203905d40390781d0490a009000a02100c80001c01c101c030b801030302d018018450484110300f171034540ba05002e107824000704001c21007a0340320303881e2079028003d9074414090200641100e031640e250785010140c00103000d040b00c2c0b02040d80c40c000100c2900c00800c8990b4680010051820b44c2c403103994040103010440c0080766100e0382000e000c034440008110700c80c401c014555020803981440c0c240141143c141c1d4000c02102c2c2d00410800c08441d05214000c01011011f00e0181c1c000c0c0c0704403242c90b01a0207160f030303201410800000c480a068020210300d80550b00c1d400020400c690f41c1e041041028418506101d8010034101002c0001c148031400b40c0b5050b9029840d01c050304413050b60b803003045600016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 65314022 1250 65312772 65312791
    0xa150503061003020c190219030c03081c05010603020a1805030d030b0607060203040305070b07030b010816031b020c010801081603080307050705030a120b010e130b0102030d09030f0f08100501050306010c0b 90
    0x42412066241c99044460b423045555804280300c0c0c00d5856103d003501440c000509105400961250001c462803040044400003581c10041540c54110042c003030b50203900d5040020310261031504101982240002c2100c0c4010000e202680c1c84400c03d4020302076100400394170010900808010604a00040d8401d5119a82d5035555040c5454403064004010b0700c15810580340840a01217660016003554000c2c501c00d40b20340711071100e001c00b10301410604400c5842061840130034019250000b85200040c2401d0301c1d60311a07a0780f01e0312095614011242101400c1880f10410001308507050300442e0000c1242c500b142c0303031030720701d4a038036103180d1040b212000000c49060703000029181603c180c03041d0b40400d10344980102903a80001d03040d000210240a50150380705440700041e0f0081040305d009034801c50090240907a1800d0107803001c00350002020100700c03100c500150b00c9218070380d0603100f142000545100107080c07400445182c0c100a01403070500503410344410103d1404842513101e105030f81c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 65315272 1250 65314022 65314063
    0x21e01060302040f140c040b0301060509030307020406030c050103060e0603030706230118140601021b1c0b040b1602030403151103090106090b010e180606120103050c0a150503061003020c 82
    0x1e1150041d46000510f8649000300071f22017401010f81e00d074122811155a446c149455001c0c440009040d4031030800001e601c146040800010400c4402e41d110880e10240c0301006840d5403800d01980d00381c405c45600d64160410003000000644950102116108a04500c540e40d005c050049000b03440070781101c110820000d2996400072598042c107100c1410340203400c2014140100040e40e510014a06031a4480103031404002580b5046d9076481d48201d8030103520b021074801e0521055050b410740e0162a0340790344c07500040e8508400d400052050034a0381c000c501c1c1a256842d0040c9404003000714100391515600c0035000043d250010f140920340c00c00000800516042840c02254451080366040c051490384201d050380d00c407145120070050301c00d04441d4507580c031030004400d4807883c006608004050000482402800541c4408d0034034141c491080064a5228558000b40c01d0048100050420030028105c2d050032134400c1d101000c18100581044041e9501505200002d851080f80c00d02d00b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 65316522 1250 65315272 65315291
    0x301090b150a0203070f15020706020d0b0d051218040504060b1e0a0b03100302040e0d08070801030f03210e030d0b15090d14010623030706021e01060302040f 69
    0x2036001c045a241102408601c0d040c0d04450182d12070140b003070054038091a0045040500100c0d00400c5151500c1c0841196070303c5940c6009402904480c0190128520b0300070281460f0414142d0040c01c180c0110003800c4a80681e91098040d0740050b02002841c00c0d03540c0e00d812035450b41d004050245100d00700c042003a090410078000b03200e180c1c00d8010034120340c0f264400c915440d5140c141050358540005175030380c1e035140040c00d41da00101e607000030340182c54030042000f1b165000c0380d0980141030503526012981c482d160100c44401080c04050000c40c006260880000d008882c4454441076004c6108044041120301e04216042901c507a13034160000038203903110002600c511541c4680840f10440080185803540100b0302803002d00502450300301c11500280405007109510202c2000d0003489074a840702c0190205813550304460010386400d400300c40c92850040741e204150ba07419801003010100c1200104034042c1e82c000000207079581c80d1804800747e1a680555200d4008a510210b030401d031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 65317772 1250 65316522 65316529
    0x9080a03140c0313020d0f0b0f0708090c04020703020a0b01080609100905030d11040e010b09040c0c0b060f0114030a021201061b020105030c0d0515130b032107080301090b 75
    0x8551a2034020111900c0401c07039044103035420f481d00001c010005a90800030380c400305506403031548000d011040c4d000b03002e40400603010406d510a01e0500c850310800d8542500c01c0d15617031401d1741d00308601d410402c0c0303170400c5051030307406400094040c0c4101c90307005085840e64040100203030403840031a00300908021002c030b0200045903094044100030803a041007625001d0712402022818400302e070b11001c20441e140f0a0b2000c1c4c901400041c00720b84440e59442850524551119140f240200c1c01c01802442490080d440c0c2c600d960b401200c00c034456aa40c8003000300b03150480301141d0502c9150203410803c0241080503500c04c00c41400b005035100400360106029440581c8448200000130700102c01a48618000b220841d0382801c1150712601d440550007281e0094a21404a00c0d182c1400c11282c0c0f000b00d0b40b81c8141580940700302048540407581c1005440e16105500e1301544128401010280e0010760442c0c18204a1100c40c24002195611809036200f80d11001c0415201d0040880f1440e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 65319022 1250 65317772 65317781
    0x13090e0607090f0b030414070803030c0904060b120621010c050c0105010b0a0207090c050f0d090b07181406070507031a071d010309021302040605040f0e1513020c0109080a03 76
    0x82040074854014508100c0746505d1100800003040444500c5824884140070000c41002d085040c007680d4507407030010f502c245a500980f40a5108500b89000083d40aa0304002c031348440340c6580600c10b942e40c624041c000d000c51140d6214801c5c0c1c2503072920b180c68603420310504182d108c603999865641c0f0060104c41c1d09440045c1c000013940d1504006000e03001d034002819008840e0010740205000d5615401910a03000e00040100e0381c03400000d95018448650340b01a403000c3c032800529240e500c032540c0032500c1c8a002c4440c980290040c0b2810301008480d40050703c80000c00410841c0b45c54044d03070341c990501d42d1076801216407407418400081e442c16181c1c0003c0d880b400504c4c06030b17000301802100036854000380c1034a80c1030541d035550100941d01c50400104c401c0d020101c7c155070300c968840c2c00178000d03071161141c50b41d00082d624011995080c02000c83d805041c10f48018035045441100f0411400c0d2000600c5421503400c100d803c3c03d030708080c01409082030050703185546503100f800026040d034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 65320272 1250 65319022 65319029
    0x9060305070510050901180503030f0a0f0201050105060f090301090204090b040c06031103131406011701060803092407052d1504120302130b04090b060a05030c13090e060709 76
    0x5000c03103c0740821069201c41501d181e11030910b420180354060300981c40485105421554040c0000900b6036640e13030650700109840f40159030390405183e500103049003210300038010140d10038400c2046614020b8800c001e41404140280001000001c940c0018212582014106d40b5102d180c403c04c81030001c41c00c04903008104074101444201100202c850491000074106c0700c00c0041048a2001d011070007030104214441c000444680c0d58460b20000c43d0074404000c80c030160741c03c0581c0400d4120000c4107a40b503200019003c0030030703194404416491000d1078100061031010503c40c0c60003091040100c078042c811482103070b012091800d51090408101c0440c0030180e0b901c00c0510b007036280d2044038103592007a04034055050030051140100d010780f20301c112030703582820351107800324501030120000c0c0112040c0c144100301c0e480c8803205204807070049940c0c9a0101e0410300008a14103110b000038001c5900e0085280146d139100d240e69001c5a02660080c03540f80c1c003107410040342c29088185440036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 65321522 1250 65320272 65320279
    0x40c06141303060f0e0604060b0307120206070b0703110a0806010201062304051909060516020a0308361005060a0f170106030b01080604050d1e1d030106090603050705 73
    0x1e00c903140c80e01c0c1420050741c0c4801401c2c103640341380142c5815240e902000b448002441904c90500700b88c03c001c809014404003a5100303000350440000e0215101071050105a80a00f000e41400c5080d2a080160200140b411041c1902c84200094030b1148400900750140562164107071403c02c0c400090848050760003180c070100c42068501a142080e400e03031400954100d801084541d45d0510080741241d8000c0369500e41410013150380204a0550000c52081605004c2106501c1b801041240e6841c0c00c40d03030140c040358000d130100710868030111000300b03994564130011060360744510481d850303c0340942c0041800d4100c914881c02c0d0381c11501031960010007c5501c14445400c00001c1d0341022600d1007004683c40803c243c950850f882900110011600600407261541e0b407602d0030b40c1c6074442110111442e0240e21500a1010b01a003024035200002861030300128100444c251420041008011545201d2400030120b43d03409009640c098000d07418040745042ca5440d11914108072074200520 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 65322772 1250 65321522 65321527
    0x30106030e0a0c140a030605130b0a050708040b041103101a010207050a05220c0e0111030a0c031101020c07060e010e03010513020910030b0411130504020d02090c0c010203040c0614 79
    0x400e103c100e140e8144c64103000004001503000002404981c516400108a50300301030400000f1003000c0e841c1034003103028001503400c5a50300500001120001c88041c0049040c0c0004500800e4015444c07903401485030607a9070405100c1000030b46041200340340300c0304542d21041103441900003c42e10214440081c00101100d600b0080081c440f00520b008143c018a641c4180300c10403d04000c4006181007008820044841e0030306000b069404030540d068003184d009121fa449601001044900d01c1001e83e0b901c200b290115901111400c00c540302c07074440c964090007802c00b03910003488550b00611498450a0004001da4000b500c0c1038140d134115442a454082040340d1031600302298170070b05034100c0b40c40c002d80c3c0d503d5105486400301d0341c0000d006828a58200800c200c0440480c0c00c460f5802c0b80e5030b000ba60786558004003601c1080301c000b904400202e0080c3c0050401401180d0040350740b40942d820207c50f501d4440c22608221415503100020f0001040b4854009500340307000c8005000451 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 65324022 1250 65322772 65322793
    0x909021614150a0209030a08120103020a050a031523070f0801080327120d020102180904030e090408041a03010510020d0f0c0f0c03030c0204151202010e0a08070308030106030e 77
    0x202c0d180018061043d42d80c00090a04080c0d0b0306010428007603601801d440d80b40c002c40c0f00450000d8209000403030150780c80f180013148600d001c4020070226603020082c031030600e00b041c03001c5000d05441d030060344104101c040042e942699048545200d06c180b1758580c00c180c1d40d0428021b0561038181c0c000c0d40241c000300b2118180040000e00d01c140ca800c2180546144921340001c40c0c0091a1491a09914001c0c81d00c0e078044140e042d001455a1810b918603101040010010403072210030a0b28024082140b40e41d5042c250700b03205500552103405400500d050558813185101c0c1c3c10003415102003941c40000061202e0324281c411001000c40c0c51000b0807a41540104c05007040c840b03001d420091100e804811000c203c00c20561702101a4440c006860300c0c0d0b52854082c021a1140c101280f040e41000c0d600110a40036980d07030011607601d030480002c10302c0c0540064444070710120702c8940140d030141000c1440da00c10403c82c00198400d8450599035032500200804480a02182c20425040a010003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 65325272 1250 65324022 65324053
    0x2030d0305130303110c0609030406030b010207050d020f040b120304050306090a030f0507051612060e0a0c1403161706100609030204051e010b0c0111090d0605070909021614 76
    0x3030022951508000409010170b5003040040d008a00291205100f88030801090402c0440504100c40c89c41d00c0a04c6071148200040e0313210505402540e8010912031039900161401c0f1402c4004094090000544c0703c2c0500089022003000c0c1060003102e5000040c2080709003010007006034007201c0794001e04507102c02036400070300140301078030450200300e00411a00144a0284104400c40c10b080301500f502680c1c809004203440781007402590b01614161154442c0300d400b089034000150310000b0350301103500301640d41a0340d80700c15540d035070107100701450340c006986059090030142003070718040440788249104003880c00360010610b942203000a641001220380280a0348180c1c1c0e812540440c02e40e0780c202c9002104480103041611404111000140c41e400f200004c1c110034520500a101584042c1441800c903c40d003c81d0715081101c0382104000b082c145d5100741e4110106241030019244e82c1c50000050760003004800b060910b0381201c403000c100768500f4810300182c0c0d05001e02458010b5003400e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 65326522 1250 65325272 65325301
    0x10623090907050c0105040f020a080d1202130e09013207080c070618140c031002070203010e070b04050a0e09030d0c030b060403060f0605010c02030718061a0702030d0305 75
    0x56401542207801003841e4900510544407118480e81c02003001c0c2c500303400c2024040c08403a60590040392409000304595a001c9558104420152690fa00c103216110404000798422000054800d440c201c01180340c0300030108950041151500108121041c1c1030569500304200e02d054459003400142032020007101c10340c40798800307031a0424100036a078101c04014144a5045c0041a046c500002c82ca00312301c504cc456009203008451502615406400d2266100b00a0340403581c103501c501001030900340b45400801c4050f2005d400440d0000010300d040e0328010107600041e8803261b0100d02400301e0b041c202598070003021440d8041d5058144074549948911039888a4480161680319800d000c0307020b50402e00410001030181640c580e0340381822402804011030306520541081c42c0011039600c540003c0ca081e41d0020050450503140006041c1e0840c803c0c000440ca5603102c240003c0e070f02c01c030300d503081c858000300c1004559640418410907080030030070705480007450310708014002c01081d207619 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 65327772 1250 65326522 65326537
    0x507030314040e0f090f06010f05090c0c0d05031501090303080109020304140d051c090203031207090f0902070302010506031209042c010b030f0609120307030f14010623 74
    0x801c04003140c20384001041d64810b80d082280a0b03003d07401440008118072000300d01c01c030101d07810744144022101c0038a880d11b000380300703070f204412000c07500b4489490800741c0650441001e281c0c5074640010301e2411810845141d030607901245002c0704000601040605040c00e814091805108660070741c1d03000741080c8012700030b030130000340d000c000141007086001491048000240c01c440d040940942c0c0101254402050040c1480070110703d801e03201400d004004006500801941c100311030303010f640c032034020300600c840304101da0114009114046080704170040d0201020159551702d01d41400f070300b074420150600340603a001c0c034101c80c0e040402d0800e948000c1300c01c4034007040b041004d0030f82240c0e6045903483c480c61407a10b480d910700c002105501405071800240c3c29140f51255007802503403a0001103c00004581040081400c0c060b5203400a50b480343c0ca82c100042c5103115030010134112000003031040519801040141704098000840309003803041c010500507600850703a01c4030b5881c025601c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 65329022 1250 65327772 65327777
    0x50405031801020a02190f05060403050c061c1109090c0316030b032508010e06040807020402090a030f0b01061e1b0f0b0f0109110a020604030815060a02011b0c05070303 74
    0x24100340840c1c1c4213012902a09400501509000c514616007151121191040520b05140c0482c00511414503109981c00c50b90083d01a00204080806110305c551150040c842107100b580848081001c0c5c40c402d1180503030703952041648a9581c0c500307001f41c90700003404604400c50180104500c103040341e00320508440d090b01d00807131180032117400b00c1d15004400300703c1c41e00409901d4040d1300c01c0304108010811908044020300001540c0100c480d2141e1058030094000c0f43c04100c40000340c109a0010300c400f80001d00031003802641d03901c81910080300101e0031500480280300402089601c2010800d6000050003a080c500381e50107005010b080c120515204000740c940d4411080c448500c092a100703c0c0c100410090303030301e820754040000f030b0024043c1d000058608503800322000c81d5002915200840303500106261307216501c050344c5465004280603002d440f04048280940c03124400741150a90030740000c02c4190039005803048040c0502c0c0500c08001444a80c8404281d001401d1402c42c0c1d05030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 65330272 1250 65329022 65329057
    0x2040806130503040f080615060a05030f060d080403060203060907110703030c050c0a08160e011404050621011a061317010b031b03060f0603030a050f070212010c080a05040503 77
    0x9150803811405a45d0100303568a502d03410004006601040305881484a0742c117100c20008006c0c00c020f0540a13401c81d0500045050001581000540c8440d5801190007082c10949034000d075508140f641c81500125075880d000704c107100903070501c5108960810b03510705007007415035072200c0480e554410b079120160420540c0c0c0036440a0100c14860308450641c06032003000f40700d40b102e810320f541d00190b0581040030180c52900180e00780f445501d85050747c2c202c48004203581c0c516000c01c030240401410450b808510003240600701d240090b4902c07003840e40300001051403441012a01041d05a0542c03080c05190100300b00503010b1f014a42940a803120566411450141030400758014104000e1003505481a5074201000251646080340051011011200300e0f07034801d4050301c5400c074142ca090360940c1c000d00c502c40a9900490192180c8000c46a215081c44001d40026020814400d14207481d65990701000484a5000108030f600002c0c0e02001c0c0030310300301a500c0310b41d42d125149501200040c075 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 65331522 1250 65330272 65330311
    0x108060d0602070c0e09060a0e0d050c15042102010902090705031b0a090321020c040c030b0406090b04110a020c09071101020703020d02061b0706050604020903070b040503010f02040806 81
    0x20740c0e0655002580080c1031030009922203820400c10101992007607210300c100000206000c8240c094026201101e5015104c0030a200e0800d8400340c000445145640c0940e4418010314048800c0302c44c442c500851403e20408000010040b84211050412045905058880300544c950215160f080f100f00e03d005a0751355586151101110790b040d031011a20b20380001c00b0010039500003500c4050f24082c008000050150002c1545070013a000d64420240e048119050400c0c0707072590001200d41c040d0300300803980c0303004440050110ba0b80b5401414505545019103600d50a0910421341560100001c0500c4d040211350040e54407030881741510720910b85100000c01003481004507907801016500250340742c07030f03891a000e03491300f1803502c0e44d9005109001c000b0b80361140c9002800302403400b4100c1a840c0c2709840d101c641c064900140303c26045a004c002c010441d8070200000b20040c51550001134072182400101405c1d1014020f0b5008140d00502003801401008111a50130900c40804403465412 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 65332772 1250 65331522 65331533
    0x7080703080702060c0f06060405060108090a030f0e03240f0712090204060b030a0507110d170a0b0a030c03030201110405090a0c020a02060c07030209010506070309171510050f030109020108060d 85
    0x244003a00405c50281360200020400300007403490140804032403d02140e55100c00441d94038808642c040c20680c130040d41000070030b02030090411200000d140888264582e04003080c60101075909940c01c0d00241d001c460350b841d00e03890049411110740e04601742c2034141783e60b00030902c179858401c4002c038a03599a4007400310340e0340d540900001c1040541c2e054a0303281510403000142011074084012400140858260b028042400710180150b610b450401f410400c00c5503540500003001103180c00d6440714403186503a1650800070056124440603a0a01c3c2180340c024299941c1e00d030030041464003400140a44d540e84111b5942c00803000b88001880941d140f0120300d8003051000294100800081508020034041030300400d0360b0003a1a49a09030b42c1c1d0b4010300c0040e2140e1003003d80020412001449030b0780c02c0d45070341c0e030152603450100c441c1400c004036140080e000c00d641c1c2039030388a402c0b01c0400142c03d054507058031540d8110000c01c121492600003800380e05000382464410070f00c2000040400a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 65334022 1250 65332772 65332777
    0xc1903020d090809030f0703080d1505030639090d020105090909030901031812030c1e0203030f0a0e150709180c02060f01030f080306010519020a020406080708070308070206 76
    0x805514082c4102500c1e03040003070307990380500c00b00c0e0f00074015006110000780380011150122a8082c0c5228903284d91503169800174030340104085080c00210000145075034040001c01d0041d03601081d5010a100c4000222560341604491030340d8103004181c03400c151034041029079070083c1060342c1001b0104034a01c012190303882011402940000802c0c103108400b54000003600c0f44209c20b803402c01c580c604842c10008680d80350711000704180045030804810511030780120020020a09020352802251100100d020704c0e0f241c03128006030b2000c010003a0703000511a032241c11030407000040011000c2000a00c3e140c614403034442411030741800100d84140e04c00c2002400a100c1660720070901040070b070015001d0852074101000600c9001c001c0341c40070125803080f038100c5e035000d0119403084603265140320594000904e800e060082c2444000300c03400e0b00c01c40c410710100542d809000c401559104010844a990f0016102548a00c505120f5610000f8051017036075041045503884251601c005151031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 65335272 1250 65334022 65334037
    0x40b010b071e060e010c1404171504030201050405011107050a06200a020a02031005060a15030b09040302010b130501080705060304080c01020c072c1302011101051513050c190302 78
    0x60000e40d80720284101507000c0f1200004440007030020088804048407920034411f0114a00001040304100030840d03103503005018040300c001d07540c00080c0d0241499a07031071704480960150f51540104003c101e420300c107101d9502c60717840c0842e0034120f03c2e4603072661311001c002c4004d05040e900e00d2407106c2c10701d84074101c150301082c5440d002e03580c00001c00c00a45a1420300000c901900c0780e0307000718804000e18000c0c030b886210003a08800c0b28910304500c40c2d180d2000342d017107201415a41e40c5040070548038000058451800fa400100d41da0074004280480c003d851081010f10610740380050115004c041100d008031030049840d942c498686051a15442c4560a4098000c1d803000449246003003004c40c0d903d0444603c0220006066003040801c950907405a007030001000070303280040c410040742141040b106006161100c3c48101c80340e01c26003100c0060341c800c2c41482c0460080c42c81441c0200e07001d42d2410034040d060049007404506140c0c14010807011003040820b140850385000d20960540780314 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 65336522 1250 65335272 65335313
    0xf0307080f0a0e060c010e0609010b150a14070b160c0201120e0304090212160f020304030303020a1106040602031b0c0607080405031306080414191e0206180307050108040b010b07 78
    0x7228291714040e0f00030301049080030044c4c010340000880c1824103120381221074002500000603d0310102c60f450059012412000601000103107445001c0c03111809403403068403800c40e00c40d0310300f0701c400410101c6c0300710585402041a241003900041c0d90051484810a0380b00764085500303980003000609601a64004200c0b9500c046001c0c00c1c2008896075450094001d10500218a11580c1c41101c6081d9083d42c1a4051b920810042000902c698010524201103150440b100780314186150305240086d241521840d8010051050880700740b50f04003400300c00b40d080d440ca45a03c0d8034021340c66882c01005081406241e90000e02400001d0088800c54407440740840c4034280c440f0030141c203200e0180c0302550300c42d580500000d141034000915985400e444a000c9a002010360765000b102505140c0700034030308075215410300040e02da41e0084c142804242080f09102c01d042010b15180400c6a40038074100410002800b000c1000b07038a00e2815284080e50b841d85d14142414605482500021039080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 65337772 1250 65336522 65336527
    0x120a0203060c1306050408151503030a080420031009050102070c0e0403120525022406040f09020d0602090102010b09070809010f05010f1701060302030a140f0307080f0a0e06 76
    0x205030b01c44070700800030388210758015580562144401c030b44034004c0c1d0144150340e5200e072408c001541c00c110f650541c8540884800b104081000c4003090440d0045e40544011802143c14401004a0549404100321944e1740d0402c02c0c180302d10010395185101110f158000d5a5803050100f072100a4045034603076900700708418811503881c2000c401c00c01d02228207400103174441d48607030409081402128092614000d107008a102e645054098201c114a2807034250f10550a100b138070100f65500d25a5407940044284069180000901003522003008503070010798600792010f40184d40d5030300f07081c40c1a0340003940107031500380810040c2d006001c46155268400d40316020003110302d92098041d07204041420080c080c0301c5d0100605000c2c2c80c006c0c00386607101e1103011000d02c40d0b8411400c8003500040c010002040184e03980e0080f03410858140003c0c1c400040300c81029604030410803c3c0d10080c0490401503141a2098480003160302445c1e90040380f00c440081c100300620702c06c24071100c2e8a58010403465 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 65339022 1250 65337772 65337781
    0x3081c020f0c060a1401060e030c04050a021b010b06070308100306020403141006030b060f0a030c080d1b020306010501030509100c0815010903020a0b0c100e011d030315120a020306 79
    0x1240b50800550b00c0a1841458001103480740385020b030303a0140c1404502c80c2c03420390034100c0039a03c606808030409d070148960b00d211f000d5030340c3e10f0103a14080d00210000581d5482d100380600d880442d5080c41c0555a030501900c1c038503a4a46a003100c44243d01403905c3c240c00d032150680e9007442d0765981c0c4090019030001c00d0200c1884009098410182d400c2400c840311092059091800da030003601c0054074102e8140001400c500781051000c0310700380000c3c21130f82001d0b140da48000c032500d4681c00c400200c0e482074800f1242c081c3c0180c00021070210b03400324407840c1c0d00e80f40d0000c1d980310b405004850405840c0c0e000300307440d000100075912020458200510240e0402c00d00141070480072202c0a401080d110501c41065000744500c10035603030041c0240e0030303050800a0750403440d8003412040e1802d120791200d04004910910405a070100d5440000c9400e040d84003c100b8406841400c0e04c409400800904c50740d0240b01c191511007080071350364000812120803000d17007060101000690140540710402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 65340272 1250 65339022 65339047
    0x30304061119080f06011701050f010302090d060603030908061012060902030d03150b0f030105040b01020304030b0f040b070516060c02010e01020f04090c050910030515060a0f02010e01020a0903081c02 88
    0x84e01c00d801001c101ca00a41d9080011140c1034141709280c0e0510305590014881030614100d0705c2d0b18094181005864003146001084903c0d2807c00c040e203501d03035200d000307108050384081180f005003911801004241041c3c40d6580341c43c4d06503c0740542030010003003580204200e580006280f5900103042d1480241910000340141082c5009440c8641410341d01148114110007610b0aa051008030182545c2c02c007018440105440d21202d070651006000010018075041001c0e0320030085440c0328007130342c03c2510b480c9010890140034201401400d02540c072030707022424008810190030400c003042c001c1042d081030b070040894500b104e95550000034020030b4011641c00400c05c031502e00d07004202904101204071040d00410301c50550100700071000c10101c0b403082d0840394016400314007010507209003800248090b44402586004124481c0380215040d80a206141645407118001d619009602400802c040628007008080c1200402d408500e144580650890241c114400310364454180c02e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 65341522 1250 65340272 65340287
    0xe0c0a0e0a06090204060c0201120e0304080d02010b0427020d15060503070503070803090d060212011502010b12030a050d0605090a02040f06030b0f0f041e0615050705030304061119 79
    0x11101e1141420000107061990f482100c040390703055602e040b906017040e4011a080040100d104101c00e0b10360701b014000500600c010030040a00000511003142e43c081e0107801c0d2840401c10922a51400018000324004046841e03202c90341d210034514036030918800240810304812019040d44404038015401c01459842401690411400c83d0ba2455541d4105580c0d00d41c030f0701629070b95401c14490243c42d81020b03017101e01082d00c40c0f5805800c03c4141c40c103042081000360f100800002d4542600504140c0a208000c54620251000344102403101391050b80e900c5100036020401138000b401140343c1d0300715400301d005440002d045041c181041c0d0150000394101c0d015a06100301e2032440015031390301922601030030000140400840c445200c0420000c050f030b00401f29041b94584141400c1d242c0240e00340c1d5100350512900203101410b00001100030390903820140244841085600d0101d03e00000b6130768060350255000c5400001094a11118050600c4003148507210301e0801d8603403900b02c00c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 65342772 1250 65341522 65341531
    0x4020c0f0c1201091203110714060f0901020c060103030503060f04110a031506021b040b040906050906010503150402060c01090c09020a020c4906150603050c0d0e0c0a0e 74
    0x400025803554034404500f20313040d038440184542c0814090f01180f5000e034010761000e602c504d0b40c0034180071080d182c0a100e00031404104206400800420109940680c0781d10741100d90345000b18103000381c1d800d8290391840180805814441e000c00000c0d842d640c4c610a841c4000c4002e0424418290020a42040d81e0400b041000119080803194414034040d0008402100c24980c000d001c60000e000122030100d0322140d16a41050710340808070502d4a66010316100b003445240f00103694940070241e503013050410f8112130300c242c02820185404840b150041600503404403049a600c01c010b0f0002401460303590002030088418000c0011226480d9000d000070307000a400341c4902c20f02540c1045004a165034411050b044000e0841c034115020070344191514141252000c0582c60300000b51030440e1100004980b520307140d01d40308007010f41e0844c2c480700516260400380308604200314a07500303500480b8040000145c1d0fa40070903604841c10403900d01400706c06441c4081450322442410f01c0b0310300486 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 65344022 1250 65342772 65342779
    0x203040501110a021902040f0e03030a0b0109080d080a020409050c070501060603051e0a1104080d02010b031504080c071509030308060d031e181517010806041104020c0f0c 75
    0x100b00032444880c8200700c40580b80769a01a01c0c00c110000b1400c20080d4000c1720981e001981c900d1021407451003441203464000b202c20040d40c0700c0ca080101d00c0c050f074190400e03e604100112b001048141400a283d46803038a6a042041542d600d8000d101c009004d1b40e84040c80984c00c1006100d10500c420b00140641c40c0100c00034440e039a1140c00503410785001756030400d856030310b40d04202c0c82401d03940d42c029000064240c01040f42a03100c0001c83d0540c0103500301911030f422144c070403807201d0340911a1040300c080c00d50107002009074500c3d500200c0c00e4001e002400c200c50001d504118284113008030406809a00195084401c9100b00103100c090380303010440100c2c20f0075011a075646005d07811004003030b0f8150743e80545840d01d20340c055044181c0301c0e0b61005122001a03400d2050719545e069502900200d01040380145e10444001c1140140d00d6045c3c412058080c014824910049141940540c10a00307580c0784c0215200840e000744240e00201169004040d50000c41d0f403c0460000803251044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 65345272 1250 65344022 65344031
    0x111e0306010b04050a290a030f0e030310080106080303040f030207030f0b0a050c0304110f0109081203151012050705120405070603051b090409020604030b1608071d150d020d0203040501 81
    0x10500360440c2048000f4003043d03080c103109000c0d01040f10800803c0075003908e14010405050300e0300d00030700703460400d40404013940010081110204080202c0001485550003e001c2c541c9001c00c62500c030300c006031010b031541c100c04110b801414000c002c010f000b540c0c000404080968642040c02e09080c080d140509140d060071701080c0e2420310081139a0003541c0007010b00d105c1c59101420410001c1c0007081c1903062201000000038036660030b00c51500c802c50318108180c1d83c1d140130302640c2e04110007099480d100b85034400d40d90010036030150b06100b000d03480d51000101070700e9009080d902801905850300380720600104200c10400080b0b19602250702e152400d010540b60f441d44615520400500c00c4280d110901070b01013240b03800d402c040d4a981c0060002490306440c0c0c4c488204052046076a41001903901d890f4821981d8041e04060780310481e483c0842107080d1041c6464031441c61110030314410381a01c440b81c6040301c012021146c0510070940300b156545590500c4101a4000701e40c1a5695482c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 65346522 1250 65345272 65345279
    0x60c0d020304060f2c0f04061409060a0e0f09011503080702010306080304120204020f07020d03020303150108010b0304060f0b12010f1d0601030209090a05101a0102010603111e0306010b04050a 84
    0x1183c0d4111901d0901c1d240e522030381c4c489117203403c511160f1990141d0124504810110607120340c404d10001d0b00e54642585407200c60b107801d0000c10795000c1c00003401203205100c01c00c48010070000d22500180451803404042d2242c40d2410b0241c01c070414034a001406401000040001d19001040c21902c00c0e02c09001580d5a021840d0310f030300803032003044007505c0ca801401d001403a280e4001c108601c104954a030500c501078002c220f01c81c420b48400c0380941e02c00801d01680d05400540a61039502c24a4032504d41d41c1002c0462941d400054001003485440c2d20041000f85c0064000003814000a041a018030700f0010b8481d001c2c1c4038070200180482d140c518020f480381000c86408007071046240051289901c0c1d0750038058948002020b11006029100300e03140020824030928016100b80100803031110b54034840c202c000300314410614196854150b003003000905014840e0f45d001d20880e007540d00c000421040c4850380ca89034a030070b030f4140a8180080380002e0400041d20680d04c05451582e8a07a45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 65347772 1250 65346522 65346527
    0x50c041e06050301050d020402040e07080405060c0f07020405060f030a031805011d01050a02070306050c0d230a051b0408012c0a080901030605030d0e040b03010b0f0d02060c0d020304060f 82
    0x158068a0001401000140b0460801040c0365050791f1001d0310041c54555076000301c000011080e1a000009403400c5c00f440140308040124a41201c0030701031061400d04a001c241c5200e116028000307010b5500c4d100002c50b80e82d5080d03912601100003a00799600440ea6280c020440d82c110310001d10160005c0b400807402d54443c14907244c1d001d0043c010040c80c0310144005694680100300c005085115924000c0000b800d1ba0003094061131030311032125110103031503524a0540d20003004031484030140c0000c0044d4540a29041c60f08488030b50400661611078802d43c2085e0700110510707454203440020009110b07401548070300b141048408100401d0391816403c1c0d80e0500b410a92034040b41c0c422101e240100b900301004010b00441410b0002d50503aa44012034100030a454510f03010411038800c0d01d446051900802030034642c2140200802c50860f0001006040c035144054000e2071110b1440b0115283c50003255010004038044801d042d0000b03d00960325403060090200082c080c0001a041a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 65349022 1250 65347772 65347829
    0x308070306050105030a090501060f03061505040227010203091203030906070503070504030308060126070311092b05010216030212070c050d03021204060203040f050a080c010c15050c04 81
    0x100d05075a44c0b481e5480ea82a5640904040081a5019540e62400103079000140503050000d6104500100c1d1003142c0c0e003e502a403031116803055004600400005d1000302c441d00104001141080130b600318140c00c400100d185020300c030042e40d0403c0d9039500c2400c04140010196110f40f0b403030300884402e0f0b40c0d20031003140d1034001540c80e003020600a0009000280c014002c031079120006240691010951030f003181040c640304600341d5000e554000c24071040c3c95042c001c2c040d140c2c809484541c44c00c14540c2c0421440554a0455108803102401d1240035500042500d6140b0350004001d64860130b0303c0c070b60082001c3e40107600328003508c14505042c16118016094601f601d0f001600103014501e007800f800028081e50900f1400c50051004040300e222500d000340020700459070003142ca4509240c41d034901c0a0894101c06e120300000d05003001103403000034240203500c0c02840d00201030b04013490180c0003403000c02c91048041e4100300400c12800b042401420844030010550250b4000c110103511b40384 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 65350272 1250 65349022 65349029
    0x11030705010e0607050c030607050a032405060c15150102070806040c0e061f090501030c03090b04021005121312030b0901030206031b0301090501082a010e04020c010212040308070306 80
    0x3514000402c03010301c2d045001c0d0045034020420b944a040c2d6840001e424120121010790100e100030520011030380d498071890308507011b0810900c001e20445030811004e42d0b1144111440f07000005180f034400d4405104038400305002c03000310404d50400003880e51402030440542e40c014402d0810008102c0800240b0074059a040031880040604010911410706001042140c201010030035071a800604c001c171404c048012680c90003500743c141000101622a1006810704040c2002c100781d0220f0021030f42260400e9048400740c1c290542310b0307400d032240d0141d4010030784801c040b5800c115070100d58000510080d44aa013410700700c0e502e031480680403900c5201026030000b002100502c0141018001190011801d040103d16072000c0003c1c144144c0c401d8028030102c0391260010002c0200130050000314511050f59103a00c5107803c50584103482c02500394604001218906555949455048490710034264000392750300d0340c00c0c0100800c611801c0c0d804400048110000440041c42882034000340c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 65351522 1250 65350272 65350277
    0xc070305030d0c2307110607060605010306050307270e030a09030b1b0d1e15051809030d02070312020403030c11030c0303070308060f1801091a060403030513090f091103070501 77
    0x1100c1ca44810041750011541141e21440c4018541510b9880314003504a003440b80002007102400d2500050644100794800350103907004038002c1c40302c000e008030003203600b03005401c10700504101d803040600500740f10000244680000103c0314882039101070903000781c0c3d014070300b114841d0300c07000c004484400c1100742d500781141c0c00340103a40c200c00c010f4110321f86243c80460310b02c20082416039102d080340e441005126400d002e81d40d0400060800d040c0c03100c8801c00c4508541054509503020580368840c45428030a00d41e40002d0000806009040e052040000c19108544440d10b03071034060642d00e0843c005892080c89110380320141e2030b00080c4c0c0301c0100b01c09000785044c0041a9806e4850b504060b1030564003d8a07425140c180340c032280036500510060161400c080c0d403500c4084000c40d2821501240e50326485603440007182c031a82c2c01c840880b03a051424580d1030589901c240310b002c090303030801ca40407410541e066280d15025003003001b010f4040c4201c0c0402c10030700001c0580d12642031281034007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 65352772 1250 65351522 65351567
    0x160201060f121e0b09030c15070504030b07090308030103030306091805070b0a030f05040b18030301120b130c06080601020f01050f040b1b070302010c09091a060a050c070305030d0c 79
    0x2d0052a583c003801c05010380d1500041c0081c0c0c3d20f14100302c10849400003a0f510110f00780072402c0b070400c000812280c00700b0105c4110304002200910314461800060300d4480e03080e000c1050a8400c0189000031900141c041da01c0c0c1d612450000d028020a100d40d0031918100040201100303007140c40c500000394050014101203140c05106120307a0000141c5405060781c4000c80c0c1c40540c0c80b4044d2901c5203100c1d02c0320b4500c0e0308d80091044012200d800a49805600610050100f201e1500000b420f164014281407042d03641c0342c2440c5a26080058000e1440340c10180024800340c0043c0d000780603120980035542c203810440c010a08079807040f40c442035480e0040020034081812080725a400c022a10b4900d424031991901c82480c0b170788100001c800503076603402038078400b0703600070012800303458081414403840303040d42c50301040740d00c0030307081240700d1040022045000c90240080382d886204840c10b4076802589c1c0d0900d90b4413a04260081d01c0810308103401500030b58401cdc86041c00b0000608102c11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 65354022 1250 65352772 65352809
    0x171509241611010609020409020c060f09030a05071104020a02011406010c03080f0a09050f25050d1b0503070f09050108151506090901092901021906090209160201060f 73
    0x5449400b014503a0b82155602e078400b20b035421450000300f02a001036040581c0e944040781039689046e0000b401148142c4901c0c050140b440300120444402c499103240042c0c070f83d11035003000040b9005036882c1a43c0310b4070014042d403900703806410454180401285c100560364a03e170055400105510004001540d41c80000e51104c000d51045a0420304040c000504509a940ca191401e61421358103501d1f0b40c0880b440c084d0700580e6428255100002951011600c2e00d080c000c0f07407040078032680050286c107481c0b400750081007008248a004040c024100c411090381d40c4d82030600c500850060904281c180fa00100f080500080c0071100c0381400d001e0100165680e188070401500e000ca43d240d4042020403508a50780e50362a42c49010f40b1824100050400480300d00128a14203100103540c1440181c8042160781e80101d0241d81c110328051640010400501c1c0110003460014002907100360301406000360840d41c191040d0600126030006c004490f00d40c85500b107025214421034090591118155 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 65355272 1250 65354022 65354027
    0x603010b0f010e1e090408040e01080309102601140909011b050a12050c04090c08040203030405040b0a050301090602030f0901060312030f0209130e071406041715092416 74
    0x207240c4443c2c082d244400f084071301000181c0e102015541541c08a6011405010b8031030240c00c0180145880300056181003082c50200c1c94048a203500d03d028030402d19101c401c240010011503d4944405800361142e603114045d80310f00d0001ca5100d5070003010660002400301c2414417844c4003130a9441a56041701500b14002c03581c40c0d0103441090100840054149060303040382c062140182f00c002c0305251a581060300b5071081361520340c0e007582040310746002e000141e24003004031410b803481500d002c2800790760078012a18460b11640101d130158030b00600c90051008580c09107010300b482484156940e11024115030070380d40d442c0000307800b40c1400201100514000ea12480482d48c188801500348007580000800040d9120000703100b454641c05005291003040c0110030203048180c8443c00030b0582640464440c0c0500c4c0981f000c401d0285148101940c8200418945031508651804540c9015180030707489480d0070003180c1840c200400c151240c0c40b6139080981c0304158451b86400050b0104004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 65356522 1250 65355272 65355289
    0xb0a0b070b090307080301080703030f05120a0203220b010e011508070c02130903020f0d0f080105060903010902091503120301051c020415030503031e0603100203072001050603010b0f010e 82
    0x200300302da110812180e0002409030b4007840c000c00041000d010380c24030718200900340d1040b00d029036007008400c100d44010000c151600035041401503400680300e076100d0110f031410012441c0c0700345640703180003808010030082d00a5241030366015000074540b039903039100f806140502090304201140c003080009204a21a10404003204d000801c11004a0f80d4410038a0486014900940050300300040c44410102d0400411010140900d040c030040d51000d00c2c0205580c10600580c0c0c41244009a1412141da09401003542250020300103a1182000a034500d2000a4140700c1070090107048000d9081c00c80040a0368101c1e4809400c940d103001c100c42e03e411000086581c200ea1060b40c844294080601d2070b211030740907501c10f50055035079003002c1050305c643d4a44c1c07500a045400301002005025140032a0241d45a400d01e41e000d6100c0e210701d8000d031510448100c14041072915003110a0240905402041c0200030503070003004003c90140500c00580442c0f800207000c102000350110f59070400c20030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 65357772 1250 65356522 65356531
    0x901210603020604090b040506060a1b170307081509040c12061b0f0801140a0e0405010e03030a2406051b030d0f1d06040b0f060303070c03030302030a0b0a0b070b 71
    0x800960300351698001500d54001d500120349031a80d620200380141094841c2d1500700e00100c2c0e1150a015003440003c1140c101c52000c084698000c0117800e080280c0046c62580320442c0c0200f06440c1c0c42c0140000b0403280080301c0c00c118019201e11242c04030b080450b03006005130f411441028056040c0b0382410b80fa100710000c02c941b026a50080c11011306d80d80000c070302c0c1d036600641d50180303407088000005080e6041a0809800300013640a0624223584032803a0340101c8034224002c02055a803420700500428000c8180707509400004104900c1004d141c0c0710032150000911015107040504541a201c89160300440004c038204000c4100006850141855450810403c5074039040c4512201402d9410139150118100d40720a5036030710615040103595410700d4400d004058500c1d064842c4000e1060242141c10911800800b00e50b090302e050044800f500c0e008105801c050381c3d00e1600400039442100c0f19283d00d03242942c02c0460b07141000420b411500914001030511059031a4036000301000741 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 65359022 1250 65357772 65357837
    0x8010e010e15060705100c0314060a06032307020c01090608060d03030b1203041212140304030f0c0813230a090f02161407060c081605070515180301020901 68
    0x80113800140c010403241c407141004000c0801c5030591180c002e002c3e80d03100d00810542c1a9043e041207a00c1d140e80420b041168460f250210703003501c250483d031181c42c1e01d611580c100030701d015042140b002c0c1c0028101c440803070282c0c0e420012660321002190700d45401d84d08140c0c8403c3d0b0f55440408644260404c042a03038004282540d10350300300301000e1559000780d20980706403000b1190003007484064008202c0701049401c00c100c6000c6868801d07a02c4c0d210042c0002d0900030038050110307a680c45850106c26455002001c1540d44013074100d80c0c1d8043d5042d1003031149005544460240c0c900f44404001c0c0c01200250046c807a007404c00001001801e04a03003200c202c15420b0259940302c850351024008840c0c042c95900081d044103840c901e00708545904803c0510000ba0a0b020006041e84210340b40c00003c4411516040c01034a0a181081400d502c041d5020442a9006084d000502d004008899943e070b4140d40348071208051509030701544180e1804120361002501e00d0340081e5410070340403003001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 65360272 1250 65359022 65359027
    0x80403120c02240103030c0305030a09150207020a05010207080a23010c05070b01120305030a05090f010e2407020a0b0a020d0603080a020d03061a0a03090203010504110108010e010e1506 81
    0x19004241212050100400141d011501c11080105210700780f00e22125203070611006581151006090b02c00001001800c200340000040e80c141429032040d030440f03603c804090b200c01c40c4129644d01070f411a201c181c0c8a0000440c00040e19800010f81c00d0072162100c1c0500b101200c039481c1c3d07006a100c1054169000d40800440f41c221030b0303003032080b0510b500143c0c4440b03480f0802414400500c2c0016081075405e040400c0010b80844d40100c241e942c042e00440f00030a00e5171b01c2202081c00d28080301c0403040b8660800c865103000c484081500d00f040351a02520341000d01200d0424000803109807081d10258010051080100b47c0081da40c60b402403180d0790241ca0a1241d50a03902122083d60003525427010100e451b49910380d040c000e51040200c2072400f404064108210380c1030f40e2600c40d15824141e04d0024100c04440c1c026000303081c0040e0010000c010520305400d162045421105010340080c120b0b0f400440c090a4000d5100d0588401103580880e544c0d4a102c3c142d4414281400325501003801d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 65361522 1250 65360272 65360297
    0x20306060f04150807030b070203120a0e0102090904030306140102060f06010804020a18060609060815190513140c0a0e0d4806050d05150604030c21050a03080403 71
    0x8450350f0002055510010300782d8034910b040107002d00002824140440d0410801160710841c803503003e540200d6020030005402d030b0b51582290083c0300fa81c4138690043c40384001c01080c950035a2150b81124a0b1801020000e03480000490712804110350f1024044800c40200d80c00d544070328002d592242c0b01030000b100261b2078495042181c515031401100b00341d2940424003a455022003164014180c9040c00c165038108103800d201030340905041c5502071660780c02202c140240380e115100050001500c80300854840d00d40c1d000141c4540a00b104104400c04e0129040c54060008c41d2102807840c1c0e07601201004030410407075001c007000015500e00c000703040340700603440411800e030058032090f0705004103041904120f410650708082c48002511004003042002c1a00075080f05c1500c08072042c001480c0e80c84500e403013400940d210465412090202d804810400704484000c25a0403040f08040400e100c5c064095840405000c010030607000070320f034440040c3c058035609410520034101302c1c1d80c4280307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 65362772 1250 65361522 65361551
    0x30516020406050d060219031802151c09020a08060103020a0909050106030206370210020d090c0803030709050415051002010902091006080f010602060f0a020702060706021213020306060f04 83
    0x50fa461305940130781d4001004141e1201c01c2584901031503541c141808054600c0040021962501d0006402000b2600301254190f441400f11002004d000c104440c0f050036030050000102802d00c002ca01904403000c020a842200245503412a60b00800f00d41c4540e0a112025000c0c3c00c3d81c0c0d50071585503480d244040300503540d81c1e000e0042110304c00088860155500c050785400f07100481301d0485481c08003147c600a65000c20a03469404c810500540c2d56050390145000030310b20700101500300110300c0008141c4190100043d401080d0f10380d6083e03881d54554007001704031405c9583c8000c1c0131404000c20005410244201c400050450000240c600004e4011402001c0100c4910a0b07801c100031040c4101904017900750340005040034110159814400040c0d03450101400800507035032600005140720034150100c40700d0a03800380940c0d4441c4500d1901c1e4001e500a000381003906141c04000800c0d4082080c81c4140c0a07800900508950b1925800d10504a5444e2074860b0015115100040c60303c0b03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 65364022 1250 65362772 65362789
    0x2403081e07060b030c01110d0c020a0e0408040e07091d1e0103080a0906052a031b0303070e12070312050705060103080d050c13060e0a0305060a050108070f0303051602040605 76
    0x303020300c0011500c1c92000f010507060040c2418100d040c4100c1400e041e001c1d200c0000c0c103114849140c10201002c0c1410b0001800b142c00340da000802006881c0104010002003001400c00c81390940140c4000380c803852010703240c00002d8010303601010300c2d07020b100301e0249041e81c409070040c11586245e0040325007095003901c4940e00760015038031070308000744a4220350703800481180248140d1170083d0500702440d9041491000c015801428091039001c030001050043c000c4984d0601c83c607060301d40404078496115181e07001159010089580c5c900e5441803410220f001c0c120800052010700f22480c115580d906c54107005450704000c01c0b4051062070002102080364501031030140081c551078482d51000c420540c0c4004140e03034000f2200303002030011100c16440e800c050b582103061445100c901c18002c9901c920165001505621590f0103001049200c2d50000d070613140d414081e11030154603048043e5240341203220041c00180104030489020380500b414a0768584000c0002c104070755141d00040120 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 65365272 1250 65364022 65364037
    0x307170405090403091404020f0706020a14130510090e0a0c020106180608010b041103010e040302030d0f050405070602030406020304060e150703020d26060d05100516032403081e 78
    0x180004805004c01b0602030b00c8001110300445056181041503c20a03a260080d107600400568010840c85d0146010340c4503c03000c903030880d041c50b4030303407103080d020640421141c46010b0003036024100040c84544200c180c401a20480c00300503130300b61200c0c11400014404140d01408556950704042040200b811007040801e01510002c1907003400c01e044242180c01041e61640b16618120400002480c60400d03681100d4550f10a00344c00e50300c40c1800e074190b224070300034028914a030280c402d010024a078800c5001d5030140084641c003584414081c1d0340c0e0b00ca10b010320f1016a0061108010b9648101c00301889090007404003902d41102100726081034010540440250304510507041000c2d522404e0f00c46c900000003149502c490b8111001582c0b49000741c00640102d0203400e40b8020702404000d800c00704981c100b000c01c60f9140407907800300002d00e06560071001900f0060100000a8100b410354141c9110354504040c8518540e0741340d44076030158002048030445a07800c00c401c00c0c822400303407256 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 65366522 1250 65365272 65365277
    0x30b01050d02090402010c03360b04080c101b0f051e071406070605010303051c0603030e010309080c070f170304081b031005160306090c0804150e06011511060106020307170405090403 80
    0x1640001d0802d10b0b40145940ac128141c0701c05100401901da0700040c03406507200d056881030050100310404462213500d107140079021198511200080048005041d4403850040041c0c80220b042441d817500520050710b101c400a500c110002d000d15030308910001480e45004046620b04107007543d41600342d44090744103801060012441e8030010310080312280d0b4000b850341c0200500342c1140d8000d060130399000b19460416584810f80300400551404540ca20840402240d5020703644904903901280a80241980b803911000d900346842400000d941c1521806801340c2649500d41e0713070280d60f500d0b580000581c1071040340d080300340030045403003528000e68084203400780d00304803504050213658841d403154004510b04160407407200e40c001303581c079081035000d013200202d2017050300d000c2c0c042c141303c480355080b07801480d00000794000210420f4078801c140740c80f10024150b840803002e807241801d215040147c5c000700302150009507070184090900c0b40523441c90b402c090b203d0300032603000c0030701b240c4c120b01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 65367772 1250 65366522 65366597
    0x2104050d2a021c050f0703050114040c06031104080a05071401031806090f0c0f050f0a0303023012060901090c140307020304090e160e0c0412081210030b01050d02090402010c03 77
    0x1441828014211088ac90282c000c0850034280d40700c800c2642548108000c2640da0700300043c1c000e10b034034100c0c3e00070020310303003120a10781c2e8078200262140c11070703c51141000ba990400c0d00e101d5003e0300540850960010504005042945507000036014082d001ca40462916510744d0010703008107140c1000d042d005040b807607840d042c2410f205e00c0e0b070200e500c40c5110b1940c1c1c0c2000c01c00a079001031450302102d1950030404607800900c14020001c08112200c0c20b4841c404901d151300c0c20100f92281d84980740441d56200641d0361503c81c5804c031200c103040040000c900340c80400e2201d030014011508a0100d1040301c0ca41a968170310281224440710451180d0340100c0401c903095001a420302c0040c040c1c00348048030b10f06004011810522844c801c405a50b00c20310b152101f0300040310140c440e83d04c81c80000c041c1074900003585d02031114041c00121100c082c800004207103400c1c40900180865405070101c103082d21160010750f241308220908604001d820412540c1411082d250303003880020001008a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 65369022 1250 65367772 65367779
    0x8030115020c030c0d060e070506030c09040b12190c030215040312030e1c09030b010f03171333111b030a06022104050d2a021c050f07 59
    0xb4104480d8842041c460f07405a0401051552403500c01c00c0e0440d484000003491a40725200c660405000d64091036201e00040f08100b10190b840d130041c100e80704220360411200b4000b50810004400e00f00340070745035030700407030a51070f0340d40780e19030ce0750340c4107009000c002c20b040c1e5241c0c006943d500b180840d41c119540c0c0403d08008008000100001c05215402d06008010070003041030f54841040381405070782c0850340302400c0b1450040d24a080519003100680449684400c1d81c0780e1100310a100071554040b241c5c5101044280c01030580750340030b0b00110b5144009181140e2010807040b079084288090355906048001e035040e03410781e030058400079224408040e80281000d424400079081400405000340747c021003030740d80401d080380007070784c004c10050700c4040d80300415024001351292508224801c03014001070200000d94004204c2c4690741d4441c04a40002c01c2d540000748549507d502e04140c2500a0014603001c07240000c201c4142d18030100045190320307072070318140041c3d88040b0590007441050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 65370272 1250 65369022 65369027
    0x327030f0a2114010920031504061403070b0406090608040c050301051e01050303070503160c05090408280203090d030210060b040504050a020a0c06051f08060a0f050c0901030e0a08030115 82
    0x740186042001000302d61b046240721406104116102e08130f03030790004001036a0206154804506070740180c81041095158513180364a2041c0082081c030034402c407240041d811202d4011681514a25560404110710309041075500c40f0014108607404503030b4600102d09502c0034820284100060909900000d46d042c00c0c0120002c3d0607007101d400307904100b00742e0300410000070482e0341d841d034194854102d41e00b103070500c07510704071032031b08100c0d44009800203100c00e02407000080c01d400c030680d0382d00b1511165078100b02c0d03117520400185600941c009001d51300c600d207001180140075500074019100c1500c000740500048454a400c401c558280120b07041c81355003414491031754080c1c29080c0443c80d0182c40c580246c00038241c19401401151100006050304401502281454500311a007203451031300c450174151240c1c401c98044044501d06000c0f07944400003401414001d040d002c01851400100c140118050049041c18a01d94803504250100040c0c6440045000740040159503050070ba190310700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 65371522 1250 65370272 65370311
    0xf08161505090706020a0206030c0910020304170c0109030b09100f02130f1d090f060f0a180201120906020f070606050a090b0603010b0a21020327030f0a21 68
    0x100c0b4101e502c0401d040c4016a00003850040054046450941742c0e9143d1130201c0007440740d029515040740b1218000f1a40c980c00001420a0fa401e03049006980400750240c80e42e240000701c1039500141004008002149044d4030300b80e0802c01040a489003455401444815601a0007880810640c0000d005214030b0200781c410700641148400302c0a103625045620104155125296105c141c40c000894a4400c0070890f002c4c903120f40006944c42483d080a554186010071943d03890b5060810300340500b801807120368541d074203034141c4808a088042448590051540c074800300ea003280d00b04684c100348103640019007060b030310400713000c6800c0e410b05c0d050201a110f81d502081d0502c0c00d006e0b5801e055a100b1041d03a040d9801b2440c140c0c0c5131413030700008480c00340304d114440d10f26015a6400301300844458000313600c514107284c9141c140011061003400000324050790203150780c0040c0511141202090005c0c98203e43d18649018000c00da00000d0155203000b050440c40c05a646040405231001001c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 65372772 1250 65371522 65371531
    0x1030f05011e05030f0714190909060e01050907090e2a01021e06010b0904021204030908010c0504121b030804080105150f0607060519091a0a09050a0f08161505 70
    0x2174040e482401d411542c0e2441301e03009a070103241442540441340c0e02d0312034889101c035455007110403c2caa6510712200040c40016001d4501504000c060144080f0501629003c2ca40801c01020124500740b03c0b800144032028602119004079141060502904920800e9103045000c1d4841d09020f00b1001900c0c149580d011107103461201c8400303080e222400b01d00c15044030540044599107a2001c40081c0080c8110403170515051020fa080c0018154442e20010a460704000200702618102c1c0e016140c1d40514420945980c0d596581c0400098044445202415580d00c00d01c010585039940e001a507003103178105861582d0341c0e000b0070016407821440d40542c00c5040d602507815817007020102b01c10b0722440304058521502c40001c141034400340565110030f03280c0020b040000c50444d00c3d11810900c4d02d0022040022499404581c4962603407180032807440d030101c010700405207941da401c0f079280c680e0b24069503d50b0051000e01c1c80c00c4c88000c0d003284030902ca903020240c0c220303035040400101d560251 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 65374022 1250 65372772 65372779
    0xc081f0609030b090109060f0207052104031103030f0a1101060f0605090d1a070507020906030303131b050904030804030f0e0a06030e010204031a040507120f1101030f05011e05 77
    0x504002081d0070800c400c050320340201440d40150780c1c031000d150140800fa000200407070b2804464a47d0081e6a9000d000800d01c41c10035100c40401e001d55041000e084610f11100f2680b08210420000e410b0b8082c601182c0340c09801e8900340002540a400c5c141c0004d8200c03000305450b90700c1000005020b225140c06014000e0030005402e04000000301a4087c0e01c0240d03004e007010f03030000300612600280d2020841c000c2c1c0300300d01c094509081c0050040d082000103e00a400b040c3c007040b0740d0301e40030040d40d10981510488401d031200540310321a0710220458403100050340000c001c9455110a20000d12450080c1c07114845414246001403c0307100d081007040c00c001540c2e1042c611561000c1000b41204c1e554940440c117441c082c4840790080c448c647c0001c040702c020010001c8030001c80c200e40b900c00c034003420545d842d490b92034280d000707601e00302c10f001481000d4210300c80300010700040320700383d030f080701071500203806203c1a036603c1c10ee41082e04201c20300303195481003100100b01261f03c10041d16058 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 65375272 1250 65374022 65374081
    0x50318130207030c02010c14010911030106060e03100908070f0305070212150408090307050d050106080c01050307050901031802180906150102030706090503090d0b0106120207020f0108190c08 84
    0x90710f0084ca142841e03000203040002440c899010b124101c614220001ca052000300008900c1e1318025075022450b81c0918040d508000b400103085003d901c04c10f0400c5409409015040c4100c080e0344005c01002c00d048441d410107102c1040402e083c4002c1c01074282c481d80300c1641d102d1183c01004854900c2c46d001608590090341d8401c0c4100d03400204941060b4041c40c202c4e180c114090000e8184845034100540018102c0084000d00205401000440b06907000743d904003898180110303107a101c11148140420020014240c90794030030791080c0b408000c6542249000106540000e88454000c0699112450f5000600c1a9000f090128030b411007114801c0e0301c110340b21000040d440b0f00803100050515940c4130101b0307007484001e1041b214241001090b003030151095140140300c0c18401e010301030000713091454190140019200311224180c000344200020b0642c64011242c920000384105040c0e24400403809000d48240034076030041d6401e4545288034541607002d14031040c1c5205028209a00c038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 65376522 1250 65375272 65375287
    0xb0306030c06030103120810053007240504050406080307030207050303040f0e0603010f02031f0602151807030203010c0507020315010b04170313060905030c01030e031909030503181302 81
    0x1ea00b59003101a450600587d265184200c1200000403a4029a0401c1c00e24411402c0c1040e0b07200000e2803d9802444c0c40d40c0384540722051560341e00306000c1e16205640140302541a8070440c40b01c01c0010406190091505496a0110381590002c1c3c1c813204036644003003051810150103000c1e120140105500440c185031801d00d07610302000da240f1641c509031501002060060f102034015440d00c50740120155900c0c1015400c491400c1407800c14250003440710500401e0740c2e4070104041d905001400305108a58503a03622040110f84420860311042c401d420300000181c0b03080c00b414403c4105511003075105c20490040c1410b09502d0015401407001807001409500280c0055401303840302000d0210141c040105030a19500c43c11010104801c3e81100c00100103600141220684400360165144908664010760a480303108440880c503404c1840484c0340e005890180206c801e1240c81d0602985580703403591030460340140d1506080d404a0b0801e5030060801040d1000702d40401441145000348 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 65377772 1250 65376522 65376533
    0x30c06110c130f150f05090a050702060601032309011e02040f0303030c09030c0e0a0e0a02031b0a0b0c010209010e03070602030d050712020c011b02240705070b010b0306030c06030103 80
    0x80d0000c94440700359a0304040d440200c80390710481d1400582c1994148007600c441105411803146d01c11984603447c0100040c240c08418010140550126001801d040e100e081c01035002e4502121100344c0b0b452000d1096000a103c0070304140503203e540000902c0d2612030326042ca1441d010f82c9180e4441f80104002c00280e40582c501004907505881c00190f028110a000c40c0c0d100c00035800078000c1d078942440401e900d110b402c1554013441280d0810400750061041894031101700c0e08000c1c3d41900642c89607011200046504d52040c24005c06480107142c440100003c243c12881c07040e00c16a50100e00c500300c950f00070128521004040340107011382d5282c103c0080d901d12070341c0380040205031500007040c0c0c00c5016002401c0326101e0140103540783d280201c230050080840410180c00c1c1c110b04c40900400c1800456403030b42d5410241020340f246043d104080c901c40e540989010108101008141c010174081e010280c041e0204181080e40c908188040520381113a006480d0311621080004000080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 65379022 1250 65377772 65377789
    0x10c02070312050f04030606060201050105042904020408030c070905070c02030723040c02060f0c09060702010e270103050610060827010614010809060103021507050a0c030c06110c 79
    0x2030340885461100d41148074201c3c1c041c081d02860311050711003c6404420041d00e40c0120b801d4030700da54000c01c00c03680c1e20003c000541d28150407581461200340780c444c00c0000c0d14010000d50384d6001c1d1001d8030301070380c1c0c54001d0301e107902c2520502d01c1038110210500100c01980191a004409031515491030b400380c0e0000b80d2640440e100340080b410412018540c10241c07244400031640004008015000d50050040d44030181221000347c001101e400003034014264609449445002410290400040303a0054480d4680c440186603c01c8502c2140200c048034a40b800362040c16101d1040c4095165150052030b2410142007443c1c01010503500b844606d80c4100140e9000300301c03c04401120200c03910542d0001500e40b88644154208030010941c0380c1490340010802030300f030342d0381519590b903c10b81540780c070030a020003076014891035104a403c400907800303040568001c60507680e04569a80e258030000c4642d50040b56000102e11013002010b8000c1d034201c00c0d06131070501401440c0303000c000040150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 65380272 1250 65379022 65379029
    0x608061911120c0307030b0303072a06020d0c0c050405091c0201020a0f1d1302031005040219080c041d0105040b010e0d021c060204080c0a05011704030e06070203101d010c0207 77
    0x2103c08000102c0280c070a8002c100c01d41405001d40340c0e20480750900e280e844400b160307410700300588904111429403189001004130b40703840c1e01924400004102c1290140307900d01c0c1c01e40340030800c1040420141d0780d030302c1424045d88800f001800c0b8071680049220018440030101410341e4818440700b010075400c030408500c0070035285000d8001480c40007210f5036440d512a5000e8101c08031a00040442a241e030065009550b45480c2c40c0005984c0d100b084268443d040303101c000b68101c405000500d60050803400c2e000085225454100f94840010317500e81d41110211f00c0032811a03500400417402c0c540706040000c5028a000c40200c001c80700841c56031151400000c1c0204a4944000d0b6011048070701424500c1e0f0189082d942d69a40d85120f5555013034241d8882d12a410b14140040d696010300743c0031808400b0071004001503030315030718151a540c01805103da0040b408101e0000181c0d070601426801c1014030300c000801d03e260600e1002d19141c01c0c00101c2a684c50800581460340d000601d12044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 65381522 1250 65380272 65380291
    0xe060f10090506060d090f060b060a0210020a050412061b090b0901110c030322060903171804050708190c05120603011d0a05010507050f07060b04060806191112 70
    0x26110b0b00041400d43c03240c9a00c84668511b07107a00007041010601c03172510182d010301014809040103a042040318496004542c0140c0d00058014011524640217001070075a03906150381041ea44400c009820028840e0450b03c00b9a0745001a40f800d51200e10347d11800e01d2440c01e0300009080401900781442100c0005060040c1002c1002d42001c2c10071110307201c00406000d03292141c0ba41c08590050038003020418410710040c0c880403400902c608907100841c4c1d013016031586881d4512404008542c06240d4546030403a41707848110041d121800b560340110910b0703a400e046407800000301c524100041d05070f5512a402c103500d810800380d0000a8440f640c01c0c2c68450781c3e558980c00c0000e4010030000880b0004d0104950030840c1c440070104a040217540103d00911082c1e0b40c0001c122440d04c038032070300740d0b04030441402a60f01243ca1b591004c5aa1000500001052a200c0000c00e290401c11a0828040300100c0400c0d1000313050740c040c81c0d51440d80d180e038072410140d60821003081000010240a0b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 65382772 1250 65381522 65381531
    0x90c09120203070b0408010903020f0606030303070f140406050406030c0f1e09050a08010209030f07030308130807060e060603010f050103020f0f06040f030303020a0905180c0c0f01050a0e060f1009 86
    0x150b55040c407a40d00103080c451840303542c036581c554040b4060016000c09901501a54600f54010400032901601c2031303000070091481c41c1c0d074152013520460a4400e480f420441c252503034000420030280204042d01c150b40b00d00c1e455034a003680c0201a941c10109241c2003007055050703040d406400100868031004009040c103403056440504442c2d51145034410741e400001030038000f90b06103040d03004140170701b03040d400c4c2c0c1d0003001c051000a40d15074580c40010002000f40700010301e00401d0f03940840350b0910810318245450001c0d00c4040a9850b40701c412011030b0840e60502c0120f10b02441254040115518280007070740c034540014800d03034074164001e8000d50a92003041030a03900d2400f10b90190081200f480c0003d51281030050007034001c01140c8000c03425940e13010405d840e1403880d006e8a0700e00d03000130254a58400e401c4403420307004401030000a10170320748203510011007806003074410301c4503140c0018215208501c0c83c0c82c113100501201496000e140078403840304800241c0d00c040d171f8003c8a0124 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 65384022 1250 65382772 65382809
    0x51029100210050c16150606110606040c0318030f08070f05030f04061104030b0402011b02090a1505030d05030a06140a060f020a0f03050c150606180d050d0207030c090c09 75
    0x1800784682214982c00711205c1d658242001034081c031000f0088a0204e0400c641c1e40c0300e00d8207440c02060000c01040551100e000218a0701d041d40002c09564a1490301088541031044102c6410b6641c0d40c085001c22848105a03254552244146501010a2a2452000324003038809011840090721504030a5107001c00542849515080f61402c032095224299a4175940d00342002c03524000c0d00c080b400076012501211421604002400c60190010302400c2e40d52034500303480d802410045a410410103402200140d2550244041400d060042d1941647d80c900000070400300e8803603820120a000040c0e81021207a00c40c00800801d0781d0301d900348603c00760f2803500240c0c609000ca04004080514400d80e41003015408000760406002070802c9840ca01e1040c070b00358121020460f001c42e0071010030b00400310f006c0501c0700c1e00c04c10010094107480030140c06455031400e01000304010005640103480400406c4850f100400041c44460340400002501801c01400c1110310310450740030000c000b031401c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 65385272 1250 65384022 65384041
    0x507170717100302150307020105090703020f060306040605040c0306090b030d02061603240302010e090106050a0507020d02030304090504120906091502030d0507091802070c0e0405102910021005 85
    0xb6405590000c24801030203400f802802c40030b5104403a00c00055003080003168009100050480c2a40d5005083d0700031f00c00d80200f4020560002403070913603c03940b03403d000111519284100c10248030541c3d40454500e080110450548090841039400b0380c2c00740c0e43d01da1025034003159668010700d01c0c075501281f2543c0000d0440140100c02c0101243c0480904840800003802e11000102d0303200303032070391030566140504001c0080024420200410400c000c0204868803d60090203205e03c0240529840400c079008280b8540098200c1420140e03114240814000c0385901071525941d64540100420f007800c1d002000c030000c520521400c218201c1550307104034001c0c421f8400c0d00c0c05902c070400291400402c01002407441d445401c5842200c02540843d5901e00d0085078031041c0c00c0355101d8041c500d01086110b41007030042059441e40501c0d4400c03044404140904070100750680c1440c004030b030745402152107142c4881090380c410408120503c0b14690041401880b400c11014001150740e550800c0c1d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 65386522 1250 65385272 65385301
    0x140c03180114031003120f02100506030a050636030906070606082b0201110f0a03020906030c03040b0709060c06090203011508010e070803030402060417030f04090507170717 76
    0x4402d04008000c0000406480060030203e03030081c0070140041502e40f800380d426034080c102010060b046907038504031912058100b1500204094100c5001320920303101d00342800015a401e22030007820758444429414840d4520840e01c28040d403112500d0074124807959a441003124003800b403900401c5d444140030060344410002c3c1000029500c3c50b404615004000c100c0500c2d40c0b840c0902003094110b40350b4814402d0f0054035080c80d0790302c0d1600607801c0122900790480708408007056001c024000e040d40340d0201540c060003503003041d540c40341418940406d005d440103041c581040700d105070402c1001d50090f002080385d500903a00044681c400e0003c01d02601c10001d415015441d00d4400040520055104001c030b60260350984000c1034583c220103440b1f101c02e0744c01a60100c03051105108442001052740780140000045900d0020030080080c841c0d040750380001da0007a924010481c0d6990040401880c55204d00e60300301c40e606d0180d074050b0581551324500724000f40d544002a100c403146420 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 65387772 1250 65386522 65386547
    0x6080309031906110d020304020907080601020c0919020406020706140f0405040f0b03010c120608010e0d11030936010b0f0702030f010f0509070b03010806191b050a140c031801 77
    0x544c43d52148821540006984141c8049026001100c005410103120380601c50040c02c05034040e100d80b4010000304803004c00c002e4020403002c40040c2d10361400c00d040f840204001c2445801900100e4544007026081d0b0300d445074a00410042089000d184c03074100821034054400803140018a01244403401000b0308040001f150158a400c061600c0a6003024140300380b40d40107441440f00340c1e101c0c01c0e05802d88041c0298808030740e128516a050480c002d01d82e50081c078005c40c0c1144d082c55411000110034058001d900118040320055500d01e8460176040e0a80800244075429070551614000040034492010824901000400c80341d0865600344002240d1000ca03034000d1100b41c05044101004050036201e111492003179030750000320581c1c40e105a904a07034113203000d011039980c2e14209010800310a03100c409420390b50300c41030140d180700d4034810001440c0c50380c40c29160f0031491320203041c00a40110141c2c0c2c218007440792170103881002084800c1c0c0e450510030314480250200050f1218010881c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 65389022 1250 65387772 65387801
    0x90405010b040618060f0819020d061104090c1e050c1515040b010c050309090612030304030f1206050f0609031f09050105160203070638030106080309031906 69
    0x84001040300c1000030140510050703401c104845c90741d40c1007888600303000303106822268010110000449445031125030045001902c0c502c4c55101130380c1e5442c102c4014030418246204041030900c03011207544a00800d180341801c00c203048441450aa4000448007880c050070800005003058039080c0078011260401c0c0c000754076080ea41004200b2900d4450f1301d500042c040d42c40e000840c2036962040791100e104c240c2280c00383d860503c0620505c500f403040100019000103600d080008000410001584154042e6441c02882200c1e09002045419100000c2900034206001444296242c9680b1400500c04072051030b61484442301080c10b04041660b001081c00e402c2d007505c014500c040e080651400d01c5000200310641da05000040c100000c40400c00050380240701030f50005100b9403100b0b040d00808071310f40c100c600070710a881d102408154905261502c00c1e2000039100e090900500001e000080040d41c1044e00d20000b080d551001c5506040042100c00d601005001d516400701d03480000d1003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 65390272 1250 65389022 65389031
    0xf07050c01181104150e040602070b010b07050601050307210c080a050d0f03090b06060d0902030d1101061208190516080301230907050a02011d0a0213060f05090405010b04 75
    0xb00128103050345140b0a8030888a0021140c00314a4a440358079540512552035188490a0031451600030300e00800460703060364200702039400310780303403481d038a00800c41d000010760b580b820751421604140041e0320940c044d51050405200c0d10b282000007642d85010103250260308015400e0402d01107a0310b43c8500c03030074000d00a15209206c07001c200304844805980303c10300d449569140490444e4044040a0210380b0084041600303403030303c14000c0c0008441c2903804180030420360006802e111940c0b44002c0410404100000f0a000030700840f40104012289812004050f0711a01300f10b214610030440204490031103200f00d00e0140d41030341d01030303900c1c040c80311480074062070904e00e00c3d03000f8003403010603d209034200ea1160742c000710800040100541926120780341d918040d1a10f4000d0b29200040d5521010a10201c1428811900211100f0002407291071000c0c018403000c0c00a24040c909402e0030035030b0500801440800400c03c66809441d540f000ea034541c181140107050710361050768480e040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 65391522 1250 65390272 65390291
    0x90e070909081b0706090311030c03012a0306180b0a080d030203150f0a0603020a0c170901080c0703080433050a0b060915070309050612040b0a140f07050c01 69
    0x3820043c0080d0031410392080030328404441c000f6510040d40c4103141c0040c0c0f40440038000280440d0701010419400b4040300c0c2c1d04000080000c0c00c1d581e60040c0d00040c1044246400001c4070b0a0301021038144a60404200050a245074040e106400d0203000c000203440f01ea40303c0e01d84d00c680c0b2070301c0024500d1030251880380741440c40c01406036200750351035402001c40301d1544030103160000342c2000d040710041988071011300e4480b00760003075000030150f0024040003451032404183c48280015482e0b0726040c81070341c2c4040070400500200005840d014401c0303001e201a90020341c00c07115040c2c005030401c6c5003210100b08a503a800c0e44113503000354101819501048002c4649146d00b0580c0505000c0e10f0a01c41c080e108018403007c1d0040120680e03200c11155640c044c49a0420300038110b080c000d2030000031042d1a800404d100c0d5005902300510395824000300010b012012540c075030003d601540911004044035440c14103000d01500c03415144010704049a407550043c0c0c21507000c446500c3c0280000e610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 65392772 1250 65391522 65391533
    0x604080102070605010911090d061508030c070608041a100302040903020c030607080c0a030e070312080132060c0f0d020706180803030708070c02060f090414040c090e070909 76
    0x720b8a0101e03603041c100400440c810b40e0a0184414011034101d040b41000c10703407801c10030b6400c0700030015030743c80390b44000e0340100242d21400003014240703900045990700f00c250180c5281400c941d0241c403c0040307100500000455001b000460940303007100091003600c400c0d241c06035001c0d165100a41c42490045040304050300450132580301c00d03040b002e032402c5940b030305402e80309104200ea25500791071040000041a41c02503014540c0402100d00703c0d05c40f203840781e44900388110700104070380c04506003500420801c0d840d20200c82c412121320007480700700c2145184084a01c20b18112840c81480085213003005040304101d0000e581c4410300449410002904019441c0d0900d40503110000380e500000115240071964002e08540380440111724550301d0700e600301c03022140503100d03004001c0420076038005a6280b00103050120b43c0058125030301c00100d000c020840b10a01060900400d48100304404661000d6081084420401c00442e00405c1400c1c120704003030840c3c200000107480d09214000307001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 65394022 1250 65392772 65392777
    0x121c05072103050f090604020603060409140307050601030c06140a030f1401030c0501140f3015040606110d12021201121202030712051c0c020f0c100815030a020604080102 75
    0x8454075030f001107625170b00311a5480c2d14045801942041c02000400d0a034149580405807240c01141d000204056103d6050704581c031044007550140d01074001070051240015911005000398108500d5240c145c15500c50b444c05880004010b00d90341e08a4141012010f403c854034440003105030340110740c0c41e440c00080420302c90080d40c4c0015280c2c00020000001042102d00304980700d010b050400581e816246015842c030344050380b040c11400010306000500c84002809409c600c0e4040c0f0640f0300741c00502c41161510342c0000c04104006c24915071403540483c0c64400c22900303250020b17108210f94120320182c07141c03000300ca1480440c0000010300414030b01c5c0c0040300b54030039402001e01c07400008040340e990042c00c0b006050f5109060480010a000d20001c1a0100c40d500c0800104511038a601c0c1c1200c0d01200414003580000040244440090059050084046509262103510010028031541c2c004020309084c040c0151142c82c155030070800c043c6865802040166102e4840d14070354081e4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 65395272 1250 65394022 65394031
    0xa06082a040603021e010504030807140105220b06030c0a060806030106050a180f0b0d0b040203101b0c06060504020319270f0204090c080705121c0507210305 69
    0x48911002060601c0d150058900b01c0f070300106070580d40c00509031162410b4980c005040d0610070100000000508074038080d0528500a8100700f1507a08204106806d507800140344240c074880c02004103c4444440d50002c0f8080d4002041ea0b07081d540d5a00407a10303101c1706030080c9a12401200c0c00040e000d0380481e81e14440d500650082c0411030b502e9090018034259809030740b170081c0307940c0c0344100d0440055100499a51711518082031104144c404180d003586100001c3d0703030095489040009608042100c0c0a48000f01d000820440d240034420b40052042004480100706600e124001801541d03004038000c1e20000380115a20f0408148000c66171707612011200410707082421025400000c80714030070703a4004c1040f070b003243c002d050b541d084625076204004a900c05d039511a1503000ca6683d902d642c02a002c0b0400400605003490200401400090a0741e185948450f81c40c808071441078900c5a480c0e03009043c01c82d2156811b1038220744001455500a00c145080214110ba00e54180c0286018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 65396522 1250 65395272 65395333
    0x40909050705030318090702030d06092702060306040c050c0304092c100b01051902010c030e0102130605090a150810050402070203120d020408030f03070e0a030314030a0608 76
    0x42a07035107051513264055011080e121703040b030081010403400c10200c3c641d4424203510660385400c820308103013004c5a0f49500305042e015590800001d41c021120700a5000040410113107100720b141ba400a80180b00081490f030240341c450020142c0c0d24040d070159141c2c29140d00550341ca403501e134030a0030001c200030001c201c000c41c0090510841d8019400286450304a003001a00c1052081001c035005002d403451001c0c10814100b000c103000c01d01016030700e000703040c26600104034054496030080c103032520f403586500607034410010000083c07090000001154002d04040e40c540e2072000c001079888245a100802c202c075189003218403954403582c82c074410740c50f20408101e0703a0344501c00d0004a00407444025010380c420519406541590000b4016060401401501c0d26403034042d26420350b00b215409221145000c800d100105070401c5c903000c0f8036502038401d00d50880c91a200201460007000086025000c00404903a00e01900e070000009004120100c400c050782000702400c60300d805130000c0e80d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 65397772 1250 65396522 65396533
    0xf0f010e01030308041704080d0207030b0619030609080c0f0d0f0908060f04170f04050405010504050c04060804020406170a0507140f042406080115020d1d1504090905 73
    0x50004184500324103032905591043c050360b4940e0758002040308642800b8120050a01000a103260304104400744054643e0140111501e986800c007010040a886139104607c042205841c86c040820404216900000f0101d0340182c2307405d155a144c4100006000f10340603002c2260555000082c40c1840c03008071f0f43d100c4461f030305207031812078500941d4001ca040d580c000d00c001c2103e02e100c80888607041805045004803645404a4203900e5030300c81e241c0d8096414010500704030604d02442280c0c014074003650b0034042850000004c1c6040e106a0141a040c01108000318042d0340b02c030b0b4011000383c0240c00084400d0780b0300300d48003980c0d850f80301000c80b524854100003040480788039034844500c401c054408201a400f6004100c0945111401160810075051a00f50131082d01c001c2580107160300d45401e0800d5044c06e400130758014a000c403243c02e551100310004845540324200f010415030100743d101c00440301100050b040702c2041c48160100702c1c0400c002c140c0a030b00d40d001280032403140c0e013180c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 65399022 1250 65397772 65397779
    0x31005010f0f030b0a0519090506040e070501180503031206090a0c0f0509130203010b07020310020406020c0f0f0904060c0306090605030709050919050313061b110402040306050f0f01 80
    0x40c0c00c160003403004800103180140d0b42c1480c5000740c0040c541010000c04200096445130085000e030345551912101d00202c104041090400612a01350017020940d0240a0a8410100b260b40d50100e8880d143c100f210f1080c50560b100700c090919000340a00070f090700c0d0794107845030300144003c8040d0340b90b8ac49034806102007a9115110311540c40d48403041d4039650084c10180030266101c2e0081c007180d541141c050400040b0842e000d00c000d50213010700400064940840e801410300d04000003062001c3c06104000600216400192400e40303e0b8040300c00c202524a00008a902c20003c000510340104031b0109010800c000e580000ca82a202d13aa820000c01d45d49203408815603445209940e0582c000740d2050106004e15004540c0c000c2804007204c13450622022144042221818103072840c0d08041400814940d18944402c01031071300d032410001c41c1801c0d90fa01c4001c03040d5a04000c05488403646e02005a45981c0c05550045030441e40810030340c5009005110a030700c040b101490440c3d01e620010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 65400272 1250 65399022 65399027
    0x31903050712020c07030803070e032508031c0209041407230a08040f030207080a080406031407021905100606050403050f0d020a110301060513021e04080a2406030803100501 76
    0x3241c003012034600405c40c2c0762541d16210f00c542d0025184004008201200344035540b8200b00c8001c40350308008e4800e080c0b014050800b1380321012500000427a4104210035038800c503041c0100403004401003001650b840c40000050b00401e010005440320059840800c46002d402c00c1644500524400483c1100c0741c40c02110b40043c401c09001c0301c00319941d0300118002c03071019102544107620a004442001d501c1c2c48034176190210f4620100c80e1040005001d10101c2da242c05083c11105030b240f4100074505020001944484040e240a43c034040301e14141d0050042c104240c0145504c1c040c1c0400409450b100c0040080d0300c640010364a502c500d00f81d420803510300068220400034681d01a005414a903694101404004418254036640314123001c034071503444a1404100700700c1c910005a4411318218110001e801e41d00c56490b0307000c410b000801c4080004074070701103001e81c00440020000622498407146002110034000c0d140d14180c408420485920b00a601500e01911442a12566074004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 65401522 1250 65400272 65400277
    0x120c19030c02030d0f09051c0f05090f01050a03060b0310060905180103020111010b04020a0c030809070b0306060a03020d02130501180f0b16050d020105061e06041703190305071202 79
    0x50f40100708210902c0e40c940d00c41e0030101c03510300021441145d140c40d00c1e0300d8a105003050000c0c00807481106043d03560003000603445000e075130805a0804000c0c07070000d1051001042c101e41442000101100110300c45c0d4052000703030161141064690070301c20f1094041c0c600c24060000440e0341e4031404182440c1190400c3c0a49034070703488010541e8210b900440e41061508240325003592114240d0086903514005802200801d54480304107500c141401000e516000d404881d003900400ca00f031003440d16041c2225800340c800d0b90419500d0789030001c124028410b12509007040d600c0860041400c040441e083ca084481c2646c1d044144014054108500b0545100342d1458020341581080044220009040040076022810074030201e60746806040c0f405404013078005035914000c00140d40b5007000c8101c1070501d050310310a0000954800b00700d491080c4d0254200701c09680710b901104200802c100d0741e2203190b40b01140f28907122554080d000e080180c68202c049015101d10b0170a9032220b209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 65402772 1250 65401522 65401541
    0x819050303010b0f0c07030305070b1e0103030e060d050903190906080a110c100f0509030f0906220b0c06010e071205040305040b1615050402090714120c1903 69
    0xe549564a00005200c02e80c1c4030049071041030303806205040383c10300c05028850003140280c4445942e41350b41e2401c2981e03054010024042403480d103200715507901100d42814103403507040c00c046420b48400310015496009900540c4001c40c00c01c010031041100c0400a0a00d49a5048032040d41009018054400045030f0089600240325a0001403c1d040b0130b406c400d0100c07208404031844e00e5603100da218240310039203460101184e02c0e4a008050b585143c42460b6211404901035810b20703080300107113540342c8a0102c1d014818030010a40c2995050140800d43c0d03210558426040425503d179006880303500120b0b0b20001e00d0044400015403480b00c00d091a200301010360702c003410b010f100c5240b040100f00240c011303010404244000f04440004000520440da000d0001543c02d00c1daa00e8103446d001c501c0ea0b8514180c40c1803105110060b00c91080072500f0044505298085000e194030740c244c0d50151200d00503108400d4000e1009841c0144020b0013445c4100d04a290b401c042d040003941030701c00141 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 65404022 1250 65402772 65402783
    0x6050603190b04150f020c0714101115160912030e0607060e0304080705030601080a1a040302031e030105040b0109030b160504180605100c0c09020304051006030605010819 75
    0x80c4640c000303240700b0a0079501921030349030307500365040c039901c00401c071003456030090303031456001031120b40d0141c04111410040641e086c4088040900c4808240c0001103003020780180036105007800c1f05d4000c2400002c201c00038451310400c4510707001c00d034040301d0b45020f80054081450030401003030001a40940140561700358407116804000c1e01c0038800c8550000200b0380d4010f90301c091410407041c080c00100300400c10f0700c004112142c2040704060815030180c0c4400d580b035014140510002c2c01d4000c822214070003500d6100050342c1e03036060690640c4902541c0390041032042a110040d8060000594141c950655080004c0010b100066a1008e00c9000c00361608441c0000a0f203030b10404014120740c10620b00e0070508040d501c2982d410143c9a803800d0400d01c0351964401c1c0180d09000d60340d40104c1106180910340c1100c2e68403104c0b100c0c0680e00628501540000004052180c10070000c15404a045010880a50f0702c0c01d00900a1a081c052106540075004048494503040b81ca180301c46500803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 65405272 1250 65404022 65404063
    0x403110604120c08070f0b090d1e03020903241501020a02010c060209031509060a05070903030e0f0f120a02040b010c0206040e06010c02030303010306060938120a0f06050603 76
    0x84600381c4000c3d1510b50100c52070340041020100203a46c810140300140c0c8104881c543c1402c018407907604008926269004110018141203c0c2690400001c401c1031094107006a403110400c01003800c220b0340800404c0d40b00480d0002043c0008840140c0e88181c52103120b02282210000049880b0103501d440079000544d288903000c00702d01903600400445030000d0489250b0307440380c0241c41d4241c000702c400c1030803500324000304081c1d01940d018143d82302956103403c0190500310795002e0320343c51204a040c0c1c00f42e0740401464000751100c1400c400c2212004003041028803540c80040e95030705031002c0403400b480c00c01c4804550780d4040ca25030410254002c04040c2000d0407d0246244244010105410006158000c80242c0c40900086000e580110400305038a42000b8201080c3c0344100d0b2002222900410640c007000c0c494600c01d040b0168507001900042c010000150301ca001c2c04550000301d001d060303018410005d040381440c10b054400e640c1401705035105020992102a007011094034001c08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 65406522 1250 65405272 65405303
    0x20a0c0209060a12080d061508010605030c0d02040902070309050312040504111204030507051b09040303020d110c0309091302060406080a090618050c040501030305041404020708030403080403110604 87
    0xc0c48202e0344600042c02008849654030b10303a2450114000c81940e019100181c100031059040c010b0380058030305084124089640000002c101905c144128420080c0110210700d200b01241d040380c144d00c0310001d042d521a5280e4520900950045508a0111740450700004240c14081400400140314600d80f905252a0005210241400180f0130a000ea0308100f0801d901010025803401640aa522182ca038109860040e1030031180c62803000224203d400a12110b54400140301c2d846a494034001d41c4410801510070042c3c90780e55080200200f01294002c0c0c100c0000025003843c0c0c6040318080c01a07162140b0601d60055140800380d04020708110600c1054003d200003500b003041c690000a0480007500c64408a40070301264400c2014500322041c2030000070800e56041010459041025525560300071b2301510841c03203680340610702e4146848007913845605956445030410f400554a20b454a0004c1207000c044804501089a0416198800f0000a4414452039210681d40081440d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 65407772 1250 65406522 65406529
    0xe0d230601060503070c03020c0d0311100b031b04090b070f090905090a06020309030d060305160605030907140310090809010305010b07080403080f040909030e040e010e07031712010b0304030f03020a0c02 89
    0x1586c000a60a6206844480d40c0b9a22030f8441e9034600780c080e43d41c0b016105501c01e130950401003506401c00c8110300f1700841403100d9801080d08401e80f182318003a091036100100204010f1714052300c000d03010b60307005010007c805030006c0b10b10346101841ea850103103c51300c034200c1c0811220180c80c0120250711030114200010704039401190000040400c4a0030500d03040242e40664245802c11105500014840c020340e640c102d540700058200e0f820110705520b4500d03101590303503500e48114680c26903c588135107043d403818411b02c1004658048203111007040f40c00c0009040d44400701300d50000346000000038000d120301e0309a4244e02c0e40041848d15207481c680714038000d80c009804428402d0302c1044000380b907503268030a0398000e9200741c5402e952940b036002048100c0364442402503090b410a1b581c40d6141801242c0f540980f03034030a101c0079400c4284da07010403503800b802c40b00c44011032080001144119464010b50b2250344a40d84044a0321003c0c04120203034000d8010715804100650540001440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 65409022 1250 65407772 65407787
    0x6010e04060b030708030d060f0e06130204090207030203120105010503040803070f121e0f0b060703030e01150f080c03010c0503060d03020a0b0c040303030608070302030303010302100e0d23060106050307 89
    0x28007551021454002a10000c0e0800e2680e600140d101c0c0d02c002100d0030740c8a8a8028040201004038480b08204c0c9841e48441c52204010a2684078910110011541c90304a0341503c000c2c1c0362090085480c0d128510700a5a203034080110500c00c00c054000001c0c1d0b0350320410450780305035031016a4a06640724044280c0f11140c0f455050401d0107690000143c02c5a2548a00030f400c0e0103055401e8824400007566008440e0303030041035080a070908480c45010f0f01c0c2c05080300c0d84985c0c945400900020035148050050030358803450174025602c0d000c00901d1041e02c001784030541c0c500300242c442a0030300d101094200d8540103600c0d4046041440060701d5032a00071540d6450600a0042d1068000c50396100080b03850b0032691000b00c8400410103100f4558103110740d401400703000b00240505c60441e0002a600d00051000078464001045580205841000b4405440b5000ba10314021003a4034507040840441d04e008140000c5003002100700710010000d0018121902c580303030a89551152481121000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 65410272 1250 65409022 65409031
    0x821010e090d05130806130b0a0903140906040f140102071d01140d0c08030a0e0103110f030613050a020909070302030f060111010e10150b040803030118090203030a030506030105010807030506010e 86
    0x4601381308000985620038043c1c60301c6918001302c202608041e501e81505621000307424008032905d0300d0900000240c210390620303240c03541007110a0f02c1c0d400780703030000c1d01c1d91246030040700e1902c02800000a481c880307060002247c060903000c5d075410740c0d110b00c100c41520361041311b8a24000480d400401500c0d0f401e480c0c0c0c0514000180c00980302550340c1d01e5090041015030b2020340b0365400081e00c03015060788035148000d80c3c442403809001d0b51500d0f1410946c0c50184018007101e03008004007148040d6902b400c0e00d00e01101d0307642c2c140a030789401d1525000941010248501130700300e880003e844180b0030f100303c2e0b00c01e01002c0500c5110f915844011252002a0140059550b50307401000c0f84203501003103103462400c6d05440110fa401102a664003141510354400c0309880400c2c0410f1041c50070210a583c1507400075584604034407103080c51400034002200001c3d4060000040780d0000e80c0e0b05410541c4150015802800303075036a500c0070f00341d4030380303152001030120341052005000503072480003d25000f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 65411522 1250 65410272 65410297
    0x1a0403030e0a200105130e0a02070c03030e0307090b090a090212070f180225020105090a030b040605010e13150b030106060903030201050c0906030705090a030821010e090d05 76
    0x7078280d08152400c1400324042d180e0f140400c2ca1080c0036241500c892010110a00c5c105090008003c2d204603031081794001d41003404079402c0001c01060b010b40c10b03500714a40098280c0c5255503a400c0261072000d25141d42c0f40240202507000c50012628000c50711849000303800e0866136611440c028005028030030080b0703403114501540700c0501504105980142000c0c00c41002d400b840c010708819140d2440104101d09401032007034684241c012400f15113182d200b0420240060000e10048943c0d2140104060303011480c1d96005c410300014031412031040d4880c010070465640c030342400c1030590504881e01881c400103079518a00007030700d812241d4000004c0440120706a510030300040e094406a4100c0c0300000c13005070081083c541d090160750341018119401c03e251064100115906110041101083c0200020000260740340c11070080010f5400481150301c401c544028200c0300e501d80418a441c94104c0d800200e411851b40e0740007801141706100803c0c040400301000d03039550304400e81c0b5424 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 65412772 1250 65411522 65411531
    0x5010603290115020c09070c0b01060306090b010c05100c0c1e03080a090308060f031501080610050f03060406090c0b19030e0105070f110f0a080a02010c0c1a040303 72
    0x600034000d0358580040d4081650320704510060000700000140c1c0b000072a90742c804081c048407070300807604002c8004162141801070b40c503000305969014000d02c0090210040c10000920640e240c0e00c01c400303446e0000020700102c02c1758001180c440a095001030142d410880c10258005c416a0002002050030704140b00c1e022080c0d11012042140d11600c0100800392401000405600c444825403001c0d000c0000c000f8208152001040140d009014500585075a1030178116030f90200500b445800c5010700200c007940c0c441c00f07a10b8403030b24140d070b00c00b079403910013440425a071a0051030005020300c081c1c024082a669521500e01401e4100010344809556110104151910100070700d6251750000d03c2104490070884000c0171900d4001c030030740b440d901d040240500698407115495258409180c03182d100b80104c1c4400e070030188a81141e181a01c90002020100500d40c3c014103440c80e0030350020882c2510440e000d481d0b41d582000010700e81114600784881c05a41c02442640040c0070345000107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 65414022 1250 65412772 65412779
    0x1e09010e07110f010b01081b040308070201050d0c0207060206060103090305030a020304020a0b030703020a090906030b06010e03030c0115050901060206160f050f030112060501051203121806071106010e13020607050106 95
    0x141407040b10b03c0040407a03511020a1481c40d42c000c54200d40100d07004031140d401e80c651519500e501c1c00756000040140303030009103035006d6a1041042d17554031100c009003003005e504450307806980c45601c3c0c880e000240c043c1d400001c400d58001e10a807030205415484031403842e03070384e418910001d40c4000d0040f80c0c001c00e11940400e2840c0b500010710b01c80c0085031401641c5440040300600000e42540c0016001402e04100b0b000080c0c19180035600907a0a003441241c10061000013070035400f0384e007416021503180202c400040034141d00304104a84061fa1162100c1c3d032241c0e03003280c03941c004603440d8a480d1011100440b0303403485103078400d0700111a403810f03e003814580c1c000540305510a0340114440303000d5044600a10905106190043c582141c1e01e40c0d0100c031440b40c45031a030150001c40f04007040414000b4240401030850b184601a001c030994040c1d2500c400c020788a034021501d2800301e8400e01c000450400088418240503a016105030b07981008544d00300b199542c00301400f01c80725501e800d40007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 65415272 1250 65414022 65414057
    0xf0906030f0307031808010204031a06041b030b0f0a0509010b1b03030106080109140f0a0b060405100c0b0f0903120a0e0706020106150903020f090402011704050106051e09010e07 78
    0x2481114440c4c1e84580c0841c409480d85007504c05d154002030142c2c2d10401c0104001351804c1c00d04604440c500130104040d541d6100003070008e000780128200e000410300d91070361505915900900003e9003c5030f88013200c030603141c1030001a07016401180e400400000c010f101620501010b4034000c21448080c502d0020f040c20000d06682081e808980030504550052242d4180e90280e6101c8850f444440c00080c60081203050316598050414820340e0303501c04010b0f0058840b1801c03036003c1d0102401d2098040340401d0024078080c910102907a000701301c000070410900141907902d004001c0c5030700a5041111003041d41005030030241204c1103a03a0703503003a1501107603018000c01e00100403030340002404510b020505400c041c004402e4204111040005200503650002e0500703900d8019a98610196114801607401200380c60f6403035100c6c040300041104000c015040901507990542d02d120440f9078614540942d44070840c4483d91007440c4000600c030380c4440443c290342c491154600381ca1205440000b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 65416522 1250 65415272 65415277
    0x60804110f03030c070603060e0705030907050118030602070f23030702040b060403051c140406020712030504030b01030f05070b0405130b0f0d0605010906060e03070605090103060e13061a0f0906030f03 88
    0x440c01f00e038881d40100504501d24440943c084000d081c03d52951070180703091074403003000c0d020b0700e810b001c0c840a0030b11a2201003c0110042c40c0d008504541d10891424900a1800c03885012a11812040304864110051402640c400c201c1c1900443c24440c0c1075080202800c0d0194403d070704401c3c10302000004c1002003000620300f504800c00340e4507010001c1d030014400b950841d154103600100f00400c2042d00d40c005001c8003151400950125020428036048a0b42d106da544007400c01050000003009003c002c05400511504c10011100c80c1b540c0c0f070b040f400b0742c2c2c00f42c0e10999a1100100141102a5500740c118510906004000760082c60034003001a005407003001050b10929038440c014064004c0710722a0a003c0e090300d00303210720709101040020703540e043c0c0ca000f02800c129022401002990007508203c001d0540099102580e141250702c10240042041080da040740c1448942d010001400c42c1d6064400340182804030f2554402007440100c0e000035011681612032144100d080c003030305001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 65417772 1250 65416522 65416529
    0xa02010c08030615030a09030810140d0203030712050d0f1401030201111e0a020906041a12121603030513020f0411070803090601060f0206060306040b130204140907060804110f03030c07 81
    0x6e0020740000321707040040500600500d0402d074001007890500001c1d102c1c7d03860b03070400401103c140356060400e201080c114018500d00174a500340700c8503c01c00194009001d000801240342080008032210180641a0f8501c8052881804600d01c014400f5500c1502c00404100b00f000171540780c00703e0b1300fa94101c4442c0d4084075020703607002403914101310f2812404054111900b21414010b1042c98040000c401d028800098881e8010a01c0b22120340010700000c559070504480450701d40b0300d8241c2d051600409030b0011000646094009160b1030b40d9030081c1c2c030055401920080e01404540c041c0b000602c4c580803070a4128500740b080c18001407044008600c281c943c0c00c050045035250039009421615070042110035500120204140e945000510903800390f0080d81c04c41d480c3e284c0302142642c103003840c0b501942041c14030803103508948100c8441e40c01003094a04682010b0780c1c2d90003c680b4540c2c140d40043c45245240816081d40c0341140030f1a0f040000101a00c1c0703004070064005240035003c0e030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 65419022 1250 65417772 65417791
    0x706051806030f01260a0f1419030e03030d0203010b0d0b0612040602030615120108060703020901050d0f060f1205010501050103020a050d0e0309030a0503030a05090a02010c0803061503 81
    0x6034500d4103402000c0602015401900e03818114244140300c550560b505000741041e110089185507240c4078140d03070315480710800e40c0a40c1c018141c182044146480300200c26508061980b03403550481900141c2c049000162000000c0c0c02c0c039240c0c1e02114940c100070b10059040c4828803903c4080c078094402103008107205842650342d0081180b507903080d540e04a403500e11822083c4040f070007002d5808442503020750301c00c0b401a906d549880005094180c0ba91204c001d01a0100314121990010195141079800700ea00f16080381ea10a60201c00380c1c8104500e483c00079809000d44c0131007c049400400c4c4004807640701003103035912201524003815440e0b00034100c9d10f01c48038913078080c40400e10595025000c20310f400d61503d0360003540a0650b100d2040003c005c541d0344c003040c4e0700340501841134400c0c40c640281030711760828060500716601c3d001507407a245e941d4078000106500d41e9001404a6a0550684500c01440015110111903070002480560003080d541d0400e5500c40000000398810368141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 65420272 1250 65419022 65419027
    0x60105030c01030213030305070c1205010c17010b160606083307080105060315090a0b0f0607050d080c0c0d0906030c080105150a0201090212010621150f0b03070605 72
    0x8040515001ea1420a2814944100912031880000e64034640c2a2501800c1c031a642e50401d182104080556a0040e50900f0003100c42d032003007001c1900310b0b41921601d995101c1500130004021503d0200030701c00c2000d00300b01003280d00440c00354105202e03c031780c1c0510400555107550380202801d010900c800519400550f01c0ba0040151251400701c00380d14100010001c5854540d6002d0121401800f9881c1329013030100006074510000e00f4908811440541000450305001ca0f10102070702c5030342005485201451650070443c18564143c1d0400d9030014024a000101d90350150b809940191000c1030060081202c0d15406104100e002245015507540c54070451600720020221007580c80c002042165010041005541d1100707401c00c28044d100400d03685903002e020581c014815044000d4101502a0041100f884103601400858404650081d030a0f400c1d0a07500350440381000000304410705c01081c2070081e524542c8216081015a84005808031030740700041e1405046502070b40009a00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 65421522 1250 65420272 65420279
    0x70909050114150312030105010c060b060c0a0c09060e0402060904050702071d010303090501020f15060a05090c07050c01020f0d0804170c0606010905121c14030403020c0f0d0f1119080601 82
    0x7045240804184600f40038111f50511000030a01c61101102070052a00e440e081c1d0b8031551a801103400c4041c1220460f2450b4006140c82891440284100c142c528580300300020003080101d10340e403007550b004154a10740b05400c030800000f070070090041000c41c844d0746804644402e01d502500c125110100d6030481ea5813451a0003407115030305070015030440d080000303201103d8400051000b5140715180034440030741d84400114811405540c0180d9004c600c0a0a014861455074000e04001c1d020308281c170442d410400c01640d45c1c100307001e803800c6a540036024010450703101d401c0198105102d071070100228000801d807408290820007110800340c1000d02400384960b0800c503040300801d002d651100314035422520b0b2a84070012816003035240e60780e0000e40b01c01607103c1c80520b1a0205640c0c0d500e510307410b040c280290b4920741440030500551240e0351081462806a244415856001050341d03a880196500e04a01c50200031030b1a400c140c84090a1030f0300d044031203010001d048000000c041a40c503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 65422772 1250 65421522 65421529
    0x3090604110d031e02010b03030a050d0c0f08160309060f1b02070503030708090d05031b121306030c0c020a09090c09050709060f02030702090a02030612010c0207090905011415 77
    0x190544007a101d0030030030022200190700440c515048500c584400c4100405041c0164050042c1d030341c441d945030000145280b0711903088406807100c5034411104008007000f01c00d0540d8141c0400b10405c0124103c0400120010800004900011554607022a5115450f0340d44816102542c1c80c00f000d5070384400941c00c032048040c418004d4100644010718840e0300d07000119440f4490003d000c1e0886000148110380c036110015030240d42944401120355a9801c1400c10004003218017294215004501408200f43c03201020b82e149141c500380400b8025240c5501640100818200c5038140200741c8160000750f625009404010181600f0103c0d1030112803030f08403401d92060f0082483c0c18a40014172003d02d03400950481550841e0501810b01e07204050140d1070344c01034000c025400f0440101f00500c04215030051805604152540400740c21202031460076038004c656a100140d00c924010813603200103400103841d87c1e005100009070324041300c404841d402c1080f02c9401c1c555420003070400381800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 65424022 1250 65422772 65422793
    0x703290708040b0906010b0d02070c080d0c051501050102030a120b181905091504020a0906031b09022b0207140705010e011d10050f120712090201020a06020f090603090604 75
    0x141c80d1380180c0025130400001c03071024010000311056050f07010540c1c008002c6920042c0014111400441c0d100c010321250007000310550300c40c200c80600138503200c103091408841040d8140d8005802443c1001214031080f900008914848040c07940c6403001c0c84501e442d248590240c1c1d90b409000030900346001412a0034203070012011055a80c901020855034400201d11501200d10310b1818032850346450002400090325500300c44016403604800004100110a1001c003100600b03802e0b100540d61041502d0490181c2c0c90811840320501180000c03d00034045051600f070a1034600609040b0252112800a5038040f58ac8040740d00c8000180700c0d643e003010b01610100700c24600400118030510266441412116445000344404002d103032003140550203840d6501c0300c0300e1020703880d140c1c039908000390303030b03d062700d015000c100750b8012030165003040c2c0035030310391960103130010f11040300c482c2c1c1c89500a601c04800c40d0200302c002d1100c1c42c4166a848001e600501c0c0c0200103292a00309418083c0c50702 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 65425272 1250 65424022 65424031
    0xf090503190204020307050c030a03020306030c0108010e04030f201006050a0b12041502070f030806040c0e120a060903081503030a0c02060d09060507020d02060a020a020703290708040b 81
    0xd9002401070031100401074107001c901581680e01503180c0c3c40c0d1150540d250f00410401d05458080484c10104095142d8080d41c8a80c008404542800030004015200040c0a002d0186540d903410002000701c1c0c041c412901d026501452305100c00c8150080d150382602e80c8110601d420f4026902d982102d01e91070140c400030b0310003180d0101c1d041e17150084898175071203004031140340c07081b0b0700d0001802e0001211304945078151950f0155911203807490101428010342d40110046030294010410368101481101e000c502143c4804000f10701c84010440f900e101d1812620240c41940c488500081190154030034003482a2541d0106062159013605035001006505000381c0c420b002000c10203038040d0f91a4241501900e035a42c1e41c504105c0d6401c040d000007000605082c0c21f150500c20714036800114120200080c0e400d9803855241c4601000a92040385200c10042e03015200520200700044440401d919003002c2d68201d0040801340170490440403101d460111f1141e41c02c0106105603180001c3e0702 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 65426522 1250 65425272 65425279
    0x5010608010c0c021c0605040602072109060c021207080d09120309060c0809040903020f010f0203040c050108070203040305011a010e01020303060d03080604020405030601030501151d0708250f0905 86
    0x82c0e1010000400072609140d010740318402c469514680300348000b5403411441c1c0c0140c001e101502d850b05003071000e0750101c44100c1b016480049101b0422440106451b4420050f075503c07010385141078802c1b00c0c000046c101c1039a01c05542c1c0f0b140c1d204103004011310300003468141e01402c01b006540f40060954140c47e0b1049003102c481c15030300030010f0750141c80f2206035421402c21072009141c0e420b11050318052415010f400ca07141134440300c24990006048071002e102e0000030300100811504140607808281c800400100b050312041c0407640c01461f169610000c544104d82c1040d65076203500742900c45075650126100c00142c1000d44550380141038107024102030008501e1400c00c480800c020010740c6001404000702940494020380d01c1b030301200d004050003001c8800c00e50b140e040142c0200050301c1001c40c0000d0704a40050281e0300c2101080910b030070100890596940c0ca90b0688003844010030f903035291a8801801001d18644581184030b0503c1076890380003010281001070060310301078014070312 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 65427772 1250 65426522 65426531
    0x60603030f050a090326070302070806070e06030a0908070503120412050a02060f0403110109060f05090f0d0c02030114010605030a1113120c05090c18090103080a1d0604080a0501060801 81
    0x300303d50081080380440e5489115031910500030604034803003403400313a40449501000030f02241810360000d441820b890100007035482549851200340d40346c050b0005055040b04050000400700120f9074410741c00c0e00c0c01240194a020b00ca0740d25a410b5a101c00e10740c01c1041c100100f8401841002c4402200c0c1c10f08500f4603501e00a04064060350350301d002050383e0511015440002c04042c0b140d40c0f80d01403200104020f1003075411502d010000b030f1084815074103800e844c20b8000b410000001400c80c0d10840043c0107090355460340c100071181072410001c140c1e015034a80c0c58800940e40001c101c00d00034481541c0300c1e500c0b81003103500c9500303440c1c0c01b0008100c01d00302031100500052584c86180c040300d45000302c3c84d00307000031850404007540c400c1d44651f5100b4407080401c40c0c010034240c01040d450385030640742c1e26014925410801e80020a01014106d04014845078601c01d00511045400020000000441064000004900ea03109402040460301b092140384108042406100040c168440c000c3c071 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 65429022 1250 65427772 65427787
    0x160e0108040c090506010c020303130e130809010503220c03120801060207060e0d0b070305060315040f02130b0a03060b10080408070204050712060b070b06030312010902030a0b0409060603030f05 85
    0xc2e11003a45000c2c0000d51503903030011034a140c0c081d00e80885810360140c1526251600b9454003247c441480c410000e4103411400040c2c400000c0b030400d0804143d0080320241403480041c01152150001069a030781c1d803804400c1441031200900710403c50a2148141090490952402d100002d601002807000e01c802400140666078010031084103840c91807070408084004100000c4180a13104806442007640d0b00a003c0310036495080188035900c150304640300c0c50011803c0300b01150080b11b02910341d40386545040010300d0602d03d14003000d01d0541020403a100c3c1c2d600090f4881c0c2c515841203520340d568100121050404011440a50149080c00c0026140507125410144600c800c000d100d507a0b6000001c00752030160706206001004d0210402130300b074489104c0c0083e94444641950b07082807000004403540360000c12207640a00184c1c0985182e460180300740e0113900082c0c1070041e1705480c1c158880c8551100d03c01c1c40364907402000d01045051450901400030100883c0c40800c20104200b0003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 65430272 1250 65429022 65429033
    0x606050909160203070206070b01170a0305191101050901150510050403171b07030c0f060c02131107080403060501060503250201091e03080702010b030703080f040e160e010804 77
    0x700d40c806441028484003440d09507049084d84100c080081d80040c0120f07003c02401000c0d00c495058440350790596074901820341c585d03996842609001030000c0e00c100301c3c10f0003510134514001c0b240b143e18204803181c02007900b0041d09441d82210101001da54400c3c20b69440c0d030368000341000400003034441010501c04660024100d110307601025000031b031000c4035040e0030149030080304c040c4919006141d040480b140c03c201e899000354442651080720341c490129a840300201e410007224500d0310340389000021a824000d620b00300c03804262019a030744424030340c9003001c0d000074074100303101d020003941e2281545850303002c595040c0c208030204030080c01003048001001001d010464aa9040f0841300420004203d0140041280090a8a014000102203080d000c58103403034452090320344004683c0d90b075800b2400c070f51612000300d52561000c0c9003003000c07905000003440e52660800495152a85400d6580408a81540c500404044044041140641c40040701031050400d1030f00300114102034551 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 65431522 1250 65430272 65430289
    0x1b01090302010c0c150f0e0a0509041202010e010e01060618120b1306110711010e03060705180907180807030b24040f0b0a0b0c030403080a0507050f0106050406060509 73
    0x2c0c140400600c00c0e809000d00070f211400140310307044440c0e2200f006100024001104d59403a0b1010648544000603149018101c0005690707014000098968942e1150000300d03d40e5504d4409555950741d410811440c05e000c1c060011240000100350a450a1801401d03a040994161462025007000f88400c045a076040c0c6e20490300100707400c50b0380d1940d030b101d10294540b403d0010301d071615003c111855000c020001d4000c00f401a1301402030050010015210f079518070003c194160072040008015a0044003d400c0142d00c02500200440c24074011810b0303103405499900114800750702986441c60720314181e0003e4410300028003030b1149150f030b85030318014000e0501604031020000f60031004010240c400f0413020002c00900c10b029220301c03240000c00341340c90b8503401a5a01500492060854000c0350340002e503101c0190f1906241d40c4451810740c10151482081040420404011500c100225542c1412510000914600c1c00b01084225800d540c0b00c1c5081c071200344841d02d6207a4030300d0310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 65432772 1250 65431522 65431529
    0x50d030c12050f131a04060b040e031e0d06030b011206050c0a020a08090f0306100e060a05030604110117070203041d0402060d090204020f0c010b040c02011e090f120305091b0109 78
    0x404204c0113000e00c0d14080600c4400c102001d1240c1036020001408541d801280361707481c050b2410040e00d9500c8102c15164440c0210800348030040364459001403003810020102c9488410002402c0341e200d03134800214030020f13886181d80118011200050228900c980d0350000c2c150848640b601c4032940c0040d45440078501c000e000030102040d100703001d03252103440000c42c00c03009056500c81c1c5441c10304240501e07000e0180601050b0764100040312405d04821210540f00018020f00117581ca542c1c99401500c425404d050400070f2520503a0314801482c2d0100e40226810b0b0061603c075030401c882d03102c040e411401e0503074140c50080184401744e1035200c00c03241401075180c40407400e0011400402c0181c8104001c040b443c100004441d0301c940c00c11f600144014004803011300c9460f9548004030309035041c2d103040007140c0c03203100101a0260010b5000c900903d11481800d5459401c60b161081244030030410800400d86510410120300c60a0200c1c00222841c410b0320210f101311140001e204445c0c501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 65434022 1250 65432772 65432791
    0xc08010b03040825170901122003010308070506061005090d0c0503070b040f0504020a1b03020c04020a03022206020601150912060209150301030506041e050d030c12050f 74
    0x402d0078807407060100d540032400c032403d0101d410b8064196255415051005541400040001c00c2c6a02034000c2140e611800c16074850901c2002d600500000744500c582100407483c3c0c1c1710b0001c0c0a0740340d010146000b90b00030169243c0703480302803d0040c00d09500415940c0b107071490860598034107800c481a1131814809031100103e601c2a442c10420702c080540102c0e505114000d00000c103500701340c004005580340111008403035035aa0051100303031b0150307040800c040f40d02c5101c00c10108514800343d0560720300074411141c20351100d00116040307078401002c07000004e0700003c420010440c001548001c00420340d60f2541c0740e0381351020007511201c3c1030003018045403054114040452003000414080d1030080d1441408424a00c1c10400a5112a010900560000b101010705003910002c0d07038101d0f80c10034050840c9a6441d50354001e840580141ca40441011042c903038003080c2e08000340000d0385441e84000400c00c0c0f20b01c00117080000a69290480541000c01304000b80300c22000c03940e00401d102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 65435272 1250 65434022 65434027
    0x506010626130f020a03080307110303062b0b010b0904110c100203060307171528020a09090218030105010929060702100306090c0302041202010c0201121107150c08010b 74
    0x9140544100d000c1c0f5101a43c4221300410110a002c2d0300e10040d0f0103150103480e042c0c80900f805045c103032a804101c5444e6070000e0740035107000001c00c03030306000d207840c0c682039a00d84140002643c4a542200081c0c1107644e101102003a0115681494483e4814030720b0300b20206400d000e04006232940c1c1d9090b428141400070307008008107003292000c2004001420645414200c51a4060703041695030780b80500c81c00b0341000020105d100314010300309403480c1e080390400f246800941e0401400c065801408203038100035114100084c1141c280c0301a000003400b40c0c181080d03602042c41018251241a00700b980d84610303054103d004a509180c0e6401003030403a50007884240b0b11500012080e00a401d00030790040c1c1c0c4180b0503641c0c04c0e072542c05030b403c1c1c03404150f04015080280d43c04508034080c07400ba400b2210780749880324026601440c0740c030038050b02c145400084401014840c1099421070141000c80f10000b090030400c0010a4440c0002002d82c10820041040070b007400810f6175406114803120300200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 65436522 1250 65435272 65435311
    0xf02030f043e100305010602030f0307090506180405090d0504050409080403050a03080901060e10090209120304080102041a120105060c010e0105040b040203100c0e060903070f030506010626 83
    0x104800c4a20701c000c038000701c0b014a00d144142c00000346501d001a1058080c00c20090115020748a4541a140b0542c003c50510441c0a550f0355250700150109040c0700b001c00f80080c0313035030700c5030001c0407190802c2c01d03001d803031648140c2813100b6a60090180c8035a038000c0011003031059032000a46040341c00071140417522114504119072284a150800b405038099103031064180f5030030100c254000c2c04d205000700591a80e0300ba07400c1403c001a02d250500c8103004004000442c002e03000b5100c4000020500a501501410314503c0d41d403150b0310956469401081c1002511000843c02c00741d41c900c045d640d89440e98515081c1c690901c14005c00f8414071000c030310200035410035440715021105d400d00030021030800782090742c01d83e20201c508901c24410500650714401ca28042d0445188968a074280340c10702c032208010080e0042c5450607010720400f00700162030741c51021100b00850080000e0303c0154184280108400c506401607450441ca80d980700310328800c42242c03c0c6d4030a183d100c185900b10316 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 65437772 1250 65436522 65436563
    0x11041401062c03010c030b0a0801020703020a0b06280609050a0302060405270108030301150c05100e190b0601080105011e0c02010905100306060216030203060411280501030f02030f04 80
    0x30800c2c030ba03941561078410b0f040456a015446040c218000300c0c0d078104071543d075003a01e42c280d10400350000d005070000350608002846c1c1c140d0300c40e0800300041c5079104222440da0300e07483c2d01d031340c0e4a090000321200910800060f5041580322000e070000f40d601120503400c1d074006c40c80e10b210702d21400340146907201c5600c02066850f8002840c0320700d000c414410741e50b07564010030f0340c9070400c5c020240c0c2079086200300100c2d1303805950446d00300c6034004040c1c0314084001001400401c00501c007007280e030080440409070040004002d03e0420320501200d0031030300b041c100041802d541600301c2414001c01c5154060180340ca6021a00d0808071440d0404046c041480100c807400c440e07902c1f030354014094201a241e0160507400407405e072040c0d44e085629540803071500d2054401140f0000c0e4050300b0079408140802c1ca0303203650320842040600700c00d15981b0550b42c0000c2d8024950100031400742a540144110340c3d141c055400d4a4030030003000d600714140754020b0340000001510052290040716816800b004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 65439022 1250 65437772 65437847
    0xa030e0d0602041503060501030b010f0c0b0402060c10020c0609030901120b04060504060b09040b1507031b05061f120b130201090306020409140c040b040e100e041104140106 76
    0x1229001c0040107040303d4001034046c0c201c0d405154003003810413000b49101d51250030300c0902484655988950001c007911401a0f40c03101070800c0c1c0e003000d0b081150011480d003c010052505a20b04801a40c3e0762500f455a0704089028004c4c04181e0010400c0007003036a4001004078010750300030350018414611000042c018a642c0c0d000c0e80e0000d0800f180002d405c20705801410050800781c07002d00c60411208204034881408003025101c806091001c200403912848901040401050742e582c02045181c07550392a281040310382c0c041541d40c415051084050260b4400003e00d03c2d42c0b49085959030607036948003850001400c0d10032071a07030084200e040d68800c80e4907900940e04004115911030b11020300801404e0f203042528004400d11021070300d01101001207500700d40e14910901c1c101030402101002500b005491251007805c020302c041900d500129001340154403070b0308401080440e00062200395141c059010f9441403405004115030750300096451a00c1c4200c451022841665000429112 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 65440272 1250 65439022 65439029
    0x80a090f031706040501050a0605070302010605060408012310090902060909040302060907170a02040203072706030b040c0207140406080312010303020114090c0411090402070302010b120a030e0d060204 88
    0x40680142100c1815008542c00c4121981da00a080c0c20350303508001c0c0410b480c03081c0b00c6c294010484050400620784100050243c9030f1091002141d956620000200c440c4c03c2500080196556441c1940c0340000070856140b9034088140d00101e540382858003c0c800308061f11405a03800c0e2140c40038821542d800080355492480100030a127142803d0030000e5807920111427043c070601c1a054049814000f0024075030850720600e0040c90440d07410350030b20000e500080c0000081c4a401c2c1c08074a139401a242684d460711002d100308042071407900381c00a080d900c001a10f00d0140b403901204041e119030218065083d80c03400c4403e0f031036520940740032800804841e40814686c3c00007240c4540060000344880e81283c3c0070354002c0c06202045c0820800a1320103a852000962101101e0b104c1403c0640040c8200310301512041d042c1401c840c0898142e030f0000c142240103075910356400c03802d1300e400c0308100c9114420400901141a41c0e5902130a0100307030102c940e104507004040d1301d08103d003540440e03018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 65441522 1250 65440272 65440283
    0x31703060a03051b010813050a140a050a0302060604050601030603020d061d0304120c0603110415021618050f0112031409042301061706010f02010e0105190b120a03080a09 75
    0x10f012955411806084c0e40811150000d00c980000c00e1000c07551081d40710a080e003041c003a180c402c180390781d03d2000d6207000111881c60b00501d0021130120b4403e2040342d07429406900901074a140c04010002103c3e40100a1414189016024400b6807200d501488416038041c4001440c0402a40f85118030004509900560701c00000e001c68420407002c010305a052003000504075841e11003906030155504010b11030380c1018103002c1084201c01c4688164000030f1039005560030900092255481c103581038000c081c11201c581075400103440076200303055101c081a088001c0550405482c44805a4120005800c004020201000e0590444215503820b000200100101c4103071980c1120004103001d80c10185060203000094042d01450014007441003506006109648003801910b0f02181c84c03084d0700c00c56503162a07040c03c14900b44903041c02030400ba140850300140301c05c844402d84810010403400b03855842d00d000c480490000d00b000425500d418500791395514581400010620410b01511 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 65442772 1250 65441522 65441533
    0x1c0905160f030203060603011a1504081006080d020f1207020f180603060705131a130b04090b0102010e0c0609031606050304030806090f0106080c1c020c06010f031703060a0305 77
    0x48a00c0c01d440a642124400d40644101c4d40c1d620003054202d940f0003000d4212456001d014003400e1404c120044144400d00784210701300b07a1a0351005103017211207813944400d15078370b100c140f0984504220b403d81408045c0f005100001c14504125140c550300d00d01c203039035840041440c0086540382d404120408030040c1159000305182c0c007415107006400c0d01c44034024080d550205500d40d200b0f1003240c019000d403225403c1105d1a0240601000841e40e900e0012040180f00340c0e01c040d092545404000c26800500075140c900304003c2d001111021481b440c15680742c84800c515400020801142d4014102c2d18070340c69151080200b82020203110007003203500346805011a032250003101540c0a00d00a941d000307415918102484012403060f46c0000407c039401e0010044d0501c20f510707113070388842220300d400d081104d03048480000c0c424a126203200c1d0742d00881c0200c007a1000700841d03401020340d005d6450300546140c0790b03480d180c0f036542c0100c01c400400200007060758841d1a8110025544041102d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 65444022 1250 65442772 65442779
    0x312030f020f0712050403050d121e0608070927051504030207030303050c03010e160201061e0302040c080c0403060c03060b0f03090f0304141311040e0f0603031c090516 74
    0xc5060340200c3c41101c401c0000710381004030a05c900305032802d81f6400002803183e42c1704000240c4042c103075000c0d0030b0040c3d130703c4503503240c180d0200844041004100c43c40204e032031800e1081840c05e08626803c926005458209d01540101282c0b40e600c1c1459526510304100320481e0400c43d05101959010100d404614010310081540c001030540859010345c2d800c000301c4c0c6400d800c9000701d210a100d5121000d09078000318036000650032130446001d0040c000064899500e4907000c8071081080480318250400f4002007083d07051502420308480c4091400603024078200071101d185002e1400085d00c6241d8620344109594003a074814809000d40c4110030341c59008001c02107410750f100310f4400040c1e01030f8503558142680d000050b0b0f4165600312015012400304842800103080e017500c0300e1030100d91208451001e00c2c1030207004102401201c81804c91901d400701c00f003c0d040c080504168082d50040100102901840300060302000c0c050b0404501111a810b1039440d00c0010401e45150610112000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 65445272 1250 65444022 65444047
    0x110c030d02030315010c0804061b0b0907081203100303050304050a06050112060f0507080c070602130b03100602070b03070f030e010c02030903010e012c030d0e100e03030702070312030f02 82
    0x3d503c11203900e41d03030380d0900d0b410b20f00444401d502c4d01c9004000c0a000c4c08140042401140503240b1101100341640c10069191280c402070041070301c0101e07964101e50760600841d801445800c0c2036070b90114665155040c0a004034003242d040e84800b42c108500400410f0402c40144500c00d28281c0000052019584810103114000d860b5242240c0862804104810369040c6014140c441d1602d6110104241c0d0f5501c03400c03440381d1041f02c0840d41d05900700400101c0010706070009003d00a8030f09126160714007130b88030b04002201c0b03400020a540c46000200201c5502c0c07803c995024550745845110520f1256068005c1c054a807040c3c0751550030000010030131070b4000040c11140c4021002800002500c80b8060708842400324003000c02d91080045078103e01c68104900c450070020703400c03039180440400001046030f108805441990b04044001500a17000b070040c44a00c136500c8004c0c52850030704e6100603584a489110060001400c451072001d228000e80c000500754039156000d640e140d0500428 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 65446522 1250 65445272 65445277
    0xb100507053c0f0606011d06040b031f030809010c02010908010e0a0606060f050d0902031c08041208012102031c0201090b070906270b0c0102070201080609060d0201110c030d0203 78
    0xc001c00344403a03041e08003001800181c0400f0186a110190030603498000c011100c0000c981c05400c030001610910070b1072510343c0b00081c0024000000d400e9100d040c05011030004d01e59180c01000c100202407018000700d0a80812107241c50400d0918040f0325881d440107036800c3c211540146829480c2c503003c44a80c100100c3e8500d0000c0c0318090030051141c0f505820788258800740c0c4d01c0d2000034803e216070241010294408018580014100d450015800b40d22800110380000440009842c2a040c40104641d8900b11002e4403560f04014005604043c0c0381d0b05424030f80c441309205500350400325002d54034148860600d62611395042100c220034030402034080c080e07081040700c408040c0c10018180328420141c00c000c0d103a6036901ca000c605030304003920340004005203c542280f0703140200011403280c0d00005118080100f000561264103500024046444c0100703071602074544401000000e50304ca10b02e104d10710b9030900f03284c0e40c0010010f00c140d20b40300304180415018481d03264200b00d071f550004003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 65447772 1250 65446522 65446603
    0x60203010b0315060c0c2103160302100c0c150f02030c0c06060405011208031807140117010501080c0703030b030604140d05070b040602030c1306030b130b10050705 72
    0x160822100e040040c0500382c132a1030605d10b100e82041c2c084501a24145644000b24545080300550a40300702d1100d60039980048941000020703283c50940416405128076020190100020030034401d00c0d542c080c002100000e0002c265604012141000305942c0e40114061a860306c01103490b07141061010301c099100715503c04051050400244141c541402454160ba40540b0780030001b2040c1c0c4e0b104c4105410203401401144160552000502001c010f000300a01c0c2c00240c803140b58a05c04001340540305601d1035804040510340041c0150307604032f005560083d4480790595a0f40d917082c1000c0780200041c0010681c140100c01c180f20504c082d44035010202c1c0c0c202c40540d560100310705025a05446030500c0242003214510001d0003140c43c6601855100008032440707490000040040f035480c500036009400400c3d50b40d00d0362046428080e25030302d01900c4000e010001102c24400207607405866920000411200040403070800c80e0601074902913000700321062410211403c02803511810343c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 65449022 1250 65447772 65447791
    0xa1803020c0a050a030c050105210c04050916021f06030c030804052d0112060305030703030e010f0204030203030d0f020708030a09120804020906150903070b0316050901080a020313060203010b03 85
    0xc40c0e40c0c5031136601501165070041c50b0401c814600401502e2710f07003042044008880a01c003c1492403030a80048511654418007044c1d5036500744000c20284010160628001140c0d046161903455000512800343c2c0c400200382c5010b03c0400c1e1108400350146800061404500400020800035502e01400941d041100d1203546004030b4442c001d5002006d0a00b4525001c860006030101d50040480d00d0008501c5100030410a8583e00c50520f942e10121003180020394075406803400039003c3c41040c048104210701985030502e0340e000265240120b0b960700c01c1150380c032404031012400c20f81c101c803500c0781c2c01424240c0302e140c641c0c10341004003400d15007a02c6403e101540c200b0180d11504007a84144d07802030001c0130301c3d1503050a20009240102640c0000b180410800a8554040006400800e03001c0c5009a80f071810300a400004003408485205000c4144200d002507030700584209c0e4000070a140042e1261ba501a0510011024031000fa00303440c030000010900d02102c1c801148501c0c00c18 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 65450272 1250 65449022 65449039
    0x60b0d0f1d0703060e030f030405060709080c0a06050c010f0513060b150f070201030b1c020312040305070e090c0406030812060f0604090906020d020c010c0909020c03040e0a1803020c 80
    0x600050714400c1c12020841e009401111091000880c1390384a60502c01300082168100070001c00462190743c82901c00fa01d055200b441080801548078151002070032455003d446a2460603000c100c2d4248a8002d08061200100b03240310080000d6010f0710920140c940240a10b0600e200541003000c044002640c0050810350140c1d1581089800544039600b0540094035040b0302c8030454840740c201010480c101926000148050b644250f02c521001c8541910708104458510405203845088510307030160043c00d000030400308001042c03850407500c140050404c195242c40110307050a030078440e010f5100740342440200900a40c0d00c054034480e8840300e042c0ba200d40380c1c0410050202d50313003181c19610030380401007440740c030301250001c8a21501c590005814620303045140030980c0c10880c8030707207040d070b40d03829108994540c040740d02c20080041c210110302d800b040c810041c2e1280b0960154082c0d084420001c039250750300702e03441009070381c40d51002041e5026061500940b680740c3c104a00c0d204d150403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 65451522 1250 65450272 65450291
    0xf11040e071715010302070f08030109060501080906130c081204170606030703020f011b12020106050603040c0e0c0904050403030c02070b0a1b03031401060f030f090b19060b0d0f 78
    0x2030521041c40c04032212191001e0340da0304010030003c550b11112504054080c0295400140c0d82d200e019001c3d8030030602c698507581011070010850b412a071210781004040014400d0300e22001c11507a41103841844d45e6040392a04d400d003400030620550060715244580c2000c1c4005508100181003a111300d28040110054804400b40c0d4134001611840d6154101500400040c504030320f08511114042c10511f41c41046c1030758109803040701030b000707440721800740c14411078695083c4611000382c842155a98190705003519003442c08460390183d0442d518044020400c3c460800703040d01c8051100800611840c41d19140083c00780101d100c090b40544519440491044401e1041d21680c22281d41c903c8044040955001002c041c0c1c00e005400741580c0303180c041c080300700c201c01c194049c102a40b1030410642d1102d50040443c0d034440f0500e040b0b01d24001c0b100340080d8114103505d40094541c0b103203060900c0e2a00c040030003000c132580328883e10700002410842c401c14627004103842a820a1041000303001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 65452772 1250 65451522 65451527
    0xf041104091a070210090309030209010e010e1504090f1406160f0e0a05030f0d020d1701030305030402150c2103010e010510090302040f0218040c0806040c02010f11040e07 75
    0x14100d0000b070209111405142c550180418055849200744c412169840c004106074001c660341c518050300080c1c50380d0020710650030805401030041c415005540d540350f15200180d000c8450203440c00030700751604034020100e580d40e604405c900541005034443c03e600c4500c1d080c901040810309071030b03050240c14006003004900036076031000f500c0140c5a48800c0300d000d440c01c4460034241038401e54807500d04240450f95441c10081480075024210040c00c813002003c03c0a45491980c10241040085c1c6e40e03c52410f2111411501781101e40c1400d10035200d03200d80c80055852703440c00326010070b0800041650900400c0005400041c254a04e003c81041000405100072610090180321407003e00580100214140343ea4100c40e40500752600d0b030045516076001406071030202107601081350300850340c0c0c45040070107d44200400300449007041a070203028805400c00b01d0041c1060700c200d070344041c59044903000b90084002585500d0741049444042c000a0394960010f000c0c1c80e1101641d400007508650 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 65454022 1250 65452772 65452781
    0x70f05211815070c050f0706030c021005060105040e190510050a080a0b070c02060c0601030303060f05030109021305130f051c050301060c300309030201110403080304060f02120f041104 81
    0x2400240b407441c050340e550b070040d51500f020010032a840d00c280b441028020b0070500001002d040a590046000f085420000346000f49910300204a10300d400e080c40b080e41e820004031411640d4080d014207031983e8039005101002c1d0f0714159046410700382030802400ca184400039500380c801c100d03283c003405502c0e031080c159501012407000701400c2028011030460b6000c1c428940800744001c040515000c1102e0304541000c2d0203034002c0f40806c2d21800280407210024007003c016003003c0d4020032a0740510b400240c00e801190b203075155100d5803140030074509421015200074443d04411a10000e04076403402954607541c00b6550360b003040c078100305103080b1446101164100c400c02da4900314205c050f03444c0d0307007950b40b2421101c40078000354440c260350a030641514003817520465240000c40008500f070181c00c2d6141350740c601c1408001041b0600015042d8010f50b1780094209600144460045240e40700030302c07640c039031220840130a0b030401032030340b00701f441851056124042c2520b945401d242032000340c0c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 65455272 1250 65454022 65454043
    0x70801090308011a04032003012307030c05040506070803150a0302030307060b01210509070506190e03032206110303100605090f0405090a0b0f010806070f052118 71
    0x10b100200100034641e04025101846682030340744134a406d940707546480c2100d5805190303030340e00808220110034901d400c0c41000b01c000054500260301283d44101801e6490300102043c1c1450b50b11000145050b00c00c0c0e0a84002c0d080c0945500d50380c02c0e140c107290415070811500314001d203070340c0b002203030f1a800c0c0001250200ca6016009504000c06581c070172024010301401141084103403c061080c041030f503661005800300f144400141ca042141c01d143c00c00005800850061408005044840e4498884503803141036518044200d075503103a000a0952007400814989104100100c1d80c0c802c40c482c44510072109182c1b18403140780760304404907499002c2164889080003070280700304030160280703004045100e4004c281078814840c0c07000040403103006840e9202d580c2c0c0003140316801c00070002d4107240c1013803040c00c00c03101030b42c500a4065991036006000c3d50401030074151240d91940a0025903511409040c0804918540141c1e1200c072880119500e900e43c4201d004405116040421400c401c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 65456522 1250 65455272 65455277
    0x50c04030c03080f16110405060d02010504090b060d0e07050319030e060706020d05091c0810030311121c0c0816180302060f0a0305160c0b072a03020708010903 70
    0x480740b96803151100d68002600d44505004108000c0c04612031040312500e5403841514040326101c0d401090001716130008100314019102c50b10407201603078101055030211005032a0220b5650b6501d80407410314042c1c8241c26105e0340c2030403006040300601203814000c1d51003d400704c2d904820070064080011140040190108550203040d00190600c4002403d400f401090054030346a101e40081d012620f0490700345c036484d000310000c1d10300101c48208203060081039181800d40c41c208064040d5504540d031000906000368022000300d401c2007480350412201d007c507511364440001c1c002c100c00e0782580e0100a14518a000c140e400040d01808400d40110394003503c40500610850302550f506260380c01c12504241d840c04000016a81d031002402074640850403a51140034003c40502511006440d4582d030400b0340e4651003400380d018485080d002e0f0068281421070b21103c1003540c4111641c10300402a000c7e0161700b4050a1072000c40000715442a4201c1c0c80c0316903105155800c807800e42000400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 65457772 1250 65456522 65456543
    0x30f040e0703061203030b24120402040b0a03030905030c0103051501030b0301020912010204030b060609011407210c0b0c03100306020f210a050702010c08040f031e050409050c0403 79
    0x80080c15140d8594400d200d4100081d1071034441c80346454454210030100d0000c1c0d22007202030028200a03081100c0011400741138180a580c64019901a0140311040d10944102d84000740c113641e40c0750894801c0c2403001d400f0107402516401c00401d40c0005000703d502900c01e03004003242a51107486464424000c000b441000110341d8001100a85030103c03804ea07141d034081c01001d00320f50340c5513100c4e06e095002ca400140c0d41e500d5480c05c0100070b00c2c0140007070300ca00401c1c0180050350340c12500b12030072210601101c0d40d4821031071030240b014140700342070740d098181030000c0104241d4106d18130030140707402203040d003c840d40c0380c48220100380b100b16545520301e00207440800001c0d80c150042d02400441030301807030503c5c1c4a001c0c80750f442d19070200324200d00100030040c4100c04a55108450308410948003d04c0640f401070030180041c0409803000b0324012001d901001450f108801c04505070b5110a80700d650405541d100074000d401078000d6032069441d14021500e1124000110b404603503002071803c0d0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 65459022 1250 65457772 65457779
    0x80d050f040209041e23010b03010b030d180b04060921030e0d05030f0d022104080301050609041d0d09060305040f030804170c070603050c09090a050903251103030f04 73
    0x1403130340c4c1c102980f05d80c144045250480000d4064105a400c0d54034110400d28030f021070001d5a0301b50340440d4007940c020f900d000850b07030242d00e011485447e0415103080512810088140418030709825070311081c00c11001060106003540d2110009003116640816180ca4090041c031715074001b1501840100452000240409a0700344000e8090b08140982d095a04050000b0b0303e040c2c00da404005000d082980c0080c0a40e00e0307030440c00020741e51140d6418820010b10313080c0c0c0c84c0d101d14407042c01480c0c4074560114100080b941e0b0f03900113024102c4840c2c1903008441d02c2c0c17503081c0e581c0d814042950300800c2c1d0501c03010650a10922500b0711603600400c03800008019500c05a4000c0805042660501d41201000480040400c010310b22459002c0080000318a0300c04000c0848101920611840c0d408004038006942e5101000740c11040303a40d0002042c2c1c403400882460f5200740d40d01240700461440f010001c034924061841901ea0190400380b03500600385c800c05840c0c3c407a031301d1059440c440512092 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 65460272 1250 65459022 65459033
    0x51c030305090c09010e04020108090a050309010c0f12020105040309080d05180109030b010806010524030a0c0306080a0f020a05040e100b010c0b010803030910110403020d020d060207080d050f04020904 88
    0x103801030941800d4034040316030f0b0000700c1e9803024241c0040340030b080500240021540c1c4044400c2e0b0084140c0040c00c3e6000017a40c4454981c42040c005030b04000c0c12525600c244181c6201e0700079903c5d8001e480c0e0203c61204d180c041e0190100b200d040c0c01052550b60005100540481e145080c032040d035941c189085a81c102c4200c00c5c411882001e030401c40007071400310026100b5060705003e008110b0050155614000c10080e030326604000c100262012282d0710302c240e60301c00c01a40d40100c0742c03560205080c0e485900403001016203900c6a40140320b21111202404081031910903564025a650f660081e110401c2c442038480b0401c4048080e4071042481818402c0c5920070410f403041494038909040c010b4860b5200d0800030313001040745030000824010f290004200360405071030121401d0058003242040102d20b030089100282c00f4840c0c25603400c003150303140500d01c40c2c0c482c2c0c0440c00319201c01484c01d140c1110741210315490050380c0b074000858204007071038004074804c6a0042480c0c8103955283d442 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 65461522 1250 65460272 65460281
    0xa060203210c040306060305030d0c020118030804061b0c0c05030604020105030f0c1303030e040b030c062a07090c0f02060609060607080702090f06010318120806010504080a05010f06051c0303 84
    0x800c08a80b01408003000203101406007400441c0510011a21000d20041c0a012102640d036034a00303581c0341a000c01d20038410395801d900070300d070141881c036000d55450900902800704da17148101c01e9180000080031294001066044260140003580c10403602c0e4400c0c1943c3c1c010544000c0d0204805000007481ca50b80c500201e81d214210140300c3e410300703440358140320402d43c15410840105510340400c0025083c0f034801c0102c101d0044000b0f2400889800c041034162250702014400c0c507180303035120451109500b8065000c0d040d41800c4440d45030380c4580b83c1000703058001e5401d002488401d06c0c058100e10004610b4040d880080110304682c40b00b508015a5600008084505c818284502c50240ea981052144519801f107100b0f40c151070060001011a0490103402c400681c1c90081e900100d0300300c84c444003c0c42c095080607501c64480c2c80050300c1138010741d402542c041c40317000001d41c2008010b4102d4551884030a1090080b5520340c010030405658000c2c182d240d0000031411a40440c0c4690131 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 65462772 1250 65461522 65461531
    0x7060f020c04090c1503092109090c020a02010809010207020916030e070305060604200901050a030f02070f050f010204060e09040309050306090a11010f0e1504050a1d060105070803040f080f07050105060a06020321 93
    0xf03003100e5a903074071400403068910034500070000d44c11509053701036581240d0380da50b224454500031440c3c0145540080c2d0140006413101c264135400c2154070b107000d80241e000d09150b0b0420800c5500c2e295a916019989040444d61603000fa410411060f6032071a007622030790542808d4841150a002790721004403059045240300400b0181c031088941480c00140c030041254074010420701c440500f03070341402c0303243c4074a84940020310380c81004100110799000024200803042206c2c5071802d070f150380c00d00321150820b9800090741401120244408540009584d404903440340c01c80d441d5403100c00c3e0055801c0d1940c5500107000c00c11040100f029032401544240303a01c05040b00490400740c5940201e07500350050303000401c1401d00b25000c0c1c00700d41c60700ca50740d07940700000b440e0181c6030010a0755041072074000a00010040f00043d041c0f401000000307419100040c102a590b541c58a040d814018040c12080d180a4003803000150f0100e10244044101c40c555a50480c030350b45d12012541c54210b85a10050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 65464022 1250 65462772 65462777
    0x80403030207120503040c0b0307020c0f0d050105090d02010c020c0609040509010f02180312070320070902030c03070f020c03031801020f0a0303061508040507060f020c04090c15030921 81
    0x480080020701001e003030341c0014002d03130301d0946030310301440c0400ca07204158008110b0803a00f802040082a4001501010f9080c00e03606a9099000c04000ca21340f001c2e0240010055403c013810020758501c00200540070020039802842100b5061070305071b0710f45071001d8000ba0052010892845142419009a030308003000f100000360380300718525480126001a004c1d0403062081d004600c840d46000c000c200150038480e90318901c0c000880d54090005481d410040071003040402d0f54540d080001d10059000b0300410209550b245018000d000142e84225010000b2844c6000e501c200c0502c006001001200044d0080d8a841203103031000111055514141c1c0c11031080c80126685034000703100701000984aa03d0100781c132401c00e51000e007080000c000c0442040302a03010000070503000a40c40045486504000c0d480c410640d00890801090702c84050300030382400008000c00190104075401c03981e2003181c00d240798902120031416194003680c00707130524500d024900440038010740e09100903621030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 65465272 1250 65464022 65464027
    0x20102030c0d320a030e0a0807031205070e0d0813031401060e13051506010e04090c1502010207110910080f010209030607050703120c1404180e01140103030804030302 73
    0x91020528201901060303000243c2080f080065480004100a44445a075034882050754014201a40c1038001c220b0304104042d00d80e0444c1c81012000d000710b141c1c00d40c00c4030303040796122410308000d00f44100f400e10f0090100d00d458000740c1c2c0c0d2881000714841a00004042c0c0d07409800680b40d406860f0001d003202c40305413400391000400200b07500c10700b900a511810001c15030b02d190400d01e10440b60000c010f82140307080c0c01540c00001d0808282034182c8540111413654945902004031243d51900c03000c0d42c2c10a1801a4141c1030010298000702101d1440c0c0010460b10701b0068100d02f03038054070000030840781c2815200c00a40c40c00207211640441c140d8940e866050391003050b6440d00700f92a400d4240399500146070700c4036080500a050703011a031410301c02c3c50300e00d075a40d00420300103081307840d41444c558074811168075070700c50352512541340030f43c8020326111919462640e00c8095030304505416123144c9a803000c5409018040c610899a121080c251661710b151020340d507210000707000318101030b400c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 65466522 1250 65465272 65465287
    0xa140709020406020c0414070203030f15060304030509040c030b130b06090904080c01060b040515030910060803271f020a08070c0e090a050705010309170a020307030909020405090103030c02010203 86
    0x881c80070380024411a4000c045d1040745405100449207141d18071030b400c601c00b40030064204d40000c203c90700001c21441040890b40c0303040e000102c0702d00c16400242c0c00400002808141688500542906c12013100c082010914090059040325980c4042d6a040740481c910b80103002210341c042c1080e014040e05880c900320381800010802c06007100d0403110401d0100f01d000390044240b248502600c007120304641786c1800e02c0009015001802480d503001e44000000a05503031042c0044021002d840c2000d000007522040380700d03100d030442c0e85c0340c0380c018100d11409c1c107104104041e811000d040140c51080074010442e0f0a08800f05065100801c1d48a94082000012610310081020a004582c154007890034030349405c103500c6c40a0714903101d03580001b002601240740856200222042402c00091424031441c1c8242e1074411002403040080d00440c40c0c00115802000900c00e5a129503aa02c5845468141c600101d00480c022682c20186000043c0000713405a4018039881d4014012241001c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 65467628 1106 65466522 65466539
    0xb03010b160f0f12030b0105071101050306010507140a0201030b09060109090b0a05060d0203090606010c050703060c0c05031614010c141605060108010501050f0d050a1407 75
    0x10740910820005041d940c40c25280e80460300203510195400d2034820103003008040c034003203800c1c4101c08040f58070903021104480e50016000d16007107080401144d103034000500c201c1c10b0201c00c11120011500c800b581c03000c0000500001c00580303000744001801e0f1458100341c903020740d44800038002e55a070802c090b032080d612003481c00104888003000090b50103032154880c0741c024100240b20f92501c1800d4000f14402c2d254002240c40346d03101c41c00111800c0e8156a009092908001e4090000802d19080100741482e14070f0702c40311035200d035114607065070700062202c8890101d841e020400c10100404d44010a0b0030f81000f0814803003580d401415150f2101030310f071449400005c8581c1d0b24000c082400e444590008120360540da1200c5141d4001c12080c02000c2c89009811102d040300d10340218541801039002d0007030a901c00340341d0381d29000070581c40345401444c080c81402045810 = true := by decide +kernel

theorem cover : BRFrame.Cov 65287772 65467628 := by
  have h0 := BRFrame.cov_init 65287772
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 65287772 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 65287772 ≤ n) (h2 : n < 65467628) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
