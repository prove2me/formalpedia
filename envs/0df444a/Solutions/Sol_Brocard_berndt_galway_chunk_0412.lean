-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0412
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:41:09.152639+00:00
-- url     : https://prove2.me/submissions/8f67e2be-6150-4567-9830-a381fc90cce3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 73920865 ≤ n < 74100721 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 73922115 1250 73920865 73920883
    0x30b011b0f1b050a050603090a06090201020307120504060905040903020703030f030608151b0a02060112080d0213091b05030402060c031603020a110904050c0d0309051e1c030c110a09020705 83
    0xc50700710804001740c54103021048030300c01c0c09414060000984656640c1303000b080090300607811440b0500068000038803004016115a5845d10b403641c80310320700034000301000344c5034211501860030310391039100081c2c0018031041070381d038141050490684a0b00c0118000d140a901000452140208004e030600360218024055507074a50581190700d081c8122070600d1041e801c003c001070f844800104800f15000c1c6003201e034584110b50341880c103001d0881900c1130307800071800400d824000c400100050400e83c0f10b5511190b500740e20201c100060394902030802d010040000c0e008841c00201031540c0d4100740200c844404180b4000741d00702c2c04a09000350307200d9001c98110303011003803500c2c041258030b44960840e00c119400002045140e1901c801d00c5809810709808030b09020380b009020515a5600030380c1c5140380d07020005c00401480310010054081109420a4041d13140210b8401c0442e41c80103a0404294001a01143c0c0415000c0401d4841140c1e6014156248c03001c42c0400c00c00c50042a0403207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 73923365 1250 73922115 73922119
    0x10302040c03020304230309120f0d14090402130302030312071b020d0f0203101b02061005010504060f0203040e1815190e120a020319030b011b0f1b05 66
    0x21094010600b50304030b120948000d040000d00070408480c504080c400021800211826a03041c91a010b004c280240000400c44540d07070005107417604402420040d2090700101031401440c0610ba14150038028407546a0040c0960740014108864000d4240000700655003d001c80ea078500a9040918991105079403003400a03c2401042d081c4000c0c4200102c1540c0c1c0040c1280003950f4540c0e140d080e0303012039040813a090b01401680504508561040040c0b4012504c4c86800b00c0318a00402801c3c2600140309905069151006100c1641d104040c0c50a503001402c1c2101c0c120741007038040c0c2c0307180140d911038402c03918000d08011865840d0030951040003100410ae82d90078824241c522105a8201e841d014008072540415519010701d81100d03d030ba61042d000e882120507141352554141c0c2c0075090300030150b400011214a100400110a40c200340b40c1c2c5810441110110002002681020301c0d0641d2103400c100c4c5401480308410005403665030100c00029460b03094010f13141949102d10441d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 73924615 1250 73923365 73923371
    0x15050d02121b031917070204090b0f070f030e070303050f04030507060528022802030601091b0906050a050706060e0411040e010b06160f0b0901090c0617040b0c160b01030204 76
    0x2500d031240c54072403502030b5004503101001750311510684010341060500741d03881034452030104049100503044c140181c22200400080e480c00304e1014203601510308281c4201842c10b10144074568000c651b42059a5044ca0701d965100080183c948860059030005401d5000785d060000b2080d030004000c0084001d01860300c20807841c040031128010540c10f0110000da00005034001c0d502011900020300081240c034414079640107600486d144c031400740c01c030f40744a035640c00c4c1c01800141c500f188803198500b0351922518450a1100003419806021030a8050040200326241005100c0e008280608060400b0011501d020f0400d0090130301c2a0029502640c902a400160440180190488001c0c00380003145070615a0544503e842000305042d2500f0303529980300000510b0032044580603c40c2600003181030206401c0c50824001c3c5035002d4000d1003200340780e00400740c1c1084031507035000d80c012060014613600e140c110540e40c81a101002562050203507001c0400490203800d80c1601e009403020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 73925865 1250 73924615 73924633
    0x20906120f030a110c0103050106021b01090816090506040e070b0903070509150a0905070f0c080c06010e0a050717040206030a0e120d0608011a0603040501150e0105010e030115050d02121b03 83
    0x15408c840d400c1c0100c1d1300603007111082d0105038a05008213100c6c0501803400610740c030741d03d03600c1c0e40c289504450101c01d1100c00074804c103c45120b5009007a00440704840402c10070071b20544c0181e07030304000d210f441c02480f40412071624507502486031500a00010b01805075619041c01c40c041e00114400445104804035000030500120701d100e003c3c41050961a0b10b0b2843c00ca450701520714800d41142110803031010807410b41011f5060040c40d0007450401c0000b4200d085c140c42c5d000545000804090811911140f40c034070310100454881d030455016604a543c94a807040d00768054040f03004110194840c00c0f03180801042100c000301068060300c441041150f031550541d0b801d039070310342c01a682020302c4c098103005145081401190891710490000035180c504d101880c0074483c2035072060341111440d10040099507001a4029070400d0f045000b002040104030401e40048118003860b400344070181a0310045454840c105040b003c901d00803290307102c2801c0019500000c41002e007901034001c11940e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 73927115 1250 73925865 73925867
    0x11011805010f0509072106060f060f05070507051c0609030503071b0f06020a02030d09210203120a021305060c070f0609030305031f030609030807030506010903020906120f030a110c01 80
    0x2803a13004481401c040c0078201d1911508402071546803c0b2000100c6145201d0320000c2e4861150303200074440c2c250304036041c61401001416400b028602802405000c01071000010780108100040d070300201d50840380c00750354100712800c031002d0840081901c0d250403444000e05420401030740c400d070207982d5100703ca4440d01d03443d9058000190030042c4440e280310f41010029440780c0103481d91a00e980b0403641420300780717990102a15000700003510740c2e622404161440d05062004410150b8a0307000031403408040004d02d0242140081031101c880d41d010440305003080502c032145008101c024030281d240c40300008100e440b0040c501c0344e0541c00000e504000b61480c00351450b1000c80342c150f02d4403419591074542d02000c0e50500104560100401d580100008007940708402d0500d0180e90707120828a0158005000c43c0d00123041181032040c0314004100594030001c6456100784241c07181c0164180c0440341e240790507a980990040d5010106800300f595901c10030051a41d11020f089819504807000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 73928365 1250 73927115 73927121
    0xc0503070f1205150103030e0310020c06190b0d1104150602060705031308040303030c0905040506060a050d09060e0f070504090f030c030c0206032703210711011805010f 74
    0x1c41c4034040701d100301e8100400240900e4038503240d800b42040e55a20b103035850355048030f00e001340c00031004551441c80d0182c107820200407075010fa4003001c6046292070a50750140355100c0c030081c8102402c172941d15091191a9158106130503c03040031380006004451481c200048134042e1804a0241d440c058120480404800c1d1010444200390040e02d9030f80c441c03960885840e40000c110500c0000d440701d01c1c500048800c80108015800381c0d07170001e18007804400c003c05003d4140d05c00307440b46090005000007540c1d6481118441c40003400c21741c0d603805052031a03802500b25080701605d0070389400011086c051010802800c8007480c0d4080d5039803c0c0e203600c00c02040300d0341000003070310195450407907000290048421515135402400c00c847e00c1051a40000c049034801c84e131200042180326060b0704082c0070900d109002e000140d014504265074907101c0c0045100c00303850f40d5115854207011810107401440c0901e00c030442c000080c0409555440400c848680e014011a038a43c80c00e042280203003070500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 73929615 1250 73928365 73928369
    0xa051803010b0612090c03030f070501140601200c03030a020a030801090519050a2004060201061710050601140d05070e0613060305090c0315091501030b0105060706060306020a030501030c050307 85
    0x43c410350402449090020f082d00380140301c0704c1a80b065a00030480341d43c00300090440700361030507075855440849281071030944e000410428041124070f0240301071682c2006010403980701021016407d604400c210701c0c9809200808650940000a5805600c43d0301052100980e40a500d0f8003200c1d0f66074665150803030360120394401152074107901e1142d04910540005811201c1d076400030801024105140c3d841c100003520407030707840c0300004d800c110980d028014100100304045804090098607000759072120001c1007003800069480c0000740f0103a00410440d8048028414115140d40c0051240d0b03000381007d58982e80451010503206c0c0191404808443d0b40d0100c0743d49000c8140d1500c0c40940c080c11001d0000348150103500c8140030103071810480c0154540407481401494201084403901303005030a413540b20080613507001400803c00e40101e050454605407407035036894041c1c8c00c100c40201401c3e0002024280000303951156254940c004c01e040c1d9000d0120182c10300c2e5202d00f0542c1d0b80f1201c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 73930865 1250 73929615 73929619
    0x1032105120c18180a150503060c0a1107030804030614070e10091a070606090209010f0e0102070e01080607090801021e09060706020c031213030903020f0102070b0a051803010b 77
    0x440000c0c25060620001d0300b100383c030030508010512903500000e5410401c404182c0558492a0200095030101d8014100e102c04e152101318220b5060002003511408009c100300003400c0b00040d03000d105845200b0181c0456501401e03101056100d10f031081c000d80c0180300585101e428000001e82110800005500580a58841d41c204144e10b4003809100c41084610200317118400c540002c014640b40d00210888a40c440c3c0300f0366804203031412501321000c5801000596106010b00c0510341d80040c004030541c0403d0412800c03410700e07200100e14100f040d81010108140502c00050f40c0c1d6400100103000f100141c486034911a25031803118201c2c024145003442c0c10701544400c0d00484c1201008191104c0c2c040c00135071404107591140400d90303020940c2d810480e40f00061242c02c01c1c2050004a410000005038100221030359200207044444e10302000e48203040102024030141e0082200800500d00c4002c803940311518075030040c090344c00c494500100614511021a024541881803110500700 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 73932115 1250 73930865 73930897
    0x60a0b0304022202040602010b13180b13020d0602040806181b0607020a0806010f06030b0d032a0b010510090308040e040804030803040506060a051e040c030603020901032105 76
    0x250381c080040101e21007500407180c030000c3c0142c6a0000690000784054411074002040d02007511301800707140c1c18030b102820b818501c2d0210a205004901440c1003c454114071441001d48896158000c484a461002940168421021802c1000d5a006081102d001d8816512141c0d541c85a40102c9607856064510301d030402c06405810204884403c014020050050b03800e011040c0e000c42d136815401d410414540c0d0140004201c0e0b01d80300c589060141c0024a000e00c440c002800101c1d9801c22180d000800380101c1c07078203007910f014512800401c2596080c1c540035440302d407400e2001945000b80122405010030f00c4158000c0760082d4501c00840358441e107807e11307040c43c001c1c0140002201a00440703a01d902003100102180f46c0380055801607000e140603282a040030820010388200c141d00c4107010301c4406e800c2610444800350004482036082c0d030301160100d041034044000741034540000f0740c008071103800071081c00304420035940031125016009030400c02014043e981801880c0d014008198 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 73933365 1250 73932115 73932121
    0x13150819050906180106170604060509160b07060902060d0905010c14030a0c09030506150301050117100b0a0f03030e0f0102010204031e0c230f0906030c150702060403030512060a0b03 80
    0x82d00c50710100d904c100c40c1000150080c1c50310340c0c0302a41c1d44940000a01d9510079424170003406060320995400180500082170741c0300800440d00d60045940c829400100c42c0414100309014890f00140d46040c1c0c01001c0369a18545a540b1740300615200000b5120366180000050020340101e1400b0740058200c411142075940e1503616201820b44a6410001c100102030004001041040041d002c0d4032a014040680d120500500d4210385050f07100e82e000c05010700c4492110031000c0307041543c10340c200c0404286030904601103801d000040d0700002ca0456010000401c0c103070300052480c1c0041c17084031580c80f1030f02504012402d0340500e0101070043c400d08500c260008083e440114075840c45030851a842650b111340d181e194520710022200b0207520070034a411a80f40c100d244018841c4126030040b214100076012030b40c0c49542c1d41540e805179440140d00300401540c2400d43d65040e90040c40240c2d11a260f28000303199400086203082580d1042d0301090301031400b0303240002a1800d502c00d55045039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 73934615 1250 73933365 73933381
    0x21c180b160503030705041e0b040311010c05191112070b1c0516020c0117010b1608180109090204030b070e01050d050f06100206060a060513150819050906 68
    0x41c0c0400010420041c096400a00048091014510518058480c3e0f61103a103004200744680d0a510340c00c851680f01c942e818464407680a050754250390704400d00b000b0303282c0e0800040e5420804c80030041c2c032601c10250b1002c404121005a90100c034441c1c843c0e144090440800c2c0100e1556111503010203402070307030080c01071100071800b034800c101010314005240f606102c5840308581068a00c0356480301b980000c0070300b40d9010414413038486001e11b001465005201520300b01e041d410300601d07030410b0000501c0f031141d400c1c1031100501c43ea005040c1541e04c00c021a41407269456a503030180c046100c1000c0054590307883d100380d4081701d81000002d942a0b803600c8046600415003100c560521000748600d80340f180b224864180300703050301042000303282002c1c0300b000307080052218908115441b100c100b01d000c1d15170305404801c60702c0508010f92141504110301c12500030707540140564030070411001c46101e0340b201c00315000d8541d260040140386140440d0000f5220100d68040b02a400000460740c46 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 73935865 1250 73934615 73934617
    0x4030f03081b030115110c0f01030c110111030106020105090a1505040c090507021513050a0b091c030204030c090b0121060b0c0a050c24030405100c021c180b 69
    0x40e01034480c51140300c4204030900b4581c2085e08510f18644080040201160300400b81e5a10740403440000c01c101010700e4002131491240814550426480380e50a8020303900032124074004164803002400483c8400603200d0841d042486554019820200880c4e4503403004254803a4042c4c100398030380080d9030400c0c005806018050011503564201820000d203148540c0b203568040d80c007035400351200080f000c0c0f05c0500044050a004c00f448042a158000034070002882d249055010b580c3c1210f0343c1c0c54130f034500d0901454001c50071b007a2008000442a50780d2550060040e41e1280301c00d0100d16465010b540201e41d540344c1582d0114a181c1c02d80201c0609107040c2c0e44090315415008155191079141c41002d40d00701451204140d40201c007040200902805500c101c0001554000e030141d80c0c2d40003401d441031100d0310100610400002040070310000b4051803402e01c80200c0d0a0001d05889400290340b290785100700080d441c410310302c880d0356902c10300b41d10321000a090000c1c8803007030401a8500740d0f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 73937115 1250 73935865 73935871
    0xd090b161215030c0905070305011a070212010209060c0f16140f2d01090509060a1e150c15110d1e0501030c03050f071503050601030b030f010510060504030f0308 71
    0x4940c018500c004001001d1141c184d003e01440b0102007801d0409500207415201c0c11b80010082000020083c80c288240c00140c950080d01121160005106040710034024460904055082000001c801e1540c40300020600c2d4501140412140281031840c00341c03049140f00e000c2e8105108010402803801d241c581014181424010000008800341402403080d400500e034122102001004210b546d960300025824010402036480381c04071301d00440010b1240c541e034052900c040781c5821807400042044420131004c1d01e205000c0d2203032440300210103004440045070132130f2504034034160845022514011218841a07000d041801c00d020f002040700942003441746201d4000905c07a21449501c01c038000c0a00a60140105501700350641c02d00ad800c0012061080145900030750f0200803080c0b4000c60520308400601d40041c1d107031500c0004902800b0720105072507143c8601c00c20000c2c686070640c031140c0510600754000d0449941c0d0b480035216030080d4400036001181e0061030700d0101c3c0c000e001240e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 73938365 1250 73937115 73937141
    0x3030a0e0c030105040b01140a051f0521011a0a0206040b090f01110a0f0f090504050a0905030307110106050f03030f0a050903120a03050a0203220510020d090b1612 72
    0x1a0301c458042030031200200c038291810300318072004000b4003a900d0008400b092050320155005801d003000f1038203800340204100c0702d807a80102003408445c440c4080d07590f20400400940055445a90a003108103002c1c0510034041042c000800e50051403041110101842d90f009080d003551941c41c1c1c8544824002c2034603001d405106040d0403d24028800d01c41c42c2500c9101240c1c40d400c003090300030020100107450109005a0300d504010294000054104449045401007081c0d034984403904c1c040c012084000f000c621001c81800301c8240c000f50f202041e01c0c1c05d000200185a942d50401c04080b040c2c030140c80d0180c00800200121500107401060340007082c0c20620f06c0d142818010074540044484c10300304188002c070381070211591501400342c020000507000c5d419400c02d000c0c1c0305d01c45180c1e2900981c0c400303003c0300c150b000c0203024012980c001c142c90b80215184d61409c00c640c005400c04078811215441100000352206202e040a60641c0c0503d40c3c0f44002c000600315040c0003030102070030100b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 73939615 1250 73938365 73938373
    0x14100e030c03030c0703050705010906120c0201320901020f0f0904021608070c06090f0510020c040501121401050403050306060c0c0d150c090b2d0c240903030a0e 71
    0x7007030301d0400043c2102180740300104000d03865418401d040081c5130300681c5c10090700e90300c00c020305035104502a80f4200c4068000951703207c10f007004d03801019040c2942000607661502003041d101070f03400210034446158a0303500a5034480350580e08070722403da0081825038040c80392500c58070411026001c00280900300614019a140c10311258074460901110f0060001421004009100c11407038000d1000e41009012076003422501c0c841c500c040d0051602569103401001e0a540c820000c08000240240c0304220a5841c1e82e080b21801040040c282e41e058a00104a81440d1052003903d00c190703096690182581c03150000c200142c2d0040b08400714620880302d9001040d52011380d0400300c980f19840854030601040304040699808a264105000c880c0c9000c0110f10b080b00110b598071000c0d50050705020039840040040200d001d00603030b000e2180803407500624400010500200d5004d201100040380d10140520000101103820308040e81092011820707000b1203801c03400356401188c044e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 73940865 1250 73939615 73939633
    0x5030d0c0521070602070803180f120c031207050c0705060306060702120f030307020c01080105091006031d070305070e061005041203050f0703020607081303080f07030204051e0102060114100e03 85
    0x2c0140e1b080002d050f5580d02d80041400021511070300c90032000030520003e4002e1415951000c0e84075111188110a0514000360440451070240202c402c1502c0d1005010050f0030003010062036904181a49006031180c00b00100da580742842c1900c0c030403040140001d00e40714503030382400030364920306085004a22800085a0b90311a051018600c42c170026401010741c8031420000401c02d001c1030388218050040c1009001115100c0c0300000143e0712107003400708000c2c91400d0400c80d140321510340c581840c003a0440100401c00d0202c1c1c542c0031101c44443c22010b40e02c0300c50400613400e48041d04500494801c020400a4608401324080090b01030b081c801d080c06010004d00040380e000003401c42c0103070488420000c120b6000180550008a004003ca405a5050b5409403044a010303044100281503a80090b061030f03c00d804580183c02d01811031030b503001613a002e0302141e900401170640540500000494010141400310303c20800003404480c202c20030410030341d00140c0c007003144e58060080d8101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 73942115 1250 73940865 73940873
    0x7061d0f1906020604150603020108060d1e08040510051201090b0307032003010c0203041a0c120f0c0106080a020a030f171303050114070503061c05010504030905030d0c052107 77
    0x24200007440e40f038000c4e040500c2c0c20320700008081100d07040c0d54091032074014180090303603000543c19808502a606541c3c403441c1418104c00c2504800000f170201c030040303000d5000300178850015204842b07098448600403404820b0540d00e0340120211003074100c030403c00401c40007480b504030b541342581c041c080d64410b9481e5114030071299040c881d031203030449074000050b910f0b0800344601101074403680b01850500e030030f016842010f03036003c0c01d168811010105a0300c020b50024003001c41100343e80314145030f844090015915560700581d203041c10343c0d441d0207000070701400085011030240d03600038184030085085a449541c920081380342920310445140243c107020340130b44010040755402688001455281d4a4041d00351141c150321746410140c40d5082c01480c5801409a07604072804881c8442d81c40003544034851005900c440140c000e60810b0280400d068100c10440165503055054842082041d0402d503405415400b00510961041c40c1e581c10b2040400300361010300c0f046e080003603d080c0752511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 73943365 1250 73942115 73942159
    0x2060310030b010603020901020c240c010f05013002031c0215042607020d1106070f08030f0f04030207090213050a09020a23030c03060d1e0507061d0f 66
    0x2100425030001d8194081d40c2c0401502b28052000c403684507003c104000c0e030301c40030f04c990f044940003420085040502c80d1402c3d0461118800f041c0b800f0032880d0382d03c28424198007440026881d80700012410040c0104d00c1d400720390400380d00030380100403c2e50680c1c151a181c00c0c81c100020110301440100b220703003e8501d07000f90b02990040c916016620740003440c401c040320740040c07040340c1c101003001800f00580702d4200100741c881d0801c0341c240048403110082241e920400600034050210391072544100100800554001c00b102d140c89115903940c000a680080340650f0041c026902910042081103080e030010a62910301c03c903c6e180440c1d980010030443d200a80021007903039000f29044c400ca903401607540c41c0e000e0113101002c8882055003080d83c66440043c00c0880007000010000300c29403150140b003440d25900403004006401211b1000f1801c40031207004a5050242c0e1000246940c410280c0e2007002000c1807034900318500030130030011129141098640c00c80c81401c038242821382159 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 73944615 1250 73943365 73943369
    0x40e04142410060815010e03071e121e02040618020d050c030705040905040501090f0501021905030606041e15050c0c0a1d0403090806090109020f0906010c02060310030b01 75
    0x84141280c80e540c54400410762640100001c01076008440c04001e200e038012100b541240e020410000c008052000480c1c0341000f100c04580c152182410004104503885400441d00e03800c040c0c152012034894808048009200e50040d00d00042c121110100b00c90b040b0715200c49601c02400060b8840d5112180010316490b0300d0f2494046074040785880c1e117440a8014268424240da071140e103945032450020300b190190340140b0801950f01c00c0002c0400c402540321060090304002c00150110b0640f42c054081e51004042c8070140e030000302d100b80c3d0300303000c0c0040d42d000e030000805844c02e0a0030014850031484640e40c11031030b0803d40700b00001e4840051035000c2c03400b034a55620503640749007460740b4a1820f00c48a030441d00500034032100304184007503100c00c11100da0303d8040b40c1940340c070b80742400c0b2480c2d016078220b5200d23802242c00380700364a07105510213501c0a1095409407009421001084001542201d0035070101c0c0c003888043c2d0061410600841e8130014503d554002141c40740c0f9482e210810036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 73945865 1250 73944615 73944643
    0x60601091716090209030601090903141c022803110d0b030c0904031710030302030f09030115320a030308040311010501060201140a0203070e10030b0915010905030a08040e0414 77
    0x1c3c85d0061401d0503c0b085026240c01d800c03c1c08070b1107503594003d00401c40e4100c20310100034046134150907030802c10038802504102190640d11140413030726540884000c40040982c80c0000d4800000300740c064000e0030201c51550400500349002c805811000e0040c0365400c1b589400b0703c4ca040b0070981e9641e1010380c0641e0180d5603ea88a500441d403880389610007904012260715803007001c0001aa00000700c9240b80000704500d5161001300000c079016040b2241300000006901c10003280e424011402e80c2c003007298008035541800100320500300042c2c950b4807410740248403c0401c0c4046401100d289030030510a1810f142142203c8000c0c0d03007161000e07001840183d44a200c81c03a1072644240c0c51b0740e00400394640c214074505041002a025101c03544201e03004008100035091418000d138810745021801519250710703803622143c0300c3c01c082005820a0302241455102042a080c00a08041c581d0b82c001c03201494035040c4040420380d00c20080c421030f00e00e02026111000c0350000e100c4400d00c2c2c401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 73947115 1250 73945865 73945867
    0x120c011413020f15090f040603050d12110a050702040b010203040f09020403060b09160e130603050c0a0b09060409050a0f0903080702060703020310051c0b010e090c030606010917160902 81
    0x90703104122030340c01c0c8000283d1240303103005580c0700351811360001c55203540002c07100c14840c86c40b0382d008100038200c02d60002d000ba02521200000709600300d1040b03d40000a164100094420078480c0050f60040140c1c00001507030500007000107090650100c008560305004482c01c0565840c20007008500350b070400b4800c2c0781c01190402c1040034038021181c0c101c46c00c03a0310140f24503124811280310512030b482d4104000824011641d680c5414100d0002050750600a02a498807418a1540c0b4a04c0e25281c84c00786104020000360003070340009480b4000320041030b0900d060320300032480c0045c0c43c0c0588030240140e903411904408102c2403080020342840390b00d1300d0341103140c0060f019052100c010100814940100704200e10a81890030090a80d41d007114440c00c4400070340717a21032400340c8a0100401ca4100c450001c9242e42200b504036110310022004c40725181421030605454500590313515011407240c2500b40f100c0410040030301d0301e580303103c0222644070340b100e81468402006584000d00d840e80c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 73948365 1250 73947115 73947151
    0x5040302030c0706050403020f1c050111090111060106081b0d09060b0f04050103150e01020f0d0617071409060609040c050a120e0607050304020a030f0302030909090f120c0114 77
    0x102c240700b900000e29050405504043c42d60300030500c001c03020308105104480710180d1000b9071010500c074a10781364000000b000984888003200026a001c0280d017070100c4c282c070a10000130b41002071941d069800c0d95680c804282c46012940c10640740b00c56600500301000c0c808502c111129100d00e0480034000e8101003051840030040c003030b08990081c1882e01075070a090060020503000219064015200d0340c001550344000f80c25140240149001012421000518421000703640e0b0400c4056443d840c421840e82035440c1c03080e45c2d0b00d41c0c1e00d224881401d00490041009847c002450b50343c401000360001d45044e170200b0000c1c04540060302c0950102d400403403805007455000f242807118010510080143c4c003219100ca50761000024842400c00100100281c00c54030f51501c100d00450b803041030459140024a0080e4a0307400c01000d01e40150000d40c0002c0e0f00f444009503104407000e13480081c25081081203070681d456401250310542664941011551425074000e80c9403180350b03001d070400d02c17441d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 73949615 1250 73948365 73948387
    0x210a050a0509010507090e060303070b01030c0302010806030d0801060f1e020f10090203030304110105070f0605010302030d050307270b131e0509010618050a030b0702210f1c0504030203 81
    0x1540a00102c1181c0e1400c001c001000da00880c8107416280c1c1c0154900c0035940760341c002480c42c454140014508501c0800000030810112038140940e407003600e4100707081d40c4400c281075403001c080396a54000348800c8e004010341c0d8080e6200481007902c81c0b40078410003403840b6548103110000090b1b01d0051f4003505607102824000c0c040740c80c0c1100b1020301070140d80d02c140c0000756280070142018142c10101d01e1181402e80c014000c8500140d0f01821181050341d203420b0200003410b091201341d02030300800351400308191045084a10503140c544a28030a0030055a013030214082c50010120700c60446174001c11040d18040c050411800c18281005903242403d810000c030040c4009810311001e00840103201030b503911000d442c1500d449290441c03035a05145514040c1c01610390040360011a1842c021081c0510880da161051100d90200d500e9070034044820b161441031842003c10b160001d000900705d082d1914010f01d540080341d0340f001c0720000c00d00e050a01700c441c242d804030056400050144450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 73950865 1250 73949615 73949621
    0xf02030607020c060d1a03070303080a05060d12030209030f070f031a01080316060f020304080a0e100212070303090c1202090c2a01150b090a0906140105210a050a 71
    0x5440b03101030b004051091001c80c0880c050100300039101511090002c040ba81403107240401e07400005c0440320314070760380d0402400c87c00054440443c1c03982003900041c1c0c0e41c1400c052410350346030710940110080d00c801400701c0094002d11141c40d80350150107148040d511040010313001900c0c0d24145182c1d080c0c81c502d015210118420143e01041c2050f0004214400010099481800140400005a60507441c00e030b001400300180703e81641d032010041c4010701c800790b00a4407030001c0030b850f503e050511364001c201e24004100258001030b8003052403a461000004013400d1543c1c441e05011640d022166101e50a0384106d80083d0401d010300b011110030340c64180d080075000910f20b0211442c2007080c143d03403207640121011400e4280000b0045581c5c0c060258480280c0344003c4460300c2a407a01c40b09420015840340b142c4074443c1c02107000215018040c0c1c0300d0380080706c56411040040c0c00c0344000544554012a40011224642e00b0120440140280f500b51045003503010000319450705903160030031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 73952115 1250 73950865 73950871
    0x409060b0406081207170d050a0510050301090b0105040c030603080711031204030b0c03061815010e0406120213150b03040507061103120a020f0703090312030207020a090c09050603040f020306 84
    0x8642c003070041c01c0490f09400c0101e0b1003050304201030b0349000786d000ea0066503611509240c80e0105184c4410000c9078641030b800180682042c800718898140d0380c0080600b1f03261000030103031040c036504004110524003680906c544080c0c0f421b01080583d5a92100c80983e040070406880c10003881003510000d1605101c00ca4003f40e100d1450360801e41141c840d10401d120080c83c0703241140c4004041000c0d66505503280700d0091200c0c820300300350301c0c10712404601c0229601c0803502003040c00b42c11540501e490302541040d684110795691000d24540c01704064280c40300c9607a00103a070307100c514500068a019107100a80304a004c001c0e507a09061070014078180d0b1030703404402042060003d503848101c001c0120742c491222132032003a0007500d641c2101002440b610349400f01e580e80000b000ca0400d90040c9a08007140d0240c6819103008140200175000da21503480003c4d800407102d103041c0310315942035122001c401d4940c0f800031541c640b904045880383d84183c07400d07190440e070700c0d10304011450108200c544c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 73953365 1250 73952115 73952129
    0x3070c0506030408030103030f0215010603090209060916050906090406030309030c0801060e010905091e07081e07060c0501090c090e060a06150f110706080106090602030a0e1309020409060b0406 85
    0x1242d40340903140c0416074001030000078108488000c440711040c1c42000411010844d50200c10f0465a507040701600400507000d08034000e41c22540020640d107000001e051007a03d00f107945507005a15a0740071a010b502c4486440c0c0d0116090043e178100b52103500c03454014510945445002e40d05500700380418034015807003c0401e0381041d105206101000000c07a04464401c0008540c035110010790600384140381280454202d80d00c500d07059004000611001101c1144064900440c2c0701c001c40104040c40c807640d108264801e01c010002c0300d2080030104911383c0a6000024085820341d545005021a94448803a0b15224170f85800b0680081c004241c0000c0345100400c051454101124003038010107170a80c050013135040c81460018016111b811030b41c644c280179030302969118580507158503000e028100000b905c1520228a0034000021520051081d8a40c0b4005107010410403540a8000034900100c90310f80b0101c00c0161560b000d10310441c4c2c800c94010070081d18007028002102c0d8030f0780c4030003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 73954615 1250 73953365 73953367
    0x308010e090a080403020f04180602090112020c0a0f02030f030d09020a05010f1d04020d090b040c230d141b01030e190204050702031911011112071d060c03070c0506 72
    0x40050710310000c60307080386d84c1662510400f40070080050020441008181920400d52258004000c40c035401010010004d886030400700e18000e680c0e20890044002c0400141e025100000101d680803001e030480c9440101101c112a010011f0b2509582110300d0404d016501d4404410452030041640006080300b841d00800701c800320362000b4816003e4803400d601041200c100c035103194407150101c4031140110300c000e00045001c0d207002007480300e0844094603107851440c1c000c122680e00001d11042503030840304640851860800f0000407144141080300d440c0c41c1c1d440780305c002c50000d0100a42018004030b01c480c0c040e48810015003510f4240e01109056046519200183d1000580c0d005120b81c06580029081d03035100020b82c610311034985040c0480440115000700c00d5840100d00c40304425039030003400240c16007100607405000f858200b403500034a9800051754288546000407010090031550001c2503048004076503a0b500c603184090464200050344024080050202402024151203003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 73955865 1250 73954615 73954633
    0xd05070906080c090d0512070b060901050306010305030304110406150509031606050d0e010209060f0301030606150804020105070609080309070e0f01030201021e0a061b020c010305060319020a0b070308010e09 91
    0x1183c0350f4403c55a04074031440c00e4200769003e0200820440225644503045190b46541c1c0e8107142c1202d503412900a03204070400130002c101400c01184c503034101c0c1e034801e0045055440c1e03640ca0640007002c5140c182e800a0307960000198071a0800c201035100403141c0ca640790744c0e00340c1009060030240c052060400001140342c0411040354058100c0741d01c60010307030002454103160050a4007905c554891176500400104800494034a9540114103c074031980040186603511a007207400c0050004614000c0b03007404000038003550150008046a901c60400042d00c0f0b509656104100c0e041030707501d85641d138000803091000c00703003241c6242d03000640ea6400c010590714640c0002c0d941c422451000d190100360044948050b030082024404581c3d000c24140006010910320380d802825595011006114103c41410203502034404d0034020036019014101c0b440071124100e03140d048c0320004a07004101d1410000c0c18a00303c4019203d486c2c4640d480000a52401350b41403800440504240d1183e0003500394 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 73957115 1250 73955865 73955881
    0x60d0b01050105130b0a050c0708071508150a091b1706062812051e06100c0f060e06060306070203030106120603020301020a090306050a020403020307030f060b03030d0507090608 78
    0x4400e0440d0001d1a00b0340e65041c0380d110040300107100d640003000840000c02d22000740c80d00600a480000d0f4458201c900c071ba5a6841000c0c0e071040c1038410700514103610f0612000d132074450718007154011007600c48280003441040200d406000d4590089007410b0b5200852180805003d229103100560b510b0005400c040046558a5090018080e28400c01000420f501405521031503807030110040c102c90481c0003c40b54020f081050050501c0c15114500740006080c81c5d00300e82c0c01c0c0c030080403e82000c40695286c8050001c5203945540c0b030000d1043c180d41d514005195402d0710355085200380301c04118028001291481d10750007030b02e802d00ca504120700300210070b0341c004242d0707045454a00e0f021a1707048500b080d800041c01d86404c0650154000542071030619040030402044a119000401c01569804041003c130302950100940c55001040c0410205a1401b01d65036036500400c000220078041400007495544041d80b82803049440d8410800903640101c00e8000038003030781c14901803038982001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 73958365 1250 73957115 73957133
    0x91b050f09070c14060105090a02030c1c0204080102130509010501020102030603060c0304030306050d060e10020306010c080309070b070c06090801020a09120c0504020a020102040801061205120715020d050906060d 93
    0x20164000c4200c1400104698851840020065044102d60204013104103945440f01c8090048034024246000882c19044403442280e206080303080c00c031801c1c02e24a00140c42c404012030b074200d441c5034003800b01044041c400c1c8014200400700c610745525840c600000d01401480580c040350640e40706208210080c0c81c0440c4580c0e00c070140d03c4c81940e80e0358862030241c0040550307800c0b294100c06034146d543e0801043d548000300040c5804121507213540209080402d80c4030840d02c050000d01c28003808800904000080d50300642e516068680040d00ca02a2401a401c02003050f100c2d0180f0200400000307810104400107080150700035482c00070040000760031042c09104002c0703d8440c0c1d070b04d01801c0c08400041c0001800d8001c009541e1121a41c030024080e41141c0a240255440c110000030390800c9805034110555020014000301e041d40241c03264641c102040c1656050304046d00c1c0542021644000d0025880480c40040c039070402d981c0c1103282c000c0c004c0001d4021a803d15862005c142040c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 73959615 1250 73958365 73958389
    0x905060705030a112a01050c0a0c03021c030b1914060a0e030f01050a0e07080d0513080d0c030f260601050906040906031403030c0a050a0e100201091b05 67
    0x10030681d940c1d4854200f150020410741c0700d0381241501c04600c001402000c0c0000704550081403952100b0020820720340e508940003542da024001c2e004100da440300c2800380c80010340c0c00703002e030041d2360340e01009010240012404e9030840002903960000d100c200c0c50004c1c40e5044103c84034000c242d030b45040c401068800700c0030340b1045105460205600828900c200031a4000101c09016508844807c030710700380c0642005d40d81c20144a017484e1800e40b00c6a80040e01d2001c840e6400b0052148a15800d000d030707544d07804415815101090440e000c5008481001151a07a00c80c1d951011a0301c15903050050041d10001c03c02c404102e620041c203400e208400359208103a0035000f0602002e17844610069689108030b10040342c0146021400142c003002079400142228041e4045d13001040d80340e5401da86170320040384d420b48401070a1124042c9244550081c020303250107420440c24807200240081c1401103485480c100603915011070004002035129803000b20010038490030801810b22000960510500d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 73960865 1250 73959615 73959617
    0x10f120201031a2d03030f0d0e010e070602060708010f150f0e040e010902030606010e06030106030e07030206030405030a0210020a051e0d0504050a1202071202060a02071505040305070909050607 85
    0x3c03032012030490528002c1c00c06100c0c00504800c00c6209201a08581182d40b00c00c060751410901078821007070901004031000d10005445a81c605450491010010301181180111940d81c540c2c40c40c09840081100c04080c011980041c0802d01e0510001000c0e170302d0580000c118075400d611300308581302d10030760b241030440c01d00e0400714000706003150112140d41c4030301c100c071364045d0038a40500b080754410340c0141e002c41e00a03030a60700c4030303521080196244684016101d400c00c0007040100401440381c2e0000c21000010001da0f041d076540d03500002c07040d0300203440c151215040014a0001c03107030100900720400c441100e0650407c0340800014110f80140606a07415208218241484590001c03c40308406100c1e50b04016505250414559078400e40d40c00701c4030080c240ca40c880002e400000c110085500d5500c94100b10143c43e42031141981140421109502c20550701241c01c0100180d01c8074415040d540340ea4460b403641c00d0103440c104980c1e100382c0c15189006070b0074010070408034880340d021a01b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 73962115 1250 73960865 73960871
    0x1506050f1c0516020c030105010501050316050c030a0f03051503060a150f090603020a17030a0f0c200a09020c031815270402090d120e12070608010f12020103 69
    0x1055540d24000400400c40101c040d1510040003e40807004401d082190581e900711192182e1800505003215070a025007030102c0d005000080b0159680d080c00401d403541803511506208240074074500d50703000b9800c1e00000c121000855206164544a0b040d80404682c0d4440e01400010b00420749034000035080900d008d27114500c2d855403035030001301d000044c2014a03c010150b99595071900c0249414081244142c0000600082c2188080a0780e0281d4106c140510b01c0c1240e128000d0319030400c00700b40c41e000c1c0409c00d102c5a002c1000f0701013054650620207094042205410108108102d2540020440030310500801070744200000580d0459640c0c810310007107441e88040003d414410101220741c0120700050390305000100140d80804c1171242d00d0882003807905a00400040c0d0240d100784640140030007080d0004130395550881c8040350001c0c1040620742100801143c94985041300300250360b8003500c0200059a80004d20500603d40c010b20600703864103244071032104446401c07001e410952 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 73963365 1250 73962115 73962127
    0x1206011d06130f031a0c0301030804060c15091401110c0a110f10020c040b0604030f020904031e030e0c06040503060c07030315060f02010605100f0507050c120604061506050f 76
    0x1c100b9540c0b0140004003d042c0856681e440e049404e40e20b6500703071007814182140890080a040d0055a050f82d520800c600d00302814030310211860201c5210949101001582125614800340f180c00c030410300540018040c0c0b88507240d441e0a40d00e0840804410000c2041419001b00021946411700c580c041081c800700a00800022055078095110a5001030712600512026800281015035194241c50600403c2d10080410010b40140e2001400c3c41906071046001460007000701c591081c440d080c01007026a040e102030454000c0011981e010075a5004081c84e80038080204c000028021a04585402c0c10040800d403a040c019050400702c02d0003145040806010350054840c9008a81c01012115581c100c005d2100e07031500342000c00340d4a0030030085010b0601200000760181c00d0b403075a85440c2260101200c1c4ea40c0000e1301500c8a015040c00c0342c2d402c1d82c4005240d00c805480348014411410b25051070000c8030811100c0d8425076030030400c01c0050a07003010031b40704070103504403015407600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 73964615 1250 73963365 73963387
    0x90a09090218070203031b030601090303031e0e07060e0d0f03120e03130e06030d0e010c0f05010504052a03060c0304050a0c03031808010e0303160207030b010b1206011d06 75
    0x48801c00c80c482001c46a1420400004c0e0b000000c0d510500c080799846003a1551400c002c6c1891000b80c4505001400c0342c0b0003030021a00a03085900300008040103004c0c035505100680303048402140c406074a5401003c000c00080e58804550b0101c20011120101c0d50381b0140e45520f01110008401014404480a204140061580589a40524981500d9980241115082250095005600941351010041422410002806207024681d910f960b80d5a800d00c500640b01044000000c60b90030403c01d030301c030000440c2801194041ca00c5540200f841000003544c0440021420070104180350350b42951003da81d070001601c5401c044201d01181d030341d444508266007810840c44000d0802e0008940000405900071340d03020041140c0c500f0110201e48900415003600d05c42c0000b5005503009002140348030b001d4800c1c4840001d458011170b503143c0d80d20fa580c68031218bc264080354501a012403d00411441c009196500c040300746007041d11041c08942707050302d01001203840e5000341c0d00840c2d414554 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 73965865 1250 73964615 73964629
    0x8010203060f09040804090906050109050106030203150f030309030106150e011701031b0308070b040201023918010603020d0b01030e06040303050a0b031b040e01050708180c060f07020312090a090902 87
    0x3d84541c0c40244810002d60502704050a0700303102d000e20503880c207000050042c0c4607109403401200b00f0115030603800300c04820040ca10051400d078941c580400c004e906a259400d214082c01003810701c040c0300068164400182000460003083d506100514042c00f8a080300c200005c1c1c15641d100410f4903a4900b443c14011429481d03802c0200b81d0000014288244208014028840e42c406d908440405079000d4071002c1c0b1030700d102d2010304940c502440c140d8003516280c0044044082c013618821460040101205801100307134400340103e41d000401700f80101142c0120030501c4420308080c00280c03141d130420350b5542002407010f020540c0d224040766000c24540c0120351041e01c014100c4144041c00c1ea501c4402e100780c080f0491180f490820302c1d07000610107018451081c8081d0f00c42d4441c554800115007005800200010014041d08550103240e9a0704400741000ba503140707603201d03296a180c2c810300d46001f240310000321800806005145080c0e403040101c40950740c0600380072994980034400306140c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 73967115 1250 73965865 73965869
    0x6090b0f0d0c050309072301051c06171203041112010e0105010f090501080f03070b09010e011b030c090e01151e030504050d030203010506030601030c0c1a09010608010203060f09040804 81
    0x1c028140000c0b8103100d980301010358003910200e0140d4481e035541749034059008809541007000c00151154100d0b4544c00348001d0f05131f00200e1300070180750b480540c000908861281e0003500c600d030a41316200074045400c1101c500e4203010305030004c0c03560801e41c42d1500640302d4144070501c5031048140e2449001409e41045546c410f105000b8031003543c403202d10720040070f0b103405003811a80c40c0100014070031400084114201c240c20000c1c501e060102e40300c504445c030008210010035034031a589842c1d202024440c0c0400c14213800d0308060100d0300180c00909a580d2070740e01204102100781d05200484c2c1aa907540d0440c0c55000f10007982802042c0e069681d118110b0710a10a1005a096030442a4150704000c5c442ca10030781c00d0f01c0071150071000a030704900081c0030742034001c1030500003e8402d500a501c055203540b102c2c1450941001180e81e0030b480d14452030f117141e1407030400c8030610841410074014440a4000c00000398154580080811009030001030f6813441456408003140a0080090490340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 73968365 1250 73967115 73967137
    0x90307050604060e0c010302041508040c0b030108010603020f030c0108070f180b090126010506030a0905100b03010c14300705070b0f0411040906022506051006090b0f 73
    0x85070310703140c1402e900410446000d41c3d09405092043e003506d41c407074401c803803d884900b0106104070002c10340444500300b008004840c1c8130001e59012409c1d100c98409540288400e400101d0841d0640c4140120031380d04400f40c501aa1101c08940303460380c2c01c0700c0030590200c21450700e49030222510324112082c8402c4145401415400d800210b04842424010711800c1400c3c1c0352408804003039150100755591a542d45070b003a40d0410010b109500c0c240c8000c64000050035804261101c068a5090604c040b46460201c450f90700c1403219071a040a004168144965040c951501455000f032040340344a50702140c6000d00c09040b40300c400e521010003c0b220f884001c295903d107444c29600107401039000704010b4a18092100001c2c600c0d200d52000c0e0792246034408005a541d0786c0440034003010f0300500604403038980d0244403014801d0448843d14115040d4901900e4a1100074104401100c60203050145c0b005020301c0184860350700000d100f0b0441d9088038070f840c1d40d542042c807030b05681d00500450403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 73969615 1250 73968365 73968373
    0x203061603151d0705040b0d090821060f0306010521010e070e0405010f1119210204030605090304140639060907061b02030321041202150f09030705 65
    0x4a248410107683c20040c4004040410311519115070a0720306024510540071040d80410480d40c82c108190021000540300d15131460800045202c4d0a01c06031212103c4003194035101c0030001ea5190640d4002401da106602030711265040001223000603406020700c03080319800040d1046400e8095106903103002030a01510405916070101079009441580d00741e58647c20104954510000d5100e1610003004090f1500d00c0c0107602c500c1500c0426584202c10244900c6002e000314040d260300d10500b08880c10000103907107034154a06002143d1020303282804942c000d00090203c00d0030300010b290020402c4902640701c18035010f0074140c401c29503404040000c00c21645845040c0c900c0c08081c0508404000d42d0903a5031440c0d5003a654210502c0340c80300140600010f004050801480400c03c1400a01624504601d03044444100d00c03261094070600e80b01041003005200300000100729000c10f40c806442c01440c9001041c00d071660280c12800700160710008502c81e4001002182d040d907074000291 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 73970865 1250 73969615 73969619
    0x705062b0603050f150412021e0601060906080112020f12010e010f0f0b090406020c15090d090605030411060901030f051f0b120c030604150f051903020306160315 71
    0x5080074014078802110184108000381d6110307403002c90340d07100344020300740c14405958450316507401c4c0304a5012611b003076008d07403500c0d0751241d088280203615040c140401000103503d4801c001300042510341c040c00801001c0e20040c041c180c0150703041001250126401e420f001090b074002a010801d000c036080e881c0d0f1078465095039294042d0002060180340c20b10800c99480320b4040ca8058a08880d05580c3c4400103500090008096034050b00001000350100e5404500c0c050200218640c00d481d0b01003243e0012110104445d03114403044050525803a0140c154240381e1364022001500420692050030b020400b181a42d100790300c803c0c95010725110900060600030a8004100411003a10001d417060080104112100100f00c42900f03c0c036990300740361692004d86803501904040c261aa2058954a2803284011024000350141c217111040d18130300e914000820001c60900e5040e14403a01c88501c1c00c001580c0d011510030b41c4500101c440b02c1640051030000c03001403d0f00c0070b07240760001c016240 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 73972115 1250 73970865 73970947
    0x20301110c160905040503070212010209030a0807060c02070501020a060207050102130311040c05031603021602190801051b070f020a051c02090a090f0f08070c060e040b010c0203070506 81
    0x18002c1c0381c114a00700c03460041e100c0b0b040c0003c1d0ba008940181c0790b030348104a0302c001800c000013210003d10500000604204282c8002414041982403d90300c0b04800b140c0c10003030003180e01c20340c40703542900e000610400f0b1400002075180c0001381405440c0b6507022035a441800b10a40499010000030680509529128a02100313600c00403440c10340142e01d068003581c8510b000d08110307030040504000d107001e00034410500302e029511080e482c0a0081c102c070043c130010b03240c10400c003108907000c418501d5400d00301007890742110801051280380807041800760130b20000d420101d0760700a0300040c9a10740c8500c00d0010542c0b070707600c580c40740c0d0b0800e103000084600b655085035410340e000e100f25800310464a4596010050b82d042030300c05041c07130095040002c00120410446464148245070382810003000740c540c003510150301d074008004030301030002c100501d00d028450141506400d0a00800d20a09034003c00e540e0012805103c1c0580702c00911200c503412014515916000301094061214509140f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 73973365 1250 73972115 73972123
    0x6060302030405010f0b0901180e07081f0b0d03030911091f0812031521010f0507020a050d0806040617030a14040b030f04030507020904061416140304020301110c 71
    0x80d0560300355207400300070702d2014174030b0180061402c1c00410060141e402d00e07010b146000c1030f00f141c0e6120b0690b1486e400c100c100c4288a441e0040c036001000e0540314240300014100d1040d200e1811407083d00c3c082511885a48480601002a41500d00000e900706a460500c91004141800720390040006017041407030640380c06d22062034032000c0500d035030b10f0340c2d2000e2203a40d803600b10041c034040031400e000090079030f0507800b4a46d00c0000000c0c044c071450510a9400c00100f48503011001d500d945548001134090354030b009807504a8aa0300c000c200054542d02c03002e4450546034180d134204052000030031400e03650754200780007809034007000700d0355060000c0c0c02d2a52540107a103c8400b2444036184c003d80b000b43c0e602680d007195601c0111524ad999400d02459041e08010030032800c0c440280154805a15012035140c496031284000161107840014031903405940140003801d00c0c0d40f1902010b5080f5808806c40170342e4801050040e8590321144001b902420305c0ca10720300d940303400124956134411740000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 73974615 1250 73973365 73973371
    0xf060509060a1a0901290301030c1a09010f0305060a170127020d06090c03080f120105120a02040902150712080a1b180f0b070317040b13030903060606030203 69
    0x2110400000c9941c41e0310b40614840f1581c100d6014402100400181ca40d41c81450300b41c04042810081d00d40000540c0d402a81080c0c0007a54a110070810a0050500c1050b100e118405840109404e2925150009000c0038041420604040d16407020a13a03588a0b008403001510002e1380c0080480c0c0c4002c80d0710700130310f0301580d036500d0745150f0140a960265400c40001c003094024014140000d86921004050030310010121200e03001c0500c000b001c2900c1601411110801c0c0080681d9182c00c50301403074103244181c20042c4291601e0382404540d4100048103106c031581070703a0201780d0020078000944104800a1466102c034000100c032030800007202c4c0c06940b00d01981e22001d03003d44584414208550010750810165000d11403000304040c09806150510039500c12038085060725503080c00030000e51a40306402d40600030410004041d0000180c46078007425000d855603918241d2502c8055100160510718008045e010355024113104840c03590286070800e005200903540c44100400a600403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 73975865 1250 73974615 73974631
    0x406020a06051501080c03153001050c041802040801020d09050d020606060a030b1c06022a060601050f120106091a0304030e0f06160b010e0c12040b040f06050906 71
    0x4006005442e64055014250f24180c0d1100c600d03a0b80d460803506142e0014014403c030f20303106041c1c485940d441c584081107940c001c0b440d07a6180045541d1a50000e952041c00035020790510b003c2008503003082c825a021178249481100c004403080051400a01c03542d00030740b4855000181b95010500c0642080500d140304004540058036403500c00c0b40c541c1030030348046500c160100034031041c191183e00140d8034000010003880c1e0b2401d401c007003026240e0070000e0032505103401003000100d000d160703143d0040500c03c1481100c00301c00c400520f04e8035000d000b00514140b28011898109043d0584107417041100400180143c650b100c0360050501002c9200d1110310070800080d200c540e5140c0e4007941e000703030b51544641e400f00741060304200c0e00f40c0c1c1c107010fa203070002c0d424420f02064042c118200e00045018640b00030480d410325041080e07448004041c070041c94001c12580950095484803247c0c40b0380c1046501d00c46031943d07d4200003200c60564045c045031f0524041c090b2401c40412650f02074420 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 73977115 1250 73975865 73975871
    0x1602030c0d05100c030e0303041203060602030a0e100504050d0c0302090109020708090409020f0a09021c0908040b0d0615050c0d020d02070314010e060907060e01020102070804031e080406020a06 85
    0x30440820038010103000c80100309400c00c0724030301c0f0074441d00d0b00082040c2c016801d0100d408440c0c01d07001891608101c800f640d121070281000c81038960903104910181c45144095031030b00701c01c12006044e01203401c032218000e0000011103020b27944100103480107400020702110205c0210f0800003103035005c0d404240d00c55100300c000001c0700900c92003181c0c1c4599210340d1213801e000900c1c00300401032504404c11b982000c50700c000e40d8403a03a10154940d0241410381401601c0360341c1000d00c518111001c0e01e03178000b042e1611507000c0104401205039000c95000c0d8095a5403044d40d52688005081d1079402180d40c0910448030070002500403000c1d2506103148422180048000b050480e0385040800b15113015030020070052000c58200c0760074400008031403001040103030880c0072107450710204450541040c2c000d004188072550388103a1a80400000f48000d50074280b40b03403201c100360b1140c0c2c8401440d03280700500c0140290013401ca04000560095501030b01c1d1540c442019407030765181c020440d0528a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 73978365 1250 73977115 73977133
    0xb07120203040e010e0601090302040e010c20060f0c13030c050906010e06250f0614071d0907020c0301092006031905040503040317120c0c1c14160203 66
    0x1200206842c01c07283d40004245050340390072503030741980704060302040c10008601800b2015031581e003c0c20070722210b0040002340311100d111005250b6080403000c042c4078902c500c4030080c002000181702d0707081996489215107644400b03954030320390300c109031444203a03a0300720b01c0020a00003d0609001110700640d00e00606580385001180c0e41078070709400640c04002802940308864955014080000c1c02c611071001400e00c2d501c50351703c091103100c000c441164031884581100b01500f091160000c2140c10446042c699000c0d07010b14042c00c81d0400b0740102e40174000210194400c01c8a9140100050020000303c540c5d8140300401c900341c150410610030b805901807030f060600c90122403080d64181182c0c2e00035280700c9070003005400003030402e542510091202101043c6020742910002c82c03c1c2285a5803282012642092208020400814803005100ac07265039600802d14039820a0201c4a601c031407680c1442c20751344a0200300c074819a201001c205401c110005a0708815064001c5003280d410030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 73979615 1250 73978365 73978367
    0x30e0a2a080606220902040e0703020a081f05060109030f03020c10050703020615010306080313031104050402010e12070b04091d030412060216150f051005061e040f0b0712 75
    0x807007601e403c0d810a15005400a1a542011610740d54612801003c00c0080003a00000c050301e04841401d001a00419020000c51404242003401458100050030000107100d03e848a10341ea000b0803104415100c8000910b00d81c070034465040510743c01100b41000120a060017590742c80d0006450f801402603120316620a40a881035902441e490f90041c242039480e00b046071102c11000101d50b05041d01c5150100e55200d0500c02b0308010384600d924400018558140740b20f025030b141c9140c0d0b0040e85000107010241c2d902c50004109030798280c81d088070f01c0e840040c0c0c01d450b16605902c00e40e8881e10104007c501c1250750780054803240c01d140d80c231111407007010400c16103e1041c2d115180706420b02107a0000001c4042d0007501042003000c4c01041442e445807511001e00c8a41406039048941d2007e03c00c5401d80c5c00d200f8250080404109409524140300c0415007a208000f5152064a150224070480300c514008441c00307040c40103c00002c281d80c44051002d9500803c0c02101c107100d03140d0301040c0e82 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 73980865 1250 73979615 73979623
    0x50a0207141e150708030403020105100f05040221163c0e030303040b06011803050c040b0402130b0a08071d010e03010209090c030a060f0b0307030e0a2a08 68
    0x3041c001d2141c2140701d004058940401d144144150700400c200c441c107036240f66003002500f009800360b03202940d28134107850001e007141d4000300032446041d003040c018002425490120429a801275400682c3c0d928485940e03120f0890182e29500e03c2c1c548481002043d0720f140341039510702d4804d0f480d0200701d18a46c50320951400109200310302c1402821503518a204000e10351040d010091341080d0046010340b1020a0843c1d004550656060001006100f100e5030302030440100c04d40c0303a10070b01c4101c07419640c505441e0102c64684d140f107692103403181955691164101c854110f07000200d080e0300380d80c404000c0d0554000d01801c1c408100c403100024441c60050754030b032a000c605007018604d0902030000548400040d0701500e41c1544d400c0c0480865610340c00700c0c06000d801290707052500ca05d01090601e094520b50f401c14504403003c2501080134103907607c11303690002c410341404a440c0c0c0400071071907e081c05130000917161035995040300e079081460011061f1100e9034260341c1c101150b00c0e006010b1391 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 73982115 1250 73980865 73980899
    0x60801061a031f090e07051201150e060109170601060e03060411013006030204180201050d0e03070c030b1009060b09010c08090402040602010609060519030b04020105040b0a050a0207 80
    0x480c0020000500b000d0340c0103010202402c00c1104001d0003e8131358081c4000c890503c00f20900c40e0b40991010303c414a44116000e801000800091000410600403244042254440d031420041c00c3c0c000305809070300407103420000e0b0900c3c01408a4000c0c0c000d43e495a101030038803d0030041240981445118203010801510a680040c03a4030407014000004680002c03040d020111a138504400844180000050b1014001c1031504080f030380c1411030040104a65417090050f00e80c0d1103003815480180d800009590301030445d10340c000780051030b2541c014194401c01c0d40061040d442d0701c00210400140041c1d450003007542c02224a00591994018030441e00c003402103c02041091040f08074540c4a901d644021511030354403e030801c10f08501140c181d80064000f4405170751540801d1100307206510410f0300601e411070300284000103030082c0400f11700850202502941460b0002410759004400300c070000d1000c1485641d030b86c280000010482e402058101e801030181e000001640070910101e110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 73983365 1250 73982115 73982159
    0x1f11030a08010f240c020d021201140703021801080a020c030304030c06050105060301050d060b010315291204030c0305090d0327030302031801030605060307021608030301080703080304030c1506080106 88
    0x4076915013803010384265000c0c1000300d07482040903641b0001611224842003c0100394000407614045154071103c0071000180900c0402d0702c10f129247c3e0101c01c8020066103103c0a0030300110f0768403041c010030064450a1495030081c07000205100030568030170040d201050141d81d00b040710366214002c02409110030312441d0f42c0403071941001c40c04601d180c0d200090f100414100090b0520130084804002101648209481c0c0103503460b40060306c0b4107140d00d4210b00b5000c3c0606242c0820303002901807506014101500708803180c0100c004160081d0100c5003803140003006281800654a40145036045410180707280c030006910307c1c1c00e00c4440e6803000c000d90350b05801442c04c2140907001c0b804164540c1ca0414101529201d0014117900c1d0807009601441481d80078086503039840400e0268003001d944000c0f51948100010420301c1000f04243c0141c95021809030342c1d0341c8490408440300300c0d40c80409010a091503100d0b0211011079446403040b11140f02c003d000d1183c1c0d5590070f21601c800407003018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 73984615 1250 73983365 73983419
    0xf0c040609060e010512010608090f030702090103030c03233604150504020c011a12030301090c110f070312020c0f04051314010b09010f051f11030a08010f 68
    0x1c80114054104440d60f64810302d001d5044c5010184610300c0102c0a900c0f0001241203041441640704090114900c16520b85000710301d00300312035001c9048005c0511000c0c08000310010304000305031061503841e101141f00b001002103030144c1525a083c6034440061040300e000403401c1040703903118060f2500c0080c401092483d220804920034000a0140150841e001420041011441e03a403540302801c581018440000f90b401e940c0101d00640d03d18801c3c0075441030559544241611900004503410b480c03104401017525100c0160986540c140124070804a02485400d0300c600600010060101c80c01500b034480500c0c4100c40c1070340c0300c0c200310003115002010100c007041c0300d0038150001604810040b03c07210074000b0319103078071908fc805400d080009944a80520010703242085009000d413101c42e1a500b821440d11300040d01030b000309440b0a50303072a44503007400c0d610340c0151260700501103580180c0c0d44d25249044010000503007400746603500340440d0340110b4a40407500003080d00031005e00301a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 73985865 1250 73984615 73984619
    0x6090602060f0601030e0a0302060609010803031303030b0109051804062a0311040302030d050301081b010c0f060b1002010c0306120201050a120f0207060204030b07030b0123090303120f0c040609 85
    0x1e0b074442c01004001505058462031000203a003010005070700c01c03038000d0b4060141404c10904000c24110107074040101d0343e009000340840f103010000e56a56190b8142400946003c0c00030043e10840034031750215a0046404846500c00c480e020280c41c402d5114100c204991000c1c08445c46840300611090f02e404a001c81c081000709000354080f9801901a614580c20503603a94000703442c5c82e81c03200100b800144007000410452004012001c3c007002200b4079020038009507030000384034181900020300000072100d400710a0140b654081c40741c0c2c12000d0b081e0300040c82c00c14800b0740601000145c1b54006464a900007038103910038500f2050003507059460078944011440110f403c41004152180c42541c0c503941400c7ea90043e100404d03074a44503017005a191303441d60600c0920680300503c0c40c02410700300941c82d0080d030b80c0080000109180c60345456042c401c090018000c80c007030038000e181c0510001030303015030051040f1200c5102d00300b4070001d18900d65910703903403800c41d0186d482100007003040310750700b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 73987115 1250 73985865 73985881
    0x10605070c0306020307030213080102091806210606010e03060903220e0108010603171e0a0c14010603020f1c031b0f0303060302010311090a030f05010e0a12090609060206 75
    0x40c90a00d0140e0941c100d51500c07078803080300301d81c8141d5055003c02d50010303103100c920074003051800051000d0300c0214200341c07440c008540511201c1d00c207189544000340c000b03142d5075601c0715440d00801c5104401407440c4400c0c03d481e551040180c43e0b02c0d010400c3c410700c86c45140740004e10300b80305d402d20801071420310003e1004030302e440300b0800382d41204446d1188082407001002d071030709009141d0017001107880751450600d803440f520346640080d8107007420488980c641c3c0548441d683c91213100c0d490709a030303101c140c101140c84070b4807010003e00c0d0034031a20b10241f464505400080c1501d00071140c100c0c1c091054010065007074109160900148440c840d4100441d0107025080000d80078a1a06000c961656640503517031151803030700720302081e600d010500039540c0c54410418032407c0940050b240280750380c00a404c0c400316105c0100343c140b156885004003c400c0d042000421412000c684500c0e41c245009507048042c01910400030714503d030001682c1e4844c004210860780241c0107000075440c6d55003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 73988365 1250 73987115 73987117
    0x6061207060e0607020d0b10030210080702060613060801020a09150318030809011103070201021c020301050f0d060603231203040b071824090503070501080f04060609021216030501060206010605 85
    0x25099906c0311007610050040745c030203e00c0d24441c001e00d010600311581940b0411016064030401403040012200070415020340014905421103070031140b8442c207070359558102002d0080c40d00640215400422000e04564210480301e00b5034140b25034801601e4110303942101140e65250044100c0032520303484201203030081c401d06801c044035500120300500d12540c0388005034020380f451030050f90700203085d0307100703001081c13400410381c1031240c00394034551522000400d0358040e80d00c0d5501c6407900761300070380c20450907500c240c00542d40100f0818607005005c1c00302d40c83c0c84480c11f03241104c4c0680d00070042c500c0d4641040303a02c103991089011403c0d4482400455440d0700d04411128603101c01c10b00410040124211a062600644028488241c842000070038880503079005601951000708107000340c1e07801540741a40b0061030010120196601c0c10040c01810080c0e01c48600544001713900e000b07140d1800040e52241c0302035031580e0001150340d282202203440c2440b401006801c44c9005120051040c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 73989615 1250 73988365 73988377
    0x5030405030d020301060c060c022b020319050a08010b09130209041812021207050303070e06160302010b09070c02030705040f090605010e011a070503030106030f0212040506061207060e06 82
    0x3012a8104034084070404203c0e4001e030842408603061031040800c202c1240500014054540b01511060110303011031409000588240c903405524629008905442042600c0701050540e0820031002400c24000cae01ca54007031a41400012000400414950b00d903904958280e680035020340010001c1d039050301c000f074010032005680030303803181040c50b80302c0c002c1c02403c8406406144403070050780700600081c0ca0448040c594200d90321051101c680891000310683e94010410b003402c121246900e000980e15100d4200400090780b00e00d1b03401c2e000d156055100c030020140aa40c4460141c96211094649500890000b0b5040d44108014040c03400c00750011010580b1648001c55840d1090340c6580984100340c008405005c000d80040060850144480c200d88010110705071030000c3d02c2e2074298807484140602020300d13441e20400c003880801c9070304440d01103102c0a49001c0750304051078071684480050320303110b11421000000809136400402c10800320b440a8441a100824840c20300c03955400807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 73990865 1250 73989615 73989623
    0x30d090810200d0501151403060f01021f060e0106140d0c09120803060a140a03120e0d110108010f060228080703110105070302130308070c03050304090c030b060304050c01050304 78
    0x1e8094550100c000703002d4068550503c0c030100b80780d030400072a45001c0001003c020300700070043c0108002600c81c001103031b80012094400c05180c840000050b46001e02c4001900c030301c004003855903200107003c2d5204509031000310b501440e060f60b81d55821103102e560b4040098420904101c14900300c2055840034100b03444038105a0b07443d540e030b4150944085180c84065407003081c0001044040e03c0d214003104040d1080d81d2285c0b03012040c0d5030200313035410843d0100070f02040885010300f905a000b4034103484280c000a104c1c1e1401070103443c140c2100419410110701080500b0000700b520711000710701c00d06490850340203000e0050740c5416500310051003001c80102d0050005200d01140c2c03980b0082840e0350080c0c51780e410880300306c61943c1c00c44000800d52801c262050200702c2d22040c00c28000c000b143e800002e07050316650305041c0020004899070000f41244000500041c1c14009600001c1d03103000991001c01208505005200d42c41c130040710010040d4000c0c159030f690543c01407019680140c05 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 73992115 1250 73990865 73990901
    0x90209270102040803090102060f010f120503070803070507060b011e030216140303070813020307050f130501150909090b060d0309120807170703080c0a030b0405010e06030d090810 79
    0x24112034508990060700b0030403c50300b001540c100070b07580400c501da810a00235038111420f5850480d60031130700c549034015260500d004215803414010100145e64019400c00502d940e00c2c142118046e241e5480258112401402c22030708155540c0503951070f1901a104a04070340b05100007010440095010030854003a680c0001d642c80b010400c01580103004449603002540d803806e0400c0064503512000700f00f4645c0340d24140700c00b401601c01050340c2086420580e07001d4054401d2800003040d951140c003800110500d844000502c09000716501400c281c807075122000011b07210340079413050b511b407150090140c01000002c41d14508042c1c09010085019241c1500826220000c030320b15100d05440c1039404800102d4600d0070300400006440651308203603401880d0202561303001d40742e10030040400c800d2001c04204940301500036000050741400c02481007009603110798001e10094010380d5118024454806840f8000e030003604008241c0b03104800801c06a040f5107169005491407000700f10410403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 73993365 1250 73992115 73992181
    0x11404230601260a0f0219050d0c06031a030a111203030702010209090a06050904020904031b0503182707090905010b0306040b03060c040909020d0803090a110301090209 74
    0xe00c9040d002c0c2050780c03c12480a00300031040c6184224129207482242c01c240c001000054100c160036400e19815103035031022012805003122410030303d500c0b00790054040f4000b44100038000c0301c844182d440e0340d02d0402c08040f804011000342400040b8254040c0e008600120104080f055460508840142007611b80411047d42a041d0307003060350071602507034002c0303551030f428900000010360040000d04100042031429000038140d0201420190203481a007000c40d0030316105480d182d01e124402d400c035420006c05882d05036681c0c5d1145110040b880c0251403411300301d240100c0010210b08849801d440c0281003020100011540601100d00f4819014400200b0150a000341802000d41444083e00c03454450240401c0d1031520986910a4105504020300c0c2410b12040d2002c0e00c03201840011010b09501c08911a003c14400280207030401004002c1c04500009000404170301c2500b013009084980c0301810700380e61a003030000750701c00208800070b041e8a442c0032038900800e035004103413013100c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73994615 1250 73993365 73993433
    0x605040b030a0b10021c080f0f0604090204020c0307060b19170c1f0e090730050c0915030c1c0b040c0909060806010810020702010519030906060503011404 68
    0x4103005039180158100c2c0c0c080580d00003200c0d401b024504010300706090b0134a803884074680680c0b8020f0504176141001808030304981c9441c0c4c0040545613021384110354881c2143e100603a29007044504495890034141d1103080e50410a545040020b1000d0800c3c04071824030078030003003e640015890180d032240e054030480c203564651000d082c3c0c002c0154840d8840131580401003800c082050318600a034110010310840c3d80d03000e03240600030a8040c680b0415200324500503030b5520010451108014100014070141008840080c4203413641214415600b40c803e40c0c800d0072324001101c0c2d2055400c0b05008600e61a417040404841c20003000d4030008103180000f0000e13040320064042900002e403400b90a11003c07900b8030134440a0308114005010710b41c980020a5507c040340c40c1902d2800f600451108216401030b000d4801d5610241d5405c015603900c804010001c11808105942c07240c2801c03400100303400d061191070700c200d01110202900ea65151a48100c443c0620000c2c88480360710030709032100d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 73995865 1250 73994615 73994629
    0xa02010c1b090207020f0d03022508070f08070503070b0a03050403090503010e010b10030603021c062a02070b04032a0807060e0a09050105010c0b19020a020d11070605040b030a0b 78
    0x2405402ca4016143e00040c014010000e051002060007120400e80c2071022a400085541c0300d0b90035840040d4500b0080b651452544805030700416403482400c4012425000001408094074200b100300c80c155503440c03080668403420341c460304401141c10040c00251038481d8001d140d00c00d000382010203c1d90799510109003191780030006a0500c3e59a14039608961522078001020020145000d10000c6e0554001698507082c010541200107840e1202d8410408603400408140001c0c1200b10801c2d13680b080b80000d04000040c146005004261010a00102c40c00a541c140ea0f00b04d90902540c1100c00c489280300c2d41403050b140741b5904103000014910343e003081014041c00040d664620920b80e034005000100c070b0140c1001401c141010014403491b40e1000e44100c03559000601003240b515401d024460748400c03080d001c0d80301070000070303080c0740c031030b000200c500c6551110341d0340499961601c04410303242c049500034540002d40c100f00030001040744030302540d0000c1c5807105c0082d5842040c0009201 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 73997115 1250 73995865 73995869
    0x10306180506090a020f0d0207140303041415070912060b060d02070314070b060d1a15270106140906040e01030c06090602030a030207050f0f0723030a02010c1b 70
    0x1841c1c85404005540c100060316036041012810254148142a4010304250080c1c4c0240c004195000c19070006100503058a4001030712003c00351b9583e400e207030030070381c1c0d810303910120401440c031030212103035814841d1107566071060340325039600381e159401c000b0040302000d4024001d07105561118022111a9582c81c000c001480307a2102c01640e9480c28640940000b6803641d6003c40a401800070401050070708a400350310210880d8000000b41c003900d061060320480c40d00c0046d589510340c0c03c02001d1040c41078001988501181d60512904114000482120900c00141712481c1c0300c200403c01140914030300000d20303074a00022070800d01d514001c28000c3e002a40111509101c00c4010014403007140740404c042c10885c43c00050080c140500a9580d103d40c1100c00105640020b811044c011f007030000b405034441c4001514801002e03e03d003650703240164024089208008151070b01c103654070380b4448540250241c040e1a143c0025001903503034204603082074802c04403529004d11540080414180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 73998365 1250 73997115 73997159
    0xb0a02030703060f1d04140a0c0302010e090601170901060e100302011b0503041806050303270d02010905091803070c0e070503010e1503030d2c030a0f030209010306 72
    0x2032039140000000b4103451450b800441c40281c0318501740409080050058041c00031008030036001d8032a440c00c499049000c401000250044502901c100b0020840c5801180c4c001d030386e07482c000c19481e0304001a42e0410b446c42404105100c0101c0c000002c4400b03a154040c03190000058007541c0c86d8800d108080c4102c60207840744117130706401d108568202001c1080484400d10003640f206656540c40e9582c0300e1800790000c82801c540c40c1c014106001e401040217080040c0c1500c0d15008c001304c2d102c6042c2e4a24000c4101c3e20802d0415401900b440e19580d20001d07016518a20280d01c0d00090106041d00900b1a00c1c080503180d1000f044445c0400c000c000e4144100c074202d2505c0d02e04055814510005014132003040802c100404c085801da000f50364010140c4c2141030041000710000a00d9403052015191401c2c0c1014458a41c071011038641c105801680050500c03a134441801e22a220303c00c0800390f0001c14079450811030030500c00d5015015601c0107040008025440300003580d247c0810f403442c50 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 73999615 1250 73998365 73998367
    0x100e03090d0303050412052502030304030204020406050702040e010b030a020f240a1116180e0d05070c050f06070b07090b2803150501050904090f140607020d020a0609030c0b0a02 78
    0x20481b01d8501040d0318043ca21f455403d14444801c8030814415141d2914101031100f4070540955605200703d40040d94002d0086554650705d41000e40250030000b416840380e40f401303e12908021060248503404a0010064640c1900d940d00b08004485d03203c10b0a9000b008a000b030070841e00350b081c80390604111a00c1d810751240d030a000002c190014800c0354001ca50025211019649201c84001041d81c507241c00c1c1c42a00e81c00c8134400da00a0a0840320403943d440f408140481072034020004201003405501c0e0034003040d8544081c00f001c180d03400201500310701c0c00c0203070310301103400084496040011484c040c01402c1e81c40e6101d04458000165285501d4141c0314106044c5a00c600c3e0944a203003542400e04c5807003600811402620802e10500707051000c000307403400403540ca80e80a2950181d120190160000c00f6081c00c2e000800550179182d5688a402d000c665450700002c0c10301040040380e8004c0110b4030680d82e0765000703007500c66411030610811401400015070100062886001002001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 74000865 1250 73999615 73999621
    0xe0d05070c0504023f0103080304020d05070e011a0903030f03100e04030810060f090302060d0e03030901060518040b04020d1104020a0201290904120e0310050106090504020c100e03090d030305 84
    0x60044000145d903240141e21100160442095140f0a00e411640c02540d810348955486c00801c444031070403180200070b0b0040c0203000c184200c0d0082483c0c16140007c040600c0e02c20b5050000701c0720310071003000710b078164400c0c0444480540008000e651000b480c8a00c2008580d45031800808801c0c1940c044012420070406c004054140b0980c0360010003451600c60030301c1c005c1c003002404500c0c0354000a401904000303190241c0e0001c0b40c1120072101800001c81e0341d285088000079009004901600b88220034490210010710035540101b406981c00039003401558586a080025803901854125502032003054200030656440c80680f003a10b010341c00114000500a07513482c07074900c0464a03125643c141800c110269140d2080712988258001103184072140c1c10380041e98a0f41d0200c4401e41d00d4440c0d503219402c1c10207160480b41c1201c00700c2d04d0b0349040b162a58204802c0c2d01a41c2c0c0140c2c11940026003841c1c040540350421502d01c44000140e80c1781284250119241c400e102d00c05a000c69200c4042c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 74002115 1250 74000865 74000917
    0x170c12060403030f09031704021f02030c070b04050102120721110d020d0c030507050c1f0e030105070c060b01200a0b0a090201050306100905040c0917010e0d05070c050402 75
    0x1d103000c0b510f0b10344c004000960555601810340700c034100215012511401c0007a046454040c2c25103208820b11502010754141c41c0c1c0000c1d5207a014000750b007543c1c0038811001031038042d03000a0310190b8074145c000c1c21a4014038601102140c0156005980c1006103608001c0802580070480071044a507503220300c507441c6051440e91410701149a0b0f54115130180b040c03142d045a00c80b803880c1f110b81e41440c1c030a13a116100d04020b440c2014881055620090950344030280440312645426100241d403034454210103008101800ca5204941e0b00011407001100007001802c181d028404c840390506100045201e0b252a0480070300d02d0341d0284c14168410030301107060054401700d1603440500f6000500a0401c02d072b000070300354040500054015061020306c0d243c00d50244034440080c05010344104502450180005c2c840c182d03601c200d680c1c0d001428900586280180156000130701184000e06003404c0c1c000044400d40d010740c50a03949001d40b4036010851f5515800145600c81244440383c00c0702c081122 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 74003365 1250 74002115 74002121
    0x50a03060b040f17070e0a0b0a0e070305061c11060f0d05010b0405030111041d090f010f05040317041a07020106050301060801060f1217090f060d051f080304170c1206040303 76
    0x1900001d1785d222400820803044000710f03440d400605807401060030f40b8842c01060a4101d41d8120401c2c0b4000402000030840d03040e03102c14800d0b1030840b0b05c1f504540da10080b111000303141c04c50103800803500390007200c1d0f1401e010008201480d44400c0551030400d0101d17171002120000c0c6c1082e4000e600010f0104000d250901650f005540c41004d02032800e854001110903681c5042c1054180d2149540000c500306414000c584005402d24005d01503070401d142c0031001004111007c402081c000c00082c280342001c0c03003280c1c1c442d540c0041c02401500d0030221504d40240010044021513498841c0804c0a131400c0c007074140101003d0001243c81070030103900c208524460340024492a840c40c000a000c1400200d40404000600c1046a65034400c01c010410f01d00c803030030003207400c03036000504000c404030603502c00c9110301ca2401c82122540110013141400440e18031440c107103a40309200900400d560824801039800e004e9080b10301d0b041065001c20011600c280224446410a034108001e054140c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 74004615 1250 74003365 74003399
    0x5100c02010608250305060c09040f02030f040605041407060201060f06020109021e0402070b1314011802010e060c07080303070e01020d1407110307180b040203010f06050a03060b040f 80
    0xc00240070b09030514150550741c0911807441c0b070102c200441c0000b541a0a410440c2c05150010700b554218508240d4000c083d80c4040d040d140941d14010b0900c40c071039070520a81e40558800324200e212034035a0b8550601501002d8402d540321010326001c200740c05420032a8600810b0150000b0072440d1502c1110186226254450415641042c0110700141c2e5055040d03219024070040d5038010070041c80c0864000d0240304002850100e40b02c060004c0842c0c1e040300340e60311070300c107812041c03070b02580c0009242070703903e4801e0819003208542d00407001903000390300d046803000001d000d8600340300714980910700c1c200c0381d540400041d40000044c805299480031200701400800c0c00144100e01d50b40500a10183c0d061070110f070f40319804203440c0c040120710030326141442c4005084603252a1580a4540c11501c204086c0f585c1c2e0385400542e03e01030030140240c90407140b58000d5110710910b0414140d0740ca40c0007c0c0c40b43c041665620300407c1e840f40510217040a4000500c200d440d00703080050741480c460700d00e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 74005865 1250 74004615 74004617
    0x3040615080c09130203030913060f031505090c011209020103140a060503120f0f0307020a051e10050105090c0a050d050f040c0b1306030c0302040302040e2103010311010f051605100c 80
    0x13030300248000d070b1030000484141c0302d030945940c1c01c0203074158960402820b0f01c0d000751102164004000043c01114840808040e00b2460f0410990712400c000554030022800750a000c215415801030311400d42d036000d29401d03030040c18081082c1e141c10401075080b240840d0540c0840c2e40e107100038030850a04000010300040c0146c2851302e080e0710422041003e00405502141c84000080083e407914400c1c0441d00007242d1007011503a48200742400b600140c4502d4410f611544607030a204210000180034942c12210050300340308103600c4240c16035407207a0080600800707200f010421a403080d0414810780c2d200d003420800606003810140382a0109009643c0803c224080c00d100542004c8020090502100c07035034100040c402075052400c0e4040c0c0516403010b5401480d110305141418000b19a8200310402d14542c141c0810009a6180307690100b8003002e4000c80220040260f05c1d4001e80c680017200d18035081860a252220602407410200c1c8a001c0b00c540e0089101240038001038040c070500715041d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 74007115 1250 74005865 74005891
    0x6080111070f20060c0f0c030307080708180d1a0a0c0203220b0a031a010f080f07030f0203072001050106020a020607021305070503100605031b03040615080c09 70
    0x1e2a00c0300060803075003040151602e252561180708a42c09000b808402d48030141c40143c031842c2d0750362030580700c4040c1c601e410380900a10403024114a404800c9910140d0f0191520b03080c01c00d1521000e050f5004581ca030a032103100d02900c600a43d40380c4415001e40c511079100e40a81c072000442e421a02c0c04080c044492190500d0b14108074983c0100c15200103d980c000c2d160400700c400c0c0404144c031441c41c1d0040c4560000012050209581608500072400c00e070103483c0420768141c1d004480002c0910303c0e0400051840003c120380c401101c4030a50040114940890001910305c02c080890344140c9000b00410a02e1380541d103d06018404200d011148070000c10085d850302401035107465001400910071200001c2c950219600d07030f04e4142d6540710ba81c3c4104070619102401a12641c000e442c07065038600b40404c001811071040301224410380060444103c10600d0441b15403a541020308100c0d0041d4403441c01e0b2040401c01700165004250080041c260500c901c1d060055002001d40010f0200302 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 74008365 1250 74007115 74007127
    0x8030a02010c0201060e060d020409021905031509031b0708010c050c0c01080f18030f03040606030b0108011b0809010e122208030f0a17070c030815030a030e0609090a06080111 77
    0x4446c8012680064240c3d180d50000e10b1703510004004080c4100002e520440d0401c00349050040c1650030020b90705c1c00d4044074002449008242e41c040300407103100805600811a500b5003078070391003200c00142d00c080102d440780b80d292005e09095510040344500000c00c01b00740080044001c01090031514800c0c00c00d20001c1c100341e2041300600d50010305c00301d40c2d0340c10104543d02131507040088840f42031410340502d40300d081c1440c11001500280c8400d07105000840008101c591042c803601c800c0320030584820400748403540341510360b00700040010b00349543e503055980c908603090065072030300d0604281c0344c2d41d14580c82d18060852b6114030f40000d8110100345060140345000000c4520580c20040c210341c680400d460120758002c0d04162070240c10000300d0500ca4040d411940145180e0300c20340358030750b15507108142461114150100950316a0002c81500d001c48c0c06103152491801c00981428541303c0c2840c041040345906480e002c0d2101e94a030003c100740c0200b8460f03c0d08001c54012440e103485 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 74009615 1250 74008365 74008379
    0x2031c1a01030c0c020603040c0e16090323030703020105060102060a1a19080708030c1b030c0118090c05210610080a0207020904060506010f02010605130e100608030a02010c020106 79
    0x19203009035903061607a00c0f08040306860260081c142603650080c07815036603140621302844103100c94461a0300000c514400320701c0700c5c0400a403030150085240e80745c2008501c0c0d034403444c0450300304104601c0d900c4501d85203821341c2070042c801040750a0082e0000301715800d0503800245092801801c2c0c2000318540003041192343c140d1240303c56184011503408056556000c4404181c0641d80d2040c0e06c240314071070380051a09000b102810b0300011004c20b44821500da24250241140c1c2c1100c025495000314000e400650301a01250b41c080c2082d0012444190300ea80c0580103c0c4d2000030700c50041131003c83c000d05041c1d4070030f00322601c80403000102001c5041940c0407500c50a8040c0359230701880032120000d10b088109505445c2021340080c5900d140d4181810284010003098542c940001e11030307519400d03401d0050041d0800c60320041d1050407078505920a0300014600910880b9030307401013070100c0d807000c4900c0c05800042d2203444d0203540d683c20741030006421100901643c03815641014004c210710 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 74010865 1250 74009615 74009651
    0x605040506181b040f0204030f1a0408030103061d030a020a0b100305030a08090c03070605031f050108060103090501060306150602210403060f02070605180c03060402030604140a05030a02031c 84
    0x440c140c180403d910400c40c0c00040242000c10740a000c0369102240c000113105130000c030703829180d0080000c0049202c0d1009200e81d5040100d0703001c0d00c000c00030001040042e000354000c620411010501402005e80000b04608550041c2a07000041e40102d00c40c0c020301c000c0e10f0580b03070862100510b4460507440c40e520700d5224011050410b051040030000a20400c10500a103019000d0003803d80703c4030354036034801810f5600260340031498414841c614802d614078002d0004103940d8140c541034107030b644107001180640100403044a241d501c0d0000000020254000c10f42c2d40c1c031446d404201b805007080c10081c0342000510020b4010403c1204c48014845003070300b02c80030b89070044004100c2c216581c220b40046c4c4990000100118030302000c000c00c102c41d00066920901c0000180c0d100754402e1400c2640e0713084291400395064104001080015020000c1d00c40d990a0071020344420115a440d03c5045070004c0d04614050b8000080c402c54081d4501c3d0206500b00000c0d00c20050440701c1d0110400d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 74012115 1250 74010865 74010883
    0x603060103060e0307050601060201020d060602030a0c11040e2b020a0b010b0d020f0313060e01140a0b03070806240103093f051201050420031e04060504050618 70
    0x15180e0f07512403074440350414000c85907a960840304403030381035a44200081c001d52207000316020b110b03e00381d404951248040308688031109290344070f41c0d880c49103844500d0100802100182e200d640c41c015032003203072001e21011048030603482d4600d0030003d159030842c40c01e00c01c151803071b070854005141c0c4500007568984c109055801201d641521440200308010091081d00035401900344013100308000d60b40103d00d00718250b4800c0030700740800c0714140c0c0000d0985080b4440a60074802440020708100b009a019280c0031070000d086a001594800d0054205601502c124045075400d44641b25416540c5d0b20303a00d0880c43c00c2c0303401c00c103110080c0c98a0401c0f00704c032020014040850340b880304100c4442c0e4045844c07283e288040c080b07200b91400006d442d9a00c00300d21103a4040b0060000143d51034a40302d041c500c200c06c2e030006880070a16421024087d0300c0117103541025040040311000c0d92a903805080d20079441000c00165500741824910f00e441002022908862900002500030700c0001c501030034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 74013365 1250 74012115 74012123
    0x40306020901020c09040f020f040e1009060204120c1706060a0e07110706170c041a071e0b090c040902060a0c030c0210020a0c060302070807120c0f08130e0603060103 73
    0x20315000040c00403810080c00341c484507817105242080c48184281801c80102c054070031119958000c9175401030109075090702080e201c6a400100d02d441c4c2c0b000d01b079044411072511803000103140648170030550108240c0e4040a40300340e0300c0341d00140a858208040039142201d480003e201510300000007030a802803a0280106170071050010464050040b11040c00d246180d02c10b90303404548030b00e8020801d44240540c008902e4cd460003048450344c1e0740048900303640c2c0c1d0003001402d804042500e00141d900001c400c0b02c060030a0f0b20151007103801c5044841d5080e214506011303c03800c101200e540b425545407501441030b40f4081d04200141c0d941c80403120010714070b090900c40c6002e14101520503424041000e07401c0480181c510440c00c1e40450407004062103000150315190b00c40200b10120b001d15000100803040c20040800800d0f000c0d109140301c20201e140c005031a1406560380320826800ca0401c81d140900803e031070350124030030812000a071001000b40103940c509030000a98840f4184000780c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 74014615 1250 74013365 74013367
    0xc03040306240b0d0b010504030b0103021c080f07060e0d0906030e0705040f0213150c060234020f060f0403110a0314030a0915020a03080c130609080606010e0604030602 74
    0x2100e50802d2802145034900584403046060342e580c3c40b10785682c45101c0119480307280400185207503000d101610140d9400000b81c400f0b40c1e0a69003030103400303003800e0300c003280c0c0071000c450395000610380c00024140c85400541d41c541b2400076103040015030354940300003900e82e00a444100b00056000d070101048914901e40070801300545040107050890381d821040d042414600b100300041c529400030031050030020b40c0354000580c1c2c0c000c0301d40e28483e07150601c400200045d1814001c070300381d50050040800d100e001c00243c031145600c00400d144180f0309241180102c1c80d405005d40c64a00c000c0301200e141654103c0c078240c543c1c4a421040d01c180d0100503c251450201035405403140e000800107140d01248541c010b0650205135541c2e9040b425000c000941c1c07040c3c002c10320042d00825982e0b0740c0803d400130444400f207950191803440009100d07081440d0300344020000381101601120003000e082c2c98012545081091399800c0480007003d09050102510182c0016221001202c045a42000c001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 74015865 1250 74014615 74014631
    0x1020c0406060f082205030405090c070302250e0702060403020f010516030e030c010212041101140901050c280c0b040b04060807090f24020a020f01030b060706060e0910020c03040306 80
    0x304104e00b05034880200c80300110700c00c00d001c0006c0000104160717007048031001e0319691600840c1c1c2e10391240140040044e000803140320303404010104500c00a03102c046103030360816203907280d50000d10b4040b90b00c07400680c003000900c03051507010300401d54801d10040081c8401d10b003108054441c0780d01d40305203204165035080f406580720420720581d150181c4a8001f03560b1445c2084611400d000300740d50070740d00c258000303600c5292507000e102c03040c4600304170003403c909080d40300d0015180b580220040d41c21a02070350341e41e0440504070b034080007101e002c2030b14110150041c40c144504c0300d1009801103002d54008020902080510a041e00c045401c280351603440f40d501c03050100c1d83ca80303c65000b03000032000d06030301042c0588a009030410550015000c545010051f01040342da908031510040d4014256408408603542300f90003882c42d87d039010300075520705806030340c400d0100c81c1641d0085200303c0c010014410b0104040c03140c503440305145c64095040c0700d0286466a01e0f0302c03c9110045c0107c0d62180c203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 74017115 1250 74015865 74015881
    0x10060f1101150e0402031b0a0501210908030a0f0905060109050c040f03060605130c0822050609030702030706050301180f0e030c01060302270a020d02070516030201020c0406060f08 79
    0x7400d000c090380210320525030f42c07050201c02640007520101d2107801b070101040c0f40410a418082d2581c00004c1409180c80c2c5440c1c01581c006c1170492185d0700f49d8020b082140d440d503116010303050b175003031007003036200d03540d2a102c400001200d00d18030381c02a010341440310400208030000344043c15942001c20020300d41c2c0310040c04082507c500e900c99090f0707030f408040000500c0925072068088880031354801c503010560120300c60803141040c11840109914a010400c5101001d54003685a501c01440a0310b5100320b03240c079481c18204885084a41c1e000007070400840c1400e0051400a1001382040703400c1d941403405140c507100d200704500460540e1540c10b142d21a07800d400804000c55010152681c507103204080318007800950205a000b12083d00007200042130210100391039040d1101c2150710703903c1d400c081101039400410113400940d001d1200501040e0140320b09a01c001440e00b004426525510019083c5682d07a044d09225601d004400c2005680014400c42c0900907890b08981c035a81e40301c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 74018365 1250 74017115 74017121
    0xa05090a140712110306060d0c030b04110310060509090406050402010309230601140114071104060e1914010e190c05040504050a06060512130803040305030601030510060f1101 77
    0x1c05218810540002d22428503005207031224200c14481007805102e25210204449200a40d42641c01500c10000000b8015040d88280c22602440c0340100c4c00c040064001815a4030b40c800410344101c0001c203115a040c0380742c01000041200c0e091490a0201310130000306c418000a0001d40781c41d0710ba400240c11603219500c0110764a5105890f41c0140c2e503608038001b00c181c28800e003220b645c8168000031801000c1c1903050a40c0e803070f059461790a40811120310340340d1500b0024088411030a5010480e4145c0c0c0c2d207006030009089200b0000030207284c64031000c001c0e0401c9a854106036450311140a540c103c0d0140301c03e040d00c080344100c184507110081000c041c5101100c0d591541d52802e1640e43c1d00a901c01c005004540d0100c0302448903484051310300b41190960311650011071010031019190000400c000b9521040c20a94402c030303800c8940301c0001581c0102c03002c500003800041007210300c0da01842040e03044011a1202800741c5d00b03100000d0b2051100d00d25000520064036200149144250 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 74019615 1250 74018365 74018381
    0x23030d021e0a020916030b01170a020f090312090a120b060409150f0f061a0417071802030604050c0304020f0f040e0307050a03140307090b070204020403050f0703030e0d020a05090a 79
    0x14240200c4d81c1381c11041020000a400c251400087c1800c04803051756101d058100a14020080c550382c03503443e8500400b0003584207042d000400d0384280800c81d4a55010300140300760b00810340d020359131081640d0400070b426486c3c0e0011001c04401c40c000340d0200b8803444445da1f0181060700c00107084900d90506031030060402c043c841e802802c144840b6000e0b00e51390060242510040801d20040351203c00d140c040464556031001c9500083c40b0400500c50100b202e00c000c0b03240c80068401403515001000700b0b108030b60100c2c40c10190000306100c50360615100c2c0380c0e404100710740c0c07040c11404c16500003403001a004803641c1c496440c900600302d0300d580383d030b03c0824618200030441e55140c4080c54450b845045107201913020611284140c40c1b84030403c03003243e00c600c04555541051504100116205800450040e41c1065086c400400080e1007003080b48c62401d050f81c0140245859440c0080c00c160221841d98003e5000764081c1d80141c4030f584038202511011100b140150780e03141c0040d00104005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 74020865 1250 74019615 74019619
    0x30402060906121003021002070806190608030301030c0609090b01020c100302090a03050109060c0e0117041707050303090f0f0309010c02040f06030305120a0203011212030f050123030d021e0a02 85
    0x9800d00203102900101368085a01c00c2d00d5010000215010698a5800d103209501141c1c0103040010f5030506c0d910109400c000c10b4480005080d9111700d00ea5155030000d0700201d0f00a0900d030740a01071182c0100310301c0010049075506004200354000000e4071180340d5652240030b031140001100310507010ba010764031000070182074810000d80d00d040c01406407409031003c0d03a040d407070100c21918041c45030310080120b0b4410707100c0d003503a44101c1c031090181d1030380144141ca109110700c1b880f500c03c400d84001060000d000300000d42d201e040040c4c0e8503080098981c450550341d801504030200b510380200030b60314406401d00b4000800c0515001180142001c0302400d41d4040c60310301c02108054001d80075000c004c40404d942240e943d00e408411040f403000f8003401038508081b07005200000c01e90040744916010514000c40c24424a903100802c0e59420307000f0810303a494004910344a1118214900418402103000304410310341c195000e502d82e1200c0340712403c03d03114542541000003082160350000c545c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 74022115 1250 74020865 74020897
    0x30e011104060507060617150c03040b010b0307021009030503041a25020102040f0b04081203040512090f03010f0b120109080a03020c0307050706170906090706030b0111010603110108090d05030402060906 89
    0x210381f0030151a440700d40c181040b188406400f0800d400720b140c00740d0388502c1d40100c8203420f517401c2c550a41900d0300005e14141c00c62180c0e90780010300c1017007401922a014401e44849843e418a45022403020440c1e0324501070034401c43c02081001c0002d201c00c1111031100806203a028105054120301911654001d030b2221041d100c80099402d010b00c00400803100100141d42802c0340c0244040182d1005481c0504198025140c0700521020740f001000911001003c110303551618034042407c3d50710701c06656484075660020800b49003052000b84400d1003080f0000c000c84881991205a40e000d60940402099408100c40d04010713020412952900d41103401c44030407650350007000703000850140049441c8481c1c0408160321950000b0010f02800450303015050003030508004400501502d05070504101100d611003103030031400e1140704043c6000d00c085506508180001605120019088248170b034000b50600001c1035010065903005641154001d81e540400b40c0091100c0c000d4040f400c0704625 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 74023365 1250 74022115 74022149
    0xa0605270a0302010b010206161d041b030f0e0312040f0506010305010204090b12030a180f080106031103030415080c07123605090430030e0111040605070606 69
    0x80001d900d0010510a50007400103081c104012030300d401007514080b1022640d0518041001c0c080c14103905404035084220380c100c0400c074001801c0d00d140814900314207218143c0f0400c01030341805003034121200ca400a10000e14078038405a600d12070515155034501114010400b00016071503101c410540044c204d074495610307410514000e40c480d200e50080704d4070348151910b550900003c43d2800d11403450142d401c1211589003a41c100084880e9511a0760001c040840d41a11064511016003429400000c0542c290300d0040c154030000d143d141e200794000d000801c855040d6000d001042c44d40b51500c8000780d1070b01110751406010344030340186009000120140d450354490704820740480c80341080503451a46001e40c4070600d07051829480c0041d0714407000d000d1424000d20507500280304130446a840726041502048804049006680041041480201c0c4a62501a5401c610040e10007005601da072880320700003603c1203106043c14040003107212010702c000c662212000301000c003400c5811712 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 74024615 1250 74023365 74023441
    0xd0501140106180f06080a06090608160f1202062107080403121401090e0309030307052d06040204090203031209061006140a200d170105010503090a0605 67
    0x404240105030018030301c00c1c0a690380fa03080c0c0f03a0034400c490543c01103001003820714508030384110000300200b01654642e8800070300c0c003146215070402009a00c000c0e1000c808519007800b0701c3c3d6203640c44820b10400801040c000e800c01520712034070142d07044814a07998a00041010a072214614131031415030034540420803410f0300f0400092146101c0d503034100780e60b0b035444241000c0710719800e105610703000b44600600c40c6082c3e5901c5010b041c2d051000300d9090040c901e0001e49161301021084805410003091601e4602000d000010340042903840b099070a02c070b005400c0ea5510340244007a1055440b4107070002951070500403100c0c640821150450715240501a2070361760317403042e5a170294400100074005000340c0300c0d00d10080100304a41c0304610388921120700701c07041d4030040d10140c0c0014041340d20180b010009c0000070300011030b94032040d0a1410380b5201140c0000142d0000381400400c20801c448120042403607044031758071000c001030a4580d28869021440b4509580b4410010b900d03540707a0b24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 74025865 1250 74024615 74024651
    0xd051c021c0c02030c06040611071506080c010c03020c010e0103091208040b0709030c0b0f040b0a020a0303060b03071b060b040207140c040b0612192406020d05090409020d0501 77
    0x34071010307002844410091481240e0300e101709100110f45400c0340c1c01040000c0c85982140c2c8420203800340c502c0c1444020b8664490440c42ca010301c1030031030ba0341c240801080c20144401c41c20000309082003424681942c601948175001c0110307190400c03190b051400c00300d80c082e900800440e0740080c80400049040c0d07002a044200549003a203d118450000594051042c0c000509036580101c00400d1903162421804d9a9080860310078038080703082c0300102e8916694806132012400d198000d12010015040140032549103030001c402803a000c0040120b0950407018102c0024140307034255410600d11308200008000c1c030741c80c1950060001a541040c443e800e0b100004103040b207010b0fa0b2020040c4420081142c21810126420a8007403005e059a4102144141c0d07200505000070b80d114a1020a524220790041c8680503001402c03d10190f00140d849030810081d090900040100c051410320240203806082c83c4a4810341d2901821411521803145c500201644003000b4050303000d0303506642036a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 74027115 1250 74025865 74025907
    0x2030702120301122012160b03070e01051b0303090d0813050c0d03020a020411041d0105010e1c02030303270c09041e0b0405030c070e0103050d051c02 66
    0x144103214155881c0303410399080303038103c4151640040c501c1a00740d64600380000000324100100606001486098650901d120200c1c0400341c00f42c41240301068240410801c6030308000d20038038061007080346154100c1c0e80081c00a81c01d08002d505c0d07503040b5040c0d0320004680d0a4144541c0804170034000201030010300d036034403820b01c3e8a80c81816610020b00001d4a1203d490141c580d038071a4160640c6824065040c840c4103010b8410b403912507c0342d4010400b038038090388510390405400103080161051500c2c1d0400c4420080c00507044030351608000070010a40c3c0c4030300c0380c031460000501c01c2082e0240030411100543c00703011b407500e81c0781028404100e401c24070be46e6202500340d1182900c0c21000460541950039009181c6616a1520385405588081c01a2aaa03086900c0b40110010a030300740400d900c10340c4510001c50380d4040009000e800c1050a41c03008580c569100c00500c00600c010419070400c0550b07107000c0d0b484004890082206042642c2c1d196280f0307200181900f119a03984900d011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 74028365 1250 74027115 74027117
    0x91b0e0a060518011e0815070e010509010801060e0604030c120201030b150315061213030f0c030207151b03030e0d0504120209250201050906010f0b220906030303020307 74
    0x11095965400f802005002000241c00a640200040c00140003031318800501c9041d11101c4903029440d007060a107401e00d0307001d544204840e900c0800000d2580300c490400201403e10381076080499020001c1d00000040c0100c1003840150144580c0e00d0302c4030810b650003190010712070401e5503a500f003000d103161000c90040e400a03040c5a8045040c2c2013085610b040d07401141e540519640d03800c51701c0a9940ba440200c1a4811000c0002c0c842d0081c400e5807142c0220309090350014a0600c070320f0080c1c0041d40c002440014081c0300000a00842d0f0040340500c101d030b900030404046c1208031207003101c1c000d284103040c250380c3e03120400c0202810f505a01c0241d0744849801220820b59100780142ca45025520070f10040c1004054603030014200344a01c2c503041094910064294041e601c003a0b8250b4030001324841c0142e644400300854070108102032401800740c2c0400003003150a080d0701c0701c5d807441283c0302e082e0400c01c0480145511282c01030341000424611104100681d1680f030020041c0d40b040d50044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 74029615 1250 74028365 74028371
    0x601050903160807082d0a0605040602090117010501021e03040e011701050c090d110a0803221203020c01050a14040608040b180c0103090206070b01090606020609030913091b0e0a 78
    0x481c000c031000aa02000143c0d00d40404c1b6480181910b00b208400e0000b14048580105154400007a92a0140074001c511541c03016840d030b400d40000509010681d5002d00000300848010020f41c1d80100302001d00070000e10040c5a14041c040459203140300760343c0851400410704d400002c0c401071060314818000c60081c02804607454134000901300340691603909900005080102c40025012100d03408480c10182081d440c1d142d40b08111400d6130000d103001c101441441a40b43c5100d6201c0c4221000350034a04124410300e212520b009640b4401c05050906100c00010100b903510300484411a540c200c040314245e8a42c0c55a000510940007564101c580e20701007404525209071288082039210b500c180140700d00c020000044019010255040e80c2100c030030403006000c01c4080389038501034441084040f902900e442802440d180000f00b030350101c0c0e08140820360017642da114405040000c0440f0228960080c3d00303004800b03481d180024007041c4079605d8000f07080004041040d1081070740140070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 74030865 1250 74029615 74029619
    0x1080d0207060e0603090a0b0703050610020102070503030f0606040e131e02030c0405070e0429011b02060703030b030a11011803020916050708040b0309190f0b0601050903160807 78
    0x1a40e454003140590b101142500700d1603a41410f002024591160721030f000c80d40801c0302d549403540321b003100f078407160b000940380c0040105900700400e000d002090b8038402180342c0486030302c9140d01d901014200741001001c60010800c1a602d034000d850140041c0d031020540b0b81072000100e0745050441c1d8044400da009855090002c40b0504c1c2a06501600035014107140c00a0404010082000a1510301841200032004100d920f503031240c1c02901303400014850107640e600b0000400c18110400c80c5041120200441c150b0079596511041c01c00e9040e00c4507920380000d4a03094000d041c04c00b0707250340c0510400c4960301c18080d000e298681140020780b14582e000441c600c090440509902003e90080680c0020038640c160001c0c0c0c418450720701e40f030424203140362a5588003a40d0311552020381081400700c18402c2d407000034040c44086003819102c282480030306a5038800c40407444000038080c4003407840040c109901400449620f580d004040d19107603030403115464448030f094014800f007840f6403a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 74032115 1250 74030865 74030867
    0x6180a0b150f031915080705040f050705430210020c0315100302090702030c060601020703021023030108070807050f0108042d0b0f0a1401050f01050702150301080d 72
    0x22070701e191412018643c503564030090414940300302000f4a40000d0390f01c0c00714000410070010740c60003402810019110f82840c102c10013040d02c10510490180038a420240800786810204840b01c4032061010817a1680308110540c90100d012a80072401c5d0340c0c101003800d03d11301c541e039910310090700c00c554020030180d2901041345d503840548450340e09030f4440525802d003200004903131a03000803000904032030503480c9d5000c58511041501c4c1c2c48003581c00404d0001c1040800d00801e07511003800e02c020881e0f01d146400080c007403043d02d0340302c8090050b1280e04e400c1f0540c10000107619207441100f455500d5a4400000c1d580e11918803c21103e809041070204031850000403200868505070740d400300940351902c0703c1010b9a11840c5880c500f00e4103401000e241d06012030075440aa0188010b00c0d50303458500c200700e1103a44000c0c4901c1941c0d01d82034507440301c800321034601815242e040d100c188070300748201c0c0180d03030f1407041c0d005c0030790701549180754500c009509500450590304050203440c0035500700c00c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 74033365 1250 74032115 74032117
    0x3030f02060906070e0a0b0f03180604020a0302040207060b0a0f080f0111040902280215090c01090b0c07081009022107060f120c02010c080108030406120506180a0b15 73
    0x4030b0544507004140424003ca12554200e0404000101344111896032680c070103050380d2004c40c0080a43d0700110400441c0a034004039810245c45150143c09a841c06500040d0f00b0300076400005d10840c1d0108490080c801954040c60b2a000040d00c0540d0070b6031507a2800c0b62072401b51103400e40714484c0c000e01310301480040c000c1600c40300307282e0180b82c107142c142110761b030194005079020080000ca01c018212035130172818401e10004d01c0b0360007800c05c1c1c3c8461080900b484030001c0001a031540b05050384201a40e000c0404000ca8214880c802c1c0c0310f0f500070503000d04041880e40404010311803121542c042c0409607002005c001d00c01c44611f4a10410346151700c8025035090300c00e0605030081003040051501410040601f042e00c2d2802d12640001e465588080790318444251005070355230401401559001405540035000f075100441c102403401c80d009040c00e000300c040c5050345898101046003500c40024160410007815010700d02480e1403e00c4400414140e01d0452040312401a0f0311390341c0d40100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 74034615 1250 74033365 74033371
    0xf0c06071707030b090a1107020604030303200703020c240a2601081009030e040e06070e041b0c050a050105040803070207060c08090616020307090209011403060906011101060812030103030f0206 85
    0x90101d8071291ba96111407001000c202a440c150b50504100080050351010020800b55101380c80c001500c1140103581d000c0032001c24900c2030302c21810420301c80440d400180031083c4150486e54030001088002a4001c10306070300000300008200440c440d0745517a00314000c1703803815011171201c0c2d072402100204054800030a200c4d04555412110201c2e400103110341013542c0b501d0107403c04c240300c1d80c100c0000c030f01103d0b40441814016000704050104465014002d506451030440b401d1000d6001e0800b4200d054034203003c0c08007440b030031003404400c00c90144203850520740c01c034000300014034090805841d141c0c030849000d0018020302c280410340f42c0c000c03440c9400d02500114140d0800c0b4800080c0480c6070301035180d0488549a502d42c41c1c0050f40d04002c0e0501424510b500941c507420007000141c107040300b018021000980a004011040d165503201c2544000c0900c2d10914008854890034010621a00714501d1802001c9818000c49005e50055040340d22aa03151540c0511080040361105015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 74035865 1250 74034615 74034619
    0xa0305150f01081806070917011512030c0f05031918090506031015090b040605030c0f0d0c0807030b061806010806060c060f01170613080f0c06071707030b 68
    0x744018000d40d5104000481e4000402043d4100840d1408041440c0401c200d944030001b03610310100740000c10004081c0d81e0040c440000901454400c107030030615404050041c0f5488280041e203003014144917149000c0c01940003880414018000d062503502e0f64010103c01c40e50500c0130180c2c03a98070348254201001c0c4d030443d0700f80007034003800c020320903010706030241107140c1c503200d26605c030f042c00e500782e21404c2000309010710783c50300440c54038261900365001440c0280c40303945000303130400003500c0105440c000050b080354a54009014400000c1081c80c001d000039140c1c4260001c08250700100203100010b480c0501c030800d030300d503a448040200c0c000704020710304540540540491601e50250000070b03000721009261a060101071802d1902e810011909048422000d0780108a100c591038400ca19401a0101034000b6144c000902400080500c60080101500054408103180c400c01a034003920180c5081d40e0140c1481503004021522442c10f050040d0605400705603030500910401f02d080f100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 74037115 1250 74035865 74035879
    0x103060f0b030f03070303020d06080d03090c090213030f02040603080c1513050d2109060605090603150705070602070c080a020f03010506180a0204030503030c0307090603060303050d051005040608030a030515 91
    0x8686d8044003e504141c00040c2516120700c408114032206100d007182c074101c0c5640002d8200c00700c1c1001258070301306a001c4803410f84100540c00e080d50326144420140ca8100101500302c105c6031021400400e607641c80134214040114444130300a501044829940d101e586c40f020540d00c45224082450241c01d2008004da031100144080b558010012141c504034146215040700e18181d250341d050341c0d80341c00129240395582509101c0c1e458a00c00303180c1c21040c16001002c0c10300010b020002140c0c000740c0b1400601c075000c280b400802c64117404855500d030b0301c42c10006000340d0f1000b0b8680d50703840200040307100b61005090614079050501c10b50f8422203000300740340c142d100c400003600d81000000d845c1c3c41400341c0810001c00401ca0400c0114020ba02105800e80d99241c02000201081055000081058104481080882d90010a580801040c7c00e00007695444a102d50480300000742d020039040341c01c1490005140c40040003500e9640c0c0384c0e032000d010541d5020b031b200d1200540c240c05031b6071110b2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 74038365 1250 74037115 74037127
    0x50706050402041d07081e060718051003020426060c0a0201090f03020f060106080c18010c0215031801090b011511160314031e0c030d02030103060f0b030f03 69
    0x940103660014009440010640c00314921001810318500e4968942d900a400402561408000500c1140d041000038255075100e038082545a0748064036800130414092030061542d0748080b04107000340301c02004180e2031007050350054042d411900c00c080a80072444c0520316889402a48182078081c1c56015040640e80e2000b83d5209401940c1100219946c42c20350a001030900c01c280d00e5810300a80052400c5450700b4056451720340140c1008040150300414020742c0039a881c1940c3e00070807090122000540b00400480d50341032030300d00c040e520001e140000929007849200443c040c0e1041c4443c984040f80607031100307098800c0301000401d0880b40600400c000307442907100750214100b62074107014440362030000b14a041040b0300b000283e500c92800820421545e0110701320750b00907203005076090440070940054414001000081d140200003402c10581d0010b01c1260b1261450174011074503540c513424054000c10182d000a6881c40c40c020f2143e07483d14001902201ca1003030703580198907002e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 74039615 1250 74038365 74038373
    0x30e04150b030901020408060705070f030804150203180622110402090607060209131802010807051b010501150c15111303030206060306060a060203041e090e0d09060e010507 76
    0x8005041048090603088402044101210005500400340840007588407428190385171f0815002074611070030700100700802d00c002090a00b09201c9550141050801b941d124140102d040c1d00a1000c4210390380700001f0009900d249054407443c40464a01715411650380f0413684d010061845004161580e01034200c0c000516010607410f40000080d1001d810100c500d0040707034403500001d80450300e03250041140307515403d0400d401314961703c0d440b50074002d48100c01c21100300d03150703c240040e0401c49014000740f941ea0090084910704d80c074100020308035164004076a4020582030203800312010180c010300807454440c100d20b00c0d40301c0e088800a00c00b80a80d065000080080ba521203561103001c1c03100d98504403940705144010f6000c1d401a08052a061041500708003000b8106403044898501c00d10569034000155420b80e003000c030414640c0310118111003005045940001030360f509054458103900404600072081d903519480f06403a0700d4540364113980742142d200c5010300003002071110038085 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 74040865 1250 74039615 74039621
    0x309010c06050a0207170307080c09060d090218010909170f0301120309031a040201080603070f09020a02030408010e0f070b0a020604030e0f0306040309150206090c10020f0a121407030e04 82
    0x81070a80c10f00604c1d0041d00d035190000d9030780d614010144400e0110400014030b40000c5003550020102c01440d140429140008040f40101d00394080c059503103403556401c640380d540e0040301c0c201c020444151150395a24800c80a408030a2003154100e002c590b10100d0000e18109440ba08840d050340d55040d41e00b04001000201145c10090301003000e4954000040380c01146002e400010b0161806501c2c94180000b4000b10030181209010b40d120710010000042046000c0c01691105100941d48007044403040b4514002e0350442151035280080c2036540240c001000341044c44c0480907240c0c0c2d41c0d5203200c4003140e4095005004007507040100064002032040303030081450b020052103070f0304244c40000864906402110210045040c5820902040112506150161103d44010030030740c40e01600c0d080d110703c0700c41c1959008c2c915515440ba0010300074412985020811002c8844170080c034104442e111001d00300d1007000c6000000140c00d9034000a04881e40b01c3d8058598103003c0b45d2080500c401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 74042115 1250 74040865 74040871
    0x140f0a0b18011e09020703030209010801060c0506060103020a051e0d0b0d030e0d0807060f0e07140a030803040606030f080d0b0901061707051605031b0109170a05040e0405030703110309010c0605 85
    0xc58103880040340d00e00c4c852015251840c06542c00588030100600003507e0031506820110074000c021400e08001840051010ba00400038a00541c82e040844020b5031036001c6c0f4107400344c800d50389032440700300c0c0c48141000c1e00320b02038104010b11192200c5410300a00340342d084000742c00628032500340d0030f65041c00000801d40c036201e03902c847d00d02865911880203c0b4550031214a207a515906081d550404c10001c00d00a0540d43c140038003c1941d500003d10720713004a10004045241c0840003d05020050780041e0045401c624541503254462038040c0690f441004a0b444d5140b0b0291110942c0c24202100360503175005440300e0000141d81088158000401462007042102c200941060807500b0f070761100c0345d940304a008545450440445d0200354102c201c4811060f803605a4010124248588000d0341410040300c44c0c1d692180c04100b1503081c443c0ea080182544248400e100c200305c0e00200500c10b6501954030001c3d0070b60304e04040d82d00d030f200e0001528001580030800002140f1a0f51040360 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 74043365 1250 74042115 74042159
    0x40b130809060301091505100509010e0301060e0405060403030e07031707050a0204060807031403031512030d0207030914041e1d07080604140705010903030c020301140f0a0b1801 78
    0x20508401d04005480d40d4801d0300002d0005071903002100c240c05800d1480c4014007800c945101c0201020700c00100680a100242e0b410010384084824040d1420b43c80344001c0d1684460902a919103070502580e20f0b481075808400003881c221000c800240d0104001003602d510490040004110900b2075507946c102181c03c0d074540c000c10b020070300103998910076440244241030140041914500f00f2040705020410760803070716081002000456100b5030440c0d000f5503022604485c0801820480914500804404c00401440041e04a05150300180b900f0204c2c3c40d00400145030344880400c1c401580c1d0811881d402c00903900440400c0d07269190001400759091b81c00c40103081c1d00c21543c9502e001c0d2141e11098203608018284410310400d06075810308807100310000c021591030007000031300c0c0d50900c1c480502048100c0091a045550a400c0800140d0400c6407104090030000d5031229a0081500c10100481ca4205007a1300c41c10814610f1034540000070001900361302c3d1401c0310602481c4031382c03010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 74044615 1250 74043365 74043367
    0x405070e0405010305060a1a091b0c0105010902311a07060203010b1207080115031e0504030906020c040b0a09050402010509030f01020d0c0e06030a0c050906040801051e040b1308 78
    0xe100307500c4612499000b50301402c0200918100400701c00c00302c5647c45031184c030b200e0346200c0006042d2100c843e02e5030007401600501106c4607100050020341e01030206984c501d1350030a0000120484a5005484107030000c418441070100100c00d920142d5038410b140c031030a2420700201b040022005a8050070300d03107a0b03840807441c1c103125545010490b4426084040c3c50013020030b400ca2005051035540c1c3d80b150f002d042404d60317541010079079401c2038000b0519a0415072541601440c00990304180030030b001800a0510060501d4503000d040c0e1182405803400511171810384d03058520302402001702a2401418003002c640c10403800c507001d448010010780c103121041011800a40f020000c070001504940300058440d82041a0079090b5224031000a00b002032800c030311710141e9074035000c49403c072851104c000740d4140d10768805d9559014024001d50b04c40d0340882d00040d1101e0641180e44602c4002010041d048000c40002c50241070646015100d5030440c8001418803113004590800030b80125081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 74045865 1250 74044615 74044637
    0x2d0907090c17100828061d28020103150b03011205060c0301030305030a0e07030203030c21030103080403032102040902180301140a0c20010615020c0f040507 69
    0x8403094440c0c00441c0d800140b190040d001100950106158000302d100d900b501141d03140818060713841c424640d400d1918803100f036885220f103019600400c80d080d032000042c02442160359400c0c035a08005404c265185c0652881e4243c803002400509040419000498000c8140e07600110018406198004400c4001141c04950441e00d04042e600034842c269059010f2140340c607249041a84c0588901c6030084240014000a034005058903880840e00c0000102c41c201020300302c0c03504070103500c040d41501001660020919020a00100c000140080300c440b6203c1c08080700110301c024400505100414082480003911440301144c0100c84134485081e1083e08011040403030380141d1010090365800900070ba02e040a00507c1910240110000c12241994100030162800000e0507004110359038203c058070ba40c099a20a00c0390a00259043d0100300b40590850087c8030500984100c002c01400d000078951000070303031203035400001c1d040b5145400c246060002812001e8281c0091024920b20 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 74047115 1250 74045865 74045879
    0x3090b030a0504020109081c2706030e07060e10140c061302040c0203090d140102220603151802030601030603080a0e0103150b0301300f0b2d0907 64
    0x1460003019408070015030b03824030380b0024104103500d82c0000340d00d81001c0b0080b1041001411509030307401041c18002d0b46c218801d043d5035040305440d0402c5106001058011582c150302d0340c031029801103c0300441d508070384c1301d80c401d80340d600340d81d10314603840840059180065031082d840320f40c1104861060030f0520054000040c242030046a41c007101440d44c81c0c0b00c50035841d0600813009402218005545818807000102d00d03c01c02c00342c03000c0d21030402c92050488d546802d50440754903070302c02d5071040d50f4041c441c030001c04416000e11035000000d0812158520318a0941030030303411a00140c2400a600118600743c8004c2e400003045a414980c0e02c42000010590780030013052110900da440740d0a16400000240c01c070741d14624898600340e0103400500c00d4261020883c2d040d0380c0c40d4800110000040c039603888104880d102109504000d00d07042030104620398442c5036403644281008013040d83c03948140c0f14070a03900700c82a482c4ea211101100c000c007400c01e40c240d8015211505466803651a120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 74048365 1250 74047115 74047117
    0x5060d0c090f06080601170d030b060a2a1416050d0b04050c0a15030e0f07090e032101090c08060906100207030203120d1503020303070209070c020a0f0501020f1c0c03090b 75
    0x2000081d03103130707d4481002d840c034002e010b0703078003070f003140b414104841c1c02c0e070002052250040700d841340705100100302628034004649214124002503010b030700d030b2100c145140084000003034030000c150a1103081c0c481342c42c0d2402040c502b401e41d00041c0007210041c1c415103400c403611070040d00aa13050702a2003070803442521880c101402504201f600e480411030384003c01011501d03001201219500f210f00800842c0001084010031180c0c070346000f10304031400075041e5065100f45150041c40c002010100e0300d003607100c000214100e41d914802081401c0c44400155801001154010703403000440b800110399141c050505641d02c01184101c5e140e880d22507010902c0e20b152042c00d0600284045110090f440550184903528101c20040701084da1039640400e59a018018009108004510014509611904800c2519500108081109959694038000d201640d00880307005004000400d000440c0020b20a0344030106040006207039000b50500702d844050b2000110200301c00b8003000a40000884 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 74049615 1250 74048365 74048369
    0x8070c090f05060108060301052806120c06080a0902150c0a1b0521030a050f130e0402151306120b060c060f090f0c0d0f0602070f0605060d0c090f06080601 68
    0x1038002031034100f00d0009405004000c041c507100703a0614041000a0046034003c0e11804490b040c0304200d000041d4400c0082e00058002059016078200e00105104881c0200380c201d481c143c6440c500303078503661445000e40d084d00340040c2d040101800c207140d01c03240403401006541c0510003525814051035541c1803843c0c50651a4071505190f403001071100380750202584482300b000140642400c048001d000b5103030700a01d10382d44184240420011000000741c81160a100e607500109101a51145c41030111004203980590060201c0d069a4540926a1089610a40f0300a080d04d039081d03d0803108464020341c84840c1c682d200d40791101680e050720383d03c01034149441d24074050026880d0074800942140ba000786819200d911aa60302c104002000c5005032100d030782070340d80020a20352420a9409042d138004000c18041c4002400340511108195084005100b6601441241c9809042205412840c5000b40c4107000d012405c0002e1186640070700c8035100401c0c0d010071026511440c1604103075090b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 74050865 1250 74049615 74049641
    0x20403150e0d02010c0210240602060a0b010503090a110102030d0f06090b030d170603031201060302090301061403070506250f05060f0f010302060c1e0a02150406080408070c09 77
    0x246101c9001103500303010000c0c2d04007440c07000308401c016100c0f000b50b031043c0d042c0701c610080c0e50320807107031042c407244201e0101c000165a0070743c1251a03403000025034902044038100c001e585840041c8109601c81c80450780110340900003422003005039120714884c1c1c00b0441803103066120411010b0100381c01401103000b4400c1440f400508240346c0108881a02ca403080c0d030394841d800409e0300d200c20307d4002c03142e44040c40504c0301c11030540d03849601107851445480300611040004c000000707110b6908d138008210302c18003035000b400300c5d41e9107010114500e54081d01d5181c0c5600999400c2c415800c001c0003500642008501005409a84034454201483e2001098520705440352007401400b804000d0b450b00a80800500c0183d03180c8034080340b50994040c00020300c83d45000a200880c50800c002d400ca42900f1010030700d5820070b04443c00c6030794000ea140224002c130b084280901c0b507591a407094608407901611207184aa6031031361020241d9100242c115603034410048040b0b000441e40c41100303411824 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 74052115 1250 74050865 74050871
    0x80a021c05121f030b0a060b070606060e09010e0a0e03130b03040b010b040518040303020c0f06070f09030803010909020109080106090c080a1b080603010209041a0108010f14010c020402040315 84
    0x3000c0304045154000428284000c1000340f07501020126040c1504200d80d0807401c56040d6444520b450409890b20f588003030898407000c01c1030b20034000c0503445481120303c280c65214800200c0018085410000d200b02801528902c00181c10b0760469000314042c0c54601040d2850803100f410014455440354103c4020701e40080104000c12006048040c090901102c0407400c0928180009400900404038034080c1920500450304041c000d40540381d0b08a4404140d4060301c1c511034003540e4511088a20360006040c0340011a82d05005800e01e50503660030012581c07031603080504c0e0030302030410908202d04125003d400024090300a00c29000584000c0501107201100b13840001c0000310040c00d400046884c0401c46864003c0c0490003014500c5c1c68200207880f81d072180c00180c024050320300c0090f0002d05113514a9904c22803081826490502600ea40482c0c1c7d8951700c0603031a8007094066030b28401c45801c00d05071990f000b908010300a1f4801030002d0714088e100e54603001411140e03119401d00d540c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 74053365 1250 74052115 74052127
    0x7030803040b07080903160804051c060b1509040e120301090b09060103020a050a2706030b0909010507021b190902030907051905061605070806070906080402060304080a021c05 77
    0x3881d40582d6080340083c40c18186a04144456036241d11400e0541d01c60f21450b00c0e040740401448070190340003408000d00200d0102c0900010000c0c2c4200e022040720f00c14501764850500386071410ba200400c090200f49142810103d100b03001c01811041441045072107020300aa00f5407075004011406001050300202c2c884184005100000c02c0240096046c90700501050700f00ca40e01134283c408881103440e1030151344220103844428091031075908402081001c001081c82c03a0950440da50500c2c3c240d030b1948141e0740d0043c00f1804c941c4280ca1110040c0c10441d14440c062070604261074107240003c102003d00510854814a4a030562f404001f58a40220400401c11018085d1500810f0195209a0f441041040c1c50303419050b980a0584104804148102c030840820b11220000b64810101c0b880b20b6119404d460303407000e044940300001035110b00c010840724840c0b10518041e560103460f40b4159103543e82e50b181190000000f540c218410308400b081009185107080003100e803951903d640e507003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 74054615 1250 74053365 74053373
    0xb0f3105040e07080f150601080f0c1303050d0c17040b07030f031404030e030c04110405040e100f02070b0c0703020316151401050a0b0405030601170f0115050f030c010c020405090f0703080304 84
    0x3450080c03240b23045c000c03414100b00040d550001d002e030f0b02440000c4010399602e05821440c0342d8407403640024190340b1400514400e8030760480700340d401c1140203200710701014001e441240a10302c1580921004220b0034000c00000078041c45d20540d4003003541c1400b0a407600329080001d41e11000b02d0703068000440348120300380c00741010300a0040400c001c0d6014408181002c0e5500068401c5100d414061039984244c0c10302048203201030100c005001e03005006904440060030040d4201a00c01c0d01c011480d8004035602c405d0845c00ca072000b6034140c01035824024280808100081a040152040518841100181141031045015201a150b01241654142028800f040b0015003240f90101c200300400d001c3c984c0d000a241c1d044407415250107142c00c0c0a144061308104d8000003a08140d800c28114114002201c003080b015150140c0b100301a220003041050350b140300151000c1c1c0802c084c8801b43c005820b258001c240d220480404450440380621201b07481c1c0b6009610a03102aa000b005010401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 74055865 1250 74054615 74054653
    0x1513121212050708240303032a0a0206010308030406020405130515010203040e13080c0d020606040b010f1d03010b130f06090905030a050706060b0f3105040e07080f 72
    0x1401c84103000c000c185407820380900811006000c1d000d40002e6001c450f2140c1011904e580b11000700a02940d07128200030a6140300080380341c0c070f0030b0440c00900c1c98502e071207211082900d1003c0c2081e0b00914a0781d00e152241d4141e070340090029909181c0802000c185500e4001880fa07065804140004180c50000c1e410700388000102011411034008000402038624881205a000000710f031081c0406501484d00c0c204a12440c10700300c0d124060b02401c0005290081291882100143c81c148440e001003001180c1c8140c088000700c002c101c0348c4100b030045681d0300d41080b5580c0406000000d4048081000030020803254121a800c07549500a0384500314190003108014181d00c4001d0258211f1682c40320749902030f4910b20801c10a012544c003060000d150400801001c141c00c45641e101c160b0201d03140586c0c0030307507119083c101044428200000070500c0061901510840b08074056052000f040040d01500715041d41504c0703900c1001c610301c481400305283c010f8012000700035050042c42c000c42e003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 74057115 1250 74055865 74055887
    0x7050a03030b0a0f300506090d02010903122301090209011b12050c010209090f090f07180b010323042009070503060301150305011a040b15131212 64
    0x1850b10f4100810028205200703210588619281c008103100500380d0403a40b54850541401c42c1d203910b51429000e20001007203542c0500c08001c2a00c00041e40c03010141d00380d0344007000080000b90100c204500c1070809034820000d070081e000c80c2041e02d986400e00405001001c1e040210403540c0001d41c8601503800030503070f1800c19040a6806017440040d02c903944100710180008051180000f0076040c0c070003003941150f511144c01080d60a440c00d006180c1c1040d803c0072200200c0b0791050140c06200301c0000103501e4100c03a045841e11051a4456140002505030072407014141031716a244888054668861000300604401d0b18400d185400e0800e07980c8400a00705074010769000d21425410f40d01c8a88045134840c0050078000d580341c40300000f1a004000545407250340840070200070081090640088070b000141c00ca040d5a085001000c01c4200d9640014195220a010545030341007a140310140040444000310001007a17910800b902d41d00101c240c0441d0907c41c21000c410b1741c240c2000030560 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 74058365 1250 74057115 74057119
    0xc0105100f060c080405010804080403050a050604120816050c010608100221011203081806070f02010c0f09031709030d03020c07060306030201120f0609150306060b0c0a03030c0e040207050a03030b 86
    0x8560480e11070500174130aa02805041160041c001018400000100c40c000c542c000105d484090490402c036844d403800f40d4040358441c0c011301c0c007041010311a5840500030303103240d0740900990b146460191019070054030000460754940000141c000414800ba003c4100ba00b400583d58015043d150002c2e00f40c001c6a070101050304400621850b40030300d1071452170075414140b42110b07403a107a601a241d4841e84c0c40d409810f200e56400c02003800c0c1d004c081c0d0280518560000d025442035100705903040500210001d001411845c410404136051403449a80c2f00c43c3d121a1506d00041c3c0c00c0800d0401500c0711500b0f0120f6000510101401400c000d40c600900c40c61034100001401e541c00280046052081c445000c4e49902c02c14210396140d501c01c10040110b42810040e50700d01507800c080001c5c1510007680c84500d04080022581c054408403032103280300201401c410501070b41c05030000d2804030a0f030800c100642881441d641c90b00d1009242141c003610052200904c40e00d4003c5c1919400c455042c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 74059615 1250 74058365 74058377
    0x8041e2901031e030e09040503120108010b03030a08041a01080d0909060e2409070e030705041406060a030b03060f01080c01030903050901050a0c08120609150d02040b060c0105100f06 80
    0x701154000343d141c03000e02518102140c2d042e1007030508030b5182450003200c40e4066a80340c24041004400030081940e1400c1f034407140c503641c0c0d03904030407400c031555103a45940507002000044401c03071140c224198818496036070841e0b248034103100c0d06003050b001d03002201c0c6a401000f08040c4c894110310a02d00038802001e06020144c01c00001380c094040c0a009030303550708003204003c00c18003081841c40302d800201030300c000c800346440400105101012003002d8003a020388000800ca90800d8010205040300d600613184e06900c9490502400d54000240c61082664441044095960034051035008481c180108551541040101803c01d0320b41d2201074145480d0080580002c0e070010f06a40b040d06007402d2041c0c076490a008152032030980002c0042c00104001589105c4050040c1c415028202c1501d900020340c2c6d581c1da1160310003029120705070703014201010150061501d80c2224210503009080d03241880c0c600c041d04d5007901d83c140c07600002c030040c0034400d003c0061481004401001607190031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 74060865 1250 74059615 74059619
    0x30318041413170711010f110f0102130f0b040608090f011404020f1002070605030709090e01020d0c090e0a110d02070b01031202030f1806190509010e01080606030708041e2901 77
    0x10381d03a24805011400e0500400b030090820003230080c043d0030100120003003594140da111601042c000d500c504100864085250404110340302014080d0080d51a140c1a40d407a0a0a00e502503402050081501600d8031807848207a4004c0c1c0280603135410760000c0410b4001c2400c0500c1003040c00302084008501451101c2021380d2071550025607402126142e00b0095070f6901d503824101c90104054012409543c2030103c0e050b04041c0541c010000c00c10400d0040000540032882280c6116543c854401e8400c07862000c1042110958410071500440809151406e440704034060240d0f0050b000a444110541c0c00400c140400220900d07940310781480510710b0801c0c0038400c0d05d0035000e10306040d10f032031141d012143c14030b440d07050880301e07051400d0001d0300381d4014000c80142154041c071105400142c5100c00e0120ba54001c0050b14080d8000403d224155610810200d802450003070040e1602d4241c45645801030034401c4da0005258040c2c0ca8988003030ba11000544400c0c113589102d020101984001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 74062115 1250 74060865 74060873
    0xa080304091b0503041527060609060501051905070b041a010b030105150d06030f0c0602010b04020430080310030c080c010225090203070809010e07050303180414131707 74
    0x4480d40aa8440e00300d03403615a05880400c01821f2a0304114103a1a80d03014000c0070301d9400c03980c005114424041889259160350f600c2d01581d07a2841001d0110303105020550024541c2d058404556100e0710302607041080a4655003000c9005542c245d400e0000020000c0200000d02e100758050b1042c0c40140f4503651416000c100c03035a10b8400e014204032400b00349280f020344a500100000d5030401c86200c0011611b08104070360212510440c8003540c03034584880c41c0c45c00c01d4001c0d102207420303442c0210301f0325a44030141114454802c004800303e200517101d040010b0880d40185000d03054030074070039010504518010001c820107810007400c992200a03404800c3e0f074001583c01144030300d0b0b02141c1642007078a16042c0000015000038a1141c000f10410110a500610300c51162250f20028881c44081c540c0064491000307000342501500308200920708104004400c41681d600588001a07801c88480310b03200100b001c0e070b40c458041460100071418001c84007a107a039141c102401a514000c40c03599 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 74063365 1250 74062115 74062117
    0xa0b2511030901050f0903070602031c0606020c0105030a0213060302091311070f050a0512070b0708071205131e05150108070510030e010e0601080d0903050c120c0a080304091b05 78
    0xc910b90400400041d91445441c49030700751010300101408407217400e40c0b07030301c8041e40b01d803c0000910764041d0600aa40c944201c140144007c907440780d00541940341107400112820f44c0300806200080e602005814a001910100c800c028441e0b95001a00d50a043d0100f0224081420000402a040c00c1240c1c203407640c1201240c40302a0f100c0c20b84c98684855140c001e05240041d403010300540201ca080c20040000b04000b40000c42c4204800c0801382d60340c510550f147e40d401c0e9041c40c00141c1402c0741c540c05e05400d07030045400851120049490040d03542e218848621070b04900f03003032241011030140800000300120b002404810004006a6040000440e5140e0a034843c00f8820008425101071440c00b070b900c4420b002c00a4402401340b00456455556958000e1040401501c10503825445c114468044c04068a1303200c00500100701079070301000310b00742d004d54640b0071074000c2d007412120595800038003100a100d2007001d140c42d2440c00440704120741000c000c140030160502668200980c3c000c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 74064615 1250 74063365 74063377
    0x50102010606092304060e010b0408060c04150305040222020c0105160c1101090308040306020a020c030141091e01020403020108010504180204051311030318120a0b251103 75
    0x10800b03103002948034000078080c1c2a01c7c0e21001c0e0454407000003281c3c0100d00710050081d1000203049840e2502ca600300701242d84514880c1000800128030b00c07602c05840b0360072868206000410840c4201d0303082c560028080c0c82c4810301010241d00142d0021281404e000c0c0b00d80c001003050030202c1c000701c3e240c03015103120454180117181d0f945941c5841c0c2e003680900100e2001d980c218500c0c9031155100e281510003035104419081c0913101d00d01440c41c031441d050007551480c1d0501d40b00c18105001c1030b04207540441c1000c038940800840301c00380d0f198090050200622a00d103400c0101640f00310b408902803c0700c00d4180098859004000600140c3d8100c0ca410b41106c2d400d40d40014100b10504900018113814200207500074208810300103104515000810010301404000700300919101c20160b40740b2076013540c00241505000c01015500e8403080e0241e100d030048080e00e00d28101582c035404600000c0701c0f0120a140c1b80240085044507242034001401428242000e010410380030550784d9000758 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 74065865 1250 74064615 74064659
    0xc080402060d02040f0b040509090a080409020c1e0114070c02030a110f130b01090905090d1b05060901060f1706240316060e0d0b0705180306040c05010201060609 71
    0x1d40c0c502c0c925a030ba04440040100810050f02140c84d208003100e19400703403081c01d200e0a040c1d40481c61110020410b2385070740ea0b00c08150780c6410f103803d6410010b500411141e2401d4001c2201280780c4111000454000b0310f8101c0000800c0016140c55100b48800034050000704289001c0300801030b1400240208411b030400700604c04004100001b5100240079188142c005e07915105c0303403c1c481c9007a0030490b52158240c8402860399250880c4100726081110000026408000c5c0c002070203001c0c0e81350340c40d074844640b00c45400e4160b60b144c281c0360620950b4103070000d039500d0300700308441d01866151101611f825100720300c920f4091001c440c1c2d00ea50260100d204040e0b4040d0f4441e00e0074229803001015040a000c1e2082038000304520a014402c0f445148007040c011600c103804d902e0001c000281075944885904c105842e641c104944980004030b071100700d44041d040b01a0155000c100f190300c164030600c5015100e50400d4002802d4030407541c48078040c030180090038458001030703803183ca101c00e8903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 74067115 1250 74065865 74065867
    0x3d05040c0f1409060d080703111905070e0c1210050a061b0b1005130509160303080106050306150c010504060b030c0109140a09180c06020318060c07150509090a0c08040206 75
    0x1000e00041104441105c010112140080c01d02d081607040381c1b0450a010000c803c1d01c0260401c014140400e1408640003004c0d074202c2c190501207404075079a03081e0842e00e03031903841742449866a800a602d490507101c0042524611070100540d140214842003d00018a4000300000b11500d00503082c035072202001b000c0381c40400015030301d02c60416101c0010a80201040d45a0b200a007404c0014003056403201d0190103080101030301c50000b002c6100c1100e5145e0b9070700c0403076883e2500860740c0d0340000e003003243c2c80a070f2121001100382c4140050040d4440100000400b81031078540710040312083c40c90350b4025000402c6c110340720313038014107070a00302e50f1781810342d4036044891800245120340350340003000700925000d5210300351040090780400903031184040020301511407800b070740e69000e4440d504180c40400300c040d86271800d041015141c140c00c95402c030f400590312000c52920f0070b41c03c0d107140b20000e42d001c11400140d00c0c0a1004e5600801507200411410340c03020401840880000c1019000d100c1c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 74068365 1250 74067115 74067121
    0x1205010501051503060409030215130525180612031e09030203060606090d020604090605180c0a03090201050705120315040905070312020307120e10050306033d05040c0f1409 76
    0x2000384600070034104000c1c4c03081e2941c601036000145003910f1a0703080d42c040c401d0180b04003252140000c100050031030082e1537008545070100407811b2281200f912000103444001c0000c1c3c11065421404c92349100b41c40701d501160312100e00850703041400c004a010041c0801d010000741e140819a960094401e03076070031b641c0d00943d0700400d04a80b01d0420094210000140025030004598030807401d5038000c4601c0c0f009025081d401d004900001e40f03080007c55400c22040c81c0c1d01e0f0003640058413a5206040c00760408200e501d400741409003041c8000704010000003001032500850b020303c0342255045604100342d1038140c84c3c4075545c2101c0d0000820700c440b02101844420300810a440c040e0342d100c001014550f0040c040246100c6807031810f14001e15100348013100060040d0107407032080d130b40503000340032565564484800062031503502e40b80c1840e409001420500200340d071421001000f80d008101d60a0601d000300070403001c0d50081c1403140001d0024008509200d0014200c3c00c022070fa088040d0b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 74069615 1250 74068365 74068367
    0x30b0403170717150612070f0203071e030e03150711030412110d0203030a0306031106090f010c0606261207020907031a040903032a050f0d110301120501050105150306040903 76
    0x180500b1000da01c0880464000c0c924001b40c0321407480742d0007540d0f40d5950708100c0c04c030590780c1c2d004031040140012140c4020117203c01e200380868004501a15080715419941300102e4185030030b002441c0030f055001005c10103c00d0b04413110024004040300110b19007440c020725549036900500c8001d01024050016074034030303a24442d0089a442d001002d5968800c0c100c0b402034000d1403103200c00c8840000e040d480c008070f4030f4100305880e04000007411105000c4a1480111460142900308a80c003550b43d64000c91119001403840744591915145048401030100e515860030918800980c1d400c070007003003800010384901c01c449030440c019090102d04002d40f00105414103141c0c07056582c1207072600e02108103255040d0031004210340f44082c05142c611681800015203e02c030404100862000c0004000461101c4002c104008203080d0014a42c0f221500b185060b901c2030340b061100c80780da1501c40d03007030004c207124117801000103d031001000202c2d1242140310780801400c0318452a80e54207048241 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 74070865 1250 74069615 74069641
    0x40209060a0507060c030b0a09020d1b02070303021005160c0510110d0510060801050f0a0503062505091c140a06020c0c010503010506090d0f0507030b0403170717 71
    0x448005014545400341c60300014001e40140302d05840c00d030f040800341065640203125121300000c028021103440c508001860340698000d60071001842da881000010312850703050310001c6074140c1e6019280c1e1f21325604000349042c2c0f200703548094151410b400d015611554070340c0c0e035901003960308101514034a40d04140e41405d907070044e07522895007041c9021410320031041c01000c0c01c4060310f1041250307484283c81d428a0400b10b000b03c4000c20090b40c0141300310f1408070b0315003800c0040100f0389007041d034650002c24145001542c1c5403400a8540581201c4100349002c0d4018407034040c5003da050404e441c0000c0c040301c00500d2000149014007404109000c010200c1c0107004c400c1c0e004039840740d42d043c5071842c020341c040501007500d80079200c080c5040f903105904690403640000c0105041ca20608108010f00d4a0f4000407a40540542d00d0800000e1040c45104000d50280760002414509800d0141058031004000d07141016036904000d11135820003107910180340654444603c9640d415181d9043c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 74072115 1250 74070865 74070877
    0x5070c080705060106080702030a0c0b10030f1514071b06021908040201091409010302041a09132904060504060e010216060b151603020a170a080708070c08090402 71
    0x10081001400c80144400022204d048840c690f5580704581d86403a0126240d00407844418001009080d00304089401c030b003565600300d00c00c0281c4a4090340e0b40c2d0b580841c5030700440000c403844c1ea0701c81d108800804207440344100c1c00b01a0a4900300900d001c0000400144450007010307071075000e41100d80244026a410381c0c0720301840000090f244c0c01e025130044c2545c602250202e000444850021820a03150b248828069070040d14090356a400d40e42040050044011101c1d54140c0d1241039900540d01c07000038500500c440310310100d008605081c16002d10003202d104001410103006c6a07000e129015907410f030b00c182c001d0400607841e2154074100c03001c0e01600c1900740b119030000c24500350b4030030300c09440b00405d0711450301040304907180c4060020201d54114200004841484074040080c1c103c0d0b04030004074406e10545058480558a20041c5070000042d10085d100220365025174a400100c44c0350481344070f09140382c961504020003050032000f03450040000e100400d50f6901900c071038060300c1c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 74073365 1250 74072115 74072123
    0xc050f0301090e0d03201806031303080c03192309031b0606030304150c0804060522050f0d05070e0405030a02100b030312070c0c03080a0908010212010905070c 70
    0x19595a4403840034002c0c0503c0000d403010b902420000c55a02802407003075102012041d0810414544070105c1b004080d04480344604000640320302d505510b90340c900007103108035060b4a0340706070301d0b402e801c005020303034402006811800001c1080c07204007601f040551505a15a010102d850400e900305d160304480a0850070301c14045050a010002c0c40200c0a814000000c68060f440312689603e0345543d01002d68020b50140c00401c0240004044109640c181c0301250400c4031004402c0da5030b8041540c407070b92050000510200f0b0003030660a20304400324681c11110066201d140c02c00c00011081e48030041d200e441070005001d40b108120003032020000900c4100e04480c42441d26046c4a6201c1d4404075120005000b8000305010050303452082d89107900003c0c00542c20041c00285032281408054500c80038408500781c9003000071104030b03002020754421030042c0c0e04c9152402002c0d0074600b0541104440f17034018421600c106100414142c11945000000709003034507a00d0090b546440034480c064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 74074615 1250 74073365 74073367
    0xe0f0d060606020708100207020a05060915030a060f1e051309060608031b0f12071a04060b1f0507080a091502060106090e0106020a0b092d010b04020702030a060c050f 73
    0x40883c0c000c01d00e00220755004054641404410115804034410100025404080003c1c14085406c00703001a207070070314000c0c104e8003000302241d0340302d43c1c1a00708032010007140c1d80301d03082071200c10648644140180b034204111521500c0111030320040c070711280103e0380a04005280081040025000f090000b904200c04110154451105236183c1cae005c0ba003400020900c0000d4691250700000e403008002d800c02001c0d0160b011643c1081c600b5502415003039911010700c1c00303c00014503003401301d18016481400001140030f42c40e410700c20130000643d60082804801c054165005400c4401ca0301c1c41a44114565070b540208401551559256000300c8034641e082240c076030005030000360f01d0741610710f15201c0c500403e0381c61200b0519038209008050050f04240c0355200019402e00c1825048074a1409940c03800800711400348200d00c00408407240b02e814900c50f202c42080030310503241810001d8405500d000b5036070300440d03a1039481400040c4940e0341c4281c402c15003482070b0b0555090310215074200b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 74075865 1250 74074615 74074619
    0x10f0305010b0d050a1b181a1207030221061e010f140c0a0f050c150a0c0201020f1c080609040f02060a12050c03070201050609070801140f0a0603020c0601080307030e0f0d0606 77
    0x8112002c141c40d20944030040c040301080b80704d10004804c160101d01c0d5207640c900275050140380e405c0c80c0003828400c28950203104140c031580d005403454014610070080200c3c06e00d0320f801000415190202d0307599140040216215090764800c00c100721006950070140403019030303e00c00d01103610a41c0c2111030030f8001d16105400301301d4038400450b9101d02400840d05240100c0f010001030300c0c00808811069001003080c80c41c1580100907000308180140142e8200004035040c107800c2c039041c17244496070b1040910010b07820704d03046151180c0010065400103c0740c90300e60740d0010340518040d0060300c2564041849481a4441c0d0061141214040c00c24455401c114030000e101c0d40050701c40c000594201800a16181000090540700c0c0407d075440003036991912468901d4001d0800c40190484d02c5201a04000d0311140c0c9818000c1c213055030016920704684c00840d0820324181c000001c2504204418000300c2d41c01071600b016020102c480401e0384100342c0014459020510004029a0400d140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 74077115 1250 74075865 74075867
    0x16030f0905071205072417060901120219080105060a06030b10080c040f0305070e1e04021009050d0b0f0c0f04150c050f0f0d09030206030406180818010f0305010b0d050a1b 75
    0x52806c3c401c219282d61002c00d680360310745c0380100320450300590418406401003203410380014802e071440c2d0020f000e90212102181030341c60301d000680c00010302c981d110001e01c840c60130041180c1c00102650300d0100305000f80740d80040d100800c002500d0b0100403000010a010303802d2042164028001c07140c0c6041105d44e603241040d1507883d10b1041c600981503600024501c000000c031035000c0d215044c4105400c542c1c40340e0801000d181405802e00400401d40780100b855150250520041c50241004901074034140e42c1001c5483e6005000040c00b40c81840322408030441c15041e50143c408500c001c0c452529025821500b003d96851701400302c0c441c458850f120000d020a504c48a645500103a40010003040c005450a5604d848001d400c1501000018046045940100d1072540600301c5000001400c1d10303600e0145d001b00d0b00c101541c400c240e00c04000c568000402d11000c0b00c8038101406150b1409103080018010542e500c0a13513901c0303100054032404964031656400c150142a00707015031501d84 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 74078365 1250 74077115 74077169
    0xc1801060201050c04060509040c02030409090b06040b0102010c02030324060a0305190c0c0602090d0b010f080601060f05040e09122b022d07060516030f090507120507 73
    0x4940c8015503e00300110301d04050150490f826110305861f1240b40502c4075042c0310041a40004120440c0001c0c04003285496250283c65000c41c080c80a844007804e0402c104012503e0310030425043da890038940c04040b070740202c180c0368170088080343c00002c200c0d10038118003182400025a54040800216903144a401d507000078016660340708400b5001c01d00c404d9a204681d841d00144020a640c0c911500c0001c030190000d010410000e415410100c0483d45e48242c020b03003c0c2c110580f8040314010500c5118410000c0d1070040c0550700c3c148a00c03903c071280c042d00920541c0070b039030400c0100700000b8940a0b1b0800110701c035582c5220340540ea03500324400080c51400c4154003802c03205580d81a446e00d1440a00907580802418445100c000c09800301100c01d407403c3c1a4403644441c400d00580d00800c18031310425100d41d40320382030a40c20b0140c46ca4018100d502010010a920707161031b00000200310005841402d4544000c2049024009170418906e020030f250b1211800105190f582d40031103032011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 74079615 1250 74078365 74078369
    0x10e19030e0901030c0b070503090604080f1506061b0309120106060f0e0303030a0509100c05040315290609030106090914030406020d030507050d0f050712060506030c0c0c1801 77
    0x556032244524041c002c1240280003884040d0407070b94468070600005040800502819201e05d0860786000900d40210b103440c0c00640c8903041c2c0c0c1d0040201800396081c00c0c00603412448001e1a56002d503c0c0c51400680c1600452440c12508007034003c6510144034100202d52240c0c600500000310140c0c0d1074407041c00782c0300700e0040310f0008800803501c0b451180119903440602c5001409035085644503600c0b50001d00307008228910b41d03c0368038104003521300c01d481095010003565451581d560f0542c140400450388507000709807050700c0e103005800c001c1514948501412140c096078050003070401c0c0001c03404d001d0412080d91651808900090540d02580081001e074822080031103a1111021081d440380118400d6030056048106404140c40c442c0e40b001e40e10004a041241c00c00441e0881101103c0024a502c904281c2d280d05015041c0d40090702c801c451400c07488280701280c00c00020030800d0001400d008141500070070456100300c020706c0351401c601d2000c1d08071900d0240c2c501200c11121028 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 74080865 1250 74079615 74079617
    0x41e09060602031213020a030c090c030612021c1b18061502030d09051009110111010606050702130608030f1b01090308070e030a06020c030d0b0301052205010e1903 72
    0x4200181c290300200c140c2e1401d8400f02e514004543d40c0083c05000110990300880e80410a0080400000c07400c082d0f01d0050210848000707000300c0d8070500501180e1450f0040740e591141c80e0b44860050b41c80550380d10390481001750704020714009144c00482e002c009502107050031442d18001c10003140102041c420303002c10110900507140d5a000303640c6e542180d01c0c400c0005810409c6030040f4018550082c10101c0d00c2001102c41c07a040c20410b685c21a64001e034211290b0348801105480c0390381c0551420074440550300200011840c203c006096407080c800002c0c01403108404a58010b041907100c5001001100e065030741d2400d810707080021560244250f03c0c01a00c01900a0b4105c120510502c0c481c1541516030321896103401e0b03000d0320402d201201c059810f10503015118001101400138050038070243c001903403a018810310f494113403201d104202d0b02a07850320040190500c07000380605800201007400703054940300d80c00c0c070501505a60888404a10071a98500019400e8580e100809806 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 74082115 1250 74080865 74080871
    0x2060c16060c0201090506030121030e030307060608160f14120a050d12061809060b210c030f300a080609090c0102060403030515030a05030405150a05070303020a0302041e09 76
    0x4035000c00000340000e002c0e01c2c2c41100220300354ac4945204907038800301140a401c0c662286102c03100064034580c0400d03012500241c90705002c00c46104200a43c08040c042500c60710446030420000c3e001101a40c0f140d0000411510500e281d2500d848040c030300044950b0301a615007a507281815661480c1d40c0e18001d0010302d150211182100c4030b40704031010303284015001150036044941400140c803441e10203480242c2c0d100880d803055038520350180341c1981f0460313100c01c42007100e03983c6500300180d0308101406a00028001681c2001c081810213200c20840e0000345402244461b0700b00c1d441044030070744086030001400780001600300603c984a00b0301150301c4103156a508040d151189802c840050160380070802041c002400f9400641c4d00040d1030320416071004c00b0800192038004001c900743c80c09e410004060216041c0480780b4003990f070940f6601894005400402401e43c410003001400301580440e800300e40034840d404940050041c03064070202a0018284003900c0c15840c807070100344034a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 74083365 1250 74082115 74082119
    0x30f06030313050409020f0612040203010501060309020603061002030708030405030c070f120b0c090316031a0403091701090606061e030c02070e06030106090504150e07050d02060c16060c020109 85
    0x14000084803904800e080000c0c02c0c8900c0c00b41070101400c8400c800b26842008200c03000242d44030200540b0b107034444c0e884071340b00c1428940185803c440d0181c004004050500e0115130258545030304580d002502942c05200918001200b20b0231805a0b020007000d05000000744018860000050800e0503d22016a414913a0710221100c40b00018859100c0003403003120101c0209a840c80c5940c2d01c011400b80703062804200700b00103401c1080303407961440c03c05140300051080c8100c41908d1600501b440001d21524101903c001d004030382a4800c0110410065082c403d00100c02c2d005690030903406402440107035100ca1026103060600110540d40c44040140b0104141c807a000f040107408007038003d8104203050074058250080011704064066403074030800904050f01c3e22690f4420390040c40c03ca1074400d107220214060312407101e1810f04540c09005d007481642d030340014400c01c030351781182c050b80c0d01c5141500b91030500954611001d001c1b20500400294a41c02c10700503d4001c1c800d0780c4d800c0001f5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 74084615 1250 74083365 74083369
    0x6080619110406140c0c06040f0e1b030c0706090b0a0506010206060405010e06190308030109091b06050406031d0604240e0a110303070b0a06030c0503010209030604082d030f06 77
    0x1c0281e100fa44005100f95107502135601c40300d801456030301d000c3c00c1900c144000c540c0219541e940a03921510740e065143e0400c020304050040240c1e0442101c1940c840c0c04211058101d206000c06011480031000014603a03003041000d9001948450f88111500381a1038000d00304401020211816400f5006036000542c0924042c0300b5241681c00c00701d00c0b0384440c0c0342c1c54140318080403415070958040822480100104100e1401b030b50007042482808107400c0003034a8040c41442d80f98000d00340742200c101e000d04c46c068110307094a09172400d40c500092180f4600c3c032046145072800507201c2040c0181c200740014000d00300000344440100b06c00c50041000b8080344141120922820403a140c1c00980c0c0c800c0000b0f9405504026045008003101c0c140341050301c80d0b20703181006450700700501e0b61301d4100300200070340704403442d0081008500840c10009401c0100382c0701c2900a00040450500084550489800d25080100850028118805001290b44c400d04680c42640c030000c1c00100440011603074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 74085865 1250 74084615 74084617
    0x570e0a090f0b0406120c03060b01140318011121072001060501030e150c030702161401120207050a0303050c0f0a0206270a080d0f0504050109020a1a0403020d02040608061911 76
    0x170551041c607030809186541c0742c11b401880c030b43d04524100940c0c0844c0c40c6102c01950065801750116008070386000055440c11801c403000b5401c0c0400c08030060006090340e404060741050001148104560b5983d80e90300110703100c8005074109280c03007400742000c0303041400561040042e9070080e02d0400505003560281680d0f83d614130a100c510000e840002a0742040320b030085d41d000903150044840200c403000400402c456241c21803808500c034100e443d0300c2503078014034160302c826107504114940501c070b0b110385444d2920464040d00341502c40c4080703a12002c0d081c04861400c020054070a48071b50340e496009480c2d10301601c5250041e100340281900701d2482107007040d04895020018a010001a5642e5060340c11107920b064500742e9034140305130764800500409229601c908000a0500142e1041003461140c94002d101c11800d0304a45490f850704900c1203030305480d0100c9050010005510014000d020b41c0c0d0001c925a000b000d05100300c0c062a20004a080d044414051015800c82e624000c41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 74087115 1250 74085865 74085899
    0x80105030c040e010207230c0105030f1f08010f06030b10050607031407060c0c150c0219050703020310050405190302030319570e0a090f0b0406 63
    0x1058006000072052450306500081100e4403620000d810011940c49407200018090712004100450791020108a0710607c0b20041c14102420300505604000300088030700f00004190340382c200e180c1f01a070600f83e041000e240b401405200c3c000d0007501041d0b5200005400c50b0303c4102c0340c02c40b2006c042445940f000820909481c000740c00507080c15610786007110f00c3c1c82c0b0320ac40403c88500400c01407011070010f0150001e41025030700c4440540e03545181181003ca480c03c9031083c00344c07030005805201c56000c556281980409601100b10107000c1c2005401c11469500080d8548141d102c007038110791142e004580b1a5001e08103403260b000d40311000c48154001100c0040058208100160786001c17507a60315010200110300c0001d031162803103021040d082c00b4000350120722904044902038003114161018030301c0880b2044007001030381d012014200c0020012104180000a500c040352a01c0d4203c401004101c1c826050216001c0c10100f0360003421200c5495000da0704182c03000c5001440020b143c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 74088365 1250 74087115 74087119
    0xd27150e01031e050c0c0a03021b010806010f120e0708060105030f06040803060118051201090203060106090621110403060c0e0103111b0102040b1209010b090408030703050702010b0a0b0703030c080105 88
    0x6500342000480f2401002d00070b0801c12040c0b0280300da90710180041200042d094400c6d001040125035900e2200f0382e00040d40035076410010b202d4100102070341e101492800807441814101244005109584060041d000b030301120b0307109228001070b0850001401d14125081035040e14036a000b00c038140764403000200c03009003a0704410808954103500c90103800c0d82d0024083c56a80c1c0040d200c000060400203801c40060b916911218440190718081c4071440c010407290508501d6140b410401519512a51003043c005c0c5c1000303000e0800800e181c2d00020940b80c03408052a80e00c40e202d1400c0401040d009440741c00286481015862035402446041c0c3c07a02c03082135099007000c202c800c0d10201214040c43c41404ac0d5001d010004002c0070090240c000344820300c0c0303001120301d888004e090856503e010403d100d17060003410b010208451004503900103002c1d00c0e001c10559070b9080242d025010415006130421140000000e0809502d805895828401c0c1e500341304100d031000c0200d40b840700c00e001e169 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 74089615 1250 74088365 74088401
    0xf030302071404020d02040303020c01030e1c12020c0a03090f0b0a0804060b01120606170a090308161b0309140906030c041e090c03050601170d27150e0103 68
    0x44041c0102d82e120000755680100003501c0c054a040800090381c0040e4800c0b40541d102c0004c000071580c040c0600070070b00403c0d000810605401d803000c002c43c50320b84003020b0103000b903a031003855070091300d0b4044807403c200c40c2c01110010034061900406800113449a1100018180d2003c40c3e203001620440e050803c80396100d11458a07962079200c01007003c009100d06000a55800300005685c6000714030045c10075844000025501040c800480300c001000901c040345030060000c0001d03000b60a5175003094178030303e041403a0700ca4100d080d5420004001c7d0708210000c030607250001c0503405420070040d264100d401c1855080d0f4001404140d403400e480707c80d03051b045464a10702074101030b4820000303008e445004d18840808a100603085a204400c00d40f40020f0a030414414070200b041610f0042800300030459400d100050601e031548514044101000340a40210300d80a00400f801e01c0b0400c0042c034048030b403e40d01ca0005030131a540400c640c0106034140d00c206032560203440b9100d4481001d450300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 74090865 1250 74089615 74089619
    0x1103100905060705030c0c010501082a03071403070810051602010902031f180501020c060603060f1612020c0703020f01020331120302100506041802150c0d09030209010f03030207 78
    0x3584d9940000700184550901070140321081c030703404d000c0d4074000c0002c1409811301000b011b0907841065000500185444401450b4580c17035100040c00c0e004889a40c1440d0401d411044006820311410b40d00c5480300380f240d01d00d0440c0400c5607901aa02a407014614100110ba001106a00340d8440000c081d40c181c22007048081050b1900c0f21026800c1c01d000700c005403a03991006034064900190f0b00560303250b940440c40500a00c0100b100c150450400c4000b4201860000e410010b0150020001c03a404a4910705000780d980c0100b06214110200180641d00d03107070481c04081d6150071a02c020780c81080141c80441240d400031013100c5d24003090404205000240b14070302e0f14201000404169480c0441e180000c0c0703c0d807814411104c4500c0380c0e01804502c019a20100159180513102034880c1c1e00d440072008880ca5111010440c1d00e5058804032410b400c40c0c034000c1780307034020104407040178090000340d61061603207c40c030030056034400c80da4019a0b03605c03035225540c56105404014090781c400074003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 74092115 1250 74090865 74090867
    0x1f0c030e0604080106060503060901060e15070c03060f020702310b1801082103060f12010b1f090b030402030c191e06020d02120a050d020d060311031009050607 70
    0x180c2120901410951030075640346500307401c54540f0b50100c00001c4c1c000c030071300041e483c040d030255004010380c1c034200308200c9214001a034144d0701411380b1201800d00040801c100310310100c800c0c000710b4100204024101c640c03407950340a98000a4203d200d00300e50441603003000d1f001c40c9a01c51544e10074940c0784000c142890004014140c45508690083d0b0a124421f460101409618080e0041d04064641d050014407402c09030300b002c480544501c20203108110302611109500000c4d40c0040341c0c184024140080018014a031502031700c0e03000290102070441d0141d03466004104810940e9034404902c2d6100d40485c22030100b03940c003d5054010140d00340c1a0700e454500103140c10348a1442c0340b0101c0d5910805000309500984070000c50400f03010411099805115102c0300103018000360001c500c441141030303228450007180c40284040850441821842541524200201d5001c20402c2c15200c0c01c14000103c2e00c41e03000c1e4402c0c42400a1545203992601510b04800d1f070000c0105802c0d119180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 74093365 1250 74092115 74092127
    0x10c0b07031503021f090e060d0308250e0a080a2001050f0a020d140304020a03081b0a0602070b0106050f180d150b1207060207050402030402061204050c1f0c03 70
    0x1d001070b80c03650040c0020001da55850304800c426400000d840300840c07030121000d0b000403544e5001e900e426800340b0030003c8540b54103500c0036030103905240103d03999650005501599441002c2044d1444107040d2880009410801444007031740219001c00c0401d0b9910381d11079444580340001001c2100342c0c00001c036420485100ca03100158141800c6040c43c00c150600700c12600520300c2100168081d09401e07803d16009500c02840481c1c0d170400724954a01030300460350f02141407000800e5280001140f040001c1200703010708030b0080d0501554400f9250341896000794110300301c1030f03038030720410000003440c2401201101c02c4c10140540c0c280c05d01d0702e8200f10b04041c052014982d500800c0c3d2100240010344100021158120000340024500c4243c1c001c0c064011f480d1492940b059000d41814000203400062000c00c5a0080701d015a0b079541d240701140e075030302400340094415007405062104100d40454200d41000043d03910440002e801c00a46001c100051904000b241904a0301c00220780306035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 74094615 1250 74093365 74093381
    0x2509020a0207050613090b0105030103020303031302010e03070e0a0e03040302130e0a08030a0903020c0312070b090a05060c041809080301050103050402011107060207030b090708060121080a09060e010c0b0703 91
    0x70041c1c8602ea80d40350013044850380443c0c0f0402d41140c0c8142c040c01003500300d1058900308003080c68140c0c00c540c11a030100e030360b901c40500f03100e90281a411070f002c1160300c01c11801110384005816a03116a9649821314404401521212205410030100c2500c0032000015034003203a80041131020807070305c1161407100800c11001028001d014440400d004100244021030041c0d0705004005841962410000d0038031a211681612a0304402444941480b024050744c80041e040404501261a0091000d05d05001104000d10501402d020000310300450406081250711418841140302d044000020881d051110300500004041c00140101d520a0740001c0e4044d1060400300c803040e4143d0412450300003180e101c600142d00c124014000c000720404401d40200e00180240b40b00c41c2455a800d441d820140118402c22143d0100a400ca001c25080108001e03000100b990751b40c00000002080390307896004010125029105141e0a5407041420f4264244c00c01e4014030f141d180d01d4011405083c001e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 74095865 1250 74094615 74094617
    0x10e030c010207180b0d030f080912030114120a03020a140a0305040b030c070c030c090b0d02090103060216060606091706070f0f030b04020412031b03020a0b04020d060c08092509020a 80
    0x440d403403078150702c0746c00c40c58098034001d850725070b81c0319101d002c02007034640001c0844484e0303004906080c41c40f102190039281514054007000740b2039071944012402e038106408114803548180c9051009040d004650340340d4840c0240c03983c42c51248042100c82e600c0001400080c00a01c04100030010b1a20110185801100e130041e081e180004607103ca000c1c040440d082950b03a841c3c00c0908201d52920f510460035107034015105800d096460341c00042e01103005210281a07150000f0380c51446071041e0321042000c60384030a0030001c0c00e46562009107a0a2940070307005800d502c80d510f6212100c1c002400c00d02c103615035988c2c44041c01005000722a00d0f5255851407042c581c031440208802e9885002401c05045d002d20002c02000e42802c004022000b03600304184841000c0384588040b0f036010900c0c0040700e4004450a40a4130385101244000100043c0607040c24501081aa085648042494011030848049941076030b08840081061044000302a11142d128101040f41380595005003000c0019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 74097115 1250 74095865 74095871
    0xc0807020a08071e0506180d090504020901030204121406010905060609010c17120619120b0618090f0f0706091206150e0717010b07020d050f0d020a02010e030c01020718 74
    0x40b4103412500c421181000312611b404c03140030001050300c604a80131201150000814082e0480783c00038241c11414001d1501694000400d2040383e400f0b43c040318024054a4400424030300c0754180100c0d200c8490200c910140103080c000100f5071480e014450140b18010a034515101d02480152105800c2c041b0440745401e4881004009c0b4440c500903102940520000c0b1a0740e151a030300b08070001025407450000c071281c4040c1031240100c0d030a24041941c0d4000050700742a21003030b00041c01c1d05035283c4030800c8000408100803c1d0b00000c034468000884400c00c032640d025000d0000ca031141640d0207a040010b581c2e000401c20300d64030005030300388280101000200e0780b0070141502c500c0011600081004213844060200d03055000480351604144160009100d5040100405684c410500064410070b4030310103040a2100a00c00071390f481d00c0d00300c100c4825240c407010103502c83c119854181e021880722400c2d81d29904011480c0c410490050740904401c40c105884407003803210503440b1540d4a42d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 74098365 1250 74097115 74097143
    0x9130906060e070906030b0d05070b0f040306090309140a05060f09010c02040510031203050103050d05070303020d0c120f0501080c092a0310170703021c06020706020405040c0807020a0807 82
    0x1810001540905030f15912020300ca03080060182c04d4070300d01d00b0154024140000c210006c03c40c0440d811054a042004642d5540c038501d00c81c032035601841d0405070900e4030700014102016003040d4148215050281500005032412007000300070203042c8129500030508000c1006c04400c40c3c0000c0030445014140010b201c203031034002c941129012940d245044102c0042441440003003610351054201502c0e05000a47c1582d0b6480d0f110250f403400c04040c0301000c10960304150098056079a206110703a810440c40901c9a40245082c0e90001c0e0810041d25002c1401d030006058060039050f1003841005080c4c2c009174000384210b8004c01840b8041c00d442c0b5007180c48901203503141d90141041055039075512030a1401d800020b98442e503100e40042e60860900308d8541d000810310341c0460360125007410074145e0a0302288000140075000074102c62000071010b08000300340d8040c00035034000750b40421491562450544007020245c8070310300540c1c010030b0900c00160340c038002465501d200700302d80501c4076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 74099615 1250 74098365 74098379
    0x60e0d0c0e040221030a03151e1e0b040e060402041a04030b0703060e04030c020112020a0801031b030321090204020703121b0507020915030604030c0308060301020913090606 76
    0x200d11500080d18108032074052200350316040c41c440b6400003400700d9100702c1c604450204c6030303240b161107010018141c4488445210403000300e02c150041c512282990200031904c0491550340710300c2d00480050f15418124080801859a61402038031041086146030070700b000104030500c180104042c2c0d101d9001c10010500c2e92010941204840c140e104250b1514214a0189914840181440b04051900b032040100075070740e00c1e042d6081605400d1540b5401454001240c0c203030814254801c6690000900d090a2640429024100c030b01603440040c2c3c56032035441e840811300345440b02034001004080034404500442030030400201400b01c0000d00fd034500d50124080c3d0300022419800314181480c1000600554001c040c00d25115040c0240c2c04c446586000d001070182000c0640a884200001400080103a81c010411100102110302903d840d1500409000707552070120b0001d0540b4000ca0820305050090b0343c1019401400b8200d081e21411801008044144055a9454036400c00240f24 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 74100721 1106 74099615 74099633
    0x41805061008061207060e0108090102190f0507020301090602090906030a021c1401060b070507080606090105010f1215080f06011202091f0b070c0503010e07060e0d 72
    0x50f032030711408105407070000e0445507401e102e640c2c408680e03141c10194400c0000400d80e5802220356401380c113103082c0e000b2103090030303030b207200110003102c105000361060190318009150050400070942c000900390741540400b62070195000507222032500f00f020b03030302d50f10903001d500518900f400d903400720701c100380108945050020440e03042230810401405d20395000c81c1078030007406410f8039100c4079422544005012a024807032010f00040d11040410190f114500040c0f002d48035030329140c015582d003030340b07003640c0700420001010070402c502c010712a50002400008001189074101070010380390440404040000340e20890040003546000314083c180c1d1035042d036600f111030f1292a12013410301e401c50b9641c466050300c52404625003100c0000382c05094055282c1c01d1407255104141401c9a000000704c4115403c9050203201d414020781040c40010030160004d90030900f01e80f6502a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 73920865 74100721 := by
  have h0 := BRFrame.cov_init 73920865
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73920865 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 73920865 ≤ n) (h2 : n < 74100721) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
