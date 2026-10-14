-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1765
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:35:38.420663+00:00
-- url     : https://prove2.me/submissions/05e5a137-f127-48ca-a677-4731739e643b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 317266187 ≤ n < 317446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 317267437 1250 317266187 317266207
    0xf15010c03110f10090b0c0906070f0602190c053c0a0501060e0f130309050402090102010e010606180801051b0c2104050f010305090c01032f04030c080712110402 71
    0x1151001c3d90030507003408510058645010030a13424028a080c1000100340840e540e6a41c402049455150700824204284c00c070030300733003a002485240c4481c10a009109070042c0b085c6e81000300030313041500450640f0180c0c801c004025007940b0040d503040c018400c450555a000c038900c0c40e5841031032883d00086811255040d44c0b05421a022900300340340603086182001000034000c07080903403203102c03130b204c0408141c2250350142c00c00444d03004540c8910b0700407070481c1c00b50f4400d52100d001050120020710110f0f0382ca54000c0c0c10b128840c040b61090314120300c0701081c1d01005001e0f0900900c0c0c0040300c00700c0c08282022080c0b0079040300911958901440d81003580c11503c0c960100401d10090910f40d03a517500d400204103e030290748006074181824001080390200002c0307403164100c00c3c00e0801203200849580030319a501c0090800f600d0810141000d03074005d580307003006401900e114500300140d440d2108107055941d4146e1003983c01c00c0d295020080d002445201680c901340501402c050304001d0b01e0700c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 317268687 1250 317267437 317267443
    0x90102072328060f0e01030b12060a1a040b090105060f0f120108010f05040807060b0a080a03270f090c050409050106170601090605070b0c1b060f15010c03110f 70
    0x44a200007000d411060940781e4a106a8010002c003002e08001480c4d081040000d444d07180d01c000510306140d91159060402e45031003c01d000354403101000c0e45d54603e85902d000000f40000c8000d480c40032828629500c450900d4800c0796001040144446210ba107414204030702c4d6401031311503030100070051014556166584000d04003121440b281400558145456203003161803040d01c44034041d06005c01c2c8008a0351f0401121034554000c1004a4a01c0128001c5207030f0f50b105c1c0c0e000d4445407191030030401c03d05074000e1082c01c0040380780035030a020040c00ca04039407100e034440c003c04105400111003000300641640c8404800d1079103050990426035140782e542e084510990001c0c02250380002a811584c04080005034004401d0030320150013810b005c801003d50160140007001070b041d40c0d000c0342c2060501400d50ba00882840700c285403080f4008400c07a107580050b81d6030f4051501c0d40d0086640400200400210414103a50f8400d24140c1d40e02c04488400c1d47c5010103801c0d002e00b078000c4403680300134 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 317269937 1250 317268687 317268709
    0x901060206040b0709030c092004090b0909070302090c03070c0c0f030218150f0307080109080c1606020309061b0a0b1506090604140a0b040305010f0608030901020723 73
    0x5402501e22890070b0304010341180c00052000c010407919110500010390303c1c465420039600c0c0040000f814016006280c03a01c0280303074400517002d4101003000640b01d0303955045031104590a42c0c42c811203413280c4902680e621100c0c00000c1d030000031000000c0640301d00e10061030380484070340342011045d8490784403581256015009200d4400c0d1040c41803040d801d10155208407000c8480381c000d5503180c1840c000d14010341c1c0d440002d1040e0030508856049980410003400504550340080000307442c2460b08021a6001910007103c42c000c507400400a604007050020460340550040c502d4100d080c0104006680210000d460790408040c003030b40c81503001c0040c022002d1040c1d01500c00350401c41080419001c1c07513884180329420400c91040303152229002e40707084400309594508807002c000c000800b444003503007140d281c441c0089400010310005400c18683e544290f50200213180e194045a40c9900c03c0d240500c5c056030054400b08407032205802084414195900c955038080c00000006840c0400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 317271187 1250 317269937 317269949
    0x10c0b04060501030201171006110312010b030603070f0614030a2c0f19120e12070e060a060c0b0c0d020708040801050906010609170a0606120b0c0c0a020603150901 72
    0xb5880041c000c55801000720861000304449006003450b00e481c8282210700e0300c1c003609080280c8a10304194142c001c105481d0004514405403980c0c1d0b03105d904188854004a8109200c0d210300140020032460726400042601d0080d51501020350030f01e54503d605a02c0030f400149619600e010410340f81800c001000700d00100060890303910302244400a19080318003814040a41000070129105016407003011800d9901a007000008810380c0d1003507800448850199421010486e10005800c10100c3c08200b0b41e0030255002c640c648484d420300044028500860011035200981000482c2010703803450b034000381c3c4102851425000040c0002643c12100044820b07a101217010b1005a10030300803d644400c00300010038186d8902000242401010310441304100004440e066080c0c2091201c03041061304107a06101c041e948000e43c0400700210364065941840510120b220600503204a1742000c8289004081d2036805800b000b24a42c00039182583c0703120000c1c20207949490314403041e802048 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 317272437 1250 317271187 317271191
    0xf060f041a0f060a09090f0216120f0201020f030c1305130212090105070c081e032401080103031d01090e0a021c02090a03060e03120115021b0d0809010c0b0406 70
    0x40d02010310100301c0e0301d0b5180b2446900b050148501180c1d10a0304075084980f5000c0120b00007940042040080c8101c0c000b100041070903801c01001d01083c803e00c8101800c0954038001c0b405c0440208074200c0c05018074040c1ca1840810100700754011030800741c01083c220f5500084995644e50001d004540b0440224041c107070082803000d0380030401410305601c800c40030024055450000700003040c218242400030031b107150100310300151115070a035040441d100f848100d556810710301e402c0c00500401c880d60000f070001000800c140d651207000002d040300c0e8103403100d201e440005070800307000851092040741007208504000918413180c025060107101c08501c0180e0798003242801c094002034440d4001d00c0d41d03004000c0040181c45a10401044980118000510b030000391102030a40c424041402280c541e0b0500203d00c40341d060b000104201095000c407484160a0040f00030103640060740e055102d2101103021000c101030350b0090540300300506d0300016035942c6a4038441c2180d002e46d82a2040340d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 317273687 1250 317272437 317272481
    0x3121501021b06030a0e10020a03020d0b040c090608090118060e07080a0f30031a1206041401110f030a2016150f0e150c030f060f04 58
    0x560140804010001c005045900b19820100032500b5448060448140d03c2c1da200ca605008902c203204550902000c0c0509543c0e5410085e8001c2c0a5000050307090252071608070745220614162250f080398015076140d21494a207415000d9442000c010240e01d480d54035200454204100114070130340c158030440c0000f03150a004d2500b54500107082c2c0200b91958000c40300c07440400e46400400e5030300303640071045c1c08902d070320071402c1400700006041e42c401c1c074071700c100c040c042c2ca6816400660300aa1016404c1c82140d03025000c02c1400c003004084c9040030341012000c10081031451b915910721184240c004200000d100d481e000899000c5411f0101040001c004d1001c41000c90040c0ea4090f0b130710301c16618540402c0240c44005108010000d01c10398102d42c030301010030101c1404496440710b4610200400f00040c81c01c1c0020303202201600b4014002d0146800100c2c0030720840034016085e0400f82070541e543ea01003d14a00c4000e00111f6010500c01e01d818107680d600d000e400c000c0030500000561007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 317274937 1250 317273687 317273689
    0x90501060f260f190305090901060c2d020607020a08030a181211090a140901021b0a0b16050c010504030e0909010c210603021507020108250809031215 66
    0x802c2c1d1840611681d0442129401d00e2040040d900e95090200c80c18541e204001d864165998800d80300e40d540c10042c90800000c2c8541c0020002d4412030240310003004080809412000740c045c402c1134a100740d61480c2c4d23130f0f0002d03003800005418004d00c054450201951201106403030b5401140c04400000d0400555070900385181c120381e4003c08a103103060828403034607915441c42400700602c00340160300c080001009586c030f41d0001d61100350425040d805e07030305200c114103010754011010504040100118400c0060001031105042038001c0b44c00d82c0c8540f5400c2c08000249000d80d82e0f803080107420720030501c034050300703115290040d4403a88030300190f0140d6505200384080020000d1140e40d142a10769440650000b151f00d00c0a804449110794040a82c15141f00404480d040a50030825401c405164140450b0041c419a4000d0701c80b61400e0365034540700c226040100301030035002d07815148103c1c0258024500d8581148010341a2410700000d44140c01c0e40ca80100d030001c011041c42c503101c0b001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 317276187 1250 317274937 317274989
    0x10f08102601090f050f06010b04030b041e0302030a11060105130c1707050406030605010c170a05310f080a020d020f1801060912050c1302040b030403090303030513050d03090501060f 80
    0x3524060700600309642c0340c4030795849d10b80036510001c1c0c0102001d10008040000d2040f203003c520501741856070a522807030800a40d260420400100490b040304503005c8034032000a030745412600c004018461b1200030106a03800f800c800d000c80320030f000840c1c500c040b2908041100301d22440b0711740da030300d030315149040d500509841c42984a0381c14801411007070404583c56a68401c2c0444c00072907010703640c4904031003c841c0d610075402c46031005e103408882c0c540842513100700d0340341010f2100305130120284c40e5048491503158912a00040b0f41c0507580050050420080100000f80011304444e0100300c4003003c01c3d10700d030b1400c040d580c1102c0702400510220303030490b01c500302070320b5505543c0040ca045507859503a0754900256503885103046a812110982c0d05804a90107004510595912410b06203006080f94107180000c401203030801c000683c003040c00150700503516400c0030040100719810721080c2e00801c1d00d034405840741d54a030440400d04401c043e071404004c0048480f010311a901038108640 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 317277437 1250 317276187 317276203
    0x80703110d08070c2d05070e0c040f18110403051f0213090b0607141b030a11130608010507091a0307090b0c0f010c03050105010f08102601090f05 64
    0x401d00c80c50074188000c0d10b1380074640300c104a9000d5840e240362002e00110715058a4028180e148a0001c40010410808003154006c21100e001d594a5416110201e84c04580d000c0c6018054440031400001c014640b882040b07106000b4240c440010380c0c0328a805214030643c050f810945503a802090704010f09468440246c0098005031411030409142c1420003d1401691203400c0c111512010151901e0380c600080300c10855000e44010206400403840c0c035204c0983d40398118580c201c1e020b07581038509000c03806060b200d42c80740d07042202812100403c03c00b41c4807000711060403a82d920022800c104244a5240a111607444400355240b4028010b03442c11105110859540b0040c8207000026400c070380824240d0307450003503183d02d50200c12141482c00603c0c0c03011441540c2080c1061824541551000b4180c990a988010b01948000002d0326001010340d14400c8001d4a58003c0011426100c001c2540c000b4085805880d021004c00700c90030b4450303c90054445000d401e100404104c000c010700d007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 317278687 1250 317277437 317277463
    0x525030e03070b1902010e190b010609081203090309100e03070501030b03210d0906060f0801091a09010605060f0a0e03060417030a021b1608010b0904060908040308070311 75
    0x8280c140c10f103000c42c1c00f0380c041ca03011018048070400348942e07014000e401000d005101001282c4107031030528071011102c1c82100741507482404510002c192907102d2410301040d02c00e0000100940c11100c0148c401c140c1c80101041c550740801e20824003155540e54816158107620ba84000000c0d54507010141442d2495200310305151820508859584022980321151104074801e540002804003806407144144401403038040d1170704401e1000c110083e8000002d445113542c06c40b001d00c1e141c180c09400c903018108003814800e03004101450301f4410710443c65020030a8000441d5040e51200402c4c9140c20144e0004207052010450b00d015941c0b06160301d41e06d0740304030018800d82c14542c886074081000c02021941d0003c001000541c0c10800d601141d0804944400d410007948404409645840d0143c2130710184070500746002030101c2c2c3c14000d586061400400404050721a59100002400400c0003102c0d1843c05110010110700030002901801e800b9442d800900c4040300b80090811401c0c40c2c0c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 317279937 1250 317278687 317278693
    0x40c0302180106020f1b12150a05160302030934030303020301051509150a050f04080a060e0c010e06030a0f1404140d080a0f0603050105090307050610060e100525030e03 74
    0x245d68201125400480203606031131084441f40701802240c100b4032441d102616882c80c03803060162a04d0f69601c8580718003503002860845600d40c4004405030303c401c0e10014099404000d0349650045440fa0f02e0f94003031840c0004040c0a0a000c1400d644d18800b54403e60201c0c2c1d0100040041c0c0c10004c0c0c200740000e06800002d480c107100d000000e4244140c8117910030407001d02140304500e80e400f0b4001c88031b203816107021080d1540d0f901e00c203041c1d030342d0102c40701184d07914203000c0b1404070442d002032940c1a401050b12404040e904440c01e001c8540c0005003d14425501e60031020b580b24120300c2003c0094061114841003031600f41403a64000c82d090180d074410380c2c40400c8003140680d004c005941c0200c010324001c181441c0800c08840a001d0b160005401c40d440d00c1c0c1400742031030300003000f02341c0c1c10311a6043c1d4065a80c3c0707030036081100d18140700d11004038011480c00c054501e440c0c0318400582515003401e5080144809822100600c51008600358202043c2e440c01450f4001c410100240d000f1401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 317281187 1250 317279937 317279953
    0xe01050112120f030f0920010822150501080f190305030c070221032a060103140f19152f12040c0f0626040c0302180106020f 55
    0x604103400d6480e010380340400101d1004aa103c52082c4c001503150903682c1401d003c9007180e420302d140c0380044030818654440382e9600408055000b8031500e4494125041c07a001518041400008010f1015204032460b080c1c0071a54040b42e505849241c0c0a03220b11801070120040c6c0c01c80c098906036801944600134100b0280e2040000e504c01c08480d846009000301e26110b4050b480851008000100125520400146140e0b44443c0c00406003003843c0740359a145410500440144810a10545080e41a43c2140700144045100c2000f0000c195640808a50baa505440a00d60400d010044000d41c050f4050071600203000244600074000c100c00b010801c80d42c14240614040d01220941a04542d9050071403c4003411060050311629080e4800c0180315141c2494004440b80490040d21161207075181c010a9030f0388610b44009140c0c107161821100b901141030039031440c0c2c00040045441031202c4002100580343d95401d0310107010005031422281d41030140190501110203100021940301c05c2d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 317282437 1250 317281187 317281193
    0xc07050619201b06040b1902060106031e240306060501030b0f10080c250515040c06030e0a081204060c0e030a03030207060f020c0f060702030a090b0d0b12010e01050112 74
    0x3515143d590034803060a0901e0000340c0102d02d441c040c6038000841c0e400003054a9501003a032041e405400e0b0080e5003520611383e2141da09404489040200c40038450201d07070410340402e620f620154809018010480104e00c2c40d0005510303c06981d0001c0300c042d9140d0504100550b018042e4101745102280d01d148242954000300311001c00c00c02c01e82c0b0407c101c4001044510300710b4030890303021080392482c0c6c1c040c00100c2400f0f4814400c039100100e4030b6118010070181d4080002a0b0940541d600c4800c4111951a103442103014040704107000015018900c031400014103020020005209030782206942071a00d410400115003a81500e1020b200800a44244950300401d212170f506506050041c0c07110003c1c10000010a40c800700000c50302d20000d26040354143c000303001044403242c00100d9240380d480390f07412600c0c3d0046d000d0303034000b141c2d500c0814440d0315483c0c000303403840e812071000c0081c103a000040080d103454041c8a115041d40d54444103003e080303c2c01c2c0161405009002401d4561204c20341d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 317283687 1250 317282437 317282443
    0x506030c07030c020f030609160b07230c0a030308061201090b06060a03060509040b060a09020408120a0c0501050f0a0f060317300703050f130204020c0705061920 71
    0x14000400f00074205003d542159a02029542194406421a650f616010020079034a42c0c2d00070b000c0e8031210f030044000130450400703003c48480301e90040081c3d00400407254000d003440003804207032030903010b217a0a0340303440c1d11003000302002140a640ca00070780381000e50500204607084a1070050f140d0605401c0030101e80403144241c0c0181042c4c407015030724100a0030490090980d6040a540911032070305003c180020f103a00d4a010b110100c5940002a42e00c2415008a100318812604940c0080c941c118403082a40090010a20760b810409481e071200d540c0e0394219903003241c42c00400d806c0d103020f1000d003074564807480c18140e81d0500104050340c2551512004441980400040004005404035808000040010248100c0300c10031214056203c802d1513030200403a4031000003490500080c840c058a40f00681c00344100615110b00c803581d43c2c00b400040c2d404480b840ba03291081440c00a4a5111500104800d02c444003a0b0701c0250310b1514000d1a507810514902e010980604403490010008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 317284937 1250 317283687 317283697
    0x5040e031204150e10020705010b0907080705030612010c110d050a050d0218100201022515050c0f2109011401092703031a0108010f1e09020a050409060506030c 70
    0x101050301c00c030b03c0000816102070140c241d28881207000e192140c02e03045610784c0140001d00d1280e4002e001428046c424400304606c21110f02c800541060301244003603003d00d004582104010705100d042d07001c001c0d00c240c20768040a1850340011200d0000d001245010300918000b2412071420521b4825566001001402490f01111119a00150500311042c01e003565103401d05005e030410001d5801440301a0003034100c0c1004900d041c0c0c8241c84248805441140c0da107400d0703441a003508000b07030005091001000300512500507110200056100e141d452409800042c002c000c600f07821707902c0710105601c010f002400e6016660704041c0704032003c8030841040e0741514a040070024801031050400005070055020120084400c000c0f04010b0540c144c0110100311840d98010744a04a5280110340031107003449221a04081da100030300c440305803204011170144402c002c85420607101c0382a07404a9100036400760118400003010055440d5501800700200000c481803030640c40d040c5201c00d079505c11 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 317286187 1250 317284937 317284943
    0x110408160e01180b03011d0601030317060916090e0c04030201090f050901030f08040b030109090b0f0105210c1207030302120c03040510030f1a0f090907090b060f0307030605040e031204 81
    0x640d0001040c5403001d41c089601c001500103d1101f41032150742254540d0380a00050b0001000c040350304040841c0d0f01c6d80f44e8011000502003060039681c04a0341024000794002ca0010085074200000f00c00300549903181c020440c1e10701e03040d511131852001505003c0140c0c800c1c0071444d1050000c104c0c076910350040504403a0000c0315010340c00603070310301807045108a800500424401200200e52450181c0c018210310384900000f06194580c04004a1b51040c01d21540d83d10105070100d11030240c0b00380501c855003203c3d41040318241d0790100c00265070b6542c01e4000401903805510108141541086042000500342c82c1031868020811107142c2c992003107014082c01000140d0002044034800c3d80000304c0020410030801c508000e448161640d841442400c910518030050108243d08e00001014091315003e0000e121651420381104080d003071140d0300700d0384150f0600c818660303483c142004502c1041300d0380e80003802c80e0800040008072003280004003120740c0b0030b000e042d401203001c41441d90002d030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 317287437 1250 317286187 317286191
    0x11107030b0705130806010603060f1202151602041a0301141302010c150e0a020406062c011b05012703120e0f0703030c0c05010e180a110408160e0118 66
    0x6903001d0a000a813034a600c031075124440d003000014860392550008081c0c1c0c4071402c1d0200950b6641c150303002444258100079600020540070707070a09c2cbe030144009045920034070a2000c449210740e0001401c5038a00d800d00320380100c0115411846150031b01c11907241c0610700600320301c141402e00188200d20b480300e00003814490740488070010b000c4420042c03050440502000d000104440c02c1c25911054810b100300d000b40d040010100704103026078007030341c0350f604054191030704800d05903480304404d6000c0c5049030500828000b0300e41c80741581c2c442c00b02400c0c011400862403401001041b00c00e14206401c103c1d0b0120301e07001c3c03140001c6c0d000c1c81160342202003400101e42c85100c3c46185040440c100c1c0620f6051058020010406822500080d40180191900c09102d56a80019121030004000541d0301450024410494403900815070f0303041032440800183c0e55031011080e802c04d501c03903045041b080d03020000c03000c9110b03a10004500034090046010788554034200041240c0d41c5c0180e036a50f0456 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 317288687 1250 317287437 317287447
    0x6330e09120c0304051c0611030105010e1c080703050c0c040c08040803040c080d09060201051b0f0a050706060e0906060f0102061b070c030803010611030910081e07030b011107030b0705 81
    0xd03200f08240c402800c80103041030582020041c8030350038080c03840d000320385040c1081c80b82c01200b4001d00070b81e0f04030b96040e140c1c0030901d4485000c01c51107040c1c3c082800b800306031070a16280428000409001c1030b030320946549035141e0399240c00300d18208000c11306a1080341010b80c9200d429070300c071903550741281d4031130b0445032a915545800c801c00b800d00c0d0440e82040c828216040e41490744484050200c0b20b0f503400800c132640b500100002d04440c0442400701e900c40400581c032800b0b00a40080030b4081d0180740260030180e0f0355a0f114141c0700b6685c40010503550140c180502d1007000c0c800c035500000225a80c42c04265407400103911410300a00200e4400e600c1ca020502c0d10700d050040b610300f290700070140c9090700d440346004e0b10503410a002d15400503004a01c10b46049600000300c1e203554000400c50119120892000c80381c91034028400c05070356056126261a0382d40c01c1d039080c0d005000d6031700e000c1000b4000c0f500050888080d03081008603030380040740030000b050700d22400b1078201c1298074140f80e0311 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 317289937 1250 317288687 317288707
    0x7051002180d051b1f051b030c1501060c0308041e0209040c0603060515120a09080a030b03061b0708090102011104090e100c080a0906330e0912 63
    0x104401d890303125000060740d01c0070000c02001192610603107812103200d640e91180b01e0248100b40e4440f07240380d8545400c03400b04801c441d0146000e080c0c0c010520301009035014542110078156002014005e08d01e030700001400d9000c001c05410303a400340c100b038644005d02d075078651402000905e000d400a042c03002901e443d000c0b81052600c45d603000507000790000c01541001c3c5010b09600344140b150000083c40d210300071074180b6140d20444071a84485041d00e0420401440da6100c40074003a00b0341e1907455460605c0e4001840f044003a000c0c00b06c09407000074070341e0010028507041000c010403a210321000d01c1c00b1100d0000c0840180c400058100f0116500c4050910050340100740c46039001103120004240018110150f4101d84011040c0009031038410450b4403500042e00ca005000c0000f0841c600300040100103e0380c0503800103801030202017000389070040b6040c03c04a00011140b40c00c8613094000e03d1300d26091814400601e045000e00d155490410103058544012200c40405000001034070f90354 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 317291187 1250 317289937 317289967
    0xa0e0f0109150903050601080109050a0305030702160801021804110a03051306060305031902010c08011e0e010603140108030a14032e0314010501081f0e03030906070908010207051002 80
    0xc0d150b20802400c0b660216200a4205061031204907483d10818001189509041c0141c0c14003e0303002c8010b0000700115a82500c090b0001041030086202d141502d600140d90901ca0038010184000010780e5408040070f41d10704c80003000030103030149043c070700e20714104580e100445800e0943e0713150010300754603615070084e00440300050107408103050841c044184440030004040000c80ca4100c0c10141103000d13030680c00c1e1845001e0f8070700407a1b051001007003400b4494000380c03400c1c03200da03411507242a00d501540d0799195080c1c00190029030344000c01c860100582c0942e034090b007008801941070285500c4001c003409a980c1d51300c0ca05610110104001e00025651b07003010005072a03000c9502450f100c0301c144080030a102c19100c1070344208824501c15010b2003000d060341e5091024095981d0021842620240740122031001140c0e151001202880280081c50040c91000064000c5081100000344072510700d070415102ca910412202d00003680024102c2400c0008840c09030f242c124020350b00d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 317292437 1250 317291187 317291189
    0x2030a0507030912060b03100504080d050406200c07050901050a03080c100f020d061d06060a0527090717070e0109091418120405040207060b0a030803060a0b0a0e0f0109 74
    0x500b4200c420340c03c4d0801c00641c00c0081c403a2026000c40300d000041113614420b0ba40c050b140a40f15980801100380040d9007500b01583c00390050002046203004410950035070b140744540d44400020116400f500c5102c148041c60003400c048421200c154105400120051140c0c80010b202c44000611446410070030301946c61050f0b1480c404010124550035140c0c040d5103c0d0003661000740c43c1c1400803a41c82e081c074841e106100482182d030300a5940707002c01d110b0b40786e2100961105000c3d0500c10b0354003045845100ca0200c50311000c0c0c0850b0b22001c1d60501a54020103490030b002d00c1801c115034031003d01c8901c19198048418030303041c44041902c0d0016908510b807500302c0450386040042e8840d0314903c80d00400d0103907072031000b600c00d600e10a80030261141d81411032080c42c04010441008a0310302500a041c05c2402140c0002d09804400001080c100440d80203c82041000c420072105c0e140c00614100104158840c0500c0c0c003030a00801810506080c00041c45001882d02c40c0c001640304100c82c01c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 317293687 1250 317292437 317292449
    0x120d050a1112070306050103060b09040504150213050906030307050d1b0206030708090607020c010c03031a040504030c110922030201060e1906050604050306071103120f04051c02030a05070309 84
    0xa0780c070700000108000e1102c0807203401020030f00740385001680b544280301e00c07000c4410300b180d8241440e450a08020203480040d006580545c04030b0410300c90091284024031101d21900d03a404815031404062162542004001c3d5100b03420600c0035401041004c02c91000e0a02c051401f03000d0717240c0180d54408191300d0310501a41180021003004203840e00181000d0113110b07507031704a4500382e41302e0404996440c1d002c00117600141109150380d000900a420004142810580f007500003070101c0049002c56102f1682a40041ca0104596081c40075580d201c1701085030030ba54241003460304d200070004180702c0040140780510090f2032401410720039440000030b401406200c000500744440c40ca120403e1034801106028a000000141c0d4a8404111002c50f203024001e49000c1d602c000d8291025400f155100701d441c0020842c0941126844210038440c1001c020901e66070306050810f6854041040c2c4003074480d8852154440180741c0000603650744058502c0c10541e10a9a46412591500c09070311030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 317294937 1250 317293687 317293721
    0x2003010e0a110d060603240902090307090c0e090a090c14010302130e0907060503090618030408060403021e0105150906040e1f0c0216030213060e0a0b12120d050a 71
    0x81c031080107801001c11070300710740d5082c0132032607d0b82001c445c15129601c040d0902030321400e041290020a8015000c4510014150b456aa0f602c1d440f00c030580320001191720020307000100c261198030340003078600d070400e80584042100f2030941d0740f070b03901c08481401817078011117040a41c991941e00c642c048440707641d400e0340f40c1010955a00c1c031070030b04104141d9000c030f0540500c200126502d4420b0302564406c284070001003d240e00d40300c0310609003130040e1881e1a620f000070840440c00304000c00a00340514800e0f4020800b00302d092107075100106019010990b542d041209101c9031961088260302207507022920707040c26803030b032034000360050400c14080100b902601622906050035500020030340a0b0201c070038080fa0905001c00c9841e203c14180c49180c60a4441c0e0078400340c01c00d1900360025142826001403c035840c1d40c28401c19080859100c903042d5111541c00803103050031400c1c505c214243ca4000c0c258191007480b24030582c01010090584180e403200014084001a00400301c128846128 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 317296187 1250 317294937 317294947
    0x20105160512060402040b19091409010e060105090d1511041d10050406140907020d02070303080403020a15020702030c0603010b0f0f0d02040605190206150105130512010c032003010e0a11 82
    0x1054100b4150740900443c3c0458800159180703000015010100000d16241081c0e0a08580031052033740680658100101070045051035181c0c038a0360312280b4002c0c50b440c50480c000c181000c0503508071986051001d0f200344801c0140c501d03150445205000b50141ca02c0c0c040e5607011070034908400700e6100e65407060816900003000034403400000100ca030151041d04060350b9119042ea91010760f0082d40d03006074030042d03040001c00d10564040d0341061091065075580c00c026100c2c844046060000711010541c0041c628086103010411800c4500d01030b10454111b601d02842140e0350f014104161030001e1001840505451700001100c90032010000110f48454540600400c560042d050007400c03142c00341d203a81d2003580000b400034880c1b041056101800d5103101c004440c40d030044a10120280b06e8150046913645e122180044025425000043d07450345070300c0f0003010741c0c124002510040c4c0c142a0b481203520040c0089074151070f0f41c42c61155171502c500c2c000b580140042e2070b04005031040030038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 317297437 1250 317296187 317296207
    0x50a05150307270f12051e102d06080c1c1b170c030703060b2e030c0504081b1f030b0a141e0d0b04060c020105160512060402040b 57
    0x241a01a14094600c13810410f4603110703900c0c0c91305143c903005403aa03030104003001e2261803c845806210644072003a5880101e640b0f90140a0700c8440720020300424501211a1001c9845803d080c68029a2001172010500c1c0010305900c403140107954502840864040b0350341d8103140c0c1c2502105079480000c100710921700a800c80b20030a4a801030185107580351034691b5004400082e240e45809006016103150b81c91503413850f0040101e48103064100345d81d001010707100440c11298200c54401c00f01000c7d07025401e560010120b03800c0d6928101841410b10003446031407000a0b890b611030344000f0000a407940d100b80085e10340401c10005155a01464100380c08490341500400600c0400740c425661194a4014508181401002c0590441229924174001a1050380c2e49005000050801311381c4c840c3c0c1e500c580220800c111000c1d2a66074440388402c0940c0d9092040e1640300c1100e10300358a03039440440c0e0091061141c0c14942281c1036545010802c81e641d0303641103600030701014100c80d5131014246 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 317298687 1250 317297437 317297507
    0x9030c0803180d0b060103150e090618030a09031403040810020a02070509010308030402011d060d150e1303050c01020909010303030c03060605040f051201110a18050a05150307 77
    0x18901100c81c2c0c580c020350072035052800200c401d50754020032850540c1c1d00d41d00110000c000a11704080000200d400001301d24030002c800b203008040000203403803949441c40a0324180303e0100c0080030607502c200a9010b505612010400640364049603550b814141c40b204207141d4001da03000100030b4010484088210211070b8018400030001d5000c0d1750050742d5403410410040750034813016108a408000160040d8420030301300d0004140500d0141c5a8844000401c1c2280c01480e10403556a80d55803404041c0c0b003000301c4c001d0003401e80300f032640c0b442d10708840900020300b1066001002d109000c00c1d4451070714001c2d0159a01d005c0701405215036903a690a008010306140c0c40000042494004c0108032a4030800459064a038805d60800030945084140403101c0c590130b0b501c403129561912603145918043e002400b0014031503031000c3d5101010400545850f03100d500a9100c0d0084000400031a1100c0c400d02e035000c030030301282c29102e0f5642982643c1c1d40200d50301c01c080d5030101c05c404a4882c8562 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 317299937 1250 317298687 317298697
    0x60e0616050f0f070e0705130e0a0e030d0c110a03091a190e1e0307060e060c0303010e18031c0506011b0b07020106090b060d091e060519020a0e010f09030c0803 70
    0x16148480264882030f90682e070621034500070508c1000c18501c240204034081c1116078004c02c1c3c17060001884200f18030b01d1070968109800c2800c4076a110195458455804110000c1e00d800c10030160034005a142d5029040007001d20407041e03c150b6421040809016035025100f010840340000440804100c900414180c000c03a110b42c49003192255058010843c000a24241040940240f01c0c09052407410780d8070071b090100007507100700204101600c020090001d14007c112006980501e41010004100d03410540444820660300900c2144031000b400340c00b650140d004031100103070a4540c003004813200c114250080303840080f10101e0800304507140d40010b00c0b0300040c2e4000c1080c02d4440d00c0d103405031081c800d80c655003c0018860351140720255401101c009108150144100d0000d03009080d8041ea60301050300cac01981d80003004015103103420b025003102c02c1c200381113141014402014000c0703101560520f0412640942c080c1009020340380b000c0203950403002c1c00d1310341559682c0b43c66072a440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 317301187 1250 317299937 317299949
    0x7230d14030d050f0a02090102121b031204030e01020312010506130504091202070501090b070b07020106120f060b0f2206090e01050103060b0a0f03110402070f030f0801060e0616050f0f07 82
    0xe244000317000c0694030302c21b65041d8501607000e040c185403150914052a04185442c021400585c10380c0b00f05076008000424070650f0025260b15a481c3c04c0c200545000f024003643e034150f4008010402408613a840303201d043d501300312191038559002040486944c070040d08074942081c9000c00c01c0c2c050001184000603450040d500322030b0840e0725040119a5001c2c00d118080d0707040e00a001d40c100003241c8800d4507520a6252000241299456041c1080c6014400d0706a0301c0c600c0c0040307245d0a01980380146803075800300352843c1c203000c005e100c00b08882e441c0a960044128a0045044100782c0e000e030440001403080d0700741404420013200002d4024042032001b01d90300d51420881440702c0c01d00d52a440220358044030034214480c03468854501c0f00c10703405090303680150708004613000200d60950a82d40c860195460181c21248008050660740041c0c015009010003c0c1c0151455501c4100b207030444688003c0200d034000841c41c0417403030b140f40c002c80c560003401003010580850000050b05401c0f905 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 317302437 1250 317301187 317301211
    0x3030b09160c0b0603030706090c1a030112110d0204020a030204050f0a05010e100c0803040309060f1103091009180203041e0f06050903070b0708060307230d14030d05 73
    0x44000031500e0146400c4805008281a11a414040f403074000e101da40c000000b5081d00e181c145603580e000201c0d2405081102c007000c01141c00d119090012244d80824986e5240440c075550425244201c190440070000386211403000d8101e9641c2c4841d0f40d02440f0607130140040d92141c141c1c3c90041d000e50050b0050b17900515280f01d08130440d14003009540304440041e100e1b09a03d202d42d4003072200c810a04c08c2d10f01d003404501d0040c0b0300000d01100c0107510450090740c032758484904002004040c3c1001c4010841041010010301080c104048211240110101c3e02910b00020700c40050718031405640c0324000d9078000c195a42d24041d0323107800941c40790344540351411040c50543c10041300d880035a034000e4100c21422440034001030860748840d170031a000c1e10890742040d46030ba44104e4014400c840580c0060b01c000c0521210382010032101011704400507031b100c60304050001d2094916148a400f52050303a07400c1343c24040c0000c500811000030309900603695108502e185a070064501a20041c250741 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 317303687 1250 317302437 317302441
    0xe01020c030303010308030f1803070f020a170607030f1104080703020301051f0e040201030603080a0309060509070612240909050d050918060301020d060801200a080a15030f03030b09 80
    0x1290100442c4d05880d03021034a6411921240d2019007804c400030541d2440c40d5400c03c0d0365109140400203031051034400e15894208201a2052022640742a03004c7c0800c00320301200f648901c613010403941c0d408041840c1c0010460200b0b021580a0404240c7c242c0304000001400715284802040110699000b64000c0c4802c1d26811481c0005c82c042c500700d29108040340500f0300441500050054106005260200305a03450f40c43c0c140e05030707111350104400300c0d545d090f1403004c00015010311540b1104a00c09010b001e40303448030203420210baa80002c03070f00550700c0061800750741895a98070803081c03450f0503c0303039015101c030340e17200c010103422100f03640c5031260704201c1c130a10b8404d0085070b0916034044c020a40c40d00c1140340410090401815007030341550240504d05007505188910b9005107000c800101d4006034070509071856281c018048030401c502003040300100b680003400d95400c1003d8242c0001c02d0402c002c83c2d80e43d100301ca600020b010b10403040180e01450b0307058002580c2d4102c1151055084c5d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 317304937 1250 317303687 317303689
    0xf180f1518150903081b070b030112020f04110c0610080d0504050909010b0909030405010905180f0408070c030b01061206030c12020105091224060d02121c0e01020c 72
    0x3410721040c4481520900c00018880180e00410031001001c0c24204100296240d42c1d4404882d040040c0c0c070440000c080e515080d03a208200440310060420f0241546103504007855103d8044030400040d02410007006889910388995010b0304105982d60405074940d0409084682c0300c503810340e8211640c0d05640400b1907584008201600c140c18152100c501e05840c003010320140400007413050704295030320380e4031400640f83c2a44480c4542c0f84440910356070350800d0300241c80304090f174000c00d0103001100081040024008401e03500510700758842402c2d680c807490500d04034882c010300181100a0130030000f04001841401a058840301d4403107981c00c003544194241159494840907003603500c4450b080241d900204d401d140000e0042c03500c28500642440400c191240f03000d04031a440d4042c00b0800000341000103083c8040c0300d482c061001701c1c10035800180d644901da078800ba00c0342205521030ba40d65002005540c401c4c1542d030344407410003030410401402c1480b030042c613240540501601013400d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 317306187 1250 317304937 317304947
    0x403030e0306011a0930010c03060603060e060d0c081605040e03091014041a03010501090518160519020c0a05040926040308120417190f180f15 63
    0x3000e10102c803014100300c0c1701340c204401181c0d404441c000c1d449000255002c0c04040ba0a8011641101c0d000814019840b64004084412990149080500e042c806101ca1200086c105801c41d0044882c00c15802c40c030b08008101c0d0403117034080d54140c0304d5405801c008c40c02010b81c060440304111400c0000d800440e8549450380320b04603800b075000c01c2903101a56050301840c94100804100c1d1031840c1055180c640781c0281095540d80e070b1110713182c0400104420342c3c0c407280000140c90150b901e0046140590a0300c40101c101034134002d2500c0900c00f1006105110342c0c145d981c0700300e041c0c07050340513031880c040065120f03d0b040c542a801561060008140303801c1600480940316842011000a0412103112038124080f40d40036402100c1e04200000c0441c80380805400310208180c541140d0342464900500484d10a40c4424038041060044911002e9000220004d0310450b04006c010483c003000111101040c00f806503407940c94600002c10a10185a104404d8400b0110758003981e104c61001558 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 317307437 1250 317306187 317306219
    0x90807090c021911100315080f030a05090d0c0314010501080f070911160c060815150d090b131104052502030d050109052e09110904020403030e030601 66
    0x2015900c5840e141d0510101c1d880d11006142c02003c400c2904c4070a030300029104040100c00704006500d0b0381494040c0e01c2000c1a03a401007000400904070f200c805c0d4811600d030b000300c942d80c400b40030000c1840b822507200d40d8640720301ea60703010074420381d034903101e19002c04085502c0c10203c240f036103002c00101c0d0500c0005035504285144000410020f0305c1d0034a1840a82400031035000e6501042c0b040c14503000a803292000400c2c800d0011345045810090300405a01000340500c212480501d00f9240a440c1c0405d048880d5240d442d5080c1d0311a000e51301c48014043c2c44100415003209401008114815050000084c510500705402c03517601c058200400e446082c0e44801d101c001d80c00c1100c1b00804031b0f41d519000708040b80141ea081ca8004101c031000c0b201c09070b0064801d5603c1c0c030700b0807618280700503510314085100c14041408510186041e04241014000e410800da611403410740024200415100d2026000303000b950b40d56101c0c68020718441a01e03440340d000380f00f4080041007130b0904c0c41c1c046c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 317308687 1250 317307437 317307461
    0x10090e061509060901090305031207110303160518120c210309092d06010e0306151306080a050d090e091506010323062718030f03010609080709 63
    0x2814904501d04014056001d01380d81e9040c46241800040000d034144050a00d40780f109280c40c0807484e04200c00760000d4000b60002c1d9003604200104000480d00400003000814036280081e2108a41030000c3d990488420300c20380c5c0b01420385018400084005250030b80d101d0151200c00402018040c6024142e801007402d0b02c05d0380007441107020718200b0003042d95220b6004007440e048900075141110950110000e1900840103200401c805d65070002e80300d00d6142415001081c0380d24040f102142c0307000c4040314003071044141e90b2202e002d110481e005040038020700c1040d200300e40d2051400d41d903103508914080d000710324942c4c40003c1840050b00014894403d840c050828100140c0090000a000404540c10305136207498240c040c0c100c040788421b0380505096840c06e40d00f04a030030000c0c801102026009031071095988500c1038205400c02d00c0e001a891003c104040181c68002804c501403403d0010b541d4102200000e4140d903c100c800c0c04603485842959580c585a1150384140c03520403403c0c0e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 317309937 1250 317308687 317308729
    0x405100c0c020f041a0d0b060102010b0f1309050c130f1d1002030402011b03030506040506060a02070308090409060c02031b0109080417010e100b1305041205031510090e06 75
    0x43d100340d0600d5045940c00d081d0340344c1900300c0c2d820008005040703c05094000e4454403a2481008440d5070241f10f002c503012000c90f0500200f00100f800202c60000700b41c82d1607100380e11113402004020b0100418403061400504142440d01e54a10003401400f00e995a8680942410a80d00c640b121080d082c11000356500701410414400ea040075020b5407000d00100e04001c0303c9500b0400450704e600c500c0c032449103ea0b82c04149070609504210a4600162904d442800c04000c43c10403d90005031150489074043e1000e03071110341e00b80014009000b0141c001d84039508026245108650100042018094841061049000142c1c07024201d80d9041402040d0a0003040705102015550740c420300a540c50340008a403010081c0015818003066080c000240c3c0e03100c4210040030314000259080d070700302400c0304200700d1a09495181d83c0c3c0381c000188409120002000c50518075480304104014000941586000d007600e400c002c000411510400340241c8081e0081071040c600a40e0840000030300d0415 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 317311187 1250 317309937 317309959
    0x5031b240304120909020a03020c150903030a0e0a0b090c100306081b04090203010f1a03011e15080703051501140a0303110708010501030c0509010f0b0a030507170405100c0c02 77
    0x15050350000d43c1000300b0900c408054005a00c03900c034001460422006c0e5800b5840303005000c2d039140380580700c03203000880e07040706010081007007000020360390b01510316440030580d07010b64031009040006603031016140024590030012002c60004004240c40703810740e40d0400d48549074004908844030750041a805800c0203240c402e0007040c8002031400d20400500021f515034065001034210366091310a00e49590301c0c0c20441010010018245e045400240c4c000e0000300c00c00141d120000403a010143d00c040d0f80d460070000e407943d0400c0079074040c0140c00102c0e600076482c0d06086956001401c3c1d14250807481e00000f08001d4050504e03940001c070041c0900c0c1d60f441c119502640d2003140c0503003101c450f00c1403507400203000707800b4003a250085003d030701c03121030725800e0500340100030205070000000700d100300f0020403d155500301203840000d503502e00000e49880703144007100c500300015050146464414140002c1c8600407400c02d02d1782464080412229040600603102e0f01d40000020b5801054124 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 317312437 1250 317311187 317311193
    0x1080714010807052b020c100c03060b0f0304140d21061202090a0f1a030f01050105090a0207060b060703110709050c041e0503030a050a080105090f060d0201030605031b240304 77
    0x103051102c07400d0402484400115117041c0e001c07601320b81c0032444107a0040104d844428400d10401040100d640750500c02d890400c0311024151140344101c5c09e005500000060602105a03031220f03a000403d4151040341450010044c41c8a000072003401001e100803541152010301d0388911000c551490300444003500c0c054080084070140103001c103c01c0380c0c0300c2a1a00c000c9505102c0c0b904080d00c0d0072072481248402c1c05c05e15281c140c004d823440029a2409006005a94a600041da4403e01d01e6501694612013880d0076030280904410940d000318005c10b0a40405070401c0d0740c0340150640e08115000a03a5408401d41500e505a0390909141070400c02800041000c04840e80e04800c00c0c4074102c0283c3d41c1d040803920b181e0044040c5400102c0c0403988081c6c9a51020683d4018031040701e81d8545400c040c509031788040400742440e031080e030300d0498200840e4041e400c00700040c08010705807460210f110382540b1440340641c01d0f00b403080e2500e4096810044200b25108c500c0290202d02c10b003181c1d182d41d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 317313687 1250 317312437 317312467
    0x6011b06091a070c03021e1e011e0c030509070f050d020301020c120316050406050405010e130515041104030506220f0501020a0305070e0d02061e030108071401080705 73
    0x709050341c0740c01c0d580c1401c0e40c908000d4150180618025664a00c0c0715015060090034421501c0710b800c905a4080d168070320f2000b000038641c10800c901065000c400104413600e0380104204010666000400030307040e10240b4003544400b0507440f00d41c8040c00960703594900710b500d444403401280e960100350380703081c0964100f00d0403400e001ca10150005140042c01c000091030302070042c1c2c6e401505040081040100d040e104400200c0541030f040c07075801e00f0700b0440054114000c0c0d0051a042114014104a071a65040b04240e081d40c0300e40001c01140c248041861526098412114096400e01070800b511302000c40844046940100181c585070b16014210a0f01c1102d00e008855207450328004180482d40c52190a03008034861400144d07120300404005c0d0545030003c10010034003075001c01010b21030700c0d98140306007250703412503490750380302c08501807002c4c181d05031141d042162801200220314010300050754401e844d01c0c00c07102e60b040d03a007407401110710b22070407104180002c0050000044400d591 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 317314937 1250 317313687 317313701
    0x411010507050a0b07030c0507030206011a040e090105040501110405011b06020c24070903051f02040801020a030207110a2405070b0406150812040605030c07170307020606011b06 78
    0x5141035481c25200d81c45482c6040040c4106440424214041c80042c03605445030030440c030341c24181542000b109441c0a5210b00052090084800240c82004a99440b02c41100d02500b10640840814100380e03d005009004c12501111590b1800b90350590b030070b1155003902c0c1100e005a4400e801d01c1c0b850400f41001d40c20500080711016024000400e00e80b0040c0302c000031440d90001c0c13190003150700300c1601d407a507000600a8800c2c4802c24405101042c0c000c901e4100d0044101e2042407540d4460903000002d2190303600040455102044c294a500d40c142c000f000f0380f07802020603c40f41c25106040120a03100d0744a82107640c44102940c0c0344180da16003404040311a6414000d08002003a26010030880c2c046404881d03c564030006e8a1242c0800100000600351704002800c1584c44103020400f10710690182c0c00501c0004000590316000319001ca0301e070154010f044035454840c0f6201c1c100d80d90401d1f0b401c000035004c2c681c0020760301c8d40318450038401ca041d8548a13604c0742e0510b803580da004001c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 317316187 1250 317314937 317314939
    0x6091520010204030302032203080708030613060803040503060c0a02060414010f060b09090f04230c0d050303040b090a150c050d0516030608060411150706060f09050a0902090411 78
    0x1081900010440d03003840a480118081c0d0007035076a0301c001e054407003e03005065240541820f002070040c800300c0c207140e090300c145070f40c0b22190301d82e25203850b40000c5041c2603811180102504100000c54000d9003c0f01030021200290105d03a040e4454090300300240c0602184000103a10020010700480c001ca44404800380c0424000a0103100802d82c050544219030085042c425001030300380c2003401c19448060b4001c050a00d50310642c1410fa0b40e029514250010981c9504040c115a44400d9800d20143d52007d074003d1100b00c982c82c1c1d0b4501952240c200310341c140d500d004e140000401d0394002080a03e1f141d540081561150724806c080000103000004440301000014400304040400a202d458007070341c2c4010990703e401540c1000141522910b401007407007500250103100016060401c1000d1034041140c9580b01d40c80c070024001d0b030900600b5006084e2604045002070000041c2e0b1950702914a0302c00d00f0f20403699170380100f10554003099802500082030900140224032040341c0c440907158 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 317317437 1250 317316187 317316227
    0x1e0a110105091f050405010f031a060c0c031f060f030c180f0510080c0607020603060d020607150603060b01050a02030a08071803030504140f10031a0603150901060915 73
    0x100f0701d0b481c820f6403042000d0369004075100040c103010968100402ca800b01c2d480c3d14081c42040704803c039900f512111007408900420010446100381c032000c2c090381c0350300f00000e801c440c401d40c0c08109500d40c1a410b60390070b100b014606800400d60361120100b4006581d000341502105a2800b20044600c01780c140900d4455a6109441c604010f801d000e603900031341406050480319410b14020a050216039010184034500410842d001a21040150b030303840301c2c04a0310341d0015141800402d82c01d00c2800401040014258414026040c0e40c4e44810b080c1c0b8040c00f0300b001a1080c0d01e005540c01d104030304201e0050ba0080c0b11800e892481b48078455402083c034a401005800058000100c494042d0000c5011400100e42840301a280e0040e01458100891700c0441308070314140030442d40b030a9400c0c002c1c101526010210041055141f520b4840300d000f5120f0f0b0354034540f05100303000e0091101320852064003500d00005905100346901c0c030580740161009400c0d84281c000c103640c140722105810b01544 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 317318687 1250 317317437 317317459
    0x1207050c1002030316021b0415030c0f140a03020d06020711060c03040e090105130f060b1302070303050604110306100e0306070e09070302280519021e0a11010509 71
    0x5220804030301c6841c4000d8008644a06280c50b18001056880d05c0307900440d80680110301040c28051070710004601d060b14001009402c081e100381d14a0440e410182ca01d103c45030340010949101c512050441d221011850509042076003013000503600e83c800070750300030041c6100402040a07a802000d18500c00c443c0070014107002004a070458010524030085a000402d0400c00d02d2505071841d0742c0b001e0880020400343c548070005181220f01090064804654521a8010406a54890986d07010010143d0107092881501c2401035401001c00302c0c0024101008030b0307490700b800d01800019048500790207045a0700c8100740036521110640f1042000042585d01c1484d480501c0310a019804966800501c680c2080030f114140300d003c0c0501c8101441044444109400c400400030558040102500c1e071900715013003298140211859500f0003034619a202c0d01c00da1b00028a402d0850542e0180a05000d02030701e01d5443c2e140081d40030b002c030a0707400c02c00440d07980710318020404c1c070034014040d034490 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 317319937 1250 317318687 317318689
    0x606090607060608010203240a0936030e01020d0c060b03030913020c1c050409020f0d0e0601050108011202090114150406030c081803120601031e0b19081207050c 71
    0xe10001d0303200c00c10b035950007c14410b11441d00907074a080940900500780440c1101c4c1e006c202105a01d100b0510b02c07030b50340c04403050100d045100a400c003503560841004a068800704010b803840000d58100c020403101259141594004200c1400c001c6098503844a05d588070344030707140942150110541c1c10f0104111500c071a980306460340305111000e41c4c0042e102c1c1c0400500e03d2904124442d1105000b00400606c40e00360751180481d000e94103020700150f12aa0750319100000f07030041c0c000342e0780e6036400e240c61840025070010b51103040b100300740d0310110140d98811103022a8416004081d41001801c001840064104c0031032412102015000414111405600d6842034100d030f080000001e4680c40d040001c207030302c40403480d000521800140d000c0d1140030406640ca203c0c0d481c0910040641c00000352840c2e020394013401514083c0d0788069108030389000c260f0000e091454420748202c01050008140d440c02442c01016070b9682c02c010301d00034000d03005141e01600059802c5a142c450400c1890003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 317321187 1250 317319937 317319941
    0x60c0f080c160306050903030903180307030b040f150204050307061817030309010624031e020c0d090801020f0a081003050d09060f08090c0d05101a1005030f060609060706 75
    0x550448100303840c0c0071509504e4038909441c0c02800c2d1801c641c0c0180144129a18048110b804044183c480251200e200002080c2004240d0b070003d044103a00b4401c00c014081e5155030620380030f02c05d9007201c21101c2c003d02e8000c01c82c05507020b980c0d0154080e14007403200034040d015412000f6841040719400170380c1d82e4880c6c000011820944036031b540000c824081c40c20801d0296501a010301040005400d03925000051000c080901180400d52541c18440c2c1d1041000c3c940541c9031b410780400e41d652203003101500e60307a542180c14540010990400012030100601c01e0761840801399413410303d040c4158008030b40c00d00d000340006405c160840400000a40f081100703103007421003a01c072101e4103440c00380050031004403403001000b4003003c40704001c40258086034200d6500b80444a401d080852810f190340340505003065442120715044030f410501c0c2c3c0c19441d0713190458048440001d0042c40c1a400c4480e40025203400303020303015620201d03529191100186c45001d2002c3c0c6041d0401c0704580350082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 317322437 1250 317321187 317321203
    0x53108010b010f020309012c10090512060105240d0912090b03060a0302040c0c0203030309010603050607020312150d05010c0e0405061206040b04020a0f08030406020610060c0f080c 79
    0x20603a541c0d44110a01d540c002030782c1c83d102c030304a0010b14200a40b110019103040c0d010080100703a020300f51a2848074805284001c42e00f18405800040004034603c0003826282150240510030070342007000f00e41107600020b800341a2600501044d00400410000c3d0400000c2d11580c4410a01c00344040e00d1201074620543c83c410303019042540d242010780340080c00c1d020f0340390845054000700700100489911002001d804407623040c0c400060402240400700c4160090032002035141c003000045c440c1413501508613605582c0550107a0350f25844042c001c2e80d032442011541d81c0304461960004a0041d01c02c40102140c01001c0e00f0200c54020641d5004d084a2603c0d40380c0c004101c0c00b441e5818a800c09104a59015030207440600e07510604405d22555623000034001808040080001000c540f1000109401441d550b041070b0300c516116050903460b0703002801400b00520842000a6546000310910800c56100d40c135039808509440c3c56160004070700401c251400718081001e07124050007000102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 317323687 1250 317322437 317322449
    0x51b0102150f0f06090403020a030c0c092d0c1e120603060213061407060b0a0308030f0912070f02010804020a08030f0408100b1008090c0307090207030806100531 71
    0x49080c43c01c80c81c04944220050a12130249881508000000e41c000030395180302a0142080d403149131080c80c1260194945400a080440c240038400103e1000d10b44481c1c01150b4140c002040c0303000c00c400780004c464550705d440001a031070780461806000c0326100f181150203103103000c1c2c103aa250ba51aa0042daa0541d00c2210b1080d40060011590380b0460340c032a020344402d00d802d10480a410703101c007520b40a0807901030b20660350303001e08496a580f480030881c000c6030b11240240e124134040c10241d241c40d008880a141d0303409080d00204152841604481205500c000c02c29000d00790b47c0c004644891005008a030407000000d0086510340e002c0000c0d002e00400320007030756038940c208407182d41010314245400c01d010b420168001d90036656000c880c01240d043c1c0c07a1044059840001917403034400c9900d001a09402140d1010600540b103400a20000d8001c0c1c5864002e41c40f04014800c0703010440308405c4c00150107101203496102000480c03600a401c03c0610200d88000e000a01d020044a80c40743d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 317324937 1250 317323687 317323711
    0x1a16022209200306060307090f1509140c030603030a08040614150123040501050703090e0403080609180c090c0c060f040501200301090213030f141009051b010215 71
    0x364082905036102c1c00d100b404250054031060500c240420313034443d0b031030080c107144a84032071800d01da85500b0781c40180040b56603100c402c0e034950f40316031740001800030341c4e13441c0c0b00d001070200040c40440005044174042c5030040c000f58980410030170200e0f100d120141084489540316108000040a5a0301007802031141c16007251800e1102400500450b04c03500307282c0030258140d8003880008407040c0a680481d1428207045076104560724046a903039410f40c00448040c4030100920007407541c80316100d845008140c41c40e403c0c5844003803030000480c10900300b00f41d041c3e0080a8620307450601c80d80e0181c00100300602d0320700f0986909480c40c01c0520443d55600b01d40030000400090107800d0003100c040c0b00380200504091340741c2d603010151030b01c814003401060640000302c4606201012030041c0080d130300004504600c0c4030610701a012141c00f103094030018130031104402c40028080c400c40c503d00d80d11600600140c542c48102800826003882c100341036005048c0d0844941a1012600d8450300c2e011010b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 317326187 1250 317324937 317324963
    0xa0509220504050c0a0503010c0e090c09060307030605040606090803030a09141509062a030613180c08010b030a060b060403060e1f1406091812041a16022209 69
    0x280889045d55030f00091203070b0306090003081000e400143c40400180184c40d41010307555002850202803141444898000c0c100008000000e43e00d50b04c55800c0c1c0e2800c803418041282c0e540b004072940401c80c087c00700c4640003040800c68000565021200341d40c8114841d01c00017107125141414180d1002000f55500702e51410010501e4060154540c400ca0701e500d82c15200d0a414094007201c04194000300a105001001c20300996841c010b9203903070012508288028182c01030f24001e0314800d001c084038400f11061012070341070818010190005800750050910107030b586c5401010f080c2200209800000404c400300108006000f10704040102c0001880364140440d524143c1850380890103401d14900840d4400700702c8002d04040d0005002c449a06091301c1e034804211000000b40700030034203481a903e01c0209200c882c005081215080345c8070200802d41da400f1482548a00e0b070080c0100007040d2070810052615000a50810b00383d5510307842c9444046e51480d0481c3c02981056419282c0050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 317327437 1250 317326187 317326189
    0x207031712130c030201050c0c040924090b0a02220806010501120615050a11060f07121104060c081303060b2704020105030a090b1611030a0509220504050c 68
    0x101e54200d440949003046125107600c8408041c02c0a0000904001e80000d102c240030310304014504078000c0042040124480c00e25180c50b498510400d035101d1086500d10360001d6040e5481143d0300340350454644101503403001401802507210300a589944280380083d800d0356145000345402a0110798024900d950503e80050074116440800340d84040c00e20ba428042409651604d02d118140c5080c099210b031480b2405841c1002c10380e039081c0441c0f2801d000c100c018130b0125081d034060803090305c408403080c0300700c410003040d18102c681041d00e102d4108410044144640340c40c1904601424150742440e007900e8000e44801119802901c1998407105141103030b143c804150116440b241011010b078108102c4643d0148000801c081e05015002c00020701c1c01c40313a07403c1801007a03404003002a1520b81b00c04881144448405003400040360412040d48040002044401758115a2101410070102c0c000b004503800f05980c01d18804410480070281c40a954003075070f400765100320080c00306551548 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 317328687 1250 317327437 317327467
    0xf010501080f03040b0d09080c06131709090411041116020109050103020313031808030a170601090303090b03040302011503050309151305040203180a0803010e091501060f02070317 79
    0x42d49404107600104002c01214204004031000e441e01d2010109840101d030422030114010944250f226000b11420480350711051110401d0440c40b61a41803d140c1045103001942d0145c640110703048517412b0041408958442c03010b0124407001000031405240c0c440e01020740b03030440040c00e003603524420044011903800007150340c06041d082c80d0441c154500718900c00503521640402800744420900142000d10140c01c035100640412400c60350f86010310080284a0004124054a40718499020520035845080c480b400c80b5096510700c02c40c1810a0008002e50340050300807800d541da144444074848603400b04160003036005070040c0d80c40e51403090a0005019a00341c020154003010044101c441403104040019550251030040c1c8943d107680e1050f99070441031f42012000d00c44c03003504070104a0120021410f882e00521881d42d1b9442c0d17803458036502e144a4088c2e0040c946008011f00c002e40c49684840300014151040790b031032070b5803a203425844013085905951403940c000746000381305500c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 317329937 1250 317328687 317328703
    0x1908070203070822030b070f12050f0408210c2703060c130b160c06020d02030a110118080310080309030a0204240801090303050717040605090307050f01050108 70
    0x5400910b1801d0389640d51140b29108801c82940f00c014955140c0c0f074a180700f0240e2502540d4003454061b814208070f00044c12003020840b01c000007803000f50882401c141c1da130007214000c0c40110703100c00560306c841e61040781503081035500400451403100c0c2c00303031103044218006004440e1611040d682f0803444010b030001c40564807021903d20545030640c9840d440c0000c4035039000c0400b606007912030944103400001d800c55070f40076003084c4c540492044040b40e8182c02d01134102d441081c10b40c0145641715000d9841e01c4910903034602503001408040e1410740a0350040100c0d41813440000f440c034008c46116000d038200b42e43d0030b481169000c020800c09108500c0910082c01c1140011400c00a10750000b03070761685540002401140c030340d800c00c2e4078148218180341044181001841203a915540d0050003030021900580019082001058003113004004910240c8040031408107181e036907485e104041c0101900f4140584001c2041d41c01082051003461103246021001203410351400d46424903210745 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 317331187 1250 317329937 317329951
    0x2220e2203080103080904290406060807020a020607021309060c0e0118230d0303020702040501050a1409090f1501030b16050403030e0a09060303121401140405090309061908 76
    0x149186540032a0b0801c2025045982c004a010fa841400102043c0a0710075182402d64110488030038100804500c40348009000069508002c100d0342d41104403241c100648120703001d80c02c00103151f0003500341100142001400a010045484c003a084210200c0d00c4451b41511455510248842010790201c0494081c1d1424a030941247c0a101c1803100f1548140c0b090400e0300100c41701c02003001350501c2418000c0c481c002c00b801c9410249007000b50107507000e880200c6c416458840007044500d0950306078003d6600c0012400607000441d0244041d4600c0901045854450804850b080480410040d40d604ca0140303c4982e0320351440c5400440c00c0005400d00074802c000c011030102035a0b00609030b40460750540f42050344c10101c0d001181c2e020070103400804406041407004014507400019440942c07901c0c00701006084ca0110703400701c030b10a080c003c0310000b43c0110500e6031945050f41100390081c1941c01234900d0301a2002c00070304294400104424001035513200b0b01149908050840c0d40164 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 317332437 1250 317331187 317331241
    0x15040b010207060c0c050405070801081204210218100306050105120a0b0417070b1e070f030207020612040605040507090c0f08071701060201061e0f060302220e 70
    0x849000042e444000c140600d03420000d03c1d1a903503091040c088607220050038060f00400150825040c0201008070034000c00040380304051050b1101d5515401301c0701211482c607030007203408025401038a1003001d070440580c1c1c410000142800400c200f40442405091020b0741c8483c1546940b510400303450050f0f018911134050040f1400041c80c0120752100c40326800f440f00103040d96985410700305d91114441096601030f000c00d02c5020801e800c504180070b1000c0f444a08607507038040107510380824045814a00080320745005001060081d005815442c0c03004010b60304091088003900e4040d44200d80603114240c44006010a1101c140301000160407a61002c0c0850075070340340302429902000c01c01408101054000400300345c802c016540d02d00c460400d01c49807039695480002c0c0600f009001e0103518100d00c3c2c2c03040301195403d400d4003007140c0a0309902ea04d02c1d451301e40190300942091502d9161185113494040d200c1c0c000d115000d002d0805803640c0300c25810100e800d051020880c40000309152 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 317333687 1250 317332437 317332451
    0x1003060b03011403070906140915010e060a0e060d02070b010e010308070816050d0801050f010207050112180c0303020609010f2d0b03101d070b1b03190201051504 71
    0xc08650440341518000c64034160103009420200e89003820651080502d140b4088021030340c0080000180483c5008071040c0d584c980b00c2601c13280c0346a5030380c0d5001c0c0c04640d01710350409903424680050601c80c907440c1014003c1d103080c4c501040d150740c40812161096070340090038104003c0c0300c0010a014000c02011031110350304513030360344100d4130400f540a00011001302d49080c0c28000840050440d503400800d8650042c1e1310500604a00428020030344200d0040e01c220019510004260044800507510307014181e650441ea58000c0c0061900801a682030039581c5003c21000c004a0008520a0f8003c10603890044100c030f0031140309880c40340d900e504090029400440c1180c5440d10182349000c1100b884220202c00350041a040e469290075020b90501c6146004d0650302c13880030201c004000048041220501c942c840ea0180640d4006110901004d81a54400e24406a0010b91282264904007031b520900c1641d0100010403001030b0345440410056026107030780030007141380641e0180102 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 317334937 1250 317333687 317333699
    0xf0c090314030c1915061d06041a01030e010605120d120c0509121e150603010b030a1e02150901180305100b0415090231031707120806100306 62
    0x4584c031840e900819101c801070007040c0600b1005d0504c400c10481c80400c1840c0c0d613020300030a840048101092411a4540025081d00b068001c2150b5a0728603143c10240701d00030030040d0001c1408845010096503580f03400300e599111004065807541d002001442140701401c0010400c5e413014821031382076801c0c104444d00d116001019659103450455000c0103311142d40e900b440c0801c0d01c0c401c15901040d40c01a1a15403801055607070f1403043d0340b446114250360703d0b0203141c05c0c1d07075a00c03010b69010391243c0c00d0b042c041200c2150843d400c04050310b0061001d60150002945c0800b640460346058100090610083d0380101141d004800c1d01d200e02e81080789962102134580c0004441c0940700ba40340c1040c10700030794483d44914481c0c0c2c140c10b05002643e8494010700000e4000a0003d40d0f850110500e40800b03405403640c00884181c4403114458040c2581da41030f41807401007109103510041402000000703104000102c3c0000f03010b6661982c1031410004010a100c142050750302410314000081c440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 317336187 1250 317334937 317334943
    0xc011b0306080709022d0d0b041107170c0a030503161b110102010b04090c090506010908030423031005072c12160f03021806030a150f0c090314030c 65
    0x80340c1c999000140c07501440100180b03c0c05404145080308401b21910484020021001e80220110300da4104040000035060000301e40420481e031818510a0090400086c0d84400c00400c0400020005092009200980b441c01e0f1000340100c0c017151010007000418210703120710034014086468000107940a10f0a42c1081d0200090301a18500c1085104e4a00d64001d40100544080141017002002081d040c0405402081c0c00303410002030519000c00e24961103020850b080ea158a00070718501031500805003000c8020a49204440016007094038180d5818045041d2100713105901103028a000340008000348024000213604002c030031100c40a4201b041e0b5500394500003501e211380703140c60300040b56150030301c0b00380e428121841018010561228002c00342c011244266022449041d01c0ca20f02d0120743c0c011540170b03805900444c64800805c80600c50102a85400d010000d0804030100c9200291041d8002c4e41001c50004107007013003000b5207018880d0314242c4000145050003211001241c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 317337437 1250 317336187 317336189
    0x50c0702040b0102071a040e0604020a1403040c0b07140d0f020c0f0d0b011706070e0d08070201121104140f03070e0a06080d090302010e040b13090f05030c011b03060807 74
    0x1000c0c0b580c503149112583d000300002c0700500302d44403008030816020851500b0940c0180030311031040e4111070114440c1d003480e00a48200c11101c1c0c030380d0030340245c2103038a144d49500003c0003600c1240200400064a0380d42c5001003040600841305a102c40d41c0b140b00ca1490014008154810045540f1011315070b544d000c11402c1d102001210a40214420000041c01c5040a00c00162100e895074000180000c07a407402402420140d0094644998403181e040c2d40358052541442e4011010150300e00000784410018281c0368030504000345a01207480c000421500d040d081d01c10301c6a4006014484c03101da445901c10141021265403031010091000300c1c1d01c030f00703030342c0704000090140b000800d000342c42a400000207070502c1800c680081c01030310070051200150340710036800300b0a54401400c2c142040d001d8154030050240c08a24181e00c034200070380082242400c01c2c2c4011b200c541d42c0c000010317010b10040400c45042000440c61104441e42110001c5540c2146410b042c40c04000f044107010110b4504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 317338687 1250 317337437 317337439
    0xb04150509160e060c15270a12030203060103020d0f0608150c0702010c020d0609050a0b0f1e09030c07030b01090b0a1503050c070b0403020604140c15090118060302120a050c0702 78
    0x140e245e2000d625010300d0301070114040445844d41c1c0041003044000c074400d507150300101e41307818218002d44061300c503100d583c0d186001c1c207241d42660201d0916802600210740050040c03400603e001c10700c1e000c071003c6404121150f442d0640b6004100729040e010000c056102c0030240021440d170510208105c200d1040700700080c18041201c1c45c013410f550f1010840d1403042e400000a1100118900d485620b5030143c880450b41c441890300410803050102c03640c070303120301c0d420508007140e100316100c100802c4100400ca42c1d00ea210403c02c0d0403076000e052040300c0007580305403d04105541030a04010a45071214405400f0714901c44040203000c0c42d403a94483c07404070a050008d1503842d44c0d884407403684100301000c0c12504048060008040d4005655441140078400300a85030485181542d124194159030035130003482d001d50125800302540060080e040141000c0001d045034102c0490160100c0c0d1001021941c08100d240c00741c05010070a580c01054000c00300000e04c0d01001800c0d83d03000741000a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 317339937 1250 317338687 317338699
    0x1050d090203030702060f04180504111509130e010e0a0f0b04080714031b06060d150626210a0507060b130b0109120203031c0b04150509160e 62
    0x180c09640303040c01103940c0e01d0b802622060391303400705140504c020380c894400d03812403810303011800c02400403030b1040e039010f282d001842d5030b13a90032202e0800103a22210070400c40884070401400f40d25603994800c141c0401040d407008100140030580da1400c40d0003c0b01c05000da40c000da960540001c0300c80d180c03150565400b40d0300c1c803aa610303641890751550150307482c0200351072004112031140c508000044d0410050340180105083d4988200a440d0401510300c6a00100759650b541d0001d0f01c1c0300f00c070301d0f14124982d8000402641d05c010745440030341901e0000c2001403074001202218101408141703000d40760420702080d00e010603000b80505209404404080041c0850480204452a0420142448010102d0900c04038410f14840101014200706022900d05000001c8a140003031440e62416002400b8604220b5642c044001000e0610204820702e65102403500055175140700f40d1062403031414104101c10304050a00030021001b5102c3e100d071449a014840388280e1040020080207020f40301 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 317341187 1250 317339937 317339951
    0xe01060f0321030e070608010510090803042304060603050906070807080f0a1508010f061403070303050c071212030c0809060c1b101a01090e0604150305150f01050a0501050d 76
    0x480090200c0b619a090385d0007000c0e000902240c2c030007100da06890045074524004a00043d017540c41940318031480c10660020712081085005051580d030390074402c03540c4018001403c4000404545464000301c011071342e104d00780710b1600340400ca260343c0012103081c40843d50500075400b40c030400f4020725120000c070224002842d1712036141c10240c1c480b42c41c0d0420000081e00c51200501800c20f060704125054a4868002040810000e020b00c1c00180034020707001d5a425502c080fa0950300030a102c51a51107144000139040010111602c4a18040c4c0e52001c1407004454000f01551503030300d8500104010902405280d103070100d00d0541100c00d00c41c18a030741c1c40c0a034a004509680b102d00c034011602418a075202c984c1c0960f0020310754000f41e50f41100c242111180113444440060050a40c1c2914140004200d030419900081c86443c410b111140085c1d41ca0b030b21240b420504103030500d01102c1c004103100d4220b44d43c0800038003505045402001183c100b500003000e0f40035041d10301d1603041d12468 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 317342437 1250 317341187 317341253
    0x10050915070818010810051c060605030712200141090406081f150f060507022119260714011404020f13050a0e01060f03 53
    0x20480781e410b0b82c0461042e89640b82d81e0007035040d50400403c0d03c1d000c102080006000c41700c02010341000ea460040095a00f0101c1d9241c1e011310190922084404955600c0041000c1e60104844001800710342907403441c0b40e00c185400b82201c0050106144915102c40f003101b9140c3c2c111100303c5d0801c3d040000341201c01800085010f11103007900340d100c00e81c0300c43c2d00f0402ca51513107100100955041501d0078000d01e03a4440c00c4655601c1c88403e04410f40c0381801c000501c03c11150404042001c0e001046035050341c4519020410080c59440341003ca01d0001c2c8417030450070b06181e50110200c100c0070079000503040140c0325031128160040a04000d0b1000810410880304035860485410501c4052070300650400020303260343c0c40305c041502d0b412103281c0680522041402220581100b6000000e066180c40c1c4c2400042d000c15068640e202043d03680a0307413808500e00c2030030f00c40d0304012000b2400f04201519182150700340d811400307610b9a0200c0900114000c000100c40302c0389244d640041030b4030381e61 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 317343687 1250 317342437 317342479
    0x207020a060f1403070c0b1b12100807090614300106090c0504060801090e190303020d0f0204230d1209030c03150b03011e0b21010f0605100509 63
    0x614503075070f181c1012080c0080290702803810b1390481e01c03504241e089030320391010000c001c8802c02c601d240c80c44c2007004448800402c410885822a03010351442400076250030f65a400d0500340d4210212140c7e80f040200442a003500c00ea5000c0c000a0b19425181c0030701351810080042e45c58264554110f10b041500340061095000310000c0504281c1001607020b003450042c0254828807644000810180c004a0000000d124003200705031114001c1404408440760300600d0300c0b0008080c0e0030315a09002d1010b0010180c05800f42d00c1030740352070040c6d4a1f0b0408491009601d05990740105055000100b47d03030641350f1120003d0b1042c0c110701d0385a02c1c0c9080640448a14007503800040110700210400070401c1078152415440121800c1d041c0844100c400c1414200e903070500316510900b030021040001e45607158003401204070098022a0182840451808041d80301c0012076041e80d03450076660b4001d22580b0815001c0c01d41260090300680c5200402045030084842c1c0ca0f104110091541c0448240a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 317344937 1250 317343687 317343707
    0xc02071415030108010507020d05040e06011b06020c010c020d0908151b0408012c061807050d03020c0307060c0f08250506090c0603010503030f0d09080c060a0c030207020a060f 77
    0xd8065a42d01c1d03841d00d00c024080d0600381c541130054414224800009030064094406917494125800820780d134243c01120034183d4a0703100c40c04083c1c804101d4010510a0008000400c0e01074004a2441042c040091402c86030030114410000800070030f00c942d02c4c005c144e02c1c903640c210001d543c0c61a103907000540d010408030300a84100080015001030711310010740019040c51890146060002d00c04d00304160380c002600d03808030b40b0b0f4109a00181104c051520090b4a558050f4101c0d0b440e00d4032400810031060001c0343c00d4000d42c0c00404908010b140400c0311502a181c80d2802100d00c520507968880e40c0c0b403807240000c0110303c012410700c070714030140c10003c2c56848036201000e4068542e420030b19201c14081d92811164001c0300c1d07412106040400c200c030f040345d00c051300541c94590f250004000d1078200c2c03000081503585075003c80002c030b42100040c1c6040006280178015a051001030b40003120300803000d007000d02d4014840a409659032841c0d0308122600c81c20009655003440314111040492 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 317346187 1250 317344937 317344969
    0x11091009020918041505010e0c07030309051c1808030a090510030b0a1211030c09070e0d050f0717070617040305090a0801020319090c0510050408010e1b040c020714 72
    0x145020401844005c817032903000c5112011080240d84d0321124804100e0304219000c1c40100000c00078400044e1207070340591001405601a0b5580500700400c00d01c900c83d881c0500c8000846942d2075038912180302c1c09440050080d900118a0a42007402c050b041007424071820340700300b070002001074480b03020345c1024045400081420410030b44031104170101c401c0041068850f980c5414503141d95080010f060f0070140c0c4002d00c100030b41d54544104468098004140c1d80c0c10403090b201240c0024010000450364010b41c00150600c5410944060451440741720f68580c42d5010b10400c102141e00190107108021403095886459922420152241d102e9100d01d280c220501c070301c000680c120190b0165004150f80020340a01120050112058965116010b0445425a1000c00580c03401c12070301d00c424400d90400301d050036542d981e106d0031508000c0800350380d80c003d04c0c20b2030a0045090340c00002180111007c010780b14017464001d6031a440c500401382042c4080003a0303145507403004061130030108 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 317347437 1250 317346187 317346229
    0x80a050c010e031c020c060a020d06090509030318060c0913020f03040615080c09060f01090314010204081c02030d0b030f1b04060605030c1204021f0c110910090209 72
    0xb072080610303070b41d0b0361106000b0080390400850040f0005070302e00131a03212540420040c08240c441003509002507200d2000290501d03615034000980403501d000c0e041c843d4100d078000d15181c1c507040c1d00c404114880588581b440f43c00400c100b240c081c1b05002a034103081c10a44401c40c1038000f002e0764800911890b20070800c0b401000c000c02082168640049480b41600800c04c1046a601d4118580e210030349540c140d030100310b120000d40542000c1c210140295014509040ea5540e030f42c9441001ca5001815040b96940000b020300121008100e40d049200e10f4007141020002840381c025102d02809010311503694850402c3d00107070750b04200d101114840a416214403001007145c0704c0e40e003040c0d90a040c2c0103a003040310000c2e805000c3c500f600e200d1b02c04668150b2070a0042c810346240f02400070802c0364811701680d9490380041650540c0b41c01c48065461b84a0304202c00c0c10945907154480358407e100d0441c290400004001540c5540200c0d80700d04000740e1075031b4003030f00003806003044c104448540722 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 317348687 1250 317347437 317347451
    0xb04020909070b030f13170318061311060d050c0d0b060a0f03050703060308031e0f06060f0d0f0911040b0d0c050f0a05040213150309050a110d05070b03180a0f080a050c01 75
    0x3100c7c0d0003c5019031509803540700802d001402068488100b20352003c0c03186107035031806000c80d01e00c8002c01c00301c0c00002c04071441c001c81c3c451030608840c01a2504403505d84086550b500940c0607214041001c50229185030602e000d41c540184848145065401015103640100c1e80c420700903085800a5030384405866100d1500315200f40b00f070010b00b1401c106401c0c040340480d61500c450360740c0300d0142c08042c22591610b092210003030b060b548072019005c5602e55509040c2c2546059104d2140c4003842100e4624100c0458003c00080e154502d42e158030825004111000107842852000202c5a044d40c118041d800010000341c050b180039480f05402c80d000081081407042003407407120070350320440f602c00c03280980309100b00e00722034880300018442d44c0070011120102f159080000325858004101070300e908500d0ba03c3c80c1c1094081d41c04401f0710300010080c4460100748030000c01100320280024600b40155486410a180e044d4001a220310300002c0d000924611900845512000d200028030080c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 317349937 1250 317348687 317348723
    0x1090606090c030606090806010308030c04080304060c020a05031b04110403150228020a080f0d2f12010512030c070e1515180613030b04020909070b030f13 68
    0x380002d28110000245005404284280503d54001c15035000000912542c4e0035562440c0c415400a440d0850001040c40001a8403030304000401c054640c0307039540300300190644180490b940068000c02d00c65044000346494281c0c1c136159441d0500780854011414044a9050551038840ea07013000e00094071b464291004000c0340e0300107008911017001241ea10521208050341c040481004c2680140c10009403200890028400fa00301e100444c08211b00c1c000c4080108400c444030001003401105400c04171100300e0007503c0ba1600c00203007454582c0c0c0380c203030084400d45240398140200b9124000b5005501041e4000b0025540ca0384540e804076862140c590500d0541104204e4042c015023907803400c5c400c124108101c4500c0c6e07030000c546016013031604040318001e0340380090300e039183c00050601403800f0444206805400450080100b0f043c1c90915006114405d85e008210280580c08441c08118a802810850b54002070000303603e0391544844280c0e040d65048581c0203804d005106202e0004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 317351187 1250 317349937 317349941
    0x5030a03030e0601051507111915170705120903040519081209130902030a050715080c07020603010b0d090215190201060f0501121409070f061b02120109060609 70
    0x2c0e4611040c1203c810780c0ea00d400304402c40f50540660000c00c0020710081d800217030100b442d95465840100079140e541509a42c2c0700015900798411540100080816039180d03410412101032000f4420f201c8410307180058001d40a40b25030824400d00c2001c0400049401000b482a54040c004c010501d00c2c10034070b814141c100354140c5000701680344c051848051000721000003150202d207c0a403a076540d100f1980740c47c1c4000c040c0c0c2081030380c05001d012201070000e041807140b1006490120344058011840305001815aa801020316290034004c00c00340d009a038803102036074116054040030f81d60781d112042400c00070709100c0030025002800400300380d80d50000c90024010541c5410703515040151000341c220b082e114503203e103400c5408114002e00040d40b00b6500302c500010790007004252450be400310052486401c48140250390003144d01849a6111068010000c0800e860300e030380703100050402c4990340321414400900c40e844071050460400000c0d00204c41f1650000001c01400b65603248d0500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 317352437 1250 317351187 317351201
    0x10606050c0d0807090b0c0c031218010c051e120a08010e0a1e020d1d07050a05010206010f091824051803040e1503060709060315080a030c0c05030a0303 67
    0x40501030440340c8030702c403449403803954407415076960f4180308540350140c40031155011070f0860405008803900000161020409029a2840308400c41e40d175440340c85003212004150300155040201c117613088008142c0025015034034410759100140050082c401e203510b08001108854000341c3e01258200c100764218031524100c924100228041742d0350700e40100200c1d00040b1004110019a000c0e009450a030f9601810f030f040c201035070005080c0416000c0d124012036130591080d5950051350b040c4100c0c101610514000e02c0280003d060b5541030056544410449008000a0341d80d28400080003211140c03111220383d41000d508028000c05001d04070700205107030744010320345040101150410740e20076007040b480c1c1d40b80d034091420702d810442801109038002e481e080c8a03c2541c400300713007039035010f022481c040c0708a0749560514a180280260549001c4204560124901d140410580b600031906000503549860041005a070a20f00701d0b660440c036800a5030144260400c2804254042c0e010340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 317353687 1250 317352437 317352457
    0x3140d090501030509100c210e2b0e01140403050607081b0702010e0f040507081506030709050f0111100f15080703031d100f08090a0803070c080c01060605 68
    0x150321544030801503041d41e0040c1d48080c001d070302c11040c2c0400e6007107a030f1060020071803610b4000e146100709980700e040d4061540039a5120765590000d10a413880030020070700c1d0700070440c3d4890180c003a800d84030f0213104a0055000144181c0000381c013080d80c40784804103044810701c14001e4459499081255944c14205d440001040703c22001c1003810070034880380d07590b81d041c3c100380c00d203000c809500454101c205c0d0100d950b00b051801c6044010f0369114040d181c4a40c01942d6800150320b06808580040d8001c1c0034003170b0003080200240581540d0111098007640c1c026140c3c909050507040040341c2400184842d0003140c0079210703031240c00c503440b60003a4200b00e8001d4818001400c2030142c82801c0b04951091003140e6009442c00c100283c042e000d2407003903003455580340846c1c50702d140c00319104400740c80505000900401e4207840c8150400c00ca25001021130000303180302c2199a40f00e00c514440034000000b032026a00c071807820440320030115030259090030000d02c0f10540c0c600f800b07081074100f0102c030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 317354937 1250 317353687 317353697
    0x50603041e06020c0d09030503032a07050d08010b0c06060603130204090b060112110307031e0c080601080f0f06010e03030c01150501110613020d0f050105071d0406032a03140d 77
    0x420141d01c111b00e00c1083c3c0f508070000d507145455602100f00203503403100c45118010503140500da810481032000e08055405140030381000540300038000e14088050b00250281c0c10300f404203c0c03c003400025940d034000820b68a80d0342d42d403107004a0090140742c10b200294041d040154010800690b14036140c002d45083e00c40c0c07520003001218030410350300e084080904031b040a1002801c90b5205e5044050000e110196a0044126071040c18065034880c0e00301502180750b1606000c2c403564080384159011810540400c51420200c17a40c61450b000903013080d04111220040d804c903640c050080360303100700740c8000070400c55140c001c3d8105070b202680705090101d403000501c940e00000c0400c410b84100410310403035040d00102c2c1d080000010400c0700c1a03e1101c050211800014005d2090310300039482a12503841d40d8442070021412071142942650240f41465002c100080500000f60700c40c000203203902c012030408900550220b40d107984060f10202c1003910405003004045440041144245e880e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 317356187 1250 317354937 317354953
    0xb07030c140708060c0703050d110705071403100e03220f0305070801180f031b08040b09040b01030c09032a030308040507150807030f0615170f06010504050603041e06020c 75
    0xd172031a00e000303564000e400b00c0c004100e224902e0f080e580c000d00001704601380d540e0410591303840d42440d000c1e0b02d0f007108030f014458140040d42e0780f40400442910b101c4016080c0041d41018400c2a103034010500416194104084600c461a4208c50310002900e00207000f109425600d00b0001da643e145407084500365441d0224032211800c01c1a558411340d60000c1840380c0c04c1006680484041546032108a000d0044100800003e06100c008000420001c0c01c82c5071100c0f400c004020444020704103640c18103140800742106560000c0840086a4000301000840b00844100074a10303236041d400090440d0900f1008000c05800c1402c0d54025030045048a034101d8803075104c002914031041224021480304400103200512903040003101d142983c8010840c02d036611100c9038410446207808011601e1080504c24a41c41c005d40c550b448000c0c09040506400e0490020b000392049000301802100000001401d00408003911640c10068000c1000c103d5100e050410013900028100f403013078011502 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 317357437 1250 317356187 317356201
    0x21203070308010e0402030312040f0b0709080c0301090b010b0a0207050603010303021e07080307150207050a0b0129070204020f12010f090506030f121305090a0e0c0a0f0b07030c14070806 82
    0x4d6413440b440c3d010b001140380a0042140844225000b08106c41144070f44481d1000159444840c3c0d0080c051529518004e42c00c000855080c140b0b032026040c041d0389006446c034080740b00902d0740307070444294016041e0341d65145c3d0400c0781406070540041d500500300200000815500148501405111110802c808156204082d072038080c24408c07101c0c150310030700c0001c0c040750020509448500c0b00e2000145040007507519070b4204060341c001034032114070100040064051807400d0000100e07c2c0b030507000b60040b4410105859001303001010f4001e60b80030496183c40c10418088554000d80c400c8003141e1f9607902c035860040910a8001c0d02000707818000882d04509000030041c500c4400380700a0140301040084000c07564000b00b041c031180c0c07800c00c100080d1030748503201d869001d40340304040407890002c64103030946013011400010b8050162131004200700f007030483c0c0080a46030404401a562407007410121002c2c602603c0107450842c100080350015000003030a682210308032801d5034119a10a9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 317358687 1250 317357437 317357459
    0x31b0c01051e030c04030210200d17040606030c080a020102072705040c050a080109122a05010f05010618050f1309170f0a030e070f03060b04060302120307030801 71
    0x1003803075070741048a80c01200581c14088082d651184d4540c076501d003010354a0300040c80f01c03260180722070041182088901010a010408140380c0c112082c010104041c02000007003103511110784008105da500c2000c00d00b0003842e60044001150850030708002280c0b0f0705c0d0100e4881107a03c01c22800343c450000300180303644410380c403c60790302007504d070300422081005088406030900500c221000b081203e4080b515544000002d0b01070b100300710002501c03011034580030314030484400c6d6110a020071701d06101200541644c1d0080460030502e80e8091002d820300c4c00c280582003072160154145c3c01d003c00421501e5000103d40c202c2e0014100014102ea80c2d4000e009045d2148203920380c00034102140c0a808810780c2c0c114a44851042102c5040952104d41c0584540c00202d502c1c0200400080c43c116001e902d40a0103000c0360381c41c409003007c24a49a40419601c1540c40020300762512400c00500c0340ea02e0341d001c1401903030003034407040503148450b5005441c1e500140c0110003081a010001c00c0990800e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 317359937 1250 317358687 317358697
    0x9150403080c030414070603060603060906050d03050c07081b0301050f0702030d020a02030408070b2709131a0709080d0c020a03032f0c100e01120b12031b0c0105 71
    0x1515070030802d40300e000c11140181d100130015034007144804010a00b80720300704680f02c02010300e070354001852030402c1c400609450090340a03082c01800d03d0b000b031103541d495a80c0032070900c0d031600380a030343d1f02e00c03007030500b401c0c10103c0d80802136a0148048083e10007640c80086044c1d143c04030020801e595505d41046008035090b210080140d0090207102500311444c0e005240e40d4034940100e0342442d544039025407a10b81c45401003020f411000c17910401c460305084490f0080540782c400c0305040305900001c51624003004000041f00304c0f082c4440801c0c05444902152800a048102510361402900c00752070640c844c41000050300c039600014600e01c0c81610411b1074203030300134540c0c40920b156407000c850621071442c07044014014498038070380d039944c00d885191100c0324010161581b09481d008010010915201110601811080b001d01507070740b01051249217110a0301c0010f0b4500c59101042c203003400f500c0704041500c40042e00320104840050241803008601007211441c500d41c00045805000b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 317361187 1250 317359937 317359943
    0x30f0f100b0903010e030c010207210e010e0406030b09011a0414010302120c0d03090e060f280b0a081005100804080d0b0d080c060105010306140d05030c03070b091504 73
    0x5440c014000d4103000d800824140e8001070020801c4a2440c103118216804011601000d81d40024142c04200c0f61181e5451481c02e00302c0d20110b07040442d0405040b00e00e00d011030a04100c588005112035070703a55070090010356000b83c0c0c0f43c0750034a0015030040c0286601c00241c850500f0030805248203241074003469400706006072003400d4591855083c030140100f94803d0107001d000c2c0a031145144e8590b44070031800c050095540c81d811501d4200c8561304c0500240003640541071044071640d25072203106246004034030451054000c0410306001c51a100c44030341090b041c1150007e07610326501e034002540ea000b10001c000c5403c00981d01e10410000c096510003070004541c0d14030004003c500c01c8005491075850145020401230030060018905103542001226020320100d8418400541007140314050b0074282000c020150401108114103001441c0d418882d200d2035000c80308110301031046d0750090301840c04494070f0f2041e038903001c003d03500c04542407800741c1704041e80c0ca00443c40c4400b2170707402150 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 317362437 1250 317361187 317361211
    0x306090c0801150302060c150c07120302040501090501051c06180612050a0b040f08070b1501030e0c04091707060c1202091c05032208010b03120315010c0b010308030f0f 74
    0x4c80d41d800e015403900b0480703070419640105080d070b5034821f4440c009584212007014295503203460a18004d44840301c646245404c142c810300c030512140e60009010303000e50301d003400c0103519600c2d001a40d8241e00f0701902c1c180c1440303080c520005202c900721040f144142080030424450309445a01240ca047c0800c180a00141d1100241e0000300d00902d01c450b0704a800b5808403e1070001c541c075140e4059000d540e0803156a031613a401c00c281548000c496100c0c007002480c0078401e80d00c8460b19684e43e000d5011800d4030031a91800707202c04003c81104010329968510320322a403510400d09040c2c00030500c0030f25030404900d02117000c51044070303d80700f01c0b640a42c0c0204811401c03014040d6050216210403002c84483c4230801000002c0c00102c1d42850004060241c00c82c01c441c10028070b40c0c255014484034034040c0d8001d0945c182c41184d00c80030340764040c01c0d20a4180b290500c3c4401260b44103400c01005c0c01813400b6074008024802c600005511801c8e011a00c01c01c40d032160000a0240c407000c44060785001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 317363687 1250 317362437 317362439
    0x103020903070b09131802011e080106031d1006030203061b0301091104050316050114070b01231302090102121213020f0a0e0402030f07080607270306090c080115 71
    0x822400c0280006003005403445c1400c0d004683c4240448001740c4a040705444810341c070318210b42e403003c280b40c4d041c120a03103500000f00410a000e0030303006041c0507580605441c2d0101b0401c010105082258580100c021903a010204045030801014907000c180d0081c010311001940c070b807080000e1103d8000c4200e403600d01c0c503842c0101c0440240150119010220030410000070156020020002e10088090309421654030345030024000f41000880004c069205000410200d012907418a04607900d0f00c2d002100300203581c201c100b040c0c69048c01e8903403107044d201c04000a20195800342c60800c0003030b02107404680c040d4181107601d0103a0360707081d0441d205d0f48000452200c60180c3d04c0f41c2842c4007516841740701c20b6450000360030201c0b44e0048560a5640310420040d464204a01c4411414800140c50f0960520b00341c152903a400600f41000c2c06044a0b81d240ca40350481c8412189001260900d01c102d83c0324030303009010700b2854100b602e400200c4000841c5802040c49020507540107009000c3c41d07a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 317364937 1250 317363687 317363699
    0xb0702031507120209033a0306210f140d02010507080408091009210c050f0303190908060c0d050721091a07201b0d02041e1505010302090307 62
    0x181d0b1002c170026816000c0d1b90b07008165582a031030303446a15456844021440c0f0036000c1d0640d0203081e07001900c0201420030004001c00b8800c1e21014450840f41c803003d13000e5080030b0402e24440d80c001c140040c02c1c0c011a481d0389002c00c60218402007078001e146e00038045030b00c4541e0115801d01c0151400307030480a0422501601c0e141448881c07030b4140c07190030107500b0315544004503456200442c20032801c400000741c00e241041405234120014140842c1c8240e02c100d040d50101e5500c0c000d503001b2200b825401e1030f132418102d000b410244001c210000c22100e00346032400e225659a00f2030020402051b043c00c0115030b4941c01784d00c0703041c0b940a051001c064008651000440070385414801034079008504100c90000b5182d4644d418850341168440d592074017654401c101d0003000c61036001203180c1280184d1700d00c1d01c001100b50b00e80220103ca90603071014980c00041d005180d01e0011510b80c030000c200780c580030b880036004800e17022000710b0701c0c040480e0f450300190203900c151001a9803640001e0000d01c11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 317366187 1250 317364937 317364941
    0x1104050a0e010911010e09040b181203040c21050d0302031b07060e06070908030a050304060f0c030b0306090109080d15050a03030513120305120a0b03070b070203150712 74
    0x1004140d4a03020030041e403403844490031540c031030109680c1c615600c0d031014001e51b0031080e0304210103410b03654000315240c151514012440041c04000c42801c2c0345908410a400c2000788604801a054482d9502c1c182807410f071041c003110340b00e80c01d410102540f24442c90300605080c04d440b217070044c002e0074105007220300450003503200402c000c0c01c030034000e00c0141c150704440300900480351280500050f10305d000440e0610388440100310b1420070040007818014054084181c442d104001d04006072a522640303024409811003a1130764400a10340091502c5c2250b03da00101c41c1070509505940040e2914000369082e85c5110101512000c2d081010b42d001d00e005034003148c208021a120081a02d0302e9000184a04445600590020340d021940b80c03113030030b100e4113000010442000b20b00c15011241d50064401c0c006c8080e44481d14440c1c03030005915041e160441015190014140c48440361a15406902904040c03400d078001e00c21411343c0e2805c00c0c1380c0004c1500032905a2074202c01441d07c4100000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 317367437 1250 317366187 317366191
    0x30b09040b040c0b0a0c06050a0213030305090103020409020708070201030b1903020d0f0b090d0305090304150c0f06020c1f23040c08071401020d0804030f0e190305030304120c110405 80
    0x7a82c1c1103032120009924940ca8045c054000171940ca0314001ca8503418007905888020b00200003061040101e898501d02010040040300e80c1803d0280e210020000142c2c001d00990340300c0b1403414000950b10040181c0c01c8014050326100740c07070030001d0f4880d58090014510f000000c404204840e05e10500c054a0080e17000c40361780340b08103c00b205003203c070b41d96018103060541d110f84059102001a02c01303281c040c041d890340022840c0c011400c0078501301e032191804020b031741e44601b03110488a402d42484401c045c0c0b10242c40c1c20040540d984c5100e00030503a0b031400703101001e070f140c00c0e8101120050034086002e080c1d80c1c5d0300186002400d60310094100c141080015004503a910310300c6800180145040c004c040003442920304820581031100006400d010281208408005004c02040000b80c0c12104c900860105458a000042040c1c2e01040780d00d02034110030420080078040006c00c0242c000003c0d07110310312580d105d002400303961310141c07904014000005c1c11141c10300048000c9007000d5210325 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 317368687 1250 317367437 317367443
    0x10b061606110c0f071a0f0313061103011e0807141201050a090b0a022704020f120103020a0506040f090c1e18060e011b030203040e01140f01030b09040b04 68
    0x180482c1510001406500c580c3d481c0304581c100030142e81504100341301030402001c0e456030841c00e43d801c1388503161443c410014003078a0b654000c008180c0908482440c22038071a40900100078201000280f1500d540091043c85211407150039264a00ca0052181c001183c00c143c0080210f03904080c50583d21003103860103d5001903c80410040e201024041c07070b8083c0485100010b0b0302c5000303007050040c00000602c81190203004000440380c01c40e46802c0311503170111124000d60203510030400030f00648030360388504680e1780c0c0114001450507000401c0c141200e01c21540d42003080e9403602807000a0065124125610100c500c0400404c0340039040100d00c11003030f1500d149640318503080d400784292001f45010010302080e01040300002c424030007102400d1641004980f05a110300020140c1c0c15a20680520300d42031a030142c02c05008100350380250000002e5610a580c48080c003501410411080e0303441039201807116007155001e4400c0c03900380400902070000550307868a414074035030070180c811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 317369937 1250 317368687 317368691
    0x30203100f09080304081e16060c090f03060b2701060c0f0b0705120a0501230406030602040b03071701061407020a170309040e240a0b0301050114030f010b061606 71
    0x5030b4002030501d00118070582c4503c295a1b2a00c039807940d07421081c041c215441d101004d0401c60344468a4003d071070b248205174045c0d0702007915606d9a108880101959201c5c3c58080c0d00a034001c0308006080c0c0040e8119001500c0c1c00c089155154660104d540300c0154072442e1034080070043c0246071140d151a02c25a0003800c0a13a0304031020ba40f482c27414841111220001a408210340c2103101c0c21511440d044119800c01344425410110920060740c0401684102001c500031001c1300c85e200c5801020003141c201400719100c550704c3e100400c441e40115502d9000820b11400000207030140e0f0310090599100e84e80749002444040000081170f84461010b07a40891000400654030030340c08008900b21003800301440c2c80d10442c07000d02060b00c560b0803d00380d0603000041c0c41e800704030f110075000303010689843c8201202d0300c039100e0b410000c2c1003180003180c041d420b140001c62905005111441425070a804440180c0b0480003840d00300c0d0640071015034000402c010f9100384ad0883d100504651b8010540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 317371187 1250 317369937 317369951
    0x219060903230709050f070c080306040c110303040c1703040303050901050702060903251d06040914060702060f0c03060906100306090f0e06060904110120060702150c04030203100f 79
    0x2d0680340211542c04110115183d90130410080041490983c02c99460708103450b400005590b510800e01001300300500a643d100c012400300b0784945d24020348241c1030030030780b0740e00d080030b04101d40700b0b91940c0a500c0207042214010301d1036000000807a421250560f4490341400d44000044030554080300b0f059038000d00521100c00c807036400740070748218010811503c0c103925010a2007001304008540c0407640301070f1403440c010120745002410543c80302e01103900054a06062515089503220301ca850720f464071410040081e910f4000031164080c01d04690140103582d02c44201507414807040315020b401038104070101e0f1a600381301a0b1800b406144d82000310343c0c161643e43d2402110301c450200780c58542c0300c08600c4010407080c00a41e030841000c0e103452846180a403680900c2d14203261000b0b04001402e0383c0f9000c2c06201c0411041140050f41c195401410a050700a65490080340c01680c40b42c000700200ea8000b40d0a400c4504881d4050098405006107085030401080d4003900c9010003030716884 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 317372437 1250 317371187 317371253
    0x1d100b0f09220c02010e072304020d11030408070203060c190807020f1203011701020a142a0115050103180312020d150303020d03151502070302030f0a0219060903 71
    0x4050120b0f9907a400005e080c90400041460f01c0c0c5c00ea0301003041c0480848c0c0e0340d0302d90400c601003110301e40c0054038090b0b40c0791074241004000b0107504800c0a14070201000388800c00940300018014140202c04441403034031a003029010034410030060300b080321801742650140e80e01840342c82e0751024640c010b8464001241c90024145006114036100841c0004010320031031500445076921204207800071401d2500b1450f015020b0300ba1148a6551810046045040400c02e48480d07801c5034920300000c0400405408501d020b41905031210102c000000e2001c6590352091080041d06001c200c81c03100c2440154400b901d000106c000c02c1126180c007008855210051401450f4500082040e040c001c589076041c001c5c1002180f000d0981090305200840c14800080441030742960f09003292565030220180c001e91400074103500003905405091704104034003201003040048280280c2d00c0841900000c03081070100034803800742e5000304200780010b00c041480400790602003d004070105006442d580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 317373687 1250 317372437 317372441
    0xb03061018090e060a05010b030c0304050109021807110f0c3d120507020a0201110102130e0114090405121308070f170109020f0f01091d100b0f0922 65
    0x604200c100548418551074010f604000e5190b00400c80d80702004294141803080c4030030301c0090040f480091020000c102444429803005016075402040e034405206280a9103618881c100c0c3c4c1c200105113401502291803201107031040b68150701c000906007040700001008601c0c441e0000b038440c01304220071407107000c0c10606403c10340c1c04541400c0111802c818000144078240828130540f405081500303000116800041e15190181d0900b0714880342c003c1c4800b0f00d4028010802205444d58640800140b080004400f9034180c1391180360500302c8181810522681e58802d076401081c5034480c1e0065640c900e100c802403d031405411600210300be941d000c03440c1c5025070540106d4000460414104071a03906034080001091491000f0b02c00c508580e000600c900034000d41e0030f4011000b040c046405603105030140c50141c921060384102c08240703070b486d41800d02e07021148001d280806d0303940822a807203a0302c26601c200c0030ba03000b09031a109002003404541d40b01c00000000c82c5c4410002200440c01d01c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 317374937 1250 317373687 317373689
    0xc0e040204031103120a0206041502070b0a060810023912030609010501090302063a02070b01060c0b130206070204050411040528050606131e050402040b03061018 71
    0x10350341000c1040083c0082508003594510f04070080407080186a40d441c0e000f1806980c856008210002c28144812700c0e10081d1144074402000d0303600810820400e0741480d40800709a5894400315509886a1030041c8202d1007040207405401e8042c1b044280c3d9010030300c01d00b844001e00d81c0b1107803401404140c0386900d061030840b1003940f00c0c8004020081d1600300303951004d004060074079191780c4861664010980c14420f0300702a802400ba00d410480e00c411410703040ca010340d1042e00700c844021305207407030359002500107480448041c540c0c000000f5403e4441c048601c800f82d04910000190745030408a09003c030850b6008a801c6882030001c84003582d558803420b881036000705440c40980404508203c1220381c0201180e0019400c1c41c1114001c1040105041980030311100005403030701c40000041d054020041c816020070801100803641c010b0309000d585e100314611120b044c0203601c500400c41a03004034024180b04260900005040740341120020460b5406820050311410620210007151503007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 317376187 1250 317374937 317374943
    0x3190509060406050606120103060203130b0903041a0a0801120609060c091e06020c130b06040b070b0f090a0602070206070c080106060e0301020c0d0309020102030d0c020c040e0109150c0e04020403 86
    0xc810100b109004040c09540d034804001c8654601e820180070680c040707050103000203000c803903011000031a21142010a040031903000404000b03035181c487e074616544c0d40907005183d8040c100c3d40b646c3c00005a010103070740081440c0c0c2c82e114610782c03c10301552441e0100940540300640c81e407020401049107440360300c040000320380d118030000e4200a5a1790300503800c040602c035280328016007080600d6000c40c0307a058a04080b43c01c6400b526144213500041c24401543d0b40d41304200060008588207008003d12950b84540e01d2041c040d6551212281101811190100070b41c02148a80c00004c64a500130192244000c145504000c1c0d0303920340c1413496286030004107503607550700001d01445801901c00e40102e1011802545404602c00c3c106856203000a245818151181450001c681c001c2c0281d03040505141400c005024149000941e5440441400c1f402075181c2641980743c2901801403028441d00320400365100440309d0300d000018000d00c075185017005a040c00c100340c0b81c1c3e1540001c00c02180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 317377437 1250 317376187 317376193
    0x6020a0509120604260409050108010905160e01030206130e07030603060b04060320030102072907080103030f11011509021806130303140f12090d0906050f03190509 72
    0x10030795007800720451180060309002d0780018100000a081c0c8190041c07110210341494070043c8000900350114012a000310740d007681014004541c40d0415030015401034024000c0301d400520015007080d03504003074004d084400020800500140c1010001040920002c08a00c810741d6a241007686141d40143c1d0300c0b0b00080c0e00d5140400c12700c0045c2c01091080742d0120f0b000c0146928540e0380040780c1b100d1864941031f079484d440c080c902540c5c0030340c16120341540001d60011449d400258402140c80f5580c8494450748000010610b0710344110241d81c1a031b41d05403504484e500d10100140c0f14185040c2e110307a415900c41c00d6000d040800049164020a4580d00158131482403000c58517908003020b44490191f5000c0c403240041c1e01c803e44015003103030303014140180d1241011014425a118a9022030a4440c002500710868001107084510034440e0009a6500e80c5d1403260468201074144030301c1000a0082c030039460180d81ca04001c0d90060722480000c4000030041500d0030a070780d000c40c1c1146660b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 317378687 1250 317377437 317377447
    0x1b0b0609091605010e0a0e07050c070b0306091f0308041e0e0c0901080417041205060604090203030a140903010c02010b0111190825060b010e030a0c140102030706020a05 74
    0x109040540039000704059000d010101c5000802d021462100c1c42020304101500c507041407903494a80c0c50501030461100840ca10340340030a00580590310103c000c0d82240315962001440800034400e4a028581c010103020302511031800580301244080f262401000040c10004000756010380280020041d03100039010800300c2c0c00c000c940410903584a031050700d124108101c90440721104840c00700c0f20034213180340036807280d00706002030004501e21030311030030340003d40851500880d03000c4048003446002111520754504e400c2c0021b03200064402909030f4402d0022000c2903001722407980b104c200c56003081e070130141890700007070a440b0f24031650000741d0d5465a2038082c3d56030101c400501185548010204000c1d6458410100d1050890141c440a03012540b1440c0c0b00580035048182e03101c20b2141e01a89060b81001e5008094102031103000c2060f8400014550502003091140780f84c010750b079640c446103003500902c01036480820b0715046000809c00000001c11520241c50508016a1415296 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 317379937 1250 317378687 317378689
    0x302221406030f010608030909071404030503130b09010c020402090103090b040b04060b0604031a10030206070302060a0605180c0a02010e0601031a06090c1c0b03010c020312010e090d0309031b0b06 86
    0x3c030301c102200c81c401da41448000d1207070010000032070782d182401b070706c0f40e400654070400100c07141c41044040c7d0060a20015001043c454000054120f100940c401d4003d810380c0c034076200403144180010140401c8502d40040054941a405801d1f5501c2c10704000ca021051503540000034001101c0807943d0030a281c2c14001844050300c1038000da4241030702c007107191900755101e018804c80100c0c0303c45840b4074184001038940c50030f034807540010750780542682c3e00c0300400e240c042d498a004507510b1452038030b0482e00195611700405030641c1d40f1403056622506407a515112001c1c0d611005261080d50349402c0c4d00130365044100581c3e4020340c040c101200301c4c0d03011200c21100880303010b8041881254542d082c024056280c1040311150f01c000c00030040300040f60b00c8041c0c040c02480c0d8095504d546000d00600e18250048014018040c007083c0c03042c03c3c1ea80310600c80303415003400e46241ea42a070016044001d003c5c002e503c42e190580c004d042150501480080400f414415010b0484850303004106006807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 317381187 1250 317379937 317379943
    0x30c11060715060e011a030a110c010912020303150906030c30010504020906190f0801021e21130804090902100e15090d080a0305010510080106020304030222140603 72
    0x1a205507103082685525103000342c190252240221006c407403000003c03a800c0e00780399001c0480380c2c90466005440710100240f01d402048005001d440940214002e55601031001c0301307c03031280900c2e0418030a0003042c481031042d0860b0041080b6010307c5090b0758512243e0f41c1c0003d00f01060a200002000041e40e807140e002a2500b50b03a014a00d0f0b0f0421041c0b000580d81c001256a0160f015a107131a88903130380b600a03c200403200c0c1e01541e0701041c00b03080460800010340041a0100340300c00703011840c415006200ca550312802400c82d550251148040740d0091720f0300340490300208005004034440103a034076403400940c0943c1c4103c4500d5501e044140850a00494412444916052443e0700b090740d030012401000b00640440e000e00c00c0080c02070a00d03502e04603030484d0b00e0f810000440d100e41203020081c000b000d00380035840c030400c5290406c10741c440c45100b103241070750100d0f4041d5040500d0342c0e09001c170300004a003605040c00381c0310401d8079034107003244280e42002580300403461903400c0190034182 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 317382437 1250 317381187 317381189
    0x100207170403080403110409060507110705010c021809030c010c091a0c0715020a1b03031b03053f04060501080c0303040b0307052b05010e070c030c1106071506 70
    0x501800030321003000803500103c156030440742c009060080b010300c1500090020310401c14000c5c10103103441c0030700904d15403001d03a61038640d642d14100c8003000e41f02c00054a2940010b10020342c003403000e075804c4007104001d148081d0091007010440b820311130b03200200c500751816481d425000840b80441000580074400741c0402d1b4170001e0004d145090b4801e0402c0d500ca8010340a840391140c00581c1c0c0da91a28420481c5916541e0001d8081020302145643e04641780301d01d101c181c0c005004020749101c84100c25030018000e49c3d154817040d1815166100040381151110f2100204100c400c00d40000300c00b00048a140d9260b0350302100c9120318251410808444040c8c010700402c1d40503044a40e001e40b00017040702c058a801081c41d40c0c0342c0c1e83e8000d00311a00c3c810011160703007800d12500e41c022940d00c1040f1300503864031402070921043e82c90b03000c4480c00341c0040f210040020aa158450086070045c0386254403075000e0480390101c901c035400841c440c0da0041008034ad80380c507903102c007200740c04803441258 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 317383687 1250 317382437 317382473
    0x60d06122004021c0e07091505120105060915240a12020a0c0818030f03030106020c09100b07030909020a020708011139060115030509071a0c0c03100207 67
    0x508018040d110144904420074024003841d82d03880083c0503d6004000200043c501d484050000c856028208c00d01135000707100d00ca0041055038440040140c060054a00c10701003c1d103034074038568642d514601801d2810051039007040700020840c01e0024030a002020443c804c92440b9524089000300030080003120200c2540c5074414032040c0c90455001070982e4032142c006204036160414210343e8059030400c18402c903403500c2140c02d101108440400a98103c451503000d4901a01580c0103100c2e243c1000c454066034000381c48001d2106c1d00c164000b500340356000c1c0c0f40c1800001e80320385012040340d222000c0100540d2200d8410002100709000b69060303100511000da041014503007640d40365500c0c55844141c28900200d40c81800195031f1044c50706c2181100c121607455942d1150091250000d440e0000000c1c100000a80d18440001d1540c08a8841d0b61400e4509021030401103260307084003a40c01c1c1d0b00d000701c61381f00341159420071059040c440000070040e528a0507162032812460250000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 317384937 1250 317383687 317383691
    0x50306070e1011010f0c021f020f070201030905010b0a0807150c1a0c0d09030503062b0305031017030d051b0706020906071e0c06090311060d06122004 66
    0x20106466503a0b100c90180010700344070100059002000e80034010707400da0240c0607450041d81229280d80001e015580b00c3e2204601c02d030030000102d10401ba84121030344a0002c4204006080c01544642c0c010b400700c0c2c0c0102d000155145c824000544402d8440d070041b1071039405100140021702d05101031107040b03080d83c105020341150b02e69655541c44407038180300da440380c00d14001981d10308451080720b00b180c020600030000c4410358a40035129400a4030024003440c450420910020200425401102524044940b0300c01c050b650071507050b0300040c07860704883d540100c0014528032003454408900c58210145403981c401a5240c011110014064081c200c00d18548a0a2185035000c030340c000c03900128056030350441c1c82c003c00c09912031248020b240300110040c0038401107505000f0303c01c0383d22903030000c000c69644503401c8408050f680005400061040100e041c2403825100812410360941c80119540e6602c016a4070b20400717461050b00c020b681002c007030300d120022600c13403200642c00300c0741 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 317386187 1250 317384937 317384957
    0x81204110a051c260d020414011d0904020418060b04050604020412030c03020109150b040e03040503121308150406060e040b0408070c05090a0204050f0306040f0b04061e020405030607 80
    0x80d20742d01e1200070070041c3c40141448501040080c032456060040c0c001034521544e5928041d144200031f511174852021181001c00104850350f1050400c617420320100029040d040444000b0000c2210002d007007260300076614040e85608080c07000304080c03070500640002400c56051400c0c881a2100100128850340c810001441410103010159400640604c5c00b11900251843d0582c01051310100191484004981c0d06c00c1035511070f004803201c0441170b01e09001101c2e410740084d503070707000314010598960009042c1c1c000034003810003d030007245a6444811502961629040e082c03412444983d1314060401c0c04010a00c00c00e800f0302002005039079101841480c09032200303101d0100c040c00c01400b50000141c07080c01e100300c408811024060003443c0300e130703642400d000d142c0080d07009215071070040a2000040b2500e1030049052442680c00484030340500060307079604170030074000901c11210181c0d1014a06140b416220418034501008a001a0b0380c606001c101881c2a000900440c200a19411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 317387437 1250 317386187 317386219
    0x903062d0e1005061809030708070b0402180106091703040f0e0f0f0907060f0c20040609180215071a0a0b060702012a4409010c081204110a05 62
    0x10017089100520010841c04d61109800c142c150704c0303050301c040e09041d400b04102091080409440c0e01841c401c8074810340903208616001002c41c424132800703011402111081107404808030800d05003034400b006403490700752111400308060b0743d20b0300303da510b0b81d80ca442008014075881201e039401031102c00781d000040c94400b01c1c1c071f039448100e40681000c01c1040300b150218076004240c11481d45078030841010441104200310f24a2003030480d00b251045061030800620b9101f540f0640450074814168032501d00416024094054000b001461481104215040c04101501c00d440f01040b903984450006051206540041d5110110524480e180400540d00140c3e000000c4010440026071400005000120a207090078001c040141040f030548d1003140d0001a0400c240800c01c1080344520401c141011402200c030701803100d400000700081003144015805078103041c0c200c7d0306c2620780518181d000342415180c840c042d501281c00340100140d444d074500d80305204601600b01601c200103030280c658 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 317388687 1250 317387437 317387449
    0x30105010e16050c07150311070f11060a02060606090105190804020103150b1602130f09020405070306060504120c090e3d15051504090614010903062d0e100506 70
    0x40700b000551883c41d012031006d18025004500c091a20880c0503481c0d040505010340803013039001044416181c200c23503180c0103107001c80030b9802a803803940c01050f9545d5a4000e01940340c1c0711402c01c9040c8042441160307200c1c89103240244401c00c0c140d0740c442440c14140300142c01e445a000c00070170450b074100d00a120159604064816846110344402101d00070350002c918000d030b84c2d414a18555003003a120b16200103503030b0020410640300f95002c22040d80c035520704170100c1e8218010800060030402081000c0080c00e00c903542c1301402061440700c5560b44415040840ba801d055141c0c3d10341001a0560004810814142d861401e52011025070201030200c8440209541060707040e080e9540c04200010940503d60b9001e800c002d41000350072580d40c0403203041d0fa0854030070b0f0801c40d8104039010031a000c20041100300c409068403115004c0d81541e4032170380130700781c1c080568603030440761003050b038411041c00d551f542150711528000030742031004150982810396420166a60307500306414071426444003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 317389937 1250 317388687 317388689
    0xf060e100f0c020d0606080106050f03120412030323070807090510030e010603080d06080f0a170a031503060213060302160318030c0305101a100809070302030105010e16050c07 77
    0x140c82e281d82900003901c0001d18401e012540900304914060f404610340005502032415140304841c8503000b645110209903651280c030901c005c2c845014081044942e54846e001c50b0709520a05010403203da4440c0c2d190601d200f08900081c0246c10b000c14404501c2d00400d03d1134000815241c818401c3c0c0c14031020441821a0329044000c00d592400b4400c550391080d40310601942d030007602d107541e44020b200e2110107041c0394040d06c0b001c1e0007050403000d50340000042980000b40d1062944d207880c035440c60b040f03449804c10902c01c010725440701404034a203d401413410024500c507040040c0c440840010f210369044640d042401494070401590704801440054041003651601d04004401c5005109400f01016584020000c7c00302d1035010040210100b12801101a5001d0070404078200e003041507018018003881c10380140306419103401152007400d4103940715603440b04540c11640d0390e50209085941c01d0380800454140c170001c2c000c4d094107001a0b22000c1125140441c10a1404c01200d07480b02ca40d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 317391187 1250 317389937 317389967
    0x120903021b1201050108030301081c080f060a0503060a090c120c050d141c031b1d0103231605030f0a15170105041a09070501081504060f060e10 63
    0x40905461880e0707450b010902e085010001c000d01c60303960343c1d82407250b8941082c0104e806500641c28101901034001d00605421907a0342ea90144548603075102a212843c05811b15410803142d60001c078907600c0400c440e034040c0ca4803600000c0c02d800d003803c05400e400440e400c00701840c1091250350010600100d526800c1d25012225211810200e240c003118640d29071104241034081d110f255900c03620a850100400d200c56141400000712120507046015500746101020500c01c505030b003100416100d1180324280103040010f0342050002d9940700c039140c03050240311043c40840c100106a244081c00e03c45c1010681041810340c1840c90400f000c0d803c0c000c0c12011115910031046100c039100301050b0004080041940030050385400031729010b88401c45098401410b0079520704200720201600740c3c410700302c2e80007410300c05050100444018002601c0d114003803081c082e20405590741c074494000207003581081d200040c5c0c50311034041c024880c84041c1e80d03c200300b20454109080d40016039100741211b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 317392437 1250 317391187 317391223
    0xb180c130b0d0b01030f1401020a050d021c1508120405180a140408042904050409170f030708132303070507090b0112060312080408040e090105060112090302 69
    0xc4003240d28190104000b80000700c1e003000020500c4030300c442410420b0701851040910442c142c7c1200d0903445000007101c00246d08001056a000107540600070f25403003092000d2074040e240400109942118913011041700f0303844001c00144004002c400f002404450a40d4200341c0b0b031800040103a8440003010809802040010b018011640d105c04481801e81d01100101d0905043c107484a0b04580110802d0050b50380ca03c1c02c1d40150303058541503800074040b000c1c0c034146c104024400544409070301201c040802404110b5140c800c040603107890350031440441d03182e290281000f00725000213410109480084409040440c0001c0d00b0302d00621700b0001d1000c241c0318001d080c00d20b140304003a4003504500444c100451407c285801070070354175001740d80b66442c0911340c0301c031a000c50324180f200501c110013002d400c01ea264051400950b00c00e004080d41400d0683c0c0c2d2180001c0c542d02103821030320a13507548003001801e6030404a0410b0143c002c070310402c036051103503030080e40da0700445854a01d04c0d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 317393687 1250 317392437 317392451
    0x30109060f0e22050307110406080616050a02010623011b03050d0c1218050d1701150201060317040806150d021201020c0a140d02011b050906160b180c13 67
    0x283c0c0c10581000c45a000d000c49654060070b0903c1c15030f00c0940c0d16414850343c188540098500310019115000b03151b801c2840510030764005c1b00b81c0711b0741d0000303400b0030655480c1c0800042d1540700f040181e1311300c20034802444120f0a4080010010560a20401c5c0d003440c22541140200354440d080d40d0303184084410010300346011000560341040480048a0003d041501c3c1301c40700854050b40300001e601c20421581131070b42d811400d4404104c0a84004000f140800042002d0304c041d50b41e44210400c10700000801580700c0e100c45c2c6c54030f0b00061200994880000b8208a000c208000e00d56100b4600807640c80d03124500d90004204006090029102d50145108c0409042080d412a0b104110640403900781d8035162820000c50b403203030b0fa407580c500e0260300303440502c1d83d0041c01421881e001d456103540d0b01c0071101d141941c01c1e07080324090729002403050204284005108130032903500b9004102e26106450603a6506200c0c20340c40700c50101e190090400001c0b03d8607001040c516228030b0201c04200c034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 317394937 1250 317393687 317393731
    0x11512060902150702031b01120213080a0b01150915272309100e07020a02040c05270f0f040e0a0f02120307020d0b0604021c02030109060f0e 62
    0x5804407410295101a0b070751420b030421001c410080841d00e200740d00795580c004000d00c00b441031842c69034845000c11910694840d514030f8070780c0100f0703145080da00e00ca07034a540c492000b1461314095150458100302ca640041c0401c0701654524100c00549252854096092416000c22002009402c00034401500395048001a030f9110f011004041142400e02c11555420340072075030341c080580b50b0001001720000d4080750408001e0030b4464404003031444507182c9001c0784001083c0000303180750110f004800c031b04401a5a6401180c030100e030150b580c070303481d01820f00c01c83d002c00e203007000505d82c40c82c1148141038a98403410050b03405000708440041c0510845030100d8007820300d004840307007140111310f601400c11100201d0504d07014001d5818040c03140e40310b034207171341da80c80352a00103580840e440c07001d803001481c0f408007241e00140c05000503040110940c0c00010341d1410080c0031040305d40210041c0302d0f22040e8410704009058680e4030030251440d181200380032200c044d000c0c04203115500090018 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 317396187 1250 317394937 317394941
    0x5030a0803070e030f0115050603130807020109031208060a06020d0903060b010201060512160609140f04140a0618200306120d02250e180c031204031401151206 70
    0xf02001405580404622100c040d00038034282201b04909070147ca0042442e0511006a900c66541c0586612800c81240c48500c4507030411941203040000b141408800216840c0703400a09002e103888603491418000104401103186800c59003c5510048060000c5503022144d441102c0e001040000d0312140300c40100c1c050400c6401698210185007041c00d0130f0340c1c0016032103c416680800c0c00f84c0e42e40d00d8482c00c0b03d0103d260300c0740c0c40d40d402d0340010503003040c030340360303680c0d00804000500004101c400007a0b500300303420003141c49807519944c4540802c40700003c0c407aa440c0036240d852040107140c00e401145101e200c4607032441c605824000c400a400c0e603d4445c0011100c540580071a03900c0361242000a69510440400202d950301c003031042d4007000c0203405010b0503a00703545504801565016074191280490821074850f0340300b00e000718146600d0502c0084441047c40300074503600c50030350030035500708000400d10004076850a00e4800c00020810309207416034024020b0303001ca1829600309100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 317397437 1250 317396187 317396207
    0x507062a0228170105010b122d040605060405090d0c0503040b0309060a0e01021c0b040f0204180b0f030c12030d02030c030103030e09090c040902041119090e0105030a080307 76
    0x103440d1142c6403001860140788140011140030340340c1844854000040349003643c5080c89180c20341101400100003549642400590105010780c06c030051555500c40180d601c15180c00b418183d040ca0070501050100a001d002d501c0203040d40e0a000606000100a0703540061014000401060b05130600411106208541c000c050001d8250303140d05002c45034503103880c8140e40181c07100c0c1c81e24160441005040c000d64080b6805032130040c03500560020044050704c1e41d25440c1e644560ba40c980040004400d10190001d0082040341c0748000003400103c40442c0c8001008030720403810071404001580d80055540701c202c006403141511008445400c0d4511b0142c0c0b400c0000050000c002c000305140f800303015504880c042d13aa464807001d510414004004c40035111408541c209016040729414590413030038001d880a4400100444100d00164aa0700071500070b089040308101100180f6510008100217001d0303001039007045514120001f82d40321104000100400004400100a6406450022 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 317398687 1250 317397437 317397469
    0xc03050a0b060907110714030a02040f02030a060b070c05010e13090f02180403090902160605010801021812060712140f070305070e0d0206070f050d05070507062a02 72
    0x404149103490039181c080c4007110854020b20b01c0343c000481103441020862020400034015100c454102011000c0085203440700c190107104540c10b010051307d461286044100041c58010780303900300380d030007101079908541c00150700103010700c1840e000c1140c440805c0101d500c2420300e0034040c0300020204410340026241c44034071901c6c0808860511406106030090584200c4102101003074032010075600e141c09a8016000403c2030005004400c05680200448403d040d00348103800315555071401900d03000d80140e80a40d40104150003000042848020665022606e040c2c0c415841d82d5113564986006004c5010003400c2e045880711658154413445800200c40858451403a110700122074492040c3c4030080000d14120000b07500e00d11030743c070300c4601d004000c0104420881d10740030030801c2d40201d8000d03510480c13060ba1103000600204001d2094140940700d40341c070b91406041c0982021410703880181808010b43d0700d500b1480078800c07111003e0501913001e4204104500204100403602c50240c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 317399937 1250 317398687 317398693
    0x604090804080f0c060c190201020316200105070b0406050a180809030c040c0c0b0408040906080601080106050307030b06010c051507110f011a0603150d032001090b0606070c0305 78
    0x458040302c00b182c40030310158101c04980c90b02c1441d105104941c8159080480941c2111041c100a40d160703600c3d03114030b180144102e0381400103066490049641841c1c0c00c03034030103288941c1c02400b0314107503c40002c0c04c40e00f400c109082a8958440c3d510200b8001c4c00240038683d80d00c00100c031138a041e4000f03100492480d0001c1410789280c5081d000c0b591001c1c0c01c1900c40e2081e04031080c0307985020b000da9261030f0a9a07a95229802c4c5a540d50701da2a072002e00112418181031001080c142c003144529402481c80c600101107652404003c00d003101c41d1904068003036007001c0c4040c130100d070100c8403464020800b0b1170041100324140c1800d40c1001c5548080d00a00844a000d000e0b110b5400040242c06107111400e0301c028450000070182201d980b0b804252002072558102d40c0c0d103181c881d024503031241045a940c0040d210810000c0c010b50764480041300440c010740d03c9034840c030401240c0191070441072002080306010503103402c0e1020300000c103d03e224000000700b44041058420302c54005550117411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 317401187 1250 317399937 317399939
    0x72c0d03050d27020f04050c090f01030f0c02060124050405010f0e03010623031c050924040608010b09090103020f0117180d091206050a06212a0e0604090804 69
    0x5291241400e0060a1744070b60781d59a01080343d880c0070302c03840307011300340c01194180341407400000c0c8020b1900c54071a01c1c0c14955982d41e004040240ca00844204c5030059010b02102d604160b00702d2000e07451440c2d513100800041c03110002c000d802004841c1030b24403d00308030306100c410440c02c50319030702e00c00001070301942402000506409282803001c13034900303403554030b802c00c1d052030003030660750002040c86807180e98100c002c0d034199500070781c01007100c028041c000c0361aa550500d01900041114041104000d4000808200c466030050f013580c0540f54003443d491410ba146000140c0c1c2c80018003010388035070501c0c043c8200d107230301607841e0a2181a108c00c4924081c501002d001ca2044000c29141c2018081e2000710502d203446200014142c83c482e2180c802424180c3c0c40d43e2005080041c07450034281d98440021654101e1509110703c41600c00c0c60b01d60841403540781c040702d2039400c102c60790380d08000303002c041e00c3c1c03901401883c2094409018030b10000d40e86050000d8041c1031607241c054a50b03100060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 317402437 1250 317401187 317401241
    0xc020a240909020a1d1f0504060e010504150806060d0e0a0203010c05040303170a0f0908071a060a0e0a060b0304081201120c0b1c05072c0d03050d 64
    0x4520440d100c2a48440d4201a0303a03010803400d91080b911031100040c2000701354094022030401d56801c107000501203240a46541c000610361240c1d01d0848000b04101080800c000c542c0411241802c1d6000c4c40d243e4181494403900c1d40160720300000c034105110545002034107648400c0b081c0d803800d4035009001d101e1595118503141e213403043c07468143d0095003000b00710a040d038028000c46080340da00d42c1e503440250048841d001003500024046000c2d0f43d80310054040000c8044c09803002e4075004101d207940c2c1300b5003031403d0220840e00314106a0741900090030000c49958816420044488190b142c4100390303110103502c401030149401103c01d018000c8203000a010506000e844111003c0001035543d90721446030b4120802c0649000b808405a8041442101a01400303170903040105d26a80c681403201c030078070070305039502164401d0015080c40100e044121007800c2c9544500300001003000f40e140400c0c04202130301c01041000c0c091010024040c3c080c03840e80e50140c1c016004030410480000c803220 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 317403687 1250 317402437 317402489
    0x6040510020c03010f061806080706050f07050313051207060f05090d2108010e0613090203160314010b040203060f010c17030a1401060806010c02040b13050103080301030b130309060c020a 82
    0x80034802c107d03a0020002140200d6a11841095074006001031019629290007125070341e04c0b186085060f000140411000540100050841c15260045401d5034908003400d2100032210059a05005c1d0b101a0080001c1a0095600107804800d841c080da6504181c1c03011070032040403404010300e102c0310b091110000d50a120036141b40c005055584081d0344e40d90b442500c0f4030034001c0c1d42071944111050340550f074001e4554000301800c2e101500752943d10208184241d19081c4642c02070320543c041c0100300700c42e984203120f20701801504550131415400e00d00041842100061400390610410010140500c01070002070130410400f14000f83e034a15150914a001d840700701198200854039000104c0e0f840d002d65005407042a040c1c1d103840540130a0f40801002e400000f0407540c0141031100300036000040b60003014061030241c1d6541c0e549500d5481c11100002e401080440d440c05440603001c00a40c1c00400142226418a4131117101d40180c000614101015400340e503c051140d07604061000f203d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 317404937 1250 317403687 317403689
    0x30c09030f010f050f01231215071b0f111206011205070609050603070f120216120806060d090303060b0c0604060b060405030a080d06270f0b06040510020c03010f06 72
    0x190b0f000e00440d141d6180e00d092602081c0540400b036041303184400c580300f548601c1c0d00c00381e50004001040c2d4028841c0020304190100700300611103c8020f00b00444540c111212142c2d1002034074520a070010140c8038079800702401e03100100703518903103000141301e0b9840c083d04180c0000e2390b106440407541e40d803107001458016241c0456035401190710026080c2e01500f400412a0000750a071451540e448070304881d1918040e00910901c01200703c2101d12002c0c61010b81030480c06140a0b100c1d00805041100d40c1c403000d20201400c000c91001003201d142c5508094404175946010f001c40d1a40b03851509401408881d040781e90b10303032400706849012140000d0b031070b40130b10b0041504000803030f0700d1018801248a68041c8642550007070280900040380d440c0100040c1c030314108002075003a00e8440d4040420440c00d81145024900b039081d070034460407881034215105042c6c000708800010000440d4190045d403103202e1150107002c207072111142c000d0280c24001e010050003007240c010b000f0303001802403241d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 317406187 1250 317404937 317404961
    0x210c1905030106110304031106131e06020f031911030d11040504050a061511010b13050702100e1203270106080708010e0c09090a0c230414010b030c09030f01 69
    0x352442c104c14113001208403829a50040084900e107034105042c0180c0c1d030310504141c0781185a48c100022806010054401217051542c445181e4a20f003120081c5050502250559150820411001c0e140c0c040c0c40d00d40325048031070521000d030060050ba4581540510030508554038108922310700c44940520007030065403422581044140c450241f900c00300c0e401c500500c3c000c0b0644001c041c00c0c940c00b6807082d500d200200300010034503020240101c0c01841080a0000e41e0b142c580c014880788a070144100c43c100319041c8410002a5031440500d030b40c9841400070301e214228000085088000c2d2082000842401c680350300b820110401c1c2c030036008114501c0f95004500805070302140d90f050600440309043d1517000106072028441c010808002030190000308a8400c0c0c0c40a03d0000319481c071200014002141d141031501031005402c4c6844943c151420710451a005421321000312003d091815501203000031a103d55880303500502da8401c0404103545840780d05c240300c1892005402081c00120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 317407437 1250 317406187 317406197
    0xc03030609050907030b0903040803070f050105010503120f180306070903020301050c0f12060a03020d110a06050705060f06030304050a0b04090612050d05030403020c0d050120210c1905030106 84
    0x25503000004102c8900743c5400e10a60025841000460406403c0310741100e82c0d0410f40c4d24140d0f491004034910340c00180102c44030864803d01d0811f00100380320f80340c01010294041c2c0710001c41c01903481d0091180c41c0c0e450380c0c81c840124240f0180310100790f4603481214098129550b509140c0d030054040707200c0b8442244250f0030040022022022401550101032803080c00501742a100550aa80040014071080d0031503c454400005680c0d0400380400840c01001103c1003e00e541c418000c02038456003068041c00000c00c0314000249001500541c80410120468040e8941e0700000b8103501c070b142e0210782e101400718404200c40307010714000e0040f034112007000c1044640e28903040c0d8000e00882800340c000e411001c0400e012501480003198003510905c1600c80d9044210005411041104000e540b1a9541d00d41c1064008604071010000c031b24060711030341401c0c0c500004500d0001c2000002078070400605c08030b03843c05050000e070b40501b2030292a01000d004500783c002c100390002d2140c480018 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 317408687 1250 317407437 317407439
    0x53705040c17100803040324020f04080106060806010806061602090109020d0e0609030906130b07060603050c090412140d05281103060609010c060603050616050c1c140301060c030306 80
    0x810b0040d00504903800100a1030400346580c454188d9401c20400d00c0c40c00241031240c54410101600c004e256500410407965140d0b0300304100b160071110f4507040402800031900c2808026a003080545510440488004da5030b4110020900450740700d00030000e401c829600f0000c180002c03290081c10011391181d5007001600d0005000a613142400e84029003142c004014071005820204001c0c00c4010380f158502c07101680e01e60340d400460f80001000c1d40c202e581d901003841045403d1089601112080351305150300c0c00c1584900d40c141c030701141d41e002440200c0003100c80c61034840c0203844604180c84020003040c130740008a05200c500303540c01e401440c07030455015102e8120500c00d210305c1c1048180181d041d551680e0031300c0155840311150034103000341c030344511000400900484000d58407400140c01b0606012880d41840c1160f62154014081d00340000c2d0444034001841091040809816002c0c180e14003505842d14860307a1604c4d00ac6200000c00031a0340c54000800b81a0b851080d0b90400810b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 317409937 1250 317408687 317408701
    0x20a030c08060f09041704060e040509150c0a09080a0501050a0506030f0d03113604060b090405040624050109060f0203090f0102010204080f16053705040c17 69
    0x180d80c08442c1d10fa4408690035a40c1000e0034080e0340d8980c4288249140c096001064072848141c1c0c1199010000181c400511003000d414107010303081d04400024000d02e0110382d40d49540c0c0030b2900c0245038a074541004a0500c6019104a045200800b0001c4c01d880b01c003600d07404e03d580070380402c80c1c00300c0c030250610b0089003650800080c0c4032054218400605130008800d9411005000305420319500541e040c4500480d0b006500a83c108561909503d821044841c01b130f80b80c94010749284462003a450580e041100011003003c44040d907004950001d02c55407107150800040c03001e2690ba44043c90000700580e501c00c0141c2280d000d9440036215021400d50b102d404032131508901c9000c0005070003e010010640c18001c070700d410807100500000d03040940b100d141502c3d00842d420048940d0340500c8204041c4206500740e0b0024113420b40e50b01105404906101c05556044070140010001c500300100e50b020940308900003406d4010700a20910b003210000410b4000441001030300d01d45801d020540e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 317411187 1250 317409937 317409947
    0x1c0b09090a02060d15150302070c060302090a060804081b03070501050c07020a03020108150301021c0501080c011e0c0b01061d01030b1e01022d0706021204050409061509020a030c 78
    0x2070356078010103c1d031a20002d184910003414810b080d4025122008002054051000da480c0030a1012940e00503203a0040e03081c0300c180099554001000d00d80704000c44002ca48441130f6400079501c2c1d500341403400e62250b240400842c45080c5c00c103011030301c03103840b03446a155000c401058081d020784003d210540326040300584a21403600025400981181e003000154002c1d4199a4007409540100d5034590921300440c0c2641d10820301201c44610048100390302c40001e104042c094140c1c0c10051170301c955004000780548081140c0311406035010320300f030b2040900ca0f00001c2d041c00e40c8101e4681c09942d55100240003a1003003511f01c40400444100c920155101c0d00c10700c03961140085c422036401c249600000c042000c50841c030350440c0550842c0f45442992180e02d84010007800c4040c0e01a0280c42d2051818403803141c00401c11074001c407034142c43c140c0102041e00c007038840c00c0307900080c0e2020500d0188000d04100b0140324155445140004144040341c0c081c02c00003c407901d0900c404100400c0c101c075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 317412437 1250 317411187 317411203
    0x60f06010e0418020904050c042f16050d030c090914181504050d080c0708090f04020408011a0a08210307051201031203060605030c030711031c0b0909 66
    0x200040100700d51000c64079141c2c1188540c00c0070061180500d02241d000f02e00320090444080e00c65a000406100f40ca040c00c1c0301d56100c04d0700c4040c14a000142c100b0701081044c44041485c944003a0200e00365544011aa5050744034035400001c4440341c0c2d11035500540906101541600814810013000517091490b014110891594021401c031781d503601c04614141c3c1906090044051003020100103050b00307000d82c0140124080c000601900c0e000341c900404004004180000e1003400f40020700024038881c5c1a0b4021850841d4410018000480400c000740034560101c042c66003884d407091291400c40c034544000740710685454001507120420b0650314040c0d15807104903943c00c12161100d1101c1c80014540011040c54101d240000c03049102003840020b0f041030b80c08404022220000c250180319a1000304010b003400b908502d0065402106804000d00610030302c00d140c20800682d5005200300c3d5144a00c3c90440030301806181c40c01c100034500c0c0c10b4018010400c00010a5403120006071001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 317413687 1250 317412437 317412439
    0x201020c01110111070602070b0c070203060708090a020604060e09091f0b0a030f0506011403070609210c08010e01110c0706050f070c1d130201020303160210060303030e060f06 77
    0xc4000308101004503903401e07103180d42ea4102d550321068411072100030302c014089140a0240540c503440c0e00d080c0000c0c0302801815031111960200016001a00c0110b40070f07038132070b0050404c5c0000307544400c00f01c0e081001c01400250700400000c0c001c41e2440c1c01c07990280b80c0d10010b032054a05585c99048290341c400d543d51549612004200d055056040c2a0700b0212442c040a440500096a01d0741c40300403104100004950f183c104600601c9100c81074600070a442000f02e00502c15585800301c0a4040601e901480550031042a45940301c20140407144040c554030909401c001540c980c41c080c000c0c0303030504175a0403950070050300141813031805080d2142d408001001c1d1a403a0319019080d1343c2584a80b02c0400d800c82c2c2406980d000c0b5282d016038400410420138080300815142042d9215414006c04000b642c8983c0081840542d9001003500d6000380001c03001a55056202000d91900b00814001d80519081c108003004241d4075400c0607a15107480c0044400303984030944592060719044440e6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 317414937 1250 317413687 317413693
    0x809010c0e15090a030204090c050112050408090d02030102071520070b0a0506031e010b09011d0402060310030b010f1703030106021009020a03021e090601020a02090406230f010e0a09020102 83
    0x1600340711107850010048a10010130424506683c0c0e400715040d1500b0a6080d41e10a2502c078003040b00e56006a8003d0040310402c0c0c0410180c40c01d59502e00c0c140c061901a107001d180d14124120440d10254102e550941d0030201d8804145009440007010345655040d03280501c10443c0410031495101c0c0566890b01d034803086514090343c0303003406a130050000812550385071103040d007241d41ea03004201d00002c1402c006400031411a00c4001070010780032043c3d11400b91400403070010f211a0000c210441c1c1c0155040f180159291034201070007901c186583c1000d0314400300e5500015140b01030004420469212901141060000c8250541c890009226180c056001003480310394143d00359105402142c401011204080e45036008250004038413045101c144030b001c800e0a48603c0e041d0300041c0c1c031603000d10080c031410b60280e01080d050030002e84020f08050f01d0f5601d00d441e039240e400d0280710007445107003c250145042c3c24031030070080c8207228190b5064101004035940389524001c240d130b010340603001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 317416187 1250 317414937 317414959
    0x160201110f04090507170405030c1e0d0e0103110c0601150f020715021c030c030e2d0a0f031205010801060e010b1809130203100203041113060b03070809010c0e 70
    0x42a001d000c0050801c1700b040140f075120118070b554424007502582c018002075444004c0385860340e00d00910308800b5000f840340c0e07500d01d410340540020005d880003da0300d8107142c51040e010060380500000c05410041482c00b140e049202007002550780d04135442d9010208111411800c161104880f541e0b100005130451030040c03102904026100500c601c551044509580c42c1103034102840140c0e032010b43c0000e8952403004c00f515498050086800096406060080c881c8000e41c5824a0b00c8401070119840c1c185140014810522010110301e07001614450b05485602c3c0041148040f500140b1582d458940003040051052003240152103100d4420181c42e405c00b04059401e801c460004071380d010146840001984910135803034015001d4072282c8500382ea20307204041c14200c00300002880544140200404204c200b00b4190b01014140c60085034220b003c02e03210090000c5401891559200100b4441400c0d4843c151a2241188400070804c010a070380c0c0c01c90307a0841ca8a4401e40c00210144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 317417437 1250 317416187 317416199
    0x18140303071226040308070201061401030c030f02030708181c0509031903021011090f040c05040918020405130b0403080603070806010f0303031d0a08030a060e160201110f04 76
    0x50709120201140c1860000d0401c48078444a00c601d9607242c0f401c1e0000075400344010160840d0f81103401c014070b8002408860b0074251a042e6140d040c645041c109920744099400c1140030341d00949088501440c103554a1420311405881d8880c2a501103008110852640015a001080d9142c2c0c1c42e812564103010040c00290440301130700100e9809900d0b00618001a00e035940c0c0c0c1d580542e440384690050031210381351010314421200c50840346c101c441d80030002c44450703507100c4040200340e07913041340d0000703802402c09000c540707900a0381c01c40c150b1039142088044044031038180307100c070080c1308072818020b9940f015852940c0082c0c442d001401a424a4081000603004921056200d00040e0884003515610140369140c990281d01146413080c105505000349a41400b9498040300c1c2c030504400300e00800e1880340c1c4d0301c1030161809407800710301001081e1211185d810442c01000f1b291075004140c2000d000540900c0403101c64680590318043c0c03242c1600080d0025100340800c20722101d82003500d448 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 317418687 1250 317417437 317417453
    0x12090603071b0c06020d230a17011e060f120908090301141e0c1b0c0904030f030b030106050f040b03030c011113050102121b011b1814030307 62
    0x20700001c0074040781076500c0c444540d055a81d800c48500946069401d40d2500380b02034101804e00c80d086d800c001c0449020050044170041152140510f00a540d0740c400d4002c200302c0364002c0003c00a074488020703100000d020100a200c40700c00101100c540d1203044d030b585106440764008c0d15a840042a0b83c81c1c0b9410000321a03170300000d44075004204841c80c20003084006801c4410a04403e40443d003103a050040c422290b80c80e03074405001c144810211402e00400303030a418020080f683d04600350424030742d070884009001441d07030900080c006c40a1400c081c503020b842c0380f110025200000e403400500000034981401041e08075000a0034048280c800d00090201420801e0340b4190544401c0044441d0381c1024412501004105408035443d411000d14400d08200c1542c401c90466001c5102100746442210888101201d4080c90120311542107206c64050107a041d40001c080010030045541c180d04102c00d80c02c081d0308502c00d02030b0701e620340c501480c4411459401540544c014003507040062000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 317419937 1250 317418687 317418691
    0xc020f060c0a09090b0307091b0810050a03020918011401060809010606080a0905011107060516050418090f140331120201021e031b01090f1e0204050a0c020f12090603 73
    0xb034140d902041e2144190000d8948100103103411540c070444102700e040c0e00094554010080901400800b440e000024800325418000a0300c01c2c00b10310007040745030142900051040c16407800a0001c44180e043e5003410007824071504000c0341c040000140805c0040c481c035002d881040e12030200603100c00d80240024858040122580e660307980c5004142c0c10701c1320203000c104d441220081241d240c0030342c400c0c6064510f540d60030240001444184030a00c0c0310724090001d008503400c00100710006082245508404403400f51000348824070060309038402100400b0508080d070038440301091070a45043c95442240e250034074071002da5078107001c5040300d40f5031181d8941c0144111000005d4168030007001c054146030003000c66100007003519400e6140082c856204204070000c1045070466220940c3c0314004400c02401044004a90b0b5440281d650500d07241035006001041240f511013004801801c0c503641c0700e00036216881111002c0c000000b012051142041d00d41400c01d03402c0002e0089907040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 317421187 1250 317419937 317419939
    0x100f24031812090b04170d0203030702070302010c020607020402122202221d1015050108040204050703020c0a0305030a11040302220207060c0201021305040608070e090a060c020f060c0a09090b 84
    0x24100f00107102810003001c5c0c00a810920142d00303074802ea0421040c9410803500110341503400a004000700e4035004035800b400c41e50203090003811000c4903c0080d07618401d081c40250300174404a0046280441c2190791072244003030340812500120419054503404881c0100254841009560400c8543c1c649040d1124103a11490100c1c1c07041150a000040194180b22408030343d00c1504914a00700c114083d1070046441c080044091310b080c040002c01c5000d009001030300954a0740049005d15210764111082100688191a000ca82d54540201070343c0c13090303c8800310141440d901c40c0c0c0c9002030b031084a0449074000c051600000d81d84a1249580c40d10000c0100555404e104a07030101e10240a42c02039511b50343e00060307a51070528042c84484440340c100e18011071900405024118001030a5402d032044102d00391b80c43d5850346805883c00e048000b0041c07425040900c14481c042d0000707070f28012160144140e1f1940e545141040201d401405081000103411400410600e01c05510103a1740b81c00c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 317422437 1250 317421187 317421197
    0xf03070810022d0705101401060c140706091a0306010c02120c030307210f41040e0109090308070c141203060103061703040509100f24031812 62
    0x10345a070401483d10058840e01d4000200041e81410840184441c210220156404202001012521100c14a4140600e40500c03500e6201c1e041405494000e1114401c18074084a600325101e80b0028092100f034440c105240b241100710244940d524011f613442444103a64010b0a21107940801210301024100d040b40d038004c1d011000e207240c405100600c8580e020b02c00743c0c0c0943c02404090300744445d84a004d60200440c02c91040c0b00c540d0702c1a4107042d41a40100403484250810024550403c04036903080c10311810a000150107000450203441202c1c101108010140e0742e8060620642c1c450361130040004820f403000031041c038064000500032602844040714030b403100c141c9030303440d0212000c410061080701004001803981d144c00b1700805005800c484d40d2120300c000491590300c4c0500e000f024401e11100c00041d05404080710010004e01681c0301072a155940e03840c08000740130251400d0080c00d1044007056403c10700902441190b0350641e000040240e8180c1c403495101d805080304181000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 317423687 1250 317422437 317422477
    0x30d0908130e07120e060403081905010312030605240a1403040606080f070501020303190b13020904061a03150609030109030305010e010f1d040524060f0307081002 72
    0x40e0810300c1038041c148039484014981030403e4090701101c1c0d016001c007601c1d41401900f041e6440b0101c0c04507005641800d000b1441d40750500c10784116441c4080c0d201c144c0307241900000034010844815800d000180d1010001075465100380030030204160480d26a040080c80c1142c00b00f2506002440261201d180c08601da850750701d000344480d031050360280c1d246900c54030b05116204040c8600b80c1d66004020003050210702e440700103901c1c1d000052200440e0a0314248250120740907030000e5204c440000c01c1c000303910092081c048000c0d00300d08440d500039071420b00c01294030301110f8000302100388420000f6003980d483d03400d25130003e0306020a481e0403030401c4c800480746403130034000c00c01214402e440224a0703604080036182c0c8450168480c2e0015114608100321409844031006410402030201030025503e505015180c01d010016080d50328219110940c0c0c3d021055500e280601d80c119220301d024a0000200360b9500c146026060361078201c0d0306035118071704207607008000d00541544244041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 317424937 1250 317423687 317423707
    0x60f140d06180b010501030c020a0825050f1207031d010e0a1d0606070f03080403090f030c0501030e07080709020702010e0d03050c15040b0f0a0207061a040e01020309030d0908 77
    0x51808070071882c0d10035001c50b010708100180a007071140580428601009a1281c0f0400250340f00f482c0c10000e028242c0008098442c4441111707101450740e40131030f070207110300318900d03041c1e03945c40c4007428004c000e018004400840c18803510840700140c7e0150368104004013000d118816848038000340906012400c29a0600c548803c034040c002800d4111004d000c40360443d455088500c401014184501070400001000480030120307080c015400d40f81104d00c030350f503602c1c3c19a03000b04e0603040013800d452a100000708200850380c1e0b40e0140d4400f1380e01449043c2d111845165950610300070408a908944014080800306a0140070b8050052600e00100b00c01c030b0300880d100303a610360b006030001030001559494640082000c150058940c800c211030b03919180d1100141c01c035001d41806814403884000c41c0504a4a40540c3c0500e0740007e42005030065102c40ca101142200303040714007960a01c0052206c1c44010310a6034410041240030f10b150202c4150ba40c1c00801d035070581120000d000780030340004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 317426187 1250 317424937 317424941
    0x100e040504060219031e020304080c01020d0603030f110601150e12100c1b12050c10062108042c0c040608010e04110103050402063901060f140d06 64
    0x314042d05005075500d241e1012040c820b001e01040d5010f15050072203041e070140854600220240c4540710068607601c844c80d198440d4031900d40300003441e40c00400c1c500984c0003d0380c030010807039109484111028003101f5085d04c0d0000e0760801c440303540c0c0082c0700405c0b040603d000038130608107017842c1581c0e0510884000442c0da01051542e2032040c2d0040b00c505024004a114004829005091448005640500c1004465880c01004101c40705803882c0c21080d5000c0d40076148404119000e03140d001e80040d107c100107207241d1095856001d0301048008043c5100e1401e101c40c242c100350080e14103403c00613440030003611054103485582414060140340d071070000040d030060161290f5199610310b0200001d00740b81040e080b0f218003018031807d12002424007407100896803000e003000304aa555600004e41c15009410b04842502d0250780003120004c0a130040070001c4490b0260300d00ca00403800c18181c05c075081c0e800b41461f001c0d0082014010754000d1011804206001040783d503110683d990f485003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 317427437 1250 317426187 317426191
    0x30708070c050d2a180b03011b0909091502040314100209010519110d020f2803050c010e030d0b030c0d08032e0311090a060e06100e0405 60
    0x185041020420408100022119000418080380d40660011150316000000c1d070b4149060880199103042001c0300c2601350a0600c01454103004030b882e18000c1500c41809030401b185e41c0307442940707001d809100c00c542942844440c140d00d6692280001e0911300d2110080c030051a041c0c0d00c84000c9000c0364450409400140041c512071059180301900300c100151800e800315101382030312401404291020b076880340644180180c001710392600032403860340c2555156040200840386010340302c564900b03250005000b04844000d48100c80c10790740c03c40741c10803504494590761400e9a15822840307010920500c046c2207807061010000031500116403082c0c0c0b440e41710f8070524400645407087d2124900d024080c0389000300c0180d90744450420203503141002440f00070880b10344851081c244141006140040b40a04100185520301d040c0d100d01305100505143c009640c4689021400640c0c0c0303d0281c01000300315500d41b58800e0342d03500e4010402400d8042e9404034410804900f00720314042d43d660240c94 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 317428687 1250 317427437 317427443
    0x22050703061a03040206033403020c0c060c060a020703021212041103012003180105040f23070e04020103020c150708010b12190207050706031401150f0e01110307 71
    0x54140c504002006160600403031014540b40600810001d0303254142100e074400191148528414040704e40d4421010801c4a810100d840107a050104c15030154000d003054214241260316074110103080008034420303100300321419000300700880e4500d841034000d000194801d00640f034803400d146910f1840e582082003d10043c2c460381c000d20007444000084603d8032031007600240081044012500002c0c45803072442c00c0071040010000345900402016583c402d40920000d11950529062400004003024410b4400700f0003420002018036064254002c03051183d005800100e28050642180c108001c00507070602d070b004c02c400301c40c0f04814407480b4a442d441c0500c80d40380e8244000f0041c08400141c01120100400300b1006070010740c500d40d00341d40500510581c4480340503d03032561029000c0c100004145128100000c656640c150700451030400c2641c0c0d20342e03020382ea545481340328541e043e44d00c000420014020710104a12031210f00c16200e034181011182403501020305461070b800b414040d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 317429937 1250 317428687 317428691
    0x20f0f0d06060f05070809240705161409010e0703060b0c010203040611040812070f14101a010c060e01140c1c1a010c0515101403010504080922050703 66
    0x42c8a09500900216050600d41ca002400c4c010142d851540300c0c031503160018800c41d41407811001c0c00d1010407410304010700c441c10050701c0b601c01e440c18940c1d40050005070001c1e00070007203010034000003404904134001401000740205920708121144242d03005403a201c03c05481e031001159601d0003400609081300f0034800140ea07840c0508180c000c5441e0b0112800c4840c0003000b0411041a00140002020403050703405680c4031900c0c43c0000c0710500d82c0c107006005401b2101403070407540700030410302c072840c02145c0b0074802c82c2600203600b5480300000c420640070548081c0708901040c5240d1004088402000c00000c440b10380d000301e00c1c03102c50101c0b0221007811002a5802c1c001740340ca41c95007a0003507040401d0195044c1c00c00d16009021403441114104800050b003602072090070400744820b040740c1403600c036040c1025003008820b07002c2405142c9007000c2c6030b0210803050505100f200d100f150400034050500000c08100408811000c1e43c0541890000d416103010388031600c225801000da607200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 317431187 1250 317429937 317429939
    0x103380a05060a030b1602160e070912050303131401112205030307030e06070f11010329040209041e140105180c1b06071107050409020d06020f0f0d06 66
    0x282401e58100420039405404000ca040001402c005c843c02c0e00000445052803103104006812443c2c80b0101072176020b61600d006000a00e520345e100c1190040f846a0f695006054035003420003501144600000e1a0380d10800019000d50214041d240701e01e441000420040f601381c80500e42900c0c0f11240c1180241030001e2207181414081c100c000301028100d0025000500e000000380c2c5a018010000c0c041c0704000c400d0500c01d035604000ca4007403561050406051010b24102140007900800b0824082442c0c5201902c40c00c40c08511440c0d4003142c91075054455030a807003808040d400a0307102c1900075071501e054203030b03071405000681e04010206400003403900582400580c081410b81c88140245e03049020168602c8040442c030398450820301c2116a40c070003080e01006501c500c8c0c0c04500c682d0085005109600c0d611000385156000007104480c02c075501d0300100001c40b008440002c2d40b00e004100c200e0001071094000d80601031039003854038103001900ca4240d40a60003407101045040e03039030310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 317432437 1250 317431187 317431201
    0x415110f120106030605010e01020c0d0f050a1101021209100c02030708010f0e01140609010b3004060f0b13090602090a03030f03060915030f02030c031c021e06010338 73
    0x4500c60086c4824644a00003210b040d00203510340180500306806600d0105a031024031005401e4481c91540c070604540075010b460411601810403940314600501462030080720816001088e1180084002c043c0840300c2015a4103540b48100140200d8060090382d1000170105028881c01060910500e00890740d20034001d4810308480007142c1441c0365400781024081c140d2240b1403110706444c56112210742d0340e410303245204c3c081200e503161000c40b507000c28a000300b0740580c0c4002d02e000310301c01c0400f401500d40030304000c41034442180e01303142c10150409441c40c12102c2032304800b9005008050040c603288000c0c001c29140c00d2150415804a00441d0403003401075810302c1000018114414100200107001c5402204007d0780d20000c0c040c9080c00204106540d02400350a1140500401300d0301d11501250410480d006c1a9a541c0c000d4003c8405903d01030440d0780c0602d40344282a0094070181e03085548000c96000b0081c1d0074828100205070500e180307032600010003410b15044040315070f2864500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 317433687 1250 317432437 317432441
    0xa020c0f04020309060f040602130b0a032003070c020406081203060316051c0201030f05040308010810020c0d180b03040308040b012c15041a1005030415110f12010603 73
    0xc0c16903015500c10420000250340204409412a80c100903070f80d401d848a04220000e400380e0096034201e581020ba0000301d00030110000c00c1d004e01c140c1c809001c00001d840301000101486134064084503c1000094000e5100300301d042c10040c03001b04000380c041d07103902c542071030032054025602174401c0c00010300626150412413003104241d00f0652000007400c00c408039000040c0f4160101c0f1504240d42e5030403c41e07009400c554030841050000f0481417510782401000b00c00207106600050003032078820011481180221500068141d000b4140031700c2c0450100c5a90300091154881c8440400010580c0130b1240c8c0118000c0380603540398000c60420b4206400c8400060b400180e0341c0102c080c0f620703101040208103e00c04008111043c1081c0d036180140000c0d10400742c21580d04c180340c0000e0084d03202901340540302c41d60b000d450a102c04c0c2c400f0f0b001a1024070007a0340c0a08600100781416045c1c0c401074000b1080300c01c0950405040c00c00c102c241400c190000c150301c3c2c0400c1e039050010300c10b495242c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 317434937 1250 317433687 317433709
    0x10e01030225021c05071511060f190603081812031602131b1d0a0821030c0f03040804090507020109020922030302031f080a031209020a060806030f030a020c 69
    0x1140e000c00302d401c1217a890541d1500782c4e105001d1000b164407894902c3e01e0040f0124500a01440c00b6210303180340940aa48241c00c04441106c0032203084840480c03003100754071800d070a407648030140904d4440c1100c403107140c0c0111080346550040d1451101c40d621042400038010380c241810352141902020300c10800100181d24003010081d1070070106004803000101c1060362400107062081d03005030200724428605021000403500704001090005d48031000240c0301c0b4409514400200107078514138000c60721b0344004c0e20703032506401c401d100d0300c1c0f6401d07154030040d42c000e40310382545032900795105604030545800329403890240c1d541d08030700c9040d424403186096201c4815401450008a824900e00f82044e94180c0035081550201c00078102081d400e0208108100c103442d54030b0f440c2d55541401d90b0f14819031000f200010100f11078400a08960700464043c00d5004105404e40ca08140d022a201800145503560620234803804220002003031008200050055000e8001d202d000824802c02000c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 317436187 1250 317434937 317434969
    0x20f12191407061127060a05090d1403071704080d11071e14011119050c060403140f16170102070c0312110606030d030b130507030203070e0607030e010e0103022502 72
    0x90b117041c11000b81e07184030442e034074030302941823140d00c03088807101040841603007400003001205041c80c94003040d80b0000140054501c201032046849111540701d030328502407881051126445005074140c114020034104043c401940200c0d00ca655992200d401d0b0400c400241001c000b19259003030041c80310f68038038040340300c000313080c2180c0034de01240c00c040da1078510013040c40c90b421128803a0b1341045010f200d6802c203020001c14080c0c4a9449081035148005505240701c2c00c3c4c40786d94210140c8031404140c95410320b090034058200245880c000b282d041450613048007c0c0c0d5030811090000901c2c004a0501440c040c0700b11074543c1424240151410030b01100604040d809101000f949070f03000a14900c1d0305035285004a0704000c00030224803c41600244d0302070341c9040230100400c0d140c1c941e0140d4450a0f0700e50f40e8840011a040a206c1f0501c1554005000514150910072055024218202d00032806240c01031030a50f044003035401a4580000c00000c3e00b12a955940540c54004808111600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 317437437 1250 317436187 317436247
    0x15010e150d020f0f030705041e05060909120a030204170d03060614092b080d0b060702011718010c0207080d0302040503030d180c06020f121914070611 66
    0x1c91500003980c3e112000d1500f43c480ca00040c80010151010f012072801040003800034815260710980100d80c44055091800c00c661810000615034907004c0c00042c01130140740c018001342c3e905800c05000b1a4030103424841899000c0000142c188101c94423402c18a80754409040801c002c0d080050030388210b40c0c0801d0811460404038040108010201d80c807800c811916154002400701c040f40041c12655111030410200380084006d1100c818024004000031141c00c11107080030204200c02c602410501034001803008891084055128070f59541100040c0b2210b410078510301020b6080d247c2c144109801601322103410441d41390304108402e9038541c41d0805604203070820300400d070b82e8020240c1c084e132202d03212690036103405103021b80c03409500d412040c1d480840b0f40362b4001a40d685036000c0303003400301e00c01c003104c000c003901801c002d0320003002c040e100303821500c150300300e045901c140c004004120202c0200018400501c2a05c102d020300702003d11081d44070f20000500d0110b164141d2680f960600e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 317438687 1250 317437437 317437459
    0x50901050108120c10020301030804081204031a310b0606090d0b0a091704031203051012051e010b0102060a0e0a022e0806040b01030b0f1215010e15 65
    0xc0040750300e04600b032640140e9071301e49030a40c6001d46000c0c0804003450b41c0d903200200210510200e800244250303002d0204136120001c2c2c00891001521a5102c042e001022460400c0425144001d00d10380040000c44201c40c2c041900c1c140100206044280031020b0440c034990030100301311014116488501101d02c01d00303044c000b50116260b05e11a4100821040c902d00c00243e451081d43c5c0700d502c50f65001480d40b5100100101d420f0605c2e446400300342c0f44440c5506045027094828041d440c07088410750820400f00f07150848558074615007010483c0d440c0a03441c00640c1c21340e142252a40c00402110020910035034000001e801e00401038a511075042c101020000000300029001c40000d605035400c846200e000070f50078100a0200501c0c0061503982d061101c85168000021030182504450030460003852500550131110b4514440b600042000c2508001c1d10780101e094003034030002d00a40d40d0003c0242440414188240c0003d1078080c0c001013070015580d5440070000030710400342c410078070f02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 317439937 1250 317438687 317438699
    0x11091620060604091a2a0711040e0c13021b0f0a030f1b060605040c0504031a0c09030307030c0b010905090615030102090d060501031713060e190b03060102010509010501 74
    0x81d000c01802e2a008a4070350f0301c0ea4041005100701d00441c2800d000c01079101d0b0610403030200200491802c05a24a0700780000111180c1181041342e08069010924005014000c0c06110240c46040c10307098003801002c0000300d603a1141550602d0049202c81d005a840104004044188031140c4590310305074007800780030700a86400140140910340500b400d8604c0c08060f401142c1181f07500403079001001d01030124400304180c40e00300030113840b01110184041e0701c2c0200b089841e402507100190044000900c038400e400c881a1143d034000b030b450140c01e8a4400100046459644220700880004240c46210000e0000d09002c0d82c0c050040c0c0a024051130801565080da103400281c0289031608451001c500307943d03825030483d40e0001001c0d24144045449040c42d0000744000d00c01500d0b4056003070010300319a040d0904030b0309541d44944106400900b001c40c100d615502e41188283c010551001d00700d1003940c2c40722280d00600e0808461035480c82d2090009081d50400b9201b1130310750381040014414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 317441187 1250 317439937 317439943
    0x609050a0c031b03050a060f0b120a0e0706050304050a0206030f041509020609210d210b0604063905010b030c0102071401050403060507031b0e091311091620 69
    0x10b0207144c9000f041a880d00c0d04d104006003a682c0c40b800b01d5840e072400002e520b00c0d40ca0041c06000302c2503824000c4030b039a1150b83e0011f5488510601e01036800980c400c0c0300300e034007401c003440c0c0150050707045036802d030764590125030141e000752000341c1031881c44410001001090f041180031042d41c20003d20450019501050841c014100d40b64450901d80b0840c4d1494000c05000b1540b0300100c10448061408004004c1d121030418030040a540c0c2c1c4038501e19004140500401c000302a02600c52440c191500c1d40894480c01ca03400c01d4850039070652503030748203170b07010028100301a1071505115007100c445290090846000d1503182c1d0080d009800c00313010680e008261072003140c0f501e0543c1140c441141c00102c46c03a2180341c04c010002c514020030310203c154580e0100740e014100c00707407010000748842d400b0340c0c1c081031180c401540301101d8000907042d58890604003109a109921081143c451140005c100303500032104084c602120511541d4030075030109011042e5004800942404c588582036503031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 317442437 1250 317441187 317441231
    0x90604300305120403051c0509070f0b1912020f0301141e0f1504090c02070503060c27060d271104090f1a0402040507090e070309050c040609050a0c03 66
    0x4245820400141c24076011b07200311048068004c0e100039000381c0c10340c402d42c0200340035142045a803140301c40100e0351000d20300c586425500c4044c5424101411454406810726001c0c075035108104903048110b240c40054005010a0600c5150060316981047e1080103903001c13003000176101c2d0000400c200781103030280300d82d04100300007900d04030b81540c80c0c00d001c541c8a0502d0b05024030005000240090045100e50040f441440260f094030901380e03640040698841043c0d6400c19001410446400e0120100312150182c1d0104400304200c041c0301c000103000360300004000400e468a40307036056421125075400c4070040405041c1035040940c0d070b40b00c490b00b1000c80302c2041e0103143d40e0103150052140d90300c1c160150700d0b40311041c1c20201504610381804d00070142e404030300442c140401300b86514001e02492041c2c4129260005640d56100021006400120400c0d141401403031034220840e280c9001d0309016144003680130805040c1202c1080403a040c48204000701481d1265464081e1211000e1107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 317443687 1250 317442437 317442457
    0x120901120509070f0807050a05090717041104022101081614210703062a0c031106090309011101050f0403050f040509070e040c020705010203030c0f090604300305 71
    0x1c1d01d03954000d07881e850b00085420a0741074501c2e2080015031090009803042c140c0d042942c15180c13055454043c80210305040c0d605a02141c00d401100000803600b82a080c0e105004541d80c0789003023003d40108049034403009180750215018003c030064283c1d8801014011f20041c030040c400703400701d24180321420046000381010341c4105454000d50341e075001001061042070403804d12103a410040d040b5519a0244003c4421609121581d80700c44000302c590805142c1d200d5449499408a606c101d40c08000c20b8411014420400f44900e071a40082080b180f081303458800640e82c030940b130380000d0514061382c180c485050381030030108101806060340340e94129a00d0b0034101e072104420a01c07150b2900035a0091508608500d0402c001d55a11245080c3c0c0d50388140d0741049240b604500c226201c00041c02a240903038010004a41d507080d03200c0090541c581d4103020700382428000c2c07000416580c080c1c1c1c0a010b00f40045c4110a0b12402402e07000184101000c00c03466501c00b8598001c3e1541c01036800c03031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 317444937 1250 317443687 317443691
    0x30e0c0d23010209060c1f02070809090c07050706020705180103120c140105090106231e0a03021e1206070e0609040b18040b0a060308030a0c11070b0301030512090112 73
    0x40580703100940580d450640010b02150721025220799a40e07403100030468000201955a90380c6000000e50302c02c580e005074102c00c20500d0b081c001014082c0011f005840100191020440000400d030180090400f0700225130281151502d800c003080780485d01d01c8104102e64094070010400194030706d00102000c140703828040260201820000880c408062880344554240340410076865410344c03004090b5114201c0811070000107030f5202c00e4121100c640d0f01e800440881d002e1026198180c1c1c584c1d40b441c40241101150f0741c4a5020400003c0c2001c408619500540d0b4405407901e030000c101c44d15942500000c0a0b14502100020083d079200c1000500560000805480a84568101104484e4081c1031072654400005480c0b12044040b501501c0054602001c81c54030040742c0071b00e20840e0380108040d03045845058542c0700811000e00c1c0001481070322070054084a6090ac00c41000342040d210b0b103516903145d410000e00742603201c1c501c5252200308104654840e80c0000da060702c42c0180c0440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 317446043 1106 317444937 317444993
    0x40506060a230f040209150909070f09120302010f0507021006080d0f11010b030706080f01050d1203050702010b03070f06030b090705030f1005040c030e0c0d 69
    0x10b100151101020b8511589000804911440c2c0020401450b24420034005100400303450b035444134204022031180000e00d06406820350003a814100000e4a4409100040c040c50690050010201c108103c00050500c02d500003040704e201c4030400c209500344200040d581d043c800c904844a1410004007140059022840c1400c0030815110b5400f81c0d001d040c3c09807552038840d960b00d1103075982c81045c0301c003a503410010400200480c2e00c800c0e1690070180c1d181f004400050b00428010b86140380070708005075881c140346070301841c2131400080940303829030202d000d8064451102d9061254401c0803940c0c000d440d95040440d030a503203040100c0620102800140c803000c442c0da0307020039001d200107841601c2986800e0350061f8100d0b184000b583d02c07080014106c1c4c0481d100d08002a644903c507440d40e210070840e01400035021180c290b0050040c1c0d5810710040d00542e400e000b28090908 = true := by decide +kernel

theorem cover : BRFrame.Cov 317266187 317446043 := by
  have h0 := BRFrame.cov_init 317266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 317266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 317266187 ≤ n) (h2 : n < 317446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
