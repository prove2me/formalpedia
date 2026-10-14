-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1994
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:32.232995+00:00
-- url     : https://prove2.me/submissions/ed4c6c65-8b34-4005-bc37-69ee81c852e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 358453237 ≤ n < 358633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 358454487 1250 358453237 358453307
    0x3090302030331060e06090109120506010f060f0c1520340b3403050903070c140307090603060c0e01020a0c050d170a0206011404020f0d0c 61
    0x4502e840140110920205610303c442030101602c0f9140e8902c180b0f40c00700300602000750051102641449140c04000c10450f00b0002030402c0305000d000144002e5140c02d00b4012070b5910b5801103410012801101c80d0383c01c0d009107000380015409114459460003002c0e007407008100c0d40c00c21100419652000b000400300c4d1074090550609192180640003441454000c2a841034000819039030403c3c04898001c161401042c95009050079400006981c0a0101c42c103c0055400d22080c040e03072010307004a015506204a5074400820300c000e624010445d103032111040c00a00c5800c003250054900e441041d00c0920240380285280c000c140a5171346c032454250f015050009007080010514507002c40158800118002c0c0e15410190041c1c0240c00c1c2070910550343d03c1650705482c0714811503000f0350701403c504001c1c00e10348002e60141440754180308e0900000c0d5011041c5500c1140180840d0662040c0c00e402c41c1c0440501d0000021909620030064480c0d19901034550a04a511a14403031145402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 358455737 1250 358454487 358454527
    0x80f060d08040308120a0b04200f2b0f06061b030306051215060402040501080a09061b03020a08060609060d0b0301151d010515030a0504031103030a1505030105040816030903020303 79
    0x200e0300901c070f180140d9043c0720803222480c040c401d03003001c200f2400f10f44070009c4000381000111115000d103020b180d592903000c0112140c0d00c0c80040001050032200036000b9108a101c8800c148000f0700c0003601e0a00c0080c0b085012145291030100c050448508041c000da02c00801400b001e824500c01c4555608080d442ea42014140c404402058001403201d140900c202c1d820340310140c5918100e9203c0f18542c00082075400c0048510a0303852079001400700010700015045100d940e03001d81d448500030b000070080800904424003525090000240e2030f0345480558006070328012000803400c451600203405052940018480780c0940c4401148600444550001e000c4040108100591741c0310309101800380c2100001c094002e040c8017003080040da40d0400c41c0c005d03020303280510035002e0120809081d60700680e0781d206083c3e1b40702d83c1d5400651031990302100422040380208084e14164807415410300c0740c2e5403036601054003054801c00300350050503240301464015040700e4035103035422012a848000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 358456987 1250 358455737 358455751
    0xb040801050a020408031c020c070906080c18060103091a010f15050406050a050702010c020a0803090423010312090f06050909010839090a020304060c080f060d0804030812 75
    0x1c001c0040c40c0c0800c14002c48084990380c400551611100066420f004610400141c1c82c0d075808001c4410b5180003040584080e045802c0d000628500d801401d600c0d099000c80103034029081070b001c0701c0d000c252482040340c3c030207400c0c200440c00e0070312f80c07519000f140610041903005aa04600207d81d03031400071080c400360380d150306118844146118066440c2c0c01039202d44000a00c0800002100f03c0c800e201402501c1d00c1030610000720f190319400108120401e8200302c40613031012800e119289028000d90319504502c2d00b060062014101084501d100140406040303410341c00b4684061034810401c1000a00038003112070f0001d03448510050032503101080c500d03c01c095100011800040228106000c2202e001209843e000c0c0d0942417507000c4250800702e001e10046000c49000d540b00c0030042486034050440050303481c58107140c00e40c210303a6031034886410086e05804000118080880300b0b134001d0022210b90a45809520300115944902d0300010045600400c40c00e203c084424406070107104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 358458237 1250 358456987 358456991
    0xb0d0b0f0111070303050f0d0903110607090b0708030705043b060d030f021204030302030d14040f030c06090204060603051009020c100506030f0109081c0510060323010b040801 77
    0x640c6001140e00304145142c088081e00200e4040000900910081c145c0d40c410005150812480c181d0b400102d5070401c0007540426031a10790020031090501041e98003c60f1420a481031504004000b4902d0248200080103100d000001c500c0396030003003007646c0040043c0c1c01c0c40d8010106030400358074030455866203000c80c0d00c900c8100d100708680180070184036a0b800380c50780c5401a00d64608843c8088110002d4040d802103021507a2041141402000514000d800450781c41e6035203460682200d560641d083d013814a21014000060b026a01e01503405d41c149c60094202d00190414000800304100000d600070304d04040000c2040c0c054002c03910803140e10050790380d215604c054520980c8181c1d412600c02d900090f40b0550b800e04a43d00c1641c0200029044540c85801b003401d0341d08440d00b00c2c006940d10710001c65140aa480228681e05030b10014007400e00c2942007685040a0004541c0241c400340360710380d1030340550980101031100c29080b0305660329000e569500000e0605500c00c0c010620994 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 358459487 1250 358458237 358458259
    0x2102040507110c060a12051308040b040608100602032d04180b040c0917150106080f0106020109150504082b0b24070807050d0f120507020607180b0d0b 66
    0xc40c00205a819050041d203807486c41c0317000c4149000003000c1c01440c01075400900d54103074022908501c040d10107800d160741c00f15a25401d201c0042c0003c940200715410504080b0340038414507601005075296070521b094220f0500c000e0760328180c1c80c0716034212200c4995502281c00650b00041040c0e00f60090300c4001d040140104e4401403006403481d441124000c112400d8003080030f0750100341a01c030841c0381c06055601c0c4000c100c1035003440040a81c04403000034040c4d020b20005a0600c0100d600625660008101c0c40c0c043c1c1e40c0790030150300d40f60a200c0440d0307911400201070048003411110b101c101044540001e07200d06882c0082c2040040401c040d031441e107206440942417144d8490040284020382c50144865685076032815803081200721208001880f0040c001401080804441d4403603483d03007190241c110600502c9418400102031099050006201ca16600894001d070003026a1801c402550403154117100d181d0510f511010403c40d000a0005543c0102d40c88010883c030100c0312070000c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 358460737 1250 358459487 358459489
    0x30918061703030f041e0807060e0706050a1d220c2a080702120601080a15140601120e0d020709050108030301080d0503090703060501030819182102040507110c 70
    0x2e0004881000101d83d61001285c0800d9400c82c000300359211000d800520003080380d030317414240e410400d4115030981c5c66541c001d007521000d0001c00d02404280c5000e500f014258038009080c40c6c000c0491410301303540c1c1e0140040c03a480700388100341d610402d12003138600c03a00c034030a201000301805100303840000c0481a40c1c3c02c0c0415080486c01704c0034a401c000026849040d02c074070300c2d075034014441242d22940d07841401500e10014440c140c0200300d000042c00c500309441c10066070041d1103040e120141c0e85003080f00d10140600050507500a0000e18103081207000c0710b08400000c06001742c80c3d03070300c503c5454510240503500007003103425210741d8001408580d984101480c0d990000780191180f5400c8500c80600c00e900c51000340d03500203108000c031140b003640c039121102140d5080c0c01c01c1d0340a200c00508203c88000b11440810202002c1c6080c0ca0301202011035400c100362140607814401000244011024502d9403924034080d400603c2044241440480500007111444402e29140285603460000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 358461987 1250 358460737 358460743
    0x3070f2601051902090315040b010305010b03031303140a0512041403030705070b0703030209040504080316080601020601120213020307020607120b01080103020f0607170306030c04050c070f0309180617 88
    0x54203180000071001481c49150f801a42029821680610503102000e203040d080c20b0845000724000c400c041a15411810b1587c29202da640070503009a000b00225600d1540302000b1404480d0001502c220024804100900304240c007100500507205e00d890800030501d03818000c20032242da141040e1132a0800c0014191240684c420180c101d420003032041088810084c002c0810314400d1800603d00380000e00014202d81044d14242c0f100d001c0031003004020140025401c0178080f941c10510707254500440000e542e0401402032240360b410082014045480e500328141201d8111641551246441a0300a50300c000840710000082c5518020f6030200b46948502002a04180e582d405180c1c08c5400f841006101040075503080101004000302045100c01e0b00c6000d403424038185070703590910400301842c0285001d5000e10851401050110403081c0d40110345072154410b4030134100081a003001d9400403002c2e0f0000d4410340340424400c00725410380e03000700280c9400b0410703901810850b402140d9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 358463237 1250 358461987 358461991
    0xa050d03023c0c13021605120a030b0d23030708070b0f070f0e010f0e09090c010e0f0a0909030216120b010e0105090a09240b1003230603070f260105 65
    0x2d0012100001e074166040310b170300181402c0d0b4040602c15202c1071070303030390f6103103081e100201501d502e01000c42c0110009038540188040810111040e0f0502c2100c0d07141c2002068100f81414000301c050428200407441c10b20942e81c9081d005000c540e01d030780e55070501c210004800c5840c2503030000240005211140074030420b500380400e41c1e480315892420700b0015104005022560014000702e000c000741c4503a00c0360b601c00d2203806288090022085018009046598003030510f80c4200030980f02000d0139160001c4480886108100100d850812410140c0c06d004031100e144a98040d5240c0209072101c444510842c110710401403e00580c1c2d8030448132261000070300030303a5480140b21011500602e00c94000d041d85034010304400b60400e44010f038200106e11240e0001e00c0f0035407100960b40d46450024140e01c0002c1b40c3d07003020f00032114102c0d150000c5109103182000c90b100300a002c9a41078030100280c0d80078210038607429041e9611600a0280000786861031689100c0c242810203c140b03040c000c0d58 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 358464487 1250 358463237 358463239
    0x31801090c120807171c020f09010c022107140402070c0605030a0f0f060609120c0e191409010f06060e010302071b061107080c0a050d03023c0c 63
    0x2540755420052540769071034200d8002d6034900d106100e40c1012a01034001c0d007490406400b0300513030314000325000b100103106810301200420300c1030000001c09000d4500301d4940110910b080e202c458201c1c80001c0c0075103c46c0c1c41080400c5001c0a804000c00d60028000080c2c440c1421040700e44000c03541000141c2c03240450090400c4840301e410403815026102440d0810011030000c20799010b480c2d548001c5410501c0320201540d201e41040159541000900c0003401d601d44a0305a01e00b1161504540f0310304034420129114024000100907000044000268a801c00814400d18100310001c188074401a05e0000c5d0319480c0c600754411291203441214201c60380c94441c840f100b141d250040d0000d4000035416615580384420703105040450b20300c1100a01015140c041d0350107030b04075049240000c26000401154030440d07013081c40f0741e1102e405c1d00481d80704031035001780310a035850200c3c18400c0415614254005420070301c1c0c1c0b42e01d01c2081b11414a103c3c1c1d40c00541c405105001a50b648101d200c800b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 358465737 1250 358464487 358464503
    0xf080f16031109040e16060801080607050a0207081617060f01030b090a0b04151b0203043c03120504030b040602180a0605030106080f22020f04020d0203180109 70
    0x20424040c0242c02c07075854400c1802c002410000f038400850159054460707908000d8000f494220100010380d0200c0700504030030710f030a0780e25604144102da500c0c00701500480a00c240440c0850500e44208080c1024160a40540c0c4045000d880450001c1c1c1c4e203030203000d0380c4002c0d41286600e0030318005801c0c0d120341152090047c85900e540c491a0720481d0103081d1f01010300030501c015020035151944180501c1c441e80304a40021000d01006040b6001c000c803030b41c0c015401122001c0c02641c00000d95040e00c45a0b9640e03c1c0c0315034100411009048849036401c4000c0a6038010301c1c03070448100078841220701841d0802401170b061311084032613120318007009000300360304004500415000d81c041c0c03103200030542c00c2e00c1201c20704400203001c500042e0b200e800050b9001005203c8982e0120309a60045440090030070b0b07038140841003024501c644200c0081290000d501c400a5641d141c806100700e1b8400740c4210340e65103a00c0c0303819010b580b08486410b02003940549144920105102d09264140c009a007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 358466987 1250 358465737 358465771
    0x7030203250305070b150406080604120203030727031e12050322080d02040b220501140304170d1d0303040b1f0323150103031d01110d0f080f 62
    0x40c10361400014120200003060250b503000b080d110303480348c00041c1c41400020200303442d003841e040c4e00c040301410325201150010b10031300c0403941d00b101d8610840800b504110180c14401000020388207050b5201410070001e80c407000300d00c1030701031031800021405800014044a200b050994181c8815501e2590704000502010754006540000002d00e078850541c8a02e040307161041642a60420b41109400120028640b1011150440c0d000114400544002c01e020300d040d0001c1e0000c1007a406004403203000000180421000040d0103111040b131081c580d4540e1704032803405000f0700010010f00c55003c89010312841c3c0400010a5070b109562148000089aa603000302c4079048ca100c09403200f41802120380400000e0242c80320324a20001c0703281c0c00070784c07143c0d4007000b034030b41005d907030415072020035140040c00840c3c2d006500c2000b0b440400710762a098103110700100c0d080004024805102d0040b1821070140a601c094000744003d000d03a0741441d140c0310301c1c060404074201602d08090041440c65 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 358468237 1250 358466987 358466993
    0x3092109050f0a05030106030605180f0303070e0d0c32060301060323040f020f0d02031b010c1a041208070e0405040312050901060f09020f04030605090705060703020325030507 77
    0x8540200d90b0303005481002051381ea000883e0035110f403078204864007901e603002c00c0140c0ca00780000103008c410100003000a040e146458589030b10020700b410040028030f4002d40482e4490b20703883c00c03046900550b00c0780e03100c0d81c465045501c1c0c010041d20030300b60704a40141d00c60311420004508140b107001002140fa59203040010790042c0b200d15500c2d03031088045800e603035210b0480c10071148564082d0b4a8090ba01080303104000044000c000558800c03ca440d130300001580700001c1c81c0c58010308051780d030358400c4441c000580b9401c20054004248440442040c00b1f8135204c0102c150240e4030404106080c030044072805d85200740c003141c4501c002442c40404071411300d0690440c3e508107019040000340303012024424020340b081151a000c0580d112101003003800c0441ca800c40041c0850325045003410390510300614148202e200c00790986171503c0104d00c01c200b0503c5814002c080081c422941c5241e645800780d201c1d00000503200c40c48100c06039030002c4005c0c90022805181d031541d501407924072150307 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 358469487 1250 358468237 358468249
    0x60228180602060f090703140307020102100e0a111302211b030c21041101110102130b1308030a110c010206100e0702070807181512030809030c0604030309210905 71
    0x240000718600c5551b83c0007000c18064207404240c0c4440c1c9019540c3d0340c0c0c4900001e0700c0c10b0001d0015010452070425501d04c1c00341d010480c102140d5003d804d8683c605a4480083c3c54030010012904100348000b031081e40f8508400020440e406060768011001c0ea1085201c8540604400c6601c1c201d0004000240250b6038040081c6107a040815880385c1030305000005034404002150300700d4800e1040c402034031083d0307003050300d1600100c2058001c2d482c0803d5403484c0c103c8588140308001c08820081403081104600c40c85440180482ca02126110030324803600414094901c4880c0f15180101184601c040d4404594603115454030004042001e1410b00d00303200c05840200f8590440c0074201010691007420300100005102c819900c1d907603d0403500d900f00846113100c548410300e01d050042040301380c8401854161151301420130000c1c0e0f035910401203086206541103060217024940030081095010f40c89280c0040c054100e0b2005000301c1c4241c141a0070203004610082032038042c04001a203070813 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 358470737 1250 358469487 358469491
    0x2d1811030f04080706091b0e090106080c0d020a0504053102090606182806081509130803040b01140d1505070c02090109050601180e040609060228180602060f 69
    0x28110004140c035054031550700b00b64401c401c40d90200f0041f01c007041808503d054007034100d21840300030072045203403010080d0783c1d841c0c0010690054400c001940190350398074040c4401404007400604c0700d4a0a01a03803c000c18002819104030140c0007a04419950f0f680c0444031495030150080d2040e07102d420405c01300b9000300030712200c92402e5410340b515548503800c1c0d0200409000e0040811f28144400c0052603e6254015504100c211420000304101d444142c04624205a86240180d103030740c1d0b24a0300c0100c40450142142000009000810000f1200a03040b103c92407107045001d0805001c005c4000c42144000d4110007562100301e42c4141355030712084e0454030b00d0810840c103e405070701180244000741e000b120503640d902c041003087d5070080c81d019a041c58a1080001107424081d941c0e41d82c00001e04050305c040d50b501960002c000e01541110080304c401e98042040750303041d41082415150707801740a80000c0313040d031580101641c02150313601601c135981c01600c0d0942da420541d0302000c2d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 358471987 1250 358470737 358470743
    0x6050306040b030307061416050706110903030c03040302090a06060e09061201180b1e0c030a0b06180f0a0510030e19140c0109030c2d1811030f040807 66
    0x9039a0b10541c49a4007000140419880f5100100d0344000502680002010082562a08640104107201000d030700030304813251a580000001141042d480c55017603240141000c03503806200009030188060340c0000a802220310840788080301d40e803101d00f081c080c0ca280740304000c0814a9003601003c2490b042c10401c2e4009000f4003614007000c05145000d003900d580c0c42c0301901a0903071030310300801c0c001d80048a40e4000000503a4480d64a00c010805a40010017000f644024101002191404c0040d4100d0700341c148000b030006468503806185948500110552103104102c00300621030035040a0ac0044200e078801020b0010070040680103401515440240d1301443c0104074846c42c141a2006402103031600551001980030013441c60649002462a01c25062002c2c0d01c1e01000041c800303200340016101d603614a400d03484000c00c0040c0030100007112003550381244074404154548040c1200c08411181032007444026900f4240355694881643c020301750101239000a80450300c902e00510345244 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 358473237 1250 358471987 358471991
    0x30115030e0d0302071e2a08061006080f040203071502011508070503070905060916110604150609090c0306090804081b0f030303090d12200d0e0a03090605030604 71
    0x3181403482030800d0042c041c4040030070390100304401404007524103480480c03000741d4000070701c01d907503154040001c0820303114a02c126840d01c0600b0805081002080050410300e048501a00313040d01c03044821080e5000d40000502c25030000b4070030034bc0e6600030600079030300500035108140c00c0c2440707075011180407200c20080d5074036040c418840c1c0c00c0d0207601c03a00500030103000d0108241040d00f007504283c480e9210800d054204004c1c010540d940c403d40540200e0302419124442c00c01d180b00350b075256800c030007401840c06000c0401c401d01410b0000000c4001052004220654640160500b01c4108010207460896a000e091001800070785c0881c03242030003140464240b5590345006803800300b078100b0805600c4000c40c1c1e0035005040c108450034504101720b010b075065243c0710070707600e9680390814214020410400b141c9003900c0e00550141940c400140c62407828001c0040c852541d951115011008003441c0400310381c104000841c7e4004010390694501500d1860003004407200c0d0006002664015 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 358474487 1250 358473237 358473251
    0x5060906240d090b01060903031b020f18090105130b0c09010e060a0c0218091b060c012a0804030906050325080f010f1511010204030b010f170309010503011503 70
    0x1c44410090100e0141c26a40424980ca00b45403d4152000607032024040c41020710050002a8000c815406141e110f01e55041424469000040d0301081c1401d15a4200c081000d54030b0b0200c0348880401d20540003100240402e460710251102660000c0c80c0c0604040340c103001041c1c251180800070803801105141c100e980c000c100000035a2580641c20b00c0c0e000c01c030301c0b842010450400e10200705080c0e059140c0440b907407400d501d03d44e86899010300920304017200070040360b0150791414290ce91014850000f0040000401c4664095081242500b04003441c0c100c12040c0080c40350307824074491075069a400d0111032070040240c50355040589000200700054019448481c00e00e841680705006643d81c015031828464224607445406030001406000d4481081c4060751951280d408200600c1c40d01007030304020203010382c0c024016500f0080c01c800380c0800004800d8040851442680e0549007410b030008401e00c21280d0783d00c60030580c540800c1042c80100070204d14500e00302150849070030082030701 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 358475737 1250 358474487 358474549
    0x919060504021512090606030c100e04091e05010e0c011718011103070e04090309270c09050310020405030d081f08011b0203040f1e0f0605090108060405060906 70
    0x1e401040001395400d141d0820040c0d000020010b00e5007100c0c0540160440b03c000c200130913804644020380f1020b1044a2074154580d4540d940000e0100390802c1c0c1c0c003c007520036a18102c2c0c4000340c125082e50f89609000b0542004031002c9440c85001005840d100141e04041c0f2a040700c0f600010300d00381d41c0c50321100030803181d84030038001c21002c040c0300c1c540c2607a40e181400d4040e00300c250800440d40501d00d000000400240c00c103242c4e81c03d44100c103105140040a01d0405d00c0c210742c5000c1c02006180c106040c0790b5007103800030003440540c0d00031410350713000f0740c1118401000c0303008038802d0030350552011904201345805001700503001000c08030983c04084803c1030418062895034441c401c0c076950b9112401380e0382e040e030f41c80d100710075002c0c4041c44c5000d07d0101d040c80300d041a4013404500041c41920860003000b035568074802403981468001100d5940c103405001608041c40e0103010030410302c000b611a00d468420700e4405c00700100160203a88a00c410f2007a0898903400d003a009a111070800c2040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 358476987 1250 358475737 358475779
    0xa091a0c0714031c021e0d0609060b13050d0809030114070f0201060e010b03091c180b1603180f03051e01020f0301030602130504090b0906091906050402 67
    0x800d0034004a0241d40d009186004901000c028111514a0700180007003030841130040084042c3e020400000f684500414105414007095504081038109002811648441c490381145080390b10800040000b207664400002c11485101040100642c0244080c0104d140400301444120700a0384031508207045030010908590028004c00f4980ca094010801d6242e401034050000049601c003e11030545440d0b020b00f20101c06018000d10fa000100c00a1540c101c1040a805100b6141c601c03210a500c0e4104058400642c840c283c50440074117a0020035014405412a2917420210003415801c06054a0854158194002d40005002d501e00d00013011540484418055401035010b019030030812003a05c0f00c5224a07107900c00e00f030703401484114603980100c01070340e0441c0c0d0007003005681c80d090030800c1c0629815035000641e20906e050110403d20108040180c82020b03548202c55241c0c80300360340703c0d644424074101600d40000c01c40307410002802d50b80000b900180301810008206200c0400590 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 358478237 1250 358476987 358476991
    0x2105190318081206150702010c11030a14062802090103090602040810050f04030903020904030903060c0815010e0f0d1106030c190807090b0c19032c090a091a 69
    0x103901c600814a040c3c410040745070701c2c1d00180704641691201c01d41d940c1d8802c1e03c1c01000300103810300001d01015800d03c01455030740140c204005060f6403030003810740f4110060300c1d1147c0c502a002e20036100011844842d41c603902d24002c410352000aa00e1002c1c800c41d4010350b0107400c415040580300d4001000282031030020744007410f00d40c8043d00811920100c8242100c80007001c0c00c08000006007408042504002d4803010f807501520742c00e02e01d6840e03040680341000c596000900403860950000e00191b4803813007050007241000d015407943c64005004440d491807021102d9484071080c60740c0665860041c140881883c494007001070201c0c14403002402a4004844807840c1c0c4000081d10b1700210940c1c000220101c0003800e069070b940c00c01d4100241303e0705003401203040c1c0c02c1000690b4035074641c1c1000208610751015020b40c10b142c20500e4014041c080020001d0303170000d0307022140300d0441e0089024900c0c002014060010550310f50364020040c0a048105a131140300303036030f03440d614851030721349040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 358479487 1250 358478237 358478243
    0xf05070b0a0513150f0f06050a06110f07080604020f030a1203020d1119030b090103030f0815031902130204060507060903050c19050d1103030a0b040605130501032105190318 76
    0x40c200300d05d080303107001750340480010003003051800600388582da9031030401d10b05445003480d121100c0d11096100510f0322012440208191061040004a49a00141042c03146200360764210340d1402c4d0305d040c9076039240ba03402d00070301140c090480100018403030342c041c040410308810003083f00c4041001101207507100355540400e90f0107181e400c01403036400d406220503980d029034400c01e20350b2668600521581928160208100d070800111b1001121350640396094000141501c05514036072200903656500340c04124040c01521408141e141c0c005d20945086800b80d4a070540341031060354400004251240d0b040f801e000052142c11101802045071800820507072881100184090404500d0000814854800c010041c0c9221080c404040107494000e000e882c030101e0f036010000700144c0589400d0300000d800c54030f1000c1d0404540c1040d040103040368040c09030352600b8001e000f0f1900e00001000000000700303208010241c3d9942003004106d42c0b840d030500c1d0014000c92103000c03585122014180503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 358480737 1250 358479487 358479491
    0x709020a120b030d0816030209060d200c120f0f130618140409170c160e0906011503020c0607050c01140615071a090d0f05070b0a051315 60
    0x76507903030000d1207001c00b0008120018100c0040d4440f0081c00001c0040c8500c40c44443c009288011a0103501a9880f040c0001c01031501c4405105020005020480c003107080070030074000d8401c0c40c004800490740742e41491405400018030000700c0b0f070303625408807038120000c58003041765420028030b0101400c0000c1c4c459240ca80101d140120040112021201f031303600001d81c88000b000401200307046450400000d0302c0104940c001405c24220605000e481b9000c048400144089000e001151911101040c0f0702440403064650842d40030704e4900302c804154030b41c001401402032080391000d00d00b203860180341c0945041e6061080074209402501c0020100c0c2002c80e02130010802030003580c181c4100c4040403ea03e240800001c0c40004d906410080d46080014502c0144880790540049140c036401c44034009040002d081552000209000300c0007685031424078018030f1150781110296500280b050903992030390309a03000103110251800410003c12300941002622110440b0b60130181b020b00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 358481987 1250 358480737 358480757
    0x2e0501030b06120102040f0504050c070b09012712080402060d09210503070e0402090111030304080310150503041211060a0519060506070605040c03080c070302010e0d03050909090709020a 82
    0x82c49064a035021a41c200b03a4010301040c800c587d220138003132040f03400446021a054480c400002c1e20b41c40b07030060207403411a0007004c0000c2035005400c81d400e069507140f003011000484051045d0240d502d08002406204803408914800e80700391503c0c3c2c3c20900080103e80707040d403094070200c00c50315061401c03105e4180300c50140c20707200e55000701056030b01d40ea230070060301e5407800000c0108000f10000c6081e10803a40842c0c03808442c0d100c0d0084c0101a0995000c4958905141c200300b03116400441d04084c1190100201043d070050420311340e040601c80f0740301c4c0380c00c6890740e03520a2000780c0300400000401100500307104207094100328190007601d24020014507410600d07541c416900d8030a2000c0e08850400306c00300301039140d0314100e07085a90441300000d800c0e1624036080c01e030f0038066800a01141401702e40e40741c802c2ca010621000301d038800d880d8000b00003c03400920001c001e0005001d00482e0060000103160305140e5907141e404003668003980d18031034981c000b210032a0401840c050001d000c0e031f20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 358483237 1250 358481987 358481989
    0xd050c09060d030e0d140709020c07080109230c060406050904140709090e1c050c010b0f0904060506010201090501021809060d2a030c1706060109082e0501030b06 71
    0x3220341c1c100c481030b10a107141840c1500c0280000c10107448280c06410855007410602a400e25050560307101c20041d502070550710311985019400c0107603000c0650003401000507200c1c105100f600315041c0d005ca42e0518041d02107039424482035000d00d42d102640110b80b2401e62640d035a20040c80900410b03101d1645031641002440125a0300c00b51440c1d10607030b00010f01c103070316400030300300d07004c4503d03044020410403012050b1504140c4201104e4841211603210131708100e0b00310001e0b184490b1080020032001c0d01d03101c100029502c0140c0c0f81908411600c0204003c184117411031503201106000210b04114503a40702c82c00ca070300202411100c85581c844948062400c16160340e0400400c5070304805080c4141c03101d03883c0c0c1504014008400380708810103170100007042400f41c002d5800c0045d511041d69100b19842117942100741c001042e01034400014515801000c44c02d069802c1d54005103a001d40481403103a412003100c08099150910412190001d007440c095503010310b1081201c0c1d206410300c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 358484487 1250 358483237 358483249
    0xc0a0b190b09010b1815040302121218030c031005012309064606020d020a1106040b0c010906050705072013090302010e0708210a0e0d050c 61
    0x100e541954604014100ca01641c480d01000e054807181600c04c0e5603091107150402d00350301d150740300e181c01c112a6820002c80c0d04190019100b140d00030341d00035096051200a075a15180104803198a041d0b09200e50342c00310346054070311030b01c921024041701d10140421002a00d85400b291070039104a4171a40103201c04400d82121805120030700300c060340780141c0800010b9070440c2c000e0207540500c810b0801c046c503506c110400300c41d03241c0b078026a5011142e00b07403c8820300070341107120000814515480000b002440000c1c1503484143c15405440a0401caa541d0080e2031318075403805a224500b0310020520848440007404d05180d00000040c07542030358500355003920030041404092103c24440c00c0041540c2207490491120740e0b05524001e0050880000c3d000009c400c3c07200d600c186080c0c1100209030301580304031041884441260071069840c160203580701d509101c0d80d41035031a490292032400350060054054413000b41000003510248a020078007c00350040e041e0b0b01d030381c03000200c40c4003810700c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 358485737 1250 358484487 358484521
    0x4170f1213020415050306060607020d0b160e12030a11120406030e0706030507050d0b040f1109031c0c14031902070f0b03011a0a02010915140f010303081306020c0a0b 73
    0x416544c0c1c600e45400002600c600e070040640703018010000b1070808542e00c0c0413880d245154050b400c05554105403000100d0880c01525945c0482c60307030745e42c04c2c00528104454560461408004601d080c8901004403a07072680045030701c4541c80b9140c504040700c80800c0140010b84029500041c0c6088400d17843d03803400000382d0100c4245031600b024862a1a440301c12a03030358500106c0085606c02403280440c008140c2840191a013a107444400d983e402c52070801800e0118048048500a80c03140d42003641c41d811017a10040400c86c52200000000c0035041c0400c0c15400710400d480c205640011581d041401540003080140c01800090256081568101025020030941c0d1400c56042070f804015508500740d200311542c00c08141d85004034400d4102150280e80041000c1d920422043d00102401140c0d407007030490b120110002d07007190442c5100e68100c98155440d0107454581c10100243d40d00d20010540b1000c1d000c0102d030400c20406c00501c00524454015120700e454445c410440390108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 358486987 1250 358485737 358485761
    0x317070303050f160c080c06040308040204050609070e010c050c0904030302130b030108070302011202130f06030b010206060306071407170405011209030f050919030f060b060304170f12130204 84
    0xc1101480f132104520441e04641d81c040e030420840842045c1428800c501480780d40c40414840c00042204050748194054092882a10144015200c0a00300000c50104450800004030104024080d5611446480e0302a40c000c00a540c058845100411083c1c03508880c1a07000c20380008001c00054040b00b000c0000349100d1581908650502c105542c0b0783e0400d100103410411040d07164143c00f0361b194100d44c107192444603101b000581d505400d06081c104d61040002003031401c2001480c1e5400820007900c5044028050301c516650394100313480400e0540d9481c165070b0414020080080c40000387c40034114100d19420f6105c0745000700052004d0941c2c0603074640d1a080c8921200000d030086281040b40e4a2030911985421040c80860101003410300a1241c42088140020500040c01c80300415103000701814003242c0500e1042c0417151206540082c61f240141400f40154244000540310080d520b4200c6031030402c549400c040100020340b030864000b4484180c4800318500703071103100b500c0b00c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 358488237 1250 358486987 358487011
    0x30f140604080304081809040f0507050117130c0302030a03020c03070605120f0601050903161e0f1406070b240406061709070305030309060f011d04110a031707030305 73
    0x240590310b0704101d02019100611000c070100369607002260f1002c1d07130344c4c0f10319000d00300440915250030035144451140d141070348c0902603284081801e500c03c60f00d41e2919116088410940d444000d84180310052300c203070503580c2d00050440403006941c280400e145031070096004208164007401018204421640481d05008003005507030100311194040991114403815000c0a41d80d6490058403c1e1140242a40e49130007000080384034416812009019a03c10072028802c43c42c0f0f8002c01c03002c10500f4014081c841a00e62010000c0c0c0e45410032181c102e0b03c0c042c210130704000f4a0342c0d618240c2d0400740c41e4042800c0c0c07a44003281c014007400e01004101801100c0a00031140341c640047c15035958001842480400319001841a60040007610003c44e8031008490382c81c5041c4400c20740340c0340140e0340140072000640000900e03200c0c0a003182c02c0324005010340740907070b103130780d45c80c01d03048010982c02681204c9100303400070124015400f03020b03038032108044803a0340c1c1065180060840f4002410700e10042c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 358489487 1250 358488237 358488241
    0xd0501120b06040207031110020714060105030304210b150112090308011e03050706050307020f0d020304090f1d1c0507120804030504090501061e080f0c1602040204030f1406 76
    0x80e10700801e164200c00291401079685085050880b2040f408000190b000e219000408c2c1c1441010750040c00250301900040c400c00c98410410340d140c0c1428860380360b16900070b02c42407142d45140d144120829180b038225152164035561400d1650340d0071540001454080703160f040030380d41c004c1402c1e0160100b81400b0028a803240d54040d00e04001801a0700c0c10004145c80702da01040b005225901039600402203900c03060340ca100041c030325032040342e10b030b001801080c0c1d200d1200c02000800740000311294014600349810240300d200141108064212903949608a0354000b01c24800d6401c4446c4103400508409a00035101111002c400c44122040100412550002c51950401d01d26810b55524052805441d01c0c20112160300554000c071000500e07000c00066180e4120445100c0800c04d600850200a4004007d50350302c1001c460b9891440052000a9445c2d0b103560010807541c800401232418a41003500800c049030800e1f081103990030150812001031098107005105000c0002c80102164 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 358490737 1250 358489487 358489493
    0x15021e01060e1f030803091509010204060f05031003080f0919291c1b08150604150c0201120e03090406050a06020a03030b01020307060e0a02041401210f0609080d050112 74
    0x1e407011310001d050719101102140000c0c0c020302104044029071041c01d0024280102c00701c0c000d60003442a90040b50ba00880907030418028801c0d41c0c4205071080e000c0c01e0040c50740d2141c00c4594070400e00451201c00400c044503065441e000080d11b0b0400d00b40030746001c01d0a1600c1700d3700e0b60441e9a607040b00700d00980300b0158802401c40840701081702c0858521940300d11410500084c1411401a1595114040c22454440d5001c22040d02c5555079881c00c404028208003400307454400d83c0529103582040500c02058580100d040080c007510602d08580003410000ca800116401c0042100c3c00b5040051404260314040c00307400d000c1d20f001c941240703c9921b840006540c1d9458400000d05044e142c81110034180c0c020700540300300f0764200c142409101407190f0202c1d180c0000a408074820351528040ca0751240c00c602d0f40d6416201c252507000c4007019540c40070906c907092144200c6041086203815400a04d5a010b0401441d2003901001d40703414001c4000e20581d5016049105070b4251202c411001c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 358491987 1250 358490737 358490791
    0x6020105090c0f04060b04030b0412030b010c06051f090c031a1f0e090c0304050105070305060f060c03070c09050105010f1b140c09070f020f0601050a15021e01060e 72
    0x2c01d420499a1081c44040d0300003040c0909001d0b4429031106402280003c00d0000f2255014881d9114120841981100c510140c08075809004403c1c0010b409000c2140052810340c4000d411595080c00740c90902d4034400e00458407102d507000201015201c03281c4200c204d4040c001c6a60b845111041c200101080e0004104d41d02115580c00d4042003600c021920b2242c018601c0088038980500300d000c0910301309054400c15070003030302c0031500f0350304e031400082542d4402c1c4242802004000c1c281c0340040f0b0b01804010250f04280304042860004201c1240014010200c81c00244840d0001050769031600001400741e00c6580028828000b914400785910301e0704032500d03526958014400c0c0804440c2c0d00c289440c203040f441c00c0a8001402d8024020f5a0b6000605103c1a041d1a4221501c21404070420750302c0312001e104a80d0080b003c0721050103d04a030aa58611005041c0704960142a4802c10380a4103000034039034070526556980c0030f018441454031650340c420290074030603504a403e00c1401e20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 358493237 1250 358491987 358492003
    0x70e0f1212132c060d0503070605060f09041a1905010f080c090702060604110405060a120e010b0109090b04020c19020a170318031c08190b01050a0c1704080d090602010509 75
    0x1d954000d010016403035a480d07001003624660040c00321fa807602e800789003520040105480c141c4c8642800c109480d01d5140100045205592081c040060040342c400d140c01d201c180a8940842c0008c0110000c45d20341d40d03031182c54020032203c1d054038045031604600c18242240c842b8254080c031800000c100b031054001800701c1d00002d0550b40002e0601e20300e07800102600031034020f0b5600041c002280e0340740c958050692280043c40600800801c2c610b580c516003201d4072140c0d60b5000c110091000c00c0410440d03405604020406040540340c0741c03003000382c141802d002c290345c0c2e000782c24005900815410422040e10281c400c00440a4544280700c242940c2d81c012a251007040c90354460404009413018415188030b020341c2d50782c8011180c0f580c0b00c05020345070f0031031f0100f02017200c188083c00c41d208030f07000d11810380e04180c41d4903140c0500b070f42045541c03100b03d02003910111a50101426120100002000282610380c06410311100300540186500d4903940306200b1603051100303210b0f00e200b010070004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 358494487 1250 358493237 358493309
    0x20f0d0c0507050423010f120f06150803120c030f0f060a170c460302030a0b0a140613022508070506070503070e0f121213 54
    0x10500d100c141c038000d4509000c9400180d000f9040030b50305d002c0c500e074181c00000b1624a104c00704007a681c0700c03800d07030698000d548541980c0505030032103c008283c10aa48041c110b025801c0407a03c24580d42d0b02c0d841ca18515444030340e032039000061402e54044031000300c0381c0010201c90018954142802c1c500206000940700044a6032480c000c20544e50f2088c0d10320004110000c1ca6240001e10004c605454100003081c00d4003034011843d80010f0b003c07102050841c55106041c0c3c1070b005041c2000c464011b0b00032940300040b4181c1d058804030150740c0401c20002018401c0d2a10082c07442c0c242d5409054401650302140695881024015070342d030390200e40545071403990001a11141c1c0462941c1a90b50400c9004072804049841c07201403001220003488054002c004507846904d584404a640788030407200e0b080003680108034410311785814010640101002482040c400c00c0c3c0d9401c40d4141000315030740d801100c000150070880a20ec02c40520020061000d4010b0340381c64644210380c500c241c081d120 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 358495737 1250 358494487 358494497
    0xc02090109020f090a03060e0708121210081207060b0906180a0902150a0917060109150e1008010c020703020108040b060312030a0213050a150c0305210412020f0d 71
    0x407008580c1c003041d1101524018081755440342e490030140c0044c0000c04110b20a8041c00001090040000520244003450500b00525009900d0640d240d207041c0948440e05800b100200099210410002d0111a803144103079544d030307006d591600208541e800f0101500840b0700c0000c01c0400d075524540010303e040c240b0403048180d070b00c1c0c80003140100800c48000354002440c028500340c510500b00641800759041c0c841c1a0656210300c254074140403d50201e4000d6030000f00140b04001c00c50304410104403100b084206090344607440c904043c1c0045074006030fa0078042204002c000c5003400303004080e0b29a4009000c6180c03c43d000200b03440d000802c05042080d4800100e002f5403010841e00c1907042c411a1600c0c4c503070500c02c05000c003030352003509100c2e020301d1a101d01180781d2529019000c105c0c2c0041405032148004010b06035001c182e0340c03a05405000d002d10891104200a100c01002e00704111407040161602d89030030703d0b08014049009046602000d01d10442081c0000e00078141d8010f4101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 358496987 1250 358495737 358495747
    0x1080703090312020c03041d04020d080921010c090b0c0c010503130c060804031d060a03201303020102071421012007050d080c0409110d060b070b01060c0209010902 72
    0xb040d10141c40b28000c0b03403c500e00c001441421000040003070300541d44030b58101380d800f1a84a02d140c1c0207040c01d0f0b46c060f5100d04010400e41c006220000100400c42c000361038000724003000d1001c00d8840309070b481d001c085a5102c1035800d0059074421112400f424000307140c142000c03904c0484a54403549411701074140100080440e070b85013440c3e0300000c87d071030b40040224201030311290000c0021209503421004a403031691401d94400c0444032840e19040301078030342070402c401004c00711702a00b00b005915589005400b40101004940002408400076618100140524500c0024a000b16540c0041107043e4100d400b00300136955001d0b034400e01040181e860b1701605612500381e00400e0710114a05140c1079107610300d491401408050000c160180301a244451f1544005844640e401c45100705520402c00080c0080d52a0b035000fa629130760030384101414810302c0c4501d4800c486031a044100b500c0408039070581000700c1115018050415450280c0c0c0d031070900c0e800700d50784403010b0080d88591500414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 358498237 1250 358496987 358496993
    0x10309080d02040b040f0b070b19020d050f0105030706030b060405040c02100204060c0b09011b1d1207030c15020a0b060d1e1103030a09090b0a1a03060913020108070309 74
    0xc25a5034030660030310304658035a5655404e2829034030600c50342d612164400c8001503542c0d0707441c050b2580b00e078202805400c0c5c0d40e55943c01c980075940e00030b2406180c503030074001e0380c900c41c249105203442160303007401c1d0408239410201010f10b00501c2c3d6018204060a10225a8140e160303c01a107045030025200030401000010302a0700f042d001007070300708520744081000100ca0b6406080d400105014810703248803a01d0725605e0b02c0c20384034088402c2d4842003002060450b00b130f100e0300401440e441880c070540f40280c61000000c8820082040d10355241d8001c41302842407000500181c1c2c02806241100300c400310840001a4542c03103000e9000c0c0ca10700d4640001411502c860310b000795115808040194019226074140d06001c00310b00f02601d81010320424507655050010407519150b00c80e843c0d05140500d0a1818030103445c5071700f401a08001210000645d81045400c1c002c002869821050740702d142c1482404984807004012840181a440caa0000350340c1140ca007540140b4589800304400040381 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 358499487 1250 358498237 358498253
    0x30e060307091a0d0f060b09090a02130308190201090c0e0907090c03020705070503011802040f0219050301090b01050f25081305040501050a030b1311030304090501030201111209010309 81
    0x150041503400007405480c1081c005420042c2000344c000320341000649120002042203c2c0c59014400d40410108400c2c0c00900d44800f0055108056440243c079041c40c00095040f03185080c0d00882c0c02402c007141003414115906e45522080525100030131244c0003c0e12000002055480707401410001140841e0400405118500142256800900042d080c0b84c800400a51010805807100e00032040041242e140600a046032507914025543c00e00c8900e808020044c401d080030003580550030840c1c21540005254aa0b221010688420303460b9031405580206682d146d1010b6410004200070b0028244011015554140350b505c010440b2000d1045c8000c04142e40101e0140c566400801e40000340781c0c4a05d0058141d501c280d070284000e9031303140c1c14404080500c1c0030085c14043e00740c00040801060407052440750f4050551541015200d10109045030310a4000d0340d030329900e4600510039941c116645c05481d580d42c3d00240980b05121031800154020301005504164940140740c091006030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 358500737 1250 358499487 358499489
    0x8070312090b0a1a010f0509240c10091e030e030f010c110316030e01020709090b04060e0f0d140f13090c11030a0311040e0a06030b13030e06030709 65
    0x4088204048521400d040714140b400319110000340d810407801e003a04c002101041c2c541d020045c2c440b01038040c02c0b410213031010382001021030782051400007090300741c10300f460201d8800b1030068419030b51000c18001250600e07168182030841ca41c00c0a003490000344c803a401c0b0350400d81080c4000d42c3c11a0f1146001c881685039070006950500c80c05811003d4500190700445122016032035051324542c5803e80152203000d0080078114015034020144c2c0824083d100203c07240304140306035540741d52107800c0b101c12141223450a4454018800030001001403134400d41101c0851a801400d210035044081c0741e595060059031010407851070440445581c0050507529214000c0f15201e4603001030303406142c0b840119121b12018181400501400c40d80207144024421b561840907510b00182e071315042d00500282103040c103255a00b084002540914004194058180c241c00820b83c80e240d030070942c01105c409410042c01f244803190b400c2c0040c0d085010006140c0d03050b51360319245d40d01d03c070742a03c0001031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 358501987 1250 358500737 358500767
    0xe04050c010c030822052e0608030405040f0b030609010e100b1e01030204050310020c01050f010509160c060c0c030e09060a090f110304140d051e030a0603050115141c080703 76
    0x60144110313140c1fa072004101d4490919040310400040c4e0b91a036401c00d40e11039114001940d08204002e20035414950041b0b0071203103d586000c0391440110380032920b0201c00b25091922655a16240042800180000e00151003060420300080300082d002a04501030b403600305200300c4aa41040070300c1d9000e501a140107200013001d82d800030001d101d035200603600c07400c48440954030780400940300822150005050341d40203000c852207651902105005060501d80b040c0910600f400e169000501c0342c06402c4484480703603190bc044084500e0040c260b40d004502350b900c41d4645204000064880181241c100c840c034680210b11024541e450000801c64004168607956000040200307004503401c40c804121590300481d0007112a802c4112034034040e1003400035180e01c0f5004240c001c91380d45c10140da00a4a4000300240240da60b940b06030031600c49200d00d0080f03034640c2c0b800700509201030030718065040080d0346519144464021810062034800c0c1c00801d0400d0204040090600c6490751407140c140c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 358503237 1250 358501987 358501993
    0x303060f0509161e0903050610120209130b0a0608100b22020d0f020901080c0702010512041e0302060a11040803030a18060f27020f12160e04050c010c03082205 70
    0x503501c480241281741c1400141c903503120b004085469140341c5e41da04401c45207115006d003000e200030b500708030111101904210300c12403655000008a02d071001c58901070301c001500090a40d2030105c2850500500d4500080c9452518982007104c1d1590503401c24090380c114040039900c2c0d07400d03107040001d02541507414522031070445241c8804005074010504c00c1c8090b220a81169030300400905c00f4454084000d0010b03a0502013500d0303401450401c00d0b00284120041200c107595031005000070f014000c0d044d001a030140040c004000b0b02031003499010301521040d540f6142c00c0044190b070300c2c0320141c42d15100d9581c85e02040c0fa440100752065403400d41c001414440201c81c411000c014003400841050040441d00104100280c400f101c4501e860780030748800c400d03145400410007040404490009540a465078602c16240c00c802d0540182045101744009420a410901c0c5000040a1040d05100300d10030302c080425007000c1619403001c3d07040c1c1501d01c02402203040b01c2e00080c9040e001000342c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 358504487 1250 358503237 358503287
    0x9110408100c0809030a1409061605160506040e0c0a030b03030403030c02010905061204030807030b0d05070e070309051203060105040e04260406050d020c01091406040303060f050916 80
    0x3400d607040070a08440b259658156603e82984440c2c40b03206503640c11011a4000402e65001840d0401501d120f0800a101900b00042541d0005c3d07a03c0d00841c003181c59800c0300141104551041c0d200e94050502030f6022420203040003540c3d21485405032820b002c40320080b401c5083d4520a4020710000704028081d2600c850b503c0c0360140101585c000c0481c04a0354000011480382403e03400d890034030440c0c0c083c9800d0394860703031416070300104041c2018040603140c0110281548680e50b184034901e2144001303140041ca000311000d20f40f40068006010182085044004980c00081c0e2000c4400007032011680d9880f500c0040e6002e201c2c13035007d003404a580d0070410060008044c604114410404080800c07005141c12286452003140610000b0944c14814000d03480d01139805440404051000000d4604440e03c405420341d165620801e030560005c0d040208055041c000d10005203181803c4100c403505200c002120a80001e141c1d0b0203007903541c000b10303409911420076460b10170840040c4094007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 358505737 1250 358504487 358504513
    0xa020307030c4217010b0a1706030319020a0c24210906091a0619050307060c020301021209160b030105030304030803060d05150a06170709110408 64
    0x45006442001510514220b45207408040d2070f0500190845890103e80340084900c10300803c14420f804032401c100c242d42c140c14103444142c242c5400707040c80d242e100e51240c2c1071160080070120034100100202c940c50f024040039031000001d907004c0481e4a0903016446070346000491422041e0030380070f0034103040d001000500c0b008800c0d0b151860071141050080c140e11280d016030304040081c6d0340c920070030140942e410001180b540200c03156480b8103000315125600d5116920340104644854464030206d00a000280ca41740c00f030b450070301440032003215400d8909000661103000c03a2103000103000070b0901c0d04046542c04c0d0304540c090800300006140703d081141c402982c80c0c1c6128540c100d4204404000b10311120751400762812118002c000354507045c1580c0d80e821042d00041c0003c0c2e040390000080a00040c0c3c01d004541c203008212800c8002e9190181c046000c0c1c0b1460351005402c000f04c051a100e65010100d449400d8655140b804540ea02103100d450140744555130000304240a03a00007a42a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 358506987 1250 358505737 358505753
    0x50a0f030905150a0807081816050906090906070516080a030614010908030d09050c060a020c1f17040510240603020c0304031104110403060504021207050612090a02030703 75
    0xb6241c0a4511401c034032000c06807a0690b1180c0289034000c07500d07410008000500c11100c0b9503010021042880d50031140c559900e19044115003404583c050b0780c0414046400e01c0c1c05590351015040725040428103010702040d842e14005807a0008202001410820200c804c0107001d003465031200350540c1d1001320040080c001c000501a6541c3c1042d9480030b002290721848000c0243da071060051450f240f00c1130b0591000b0103e1442c02c07210b9000b00000703140380d540c8210103031410700c8264014241d40c0350f0303a008210200c008040c001d040309416800c07a050540c0d1012019800301c1205179240c3d10b54075207042071454400c6038580c0d0301280e070515141208a040084030001c2144805c0340248489440381800d90590190600b03441040c0e00510042011601d0042109504000548005143c081e059000c0a0030b0b03000b600251015a01c1c4da041c0400c501705034180d544000000000f0701001420280000c02c1441958042a100c00c611008140b95034402d1019020540c2d00400b00c818841d035034504070391 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 358508237 1250 358506987 358506989
    0x1a1b010e0c0303030709060e0307240305060301180803060120010b090f01051f26191b050d02130306150f0b0706050408090409080c1612020d050a0f0309 67
    0x180d40c02010788000311810000140e900500c40c03034445451440c10070000300c2e001f03224400e09a50500c11414001703400c60020000d0310720707200c0c508019660000c511a020301640d8025100b18040c0c0e03d0520102101c91a03003c444501c4c0780e2240b42a039030f0351140001220340070082400c415241c0c8641070100702c1e041e0b0540c4800768541040d1140303e02da5030780d41249484070900b40726290300300540e1120280b050081840a8658501500b131010603080861514891391449040100e281c000385402d00c0101d20700c1000d800b080700b071002d0302441103889507034038440c0e00643c0b070300da403024400c020030f00101030105501a09d280602c186800209151f0300d08114005d410380071125144d9006a46012a00200010256050b500000002803420311550740340ca000340700060041d03446840c01c0c40803004550321405180c0c4042e010700413058403491020903007030500703104140f2500301c2d032214002000b4105401342604e034040d404640c049030182003810503c2c02d10a908600802c42c0d904419160308250b0002c40c454 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 358509487 1250 358508237 358508261
    0x301080c0f060409110d0e0615030105071e02070305010219080c0708031314011b02060c1204150216031106010501090e04060f060510030f241a1b01 65
    0x154464a0203400c0c09000129141219040320041005225001494100d098200d00d0448103a1503d002030512004452040c45407404a410101c148806002030110f03014140c02d085000b0030840c2043c40c00980900c407000e013500e04000000f00e40e0010700340244071640003590008002d43d0349068081d500c031440c00d40c1c09100b0307001c01c4080c404a0310542040c810341d2300e0590300040b0949180c803584446407145034294411a1855040144040c0d4020280500404501c2003ca803038241c0421036006410302c1c10040c0301f200c20034020b0106180802140008036040340d0001151171240440d9480031010f8441d80d030380f003010030b0300400201041641c0802041c4024900c2010380d01d050347c0701c03401192861094070400e200f17002d0301000b04001c00c402d988000c01c080000d0b40700044040c0d44402140c500360020300448003082e0368510180d050301d1203004011010303c691b1080404400b03407103000076403c00d450049041800c0083e607440803001000b411550240200b042841108200510040c060700c1d4502c030705 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 358510737 1250 358509487 358509493
    0x16030b0a050c09010912080403150509061510050906041703180414061c170d0510150c0302070e0a0f0e2d1507080402120607140a0302190302030108 65
    0x314500040300c20344403881d10503969508001d16146c1e01c4501c58520000c1a2500042000b0002c00141c4410511100c24a03424001c1424640007101c0c03400c0440c0185681e030340b01000080b0704060313902d64030038900101d02810a0f81d01c44a2041c003040c0c02d0700480e0407003c101712007003186270f00b0507100001410044100ea8a0501491008014482036aa81807600214203c5180c0440c1e841d20741014868a4410f050b07a81c4c079000c98030f680b240e0b250940c40184c4040030580018102001941c4c500500f9030003100000c0002125261801c550802285610480c080100e0b820031b540c205442409010006d24800360a4070440c14451010380007486004a941240b510b46044003c1004001c183e203109c0d882c02d4260340c20b11585004101c1c202c8140782c0c204160602860105800e07050548400c1c0d405500d050366580300d10714040c07051094000d11101000c8681d4000410030010980c00714607002c02100000003151980410b0070150080c2c01b0310311810a88041c4901e8107015681d1550195048905410407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 358511987 1250 358510737 358510741
    0x360c0a061106070f0906030209190e19090818060c2b020c130b180103060e0d020613110103231504060302010504140f06040b040f061403150316030b0a05 67
    0x2a100283c0d10b111070808035a0100702081164008d601030700d0010809421480504260206454a0041c0d5000414417149038014040d440014a40a110f11403005c0c03800c1043e8034090f1250781e814000c7d081000000e25521100011644458040e10000f9010100303d40001c031003146040d41c0031740c01e14443c0d100c2c2440c000301400400e10000343c01c83c0c04603019040000c14400302d002840a4840059829004a141c41e8084032548044c0b9050b4005d5010b94400102070142201c0503080c1411201000110750010080c4072104080c108460b00a550200d048204c4000e45070040c3c0250120100d81031840314855a170680c00e00500b94494410000c0340c841c229200c003c501008121001408080d00040091105020010455540e00c9040c0402004200b0b401040e90014032a0b50007030300040e41640c2c011604011884508a00d44042c3c00c1c01c3c100a08510340680c8500ca00d0300000307040211a854940507411540c4061000f241307005000400c0600050301e80c205044071104c1a50114a5a4a4840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 358513237 1250 358511987 358512001
    0x902061206031b0f0d14030a0c1505010308030106230301030b0601021509030909100915140904021c030306030b07030926040303110c03010c0e09360c0a061106 70
    0x507414803003100003040b8900c1c0b0400c034021700440702030501c4210307081e10002803c0d1041310810805401d102c0120b55500000044502d0024041c0b88892207829075181842d0060000601e6441940d040d101285880c001c8410350050003940e104400c110075800c100000004401d0211412005100b0442a000c8907005801c0c01c48500101c0030071034805005070801d00001041d0701d420114580c100d1082c910003150f0075100c8a44100711201f95800d2210100d0940c0100001d082403480b180074801c00700ca03484c0b858030b4250041120601c40c1070003210909003800c400020907000c2e903c05005550091080e006070f14040324040d00030f2503071040a4524110841850f43c0543e40d01032076200b003980f140c013414213040c5503a809592100a00c0c1500155024988003090305450902c940182c003a142c2d03031110410000031082c4400100090a681c0b86001c2c2840488846e4260840000c404004810031041c10b11419040c182440075100130560712a1010000140f0766a1104059650014090941d00f1544502c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 358514487 1250 358513237 358513273
    0x70312050306180115031a030601060c120801120201050f0706060605041a04030f030806011403091509010b0f090601031d01050103060b06030702210f070302010606021c170a090206120603 82
    0x110800ca00c18100178075501c40c0b14440c0e0080c410088440502c0c00300301000900013030408000b40c00c00300016100c00845018808226410080d60b2201d080c000e00039410121b10009900c204039001e410f1003400103035040809003140072911a00e421240800c083c94440400400c558064424018190307600b0018220003030813103049804481c1d10001413560b54405a40507240c15100504803418011143e00a070a40c001070401540701d198800060144000380d131061400d003000140c202c1942e1703807400c414096207445c1d4640d0391003030810441e85490300360740324801200a407080c3d071401c003da0a1017480c00341050405410041c1a6031055009200e440d110701c083c4200f82c00100d81110050307124007041c2065000c41c100980014a0900c0103600e40140b0810b00001c0b9404458101c0042c0c0d5907180c200034040e814041c40490350b41d0401038880c0d0501706100200385c60015030a0070b444c444448082090b40440d42d11104401d80c0c050540c0707854100d030107520704400100701d0340c042c003034054640d110810642c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 358515737 1250 358514487 358514489
    0x504110c060a1503080c0d0818060a050405190f020a05030a03091a07061112010803030108100b0310060b0703090605040f15020f010219140a0906110703120503061801 73
    0x24001452a03036580303040d400243c080c3c589401002012100080b02181c0010000c1c041c000c41c540080011510302c080051580100501e41c003405e0f0820020561845004100c8940041e40450003050310780300e500f41300e0304200d0402d050101550380961884200001040c0c0c0a10150089901e014030550300c0c0149600e0742003001c401000a42e000c9414031400a410020304640f4181203241d5042c40d0300d03540c440302101c0d45541504280c0341e012818500c0c44072082842e50140259130091400c55240050855840c0740340d00d044414a80c60341601407003903c080140b0b0f141195004401d2003115a00e0712000d0741c950000500340c0001c1e69490300440d80034090011101200e01c021240e44110b444c0c4a16142d108001c10300902c214041c820114645103024000703000201c281c5480800c01c904e82c06d201900301103102d0110100c140c2c080c06030802e02c6802a80c420210740090070860990542540954145007194000030481c404015400024541c0080075600c10a0306480760844110000d802c000c0d44102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 358516987 1250 358515737 358515757
    0x305011e06180807030b04020f010f1409010e0a060f021209031f0b09040b10050d05061f0e04080414040b0a060e01030e07080d0e060a09030318030503030a06050411 72
    0x103000301046401d1045a0700001e401403445a1401070b501c0c0c0d4440b504200c01e41d4400d841c9146401c040c8401d615001c81080c48421090134550640c205c8881d0140c200d580c0d0345244015010080b401080990040142114a5500915440890b5142d406c0980b00d07503800d0244100610402015083c0164070404844611a0080c010324841e6030700400100c0202c4142e105c426030b0768440c00b80c0c1d803498a681c1d1503103004500c02c000d13511240c0b030010703210304009586902c0188508040c50b142d4011030310108200f9004080d0300740705d81c1510b40082c100030b00303036642d5484141a00801e10800042c0f15130301c1301820940e003458440d001000c40c000700308415242c072051040d41c406803942040040c0e90081c4844540b0325010b050116450103901c5a540c140803c40e80f01c42e059410035101c50303400c1a4005c50842c14520b04031045810800811002007124807540030040c144035070400e2940f091403480743c0310f8000755445011070360340385080003c410142809210701805141894a0007407400a036205590103204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 358518237 1250 358516987 358517039
    0x1104080a0528060504080405062109010213050d031b0b0108010c09030218091c0c050d030e06150117040609031709150c041505180f0109090207020f120c01030501 71
    0x2c20f866583c01888007074002c8440c221708000004590700d80b28083c081104145200228851035841d4a420080c3d000f011031940383d1040202601c0004c2c00e0300900182d42003540c81c1010303a41145000d0b1000401805450303002e594002c03104007000f00c102c49403030517600e03c40700030b000d024000201690f80303101c41e02000f544090b070384030459849120286101d90001c0d140007112148200f00d42d5402c1d58580094590000912003020314007404004c00006919a0891504105a0034112402d40e00c3c1c90024140030307610400c60301c1c0100c00341e100718140d1484540c40e00d80740340c40f400c00c2d1134060020b04010108402040007101c03c0340745000d40508051284c2c1480010b13220100818441d030004e00d0004020081c03e00c010301000c980111112040c01003608aa2a010765403082203000d072422000c0d01508501c00c4c00c5000c40b1482c0f590344401044120b4010400260f00c0d00c1003072000800c001502646580c110003500d00c40d108203d00080c13145103001d82038a0401040e40c8400841c144d064280c00110a803203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 358519487 1250 358518237 358518313
    0x308130311060a2c120f06061504120614130317160c0c180b131a011407171c020304050a030f02120a030605040606050306030a0303020d1104080a05 65
    0x2580c44c0b0b5001c3d0b4440c500b04184002c0064000600d14500f482e102d010107038800021224030a02c1000f2040e0450b004a03070469003803502150010142c41a0f0280100e520511a100c4003040344a8118203190302035801407009034034041025000c03a220620058000071301c060406015000943c503c10300414508401071002c81c000701060320250003852080b01c0c0140da00c00002003039060000e00407440a5030b15004203420b00340e20104405181764130307103145081d4549180340c0d01a91444803103800c0c41c50b0a0a1a99070b01d418024181c18070b0043c9240a00b110380c0c02100c0a000c00260300007061070056200320841e8a01d10032a170710080f4017044600610950102034880e01290040340003041ca920544111445809001c07202c440c19000119804c000c80d0316910240b10070300c0c05018282c090080b61820508602c2c104000a654055010703010b0207140d0b0020301240c080342c0542010741040c2444c0b128666480c0da903909595140a00c1da010b803880e014540034512100498100c100e050404144600b21b03003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 358520737 1250 358519487 358519517
    0x50f0402090601210b03010c0504080a030e01030b0d0b09060106050f030a0504081b06060a090908031602191b080109080a08100504091208100501020d0e04060308130311060a 76
    0x20001c0a02514180b02002140002690b2113844c43c2c0301d4007a83c01c50106281c401807040c1801c1d560240c2d03603602403003414001400701480c00924546010307003510307204510301503040040e4000d04032000ea02d50428802e5160700140040380780300340d00441c042001c984044ea665041294035004428074210507031410004928001c0c03464010781d0708180511400ea103001040000329040340303001926244160440c0c01000003916000e01248000d121064081c0503a51444c2d0304c1022611000b05501074428020760740741d2001c0d04c20800070790030302403242c100404103520742040003102841c0082184862040f900200c1d400708180116804290b0240b0201d003880d810300001d0724070300d00040c59815005c031851400a01580d8034021b8402c6140241400100341c4004000200865401440b60300f18111104040280fa6400210901001030502e00504107501c403000040180c0070300c0d80050100807000c42d60481c00381044c0020341c2160f200300c04162071140d100d001d01120340104424100450040300840082d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 358521987 1250 358520737 358520749
    0x501020309120c0c01050f2101030501060b073306170f01270807050703030f080609010303080112020a0e01170f07120b09100507030b1008060d020103240b0706050a050f0402 76
    0x2e11502c3e84441c2442c1244614a85054443c140c4075288c59010004105005003841400c0150110720b40051a001660f111090184100c000800c0c101072203400726480111703601524595161007020a004841e80da001c041754000c5c4504407426035005007090341c80000d005102e020210720840803440d420f05410080c007941c10502c60002c1e5070416080046100107801805000091807180c0c8501d5402a1802401814070400810440c0504030b0b4400500110380c1100010b0304480c20f9a107020054a07a07440444c940d80d10171350140143e0540c94001003296400304180780d62061501044442c202012000c965a400151040301180320b1500c038800c0c0410000080c2e50b81c423000f04400c494004070000c10030803c6810843e070101c00a603580101c000e07a40b42407181d60a541100d4504100c0c0c03400d1190006070b0f4082d045100a06142c1d940d038a0140c440d000421041d002c54030340e000e0550303035555800d41034150303802400d045034040d1a0900044000343c441c0f08480c0070306040e612011050342d8650a1006d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 358523237 1250 358521987 358521997
    0x140a2406030213030503040b120c03060306060405090f010218010f021b010309230d0e0f0310090302010912020706020106090225080d021602040b120319140301030501020309120c0c0105 81
    0xc030f1120030f40720101c0414010030081c07006201100c07101c0c1c0c0c4ea00c01d05480c590502409008140c1540080083c801c81d40d42c001400364010908071000603440e2501001c2034545809404852074950011429004c0307a41104140d41002900781c031440c000042407070080fa02c2d824003812911404034010300c68030041d4400e5110034441441002c3c5094812505c43e821952920008002589a82322135110800f4542c0b041240b000c203501070b035005965061010000351103040001d0440d80c1d00d03aa503209201410303c02d4100d0154190010034024a00e0030016000351201610f0090078050340c205070000400d80200e1003102c110038211003591000b82d05504026410986044041d581c2c0d02c0217200b4544c2040c42c80c40186003090b090664941004031034030511041d180081292489560070580c0c03031150405c04400c075101165a001d071031840600110042c2c3c0c00320f1401c07882010643c1d01000210402c8015402107010b5640d15040f00e2481ea0b43d0450200c041c883c44001e10440c1d00103000c0056254082c0010745 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 358524487 1250 358523237 358523257
    0x2100902191403010b0402090a090504020d0605040506011a040608010302010e01090e07030903021209030303130f080f0a031a010906030e0f160510091d0403020c04140a24060302 78
    0x1000240203003400c880141d078150000b000245140000400c985000d103c5c400800800303480950a107412040055a00d80301c500c034070300c10552a0340c0014210f40d280d03c0903001442d03000c042000a818141803080d596a024001c22103580780d024403070414016810241d9048400075640c04280740e00719070044980206003032038181448103042003c107041184850840c4107180a03580001c0490450500030f1820122007010340c00004100a89012500d0110440c2c0e03202440d06074050306170085190048902903044400f500d004000300707051900040c004001c0c0412955640c0c288088110307540079084c10034070f5213030483c0403500c1d4a45c00c100441c001e800c02200700b0344074003e076100b081c03c51103d80c0c24502c2004111420312001c8030240142e1400001a01c4100c18604d42122280d0403c0c0030b04242502024089450131812000102054800c0150050200020f0424415070403104294890300000350380c4c1101c010700309200060703080e40d9007280b500307030403511102400c400d0702d0614160001e50082c5154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 358525737 1250 358524487 358524499
    0xb0d0b04140106030506011b0c060503090f070e010e061008010612061a07020a0602030a0504033305010e0a02181c140a0501050604061202091009291002100902 70
    0x21042045070301040c0d4000d0205840c040380b1860654001421060b00310005a00c40061002d40030204269820383c40945005040040da44e0310369101540c0740c90018883c1c03040b0b9202c0c0c11004500c40020038005412502a00c0280c05030307864240802140244040c031410004201d58010096a8441e0345181041c000342540021465200c450495900101c0e40324601c1800000400c4021410071200100007080144091420082c40303d40040c118841e0348000340803240102034082d02e841044044000c1c501c8020f054028100c0200d01d000d001e420244502e8821118100004010140c03034000c5500e403070004440103075440b078102c0801900c0d05030140700b400c0c8298200c1c0c50000003407801d04e191f1048030100f4028130f11821285411829510003d01c050300030b41c14582c08109001203d410341030440e60484240f0ba01c3d070b0b00c544d072190002005920080708542098001e414014008041e440d5280700200c1c0980d0049500c8240400d490049040000503404100804261403040d400340121510041030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 358526987 1250 358525737 358525751
    0x30c02130908040e0601030507021b180a291c08310815040f060b04150e0609010501080c0a020319030b03190309140f0a03060603020a060302040b0d0b04 67
    0x500c2281c602400454080000107024080c061010f669254092024a4144410f10f0214030003502e03210303401846090901180301040060703031500798030b8145110aa00d0780d4260700c0c1031a149005001ca80e480c0341896000c3d01e00f05a86440170307214141054a002c4c003c0c441d410113480503001d0444800341e090324040000d100325005882c03060b0381c90f0000300702c240e51074103040e580d000201c01406446c0c0c0300e1086035100c00001c40040d000d11548a502541204013100034107010b00380b001c00340200504042d030003850200100030700c1d0007203007000c005c0d60480c2e901185a55950030501c22039500038001c43e8041801900010344030b902e008000e0115081c5ca10681307051104860b107900b050144c0b844030601003a103900d003d000c2e0341808c00144440700c2d1131007081851340b01c43e5240908000154019200350b118214088401615100d160510480000d4104440c031941e030f00b4144020001c41c00102e01c00c0c6202080010118824000e82c2c05942c60000311600d4181c010200780001c1c840c150402c2e40143d243c4503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 358528237 1250 358526987 358527019
    0x80f1303050f0a1e020906060c030d0501031b0603050f132a0504050f070f08100b0408150105030a0312090f0209190e011103240a03030f0f0516030c02 66
    0x80780c03142d00c0400c1002441d03403602a10301001d0501e4410501c48440c0c8284840d840580e40d40c041040d08075100f501d80ca5603800d101029030342584100038030f4110361400e050000013003011b10511002041b080c600110f088076245c190407402ea0302c040d40d0040401c1d111001294250910160b401186441503c0b4105140c2c80007409041c2c0100c0702402203910000d040c020041800e0030700a041e8004802d1010191500c1c0002000e481c113019280c40c88100038500e000606011002060341c000b030410032203500c0c1c899a4400030f46aa0f00646101c03a004504881c0c0000341c01d05000900d030402a5242d01d500e41c4c1c850724455040d0040103000c034159008242d001c085409a10790b005501d002d00c24a03001040010801e2118505540410f06900d2841e071401c07017200081440401501c0c0c01900d0741092002901104d800d4140440c03020002590007609000b00104154010300b40c1d811444c5103887c0d80001000c0d610381554a800b035115103c488442d6080340340c0019115011241c1d800c0d00c024140d00c0c244e40031403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 358529487 1250 358528237 358528243
    0x907030e060c04030606050d0203150c090a0825061704060f02031303020601150504090b040e01020a050703081e150102070f060908300331031803080f130305 69
    0xa42d5504201e24000303800e00c203010301c038007070480a0181580c201420903840e80c0840d03074441001d0205007000b02180c0100303a50983d42c60403104598001003184c01c5e11511107581548480e46d0000c05070118009014a0080381051501c07141158002e480740070816884e00b0351084085001041200c40958641c6808101c61403840a98040c004240b11249a5401441d0207407034400c040c1c215500b00c59080100d8070580b5072103002c0300d0903120386450204000724040c0204000c1c1c0b5106032000180d5001203201250590722801800406000c2d03501c040c03042c0c4404094000c4c0341013004c1035aa03140600e100050384480c80600c80391302e000d4180304442d041c42d52510010380328407039600315200080c070f603210401c580c5004008034800d070f01400d40c403000c4014869003025240d62111034181c1d560b0380d0100000304038103c07400d403440d290b40c499140f10451412100100b500e40c0803802d0114085100c12211a6030100040c0c1d8190039a0b034054100c5181c851000444036140e0443e50905001555450012001800c28 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 358530737 1250 358529487 358529491
    0x9010b030706050a110f061605040803180a09020403020d02120c120303010611012901090e250206040c031704030501020c010e0f030a0f050906120f01051507020f0907030e06 76
    0x1c2c1c0d00c0c1600c504200900400380300072030408440a038001c15202d00340d95400b0072a11380200c8a4503004045e20121201503805016a9100c1cbc0030740d00020844110411010043c0108030350308640c01d004880e1946d828100b203014500000e0b401102910341c4000604041d50341b101c1e108408421034103102442e50016802c15074200394014190008001084441c3c2c0050b8020507815101001b8021000140c4083e01074011402c0c2c4071006005801e80d8425036406444100054541400f4201d904e16004d02c00410709460704400c0050240c601100303a001900c042103039801907510030800c034482403550300c40d40c941c460200c02c0a60b02d00002c000010005009200401e403035805440041280d14581c281c0b0f60804204004455641d0803c0140c400c441c0e81c40364045840c1440d500b0800e4888050b000401e009020302022000c4081c620301c1480040c010001038103040320340c101c41c1e5856000300000181b409002e9040002c0d0020701e00e0700c0850300d40c50a00e21842c0d1142c4107140005004910781c0c83c0b80e28100301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 358531987 1250 358530737 358530749
    0xe061314181c050904020d140a0204030b15091902040b0d0501140a0317030901020403061a10032304020415030f030210060b0421080309010b211509010b0307 69
    0x14022501c0e48003030030300852035580d41d502e404802c941c0360700d54054140c0c4141c0c000c152080e54005104008180c41d980301c2034480788a003c0707000051501c0480b00d402940140002e68501040400140101012003040c42076408050003a00d02525003e0b1a000c840c1044519020701580a200104084a00d1005020004103a84001c115549080203c9495202a00040b80140f4051b0002d101190342e405007501d0305044508034985c0c9640e0201030500a015640000706002d0612804c0340c1d03407055034010821140801c940c1c41031820200d131400d804441c5c8202c0240c40e506040800e5000f103c0000c1c0441d6030082c0041e1000c40d910b802105860f075103034404c0e00202d84c3d501d101007894040c584e0400908030f000340c9074101089030700e0a15620340381e075024070700c0380040148a0450401400100084004400764410003481d100e00701008104d000c1c02c0d01034440343c042c020150200384448913803050600111004c901030800320581c020a510444030050a1184564881307003104400d031400c00801c001081 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 358533237 1250 358531987 358532011
    0x106210615030b0f03120f0304060921080f06010909020d0f090506040c080303060d1103190507050324010303081f09050103060b06030714090d05010f0608010b0a0e061314 75
    0x4010400c0001030002d003044c40380668001c0b05000901d40040382140e0445004030301c01601d0390380b90318005029000303014008000d20100c016660b0321074059003000d440c1c10782c5034407408407a03507580e00c462024090072142c0e0342c0001c008a40800c081210390380240400c0c10461000714051004400342000d0328004201191107600c65800c000a01640c01801c0c4044c11600b0042c625509202000421000e00054041c041c00e81c1000001880d980420412941c032403004d85407514842241442a15070415208442c000e0040c1d1070300b00000c211041c0d4024903000c14030302c00c00705079003161411921b403030000340151402c60341c144003104c1c402ca401401500a101c916404101581545007400130340e5a0351250700c0c0944014420b00401c15006081440c4800d4484d200310f40341c1c001480000c0c051105401c000d0159440c01009110a901030303008442611504c500901604e401e600038401040c1407885008252108200410460314113114001c940d0006030201298601e01804080011002901e011483d40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 358534487 1250 358533237 358533251
    0x30705010b010503010b0405133201120b1603021b03070309061b11060d0c030e0606030d050406080a02070816033203040206040905090a050114010621061503 69
    0x1120902a00e00000000c2c07030080d0035549020b081c1441030190340919403082102441c4101d039000d450380b007000009800041042210004584081c0c480c06d0120102d0610380c90300c0c004500321b2000c4692010701980070b80302c548195145440344000e0f5082c0c1c071000c42050340801466481e511481d41208031081d80380702560382c8032103900c0e0142c02e103ca00d0780a0410301180604008252030151000b0301030302e030014402c140c04400400010703440d00c152503100c45a035252a14460049074150301c1601081c0b503100c22119540c07580801c0681c0c903404000c0c0c82c00003800c100414402648510309558000140581c00341c149446030352605402d420003e003001c00c4108151043c020706030300c1100b0003042404040940307100b1034141c002441401d850f003266188c40c68000085411500c03101c089030000c10341c90703100300454206008415143c64035100c00b41c0d03241d070070441a500f8032a100d80e1410f04945154445580030301c1c000d00b0040090700b5585d100c1900c0340d91034200084034007110103c2001001c0d2550001707180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 358535737 1250 358534487 358534493
    0xc030e190b030a0f05060f010503060316090903030f090803180f060705190e0a050409080408100504050d030e1b04090606060e01140306060403021c0609050607090602010e070b0307030209030a050307 87
    0x31001401082100c500300400e001b000c2d1520328002400607001e02c0c2a0f039481e070311000800e01d412929954a8040d180568001a05ca1a6903000382c12a0b886a070702480011a00d00050b01a06c0c49218050003662040020511031440307103c0c02c0389000c00003000e1303e0840050300040742c1880422170f030a0001c698005a4404082c21001080306004030b01c0c1080c8141003500303000b03d09821580c0c05028022075680d80d0780c80901100300148d60041c02400c0031070b42c144403008107010151005803421a8144642240c0d0345d5964000c5c012041400130500042c000b10b1004c2d00303da40d00a5101c80010b8200d595072415030041811805008090702d4241c858240194440c0300040181d0040f0084080e019414402d009442e924001124100c940403a081340c000041000030a00a020450700101800c0c03610039800100280811694441c80300c82c0c9401c04050358511080e402e0b10410301141105030081d080600605018802071500001c10b841e00604203400b8002203407610905c420706550650001c6500010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 358536987 1250 358535737 358535741
    0x204031a092128080f040506190209060a0f020606100e09061504030308070318050d0c1b180e01200d1503080316050a0c030e190b030a 59
    0x10080c8031a5031200d262408820301c60300c0d1503840014041e200d407280e039840c0e034118035442680c00c0c0c0004022a5400f2041c03000c3c042c3c1002e210745000340e020070000400600308690200d2001e00c01c0b50440054011a640d20f0706421011048003801c02180f0741c03c0c08665226101d81020f40003829a98940010500419030080d203007100003000a071181076460742c1d43c8200340d80100100c01e03410707080c0c0344900141c03151000900c004140000103224044041000400c0c16840074865015500503103041005a400f25007208072800d00510240440d40700e030030210401842900121207541c020007402005600101089011071026401a00c449202c1080e400f00d0300c5561040d0707420320800701c1c0200401d26070364407040d208100000114000c03101c0070a01c05912000b035001613042d43c03020740490554a8a031300d1f210700290019118904080855802000c015004808480e9250613a40b5401d000030903560f01210404e058103200c0d41c0044401080403200c10b101c0d520240a000654904c0da100e14090242c001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 358538237 1250 358536987 358537013
    0x90302071403031215040c09150201020403170a09090c0c050105060913150e01051014040501030803150a051203031e01030f030f020f0a05010f0b0102121213080a03020403 75
    0x12520141c060031519940003c2103940050321080b141860350796107444005003042d4071401c41d0304075090080c6c80300c80540c010040c40030b07900c200c480400c0205030403200700c0c200d006901005000d034441c04082c0f014015107034080d020001e410300c2c00020007a10303108020280d81814034108081810f05105c3c40400c4002c2c025164810310580788070300d46280180740b0080481e103400e4050b0040400308032848484a1580004e121550100c00074000c1e41402d2101c000e0322402c41c4500904e41d0301d60903550001c4c0ca400c2c01424100c036003264a0f1401c549035055600c0c0260b031821001640a642c040d1700040e1034443c200701a844010340e40c055030b04c070726252000200c0442c059008140741d2090741d006000141d0540c05900440c0c0e05403030044034002c100c41e8160301d00594141c0c24880b500c10180124200b20b01500454024051840284104100403005907545c20390100e0744c0042d00400d00a188483d01c0311200c1d1a0301c0903241d551404c0c104c0301a10b41a0741507001d21100300000c0d400050030302c103000742c1042d0f1079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 358539487 1250 358538237 358538249
    0xa0204060801061809080d1d0d022113060e06161b08070312200105043503011a070f0c0e0c0a0e010807030b2206060201051308030402010215010909030207 68
    0x405000829582c201c6c45d0f22801001d54012540c0340580140c07824505014107406604c0001c132084e0120700b01002e0740d40c920001c01e40c8814111400c14003501da002c0e8017500c0501710f41e44503918105040c4001620118001c00324560480d10034865a4020b80b6100d4070321282c00c0c0141420511070049405a41e42e41002d5044022103602c02e03007040001036010900c214444070f491400702800e0031035282103411507271070b40d8a1191541c2854103100a002c8180501142c0240080359181201d041e0600030300018079411810300c01100610040241484008480854054592255150524a41d120420504d4903141079403452003414081c000083c0303d0340d0640e01300e400c83c0c000504040c800c10b0020084100116a82d0403c0034100c082020b40d40250444202c40000410703c03e070499061a001000c1500307458810f5915050a100007201030062081c103000b103410102c03c0b010746c5000d44407201030782e10240c8100d04520582b200714178403280000500e4060b281000c4085120f400c2070070001c1c50820349400503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 358540737 1250 358539487 358539491
    0x2270a0507020a020a140d020619030b2d06040305070e160e130e0703061a041802060a0f0e1f020c10080115140c0309010809060c1206030a02040608010618 68
    0x20f0140e918000340c0750844884414043c04008400003040510410b00d50007500104007040f5490385281e54094245c44081a13a07003040b4400140b401c001c0f044550301044900d10045810b4290a802c0c083c3c1c11407c0000040c201c1803a10707503691344070351509010b50b1001e100c403043c0c0812700107901e0100707210300e601030054940800c1c5001500c002072040c150a0001000700b82d40d65143c0c01c6180c0d403d2048000071034010a007080254000c8888924100ca8000b6440c030451030409a11094000034101d0310510f40c010340441e007040d0200d103090b0345a00756148107000b480460b1441c01e40710b5441010644000c2d5078070f509600e05480e8508041c2c81c00c0402941c41e03101e41d04d414010709a40b0f82c001540b0f03045405001030140c01c0c14031440181e48104190500002d074500005920042144c0000149020202031340c418405a641d6911146c0b140000d1ba610301440c1810090003800101001109030401001002c0d618290709030b600050446a01e580400290b03511100c00b048410340c040d0b01101100303440e41c07007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 358541987 1250 358540737 358540753
    0x9060607020301110307181706010b07030c14100f060f1505160c090e0c0312130e010e1617060d020414160f020d020705041505131a010f080a0902270a050702 69
    0x210388072700c0d05008503501c1550120782e03074060502c42c40c914883e4580003460040d0582c0e0034088607031600c0c6800e400820386c2c0e0501150a12a1000b0300c01c1c1e03070480d206c13101074182190400440c0e041180b0020b040004000050141e25403c0103510041c4070400c0c031540748184102d26004188003a594655074251103038000d25284003260720042921120700040b9207003aa560704d880c51a2074920f03a441c3c1c000c40c04083c070035000400e10412904010f07004030703109a04100c0304810004101c805143d4204005008418080400c01c9410844c0321402c0b030130320003030020171801d04d050303910300c1c041008071a0100f81d10104d0402424894000307e100215404500c09808503440d0500e020395911103e100366400b60350388404d6101c00201c081015005010001d166000480782c1c420741d1400703803e00140105107920311402c034000c1e560181458807c0c65582d9200d441e4a90340350f20001004104215050380c00a141c80318409004400070340d000314040c002c0c0401a51414844007100865100501400555002c401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 358543237 1250 358541987 358542029
    0x50604020306011d150a020106080c0603270a150b010e01020118030c080904020c030d060609030f14010608061f0e040c1e05060f0301090506010c020906060702030111030718 76
    0x15503031315401d10290b6480c0f98000b100f40400c0c1400024600350300c040c90081060301c0d0040c0c1c190003540031030b20a0b6049500c0103031000104103091100381c5140c80c00d403000048050458550590340e4110170003c1064580000f1240c1781c00b116207070740809116110b039607030441403003540e005100c084000b0028402048211b1b0905202156801c1d11507000c0c092001051400003001030382000c0320f151034030280080d03490382086120396540c6d4002d0500c0c1d14036582000c1003c100e0314801d0f4424000c07207410400901070f010a0342c0307800312200b0011030f080050b5500c03004040780e030280801109010f5107100c040510340b0011040110600045a000340711709034801d006000104030000038603415280e240c08449510940d0301070140000c8000d6103d07035008440855143c080c00c1400c2d0180d030480d04c1d001000e020aa07507050044a11a00c5010001e5100c1000c00100300703d030500f180030b464001e2018000080c2c4501d450906000c44d04212414000110031451341c00d2103d20850313941c0b00815141d8031140040c6054a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 358544487 1250 358543237 358543247
    0x90905160f030e030c01150510020c06041a09030124050906060706271505010902090a0311010c02090103061d030a02100b060d02030a06090c0e091306090b070c0605060402030601 78
    0x31060040686030303e107408200005004545801c90008001c020401e1360481d42000104070b40709084c4581c055848848020b4008101c11105074001400c06281a0414042c05110313070002d8800d00c1000002d0210b4580c2c0e4400b40f0402c8010b0100cbe00c402c0002201c0540e05003260b20040d0002070040e1205800e005d6541c03201c505a507001c942c4a4800300302c003d40031002d5501c100e0020030804501e40c41c082500c2c18080c60f05007100c11080000400d1025a0322515110700340d100300036403250000c40e088000c00c040351800b038814006a8052400d0003c6e0021600042e08001303081c0c1050701c1c1c1300d90b02c1031003003010440e00210741c07510720380600a0750600803400006500d402420300c0e0034101684540c0c00b20059900c8900721035616006c12021503c90800d1500e240c020851805044506031824030f40d8051980208855400c21100401c800016038641c44a0302840900e401c0468045440d144071100080a140e01503201d880650703241c0c22100c0003401c168041e6803000d00440c0c0079030710410510032984d902c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 358545737 1250 358544487 358544507
    0x5030706140f0d09021e04200319060f06030f14040c03081305060d0504050705060f0423030f060901060e04080702120a05010510030b0c030f0118061509090516 70
    0x30701c2d00b031601c0310f040c25448809003203c100000c1d4813001503803a84c51540e1211031103400d805000e8504000d2000a01c0e41d85064210400608480390000d10000c0c04040080c421700ba20681f40c004081120327980c41442c003000c032083c1d420801c080394440b40ac0000b980c00f540309512004402c40c00614003420281c45640107801c003400040e089210000300d00c401c080e001a031034402003030050002c17a900c81c01402d1507001000b066508940500813a0700014a525080d01915815802c643c4494641441d206039012016181580a1812420942c4c1c10305195414080c402d29015040007612003450545c100d1400c461071a04080843e000a0007400003003913000c0c040d18400d65061f1100c40c91200e032814900d18060744031000170241c0d07003008204030450300c0c12881141100c1c40760405015680781d4103911001400110b0b21241050700040040110741400807140b0060480c0d04c0c400640c468941c000f40200c0c03041c0020001c04112095020080d08a00303121315644010103c0804500d1604014014003135000c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 358546987 1250 358545737 358545757
    0x60c14061302270a020711040b010e010f021903021623010804050a020a080d030b0312030f0c0f0a050405010809010c0c020105030a02040902040e0402190e01150909050f010503070614 80
    0x91154001d008034218072020340b420b0f01c10000d10b499180c440d06060107948180d20440c0c3d0900c801046420506040c0180050040140c440000300e000c00c600464900208103040001c51080c0070b2403400e0007880301c555540483c000e43c050030110200c01d03060b503d07241d5194003408200100340195201110801c8010a04003030074070b80300b00551101d0030164134043c1141c0019520286a000002d00ca8030005016500041b040c3c5041c070a014215040507103c104144000709074460410000f10004a24410702e6800b480001c203040c00c0840380c0c0b240e05919003003200301c4004105c000606012668114a089900c100450001d010016403240018800c480f08000241804808408120f001c0354540599002c2e00408004649031a604c25007241e1061055400b0b0303029450068501c0380c206206081c61058500c0a80641856481c0002240308002407001d050304004031482c0106000380e55000301d501920780403601c11103c0d41408201802c114950f80246e003440060314680510b41103032006d030703000307100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 358548237 1250 358546987 358546999
    0xa0507030e07033224090c06040302100207120c03030201141312110f0309041515050d090803160e220509010209090106050d150501090b0901090f060c14061302 70
    0xc000d4020546001340500c080d41c40c0100c0d010b1241031406100184e80e40c01c9484c100c039405444260855403650500100300e50040001c000030300250520082e59094050144103da00c0c040e56a101114015400101200d811100203020424980c2c240519460054800d1400469040060020600d80f424500080c40c1e02070708120300f0107407070140950030034000e1140f041d108190a0a03074400e8517a4060f040c1300b48641d00e44441c812814900c6c1e5441ea041e01d01111a8040645083c40155030a812a22100e6101501e07402483d000a420780c010718001d0700b07194100e8825007030a810150071103c6c4000710741d002d460110f039011644401c054100751120080e140006e8507485111240e80a841131010017a045201c0700000160181d01c440180302480c0f4a1100700104c280c10180f4013a10f05003485014002080e801c010302207142950001d1140540c141840c0100d650380e003034420162807942e40400007149050145000344201c08103550a505003a4024008610b4100110003020011240c080e024079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 358549487 1250 358548237 358548293
    0x114010c061e0609050c0703020309150706020f0426030301060c17070b06031603020a0311011106010303200c1c050f030c160504091203020f0d050a0507030e0703 71
    0x102140d0b01002c41521060880384003042040c511a000d041c0c1840381d008103c0c40e00b00096100c01c0300c04113542c8410791542c040d5181114032001c12501010a14051820b80c0e020030115000500510007480e40c00b980c81429500d681c40d004c518160030a081d003400700b20700c0d91b2700703d1281104c1000c801c8074152012810520703030ba0300d22410590103103915603011300807254000071208240148084658450074040302210101a64010f07001081d032030341d22000390003000800081c0300013480c0c2c0c02c2d020f10b001010b161401813a0801000c09160140c00e9009034085128559901c1a0204e51184003130061115402031144003221404207040ca030038004000701300380d86c545401e0200202405401200c81c0c290040341c6d111441d401545480383d0440c1c0c40300c0b8007030102c2d0f90000f81d14101402202c144503008002d8004540840fa0181c010358081291942001820040480320700c25520880f03020341c2c061030001900d0b00d411000a01101d8041c40065299441100b0030400241d40d40c80f001c00940c03c0b41c6e8207590b0a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 358550737 1250 358549487 358549493
    0xe10090c0e03011811030d08040b0a021611011b02130209030f15010e0f040b071d04060305010914280c0f0303050d05100501020d350108150114010c 65
    0x8024a42410380c0c2c19400e00c2008000386501401d203400d600d00070001110303e8501c07003042503a40c020300c8280c0d501103800000003c001c200c1d203400140d0302550050026250440c00e4030704511840b000c100c100c039001e0070a4032400301c03560301000204166000140203c58440d060b00000d12081901d081e00b0140c5400090208440e01c1c01c0c404040131624800c1103844075007075075041e08241c681c03d000d001c11005400c000030302041010010180a00d4020130410100d03100c0410817100001507601200462242030005d0072661168802d090065015800018a1482520703080303102108125054bc00ea0b0b01c03070702e1030544188490580011014a401a00040034528640b201c1300041e142e01004040044107030000074584c01000500e00e00485550130071080d0346400041e4031428445c01040d00681c420a0441d90943c0900d80c0307510f820000095005001c00d046100c6c104509503609102c1d28651168010002c0c0700e01080301c64426100440c0740ea18641c14102c07103103044070300041054100000d2440078403c6c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 358551987 1250 358550737 358550747
    0x1c060209060708180402030f04060b12120d0f060b042601020f1206040608061302010909240902120c03040f0f060b030c01020c0306040605220c0504060e10090c 70
    0x101600c040e003450348034a418142070000360016204204102c40c03410140102d4a0300e032003141e1040c0e00c04440c0c40d06c80e032269158a0000d00b40d050302290010f1400d031030002107450420680c40020049506155190002840c56041e94810505030440e07504000060055138260f1081d541614510035040c020348007505000c0e0f2040001c445010115440054203240040d039550080c6101c50b140d80450340151580800c0c441294400c0c4906c0d030482d04000040b6406241a240d90001a4014074090115585841c0c41c070b02220000f400606c0f05280803801c4150803088644000010500c1280c1142000e044c40d0f1005c1601c040144001102000000007070304021491000d156516005072103c905440340317203400c0e0018062001e009219100d00440002c02d9840020f900c00307040030160140503d41ca4a03607640c000b61201502403480e00403200c1c1100c0b0601c10030142ca443daa801355800031002c82c501000e100440b40f00c0d400c680340c55070080e01040310751080e5040506c100e0360404000954211202c404981c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 358553237 1250 358551987 358551997
    0x7090f0b040905060d0807060501050f010e100f0c020301141e010f05040b010c051b0103050c0403020109030209220b0708011401080424110301080708030c1c021216050c0a051c0602 79
    0x1010310800711f580c505101983e0f104034103a038401c0d80c24400217400500199440600e000f2030301d40c0502d205090403000c5110f8203908686810030300b4003030401b5a01750b00003400d462a2001260000f0007442c20000c802d416a901160a4040c20961816550400311004010882801340500498540d00701c405181d2140c512444616042415203011030128607040403c901e00c0c081c0640040d060402042c042e54040003181c003243d13416128135070795500d10b03030a1040c811001040c4807880031031151088117843d000c600003050b181c031031074130100f16184c08103020b807000340e040c0c010f40c4069458030b4080c0c555903001660a038005810114081081f446804031440c1c03414119044c01d2140e09281c00e01280002c0000550b068174a00015a4042502d582c40b0740d9990150541d114850b900040209912034401c40c880103130707440a44141d800145000100a11541c07200841c848454498940356051060a101807019200100c3e880c18081d4548000101700301d281201b0300e94620f42d06c1d143c2c07008016050341259 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 358554487 1250 358553237 358553243
    0x30807180914090c1c15050f010306290609150f090f04021912020c0304060806040f090c150e0333010308040308070f06050a0507090f0b040905060d 65
    0x9100e907030301e42100c031024254100c8030203140d035003140c086100070350301003071048a0341005000540c282e1241d01500b104410340440c10385000c0200505000d0103803450003424895045009806025451460604122403070740b0305152100321444804203c070048124500040348084840341d850f0000003000030028000c148581000c3c52000414410a22000c0b014000d81c440c201d400c0f00e4907030551800d000c10f0384101e1600607080c0d050a807070078000d140148504c140d1030001d40c0b001030034640d40500e607603c2c55016800500c01300c0d071000c04101c51b503c2d25020f0421042101001445944059910243c1110b490702403c3d07681c0062082003202540b18150b1501201001400c40b009140410b840920b00306044490101c0c000c49041d103600d40d180c1d40c11a05040744c1c1d000385020310f403520b50b442d0794801d900580c50071031702015400f010038003151160113024000d01440800080505048401910400c22030307010700e00b40516003608100d0034092000341c504036007450402050036621000040e040d098240383c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 358555737 1250 358554487 358554527
    0xc0314040c17010203010b0f0307091211040605040b01020705010e0301090c0b0c070803121f0e0a05060f03010608030702091008030a0c23210f160c0b090a03030807 72
    0x310600094012020031103090b22503078484240c040082509070700c401d024020343c0a01c20020f40a0031015800110340c48405071401c100d4040d00c4044503002e04208840c155102c6060394810119450507205510041a0445040005002840001c0d460760500e11855041c000c581e01c0d044943e440c04c2d0040c080440c0e01540c8030b038019890380c240c0d11050300800303005007691041c00c1010820030000802c4440a4101840300340b42a90f41c50320150058100682001404294610004000f0360b030250050064003a86004200f5203030401c00e103d0841070f884d103618031981c1480810000d0020201c100c030b0703a55030140c584400550300d0442d128545042507000c40f665110001d24800041d0303103d02103012062241040c040c203844401030b0708003a100e941903040000d401c40504040039000e21116840e160b201e03495042e042010441e4000c2a5400616084840c1c0411644400800c0085034288001d0031220400c03504001c100c030b0114850051501000b4240611310380859078650140440e80b0a030000c0300c0b0781c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 358556987 1250 358555737 358555741
    0x61c06020309010c030603030c110d0c06020a15180b0c09060a11010c08041515082d010c05070b07110118031e121e06090b0112090503030a0c0314 64
    0x60000703500403901e41240b9440c1104020f0420b1090160000b1242c0690f06c1c2d203141c0c8107a407585901448500c0065900074969401c2000151000c0413030700052a960300581885440d50404100881491090000c40c614182c41801511414400401010340150848043c7d6840302151a07680c8200b00005500100114004a216a000700e0f222285d030160b2009010060391110141d800f2041980c004100b8440e2a115098118003584412007071200c1d4086018000d5513150128100a60040c0c01c09000380020f4a5951050900409001d0109000c000300849a000300d40200386000d03103140180015102d00105401c1842240180342c03041c18200204400c0c0f01c1181110303526011110210040b03580a051f01400040b8068222101809511000503408219404900404141c0c11a1090000c1303c101c01458024921515000e003003000d900096001c0f0290025210400c9801c2c0925502d0810a030b2000156011007a81d0304001c81c0403000c107240c0420311003900a4098481400e541c1a80001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 358558237 1250 358556987 358556993
    0x40b040f0609230904020d02090f09071e120203070e01090f054503040e150901140105070204090f05070306051b03040209070e0d0302060123030c0108061c 68
    0x80c8280440301181c4651599540d03806881d12032019095540700501151052000c150400d011015030081c801081403801074210b07070000c4c100c0d94007a80d8040b00c50340c04508128000d07004004041c0074158100d00180c1c007503d503000700f4034081128001c03085844002e48041d02103450402a00018016842c001c24482d82c4491340400100001101022203504050215159804480c0350504603000b011780c486814090300001013003214956204407000000f20146c4035450780a05c064006001d140740b107401c0c0360a0000e501d0744d0789400c4c10f403c0c038410080540100101e02c070754041091059420f080c05911341c0c0030360001800a004814020780554482d480e00002c01c2404076900c415244100000c101903200d00c045464980350300c100d0100b21040400206016190220301c06903c820705241900400840310007007000501140f504902584c05100140401d1448582000944510103040304608180300300113551900d120803040d046c041d6180c04a03c0e103454090941f0034425101950340301e0071002e46 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 358559487 1250 358558237 358558259
    0x1207080f0f0703030c03020a0806190909150e01052203090e04050114070806010e0409050705030d02030c2506030f0e0d02070f0b09060a050c0102130914090f030307030908040b04 78
    0x360088000918002c1d105410301e02901c00e40d102d00c2d48c1c4e41e0b02c00d40310303580741d60610840c3c00465961420030024000700145000ca14001c25030040d10031041484800c03c1417213010242c0c2d000038202e5560b039050508110360514440c01d42c070110b40036060052500c1e80b840c2001d48841c9100c0d08800c1040041508002c00c0c0300054200309a1031060041c920070030358890380100ca1404c41510391900042a0b40d5032000245442c0d000301003954020001e8032101961400003034580004007c000c00940c2010506505d100010310802482840b00500c18400b0034001e104036400b80100d00500c02450740c1e480100403180d043d0740c003110035034a03100c048403003e070441c0a020755162035902c04c0513030030000d002d40880d58240940c02c3c0d421030000a403105041c1090320409980d190055030300b81e4003540d400c0c4040d00101c003407101000000c00d085000050900107542c0040280b020003400da00340355028450010850703000201710780c0c1c01640e51400180000341e07860203104910543d4000d09241c0008240070a4480c400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 358560737 1250 358559487 358559497
    0x621120901020d03060501092306040306051906030515131b0f0906050303070807030c06090b041703060d030f020c03010f1418031204020406030f03020c100903051207080f0f 76
    0x360202d9079080002c0d0401c805580a43c00344600160f1488e008008034140c20100115144144804407001c9074807802003841074000c2e61044e60020b40b03a07400d12041c4c01c22031a04115110214005000c00390668840d0399950b802074480e00e00d800101c80000300030000c4141d0b5008401c0c4e100c6810a00c0c2c10b042549084845000d01984450800c08040000d450896115003001c94502601a40c10038116807240d04a9801c000c078107800313110198450720b00090440c4030316141c0520a4103540c400c1c0c141410012410b0380000c1d110b007000b000030010f005e00c82e80d41c007500154203030307041c640400c2034460448101d0900103240c0d0000e4041d0700704106120004070a4203e6003451610284800842da5807408001401080b540740303207a603400c10801c84101c080b0a0014560042c0042c0c070110352039903241e0740c000603c1c1c08400142e0050b082908034010070720700000c21107584034461074400e0014ac11500d6040c1c584254146400210100145007010000400142c520f4a0305070103100d91250700100d0a8002c40e801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 358561987 1250 358560737 358560739
    0xf0115170604151128020d080408030915090a12050304020f15090301020a0e150f04031202070b0406020d0206071119050f03030720011e05060102100c0f09170606211209 74
    0x12001d0b41c0d0440f2440000c09944d1f042003a0b403690026165a02c54800c190b001030043d0181d03000f80c011780c01c0e080c10f112040b10700541341400100079042c0981441c0000e5016400f000080000400c01e00c001b580c7d4405140c4440202103410f281c2c3c103901c180100d4514440c2c02801c5805500108611010039000b6141c50314042c42640e84601c10280102e00607024441c80311401813200c01807005202017201000340213041b5a55004030342c543c036100d06d80c10540e0382169014500581c880c0350500001c55040c408c103504542c25003044000003541054407619403140782c1000d2011454025008c0501c00c0812015001e9000403050320354a0402080c000c0101c5550400809655849100c2940004d014842c6a02e1841c80d652550352886051400c0d101900014005030b046124080e07440f01ca400442c0725040300420071b915104191500160b0142498900e50720286800102d00407034001a01c002c15202d80c0618205c0b4100034140c81585880c0380186030350b54190107031050103180358201c41c4200c010450010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 358563237 1250 358561987 358562047
    0x60e030c0d0206030f0a0b031e0d030e070b0c120310060f05181203070c230604050603010915080f010501060809030309070312050403050f01151706041511 68
    0x1150502180340c460030002034003d81d0800000b80c072404100101a00000181c402281c003605001c0040d140204001c0701100e280032851464800c59030030011801c140c0c0031030038240001c20f02581c043c1c0e11020b0f140700340403005038002094007194005103c640c407900c0d84102160740300d0a104030009401401070045002003070391040b816407143d00600c1a1805103100e03020140302250040c00f4401821200c01d0ba81e42c480c0300620a07440041c900000706000307405441c0e414485a205004200314800c0502e0b44240208020070082c04642c07902e5080ba4190b441180c2c0c0403c0180c0c4d040503550710f800b610341c032101090041c000c107001c0c0c840042d000581240d68955595829807601210f55072684010f0314240040d50105004000103000c62a40400091071410114102582da03259681402c0303510356590300ba83d43d14500c3ca4070b520211001c900140c00392242003400c5034003201c0340580d00c01000c0d0000c0d001180c00c1c88c0d08d122840040d00030404da0382c0701290050303c0b108078540d085041840b1000304c0c499a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 358564487 1250 358563237 358563253
    0x150406080304080106121509210e040c0c05030d050c07021201020703180e06012a051509011415040b1810090c020304050d050a06060b04090c30090c060e03 68
    0x245295030b1b5108040d006160141c3d640c1200b0410401041401d0742261752488400700041401b6208504144940b0503850300a00b411020f0304210440340006005018065014640b80104800009455000341d034045c00107050780350100200064010130900961181283c1c4549450420640152010502ca5160710503491a4820303512415030f102d001d10034699083c10b000498962143d0b4003094044c0010340d0602c03507100000b0748100c2c40d000c244420b0382c0d142d201483d6580ba62200c4450031b9804500000200101558102c01c040c5010007d00703440602c24a000c1c0c00403139980c40364800183c080300200041e49040c0c11410701d000b900801c80f420085282d181e540040c0c11002d6001d040c90703510240c0d000d5840d150510013001001e100404060350144900038103040026501e01c13841000c2e10207840f0071911640380070507200c1500c01c00600c1004010000384101c45215103049a9006840b02034a8908035001c03812000004103a080e40103860540c00c0c4a00041c10390300b0880b010003480301601039840b12 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 358565737 1250 358564487 358564499
    0x90a0b01080304140603130606090b01080610050a2a0309081e031911060403050316030219050a1215060306051912050f01020c030319051b03150406080304080106 71
    0x10f40120f1041c0040c40050000d680b03e545030410045510504031000104282100c1d100d0508039a070039046072007629582c0c4c0c5a121b0941e004a580c80e8480c2e0100d428840007401040020140e02554103000180403520300c0b41500f102580d004140104a0076451b000d05082d1402c0041c1210054415a200717406070388000159240030084080000c0b610b18002d5103003240e00c071651003a00c11914144400c20861948812000314240301701c40c020f60003030792400c0d1682400c10014001c000380c503101c0070070f00d4410450b2a440c0d010041c5140741c40c05460070311644a050741d6109444040e16420038451041c40d244000c07071307a0415103c074a000e4a001e0b1f582000000c1c5c8403414084000038000300180c039084646002c01c0810504040894928840c1040d2a02c1b8480354660030f09a80000303540001c10381000c400c00c420b600c400e5400c0408001c01a000380b00c0790500e05000251040c6802c55141000000000644032030f841011b54204141e020f401081322964846002da260780040c01103035544d5090000008803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 358566987 1250 358565737 358565743
    0x4060506120c151c020d0e0c0d0b01140f0d06050103110a0f050405040f0b010b0301230d03030e160f05211009020103090209070c1406010803071514090a0b0108 70
    0x31a0b00050094445030b84081c18400054202500140741c0403296002c1d240d80070802c0c00503145041c035000c8003045094003036031b241b0304186007041d0450080140001c42400704004141c07403411144411100c0d0a0380000c400425404044484595046001458824200195a0702c20360403a400f035411041041c11000401428809500c10660041c48004040c016840c0550110707421a2183c09445988500c9988160000000b40d008401e0340001000401850b04808002c01e03188280b001004201c41409000400c28601100050201a0369096100840e4070800089d5541080a80f060041e550760341903103800401a401814020507014401c103081e4000346d0080c030181001d250240c607502901320034144c000c0429050a81c10151219032420160b00d50307642d11030080340542d40d0403071480c40c00d00b07089031580b000b030780a4910b0364000c1c80100300000e400f00503100c840794042c100600a0740318110000250107075646144101c3d00000501c0300c0d4613000289400328074410074084610780c5c1c1e506101c0c0e031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 358568237 1250 358566987 358567003
    0x705040b0d0b090c0a0806100f0303050d2d09020f120c0d1b15110a2003070b040b031807030510020a030e060108030c161a03040302030d02030406050612 67
    0x307004040c000e16800001c42145100341c0c090210001c60390b15044200008064464035441550310381c1201d014000d0441c0d584120802030500726484a8104d850b5503001081407041840001010b1380d5410b00003407903920042911210701510051500c15901c02c9003c00080c40100000c91042c4940800c40308241031030143c000c2c0c045072010160500c105080248040d420840c0e400f1140c4c0c00002070303100249140e04a42c01c1c00b41c581703010b440d15441404000a8101c0925039529034845d0700c8115071200050158a10544590551180d0b40c1c0352510300000c00e1030000e05410400b266540450081500041230b005180f050702043c541500c101e041c926041e03180d02d1680005003c9401c8001c2c40b0480d4001c0760014104c0c0d801074540091601d004211680c14080282c000b252140c0001400d00354129040040b80c240a0030265540c2c80d40c2d00d06050310144039015090060000400700024051500a0041d1200d0001291083d9601d282c18035020b0014001291000d01c03406104004542588000602007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 358569487 1250 358568237 358568239
    0x1806060906090c080606070f0f050d030507090512071716030f2108040803040c051f0807030b0904021212030408040f090e1005040c2615070c0803040602090603010b0a020705040b 78
    0x1464028140c403460000d581d00007003540c2703229042c001000000e001300969051040d590350009401e007004240148901c015501c914459010540541c01c4c100d80030603c00300325000701d01e400c004031440d0418581007030303164044658035410b48900081031142010124032400c0c40744607004903020131a1992151001c1ca080c7d0701d0001881d501c0040d002030052002907410030302400c08003461642e200c4c00201ca04000c003114082a2644210740e0071503542240c2c2e0148c0210560130144810207440780400c640e800c00800c00b91140720b64101140d80030006110041d0302c00990030340c0541d00e103484d040822440e401882035205105200f400050a4a80c41c82188c803071f611803001a084096201ea00040078140140041c0d4408000c0c8600040b107295015a40201540f009030003885041000c80140c10101c007502d8411456266204000009a01820140303107683d001070565126140c4d070820b94000d015540c0200d030000000000429100c941d02c0140c85100b540ea4201c50036641c480b01880700351000c00c0390003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 358570737 1250 358569487 358569499
    0x1306050a0203030412031d010c030c030605010f1206030507270504080301050d02040e1b030705041413060204050415080105091b0f030f030d02031f0302010c061806060906090c0806 79
    0xc00e0004005c0f6003603441c00061460040b6003000000c20104e600c90034440700b03003002c1c1e5460465003211600340c010808485040e04042003503600d0040081c1c9580300310388050042040c14404e09210900da80d100a02031904a0111000030791a48000241c003c421020a003040058024800354003c1c50701071540300740d41c81030b000780c1142d1038602030104020920201f02d0344076072506120b02c8039200800041c20940c041010b41a442c4110009042c01c11015403c068065030038aa141029024154a666081030480503001441c078003a041c40030081c000d41d08840c0c1d125041c800d17408a15044040b070340081c3e42569008215039222070708500d6441c0d806656690b002e11416002c29281c0c50941503510091380c01406542e40c00355140c40d03150643c1d0007043c03c404420781c080288010208020224a0044c8025800c10030b40c42c11500040e10300607540304001c0855450f80980441290030007248403845e58130090902c45142c941940c5005468103000342d20310a458100710701280c520030018030740035110181203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 358571987 1250 358570737 358570741
    0x21504110108102103021e01020a120203040f1b031b0e0a02030f0105041505030604080c0607050a141312140606010c0221120c0c090601030b130b03070f030303021306050a020303 78
    0x42c4a000d0b9482c8019400c0d402415107400306040907d011120041140000513a90690041b001c0d01069010000480c05031040c070400c070006085850302c2c012950070000201d842c41c1368840c0c401c01a1811340004041600208603680c07d01d4400d4008401c2e68083d40d105209030b600c00c04103400324002140c000800030710490042029003826400319034030302c00050855118a440d440842e16148081c0d804440c00c240016400241020071710860350082160b150441c50000200401000d0a550141d044820b5000213460040700741303140301c801d005080c4100282c8070740d55070303050480c480c40240c500c0301e829008001c0041e13070275846081040b11032a4010f0100d4144e0800c400013010300740103a041b107015071048911440b10b02c85640003401e0f0b0644c807200109030800c0300d24107200e80c1d140c01804050506051815051280e901c1032100035410400b000300240c05150390300007900c0c20186a01884001a00b5240401410780c540c004110304481d8080750204e85580c0c1000300d81d6841400071050040e001400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 358573237 1250 358571987 358572029
    0x40b0f0906070e13110c0f0111071e060903030207020f01080c0f0715050112030e03030f0f0904091209080105010509070206010b0d0e01020f040302041404020a0605070302150411010810 81
    0x95184000300031302080c0302c8968a1065000301c519012207201c2c20540820031102e191030070403078498242c0b80b40c2d0080c80401c0001c45000401c0c01100701c000c0a6080e0fa640500b400d00600e008014625001001400034041c48c1c280170b4029405860141e0141c0720110311520b455010320f2400e40078140c0714020510700209200030701c40d19044540203c421050800a6802074000c900801e4042c2c40524003003000311801d440d0240c0706050786e00e4142d0003034000b4030411101440301020f44120004c206009580d5600e80d100090081c40301c0c40d00209008810a10f4680c201e80c4402d80748207454580000b004580d0300c038000c0040b05042217a001d00164000c0f001030000700703410405407141106291001c02d003031a40408850036600101c84182c4100320106003081035140c5402031206050002107204070604103034004c00c60100b4540202800d100c00050700c44209882003045c50716020800940060905041c58051035407019410300300d0018400c0008030740b9a2555580301000c0721403a800e000e030090a112 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 358574487 1250 358573237 358573247
    0xe1002031903060302090702030301180e1c020102070204050106030203010915140607031e1206050d050714010509090907050414100e0c04050d050d031d0a08030a0905100203040b0f090607 82
    0x4200881010380f00e820000050700e5600015010b0701d0981c010355100d40c140302e200c00460b903090b03802000203410704414031000140814024452882940d810100703041c10b110981c06880b40c00402900503280c2400013544541c598090350580da03c005044c003040c4680a0b101410039100e00415080b000706441d90445441c162000b000da1912906200c0100b80030118000e03405003801c9044000324044410030320f4101001d10480c0e0150034100d03107522010310981c5909540f900c8500031450994181d805055850380100142d652243c002009511103144c180136480d03c8100c1840f501d4099414940c013500b0b0001401101392191903031690082031503150108034016003001501c01c0c40b03032090420021031143c0360b00d010051154042d20041880740314401d0002d08507501c92804e42c2541c002006414454040441c0b0340b01c5164000d0303199504c03a15040c0300d0b00003c00390b2120003000703445203035128148081325070041c511030303030060760b6121103942d426480c803001d2881240c2c041c485030000c1001404042c024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 358575737 1250 358574487 358574527
    0x7020604090f06080d020a0614040f0201030e0f031305090c09061206010e040c05030f091c0311130e07020d030b0d0b130c080a020a08010e0c1c0c0e06010e100203 71
    0x2214000c0f848a9a40c000c450401901d40c0208005811295582d010f1008500415894041310103d081c07503403030240c0315400c07440350911009040640700c141e800ba0b00501000011030702e01c0e0031010382c2e0b985d0744107401c03040d03004903903110381c0d40a2006138000464040d016001d44240003405041603152008a040d901c1808900500140c14888a066120b01b243ca581c455458000281d8480c5075507420800012510800c0040c0b8500095000410104801c40401100c2e030350750440707013004215070141d43c251151074011341024880d4501c04500000780803003002c0e403a40c01640140c0a884a02715080c000700c0030743d258600302980260110b17441c2000920000b65165101c0e071495104100850365985272940c2034525401400b155002038200c03029444e04507118001000550002c01034009014105501e0744181450b580c82007190283c40c00c0a6519000e107e00c03d00d41c40302416206a464840740c10405c0400d030b0b08240094250242c80b404d42c10000002d9106100540086040a040b410356555000007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 358576987 1250 358575737 358575761
    0xa05010f06051f170406061e0b090f041d0303010f080105010602031206030c1f270504050903070602190801063b03070801050a0e1b0607021203030a06050f04020702060409 75
    0x1130007100c05442d6154400140101c0c4110404a411858242c84050650440d030080e171124884030820071a840c04082103070341d40c4d50141c54540100b17100c2d030f000030020700880c00f901c1e41744004141c821000000100065060345c042408a8002c10745070014117003260400d009250160f402000203202d20002e00c103415a0101000341100c4010a0890100e05580b02e00c9a4004480c0e000c401203010060300103101c110001004241d040400c81c0740200c0448581e840d110b024042e641d9100841c51044050003198441030300035005642d9440e9050701420105480146900000c000b00004292184902c01b004665454408851501002c641072a10000c0c003800780c2c1210301070340c5001c4081380e0300c0034090070000341032542c0001881e10700303906d61000392550109030902d03a4200b1070402174000a103142c81070303d0360016229161148107030710114800e8002803441036210700c004401c11841201581168060701d4040da40e601409210700c082c00140c0c014444003c1d4000c1060109020f0011a5400101e140c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 358578237 1250 358576987 358576997
    0x70206070c080a230c0a030806031504080306031203091501150206070806060c011a041d0d0806040f020d0506010e0108150409020a0b04060207172b03060302120a05010f06051f 77
    0x615030304e01e00015448800c00c6a410307080410000241500070f600315520184c240c0c050054120780c0c0d50b0841904400078002401d140d0040003040460f241003003080700220481c9551a0740c7e041030900155107081614000540003800800800d11510814240084c4103031500200101c0e101c040e000d4516090040ca00394101409000c682071a40d001d00a85c54408804040801c00c01c60340810711080c0c82400c2d60003000500043c1400a201c1c0c0000f0b00310701c3c032210915102105499440000700070b4882e14074054140ad001280c0c60391007580560207903009000988074540036844903801510b42900490b8001e1546040801c540e03207030f0406402c5442d1041c4020308040343c15850b82c180b10a43d400941201d00180e0009906000003081d20b01e00010074150782c0b0007004202c83c0c4524400c08840c84224140985600d00441141c0c98040d400c540081c5a004103041d0030821005200d955918821805403400c0d82840030f4010340c0344841c481c000135143d01034540d140d08400f51090180703e6084441030400c201c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 358579487 1250 358578237 358578287
    0x10f091e050c1906090f05010f111501030602030703180209070c0f02060a030b130618180210030f0b0a120b040503130b040314030319050a14040506070206070c080a 72
    0x143c0c8801c000400800c0c2440e0307401125051400040a421300b5800c9404501d1150f1414011680c104d0302d2000700401c2407601c5a01041c4035800720b820030741070001940c8000d1482d00080104025078000c0e41c4105650743d0200403880a5101d000003c00c0c030804044d400c0740f01d541c00710320381501c9610704190a030300460100030910321b550f012640075030004200c000040d0740c601d550001880c0c001241c00c15224500340501034241840c400100500030605080303104c0d95518000000000c14955a10754250020244844410b4161016000c1c140c107004002c1a01c0c50a10550035078a003800141c401d81e10001d1213082403030703240e55942105650150060b90b00b841300b80404500703040300f64982c00c0906a11035009845a19500d0842c48a00d07890200c2510f0750010310401507500e038440100c0703004011000d00428141c44000c4814000c01d102c6d00102503c0000d0310401061080000f102c60007503081d07900b00d64203940c46040c00c550f055000840245502800c01c15104071a2203891414010382100011085078 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 358580737 1250 358579487 358579489
    0x3020f0d0b19061a04031101080103170a0e030a0c0501031503200d3005030403050a030c09080f010203040215040f0b0a0e040c171f12060207020d0311010f091e050c 72
    0x28860102d5414000c0b02c001014000c0001c10403001100d07c900b800e080d41254119a00d88041500b2140c06440e01d42010403813070388281c0314044848600d070b4060250390701d5040c103084c03140c170010203030140c203010070700300317900254245000c403a50380840e60480b040300072040b2603100c0d044152010b400c0c641c1d8401c6c940101400030079003c41c102540f02800300500007801502a11048042400c02003000500c0824820403004c40d40200440b100c1d00b82e58030780020350801440c0c00392454000c07500440c0d5a8401c0c4107400c02d103002c056008500450084619070311112040440f0305540c40b0b54001c401c4c840e903150804120111190740501100c0c81d071410401d8010140301c01003001c0b2000d0151810002d040080f0001c58807100c841069005800c030110350b0303055001c10b00300f082010002d01c1440c2882514102c64002c0c130450782d06880d031682d4004e03e10500c0306c4441c24020654071059103489415440c2c05206115410244540b98281e40c0c810343c50a11421441d0082c19461441c440950b04c0340079004481d142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 358581987 1250 358580737 358580759
    0xb030c04020f040303020c0d23070902040b04140f01020307030f090b130302270601110a05070603020c0d08130308090f06070201020a0f02151314011503020f0d0b1906 73
    0x118110110703591600d14501700245000c207124103072809082280c2168010031507200c40d0008040c4900095001300e05c08280040c5004070381d03404010354910100740868a8481000280b0458a0800c8281c2408444800f00402d4444d01c5000780d0160307004200c1b040000780030b583e428924100034204140c0c001c6c0d480340d0f40e00e400d0f07211b489401051600d40c2e500340300b1407500c00258001c41200c1040000b581c1e104000d01d6000901c003801550500c084465005103450003002104441580070003650320700303651407101030041d4124400a40300c50040041400c1d038644550400ea00c0340d000c0ba0b8121007600866241514840006042008507000305100d480c411202080014080c00842d400140c0da02c400758401804243c0d03c01075001150800c0704101c811203a1a4501600f1007014001300f02441110f1508071510702c5c010781920f205509003c0d124140102c1111001c088034002e89898a50b100c000d4100000181c420100038210310310307070001c5450b0383c1e0b44150202c0c5441c034501000070416102d138402d00c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 358583237 1250 358581987 358581997
    0x5180706181e15081e13200301090b01080c0102030a390f0611040509060f01030b120c04110301180c1404030602090a0621090201090f09050a0507020c0f040b030c0402 73
    0x200b004602800b00b401002d001700d0f01c0c503520441c490300c1c5a051201010640c400d003110054800c0e541c0c0c02016070704105804041c0e41d098001402040583c0c240d160000e05d290003446003c00c1d9000f1813041c991107500100889281c00d541d50350701c01d0f40b2810f184041142603d950300c05d80e81200f0f1200001003c07080300300086070181c01842e94100c03940c0309184c80d034103a601710401111f0f24003080c4002c010742c0e102c0c100741c3c41d0020811030750715400b01e5402c0012030007403521054207a40124505600c2448000c00f04200100c10002d0750140070042e0140d0f448600343c8001c0c030450340c80c41d03041000007800001c29401010b6410b040e203000d003014040c001981d0101d40064006580041e40010500c081c0d18101e1115801840c0f10b04004640019000301b054a0034002100d4564403034071251300d001168810130820001d40051110011080d803106611002010111203400116142c070340070a110302d000081a01d04070100906200f08540160203210190100002003070305403040300710761f0503540c0c1c41c0e0010300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 358584487 1250 358583237 358583279
    0x13050903031311132c10050c0d020417010b01030920011710090605030a020a0302060d0b130e0d030e03090d0305040509070e0102190b0c0a05070605180706181e 70
    0x440e022540040f6284840c0f18901e490345d00428540c400405400b01042050a13801702d00c0c0001101d581c2c0c00d548240c140300f54080e80410134030005001c200102c4100d40202c031134640e04020003100f00210300540454a04070b10141c4000ea00ba21105da08640342d01984008100c10315001c0740f0030f001383c2000301094005640304071a00146400c280145450f5106034001410110000c0c0b0740403500740c005c20b060800c2800041d016100000e810400d20b0004c0c0c21844840c0340c0901842d628418101140d401483c80c0007280c402402080301e1a504503100b0f01540d4121642400510b11b000100b40c10003403103405402c012401c0c441c06100000d180d80d11891a03a100e9652a03c4140d040c13070b201d9000909007140302a0b941d030b0500d0000001c0c0301082842c1c100692015401c0b12641d9a4603204000360b6190044200003032800342060b0401c400030046203c2254000d009a045074105038481e18296400505403100c6c00e1815501c402c2002101e00b01800d1101962200c60619034a0391180c03041001c08032030601203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 358585737 1250 358584487 358584491
    0x20a09050114010305270a080703021b1206180a0b0408070b1006020d0302090d0206070f02131a10090308030406021903062129061305090303131113 65
    0x402c0758000700d00b10008501024a8100218a450902000c409118600c013800245a850410300e11100801a034855260410102510b403c4c07c2e140095945c3c2d0100b101108100d1144030031401070800002c40d031031803542e1101820850f592030b00b3340401150f0320a41d04400744950600200882e0025483c05e0255024035400d0742d40710614100001d10780c10103040703c461070009040c100211640400c815101c1034861801594400441c1c0000300401d84490001c0c5d032100001580000300000c0100d9501d40c80d02c00c0c0d42c84006203000e0305030b00b000c41ea80c20307000c01c0e080303542481c00046500d0700040e15407442d83c00d8185504041d0320b944600003a038008a40c02ca0300e043c0e00042ca001c80b050060004018140c10b8034084c42050b08100e01964260b40104d40302c61110b2040c105035003002840b040079200900d0032160b0340110740b560310000d1410481500d501340214241c02c80d41c1c004a400d4004d152007200844015481d503120707440d210001c009000c0098a1009602880f842155540f00042105035041100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 358586987 1250 358585737 358585739
    0xe040f0603020306060a060807050f13060201150801020a0f0818010c082a0f18060309030a090f0302150a0c06051503010b090402090a0b030a060f33030803040807020a090501 76
    0x1414a44031005c0c0c43c4c240705d0320030341030200b0105070300922040c1d210006203000703500c40d0245003042040d80503880c12824074540601000c106a0390561013b0708840040b1100654580d075a07000303900701c0c03042614a00005100011005040d4010540181c0014100029401c8d003041e950741c1508480c00b0212810020341c0c0341081c0084003600c20442010041d051001211201c455181a120b81c4542d0b403282d03514020206052a048900c01d03442c009030340000c4e02c0c01d5039910788594260b880c0d6000c41a40801300341c1e00c200c0481c5051182c1e1442d82507d1703001d0030707544102c507440c0f00a514a0304460440000c20100305c074ce02000400358090b560060b280d0031140d1519101607000c040c2500d03440e0307600ca4080c0c0440803c00016a46000b001504003042450000d141102100420704000035400302030001e0342401601c1e02e9401c1654810180c1005002003400c1000100050080c854006104034014400d40c1c101400880c0982c001190454450400e070707440e0419542c0411005c5e5280c0d0700020040da59640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 358588237 1250 358586987 358586989
    0x8030406021308030a05030f0411030609070501021005010b030a020c03130b030a06050105180105130b040f03031107080d0333030c06020f06010e04031110050907120809040b010e040f060302 83
    0x2c42010f4807858001c2c40c1070000c81c60000b0000c0c0002131941b0380203081d034000b0a042c4500ca00c8171240180e0068262900740c0741024400e651140c40b80305460052080340c0c2807150109243c0318560680d2002c00800d40795840c0c405000c0065000780d134410f42c1c0c50008000f1001c564007030380c000d58014420881e0158491600d00c00d140101c0d070465000c541400410000c1000f0032003221030556540e0024201161110100030754841d00079001e07040005480c20000e004104000d080524104580c401d0341c5800ca0185040c10780c94440441d881041c14030b500c00034041e0344e000e0090b0800107152404a0b1025000d180b866001110503400c42c1c00d0302c940d00394103070050050007820420403014005500040c064081c1064110b036607068144100540041c0d110081070425200b09004940b04104108075280702d10325260010040c1404e42c1e00441500c11081c00041c5407165006808040d0b4100d4100383c282031061007400080c0202020907030400c13004240515443d5124030460503400040400054240d05502c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 358589487 1250 358588237 358588267
    0x2d040b19030b01031a091911071101090e280c0c1205092b060c021605010c0314031305010c17060607050601170a120e1f1413030803040602 61
    0x2d406070b04050404520100d0850541111514640306031107840c0341c1c1d41d4522520410740d1701060700a00389030402c140d201d0b103020118080c10005004015911144040d0720043d03550100314071954104c2035007840001c03008920360341d014208212140c085070b0040c000100010071100e070b10a903400030031a4400480140300345140405415601c1e41009444c0c00f152200140817600b600d81c90105140c104a69420b0503c004540c12180c254008018440601c02140103500c44800308100c61103851040000070b00c540c81540400482500350b240c0c15081e03409420000d00940c802491a01d0104040324041c002170400d02c0740404210b803d07030300c0c00d00260848501402114001e0036452003003a0030302950b40421000324190341181c08809800070895500c45810303040407441003020b014103a4040d200c0c2445900445000c3c0201000c450100c0e0001d90001d11000d501c48800520001581e281490070588000f07500410402400e0220703414410b9aa544124156008450486030607401107a036000c009298 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 358590737 1250 358589487 358589501
    0x14010906051009290f190b2107050f03040615091a01020a15180c090b0405060108270709050108010b030c0105070302060f18030a0c020909032d040b1903 67
    0x51100180782005031007120f003094981d0f1341414803d15101c0718200c031a9071562004400c48102e024511003240d590b0030240d1007600401000c8502041501a0f000440400080385125503aa034440c0c43c2081168855500700303420090003150700558034514a4181c0c0182c2180400500011201045522400d10b040c0c0362180341010650565010590710720004a01c038000104181d0001030000e40300c02940550b2171a54096100581002031814020841052942140c1400e000c00e98042c403035615020011550039208598034840c044691400c9842030040701d0315810030360758050480d100b16489001d1103044580a90041d4042d030740d0740840d407000d800c3c1840051062002402c0160070440c890314082e49429004080003400f00c20840081d0841c1400101a00780d4200714080b00d85070203802d48058402d8a544200740e2155a032100000d5941340000102c03908480b50180b695628942c00c580040700351003555102d4496003042c4808517400550350054018411441e40759280400f0040019080703c83c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 358591987 1250 358590737 358590761
    0x109060510090b0303070f0c1a1e03060f040504030e040e012403030228060218040605221d1504030f030501150f09090501060504181814010906051009 66
    0x14910f0519242e600442170302c00994211107104e1101d400c0389001c0002450f642c002012251030000515906c2d0340c0e582c0604146604031408100020904a42014074042101c10f1a80700310401030918650800ea00003541042c0b0905007445031081040000741620703c8000142d90b240e40d205a940c01c800885003c43c40501e100c2c019001d4600e045460003921079004d26500385d40e40980c0d14500d08010004854444070742d0f0813000071034540303440c0c260340c0c000040c140d00b80301d218505040000c2174615180100d0760441d800d441400558480b0700d0009005800c0f0500201c00c241d065682c01d0121500900c0b000c892078a00303142c0780844d480c040c80c0140c05500480e1510341003500c2c100041c4500e007030300c02d902c0c22910844d0519600c0d0401d44641102c2006180d000110814101400000e91315006005401078409034042d80d040700040307001d404101c40e04150400e91001544a4010108098a0700001c001c56800300200c2c0300e440c0354640354207444055615030028407404100304004400ba214002d00001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 358593237 1250 358591987 358591991
    0x16061d03060a0f05060f06190216060c03020f010e1b21071a09030303040b1f06050d0e01091505070c170301050117060901030b070908010f09060b0109030302030d02090f03010906051009 81
    0x1140c40041a9540900101030402c944641000e502c3d0500030404160042502e10444012b00e441d00780042600b0200402103003d40305078080c16141c50011300a207001c1c0f0711400c0040450140d0b902c0c1c0c500c006018480c1036504807404d40c429480d4101407649600503030705488001d2484928181019001010004002c544800705015044140d54080700300c0ba002078011001400540700d00341c00c0001c00700e0070400b00d688120325120010305645c00c100075158074113a19a04005070300704c026026083e02e0140d40004d00c5d0011030555180184020f40c081c68011900c1e01e01030340d881d0401d5031920340e590040d8140201c5048040010406c66a00002101e030482c1081910782007824080c0110311400b5040c0001007041c00c1c0d540006003820b1003407420318028004a002441a500000140c0c00108041c0d0801e40301c46081c50841240c65000300120300440764560300440ca0101880030f07060003500a00c014a41c00f9200d00c0301c2028030b83c0d00740111954540508070009203030421520303c0b66684055806020024 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 358594487 1250 358593237 358593259
    0x60e010807031a0a0e030705010e01050106020a0507030b070201020c0709020403110109050607110415030b0f0f0f0106050304030201090210030510050307050604091a040603140105070216061d03060a0f0506 90
    0x408000742d407020103003c460200469220384101401500074200c0d01e81840c8000300380318061040540201c03060881900082141d41d80b100c4003242c0b41d1001c2030010b00780b5485194104009990007100c1d5504c820f56100050911007441341d5a42001b200782d0080385195000301e01842440a40307041781d41c0c0c1010900706a45e0f000c1c54440441c45a0190b0003001d070808a5605040849403569002800e08503540c005140e0400e44a140ca44980760040d146040346100c180f0015040c10780092040c2e0140d4590804604280c1ca008011a010780c0300503c103c0071035403145010030050702c2d07401c0c00503000002a240400c0d14500294140d582134101d5200c54801d81c007061042052307886100485043d9180c8240204004198490300490428084451600f061400c20000306000c032801c1a07a9441c181080280801e460700c01b0200e944d142018010701c6400c100700e1080100c180100d4684181d00d01a44003850901c02e01000030f03003881c00c03c0751584e2896440e180000342074415071081d240c2c4041c003200c42c22100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 358595737 1250 358594487 358594493
    0x1e030815090714090d0209010b0a08150108040f0c05060316030b10080c0d020c0a0f1703040c051c1205090f0111060703090c080a060c0e2e0e060409060e01080703 71
    0x3900810700110f40454002a035500682c0f9084c100b20a1540c001d400e040c0e095075540004074082d0300c8191214000343c501c00124123041c162041c0c0c0d00007100169140051502c440c1c131000c003003006842084070035400007030b80082d07140c4440001e94400c1040b642c504100c1e814883e401f03020746a1480c8450301c168000d0380100c1c90260132800a0f0342091034811015110704091584400070300c5402c92041103442812500c4080182a110350403079030344200c120901054a45074480005c0c042990f000b0130265440a0034040c90500390307003403210900f120940c01e0940440b03841d40d5104179030104100c800580d0005e01c82109042284510908440a1070700300c004506200d00307140c0303883e00500170320101074650006105000030403203014081c3c10446c0980d50101c041e0302d01900284400f005080c08100d01c1010f4601a140140c101c0b084803c00341c1d0309094044800425000c03400c0095201d0301404000b40d004603181d1034400150000e4502070b5000901c3d00d080010250710308405a00028155000360428400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 358596987 1250 358595737 358595747
    0xb03030c070b0c0f0a0501020c0106050616030c0206070f031e0f020c10110d0806040b04090b040b22030801031704081e0307060c08150301060515071e0308150907 71
    0x2110040c580d4551941c03411003c05082c040c0c411000c1d8020b1083c54a10424010190300a16000350003e008011180e601c83c180483d40c022070406241c81d40b20350b155000403074020704000c840e603403000301100c0c07420245039150444000e1603001a000034a201f01801c0840b07c904184001d404094204003404d0681054020740c1c0d032075500701060141c131a01d900360b0030040c094065484203485443c141d819030f009e1035400600c007010444130300e41308134104003d028090603c2d2086800d52600318146108507035954a541e000e0080103819201c943c00003602042500101c040c408800314030903602c00b800c0e549942001051040d18203804204001d0801040100703100004505800d8039946010104050014961070b080d409190000761480341060f03981c01001360700c450003070303c6104503003001402401e800c0701341741c221411401026005840707010f412070360101c410094007000b440344910340a41d10b0412400b61580400003403c80100700e40005200c200d90b200134507900707840001e40310060103160200b40142 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 358598237 1250 358596987 358596989
    0x503061003030c0c0902120f15091f09020a0207060215090607140c1204180e1b0303090303040806060909150105040225081305090c090906061c06090b03030c07 70
    0x1c10303c100d40c0c2d03402080011140c42407008101c3c04c0d204640f5802601c600c50030b90401160b01503503500c881c400040d294a00340c010300c41e81c82809401e020142e51154a04417003064441c080c602c1c521420360b00001e07981150300013082400d00750350240c00700c00e2610310060300c1c0c800700c182c420000490071030401c940740d800010300c83d0b03110006103086842222a1500d4400c203204042c0204420b006000002504150a4000300201d0f000341c80f90070b4882501514020465444240c0b01400307401210a0448440041c000b50700000001000e42346425080f00002e4616449640020019000300c01044a20314080000320341c0000c0a1014101d414078210105280f00414041c40f8840c590115400d0881000392139000b80c810f4071044585000110340c1051901030300103050078130038144aa900030919040814a29008038a403980f00f50810281004118124400610300d5070424028400144621b0881008041d50706642c01d00090f040d0a2203540c01c00c3c1c0e13480201080c001e0b4400c1014650351800024840 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 358599487 1250 358598237 358598243
    0x906191e03110a0c02010c29130c180209041b08010b03101e03050d020604050f0c0109140d08030a06031a0408030a09031e02061608090d03110702060712090503061003 73
    0xa041c00d813030b62005a030351101503100a4810b8502c0d0741440f202c0700210403001d005089801c484c01d02a511b03042c14032414500754600800d5000d01e82c02c02c00001a9800030709411a0f98403502604290366480410101d0b42c00c3c01a80c4060955280351030710082d0441100d9015124644080e4910b103404007682013045124421130783c02e1080d0080c080d280607868001c00000d15405000d603284562444030003907a0311419601616a070156001c411068200054581c01c0000c7c10b850318001c2d20b103449009603483c0410410720750028070641202001413100710084d03202e5440c0d944001a4207055041031400384800495054150608005000c08510341b17805907548000880c01c0030a1003509460100e0f42c0074051034044060809004c040010703990045119841544034008a0115600000040706c080e401034079402c00c980c10900b01089030600c282c0040c3c1070400e40090152030021184e01294107540400c1c015540d05540d41ca800c0c22244c0d106560701c004090440c01031505040501c40c1040c0c82d00c00703100003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 358600737 1250 358599487 358599497
    0xa060c060f02070515062407060e0708060907080a0b0a050916091d16150203090d030f110a030801090b0a0509070206041e05030304080906191e03110a 66
    0x401041029002510001d9008009549400300751619039a02c242143c039603000320007541e0000e210b60a1408801c0d0304442181038820108500c9690320000f0b40c0048030a4500740c2c0c0fa54800c0450341800c0005c44000c1210200510803840c02c003860300d0400d103182e000b08035a5000b98652a02044005591a801c03a65940e0700203140c1d21444c1e1802d04d4006070310704055a40c404810300080d08603840d070112411215501c1840c044d00312030607500da100c5482d400014822040c01c4814401c03404c007170400c2c005420060048918040c1d0540003d00c40c140c001004400050041c140350181d282d02c5010303000c412014000a19441072103942c060b11603001400b0701c1004135594070700055a582c604021000404010f0b00c5c2110b03074145490002c0d22104100e034140c0742410400d00d15086040074213040c03015150030002460139905c9035502e900465005c8030010b640600103000d41c7d030b18070511120f00c8030300283d0b0b03454180c3e581d04c0800c800c062240d01724040e80e041c180350000f0710302040d600504603140c4003241d180c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 358601987 1250 358600737 358600757
    0x106022103061309050105100b070c060c05030706141902091f05041d0109140405120a0e060d06080c01051608220e0402011d0d20060a210603020a06 65
    0x210f448444450380c0700386043c1c10700020500b480700c1036000a014800412001034a16154600441588aa010004c15a050303a502c100300340b61052917041e5001e40700f082684d02c3c0c00c10742d07141e00c02035410071240d9645441001e410711600d54855a0501e80c08440324100b9400d02c0c0c840700010325840000d440b40d9000d09204499100440c2c4544100d50140100b04003100d9450058042c52040d1242401602c4c100d40c5401c01c7c0d507459900281080c0e10482d4080c2c000c00709800d49003000801030301f00710344071400c0c080c440c1c0301040669100c00203801ba02207242c40014401d032404441600e0b0420b04181681442810443c41d854001d144102e403580c5501b2000081c1d4895001d00701040858028007e190320881015001c91035014a00300180228002d83c0c921140c03d8007403e04090140e00225501d600110400301d1000141303841007108042070090200c40c51a101d6403001c07070b03030341c0c0e02001c100c400180d03100803607480150450800c08546000110100102400d603030104400302d038140102024040c150710 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 358603237 1250 358601987 358601989
    0x6030c110627011404020307050a030b0a02070c0e0108030c16380310080f010b061801020f0105090102070204050906040f080d020906120105012d031d070e0609010602210306 76
    0x418540b10104010007041022800704880811860503030b0124480c0c003d030080010b451600340d14080549410030400317400358444006a200a600c210800c448210940c030000035581104191301d402000624040d5964640e01c02c00b90b41000e5810355050bd10b900002070601503e00700c01040c0e400f00f1322040103c040c2505440001280122410540052190000820200c00c1050b10b4102c1243d00310411100001c5502d44a0703420b0f501c1180c4560782200c0c00340105288013518540960380d004041c0107a4031109503107180743e800d44004607080c10440c0c0d00003a140c0118242803080a0344612a1005404141031594074210031040510003c0c0948038081091100d05200e81d0444142080090840d562400d521b8404c0056441c244074041c04211428030040074141e01a0300080658607010803883e1203450200300390018841e4022028412032030034028035001e58100000380240c14020790440300d910f0000c081011041050300315404540000b008403a410b48001c80203034a131f03001922038a0312a07507094 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 358604487 1250 358603237 358603291
    0xd020c07050312040f08010506010e04020714100b03070e01080a03050304031713060b06360d08040305010c0f0e01081e0403030516050403050a2d080406030c1106 71
    0x6048075915024900120b04140c0102008104031007040060510b07059071094030b14200c50084a449021400400c5000d0b014545640200000c40c4030741007880c00070800300c0100c0e00c0c0c5403001184a000541d20b60841c5c0343c910b41008140700034055021421500e43c18040c0060b111024841c000b02889404404101014020340101456400389103001078245850300306130802c241ca660090354014540300d60300060b030501004a03620101d46a440300056175680321601101d403018504002c0581c80f0180d040103c0d0344400c041c01065002c0d6441a85803811428840d0841d241000780c00f080c0410b149440f04444e41040384854071050908110741c60359503a04021155030385032103c140140502108100c2015055404140580405516002d01c9843c1c14030660b42c0340b0550201a040d0f602c900384400018107907000489851404200303111280c0001d484075001040c20100441b13480d0700105003440103590500c541103c0102d03038540800c2c0260900a040e8440350085d01c0109804041840e0b054404000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 358605737 1250 358604487 358604489
    0x90b03131703060901150e19050316050f01020604020d060f0b060f07120207061706030f12030a0c030209060403020d0221010e1002040b16030201060f03030f12110d020c07 75
    0x800180c03a0004081100c1d009501c11a0360601ca03d19800011034540c0e0048010740c5040744a0320303220380105803a0104220010b0310589000d800c0031000011505840a210701d42d10000d02d801c50001490070082042940b20044c0b001d541154001030410016a80326104440c04035005200025030b00c0e6090480c5016003913190305c1903040300000070711110500ea040300401445001d03024203040000504012a2545054850301c8005040303200c100445001c07180e840c07508010000c00311030350f5092543d2101d04002c10101030303145056011041202c0d28166001d0007189442d0340c6421440d007544800041c090f400340340806809000c0258550046481d5015010b8541c052140c02120600040c0e0540740a414680ca07110418007800702c211400660300d00956064981000b0150300300b80483d02c40050b145082101901199201c400009045419411510255000350f4402203086030f2188040e18803820340e0916000e2030324100c8500c0000c10303000182c1d808120008405640da291040410f03103415a5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 358606987 1250 358605737 358605743
    0x81524060d090f0f050609070303120e150406020a02070614041710060e220f06050c040e01180c0c0203070b1303080c0a03020d0f020a111f02060421090b0313 69
    0x8440105403d01c107131081e00c921118410070440b11555280c0801503250015840010f0101d000c0c030100d12240550381c0c1011000b80c490034226200341141001c525403856064601b0341d0096400998081072075410b0222201400803801c2c10101d04040d030900764014811446802d42c0741c0310f0b640c03d092452500340300400c3da9680076401801405e481e128100309005043e1071010030555811009400e0540f603010210046400c480302d0101044d55444143c05002c0080075481001d8082002066040d150042c0034003828185600403450b6a4034407a40c022a00c01d0301c011414403c43c1103511006035400280203007500e4018401e2500d0307540a4003025201d80380d0fa08020405600440c200c3c40b40c86000402c0300d8458000d9080300c1105119400c2501c0c5125202902c0e40141c116103000f1011903240304908101c002d001d00080b403030446640440b540324126400c0c00006030880014002032100e100d1003546c5a481410070700804810b00305001e0300c602e06030302c07850248082c040000782c1121800e280001d0f980390 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 358608237 1250 358606987 358607003
    0x909061e0417221508011202120307110306180a110102070506070503210603060c162108010905070e090411030304120b010f03150b19081524060d09 65
    0x3080355020329150303401202c0410303c511092800a1840c50242440340341d108680c4402c072069081c11840780110500d0201030f0f0704942c25082400345900e08000600a80e4050048005450454010141081070240684040c81d503c01c4d516640c0400c00b0407250a020391000b004a00643c02c800180d08004050b48000d50041020840f6001d215010009007000720b2068540360f143c005a41b2410518102600c4854241e44000d000130a00b102d10001013440900160a100b4500b545648248083c0d5442c04034034248401700d40542074160f04428030901511f40e41c41e00f8000c40c9000100101070002d12296a44500107182c041400c0c001030901d0189481d5001c0c0c141c965407a124071104458100d00101181e100c00711200019480304000d00c50000d89a0081041c05610702c060b20315006448003a07001507210582c4a00084102c4032008454000c0c84038038058400ca42010000c244403400090008030326000040a20b030740d08980b00603c1d42d220b10119a00c03071b1503070503036039440340100b44140300181812 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 358609487 1250 358608237 358608247
    0x60a020405130c3b060403030e0913021c050105130201081518040b0610050c0d1d1306090b010e030a140a06050709030c06210203060301020f07110909061e0417 70
    0x80c4d80c402d180c0d5102400c4841c02040c220803141403203242d11072444068005000600c0c403501616043d4219174002003203280340d000010464001600700341ca664501100d5585c842c50070010410280181503004540803003400240d12103800213441c080d001040c2003802103209020080981e10700b03680124071960703074022023801d18081ca06090210b20980da07982c8525045060302c803145115070104d070440c0300443d02906181120701d00075502014402c2019030800c204170880602d64403011200092079a0924020a069184c000760390111901c404103a41040344140504e14644c40014020f041654041e642103007451003140c059007483d0780000d0081c05903044c1018000d40580c09096401940e02a504950310303d40d5828003039801c10202001da1941c02c0380c02c10503040c01401640699480000074002601d040210b42c00f0b014142e201c504100d810b8141304218000d58200207905a500c228410010080c0c3c0c14407840c10903844001500364002d88102c54006000c1110001501c0750000020300303415252 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 358610737 1250 358609487 358609547
    0x10902090319050d030b0d050703060f020f0d0605040f09050606060f070c090504020315150127080604060b0a0810021804050c0904050a05070f0507050a0c0611060a020405130c 77
    0x10710000000390300086c1484242c01c16840c215000289056020300100301c601d00d180e80710b1001d401c041c0e150310b803856824085001d030300e80108002d00e505209258001006400e05041000300c55000000e9411203240c02101d41c0080c1c00040c1d4150802d82c2101d1030350b15440c0c0e0300c1135020b1070300c140c07a0300401000282e040011080d40c140c00c2980100d01c220306881d085995500c0c0502c4603c801c1322041800c9150900d1204294016a02042d00f2100c60244194201d40c1030300100c100f010503400440c5940c0b000d0100401d11041d44584905860200c6050302200d10380b0000715540c2d10300740c03c48180300740c2c0021070000c51441c00c01c04c04c2113017078050020b01c80da1405220384940d0390030103444d9a00503814200041c00c00c9546100b100d10410903629052440d4031340031001c0315103400001007107449102d184404030201d0300144039880101794665a484d80000e0411246045c11000350040004a006100503c00daaa96011070148052285800205031400c4501201d103070309042c07107805000b0699601c00400b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 358611987 1250 358610737 358610743
    0x3060a051215090d08070f0e0306070207050a120b040828030203010e091618150801020a0207080a1a0a020d0903030203150307140907140c010b090a05040b01090209031905 75
    0x15040d016505601c0360f8410014940381c014a4100030006144503002a4000780180e2100c0301c840058a0a40203031480d038800f003454040199020800750340b0941d0204081e16007162160060300c182c00310807181c0c034004d94801c0c00c0150043c2000340880c00110f00c01d407002d040190f0407401c1c50f004c0b55040200a41020024000358028055940c407007c030303033b40050f0b030003640020402007c540c44507403441500d14100402203c0184040401422920380d00c038140c0d0441c1d103102c00006081080001070349c500001101a1a01305142e1052050343c201c2e16910b4003045989030303504024100080703104284e40d01c000040e4002c0c405c0f0f625a207480c0707160074091014160b040c1c0c003452082d20200c230310b50130141d000f0b0f003050780c1e80a55108060a2a0f070849540c001424481e000030740040890030029443c0300603514403051030f04160080704c441d0b036480c807040506151581800e904144400c904000c030b03080a1b1a0143e94420501030340e0301e0b80360001129542510100700c0d50301c0403c48451700e0011660940b4202da1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 358613237 1250 358611987 358612003
    0x8032b0c080a0c0e150313020414060a0609060509130603051501030312090b13080c1f0c0306080604060b060906121b041508130816050105010806010f0b03060a0512 72
    0x545151802d0100844c1c042c903514000000c005060148058405414002941c0300810424456050181c0d2100507101d90041924441449616450741e1812000340000070784240d00100c20010640010081c0c81c2d0040212003c00d441920100041d5000301403031030190600d98401006840340400e2000090094007029060381e00c01c1d07482131500c0c1c09180301502640c508000c06410b8007003c40208490304440d00303003150f0f0300e48540d40913800d01c0d1034180d20a04003000002c1045e0440405007901c0040885803250000340b0035141030821140e4240310403103544840c0100000c0c00307103070350301302140040e5a100e00359800d5610040c070096655034251401c2d1950f010540d80c01c10b07080304000740200703032616080035941600d50509030f40d0b540c115469001c440581c000f40000d14010160220240403544200052400c13803980c00000303c0c00302c81458a1800c4880583c0041e007241c00003c014010007824000040407178854440c500d450b91106400114040c0850344030319800000c19005041020f00414404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 358614487 1250 358613237 358613251
    0x120201051b0c0705191505041a030f0c0c1e0c03011b0c15060b0409051905011505130b040f23060405040203070210050a050a110408032b0c08 62
    0x40d0303601040420740c14150207010010301d80d41d0003c0000f40001e040c200c00c1c03d204c1807002e100c60fa00455441045c070b40d01c030302c03019610400110002000d014441070516000703081c503020303c105861807a04042d103ca8070840640510001d40000601c109440d000300020041e08152001030a0120f12104121340c0e07503100100d40f20b0107542498000304200041041d80c151540d00340e20b1300d040b0480c40d561865415440749205001c401e90381c40002c64541200009000a0104a0380000312030820307800308412000840c5000125609110040c402c1c4284503040701c81422190600c0c6840c0c40010401c007a0040a5411400792040d0125000900d241400c034800215114046034030313060240c11211101700142039138104d8001008010400c09810b10307074005c613070100c01403054443c40c0b03030404441c43c01c3c0c1c1c0c019118120825182c1c0c084c014050414810540310303000b2681e1241c80d044c0350002c0d540d02c0307000e5045020070300c41c01c40c5c1030302c43c2c015000180208000c00b102800c1204000f14803001d001000256015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 358615737 1250 358614487 358614511
    0xf0601090602300d09030203071a060a060e06070b040b0403080106020d1d120a0f02040c020d0c06020901030b090a140f011409060609041a03150601200a12020105 71
    0x29a060021450140304100d070401e5401210a111150104100d6101c3c40d6808040c1004104120101ea2044140152281d40178654888003800c100e214a000c1500e00308030094100d0510100303540e182014000c03605142041c8500003403210000c0c20324014020044c1804054500b00410800c1d141a0644131314841c0d182c00081da40c0f07508089a80e0800014100042200e200540031080c0300d02440006404c4014010403003044140b000600702440448102c2c1c12066458290701140b0f014045c45200b580c01d84000c08000d00f02210041c0200804100900069400524039555900c80d4102c06402e0902a040141505007100c3d24401070030144102058003100d20007040c035a40b01100310a040700d41c0d901da201c5102d000c0350308200401d0009812198807410800003800c003038545008920051a4400040d100410190306143c00c103240340d0340e203c02e00c2c2094004c002036603810506075020000407600c5001803541c904038003881e04050080140100500a18410f1001d1741500024490310030f00c149 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 358616987 1250 358615737 358615739
    0x6030420220e01140f0405011d030315011404180f0e0f0f06070e09150a080705010e0301020a08040f03050d2901080105030319050403060e0105040515040503071101030b03060f060109 80
    0x8040c02c85004132812041341d00000701180001c0c1000c100c454003d400340740000b800703101c006c0c4600000707414001c0000040d0008001c102c40018a10082c010014080c2040e440460030a5140001d40c80f840c0182c0005480000885c01c6000349030b03100c1c01020718100010051070030400c0e05c40d40d95046808000c0c0444c801c00400385810000851540d010740020340741d454104401004100b800304001b0300b0f2004101480719041c6550b036441da481e0000f4a808405007030300c030707081500042030403d281000500980c010008080c1c0e0303030741c40802c0d16401600715020807210a418602182c452095599400d001070600700540300c0d410701060030300011344c03041c10140403020003000150f6400c0c0c1c0c24403500c0d138140c10a0041c0b407030102c481000b0b80d6035686940742251030603032070b40e8070501250500c4215444d140c0d52602080b0030042c041201001e08403025411152618041d40c91507960f200c1c021000780201c0790a5802903450340603400c0307121040e0008007606d0a0f0300c2c19040c90b054003442140c55034000b070450700e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 358618237 1250 358616987 358617011
    0x4030c0801090b060607020f0a0e06010201060807080604080f040906060504180509150a090215040e01080304030f1e1e031b200d121205060109050603042022 69
    0x440c4041c0b6a60054105034166210010041e4a03002124266005100303102110220303610600d11902401015105a80d5030034828002800c603606c1c0c0e00240b9aa600c030300001d0190301400a801c0c0c0e8410740c4011107a555030a41009810035001b554004c1c041282010008250310b608440a00282c61241074406c541c8203021907100309031202038401c20400e4000b5580d1101e50030030022031a610005000c0c002c0341e4840c481e40030503c00b0a40b1510200250408101440824480250b1500611500000354100707030444c1c803149441c07988913400402107000d9a01c041025034404103990080764100d0100c55141e05d803010b120700c080c09900022030000d62000340c1302c2c46410100501c80d00c01604414816004c0308100c24900609032580045d0b6449100000820001a03c0e103180c500d031506103640b5000030310b0415500109440015000702d040c8552003d060166886280542e51b00903040000e20040c602000061200900d0b1440503542240c46607040e10901e24501c040702c51012136103401000602d07000c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 358619487 1250 358618237 358618241
    0x1050c0316060c0e0f130207081204051b061c2003060f01030603121215091a0406060c061109030d1701050102060402090f101a04050a0e0103080406080403050f030f04030f0206090d050d020c0a0804030c0801 90
    0x21568401001d01c201500445800c102a10163f00318800080003c0840e04410600a88903104850814004108174141c01e1012401550003401c1c20103109150443e0f4900801641030248202000086031002100540f15000b400c0c807041d18a90142001d500c0300710740c00213000f0811f0f00c1c0d8075505100d0921079450a1500c1044111042e95940740042805540e0303010142c40c103640c0c1ea4104030014810319118ae40c0505c003414040020340c42c0d0340104090216400c040b454141c0c0218159004141004050b0303c0d100d005580c0012080c000b0030150741d9030b10a4000b040f019400c42481b140042110000000b03100b4020020350324125030f9882c1941d654613103415030b403109000090003004103100400202e40200340c056007042c402c0c28418141440c4015074001074004440e420701400b40d03a0305020515410144807800740340c26101800d82850120340c815500d20b400c50f012004c001c40080c40c281d0000d0258160b40001a884003074401c3d111107810055010342150000343d40c0c9020f440c000041c082414 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 358620737 1250 358619487 358619533
    0x1e170a1e0c0e151603032c1b0906060d150e10060206270a0f03110106080304030c0e071205160306080c031c0908030c030301050a05030d0e01050901050c0316060c0e0f13020708120405 80
    0x140061270555900c1c080c00310b0342c2c11003000d40395007544480b0001904548016000054a40c680b034005030351401c0340d00b02441800d554480410754000c0c1040c05445000d1380303d051200039070821038014907180000b8180c90030f078640801901c441d260102c000100b5a00001007054580b10780020b000301503c40004139200d21803480001e1055040100821210b58924a026440106410300407103e200c01c10003041944c03021614680d00190f00c030700307210211b9010321614024181c0b410080005a44000200341e48414041c44040a07070902c1401d4450103110f500c031030002d0030a0b1800e40c0e07198503084400982d0794100f070180d184101814800442c1c5810001020302c803c00842d915150145202401545c0c031354807aa107141d041100801480c1d840050800c0141800c150484166214200701e040c800d04032021030481c0c1d0100329120021500d181d6401e2665114040111141034074081020f0402d0001d01c141503000307009100116480c2d440d5034a5658061007140210195180d01304c000344144262800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 358621987 1250 358620737 358620739
    0xb0108071110091b06020a06150605121018020706050702030a05040308031009060324020c03040302040e101b1e170a1e0c0e151603032c1b 61
    0x212812500d40b60103182c02202e0f046020700443c441151007001d010340b0220b0260802405a40554102810441c20f8802d034107103480403a0f00748030303090305201005003644a0780540c101111841c10108480c50710070300b42c0d14010202d09000c01d240c01d44034a5801c2c040e401c45c40301035415a20300b00004902038004000c41c1c0c91580e2541d01c1c9442d00c4d04641c0d03914900d4001130007030841d0640c10100801c10032628803d41d001b540c007a503504d0504000b0301c0766058450340084004416140148001c10b0042c40010958059030380c1200c01080301c0710202821841e02c00c0c82150f240c0c00c00e0034810046c0f00072410445002c40b4502554905013180f1042c081000317907101c050f10340b40003d100050501c100d0352480c080143c002031158400308190701131010103041415071503080c20711540d0b0340c80b0042300250001190f202da007100f5551304041011000da03424180c000c65510b940301c0030707200000c2401c252280e40110b240c4410414002c1c2080064000400300f8010a042d803405442100752107c52105d40d00c0e201d6004140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 358623237 1250 358621987 358621993
    0x1401092c0d050d060e0c0c0105151f0e06070c06020708011802010309050f0d0201020406030e01060506040e04140a03090510020303040f031202040f0b070204181101030504240b01080711 81
    0x10703480c802100d1a50090f8000e0500560ba0000840c0b503070001c00c0f5060046000c0c6516588030106040c41d2403c40c2c00241c8a2090600d10259020050b1210341400b2000300d0303a030340e0903203c0c281c1c0548107541004084990b55131105000441c0700400031107104c0d0308203450b199800c07a24950341b100308640c200ca43c0e1041c00e01c4001e10303071202c140041d80309412014080d84120300f0f44206000803100c151601c0d80d400038440160350041814461240c9c9031142015403000c0c10000e100d01c5191002003841d902c564029525090304003000034085c0108142ca80da9820300700e00880345c0e041c909080040c540c0381c150040b40d1060704a482104025403000094a0149801102102106110750350507225010403100759208240c090000140e40b19040520000500c2072404090340d800151042104a0301d41d082642200c00d00070f0040c40104041c541c1d104c0442c3c03c20709000401d17031650304041d818108008040740c1040300c0e82d030102c800c080454015803c512400e80300c00b50300f0744602206442d14104012007525070748c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 358624487 1250 358623237 358623253
    0x6080102130e011a030406020a032301050906190905070c0f030512011403030a0c21031410060503190b100203182b06020910020d141801030905011401092c 68
    0x981c7c41e500510001c0c00a0a0004d015102c1102c0d0342c2104034541141a900c1030104010016404d0800c0c0b826400003048800e40040200b01c058140d0303032009405030114560361400003440c040e01038510b07803041503000001c0c5248801f6600d4014115031003603414905030303243e607000015000041e5103039203030600c40100078509045480804450030083c00200b07076210703c21811842a2403998500000c200301041e0741c08100c0442e0b40c40641ca000401070804c140c0800142000c0101c2c40c2d1100a0b203030000d001e4880444080651500d00010700410030040d030b800f004d80c9001c0c40446800200a0003444524219419a4049107040200c4518072903103100d106207491480701040c000c54241d00b41902e00c51311005041002120105d070584000080300b102590007200c031007500381d03000114011441050090740349043c0c019990620100d10003840e8506040e290200d030001c200f82034100c1300300000e14084d820034541e0360b914031b0000782c80c80412000c03064a049411041400f40c50340c90907101200c15008107201 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 358625737 1250 358624487 358624493
    0x3080c011104030f0201050d111b151003021e1305090c030a08030705070c0f03060204030b09030a0c020f0619020304050f03150112050a1a04031209030c0b070306080102130e011a0304 80
    0x2540c03048c1c803c200300341c0d500d501c43c203602c90a41024000c044080a0103c200010070102d0915049100d14001181440703401003000780b94100e0b400d8429240c2c1500c0d0440c00d8030b41e2541a031000c1700d603001082d62040100341181000c00c2035906c11803040c000302c1c00700c1c1c4001c950f440074951035580341440504480000c10014800c0c0780940014800c0d20321820702c40c001580e403150403604603422a00104c480fa500090100240100484003a0300541040051480c0409841c40500440c80402d802400b620500051804d00d44d0340741c01f41c0f251400303080b200760b64900c0714030340080d12a4012702034103103e90321440c08844d2600700020418a8a00f0010407404142d0078401c00b20b40004c100b02d4100e41c10b02c0b5001c1050b0001e00e40130340c52204c1608110ba01c903885d060a10300030b0309514100060050952030b04011300e01280d401881072410f140c0000103d00d1a44403c01c044000d440d15410001c4a5070000922100080c220b001c500c08a0785c0901032401c0603600c0d08600c8901540c0c5290380c544480c030030b01c00300c0c000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 358626987 1250 358625737 358625747
    0x120733020c120c061509090a02010c020409050d030603120201090506010e06060c150402090f0c03060d03020304050a060909060b090303030c13030b0f090c0108090d050c150103080c011104030f0201 86
    0x56804200704890141c1e9407501c0c0500a5400080b246034641c008205100d540303040c0720f151111940c42216002c0d09850210055a03480401c828041d040107200c1c1500410343d2a15070050600640203000c5e5009c404003881c000d00034007190b01c4100c4a842100c21a2807442c0e106103d08005554030001600742070b4a4070407484900c1030050000c0d41c0c04001008003020701d080410294200701c1c880a60b14085141a004201c45000001c02c800030b0001c40b001081000403075001107980c032540441d8100032521060a003281303103010b50b8110a41105e4400004178603982c0080b501d004951400c0f20501141e5100c0398101228012071803c81e0b050762007032002c152511400c001403d4004012145101c0c0603940c5e898084032601b09607640440005240c060081000d4240000b8641344401c0c2010700b040d042c8a40020380d16144a1146c8c010003901082208a0840600c040030441c1640070b2412180d58490400142540c4002c0719600250318080e4980301c1071002105590490b80c00c400ca03080c64074215001515 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 358628237 1250 358626987 358626997
    0x611070303141603090608070c080403200924061e0a12140105130920220c080a05010503030712030f050c13050a0b09060a0207030512073302 62
    0x603030b0609200c01146210032424005510b4025a12aa1940d19150f0003a18046020b400d050810641070300290100b040d0004440c00c0703070b034450010411403014896800b1000003142c0322580c809184001d103e100d0001000714164907041c283c0031700b160b55145042100c42e11480c4200d40041d00c004d40349000042103500540038900b95030600c0346c1c144d10000380ca0021124500307800c20085100800500181c10101c0d4400b540034200c00003040f44030955150040143c005018010429180501c50314041c0c413507141e0301e80614040c00085403102a25200d582c05080c00d00e075114000340715080050102403e42c02040e0403121301402a602c0c04e80c458036040d800604d140c00b80700505484010341c8024180a2107003c0c41246000d038826200c81003c0040c0640340c40a91051307100b105042020700180075440c0c1101c0e100502140c4c0140e46080281c42a4180409030f0b01c0540503001c0c1201c50801c409814000f0440c451003440502c042c1c8401011070700804050500313000d0391614500c140c1a06282c50b60080c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 358629487 1250 358628237 358628267
    0x8010c0810060e0d480e0703020c0102040f09050916031e1b08010f0212160e030a0b09010c0305040f0b07020f16081203011a09041e0c090611070303 65
    0xc03180440584403030310121451145c800394801c1c041e20750490f1004a102d180c48078030070b84c2c0d000c1d21503081a40320aa801101401000b409010000201d9007940c020350403914603110030002507455999500b0412944110303880340340b0071542403030000380100d407000c00c01960003c1d01e102120b41c0d2a00316125512040380d603013004082c00041e070840001051481e401c7c1c00e881c09048114081150800ca10a403e45a0021502e00441c2c0107100303401c8245a913203c2c43d540403015210360a5078161100c000c641c45c40e4115261600f5000b40c40a510601401c050b19038851140400203105c5541e11f4a0105e0490381b04560240c0030655850b01d00000a124801d00390304030415204445030450f0301803a06041018080301107900d007103034500070061003200340210b910b0740101d407c010b82150304d041c0c1003048051100141a003034050005881078169620307403142660b01050401c01c80721002d006802e4008000700b10350b8902040e01a000012036500c01d4100848a001d03003805402d0b02c1d03155540a88000300409800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 358630737 1250 358629487 358629499
    0x1503020310170307031418090402040f0e060403030c08010605070201050c070503060a02070c0e04020307151e0c05010e07181815091a070206010b0307020c031608010c0810060e 77
    0x400881902c00c20140b09040405569207504038a0302401582000d032003180d1060080c8150300d082c20000300a22560f80703084da9004e0f110f986030320000b4000c4c01e04182e40c03840d032440c00b4410685c5030b2001868030300c1188a42c80030015142c910405403580c00b400d105400000d0303000c101400c01544104040d001e10440c10041f24401511040028203203403044500d02032096012a01c0710a0000065100b4000c04a1080054244c185038001c00c1e11412580280ca0515516905ea10f8410f4441c0e0f1415030310300d0540c08810400c07a90aa00106030519065041d1030399802c0140114081401040c0c00080710440071071032085441100503c7d020f4000303403d2281c44007914180311000f203101e420b00c2100100501000040300c1e581c030b15046403215500c0b50819001e20b03551081010f19600041c00f2810749a12031003940d101d5440d490202c4c9803000d498011a050f000390100311589040701d40e40c01e01075401010081c011110100c0e0101c0d0380e46d20440f411411515140410090390f8051400048100c0c000b07002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358631987 1250 358630737 358630739
    0x10020f060a0e10110d0f0902060414120a12080a05190c0e060d05010302041407080604050406111210060203090105090f0f0a03211d15040f170f071503020310 69
    0x1c00040b10441401c01074990340c0060781171903000840c8a03510f14404030b80b204000001094001c1000b9020340d024140d21171200070f01d60005d541d6040620001030442008884e0745400c5481c1110b000920a0682360200e14040b000c51800359040c000d092194440010020102030490340c5003021f04543e00e15141400044400e0702c00c0c5131036460040c02c4404500038003007965459481484211000c10401c814224a4013041c4080e4070340c012411a0024800ca502296a0315039080110007450705111031812104d001842041d40d0840701c2150f0702c940c1c0400041910660b94440030b07600c80c4a0710648030f0001d08104500d04a40c50b003020310b042001005015914032210480102e40710042d2a081602d400f81500b14440f5159403024044a603e151464580b0395486650722045c005074400c13920313500c2034000c0c44549001e00002d6090398000c0040441c4181155980d0003e0b0452000704503038008030b4010704421541d00100012403808035160300708400125800c00e04211700a40014001d8a040c0c071000c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 358633093 1106 358631987 358632013
    0x270f0819120507020a050901170d03050712050901060509040c0e2404050405010e1b0103050610200c030715082a0702010507021e10020f060a0e 63
    0x2c00584600003403001401c85001500b0450708510110000580501800e41d501c401102c080141c50b24800b0a10046058403c212107080c0802c20920724510004030700e502041e8032600321400003901c0b0361143d0000d101002d05a8082e28030b20481c0c0810b104c07900c80f02c4205904401024850b4204a040e075030303011450440c0b46d05c0c151041e5500e4000909000080d0020040d0460007010707614025402d07400e0300c0c40c809031a8030351400240b8200c0081c440e814010b030321060003a001e8507241e122000301b04a081c8036458155100000780500398031010a614108450000350428a0380206036204003040180326003001480c0c0d40404002c400c204004415149044800001000d45299500d2a50006030b80d03600c150351000f9001038001c000c800c0f801e2500e24002e01c413624115410078070386072039810890303840c8290258510700c2e4020502190560819500800c0d541c007205c0203407040400204 = true := by decide +kernel

theorem cover : BRFrame.Cov 358453237 358633093 := by
  have h0 := BRFrame.cov_init 358453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 358453237 ≤ n) (h2 : n < 358633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
