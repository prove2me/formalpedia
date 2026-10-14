-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3355
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:25:36.110384+00:00
-- url     : https://prove2.me/submissions/5f6b08e0-094c-4f1a-b7b4-a69ff7ecce70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 603237410 ≤ n < 603417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 603238660 1250 603237410 603237413
    0x3020f06220e1f030f141902120c0901051c08120411030d0801050d0302070f08030913270212011b020c03070b04060e030703140307021e03060114060708040f03 70
    0x40c105000d801500d50602c6100c1110700f0004030360100007166030100d9082d100205500341003101c804a40003801a42c001d0307040e04440e0b2004a603041d07030028000c656040795140c0300019244c0d00c100d11440e0704d070851840d0004214a1901900f2100d183c0d80200130485000700130741e01c450090b40700224401c0ca03071a00320300303103c24441c05010f0024036100541c014103e0300c10046026204d13030014881d1a10402c1032101c020304043c403c0c01004010448070351100c14042d25444a02d0301c81d004800d450f4000e1110000c40040700390603000c1d00d0b10400c81d0521004180618215800004010355001da8028003c1d550000c0240007d10480301403013058102140213080d00300b402070030b01244280e40fa02c0381c2e01c00181400b08030025011901102e0b00c900701000403081c0d240200381801c00503800504200d00c400b580c5460043d002c001014850300c201c41c80101031035405921040803c402c8030300354160340490300501c0086070070100c40d90f8201d0000d028030304008460f65618915400758004200202e4092030400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 603239910 1250 603238660 603238679
    0x13030b0a0e010c020c040b030106051507020117010f06050d11030f0906090f150406090807060e0d0801080d0f050d1a040e01020f07060b0a0f0303030527030403020f0622 74
    0x40ca0306040700001d01c007500c44900000e6403441c007908000c0c41150f6800c1000141e80c3c0035800f0400910018008503020341c080c22800b8440d40000b0380c180d002c00c02d02004056050300b000c00c414113030b400a410000f200c40c20710b8000c50b60b641000c400c0c3c828055480401121000c2c80c0340240d0710890010302004502e2600c2d04090f420035a003d0100b070302c5035000da0710b400c414040110f541042d40002c0c1c001d000195640b400d00b800034008800015101400020388103060002c070382c0008a1211100080300c508490001044400203001d2140001790340040700004001885080e071100321040514100e400c1c41c0018840108a8030899500d0025500503071029070ba03030170103004818110008000031410040d000840c4041e91017203c900601c0345589040c4c0c9075075984d50410001c050003041c0740042441d604c0e482c000d4000d020603103007050b000c0929554941c2e5481ca000ca00c10a084402c00036504052840c0e0034004440d00440211340c3c800710501407074072142c20042c2d00303242e000340441c40000301c13514200020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 603241160 1250 603239910 603239921
    0x90607030608030c030a120221090c01080f04030c0302160617160822060f020d0e060628120b0f070e09010308030403180e01060e0a080d05070813030b0a 67
    0x42100c0e41040c4141104c4000100684001c05507a061080340d013480415800020300c42d1410204415101c58000740c800d02907408041c0c4034184041c03c503000030408000640d1841000c440d4400e07900800740000d00080d1083c0407031099144280100c2c0c144100180201081c55a9030300024005010300008003411543e019074580c00c181ca440c40d600000007103002c01058840d0040c41e905807031100c01c4000208503100d1080221140e000f09003040388813100c1e01050f01039400b1039450300d4040c1c06c082d664180c140011580c00c0c054100282110b490b060040c0322445450080d115240d5000c1190500142810340391446111080c410000f25010303240c002c03421101100040c00070301c1000b01c603c8031b100e103507103880d42d51506403600040555182d50325881e003110b00c1e002b45c1d800f89007041c04c01d100c001100308440030740e58185c0c0da05840e0201c0801190040c811810550710444465511848098030f00074011002412101e001d12003042c50484404039409041e00315600450708410351004108105145100f031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 603242410 1250 603241160 603241169
    0xe1c140c0303070c030203070b01031b0503010209030c010e2709070b0a0903060504111f081311040e120408070e07051606270602030103020411160b0a140906070306 72
    0x405080106030040595a030100030010014031003003a0001c41898000c206036000c00781d00072501c1a6070b684900c0c00c1403c89104001c0520012450a80826185810300aa85000b07501500418130912039900441d16254007101036a0041c403d0308040d200c64040d8041c04c0c14000030075070084001d042041c112071030003c107a4400d65040d50700780403030043c0f50791240d0510300312a04180040740a40311400d0000b070f940e40d6040e1041c1c0c00f41e800303414903260118000040341741490944445105685038850801c40452100004104600b44144007038140350552103941c0f6400f00f2012035003000c0500300c071840d0580c440d4019007190790050307004108002c611011540d00c441c3c9842c10350309202151014080d604682c00f8002c04003620381c4c0c48010700400b21442000004c04280214030164494201200250710a000030b80c0943d041a481100b5803881d0421690710090002d000c0080424545812100c00400781c9100001c0340c58460b000455840158103030b000e204014040d015904280401900b1601c25610 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 603243660 1250 603242410 603242447
    0x20c3a12080f01060c0507090513050607080601120504061805100522150b10030c08010e010305070608070203191106060d0503160305090301050103050109170c0304030809040e1c 78
    0x4100700b030402c00c044a411941d0905205403050524a0311324109072036a0030444865161030104043d8140141c1c2424006000703a060b10f0700c035241e011003150148000c4416034003084901200c0c60342c60403139a204035409400356500051045184054480b1401003107019682607002410495001c0e1151240c0b54202c3c55094030440280f90504907503100300007007000900307600c1640d0711204840ca555003286c0f404260080c068224641110000340003003102201540c000781c2d44000128041c10303a00b016038180c030782000080c0b85491070044100d0b1400d030014811b20841c0000d0100c0d00320352404e01610846002c254a80c20342100b03d501030300d807400d4001000310384188201c01210700410380100459540140350b0000c001041340300e040075074030ba11402104c40c0e0158070b0800000240301041d848610002e00c0b60108990001c482c4070083c2e0a8092030b258414650020031081000070359031001404085000b903c08149040201e46440c10310880d250f403c05800e00d40b5200c18001c0c0d0307205500610744202d552 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 603244910 1250 603243660 603243677
    0x100c05030f10050f1c12090807050d080405060901050f030c0318060613050601021f0f0b060408100b01090b0c1e03130308090102070315090c090507020c3a12 69
    0x20001113662160b0b04509002e000e0f050395110403040280c40a4514a1700011002c05c0502c0081d4024040034451240b10309034081d10344041213a142415101a0554120311410700b00f070708060800c1966400000c10764180182041156001c0c803000300030b1407148030300852180e02c0b40b6199600c600b08003408418a100d60700620304200080e0ba60720f501c080030034060203001400d569075800503454540c03402500e8100d480c08140c03050300411550080380700b030f00d16524140042c81c05642442414060707406901441d8008203145808050030354040e0041100515051001554880284100b64420700500d84150002c99080885228101d540031010304200021403500464040c2c0e004000c040c0d000041c4010000900e45405078400c014102c00355411212032803d080c10440040021700c41d10201300c82c0c0c145a088005002003151103190711450b6180c020b00415076211342080b43d00c0d01b0703a40040046d43c070101e461503400481c181c9068041000c902e40c02034488014241000c01c0d007501d161540400076600d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 603246160 1250 603244910 603244919
    0x7150606120b010306170120070f060b06040506070b100509010b070b1906060903031b0317070215011805010504150303141e2d1902100c05030f10 64
    0x4a10199800c441c5200090b85405000100d01800742507104001c0b0b001852031060300d1410641c030040c0500d40200c80c1494030349585288900ca8090b1680181201484186110215a480d0040e04141c40010001441e0a4480c40080c01c02e4001d0b03130059400208800c10801005407081040014000031240c1303c88a40c035007188600144911807004015080e4000400c0482c4803080741c1d03a0203202c500d0030a00c2017607102d0800400e896070a22042e40000c03101c0214400141003800d6801c5007a4040d50340c102c1c540c2d40080a1071050740c018050008500c40c1004502544540800f55406006004904031000700c800e03a03900d09489068025034402c6207090031411190040710350760403c4a0349420030051036103006540001038018030a40644400004100f00702030841400282800529540000401c00101240d1010801e480046004401042200c5404c0a402d0118800c104003584126030308032004181e11000c1e181c011003104045030000c414010701e14087d568090344200000710030030045180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 603247410 1250 603246160 603246167
    0xf031e0c03030b0108090304140a0308280f0801210501060303051306020f1009030909020c1014060306180f030d0204540e1f110702060f04080f0307150606 68
    0x70fa20803049490300700c62780c54282d61562800c0000441c3c00001d01601c030306541503110400d40580c005202040c1c41e050540c20018028079030102000e0007580c52201a03805c20039440d04280c0b09030f1484200610001c00d031400a80e09009030310185110360b0351151108a060021083c2810380e4000c1010741d00240740198110000084025600046d42d80115060941c0d00781a074400c2111f400c144100c5d4000a00e801d032808000400b04005442da950400c40003040b0590002020b806031001c951582200340403030100d00300107005881540401007074aa884861042c05441c5a001006808000e41c022a081040240c00d455108441068804401084030a0701c8000c2140c52114200700720b03080c00104c2c00c201026130000d0300c1c0041d2801030041128410200c1c40a94403050034220445402d17615241c4040840c82e070082509070603101d0b0542d402d10b91140c1c2000300a03080480f40803d0501c0c2071100195643e400c00c64100c880200c0005503903940344904240c2042c507080e0000c084003505001c01040034550 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 603248660 1250 603247410 603247417
    0x70f1b060f081f05030a0c0e0703060b0702040f110d0608120c030d05071b0f0c0503070f060e03010207020a0308072a14010e270a050f040f031e0c03030b01080903 71
    0x20f40c404082202d074003080c0480c01c901858000c10341600c103190400082010012000c8140c4070f4100d1341d6203181e07075841400c074203a0f003050080161110b0240320305401424143c000030b41c861005100483d021040c100720790391980010002d517041340d45420b0308006000040c0600340b1014819807540d0f280411035900c05030380340300d5800502c00481da540d0024010520560108002c54841c004542101501e070a10948d41c100c1110309588541500c10000b0380c03850b000a8034000c803500c05009141d036900d80101a1801619010250b806d1f540801800340113940e00380700d140107144a40c54040e01c03054181405045c20700924400e0300310301404c1d00000d1641c451155220b040300c0c52000290545003110004840c9201020315444d00010084401c20740c40e9501514408004c60506c14041243d54040a10003171300c1e415100c0382480207042c00440d0214080031400b20590b801b9003407903014618099071400050a4100500c000603040d540c3e403c041640c0b501070101010002d20f4824618100202610344a11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 603249910 1250 603248660 603248671
    0x51b040614090a030c05130e060106030207060605090703091709011d0316090203071202071203151a090f0108061f1106130501050f04081e070f1b060f08 67
    0x15003020a103821264007007220300c440c502600c01481d041d40c038688003984103003d0145030300c81d404c6900a80820305a900c18211200640801007500381d2810030300341c0007503102c0d40081e210142c98950100706910f4880300f960040c8155500000c0180c503a09182c0e680030b1b510440815618010003500515aa10400c0d0354018604c10345c82c400109455000a0300e880030b41010f2500c1451804d4001800b840140c0c09144120610303101c050074038075507255200480c401e41d0401040365008442100c10b86120740c2c0300c00d903644402003403400303415241c0e10000c0050400c007040446a110005080c8042e05000002c498480000e0a1414003410004009174800141c80603090030344c00d80e10100c0c1d0846104504080304649010305403881c03420288011503004400307501c1a5119820240854001c0701846480740c4200d80100c1100c1c00c0c108500b40b110031001d031a002201d01c2207002d09c0243c0214281c51024a01e0074400c03140400340780c040c0004150900c03084d0b800309084c440750940800c503ca40000d00c403503001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 603251160 1250 603249910 603249917
    0xf1d01081302030a030e030706020f12180616060605091522110417060c0f210c09120c01052a0f0303091002040302010516050727051b0406 61
    0x980d00e1507841840c4640460002e545840b42c40d210206060b0446041501c1c40c100343e0a07a40280c0c1c41ea201a42e5071185c6205010f1140e00012407044021490406080401d428440d2080708001d100e00281154211011404641d0035464031380080000c54410000146005e07100003040e4540000104100084400304038015126055003501152401c00760014072081c0383d00810ac1b41040b04014407241d00203024100ea8100404004990107900190030b030f02c01d1402045081ca000d0104129000c16040f40754860207440c1415144e11562040081c864820414400c0030354503241c00d5001c014200346040605452a0031021908080e030b6480340417119a51041161086100314a11100f00c000c0c60070210012280500c1c2c080d81000200800114007600012003211116131400d1455400c0344204e01c13000380401c00c2008502455080002620901d60090341500c000a548003c03c08140500f8031040794100e80007075640b041c8008a115154011101220f0806551400d003c100450b105600504007170 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 603252410 1250 603251160 603251177
    0x70b040303030c030f0c03091a10061803150e1501140402072301090210021b220c030e160b030414030f070c090b011704080a090305070e0105010f1d01 66
    0xf85406a0008249840301000401486003078290003402001c500c0030444110310b4100307411680c11225162540148030780228030146524040741078504004000b04801e00c05e80d10780d4004040341d40d50766241c1c1c0300c0014050204d4154032008850741040214800582d90390b403d40e005000460b0419201f40d244107090303c00590f42c40031030409242c03513800b10b8150803c00002d10b0641c841170006400080c5841d109039a000180144000180d842d500d01c50b0007840c088026a2810005103802d144040e0303030388103c01c1c00802c3d09140c03040b40b030146e504204104006c00e4581d040380710040c000b04440f0840b08661162101840d0410445000d40e200c041c1c170140980568409141c0316403003e004403010810480081503070381c04030b032409200b0015644208420146010500c9031994010003038240d100100c4130600103180d8803a6a40c1c2d4040c0c0000c00400e042025242010002071030400c02d51025011031600c1c07140d10340c580360004222200d4034030300b03804119000300f02500000d507046022802d91002d003040f94a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 603253660 1250 603252410 603252431
    0x411010e0a0306090c060311180904141b1f0c1203020f0301140901050418030305280f0b01090302060703080402060f1602120d0207050906030f062403070b04030303 72
    0x405584603000540b081380b602e110b22080100b001c0c203100443d203460310140880004991000c04501903c0c40d51842c03280072484a000c94a0822000380e8001c1c0f1036181c00c10a03e001a800754139001c004410700042da90b00c03161000d034030724010303400d1000c850554103254402c171000d81c4014000741d0500002400880e01c0c040c00d04d4064040d805840d2840d0451210320344075a0b5610b0340741080050000010301811940c2e0000c6030300e0a040c094500c3c000420b580e000140d08035581d04030001c0a004015004c1100f1491a1100009103060401c4650700c680c08045010541d182c00350f8220b890502120307050001580f020030058031100c041c2c0f82100d40506100405948038008a64288035048134040c0512002900b0000001800750808a103802903a0301c0782c20358031880c4500c1d238544c0b44428400141c0e0102000b00035501d491004561320400240c01c1e520210030740421145042c805643c0c3ca82100080103c1c0301c01c60300c00c0d802c050300415040740100b11b12458a18070f4100ea2086010240805848009152 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 603254910 1250 603253660 603253669
    0x20a0f0f06020c070f0e01260f030307020309011d01020c091005030304271401050d03020a080f030412091a0a032324130b13140f0702060411010e 64
    0x28845401c48815075541101c044240c1d11640640241041000358030004595801d1700010b09050b036a1003648901041c0300301e010403109100012070011540306111a4500d5a00c007400511b0080760386170025034403800369900141c22246d040b046145803500402d4407611680e80015154404e40301a079a211554032507504007104000c45400c0039401d44000540002e0340201c0d4902030b01b46140e12107680394080d22071a42c00302510f6902c0248036025581c40c0050080b49090401c5050161180c0100c441100c07c0e03944071038a6401020300d0048044000c0104014071510f00300084102c070032440c3c14002e1504003028508949140c0300342c6480da10300400d040b0266400399010704121504c40781001030100c1504095000100103d50007660414640c03001c2c008805030f5810003c011034003d040c4808a0400400c0c040240780302104140d100c109085503002d1103126201e0450341d14907010414405246c90400402c6000f0050445000c6610910400c40440e03401240e80c0300700c5e03600b4a4030700720742807a040004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 603256160 1250 603254910 603254933
    0x1030b030f0c062d0d05010e064207021f020a1b030f21030209060d0902041107050a050714030303060f01120c030209030f010c1b1b0608060916020a0f 66
    0x40440403c01111800d0130321261010708120301e040d4809200c140c0c0c80d503848104a078016507920f5003003120060945504616900100c404410641c02c00240040040c9561106620f1000e4020545800140181903040450080414440f004100c0c020040003d03002036507050300394000f41011662040003c0e618140020800085810a03410b80b0004010f080801481c079086a10440368542c00b0f000c0c00e2850300a00903285100c07001807031142800b0083c9022005054900c40032a071181d999003030700c070f110700004024003c418001c000421842c041da280182c90701003a0f03004514400242c425259040d580002140e41c40a41540c40c28026605080160b039064010001940198102140910400d40c15806030141c0c050484c200c034042c505095546080356118458100033802076001030a01e080398103181c03100c4500c41c4d01d005100d0038548401d02d4034504940c122000084a480900c1032524001c0d01c469000010f0304010030541c2d48228000e0f6482080c000014420049030002c0418030514281c00c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 603257410 1250 603256160 603256207
    0x61107020406090c0806040506030c2e0c0605090c15070303060b16030917030f03070915030506010201050739050102070f0210080c0a11010213030506010501030b030f0c06 75
    0x9200880d00c4050a0340500004e5070903200144c0140c00041182c03030180107141c0903410140184c0240300d840c0d002e01c148200c00c0304540240700d200c000d00c408401c0302d10b03070407851b03a032025503078442d034104203141c40340a0b900c015202d0840d0b41c1c02450218555074400601c0c1d0b20168403503100d0f03581c900c85458141d0150416a12a46414001103400a0460401c0040250480c4681d90b0080c9494607071030380c094451400c0c80c1280071948144443c11840a03540c0c01540c00400ca8245848156501c82440003503040f03180070749001a03100d00030300c6801d50b0240a0260420543d01740f9480d0b20201a800fa200c00140415045820016180c504191403101034100901030308a8000e5558401c01c2c00c041e150146504c0e4100d00400c000401615a64400d010246c016212094070030720b80800d081c1c04441e0220002421035140d5403c00c00c42e610b540700b240d84080294403920140006600d804000342c07c8a8401c20038a0081e0000420010864008514199055000c07111603071a010421480a400f034600300c035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 603258660 1250 603257410 603257419
    0x30c09030c09010b0d0b04020f03040602030601170103050114010806040321060b0f0a0906020a082703011b030b0d1505040c030503070507180b0d11150f0904110301030f06110702 78
    0xc213002e4074100007800c0a0300c039450709103d16414842803108a1042070f8410405c100c00b03001081c0020320640045801c2a0145018560710300e05287d040b00b030742800c1e40101c1e256951070000c1600d00e550000414010420540a08030710705e80341e18084d0040103400d088a003504010041d0011030801684480081c6c0741e04450991201035008010260350305c900c80c070101250032a100001e40780e100003007080030b941d80100c20a0610040307005192503101058003900c42c1d51680c09651030180c90034840c50840c0c0c444949007010f6910000d034058226200070340e8081c001c00124607e003002ca09190161103012910010004081d515401c02084144540c0c200800c90300001555100b445000100c08090703481da5640101c892005c1d080d40300c00c45841c0414650001e2850030307a18042840b068a4086464001e00f4000300c1e94201c107180400d5a005112100f0000c20101d05d2030181c0c103182c403442c404103d03881040c0c1e20315415a00d40030050440404020a915200d03402c84400010309419a00115030251 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 603259910 1250 603258660 603258679
    0x6020d0612060b0a050a030f05120a0c0c050a0f181b0809280b090c0a17060903120f040606051f1101090210030b12120408070e010506030c09030c 64
    0x1d04400300d00304044415038985003081e041400525081a102040703510003002481814516a503804000381d01e95030607200c0e40106514014002d0303444d00180b044001c03e91301c128150146251034070104d542500070310f008541d441d405221210401846005840551055207821005900c1c524050308034594980c0709010100041081140c1180a081c010101401651062421010341400781040d0701d940c50f22200c5444900c20228120344c40302d50f080251038040d42d950012a00103d01c02c49a69400340d0f80d9180d0101d1121510326040c0452034000e10810701540c54000c803500c0104050390041c01d294103801841011404100b07603a40540010200900301c00c01c8030001d56030200c04c401c80c2284131408101c070034010668a040622070412006c0d8010505409036180f0041200145040954150440740406600f07280341410425420741404582c901a41c5508051a071428a1300c0b6500003202c8050030300c010310080e41c80200b600c1d071082d1600c0d040743d119000280082c1c03074206003800c0540c112440f007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 603261160 1250 603259910 603259919
    0xe0d030e130b0f01110f0a05061e06060406050c03071a070f030b091b0409090602040504060b0c060f0606071e02030c0105030915060621040210020c0f0f1203040b0c0607091203080406020d06 83
    0x101d413051140315440c035864040ae26190422858541c1107c104d41d0215040005004442c060005001b416202004807400c08680703076103801e1403109405081075101c0d140020004010340c401341e08011100380b40b409102148040010421800b4081e00d01d0070f0b9184480807010405030400d003910b00400c000c00d0f09105044090508400950107401641c3c06242006008a000f0700d608040b60403500e40d00004040503078031403005050101019050603404241082200701080c0c41070f41c4000502146007400241c406c1c3da204251900842c1d50f01743d03041c00346c1803041000a210218801400740c0000840b40055510000010890300c40e1103496801801000f8800d030600d50001c2e007540c03056200f910b8034074803a030740307400300303a9480a081d01d05942c1300340c0900001c03010741840803401e04d441d034000d445211800c00e091f40f00c50071a00150800d2400a00100e01c0e040454020030009401418900b003041d0040c1c18500920081c10760300381c0250a115500303010504001170303039044940c110803064007040b00716201c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 603262410 1250 603261160 603261163
    0xc03030703022205010c03030e100204080102040503010b010e060f1620012d0c170403050303150409020a09150e10170102090319030e0d030e130b0f01110f0a05 70
    0x40c1440c448405030960031406100601c003c41c02640c0c016120290071400d0355908401a0250200a201600810a03c12442619400a4000307030501c08005611a41000c1c14542121071400840341007010780a1150583c0d02c8100031031349003007030b0400201d030b5030360041380e2400e0301030103092006200500b904042102217040700381d10303134804800b66180391104080d070040074925a04e000c02c40d101c5140c400704030403d15002d1025914081c1c491880c02c801e038108500017280e81d40255000380c49681000080010650ba01c02000701c0c07094040b0f40c1040b05400e0340c0c003c58092038150040101595503149840140d20380c151218004180302d52003070401d0b20b0401580d01b08001923120342628140030510245c00008103000303540076510050020a20f0a40348011718a001c0c9244009500f40905100040c180303403030350224560740c18003d07111444020f841d0f07070034800201044028025128640507200420faa124412400d42102c01d01e0540b600d1400060381e036081c00c0310084840e25501c10b40715514200700c0c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 603263660 1250 603262410 603262417
    0x6072a0807060207031b050705040e070b030f0f090706080c030403030e010e0309040f0b0d3f0905010203030403021218030106030b06120609030d15170714010509010509090c0c0303070302 82
    0x417995400f00300c0002035010001e141e82684004015400c24003050006041c40e41c001180c50440c44111040d0940d82e00030404103600a6590301c50b40340042c0300300903141d100807143e950402800c0f0300030410145401c070002d00c6442c001e45480c2e07403228004040303010700d4401d41040c0100712522000300440c03042c0e4000107035282d00c0740000a01440c1401038034004421b0300d2244920140018103107200c0c05a0075521001e11501d14080d4111440d44031071010042100226498400818500000b580095031500541541055802981158820010800020b0303020606d0412000b13869202600ca00070b60070000080040311f0841c540542ca4944000103000303060003064010302e4203480701c895035640b00605903102c09041303500484540c02085a0b06d2208001d0f031240d140034401e10102100d094941b0315070914004a4a05114503502028081c0001d038481c0100c3d14080e0805d0804902c0c021904001910500415000c94401c566000015100ca030141d011581e8020310041565580c1c9460000a8001d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 603264910 1250 603263660 603263663
    0x30f0d0801050d05030904020304061e05040309090903022e0c0903061410060e01050403020405150907020105060f040e07030503071b0f061713150c1106072a0807060207 74
    0x40d122400041e2905240038114005038000b4040c43c41e015043c0240806503001820844000d652800003020040c15500004603490300200c0100345401c01d818000c0543c0b07480c0c1c00c000806458000341e0b41c00650001028454080e1f0342742801c1038005d030038016010303014034400300c0c841483c10a00803c0c9030300d40c040c80c6001982c2c41801c007081400c062604000320600300700c031045c1d58107080c101c2c2408014000d80d088444101d0525140d0700d025125404241550010340390040c0c0b85041c0000f8140c5843d002003110345c05208c03032000300081e1810f84002092901902c106138000d540d1081c1c80c250080e020301c4410b02858210044a50b180824a090701d03c0f20000d51400c10070201400c408a00c0f00d40c07014000741243d41c10380d2600c030107245606031484200005130036030031744104814118001503491403941381401c0600d00300150400480c6000f5158000c82c0714056159081241001300c1c0e103400c54500e1012800404000c00e5041760800038240d1996000005801d000c0045514410030440e03800500205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 603266160 1250 603264910 603264917
    0xd080c0706033e0408010c030b0111010b01080c09010c170c070906030b071b0b01032a050603012c1f05060a080606030c120a060602070509190c030b030f0d 68
    0xc28034010034040e1008110004281116801c03030400e164403110f091041000040440c3c0e5140075958084682110348420b822000b10341c80e0b0010003050742e0820b200e0780c80c81c95400000c1c4400c01ca80e000081c018100284002400207000c1103100050340324400005107554403800c9400a550a178403c865540c000014503156845220400b069494050003000100e80d4810030792245a119003206450090782409519002a0210801d101044012104900840c0609031850000e80b03500c076032a11644c06000d104040d008590700810a54481c0800c0701d0444102c050800c400a0005604089024a1901e07107401400f42c0001d00400545180100403002100960030701940c1d6214113001d01030250f00c1041011810701d200041c04d50078400d00035030340031942100d00c0c2c0c546144c400c1c4030b411100c029100700030358503a55a401d0121540401082000d400704440c64622468050099a90313610071641c201422501c0e0704200c0d4015001e40c114183c0444000c0a5640c41d00c01556100d0380d0301040078600001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 603267410 1250 603266160 603266171
    0x908070b04051903020c130b031c0e0a0302030c0603040812070f0305010f060206070e1c0c0302151e0a0219120f080c04050411090a0e01061205061c020d080c070603 72
    0x10780f404030641c010b40781e154000d0900010707481c0c204880300c883c4003001c1c1e034115210354684403559400d00108020000030b03890342a503504d902d54014118201d00700c096000340310449050015a4002600017035000c001c40e007580c0c1d239585504d40312599014114040700e00d91007040074800c810390400c0016201060395076041102c1d0303170384d14030a900140503032064401607045403001c1041a44260b51903000c00e5400b41088030440717800580b0114241d4000825a101d1101c0c0d10705104500e046c854090100140801041c1098241001d81c54540b2070559600300d0700d207000a4003040355009101d00340810782405201072170071080d42061250052840b00010008400d03901c1c000d54503000f0018640900030001501d4240f07402c0805010007030241c403011450101052000248590b03c0b10ba07100701400314803001051a52400324007507c01362005080018150400c0100903846e1200d90700d0f4040840c684196003401d401030300200d130840381c05040152101900141d1002051000200d02c030031070358281d07000c004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 603268660 1250 603267410 603267433
    0x30a030e0d08010b0703022109030c0a0501050a0810093308120d02040f0f1e0e0a0b12010c030b03120319020c0f030c011505040b0a090c030908070b0405 67
    0x1210700c014115100801c0281e4014030202a0304005808500d02c41c0c01141c96000d1011a607445405e590300120384651350000d10f42515060a0000c1c007021541610004252420403002030f055000c0d21715850308010414002405807018111030200500011104002c003040c0342030301021108800c1c4c00307107042505455500c043c80041c007034410121605030000d0850440002c0c00c00311154030103c2c43c401c040c0d07020b00000c40ca140c3c989480200600034502802e14051500603854880c001c40420b0064411070701804000c400f02c1242c60b2030744030348a1600052411119000240180354003c0300e22010f40c40d2606039620150180c0c00082095011001c80324500c209001c024560310048682d040420800103541010541c25005441c1c0c2c01c0c580030503245410401940346241d43c100025900d6a40c2d15010900c550030317190a40b610180c03000340c80500441d015940811140d145903c41e600d042d0703035602082440030344a03610104440c1d600111700e42e51090b19003460f03c0400015101078a080c028803000c2074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 603269910 1250 603268660 603268663
    0x15190c1109070c24050f01030507270f06030f11030601050d150b0102010e030706021321320105010807062606030c10050c0c0f0d080f040b0c030a030e 66
    0x1442901c03181d80795010b9801c0c550b180301808010040c120314040d080648101e089480d4005d440c0308848100c81c05819601d507040c07d500d489603039030107c81e2415060800300d0003c42143c02420101170054404140803003450f200c100180100c0d80003134815207c003000d00042040b00070030329850300d5040b000c6807003036600c2e0020401512103440000b000e0002c1c411121200d619140c201c0c54801a0500000036503500926200e411580149421103403960f00040c0ca03903200d4034120346c00b07001d04034180d405540c40b0010000901c0b81c0c86035441c0501100070150080e401c0b020a00d010402200b074001820815030f42c070030380711030191178280215182c0b03000390240030030910303c01d040741500d20200741908001c0ba07100031100342c0c011074041d08040e003601850701e590750517807241c6e5281403843e07005680e020396845500c400c2e14203241900301c40305d110354144440042c4030340d00c0342c00c03800352960070800c06680c41404059910700740c4269886100344990105880d2070307801000c4041d10200485840034402e203c001a61139 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 603271160 1250 603269910 603269929
    0x70b0a05090f010e100806030115030f051c05030a0515031c020c100c150605210c0f0306070e04090f06020405010909052a09031006050f1e15190c11 65
    0x46170840d200220941041d44a031581541284002d00005410542c1041554035841103400a0710700c202007030484d404103c0100060700081103140541e8541c01040a401031a911020f000b40d5002c60711040454001d546618484d40e80c00c2009081312699001104034031041c00c030003254640580600e2004001e40e00386074000905440180d6503202412005907141c41d50f2401c0c003603400c642103544460204841c0c450000c51083c3ea0540d44102c0c51031098501d200d0320b404d00742c02c00c0d0b41c0100c3d00300c60164455140010b6081d0000198204150704060860105004001d071700d0000c0c0040c09699250814014039034010803c2c1c030404c1c0c1c0ca001689450311044001e50b401640c2e140701c80220001c42009002c2c1c00603036489807001ca110441d01e00b80071000024a041d0111040707005682e542e40041000b45000984461095820380ba2440307047d800c80c1c0741c40c40d825025401039020300400101941e143d100714044690b01749a95a28060000c1060001400360000d900c045030030ba140c002c0184590b1070b104038107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 603272410 1250 603271160 603271187
    0xd0206090f01180210050c011802040e0c0f01050a03110f07060c0503010b0706020307120f050610020d02060402041a03060c03160c05030313140102160203060a0626070b0a05090f01 79
    0x1c12900500650902c0050303105c250202c1e00f040400d0016110404084c000c11082d400c540200c00a01e442030b00401080315100e1002c216640d105041e403180d40d03111804001d800c481c00342011a00d6828030f120540150810130342e5465642000144803150201100c003800c02103001700000c2001910288003a00c0510083c01400d1380c0d85010b01c84080024050b40046030322181c2483c00320706203403080c844a030584402a480314003c40c1c0f25401c000c62424016040000f4142510007841c2a405000c0c4c01307500c2e100701410180c003c64580c142072a88041d6401e8800b1021800303000c9a8040c500f01c400d0f00f01d9904151800b980f81c0003c08000098603100307900c10310a45402102451441c0c607102c404200036200c011040303030003403080c29191070220001e1003e0140482c0a0665014207001031040606000c0018581041e003444d01505010003140c0d14080e142240f030007600c0052800d9050552441e00ba120303440748080d0340d800241d071811554400040c01c2c0c4100240c0b641a03410030308400540d07940402c1c070f10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 603273660 1250 603272410 603272441
    0x421020303011a0909010303030c080c030112140c12030403060507052a010921091e050105031801050a060e060901080c010c0809090c1b01060608040f02120d0206090f01 74
    0x5125901c00c01031410440c551000f00c403458016203d02140280038240d10550100eaa1400602030311a00050b245901041401e1090314542c1001040e6000c072a0010018283c8000c0c00c90300c6c0ca569808200c1030002c034400030070102e8969140c20003280e4079441400100c6050b0300300804104290b020b00305988581d0030303283c00141074248452980545405030b00310340385907641f00d04d845c60126506110300d07004030f00d064614040d401075500010708090019884000b850424030705009047d6940b000b00f1b130680300e0900c1d2082d80c0340c8400706400d1080d258040b202101d03510300428408020725070703801a401c40e0b011407000f0003965034180400081590902c1070b01d0081e0400d004044843d8414000075440600c80c103005400c05035842c0101d9030b120000c640070f00721600002920000004842d840c1019412400c00a0214a0030420010008800948020b042d200340c900c2940441d5591384c140e81007101030101f15075489040500080d0381d20000d03a580c08881c00b5055a58441d14410b000f0b0981c618013003507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 603274910 1250 603273660 603273667
    0x1150203120f0117060f0f0618010f08151b22230303160201080606040b0712032406080406020f0c01060306291c0b0705070201090905151306080106080604210203 71
    0x9519046c1c0d1072008100c542d00c0052241d80c203815540044415001e80bc0da100149900740c1007540c0b0714500104100e03c0d44120f0300c104100514400343e02c248528094440d4242502c4e1042070b00c00e80040944030ba03140b000040840e074040780705003459814201020441d000801880109030038151240f158003a500a600080340c0ca0783c0240d4040c000c159000040540488c4ca400d0b5034a003048019004090221a01c4400d4464804560381c90300598804954030000c00115109921030b244950f025441618240a0818006424400150306440e031800484049603600e11000c00603034001d20031303800122181c500e03103108450300c07000109000ea10140459101c8030013404840401813410100d482c0c200310360160289082c0007521820034035020b1000c940f01c5541700d4205100141c000f011640101c0c690700d01d8001040452070600b280a0b0704501e094a1000d04005046403040140040e07030030030700507503080c0750740080e414100040480c8540c0c0100e201028100c03c04408811040042040c000180d1051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 603276160 1250 603274910 603274921
    0xb03060a0b150906180f040e06041101020309090118020904090807061409070920120f0a111c060e091005060307050109170727050a0506010801150203120f0117060f 72
    0x36142c0c0c990384c0c000c06c413401200b0000001415104054000120f03500242c1c00e100c00c0040c2e041e045e07181803409002850420040704007054030200e0500c40d400030324021a41c100301c06a0384e0f0b0b04460742c01c27a003d80300703002c0d002c5a41016030140e4840c050494007030345070081060406501c0d03031000d0b0003146400040c015503407074403185801809140b540f0300f81c50a40d5583c2d0201000282006003000492410020034501d086682c8450001c0000d100312035490610301401d005454440c22154105c40b10b9240c9101d644044410a0045c01c3d0358120544410b1071405200400340d0000d213601c07420107900d10600003075881009241d160390740e40c0b00e00d0b4040f4450100c00d00841d00800211045c40b61400200c0316210f50702c0f100e207081c0ba11000c92144108260010203000c20b503090085645c80104828140660300301800001c2c90700105101d5407400d01c48841c6030b81105131003442180c5818a45002d0011030f403e00100c10744401000b80316082d07240c4505a008550145c0200b001845010500d0000403156070341c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 603277410 1250 603276160 603276187
    0x42013061809120e0112061d0a05070c0b22060614040605030a0206030c0706060b090103230c0904020f030a020301050f100f210509060906070c02150c010b03060a0b150906 75
    0x80135889418000246034070002c0d103030903120b81401000c6c44000c3c4111031000c080010f0841c0e03005401520800d04103003c21041e0307900404840d16956110702c5180c0c0b680c0c1c81e180c0301503095102007a20b41000d0000008803003801002e07001030094980c010103011515044004000440d070070740c414560580c00245038900949404405954821010311000c2d01e012100d94468044401903001102e9044021800061659040c8a2072211002181d10709996601340644a10b140c40b000300311080e4942d000074018100d0b211501910040c28600b02c04136164103002d6005c402035042401168000c90710102030040341c1c98190b15841034150941ca03910391220241c10202c80700090071030214080c8440324603010504a451280c41c1c402c40d000001790110341406040c840c18148041e1940d400c00400940d9040943d403205111030b05c800c03041c02102d640782c00d8903ca06024015640285034940600340802c6050200c503044003000c90022100380140e0000c01190b0320306400742074182c5400c604180f101b07825900d503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 603278660 1250 603277410 603277427
    0x5030a051b060f07030c031202030f0609040303020f0d0b09072c0406120f0b061002030f09040b0406060f090f150509040b0303041403190b04201306180912 68
    0x10141c4494542014407401c3e070540d902c4800c00b10001a05520f1217414103034000036950920f02c0100f011361440c00c0603225049481c0c80900081d10904c1103070042010103019904443c01c2002400e40b403612114103d000b00002c00862031060301895618002078070b103510a8039003101c1c4010710b1035190003a025076914501d201111440d55030b04142e48000c085a1411080d046880c814440c49000140c0c3c11a23113011104188003a0860b4000c04440258190700da03004025a9041c4520510060319900c001002601800c1c807060490b81080c03910501090407913100c110b04611441503190f4480b0302d561807400c040020224400c02d40040b80010007824120b204400800048000410100e02004c910b000a4215406688280c108007005c4005111909082c0b15200300010a804615003034402521041d1806600030710040034ac220f208801c038140e00015028058010025102950508090032080c00401b040d0060132a40402c0507403050240415000e840d810a40c0400400c20164110341e06484280 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 603279910 1250 603278660 603278713
    0x70c1502030c070905090d1d130603020402070b091203060312030a1d0705040c050405090105040e12040305030307110a150507050d090602071b03030503130206070501020c010906050105030a05 84
    0x300318100302d68104000d50005098101000161810f0441d4400d14000900070341c241480020b0f02404030402c00c4521400c215141580d4544010240300004c400070006034000039441840464600207000254034058494520310382102c0e01d00e40d514101c0e01050200311503966040d403210494084141005000d0364201000300d0b404180340707090003542c001a030144051074030a5401803808003c42d151c940903054200f1940c0c1001031a0604000115100e104140a03c2d8007650319450403851040040104a003041211140b45450b1502c0e40340040c0c90f0392007a21031750002a080c0c003803001170120210f03030903001a41c0315080550050440c3c11200141400900070402d110007409550030000d0703503001c0d941c081882070b0700040e51000b00d85024009484440418000d6594450302840043d4000c801c4075027255010a0300b0441161510000e00c240c13140b030000070b0040d400030130400f1001c0f005401c6805803d2052600744502d0b81ca540915544144101001d00290300000c175110815020313a03501c0d590305 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 603281160 1250 603279910 603279913
    0xb181203100e10061b0b180c060f09090c1308010b011701060215040302030904090c090c081014190b03042003030f03090109050d0c0317070c02060309150901060f0b070c1502 76
    0x1150329140c491103031b0b6084030003144a40b00b81c03096007445142400800c110410403114981000c3c0c0d401c43d46c030002e004006c08030b4021740c52100030420503078090341901c40215540010325803040c1c4a443d6076018107200c0d04142d010441c0720180c0603210b03400143c514180c41c3c869009000005001030320803405400504241c0070b41c001000003881c1501c0303a0041301c1c20513005030022109546803404000481d01e000d4403103800c100f010024040d030f0901c02c0c802c5034201c481c00307444ad050000b1420005691165089504d45d503515003817000003541000340024611030741c013800d0b10a01c0408180f22000c1e0000c0c018a6080d41500104000392405114201131030700410000300000c2c0554007503903a2882c1102e8004a000800e004140d990f0070180c3c0154101c6144001e240c0c004010309148001905507014880c009104620101c000b812000e0200180c012040081c9401151410040c50081c000c02c440e00903801d080c02d2061011a04245000c1151629030380901c260401378a80b00040026580c425102c8045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 603282410 1250 603281160 603281207
    0xc0907030c0306211505091e010e03130320030601050607061b051b011103070c030516060c0e0d0b01050d0c0b030a021206100c0b181203100e1006 64
    0xd9103691515a1035000503500c0040801c056400c151403203000104040c1030040c240020020702d0000803400380281d140c0234500c52005604070503d81c0c09016450b480c40c40910000c03c15080b4444020140380481c2d020744004503d030000800b91000c407100105400d60141d008138010845030825600414580d40900e00001b0368041046054200d0105d0803a2880041c4c4d010420300c000491110f00c04d2001303200304000b00107090441c0b004403c1e5020081600381802008092441814042c1040783c00500100180110900e5203141010040000bc24100f0000b8200c894606960404010018101c0d03002040001c0507803800040041041c0340e42c00c11540001e001c140011440d070f01c0f0003d1400794824080160b1940d0031070701d8001d005132000b003c09124501c010040751600742c10154065025030001c3c209006565814800980e401010b142000d0504c910480c182181d148440070390701511410318500310041da1006141d040c52030982c0d884c8035015515100b041824080d2000e45801140318000380344 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 603283660 1250 603282410 603282419
    0xf03120c0303011e08060403120609140a050a020412020607030c050a0311100501030209040209061f0507110d080d05100911120c0f0a030902030f06090318030c0907030c0306 76
    0x50940008440340c0040d4030102c0107201c681206184100104903414641c01c1d10345c80e200c080c0b503903200054401303000d000035010140248501508104058950100305001007035000b03a59085112040394440c0480b441c1c0b00104070850003e0086508490a08004c001c06c010ba580802485910017101141031100e2100814005042032240403143c6020742c03215144900220592818490071a8080c20801c2c51b10005000603543d40c04d445805c16010388541907582e07506404a0340740e54051184850403440300c651121601c0e80300000702300d020b01c50702c0940c620740c100d1030a0101d00e03145204010500d95050144040551040d40629406803050101c5108140d44002040489001c401e08120300c0f600024482403400041710845c0e000401d15400c84d1600e60a40c6802480c2c0c003880d1801402c15072502e500b83c056544c1000010400715603002074174074030f06000304610f950358030100e0030920b1041c114501c1c2486203404940199900405030014902e41d40d40803003140202246050041030640e109000316 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 603284910 1250 603283660 603283693
    0xc151302280b0705010b0108041208060f1309050f070e0f0415020441060c07150903051c050d0b04090c3c0302120a05010203070306060f18050f03 64
    0x30050800b48030590b40c0c0e01e032600b006800e5507074944016040c0080c001c240f1000890b20782c4050a101070fa490034404503203c0c840050101065610001ea10090201c424104c0c00195807102c12520b0ac12011035080c410902d0205803140001d00c00e0203400d5a1110020f240078420300101540240328007502e04c41b40c10100c000204030f03049600112030035009101e40741001e943d4840c82e801c21482031150400304641412082481c80c2520400d5409510041a0840690410400e0780007a02c0810041e1039605100348004000411920055465205030101c4d00002d00701091714074150080d0f43d442c14035000e1010a03071000383c10340c80000c1e070b045a0307907000702808107280032074040c00340c50400e040f11801c0410903140018220305041200c400114800402c00f52103ea6590404482c0e0684202d0702108000745442d043c06407107031b000b8005500000400004a5059204006031070341c0b615240319071101c1d00320407030b01c0e0b03000303240c024030520205401440745181031b01104a81d50f80050403500d250b8030540d080c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 603286160 1250 603284910 603284989
    0x11040905090706080a0b032a281208073306030c0b16060b0a0302090c0d060b120a1a06070b01090507020a020901210b07050c151302 58
    0x109541d040b0070424062540e00c120f0098200c0d520400510005079598000b0741c071480e036200200107628161a50b82c0349880c6542078001c1a401c000c080200e42c4000341c280480c0c4112400a003a01d64105040c00b0407012644035500e10174a40240e840350030082a6a0f89518032007010401e1062400c083c000003006030b08256400b84e640c0d55038400172841138591310700101d482400b40c110030982d0318240800c42400650340c4e00400b8081c2c100b0780105c0c405403020041500c501040d000a50040d031a0000c011095810304018160352044000400c0003640d200340341e18050241803c0130581e00115408036540d0910f940085808845911203042007941000014400340d1018500706d840100b180c004111446192140c15030242550015104901c026400074a8012050103803070341a60b89161000b59038941b41d00b01c004003035405107042486040010300a0300a41207030b50031202c1c910440014024450110711004c1c0561545508a1200c0c0201c0d0308100c0101c0c20400e4080790321004150b108019011250305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 603287410 1250 603286160 603286171
    0xb060c07090e0a080c0c0f030106080337110c0405070c060c210c0908070806041b030804030629150703050d1d10090506010b030703021e0417010603051011040905 71
    0x7008140c02600607c040503003008034062013640340c12810041400007008991000660404081c102d2070b00f465003042c07000b00c041c2810101c0000042032210b082c0c01c00c2c80072042c98001d00490b82d403040040c0400082d03420494003400040c41b1140140000780301c43d0031109000c0c1c07807410704070381101e000301c800409003180341030031202c41d0785860740b00c03c42c04c0e000010400a40340f1040a80092820003040507070301c070f2010340000d040004000c1882403400201040b04003440d8800c510035038a583c0c0c0d0800a02501c800803844407580e40c90560242d050540038544001c4034005450010b5450451000160b550000d102c142c05100b000c01400d440c0010354414600500c100407038000020f14290300c514a0503080007489050240313081d000da030206400158280c11295100c2809a40e95580e0404034081c2c000c400703911112220140d1910390140030000a00300340d408195003a86005c1c1000388207420b80d100b42c40050102d41100c8105508060b868014007111180f46400380d18155a0700c98810445504a0f03c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 603288660 1250 603287410 603287413
    0x290a0311090d0309332d03050406060803070201090e0910020319050606031e040f022d0618100c0f0602030103110103020306011d13021b010b060c07090e0a080c 70
    0x288900e412020000010010f0413010b6803048420003202031a0f8541c81c429401400140481b1202c0c0c1407074a41ca007191207410b06660301c0411034000016010303000503a021a0f0321070030401d001c54003010020503140080d070140c2d1110304c980c0c43c02c1841c1c0c1070520080c0440220307000b030b42d00000300c40400d03000075405001c02043c80e4510240c1701c06064200d0304051310f07891017041c0400c140158020860710008034500d070395809801c1d984841c03400710340050b14501e00a400c18015030343d800008001c240e1408010319144440e0200d10312440c1004064070403180c3e04019405c03440d0044543d410a11814035030b81c0b0060408415075581515401c041400203901182d031260000014010040c1021121451500a003015400e500381000080c3c18420003640a0703840c141fa046021140e036691030410068813001c05411955510b022030004820325104c01540f4040d0700381202101d2604190040302e09a41100c0b02400d4482c2c140900c0601400410b40a4113151091000301004100c001c80140044442c100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 603289910 1250 603288660 603288677
    0x21009050f010608240702010b13021201051210180c1e1d150f040e0d1b0c060c03020102040810060914160f05120f01290a0311090d03 59
    0x2011500f5a000c0360010451900480d00413008043c444541154030040d08000740c4040d42c030040304900411025140640c081c00303c4000b4108860303a5801412580320341038001145a803100305200306010100480340c1c05034411070200d000007159610204420344414040c1c0094022500d46200084440e00240d03299031140d150b0740842003040d0b20740c000910300b8880011484604114842100300014011001c1642410160380140e680e40300349110450010020801c040d140c4080ba544c0d80b64182d07580000c00d60390010551b0540107226540d05403503100d1101503055082901c11940c40040071412004c3d99028003010480440501024030407198400000401ca450250181d040e110031141c1d0103903030000d95051002ca07158044104881310381c9803d1aa8000011040c00c8501c1d100e00d00e41030800300d44160900c240602c9480510b0f040340d0011564640201d80200011004200300700c0759001003500700b01c08000140203800a401e40f616134040c060518842c80c000c140c0004040008130000361859 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 603291160 1250 603289910 603289933
    0x6180c1b020d062301140f01020f0d0c0203030705030406020c2b0602090a090f0b01020607080708040b040201140c0105040c080703020102061302040204050a030b060406060c08030a05040302100905 86
    0x11445024420310100051034000c50781c0100d5140b00e01008040d01080d151080d040e07248448886542c4d1414442c10940019a07540c100304040c1c201c40710b00c0b40e03c12070b41a030100940758400901c0e440c100c648540039000c0c2010310801a80d554128078402ca8140c00184588070200d02e0603c050001010700707401030041803509104010b00d90000007442c1070001c1c4117a044c00c00c0c40c41200c20031164607a10a40c01680c0d005400d001401c09299a8050107485007481c1050a01c000c0d150007000c0c54001c2a000c65403180c403404425180860308940c941c00049106000401003030b1007221b0a07810500604085e10721300f10342c8040e80901d0344803180000441c0e4603030381400708002515a01d00d00400381c28014042c0c540c203640c0000e448105c043d2049440000307191000e02559550343c100c5008080060103074220590b40d10300a40111022901503104916003280041c00b24003030072846003080d5002c1c942c01c3c5540e6881c440a00200b00250013503085120300960108101c60074403c1c0c2c50300318000d0005145c040e190 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 603292410 1250 603291160 603291167
    0x3030c15060145030309090b121903031805150106020f1e0f060115091d0105010309050a0210050403151503080a054003080f0d06180c 59
    0x9020241001461041482c0c01407440030580c0f04034044005181c054248040511008100d4090060b48603072000300c000205a0080f41d1030701155000c80c02030000d407c4030320402c001c01030305a5800c0ca85030090308003006068031040100039201d00c6410002082c08590801400c05c0310a00c10444180e440380284070074803003400c040c40e401041e05100410400c07545800c400d865598000507800104007000e0700c01510401070214802c6060050202da60139a581d130100c0c2c0000e003105110401150000e0008079501410222001c990000e01c19602c1d00d6920b000c0046008000c60030080d00d29009101e000001684c4416200882e418160381e007d0329141582019200810300c515400c40aa01c1d0203144e002409110750080100c0707400000031522040b5040040c0c1d124031400580e0010019940c40b19941484074901100d070710b0b8076114148021100d04181c5404040c11400040c0511100b840b8016400510304004c040c030131060305000c00c1e401d60740c4110000c6004480003aa02a54451802c0c2ca4566170 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 603293660 1250 603292410 603292453
    0x4090b010e100f18051e13020405011722060204140d0b010302240a0207150302090f0415031a061813030503070e1f020105010617010e100503030c 64
    0x1400c075100c400600b510180680100c8920b418a820312004d036624180a01320309004100500000d051112500c85c0c0c109401d041d103c42d040210301c6103c03540745088500301030341b00365016210103850300c400f0340290415015400781c00900000c428007402010341d011182207040c80701c23a14441d40d070140c1c0b100d0501ca0f6031a1100c1450440d14091081007200c1004900003641780350440b030701500c180141c11041505180c03444101110300c0b8007880d0000e01140c4565001035a541114118514a80030031181541181a8411148550b6110b07010703c0c5903c4407850246d0000c1010425803003075510b55592652042841e0340202c0e8026050301c0319000300300660070b101d00e804142400302c00880755a49019003009140c944182400b03000c000c0c0100000706d20718041c1c01b6064012000800300c1100704a83c02c1541745204c1003038461380055003400300020b0028080c2516980d00e111100c0b601c8510703803e103013242a8000d130081640e01441001c1000042c542c40a1004051441160380a031408909a40310020300c0035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 603294910 1250 603293660 603293687
    0xd0f06060e1b03040605090307021002070e0105220e030d09200f03060403050904182901050307061b0602030408030f0c0f3a0c03050a0b0a0b071704090b01 68
    0x1c0030042c6040259824003ca980c41070f802080040c5a0302c402112a00c0d50190403402500310750b06a520f0515141c0000f0300b4421901c826503a14070a80c0c035501400b0b100c14590924107449000d1481c09030310210340da0410402c1d000003004030380c184045102034038240e40312204244c8001c02c6c0d150041c071180c030049050204482d000e44050521004500210b80c2e6020020000740805c10301040c14003e69583d6080503029040345007110b580d0f411f05040589400c40003490071302c1803c0841c070b0b41c60503101940002074100d81000b07000d41030880c5481c10a0390502c1000369003550824452040740c0000b0b41a1002c1d60007980144600d0741c6a103442084540143c1c2c0c01381642c06280024130a03180d00d107a04800b1501c254641c01410814a134001036813903043c280070303803143c00410143c0c2141c10001d03c075a4805641050310355070a1101d0b8403280c2c1410200c1d5000342840341c101508107000d0264030301c00c40003040f00714403440c21012108069520003a058000b6044148001d444401401d001d6034444103070700c145d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 603296160 1250 603294910 603294931
    0x20a110c030d08040305130b0d060602060f0403020c010e011103040e0612031611032b030b120a061125031103120f10030f0501050106020715020d0e0d0f06060e 70
    0x2400000d0018103c410018030003010090002803120101004070603110040102c00080354542e200d41c1e11040c050301942c02281c0061245200003000480168401c40c00365170160060000461030100460f08020105071075410b101c40300040302402203040000b40010b03c18103461680c1c038200f100801c41110b02d4015840740710b62052100a480e0180c08405501d0076031711031070707410102e103000012030b0401081c8150301552004048d521454050303000d040c1d80003805241e8040001301500c2c820491010006250380e24245c0c01100b4200000d240c070b07400101c1d03500701c20301160b080c4850740d900707420490701000303400c0c0e042e00c3d68404200405400408456481c403001000e0760402c1d400031081002c0c640e00421141c145c0700c5030004034407c070090704100b6024503040f00c0c5d01c0b160742172a404d06501a000a200e000014450404001581c102261a042004240b580504008403d040c412180c1c5108201307010740c800301d4501c4410018201001d083c0d00c50307200c1d0201140722441e0581c10165010000c000030f0b0a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 603297410 1250 603296160 603296173
    0x30a020603012603182412070905040c0210020309010e071202031b09060f060409020d140601030920220e0d020f210d11030103060c18030201110a06020a110c03 70
    0x8007050f4204130280f2017055840111070201c400082d40e80b50481c40700f05c1d1035845d0014402c82401c410b501d6082c0b01b01c20a4441e00d090b503940e0014442101d054075503210060b00091408980110306070011504600b03100d002054101c0448102d038217000243d8403081d000c00c1c0d80d007141400c6090500840e6000700038aa0800303200c42c0340300d010400c910802031940d44110400201c4180c0d0380e0790502038901520300c07058119220408800c00000510040310f180102c0c481860005441c4e41c443d00a041c2115444118035402d11069032005005410302300f00340e076111142600840c0807100300400020416125200810810180c0160600341352070340213034104542003001600103440001503415401c040d294451201d06082e0240c0592901491031032208003800c00d10040800c039071560146068901420040100d058283c50990b04210003040d080501c5421202c10800b42d80110a0a200162000156001d54141e541e8050480e400301503010049800040c41d624201c808021240c80940e041c2c00400380d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 603298660 1250 603297410 603297427
    0x903110d0b06121507090501030e0a05190609021e0103050709080309130212090a0309120c050f120109060f2301090c02071203020705100509100806030a020603012603 73
    0xc0440082c007030b42c0942000164501c9207030013007008010b903848411460f084d50030400d000603c40840b46c0b180314000780c14110000c1400d0004106102055445002044452030901026054114040007a107145035148407200160300c400740f40c0a0015102c64040b402010b812001604607840a021001042490303c4103111444000040b5042d441c0f007100c41e50468000c040421000c0d00c0f4220120f148111100c05008000a0000b045820b4603c0398032401085030320795107046544001d0400150400754032810810044c107192860344600300d00035101610003130700580210300b503902410003198007a6582460072184481485640520700d13a00c0780011a008510000580d450f00c1800713803003100d0740d039a04000c1815000304940001052020070035000e150043c1000382d111052442018098000c010030418954032480484500d030800500d0210210065141100d000c1c0004016603054031500003d0300c056aa44006103009083c25107140d00300000c85081c4010340400c0118502459005000248 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 603299910 1250 603298660 603298673
    0x6040312050c03131502070c08030a0f0f020d0c060e0303070c020406120809040c02160f03060b041e0c020106090e0303091510060807050d0603060b04150f03031803050d0903110d 78
    0x50b00d50131051701500c82201d900203038020710526000070b1010068075030000309501c020024019001d955240d0b401c028403619000c0d1284604109d1580041e040028038500d078502031507212800ca40114400161100c5804e14286954020380b24035000c0780b242002d445c114500382c001c0c8006810131110050210000d651082d0040c013900402a1040e61100f0840d02628402c0203a400100c1d012115490303540e684800d100345c00c1304036001c140d5089007014101e0402d4142402000c1400300c9444001e59444544020040104840f00b044030440d52543c1e40007a103a615070203081071a03440100915a20700f029841a8502005440510401d056410400c510720186607032541c11614075050000d42076562075402c56840c4039141e40410180d19112001c030a01006500c02041d07800c0503070301004034490445602550050510901d1464020f04500340002403082064564801d10012003410240e129528241130413014180c02c00003075407551003082403102c0704d900b9006091059401688184041d240e00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 603301160 1250 603299910 603299941
    0xc060e1201021806030a11030408070312090f060504150606270b1c09080a0804030f02060f1501020102040518100b19050c0a0c2402060f060405090a0506040312050c03 73
    0x200d00c1107030003000140c25000c140d08040f110380703000d41d00923649180030b1900e00e1607038210b0b03d01a800100c1d01c902c5079035080070b24071072072101c0ca400003803203c114031460b594079010f080003d0044034058040301007141042d011f4000c0401505070f984a404240c070610700c2c1b0300c92001200d17403503000500d6a4072041040d40071031740480300a48914542c0c2446d407030a040320140070381314080005081a00004030b80c14901c2e4001700d000d00541c42580e031102c076201c03401c07404c0740e0381c5009440d0300d120b080300038000c503402982d100700c80d4042c1041800050b082ca9601c00000b00c848041c245c0d003400220a800401004a000c1d802610103020b50550042c1082081d2418246000344400e2210034440b00040c403c40900042182d1001d113580b080c0c0e0b90810a840313070295040303022048014030301660920007242c2018008189030340301c1ca031100e05050503641d0764410440900300190124400c0d001c2c11400c18040f9205000e1144554040e44a100790301c441e01c01c4040445600403c16201c88030f051092190225085081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 603302410 1250 603301160 603301207
    0x40614130302010c170706050105090c030f0a0c0c050f01020403031404030507050d110d05010e120a080402280905010501020c0a06020c21030403050c100e01200102070c060e120102 79
    0x31111381d074807468504178000320075036a00304c000b0000c5080300401c901034101505032801a03030b0058040c2c40d03d40b01030582d0302003603401d10450045900002c41080300c5501206540d06103141442d400076041c0c55050901d261070300079004a0f50001001d20038142c0001c4480812130504545038039051071070312401d0300d81c002809524454138007040d0102c140494034482d0300c0400300041017110400e0042c50440d0007010315001480c00350152070900c0031001808025220b004c507694580003815a40ea608000c0740040004104003403a142c840c41028070318844a641014050316040016694101400a4500f841c0540a00d00c2000d0100082c8445a40170403030940189080e16403100a802000028505a5240300004550720012034000288070f40050045482c10b0300b0b40306440300d007800d00011580d84d0801d07100076010880c0c154080d500012640c6500c028103160200060602075156940c0103440e0f8294000302c00100d0243d0407000d14074002c2414804081000001c610305035440b40c00402c4404e58001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 603303660 1250 603302410 603302417
    0x30a050411220501061b020418170d05060f0d06180510060612140601120f0204060804020906100f0c05120c07061412061e0d0804061413030201 63
    0x49400c001c0c007500c0c0121448002802c40321840e03481d42d9524064075000d0000c202840c00c1c0340002441c0c50042030084082258502c001c14414603035000c1c00043e002100341c640702255510302c14004546030110a0003030391000140389584008090004081e52000352400344504028410301140e903a0b90381c900131441d940400b0100e0703d00031451910a180042d524050000e001d00780360500d00e49441c0c0d000d03105681c0d10340c903a50100c03a01c06a00c01c00303c442d19a1014400000b000103e8803960003600b0708555100c40a5000c20b48100c41881c134020b030382142c0c0c498030115802c207091100310324241c0111544000c003030b105481061000700300100b980c0c0b54070029000703000c02048100e052100a000c0088040251400103650703a08081a032951200217100310000940a80c80340c00905280d142112403007903242c2c10f5414030792a10002c100071041610110310808000a0700c0c030109454980c8031101250140e02c03095103591600401610000c2c40c1b854088107104200034400f801d07050030881e41c2c2502d4082c0f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 603304910 1250 603303660 603303671
    0x71d040e0c10020304080d0915050c12120f13050a2604030809040b0a0810150e1501020607030c0c0f02010c0b0c071707020d110a0f0e0a0c090605030a 66
    0x160506250340c1000b504660081c0c002c45031260000002c10446041070112002030401c1041198020700c580202d080b041c1d01c4180400c101d501c900043d10302d2011050a91304640818244005107521851054481590a0040018118504a82d079512040d001030000e035600d110b0791450744424450400814090031506204c501003079003c0e101f50454205000e007a644c580700c0c2400c100580000c0d6801e0b103d00d00b45400c6094030308200124004071600d0700020690b0b8903416181c1c03400341c10b00d02440c0c620100910800515441030301c00c00d80c0122001044d070030b80800080b00082c188000100440305050911040742030540e8010042129941c000039055211941071004a4030515141c00c042e04000b401000c2c412100342c0b0380000c01d02d043c4214400203202c481c0c5203688044c3d00682e04040c2d0301003c00c05000b40031505030070426940c00300c010305158a0319241d108440152170240c00c2282204061410003940035198880e022407403080341805890346107005c400415500c0024042068162102e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 603306160 1250 603304910 603304931
    0xb1c0f02040e2d01050112021005030a022b051f14061908072c1c020603150a0504020f0714030c0604080307260106030207030509030307030e09071d04 66
    0x14885100c04143d0503500203100011000440c0d40000d0141d502641546040000540089a802d1090115a01429407101c035503900900740d605810040150088540801908203402c244064411001ca52000d04078045810f0b0684181160002492540d0301070464070b03003103484020758024a040702d0a01107031041d514903250200e01d050081d800da030b00e07554445209142c2410303080305d2041d1142c0c42c20340c4c5012280403000d42d1b40031140440202203410250030303204400315042c0340100c6000d0103402605490728545030b5002c03034156030003100c815940c0c8101d4001203801e85000c0d489400105003c031400d500340140d01850340d0803803180d16002071030240e0b0010300d030f065541c0910070b844840c0041c01c15201c0c240b134142030080c1c003070b4812240c081c00034186000d07095480740c51607190200c002c044276100300c0c10384c2040410750003948412001d4003801010301c0741c50b00302d42d400c00090000f91300c071341e98558001840d40d06004641c0400303007600c42400007080782820014440b2102e240902d00450b404607100c2d004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 603307410 1250 603306160 603306163
    0x260d090501152702030c0909040f0512040519030209010e1e01030c0603050f07020706050901140c010f06081209042307171303140a1e02010b1c0f02040e 67
    0x4010300103440000c256800603a00c809510004401194189803036805105080072100300d10041b907491030f2520050000482500301140d0582d8010b100c0d0415041e40c001c10b03101c06140c950317041c2d140790310300c000010140b02505000c3e80c103591018030740601594940c1180e0024200a205000d1646080c90079800604d0026141c8050071100030803002c84034555840c0c2c10310205010840c0540d50200f4108400310703c140c0c9030414241e02c5458698054035450f030900c181201d40398400801141003010181d51250304210810042c46e2654001c2c000003414807045044c1e800743c490342d51009100d074001c810803610348040c850031200986012640004e8410300c0c0207509140030982e10040034014030070400c104070250400c200f0454500c1c5c0d00040c541580c0c2e4404840890220248001c0c0000d04070000d4503a03aa54031005070240d440a4240020344031000040c0a0807800c0c070300000c3c1e0060b91a964292180c2c00c0400712148a0f00145180781103020207604e400054040c0c01200900840d070301c04111030f15100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 603308660 1250 603307410 603307421
    0x30f06020f16050604120815011409030f010e0f06011a0d0f050702010506091b2505060c0d0c080c030112060b0402030c0714011a011d0d080403260d090501 68
    0x601c0707002c1540004603402c0c5036503998001c8a0880303002c070036000c05c403c5503406408240e2184a40d9410b140c0c108000b030004589519075040340340310003c02448483c50b159020b02c00c8811030303c1d808000240404080d80e00310318052280e2081241038008000500404c030100c0d040314040c8550003065a566810040a032004040c511403009081c0d14140c240328807207906411650090200303c400701c2e525141d61000f11180b000350094516104010801030a00444031f00b20002000f041148841c01058a5110a82414002c842e600d480010001c6c8001c424442e074410841c06400524160786a07161000065809d8030060013241c2140b41c44810907001c220a5070008103000601920943d12418210074000c065080030004481c003010011a81d00415814464515020240e500901c3c07000f07214001900c011080782d0103c29812045441c220085c0ca503001e2189042d0b1240700419a100c0c030b141020a1058449003e0503c1c05504581c4a00301002c44002e48c0c0c8491806500081c881c041858840d00601 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 603309910 1250 603308660 603308677
    0x50a0c120624170c1f021b010f031113030302031b0a0b1801291206130b0618010303020604110405040203071802090d06060f080316110a0e0f011707030f06020f 70
    0x401c0b9014400c620381003a0f518541e609102c0d02100e01ca00b1f915041c2c1d103140d0780318007085400550280c410580d82ca10076001501d035140780c039598616010000d03c007030001c04c0c456042580035a20000c0c140905031030900110f400c03841850050f010900e080d50b1401460701003d4800d03891803400c4103640059290a501c0110b04030140a0750118050000d40c0d11840d070351404469501c0b8400d0078002d11007801001c644c56100d410130128086400b20107580f4801c840c580a000290000400d0340342d40c0342c24000302440d5010318002d800900641c81c00d890300c0303001101d613990800d005034204400e010050318005003e80540b484e0b00051180903180b110050000c2c00f4040140f940324039800f02003014400103031310500956030410042101103440305c40c82540d910a490242e410760f01102c0c803400110b0080d500c292040c031300050100349a503507102e03a40c1c061131030159100300b048152040104401e2034207920125503160303c04d010f0504580342d5212000c5260101201518003500007803445020302c440c1040b1002d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 603311160 1250 603309910 603309919
    0x10e040e0d081f09021308030301180501170d03092906150f1c0b0402040303050d0f0b130504020a030c08160e22050a0c120624170c 58
    0x2a00e03480000c0d940c0e410403070318aa001c10568800709100300034618090000303d62806000306000d141821290003540815071a800c2d8078410344c40411950720500046000b407105101082c02092001c030700a040b2601a40940e4603240c0c5c004a28040c4072000ca011180b055150400241c03242960404100a420102d40541000142d4003541050300b100e0380740c03501503181910314230006804c118203480d541c8240d0801002c4c0e01014041290303403100c140003e514000c98030101080050f441e4011400b680c01c103400032800302d08007041d40b05a6181da4842c510070040c082005000c10480e5901107903886c8400c0c3c4ea401030041d11500010150744804080100039039004a050418642e103803109510f50b00e00c41c1c403400300050b00045c0080c0e5141184015800303280721101c4400081000c0d07104030b04042d100c0c4003c88a0380640050480032882c44820000100040310041e21202c1440c9054811030315581484050074607990f05080102d101c02146000b600c01c01c03600203080380700386514240b41490700d05006138803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 603312410 1250 603311160 603311171
    0x60109030602311d100b04140f010c11040207060e060a0c111c0f02150406020d06090203130204020a091203050405010915021002030709030c0f0302030c060f0306040506010e04 77
    0x8400501501c0203000b0420101c0f0f040d500400444090860307a01d12520344002c031008000e05070039400f00c0c60a5002402c0c03485505000341d4441c910801e80d0010f034030051401c01c640d6116145030409811400d0540824070700450302c500207a403448054400c017081213000340e0740441c98070100b01c13240e4051420b0f50182000ca1308580f819840b2400600710000c500d50010f00c00122030700c12160009071170302000c0d0001e542503403d56038140c030890361a0550f03a501011445403001040031081c1110002d4003443c01b40302d000d69520110030b82c00b8140d4500b640100801ca00c108200800782d643d060200c01240d0b812900565902c42c1520121003100c056040400d02d6901450210201600718006001721303a42a03c841505681c2d81d420854a00d02c00095040540c110900704201c2000980c0203507484101d6060080384241c036921080d02d10445900119400c0406c49028015490304104406805070202d07081450a180d104000c412800041c0c0000c0c01640c494000c124180c1c054034210b080500003034000c001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 603313660 1250 603312410 603312427
    0x90203070302130f03020f0a0f050411041509050103111c090305091905271f0f0306020408101e020c24160e010e0f030c0a0303080f07030c0c0b060109030602 69
    0x10783c80e69600c03040307104404699140f103448c100a25546c040b18012290900120705d480d0038000504240d00c4010b4200304100008502080e43c0701104400c9116a5984807a07181800009011601121560100342c08103000c1082a610010307101440807043c00c3c1c000c5034080323051809407494003d185000ea400300c040054000d9a1800300c4210040300c41c21540d0b41c01000c280c01030b00d06144819040566203840c0d000024041ca042e51081e14089210050803d00389546c2d038410610450032134200312200303600001c081104440c104820501c02580d500104900c08413070030300d034103880c60039010341540680101d5040b2014000b0300c40803040249041c1c800c03121881807a10b0400756903080b02c04401000c0741d403120103500d074480c0f412200e203944103071036040d00502180100000a4201000c50364107100d8101d090300b00e80c17034800b07484005500c2515800c011f03080c4400e0714040c12800404044c1090320301007018035082ea0041080052135001400b40007281c503103400485150080b42c00141103580001503200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 603314910 1250 603313660 603313679
    0x10c080d05180721060b030705030615010905040b0a050d0318060309150c052b0e0705031e060a02091201091b06090e0a02090102160806042a09020307030213 69
    0x41800d00c40605442800c1d84865001480704c3d0261200d02c2c20440c44a43d19002032150b50101c0022140102225030740707955040068903040003154003c44440187e0180f5a0a5030000d1602025280403141481011500800b00b038006c840c610401e441101d20241000030700d40241700100b5264401e8001d100346944515000c1e020b07000301c2c0d070100e0707003462082c14482507074500740700d030000112644e40e6451411400c8805120052003400c2d40b5500306040342c0b1004201001c5214842c11003040401902c07907a440c2c4400c143c1064031300c040b041c14501c03454800d00d16164010642980c4003612074001030f00d03444004007040880010b803c80146642c83d040300c1c1130a201e0345d891080d0038182865814440d4035115a411101d15007a031240c00b0b4400303407120104e0864400d68014145c0610184115100064008940408044258800c0445801c20310600c4240000b544140c044a000c0d030000210032001d0b0b2000c10300c134040511402c1c58460340480072500c1c035446501100c0c070708400115200042c41d1214150b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 603316160 1250 603314910 603314941
    0x1118041214070f0b040326061201020c06040f12080f060910050d0303060906050a061d01141b0601140607141c02060a050108070302130b0f120f0c061305010c080d05 72
    0x340c022072100540f42000045070740782c1f00f0509441c06a80001910303038500b44010038440c4444605255000c0c00b002c03403000001c109040c0302e80d00420107070040e10b255003006520f18410115030310411210f801041045040b0b983c1103038108109482c0048075a94900781e40d6013400c4e094000d02d83c4034102c1d40c03010051640c150000010707240317010710400c0515a100e0822200445510412010851118429443da0102120315111050604044031096200c006102c901d50201c040e207580244c04424804128104009150141c031040420481d140440030005d00f0900412600402402c0902403d01c850032050192100c100c0d2103000e1100002c0350940042e407240c40031203041d003010745400000141740b40c0010b041001c403900548000c6002d803403464110041c0441c8030006410001c1010942c40d1a2940070004155002140150544207004002076041005442560340302d024103100542400c240f0941941c00c4660909042c5c1711340389140760214250181c81d40400c0c0c10383c9001c00b000410001c50401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 603317410 1250 603316160 603316163
    0xb030414070315090308070827010b100c060c09050f10111f0506091b0a03020f040b040603050a061809060b04180c0f0b04050d08161118041214070f0b04 67
    0x9640342d47d41c0c0e032402200c120100729099081c42e1004440d803c044501e00d0008000702d2142400851105510808210f900d04060580c0d000034402d150301a05100f118800e02c015580140350404405281400081a40c0a4a00083d104116440b85e804d069405a01c004e040300c0416400e41718104140005000c00700340c1043c03440b04280c100b2001640c14602204400d2256100d00c3d151019091003181c041000c0e041003140505042e0f0130400b400c040d0300c091010340000d20402d00141d0b0313940e00307000d4010240c66000e4900580b090400505020300e501110b080c1c2c90095980c03c0005030003000d4203100000d40340b01904d2035001407a000b24020010840009001054000c9080c582c000c0e940381c40b0801030300c2040c415864000fa06200900251806848840d0607a000b106d1050400505140001d02280d112a003181d042c4d5a003004604030b400c085580311a551411148501c03545016155540c0b04080c00700e407601005659a5940e0700b129190054820a5410050182524055240c01440400141e80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 603318660 1250 603317410 603317417
    0x81803061f09020903120c070e04050604110916120617010b150304030c1205070605160e060909010e0601090312030207050115051f091e0f050405010b0304140703150903 74
    0x404142c1c25402c0c022540d85400140003400100c1c80e25814240b00e41002500c0825402425070001c2c01c080c10b804250300a6000304c003d00f816040c00d01e018a010b02d00ca50f0703403900400111082000e1980a800c07145a05804c0d42004804d10b07411043d580c008050301d4000300d4400a0508180355204015072010b204503405403003400718403090710860a1103020403500107001030001c404140006100900c184501111800d05a04218056841400355a4219038030810a0131741280900c22903030182941d1030904055804500d0f020340800841c4080b0300501030f000500342540c002c5403099100386e140000440d0081c40c010303259015840f00a0237580076142c151142d41c00c04040000b0441c45108400c12180c000f046d42103017052002d100d20310b00c2c00f03600950040c0b24069000192036050705058606c1c3d040810102030034039061229810f403080c4140c00280c00341e0710f044018403804800f0340840340c1080e00402d113808100c41040c0b106160140980008200c10142c0d101703031001111603003061058074484d48 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 603319910 1250 603318660 603318721
    0x21e0705041503120c0c12020d140102071119060806130908040f06180302040b040e010608071a03040512030c0f04062d1407020a08010c08040201020d0f08010308180306 74
    0x8412103106070048401b6100d00280c5000300000b520b0884c10303000c020320107007010305810190741300e4038041100a0212403659400080750400c002d41c98960600c0d1107421a02c4015151045021304102101c6004480500c210b0b400452017990700c0444841008000c08000c0c00f11034541e01c2c12096075001403065100b545003944010030641e025602e017005144107842c565211a03c1c1d502080046c0c03015030500c9070090340d1801c2c4007010020a004800240c20f1000c010130f55240303070002081940b40000503d1540d0310090082c4800035602040810540209441e030517142d40765421802d00c0341c401d92502d4480340900060002d81d850300100c45a801c5000340f9101503900001f01100d08003407100000440014a4403042112210105005454100e00240c4140340c4107450b80c40701c5003103030341301c441c01c401203699002003000b1580d040111040b1300030980fa20760045088800d000d8000e00d81800014244e12000c80e000400511200c141404208010121912810480001c03400c039051034045426005032003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 603321160 1250 603319910 603319943
    0xa1d03060406090b010b281b111011060103031404080d031b03090f0201081005040e011d0d0f210c0c060b030d0c08090a050303121e0106021e0705041503 67
    0x81d06444c10300303c01d00060350301d44180050031940b191035003042609104103015044580781c5120581010302e403185414841000141c4104a2030410102b0a002001603d021140103554041001c0c1d0442c0d81c141400703840025a00000c0140e40207582094540c0d00c180440802c82d150f0507000342541142490070881c1d4107107002c40807000c0c0d91240f10054090407074080f0904c0194400c095046c0d001080c616101c6901d502c8000003801c0d0364011300040d109a444101c9140b0080c80340003064150345408000300000745000c200500070000400b280014452000a140b400481d154800b424043c241001000100100c40001d0650200c00c04103a6280340b03011260909400c00065080c07114003103803500ba460f4052980c07148440d501002c1c82030b400001c150030018054800308003401c00600c0812030440903103080a0048403900c0c4000403a150302c4e2000e80100400d50b00820312600c00303010402101c0340010200e000c107243c0141640403581082c034000c07c2c22801714510000d072048d43d1003901ca500f60710000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 603322410 1250 603321160 603321179
    0x60a02030a033c0609090311011401080607271e3203010e01060815280c030e060c0703170c031f08010203041a0f0103080a1d03060406090b01 62
    0x2d80100700c0f203054042016681000d06100c410101e070440302808209140c031003014074180e488a90040b0301041c030001e00e00c0d9401c1020f0090800155001c0b10300003441d8075008840b5030f228005080c94061200d02c4807200040140800c40703071042100d452408000640d0349001d01c00e04c0050510607130b0032280301c040104140b0300789000080303464800c02d0708410742c01c410010340182d1f20311080844c3e0b0540d80d40840010314002070007504010580034000c0c040c4107121442104134140c00070407220740008903903000c0805290144c12003101e01000000001c03000c0303244200350000c000349c405c042c25500c00d04040006003080d0b800140b16542c426580d40f1401070303c19035844020801541d007000f104106000280c0314843d2290007095600040c190392812907513440c052822a030042d00c007a80d50005480024a04029817082c442e003040300c00f40d0181442d03155441c3d0752041d01500d0f10840410095048160f640246000360f84d62080004080d15104c2c145032a1010060005800449010241b0300000402c02c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 603323660 1250 603322410 603322451
    0xe0102010e0601090b0d05010f0b01080a0b24070b010f080d020f150c1b011a0102150a1a0a120605010f030503032805070905130204060e060702040b060a02030a03 71
    0x880748000d104590030201c0d0580900307110701e07200e03400051200054011038000d00502d5281c01c80c9200006a0480c000001800900010000e021450074000003004030703110602070614a0b0b0045142c070400d4484403c8141f03e0b8420135030080c0c50106501c00208000c1e41503400c40089803e1242190460038048030241d844141c00801805160424425890001c081c2d50043e40c0c00301a4450203031819140081d0307520044104081104141e5489221aa8001403100c1c0ca8207906024002009020782d441509224504020a02102c2607101c1c40303c0100a580e9481289442c500144101d4044d030b114102c1a03400300c20b00805490480c00c00000203a690031826520f42500d81000c0514a580d640030044220b0320310300002901564a4942d810b40d8131903481c41140d000304595510030000ea49000104080c511001c0002180e1074030401040090541011003d0307506801a142c880c0c96480e1800094001d010745601d01e0b8102d01c002603042c0f5040d502100a040c8000951010809807802e16910003a007907 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 603324910 1250 603323660 603323681
    0x607060c2613030309020a08011e05160c020102010204180906063f06050708041406101e151e0203490204140306070c080307090302041109010e010201 66
    0x112000418041d082c51403450352020700030304010540040550100b0050030441e031180c45540d5544000e0b807083c0302c0540f8001c5650141d100d00b44130381c0c1401a051104403585800720414010784007298000c590007034042c0c0d4024050040051182c03049602080b01504900e070044070054034010f07000c18001d08070018a51070300f11101d64003410b0340a5442242000c0c07102c0c0f07501881d13115000c46140000b0701e42e008142c440c0c015a0340c1c0141c5400e151401c954110405007800b03200d0741114040203100400c0c02d10881c12200046040e1500d01c24541502104101d242c000d8583d0040000f041d8181503007104844d10b013a46564414007541c44182c00481c0c03a80118448400001c001e84014000781e0a82c50084204071041e01c081440511040c441e5000d40c410f4080403080684c0105041014180110014041d0740060700605820302d8808002400340d40f401d04000c00201c00030000c2134030340340320300380e04406594050310410000c2032100418110381c0203420541d0009820f504503803555481801111101d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 603326160 1250 603324910 603324977
    0x62709030905010f170124020a050619140a0c0f0806011403190501320306040201050304081303060b090c07020915030a020301050a05070906090b12070309020607060c 73
    0x80c1040b004540c1e0407040b588140404c50000d0040c81e0074449100058024030641007240a60350ba10600d02c3d50003044a00000155000004c0c440003160011843e5944409659108404c548042014800030721054070961840c2c44060100502c15000d640004403549a07a10b4840402ca04800c0031500080c0440f0440d000604080b8100c0d1125002c80295801006c0e032002c0c0d1201c0038848001ea011100c01360f00c00041c00342004040c40100032543c1d29849205e140d010b29800e0b601d40d02c008242c1d5040050320081c10031000200240c10300040b00242c80c1d038079160b0003660308519035900300784000e0328081c0d4030144611004004161250543c4003100c00642c1e0282100c2d003d43d880200301d1540b00080c0307140d29014002c0b000f0200050b5428803550384245201c0348000303082d0038440c00081c0b0381c04190300201c0c10b10000f50302c180486880c0c981903504000240c00e0700c1c14103230f031060421000b4182c510700003508008041485030030003001e41c01055121105540f031240704207864640098182210100e40b044 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 603327410 1250 603326160 603326177
    0xb070e1009090b0a2d080a0b01150203160506091b010e040b031c0306080d0908060a0525020f0c040b01050a0c110604030503070506160e0904140106270903 68
    0x20b4203504100c07080100240031a032269690072143d010000c507052606805203124501c14050380c0c2402c1100040e01031a8000e059030801941c0b080265039043c0525a0781140354100c9441140c0f0800803100140303040360050480c0f5900380b90159488000ba0b401c040c0c42c1c0183d007641d450007030508000c003240d84816982c2000c40203400e002e1000500502d80d40e1030300360058014a4007106000c6842d114004080e580020740d0a161034189424109822400d00c1040b000c00c078108641c01d80066401e41140b01030100095589800e5540d0b08000311201840000a400041e032a01054022072400a041010070543c0c1c0720802038402c0000300d402c01c81030345000c1a424807103c1c400e07511400324035924603c01c0704da416400b80da2000041e6260030903402200e0303d500001e0100104003007405001c0e0820107486150354003604100d0081c100300c2c006c81140b0700030640140003a003070206206004d502214940000c01ca02511140b44070741e00c0c03410103c455400d092042414500440c284210060342e030701030395001c14 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 603328660 1250 603327410 603327419
    0xa120e060420031e070f091107080c010906180516051f0201020f0304050c0102190f0b06010e1801060e01090305151f0e04020406060512060121090b070e1009 69
    0x350340c01c0c2c0c0036150144250400050190410ba26102e0300c102090010f040c07451410420300f0529400ea00000107860030112120f5240348030038265259540d2010710103031911200420f550040c01410ba028000c58101038040e185003010242034503065009206440c1c020b10b414141100d07450070341c45160340080e6090a00c0c000d50031f1070049000544550b100140c41d1941055091400f40c10179a82a20b03207410040c1c40000b1981c0400c418000d144d4005000300c0c0c00030b034a844801d1050380012700502021030034400190315a210300c901150714140148140b941092204200c14a246c0900550001c1906140b03640002e6004410820031240c8c03103001090050b95242e85225081d00240082c01082c03c00e03010001c03003c444405046c00740113001c151101500c1c0c50300402080c2c03a401d60202003400020000202030b03440040420381c0c0200c01707007403009101c1400760640d40b84180e0703411845805440c1c480f91030708004c444405540907800e940d440e0b20800c02c444c820801c081aa1494000101c4c1c0c03080020030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 603329910 1250 603328660 603328703
    0x9020705100c050909010b09090717011e0e040b1801060b031302120717100b01020316030e0a0f0312020c01020a1202120301031b09020f04060e040e030a120e0604 71
    0x2002d041c424a0f04900303001509001c540320301001e1704100c882c0c084c040703010300c014207000c1035050b4080d8451a081c84920f41004c5000706007201801200100108501c810070502c60010b041401032004850300e03203081c9000d04103947c1d40e0354251400081e105603100001440c0405000c1c44e829030b0800c1d6001465a25070318010300700e00325a10030890300904101e00c000c8200c5400d200480042140580c1c40c00c503a0254808181012080b01c0142c002500d003881c0001245d9002041d90110340c04941c440e0021400c034102582c1200c2044460381d404403c002c00415510b8641400c0300c1100d11540901180f044001021b0742c881c1d803010141401a8419110100800c640122980702c4200900550f6081c40701da0515140c160300c240c00507240010f00205840403031035004d501b0710003015940421800e01088001c1c1160502c40c0b407003840100f081d02c090b4004550344590146444091010440e0794407144010b02821180005100d4103159181c40c28802e8a00b1004c07a469220359800b44440308039114449220 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 603331160 1250 603329910 603329921
    0x10905061b01020703020609190309030803040303060b160b010e040b130f02090408040608090703081e1908390a031401140a060207080304050607170f0d05010902070510 74
    0x142400703a401040c40055101c20700c02090040d00a030b000e0b0000345880100c075450100c03907201d150320910310302003030b1004a0b0b4081c044c6000e8a80c8081d50a6494440382000c9014101a801c40441c0301000a0f060710014038100141842d00c1c03051881300745903aa0340050104202003241c004d040c0304010030018030480b040d0444a80020f12480142c0d40c4000540c010840100044404845d0800001410300c0390f181c00c292080d40c030484c90401000c0d4241141d484101a015081550f1000c0315544100d02c451040780c001d032500e882c0b84032010220ba0204186c014481d042c107071000010340c0b941d41e9200071400d059503a03608080c81440242e20f6650500c0031038140690000d104041007660b00d99000c1804800c48070442d0080c146075003030901401d40c800402036022180d0b4041029903000003800c202c510390106c10749080320000c880544c2c81b202141005840c1c2901c0080300d481d10700c07001986d00c0080000c940a012404090001085079a80720071111b4100d20600001074000d40c4041d0710039000c0c0c0402c0e00b12 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 603332410 1250 603331160 603331177
    0x12030c071e03060f020301090f0507020c01080702071d011502160b0d0f020d1415130b030c0a06030501080714030a150e030d0204091505010c03081b03090610050f01090506 75
    0x4042650b07503a485110849403101d1a15494036000001004404014042c000311858088420080c0342050903000e076491119180031410f00540314006409071340284005001004001d002e090003030103900748100e10f5002406491409844c0803030f40010244006044030503e0480c1c410005405d0502158802d00e400c10160110415110907500c1c5560840340003810f0110000c01002c41c1000107a1200048000d00901200165000c080046015501c020707a42c11200b030900000101c00d1410317004030b414400803408050704004030700000202c1035070560003681200d2050302503694040c2c9a1902c107554060030040701d81d05a00030300402c0702144118a402225244c080400204010b49035441425034000307458040c2581c0c0d0100301000701d02558000d0002c1824040000e2005d1814440080c145000c42c8202804000b40200007840002c4001210f08140700000c010503240c2c03402c2108256915022111120300a42c14140000e0a092619000381505416150b044105003090203020180d00203515 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 603333660 1250 603332410 603332459
    0x305030a02040f030302030c06010b090a1707030828020613030f180b070201080f010b070b0a0e030d0603020f0406290d020c0706090e15010806010c06050903030612030c07 75
    0x8002410310310107010f00300444c401c3d000703185c8900620741d400303003040320581c05601060000c111000850344c0f1801c1d42c40c10b440d480c0170612411418540c0741403070840301c0d40006203100390000301205007031441c00006c503101d076141100e05c070240b8004d0804ca80360384041c0d4800081d281004100b0340003d0060009004001651401e1280460000404003188a440d44028213a440010b040400c1d940c1c4074035140d901c0484604200401d51410721700052510800300b02820000c1100d0120700150600e42060480031072960449803121071221345440103156520080784110030651040c3ca0380d04142c0180f000300d0b4101c0e1032540c0c140688003400f5002c4448170304040c1d194501080310403002e18042c0f01404031020f00c4030081c00d941d81482000390055265802c088003411120003004113000303c540401010070001c2c03a00c0102c0d40c031124016240449030041c000d2016007400304001840e8400806184640e0307048458042450001c0c2c3c40c0c54803031149031108030365500240814030412260014a210350f03a681d41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 603334910 1250 603333660 603333667
    0x10050402040b09010e090118020a0b07030507080304060507030605042f0c010207051501170a0f0c0302041a130e060c130e010909051204140118080d0e100e0d0305030a02 74
    0x60000f0f4510b5000d07006500c3d40c850034003e2050700e5100340300716880c0d13460b10300d0089000b142c00d800094654426100380304060000282c100c0c1018071403c00d03500102c0d0301060703032a240d0038030b0b01e0410054131044584c04002440d0980005251400c0e0084400e494103100040704c3c1039135400544e46100c2110640da8038031002c20449044901000d2004140c0e01b401000500005080740081b005000c206a0101192035026125140c0b07590300414a20071280d0700c00183c00c5142040d01d091000c00d40e80b41d0000c0d510914085400c15103000c440103200740a54101c414000400c188a40901110300720203950003a0b9200ca000902d14a165800030419111a40d202d903d01d590399a0107a032400d0b01c240c11110805486004c013504200d4104000c41a110041c2caa142c281070810070703d840031507208044241000411802c00c401c41c9011242880a40107031416500c40080d00540074141341c85810603503008010012402030001d03c80c0b4240c68a44000610f10402c150058804503041d802c00b9040100042e402c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 603336160 1250 603334910 603334931
    0x60819151e051b0d0501030215040e0c090109031502070303060609081504020303070506181002030f0a02070f060e07030b16050703080903040f06080403030f0c080604090c1e050a080d021005040204 86
    0x1c80c06050f82420040011a0725030440c41030059841003602c1c09481680c081c0014015030000ca1400c330382c802450100b164841e950400101c030100311a031700c0034160501641114031480351540082911500076101404920780e80c00003203031003030307030600c141e2030310380c2210550301990707450000c005402c00d000800710b0703043c0201034036443c0c2450300956450003000700d0141c01c8401e880050041030740011035020118210301d842391013010f03503100040045c001c580c3d0005159040010340b10f001000650813103c2080100302804526507148028003096034500c4400000030501c240f501108060f002040d030f580f60070410599030036110010003030801c600354017050002040c880c146404401c000d10203551540b01078200b504000e41140c1c0c03410000d0f00780341e0030808412406d54100b8095600400280e81c00502588542400c10949034950000f41d54507444860221044540769508016100708940c0000490390380c0d0f000b42e984481e80d00081c400f60f04100e9907150040e00d5603100590250001c0e0010602402e0f5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 603337410 1250 603336160 603336211
    0x70605090604170706080108010504050303060d031b0c09060504060b090603070c05031206010f1d01120915090201020c220510030f03020d030b011103090d06060819151e05 75
    0x881c1207510507440302c0130400c0080c1c0d10032125801800c501d00200b1043c1040e0712000c1c0c80c3d110003089580190807000400d401c240c86544800040071100e00840440f00e540d21304040c48003d40c3c1300308000c1c507040c20400308140c60140700f040219400381c201030345051403800034000c40d41c01c018005424415401e031034601103001400105078891025880f0100c40c83d0104c00580406660125a0100122000701842000c66000041c40340c180909100030403580220700740c00900000140104088600091290304220341d40014035444d100343c00344d5221003052400c1c0500c1405900f8950b10340b6001d0480d5041e08401d40c0d1015401180c9608042005601d0f512000b21502c1c9803481200113030300c18002c40200b036906100e41002c90400340717412400200c0c483e00da5a0f0b81d0085202e800d108030702c000e400340d04101c080d500100043c2000c4081d100c508124810043c805160040d040d07420024030001207030031105512540607940c00b282d00421030310814450000c010903005281084804198004032040071a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 603338660 1250 603337410 603337439
    0x5011e1205070c05070f060201063008090301020d05010e09030c07090507120e03030711061302131d03070b0703110f070318230a030308040201081005090106050c06060d05070605090604 81
    0x6c0000318024041ca03000c0002e08484565003e03c100603042580190202d642c214604400d10448070300241c15440e83c1040c2c41c05204942d00c1c644e1542c80021481107540040c1c024604a1b82c14a0700102c00395a4907044e01d1b102c1c82414501032a50300503200500802c19564400340c2c10203081e10300b501400700f00c0d0080300d040359031002030100958008410442c146070300401c0c0180c00081c010140800d07080c140706035402100d0300d60307000784200c03680d1100591001c2030b9480906442809200c3d032000e2500140401d84aa00c405025140c101050000980310390090041014840c078603e1080d151076048041e240282d04400b138200c04000c000130601440e000b680908202400345007881c142d0100040507108000c1c4c1e016501c007401024011170410110390001600380c8c0c41502805c00950300d940b21015080854100d40020745d0107410603001003a0560310201070f2114222102c101c841039100c038820816440c010480060695004250034030603184180042d1000400207000a41015110f0026805199 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 603339910 1250 603338660 603338669
    0x3f1d032109030c060130020310020901261b090102061303030e010c03241203032313020108280c0e130f0507051314010509030a0c05011e1205070c0507 66
    0x594440b0300c0c44199031146d0411a845020816801100319404641c54024544841d0b208550100380b811640e401440441500200324440c85501600d46038144602c440580c0e401c01d80d00303c2d01d90070b401e42407449070803618449816001030495036581c0c0300e00200c50079400c0049007010f80300c0c28005603040c4240655002d050b015140894850b50b801348403002c00340d2101038140144241401084240c070b10034841521580c0626010074003c0410603c2e0540310000d41c49410b1000003c070400c0052181007891007500c900c00da85141154a070305119004042d1490f00e812000e40c076030880c01103141d44640c49032054003414245400454402c0f40095491340c0b52108584405459030b9040945040921070340b51b100c656421b0150402481d0b05c080c0742c00c207201e409001c1da07400300b174809002c0c02c1c1c1c000c04c10340c1c1d9044e400a045540c1d002c501e151a00e00d528242c8540380c0899031810303400d000c0010410303419180e0b113041da42d000707420045202c021010b480081c180505000d00d2144030030100d081440000d0262 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 603341160 1250 603339910 603339929
    0xe180703170f12180a0b010b0c0f1203060f0d080a08040204060f06020604051e0303040f050106090204031a090601120209060d08070305180d02013f1d032109030c0601 73
    0x285004d8038140c03500041d030010110356400c510781c0b00c0006801800b000307056410a503070498480e00c40221041c9014096900d180c000c0c0305002e600307010310200314000c520810055031100c00c2010b002080c0580d81c1c04455008001c04402d0002003241c511170703814254050b00040c03012403220b40d2181d84032900700340c5412880050300400100410310504200740c075603c400807646041340403411011607071640000341c402003008181c2201c00c0c090000941003400a0300c41640c04658641da64a0440e1844541c04402c50340341c2e251900203229540d000c41da981c12210745d86510b5404d814540e0802415401c001c220350350050600101c0d801048050703000c1c0a920340300c1e03258203a95002001d4100d480c1c420310010148500d0401c0344400050760302c8100b00b1140202c1c000c0c407013001c1d440e901c8a042d0004a0080309003000d20501501d01c805112a0440d02144110501080d0036519040d040d985078070440c80501200c040c0704c01082c0c0380460041546a004e08050301340c2e803d0648154240c0d040074401c1c3d0250320034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 603342410 1250 603341160 603341197
    0x1140f0604140405090a0215070c0305060f0405010e010c050a0e0a0801050112022d0d240b120606090103110a09091a0708040f030509030c1201060e180703170f 70
    0x2a0300340b504c14560050703070300340081c00840780503800205558041400d4030285071020980004008412000364007540c4d0080079034031365180c912820024200c08590030354440d800c017044855040018403592070020003c3e030784c10f0320b0010310100590303270462118051504000d00c801d00150820080c41600c0c081c0841c4038910400003854010041d000c6070300c070b03040d855880c2d0042c048003840d040440b11170100078081e0b888085104103030500b4a00881c05000500021103403050441242c240c5900611100d0801c503000404d10a6000440341d40d480c0803691590040304060050022030030f000b10340008510000d10814805842d240b042e0151030000200710b54101384050401038000350404000e038002424501400c0515194a17548400710390b00c00042c0500c0400a242c44d4241c8080c010500c0e40c0401038800c5900c0050b03031032200d008003040d1142080403007007000844ca151500c0a040801048244000c0c1891030071512100110100c5954104690300d00300030035a0b00c085130030003810710400d900044002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 603343660 1250 603342410 603342449
    0x50406050417121303030e06040b010509070e0d02060c0a2f060a050d0b03010e0312190c09140a0302091e01060503061809070e1023060301140f0604 65
    0x20b0b4250060350082c0e140c2c4148082102c0d15601c0d640076500c0700c03d080b40240704d40b109003010740040c1420754a940260091ba000c00c0280720308040c50504803031090310382c0b00c050b560f00329040312003911850b4800d5100c10302168001c052310b00000034103050500076043d9050a0344070b0750350440b4040381c5444145241000c0d50540b46446180c034800f11030741010344603d4904100503c3c0101548074030614140d00540d51885a00182c80c00d6020180810b020401c84e070741c5d00e601c2140f44030603100c1101e0070500801c01c440c0d0410005181d01454141c0140380c1c075510803181c20104180f04100e03040c2c0c3d91540011000b240000540d03223990b64207010b51400c949e41081c102640d00f1120030020305030000418020f040050102c0e40c0c0703400e0000140781c08140142000c548a04006500380083c071b511411294900704280629002c3c01100d46003150356504002c4110769511110710514441d2503c0b4960055040c40100140c030381601761000c801c0340080102d41c181d400400007403151303006508502d42d0580e0100700d000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 603344910 1250 603343660 603343673
    0x305010f1e21050c0402190809010605060d0209030705030c0919180c0e070804110f030304030b0c31090e030702190603110720010c05010e0a03080133120504060504 72
    0x600142c070945040d07240c40c10030607098110401d419801d504200040c030008100800039402f9a0292400414003030391400200100c001035040010650310038012030a000880b450000f4140c0e01c458030280c4000d145a5680c511094402050301e003030300e078041d107400e030011400700b51100d0503c00c035101e0801e0155560801d9000c0c0001d01c0024080d80a00c5140018003012a4402e0880c2c1c1c04d20100700d07501052206548042400c0d801175500050002240300f060241c500e65500207082d509100d00120325132a209200040390032150a0101c0d111040005e10510035500c0582100622040748022030f8680602d070303800b207640c4607001552413100c4000d03460b0078810b183e8940241e803030400ca50342d481c50030407506d61160380854081c11000d13491105168092410f0745d0140d02c1e406055074100c3c0082200d101010034003511209294003c40008201c00d00100310004d1a01c007074485045080c5504040220440708035451010b104403d6003449108859600300b45000cac000c0501c11071180301c011481c9d050a25110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 603346160 1250 603344910 603344923
    0xa061d06010f15020c01020a060b04060b120603010c1e05031819030e0402040605040e061503040503070201080726041b0b0912011103070c061e0c08070305010f1e2105 73
    0x4115081703d07407070b224a40e0f07002400030201d94000000040317180700074000800604899204030303008640820f03501440340c081c0100701c5c46007170250001c1c417030009844421103203031110303101d401d00e8505055034007105e0354401d6002c0c40c1c0c0f00700c0c40e240880e0083c0d0345005052400c8400d003040000d080318001100d0806074441c011303034441c1809440030340c2446d00704200039289002d40d000d403e03281101e840c00a4030581d10500360b241229942c0e80c4c0c8130f80c0c030700701820919229840101c080c0d020812000c0811310b8588244d03007644a0722403000104c00510302c01020b00c10790342d4001d001620002c1000700400c01480201020400070010020510781d03818901013401a43c200d030031000c00c3d20742d14105031030400039003d00491790300110518000c1060011032411000a181c1074421003608440d0a100c14003595407a44100741d402e1703d603140c40341030f42d540034021010f607031003401000307001c0c0300e40881040b51a40c3c00000401850504030300d008299195816032440c0898402c80390f8081a02c001d4074000d0000a0203031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 603347410 1250 603346160 603346199
    0xc0201150b090d06141003030306060905060306190b0a02030a090e040201140a020307050102160204140606180105070b070f110724020f0610050f120a061d06010f 71
    0x1010349903441d0200011050160007002e03030041007400914000c0103c10303809000410006803000c902810300c0d0002c0c0e903011807035000840110740340c208041800c50243c81803c046802c002c0000e17146507504030602000458071080800511480c0b80041a201c4074400038040c0b01a4907401180c50780c0000303200602c49100d9a0081030900c2019081c800540d9200f04412490300b880400315940e542c0d5242d080b1b103541316840d0081c00951000c41c2c0480f400171440c0a50390b0b114001c44007030080c0e146103202841c04840a0703c0640d440320041101d800301c03c4100005199111050402d1410000e003915410340c2054200d92860010340810303240c0200d1070b0070001f54481d6400403802418954208207400c540d4040c00b40ca4142c200704040f02d400c9000b4030800100c1c20303e521803004e07602c031802c103405103401c01c40440c05003034031441e492081b00383e9034100040c28800a802c48170041c54a01c0302d0b6201c040040950659103000703c001c03030340024513212017000003a008128041c00e4004461030185401e6003033a04400c1d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 603348660 1250 603347410 603347441
    0x10b13270503070201030903023904020c0a030806030c040f0b0406080d02250b0712080711060f0703090b070203030f1006020c1201020c0f0601051206090a150b060d0c0201 75
    0xd0010100340004280c6007a03560a00300001e01c1c00c0c2c0d6003030a0f440d0403044400102d0312600e6110081610f914031603080c1c0300e9050070000c1490800070804201c164020007500c03040641c0200c032143e000c070388140c2c0c60303640000010b000d4580744885000401c0903030f0700140000200ca0344400503005541000d22946008011005c041c080140001500a41300c03440801440180e07148407601e421600c5011010000a21400d14100c0da00c001a1900c1c01b0f404030401c108101140101c40028802ca004181080300e54641e40d0291220340c0c1c602400b01c80301080544090200369aaa450400045888041500400c40c40c2c00858492030420705030200150f0061107083c41d280441070410100740c001402d00040301044030390003c3d4004507e141802401513515464962160500304000b05c480414001e059540035a80101030a40031400555924416900c2c80005c0d40184030100228003c1048053f003080c205174080b90600c0c0e01800103040f90400010007404079034402605040740d80900c0744140d003802c0940c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 603349910 1250 603348660 603348731
    0x100504030206040b090a09051e010510050d05090102042c0109110304151b030606020f010510060f020f01060608240a15051b0c12060c1902010b13 64
    0x40c041001400f66110714401007501141ca40025503415090310007a00300c0c00410041c40c5072011003030406401c0102e201c52000525000442c007400d10114482d10003520b40c031079520b4012059a0940100750042c0600d07180d550a10020850410701d4030100810f0212010014120710001e0380d100c001081a40040201843d0046903240c0d022102d0503250b2007a04041104592400c2c0c07881003001e0982040d10b040ca124559882400880d0554080030603641c055089584482141290600b00e079070a48041034406136140e070811441d88a250340110186462068440c8c0c14000000c25003955080d0b0052004911110700300800a45503a154502e45a800c803d901060991400411061200c82c010701407074402500901a4860081d021140c4145074602094012215003134072030340751400c861a50384900801c01c0d00c03100b0030340002089070055009495031440c0a180190000441c91503075144c0c4c3c03d554a5082800c000c5e610010240e04844a00901040010301c40040c80d04039000e82c1c000c5c40000d031817407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 603351160 1250 603349910 603349913
    0xf0307030906020607030203091f1d21070b0f280209042a05031308071103191220060a050103030905040207080313020609060d0c020601061106040201030f20040510050403 75
    0x34008811030581000201c41700610040c00002d0000c0c100d925402104a5804910343c601c000382e02c0c900c503301c8101c1045090b070f00081c5a802c0384078444010f8090540d03000490b1110505489403608412083d259030300c082d12412071601100d04a8003c043c0d076560200324000c1f1401c2c140108003036120104803540d1940540c4c005103000c07944031701040c0100306e80400081c011403881c40c0c0c240300e80e035040500c1948824040c54419032108075011114000e0041c00d00d06101001815105440310354022680304100c51a080100c41710151040001c000012010144610400070b10459014460411012540750704608014152180561010b0301880c4108869000704501b103003920317086180c121a00c000c00910380000f4159002ea0803010350320020005060315241c0c86030b03001a8000442e6004d440260380e0f1120240e811f2840c05102d058950410800100191321076842184250001c034800180d03109096110507000c8005541090220b0b00041c05220a2070302a035165030301e600d1031900c240b41a045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 603352410 1250 603351160 603351163
    0x70503100b04150e0102030f0f03041e0c0b03130b011202121b0d0206040510020607091a030604050a0f05090706120605010f0f23030a05071e0f020f030703090602060703020309 77
    0x4001d04000c00c0f01284c0c41c102945c1c0300380700704c500c1c045194500c0c50712084c41021401c0b103a44140c070f048032782d40504500c03540c010000d415031207082c81e0048410310f5a549010131003419a8001031041d0000c0c44101c4031400003032549542c480c0a0032180300c18078404541c0d48180b00c2941076442c03154200e584409002e5240f401030302d03c181501d00054554541c0d04505202090a600441c0c12903a0b1001580c05110441507000400301d1082545a80d0b01c5591380e62041c1200c07114040c03100c1c40e1464070003080029100d0805810403078015903c0000000d00c0b0901e21002c10845a00303584007440c503000744400300000b40d0f10042404860503980301c00c012191400300041c3c09410340e40c07080014800c010301101c4000d4043c141070706001d075064090003100410850101070a0f03008485419442e46030001044a003071190b9040451401c0030460032400511064041d2a82c404001c00c0c0c00c114807405100284508060014100e81e03403203070311480e500c20304220707001c0d0910340d00a120104140c030610410002000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 603353660 1250 603352410 603352439
    0x40302010b1e0f010903050d08060a0f0b0901050f0c060406024519080109060e061512030c0a081b06150607030e0306100501021902010e130b09070503100b04 69
    0x2c0c2107a8001d480900c07000103031103800b0a40e001810501a0200034a0100e403c83c20040c846ca0080b10358186184e2960450016002d0602603111090000c0c0003000e403030b50141008180d0f1240070007026080c110040c07885450490304a404440054022803200c101e8003205480a0509030440c0c0c0640c0c074840b180100c030500300f01400c40c0f04d50030904819a110540c0f6480c2526800d404003071503444681c0d480da15203601a101c501c50480d01c9501c1c04c403101380d500308041205405407410f64060503107280c0d41c1040154007807540300d8841542c00100064146d41c10104014407409110707480b0305840c0c1e00c04070080e41006400440354042d6030000000c104400707540904507000d0301011100aa103034a407c1c102111592170342566250903124403028400305020040d4490100c402c00d0f821116100b040300c507012074484d0003c1000f40811503150109196103051100d040f01c000b40018002022129400042c0c0c02c1d40080c0d5500d00800c1002040c4005100e21002800280c02c440343d080d481c1c40e161002d44900d004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 603354910 1250 603353660 603353719
    0x90806040b0a0b0303071a010e0106020319020c06070506040213060506030103081c0509030723070b07080c0105070504080714011d03010624030e12250606090203040302010b 76
    0x464800001d501c2d44555100454202024003240d842d6003883c80c3c0643c421400262080e03081c1406000000e00b08000d0283c2170595000d64050742c180b028580900c0e4480c200b0029040c00e5000c1c0403000010b58864030080c1a649010302c1c014501420036005000d14130952100d880e00070b60800c0800d00c6961944821241104d910030511035035041c000003131003042c1c0b0305440c00780e6102d030822043c0481d0860020140101d18003400002c2100c030400d0310090414503107140c0a00c055013248204000300c40d60000541002802025442c0c94003500403015070840d181241c10102241c0007080c14008000104034101c050401140441c540100030300000c0d0002c60200000c5420882e201d090540503242900030784010401c1d500c030380c0301421a150311480c90180d00400000000c2c58120b07140461003002403413180584920301d040d40781c46503c80440742e410540d02c0824900fa17094100c0b003800542a4481c2e60001d140002c5c0041e220b00300f615000f07003594600e540701c51044100302421200c448220240781d1800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 603356160 1250 603354910 603354923
    0x1104030c0308030a0f0606080a1a0a1401030e01021306021905030d09112d041103070c0507150e0f010f090b0a110f0c0a06080103031409010c0210030b0a050109080604 73
    0x241c0c4e40d04a040702030546103c2e000c00303e506080d40010002e401140740d45c000c590203103052240060119000c01c5600004030a0781d40501e043c038081010390711501740c3e0b031010760f81850301061681c5c1660030340d400da9000418110b000f00b10101d041054945c10710041e00100408105c540c9004190784a4603506d0240030130a140d42681c1d810f0707200802240da07140401061000c0c101003103c1c00003a901c1542c2d5401d5180d10005400b03c500e4560480c42c0c28032485440d400c0d41580d41e41140c594807001c47d480102038500302c6070b51090903404a60105c010082801c0e80c40b25564105400040b0002d10010220b80040c10b030510407120151840300741c001c09100306640980b4142d549032200c400d8100c424151403101e8040358003916900c6400744002042d4480d5003071017a03d819210956512040351886000d21001c1e0000b00701e6154106100400f4000f0489501c0500d826808040b00b03800048030610121070a00c0425640c411204280c01c20b103e84a004102c02d0800405640c9407900f42500c0300c400030f1000b0b050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 603357410 1250 603356160 603356167
    0x140304180218030f010c1209050604060902011112132102040e07050a03030c11010825021509010e2a0d020303130b0c0705031b090612011e1104030c0308 67
    0x11800e0050021542c0700401300d600b41c0b030425040314000c007518500340e40010002094540040b06a000d9a5481030748403005041030340c0c1c0c94550b48000c202c3c8a604a0421016485501c1440f0f01006a01c40a101c60b802144c0d03100c00d500080c1000c6413459001d00d01d134400130140026070118050041403441d030103490104a0080c0030121a0510b10316400c059408500c0c030740c0100078140e05c440543e580c41d01c581441c0c1d00c20381c0000015a04030004075560b00c0c280ca101c100640034100c0364598005001140d00485040402e40901c42d901d0b03240440e0755000c90307956141e400c001d8040821040a42c0100090740c90b100d02108804440b01d402c000d803220303001e8007001401c1d0303007191410022264080100011040d482d83c580071203000a90068540a0103841003580214507440c001c1344c80e5940310440e980701c010305c0350050180640b13140f00400b000c0d48540079040380558982c00380070307035002140c41c6002041940d411002d50812141c0c540f07000d60461809200070700c0040c447e88400c401350790300480003584 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 603358660 1250 603357410 603357427
    0x30b0c091927020309120c100609020d14060f190504020a030b01021005130f0201200c1005040b03010614070f081801051207030c050702040203040c031403041802 71
    0x2244004060401c0841c1808400102d80d441010440c0300c1801806072019580c1d12540b50205901042e15850426040006a007500040d1364004040715400d0b0750645205287c2804100c08544c40c6500210406800041003015108684102030004094024090f0300303060002c0452101c0e031207424020301440b46421400e0a001641030408000d0000a0065513030310707190b020040241681ca1100e0f405071040244040c806491030140138410072002612098540d0300d034540480d2401b407850180e05100300602145100070f80020402044d01c01d000050400602c1d0a090081d4500940280750410506000501c041c00f941c0007107a0458001c0d14080c00c10300212040880d491003140402422215001000307070070090075001400b08288051204030509046d0001512107120f40c1075110303030700c40181c0000380d5854080d5104122580162030319500701071030ad038040b6040384e2040d10180c84201c0e14007410020403102c0e85004211808500145040c540303005c2f11210406800d80d05003003410f401142505 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 603359910 1250 603358660 603358669
    0x105070c12030f06170d021f0c0e04020a030e240f040204060b0d090b07091518120b060405150a2d090506010e0f0102100b040906050c03010e060a030b0c09 68
    0x1603070b00f0008810008141d466201c1d415000c446444c2820030701400d605684440c1c0040b4000d10400040c10001303840c132400c07952404c02014060143d0b410311050310031035030694586101403d080748150f280001c1c0146480350070b601d06190041c03200420340640e07207050601c40308515a20f8104408084504680c4caa138030006016204982050f116488042810030034807201d40c10086800e40a4190b0011075102e41004403012000c6014440d070003204541e034440000e2160000c10148803004034104030f001c2e01c0b4200120b150307283d180c041c0c0382e0001d20414400d29150038424990070214858605441d07190034030104420491906c01c0c5001d08070210000b40b10310010300e0400d1004001d0300f01c0151704c1d980340c00d951002410195080c0c0e0008030242e00083c0d082c10040d6920b1f0840360160010322914200440e14806001e403d403805411503141c0c8a000b002410a0040c1c40c0100303000c4003116141d6041c004064030f2140000d000d58030540c1215001c2011486141c2019000505114025503602003400841c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 603361160 1250 603359910 603359921
    0x5070312020d0513110103050c030103020d0c0b0a020f07050a0f1505070b070305070f090803031501020717030c0d031514060702030d11120f0f1606020a17090105070c1203 75
    0x1100494100f80801000c1d498404d8200b0704e4034494203e84d0800d1003d903004408032031007229008200002040144098600007020703016292044120844407502c40e510b07501c088e00580405e0001d82d00c284102101a00c00f44003d00180c50140d85c0141030701d01d414190300c0094040c1c07113144925004201044180c900ca601110364464200110400500740480020002c010454402000032018440e0ba1b00a601c980700c2c0e0b0044440c007000441c203513120800343c120800d8940b04258103502c5001c9000404054010308660040c50840140d0340b10305840c1d420740d00308000f049402d03040600d03048032080e81204840800b825a101e00912407606000c81020481034401c0200c081d51501c04c840340030140c10f03031181d4582c00c400ca14a06844158211203400710550195006110f40d0000901029034501c10520140001c14100c406030044c41e5001e46490303040364460020b07803001401410f003260f003140d8580220354100c1ea10700c00821051500c60401044005402801003440b0b1502038841d400d60320a4028 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 603362410 1250 603361160 603361177
    0x120703021b0105010b07140604020117070e18040b010f03031d0f0607121d1c02010207030b07120c0903020f191d0417030714030a11160302010e010209010507031202 72
    0x208211350715004120140e40004000712000c5c2e41010304005d440782c021980501550341a160400300c3d048012070000c000703400514440400c9812200b072161a03071886104554042038403907220a0741081d0400c081c1502c0160008d0140320001042080042c0d80715556400c81c414200030b000f507680625000800365244101e0042e4424000300d060020700101482824445001d038440c1c0d1801c1c030013003201700807400d08515030a0340503140c01e07540e060f542c01c000c107a882003620510540fa1250f480380e4544000042c244d544400140e000c4d241a1111480303440340c142038880e42d041283c0b10a00d07580c0040c10329020450010300680194280c0300d241011004044c3c06003054410958038084450041080e03141c0032541030340c0ca00800c2e8920781c81c202c03004045034090221640c03100340181c0d03090518051640301800da0030071103a5a0b50182e2008800d50003600e01016100b1000241a440303080080c25282c0203103450100742d1040000c180142c0c0c02c64200d40109500d8106041181e0150100038000c2c01807442 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 603363660 1250 603362410 603362413
    0x20409050c0d0e07060917011812170f0a0e01110a020a030e180105090417040323060f0703090302030909011d0a09120302280e03070803120703021b 65
    0x140804001124080d2403103942500041195000f60081030755151140c3c881d0002243d05403005011006051201d03150409102001043d1400d0501c030107a4540c20383c80054441e100360348142140550303c400280003005417080403109030708100881c440e4103072010740504402c580c0c94010720303d01c01080d0001c84c0103040115000e41c03142c10f145c00103500c84c1200001100000c0064111050300d14101c2c4c404800c10b42c0c6801740702d44980c00e10050154060014005840a205100e010301004030500300820203036115007a0160ba91a143c2820700031000c0a089070359a41d042781b001c0110600302c40384c8407940205586408a51001181020390440c8a40500d60b9007003000c040021500092000405400f041c10114070394042c0d80d080700c0c1e482103c0c01130000030521900d80d05210141031003038014152100d03c0c80e10f541a81c840c4100359440302928108444d01152810109003003070303d401e104480c000c0070440043d51070311101c2c640100302210014282c406041d400b18021907040c03110100c00081900700300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 603364910 1250 603363660 603363671
    0x31c0902030706080106030f05010311090405030f032404090b0417040306020415020f0706020303070e040f0c02070e090a0203120d090b10051509010206040b0414070618060f1202030901020409 84
    0x10164113003401024042402c10340b10030b400003900d10600781204d802c144000921200c0d10f042000c40d102c080c00c151000e110034045070940d0b074400c0c8000c5019135601005240e00d20f900c002c0640b01141a0081c4601ca01d280c115981c0c0410011a469907000358800021640400202031940b824029904090501880481c001c41c06038040002402c1d040800d40884441081ca1a042507444400703005060050300180046080c0e24043c3d015000850b07401080405e034000316149200440f6000750000b4010703400090b040044025040301c080e003099211005d441c00e11f11540202c1c1e540d00340c18a504089c800002104401900300740c0c000035a55902240c02610b0703003085203002000501d40c1c050345104003000a510300000c03981d1000c032a800d42c0180c018002c02c1d6640d840369540c0d42c02c028829164a081f96104e2100e111042c411100a02096112640c04c03000301c0194035040116a001581800100040c403140340350061034070000c0ba051411701503601c1e40d90081c190f02901907070340090b84043c1000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 603366160 1250 603364910 603364919
    0xd020705010e010e0705010906030b01020721021e06120c071208150103090b01050f041b030606110703020f060711091603050f0c091c0b0a0510060206040302031c09020307 75
    0x42d0003828622032208003d0000c80071800c00552111070901c07501c1d001c41c40303600d0200450742c0281c02404554405005607085681c0e5a41c2c2415811160100b01100f400503038900ca04510f0202078003080079106600701c0c40900b0300c2d400860380c24482c0d110309650302521080065035604000301150989039002501c90240c21070781c100940f20b05d50941e142a41020b00310b18101c640c0d4841c0c0301d60210ba075001022868641d18150030300c00c006260002c003a41094955014580c00000c100c0181c41c071940903600000c40358035140000740070891403080d00d0502e4100e407008002682c0d40382080c2150020844400c1e0744c0d4445803825146022010a010740c01c125030408201089220100f00c02c40d50189850603c516955409070107c41d42040322001c2003c8420700035007100d0305091300b2030074000c0005560030b08251036603196580803a400326842410f1988800030804244150201c13500240410b000911541c1031540c0c1c041d480703010300c0c3c40c2d11031200098500740000c0d0065030070801c00350380c0180c1940c0e046600d6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 603367410 1250 603366160 603366163
    0x602210c0f0904390c03021c020a0b0c03010603180206041e0f0b0a0809060721020f0301090e01110406050f030c04030f0308060306090f030f0f3601080415110d020705 73
    0x40f00314044d02c000500c040405980c000c038500c3c0c00d5286d15038040c0c48181c1d0700720044982c001000c031421003140f0a40d82c80a00041d100c8440324002e07200e801100d51a0341c50008024161294250000760174003111901078010b071101010741c0e06480d141c5400382c0c1244082240d10b00e4907400c035440221000421200041c40e21100d80041c44900c410350740d6081c2558412114075a0381c80140e412000141d20441c40c0c0d042400444031240c40c0420080001d443c107020b1040300c20a07a0070a0f0088611203507180150784d107140c424401e004001c0100c1c000b05040501e04880a0200d001e95003400100e020004000340720010346004803030145510801c3c02c003088846090040c11807000302c030828000e208a0011918000c4001580800064400019407400410f41c03424000e50700405a0b20301204410712a4042803a030308055180c0403101c4004003044c031503900c01030380d0b2004440038003d41030040309000d1001003940003035050f0002c14219030104040c001c0b80c1d13083c02d0610a5061044007584013281820030443c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 603368660 1250 603367410 603367481
    0x30d05040204060909020918030d0606020f060a1b0c030320130506041406090f100f18050a060c1505240f0d2d0602210c0f0904 56
    0x99400300312261300e81c0941c600b00c4110400c00303540100c20310b0009110b10540350541148007000d405413401c0101a400700380076120503810400150300481100380c03609d90708101c1943e002141d032809010030071038848481c2800b40078400d51020400c10394000000e060290b00300c0b07800c601c1c0e0640441e40c0c40342e00711501c02300398200c5640c120850009020009032490410140c800b502d40c01c240c5641031990714010404140c3c80034950b940c10400402150366a582c80c07080c0b0384502e000a031070b0b0440ba2310200f00002c1001d001c51604114001c02c1c110103004548070148503009681103030901265241d4035042c0350180480c58080e0030502c0d41414104404407a50401c001d50840c859680f80c03103070825920400c415003681208003074210f01d0400d4010082035507119064214070021b0034081c0d1071030a904200c0c00d8641004401d44401e500052000020149d0f255007410118608800c07190b0b07800c21582c511800e2248078003c8490f48004101ea00300744e036807540042081c2038104480480b099041088454281303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 603369910 1250 603368660 603368663
    0xf04050c3106140d1b0806090f0313060f020f01050c0c160308160f0c0801090c1202010c02222a02060103080306100e060d052a0304061805030d0504 65
    0x640071044555240c1d154041c003815501c25021803096014039030244560200075690035200d140513420303081182c0381c0c480c80010142c140400034010038680105120319010b255030480c40d160303100304800100d00c04001e124200307880d801e143c00400c01d11031f07910407803801c0c004020000300c82d4a0320050250340c1c240c10004044c02455001550b50403234030700101c40c12140343e500c0060302000d0200100c031481c1e1112072084007aa0b2103000b8100d1000001e46941540d4103150700400c200e030707540d0030380c02050110a50301c03c002042071158440c20b1030040c0e40003e1810040d898001d000780c10100162101042c00764048260140d8084200484442088011940c0703220442039941404030143c1e0b40121440441c080341600c1d00542030758070759110281031081c4a60303a9480302003003103a80719000880759600f0000b40001440300c1c6c00455142410003421401e10040b003085105105a00c62071841180c40c0c2050781d911541000001404255004407001884200ca4004119000014804041017115031186020310b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 603371160 1250 603369910 603369979
    0x5160608070f050d090f0510051b210406020d1a10030c02070b07110a1d0609060d03050c1e030c070e0615031009020c072c0f04050c 58
    0x40e1141074095030020042040440020010040107203040c005030000c012083c0300d048070803040c0c1c0954850318200f20300e51704894485900d80d001e11450f020000a18606000d42d805071a00c0d10f040503950306954201c00c04102030311034506c0005800e0014681c1076481c1c0320807100c4103021041c01d28403800394040030b4494503407048140c0c2a803815094420b208048514a258000704946810016502032581140d241200d1003a42c118550304940c13174594000d4000c3c00ca500c9010500203401a0712031103401d0040919018020b039074200300442d42c850020400242d0141000c0350b0b40c0c0d07260700341281400b094003a0740001e0b41149000c071200860000c02805103000c4142540d05040d00c6180c002c0380380301c082e20215406000303d40617030300f80d490200055810100c00007454942c16500c0c040f0005a03080790780b41200f1500500300401c01e03a034150201e20302c003001c640c01d808100003c40031b040500702d0b40900442c4840d80604006410040708200c801c805240080c54140701e6115425560513800c240880c08080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 603372410 1250 603371160 603371177
    0x6030b030f0304031a0a022101080d080c0912030405060711180103020f120c03010f0c1710090c0908030309060709080609070e0a0b0d0503030402090105010c0c091107051606 76
    0x207000010080da41580c0d48060170004000406080402440340078190144186e403c00a02001c502e10141107070080600220f221000d41c5481d401904040c07a072640f00f0180803071202040f10019a50f8200e42420504441d482040116455498507501998025035040200060920240070a010b0b001d4180201290541d01c20b8844006c40750943d8000c1c480203402c040010b8880015140490210200c140f03002c041300d0305002010002420366001d10548003009550301244030405610041620032141c0c2400090000e040c8031a00c2d50700c032141d038481d20719841d44c2c0c0ca82c0d0411040c07241c1c20b1000200060300032207489041085090351540c2090310f0600220704103580c00900750303001040f200d10520302c800190140b146070507140310f40f0f070500501c902c903c0d940d200c158000a69600840032140340c005d0000715104c0c5098414464448010f0300228180716800074142d0014038480c00b4102034a406400101c1d1100d040310b002c1e4400c0c0100c45006169020f900e400003268442d00c0d021104951250799194403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 603373660 1250 603372410 603372433
    0xe1e1206061c030509010309021f0c170f1c0b0d03091401090803070212190b0f01050a0b0a0c06062102030d0509060706090c03060c1101050a1a0f1906030b03 69
    0xc150603a00b000402280041c4040e4a456001e544010300c40340c000f42401500381c50707488a00854104c404090804134950300d00c01e00c20b12041701d1138900da4000740d2607118603002c0c503c0c00f20000b40c000c4800350b941d100386101c00302c4001d11143d0449400345c01d01a0007901031080d030303150103002499540103244020303005440f4802c4641c810310156049a0f00c1d00c0143d840c0c20065002e0010305040d0f4240b4944034030822003603156040c074411511002e035000d201643e000741405031a244031200180e204603c0342a00300320034403c0800c000103c9404040314204100d602d1468a40707000540314070340c01038512070350424507040c51000081241030071501c01c909561150b410040e00359014003d112065800150034810803000402d50740c04442003d020300b0410070500d41da55510003d90b6608042e50000a6410420b404504800d0150b95002401941c051000400c200b21031150b10301c2e40003109118055449a0790680c0c1c072210b041c010301d0061081e0380e054150302d40c0400f5014048034000c060091241307151070b41 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 603374910 1250 603373660 603373699
    0x2105030a050d0b19170a02030d0f020c0f06030f07111c0e040c090b0d0e100212090309060706050a1b020120030907060819020d0b01080a020a0e1e120606 67
    0x101012107607400040280c10a003102c0d49003207044024005a100c0d81a41b4405a90300f002041080700c0305907a4901480c03401c8100030309281404c02072602070101c00c030a0a410760384120030f490b80b11104205100d525a14080102c0302074030481d5480c82c503801805413081c5082100c1c580004000741d40d031100001504030b0b10901040381c11071401640013690b04d510034080e0724501802003104210f507200c04956500702548660808103c5054a40c0c0998009520b07043c80d034120441c1a070088120000d9803c1008040c0818014424204001c03c3d81c0c0d51400042c0384410941e115001c621031010b4030001b03040c900c1c07030064001e04042d84280d5071000c0800c2100300071a00002201d1060062a000e800254500441907039440e03406071200d000e0341c3c0c681d01080440c640d1480940041c00c2510404039002d40084000740003800080d0440c100b144c0100000440389801040001035403e0942d0181d4001c4000d004805409002c0e01034907500c850755002400c0a0140050041e0040400300c0f0303a09218074100c603408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 603376160 1250 603374910 603374929
    0x180c0d05071b030e040e060a05040b070c0f0f0c080a051e0a0206040b0c01060e0408031005040e0303070807020705040e0309040c030603020904120306150807080f010f2105030a050d0b 80
    0x1203050244810400e0011348142c5615a401c03c014001107841c60b500c08503103043c00d070202ea001848aa40b442000140074040403002c0e0130a007079003031400c2e00c02c03243d0312007000041d01c598010700060444c0a802e001c201c95400c01900030320744d10068424050366481e0480e16140340040300040d080c2c211540400061000c907078400440d600915061038146071008803047ca4000e084016119580c0da4000104400001c0c492803299105800c401c4c0c0d2458608059000b845240d0030a0340036503d081035041240c0000401c13260013100500b4114240d41c1e6a1808a150288540285410030704040c01281e4240d8000007904000074200e5050091105141c01181120050310001c0d40c0006644040340102d203140d0311141801000b81303404222544ca600000c04141482041039001801c14010800e62035448030300150813002c0340400c403040d035160082030203500d2418000d507400740300d02198040c076520f14030000100a0342d10500b52510381820f00e10140c0103400400c101201e8504003101403c0341d11b8840e419 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 603377410 1250 603376160 603376187
    0x408031804230a0b0406061e0206130f11040e0d0806100801170a020a0b030114040905070b1612200d080705091801081b0a0b0a0e180c0d0507 62
    0x10241e00b51030300701200b6200d0140a0724281070781e0b00801e00c0303030f5121801001e010b4030035521a805c010400310300120520542c0c0c4403500c1190450018042071408041c00c003c0b00640000c1602070304007240c2800d220740c4904a00a03944180b5044100d03000140100c1c0c1800000f24503102c1c0556956650300f03010b09600d608800d480003030500c400603c86421010049043c030301c800170444003941c0590340464000c6095801100740588003000410254203102c0c10007000071400d035024071101100e50398080c2e0700d071101d0080111511001c101e481140c04c4144c07030312458541146076440c41070112070008d049211400381c1c25858200901500c42489000145108100360300d036200b031510fa41e038000490b91b94204001d05644425103d00c9031440c003c400d90700e14082c148c1c41001c1c101e2095444070510056828000b4240100c0c1401010071480c0340103003c0c0c0b902c41e0304a041c07001d49401600c00190000204540c400780000d04001404040301c41240a09298003000ba0300b006a030303c0d40981690b0030103103e400f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 603378660 1250 603377410 603377441
    0x106060302032e030b07091a16021212071101020d1404060f0507140705130c050f0304020111150f0703272108041a040201090303080402150408031804 66
    0x3100c034200320f00e0900745030b1800d8484544003195200c1d83d5001c00b000c419140c020010f132044000b80068001e03442c8021b0f241c0340b90b401c0f10789003030f4480c0c90403108030f011070801912030104184052800d07002440295900f031520100c150f0740b00524900019800042c1409900600c542d10046c2e031018015000304c071514140c1c043d92410b00d454071408070344200364500e0007800c0040601c0704800248080100030056100b0101070f0003514181000d00c14520380c8500da0680c5182020100c074100d0b500304003103c02e500100241c1e00c0c0d9a0383e4500040c0e924043d441c010300403d1007840b0390004031500d102029030107111100c6841401780c46074001203007a12814410200070320408200d203090102e40f0903500083c03504c00c01c16a501849142d07842110000700750368420208072100104001c00400700004094001c1c0c80508000380d0921703400003000b02c0054000101407246520100b0290341d0b507807224242480151318500d80e2981c503404155201c0e08004040f03c00700c0030100c1c11400d5485d05000f508001000c599 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 603379910 1250 603378660 603378691
    0xc0d06061d100909050705100f021209010c15062103020d05120c03070e13060501120516081807120b0f01061b020402210f010602010e0a02010c0303020d1d010606030203 74
    0x46100003040300d40012540341c071030f46c00009400c0d05c4245001e604e00029480308002d40c009000b0181c1441089180318211990800020641e0780e005915194010b0300204140da403201d00c92030030310041c8559000070505443c1e070445081003036900d00c1800d604131301c41d5007601c0758000e82003803e03900e9008400d000d00c080d400c40800652100c43e0403002d0740d480001481d120000f0480c0c100400e04041200580c20100c60705c402050205503005801c50450420a000800142c035140312a40f5141c10b5400310f020801c00e100000c21211310540d41c00f00f0302c0042e168142e440c4c0c0c03943c908010408400120040f00c1c0080b000001400489130042400d040340c806889005e8100342c4280380c0c0d09038810071081264415030034008000d03055220785048600c4820200c42c070486007003c0d1060580c0b020305030700c00021603040c400031a401031404a00a80c00c3d41d03082c203140940c1e06551070103a0203402100304070706145103030030780100d03605805500d840d5241042e0402003219a0b1145000c9041c4c2c8400c854052484280d030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 603381160 1250 603379910 603379919
    0x21020a020d020402090409110f090c190918050a0f18030f0c06180b0919380a0b010311090613030b0708060f2707020c0d06061d10 57
    0x40c00c0e0700a8a51000f0001171401e04a1000142100c001c1181500c088001609a98690401c604c1d200e4080b01c3c100e0300101c40b071500c175800002c0c0744141c942026480300031410a0700024086c2c807100d0090240d20180c02021170700c2c15940001894201c0d40d1002c1c0c5410f1407480c0340b40303028031700c81d0500902a0200325070f01284151800c1c0c1e0702014007540c40d810410f01c01304040206c2d04901c80c02065450724000b81000071a00d0804541c888400780075005282c0002c003207094a0000d5114105183d41c0c010360a184208800c41082d4454880d4800881c49036508004903903080f100c82402d40c802e04101104112095170080118121000300000010702a4200f11000003480e001001d46000020008114030f030030b0300c0b5500d0308200001500c6240220f0340400501c4110314000080c420a0b4209841c40d5030300212500401094a590300c01018005000201107640a4424046003810800280c0500340043d41854150020255886880c5444d00803071605000c2c400b440c803015028070710307519031403140e642417 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 603382410 1250 603381160 603381169
    0xa020c0f100c03110a050a32120105060909011512020c010c02060703270507080f070f0801200a0e09151e0114180a03060204032102100209041107050a21020a02 70
    0xd0281c1c6508c603140001616800c043e031085941c02c044c01c0300600722780355a10407204243e9840d0680241d88a008244205050b03070b145d61180710b0440d00245032508000c0b052440950340900f04191901e0050b0000450441c1010305401140d6480e2080d802c84480c0e0391521030480455000280c0c00781d2030703203413034009900d40901d0000142d100c601410946803170b40e9403246841e00c0c110702d04140ba10540c004000403c001c6600d03240e442c0040c07030544001d0140500004c0c000d940b00c0041c1040721540300d80418400400d84c46030040351210103020740503410f030742001c07250103000024440040b4494000302000590030090810944038490068440c9403554007109000350aa070011051444660010826145165902c540d00c200460140f80c0041c1d455045003464115401c0c1c400d003200403004501400920298001240c0d00c441c0160100140c0360b04035500054050180d40594008100010450100344080452006ca60314480c160007a003220304500c0c0348210003d9180c2c2c4e5005a00f151070301700050b042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 603383660 1250 603382410 603382427
    0xa020907031a04060e06031e15070c0203060703021917150d0501020a0e040606020a0b0604020d0f092009090c092e0303030c170a020c0f100c03110a050a 67
    0x7120780c0d00b468407401140100b0100d03812130b401106200c0200e4107001443c10140854215070f48003e800546003040c10b1121551180070002605030117001c2d01c00241114410440040b80c5540141130f905a42800742c8028040d40244082c079500650324041170f025103000703d135005004003142070300044543c4c4900c0b00b0031484a02c000d403260000c40702c201c1400003400a02c0104440041c5441d684090800c000c28401183d103140c201409661006c01904041003681c1d03440384c1e00100489026039100700d94554040a40050403180c0001d84c10000c206d402c104088010682d41c4403284007564610b08102e0030040712413000e480d80380468109c0490104a0b05100c0700d0154410700720b4407100c0e4050000c607880907014210b0203418070b1441250340300340201940340c0980380c0c035414140380417a0101462031000100b00000b81880201c50f03400180da00c002d40d0240072240e070100410381690b6049050312406805401132480c5400068a007403005648108008150350301510b9a80d503181c20001d42d88401c0d250100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 603384910 1250 603383660 603383681
    0x307090908090306100614040305061605091c02091b07060507031b0513060305010b0a0c020a050306071706040504030c0305090a170d030515010c02010807030236030a02090703 77
    0x2a041099409a40f01046041d019280c0b615001540760714012001340101500101c40c5c0322181d040000300f0100e14001040d40e08101d922056031401d048031030041e110b502c52049031607007140c1d806424021210801038070060310f90007a41d021400740e07030325840521100801c440b001d007000303418000103020902c181e0000758070491904001909007144121003465443d050030490001d000002c44c092010ba90341004030040200b03080070700440d4185418060a030041900500030021061041c02c190350f942c69685000700740203400c0d6a41e505040c200200a40e64031f403440300c8401c42d44000302e12a806c051140700d1085416a0311038000c8240c59030110344a034011100cad5503100e180c10b640401e20a20b440949443e18840000804900010800150035140000c0403840000550002c107001c69811401320714141e03509281002c81a601c60f48250001e0103410f00e9220111026006c41c0722103010b03523104080903218a4000030300da11450f41015900d6002400082d0801c08400114030100e0181c2c001d0210305 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 603386160 1250 603384910 603384923
    0xa0c06060503030d2c0d0e0d08030c25020f010809030d1a01020706030902060702061c0c0c0b09061306050c0408030c070302040608030f0307080c07051903030c0c0203070909 76
    0x781d441c800680395800000010840a0340c40034070b840c0d10005c0c820208100e96000929038440e48000d943c240c2c69840d078036a44414032184441040b90742d560f90031843c0c1c24031317030181c0066100e0811584d18130b103a4000e11000030384e005c04d01150320881c00305a21a0740703129900414a1680740405001103c007000060414a01d91000b03001c80740c1d00c04814000e07150007100b001304440d40c10304280002807621b4500d07844a803c1c1032800000070050b0b19554111a01d59405071956a42d030102d40d44521103007005854058021450b0a1413890b0b02a40a61031104081c0102c1c82c0d07114070f41301c1520b0700d5100c400c00d035052201c03101c0d82d000600008101e50841303a4484100d5607042d040640e41d178003007400c581c8942c2d038207407568010140510851400c0d100e404080c200c5007002310b0424141d65103c1c14280300284c00c90703043c404000001541c0f440b0b540211120103601102b902d003d61000316820284034112a421804641400741c3c80300c94510601070040120340007402489198642030402004045525058071403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 603387410 1250 603386160 603386171
    0x70c3c05010e01030e0d0c02010828092109031704060206040f0501060b040b04091a010f12110a0c0614060319021c050303010311060304110415170f1b060a0c06 70
    0x450009000c5000c90704000c6d11200017003d11440014402c810080600c9805000202f141003c3d050300c42d01d550101489080004a503149810710601906032101c11100102081101c00001c562042841080783d00c07a40c0307100701c09802c0d2484255140154020300005034088000036010030a0041f280041c14021000001c034581c403081030385000d80c000c2d00b0032000c41e0800103081140208900c10815060101040f0745d200311180360008001d54028140e0340200300c2186110024403400c2da001d60b041c26407020b00325580d0010120f02800e039400858003500c0e120320b0030341a0907411140c941d410340f085200501414240c0304008171303041c614800303600c10398000700301e4144039140142c1030044008060103400215103035891480d010200425440400b4002d0340b05005020001e1041c0a0b039443c0410212008a000d5000a0802e00c5a0744d060340005440328014103403e40010000c111321800c010003c007a80d00c0d01489991501c101c403924400690040006c1001411080c070a07040e149000340b10700c402060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 603388660 1250 603387410 603387431
    0x80f01021623030f1b010506010509090901111c0b09040b01150e0d051f02070201120507021f0507110703080403080f1303030801062d050f070c3c05010e0103 69
    0x40c581080451041d02d02c4000b58402c210348800d941c044c001740211000b8449441d101000030000d0141c044420f00840071100030640d4664290003180394001c402c0d144079250b4072420340030244a11000d003009020303440d00c0b401074003d040590060344101c0e00918900700e0f59180101c4409030000c209281c808200038010341d01c0c169a940f142c442e8109024100a0819601c940d4201c22000030820008070300c0c500c100050030050340c20009030b4901510818000030550b5070850305a0800511483d6021040a480940c050000280c0d11090040c1340c6a0307a41041c0400005556a8600442c00702030268001400f0803c00127911500620880c100b1861190402000500100903590140c0084002c00d0400300180811944841d03188280149406809842801c5c0400843d01a055420001c20010001446000c0c0c0440004543d90a54403910b484a00d03a519500501710380c503205500d440e992800644400c0100007040107818000340343e549a0314142c03400e0010341340c041601008505040e151000101c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 603389910 1250 603388660 603388663
    0x1170412081f0803090103062403020d0906050a05041103010218040b031c0503150105091e030106050d0501060801050606070506070e0d0828090f0608040c0e10080f01021623 76
    0x10010000540115194402c5900240694100c2d4200d020914049050300b0a007542751001c40741403c41e42d080c010396841340c94045202600781100054034150a01c414480c4c40c208a5100238490b030702840705c01111000d9402090309070712400091a0054071180c0452446207456071207807a44840080c100d640c1f0400800428640112010f15180410700100400100c3e4284403001c0c01c0070002468603e2500000c04001a8540c40e45e000c48200c22070017000c0c0e10a142c07000d42c01400031740b2b0020446a501015441e0007400303070415001d078002550802002c904c050420700103445a5950100103002c555407443d00c212200410b449449030f019690044031804500e0b0580280054a11014101c0d06d0358181e05250b010f03000c0302c0241c04100301d045d0300c0c20450030301c0c454945820b1394504c0c68601d88a407a03a0402c00c2c10024190062240d40760a0700a007d085d2120711040c0d0b00316800002500e000040742e004281c200d000312200760988800925005000424584503541412400c0e080c0300d0550b4044890340e07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 603391160 1250 603389910 603389971
    0xc08070909050a2304060f09080f03100b0c0c0a0806041e05030702091e160827010e0705031005010b160510050a0e0f060c040e0403050706050408090117041208 70
    0x2484841d49400174041800781e90b00640c000d94211440502c110f0101c0e5840404911496200880c40200400070441c2030b1b082120003030003800080542034941c0d414041d0715407503405d5078003250b2061549510026a545021511621554108010f00c41783c0440c07290580d80d100c22100300311a180003c000460040e60740d1a000d034003401910031000018440004000c000c0c103800ba008009050390703001040d64040d8002411940301441494458043c000c03440180081040c2c03440c00780e03c0354280145080d1003180011080210380c8201c0454050000102d507110448200713004003414801c04000010858020100c18102c0510a104454083c941052203d0840340b050310089023032500d901405110781d60410500c8200c90101c0701030449410105020741031881180304150000741c6101c005424507002d001520015504000704bc001d500e4a4501000d87d070f0310500042d40802c66050800c214401aa05414803136a40041c40302030b10302422138162091100241040d40b9420074900002d1642c5568104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 603392410 1250 603391160 603391211
    0xe0c1303120c060605061204080a0e130e0601050d080406030507050d0e0105011a0c1504080c03040e07090b09100e041b03020405030c0319121205090c0102010c08070909050a 76
    0x50352509682c924140c0240e550540c4000d11a06007408081f003079102e03095246802540c0064407a41c2c803040c1100c140d6003080c0f16034005a0040004c0900d568a10803904109000081c0c078040d02d072140c0e00c50342000300351403500c030024240003003e100070311103240254440d0303402045505005041035000181c000a50320904105001c40c1d44139801000402e40c0503288055059280c60810304183c15615116501c0c00c0381c1e45562841c8a00b0382c00320f0148445101200d221001c070000303599841d1740390038503039213410b005032400d0b0001417520900007000400d040541d524410010941c922401405808843c030301d1001e04a01c0d4443c0e1303201c4101c50054900c80d20702e014014141c5025842c0d91420741014200320101000500903000001545000c582ca80f10521000703610103502610306640020880c0d0f03a81c030b08060041e00602d040c05001540f0070009041034502000da00900511801540c119080743c0c054235081d010889850007841104031a802555201080340350000c2d805591245203503680800c0e81c2d9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 603393660 1250 603392410 603392417
    0x60b071401050c160c0e0f04110105030c0d0b031f06050415081e0c06030703050f0901090507170a02060a050a081003020303041202031e07080f01060e0c130312 70
    0x1510800c020900054409040a400003005285000c024060f15881454000040d52612201074030030050b0a0344440301a0480480c003545514008104a10150041c4c0d81039401080b10701c0042c00b00e62080c13089a124581d002da20301e0400306a446080082c040001a83d40e05000b14031881501c0c42e20100717804000e890408e0003245491a0005110440c0d0120070034000120340c907102403001200c00502000f00414404840d07164200142d541ea04121061070441da00200000074015887d43c035801c0b05010340d00c00c120004840e00c0b1700601a00b2190180002040d075000030108214504000e081100c01c8114001540e1602d0080da00146981e401240c00740007013800459242c0701c032a403181881d40d01c608801d6000e09801d0460b000170b56280180d21174404589145c40b101001c40d101800016400801a4505882012039060064645140d401000307041d100d100440c80755410140241021200f5840c9102800e1719081000c480c10760141440c4098080c010310004005480e0f801d12000d660342598 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 603394910 1250 603393660 603393667
    0x617071e030f0b0319031107091a090703020702010c0b06030a0f051501050a061b1703070207150e15070201140309030c010f1b0804020f0301060902030603010516140d0609060b 77
    0x701207400c40d89649000307034000403001880640c403000008100d0b1b0503081c2201c168211416031890400300303800c02480141012050350a07603504041f07140c807601301180c07401250b0b80c4030441103040380604130700a80020500b081d035a0115440207011900080b02405603409000d42d5100d1151590150404489550010b28401025041480740718050001200d0f8404401d20b8060014080b1481441380610081c80d00d1882d401c0000840700310b80c1101c040c1e00d0894071ba10740002c01a403070340c809100380b0744000c441d1a080d1203000d03c0341211080a16008100d0034000180c1017405c507042d001403004070b0500052007030b03c0c2c2e0b01100e15005984a40b60880065644540070170040d03095502d0004411078450524800e40030559407a1040200854180f42540c0d0796911400040c64804200c0f0700b5a0b011352a10700085403018198000303502c00da405600078071075a10303440a050030040c54050800700217601b800d00c450900c840300000b490306a944090110703c09441d10000001c42e506503105586101000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 603396160 1250 603394910 603394931
    0xd030905100e030714010306030c080c040506041b05090f0a120302160b1b010605130f0b030f0c0d14010c0e01021b0901090b060408010c080603160617071e03 69
    0x94140703504640740c45410660260701003541e6906501030420130403a400b2000981d40d00c01c1e400380000396000f0080c81202d541c1ea440054440b41501d407020300681c10000001d00ca030419024203021440900c8820300d044180a40c1110141c00c81c0c0450b55112046007008400742e0343d504010b0000d051244801c130b1049901e8500130785091000c2d0f1040c424403080140030400036000c03d05aa0001a81c1000e589400c01401c1c40b26005142541000d9070100900205684d0f200b000e9020312810602c17007508205040101d01099507a5260143c001c4090344114095969401d1256003c90060710402400e1500003d000445007940d20101c2c00000040c69480292125a4108980b032940200c070300d03070b415040f011f82022034440f40b0705000b0440c64030b4503840102419181c0341c2c1200d0082c181e120007008003558040e40141200001e42c1c109c4e00c2807180c42e00c4280041e032590180300465400f902c401060340342802e0b1480030300030000c0071310b0103100003080c081040310b81c80201c4500120003550f000900c0c0f02c0c20b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 603397410 1250 603396160 603396169
    0xb07080901150e0606070210030c02010c2d110a0308161e0f020f12041e0f09150314060708010f050609120718020405010311031e040309050d030905 65
    0x40c1103a01580c1440c4800c4010984481c1080c00d6481542080074255960008110746208103d8000e40040c4820485021143c0c540c0c0840141c04455000303100300700f1a501c3c201c441c0141038031116404d04010504910010100110510101d0142040ca20f04d200300c52b4028140203500f2000d44c04200b4040400110444000488082c40e030340e030800c0120b070344981040c4001121500280c10500400b02c0700e50f0320040c000c00510300c56940c4641103d40050386d4a0713844800da00b15104030359641040203210046803408142160079203183c1105070500518260f140c00150030381448402100403580d41c040b0214071082c4d02e402d24030503901c004107141d040240c3d005012240580c022014034880345000d100d99a6054115011081c0c2210641d003020782c0348a0450408859030f00c241c100030100c8407882501106078000e04102c0300262400c1000f03211035020100288800c03100d407010402601541420713243d040140b19006406450061045a1600041643c06000100039400b107440004e082245241 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 603398660 1250 603397410 603397427
    0x60e1522092f181b0d0f09150608031e0904060816080f100f020d05040f0510050c2a0709060311040e120d14011d1003020f0d0c0b04030b07 61
    0x5090b80c07007011180c000958030740358a6024099072034000f0703c0340314062401c4041054450403403006804008512404241c6401487e100804881008070007220203007901d210f1040408031042032015502d0081e4580082940c92001d0854000c0c01100b44001400c94546100740c0c0d001c0c2c0b840500a0580c0c0d200341c00c5144008216a12481103980100000d490302a4003181000050011101c00701d444a0500d6001020340035a00f611034070030340f07840c0800041c0403608044050780e60250f000d441c4001e85281e54141036980456407448100c6d010400d050005003840406400c500d45240c034051100c0b00e06001500b05803c0390b00c4918101d03158101802030024440c03900c4c00d02e0404a4082000784000b6a00588610342c103000c4a200071004600e06000c1c1940b174004158041c2000d280040360f60316070100e1140c04110300810b52030502403200085e1084200300d03994051380c0d0018039440c1c0f000307180c0d8100b020400144004942d408000d80d0006107800b40c110280018503c207034000d440750303c0c0c8814000c00c4000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 603399910 1250 603398660 603398753
    0x3071d0d02130207060204150306031406012105012406020c1206061207030b04240513080c0304170d1704030c0f060915060e152209 58
    0x664480c40d4801a5201c44945403240b40010000da210a80c6080030380c000d005a0340480c4210703190845101026502d507101c0350640303200b145071f05221089840b10302d075154400d0003400b210300306180107030b013904612400e01c0c0c1c512071164001180c0f40c81042c80e0307040109d00307141c40c0b4181c04403d41e4042c0310054052104000f03140080d40c00100d442101c289890741d83e48041d1025000b10030045010340c501c0d1060200700041e5803ca024681c1c2c5082c585803104640044121942e0140380b072a00c80c80c24003000e4000c4900582c0c41c1c1519500101c050381350b04c03c0590014040c0201031004210003d2240103e030014003a07111040c01820b48060050700161620b0400c281710240712000c1c0042100003070300b110600c04210b422118080310303c0694582000140f50130400504113403900718403004280120f0b0000820307649103140420b642d46030b0f840c01c0142c400c40030200e9607001016401580003840e120711406030702c1e04502400300b010b0881e40c80c3d6141c240c044d5064919280c580519041000301c00e043c4900820 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 603401160 1250 603399910 603399919
    0x90106050703170417030106022802030a0209070e030a03080402150f1605100614040c0e030c0d0c03082d040b2502330901020d08100b03071d 62
    0x4141d50341c00a00141c4180a0300d010218081c001c102403220114000c50a0410401c0b10740d0b403540c540a01075581c070400301340d04070800c0d0406012404201c619440c1244d040c1c1c0a0001c107e004d03600c0c0e01b00801c2243c0100b00030100004281843c40c50740d0100300480009000303442d02e10140c28a4010302005030f110700f5401c445201c0070006582c000411004a40b0600400c140c201c48050003458043d05110800d1040e050035402c0000108002080034a4112480e0f000c540801521850034015038800f10754980c00f56054208282d609101e05142c2c8401114a10441034200001d449a0b5007800c0354005004110402160781619180c0c54500b400407064038406184450a291426880e40002c2c4511041c03c1c0d40041100912100405035a0b10011401da00402c016103014540317038001e0903451400d154070003c410f81000d00b034071000d0610482c1d58062040e406490303807600746035051303442c1b10b40540449003085440a00050000b0900091809220b055440b8900b91420f0741e1000c4442100e000039a108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 603402410 1250 603401160 603401167
    0x110418050103020f1513060f030f090b06010302090613090b1008060a0302040e0309121f150506090a120818031903110a0203030d050621060c030c0d091109010605 71
    0x242c0e48604d252240c444044821003001c28595900c0201070080c02000c0d00002591540811582e0f000328060108000d10340d42000103101e200c1d840c4094458041029107410b04540120f0f9095210381c0003483d010b0710141803645044103820000001c8490f030740c0070900083c0d450881490601e0002d000103801c4030545420403c03428040c001801c0030078a8800244200c1eaa5051b1100340001841a20300006000b004250080302c0a54040e0320b0b0000b10801c50408511003100032104501d5114035810328500302c1807900e400d802c0401703200c03080c0e0080e2003081d8007411458000594451031061705407582d124018940c0c9850a180942e110b507821010424071940010f152a003280007050a41c418040d09486c100c0080f189480f13099081c40303035005019400d4040007401da01c8910726900b100d03003c0c0310156100102c00e040e441564490880b40312002d001c6400480103c0c000b4502ea0002e0340d0480c0d1000083c51030a10124140c40c104d848152040740e45100c0314043e11158908507410702c0c0100740a0500d18075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 603403660 1250 603402410 603402413
    0x905011409040809040c09120c03050d03060f05040c0207030b0712051008190c08190b06030a0c03080304020102070f0e070e010315090e03040f0609090b01090509010303030203071101110418050103 86
    0x14500640e000d04e80181e5849044445982c850344909008007009484990710300307828101400c0052482c0826601d070b1180d04c0801c2012442842110100c4001c650586a801c0c1000e0400000d0b228815240c4214401e5200100200d410901a14021031b500d07200c2d08141d0011240420075600000c0c08040c1201151100b0000c1ea200407a0a02900030503801c00c81c501c004900d0803208110007500212081d10500c54250103030b8a112f1070045400f40107a00c0c2c1241d69440e2002c1560340c580c1050000c009000940007000050703c01005140c00030b1050042e501034680b9a242c00c64485450390022008690300320521410039080110142801022319052045811000c02d0120031f407140d2042550250b0344402804000b24140290303009014010304981c20303665580c0006103844458040c1c68030807803618000f05410340c022a40003003198000742c11a0240d0b840c5032030560003900002c12020074024400958000b90100303110700350031070144502480d1200c0c00d21503070045440480840381e03240b0b840c0400500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 603404910 1250 603403660 603403673
    0x606031a010c0c0f1d01080a020d0f0c0b031905060405041718060d050106020f0d08013b010f2c0915010905010e0c0703091806050901090501140904 65
    0x246403400a003801c4021604502c0e00301e0010600c0ea000760034441c6440008904c03036601c0c1e003e814020107a460400b04a9884206844c0c4521803100004d5021a01800c00c400060300181c200d14418040c070003040d03000b030f075414892040d0341c03045814401c0224001d040c1000301100e4441c1c3c41d0040703000d031000c10842c501070b0384000314402c90b0700d121181300c0408204054a26000b030442c425010010b0941c640301d6849a0307089001e40028007844008d40204040c400324840700041001c9002d000360381300704950f4640421411502030010a40e1200740503440c4408241000d200010f03082d54400c03d403180d4640c580f412416107070607142c00411800e070500071145228650b51800c00c4d4940085425400c9685a0724032180c0742c0801041d1650300701c1c0b94040000b03405405640114102d4241c3d080d040c103e9680c199205c6800e105210b0014049404090b06100c0c4000342c0d11070784a0041c41c440001522511440007400c0001d0036401000115101c9005004800200241001e41c00c4195400700860900740e99a5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 603406160 1250 603404910 603404951
    0xf0a0c1106010902251505011203051c0b030316051608070b09010c020904051b150a08280615020a03090b0306060f0d020903060916030b0a0f05010612060603 69
    0x100e20075500880d0810502060341070341191008400b2588209a81610b003134000c4072031b05001c1c505058030b41000086c000440d0314083c1b0455525503101d918200c06a000024040c0b501d20710740b07808030358902000c0b21544041000300303a40d07010001c0d480c3e02181e4503d000c6141249489030045003a007030203010003012400190000641e0b0404044d2034071800c0700c00049480388200203005c0c2d4012800c0c0c0c188001e010000c2a00e129083c2044000004101200c1c240000306409100003241d103001004200200c901c02c015030341d041098042e074003080400440d00152648440d2140d20449a6120802c1000d17180c92a8038015000840c00501816101c1da1805450318001e0b22a030005031400100080710740d9160300450741d8400c1d00c810b6050320755103410040b00c029041240c0f003070701074402e0301c0101c1c060840c0003c805100d25400b0304040c0d04281156142840400094034845180f0785450b0031040c01a418000d803400380047e50341e40c0d00d540324901100c200b40e40141d031103a8141072a082d0b0092030031642c0601ca = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 603407410 1250 603406160 603406169
    0x40204240605070515101d011d0402010c140f0708061b03070c050109030509042d0e0a0c060810060305040309060e010e03120a0e060306060904150801050f0a0c110601 73
    0x101c2d21003c49052040c2891543d0103640001090201080f954030fa84802250546282030101000c0c000b00b80301001c0100000c4c0503442c5c5005044040d10404580310f070405503c9071040c54440c40028240c0e486219810528128007000c0e009109100841403007000700b2001020044003c1c0a54108800d04803144034200c0302021040000100080030940280c65402141f54410005c002c4400c003820001c0036a003000e2001c034456030070040c5003070340c0f01c10b400c6122810650421484460000400644005081880140146000d800000400309512581480c000e00d941c2c1c640c07903007502d800c8207602e001c2d011941044081c545094140800309a01202c00c0c4181c0b009414160510504a00169030070504141d0855042c840c24444026107520940034003170812043e12244520200a800c1100710301045030071540240c0240802c001c2484c16070000e04c809d50001003440c041750744418040c0d003950012149045030825000c01e00c044072495128100a51505140a2128400308504e05840318418441c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 603408660 1250 603407410 603407417
    0xf010302070c1a03040b060d03021e010b090405030a0807080709050f01140a18090606021b04021b060108100c08070c2d06060501080408030c21010308030402042406 72
    0x200102002206000701014058003224183c000c00c0c007116038581680215800c94441c0304410110f009400e29440e801007155054000e00700282072240c2c40d500e108140708580245640760800003005031100da0b01240220b00403009140e4030049c1c000050200d80020340f411041002800c01c018460b82d00804030b405590048070b81040c11036806004880c0c1c0350800e424160035010002d00407075141c0d0007081c0b1013881e0041081481440766210b404900b150580e00c5280c0268116121031020b880c4004502d413241c4000400050800c150003910700461082c240c0c0e82900c0e54040ba0051020441c2001007a0030b04013a07500c10b0101d80b0146c00700904c610405032065050200807115041000801500c0942184808460341000c0500303010170060038410607070a980017483c188001c00c2c15482010711a01c9150003d1144d49940c841000599075548202003100031007003540d10510446103000e035002c0c001c41c09083e0b00f0380c880c00d041c010401140d08108022100310b0750260a00383e0380c0840010030044070124107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 603409910 1250 603408660 603408667
    0x51e180601020c2d062a0a06060308070302070b0403111c1e0b010510090506220605041404060608010501030b031c05120916090e01020c0a0605150a050f010302 70
    0x2030050b440c010186061550100c407010340144500d50a49003801424101c00c0701c0d1400f02d46500601c1501d1080d100014244415410202410403a0748502540b220f0080111454050039484074022501150400c60f0814000181e25042c103604005e404040c2c010308100c203240c281755070f40d6941d210f002d9181d2203000305541d10365203901c2040c440c00360f0442c0f50862081036244085000c68549068001801c440c003c041c68001700d0b090401030f01400b43c0c003080c0d4413203100300750a14042000c16041035028002d0203903080c0c00c080c1c40540c100c000000600d00c54540c41e444504100f84c00050038407070b411807405985004404c201ea1984161070a044510a090014034842400301007030030030030078100d041c154075074040c0c160400907840740091047c7c0d07515110360041615042c4d807180d103038045c00340100d210004218003402800603070381c8014144d8000ba0001441d1600d400141f909002c1c80000c01e8440550b62000c02100039251000c100952200300d4509240a0800d000aa07000711200c07142e904059011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 603411160 1250 603409910 603409921
    0x3150604090b10180908042105010c0206070905100c0209060a09020f0a1b0f0b061305190b04060503030f0d020c06041110030903052d070c051e18 64
    0x180e010030345403500000721120034589021076903807441051140701d43c4e40900307402c0d143e07904109109000d2031940c44101580303450718210148207100b0450400080240040039540c000030424410802081d1550b0003400d06490684c00c0640004459400140280f01c4100361306107443c1d0010703282c06003503070440c0c1000194454001113807640009400c0002540d1000440c82c800840840103810852955a91030f80c100f980030a1542036110b00c454008c0a11200304503d40c0050340c40001c2c5503000802911104480c28058090340680700151035500c021882d00a0342c400840a030b004102e00302c0c100ba10300340b200301d00d020007080d039138130802243e41c501311004a00b0380d17200031407501240d0307002d14407400316456400c090034880c8200284082540c41444020408031855010740685e11074103406454031800c05203d01c4440c3d50300710406c1c04920802d100b00b0800d620145480e03020705400c41c0520400440a0700300400d119034400d983c4489140c3e07100c4100e10030007a40c3d43c039820008103c000240700500d510344 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 603412410 1250 603411160 603411169
    0x509070305010608070c152d050906011e06050306061c0930050c010e010204031212230702070812130b030f0402060a090b0301270e0607050a111903080f06031506 71
    0xc2c001204161012424071002d08c04640140b4059041801501e540b80d0f60360141804440c4c00c042000518034900300100400c50290300a95403040d005869503103000a82360b0741403010f02070003d43c2c1e0702c0f0954442003201442511000080b582a0483c50341d09000d11038800504040300c985260301c10000700196540c9856402e400400700070f0251002991203540768903004160480e007561000005000d003c291802414500555910064071404000b06003003003054900318a000600030015071080c0a8005980d140400c005545400c0c240165030320b03201281e074200c100030460b5000701c0400c01305000f8012412400c0540c1604280d0484106545000400003511420101d80c4240001c1e42c0c0440009004601340310030450382d258810342020010455a10388045840744900c0b801e003640017000141c8030501070340090000403a81d081c1801c444519181040c50600410781f001070690855a801040540100c61160000c0d04210801001d01e0070380c000c00d60728030b4443c8011007458442c00108210f51103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 603413660 1250 603412410 603412451
    0x10b12061f05030a08120903041202010c030302120403050903152710020d0c11011e0f09020406350d0c240615020102040e040605060402040509070305010608070c15 72
    0x4003d4103844094a0700c1c2488415134200e0003000b16042c440d8000a001d02e14044110b80980d594000400d905105c0c4d40c00450300020004001c5062582c04c0128000c840711100c4000e20562003580c0342d0342da410070b200a143c01c041c01d000d50280803000f6201445101e00c1030000b04ae02085c000500c5511141044000364079103990007841050441c40000d2034840b050240e040890555200d484040419048241e1242298074100110700500350590f1012041c4c0300a4101c104440480c00001c02c0060140c0c000a04607441584a01e98882c103802c0d8136040c480382420300d81d4020351040c072000740c80c800100c0f0181d103450ad01000d440401900d0324000c020003548840c11a40000d40c1c20041882220751020140100304d01e00030500c59542100c0c4000c0b860b4814021603059614000321001203840b2640c3c0c0501820000e000154010b80900001c5966120b55501602c5440256000700d2594500342c0040c06845000e850344d010400191558000f264407086240401c0c00c0b1854005043c200c8080007125040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 603414910 1250 603413660 603413669
    0x4050903070f03020706080c040e0f0702030f0f0d1103010b07060e071a070b0f0907060e1c0c090e031908060a05030d02010c1106090d1103040b070605040302010b12061f 74
    0x800b5510806165002902209a031081c1d11000d00303a480e420320208842c00395104001000b8007540c00103c612045a416a4001540340122406c0c042440c0c90354020741c00401a03102900808101d0560300102c81c003900083c1050400d060b45154100340049845105444d40a0586074640c100780140000801c0000c0082007814107541520b0301214204e10664030000e01500c0c0c4445500100f00c03410000350825004401c61001450018030708001034504404606c03d440e070000c035a4255041140c402140c28562a100340d607055034080c00e0021560807200d5826612045c0e90003403200d0945416404218103424000d8100140e40d81d5074003002500805113900301300e415010f182c40520000d43c054110403003c01164890240c07404140c04682e5484004450528a0340d220411605106001d40700302182821490700740c80c6002d45840f50707150a036100f440225403135981d51041005055080c865901440c208949803d18151011600380d0f0b40c1402920007001da0070f103441c012200a0001180c0c90080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 603416160 1250 603414910 603414923
    0x61b1201030b040b180d110102070c090902100c0b010306020f072406050d0b0103170f04080d1101200c0c04050406050f0601080f0a0b2b020406050a140405090307 71
    0x640c0c682c540703090304503415541207491601c088089004910084442462481d8050041000300014070f02156550504050713502c0710b56082105e1404200a5000040541190040030034407650700d2042c4054040da03178603030700d040140035607140c00081d26031350303150b41140d40021000d81c542c3c4900701104020301c00d0341e900822815050016118960351003030b0b8442080c0580394100301d01c650701d405016050301d0b8003800409c0c0c01c8540b0300520015414003606007542d03240c00031460800e000e0001306211a44145c11a000e0303640071a40080c0c001d544048013215540ea02c10090045605000f0740785c0350300070a144403e558810214031014014030400100052a80080c024000c07130a00b03080001c020101030b03d81760036481110001444a50141c0380c500d010f42c50f1450048515660401d10700024201c0120b01d40d4031415214440303201104140c41c55002500d104c00c1c8c0c1c0e04c44c0d826841000210f0380307a070340014080c1c3c03101c010800100450a01c018060403003602c0100d1240e0b2000141810340c4613140000f0a02c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 603417266 1106 603416160 603416197
    0xa020a02040203130506040c030c0f1202151603030603020f0f0d06020304030c1a09010b090105060403030c11120607030b0915010e03210901140705061b 67
    0x2104c001420038440b542c5260401c1003d0301d003507981185208041c018003107002c818000419928017201e100c646801d465150140030600e0103442038010070807185040040d5000c9030881c00c00c03902010a2200540f5000e0020040e80c00103074090403924403100d215080044c40783c0340c402c00003490041004a10781e2080040d6100403c11006c0000281414000030880b0841c0000e1240c030080d52519482e189840700c1c01c40e000b01510510541003140100501c4e25502d04480135280c15182c200e48135032541c18058448903034442420b40000803252509130328400800c6090181c95142d50030711500d0300280401080c65020f80d01d4034020b01681805014541c0140041641d0180240584007040c1055492404210f081c07641c19508100020700300b0f00a60344001d00c11429018035181d9420528140c65440e9030f171400030300c443d0014010040d0f00e5160011030040e2060418005600503c = true := by decide +kernel

theorem cover : BRFrame.Cov 603237410 603417266 := by
  have h0 := BRFrame.cov_init 603237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 603237410 ≤ n) (h2 : n < 603417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
