-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5397
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:44:03.454869+00:00
-- url     : https://prove2.me/submissions/c8c10abe-cbf4-4031-aed7-2fc63ed41f53

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 970503597 ≤ n < 970683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 970504847 1250 970503597 970503613
    0x70c08010c0507140a1a1519030308090703080a0503220b0402091e3603090603060112090f0204060f061403060d0b0712110c030a0c0c05030115090b090108 68
    0x4550030480941c3d0314014045c0d82d00300381d00b0b40310003140d6101c140150500d10b11900c20700030580d0344400030740c0701114242da40c0d84e00c80d109940f540710032521910000c0e003803221820010710005c00a01c034041c00341d94403010141c1c07180900c0d04014200e42040710315091f420b030381412a82000031000d002c560741a902c000c0410090303845900b4002d04c05e10107032080d5104000141111082000490310500c43c05002583c10024002c4c04100652502c4c00707043c0203038800c540145180c5a40011003158010502a0b038115a00d484060040382c00c030040e60510b0420230310704001d40040090744015074104500884090103107603201c0a000590031894840c000124440220b140c10f03040032000a107600c0700e00181102120b0000da00d032200b00c5001103441600140440d40e8604203041d05200b0325072514405c0307042504250450a8041d40c0e4454100450140100e160401c0d041007841e0340440c0141030090001c1c4001455580522619601c80c000c42c03800c1c0c1d0078071101c0a2241450380c0120f04a9545100800041d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 970506097 1250 970504847 970504853
    0x30b010e030307060b1c06020903011119261501300f020d051602060906041101181809140f03040501051b0a120e03074403070c08010c0507 61
    0x42c03d100d958150402407100314846106c0c0e80d1052007510a00a43c4050b980d41600f034101421600f40a010f00c1c18000d0501034000d070360810b014258000126402c01501d60601f00824035a59010f03c40300c0408040c0d00d008021032107200884000a8200a0302c40c944811003881000d040034810204040c0203a842080d1912481020b8104601030700da007100040c64001706114030416a01c007110307080340300d9194a84449a961341002600d90205140e0090565404d00344c0d244041ca28a56400c076042000c401c403510a0103541c0242d803002040d5651038036688441c0110000c018040480d070075242000d81055840310b2410116103154102c0203a000b0710300e41030411006440c560421800e40800d5004054045030300e100803c01030091a00070714403480c0181c1c041200401c20440081c59a001e5001b41c081023040d0751b21301030b80e04207920318013104081d140c0c00c40a48065104001500b660090302d02d1840329440c02c0c000c00204074a6003d104504101529001d440b800d07280710300260000138104102803008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 970507347 1250 970506097 970506101
    0x5040b030601180213170706080705030606090906121506100c0816050f030c030d1a0904060b030102070506040807060507080f040f0305070b040c0509060f01080c07030212030702010c030b010e03030706 88
    0x4030304c00c071495501071180c031880500b02007140c003000701d03030147c0c06001e003807044940010324258044014500f2038694038084c0085040c60140000260003401c5502c046126541c1d08403a04010007846412108002d1143d1043d0900ba201990300d1402519403085100007607100b20703100c000d4036800c00192440c0c00c4c581c0e0b400804c9450480f0050340c00780a03036082c40030241000d00080c5001e10206c00210303116a070407030442c1c040b02c0c1e003a940c0e0083c8045203840c0f030515840740c03101c8580c8a83c02c040001910400303100400d0182c07140c282c0003001801000204010000b0380f81c09020030382d000f0741040003582d5070050141c41c00c4170260344104801c201c0d000000d0006510056014407240b09290160408006645a240b443c034180e80032034850341d211509100a0500650140d400041242d40e18404500070f800a0b1148502520350940c0100001c1e403182814001c1201204c0144900a599920700d00401d00a00a00c40701403860000303410b1115039800741d845039003e070407900300040c091032501a003039a504c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 970508597 1250 970507347 970507357
    0x30f08040302090f0f0106030b1828091a01080a080307021f09111e1c0f14011415010f02120c010c03050903070f08030406090503031005040b0306011802 67
    0x1804a010000400140c84600c2001c0c043ea40325140c0c240b050801c2d100c80b2540c007505030000320805140c5401c503c6113a407400381100f4024444440644142c481c01501203480c100c2030100c000c218021120b400c600350b60b950040788118000d940d604280c0480e0380ba03040f201d000078400e21751150710540003000440c01e40e400564210100e07004862020000d0000349407500d6100740f2503044503640300d100d01c00707000c40c2110080600e0400c41d9403400741c00d010a0003060948a2011140c0142420040c403008a10940202030317000790403488101411a5500e07180d070444001029820065081c4143d82d510302c84595541e9010b403c0202102407002d543d2001164500b424166150441c486c148200d025550b101c0024001c0149078000071406000b0080058242c5101030101c01080e4800c12411000c40c04a152866120350320104880d642d4555007015809850a4807020307040703001c00400c0c00480d1441240200c112207094605110401401c0c00301615080e00b40314800e202007001c0c900064848960340141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 970509847 1250 970508597 970508603
    0x61d1f2a05160c031103060603120315030a06050127020901090b0706180c15090828050106060309020f0306040b0402100228060e03040b04090504080403150501060806040213030f 78
    0x341c40040b940c50384100d140c034a500c00d40d500b981c01d0a0f00c4690b030406011031540040142d0090020401c1c416070054580b1005001c440c1c0c0031890400510180d0781403003c208404d030480d000b80003d5131540480a401000c40341c0d18440355000e0548800400345600030344072180f6058544003c5070380341100d030807000d074444c3c101107814a5589400140c9400076071084510140145601d0100904026403551a00d10301da5821040c008403903000c00c40b4042c0010700e6460944221b40c981241c12007280c1c013807444402140010199401e00720b001c1080c4c0e6159001904841c001c8481105080c1d150702410345038003094901a02c0c01c0d0000c2e0000b000b500b05001d0010740b400c074030320481d01d81d0303218615244084012030303400d1a6100d0103810305030300780a207a006481c41d0182d150091b42c0740038602001002c280c0f042c1d10401801075180d03c0040c003031000c0d050a030340056400003102c1d105100f2114032513000344000d02a04020a68000104520b41400d109403907100c920f4074407015180703065494140c0042200c03a812 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 970511097 1250 970509847 970509877
    0x91202060d06080a1103010f020702031f062d060804050607030b0a0b0f09040c030c021e070b040801091a0709120204020903190b09060c07061d1f2a05 66
    0xb54504200040c0c44c0c60341c064140003d80000f610105802d680e8030b2001c143c0c0480c011b10440c8003607640416141e40d040701044003484c140d101c4015031000b400306944940c51010811141c0c3c2d50a024182030304940c07030f8180d01d8140320152954010b658036181034034042d10b02d40c480d01c000f07900d26000303900011000000400901205a80c1c07800b40845911007401d114400d80080b642c0032050401d405500000a00b6080a210590903d82c0003556a040d80c0c015940c41d04201001000d04c8206000c0840038290b101089640c1c1c9403510301c8503018113140f110484070715600d043c1c1e01c403c07102e13031044050161043e966a106c1c800d2510401290000c0043d01c01d07a400b6908212800b510355082050380c3d42c0c4c0351092024144142d803414000369581e8020710701401a0030540402810300560030440e80c0d001d030700400006101e8642600408201541c1881e0180ba01c58440605010740c01c490b03248029202082003031000d40000600c070f0040030340078812004540c14021580000754000c001a01c0c480100b6050713 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 970512347 1250 970511097 970511099
    0x903021608030a030e060103050303060112150f03021e010e0118080703140d440a0e0d0e0f04020f0f0d02040504060603051509101706060f01091202060d06 68
    0x20240c0040d405500c816840d80c00002d81c103031116014000c0c0501609000e01074406076240d5100d580d01c07444002c1540381000480d0041d684005010f503c201d522442c01d441e401507407a1140c180c00c1c603510040c041644642d40700c1e00d202c8400c0c1030b210098803682c401a074904c1103e452050040d50404000a1000c141c03000020700483c0980e030801070403009500600ca04025103450070445400e00e002408503c003000081c1120101070100400408003000c0e264094400f04103001d1001c400e400d00d034003a00a01c110010007440801c0385030740c100442802030303007068a15040422a09031041d02c6550210380e00040701c0f410041140c50b050303001e0a208482520107900d4001c0801424110358400d469800300307a81d022a05003c5824584078810241c0003e0600300b010342400800b803ca042c0c41e20424610902c240f50020381c090a1121610780101039016160307014035100f0310303900d859600c01c0703c0c2c0f039000307840c42d01341a004c0d50b10903400c40085492214140c24000002d4081c000264844240d0421003926514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 970513597 1250 970512347 970512373
    0x807050705061611151b0405270717041403090a03080a0e010c110904050f010905030405041a0d031112040306020304200f01032412030206100b030604090302 69
    0x9424803502c1c119000f0807880c03ca040c40070b0071010440341001111351010000b00d0880c030300300c1480c0c1e400045600740348203d08144004196148281e80086d1703002100401100440c014048000e0740070302140b07003130340750b43d5980309802c1300c50807981d10218034184429000f00c0c011071505802c00d049001d410b41603910306561400490003000f00356108442d500c1000034422000d0381d020641ca0040d80e02440d00303032104030087c0c540c203100340d60701d00400703116500880201e41045010880c02d801c58400b00000d020411050520036100e030030a10410b4000c5080810186480c15910000c2d450070303e0051500e20071041c6610108e0702080000700c041c03406e209000b001c0d200500b192015000540c45030001503503038030703261400100c2a01020400000341c041201d581c085640d404580c8480d40d9400e01c0d00148559955030070000143d07680910b9007510541300c8010640300c0c03404202c0f1860078029021100552605000c4c03d0000c100d42c428100c00719000e001090321441d054000f001510300034030403070782801c6441c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 970514847 1250 970513597 970513603
    0x80610120c0f0b03100905010f09150312050d0e0102091c0c050603190b0409170a090b0301030c0f17100c050c0105180f030412060b010c05060c0405040b030307120807050705 76
    0x14100f15401e00000c0100a00d00344800d5090700074000380700b400e0299500d0000c200390f000c105806200c160580f500e41d00c1d802200120008001076820030180036401b001e1500140c5554803901c590202c403400c01640901c2d103641402210383e40d90029006168451120340340b44030314112400c0c221707a0000030140000b00c0780d8440001c1d6014103046080c40002c42c2d101d1164004480030043c134a4020341c01c2075121800b00b03540d100050780700d0390503184144d910070b1201c1c0121000f82c100c0e007000506150110003c404e01000750102d009a070514034018040641300c04d0300d0680c3d404815203950455010f0b07107020082d5100c0c1d80144000b0452401e20a0400000041f0316080d44c1b005c940040e10310440c40b0145148003030410a0009120200c0e000e1850a4105005031005044100028009903201c695205c80d42c1d1103071407240c02c801d4100701640d211381880254685694803512901d4440ca0804d90001d0044c54084101e17222245d0219011080308011902560781c0740c07004007520148041800040d01240c800c1c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 970516097 1250 970514847 970514849
    0x30d0f02090a060206040512180d060b01030e15130f08070303140c0c03030412050c0307030203030106020c0108060f10030e0109030216090e0303011e170d09080610120c0f 75
    0x101026841d080403200b40300505400e5802102154000014000450f40208040d80d054948000699030b8500e030000c5290383d042c20400c119000310042e41c5800600c0040d03444404e000e030090340c041c0b200403012403000341e07107070139421117a204403a40002203540c42c403500d00821440341c450301602411050684844606401101d41134010079210002c140000503800800c59002e0a4440c00b10300341014444210755a0000400007840b075a02198404a15070045081d552a106100126a0340b4505031600941300d420030301c01c10000d44100c0224150b5076000320420f5120703960260007056440300b81410840e490b44030554101c00d042d5504040e0040302400e000d05400b0350b0103038000b808420703044101116245142d9019548280c0713000301c00202520b0200490307045502314071805104480100107240341102c503605c034245100c1450030003030105201040381012000c2c1500c402a200742d5a0805035280c00342191010700180040c2810300a09400c0003240000501984450600d20380b5045c81112070300f11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 970517347 1250 970516097 970516121
    0x1503110d02070c0b03090a02060702030a08072004060506120a320906060102250b1b0606040e03040614040807090e062203121b050901020c180117030d 66
    0x3540700240040c00d4808401030404c1103610345135103404060541c8400c0b440710024450300300050030b01e05640d410044a0032403a001094280d566a041c07400c00c0309426940e030300c1100c3c900a045034004600d8240700d00000c540d0041c011610703000349040c0300081080000c06040185644102088103045030003104030319242003480448085c40c110055030306810000b080c0500d15889501000b0a50360301241120050011424a2804282d00341c569650300c0020340211100c40c41c0444c083e00344c2c241e00f040b40c4e01060150000e48869894a40030311042d154003003207000c142e44c0108810807003544240d0321144c00b52102c9008908107500c42ca038007400d118490f44240b4110347c4030040034004910070b12016410000205105004035032070b00307000000081c0480040e05210144e21100041f4681c2e40100444d030100d00d56006410003030410281168001c5d600c01e03030040c41425403e61050503c007507506210132035100c3c0312980340c1c600500704060511403503c4120502003071000e00803603170300c0d0300030003190b506 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 970518597 1250 970517347 970517351
    0x106050405011205010f0b03060d060e060f0105060306030604081e070f05150f0c0f09030f060108060c040602100e010207150212060d031d030f1509060703020909011503110d 76
    0x45408001010060f40b1040d521446103004010010031190f40700d81d000700c070307a5001e1407a103030382d90440001d004940342c4070094006030801d045807054840204015201d540c5906160340642d80350f0b0b0a009090000300c503071a03090760109002c00e0100c4d4240c0c01070032460b03000c00b403451500c64400140ca2100d42140500715030807004040e4400c1085400c1c052140c100308040603808a9140a88000b03920000144c0a44242000082c2100800c46160112048551701400b21001080d80d40140c039030342d8400f403054240500440300030884041e46c1710100d800311503d5a00030100d405c01c0c1c040c034000070604c3ca0340c0c5140c43d660800490700081c0d141c0d00e0989004084040040c0c07503001d112400c902016000700124401c5004030300e07100c0000e411402010713842081d1060380c0122648140401d07c0c140156403c8034081c8644110440422a00c9200d54412000c5606481030380c0c803240400d034142d0081605040d4440762000051086200c103203800b140c4454203240200d2072009190030801e40d83d00215081c22030341d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 970519847 1250 970518597 970518599
    0x17061f030e01050f070f080c040306181424180f0d1d010504030f0c03060e030a0e06070512030c0f03012301020606060d0b060403200901120201090e07021501060504 72
    0x201c02071080a41c81501064181c40624000c8402000c0405881000b4144a01d0034042400541001c06a4000c0c1d54403020400603011240e188400003824003c0481c0c1c101c1c01d007030b05801d0594000c070b0000c0c03404002040e42d21180301074030403440303885000808090000110100c2c07031756405400c0100c002d0f42c45c0d0284c0504070b0b9414203c0c1c02019003400c03640c2c05a412071000e2142140e0f980c800215402c894001008159450461628803092900307544050000d901342170920000a802000920b0b040d1142d031141003000e400f12081c0032a80c011008068001e804c0598003c00c0894110000c1d58800c40415005191a019000700412a0001c0e002424281500c80c0100f2650b20354a4000c1d00f034140c240010b1005e840c14200240a5200340ca1810b40c85d6a100d16141c103154407271005490145a00145801c0c0c004d0740341000212101c000c405451240010400000c3c6599862081e40c100070307010781d40ca030401400c10010240da01d001500000440c170070f6218079101e141d0044031060103802d1513680c1785d0340c1ba = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 970521097 1250 970519847 970519871
    0x230415032303040611100906020a120e0304050d05150405150135010b03070e0601091d07030b010909180209070f0905100302040b040b030f1617061f03 66
    0x7490750152001e849442807540c11003034800006840c00c40365680340909481901c2c2158606144202850072100da0910310445d0030403160350042d1590305065620309000040080c108000d03500034640000040d001000141318600f0000f4009143c00e0194003140d10a60355014601c4500c0021102926240c01c00b601c0143d80c02c08803c01140108400040401c8400120f00340f0702e140000c0318200031840711031071107449402d00290030480e0710540c01006d407004a41e5030a0301c1c085804048400a0001d9601035012950020700c2c959440560012064001507543d07000c400d500074810710301c215050000c0d020002507091030b940150700740e07a060080301803c529014414040090030240441c8144103c0c25100b4004603400807e1000300c5400316011105009800700c160020312880c0c0090200c400d0005000c40c1d08000340004500402da030201e0401141e640c00c8102c0c0180200c502d650002404034034000280071442e95000380c00031402000402c40080b459224440d40714034140510200f034807804160f0403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 970522347 1250 970521097 970521113
    0x902120105040908030a09020a050a060e031216030e0109030f0807050609070602210c1203070e01020304050913050c0319060605030a030806090405070519030b1302010923041503 78
    0x1454103032030610040c03c0030340d20301c4400d000040900464560300e60a5909640d203202c03000e8028031016118400340c0d40c8440340103200c4411560000d010384240e03002001c80b1075035081207401070004050b06165466940c1e604540f8150101030041c100301d02c2030004008602542025106503204011013581e40000d40303032917400c0800042c400201d50300310800c01c01501d40c0100b00b112008410a000c400d00c00131411084c04e040c002c40039165507511440302111410500303d0015070040d1030703940740c1c0801010300c5401240c0e2031103140074040c0c225060f0000301e00d40c0d9290381003119059100e0026a0240c01c2d00c040440d01e000039a402c04503642404101c840c050080503c0307110054a010b801612002d091510080c1c403641010380343c00c0c0103145007030025091090511219025000007007280799201c0003c1c200b5111301245002c02d50b1100043c9011400081c0b004a1803a40340380c2c1070715000443c51910b480404c14040d80c5148480099042e80203099954030740c4a81005880c44441c8500000c0c25801c0c40c0c41 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 970523597 1250 970522347 970522349
    0xd020409020f03090124060f11010f0b030f1c030203041e0b010f050402070c050d0201170405060a1b140903030706060b040f05010f02151008060703240302060403062409021201 77
    0x1800d1286d0401c076040c00c0d028071701d00c00360740850400c42e4203503501080480b006c1c07d2150303035407410f54070f040d00319907445c00d02c1d070005042000300314101ca451031240c4c120151520201ca00349801c4142c296401821a8040e030040c65106c1e002c2d4203010704c0c50106000e101c00891110001726040d1000d18018050300034443e02c0d440203884203035011400c22104c1d54451701d0b452114040d55200354010b030300440071a849080400e13800c0c08015200c102ea0704261820395521803090f10403110060a1583c4104441150000d036042c901c000d50301d84500d0b50603100d50001681c0600d0180b500342c0400c2129001059503406080002c2248280c1c40382d5552409801072041507143d0407860400101485104246500051800580d048506415030f141c13154104c2c0c064019140e881500540610410008095015840644c5188042000c0400281c2c41d421586050000b400005d5004e5401e100c14004904103500061050400030203451841ca40d42001d6045d015460380b0511a01c1d0b00001d01401ca5100d81d00114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 970524847 1250 970523597 970523621
    0x90d08010b12010302061b12072f241606060609080604030302090d0611090117090a0308150a1211011b060e1f0b012a080d020409020f030901 62
    0x1401d294003182c01c0140c0d2203041c88041d2086002050050145c140744000c41001c040d0101112014000c0002d0219560000780090700c40350503080c0354a022288204410301c0c550110079040303d04504010400483e11300d10a158076106220109041215511900a08040f405081d16111610310741c5044403d40301150401d20400c0500c0e142002441000210b00c0d8000394541800b5131036103002d0007c0742c03804a0341e0402614490901c44202c0100084000501c86600b007a60b0307114041c03401c04501e4800313050944044c00c099021041000100c0e1091220a42007542640c455408150680001c3e0034808c0070b0308500a0284800714190401c640160341000d058001e080015001050503441d02c000244118083d101c00e4682c1003d00c19890140000c5511403a403458080908408400d85001802c3c4039400502181011a581074980c4c200b80b40900b0301080c01b40340b4100182c50b40c3e030720003858010800c80041140c003030001042c0030805001520030822200462034582c90f1050070207080d180725441079 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 970526097 1250 970524847 970524869
    0x408070311041b1b06090305030a0f05100501110109020d120906020c030c060c011e02030a06050631080d021f0e100e120309030405010e100507230105090d0801 70
    0x421010b40452aa408001d5260704080740c201241c1540060441840c00000b1710305407402d040d8204060300b16010358010101a5800c20070644101054170480d00c0070703520b1080180003103408201e20740c861400039101c9428a4004a034035035081c0d01060044205200c211784bd0f10700c030030780000c0e900e500003913000c0141964402080e012400402186d03e649190501a006600000d6000d0681c2825008282000904140e011101c00c8600e4594001d40058811094450425000040918124050320030802030808a060300300942102c1c00317444040c40c00404101c0b9541500090295020f011903141c14178540c000e41240081202d0b100354004413400600c0c0b8241c40c00002c614061000203054001c80683e00000483e8101c0d4400d26162824410420701300000000c10003017081004005401100c07403e0b22072500c00700c0000c08206201d154000c1680000d10103002c82000700d0000200b525030a2050400300c1c2c450200c8210450030340303100b103c494038590320240c00044126400b181480c01003c60b4030360 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 970527347 1250 970526097 970526111
    0x1202040b1e0d170c0106090b180609040f1712011d0f0a0213090b0f01051c05070504050913050d0207050a090b03030d140108191520040807031104 64
    0x3000040c1d03004004400d0142020140d5807040006031000e40104501070750031280c41d040c18110302406060940110021319040190802c0113090041c61042c04141031425103030f45590701030031321014038001002952402d9802912101040501d0708e0796903a0400325114640e42d5101d00c0015a10605c180e200c94009007481d8100f4400750000d005070750b00700181036941840c6480d2707050b4440180c01110035440010444800010b06004640d00070822544283c4418a10034a018015038150013800c44005140650345842a401c4585500440c1e0000450030020706003902e51b408140e07441d1084902c4c6400041c0003466400b400b0b010006403000511074401858041d04050203d03200840a20078a072141da29034800031079690707051080e1200282040c0701003001d400b8141100702d001d903081c4a5120305004170103c141c6182440321b081e00845801241c80d025401c00c00c0c1e0503600500030010a208806022646117041001040c014002030400e100209041c5086003001e0700754001c2081001d109600e0181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 970528597 1250 970527347 970527379
    0x161b0206160b060d0b060906010309020a0b0901033e1306170f071b1a0405012301030221010207140d0e041e050702190501050709050d02090103021909061202040b 71
    0x781c2d0312180503201f50655854440041e80903005c118802503000c405004003040030311120019020f131040036039040c0240b0340a0071000b090a9913a561300d0070b000000344406040b889209203051011070b003140300c89103085010515007a2010441e001500025030030016055049100302d819070b004548061f80c0c032183d0418044c0074129040780c00001c041c40d00c40d24078220501030841507013240b242c0785241c2e030700d501e10b807602e03040b802000d5110101068034a0030ba002001c034159a000d090680b81d02425130f2210140400d20540131850090301c0d4000c030f640801c00b480001c1c110320b28020142500c00c2c010851088100307009000780300d0b9040170b18025480c105412022111030b224805403c42100000174094803840022401d04000000c4031001c24140302861003003040561029200301e92517516682059110000c000113902c2460740070b07510914110060002d49014039500c0408510220482c0320590f8680500c020317102c0c540c3c060281514070340c443c141541014041c140d81d0a604681c43c00c081c80401d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 970529847 1250 970528597 970528613
    0x1905010602062d01051302040e041103190b280903021f020906070809010c051509072120031e060f06030616140c0c0a06020303161b0206160b060d 64
    0x441820320a1b8000b60b41c041200f01c42c2c0d41281c0141c03d801c0c072544814901800c0c401d50840680c0201d501034850b072500541c220f2882c060403220103911000c1000c068a556850301c201c3c41c0c4004807500c050703e4140c052540e0200c0c074030660403843d2017038020302500700310803a1a403818035400001540450042005034003a0350303032004a0b81100c0e40202115111103107500103c60000700c1c90300003841c0740300700c900e104201454002d0292042900c1c4003140c0d91a034990480300096000402e07002e1382c12040010003c001085004240085030308010340f2514500820300092400ca0809044100340c818154203407000c2605009140e4481c4007110f40007a80e00701440865a1240700030403103480003680401c1c04040610075240590441010303a021500c0714034001d11349031203030010380d4401e104105145c00014007d0000c4184c034891309161080400480c0346140580c0c11052108204c0b0b03c4141172124140142e640c100a030030f04007980c0342d1040241203280350005c141600500000c1c0300b203200c01c40e2640000c1c81c1c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 970531097 1250 970529847 970529849
    0x90a02090a1a0c01110304060c05042114162112050705010f020310090b03010b010503070e03030f0403080c2116080c0619180203060106081905010602062d01 69
    0x78640d0080c25081d18140b5099000718140302402c1d5007030008000044401601441c0540d000307500401504041000903141d80c031030341c4a01c03002e42c1d400032a0741c0c9400c0c0c412211000b400d800b0302400501040300b620704c0c90500c02d07086440e0151020345030051001c0c046a24019035441c407140c074070b04002c134456142c1608601d11512007408000001403c91b040120a4000ca011961251419900c9003061112108503842c1d130b000d00e8100c00e1800702645010300e0140224403420806031643c500c0e503103860000301d56812100701115014030007040000329948100c80107000841c001c42d00a83c85045c0703104a13509003240503003103040500302c54810382076812620040708c000d640c90f00b03011060110745150032030103801413510309901809003d0130040d100c909410320f0751518042000c00c1001c07002642c400003419510a00181d095032114005120007800351a045070020081303a080014406824166019560240c10a000507002442888a43e140d00342d0f000030022021042c440250220030302c140100881 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 970532347 1250 970531097 970531109
    0xf051015090603171c2d05150f01020304120b01150203040807060f030f0e06190e060f070c1506030b06060f090906040612110a08010b01090915050d030e090a02090a 72
    0x10010b000ea003520360465503420794082940061040c192000f00030390500b24000030488800501b006050160207442c49841e109a00b00c1558a290140380c0051180c220000e10036281584000c01000c10545100082c1e80e2580d031080070107000350342c10315a00d181c43c1526070344d0076015984288018403010300081560010b232034240c64161a6048041002c401410f45c100b01d41032030610b01802c8140d07412001c1810383c80f5010341e80c031200040300302080e420308540075000b250790b41d0381100700812000d8420544160b04012703075241161135902d0545810380d51403109800000c140b503a0f08010400c001d00900c049902440071209141000c9000869010302d2103890440340c8510b6881d00001d00ca9552648800094a840414003010765090b01c3d1040441c4a085001072182c5440180000c100f1414000c0c40a00344040e940c0c0c284035840c180f02d20001e0140c0140d0444001060031000c210380c0c480c0c0c20441078842c0a5a510704000300e0b1182407107105107000e0290002c040c01044880e0045d2111350100307007103c031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 970533597 1250 970532347 970532393
    0x1e080a080901180b0a0e0d0c080d02130e010806090a020603070c0f14030903071a04030b07030b13140717071209120806030708071a070f051015090603 66
    0x510301c0791590041c4000340303054404441da1a0098240311103440d056205401c1007000b08014200c10007542d0703482030780c0c2000c0c0000a5001181e00d0005081c40050310001c0c001b8100503003007000610029180c44e905420092412001100400030800c0030031045800494000c040c101100042e00030401901c4014600420300c1a41600c1004000ea03844000100503002185003407107004410a49407683c0c000c26030076101c3e1040e4080810b5104200744c01c091101c3e42a001145010300c0c40c1d40d42111708000400303d2061650310140c100144d15107030415403c01d00400d07000511b004506600402c101c50140403001041440e0b400540040d02d114606a0442002e052180c0d0500c800c81c0c084014201001000704030310340050070455100d4000194a00548049081c0e4050f0341c0c40b150300c00c0c0c0e11080e62103243c800280032549010015240f000070484140110040001c0d03004540340c69280250103040d0240c159940d00f040300c600800103024a01402d8089800e125982c074548900d6000c40c2145c3d25444004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 970534847 1250 970533597 970533601
    0x1b080306010c050f071a03090a0b0c22060f03021309020f0c2d2a040e01020c070f1a040911130308030702070608010b030a1a15071e080a08 61
    0xe8000c1c822207490b95406000c80c0d20840111021035210903131441600450500007004001c0031001c1010759125048079002003c03030000d20784840740401009882031140d48000c018a004d400402a48405003030311250002c0405d0b0310f4580300400c01140003c068007003500c18007041c0303d076801040e031700001c4402c819800b50300e8003810004010b0350711506031300e00203a2240c85042515030002841031400c2007800b50706400c80c1954182d043d030f00e85c880d10501081c4400b1000540001441c8003055018102000e00009101c0901252560890344080e5900c01940e001002c200000561210305e400a442c042840c868460aa07030445a154002c81c01094559a1601201c0b07040350741000582c1c000c850700c0c4c542e850383c0c15601c0c01d06e1002a80156030000042c02000300c003080b11030084071940d040718403044040c0d00d503689001c903100081052507600c900c000d8021101c031030295107124032509025141c5842036500c0c03051b4030b0844500d0301d106600c1103140c0a0412000d0116140c1820b98000000c0740c14405855 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 970536097 1250 970534847 970534849
    0x9100504050a0807050f03010207150c020a0818040e030f09041109060f030f0c03040c0302120709110a0306080c10180b0a0e0102160b0f1c06030f02101b080306 70
    0x600407900841d400207512400055031450015026040f50341c10b030340e0703d51035500704400e00d8240c2c400d904010300201041113461011045d181d05c1a40704103664030684041101d550790308186e40c1e1042c104942a4070071105807840c545428840d0003109210700c07000b54500300507943d2980c0e2500506050380d10850781c846842e52004110401c0783e980001c01400030380e45600fa1540c8c0d00c1d07560401d40300b603107075503080400084041006004603030146400c42c2090307048a103994204401c0401040821186020f41c6100081c11803070350181c20452041c50b60261740f5036031b41d180028100c401d07a900a010039031003804844a9500c032040c8410115030103103443c2c2d07003036506124055400e080c2c0f1351141491041c001100c0f03882c258000c0030004103180907030a0343c2e1401021600c2080e030b40da250140744002d000c03c00c5450407210614008101d0394100054250350803401140800032941c2661090b01d0145100c11040214940302001d5086031200d800c01e10070a00341ca80244118024074000248030ba98000046003803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 970537347 1250 970536097 970536107
    0x30d0f1413050406030506011a07080715140103030f0e0a0f211707021c02011e020c120709051b03070f050c03180a15020a121407120207060309080910 66
    0x10b0301c0090018000d01d0365902e00595548024410201d000c40b808408542c282c0b5a06e040301c180301d0b00620110f05002c003545545c8008800c60302440d110b559680078045a00203540704d801c0c005c500a4564039001c14080001130841b030340c0c6c14603c4c1e100d041a40380501c003140160404005441c1d0642644005508106015190001941e0068071040b1420041d2032230804020060070b00c14400e49505800e9150300810800042074403100a0100d242d0401000c03000040091103d0700501070310454900311001c0021401c2072801081c1d900c0541c20913030b024050700c40345001d100e800c4111070400d40940221258000000c1c080a4030402c104480c0c4155140b00710b03c00d5090380e15501c1e11400303a1b66187d01040c1d06050350800c0c040359502038642110001030301580c0c5602124020b401e60080d1145000f12390f510090703081404a1721080c030804254445100c04020054008a4401c0001c0158081503d1000e840c2031000d83c014130405081841e0f800010385110f0960b5110750090707a00441c441c2c0d21070001d50b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 970538597 1250 970537347 970537349
    0x7020c01030e0a1e170904060902040506181c05010506040e03090109060c0303140c0c2529030103151a0d060207060b090901020927010b0c010e01090809030d0f1413 72
    0x10884644480c45d0268003160002060345040440d400c100e000c2d65a05402e05034040c034840c07650300403070501c00030000b0b04400c0040e00c0070000c01000c81e402c03035071020490141c1508001083c3c40d6a0b544004005003800c091051483d1240c84c207000710305110190000820075440741c080d1400700580c0c10000c0301010700035000745543c0d012514562005107841101003103240c00c0200c06011620031000c100350071144441100040d40d00303850b40c01c2251420440310200d02e18548580f101c0440d1481e9941c0f00050070f92001c1c5000e988560518480d0090f4613655a090b42d141c18920106615010020b5900d555984041000c16500020144c2c48200c6070402d40000d203400601560000d10399000c02c884514194002c18881404644141a42c000500024100c4200480102e951882540184a03090070035028014030002900003042d4107003c00c9201d030945030080c608990390403000c600103045180c18800350703000603000d00d4070741f0f20f03410100c100a042125101c1a481c0c0d070080003408041598070810414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 970539847 1250 970538597 970538603
    0xc03031214070305070f03090b01091d0118170a020705010c080d15150905090a02070c180911040513060c020a05030412060c14071707150507020c01030e0a1e 69
    0x40d10910388404090003038134040b42c8040c00030300b0f0606003c0c9031900034030846803115005182c4080c3c9a082c8003282c0024004039a0703924503e80c8401c1d100c0da47e5082400784d0b40c0f148400c0c404c0e070004a0352a01c1e00031000d1002d40d007541c07844442840040030030340d800907004d42106c0c02440d1211f20020740c2d060030002d61040d0303d000c6142d5810b002c609035405800020810807100681000d5029441802c0c0848a51102d80101a0b01150034000325480b8109600501051409003000b404015550408200980c0e4085000c880340c41e107903401242070240040301001c501c03009640900440c58200080794104c80d9121004104980d81c6490f2200c00d4400c101101d4420b51100c201e03955561280c8045a4201c980c500440f105400d0061459100e44a2000900c92095a000407824803a85540e440d2200707140c2075000309850400c0c01080c02141408083c2e4141c0048810002140c0c20301352402801c240c1880d5106040c103041488060039100005100320720590415000c009140001060403600c0f181c0e04805 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 970541097 1250 970539847 970539881
    0xf02010c080c0f011b03060819050f06070e01170601020613061506110f010902130509010212070509010210060b090f04110304080c010605091003110a08010f0221040c030312 76
    0x1250104005500001d8000b05e100581c0e00c1e501142d0504a050383d5141c01040e4054004c1d04009000021100303804500b60705c11070503a10b02c0240e1b41c10061900750102d4030480084d00c0020740b2102075810002526102c2d40c06a1094185e01d04071001039610a0041c003482240200808888280101684440402091580c0c080985552100010401480110403c6160069040000a48005200b40c0c58200d03409041801600c05104011006080050944005540802c0140040e51007100300b607115a45035118243c80d003c00c180020f1801d543c001c0240708461a120080c490010484243c80741d0384002c5514202c01d007900800300300030b005001c400c2c002d68a00842400100000d04000d08144007001c0c00810400f55103070300300300b201c1d441035860a1252401a0083c03002c03c1c90b90b80002d8800c2405804015090343d41c100c228211601111008080c2e680800c44400c044a0001c189080709800013010101e41020307290600d41030100e1000806015441a0980740f0012075001420b50018407094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 970542347 1250 970541097 970541113
    0x604030518011e2307020d140304050a15020f150a0903110303040c05091312030f180b0907080307120f0909090b04060c020307030e091b040b04061103070f02010c080c 73
    0xc05020282e008a010925840042a13203284155000c1603951858009110606456460f210800ea010b4585802c0d0700c1408100720204158031680507000c010419000c0b4801c08a400480007800d001d46010514403d8001e26074800d40803000428044d00503d90b082c00044810207850262030300882c411201c1950300004c0100410310140000b07007402c441b82a102800140e9503180f5038040e0650411000340401c9882c28100700030f520a511010700b5140040d4000341e01d17241290a90b0040c0000302c7c0446610303850008100301124144005401080c0000c001c60078194165030f20340c0b1180f5400884002c000050700c0e0300d00420703c1021210020b1034805e40c2000000203a050511031490111420f982150130910308442061001007200c0f4010340540d5552140079810040100d0f00d0340140c100ca01c140d400040122008041000401c01041d2a1550307541e15481c041c00541103003501203071545260002e11150340400c10007101c0504907a82480c00d101c00104610700100540500904c1010074400ca1030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 970543597 1250 970542347 970542407
    0xc04090608030a03110f25061a030c0414040f03090b0703020a030306060503010e0a090c170610050105030609040b0705070c03120801050f0d141014010e09060403051801 74
    0x7000700441c3e50203580a0214100121466110b172081c1c1c00c50703100c0c01c4401c001c00c00501d040300104041610640d4404202c20205813a540141c0303c186110186005a103c0c000010f844c0c1004010003012055506101410002d950800d402c0f40080000d040da400b001c90900c2018031400c030001c0685003070410251130f48828200250780b0103140f88120b020900d8a000401c2a40c000c5080d24129821a88110160b0ba10004204040c2c605c1507001c542c240c85406002c110502034000110b0403180000c0108001e2400300780e4503009001c0c5501c11814040200144412a02d81c01c03810f030340c01030300522900f5054482d50011100b0f480f42d220045c0c82c08000c400013100f0410405950080024140d8a01d882643c039503003001a01c1c140200b4460380911090401d43c00500704d040784011990005003540c0c25024032800010a461461034820760155000b00113000c80074421090710f4024100e040100464036207030703801074034070700c0f80340400b11401041042181c401d81c8644c0d001d02c1c0030524852560a5140485 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 970544847 1250 970543597 970543603
    0x60a0f09090501150b1c050115110a1203090c120b0c0c070315020c0d0809191502160203060901020a020304050f120114060f04151e0b04080a15020c0a0b0c04090608 72
    0x804040c0b564a21031522001c62186401160305a270104090080750b80c0c0522020b841101c82c120001100d80140452030002c41d030740300c4600111224940f0086111040c903e0082031142c2903405c1405250301103080003022070342c1304410560000c951b48a0781da881c456001070710b1034030b80709620041105400c05004000c6030740700c8c0c0180040c8000d10085070b80c00403110320207a54281b01220390311070589c0710041c0110030b04400704c01c000740940140e0002043c1c00501823003405a81c40383d4805124040356120390703821401c0030041158401440c1000f14201061110002d469100318440c40b44210003454400c03501d569068811f0400c4e08070310000b0441ca8404d0740303184002110494019108000d100501141c0382001c0c065401c10000f61920164170608143c0e1021a600014000140c4160b10000c0460034070307602c200410242c80a1001000d480d05546844002e45074200d103000708590042c01400c550440018008199950096280885954044405101e40070f07aa100b4a0354a003420000104d0705404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 970546097 1250 970544847 970544857
    0x305061b0c071d01090e0c21011d16030f0b0c0423030105010b0f1b0304150315062f010e03161101021c0c170307021005060a0f09090501150b 62
    0x6001c1c00f4000c1d0b80c1c1c41c02c0070021180254114001600400340b021910305c0c20741c2c24121030740100030210240e44110200503085403801c0c9801810102080e8008942e2001004000800141a503940488a09550742c440c1c3e40703030410000510f8134001e00c0210b01251804c2007910081e011040d0001120180b60802c800707441c400441d2903009500e405d00109090075400101d0340c1003980c3c0000d05113402e10315840a150500102001000c0380800c1c400464002e0103143c02054801590f94082118501801d0003021400d05038001700901411000c02c1240780c460b070ba04042c1600e407003140c010080f0b01400c4014003600000c600440d02c0c0c0030000e80705004d07907410081c500d00b1900815401031000c0c1c14000699450440c40185c081d4a40002c000c2412139204030443c400d4248507044110100a10031071518071904241c0310700d400341c4c03c00100c5241081b079a05c40e240d40840700703e0740300307540c1c501c0e203660700321a40c17014040c4c1800c070b90301d9200800c02d2100c00d40207a1100884075110b081807603607a6042031120341207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 970547347 1250 970546097 970546139
    0x100f0902090a0213050609030a020603040203120c0f0610030f0b0402040908340803060d170403080c0f150a091b0e180a050d0e370503070305061b0c07 66
    0xf00c2001c05d113404c06405981c030000700a00140b80103810b035000c002094000034012a41441042a20812424a80040c100854486006001501440c1065800c18000030706800811038801401c2000c60503144400e8102d076004401000e03144c90b039002150142640a01c003400300300300010503a1009032021082c51028141a0380002e540c05200804075a99040c80c101400c3e0a00038404590f079403805050a018151081805151a060b001e000c900b1035041644145c9030103d0214060325a004180302880102e01040040c0c08032050340c0040300031041c2d006d014240740390b54a4441070304001c0c08203210f002552108614030b0340c443d80d407115440d0041c021944483c41400f8161881140304000502c0c0400960207409000b001d1407503002120711031086882c280d44940048203001c803030b640c0c2100c01c5107101c5442c0701c1481300c0c58000141c5d40c00061180c3c00345020380e10464040003c036001141c402d4020021125480f4000c0301d40000c51000d00410035040d815024080d4005440741c00f80245408030b0340 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 970548597 1250 970547347 970547377
    0x11401090807030b0a0e0a051014061008040b07120603141203010f050f01210e06070c081c0b091509060d0f0204050c220e090708100f0902090a02 64
    0x784800d0450740781c03620340c400100061031640100780e0403034584d00120851001d07070045070f02e41c82c0305840c1c82e8a404800c3c400c42c00100d61321b0a019801c01880110b0071390000e010f0381c0324034881c0c450840041030f6540003403000c3c20521403e00400d54543c4111500000040c1200c0c040c40019283d040560303d01040340076201d04d502c94540b4005215100409690489039511030040c5101c0c509402c0c041850300386030340b00341001040640c0c40003004811024901000c4055000906441d02ca54420310b440000b40c104010f1281c00440b07030b00010f5500084500c1d8200e14490b4005100b80b82400380b010741100c025a60b0b100300c900c800c000100c05101c10081082d0022195190b60b500da5805201d0304800103a805800310030031600342030240c182a0405034001040007449483d140704420900441d03010b401420b10030101d0502d003088400c44141d100707504500110f003d000d0461404a045a03070303c0f200804068001d84560481d02482550780c0081d48050b00034120600394600554050001d5101c580d41c0b80c0520 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 970549847 1250 970548597 970548599
    0x20103060b07240c09090906090213020a11121b07080d051201061d1c140c01020f1c0c050f0601060c02041805030406030f0207020d1b092a051201140109 67
    0x2081c0d9001d0142c1010b500d845d5908000e00b0b141e44680544503031141910179075120350900300107132561403041d8019600007400588400035480000c010221002c80080d050313014801c181d0386243c402d4121040c2036200000004510703000c0140500f03181c0d5030361010040e400340350760101c01d454101c2c0042180544c805175581c8141e80b42c40040e5066403486005400d00b00032460300d40061f05011600d007200c621b51144402225a42d503603101014071511300700b000711303401909c0301c2c41b00c9507010850080e0890060014102d40051461400c1600c03840001090400c540c01c1201c0c1e00380001800000d1141c0f21100a80f40310f980c5584000d00801c040b200100e00883c81c1c59603416820b010501400d44032640f2001541c40c203031410b081140903106030084200025402c0000da00107a4502c8046000140b03e44184420180307014038000c400280360b404203031500c0c10704400031903040b08845076080907071585244515040e020141105c5902640440d02071040c407480c0085540e040030f40d15410040c0003603070351401007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 970551097 1250 970549847 970549913
    0xa0302070c0f1d1312020c030c060906160f06140609010e091e010f140a050105030d080c1323130e0c0d06020c03161a060607020d020103060b07 63
    0x118424891601d43c0240c10000d000c505450441407074001c803001c040e20b40d01c0c110540303540803800c580349400307405a8041e03913200180c0d05080c4100b207602541116414101200040440c0044c0700c1d8418600c200803006100c0410044e1041c00618010781004081241040003010103000b540161007091260301e440c00001801901a1349051254200e02c0150007140954100b54564010007860002155265005005042031601c10103082c0180d0300c0c604803040c10031006000131164182c0200e4006d400c141c0c1d0044103aa008044150010040c40690b42d27500c6014008014408003604110401c0310036503640d01c0300b500d07102c1e540030203484101c5179003143e40c461050700b400b00c9080504250941d0000000e4820b41d26082035074031942400f40c200035240c40d04105207242990f00006100c0c81e0303400c41002c55003c0c8004403030960580740e100c0c0d070608260b0410700c00041079400351a000904c90802a1300c00300859129130015001850488100c0da240c110911b00030141841d9200c2420314981e11040300c10074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 970552347 1250 970551097 970551119
    0x1305040b0a18050603011a03030a0e0604170606040501080304030c0b07081603030207021206060f01080a0f02040e010602011b080609061801080a03110601120b090129030115051f0c06020a0302070c 86
    0xf94007c0207000714035040034050241c0d0030b000b10342c0000754081c006000014440303010140903d41030b1008000350841c0d281410400007201d206806c0040a64400e200c14000070302602d1550050310a413008564a1305620300c0c02280310310a601a1038900d40c8006695400c15406402804090b0710884003028507000c08004036a03140c008854050340145089208002940540c51841d0042e951350701c081070080c0c050715000b0681e0b0180d880300405520110041095a9085c4201404204440070701c841100e003c22000748010380180c2400d02c01c0015a002c18210358481c020034014007082c01c1d000a0f990382d0f40440310b4072034000740b200380c0109042d6598624000c001141e054140d40000c03500c05542c4020352941c4881001c0104841665903803210010100c030031001c40e0b4610b82c14a81464200369000605050070340707100b40c0140c2403841c40c10f0b005001070f648410700d00d4095850941500303110103680500b105c1040da02c100c060880c603c00141c21144079499001040d00390300684140c40b609a130f800720380d12 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 970553597 1250 970552347 970552391
    0x4060b091c050c010f0315031124090f0f0907180518010608040f0501150501110c030d0e040213182a0804240507030c03021305040b0a1805060301 64
    0x40790f03800c9615a142e4039130044501006009152500060494451541d8202080141c2055403060042d100411281c40d004d5400700c5681252001c0483c2c1130740c8031002261602410f600540306d035828422070b40c03090b126690030b030190b05e400401d00c000c43e04103140f019101c10084d000f04040f03140c1280c8040380340d080c020881e80c009109840b100481e0784c070b011300445810801400c100c43d210301110400000c65024000c200b512242c545020303d00c030346008005003043e01c01c2001481d507a004011504c43d41d5401180320141d6644504004500302c425400040007031048801e450821194094041800c4c20030394803034400c004620303500304280c0603000c04817100c400c0301d4001181909465404948140c0c030501c01141c01c188188070740d0084c0317101c43d00d0601c540c05060307003031208256803507041100f0135515005529103185203003021850f0100d5916450007840090003428040e5844403101c06880d10741c1e0200070018015034414040c10302c20401d80070b02825007514064403d43c00c09881070340e4030700c1c8192104 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 970554847 1250 970553597 970553603
    0x80d05071e18030602092806022817041a09130b03032b0e0f07140a061d0303031609080606090f060f1f02150105032a04060b091c 57
    0x3115600c3c1d50783e03900207940280042134100c060f800014010b80d140291143c14070b04a0340303000d58900e0501070028a0144248411207018444100803c1c4804040100d41c0f61980c2102500b115051000d20600d0705204d03a44c480040c254501081903c0c000031003000d000c9054040700d499960b6410b0070484015101080d8803154550010820181c049003260040c01c904982034500c031721644110b20154041702c6030151102c40759080000f03200c491110034001c4c88090a0341e081d241200d90003c03c0402e60a1245001d040d05029011315002c05030625906a0160700000904a036982d03d0140424000140700c54041c0700448d580b800c010031050401b00c0e1607841081d01031b2115110317540b82c005031813501c80050006900980f2007420b034940c036110718060403211140a1781e224000942c041000b45410300382c81140050844290040c8078960b03000c60482c08440e604082544075445001e80140c54185410038035a00038542040018505941c001034144050121908002c050009800c003104a1451f1401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 970556097 1250 970554847 970554887
    0x100806090d0525050706120f0908180a05090103030e091501120b011803030306080712120c021504030b0a0605010807021002131d010e0705070c030f080d05071e 70
    0x150110141104082064500300c180e5080b801e1078581300c0a08001e00d540101d0f0008a15003404080d610243c080e40c2183c00c10b07804100540311031502d83ca9078502a000358901d441c801c032000444c440d81c0b10881c0c9405818001c00e6000656541d203070181240250350640d0303010340510340c0015185804030005a03081c04040c1c4401c1083c00e0128504001001c42865881c1441912000d0032140070304803845001451280d203002862505080b446440c0c40065481401ea01c2d94000032400020503415141400100790300f072117204071070144002182103500b5060442881004a0008140054046028010001c2e14820401c503500c5100440b0085400c07aa084003503409013808840d040003a81c020500580d05201c055405074442c4100d0419258a146100742881d4100c010b10110000701c0c1029080b003000d003091072030214541c0d05c2c0d4a440703a86106c06003a11060711814003e008050702111507014000500301700e00e2038810303409003031a40d02060021042c90407048143d40e160180d0005d6601206004203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 970557347 1250 970556097 970556107
    0x1150314151314150f0f0303072006160b0f010308092103040909110405040201090e04240903020d0e21010204030519120305190506040b0603100806090d05 68
    0x922507900085400c9403181941c80c3d407510300000501d15100d020700007140d20072107001e556004001a05064043c180e110705003d0080302000d030380020444182c1644064013068010003011502c620104540d5800d40000000810a8102c3c2c1013001e20904e841c41821043c40540300c19620641c0d03d00240001809001d0401010180c1e1800e568241e1204400d480d00071030b40c0c40e030110414195085980540701d00780d02c0e20708101c1009980c0c18000185141510100081e24280e00000e007d00d046104410188030940301080c240030070044454441130b8a05516144850011940c0d401410050000e40040c024030047e48441d61154007026050040200442100032210008491000100c070102d2519035003000000001102800b00700907803040011062100006814203003484000707407600c1001c040c500010022050b0b040400b076454850b4418000545645810108006010700e0012550196001c0704005010340b80d0300d440001c0d82c1010302510400e032030381d4403200d559a40391b00b4500040742042c85 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 970558597 1250 970557347 970557349
    0x305010c0f080a0501361a01020123160203040b0f1c0614130e15040c0e06060a12020d0f050714030603190c030c0308130b1309230115031415 62
    0x100038805400491004a003c01d0000d0f5074011a00c0c0c181c540440c640d458107200c0419078081c0b0450300d020001461003040b2f4031490a6118107a04010204841400c245954560043c0308000340c402402050019544c3ca51100c80c0c000c034503401c4024214981024a400e050003e031b2940a4131085a500c40c05d01e05501c000b03841004442e10451441035052540c8201c0c1c4215900d0800c0300a03500d032942900b0480a0600b82060000c201c0950031009200b003000e01800060744600701210f1724a1014034040f1072103504080600082d2107031a010100050411042d02031000083d800107000358a592540316110201c501500f2031030104881c130691642140c8071800d403040555600420540c426500c112182c3d0301da1b0784100c500c4100d13400594128070b021a100e100007081d2032851020302403040c0803c0c07c048441c42c01a5848141d40a040c02164440d080d490221350350351040c0c070b42200108244411036864200710151010320014080001c1d00305014413400340041042503001d03007020b154510700701700104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 970559847 1250 970558597 970558649
    0x13060f0909180f060f140c1c06090906060f0f0f0306020304050c090403081b03190c02010b04020c0609011a06030103240e161e090e070305010c0f080a0501 68
    0x28030140d510084541d03010005000c3c10100e1800d01d102d41c04c0061031045885c610300031201303140c2d0004040c0c03040105119036000c491055a17941d06455548140c5080c031500b0b0100038107820303442480080d0424950a0401015402c40c50545003070f08000811941c0c1ca0120140482c1a4803501e040c448400034244085000c64000710f0380640180100c071040f03c0b450021801400c0200d03410f0b80040c42c1d90041c000b6200b0088d800c1a1101001e81103242035040107000c101151180050484a8950303070900f00341514001e411000c07010000600454a61007444951921090201c441014075407a105004e500c00308a45150b480c19480900300d6410f6a0a42d90f400d0040c55413001007103503080e4180311041100c50b0602408185070700c408058081074480040c0060849040c5d005001e00140ca1950411304200c4154100111200d07134101041070014442c03001d05003c2c040d0000b82413942044613512100786c1003010740b0001c001607a1921003035602c02062108441081c0590281c6001d400c201d0340402d03181e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 970561097 1250 970559847 970559861
    0xa170f16020a0f270603030e010809010b10090e01091a1003060506030c0409051e06010c021503010906080601060207180902180907210b0c07080f04080313060f0909 72
    0x82e000207186919100340c0c4a6100807580075040f011816910140302e403900303612950303070644983c50903c0341d03e0959502626074054080002e0420541c48001603e103082504a80034091000e00988850940800c0040c600409801611039031a4207000010301c4a80d58401e1703c040f81f1440041c46201d0341c00301c3c00c004c02c501d00402c0ca00100354440101182941d2500c00450040b90112211aa078915001c036500580318014004490600c0300e0031108600301c00c2d0f28155034031810918041e038880040d0301c001414040002000c2e02204c4000c80003080440059002905481120044402c00d0382c2c1c8100480c5d40b821640141c1c0118885605648102051a0403080407644010315400f005c03600c61409151484085441c05841e9104100c100140032513011200f0080308a01d484080c8003190b42c0f544081d204000e0440c4a240c04001034490901c041c660540b0b41a203485098251f450b40c2ea401000d5a035041060b00c20070700c421010b0001f40c2c86000d07122400010800d40c803036800140c5044a40f40c014029 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 970562347 1250 970561097 970561099
    0x9192306041a0c0c0d020a0b1e0402040b061606060e13050703110409051504020a2331051006032f090d030521010609140a0f080a170f1602 61
    0x2c1440007240700c06050000c4000911729600030304900b43e0f60300344481d0142025001080301c40b41e080d404d800e003030340c80b901e241d610a40564001c83c1c4007401d40040b8296110305c1d046040d0240080627160100f29050f08524125101e0300241c00381521a1000322507031040d040c80080103a4402141000080c00c4e41d041c1c0c18141d00d0061002944000750f4417032038105450f6910707101001c0043c80401c01149001401c101c0034100c04450821710307030000c4010780c80584080c80381d548210a4448180c03803100c08000c041d204080340505200b000f0f40b0780e81c00040681400da8111803110000840401c07400d2080c400d0302d00c402401c00d07007002485110040840b8a03000d55174413a840400401950202c0d840b1131b411000d880307200350b490350381e1150310804c05c4c03040345030100110601207188070040011170390007445801a1502100c5001d004075210001445041955005c0003131038500704d00000340c546010400e9115a030141c1c809040341118001040e0840c03082d81e041c00e5854205018801c036004400302c2c16840284 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 970563597 1250 970562347 970562371
    0x4140708071b05010207300806150c0604200f1c050610050108100302060a05130f06050403020f0306100b0a020307051605150301050108060103020309192306041a 71
    0x811941c0b003412041d0048410b5036a0380d000502e140401c80801008032002c000140301101240302c03040108003040900798068104142e580200c1e803142d03200c034034400355070107445101a80d0b00e0750b02c0d040d50340320103040f034094400305032210007078248490303105079218540c80040c2036290380d1440c5001c001c100780c040440e0014400e5107032644800a08101302e101c1c01200b04952220040e880c00000402d0301800800001c14845009001c000503160307031044e2550303600b850412039103407051044084464041603000350002e05032030740d0020300c11741c0003070081c405d980c02a20038425a04590003071550744e82d010707903240c01c60040a040421024032480d024000118251064a2030100705031502072a040550f0818090030080304000c2186140000c8450082a20b0760300480c1150b16103c0042c0134903400a0590303050640002c00108401c000f807054512082d002d418a10001050b810300d6501c0d401510728003003000c0d00503500c2d281425400210584181d0b400140e0440c3c10001000c1c2c02c019040140c40850104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 970564847 1250 970563597 970563617
    0xb04030219050102180f0d170f040b070314190f0315080c01020c0a0b030a09170c070f05040e2508071e0603060602030a2102070b01050405060414070807 67
    0x481000e0030405403400b400015840b043d0380b4882c481100f43c003c02051052001141c1d05d105a1a074204c1801c217560016541d0307a030202a0300d4030701864450300311000360441c000140814840c50f00d40250020501a5503a22845640500c108a081c030603c0781d4100341110760031907050110b100e92210501440903240108005031260440001544181c009141e1b0750040c040c0c4c522039503410400d200c074200d4205e402040040c81e2034540121840081e02c0800d10985820702081803008182080d900317100310f8250360f40d450382c0c0185942d0300c0f0300700d5000f6032414010711000040c503440c003805501c5491058402420b680500081c1c51580d1074a101e40c4850620b4201100190108041c8180c50041110500e03405103003007a04090b0f56500c60b55041030703042c903281800504c049a40007080e50006144c900702140d600100411000e00c00d84002d4665010034000100e404c20441c4004c0b8583c100d550690b01031215032075243c10841030799070780056000745e411a40b0006504911440c940350300241503091072942c803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 970566097 1250 970564847 970564873
    0x302070504020f0d0c0f0f0e060403152405010509010815090c032e21050d05250f0b040602070506070509090601171b0c03040f0f08070609030b040302 66
    0x1c1c0c0c100210f010800000820107452940650040c2010740842e40340000c1c00b0001907001130464a000c2c000c0204004e0b400d0307030381c2c05c0e6030b20388400702c50180d03800c1403051055031103400c01c82020700130850b0200250044110b001512961965064040e62416103445060041c51401101c1d091002021652102c2c2040d80d000c02c2c41c0c40d8444018060b5046242c0c03255603107040d41d29550115000c40907c4c0401c190002040745134030004024005540744a52001c4100c0780b03215806070340b070800010152142c004c184060401e940c1041c020184500d02543c0d0310710f202c1d0718048102c049200080040c0048030101c0c07203140002d0388520f500e13620a101d0480113041810076213415161440846519004c683c00081251089c40c01a4100e81c0c030a00c2440d10300029005017100b5850311030b006e40904648c80d04444034021000503102903610386460002182d484a54031140301810114500c1a503100700c08540300400c1c5142d004c03c2c04801d1f10031030788401a1141c6140d80e94280301c040200140e0460007000410112 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 970567347 1250 970566097 970566101
    0x7080618120a0f021e03040b0c010905010516180b0307030c0207030c03030f03050a2307020106050d0c050901080d020a020d060b030627030405130203041b08161a0904090302070504 79
    0x104021036584011603840c800e800391401d5640e0200d500c940400501c05d0200010000803541990303900b42002d5110004061100d0241c04440c1000307050f035003000100014000c4200c45d81004061319900c40719000f05552043c0a02e0700c9a002e0745c913100f0b408000080e8580e002c0d03080000c0c0c2a000c1c2c411240300707503501d4991400c1d9140c01d4108400050600036907a01c1150705000b0303550804101841044120005034000b6880300d9074900c0e019440300090000b9103294000e601070401004041e0114602100340e02c0c00380c1d103100140c095580309880403c00070510140c00112690000300d103400030301c02004c06800700242181c1c000c1c801c0350115165041060300b624180b020341e004201442c1c0002c06c4000c0038100e060b0300003d0b040d00002c02c0d8030502081142e50b0721400d014403414400080182e50303071540d05050940c00d0344582401e01d415090700c00021191000660050080e0f80c520340440d456488485990007102c0360540250b00042c144041070880c0b8250f80011405c9100740100c481e050307511408602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 970568597 1250 970567347 970567357
    0x3040305031906080d0f0e040606030e0d08010302010c1e081801031415150f0307050d0608060613230907060806040b01141309021308010e0708061812 66
    0x584040148148100c1800d140000b6250907041880380c03500740030119907204107425050302004148400042d0860142d1490701c00260064000d020107074681c403014004c2c2030000366018481c8a62014442c1003846130480718141c03641603446050043c1c1715150040000d50a0b241c20000141b185991070018081b2001089640d800900b40e4060391076107000541199002025100806500400c008020401d0301c020482490f0480f05102c001c400316101d02c90130300400b0301020108a00209100c10f0700c1c1c00c14003402c0b19840c8401c05100290300c42c054180c5443e0203883d055080880c0388040c00415035160030201c81081e519811908406c4810081c4c98501d800b507400e004d0765003000e00280308003940b010300c145d488032003031301c003031101d26640c2d00006c100c0718407001301603003148008c501405005500c81588000f80064001951980b285c501001b12580c002c0c0f11701c20b081d42c070708285482071043c049800c0e0304491850740a40900d81e40d41aa100c898000d15070f01c51100d0041c00080442c51807542c001d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 970569847 1250 970568597 970568603
    0x213020f03131a010e06010f02030c03040e010509101505160b15030d03290d08070602040509070f0804030e0d0b040c0e1b0904090215070506060906040e0c0d080c030304 74
    0x8550b9070301c2c10807002452000e8840c40743e0542440042c0304c1c01e207040f960f954001c10280b81c20300113030400680403411401281c1104085000c00500021507224449403181a00e500302c800ea6050344400d000c0c50b414640610800c00c8908000c1e9480314502e00440203041a1086500b49094240c16661078410401d002ca650703e521903241910041c15080030401803603880b21604040100b400a025010007152000fa000d00200c014a90121010740300c0d1450f00c41e1542d80032615544920036460010b02a400078001e050140191800143c1745610038040710f9420051500c805420352141d880840e50809120841500811465003071b00c0002c031070a900c144aa809007030520b1a084c20301c0f135048a03400000d40103045101d81d0700c0071554280f007030204590300e601d0115170001c0c000c1c13490b10100d030501d00699180150f10001241d0300b024000e0110340188504000c171142020f0303607554400c00007200c40c400710f030000c0da9210020991860411000070428513001300413107814040c5c0305030310a00e10307030080301d0807 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 970571097 1250 970569847 970569871
    0x905011d1c0210110606010f0215071707050901020c0402030f040f240e1c02070b0a0e2806050f0714071505070c05150d020a11030a09050108010e040c030213020f03 72
    0x107804050240101071b0072203400d18124080320302c070354402990b0300c0d05a80d078000401000e4004c2010180101c40d100c41d0f40a810f09980703801d10f001034001e0200c0e04549003050250146103013408403440c05100304c030b04c120910001da003900c0c0c5494a0703d10040f0304c041c600300c0340b1452100d91030003c0001141c40744d05d03204103c00c002c02e9008004101d1801d09004260054507500c840354040c8019401180240c1510320003442c05444440300790088420341c130072100d01604445105101381c24030f41a540c001038190340d80c0003589001c654512046a0390f100790b6001c18000042031103860001000c00e584401c030364650710304560700513444400c00982c0c01000c00c2c400e40460000103a42c400c00008801000c003c2808403101d0f8000402e00052584900c03800100c844d40c281e00140e2884500d00940c851000040c2900407640c45010001004d0510005405135501007262a00002801d80c04668101d11a41e40801c0504400d807540e82400a0052090900c1d41010303024420b8100c22000360000d18451026403011b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 970572347 1250 970571097 970571117
    0x160605130618030e01080405070905011409070906050307110a0c090207020901080304030305190c12030501090e0a1e0503250606060c201809010c0905011d1c0210 71
    0x215044034103a03421902c0441c044034104001c03c0e00041c0e0301440c400d0038280301e0300035034841c901a4100000c50708003482c00e602d082c00102d00034030301d14001d03c00c03c4811381e1035041e00d484000301600d8241c01c2c0e1085000040b0b0800000d21384d148540d1484080c0011f5404850003e0001d03626106505110340200a0156010905030f0961604031141801810020060f503d05030031520007c0861180c04a038011030608526050049442800e08000700b40d00485903c0c02511140001800b900003803164400060508904500c1008007113072981c078565000054545050301e5280b102e07101c0701800c0b401c0e103081c02300707024103441c009007056440012048600d13115910f850791b20b40b107c2100c1882c4c02220402100c80918000240342c0c100303280c1c07850021816030340d50300e15460000304d031403d40c01e0a184a001c40401400007c141c1504181c000f501b007900d50450458507a80111940110a4a03003507850055403804540740c20140300055a20380c1e0100b8240e20001c4580100708098510118840048c0c800740c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 970573597 1250 970572347 970572353
    0x301140406050a03050c27070804020f1905040c050f0d0e1009151505040e01021207020c130b0303091c1b1d0c12040c0305151b16060513 60
    0x7007a800a40ba00701c50503103c0d03e003540c482c40c1d6111881d031849802080d1900003038108000c00d140d01c0c10000740d000c42c00c0869281c4440c0080c000c4406643c200e0081804021410383c1d898440c41c01900e44600414800702181b40000f04800741c0389196020050007010800f078003100c90244014103441080c0f00740800c0c0c46051100ba60b01e8a040c9000500c03a2510702280e800010380f80303990074042e410980300c0100f6150f120103008000c0c002d8960150364464a1318a009009030300c1900540305802c5101100f060707599810714143d07110314441109a611881080406c3d00b256071a50001c03400e503001604581c140380341c0c400842c40b0b4900c0b032100409101091459003041040b6403040c02c110b04030341015602c0d914a03004482d0f2074086407181c1d11060400d014002440e0150f03403c2038840d0300f544440c52004605080c204a401c0315010300090b11580505540442c420b40784901050041d82c0d8000c035150a04055000c500c107030341000705035042070001c159a07400420018000c203400b031f1800030b010b044100c4042c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970574847 1250 970573597 970573601
    0x3061903050a1a0f041101090f0f080f0105130209510307061103071e0309080303160309020f10030f0b0117070f090806070e0907020c03070302061b0303011404 70
    0x1802d1143c04442e02020044c48048004186030880c1d4001080c1d1044040d900041e41c3c984925003000f00301030604440090303000248070190b0211030004040d00c0001c0c080003040c500b80e6400301d4094540386583c082000042c145000b8007548054540e55070804e4441241101a00b1102115402011507911480c1101d02a480c05c81448110341c7c1c1c0070900c65246424042500c410181c440c5600b440144040604000414000c4804260f803100c00c00383c502d41100690103840090315826030004a0b0780307001040483c2e000080302d006103241c268080348115940002c9024022050007260003005a0b43e0320966038072058020002c061240c0c5003c900342840c80002000c84040b03030301541c10019003c110804c450303035000d002600725556281598903c040301d4420780d0806455031264200e03205078410425070582c85461051413040440d64004076466500c42280c0e1003100343e554540c990000101000146440c800400c80c44441504001081d0104903841341560000da000d10958112480409c480d49018 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 970576097 1250 970574847 970574873
    0xb040603020d0305133f170a0302130b130b0f0f030c0408100509060705040303090312020106120f06050606090f0409031101090c03020a08010507050307110c091504140105010e040203061903050a 85
    0x60054142c3d4000f06c3e485200e514441e8104e003040c019030000d240c110343c92180d01100d541035500100c8450040d0303250601c640991040e00000c0c0b20f103501c90300100b681c00a010840b500742251910903420103c0c112070003021a07101808000354560704020000300c130f4405001241c100c9130f90304000101850040e18150030036030006c3c89441004030410080c000a42c000e0030300402c3e03030340210514140c580b401c0700680c010040343e0005071811042800141c1000304807c1c0030010544610b02c01e201545a20741031121a000da0300d80b080d880056035210a055085c40d5110355896402407501010080401c4240c40c2156800c43c81518020200c0c1018010341c14903c1510b4024805400200214a040030380241140406425102007103c04d400d5140c4031482001100c00440c0010500c0b249030800c1e207124180e0302d20591a6a024070b080507a401040c100040020341210360684540c0d244999440422000f5800103201707136406141405685134000e034045201004c0c40c4104020b008460850500381119054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 970577347 1250 970576097 970576199
    0x2120604022104020f090108161e0b07020d06050c0a0e09060603011211220b0a030803130c0e0403050c16080a020607050a150c030b040603020d030513 66
    0x104411408010509a0102c0040d03818003949115101c910004018181030b10b0311076801240600040f44882c0085480078950007060300031190b00769035082c000c1c01a05030182c01510b521800750100a0500b9201c001c2040d54030007000e400010403240d0303506044800c02d6440c0d210801c0086802c0310303083d4200d078800b003226908444c0384805143c181c0008101d07120502031040c7c60713030150101e2410003403440498081707880018044008000c0c0b18041c4405800a070a054500f9410300301d4981e5241000c541e8481900d0300040e4162955461050300540d0b81c0c0075030b03001c0742d1800b050720300010100d1000d000b05004030303c0b980c0c9482c0d03079070409003905160250040d05160020690b000401c80b001c000a0243e082541c140e504a480c0e14440c20028180229540060502c1000000210b0045402c0e40715505a03401d54504100402c4103000b4442120807500009400115940580002c02e0091024004482c1410904600075444003600d00640128a4204545890428480203078440414441c6a2464 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 970578597 1250 970577347 970577351
    0x309010207061b140f010f02070204052a0901022b08010e0c04120305090301020712080106170f060d0203030403030309061d061308091215090d02060109020c0115060302120604 77
    0x3c0d840c0e11110320014200c00040007061940381c0401120301c14040c101001c01081c0080090104d06807000003c0e61002504070310442c078102c00030380000c00740003844c0014000c815003140000f000d80c088c4003035988030030f41c030506500c07800c030200001460300c01000e00d401e1101c055446881d1081c0e000038045550680141981949090822400d00440001da038115503403140d09404a40d4035080590b6a449010b0403603401d94000501c001c00c0c0600001402120380d80d42c1c0d81d0144903a0303120ba00301c441508400401d0b80c071800d041c011aa06070076012029400c41d9008004506480310340c0d0010349542d2181d88110040b80d210984001400704030b210324041042203400000300e46d86c3c1c002034a03441d00b10040203c40b2840c2040301c0d80c41030041c82020f803004030307070301600503400c0ca980d82055940c0e41c0b141da107204142030403200014148a00125103060b5900450f002450241d00f0300c07064070701a40002d01c0d00e05280d0743e103114580a074444820108010700300c5403001648d403440b201d441004180300904d0240118 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 970579847 1250 970578597 970578617
    0x7050a080714030a121b0f060c08060f010c03140910170c12010b070f0503030702071818080a031e0f1415040b1206010611070602010e0c0d23030901020706 68
    0x4d5145d0003420064034030740741818800b051400c0601820706541005881410131195040401203240d01c10010040b00762504035007507490314100403000c08040041d50020308003076442e400003401030003504030b84402c20f04c2c198107141c0354101042f600d48902d00c102c0006800e05e0700526403946110b41a64001c00360a413900d1400d03015211201e004081846180901400001c1d90014095604500b11001381d00105880c2d1300c0c1025000290b5505550040c500e0030030444003100e060303099074441d01c55036038020740461043d039015403200e20f0b65402c500c99420505407214032615596600741c0d034080c580307009075400107081c014090f03520040b0741a9a004000400746101802418800180d0b814207180301101e012800009042c00305d021040000f0742840d6904c0b420b0004190345030044510f00300c0e11140003ca8884039a2070f10200e081e80c0d84040300e01c1e4560401c20040c821800c1802124440b280034a403001409804454110b020000201030410b40d9000450303a00c0c001d40c1e051103010014a003034904103041e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 970581097 1250 970579847 970579853
    0x7150801031e0209010e06030a061b030c030b030c2710032112020a0c1a010e25081503150601030e1f180c0e01091506020c011107050a080714030a 64
    0x11348010301410b030f41e003a49400006c241d681c04012031304000c1d40c040000d001107000c3c22440d244502c0180c240c000401d0614240405c064030900c500d4600c4c12004005100d4641000180550350021140c92120031441c40c030b100080c00a0403030414080d086407e905400c540c65420560300f1135441ca02020754005100409940700c80d0b01010802c0e151050b0000103075134658500c0243c0e034801407020005c1107440c4000c4500c2511b00039080e03e038122281c0200080040d0386915040249100790004a1090309015003c00500342c414059158001011003641214088820000346401c0200100e201c110f0351640800c08556854042d0048809015004103582102da080e820705a2146010b640101c40d540c0940310125a4012025036805401407009803040c0d4941184462a0109004062001d400c20141070999080044a81e04a903401d60140018200300c01c0119485200d0217030412181c403d06030041074584d188048003000b480080000e19415143c43c54103403580400025191181d08011615004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 970582347 1250 970581097 970581109
    0xb10050d110d091a06030d021b040609050f0a1103090a150f020a0207090e070f031e0204021b0c150f0304081612110606150c07150801031e02 62
    0x1600300d0340d031004034060707524060201031030103030b03445000c2c065081002d8041400202030f07a2404401001c6201111075507080141541e403201d45c1002801a88000d031032140c422a00c40c580c6c041010000d00100c0c1060343c6601e20410b50320140c1c1c10740201c012110510444407a6441100701d01c0d20900d40c075608500d000c40c059526014401c2d40901044a560b00298024403c2c2d8401c0d0200340b0161411502c418554900075170b91850360042060030703032401401c0940031000041d201c08681e24000340071921811a900c0740c1003050303c40749030740e0b11880342e40c290001a65a400940380d070940c04000200e03800c0c0c941042c0d5181441c4a859280250841030815505e22800340440b40c5410089070070580e20b0301c55103440381d800e2040c0b040f03e400c1d07495003000e0300c4d0030003240c4403120650381240d60300d21940d0003294180d25250042962242c1d40641c2c010f08081000c030800010345103c00c1c402c001d0700c012640e2030501c00b0308900c00c402c060700040d40c403070014010820716446d0408944460340c80c0201a508580c0400e0b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 970583597 1250 970582347 970582357
    0x706030b031510030b10080c040f1e0b0a09050603060606031806040809040606033309050c0d110a0206040b061f1706030115030b0604060e0c0d0b1005 66
    0x2015251400c0c100c0c1900c04000b00c2c0205540030502640901e0000f5600c1c40b4050580000c540314070009010500b5100c02080d10f20560701014003403c80002c02a0421000f445000b5030741d902181ca422843c402d41c0581e6030f1000301040440e4000c40d2640f001c0003001900a0103401c0040c4042c41c10090003100d03200091419030280e000c1e03070750300e54070b0b00d602115100e6042c50510381e01141c440c9604000030851028058410725509580600220307031141d00c01c2e400d032484038003840c0343c820109800c2003400318983d411101110020000091140c2c6652003c403d0320b0003241c02026848002604110190081c40703807003405011024800e0800c1b80d4030340f000b9119400503101409402d1940c000c244161760762550703002d504968091202c41a09485005446c01500c00c4c0c0132241408500001011400d042c06980100740e594540c0344030190171903503010030386540074001e00e402641c2e170840450a4030040d4400740c05040402c008030744a1a03081c0030201030b600c2a0952501079001c811b501e58402d508181130f14 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 970584847 1250 970583597 970583609
    0x7060f08150402070804090605090a09021804081309050402031603020307061d060d0c090510140c0111160b0c0a0801030b1504020d0b0f120304030b3c1807 68
    0x1201c01500000000c010b07001d40080507010040024000480840c10b50004040710b1040d2643e4034039543c2c5607130000880c0c25201000e9001003031028411035010406055036401486103c005050a0030360f0010b00a0700301170b0300a02c1c1c0c81c955030401d00055180400180384048140206680d1481c1190301203504c03503500784160400d020b0501c994901c00c200e020102c51011070081c1c01c1c0350720b40403082c10400151007600e905a01061918030007042300d0900d040c00f5607040d4244d40700e16488a410320505807041c0c0c840342ca501050b560f04c2070349200c0c0400c003000404c403506595200582c4550b460400c403046810141c0508903900c005c00200410707642110745181140e8002c65100d841359075842800b850b400d40d212031990b0051000400d0b00c540f00c40d03a0702920030304500781c1e405101103a01c1030a002104414480c090401d038024042000054065103c0503807002054400c80380040ba00b4545101d800801ca00b81c07000c41c034010500c0801c59003008185030b44a000007030b8881014260f0f200007910303000e59009036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 970586097 1250 970584847 970584871
    0x60e13051302190b0910030b0d0807060e0606010203031308040302090f07080903030f06120c04050c130b0702090c2a06040b0606130e090c0d08121e06010e12011b0207060f08 76
    0x34401d0710b4066403080200800141009009e11501d1411014940c0895000c8410910707022a49120080014416111f90b00c1070b001180396417035006480010000000b0111202c0c1e50821004c401030b01c42c290018018a40514440d8850170140b5000e0852080100303000c0541e4400d2003044818103402002d5a040b8005036100b003035040614098900742200028a80e130420705040c10701c0448c620707010041c00110516400800c80035203030f81c0c5000a602ca9104083d5120150300007184192901500820b2580c104103500c0d03031030b0031201200c00300070006103e40c006107801600410040c02151200603502072401c440d0310b807a00c409058270310b01e00d15160007145c60b1000550002140d2441c104402014900d00402240c0c0005c0300b850403400710703885101883c0007000c1400105045040c800012000f003500d8100407817150740c96200441d0a2034010350394583c0040c40203070312003000100b0300c1901c00307184010700401d014045840c8040d02d810110f034000c2081081004c505081250300004090300080300c8001c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 970587347 1250 970586097 970586119
    0xb0c0a090e191b11010b01050301090b240a030b01030606021005101211190302060f030a0b1302031005091006030e0f07271401060e13051302190b09 65
    0x788001e00b01640c41c281060341c030700200f482e202d00035805188000f0400b030352899681c6014201c41d5098660740104980864028001030101071030300d030803841d0560000b0700345002c1104c200781c00c020001445c512910800340b001900c05561079040c01800f554041c03e0805010081ca4102d000f07684405031000c543e04191746d4030100b62200444c5020100609035403144200e100c183e4100300142d10001d2420300d10a0303411508580111b01b05007030b55401c60350001d1a5078203041c20912400e11545c0001c00e070311005540c40410510030354694580c0c0038841c01d00f200058480c074106050100d00f41a58110078070a410160400900f03110350900310050b5000c0740343c0821b0005122080c01c0c6003840d618a1a001d6000358580415003840765498a075500c00200c50100d1a80000c0c0c03c008120343c4419500c140c078825150048c44206c0c01410382501c03202c40500b0a152540700f070525041140d100f9280b4845010750415040158075107041903042c10308240b01540d41152400d1501040c0d0b20420300c00380c1c05032001d801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 970588597 1250 970587347 970587361
    0x80a05010b1303140a051605041d0303011a090907090302100c02091602070b070f03080703090807030507031b05010209030c060c0a0201140706020703121a010c060b1504030b01030b0c0a090e 83
    0x817079040007560200803a02640500240c2040e1413420340a214051840e10f04a01940c81050020aa080b0fa5a2020f51300e5130b400c050b070041122410b0308040006140c10000e6059039140c11049910441241c1e81d211115815807040100a1080442000c200004d507240140940e6030f42d0340315900426000019800700b801c0c0c450503820429a603125400d4242c0200d50b62040c0130360444040310a620035500c0c0032095544a005900321001d44001600429042c4024400240a50000d2503030038000c0c1818804a00300e55480d040f410780540080720541d4001c02c8224141c10200040c044400044421905003440030392029901d820220001c5d040002051080048501c181c0445100d640c100d102903541d48080d0034043d1540381e41c500200756403232400b01c07107082466091002d1403842405079030b01c007136101a40d20f130b10014202030069241d0008511020740201c90700440200003d52180c0703601303c0192714508001e44580d10042010f280d10004000030616181e01051500035100007658581403915014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 970589847 1250 970588597 970588603
    0x606010e3007120302060a1505190302030f15060d0f0b0c09010e0f06070b070e030109060506090c1e07080708030a090c08012c010e0607080a05010b130314 68
    0x10203500507a4188041d5000900040007880854060002214111039488081c2c1e03250a5012902400503040080407c03a0581d031600082100c006c0070104841c0d00d40c4943c00910862000001424882d190315410800c60400748242030310011018081c00100294813000c10640c8401408140326500f00e02c00c0c80c01f04124400d5184c01103402a0000c18240741180d10f001d40c0354230110503180800c200141da904549821150014a454041e055034101021603581c1a40c07494050240000e1002c1e01c5541501a18244112a40715025160110305804c201c8280034143c87c0207810703444150700c104080d0f00c021200600c0d485d212301c46828240c3c0ea6105504002400c0c1c023546000500340180002480480402d5800001115024049844035180d551003910700703c4c1e8020240b90804400700844800002c0c0b084c40302c070340745540000080780348050b00c0c5a01d0309206048a2050100d04048180410045584902030244c2a2292200d161000200c0c1e0141c0c0020ba61000800000c1c1c0300103083d000200178 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 970591097 1250 970589847 970589869
    0x2120903070311030a0f031d160810060308071b0e0702030714011a060d0f0f020c242d010f08071215091b06050301080c0a0e0115091710110307020606010e 68
    0x78095070034040c180d276000301d00065140b04e948a54480c40418205100d5148903041c2103030703030000f25545042219038880e2010021504450102e04070540d000030700703c03822105d261060301e141e4065075850580e403900050342074589041041980c034168000d030700d40d604c4514035411603d08454172512012900c0304000a49019801381d084a410500c118802070008e40203820201005821f40307100c414207a16580c50052500c920511a0001c980410b500c08400c0c0c400f6040c400c410103a080e11118240203d415000f001e07449211113501e0041c0801400ca07003441204090001c600c1160b0000d091511450142c10101007003070802c0e5994a04030b020440c1c0507007a01c100800014680c2e507942c1da908000b0300243c00034840d03a440c0e0b0269040c403040c2032610054000648800d4540d0f005543d007040c60b484410300500f403400302070200850f00030544510b49410001010f043c00003e01400003060f10200a6801e01c0c071134122003d100f841408100f0350007080799036200350207103050b078403d0890200040300c507681 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 970592347 1250 970591097 970591151
    0x80706080c1e04060905030c13020d090204150e160507120309050a0b010305010b062b27110109060e0d06150f0306050906250302120903070311030a0f03 67
    0x62801d1070885818a00064821660a502e60440056446c410f050711585c5050340280c0c0726450011000d000800750340544046580700000240c0e68003940c4c0403c044480d080700c816680f0000001c10040c43e0070100107164045000d01c0314a80b0080e0540d0090801c1c02444001072001002e50b8100008600c079500c08170106421004940103c0c800d4249441030200031301059a540d420b1080e00310603410440219024062040d6076409189075030340c840e5a00c240c01040f03600c1015107940e1400c80d1140b070341c082113458550b40110b800255030b991824602c9030b04610081410302ca04640d04000c05a04090b443c10206000d50b18841003030920b25204d00103103507030000b07204d51039840786010441341c004030042025a4400c00d010840c3c0d407164904255210001c0380da1110b9844020241a11908824021100f43c540b504025081080031070f802d5604a03001c07155500550b2001c9a03001c14154005d511800101500b0090b600d000c50165000b44000d0000040605240c3c60340c1c1c80705807040d0b440d1611294030074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 970593597 1250 970592347 970592377
    0x52205121615020c010c0329030703020904080d060815040209040c0906091d0c0306011211030a1202010f0501081b0105070b0a02130603140103150b10030f0f06080706080c 75
    0x700100702c0c0000b9004410f02c03050700e41c681190010141e000303100725801001401c203138144000d1400e0402d840211050041034040c01001c40010058580d03000f000c0c012441a91042d481e500844401c5084801642c409181c90f8401e0f41d0036030345906603401c120307002031b0142c89290300c44c1e907581461050300c103030b5a1210481a1030320790000790b04116584401415006d050700441500d00940d201175840e8560581c86030315410140041280320000a003000025115089007a603000030071000a04103050b030002138418502d020601c041c00c50b03080c8a0072008008484080010b54180400c040d500c40c20710921000000d0307000f03500f02c3c40703030f000f80280c6010030313804441c0325424a40039841e00b02a4005048007000064480130115100703000b4000c5440e10090800d03182c1d2186c1c6035407594600060b1080351280c034241d448801d10800e8403011403021400520f40c070301152071407450300001d0450b10b80c1c4403260f560510f420070034441040c0201384101140c00340d141c8032105884e074200b21400d42c440d061203019218 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 970594847 1250 970593597 970593623
    0x10331418070206070201060816140d081206131e021b01230601231317060f011e0302210607020a0308070f0813150606030522051216 58
    0x10750300140c40c51188007543d0007801050380e26004c00d50342725980c121030081200411010300c8a8070542140040490008000019210141c0c0b1508140e0340655041030001c0b40e2a030400a071803c0150074000340148002d070030014444205403041c52101d04600f030000040d000115001e030ba80c10101c04070300050b5441c00030032894144080d65a488544c54507806011010040001d0507036000750031080003540d6941c00039803082000d407040e07040740c0c1c00b0030891008079070003003c049294607800c0d001d420200481002041507052046240420303680590160034071140e242032010b40d00e0302e42100041107070307030580b0440688404205140e9413500700380200c100c0c0c1d114400410014941c0001d4640c15076001c0e80700d04045485000d4200d40a41e07600d0b0354500031942c0c010210b000c411914103000c3c011030107801c4402030500d40b1942c400580d0b000c1d611100000e42c4900c1400b501d0014180d030301503900c16503c406440d0039841d43d06c00d62030310480072061a509001203150080c110007400c90b640a140e01010f221015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 970596097 1250 970594847 970594861
    0x2010c11131d060f0c04060e03030d0903020c1311070206090402090613090c050306010c0b06040935160f060f05040803041b051f1110331418 62
    0x1203003103800e42e5415101d60400b0500302c2c0342c0009002e0040b581000d40b00c0ca81401c1200a942e04002c0c000d80a130588070030010b110007900c840c440c120103070f0b01c698040c1c0b26011514040281503290130707a580d442c59103428641c108d80070551048071502541551007039141c5601d140010000d001c0c001005d0b40100780040c03040341070079035220b0300c00c20740b0b460030390070080045100e000f2240d5000403610301d804248000101c40106140f41101640070a00800204840810b641d036032a00941c1010301d8008520681c4088034100400451004000748144c0b14a04004905290103140d49500b040541980241604c038018000c00383c0048030114003402d0144980e00f014a4001a540d0089805848088040c030211041d48154900032044444c0241038001e064408403500c60107041d100f00304828041e000c6071689541c803040c0055600c0308600750b000503800b12060020486009001c1c038880c45014101114a0aa4200c0b080710040c2d07903031080201c0181c40c100001c10f0303c0b00c55592803042843c14440800ca04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 970597347 1250 970596097 970596131
    0x121b0604052806030b06180609040c0f0f0513050904170c0c180403170717010b041508010b160629030d0201020711060702150c03041d0402010c1113 65
    0x240302c1d280c1400081c00c0d50b490b00e0807000ca444450003140c0c404800c01c603032402c6031a003030243c122054005004078036165016000404031003264070503401040c01082030320802e54201900c2d4011151900346a444d1148440364603883c1c4406005081c42403800707602190600c2440e464031410118030444041d91504146010307a0792781e852007125071040c0d403880d080702e4450f203400a85034040c580c152105014085c1449440d0001400240711070100440d00d00e01403008902d110855000b0090840c1c0345544c1c1d0300349142038401b01d00f10301caa1424815034200401c07a00000600311001d01400c400d0403a6941c1644c902080680b41415251020074076034a10807500c08000001e03055442c80860886204440c1d12505070309034001c01c030300500b1082920348403420303509021000f030480c14030041c0400c0c940029901d080039681c100302a50314481d4400f140c24010450b0601414080b145400142c16035460f0640c0001c0007052441c41c028410510fa04800d2065204d104406920550040c418040024400c02d5008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 970598597 1250 970597347 970597399
    0xf030a030510050d050c2803060509120a0f050309070306020f0c0f0105070c140312091b041803180510020d02060a020403082d070c0311121b060405 65
    0xb616550301c0034006030901c0c007400f108400a0788840544440c208480410010070400074102d0314143e500340d4025012802c49180d0340c0514440d2000107282d00b849180c071454140c8490300d0380f005000401012018980020101402d03008901d0025500c0d0350f402600c45c1401d21560000f00b2107030005c24a02e00c230301d0110000e450002d0b4000c0460b25002075801589003a1141a20442c020032201449540420401c0619401080201013101d28111014510b00d1901208441c0c115413600880000040120707040d080d0042841d040703805001c50100d09042c0034441480c40c078014103004041024150802c1000104401004014030500b010505403001039141e1112409981c014001c06000626800061003581d080e40c1c0c0141469040c000701011595503500f401c10f038000e00112181c801840f23165482c00809225101c5d80c01d041140745540782401d4032440780e90b012481512354041c09100e1b805d000a60791210340f9500a030307001c00c404ca81701007890b611458024940288400b0b0340280b0ba00510714040d9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 970599847 1250 970598597 970598611
    0x602090a0905181b15070206124003020c03060403090906060813080a090806040f11060c0a12090305060a050f0601080c0d0b040212040f060507030b030c120f030a0305 73
    0x1501c00343c0110b04031603c400007030681c80307180c1c40d000f4941c1d03010f410100804403001504000452402442e42c001031420380015203015905c00708003080284a1000704540828080c81c6541084024120800e452198812000b0740c1d101d0000350181400b49807080280600c880c038090103665641c102420020081051800703500d03940c234104100001c00f2031003100c43e603115145c001d0b1100c03001c117a20355440c1c4050384100761400030090032003408182190180300e40c50042d4440d480d4402028030380d10b89010062200d080c2a0f104140522912100c040081443c20b0466031080310403a0030029140140c4c0c5517149900040c0a51061004000b040035243e40b1280c010b40c1c0c0d010b01c00f61a0303130360940110f850303c1c0212103029444500b8000e041c0e00408540089240643c02803016080150090020702e40650865058400d0f4500d80d6121081c00840d05c1240d411559502e401d21041900174080b07562180e0704420306000d94071042d8809001003040c03060300d00e41419081640e6550b600310400802034001a103c2d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 970601097 1250 970599847 970599871
    0x20a0c02030613240e070602160509040503070308060301110a20070302180403031107030e24070b0a061d0907050901033302040b040317040b090d0602090a0905 70
    0x3003494095443c0d00022004d0b4003203e8000103113181940749200002040a0703108035520f420b1a05800403041c0003100141c941680184507402c510a241004101076600c298001c2d240b0350b040c400800c0002c130480358181c0e050b0412015645171000441d0040c0030b40d405010840401061545d0410f504c8124078244011018603038101801d110b04003a00d03001c980c44001d50220f0504844000500c0568215510078000d0500045040240b07000d210182d0020307504400045000c4000b00785850305004050122038600910700505c1d0b900521003c562051540283c40ca1540e80001642441e1580040d40600a800c00b900c00f107481c9080a02c00f004803d40d60b00001740038006011940d41040365000703040f02d4008101e4103520f003070714144000c2c8909203440c08401c40c440340d001c9507040019000400040119003a00b0f5500c62a50400c0a104000c9520400c2d241c00c0400007045460506011354901500c2210310a600080528010009100d0249501d03005003049800285162240d840b5607c0b0301c2d000400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 970602347 1250 970601097 970601101
    0x13020d02060f0703080c0a2007210218061c0512070c03020a0e13030e120d05040f06050301140108090a17070204182a0306060e07030605030313180f020a0c020306 71
    0x1b02c0c81041c0905021203000402012280300850141e41101d00c080c6041015034000540721103290307241c02803640310100074100381506802181004030400809442d003001703000e9142070a4000803200458692295180d200715000b40c1d060100504c0056541e042d0b407000c071035a9680624107041034a41d03078801030744642e40000c0c0c0020b5010300940f03e14400c071560f0002803603035000b981d415992a00000110f03900040c5e01c2d0324202d003a031020003424a14201e80e0300d07040d0712a0b00d00007000103000c1043e00840c00300601400104103011961f40c00c5c00d03901c0c0c001d00301403c5a5460b03403030303142c9880403041001d000018070542030118221040002c0c4a03060096405101260400c024074840c4040d1031401881c07410703803484405032501c0041d08228072122500c00340c40360340c0d9a0780343c0409a5446411081c3c80714458000d004071683c051091200403c4103401842c2085070040046080c03891070b04c02c0106210307120b4000c4161440b0b5521140301400c041008545400501e5001459804050030403800391080c0c81c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 970603597 1250 970602347 970602361
    0xd021f140c1b03060c03040b0a1805010f0e0d0c1514011e0501091206050403030f020f04080c2d0307240306060908070b0c0f0a0524070813020d02060f070308 69
    0x4d942403041c0b001c000c4c00341c50350300e441e0f4a020390b04070001d081d001d0141c0eaa441014000303000d0403011100391f00442c008106241041c60f500b00b2a0a4400552600e900096000d080705400401c0303440c205400c6003000031840c01244000015044854048003200d0050001186071a21311a0701203040d20704514000c4c5807074842c4010340301c2c03104a00910b00c040406c42c2c0c805000400399000507501510a2a0120355940504004801d80e044054900c201103404a402d0141400401c28000e00c000c0803120b003010480a045a800706e08451159400800d41d00035440000752030402008000b402340080a01c0ca044a103031903203405004100c10b100001e03041080002d681c5208542120603a090000604030807032515040c1c1c10f80380d00043c107558260150301013402900405010310b030300070350044c8064503008100c5008455515207041d51414512110f201707015119501c964020b503c0340044a400d0f00500281c0005198500141c0000354810b00016200c810b61000201030b02400e482600e480c07800c0d4407124 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 970604847 1250 970603597 970603603
    0x50d03110714061b0111030a14090111091c1a1f23031f060501020f0d0e010c2301021321110109080102030112110d021f140c1b03 57
    0x102c0a0398400001c1c070a01904e500c08413801d1a50142c00000081c01200c1e09106601d42c0c0c10440341610066510401c0c000480b041e0301c0416072003801c0070020483d00e5040c0c000c3c0e10f00c1d4000c60b03001c0703400f0b1f00106441044400d183c1c100140780030b80100300702c0749805109044400d552400c0300c9030824901c0b0303a034500803240c0340c0c8142d042c15140d8448990350b165040381d820461340e0641d50401541032180e001008110083c061030484291740107075001c0348450800b0006803501005c107004122030340c0038048440d0007130b50104349240005401d107451000d00d0749038200700c000c0740d80114050103000302e0188011076144c0154010030405000070500705042da56589603048101c3c0c0440b1096a40b2041d000c1c95000a000b0401c0881024050420401e2a40c507000c140d82240c100740c200030740c0065a140540e050041d0000c0f000701200c01216404c81d030107a55408285000310300c0b4a00d0000801c0e2108400c4c13207038010448070448a0600d42c081e629944800c03682c40d80c074105804043d1148004042503c4542008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 970606097 1250 970604847 970604879
    0x60b0f0d0b0c0f30090d0c060b010e09090c190501021b060f0706020307020105010f031a06060c2a06040e07050c0a060c08060114030907060810050d031107 68
    0x12110011442d40ca801d2440c0e141da208041d08241c1c1a0f0820440205011039510340411000401800f400308604601c122105840640205029030000c070034603029a42c80000ca064160b48054081344038502100166105001d4005140d4001c03c008100482c01200003000f00501c0e20880380c1406c819264404004005460b008090060304080146500c403c01910b11011455000c2d026034070340320182c8002d240c160094602102d0040d0000b080c0803020741d09000b01400340c440142c080d8035142c41d6640c0c100210b61102000da25010260000404580d00c1e141607525020481c1c007556141c103602915400e039076105030350045094891914980e0103007400c5040d6001e0f640584c0e124101c948440405031240e40190544229a2060642180025045004484c4201c02030b44415483d8203001002400300300c240048802818021b10400280b050001000f804a682d00d0600c0c000c0d54a504940441440447c0c0000b034000380344a880340100340e889028100d801940c02c040d5000d06880c0d205043d40300701d103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 970607347 1250 970606097 970606103
    0xa0f0f020a1e0e09101a06040303080702070e2403070b221203090303110307061d0d030c02030d1d01020c0c010f091d131502090a06020f06010902070f0f060b0f0d 71
    0x4442845c560256656104242d9644040340c1c1245c2080340500084459015420071000142010f041c0f0031000c1d0100706d06800f42007140030807040c901c0c0010a4600040321000d602410444d01c0c6d814200c103440501080300903254440120303564001d502c0c00e0004083c030600300102d000b146544d001540012035100604001ea1544d502c020f03c1d46151401c03102c095111252016178001040800009440d80c071a4481d4010380c2c2c41da02d2842c0d804e002c4500d0600391184100418541010304402c0c810341d01000300c4401420b003000001d0072040745414a603595486503044010396200181d40038000000003850384024000740c0c0e034000c000440d00400c60750f0341e00d14401c80e00e01e119914000999440020241513100388080340500c50021213842d2008403410f8540c044551540c00184a1114100396515101519842c0000c00c507031007030491304944d0384070b0511602c82656804a100c104001e000544888069000b07a054031024140f0b0404200501d68684800c0c0b0031039024503420340c242000c400213401c89030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 970608597 1250 970607347 970607353
    0x3080702091b070c03031d31021602191208030406110307030e0606010f1d18100e100b0703120f0c0c020301050c03090a0f0f020a1e0e09 60
    0x8840da003401038400014200d01c2a40d840342d1000040030091a000e800640d00801d0740c0183c080c91800c0103841c0e01d80d5200b85074441e035041000b07080ca5807960035048020b6540074a48114202401039030440142140000c911124000906020040361042d0a030315020300840d11014044050308902c850403040b40315a40700e18103481884004510410040c5911a004010128030006800001e0340143e000b12041c0b00400d550b5860040c00b003404102260340280f00713090059054608410140165441c2040104202a0b100300304002e03494501d400c1b4414100000c0d00792481c00c2c40d80044181280c18041c09400501e100005908080310b14845804c90f00742c071031021701d0101151012075524801802c0114600d482e420550311181d442c0c8145039415030f55544a501d90a420f104140c25034101401c6204420f07014410300c4911031000c1844c00103150f0192506442c150380c1d2030510700c00303124840041d621000346180040d142c003411a200c0c40401500c000a14460385420340c58828200540e46103482d54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 970609847 1250 970608597 970608607
    0x504030b22060207080f0712080f1e09070302030111040e0a06060516140d0507020103150e160210360b07050c071205010c02150f0f1806010609060e0108010308 70
    0x1200e0343c0c010f01c1130380d000c0c081452030600c5107007509249900c8940c0c01c039920208800c0e03546042da800341c20140c01c103070030a088204074242108160020109400036400080c81da00100d02001d00410444004540c003070002c0c0900e104611644545030010300c40e2815008400d000070300310a00310b00c9103600741d6100340c680d03034200282008459003281c41410122070310716800e000602e00310010003403181140720958a890b0b503083c59200043c291401e20551034403045082d00700340001007e846410741e00070003007100102284d44502003245404020203060350610302c1e002420a45091110710768004006240c1d0502c50502c1c4040300303680c0301104a1000d4490307540603000c41e10030380c4108024803241c502d94044070b010680780c410074045c02d40b030b100c821038460b992030150022087c1c042c4620750341100180f410300c4003890729031025160400000c1c50951500c0c95000000c103900d0b180f80d2801d1300c82d00b804084034203035030710b50702c000e008040680a0280801c20140f0f211621f58810700e203540c166548030b442a4141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 970611097 1250 970609847 970609853
    0x11b080112080306041d0d030f06051c050312010f0512030715110c100b0405060a1404111207080103061a032a03060a0b090a020c0a030e0f060a0504030b22 68
    0xe0f0000b9108a078001d8645012503e800340620108990b503d11030003800c26820100006000c0f80c0d0841d003901c0c407260030800700300005d9441100101446501d4000c0b0003516602c0e1408074114460400c4d0141006050400030900e01c680c40f5180003070f6001a1283c0d07001c0004542820382e640a503000041580924903022460030603182c200b50000881c13134a104d800c0ca400401400d0900d8010b20101c03811aa580145040c24601070003204d800030000d890702c03000d850030012080e80303004031680140c1c021511541ca040060500004030350003070385411030751611810131000044c0200c20030b05c03042d80c503a030620440c0760307001c00100449041208002e00524080d248045100c4400b200a50080c1300766900300e049000603107050240c0c51044004400004402914070108106000050f00f8561050310500840f40315081c00100e00b00c00302d40508296400d40c15240020f4031696100007125000720002c104440c2040e0090054000c2d244100d0070949580c0e954421140440d821094882d030074036946104c0404 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 970612347 1250 970611097 970611113
    0x7080f031e22030e03070602060a0b0d020105030f0606040e04030203030711012c01020c0f03071202011509021303050316060b09060d021203121815010605041401020f0f011b080112 79
    0x1522a0070240a001e12004c00a0300b0440d0540c0010056040706003001225886403241c050390403011240d0100c284c2a40e00000e0160100034401840402c81d01d011661a50b034020076140180410380d0b125215181a1030001e40301d42081d51040c000c1981002541103098041c064442940710003100060a4000b03a5840b014550409140034110355081104c000000740074025144004880c0b002580e9441c0d161916801d800b4402e1455800c6903d060350400400212508a0f01110ba4200c005a00c0b03103212070120400c60b8017a84010254400010340d000c8000b074501d1b2402000e401244200078001e6142c007844042d130811200b160f40f1030300d009500b01c0189003c0e101c03400b280c07440100316420060f1680060b000d1a005844605054440807034007042120100200c620108901c04150b4080d49000c04c013405600070350103203100031443c08400141c641d1003001801c40c0545185c04503a540c51042140070f008260100d0780918041031801400b013241e0050f00e01d64102c44418103803985000c016241d00360 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 970613597 1250 970612347 970612411
    0xc09150908280204051e0901020f0307300c0e0402031614070606030c1a0c0d03110904052502030a0e040f2409061a07080307020307080f031e 62
    0xb84002d40d80307070b01001580b15481410711504903c00410548010b00030b031020b04a41c01051140c0e1a03004003c4254240c0c0030b9001d40e5005030705800d0040c81c24441c411102c0a80d003030303802900c3c402c04651b01e207000600720355004000e000c4013907102c200c7c9c915860020702090b4403040b918004c0c102801c1178403006051040310441c1c8090b0a40e04a1401d04180f81e072810159419a071003030f1403403441d00390184000c031000d551130042289003101d214907240b0301c03010b559103034140f116549051554400303255010068560440d984240001d10420152600081800b805424080d0034403c0300030940307138400d0b50b9000004031070b020301d555190540103441750010071010740a01e412480c49991034001c800a00810848001c0403502d104900005403814041c02c44119100340d031060355140c01910304000003213422000c41d512250058016652a41c0c0c080e0140d00c1d43c40340960040c0a9040000c001801c400000c010303600034400300020b41d051103205074680340b02000a8418000701c6481b0038a90603c1020324101c40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 970614847 1250 970613597 970613653
    0xb0402190b07050604030815010c020d02041d070f060206042a050406150f020c36090312010504020403150b2110050903031303210c09150908 62
    0x8004030703848a441c80c810382c004880848407a4003801c103200c201a0041400780d840100442c03881c0080040c40002000d50000040c06800303a072080030340e40150f40300d54000108684c0c003401c40000b07215519540f941e849041d8825000c40005908010800c03603c00314283d030055800c030382d0041c100841d10ba0901400843c660b81c9151032086448009016100c5020b1900141807084500b0486500c005004d005500d454403d5400c41d0025140c07005a60b4804d03001868000c00180780c50003000113120781686085a5030f00c88012210403100b000a5084004007c11440c80f4407013400c4001e9980e50103101c180d000d94040209001600c001c52404010340f1780c003c00700040014171040d034802051001ca12411500e000038007980e000b60300b0b5000c08400341d001e00c03500000080000c51840c5080d4403000b0030300700090001400c02031100c110042101c0e00d00c515001d5504401020484002909005820030a1600c21541d810740d4200c1c0c1e8445090040341101c0480e030011019083c000700b49140303410901c00100c1e00e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 970616097 1250 970614847 970614889
    0x10e100e0108071e2a05192a18020906040b0f090a0603050105030c15030f06270f070f1d010203040e0a0501031a070f031a03030715050a090b0402 64
    0x1c00b040c042d100c03481c4c3e8115940c0e03071500c08100030030150201c0441c5030307611181004c120715510500081c0c00012414a06000e40b51040305007050340c607000c1c05450200103182503251150b03280c01c2070092221003c108485441800100c0401320b09602001e0303008140c4590b13448942032004105d10041c8000510010001c40602840c00c50b0404c0080d0005107a6002440001c0e41e400052001e0709040040d1a011102200c0114201d0044e05000c04036100042c094100c1148440118000761900100755180701030020842e4021101d03810801d52024088410815000303140010910080c002c088240703036010340307582d061611302e05071050100d03d9400030103803411840100300c001105840200c0300b0340604202c200202d4135500d982813080e070b140c20000074a503d140058043c403140c25001400d00181c1c44007414003203070120300030001c2c0e602c00844142c9142c05000c001019010010080400080000114410401510b40301240c0c0b040f1035600b2001090010308070041005442c0c401380d04044e4041c0d40300340c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 970617347 1250 970616097 970616117
    0xf0c0111070608101508061203040b040306093807091d18030a0e0f0f090a0e0327040c020313180204050a06080a06122d080a0c02010e100e010807 64
    0x211905c010794076030380d580004440c4d02c10710055191200c21040c042041c1c100541c24142441c98100749880766201c014036045d5903010045c1084101080200c046104481c007202400c80341005400c0c0b0365094002401c1503d801002444c103501400100050b50080401c2281110441007481c080034001b400440380100b0064200d81650403c0009100c101c600341d5516000913000410f02c824010781d8418244901c9048003000300d26200c40d000142d10103020000462114500e4100d030742184078002c0350851122070030040130141400c0b0108d401206800b074a00300452854075004a031079000d11150508038203c1181c00700128428a1065280c6061510005242c140d45800268131101207501000c041801c001c01c0003244e640512400009201548036506043c01651300c00c421071462088100303004080c12178200f521020f4088113401a544003003099941d40c41d104001c1d00316011084101e0000310000600100744c186100c80ca05112440e803900d0000f12041401510b500c0b10042000f0200314010721 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 970618597 1250 970617347 970617359
    0x408030601090302040c121409060601120f0c0c12020f121b0d110f0f0c101b14070918021012050a0f050c12150109080f0f0c011107060810 61
    0x705801b905203607a140c40c00c041c840e2840da40c083d42c5001c1540c45007c80c4000400c01c0c0740304c001c100183d010000340b1b00160800312080220000b001c540b50784da0441460090700a9840390400d44020006005801103081c0103a261012a91a0311100100640d9044140040a03140c0390b04050910319001401e10416883d04511007407400301340b104e01d46c00007070000c1c2e61701c04910b809002c240c14610360701010b02a846c42c0102e040c0d641c0ca1a1010060149406003a008411031142c0ca00d1182840c8003d0005e4409907a8141005100500400403100740070300c0c407001030044171a210344586030204202e503181000d19a0200100b100c5110308510500c1131011f85030710f108056119a40c403451803c5000900b20348100c0c030020843d2402403200d0400c000400903d03c1c44a02002c8403548245944612141c0d040d800c1c0048400254039071207840140f042030003070b01f4140303c08144008412800c804480b802c08228004542e0f0440e0b60780c0800550300011000d102641c459910b9907801420300d0070300c0358100d039124 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 970619847 1250 970618597 970618601
    0x14030c0a060b190b04030201050d0e0d031a100e06030c090d06050702150103020d17130f0503010c1b08210a1b18170106030c08070e011508040803060109030204 70
    0x11404407070203551580c0c91502e03031a0402000c0d8007443d099566400c542d04110031041503100c1c9020180c107000d0045882d01412846070004901e800d60b260036a5001d0b05c07982c1c400b40140819444085d01881907002141140c2170002071115030355410380c0c9a0094401917818050694400f9001d5401075030200f09941c140d469500e00801ca49200f50000500c900e0015002401e150440d009405028a02c10040015a4070a0361031451a50000080c1d038229948402031605803041503240b00c81440f50031340000d40d5100300810501100c0060b0024400d04000c444c1c1242c03c0c01980402c018000e01502c40d16020038130301c10250406410f42c1c9081c40006010441089020004591803410a41c40749103244241100c140d0030b000380042810170aa1602c020001c0505020030f60103598440708058990004801d8250040f074029600055018a000d4807a214161152050b020b4a10070302d1f8840000100c1640e4000d486559849558a800d80c58a640c0e480840c981e00191016040280d04040440941c0ea14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 970621097 1250 970619847 970619863
    0x50f0c030f041701140f060f030d0903031d0307120501111812010c120e0a021305070f14030f06010e04050a052712071505010e041a0702070314030c 65
    0x60107035141c0303a43c905007802d0000002e0702515292641400c4400d03103803651100080303402c600422550009507883c040480c841c1024002115898401e0b0305151045941240c0d048056900a0780c9a8049282c59a59080a01480380c00c0d06c0d05a4032115003084030401c50210202c80622940000c150440052944951030b00301d080c0340b0342503a142803680070892518001c2d840803440410002c2c0017010004001409843d140c09000c0344c003c0c3c803100c10000c694400d2100254080d4010000404c00c40c2e03000c4440c00821049580701c4c00700d0071000b41c030601d46021b40031b028000004110341324950394510845050b4484060402414041c103450038902c03941e15402105d11038164100e0000d2680340200d400345048030004408001c40d0350300b20f00c19514400c0482c0c00e50035068030f021096903850691400e805c18180042e44c00088616120020a030302c104184154080e600410f143e04041d1100c044014a003801602c11101503400804100005030005130750032290410401501e08001000c1503442c241075007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 970622347 1250 970621097 970621117
    0x408030a030605041a01090b130e1501230703120b10020d0e0d11210f010e0d03021206040914010e16080a150e0a0c0e06100e010c0201050f0c03 63
    0x440b071040c03210342402c0c49654224028401040500c0f192030340007802401e000d0241e66080e10780001c2070100c4d10840001c400003081d11010001e0039141241003244054003ea88060020f0700b213140c890019402840201c1c10007858108641c03400e02c0f255020740340c01011f450104040e50712450b170b9a05c966070340190000c1c00c2196801902c004418080e004103446140684540300c5c2d150b41e0320b054003040c9511301d100d007000f8043c3e80410141e40030000803221104003600c0d110047c4a40302040c9407440e01900300e0f0341c9801c4a1402c403500410290800d03030603400381c2d82c0f441f00c103030280e04002a25450240c2000c2046405011901c0d82040603000c207a00351400004400140ea0000c0811805031300c0303400c4010010090600a404940c005540c2c2900c184c1101894039036240e2103031280340c1c4864090108255039a8850108841b20395075001b42c3c82150b41c1168800e2046802034118041d450103444000c0403017105a4030040c5048180c1c0c0196402d420903030528101c03460070302103088040d00400080400400e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 970623597 1250 970622347 970622351
    0x10b190207121401050612070e0402060d0213090e0a030f1b02040c020f07050a06020a030531030b1005090c07062009120109020906091f0b09030d0c050601060f050408030a03 76
    0x1c07101d07081034203460f8081c0501f0300844030313400406c5c0040004501c00c0c05581e4034412600c4661a2400003500a00503840c8070607160384009021071104036030407881000c88510960601c1b007070a040e290070742c8a84400c10081c000c52140e03154400918842c50141d10f0010061208004440541c1c000c28101c1d0b15400400016a0040a500701d29031400c0115000800c42110b040102d41d040420094450a140b00d0003401e101c030125101c010041c0600f1056010641804002421340400e4078048000009100544016000c4400702c0c4460070399480c5001502c00282c030500d80e40d02e0b980340294156108260a0319116945e0702258181805031a584075910020381c1c81c00c2d102c400f19800c00480b004140001003680e858003680d540140c843e00000c43d4449800c0b02d2025150307455188844085615001841003601900000b090448181d400307400c4003a026011600b54400301581503520700700c003500281080d40458010010b07640710f00c07050f0107451610707c0e01034146503603400000d103150080c60f2175801280d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 970624847 1250 970623597 970623623
    0x50907140d02030a030e01120f050f060f0907080c0c0604050c0a0816050405060a0b2205030c15070501141015030507051b071d041a010b19020712 64
    0x4541040900656041150280320788045580080e0b500c680e052030040501c84006a01c1c1d149030b005040b600c0c40d414a0746400e2011031007008141001300350449100c0d0120814102041d014100f41c20182c0321560003504109098880340019107881400420030102048104450b0001c01c0084c441240668411320043c21400815410044001c8141c0c200c031820703a0005004e00031100d980d49030881114000c0d5400540d035103c020108181003850f4008194410b4005500f0001c00321a403284011540d80b10310a844140d1200101500c8003d9903000561001c00020318100c003d03681d50081550a10610001038003016400025031604800c40e0600301400050204006840005880101c0034031507140811447c602900c01070840d00030184410300c0740086914405038690104000000380c040100b0703a40c480844014441245c3e2011541251780b0300204520728124012005240d0503152503000b001c1c20200b01140c0501400039592200c0e045101c1c00d400082e0780c081c41d034007690646010304101c1c9244 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 970626097 1250 970624847 970624859
    0x10207020306090105040210030b03030d02180307051509011223071b0b01060c0c21021908070b1c050a020306040b0315061017090d140901140309010f050907 69
    0x4400b000745002e0481e4100020400144d40b40c0c3c1d80c0640000603420700040c0b180f40e0001103451800f45200c1c00386202c2c4001110358a000b090300404401e50011402c46520903112030511a40001d210220030b4807000c2031000030303181d6024803030b034505040c07005a000624554038044c40d501b1461454040d6094010b400612503950741c0010741768145100c024007840c0c50740303032503036007a40004c0e05204074030422a8003000201040111000d1900801010f0a2003210607090400c0e11080c1c002d008080703100e00961508070322000500c01400303044076004405005014540400341c1e0480c1e21469200c0c00380d40a40060441c1141131340320b0640034000d014801a2607103001418407048542803a5914469440383c1c5a4808440740a5407036544007800399102107001104c80c03002c5d600c64400d0346030403080d8540301007004000380001034034142454103507890070703220201005603143e030303105000100c2c1c0018006c110300425849158001c44e000102c0304000206078100e442d922084820a03203030310045800c607107010026 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 970627347 1250 970626097 970626103
    0x2d0c05061311131805060106090e09071221030b0a230f121b01090f080c06070309031a011403070e04060e120714062206150f080102070203 61
    0x101c56001c2a4651800715240c450410341c5104007080351152500200c05800c0b503030710390405011000b144000c400d48040d9840e02e503841ea1001d001d440c0014584032000101000c81030701d0180078540e100c02a020760782c20a001c40d8100104c0c0801600c0c1c2101c0c0180c054051146000c0919180780c1c0e40c0c0c0d0001e000700e00340c4100f14400b178007580210200ca19004810100c0052241101803211003100c91200c66034846001c206410700400080e5040d009005030301c201006c2c0380b214030981d030350243e07104100c02c1d466250020120016025014180c0e0207801241c86900b009030040091074068280036110310f54940c2c0381038009004841608a0ba001400100f15031008580c44087c241030803000303440c0081c20400b54403804040103101030170043d1035440451044400388100c1148114100d8410b60701c05c401e0400441002c45c0a00792010f030700c22040003030240c16141c04a9084541c0102152001e0052600d0f0741c1c018152005080b00403203c00b800c001000211448244020031240c030002d41c64203054010035013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 970628597 1250 970627347 970627351
    0x608060d082d0d0b0f040213031212020f130603060815041104110711010804122006011404060503010204290c0312090f0f0303072d0c0506 61
    0x20003000c2062424001441140582c0c900c03400214000c500c45061422034071050300202c1182480d050b00189500820b15141c0091082c0901501c0c41e25215804900b0f1100b2442040c01c0300c0203070b45860b50144002540c1e0000c0346e5140c601440c200d00c03010103644450080341e000038a1541040d200040045140655031703428002007049003070800c807680c03405030400d442e070303114144a4007a0b1401100150130040000002825900007070010441e031410308c1541451a807216000b510401e0100c3c1031003030690b114800032031003958400721144c07c1600b64141030707071911019441050a0b07800e007a07100305041801c002d0b0341c1c02850780c5070000c54410070b090284411034200307030804c034001e90041000780160601c2a600804081c544200841c407200603070340300e10320750144803690213031801b00060340c039618242d082521303019501100c02d80f040a600003498603524403182401c0c4019030028030004840d01e004000c1c000301c445002040707424000102090890f07c03038400300d6140c00b06500341c00c00420300c84c00f000380d59 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 970629847 1250 970628597 970628599
    0x1a0f06010f11060613060b0a03050402120c0a06030902120105040803190b030c0d030219030302030f0a050f0601050a0c020d1a0709140f0f1207090f0c121a06070b01060806 75
    0x200c03001c9104556a440f0000100311070b0081084291085180215500180c014000c60f1075007610b6007412000203014020540c5d040c1d22518a5501c000041000401c10000c14400103141c604124a040015000b510f0042070a076032080c00c40c040f55800702e4080c06000e10031031140240d02c0d070381c1c81e146622070006d50344000700aa40c14686040840d2a03103000074150010a811501201c1742002482e0403450104001245124038654400890070190180c01442c000d601c510f8101c030040e51070141c0300d4100e030011154140c1001d411000314500e540903100070040d60315079140c035052142060700030880b801e814520855449606c040c000c43d00d04140c601c40b64100030a442c200c1901840c6c4245030b03912425201070303d1b10038140900c4120481c1c3d80c0d0034a41004c554041e050381c0030b2005480030aca031075402038030444c8130017810038100d041c1c000380920920501c0882601e880f01d00c40941040346000b0311103401c020007220110380d0000500daa4420180c10014170038103000200350b040820041007540050511 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 970631097 1250 970629847 970629857
    0x3090b0403200d020c0603042405011a0a1b02040612050307020a14030604060203190c0e01080c090109180917030403141e03131203020a02060f040203070506071a0f06010f 75
    0x4401040d40490000655002101d0040c3c1f29140c5003416000044115038500c424100700c030700307001d60364840e401c410f04030358420700d407001c01c0e07074070000c40301c0b160301c102010980018074160903200c16094000c4050035083c006040000d0250716819400403400903041e0580b200c0e400490440c0461410300340500241c51201440007040003850023095840c0e00c0034000174070a0ba00440010307101c07201c3c2a03108000d030507405024840305038034800c003400003444600000d0002c0e0807030380047d00d526032140c11100b0011040e0341d10340c0d0180c41d1580340407041e5041e01c44044e40b140c640b008000866044040161184c01103a101c1ea070708d0134949409044a40c82d181d403a00000414004255100c1c101c0b514100d03180e014941456a9940d1082c18200400c1000c6d0020709000c40034032100e0845030316501400c8040082d400312141c03600c5402182c8410903080720300a500d13074800701040c0101d08000e0054100c0d140308900f08041e620a0440715100e00380704840f0500c01010220400095680c000c0000101500e03500300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 970632347 1250 970631097 970631113
    0x406180b0708030c0f070b01150201050f09100207080f0d0213150c020d02031e0105010f050a05030d210504201906081003050304080102041e0e01060e0103090b040320 73
    0x10740ea54500000f441302c2c0d0400c0000c00d8030068000ea9200304c80006901040101c40c1d07607102e004000b0811105440c010041d8601000501000e01d8241020300030307003001d801042c480005502c010040d41c080716003107558000c11320500700680c2e4007402402085540d42009070700c541d404c204000c0403400907804984064840d900007843c981c1c0001d940e040c1260144c0c0c0700040141c481c00030a02c1c0000003c0081003003042c403540d40030104019401641a10300500c01c08641c0b60f0740f8803c1000300308250048a0f07043d00720480401e0740c9401100924070300c41d031405450802030481040e4001302d5008840c181c03192855a0640d9081070340402c000c0300c060780126002e641440440c402c0540080b13960250400b40b103075410116010005068840f40215449404c4070b1b0707180d440750f103014040e420078441c144440000440d1512503200a2006030250745d502c141240ba40e070710740a4101c40b00d002d4104420b05043d80d074251000407030b4441200b18400c3d40a40c8401220244d5020000458080404000b80c0c030380200704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 970633597 1250 970632347 970632353
    0xa0e06011805040f0f06051609051503100f0306321305011b1e08010509150616030e0a09020301050a030b0a27032309040203040c0503030406180b07 65
    0x303001d0105140c84540001e02c0da50f01d24050501049022029003069051182c190801030f464110310702c1102090100c1c601c0d4601e8403c252445039450062540c400810b500e10802803400700040c41d44511100315000c5040d41e40d001e1040e054080740c0094403030f06d4070750300745141d001d008860030814030300141c01e0046407c0c02c4256900084001400c504210801c2040c12000d021094100d0043d60381006070006d0b0f01d26582c02d0161111030740030407658031144030b040c1c41004180034290050481e03802503c1103601d6540c607801c4185260012200c0c80e03004800707100300d0701300b0031301ca41502644a10075100c6440780b003d88000c0040c003182c10b0703200e0b58641d0300400060019842d840700c0da0341240c1d40004560010340765807030a40060b200002d00000901c051036041c8852921540b242c503030440c0242c0300c500c42450180d101c400280c14045031218000d1042014001d00d091950003540e001d40110040340016844100280c1107500682c001c600040034000d030030b1301c4507541c0703041d0310001e00d4040020381c90080959 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 970634847 1250 970633597 970633619
    0x306050c030f011202031c0e030601050303120606071b06030c0215070e04020d0f09080703170603190f05160f05061204242a05031311060408070e0a0e0601 68
    0x4020940e0413461201c006045460800101e02c40e0009010384000c203425102e4000d02c581280e40302e4901c40c0c03043d02d00004050070301108a40e005140002c1c4948141d4a803424824580e029480c201c441c41e80c040c1d20000039400c41165080a881c5560b400b1070056441d0380700a150810078100a60403006032003e20101540299510603100c80968001d80c5070800c1012000c020008203600d103400c241084110400c001c0250000c01403148691941b1072401c94882041d10049021680103415510002f070040c04c031000709143d56081817144d0b070702c6080710070542d0340d05040010b1340ca001882c0e8544094203115401202c28404c0c040c02003520140d00b01000d00da082030b403210f030107000545032014680034003054200e00c0707031070401c01c5400c180c060140d024225030a00042c201c0f0f40101c1d121034a100c8008290500c0745040700e001d040c030040c210f07082c48801d85608800705240000075038003420400001855410038070022008080e440c0340301300103181020785402034075586103000c40160400401402100290 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 970636097 1250 970634847 970634849
    0x414070206040222050c0403021c030950030c061911150105010e010824010e030d09080601081c0f0311030a09060b031f0e10150306050c030f01 63
    0x1107614040d4104d8450038599226140c2142000c0907080000300701016011000820032248240d44010f040d2802501c002801602c501000b000544000b400300007942c0e0700d41070402c810a8401034100c201018440074440f034480c2094994540408098410711b40071864400c05200c4019409080702c3c207089030005510b031183c600d50702084103034520340340811440744180d01020481d500494450040c00500100300c620241302d4140050a4903165004551041e1070b49030081100d403554507007460001d01c0c980b0480f45900c0301107041240710b080c0c41559940800507000000520b46480050701d0a050303c160800a050304105900d90000c010003075034003c0c4904922132071045107426a0580420b241c100e025045001003501c4030314010061180d0020154401142a80b00d42d808220b8082c1410526413200d648405209064404403000300360310b1070542254070480c0303030030054071078031040344105504a41c00c2c50b6551aa58541c0034007072040184921600c1e40040040d103d403170461414583c03400c01e2001c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 970637347 1250 970636097 970636099
    0x140f01060b09010323091b01020304050d0b04020301150f08060a0e071e0909061d07140d1704080309190f03020607082b06061106060d050a0c060e04140702060402 71
    0x81c84420781c0c642c0000d1074004010003901460950317642014101290344000c0d00244201da0540d025454505600010440c0c044a40103021040100301c140c58081c010280203000340e8041d500d41c0d00e1424040c15000404014101c40c0f80d0b88045181000110361406400404c4810346501e015102c00da42ca0002680204503200401909540001f482e1089403e010941c0190891418588140200541da401088428441401c403803016030407813255595a0482e8403d21545894105070051380341400d0f109910911b0240d121400b0151030405e40c020107920070f92154039680c0003ca41d4000d40d262a035018864a0200e014602a250516400c050620810700c0000d2060800180400801c411901562610761002050220403082c80d25490503c0d20080b282901c2c4901e05500412000e001e4502d5512086145e40180500e0340c4082c1800040c0800140686041c0309911410000a180440c424007a00043d55445000d4030460203001c04d948100342c01503503170301149042200496000894a50241d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 970638597 1250 970637347 970637351
    0x230a0c0812040e010e2208040504050c1204110105040b1206040b0d120507110603070e0310090305090d03030b0d030210140f0a0f0e0a0803090f030a05160305040909140f01060b090103 80
    0x3516046daa43c0b01c4024004442c1514244d051642400506000340086501c02c0e1010f00c004e50300c002c2c210905114442d800302e283c040c00004140460200c14600340300c2c50040c10640e01d4075403581c095801c10303000301072a85250b8030b08404004044c2854094132080d10800c8c2c13030300400c4010650b13642c2a820180b401400402034007050329014400c620a0384120b500000e0091966401c00400c01004c4031180245140244114070f80d0180c0c0a410784100a441a01652014104070546040125840028030705904045d2110860500759841d110f501ca2054031079001001c00e03c545c9030802c03040e5000182041c00303644002080251080f000000740707500a140381c00c0041c440c10307683c1106004200e4a00060752070f215070b2050404114800b0010360060001c2001c1740c0bd01510307010202d030b0381d01c034041d003d10000e4002d2044268078a013141203003001c140b080c14542d08164840c04140b00319655060f003a1400c007c0251400040c40080c0180000305480e0030007880b08509000c554503c52107004c82c407504140d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 970639847 1250 970638597 970638601
    0x51b0f04152c0f090f090d18090b130501060206071107060806211c08160f0807030609020f030118050603070612110a0f090f030201020703230a0c0812040e010e 70
    0x65651a051009840f00401580c0107051031030700c0f03040d4010202d0704050b161280c071502a1a044c06211b080c40c900c20208200180e640c10486081c0240504980940d04080c0f000c403110008245801258003a00c4283e00074945c910704201c0090a464040d118200c0640001c1010310004d82d000e00450380c01070083d00c44c2c0407141c0c0b0610118440c0b503000e1518045e21f020701c440c0c401e402c00c0c144001054020403561030f40926118121000c030211640886c1e0f8003c03d000000601c9441c3c06012811f074010071034100050448d82c0d40800c031302a82d0194000f17080c40c1c0c0001005005002494041c2034607803403608810030003450b2440111382c0d070b89941d0040c5c000340000c1a407100c43d0000c1c56000341300302e01040c4040640310703400c8120140c07141c1d68125103c0302103480c494000c110f02445c50354060881e50140d00500a462454540050305501d8800030008618848110078a0081c10040900718071310a0003030700d5a0b42c3c584001281003e10701c0003444407240301008200582c0a100040c18152075111425550903 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 970641097 1250 970639847 970639849
    0x1a2e0f0e0c090a0303020c03070515043609021518040f0f06030501050f0c2803060806090a02310b010c050d0c06060e07050d051b0f04152c 61
    0x1500990403220f0744036030000c0010040541c0850f800c01c40440035001c44482d00c3d02d03901084050705416a1764921580300344400c200d251802c040350300d50501031040101c000c0d00b4403520010100c40100594001c19151483c40045040c44005c0c11007a0814a28941c00c140b69410b00f1607444286072a80c500c40e50f00c45240c100d407140198414000302d454410104140c55503464918043c1000301d07496603e0281c0c4000017501c1d801004104e48a803401c1c80c9150301c04000c44004110b620200502d400d040580d5000081404801000f030240503000b55070050240c1880e40c4108a10042c08e0300f5500102640401c00394013080c03400c4d01408400c6400000441c00850f02e5004907112404404d001d481c501c5801403503c00107800c4020403401e1405118284200f948864240d000d880d0260b6004000860130040303091207245940c80b00750000c803103181c5403110403413920041d0204e8001c10600c1d0450880010100074960a0b1f039080b0151801c1800c103132864204004590804000380181d40541007002545040a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 970642347 1250 970641097 970641121
    0x70f060504031b0b150a0812070f02041a0906042f0f1308010b010513030605280b0102060a050115080a0b150403050115031106071a2e0f0e 61
    0x44102c00740418904610f242001e59a440742610303181c0340e100346407071240a130781041d541d0b04082e01d5444008011741204c0748130060565220b20801d54118541c0322140c0f00594580c0a00d2122600c4400c0001c242100c200c00c105079402d0241c4401d110b03178580394905840c010200d0070000c0171450103c26200b000d407904002c60a0b48280a48240b0480002905210303106118030300205441c80c1c0d40082110714034002c011741d22885145514828006640c40810008202d0307040b081d0301403900c140781d003010420b202008031f40d040490070103035401b900e540c0014840d5a0400403a58042028442440766514246513060031100100e07100d01000900c40000e00d0305021504000b8001d140035108407540b40362500344004641103030000f110759500304130440d5000c1428070ba003101500e8002c0b00b00d840141b040c1007042034551044400301c852403500e0070314409060600006c00c2c420441c502260780c50940c10042c0601070031140488041c42c003844002408800108000d94050b80c2030080c61000329103545004031a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 970643597 1250 970642347 970642367
    0x301090204020d0615020106061b050f0a062003040f110604030507030b04060608010e0c1318110f0901080616030921110712170f0c160506070f06050403 67
    0x90000d00020b43c111515089a01c01d02c01c54181144020a80c2d20241c022800d86100c0c0c426000041c6011618000c10703901c21440200c0d60348034200301d801170140703141c555091503250201511900e41d25010300b09031412813030b083c101c10804581035501d1441c09903a004420074541c88090310004094002c8903098882d0700850307001e5508030003100c1603603540e0b1803c450300c004211801c0b00c140f402d104000a141c0d00500030003005a03034240241100c00800002d0043d201500000c40800350384400c000e641c100f213441000500c29008031003908100610b0028040015240c22042d400380100c0c0004005031840400d000e41c015003004441c1d407a1400200c030071405001c840034061b10340071184009102d07030100c070544250182030301d480d02101c0400c034045d015203c0304a4440c84c03040c040c0da200b04c0310009004540465100e640032290fa402c10302c0d511100c000710b03040205428056030000940043d801c0042c0b07141c00050400b1945180b03081c1180c1d681001396051998020b1240e5118400300d000c150007030a07001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 970644847 1250 970643597 970643599
    0x5180604110409020c120a08040b0402011202040b180306070206070c050a020a060206071706061605010f0c12051b250b0a2c0d0815030a0303091b0807060e03010902 72
    0x161266243e5a61000a51040d01424010302c40c3c000c405500881d02419039580f40045d80310354490740d5503511030125111004000302e041000c2c021018207c010b451000c0c001070040414840d0300c80120030f03440d85104a01540240c0b00350701050421542d15070000380c25a001050380740601092940b442c11a14004543c0802980450310b5440032403083c6d8000303001803150003290b0741c034040303d01d405224003411032050b10300c1034201404101c0c2027013102e903100041c1e00f07040c40366000081c84498900d94400321030300304c040600022131004000800d03140e1401a641c0251007200303510f1951034058a058094032990b50003520b80f40b11075900900d160f00401c000184160000705c0c0f46a0b6103400c101c81c4005160f8202181080d9580d2407028140c548219100c401c58a026401090030095a2800b070b035000794002d08203405402024403070030303660f2400d10051140c1c138402e48010440d05020314068000680e0034100c40562145c41400700710744180011000c040f54214205082a8002500440e01408102d0b0010b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 970646097 1250 970644847 970644881
    0x1502030f010b1810052106060d0b03190302070e0901020306060316050702030a2414040807021507051c0e0123040521070e040c03110a150906081005180604 68
    0x11a400e810500420081d141400d06c031140c000c070360800392070101c801d44689801c40d100f8080c42d0b03034030403448d4084815000000c00f140e40c0e0030090310340c0c0328112110301421001600108010804800d40b40101da800008180007035066141200200d007640c0002880101921001d0040d4640180208201c0700015006002d40b042082e0500b401215624075116209a01003402d411b40e22000c114440c1d44001c111142050b0041d03211502c07000a190030908050741d110b0480c0c03280e0668880c0c0500144200740c450b2010b004564100c00c0103154043c2c1c216808010300c00507601002260fa440710b00c184105416090841d5042c840250614881c051a00150340185170040080c4042518031441d00804100303404603000c040d00c40c07407460305004090350000d1141e84076100610000f01015400a440c0c140130b401d00c16000d64a040c01c60340078615249140100740d6030341003800300c264801c0050ba4014048845190704a02d401c0208074410350071408407801009a40101d440c40d0b8580d04100e90f441d02038005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 970647347 1250 970646097 970646119
    0x103021806030c0f040f03050d0804120804292202010e0f06040806040302010f06060f0e0904060e030a020c1509010c060f200901030b0f031f090507032001080f0601030f0b0a121502030f010b18 84
    0x312000c13460fc03d649590303480c0c0b40f043c000c4480d580d030781500c9200180d0695031071031204602d405101e011684a01001c1d0300036020b20000c51384960800c5054402c1e0b000303074004248400140b01e21403ca500070f4000e070040003c90950a0201e070381001800d90700c082c080c2c1d00c0c04441d039a242040002805203140c400040c0c00002001110242d0020b24424000800c6401d590f40a444a81c8800079109428826010480302c02c001404601c46a000ca040c142020002080c44803401e1401c04801002a046009081c030202e03150140c2d507418400d543d240441591840d40100d00c01001954034407510341c10303c5094a45045c640001e02c0b041c6c01c0070b50300c0c1e80e0010440791101c1c0c91345042030178800760290300e4120081403003e01c8140e40c461f204581c0191013090720303207043d900c85a0044010302040c031412001c098036600a000c00d0b444e001e0300750300101561050fa8030001420310304800e005000c030f8019010280140705110548002c00303149030440700032000055a80780d0740000880d00e0001d840f00e60ba4040000c5003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 970648597 1250 970647347 970647413
    0xc06200f0c280302060a02010b090408030f06031f020901020c1003021b0706121107171c1505011107030804060306090b0103021806030c0f040f03050d0804120804 71
    0x280c55034912021902029407500c107109008000c101568192100c2c1008802003001d428010020801c0407050305c004902c6a0078400803560707140302903600f103460303078400001c0001c180b4003060025003115084000d0080078000300b2002d03032034910080030311000540c0021a180d10768001c10a1035608a00030384140c0110b82c603a00003800a400546030000814120f03040080d803c00007180c61419250315071556180c48038643c481c2300080203440802c00002208012540100e00004009140c212083c9069540c0c0c0961102d0f504c425a00e001340381e050030b4244049185081d0103440410141c0d442031804e1490044030b070081c00d1410740c16510180004600003400318110b03a01d174120f074050341e01c5403805124659100004604078030400b01ca01c0b01004400502d070819260540055030002003c06d41c0604003d811000d491166010344d02040c035107001e041c0100100310f0240402160700e000f60070038221614003900d4450111098401d0041040410400102008103140d64160380c01c081d0020403451003601c030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 970649847 1250 970648597 970648603
    0x13051206060a1203050409020703170907061b0c120f0b0a02090f01050c0d18050a080a12080c030705092b0308090318040f14071809090c06200f 63
    0x341e256802040c441e44040780507200d1a0500d0100342e4180d0b01d071071030300b850300e5000300007500b007500210208400480d400c500e041501072014010480b400c05041018a40400605544106102c480004a02500d0030000c611400c2c00d00781100c130300c640160401c224030301d01450310303003440c8034000c01001c10300042c803a10380344560103051207400540d80380320550311040064810f401000c110000a40c02482d85841840c414022115103c0b51400952803481d2648002030742c03021183c002801540c81250320400380100040500391515581c1030002c0941040b03592210715102c020700c4032041c04000220741e44a5201c8040060040c510011149450022050881410900244154001141403020841741c0a022003258080c110300301420035015054000d006c040e04246d40304525190b520031b40b0034480f110080700c0611800042d03a45c14000c00a40c26503140c0c02c105600101c00300c5181088010018648600340c0d410b070f41441c01c103200002e440446520340980c105c900103843c2d015024103003030814000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 970651097 1250 970649847 970649851
    0xb07031b0c060914091909020111121213020609100507240c080f0117100c0f090603060e060d080c1c021005221406010f050109210813051206 62
    0x541c1c0e4559510b003003c0104407030240103441041806c2e03840340030000786400c0369010140003417041c14089490501c0019607400c0c12000268520450701c001640303010305000309607295200d0000e1882034804001e60300030403500e0083d500484c5c000e0f081200a068014042c40503640d22541c803241169184404040209410079400c141801960600b410092614001d284031032080031480000b056507840e0822088440c004800c414466000d8841d008a0b00d611318003840316800381130b40b543d954050741c40c2030080110407654010020180391140a201406011009540124003100c0034801610f035400e1a8020f8460307101c141c1d941d4490070000a56082810b08640c0c19142d803030b0240c40f07400d24008440340549000301c500c41804441152100f440c03203290381d620f1001364010240020321005280131580b41c003030b0030b03001044c4074030035004100407a680c040461005401d01c0403813100d6105411410302c84005031410005c14445000c55007016002a9002010003010000c0809071203c1580d00c03003076118803003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 970652347 1250 970651097 970651109
    0xf07030906030b06090d08030a0b060c0601030516030b07030c030f0e0c0307050415030b040f020a0906240e01030b1216031704081905010f061d07090b07031b0c0609 72
    0x6081440f501d51400c4005d072104002d001c0d00c04030044d105a512543e4680c00181981003407503440000340d250351034610107007805d195000300401481d411800e204d1b00d00403808005092410b80742c1d00c28800940c00308840398003d11035007400300b0700041071041900503107011030181000b5071905640c011002c00000d00d046030a441a01075820041d1240c0500003030303c0400134040c0e00a811403000304002440f0390400e03a4410300800c01c442e1040a643c0c000341502019511158170384d6140d04042c4501da02c41c006030136201540f68100c00c010030307402c4000340682880701e0380e65040c9507035441d9a110035101d02524003a54000304054540c4c1c0403181480f442c00c0b071501d020640701c18402d0809200d00055100c00c44065443d8031000f084802005070720020304441110048a455480b02842084050103000c2c8801618101d059803280c0da5101407101801c0200038410403c00120710010042e400d050403c0b141d5854162804000d0040120007048240120f55801800600070010004485a01205030380641e01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 970653597 1250 970652347 970652351
    0xf120a031b051b0c030309010804020d0803040b0a0b030102190c151d120403032f06070503040212061005010e0409080307050c37020f090114011b080904050c0f0703090603 75
    0x211110f81c1d8070092018007642592040004484c20340c05000215842480284100c40a621a9660901d07036001030303400b00e8041c9200030a001801c0d440307000e000310031034043d4000c40c14803224103a40b2510110f94891034081c018101c2c540c0d401d01c0800ca0401185184610041c007403482c4400e4000504c1030f03020042010303402a0021425400031350002c843c220703901a6203c25145400d440c80404107907800f405407240002121084491160074450248115107a032078854803854580107101c07120340a605510a5504208204000036001001c850180c40e02880c0071190303604080c02080003004106000b03421140040104000b00e0f5200004218100062041d0b4400c110140302d8101c4030b1040c01c1030745854403d07980c03804c060302a4072106058584d000a06d40022203c00001240d404a001c1c0c201503084400c0c02d02c3c8100550b0003180345119422000c400b0030031006261540205409007030314042c452078540f00410300c20f848036010707140b400d04001c82c0c16030395034030070b14020309000c1c000d20440d40428 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 970654847 1250 970653597 970653637
    0x1507020d18030812061201060e0f0618041112070e011406040311060f0909040b060913030203070807030923031c021914010920030f120a031b05 63
    0x844078040641c101e0398020a05030400240d08801409804020026a003180100000d021810340900803400204240d030304215241c1801d0344011b00c90314005018900400202001781c2c014115111126405600802100201e40b070960009851851200301501c0c0c81c480c421f0041101c0450221080c100e50000c4000004d01c828001230000758003c03440050584c4100c1d164240150403e0740081c500314071640d20a078585103001c13000030070280c025202528440c075000c0402c440d40c1004448036420500317501c0d00301852599598000e6a921403580010026100030811100309401030240c00094040d052008141d000300c0000c58001400c0d1001192080c4603004001c019580d42c1c808400000d800e030380c007400d00c0b03525038200e01130411079964088640d00d00705203503085038410070b00c1643c080b00c1c41150703a00c9480d0a02031208880c0750000c01403a02c80d8108071581b20303002c2d00024910413154045a41140c407104003803800e071700070184c059004404d0141800350001e02d991040c01001c0200c418004a02c20b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 970656097 1250 970654847 970654877
    0x28170f070e04050303040b060f0604030602090316080a03050d110a05030901110a17090f010c020a0302010e03181e130e16030305031807091d0f030f030a0e1507020d 72
    0x103541c25140584560010404500803030100900d0a80c080030140c80c5040025200020503601c0c0c1c0103500c150f89642d80890105200e190500003072400d01c245449a50b4400d060607891516283c1940c2c005040c424000344107801100e160308244d600d1741268400c0b6481d6a48804081c040758070441d8800d125528040c1d102e5034031401c010a07540100169a101030741c0380e102c221900d01c01c0f0300c0900706081d68800e1090307844401700c2c24010054100704503409000350100f98a000307400d503403d10801c0a101d030400d1000c08032055900e00e0108001d1011a1790011070000020052401100c032010070750000c9140c2e0001300351000e03030307007107210009048011123030754140d1103403100c15003031440c040180054000c00106007095500c4030081e051103d06015103081642d126444411a03103080d00c0602d140105000090785e008042c4800354202e508440a10b160548940c8507500511000b0940c01280d942da08889100032400c00000100e00c0c02c802d8424610b08000c20301944d25803200c046200003840052242c108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 970657347 1250 970656097 970656119
    0x180318080304050904030c02032b05031605030601090306230c0703081b0405040e0a0605010e33040f05010302040507020a0209040f06091e05010f02040528170f07 71
    0x84030300c1400a0340c00c1c142841c040244402010b031080d070400584a0181001d603501b03001c01c5228104035001800d5021070442d82d8420720314841c8022007401001d00c100010342e40240320324100c10700070b8942075036245c0d502030050780c00034003941014107418a0014800010743c05401c020020390600002c08206a540b80001c0d00c5901c80d4a00c0140080d500e0400f04811100c81c030440800e2001025201c0c1c1016150000308003158400080ca401e0356111007044020701542e40315844c0500056110721145d442e00c07140d1788000758406505996495503040c2070000010f52107200c070089410080040c0030020010f5241e0300904401c0c041a48a1443c040216170524000178940d010350341e0140512a850342d55884016072500a1076043c4c03207158940c40b030342e0300189040e01c0600081a000f03500020b0f250384c03801d003c2d003102c50342c1c4020482c0c144104410301540d03403210304405d031000c2e12880300c034080c104500c042d180c818036542c0710f00c80010041510303601480001c0740340445040d8403412640076135038031028003072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 970658597 1250 970657347 970657349
    0x5030121020f04051513051906120b07020111030c0901090501030b0d06230f04110a030f2003010f020a08370608060421020606060d020d0b04180318 65
    0x54400c2000701e103070b100c90400341c204943c040c656202c0248804024004a0000d911240e44002d071140d0314010080401e8404070728030107412042400b046040d00f014204200c91000c15800752036444c100d070010b01c01d14400d420842c04501e4100714151a0f0a18404290050700001c00345400325440c10b402054075486441845003810000300b980300011034581302c03480180014005600800d8244041650800301c40280a00440c074080040c4107d1030141000a048452610315520030009003030704002068001883c0c1c0b0303000d900120700c1003600b5421424003c8080745130341c42d5600f40d420102c4c52520b42509601900d07070210b40391120b400561314803002444880b0291040c030303400e0700c5441440482c1607041d0310701d0751f10030300e40540002c48a8440c6085854141d003200c00700e855159605010400c0180031101710044c03141800180402d0410304001043d07800388061207a01554045420307481e910003034006007078a00d00a0b2040104407055108064140764072501600441c01210700003c4032030740f00c49508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 970659847 1250 970658597 970658599
    0x613091b08101116060207050601060e0a120c0608070315060e100e030a061d03040902071a060102061914092415060901030605130c260109051f060503012102 69
    0x41e10b03003a072075030210700c00900c4d000c02501d510f0b40c2030002c000040c00c01c00c5000e02030a96070312849010f003485410402c558480da00009002c040403100040040e00e50700f00002521140d08050326181e4881c101240180000e100528188000c41d1000036243d4111020b01c40d44281030b0340c2901c11244815065551810551140360941c2c80074240002260040d07210030b0691000c030301e01e84800b29940c0e4119107143c03c00c0c0c010305005a800151081040414500082000516504004581741c0a0700107511018000c014203002c031030f64030050074090b01c640c1c040c840203859000c540071a03041201d401662085114080041243c0c3c510035502c07228070082046208019481340c021a981060003840441d42221240c0d6051613100c1d82c000c2855922030942d03075064143d2242c00104140e000c1001040300b0241c5c90545101d0802b042480220b20014290605480034444d0100d06c40d00c4400381c55450700040454641420411840841c045610900440c12201131000018045181555404030440c98110003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 970661097 1250 970659847 970659881
    0x606030a0c0b1e03090f0c30010b030109050f0106080f1009030315090b0a0509060a05060f040803160302070806240112020a0c15060803030613091b0810 67
    0x811840740034038020b01500e802800031182c4070042c04030f920842c0d0025115001c15800603500c01d402030204006402c101c4004645c0d481d0804841aa50325900329013410154060005801d07440d4004070075080114801c001174020050b0000900b04a52190072903800122154209000010340040005942a20130800805010b0f0003100202100007000d00b9641103040c035440300d0110f5094030401c00040010010004040381e050030000c10002d0450141d00a1842080c084041c8040c0c0d48408504c20150f44099805594881e84190003a825004a40c41807043c0d01c40051940704424820300403c0d1502d1280d001c58504517201c44581307840b2070084820314101d410383d00341003485540d105182442c00c132040c1020807190030301c40a41e000766401522504042000305001104101e003d250100601c182a9001c001c103a041100305602c0b8440541418440d01d000c140050b42881980e000041ea41d07406078013403c1000034078441e16424049841281058000c900300f0108440f000d00801d59070348040c9600c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 970662347 1250 970661097 970661099
    0x304030c1403041404090b0c1606050705071b0e010b1e03042a06080c220e1503190605041a041b090b01020a03142a070815070c1e0b07020606030a0c 65
    0x8c5195411034003800401074030040c1d212000c00c141f445000d0082200f40d6540c2d556298604040121480400350100c0f40d4201e0b075410013004c4960001d1506448000315507079074508456425070310290910004500c421300000502040001100a400500303e52282c0904414115860002c144030244900e20108070100e0001ea016180341c0010450040c5400d420f01c409596444c800604240e5500003c02c1c465003181413208512030b00100f034145240031402420900d4031002c10055642ca2b04038010000b07515180820100a026407501c040c60600b011100f5003407a01e410301c20101880103124103088040c141020540c1d01ca5402010481d51060f0001c1040c1111960126070801d80c85a00058101007408400d4030301c4603801407080d01c882126401c404040d0000c000c941044226400303d441c9034031031094a10000c96883c041d941c024418101594109060700300407894942d001e1400d07040b81d150b1031003a01005600e01e4007a0003407005501710380d095900d40052558030310405070042e04080da01c0030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 970663597 1250 970662347 970662361
    0x170f0a0206033102040e1f020c190318050108061f09180623010207030b06030c042a21020304020d050316051903080c0304030c1403041404090b 63
    0x80103641000711410f081900300c030002042103d0100030701c182c101d551003e10400c2d0642c0b92500800e071070140040c0107426555100c0d090b804540c40004080c00d05181c010500d41c40d031300d1003400f00910f580308800b00b0800d50300c070b00c0c40d00400d1034043e8440b00c00c5100603500301050551154403201e10130800900780202c2443c044803d4840f5000c044101ea0421084100101c2c2141c8242c070380c4034a0080e528400f042e02030410048098a070500d02050312041c5952002d80302caa13900154510440307402866035844c3d41c0724640882e09009081410302d402500380018031000741079805549004c0050760f5610301064082510481d01145650b40c0e00010ba50341c1d026180c070072002a4010b5401c40d1005221b200072074210f07621281581c208000418901422a041d403040c0b00b4284107480703030403110503540400032072241d4001d804160041c01e002d000c943d0100c0001c04043c001c0004415168204ca44041c520009280d003070383ea540980541d20440c180c07500c03110340600b8140160312840794400301e85805030380c03403c2e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 970664847 1250 970663597 970663609
    0x1101060e0c0c0f0304141503152103030c0d0b12070b0f04030b040b01051003090f0f0f1a01050a06020a02130c092111030303041a130501050f01170f0a02 67
    0x12000b030298000e9a03000004501c0800042c0000c140103d201c61140e58190100400b00c00c0218840d03503034100c100100300c065260340c40c000c2480c0104440740a0020040e84140015800494030044035200c0002400355009261020700700644103000e040c01750030850014006440100320300040250f000c1e6200f03100d511030100150420690b411003a0b41801e95940311042c440b001036506130742c2420f9205c0140100d0030300403c80c18030301c0d445060034081d4030324595034140d002916400c060030313480c4e0480501d002c100856100000554200d64a01c11038410240f2001c2500000e21400c1d1140003502d40020b0410b00104d01d00c500190010700d2060b06100c0716410f0005400000c2c026001c01100181c0450300c01602d1012105100e03109825000c00b0890303180440e462074005a01d54071039841481080001a0080300c2ea0190202004414500ea260740c03811040040010070010030a50030081082070845621500504a40c60304d4612010112600b4080f13456541d0800460a40d400c104a880090f0400c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 970666097 1250 970664847 970664857
    0x3060f0516120e0309060f0a03150b0904020f040e04060b03010507020c0a030602092413060302190e1207080615040c0503070309050c0406120b0a050c0703030902030106031407061101060e0c 83
    0x1920583e841c014003007000601c1c944c0311f040482800b40c4080390704880030b0b07494862402c0380b40d4004113103403031617086c40464041c0b400b44143c0c01e44074607000181082c030301c044181078a000300118042e08406003024504000582441e0808900139880c0c400000e818600c0060134801458010309000019403c44c0c5076000039600c100e100c00e4000c400304180700c801c4811500303000d420f100d009511a81f16044003401018245182e4064010507005100b940b101d21081c0c682202205480c0c20304014a9005002103415501c80000000300c0380141000014207040104a40740b207826040230005050f0b558408100865059421001c0054002e1000443c0940203500c42620700f40114100e4502200150020f400ea0ba40380d000642840002e605030070400080c105e00390340140701d00700180081c0c0340525800201c1c1c00342d040c01400701500e038010300301135440a5020b04007860701710310104e508000c9800e4403551044688251030000300020b040410311a810305c0343c00265a0341140101c07040d20f580000161907086 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 970667347 1250 970666097 970666121
    0x50f090907050d0c030606050108011a0a02010609020c0a050708160608070207030506150f0f061801050c030429040f15110d090510090e0a050c070b0103060f051612 72
    0x150700780100b403640d1055080280075204116131003542e4154075042e015681164010303414001d5000052161070303001155051140b00650f51181c030340c0798401d0304a01500c280d92000c4003803403000070142c60300540890b80d10600b40c0603400304c3d048207640c1c2001170b0741d8200b0751404c04280001d645040c400c4e1881050005e07045401d030302c125441203407203868a50514005885d000480c40c0d031241414850b05009000100844049580480d400420804034046100380c41c07104aa60400c4050081b490303004500b500c0c04031121808807501e858542c1c080343d03036843c1c5415005c900e201c0007403100e6000000d807c2c211010355290002c2400164540790441000c4246081e0480c1403001c0e03004169103d207400c010449054440e0b940c0d80e9612440c0c807090004036003820155504128412101340050201d01c1c2800303420001c4c420001030265180a41000302d40a05c81c80148250700060000040c05590f40102c84600c2144804212030344420414001c0c1a007017205035001f0410014400c0c100d04100e074008840408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 970668597 1250 970667347 970667353
    0x121090f2406150915180803030906060a031e1103100c260c07030e1e0112060303020a020d050705043e0d0f0f02040e090c010504050f0909 61
    0x4000e50719031410300000c1405100c00310012840c206841c1e0780340a4080108004088025503d1030114010102042070048440c420800d080026581c0c0c892100b8400054440000e49829a110f61541c0e889038000d0f031748400c181c410040032030706500e0269080f03811a60700c680980302d00e078003c0010311840000d0001c01d41364038001c4081c141150301c0a001040b43c80d03148040004034904580d2014102c0307580e400205111009840104a07125200e540e865008103500d05607030746030402032804550310407080a07101d812003514503108900207202403100c007031800240c07642c0048880020050085801510001d40168006d4144401604145c00395141d0a8001d00030744611b5620786020806445592500551002183c940b64a105074082940380c250700d80c600b41403598598030044003140d40188038407030a1555030341400440ca4005544050349010350300b4415901c4541d01c1000c0741801c070f82207030106614014000c29410310740c480c5088030141c45008140140340d6010006002c4242c40080c5509803500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 970669847 1250 970668597 970668623
    0x15130902042901171320030706050a0305010902120103080a0e031f0f06050a05121501090203070f0f05031504062d090912050c010213080f0c012109 65
    0x121031200300740000700b080d070399440391040d0050005044240c40110600c0e284029810b010003011002d03410310119070415018402d4503080c4400c081145a60440540d040c46046800100c0c560003901a140019503914104600d81ea40c1d814442030b0701c14903102c00310095005005100040851020f0000301003e0700d8610841c03150603021a1074130001d86290307440c00c3c0800d04013032610382c000e0003148401c400300a42400183d01d008041030304000540101407080302d2101c0340f4820280c08101003a0714081064102010396036800102009603c01d60341d0344c0c00030b115810450b41087c06001200d822920381e50301c0341d1031683c8602c200480000074121050344181c60b06030000b921002c5e11036510356400c01103022103150019840c0480a40308941c00718208a04000c918070114210f481d03240e500344001c0c101203a4408000c00c01500905c50b4085c101030b44417001d0808921518001481101c4c2c03002c510807142210b0b01e60380103545894071070350f212440e000703e03140c401591400c07a04900038280c45032404c000301c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 970671097 1250 970669847 970669871
    0xb0a09170c10050c01060b09090105101710030b060607121206030807050d08060909030f030709050d03090f0b0c0a082104031e0903120c031b060509061513090204 71
    0xb004200360304000250080b5039541828000e20a02000700300121040e850702c884003002c140410f40c1440b130107205103240c507005098140140d4140140320961240038542e803921f90306803003020866000581b0f048040d800001e140d0700b002011502019040540c5400c44006807508440710000e10f9628031307010b82c551500000080c44800035080040c80344014003605041100000c0503000014040c41c885c008050030700164a10200442d48482000c0200b195240d80c1d0050aa03527401541d409030390881181441001030540c410341e24820785064410781c1862940da20b220141a000b004d400c14a1604141e2010300090340407002000d003445e00c461004060015281e03011a45841103600341d02081c00048181400c5280e201c034160b00004508015540724119100c1c00074441000042c0424403c0750b2a12034145401510f694040d13420780604c076540401e240c602100500811750303002c0294401c20010484c1451111b04288000c0c0010701194060301980e00804c0241c01000410b0b40c120341e5a11f200980 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 970672347 1250 970671097 970671109
    0x2418041214070602190504050603041707120e120c011d0a0b03190605010206150d021906050d0b03010509030a200a1a1006080a02070c050315100b0a09170c 68
    0x4240c043c2c0c0d0016122a9000c010f1401d40400508607001c1040804c000d100540c0c0380015070780c1194120b50034244250260050118921448801070800e0820740400c0f074140c0d901003601079030740c00c0c2a1454060403410507940c80d40c0300c07009411036021415668903443d07002381c800c050b0340c8846402404003400c16514541c610250b401500c44003c01ea180c29505a07089883d0302861008040a1004004600e0030301180e0b24000094410303030b0711030558030300008195500c010307070f941c1582484a4948541c41d900e020284c9503510804880343c0039820b0051021451806108180c414540f050107586442c00c2d0f9482204c0c40c0c45e9228100311f101c4500f9a010070390f03200400c02e040708903220700390b04820010000d07804010418002c1120303840ca411b0390b41c1032001c181d02024054020b9101000561102d00925116a241d4450f8000980512030b07035400d00381b50f070041e080c000e000b14132000340d0b049110380f80e492880261051117826408a406404108904802080c01c615160300700b00559081652101c00220 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 970673597 1250 970672347 970672357
    0x1215141504060215011e0501080c07172218090c0305010e03030a06380408120304021c0506040b1b160b0106030603110909152418041214 60
    0xb0042e8045060b001140c115840a41d0151000d0008503000750f880008180302c900d80c80c06860f041082400c00b00d61201c1c450000e035000142c0c881a104140d170000d40340540030750444410305500701414070920180c04410030480d416218120450343c010910000d402000c0c1c41e40310fa0440344045140e2000021860070304c11000302c4030041c070140d43e40303080400512040d101c190300708840035440c15008010420440c2403420a185113a030140c008020401951141802903504c03004145c007a802c9420301c0e004c10600210f01c12403088404100d07101750350400c01e02001d00100000c0003584408041004942d4988a05a01c505045405840e040306c883c040740054001c03038110110500c40d03c0071081000380d1000c0a50161055143c104000d901e1030b11082d002c5019524914029107003000889c2d9801360902860f51a008405201c0480741007031003580f5140045d00e0f100c010510a84520300e800d034981401c1c85402049003007147c048c3e03030b00ca0782c80714011444002d65610030300405074880a061401400944 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 970674847 1250 970673597 970673609
    0x4020d0b090607140a0c03112515080105010203030415020d0908030a0e0c0f040f06080106030c09060906061d0315070e0102241f1802030105011215141504 68
    0x800b041c101100c003c3c0119030702414850304a07030180071040341c2036031014061064540510748162252880d616082c00c1c5506540001003a0070480360000b8451050f4240104641105441004a148200342114048020300810b4016001000420003056602d00312a1380302c41c0e0714000505c2c146121040d84100e0f15000c02c00c403607601011040000c2c0760020710500c0e80054000740500300c0000f0b81c40001c3c0400c500c4076101031017980c1c0e4094100c034450b001e51101014003140c000810050703403282040a2182107901c41c038066203003090740100b0311007150b01442c0d040354405c0e285c0c44a414000d10003580071f50003500d0216054481c0805000181d445580244d000d410b00c1c0d100c6031805a0004002030514944000c1c402041400e68000308171018a0029150700c4105c4031113400d240050b840310780c0900c01903903100000400c08000400c4c85050b580d80114120b9009880340c54107948081004400d90b8203c8140951440c0e04040400c0410130000e00d041080200404102c244060100c00041d2500031390010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 970676097 1250 970674847 970674853
    0x1401111212092a12010b1005131a04032618030312010905220203031b16060f0e030d020a111309050307050106080f061f0302040504050c03160b1204020d0b09 69
    0x14043d1810007102000103000c80b50000d0100703008480120f40c00b600c0c001058010010000360042c2d00c181a00e400304054190001e0307405690740b0040301070859401502003522544007982c03120309100c414208032480059118410b5081c1003146078401900440c10b540351b500341c002001345c6680c0d64200a0041c1c042c003601c0c01d0000301400c180d40c40e40094500600480142c1c44048600d1025036800001d0300e02141c41c80542007030714102254420305040c180c0c14501071075080c000c40800c2c40f5030006200b441c80061030b50b84500c0c0399124401c0582c0c400c7c08000000258200c1503550020903c156000307200120042c00210083e0000490802210746844041d517080d0004103c10381040400e008100c001e0001704010100c824092041c1526a04060040c4d500c542c85032441c10101f513103202400c07004540003003041100d8500f80c02c03c0b503183c1006480b664403034010705044156450304136009106588003405414141100036280d581f202e4006801071342c1c0044242400d00004014139600b0703200c1e02004000e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 970677347 1250 970676097 970676173
    0x6250e04020f031003030905040b01120207080c0d02061501260405030c0f0a0b0c0301030c090906060b070f1101050c07061d0301060803120c03010509072601140111121209 75
    0x2480019150882351140342012803405460ba030001010a002400040c016a164100e2402186611864111a58900911504c00803041d0089507170f900c102164088204040e8107100119503818919090041c80220038104e4120180316400c075907805807142040343d03d041d50b00000c19103042c40c0c42c400500c459021401c0c0c04108202d4a0700e05801c00b40da441c0e1142103505641d20f540d6039031440e009800c0e03c40e503541d00c01404d00085400403c028000b03480c95550702c90b49420403078001008050140d0b4549091813071100c0320351145044a440c02d038144041c1031400d04000085910924075403480d80340c0c256260032060690f030b0070b100b0080101034150080d035a450510b1660080321400600042000c8020b03c010400c0e900d46d00340303299002c2d01ca0701d44039205103c00541a00000c2c0800b000c201640d10f5200007044608090100e4845881c00b621510306080d540c1103a03a59a07042072581500901042c0300c62030707400141080c000e8105920f0070079144042103241109690500000884aa803581101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 970678597 1250 970677347 970677353
    0xb010e07230714010b010507020d06063309080d030e0f0d03090b0a0e0304060c020105070f0804051804080712050c0a2102190813050a1706250e04020f031003 69
    0x400078120650f120028480410400c2c0040e20034000d0a070060f002d110040003410400440741e01490191039047c0c02034559001104200c164414030240f443d41d40400c40c101202d059004e01544022200c0d100014601640648402c40150201c11402c504d580b06203142c2010b001c01c2805a082a0351042da0f002515100500b440308501202401c3c0801d141c0c98030410030f407050004000c6a09880c95030801307030003c02c0c6601c0100c0d00c03481804005886904078110000802c000b817002002220303003ca504d52000b402e01069000d017000251402003030f05604121107800606010345904c00650642002d42c244014100c0050a2075104a011518810380c1c1d0b440c005d070468080d0040449010070301c01040700390b006005450003816011070140c030070400404d0399071f40c3c0c0c0c50011300000901000b511280300c081c0e4540c2e4140d0440e18154440f00e407809410b0004440041c910610a9040c181032300d8a4072003062504182d8404640300c0d07846402075001c04c891000001c40d030004502a84d2402c00c603000842c5181 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 970679847 1250 970678597 970678613
    0x2003070b070b1f080d0f050c03070f050c010318110103021b0f0105070c0203060a0e0f030f040e0708060303040e0a0902040c0809100c0509041a0409030c0c0b0301030b010e072307 78
    0x2c104400c1c42e05032414802c04500142c0317030000c0400c0e42003001100d803911a081e220740c080c204101c401440002424410020002c50b000413070b0b4401c42c03c0300c1207890380b000194262001400b003601840000c80144001c5050100f07418103244041c1001494648000031352704040e05449401c1d1416480301c1c04403030b030a034803d100c0c10b5407000081c13601121990980e80000e4407050050320541c903464581c1c4d4021881e00c41806012000403440301180c0d41c444021140b24625003041c0700e004503014641d40080c407024017403140981701c3d110040c05146014107040c004140076002074022203080c0d61f20440035005031128885c40c680301480d03840d0f003c41440d20f450300c503181c90b100001005925052620181050750004103540d42d1010441d4049001a1036a061003201c08640040cd03510504021042c414150031120351070185018140e0200c10075201c8031110300d0303448288401810510004010801c8000034494240c1082d00d92a002030f1010f4120503882102c88c1e0b0a00070541c400c40051000704102200c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 970681097 1250 970679847 970679881
    0x30b0405060c0a0516170a0306030c080c01020d050c15010909020906191a0903150f1501050a14091503011d011d04020109080106090c030f092003070b070b 68
    0x207070b490070300d01400180b00902a0003031200855101a0411480c8100008450300380c0824545503e01519041c004800501904031484160b81c0c840010030f01290a01001c6034441001c00180c00030302c0900070307840007100c90354448800d04829001c3c5041e03000c110100701d00c80a00030009450003250020705401000740c00c404c041e007018400e9050144500a0107031072514003084078030013002e902d65403440d080301c80498070402566903410b0144d91310102c1c040c00c203542110701400526a6450080c0d0b42c21440466100005100d140407480c140001a0891b214080e0340050480f40c01145080c5685e035030201e660307000e450010810003030300400188013241d8404900c603408000100c10510341d51503e00d007001e51113003c080400b0035000c4d2100140075a401140d000c001041440c0c001c0201e21342d22191034000b40992a1401300180c100342e004090b040c1d40e4042c0e04c0c3c0140d009600104c1a00c0020707030040c900000918516014050f11600140e41466000035002c002e008010118240c9000c00348bc003603a40705 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 970682347 1250 970681097 970681111
    0xc16080d0609050609180708011803091a18060d0e06040213060311060918010801151a0307121e0b120601030503041509030b090a0c4b030b040506 64
    0x68481000240e9854984013a001515410003044032000c1c850b01c6403d00352942c12101c0f8039828803441c1782c1100410412a18138901030340d1033282c0c050300e800c0645980d0054903000c00700c1d0300c424010300d420a681d41c090007112800c001c1c420b41c07529010741947c0c000e4030312440b800303201078201c0010082503060080c4203500d02c0810000400440c0e04541e107484c020180341202900855001c1030048158444a4151250702c1550048240c590b03500e459240c0030745686260201101103030703c00000c6641d0300c511514080c29a406919045035642c4000f250000240741e80010b2680c0c80c1c1408801c482d0003509005618001c10801198114010090124914000d0980781c800e034080b00041000c1180131090300c058480c1c2c42d03019069010614000c031403000651300058180001c0d0f90510003070340b03c0020303142907551040d40c0c003800c01560381c115412220b4803501e40a50000031031241403020726100c1407600100304203040954072a0003556803401200142d8104403420ac602d00244010f00004104450344055 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 970683453 1106 970682347 970682351
    0x6050d02161b17010207080a30060f050d030c03080403110706080a1b02071401140a020d09090e0304210b090d0909061a030c16080d0609 60
    0x6100c1c24008850f0104030103180d20040c005d0318010780e0441d034480e0901021034400e9410f00a44248071804484260a01105420011760000b0000240d40300040c0d0342d0501e2464030080c00c3c5600316500c20800302c0e154a0020f6403041004181075414034280c00943c0712490261540405500d07a022107018601005c40c0995005200d03a100310b025580a100f13801c07078004458054601000a40010b07084044244052102d030382110304075210601d401d10301040c41411410482d0400091040141c12001510410035480b00c0799002903c50300300100044254080466601c1c0300700e101d9000103550807980c05040d07020225642856a40180041900c0d00d020b021464850003100303200c2c000309480c0321010039440c0d41ca02c40c2c1410b8031a00034101000c1c07038405500b100340d80c100600d03c603551401048a200381c00c0908400c1c2c0201c5100301921a19a14043c0380c0a01307583e89a044001014 = true := by decide +kernel

theorem cover : BRFrame.Cov 970503597 970683453 := by
  have h0 := BRFrame.cov_init 970503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 970503597 ≤ n) (h2 : n < 970683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
