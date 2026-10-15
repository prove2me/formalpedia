-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:48:10.285916+00:00
-- url     : https://prove2.me/submissions/dbfe934c-f727-4933-9d59-a47882fb8b4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 920143884 ≤ n < 920323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 920145134 1250 920143884 920143901
    0xf0103030c020d2f1309030e0d0c0929010f02030307180512070e010b030105090402150c0f031e1914160b060109061803060f090b0a0c09080703030210 66
    0x1884d0a90311500e02c420840941c0e0500f4012180c2e40725501560694100b07054510702450410408000800300707524080c0000568141d01c0384a085060520401c204025060101070202c4a01c2044118103d0314840c0c0c0c0300802c00d2544101c0820211a184036622500749002032860603030245041d03440340c250940d401041040f1115050104030400704154582c1c1c44008280354040009112941c40c05454240f01081a044000c3d07810381000140982d480c1c004940e90442c2e4141e82000d1110220301c9007100a005036006480180628180a10420000009003c06003c030204600c1c0c44560044a0300c900d203c0e040e40703141c2d5181e130260b40c4c442e25809240c0048c9282c10101d509807400610003400d11084505060448910420341c05000d081c0d6888503240c40902060b00700002e440c1107602e00f590700300c0c0c03151000810880d12b50009071007030821070b01f00e595019030141c1547d41900389034000c0780141146d074a1150024842040000e0b500f040003a03124110703905030300540301102c8000302103806800d108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 920146384 1250 920145134 920145143
    0x30632010e010c050f031b370203060f0103110d02030c2b060e0106060903051c0912150f050717101802030702100e2d0718050f0103030c020d 62
    0x1081d00d00c000c6002445445d0000691030051035603070030a204441c0503010212000f0207a0342c4400000050340e5010700300e144244a251109940c17000a980e0404e840c5660100b009415000704001e0000180b402210b0354180c8e031041c181b4400ca5001030060100c0c0e406404000b0350f060307000301e00602e0141032070380700c2d0300030101040c000d800c01e4640c621042d038880740d031550202d555580e43c00d40c01d80f41d00000e20940002c0d01640c54102c600500d5900c0d036541d5903c0000d10001c2c1a008200880a410b0241c0454030040004541c3c44034135140c1404d00400c1440e0b628004603126040c15144400801c1d10301c1224412442500c500e007070551541c1600c20003030750007005007401000e41c034400309221403480f42c000a0080c04c080056602c5c500240001d0528941c00d030140c0e220b43c1001185940400d000c40c0201202402c032035a03004404d282c142c02c40511203c0b050041746802204000304210001010b8150700070303002c410a00c03440d01c40807540100b0100034800600012000c0004900501c0c2c00380310005c269005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 920147634 1250 920146384 920146397
    0x160e060f09131e02040207030c031701050a03031101060e070504060e09060d0b04050f0114240604170316050a0b010b040f090b060702031501051002120306061c0c030632010e01 77
    0x6a1340843d08a074048013040d400710303000104842c02c00d60b002c1c108041901c1d03104214151940b41c040401d02d12511800f00405001311001001ea4103042580300030002d080c81d06000106081003500a03015601c42e002e45000036061020031505420170f4007050340185005040901e403e880f0f520b41200201c0050320032602802840b8480c05000000d001d0f03d05400010360b807242290400850020503500d038070060300000c80300503120513030a0780c40409940841e400c018030b600030280c090344505d041d1300c2843c01c4071155245a400701818048000352041000d88624401c1c0000d03602d030048105070f405688524118000e03030200c20300c05180306820004160b00c01401da00d08208140c0d00003400e15031540120025840c200004001600c1c1c07041d0711074403405580c0054003180c240301002c8074062100a00440c024800050081e10030410b60010400c1c1e421440000c104803c00c6441c010040c0006e44200c58455404940400ba060f02c56040324072500c0000041c130520310310081c010b4407400341c51410176051042 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 920148884 1250 920147634 920147693
    0x21040806010303080f072c030f030409020703141c0207031716020c0103020702010207091802030616020d03060e0a050c041a070605071806050c160e060f0913 69
    0x104510340c0a10301c01d843c0c001940c90020030440e4150300c010000390400c010950000d03a020190b216909030342c80d2424010003c0d40d40040400d10302510740c0b2503030b5424400000c0006401c100b5901034010b4601c40e40c0d40810b001e00b0300390502d04900420b107104c00b140c40072070340c0c030140c040c0d8550050100d90b209003015883d03070441007546d007401d840031509150b01c1191410440f1010340c0c14441000000d00900382107060480030340000350340700101d0043c5c1c29816070b5505402e40186000d1801c402480c0d000f0202e456500c1c018041c0c0385114481c43d00000580710b448a120300c0075003c0c1c041c0e03100362281c41c1c03100364040e07954007101c401802010b0500544001d0411011411030038941884050042e0520794a6a6aa1510707050046500040000b4100445c9101d480040305107040d018007114450b00d00760380c9070840d03520680e0402d0040e4a252131002c006807000121107044440d082d04c141002c40300034106c030986200340302035004220f45c2020b81c1c11140a2100008921000c0502c411104072985240d544 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 920150134 1250 920148884 920148899
    0x40c0203270604030302251409060d170705060f1b0d0e0d0507111804020d05190311062a1c0e0c0a1505030c0706020c070e0a0c08092104 60
    0x6010b0f40040e4016085402081c1180c1c900c1d0b10207011050a01d1f500709511b610f44007d80352504021789200d40301d22162000710308a40e54041600c5000d0340c0210b160b9000020581d1110791380e07404154111000d0140800040555400c0542c41d4424002c031210645c0d201c200d102407040c1c0354003030040000d2603039540e404402c60032810413000724076480b2070311840e0741d501c1c890a020300354598015800b03104412205c0d103100701380c03110010144c03c04d03419070f02c245089126141050402d10284410100c5d104141140c3c810315505c00b000b2001c807551442991240d84460315809141c076580c0340f00e52449503c44074200107802903440140070a01e0a05000000044940c40500070b8540d0451302a40b41e5224440040d09032401514400c001e20800010548521808a0140c01c5020080501010081c082003035014400141c04684a810860043c0c1c0e0559480d030b0741c5002c0c20305059500300d1045142c4240000c1c4103000380c504038001c1e6034040080ca190036034a1101d00074070100c553340c283c10100c207100005922 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 920151384 1250 920150134 920150137
    0x100b130203062e030f1a010e03031c090611132d15020c030708070e04030c06020a09030b2d0a090c0b04030510090b07140405030a0602030411040c02032706 68
    0xa5980386480f060b030040700d4006007600d1041880d0502c141c640415100c055020318100180f521003800c00004030b1251000003030850040d4a03190b0480007460580c070110500c15032140188030b2203600704000d450201b40005400e801411440007050050031400d000c01c150030f45c003011581d40802c82c045940c01210030800d01d81c501310303484650340c01d2501440c0b038011030301400400306d001c8041d0020800945858441036a4101501c00d40c1c402d40080c00100b010705d40300c1d0440300030703c5401140030f540d9441d51040040404485100c00d440360303041c00780410360401225900d09884020410000e000c410116070540f81d4203006000240703920f5a034001d017000209101c0c4140010902c1074200c1e42c0f40c0d03185081c500d00b4200140f40114517145002d006500003000c0d80c980b2a0481503e2a1950140305409242110351046401940c0d01d4400d44841604100340c50300118840d600c00c04130300b00031000c0c0a09120544c0c143d00c0702000541c1041c07000801e545400b03200c14524400b04c0d00f060140c0c00c46440401ca56 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 920152634 1250 920151384 920151439
    0x3022133040c08101a03011802040f08060a2a03231f0602030a0f050901021006080718140112030c0218040302010e070f0b07020604090203130203100b13020306 70
    0x102c3d0a40302040b011044241d6070303100a014486088000302c100d0340034a041c2c0c0c4014050602c80f43c0c40e0f141c034460040c1069043d2809010088003860203103840f21450b41d5111030807a140d00f8590b042076515600c80d442c030807079a500d642c041f40d031600d04000c44c61030a4020b40300401c05c040001c0b8140540003801d195030b01001d40a0210f400702c148403101085440380d182440d52708102c05561013001300b110750a6114102038030440f6245086074581c402140100d0a11344004110159a41003030004070300c4800124505048031421440e00761402c10340012078055031404101b0030702c000713000001000001020298850054400d2030402c1d0600c8856001400ca00601a08034222400a00c10442003640921640c5d12581903800240320507407503c0c3d508140c0101e9401041e966003800f040308021501c80301c00b69006080902010b544902c1d18484c1c400603031050705070a034441d03c1074084006c1d4030746c164841c02901a501800100c444000240d05201960010f041150031180b25506da05080e000030390010324 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 920153884 1250 920152634 920152637
    0x31302032a1f0e1c0b01150e0609040515220e0106050a0303030510150804021e0d0206160c17121204060203150303070605061215060d03020c1003022133040c 69
    0x2040d4180440c06c507c58808984100901c0f4a507104405150b5410060702c020310b0044a02107907594580f00800d440c0c1101000704c44d0401c45c07030411741400810040800f641c039100b9000400c420801001d842c0c0c01d071601c1d44104c41e007105a00c842032000c60700c6a008254490100002d0b00c0e201d590360020000c0c0c144040340810000380794072003800308503e803e54201ca41404001d8080c40080320441c00124203412201009104240000d948100c80b05c2140e01c14010715080a45e1501242e070720f00b20542100c0c1c0c0a100031005014a03100b40210741c000605881e40d420241c2c05104142d51207594200080d40064424144282c41d0a0030f04865a01080102142485020041550700301030003800300d4419590019000c0350040204e0f92800401070020b00c1c5c2c404000c98021401d030704141810381c10103a007404403030b800892070301d024540e071a00741d0010602c085501d0801808100340720204500c00701c1c161070742081c807400750300c610341c0c64070070451807030071500a410320205d0403540c1a00103002c440314242e0840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 920155134 1250 920153884 920153903
    0x9010b0d1101030c0801080d030e1c031e1104060e01020a0204020f09130c02210d230705161401240905060603010506090105031302032a1f0e1c 63
    0x880341d40e060180c060318130b1141c2450341c1654180004e03541c42c2c05442d109981007684d199003028200c18104002400030714202c10140110740009030090151010210108000182c40440041d0071281c1c03061488040e030700c1d119281440d0400f00100c40300c504c0780b0107280c1144161105140503a84510061462000307124886944101003030a0141e40d0321150f03c08402d036441d002541a0154011a040c04500a0140703811140d21880501c08160700030441070354a01450001d0b24a040c04510400348201110700a4510080d07860b04011101d41c401c02c508003100310b81c8205040300103586c0d1500540c1c8080030344008561000300e02d02d02c0064001441ca80701740c500200740c0402c080c080a204c1d071600420705441e820315560504001c00c6441c85280c2e13100307041140000001e68241056110701c142030380e0007401d0b2840c04030001e1995814400f02000383c40c80c0d80d42d007000c26105141034a0f40b82413007042e030503409103484c80d80703102030725021031040341d040c1c002c80990402800c43ca40038942401c070900c1a255007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 920156384 1250 920155134 920155163
    0x20616020712301b051906060e07081807060f1427010e0103140c13080f03070b07030506011e1701080114070903030504030b13050307030c0308070e0607060509010b0d 73
    0x2c08a000c0c0702400012040d2403913102001c603402040c0080a40089041038a10a810b0310f40307400101800e0744884070803501d0700d0034008060381c040456800f4410b480f002007040c0c4404203c80c0d40381c24603031248401044807542141e02180c002c00394091080000c108041c200008292080c2c0140c00c2032001d50700c0c12990a1210380f081d80c01c00200254404203107000c1110f4900040700c0b003850750015080c4041c1c03110100c0c1c1c80441d4444c4204404c00780c0200002d484014400c4008995a500104ca0480b0b0303d00c4080d00164009d446845420310484d0141d44506031080d1021032039032014030318940c000402169005c24011940e401d001240240022070000812110410003010f1038640501000c00f00441e4400c02c0002c02c0d400400d450a0342c1e0000002900343d200d41c2c0c845900c110f90074400078100c2c04041050401d05404c0740d10b500100e03000b609e407d6403690b21003408484280090307803040c3d44181e061085030045202640802e84c4541d001000091004130322000171180c120502003100c001c070181240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 920157634 1250 920156384 920156387
    0x91509030a03090512070819020a03021002012316031512030503010305100213090e0a0c17070602190816080f0310050402070f030305040c05040608010b0102061602071230 75
    0x18405d102482c00502840760401071050384500140c24896022204000078100b555101e02813080296402030088100c8510070201034080c004819941e2840441e94200d01b000d50194000c0600c1120f41c8950b03040c0080c503040d003e42c004d00d0204901c401000c0240300c082a4003006038138400f80c0b0360003616029200d62442c5400381c501401c082000302502d00501c44000280940c10f014819544058404610b2001c0041e12918001b403070719010307150618401c000640ea002110b15070301612140c905850f20a52075204c02d0703030350303040d10900c90100d0703040c030408000469290300207085000004244545c0d014000d45616501d90000200410741c003400100b40000b860f41e640002c0009e01d02594258104070b580d88502c2c200c46070204000e014541c4400c005001c00420502e080041c090040c0100070158079080164002c015441986015100b00400308600c0c000030718000b08140920b90042103003508140380c502004004a01c12507000c0312034566440030a10325541c055088801458411054404060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 920158884 1250 920157634 920157649
    0xd0203070b130f12120c0c030e030c060a0302090402070c06030e0601080d050a08041505010902180603131202030c030307030c080f040224310515091509030a030905 72
    0x148080380084202e450b00042c50240f104110f0f590056035030681140010000e030340c512400201c00010518112204040a4000480134041c50081e0748031418400c06005155449415000681d0b224070309016001846210b03800418450001030400b608000da00d9a4141d20702407a074002002203a251781d1342c1440784504008550040c0445070040c4080c40a44002404070b00c180c1481900b040410000a07007400070115407030310700200b44941040250703941e8581400940086400703c000c1e10182d4136a100350b190102c140c85c0101101c00d6416406051951f402c0303040c0306003117640300c1540424040d01c4042e400c10300c0039510607141602c0c042805401200003d113540001882000252260410722002d41c0311a900c0700010101d584030407200100728000f0301c3d0f19020305280c405420310b280d03d80c1e420340000c0c1c03001011052040c00252512640314000c102c000001c46501460101c01807045c201e5a107400800d000000321185281e514100105021074100381c25a0303401d6012500c02c00c405c00c59400c01c2e00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 920160134 1250 920158884 920158891
    0x909010305070e100605031f0509090609100204180c09080a0305070c05010915120b06161208011a1e0c0307120809030702010c05100203010e0a18081c0605030d0203070b 74
    0x401c015071305042c8040035200f40000b4003d803c040c40408640c8108840300100007000d400024000192454040311807696540c046031804154000d03c1100000c0e4925402035500317440b2511602c50100280c100b4841c01094050000300c100580c601d40015114000d01c081d2621034060381c0d8240c1d681034207080a240b011043da000038100030140900700801030180d20b582118280c1480d12103020f00c0283c400c60090410b501c260f0360700c0200003070302d4824143d828140e142c0c3d580c824018940d01c1003a8007403d0b00ca00f0424410801401d02e8281c1c11056420380d14010700c1c10740084070341e02036000c02c01901e44500f034014181940d05030f4800983c3c841804140f440c0034080300c80a1901141e5440c003680741d6612405200c8009050103604550501082002c0c4030b45144410100011500c96a584240001250b000e0300d402120740d240600d0340c5050031499983d0720441360050441894150646044001c00c090250282c4045542e244081500c0e9420702545407101d05a0340115291a050b0070b01d0740c0f580740b018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 920161384 1250 920160134 920160151
    0x607060f0e0a1a010501080606030a0e032b060f05120304090f0b1e0a050d110d06051006020a02060703110a1506080c0409050712080f0c07140613090507050909010305070e 75
    0x181c00401c01d684c0d002d47c40580c0900140c0e0b499032a906c52440d02d00c0546082000508180030102d251140c0b0050000f40c0ca400000d445003c1800c01e00d00c03d15002140e02500a400000052110034407450070b08460115614030040c2c01c503450140e0b211586030880b004486032042107501d0780901c540f207250049055941d8041041e000080c2c0e48144006501c4103c0d900c5854040c050240311070051155500c980702c01c8646c00740c14540307078070058900040100b90031500100c5981414001041c2a440012420700711940035001074070700002d68809945004210801320304a224080100001890710b0102282c0b000ca90b2001103100c81c201210343d8208030082030894011031070a092000030032000110041100c6914026540459060801c1032080c03051900201c50101e0005c1e106490b07150026100301259044190440d00b592001e04201480c0724003900e401c6c40c0c201001c030520a851140c2e20503a0418001d091052070075407000c002c0385d0b2411099105a41a8114000820007022000c02c0720343d008000d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 920162634 1250 920161384 920161433
    0x15050a03062114190602070c0b160f0c0b0c0115050105161403250b0c210709080718050610120f0227040c020c010207050607060f0e0a 59
    0x340c290312840c184046010744010f41c0484248103a000078030030511011804803080d0250340b0a420310201a521400b421200182403000000c1c04080d030a064030540420304810b44118100c0c2c1c0c49148082d008035070155a221062a00040c1c04050040244105400500045118802d00c041d5038268422a400181841420011800d8040e0b01d807003045105a48124100300701c00309010b08034654012045000c804143c0751007040b41480610088015a501c42c02841c6000e0b40c900ca5803540e5400f54551b98840700e414074800c0805011745400c1640e02c04007510b00752088540e500c0341c2d81c0c80e141c0164040d0540300000f8548018481e00c50258651150007543c042c0c040d0051b00c80d00900215200300c0100038640d80b010040d03480300003501150b0300f02c98185400c218490000980c03519080140c0a890322452502c0103c001880c0041403901400358145c010701621882d010a2000e1948140d40403545540d44d035a40141101552080c50601800b24005100252140c50043c865a01502c46200890300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 920163884 1250 920162634 920162669
    0xb0a050f0a0b0f090d0813080a0b1614180f151c06030f0c1e0b191209030c030f0206090303131b080102092b02060a0915050a0306 57
    0x2a50700c040e0701100c50125034140d80300c103c1c2d080300c0c0d0580507103000c0300d5004c03604201200902060501405a200080300d1990641e6502c800b9599240303da8a00200b40321031034030001e400010b1080030100d150105060007004402600f141c103007a41c1c4200351082c0e22080003560f445090422420802000c034041d200340c002080c648800c0700c218042d084505461030040c0c0800c1d11030f000c07036030021030003141d215004a840007442c0c9070844140a181c001da04180b40d8060000d00b1241800f03e4000031110100c0711140f501e00b0000c2c01040c280380302903180007842003c5c030030360340c00300c0492180000185c003070f0f50744044402080c540204403807801d6001c082194804000d100e00160044101ca421550511058075036104602d001c80d031860300b40d036540302c01080b8031070700080141c0107400070001d1403c02c1720780d000d045030610442000c3c1c41c5d42c101d408000f482c0b84042d29005090000080c6043c10380d5060281d41c0c00e03540c511115901032001e96200010358045a06070f481a090300800303010f0f000510341c80c090a01d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 920165134 1250 920163884 920163889
    0x100506070b0f060102120a051804020a17060411130302090108150a09020f10111014010909170307020106140607020108060112110a09050307090605060409110d0f0b0a050f 75
    0x800141800b84032003601c90119000368001c01120718141c00c08485035450b0b40000c00c0c0076003203401140c00d0300003001d603034401520709103880d200711091030000b0740300c03840c83e00c24484c1c420800e801d00811030b540040c0c1d28031081c06050014070103882d28030348451035111500d085206100c0040c006034010b81c09a840f103540ba42800c0b045900c0254003c1d016400059001c800c2d000041075800701c028413a03000310b00c003003403260340c0341d4444054000e1946450440750040f4011030600f0407210404481c9048900e10401400307075030000d420a000480c0502c4090f4480e0b04408510301309603200b41c65000c0940c3d5034040030840d1030004140050b42d544121121824848a50000b800701d8000501c0b103410000310150301054601c40394064501200071003030260300ca01d1040f0001d8094000d50258901c207120700c850006103008540030714802c1d103c0103021641010305c2d14064401a041400640c049845c0034407114018044074491014040407061011806c2920316080c000e41c1100c41d00414083d002102d8100b0140c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 920166384 1250 920165134 920165153
    0x70c050108070c140109060f050411010e030307150b04021c14010b0d090510020c0f060c0c070e070e1c020f090f0114030c15040303090905060d03141201030b10050607 73
    0x20b074200300c203914000340303134100f1500401100c28014402031030400e9045512200340d10032841588201c0041300e0390030440c00150b0300c185c01a08210350660003004880700041d0000c20010780400d4042d008a07910003007100050587c3c00c540d103024600700701801414219021f6009031524100d0ba8401d070070207075052125949040c82141e1082591503241c2c8000320030000304010480410001480841d1038115040c109a10b0f8000c0d42d081d10024401c000114410b4000401120b136070341e00010050050b20700d4100c00e040d020000510840c203000500310381c031301c2c0d40d1a004522200303414000d280a400048520411400005900d4043d002c2d01c1c0500c104200f0200094400b4191060124522001c407400c1000924084d46041c1c5550000040041c4140c000442c00203032007664881c2c0c0302c180b1100d45030780060080b58003c4640d19442100703800c0910209018850030204d900140002030b140020007079000140b68020390049900f00b50032000c03c0b440030905480700700508807c40e0b01b586042c5d4192141543c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 920167634 1250 920166384 920166407
    0x61002010e2b08060f28080303060f0f0315040f080406030b01031b0f1b0203030d0b120307030206130f12020c040609150b16020307080609071212030903020102041a070c05010807 78
    0x60900c032440c102c003511000c00000041b03005011408401c64960302c1e0940c4941098400c14010342eaa918006a586000c104c04060b000e000390080006145907040c0f0080d584000d001a02e0300c4a130300110f800426141030040015040ca5100032514140b003000040c00c42c4d40c9807030025001c411350108000500d5001713002e074103803030050320302842460300c280d81550980d00b503540029407601c00041c2c1465996140e80040302d880c00f0481d119101440440c071421345900c17030310b00000c0040e00024009203c00000d148040a00c41c0a80106101c0c2d03006941c40010325417200041002583c0190341c0c1018500d450b002d100e0142c60010170031f01ca802c502c030842d4811a03005000d00b4848941c08a0079050600050031943c2407542c00030115510076548066084d1100410b83d00d42090b07000d00000407c0310b503d414422052664400c03610b040c1d10030406c0040b4020700e072010044007103540811000500340d11807460600b0250300c40250540d2aa070074504590142c96552103241407003c0c00040081141d040b101c1d9135803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 920168884 1250 920167634 920167639
    0xf21040510150b071511091503070c060504050a1b180f020c0102040b04030b2203030504032c040f0608070b1608040b04030524061002010e2b08060f 65
    0x120242202c82d4140a541c040e08a040403402c0030582900b400015003c1852040c503e03c01000f50403070860302c01c2528480d40e06d5080d0000019488a074091803018000c0d0351007040351401410b559100c0d40c3d45000c0e1901074a0558040c0d00a045107400c0c03011000880e035038a0101441c0d5540c0380d02e4003148110100030320610b0300f10b042d92440c4010001000c3d404030789141c2078050085507902d484442c580c045401c94007065030324208020005e00010315000e00003817079a10050100361040032581d800c4014201c004e00440410185081a070361044020a500340c1c2001803010000d00c0c115040706100c102c807406114484038500349041003044c2480030860005031240008025070f10b035259022642c042000900080071160300150020790510b81101900590b48144191011002020411271080811003904401400c0f4940442e02c1d5151100d00401082041c1c00040340300007540383c4150904410000000c0780350f143c241c2a1405040080ca41012140603040512050030420003062145c4005240b550 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 920170134 1250 920168884 920168891
    0x91a090a020f1905040f1b0201020a020c0d03051c0c020c030303010e040b06030f0d030204150302180915032b080f0112060e03070c0303021b060f030a110f21040510 72
    0x2a01034403c0184a0103090090000d00050040004140060243e08203580d5122203403401458100e02c10300854890b83c480d0741c020186110705104000c59602568401c4003446010040c840d41c400102c410300703a0043e000d08000855003161407020782002451814240300750010401802280c41ca14441508207420815070400c1d40e0b01d50010138501081c0304142003c603c50f0103851100c4680c960010400d4031003c0e865025400340004090703040e4000c0685040071403102c240071044030b0402d0120540d01100400f11a8010001d02c004207080c030303401c10905100c1e103002c2c00001d2010f01c5170050b0020304a0462800017418607168040440307104040c01600c40b105044040c0400b03001c103075001280c4050904064983c0c0310060300e802c44070a000ca05c0100c01500425454403a01c0d40c00309095030502c040540480e2628000000c1b242c00c0d64002000004420703500c1c4000d407421110b2402404084000b0f08880d41c5e101c0c100c490165215900c0000304030f0008550741040002039002c00e8400f0000c20308040070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 920171384 1250 920170134 920170159
    0xb040315050903130306090318060f030c0216090f05100612050406090c0e06030d050c19290a200706200a020d11030307020312040510091a090a020f 65
    0x40d400e500c1000e400d14904002c009000c03050201176400b034807d02c0d1003512a505806c01e8040700304000c0c0350302e1042002091a059803401c8850103034002100c1e054052041d2101034000201003500c00350940c128958043e69007001801400c02c6100c1c103504202100c40c0c1804180c940500100840074000907001d9440d11403003c2020007440b030b0010b0040306d502a2000c55110745450f40400c8003401110740c1c611038454407001c00a0079006000f100c8020080c0e030f002e1320301550480d00381c0e41034011114085444203d80039840c1ca9400d8500c01603410100c042050a1180c10050b5000703017504c800840350082c0010040003242050b9010080700d010691050002c518100e42c0b61b4039940c40e514000d0000708020002400e5001c05501203541c200201c8203807110800e088417001c4a5078ac0703020403911000545e004020580740c10680081d580e5000d0700c100101c0322480000c2d00e03400b0540386803440072942e00d410510b0406441c00780e4040907510910700b40003000d6034041500016a544507075030b102c034003980340c442c0103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 920172634 1250 920171384 920171401
    0x60210181b030506010612050a0e070b1e0f04060225030b0c270a0e130201082806050a09020a1d0d0f0b070e150a05090a170d090b04031505 61
    0xa01e00195040010f071016503075900b0014060503512819009001d191034002452a05144118a44120810010f00e0040e0500550031020b5104410032000c0c4685552061240c0d040b82001340201181801001c2c2c60381d240410180c6071418602d00e4008902c00c4503071102140705240380000440340c01c2000c000d1944c8503611049050f10a11a12060b518034000001201e000c21407c800030310041501e03296445655032034840c540140c2130761098007440300b00c0855005580b00320103507500500c0c0107549644c10b0030714841c0c0342205145002c100c2d4020303440366030412003440c000b00b4007c002c1030243c8055141c80d500080080c2512035005ca610301001c000088003085403964135011090035405420020380003414104140242c0040f910300c40054140306051401e418a05210748200303042038070080c00c0ca41d9603142a243d64000c911a01d800030440000000d03010781920a10401721070b101d010302100307160317940010600c8a82c2e40140c01503501c01c2104200140c0501480501d103c0200782c002107a8a4503000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 920173884 1250 920172634 920172683
    0x3070309020301020c0703032a080a02010b030a151d1c030b060d06090b010c021c0609080304080315060903030906031f1707060806010813050c0a0f06021018 69
    0x3020b50158400300c0d400c1c1c0885000100042900d01070b803542100004580f1200c1010703181c07146008140b00f941c0341d4000018010380f0186c81c6031240d84c00003003075490245000c20300d4a026943c00f42c030f26071220281898460341c58498410355042003040c1003505d003030300e07060701e65142e0009020030482c5510100007060760780300e94010110900010019a034640070544900c0180000e0b006140c04a45800400d041a40c0104c08180e891342c0d000c0c12501603610103002c0d01d015080360041c1035411588601862000600500041d840b59114404003912800e0140040240040b45d03220540149000c000c1041c0554001041d01c540d000c04607043c41c1d9135a1104c1e40d010707946008002180b2400202c00d0b01241948500184501010b210411921407941c0c4401c2100d003440c050f24918082040103001c03500c0381d030504122156081c000c60444900580e840c0c00714045110f603070700024210b080f415080c0505a0306014800446002400030b000740340420494038800e80e000d0750002e0442c06078000201e01500440c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 920175134 1250 920173884 920173901
    0x20913060203070e1201091a100f030b091509060a110c060c0702030d1b08160f0506010f0b030c040e220b060411070c150c05070f03030f080f0c030703 66
    0x56040d0b440b07003001880904043c40d096041c3d40701383d55520701d11600210505c42ca5410390b4103c0070920500300480f01c1d07000d07030074405017403090740710192a000b00740b040307481c550000290301c1030418108130302c2c0034030301d440c01c100c040055484500e640d174052042e4000d000a08540060710686d0004021004041a40c030324850a94081d403140603800070041240f065001424a40e0300a60949080003598541110240c0a0458010769172401320061000b141c000d4000d003c1e044810303001d8017800e0b00b040e10349000c0300724038030130407103141e84a0b07401030024200000daa6070080050301102130940c20a049811554020790240400080210307002401c060348150071030703501800c101502c08403040f060a01c102e00c000111641c034026402e00c140320044c4840c2c10102e641daa0b13040043c102d02581081d01410740c1000e0301d00c04000b00400b191421300403c00c05d21086000f4243c84036280303155441e619014001d440301c078580d04240050401004442d2513010a070643c01110841802e54958509800307900904d100c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 920176384 1250 920175134 920175143
    0x30f020312040f0b1e0c070201121a0307091a090a11030c180a0620031e0904060515030106080402060409020a0e0a080d090b07020a082b05070b0103020913 68
    0x414401442003c00384070140f10f0045151091680c0d44000c130400c100c1d40d00035007204a024543c00a42800304100203002c0240c4140b49c2400286480c41b00388003950b086200c602c107a01c2503030041c6460384c9801c2006000401594005001000d20f65000b0b10317015007800a020300541c003450001c0d56202c0d42c3ea200d61180c0000d1401c45440c0d00f48000c40840c246c02c60014200d00311124091040309140100000301110401c0e540e4000c0780840d00201d40005200d1312505029100900540365903040f403061150919481034225a200c1003c1d5080000340c0f040c503480b1501480910248014082c954401c0701d0540d041410701c01d0083c3c642e840442c003644165805010414400305106c50303803580c04106280f25010444002400a0f1030b43c800c182c417244115108404258104d00422400c0350300d90207400b80a0004140c8007505a503450f546081c0340d00e40c0c060201424440c2c1c518007181d0015801c00070b00e031306540303486410028995aa6900c494040c00701070b10880d03104000500c081c512548a20903107500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 920177634 1250 920176384 920176417
    0x607050604050313090b06030a0c0909020a05090103061d130807170d1d030417011b02010621050a02040f0219090f05120715020a050d1d0405070804030f0203 69
    0x20b040c0161241c00c281200584501202c0001480310401d0103440b0500304000c015614548503120041c000b090701d403d030f9506001603440002001c0019202070586420136031219556407030b2032000103048404c0c81d040b40843d03002c0a062500d40c1642c0080295001030040c030756085103005400c00740002c5c0200040140003002e03070171060100f4007465003c2e014018290006001040e113100c07041e88144c1840710070508a900c10700040040084035001c180e0640c10003400090079403600150402101c03099056000941c0d104c107020045504454440c1c034143d041800400c40051565035240d8440b100030401034842d94030f07216151080c0c401941200d032a40c0740e03003004a40c917550640c40503000c1031140c4140c0441401c0c0080010b42e03400c1c25004506102c01c1c4201600e0010b09107000b00600440b1001104114420311001500003801003016004203215a100c50407010030702d01d040400400d050326658080c9007000c050104d4160003034030340d0790499890b041820203101e5aa03412071841c02011103e03041e4004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 920178884 1250 920177634 920177641
    0x30c020f0c06071b03200301020c25030206040b040e131203022a0601081009080702090702030906070b091216030305190f0e10020406090e04170a020d17010b0f070206070506 76
    0x743c0d5484e03a1612004078007201e001b009044105401c0380a003030580d2100307810164800d11500801582003200c415090f101c80f200f2912a00401e41035041130b041350818010000c3c05020b06000d1a210b41d900500001e20006d03519607650b1036860b08044c0d58440b4090580100f0540c0e02c0c5003c20b82c0e0040c241101d00d16030100a81c3c0d40688030b076100c20030304c24103080b40942582035503200a1801400b20298103c03072960329090b400c0d800e00650020041c000700c11800140642c15803543d0b4200144141c5000d42020891810965580ba082c002d03520784000c411007041001c0c0400c40d80640020b02180e806080020340c0f0360700d525400d500450304103075807010705203000c44e40030020000f6482500543c0101c0b040300d2811103c400800220310480c0910004a1411002007108200700b4248a50041c1706560208415820b0701c000183d503049420703031001603000411240d120f00d52215940520f884c08860740d808a51400108502c030740705c7d04a48040500c000250340d001d40d2190320440303c0d940e0740728080f2600e526 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 920180134 1250 920178884 920178893
    0x81c02070209071b17090315390307020c22392d0813030801090b0d0b0c04032f01030507020c0a03050303010501030c020f0c06071b03 59
    0x10310008049200300c9803000070a080d54410444180c185a41001082d207100031038507050407030b2907060700f001c86112081020940940342403042c019054003c007560140c0d03052102400c0b4400014100b8021400401d001c0d40200c004004c00c4441c0070b85c4022100c503942d440e0500200d080141e0600e0081d089801000d4807056110b00b42608070349002c03006d500b0800e14841820b481d462041340105140d040c0c0c0c0d0b00d50103420a9440b00c4149104000c2420100f07501c0e540012400100111904c14104060910f0318046085401c001459441480051000710100480c1c1c0d0144c8051070601802d581e00c0d41c0c44018288949469400000158001851070345c035242c90044184190302c10700040f00c201c10200910711281c110410401004203600d41c0a4411100c000b00447c0103100c0103181001b14850b002c1589401d4450001b003c01840c040c1015594030340c10800050240c680d206110303011035004c01071044500070007184280d812041219815540d04150400081c0d0100d5111100c1165041c41b00020410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 920181384 1250 920180134 920180137
    0x180d1103151005040504020a27050424090203072106020c03090118120308060a030f1104050c040501023c0d1206030f03030908040801090609050c0301180807081c02 72
    0x200c0807102504102c0d502c032014881540c009440c02904000c0c1e004052148180c1010b80c402204113841820190281101c1c585068482c2500d040d140c44110280320030a05150000610600005c101300303001440c41540400d6480c6800e109030084407142c101c80c00350010b040402c1664007070300060299120401110040d889500c2050b02c00c0c00300714080c005180c2602032188880c112402e40ec2031100d118080d80341520046c03802401203600440c2c000e00400040c0c036050700c0c4610180107101b8a0122242441408200e41c0040c040c14111003007070004022583c0c2c0040c4410300c16043c0c908486230580200080c401e01d4400034110100f2000c1980b07072404142c000501c0d184e000c100d640c0c0e000492080f9910703000c1104c109000140070a45800d1908021a02a82290941707904c00c0d900c503450103540305041c6003144c2010604440591300d0701000410310004000303100c400312044008010030681d0030a080c0c2452900706005003599400714058040c003c014050382d0200c20f400d42950301e4403038800c070442c009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 920182634 1250 920181384 920181391
    0x50a0e040609050c031e240a020c1f0e060c190c110409050f07050105210714042c090604141c050c011a1c060207050a0305040503070b180d110315 64
    0x218170507078400b90f124010044040aa800c1c80c7e000e141150f45a041316140a54080710000342d607441210000e9240d09100c24030300303845203203041e00001e9007039002018504040d40649044140e4006110300382c0c02440348c1143c440f4040c05070a0181804503d4500a8400491109a154460b2a14100400b4400042001400c03505114281c0b1882c41e2508015100c2c1d0042c41404040c0900c0c050000340940c420141450f086207140c2041d0310b0f552010340c007010a6a00980200886490b04131265020914080c0305400014150454106500d0b00c005255500d0100074800b42840f4400360b11410f800f05c0078801030400e03402034401071081d006525030180045d8800c1c48520029844c080f003404c0e030071103040f034240402c960040110038070144560403440c000160403403c0d915258208041000120100814050503101e038440c2d949440c41c000406082c5146c69100c1840007004024108401240c90341c16214104200d4888003090302c3e038200044000d80f02950303e80c05109061410030704a4440e90401e11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 920183884 1250 920182634 920182693
    0x1050c04140102150a202d09040504060e0106210f02120a05060708090a0302070317040f14010f02070f050d1104020a1205060d0201080606070611180406050a0e040609050c03 76
    0x40c815401e01c40c1e0b06880c89900070703070384810807401551f0f40d80700140044812841c5004895a062124100009080ba103050340c1c00c64455a07182d40d101c120850a000f00401854414120340080e0050041601c41021540b00205104e4080a03008115034480c42d02840c0341c480c920442d842d004807461b0050366900181c1e1254041422100001e418110005100c10544c2d410707400341c0300b03891071640c850901c0c9058415441e4443d03c244001700f9040c104542c40d200812000101014103459500058107080c1c040c14524215000450180115902c4008400459100f540d180101c81500d007020316050140f083e410340d0090000076410a05a81f210414006401c0040204425203813030742004840031099500a0206850710005515460700901a0104500031100810380c19001441e201c00e81d400350f04902c162540c0220700d1b0340541010320030640500029100c2c2d0b5941410081e210707200c030500400c0205000e40320440340301001014448254450000f0302182d4950080030614040c04815000c5080c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 920185134 1250 920183884 920183921
    0xf0e0c0c030c153102130b041a0f0a0305062a19140327070e0903070308010e07050f0901021006090b040b040902060304030c0f0203070b0a020105070201050c04140102150a 75
    0x104c040d240c0e10744000301c00d0101c2c4103545030302c8025801c3c828000c10907000654082e580b02e0900f0700649840c0100b64034075070f420329465076410701501040143d20b0b6090b03485005500c004070a10004800082c4242c118005c4141c0a02846070003181000a02000e00701007032048004c500f200c6010051920903818030a6500e0b05c09290088a031101e0341400220b80b50880ba5100f50403904c1000703e21101d00508400e074006891966071200d07040c0760920300c2998922001d0f4000180c01080c075134031000c01400750154203410060350038159402000ea00480101e11006200002c01c4041c4d68001c01c035115908440840034440b181d0303148101c9005255007051076005605080c0d20302c25500d0b191040c03031803103a0300410450450f2110384003284d450a920900b104c8207241442a071025903820070104006190001c08a556094508002400d443d40941a0401e43e8100000e000d002c12003001a602910b5a8003281218404c0b4500100d24210046036500310382040101400180d01c1a40c00c1000741c03800c18114072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 920186384 1250 920185134 920185171
    0xd021912090309150c06060b090312031303080c070c08060a0b120a0305090a1205011b0e0a1a130807170d0912061b030905070f0e0c0c030c15 62
    0xa00c162202800000c0004002110920034a0040b200c4840f03c56080e14103d08402c5443d51072000b1202c440e04180a104e5010560810703900d8100008005e040000018a055042003030014028400010009007440300840c0003410030400c42c0c0503980c0b4190058140b02c04150b9800c1484c0d101c02c0300b500c1e4803500c1400c01c20452014146424410307940040c003001414141c1c0e1544040350550021003030640e010b0011480005c200d038022030f40b1841140204000949207410609481081040e004a1000d00601c1080119159580c0d00814110740b170300c104401809240400b007404d603215984040d8481c800c0382e000030590b801c002401c00243c1c0d100050803400340700c41503020b0303944080c00c0c1c02100000d4042c0300b05205280381001600d007624803c070310100c0c4451030210084031078401c24640742c00107540d51a02e50144241040f0003801413005401421900f030820f1201c00440100a1000066200c0010b065001c00b904100300d401240d60403099469510941000c000144c805440b80c004102c54020403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 920187634 1250 920186384 920186417
    0x9151409120f120408120a23010e04030e04020405150d060602010501290f03040b060405010608130305071a190b0402040f05240d0b030f2d030d0219 65
    0x301c40e445034110501c2810f02c80081c10440304030800070012a441d0381c041c40b42d04500e0f014100039600501c904070010484815124079a04401000e10200210025040040083d01414240507800640500d040054054010080f034041d116907800346030009071014004a5890814002d415000400c000074400307141c0c0d03a00201c1c240e030b00078094100d8502400c03104501206149240004800ca03680c4075504200c03200310092025001140e007643c40c41281010052103207468450940900254104400c5500f0b03d9590b4031160b80002500909208001508a0070312212130580c0701442c003444102500c0c0d141041540c00d0007080b00c0c0042c4416030400c81c84856900d0b240c02a00d0a032510607851443c080d10740410000b030a03490f40e00a02181a000d5000303105c0003200c800402c10300d03551120100d0410f0300301051500d000702111014180f81c00c2207801d01e4500210203072428604000200003c20454100e5100381107129400140c030320b4510004200c00c00100b640010402100a9118200d4100c01d1449 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 920188884 1250 920187634 920187637
    0xb0d0203100b0f09090606010f020106030b0c030601020d020a0c2108030103121d011e031508010b030706181e150e09010b1905030c04030c08061b04080607030915140912 74
    0x10503000c17940100300010000c5d4401c41407035140f64aa0b1001244140d036907110449020400d880c40c43c40d4000000c00c020285d6010401d504500c041803000f02585145611100c2250846014070855190081c98041b01203032500c4d41200c100c2e4200c04060340c2e9503583d1070221103440704520f0f048045032480c829450b0354010803440d0811140103071a071780c02a503031116540034000e04500e19002031550362003107000c0f00b41000306400c1c003405c8136000008a8000d0365041500c1c0059640c401810000c1c401480f00c200d541e0840160102d03040f0000f05080713040122309010000d40039404c0740800c01c6074003a03d680800d81c06030100d02c06603c10369510015076211696841e42d40700e6042803403040700c03000010103015482500216403241e040a06141401d80741e90f19a036040b0314940c800c5180e80d000e403040c05030a050b032640343c0264150010710340745000d00c2c100f48651255002007043c003e0690702d00706082840302c0b0a80d41c0503410004101001031842400c00c102e00d050056503000031622070068840b080c6101c600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 920190134 1250 920188884 920188891
    0x30609060901120201080a091a0106080a02040b071e17040e010b040803070b150d030917010c0207091a21010b04021821011d0c19090b0d0203100b0f09 66
    0x1860b543c800c9006400640380c0e420b01038031b804046a603c229a0000c1107656030f16a0208411554640d019498604001c0c41da050103849200c1c1548100010000348056408031101541d100042514081d41c00500d070380d071101180070240001c6107121528040318000401030003070304c200001a2000d80d803109241e5586002c0c6010b121016803082104002180c910b41a05601008143d2420004400d05020a25103102c0c2d140c1240030460901c4240407c07150520540825150b8030002c0280285000b0002d603940018414440d00d0303a035900c060031040b100c1140d640d1000601400c500c9003080d030201001d0014070280c40f40500d5510704862001549818000c880d68880321035140501f103483c200c100111020b50103100748031a440110020720829082c00b0302c031002003001103d04200348404280394141031002145520400400d400d841a032200d000c2d541050381c0b1402000a1034001220101b0410100010040c1d8144030b0b1000e500c1d41500c09030010946400c0c00d0b40c2c2e91004940740c0e82440074101054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 920191384 1250 920190134 920190149
    0x9080102090a1e0504111201050907080610021018060b0406030c090e01090210020a0b1e01060f0c0212010c0207050d02030307062003040b150607110f04020409020c03030609060901 79
    0xc801000918008560f90b508040100416050595110000b8003260855404203810104c0400e600701020000720f0010300414099442200d02d00d04184010034440c00181504d00c82d0305c0780e8110307081c440e10801c9116045d00042d001040011100340d880b031141280c3c02c1048801c682019501e0700035040900580007102e512020200c0310904000115025180b0402c20060b550358440b65100903a5407a45041c12103d006c0d00600760380c0069007040c2c82808401070a000b0b414090307007103140310410117084050440d181c6180c5045880503074141203e50040292000e035108568101c43d688144040d0b2000460312410703001ca4100607542c00030f11071504503e0a002e075150f0800e1244c600410000e0f000301007041c007210388040004505148404242d0012344060b00d40d4001c00017040203002580c2c41440410344200c0311039050802c240c4e56102c9443d041c40742d907400340e1003451203e03400342c6a41e0180c801405014206544641406804546c0d035003040f18000d10544175038021a5042c05c210000c14140e4805 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 920192634 1250 920191384 920191399
    0x1b0602010e0a140f0303010b0909010b04030f0f03091e080d0e0a0b0307031e02190503250e2206050f09011a090907050304140c0121091a04030908010209 67
    0x2c54a0310104070701072482c0d04040b405908045a460b60b0140010740c0a40300044ca40307511a81d029040c4900c01e8016000004052400c0000b400402d070b20031000c284661b4400f285078242c04a92800711480411684511001e49817107480703035110984003600c1c42c2920490700480d907201e0b031101d1040f681e000c1c680c0262604110b5640381807002c040d0a40c0290b52040041c00c1c040303010034996440e940c0954524019014480d40410203c00813448107440444600c0c20785011419400c040052510340742d40da8200080d807900c002100b10f8603502407240d001040c0b100810319100b0310051421140704041d2400b540ca40145030440105007031425640043c0c02550207050501c0b540e0800d1440e0789000801446010025414480c818460380c801140d14411050340e940c4640b00d051528114600d0303101c94522560320340001203080903607603021140302d032055402289101400d80280510340140302680e400f90403203034400ca00804000c12460110301587c402ea54500001c0c2e40c440c3c15500b00e00a40c811540e01101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 920193884 1250 920192634 920192653
    0x80901060f0b1305100c0302122503021f060303030e150c0d062103201207032a0302060a0203010e0a02070618060b121b15040801091b0602010e 63
    0x1102e405411108001c0c07041c040b1040c0c42e03000207149040c90107005000a0310340000002019414000405a8101c0007040c6003001100046130221501521002d00e20b40c440d0b200980916108210380d1122681a1601c545c6140031000c1c104046e0940c4e02040c1d0100e410300b442003201132000103081103c40400031250209450718111145290300490010403115291417011550140c00501c11044420049500c020940d0343e26000e48420000b000401c0c003002031000d401204003012420110030005454015518000d030314007a903250061102d00c80416103005105504078102500382c1090718040d400300d8810381d0b5800c21343c8041e84004d005845a52a146000c5400c0d804950044c00a01d072040001040c10120304904103102c4452907801c1d602c45031182d502202c1424804207250728810380c030000e0400013071008900d15940c0304085406014004d803400c8801158814020349020381540e0009201c856441d04042207036000c08004080240c00c44000010040e00510030950071480c81030250a203a40c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 920195134 1250 920193884 920193899
    0x503032a0f070f060201020310290d0608070b0f071e060c02070e0901090b130c0e041a2203200d09080c1507060203091c030b01080901060f 61
    0x30030600200d04a03111501101040000a00c400c58114000000620069180410202448a1a40c002025648104240f003243d05405900303000b0f4980741d01c11002030402d007011035030440346170101d20118520042210200c802c03240d0850300448400f0b008a800442c0c0318442030505200c1c50107000e08401e801c020322000120454081600707603055004052324a01241c031140141c1c0c0070407070201c0040c3c03c41502806517141a0a40f00d4000c01d20b000204182d000540e1140c5410001a111044102c2e0080c0000104011904041e000c0d00b01146d8030f03035160409240c00d0207080d07414110205404221030005c0c0848550b44180c4081000a0f070003e1600c1c107180e24151001c1c0307507a44045844404086148444200130000d41c09210303101e9442000b11860800d40a051240041c61f19120700c6070304c8074075907040d0001d1080d5103415401400060b80e0307896119005180100004642084c0100c9030462881da980550006001100a884080140c1c1d14009518222101c40c06800c1c441d8a00030410300801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 920196384 1250 920195134 920195167
    0xc04050607120203040902070b0405061f180905010905070f061d04021602041d0f0a110907031e050414070630110304051506030d0c110a0b0c0c0307050303 68
    0x41e01c20f005992516403251100c0c400d03a4080f40c0261042e29200301400704200040010542c80200c1c0300642c10744020710311920080c015140320f21450801d1a41d10380e9030802d065032007100b0f020f501400030083e001080c0307080c030b40350f204c6031041c1149111051400a01140a000c0c450100c006c000c1c0380b1008802ca1f0003c000007500185104542100c0e00544200161114030031500203400316010003842c8010103916619101d6200c6080f14150840304180c80000c0700f80b5030b511031040003100c11500a80d907944040b00140101d51030f2509515554070321090442599002c20300460180901d158500304802419641e00740910602d80040c0c0340c90442d01e40d140c20900020800e54400709042e49807110b512501040d1400079071944400c2000200b8401044000c2200e9181d001500b14a4611482d003180001e85030740d6000d040a05105400c4005001c110000c01288000d1000412410301d035500d40000c6a620b07001103403604071520403242d5000080c0f5001641c80101c0d00000d0086141c007841c0001c00d9540c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 920197634 1250 920196384 920196413
    0x3030302160b1f08030c0726060a020310050607020f01031e110901110a170901051b070602010b060c122206030905010f06261603030210050c04050607 66
    0x54a111561074400110b800c0071403801031020440880110003110100c010700a070f00d07405070280350b208015909940101160b400c007182d160300d00070441c920f4071648816680d505404500c1607401760380100000c501e52580598004c00091504403403198584041c00f106202d10039020b0f601c03c685c1c680000c503661103a000001700707c0507c5030300317460903122029410590710303d0018280303c2800450540700c6561b0000f0b034001807400d080c008010601a60301e403201090002c15110110031000244208144d010310102d40704685002c0090300d010401000c980d88586450043c0c10055081c00c4d0101d2142c031b01030085d901406280b90181101c5841d0304440c07011648203042c4034040040c8450804400d1004054400c01004951004603902c0c40500d4804d00b100c003000c0031070020501c1c120b82480310699080c44041c0041070315003203a00744131080349002d280508102c04d5003a41100c1c44800301c20542e02141c0048000b1008001b48801d40360808062540e00690241035000b2809005050100300c0305801170780c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 920198884 1250 920197634 920197657
    0x1b050f090a0c020321060310141602030f04140111070602030f090406090606020a0b010803120103030804050c0913061401080a23010504061b080601140703090e070c1403070302030403030302 83
    0xd0401c0c442c01540600c11700d1182c0c2c000300c1d041a401c10482d800c2c24081d042400101c3d03101040480c0c1d80b4aa882c1e1090800b4111710f4007100d0224100c060503000b0001c07070300c10f00300405490380c896070340b01d2074250102c100780c0405000074150000807408190024441c0d05564040c0c01541c01c0a006225008150b001485141e900c01d031903030400070384c0310614815400034090035409003030b20030030905100414800681c0009216801003140c1d0800f0340400c0c100c981500d0741450f1401c1c0d10740300c41c01d01d1484c04500c84031240c3e100364120244000280090b0900800901c035003801d0112a120800305051520309108801d42600070041c1c3c403000810030144407186609140340a2a1488026001402c44504031011110a5a034045600410041d100c0b1074180002d2445c0481003464144002840da590454001d21403506c04211a4101401040e0384000f500400450840515000d900101000c202400907240c8040c2002e05020410000c800c4686450705600114900f6107540c7c2c08800a51144c0e00049 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 920200134 1250 920198884 920198887
    0x30b180c06031b07061a120d02070303030b180901060602190b010e040c211a060d032105150108010f14090a06270e0309010c060b010314041b050f090a0c0203 69
    0x180001e00e540309502c8404541b9103241c0c561241c01040c048004200c20304078000394803410030408115800200709050f40d62514011407031110b08000309801c040f460780b0710089141003c04011402e10150b00c41000c031002c6e982240c0758500e00039a410700000d030465014183c03071406801886003060120746241c02522420b010580c3d25607408655405000c0149442c1c00c07000020350f1841441103904a080f07151020561000c0c0310b04055000900c601c112190080074070040c0004020106201802807114900d4040c3c1408940340c107141001c1c2c5a40c844d815207021030000d0001081c807010800940301640d000400106400d02130204001c0d0a45005194001d9075880343c80100700103004200d01c0b0324411400c0351141c1c10000004407402581e03168000e001030b0758400d01020005a074845c1e00e40c2001600034400043d4406044012400303041161841d905000100d0305000401c802da0644070088142a070314030003101d0b103420800c0801081c080015074811483d00c0441c40701011507110402443c0d00b801240d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 920201384 1250 920200134 920200147
    0x31821122a01060806240108040201140403030801030b100812071b080c09071803060b032514030303010b07060507020c10050c0114070234030b180c06031b 68
    0x6020350344040e103810480780d443d0342081202c103000300507064100c00c04540c1e041e80c0030036052400c20540b90300030b180340c10854040c2c041415640915060f00b900d600c8640c0c1c16590301d8a0382000743c0b0014080c07000300c6400c140d800000d000c1380c0d0040c44181c207440d083c102600d0074441501c0c01544641003a1426200e8603695594031000c0280e2001c4d1500800050010703090b403102e20b808100141000802d40b5052019007504074003c21402d07101c0200340e0b54484000a110703c8a20003091524408101074428030680e01080d0102d068807040220443c4c01030b0702030000e003c2d002400c2c15201d000c00e115880d00d511051000704001581900059400b00725881201c141c5c0e4207030340000e24070f244001d007598041a400904c5a48020b8207003d004101019441a6030a6040c5650001c2d560034060422003401105100100c03224400101003106200310740e039101c81d5407900c0741882e071040c1100342c0301c445007501c0b2180000f49400d00030808555a0000901583c03c2d0341d40c425400f049592008111100c909040020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 920202634 1250 920201384 920201437
    0x4060f0b0a1218050114040521071406011e030308060f1801031b050102010603110103020f0f03160f08040b150301180c061107080d0e010306050303182112 68
    0x14403c10701042c1000050003481424007500f11006400d005141114200800c0045000011185801c0b0120365030315401c45600c403c1c1003280d0062000c01082da8041e070313200140c112800202070381a80c207480321768902007000d114a620504810700c4020040344081e8000f8002d4a015815950140c034050060b00d150021242d42070000c55007604111010312911807849a450061480b8101600c028002044110b0440e102c26401d01e5490111074105600050032113011840c00741610454140c0a441c1038590407c0e4030b8014070958405004030000b2005c4081c070402d20b1107490307114012500100020741544952608442ca0000410b20030b401d5900c0c0c2480103500c004501c0403201c1c080c0034402c0283c18074140a002030030765407880c02c04403250b8016201404408800704094644000605010030004441d10058010b80069442254140030215202925800c08500d8850241044403041006d2030185100300e0b802c449a028110268080e030f42100960180c0c500415012602c5051107403011320700b044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 920203884 1250 920202634 920202641
    0x60a1d0604050a140d05090f031504030507030f03141603110403080c100c020d1d0603040302011407030e1b0301180c061d0108040b1b0307050c0c04060f0b0a12 70
    0x10100d0752a4085510f49050040320640b52200449620280c01004440c58000b08217001d8844013901c9200343c1d0040900d00c2c2e40801049040c8203950031405440c0c9003a003000f40c00c54020020990101d41c805180c928158801e01c18131100c03d2100500400da5241d0402031b0361020440d010500c01d15030744010148031208503002030701c01903108070701d210b07038800490a055050410360034200d0041130809903440c95242c0c000c648402c004003e840c1c082c0c80c4008040c41400344100c14184c098104030004140401c0c1941900010034140c0b0f03a4800700c0c426128054110304541d5a050100300c140c000c0c401005400c4013107041285040c400030004100c88030401500c403003c541201c0c00b00ea80301c81c180d50030081243c021305a000c5845d91141988004101040041d005003c010401444d4a59550000d03000c0c04802501c51446a44854030a40302c1c6000640a4010390161400c0102c500c030f60742200c2000e04d8a0b0040500f5204c83d5091510402c3c40e1140a1401d500000056400e10841c0c40380104500300520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 920205134 1250 920203884 920203891
    0x210709082e0b0105160507051f030e0609120703050903030d0204150503071b030516060605150c10022b0f050a021e09060f120106090e040302060a1d06 66
    0x7107807988103070710164854200015038a01d00310520b0815140c40e010303030f0300700059030044e0a01d2441d0410b85800c1c1d140c0b00d41085a2908080d0348010888101243e50509004454842000303440c100071440c0918a090b41c5d43c10f044544514642c00400d149040b001510042e1914500c2821b1081c24800780400081c1107400000380013000d03a0340420104070b030082410b036074000170381b680c2042880d505100f03c1c000c2031100c441da80ba4010101c080844010107124108a4032890070701c1d03041408032080351078008050b00702c51207514451481d011003103a01500b040d003214a40c10079080245220700604a080c400313904110712102c40b0b04445410140f41050054400e8801c42c040e00e000203481015641d81c40450340302800703c55003284140100c03c007040402413580c1c03007800c1c02001140c84184040020300c0511a00c1c0c0410200103002c5201c0ca81c4d441c50f01032103416541540c8445008680300c04001d0308241c0c0480b03001d401a44040042010384c40d0341d501101d6000c1103228401c2c440c49180c1e035203030f01d0580d055 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 920206384 1250 920205134 920205163
    0x30324030c0f190e101a2703010c03050a0b101e110f070911030402010203070609081c06150f1e020c12060a2d05100801050f0106080c21070908 63
    0x83e020032109404050401740a0801102c0402444400002481090051031095110300700032000303031082e0076520405188040030040080c8a0710108107002005041d00b903030300c1d88400303040406214140ca45402c1d500030182c2c481c0d44112804040712907041200c11040d40f00c0051065241000e800f024040c0b000c1040054141d0040825030720300341302001102c00301c00101e09200c9080c0103100050780e01004503000c02e90001008074003c2c01505180f50180300d02c0c050700226414200c4422109200350b0000e030105d079540301041d809481c5650055804140030340d006400500c016042c405136030601c400840c0355808500c11100d00610403404101c1913424110759083c01d500c102c081043c0c48855000d40307202115400c000c0104005008007a00b00d000026030240702103500d03500081d6a50045810590003003001000900050a003c803c0c035000100a000343c4001441502c0015070710a4180100c801e407181034045400b00b41010086182d20b500003501c16010400566030001c0c410b00200f0045110b41c044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 920207634 1250 920206384 920206409
    0x613030f0302030c0f01050c03040b040c0512070311060301030803040b090309100c050c0d150e0f0d0f090603050906010e090a0221070f030b0a0e0709050702030324030c0f19 76
    0x200c4080c14580817034070b8641e801c26030500007040f01914031003082d0b0790003da001707504225a84036403038540d01c0900740c2c0d04580d40010042c511032505000010340c60086034000d80c030944103424030304203000d410b20090101800d5a0020004074000a04110089510400000690b800c10f800300d400114420b00b4098842c0c001009601c041c42800424064496031850803144002c101d1070719a00c004001d080c0c1780c07502051596600d1490b0324200180300042c1104810001d13520b00200b9840c0240007042d0540d46400090061000801c0030b600030310400303001d131310a080102a41d07841c021861002e582c0007444000705028156184005860b039003080400d0020f9240d10f0360000400180451400145601061a445c4212020070118000504080d0071904146000c2180c3d0342010300e441c60440d20b0360200701035900c5d010030098003580c0800950301803250000050881c000414409001c4c071089548594142c11040d4a201c55280c81c041c000c41c3c0480c050008804126038103480c480420481e4000c4191844 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 920208884 1250 920207634 920207647
    0x15051e01090803070318061716030b03060a0f05010b0a17060a0b070c09050a11180f0d0803191a04051506210c0316051c05150f15090613030f030203 65
    0x159108404090082c91410f066a0401c008c00054282000341149285200080000d090181709410000440c04064100e0341d4606000480c80001c000225889040d07d140200106031070740700030120f4816541550b2a651040c0c41d60b42000d00d040c0c805000300b940200000d60000d0300c043c910024050301d82c0101090902c1034902a1101c003540c60050010240b2131901812101502c0c0381410b450341e0802c81c07104101582e8009010900b19880700c42035540c4030060380c02c1401000f0401c00110310031031100314880c0c4021440080385054138920184908100c0d07004e01c1210344c0c1e080c47d0740328550103012900404000142070001c650241d00041e00040c13941c86d50b0602c0820402e4032001c594002c0308040c02c0e9072451030030364814012040c80608980800400141c0f90f0700ba502d4149900000ea4040c103020440760515101c00c4020200c0440418021003500c9861009483c01000004010310078000092501d01004100075613680090030800380e94410440c00b1000c21890254090b00c10f100c2c0d0002c0d551040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 920210134 1250 920208884 920208917
    0x3030b040c020607090b16022e0804020d080904090c080102040f0e010506030606032d1e0f06010c0204060b0c060f0a0c0e040b010c050105100915051e010908030703 72
    0x70031a0030070500b07560200c8148100c15600040081c11241440785090b1038034900b007180264007030107490103076000c0044034000c0c05505050104a108481003030720004c02240f804015034041d00c2c202c4010b98050643c40c0100017140003240240945000203000181d400490781d6003190711500c603000200e250398045010702510f81c400d0014000707400c481e0356004c001c0d85080001821888020581d902444c07010020503001c1e181403c1c41c3d100b01d444181c94003041054030f052413040c8070080b20a041c0900340740c80d0030414944c1c4c002c06140580d891810131425a07645000648102c1508003040342c010b90f4800e00001e800d001d0001070400f22302104090811400c211710102c8034450081e15055005103444800007125400a803101e424a10135200843e0300700d0b0000042c0c540148007030004d086035080000700f2a50343ea10342909000e0b07802c4000304210107140c0c081004400c0905004590f000344e1044c82c5406901e40440c2d041c0581501490100812526805182d003140c000b114110042000504d801400701d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 920211384 1250 920210134 920210141
    0x2202090f0a09020d0309060210050121080403060204030602130b070507050108060126010611030a0c0f0f0209042a080a08030603072102010f08070507061a0d050c0f09040c0b0307020c040903030b04 86
    0x2909c0d41c83c18451541031070b00707150440f05120302550851002d818502c04000c100c005480045800250031074540d40c2d641080c0703019620110341c2c90384003510400e021400348214015603040503000b400a0050340e083c030340191100b040c0505024140300e8400e402d00b099070040c110462851f49050300d0410154036203d0040c00f2090784011402c6250018050030003610350010180714580d03040b5005059046480c2804d45c4c000d1030700c04020350814140c10400081c45044050b804120b2108010400c04424110f01e940342044031f40100c441c19005840040c002c107074240084d60b0008401010798070243c0ea106108103a44549002d03102c10404481d44070010356801405c00c041000705801e010000f40b0304400002c1c41842010310050030542d60380365500c1e511800300c074030f0844d0300c5016210000200940c03c21a0307560f26200340c038a10442c3d41400c00020380c00d160511a003c0c561000c0009281401d094841d02d440d04000d141504500c08c0d0b114006075503983c3d0140002d03050007618005070000b044418882507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 920212634 1250 920211384 920211403
    0x11190816031208190c091206020a02150910022a07060e03120d050a0e100f1803090501140909011502100b060a0e031609052202090f0a09020d03090602 66
    0x18071032081e0802403c4e80b5003490000d40c407482c414002500d0007140c20203664404e400d1b086100702050200300c08003000096401808045229000c40e07070030100070181c03115080c40448004115400841e0107091540b650303005801100c0c0c0c4516000c0341d415901c02d581440581e252610314040d0b11906003085403a8011403502d40105e41903014082c0640391100d203000768400d14280310b05017552600000c0d01103800361300200d0014402d1080d20381d25484d1250020243c52000041c0707240900c0c003101440048603516550f4042a81501c030b601400b85440019110600d00c0020140c01c4a010000c9440c07907a00c900485000e020203001c04900c0b02da054074000d01c1e2181c420b0501a01700d1401e49900695550001620690a05d91a02010004121004c00c3c10241540c0000280e003c12950114002e41c15404c0719104080c4900c542c2da82800d80740e6000354455512401035000702022010034590810503031910b40c04582a030020994645580c0420050001c0e01000d034002a2806400d101442e41400300200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 920213884 1250 920212634 920212637
    0x4020f03091c03021201150c0c170d0e030a0201051b0303010801020304140c150d0603061103250e06033706050102070602030f0304141b09060d111908160312 69
    0x42980c14150345c13008aa0601403020040b01e650380c00f04440348220205080d190b44900440060366590340d0030103009000045240c420b000b10b00001e00c140c0d204403c1008a0003006004084802981e001596203901400f528040c4500121281000c410200000d500814850340016030f2480d007402d144060f400c039400000c1260300504480681a540c080120301c003003c40d0131046903100081c0400da4000e000c10342c4010622410002c011f100071032000c02441c45029900002c3c50344d100c201c12451030381c401c01280c01c808030b40c01a10114040c00c244000d5a4030490403200101c41181041030080421318020b40000f061600d90324842e100d0107180180e00042c0420300003400f4860509001944078000c407a0005d410110210014080c0094001010000846003081d1107081c1c80f8007003211000f6401120007802802400041801070420502e05166240c1040c0c40b0a1462240d1040210085e249040b41c200c4801c0074001140b15002031001640140280301c808880038a180f42c00c00340c40e0001c050560 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 920215134 1250 920213884 920213887
    0x30f0f010c1b1502090d050a3f0311040801020a031103010b0708160b070215070807080402010e0d0209010902040f120f0b07021501171006060e0f04020f03091c0302 72
    0x900e4150302d9902628110f03404449070800c4140b44005000a0061414580d40900c4802c02503061080c080344c0b801c0085c6c05144942115481c1c5803403c401141c0c820683c2403202125402030310301c19803e4492400c646410319000c0303141ca00c042c03910301035074200c0d4000c0200c0d654005044404181c040c481c2040d050000b51559007550714144440006008004010701404000503861030403400c803800070200e5603800308e0540900d041c0034000039511000401c40c040008450804608040d00071503015200e0085c0e0f581d1513500c0e0740d0315801180c8901d021400203404c0000003e0000c01a519103030305501070040c3d0700005171518034046200000b000c183e80400403041010106101151003403e83c030f001141c11900210b001d40341d04100301d03d08040600d106084e426150004a807040c0b803030110070040120340c41160800c046144401c01101c4d414407a0201084401481c1c0085062400c1c0b09240742000501c018100080c0e940318025a03402143e2154003038215064038440d1848820843c1134600b0341d0b28046 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 920216384 1250 920215134 920215157
    0x3060418080a03020d11120f0f160f050c120d060e04020f09100906030615060e010207170f060405010c0f14041a19110705330405030f0f010c 62
    0x10480c071030011880100f64000920041c4045107403c807606000001c41c1d0180e07100c070507594130890b808068940e001c410f114080820540d25112007094080c0c50100a01034080031002403c1d10004284500e00341802018809001600c0b030601c0040040450302425940d0350002ea0800d400300c411a8001c01c2c0c00d4002403080c4409a141c0f100d0f40da00000c0c05035450740030390300c68451411407030300c07150b100c050b243d410482e01104000b91a0071810000030b40c0300c3c0b07468911b0348074501540c17070074654140140160300074441040100d000180012140214030240d40548030142003190900a044805a82c169101c0c82c416071303550b0703215a40348103c0026181c00300394109500600b121380c2c4640e204184d00191000e4008584501241c1100d880d4507513028117400c1a01a03000180c4a0300413055100383d01d00910000240e90306100285d4008410703081245040c040700da407000106041d070b811807a03000c2101031001240336202084401030352040b000003000035090001819095803642a1140104180c9400300e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 920217634 1250 920216384 920216393
    0x10806060a1404050c160501060323030d09021f0816110604080a090f0608100b032e0f0b0301080c010302090a0509040f06021b010e2415030102070803060418 69
    0x2440e42c00802290081401d4036805a08030183c059a20304c150300001100e0300b03030304000c1e055200c14100e92140c4403404440305154844801e0f41501d24481400e41c004114030041c0406c40d41c0011040c3d071008140442c166501c0c81302141041c0d01e83c601c44c0210355071105211030345400880f440d80d024a83c0c502803040c3c050700004152507010241005203940341c00315000104600401408001e8031008136010390741596003100a000c44d0302600c00da07449414080c00460400f00000807284201660b030402089244d48000d043c0c42c84121050181560b00b4514021600c202c401c520300008080c020301940e100c0d41081c0c0c0f0b1030304080e065440241414410404200e240d11440856803c80c3d4044641940c03d54a50801014484a41500902007840050144506007c3e05541030340102d0b90402000940300c404803903a078450418101c0032500c1021200e001112043c03002099000303080021a5501403140c8021a00303a0f040b003103044403070305004410007219003018843c1e170b06900601c00e24201441c0d8140c0b00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 920218884 1250 920217634 920217659
    0x1103090109050907020304081501090e0c0901060e0402090a09020a110a0b0441010e0a1106070503040314060105041107020a060305130f1505250f0c0614010806060a 72
    0x111405005900300184e500c60003481614001e10708241034900c105211096011141da0902880154a28080d00c98800281c001031280c940c01018049004a90804c0816288024420740c0d81d41d00940810002025445165140008010320344000d078407103229138000f4104002204407a142a40324a5151000c610a01c259982040e04071544181c03041102c00210100c09a203003854190300d0091858007020301440c0126200a240036008110328210840f2240c0c42d00035660024020550380601c000440c50010300500308148a04212403a2696a13680d4448646c501640031085410400c01048a82810700601001950002105140c18115030001e0410144c2e4007131b000030190341c0d100080c1001009801ca5468a4100b002d543c4489018588580003001d0407a00c0054142000081501100b004040381d40121055211001c00300e04124112407541c08002454101711142c0c0c00c60002c02c010707210314401040d1001c0440d11540c14910308915204000c0d03c034500405481504124098503d103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 920220134 1250 920218884 920218889
    0x3070809040f0e06040f0b01081501231c060606030204053f102a080406330503190605060307170d0201050c0a05030726010603020a1103090109 63
    0x890009081c665401160b0040c60b11000314071051044000f0303c8248159803000c007101c5032003024146401e0f81c0b5020240e4a0305401890003040204e40401403280c5102d102c6154250b550161014070702441c4030001860b4003503000203500905072240362000c01c1c000030307020b41d00c05010710303080540c58503103404082810009000d4aa0b140060883c100303456000d01c00340c60190194180d4401d03000000101c1c3d2440e19040c20700e01c5501c6a91912004044014800050b004007200c041d40e008a0001600015500c90400801c00c850b5580c3d5202c0c031250104186036000072007014182c5207400800300b5030800f52050b01c55041948640c0c005454500c0000e030004042d80d100344d0051011500340c0300c100206e860f10000b6004400d100090340d1003095906c0f000250b81c070146155600a105d19150b1154008180c45104542c1c40021020030001d120603000b40010408034403055002120200ca48010800032002a00402d0010390000380c140c0b10305138000c2e02e8569001850004d185007040e80c20028016544070b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 920221384 1250 920220134 920220139
    0x105060309011d0d1803030c03050c210d14060f150705100b0108070908060c0a020f010f0f111309050c0f161a1501140405190905010803070809 63
    0x800121070090030342019203409124020070741281042044580c90700d0290141c000021040c01d00078a06000070710280045940540391550548421b48040b2006c0c0d100351007000c254803d0300055140c0888001001c0d501c1500d06516076190741b90740b0062800e81e00c03481102c0200e9130703481c4144405591503032090840070b81c0481d4840c0b01d070040040115898040c481c5d02a14074020300301d10070b681d10665040003a1034042641d46840303960b03513644142c0d41c0d400d49000e41c8417698000c10000c1c01d41c0e80c1240c0284442c0285004031f880d503001c0144018256104000b01e814a035807078620000c0010428011003d46402e95882d040c14010082032000310f018803842a0f400d26510b600120302402c3c0414119000c90b00301c507101c2a81c3d031401c0c001e10440041210b4007181c91314280105281316001500b202c40c010513569020800900b0072000442d4800c031041440541c80c2e0041000041e599141c25548604141c04ae0000785024a040d4014040350b40581c803c000c560410480700c800901d141c41203d5500504 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 920222634 1250 920221384 920221387
    0x8161107090b0d02031207050606030a051005040c210506091902131e050411061c38130603080a2a03050309010c05190509061207090315060e010506 65
    0x149400a003c90f481c10201941500902115180131042c1030000d2180301d004008464050302d521042c5070780c440d140503000d04140c01110109203100b60641050303411500891400000580b00c0400d0180c040c0c2500c1022403150b5901c059a04010051080c90741c8a101a0050314441e981c1e00c02207030820540c08002803280d4010790023001c0800310f6a0011010281d116080760b10300098418803c01018162429180c40c03495202c02e50300c52500c80221942c401c3c10030b5003904254002d280a02c00340000c0156944030380c0c03045116082c1400c1c01c41c11445084038520034024409961707800d01c8821013110340e096005500f00f95040c008078110400b1a00d10200781d10305800304003414080c0c2e500d40702c4196000400350404e0000002030540c04400b0f540104000002042a0f80d20300e241902d075071003110800020000d8200318209100e0081010301000c8201a20080c54420501d80e500e080c0b2500715000e5000c00d007206e00c01d009100852154021034441c400301005620b0a00309040c0703a9500511400b07110324070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 920223884 1250 920222634 920222651
    0x901050706020f0309030a140715020307090305060a150b091f0207050414070f0306031101030e0a05030a020106030b0702060c1b1f0b0f04180b04030507050703030816110709 76
    0x701da41103801c03407480b060910f07480b42401c2c0b40c0c00361651f00804440b000a19110104205181224100c8920a0303002c07182c2550130407101c0102e80a504000c01d040d06200369a10000003181003848080d100f501d026400040c07980a1a4620500300b6850708000100325041c000850a506c80c4042d00e65880384406646d500d004880380200d103040c482e030304029005810848092403054180201c24040c2c42c0766150b240d1250f201c4001281290403d10011301680104040c030754040d4000c0e40040143c51002c0140d58280f011512080c0c40d40c0d10000717400c4010b039074403a010014407000144003500a4000d00c0580458280441c006d00700703000b0b80c11a80c103480c009000194250504120f41c0080713039004007080120045680302c0f04000c0003c0b225250080031440700ca559249064416a1521070105000c91105412910341400d0400014001c0b41841000c00000c00482c108102c40c81c0254840d50f1003003294900810302c140030081202000c41401026180c00075406c00100702141982c1010400045403034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 920225134 1250 920223884 920223893
    0x21010e0a05090a0f03170c070201021011160803150d050601050f1314091c080c071707060e1204050d020d0303290f0324131e02010f0e0609010507 64
    0x40c2071440286900c1a109004040640125009151140c007441502442c0d0b6404000c00852223050382c020300503002400540300000d0b481e032042c800304004070103060601008031515000091118005c3e00d0a01010081185503030112803803209030481540c00e055081ca2581e00e540c1c0d00c3c2c00600031300340700d911104403030446511901e24601c00c008032403105125001500e005884910000e0340c1071005401400d5000aa501c6d80e04072001048560f560365016076900c1ca0110305041d0414001156005c407004405000e02e0705078000b4085084c041d007800144041055000c82c80d11682a0005011810a00c4100000d588000810b01c1c000c2e0140c424842290350f9190450041565403180c03808074100d094040484880a2010394a1190580b11501d4810740802050b560f4403c3c2c0c10700e1107031480c0007120b00801c851950341d121780040103420f4100318074003641c0e070309001d1a0000e40520030021801260070f0540d80d002c0a0411840c5940c100900541280070101d0707010320440c021941801070000c0c0040812 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 920226384 1250 920225134 920225143
    0xe091801090803190e191b120c1e0f0b0c16090b090c12012304290f1f18060509130203163221010e0a0509 47
    0xe9901002580c0c1d04d00d0680038810f60040c2e0110701188051400c0100480c402001500c0c8101c0a55543c4100c01d4440d59502c008030080f9907181d100014800940001e00f02240c00c004c0d0700304600c40c5030b020031114186071181d42e0108139021034500c0116000030800002d07140d00451001e407001e101d442350703940748100c040624010340748011081038507280c1c01c002082340055000307600d00e50003250168230f030740c03901c5a401d05113010f51102c5008000702100100910301c1c01d500300203403121107003a1a040403405d4100040441700900303400c2c84000c1707840c0c52640350900e244a80503613120044400c242c01008100109401c864440100b901030410b1400030b10f801c600070801100d003690800500c00003240c403501e0085c41c0d9006060311601584007442030340e2800e4410f00076a80301700b8420303c81c00c8003607085010441c1c2d8100003400c00c40e0f10b030f0002c50068400380708480000f0f50601c10038100070b960390207502c09210031074804002c548654400500510444035503c51558102e549802e0110301347d100c00e00c005040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 920227634 1250 920226384 920226401
    0x90c15160f050c010311030f1f080a0818120606061312051c0c0506070e0d052b03060e060d0c1211010206070c1208190c020c09070e091801 61
    0x10401411501e030100040040d55400303d52082e0790520002d154101d4410113400207640e03600340c4c0240300002076040c1c9020440c1c0f40c0445c0c4607001031038800f903942c0302150602e140c4000548460100040c908070090265850031084401034402041c441071104045803070303c40181800d0b10400c400078100c3c200003c0151944040c04a1802c113107803640e002c4c54401d80c0c1d40245400640324200e240c445002650007040c2d0400d0312901700010713000c0c507500d103802115200440081c00350710100554001011500420185040c0240d9803a014511909082c140d100020541d06142c01c260a00b00140b2071008603800e43c5401c55001d0340c400e8001161482d02c800450300700e400c818041045800b1031410300040312840c00107004c080e000d03103180d5166004200d90018402c0c4024082001c20445d43c11821302c90f51060b64400310414401c11315019042458060301d58502000740140e1181030318921600e0010740341c40d0000124100680040840700100381c070628010948011440d6151403002143c0007074104982 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 920228884 1250 920227634 920227643
    0x1302151804060f0b1902160603050906060909070315181103060606130b0c0a0b0f0708090d08040311071e030204050c0c0a0807080d02120f0703090b1518010308030f090c1516 76
    0x80d001c8d01c448000740246011512007403035114500204480b0305001c9d98850085c40d140d0050309240d421038a82654000300540b484005694070000075411860200c0d003151085d104a0f00c0d407540c02007100030185083c4028000510a070010000c844d42550091004000c40da412044251140081c40880c2c0c10301900c240090300050b00d41d030400400e5444540c285120303641c25240c82500c1d4542c001e035075907602540075500000c200002d000c81c0c0481e0040c007110f003003103d40c0c03400c44a000352201142e0300403004000010030313001485203061045290074015258405102d02c4610f0400003406004c42e0780c0d0001b0003000d40382d800002800402c1c0a40c00040f503420b01c00c4034030155a194150211059000d10443d142c0f400b1071a280b0124000520071b008100205401990000c0c0d181c0707072030074550650152001201ea0068150811242c4034100849850081d0b00038000151079140000350781d101d10000803c018095001115401203a0381d17402003101d80e00301c1041c86030761100726007801c007003c1d180b80a038042c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 920230134 1250 920228884 920228923
    0x307110307020907020c12490e100c0c030308070203070b010b0301090606020f0a060b061209030a0905010215310c0305071a031302151804060f0b1902 66
    0x1c01c1d8000030743c81e00010302542c503181c403842d085202e03d40704e0421808038441b004003034242210095580455044401511a03840600404e01c4114100f1019641512009c43d100b401c072440589040c10b05082c40104904020010903070a54950a80400c1400300609020404000c581d400307200700261000154004295030855869907000318079508248941050a4207085010920701d00c0420212100800b400007440306d000300d42e49903009451680001e5400c154140400104608210030f414000d20030741001d181d90b00701c0540e00030703c00c403010380000341950300039200c0f40704508410002c19445a280888001c0d4605c0ca024112804003907407900d1441c2404490504052007000000d030000c4130701c60002c85200c0c03907550703031003400011951554001b00c0c082480003c4203c2c001e11403000b241480100001c41c408094003c01c0001e42120920180401119a011003141854071410b80501203117100240d60900d09448140c0074030035a81c0340541c0c6100c904081000d40e000304120b40e00d90040c604d500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 920231384 1250 920230134 920230141
    0x3270c1203020f030d0509060109020c0c0904080c030f2805191b03020312240607080705160311150a121b17101d04081c09030e03060c03071103070209 66
    0xc0a01020351f88412280138080c00040c41508510803145802d00c110040e22040a1107010003070102c0c001030060300c0c0e0200c100155002000305000501c4241c007010700301e5894490304185c0f1103241c1408074110304402101c1e141d0108690b0804290fa28110f1000e40c0c2110304c0154250442d4080001e0705131400c4100510038075010560040090403180800c0214814142d4074034215082d903001e0f10b0404030a00d050708994403900d090000c0180391550003140064504030131036494034500341e004001c84030148244c6400344104000076610040041d0102d540d4090019030a501d040c00d03220f40e102c41000d000c060a00c041070980640c01241000c12400d08070050024465006409001445d00000003800300100040c5d80200c2402d10308181c134441c083c00c5020350030342021029405406842610b001c101408807140100d1903c2a042c0c030710180c150301080245288c64050b241e804c0f41c030400c0c0d12030b4010400300000040444c003501c0d8845001d103072600d11407900386541419407040c00c4c0082d400c129443e041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 920232634 1250 920231384 920231407
    0xe0a090f030c020906030105250504030b0109200301030c17100c0e040b04151512060f05010801080d080402061308060421091a030a021903270c1203020f03 68
    0x60400070b0780295041e80c0c3c0c641e104400c040c201c030000c8800783ca04140c00c46030304482c3d4103100913507a8152082d05180d8506a2030b83c450640f603000991284c0101c2da12980000000c040b140000f29016200808150840d4155642e030a5840c0c40b038011000740000000c1c0400c00030b0740400c080c2c040c03095000030420800741d44c00b00045c5200711070742c0a14007541c103255003080e8500301031044404201110a81c81c4000341825407860703801152a01d120304000c1c01101401d0041c540744200c600428240e5502d07900c0034070b450005052540144c1c80b2412680080c1580700c0c0094201c00c0c3d0b00d60003a070485075240d5405a860268410030b0b21500280460710400c0100000c020030614180351400012490642c201e09030102224038400c107010b100151024014004510f503400005076030000c41d1181e02600345907152540d041c8a41410003c0000a504c5140c5510312400d9403000c0c11030540d008070027000c1940c03143c65175942042d207403040f5900d035440c606e0454181882806044101d8904205999440424110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 920233884 1250 920232634 920232647
    0x1e070209040b070e0f0901090902060c071706010609380a180506280306031505150109060906050c011116030e0616140a120512130c0e0a090f03 63
    0x505502140035004d0b120010710b04409000b404200040c1100003980c01d09450360040c0c0114001241c01080074400088104020312644003d40000c0c0304074241507001429881c036052040c2d200c3e00c2403055507501801860307074020003120307120500d80020041c0405806080c44807003010908ea2340148021512000e6107a03c41c0c07034150300300d50340c0c800c0002c210303142d60802c00544101d002c1d03104005c660801400107401507081c10100e4034207a040024130305659413102c01000a0030b0590010300c590310f204225054409181080c0d00304000c0c81c1480219061034005030281403140681001d0000200700d100b80c96509421070090381461652241d01c5444403805e59104070f4442d1003ca009c2618010b40081600b4603400b40e81803040340703100c6c1d20601d10481d19640784210400005a50500400d02a200840c5482403035004c0c904865950301c2c1e60b03101e0103840002c007201c0a010210b400000c0e038079203404181c9200b0054151545a0105030150b210162804020540c200000740881c104848031020f1540058 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 920235134 1250 920233884 920233891
    0x10f0c1a0106050c100204060804140a0515071805150d110a09060f020102071a04080c120904141605220905040317100611010b031911060f1e070209040b 67
    0x3c04503044440300c44020411b0780580d001e0400040d03101c00015001c80c2801484a04c954900004c0e42e8190409484040c03c24420381441d5401060f800d0600034020ba10208405484040c1c8081079100c2e81860001008080c421040c5144074a0108035010806180d921001118082540707155481c0b800943c0501444c01a11070a00881d14240c015426240107008a45840764414542c04941e00c50011010302c4840151082d2203943c401d1000303840309141080401260100c9070211038440161004210940e1042c90305800d032401c2503414000c000c118884011030b20301907800c005480b82014640440d010845054002e58004145000581d246503036000c980981d0203540c0740418400111807050540350251a1004074103810601000068030078580c1c2c4c0015291400041810054440000e2030504e1050717a0380b0415a680303000714100081103800c00007540084e00c08a0802c00800c010180340d001e003030b008040d01e440101d0001002d10540b803c50303151310f500510b07040043c01c0a003440214070004a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 920236384 1250 920235134 920235157
    0x815090f010623090d031125081b2b030908011107020d0f08040b040e24010504092a0302090109090605060f0d09080304030203031501030902010f0c1a010605 69
    0x20046250880c9072441c0160340c4986203001610b4050302e03c4c1844800c081981095003004040d86105000c10001e00c89207150403c201c02e040d900c0080140c00f45010040743e4000f000743d80c8800140040044012584195810708031001e42503818803401d010307200314864100c0c2d62030841c0c2c44100b40c00c140d0404040300035138440c10001c104c254001e09041c0b800340704070840231358013800082d59000010068101801c00c184106a1242090741d140710000300c2d07800c20341003085c049010354100040700e0000203a0b15002c085260409481003d510006455485540138260241e5107511180300b08186110b03110350015500c00e045185d003510610000c00942095064900180444c1400900b140b80c0c0c3c05400c00342d4000134000c0f4601191805003d40580c40451448000c940700c001c0312003c9500e91000d940700d28042d801569a0b480e118941c4074401504e007030441d041c0f40c68803401c000541d9008400000310201c6040c074084500c041d0400090f84000e00302d00d070100354091800414400d80c414045d25254900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 920237634 1250 920236384 920236397
    0xa02010e06040312050c062809060615050a0215130206160512070302010507080c191b050606090f150f061314120f0d0507020118060f08060603160815090f0106 70
    0x398429480c00c00c90340003c1109a103151904070040000700c2c6e014000241c0705503400140544d6903452200d25010020082010503800705228eca245d40500c005c032090040d500c0c50400a00e01454440e0b02601c8040003e80603001c0440c00b03110182e40b440c44501610f070084200c8000301c043c1001c2082ca40c7c48058120019420702011810341030080d14024081e60340c1f810924101011800d0343e81c5114501090390040106601d1584607641d40745a80142950043c00038088030b1070103005105006002800f031140540d504020040d0301c001010b254080ca00048521080b01c491400c001101070107400310100c41a040c50a000400c7d034800525080043c20a45c4e800c81d460f180007001d180c94200304084c090700c40d0484958041d10500c18002007034098814140000c05800348025840081c45a0300442c0214803000c40e10601d850300191055482842101c3ca00d1442c900b8045c2504403107482c94040040c08100c0c0080f8501c0803445001c1c400ca042d0140c40ea4006140005c0c40b00480c0c0402c1c07041c075001c2144d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 920238884 1250 920237634 920237641
    0x4030f020f10020a0318170f0d021c0e0a0e15042d05041a010b0405031228050c0d08040b06010305280f0501180c050406020a02010e06040312050c06 65
    0x20031100c40c0300480450f0f0007410070140c0c00e0f1001c1c0d807a024203600318070380116000400300384c04500940011041e1314000c01443c5140000d10400c0c5041c070806481001c0d50310140501800700844019120040c1181c82c02c580031940340c001142c280251504a101050703118000c2080c550100c031041b10411404131014010a12820390145010400001c001d0741c1122034042c0b000610071179044560490b00c102c0b0311080f1000035080d03250b04801e00b80c11020480e400058200b09600d01084054003448591004a14210b01012211401101450082540364040b003080e001f0720f0050303080c1d440000c42130041d40c8c1c0030300c0c1c8000000c101c2c2c94110b40072641c810001012401d6135210b0701ca8203201c0c1c46465200d464005c1c080e6468070f00700c00c1c842c800c5c4004d41d868441c2000102e84c140206030007004c7ea06400d0310307012032613801c02040c0e45c45030301c060040040600c41008501e0b03001031002c030340c07580a080c81c1c00075420b01d1000c0740384d038411900003405002585d2002d981d41c50744800208101d5004c401a04d41985 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 920240134 1250 920238884 920238889
    0xa03180905070e0f0919050c090d0c060915050403030f020c03010e030904060909111e0406121104050411150403020a0308130b0403030c140a06060f0609090b0303030411011404030f020f 81
    0x170702650103d565250306031442607a40d019034400ca4100b10075014460410034000c0004100e055070310803c54100384059801c010302600840060003400d0040c400b0350328010035070401401c41c05a4030000c2c1c100400d444842544600a0140320340c140c201a00038042800800c28007542d0ba070101d89141d000d9882c0a10002d00100c2a209d10f052250740214007003076202c651010014030003240c070f00041c80011b2646803400c8981e030314821280180002c0c80030b00350b549480c1c1010089814180c500d43e002d14104130411000610781c0d401c001206c902182c03181040c21503190902c1c0b041c001e58000039000f2002810103c113000094024160180c060002004455104c0110101502591000402141707180000780d000500121542d01072008c403a00b10356030700c038161f160902642d213a1b43c4a080e0f4604000800c1c400c0d03661051000c4007800c0c00383c50034004070b00d400d80403e5581c880208068a6031120303030041c0b070b4076a2090540d00b80701c0c503c050880751542e88074100800c20405c2002d040b481813000000700865030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 920241384 1250 920240134 920240149
    0x80316050c0a03050c10050f040b07031806180f0b090d050f09090703020705430b130b0a120f05090a03030b0613030821090a03180905070e0f 62
    0x41d1006000340c16999141e5070107139800c0e005040c00302554000c18080c2d14141070584200c2c0c2c406c2c0000f10765400b450a107410a80100040642100105070418030022040071651100e00703d05540a500040c250a18420b0700b1103d9007040e00040003000c4007102c100c203200641c0c0b513050080581400780c41005025a0003500c10b48580545840082c0007403283c0ea01c14038003001c0e910760084246c180940b90011035503401d81071014120703410762550400540a5034541c1c4a41c0000030034140041100c03d10044c0000000300d03081c592051403420b242c0015095168014038560078020040240803540f2480c014201401c0040d8100a0b210b0040c50401c40b01c0b44003585000e590700800030007000c2d01002d80300c0e85044002d070044e6004030340c01460070041d5010a91032083d0a000071130241c0c05642d15010513443ca0701c0800311f02d5240d440190300150500c45150b02c0801d01211642c0c0c0b505000c50750351050280b4440600c0315611003001c40349010100f00d62160400c2c441540440200d8078400d0107600c3ca4200201c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 920242634 1250 920241384 920241397
    0x10f170601090209130c1d0a080c040902031603050d080708100513062102040608010207020f09070e090103030e120f120c1903170702030414011b02030a08031605 71
    0x1254820310042003114066401091041d8025084c0b21548030f0000c07500098441d07021000e4001002402c41403000303122071100d418960821203562807132524100015a540c0c0e0381e00e46c072030300c0380b03550790765040456604100080f070742e0000b01e8044078000c0d90790629036114890038032840c01080403000020213103445000c5283c440d5000307020b00c1c4145400c0c141440004900400752800450b0380301ca0101d0690064081f40440800b070b00007541c0414100e01c14041683c1441e03210f255030b41e00600080d00140c0d10b503400e281c403450341a1240611941d5011003115028240b20305940c00811590010061650081401690000541e030414000c0b01948201c0d0351800c11840040d03054202c03418a60f1240c00900007080f40643c0002200c410003107240391101c040f0b88a61b82140402c1c5e03061544401914101d41031a400201070001d542840d00d0b01c008003070a003000044043c100311a50303956000845a1806401e165500036044030320b200c816203881c5c0c81c3c07540151025500350045690352100e843c400e1049441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 920243884 1250 920242634 920242679
    0x8010806061c02011107090b040b060705070e070507170703031103070f05090310060b0c070506040303020303011e15591201020409151d07090b0c0303010f 68
    0x81c0b241d000c1c1a90345030140c00300101d04110005101c2d0710441e9080003000094810000009400d0082404000448403103440da51300501d014440500455804120f4100b2100c0e0401d81e4030095480b500209c2d414441c04c000100000c0e08944041c4c240380c00203000e04580e900c291400c0100000c51a4072a0003030204030350ba800090b504030200c0003994800c9028243c0d12201504907030f107503a40c524298007600c0742d54120403012440407030018120b2200304906002440c068410f10310301410740e01c0080d207030b00c070501400440094244c150404150304404003c01803111103149054003190900050039010460034135601100040c081b400356018000f200c0401c0000ba40209002c51200140e4215050681803c01d0400d20808118141511900c66014018540d0800141d480742444080000c8501114460910245d82c0c0024480d81c110009507141902c0901e2070340107240d40e6074034112565a22600a40340c03500c4003058480829034000b015505a8400c0102c004a180d101c41c12514444001e0000f0603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 920245134 1250 920243884 920243899
    0x3010b0313031124060409030909090c031a150406180b0a120b0403030501080102160602090a081603021311030403120e0a0c03031e050a030b04090204060f03030801080606 75
    0x294988078071424103100340d2090411420a10703204660700d091040603e8070005004900c4c054001510b880d20000354019021035041001d90368688004195095500440e0001a40c0341d803e0424400e0b00303402e01c0001e50307010901c1e0242c0d400c00e4104000040081e90303100c00b20b5652458602e8039103064042c200035640b00891500020400180d24005414a1312086400060301c040c040742d120181c0e401041098051620350310541072900d401011240168400c001c0c99106100c45019045d40001081416030040710160b1200e07901d400040a201140d40550020304c96101d181025614031010902220300859440e074500034240302000a503400c0040e111400f150070400500024050604d01c800140b04000009815821008070340c40d00b00340e00c03000d403401c0c480d8807410420590b0041544508ac028001a05840c9500180152550080c6110b0b0340502d629071500d500c0a4581ea03011031101c507001031090200c2503564010300048803482c04240d00140a01d0000302c0d840c01d00203525030060101403c0c04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 920246384 1250 920245134 920245141
    0x10e0d030b0d0606090b01080906070e10110d02060615030c0d110d09230c0a0e09010f0504080a03050106080112020405070302091914011404091d030a05070302011103010b03 76
    0x890041040e10710700d42e8092a100d01c0c0c0d8010401078440c100c0640a0020001002c0c80c00c88009401ca410060142e0242c1d4080f604000c00240d02444541e40c8480580301440c48249002094a140311201c010105900c941a46404070341c0d4000791080c01032400382ca481d143c43d41d44160803410b1348001c50304044005010000c07507060743ca0b0b5601c080c2c1c02d105410441e60808260141c0002074444911058601425640c0341154a0119820310040500118000e000c00e204c142e02140826240748100f803900000c06001401400c000c1d00400c003015414a0108a00d00d130519000031950001107000303000a29043c00132804034007c0e25000d0585011160b142550b802035802c200250a0081c100010150207111900d01d036200e205507524120070200e03a00f9400e80c103180d110001800c20300c031700c01d0410600f036a10242a0b800c200495003540d01090340401d031401c3c03400308000071115080340880d00d0710000540204041c0e00031302800100c0d200341d00901c0300c00c8103c8055140f0780020302448000b4102003010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 920247634 1250 920246384 920246387
    0x20f090607020402040f0603050601030501050609010c12110d090f06090e13021302030c0705011413320a060507030603120c0f140307021809030301061d06030106050a080603010e0d 79
    0x1e0820544024005894680c80d030318242c07854049035002c840403a8948051015541e014080c00340545410b07103c3c60704150200d00001c1280000b120042d06111440f8150012240301d585101280148041141e20010188800134110040e44c41180daa003d040b001c003003010362245401d8022255524030000464444a0b02c60245a040a5007281d1080840c3d1000543c0e00761400650f108110300f808980c0c5030101c6040650079100259181e010f089a20b5040040707101c0590f0401c801d03290410f50385aa09136080c0c0340c407080012540056080048161103030148840c0029460225030b100e12420701c40e03074032030510607029103c1070301009285802c81422030400506c03a03008009140c1c007509801042031300079100e05007290b8900f0320405103508000344440a50500144403000340c540c540310003100d407410001c99a100d02040c051981089150990171014580f40c1c44a600780003c0102001d6032541c1d2601f02804603070000340326401160b0644006002440d041c85880406240d4a000e030001c2d0112210 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 920248884 1250 920247634 920247637
    0x3020c0603270f010c050405100f02060a0e150a090c09050108100c120e0d1107030b0622020c0102250209041209081c02070e01120803041103030d15060201020f0906 72
    0x204460035100f868140b402203002401501103091503620348982d03d1781032406015480d607059982000b4849a005040d0145500007003040d03204901910021705000303d0001c1f05c0c1052400a0300e56201d0a5120901c4400700966104002843c4280c240c1c2d5800d40c0c1c0e8503081400e80c0d40074070480c9261780284449050001c0c0c0e0750050f601142c0d032403074214060814800014119410080c0e144003030b50103910410406500991440c02c0c1d000c1240062450602c0d503036411000c24030003001340f409840d469600000301c1d0030015460741070701c0c03540c0d0017551504910148072307000f900b04d00c10240b41090100d5186050000f8501100041c070f070068224200382e650744d25200ca6020b00c441004c070400c25524070000d5088410310403805c4030080040070903004000043c001b841d02c0d105810000c501640080100048201608000030722540703c91a10348035070300da08084d000c240c41d110a40ba01800005401303043e4210581c00b10350b20342d441d00d40700005a5101c000803800c0f0702800e0012a01e40c08200402e00d107a140200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 920250134 1250 920248884 920248951
    0x90b0d08040501080411190e07022b110604030e03060f0108060a09051c170f0705041404022b060e060d1e0f1a01230d1703010f0303020c0603 62
    0xa280ea00611b09500426034010092040b01070950313421a05000104a82604682141c9103100528040300b907850030380c1c144254415030341203c0100e00070f0740d4056400313280e21103203254550096502e41d140c103060140000381c070201c143d4880d001700d90000d208514034070034442c140c034105002440d95a0703c1c1012200203101c2c1d00d4040d60b0750310450082c0d0003050030f00404040300056075075400c1ca880d12020100b8000400250803800051101c1080060559100007503074111a13001c0700c01c2c910f01e00000d010400920071050300840c0a01b0703054800080351290007006000c5103080000b00540c0e65104140c0002031400d90355290f009410091400c0030032482c000c0043c041d00f803094140d480d41d040d552000c030550002d003001c8a90799002c3c01a00a8000c618a080f80180440b440061040c5c0c180e0702a1200301803001c204900c151079049441040c0582c021941a0025944008540c0c03961698124020500303980300440061007102c241202a040c22011360f809461400c01000401003000150340e10340070481c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 920251384 1250 920250134 920250143
    0x204120b090c031920062205030303040f15060f09090201030209060a091a1612050918061c17032e060908150601181e090b0d080405010804 61
    0x100c5202c00d56a0180944d00e071812400f5920014003110740780c42c805480d65621203d1001044051600309602e6100480300003c640e030384400e81c99403a8405e00640c216443d005960148000b004000070480d0040c1c02040f09402a040079140114201182040e2400ca00070840442e034001004c105044c2030f5003010345e50740c0c41410098100f400380d1020560070f810010303200d80003075801c0108002c1c2c24105150231000019010007a80360030f100344000040c1b45c5424800a0644082c1c0c2e440b41d08162007441510700c4888003c011903120100000b04145660040c1c0360507208802140c0b5194042010100313404040d60b1111100140d0074000c0d800740703201d40006000000840745c41414402c072040c82c00e42c440000300d41118031326001d0b04028005102c00050f401c03506495120304005101c0001044205903c8102441c0007030707000c041d4000c60610f0b01d40700d51050344e40084c007032803500e0403078080700c400c605588000c1c20403c0780b22000e20801805144102e40a0401c40d01000306203c194816000d20b58010b014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 920252634 1250 920251384 920251393
    0x2212170709090b15030c0918011518030b090703030206160e120705090109021207030e030304110a15170c13030b04060209060f030a050c091008060a080106150e03010204120b09 77
    0x114075143c449500807500a60001c400040041d00d41ca03207507200d00310309402309140c8962581089a4840803450300d500c480c09000019444940b0500c00125400c084c3d548004c0c00b600351b042000c100c0703941f5855030000f02d015003c1c1c540003941404081459204a034925694101c400d184c1009000c40c2c02d0b48003411102c11b002d2080c0114507500c1d0850300c0b038020002d4800c0181d55a00c00040c0e03115400001d80345104040c101240018562400003d40b45c100760001d20000501c07001c240040c41d00301c4164061800407403600c800c5420181c0001102a02c078030a001d40d05840c0d580c41c04440c2043c403412910701ca0741d40c08003c3c107202142d114400541d00c07511407440140350544100000703520b0b030480f03450f400341080c00104000483d20340303014440d00813543c01503442c00c12907280001055451a002142c04120340840010f000384c1e502d0756024028080c2c0c500801c00113448503114401c0040c20062131002c2075804040641c6400c0500c01c03101100c0043c0683c2e00b8640096461600c810030107004030709940329 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 920253884 1250 920252634 920252659
    0x71b14030904053301120519050a02070302010b0d0203070e07020708120301230a1202040906020a090e0c13051309120e0103110c0c092212170709090b 66
    0xa5a116490207086200b141c560741c64100c0300d0b400c2da07000344c403440e503414045044903050113641c100b440c000306206000c0021410350b540c1d50f42e42e64000c04201400311041c0c11b240a001c4803400560003010518060f5009201581120702805220301040d10001d400d6400540e040129070802c180858000030548103460201c0d40d81d400700747c0b4003c000c1180e400040e20000c01046050078029140e00316070070303420340c9000104c074400c0043d0400d400c0c1c3c403448000c0c01500e01d0410455655501c00034500e68408011502c82a8102004201c0f9442d401903800103050310021912481d00c241c10b407041c1d20710340300c40141994149014000000304100004800f140c80d980f030301001459195050451a11a0b0b41d509211071049000509941003080c0c5d00d500450100038291680401042410300c0354400ea411100c603840710085003803501c01141c00c906202200d4100d0104200d04031107403562907201039403522801c0030b29240c50b12038040709480701000710b800420f0811000d00260052040d0b114000c102c1d46c2004c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 920255134 1250 920253884 920253889
    0x40e040b1f090c0809010c120b1c1b170a0f1110030507030f090206070210050c16050301230601080c13081014010f032004060308070209071b140309 65
    0x4030355410200d0116114410f001801e030340400703103d0b404640d04009001011030a8000703010b81c0180701e0201203d90322034070107964a032241812403c0d110014001d205103024182800e504c0c82c074801c070f00941502d10000000a460307000210700144080d44e030340904620300e140d5441220b00e1800034812942c01d4103000d008541961050807800c00c4001c0d50b20041001d18090b0b030003d089036201012544413600e00000c0001580f15081510540c0c0d905440010082c03500d040161094003c0c5025040e0a2180740035200c2d00d244002c1d690001ca40c800e50080c8441070001c2840ca41d04c0c84029140c010080101001401540c80b50f4212500103428640161404e00a00f00d4480c00c054550443c40345588200764503803004c0980c1c031440152803592040701080d54113081c641e80e4042203622015081020b440c0522020403905800b40010520040c020401d00c0d40c0c908c0c3c24001a00706c3e1005030710800d00d8000140b40f15011340e044900d00c1e2b1070ba10102050050903a43c0140301060303007040c45110b10003800f00c80ca40d80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 920256384 1250 920255134 920255191
    0x1c050a0206070b150306090304091e0c020a30030f0e031803070801021206011818050105040b0a05090a021b2d03120610020a060c0801080d020102040e040b 68
    0x40c05075001c4450f0b80380000100401c98941c03071035036009511080802140e43c1e000302c281e0301980c004000200341d0130b01c0e07051044107503150314500c0b1912510709018410f45075000100201a03c0c0304542e0401500c0350560101c81040127a440d6114507542c081000600a10036031002e00d005c6a45c40d0002590188800d40b140303150490700124205d540b0840d6024002e03d01088040020400c2900a40c03400c0c0420045010800014003445d0501800c8001045024029059000070707164801c144090802d0f1546260041e050a1042c2805649800c031140d00314100240c000040d5400980f0406007a00e500000700c00079845a6140080101c0c04050310ba0200d005106004038109840306040d00400500b1040350307200840c2d100c10000d07500070070079000e031280c0492225901c5241103501060282210034141d060010283c1300800c15403401c9500540c050f00319054905841c900b604031140b06410b4002a03081f4411030103030400040b10140054001145c030950640d001039035a08500b00c1c0004028501c140c0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 920257634 1250 920256384 920256397
    0x40816060213050607110405060a15051c0c0c29090c01020c1f0e151303050d020127110a0e160c020d0b0403020f0a030302090a08030403021c050a0206 66
    0x460300090900c006840b8640d0b010003400c8200c0c1c00c2c0340303032140503503800c405d5101d04d030701a80c003e0780c44200284442e5a071545580003011241c48000400c0d0011400408039403000c01d00980e0100e8411800300d00040522441e0701d90a96501ca28240040c15104c03203801d00c08000703000c1070a010f81d400c40013080541c02ca2543c0a510034000504030840c0e04000a42404030541c034a40c040c044400d011400310b0300854034400c1d00d0000382412000311003880701003483c0104010890a4140340000c40401400c180d034100c1003203034000d000340c80b940380032050100d0903240000d10034200000d01e82072940c074040c034002400744200d1140c00e203c0d003000141c0d40401c0e40100d07503a00ca0040e0071090340c100001d00d10106d9801041c0c3e061841c008604079040e900140603000d40d200040c004070200d00000d810580200324074110400c0280403154400d24500e4014080d51120100381d020b020b0140001800700700010a41d4160380e80204444150480c4110848041805510541d1103100c0c0c24010409030300e5a000a014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 920258884 1250 920257634 920257643
    0x5120c0c1906050f0f010b0a050708041509050909030a110102430201050a1d0a172505060c1504030503010503010b030d020d1101090b100602060a0b100503040816 71
    0x29081c40c2800c2c0441201c0c8001c026031080c11540040007110200880b5240c1501c0400001940322084118216110b000e4198010003d2600260100d20f070b42e800c80740d002c1d24aa20366169000c094494041c0080c00c00c007035800d02026070050000c12142c1380645000c424112203a400181416000310000781030880410b2406002c0d5044941c2000c2a00c0070925060366000d80400c001092246500081003031083e48071070001c00100b8088100811011610302140503801070400e008180c88485103500c00b180ea4802500d41d206d914901d0742200069081103455041d00e80ca145c880e50b00d85014490f0a81c404c0c50104058020180a02c9071400d19a400c0c600550095031176940381d40c1020103040c211002503880034445c1e40030801480d90154002410540003104d881c0105c0c01a40810303150b805813108840041000468008001415071000004000c0703502550032101207890301403140c0119200140c80580040d0240001d8010a016100454105214100c1d051500100c0d0308010181b200380441260b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 920260134 1250 920258884 920258923
    0xc031107090e07063b04050708071b05061b0c073506061908060412170403121e05250306180902030102070219060206070c0305120c0c 59
    0x1002d06420014100600041e00344034108420314124003c02502420580448818020308402403102908031a20500c402800501450030004c030080d012010840d082e00c0007481c102001202e001720f440703004030882d4105010700320310703100c90402d00003040440b103445540c40020429a414098200005002802d03100364603042c0103018103178201c0300540300c940e448101540d0f24040b490300502160854010204480c04000590344107400b004484540d0300502060050004000c24050546a040150445a82e41203400302040c17545101d0001d0030303180680003805141c14000f032072002d640500c504880c40d1142041420010342c0010030b441e001c03036264032921403582c010006407402c0c12071500590f07400c0c2000c0c0030749400c140c048100d000d03940d182a081381e80ca0b4007001c025500c00b941280c070700b10b4020b4011380081c50500b0003000200601d200382001440b1b050001000700d0b120b962901859541070356068642145d132030141404400140c0314030001002041851030000d0100001a4103c00d034444c1107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 920261384 1250 920260134 920260151
    0x1b01050702070b03160c030e12010b04050105100504060c0201122f0a1b06020409020a050310080715030b0a0b04060f0e0406060207030b1308040b032706070c03110709 73
    0xd0412070264003d11034441d041c07090060306100c006607100005030340c0c030b8514210600790034200d44140c0080c8030150403c103010080c6440a030190052404008140c8040c4802e0f41d84109215402c03000500c40400110240b2052103282e114150051010340140341448440d00151103d008440c0d0a00e4040040304c000d440d00c2650070420301d11035a04900c07030700d0940d0502c04075840180010320400d00024030b076003440c04800204400ca905440240c45401021500d401c8028800b07421640207480c4120007403507101c00010070040c0041d801058038291100d101e184282e918003a00079158000e46240c2c800e07031a6101081b0741780c1b80c0300134200808203565108414902c00c040541420003509403580100d060080900c4403680014201080700d5102000b080356036500001d08105800f8070300010302c1d01700009000141400d910001c0d500a0030b080c42902444102214a01242c0b540c000034500a038204200040449024120090280d4001c0c1041b40641201500b854200007e58201c0c40078a5500d0491 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 920262634 1250 920261384 920261387
    0x903030a08090115031e020301021905071509080d0504020f040911010e01140f1e160210031a0f010203040810060303030c0504060c0b1503030a030c0813020f12031b010507 75
    0x2081a011352500002d4410b07801d5880301480410401c0b03660507002d444038814400c42d20b095040320040303a9144807110a12100100040166000003000d480e44003501c0d4061304403580504c640c941840d8400000d900e0600d290003003c0103400300600a80e80010076180400641d01c95018005203d48104082c0e0001c4101d200003400a51011f800c2034104070603400c2e80c00d10561501c080b952282100555903440e0480b00114060085003600105001a0081130501c02a4103841c12030104520032611240380c0101c1100440c00c803011030351103414031001d40510075400d050284044040010602c1507030b03c2d0a80f20700c03546241103e8100404400d83e9240410005d056040c032440b02801802c0c500b0501d4249403082c020140c060b01c450260444500c1d2000c1820200eaa04108090110180550703442d10603483d00980200f4004030b101000c01c10850000707403241e525514042b010b0303900074415820035004030700b4042422140c90302c3c41d03201d2204000300c02094440c41d401e00c0c0205a4100085031900c1c002c04c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 920263884 1250 920262634 920262641
    0x7111b06043804031e0f050703050643030e0d0c0614010518071b0303091a0105032e0501031212020f03071b0803191a0603060d06020903030a080901 65
    0x480702c00d8410500c002d20000e0400c40b030103080d90290901d2241c150080781880100a091180000c02902c10703035200008100300410361300c0c411800380c0c2d00c440c0032026009141d00600241c08264842000140c1052458452403181140c100700e14030b0001407001c0341114245c5040c00d41c60340000450600c0000701c0800020b801405200070515140311415403405000c25101a45c1c0c4080d24482c205020000d00180e110300e02200000451088101c42420a82806801081545426070f007103e0300b10780c4144c030141c200140310b04903100600100f00007200080341c3e5041c9100d0b468003007481d442184200b00200c45030b00070240614010307440f640002511004c0680000c013000940903406005216080146518105803a0b1200300c5040c40e9002e08910355a103034003000b4000e1700030315901011003805480c0321601c002c0c140005440404202450500e10380070b600000c1900b031035505c03050400000b1120300b40f5141c0881e91a100e920058100061000000c2c2180c0044d060f460019402004104c6801402d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 920265134 1250 920263884 920263979
    0x260d090515180904051005041505090115050607170403081c150314030c010c030f0e060c04170709020409020a1202090a09240e0f07111b0604 62
    0x740400d25004201c0d4100c01d60741907a4800e24440c8800c10001401c1c05414800640d8050410b4020001842d01d45421110011940410418285800300081210710305104040000e04030700048502a4500810803030550302c140c000b161064040001b00c10409226400740028520400c51247c039440017141c1201c1400d2131094510381141009010307862841c482c02000150307504003100402251400d0303800c40c514407590103034059642c40c101c103c030179031a41544020601038031224107002442c0d4801e550360344e5000584031009034004c108000c0003c070003c080c1e9420900e00200690341e8450342c4852880498120b42d1000180725000111055000c1d80541e1006032413480e814114100010a0089000b040c0a8081c00c51041d6984865804810040a0018504c01c241044207141904c484006e050b40000ba034240c0c552109400c0440c1c5c50070f019010341080d40038031200411100f8203610400d040000000c5a103038024500b00004100841c04074050207821013817060305c6400c014004c280b240444901c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 920266384 1250 920265134 920265169
    0xa0e1e0c0304080d140a06080105130519030c0b0403170c0c100e030f0c010e0c0405131101170f070f0e0a03080f040b040611010c0801050a260d0905 65
    0x101004166040d540660360410380201c41c1903158108415018002d080b00c2d42c080c6100d1603440c1c204504169503400c03010907109140000c1c85141c50300c40a03c803002814080007029a000705a906800e0646201e241081501031320f030050541040c0d0f05d5000d00048160340075000144200e42d40d0302441c420301800c0d900320210325440d0b481c040c003c103940e40d103840c030746072801c0305142d11007800000000040040e11451004040b1b07266030303502441d02d130500074096401c18081c5401000224941454039103d158494031f410080c60804250a5a400c10143c0743e0304201d5050005000d0304141d1050010b07400f40c442d0f080400c15940e181400b0300050130400300f10449004100044110156030344034035000c403048907440079045448500342608520240640e07041208080008100010300c540d0010007501c9040510000700900740340c03041c044030500c10074000c494114022150030007501c11300402d000012040c0340010b50504604101171030900c5800d04480000881c030010500c050320f059031000c010201135 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 920267634 1250 920266384 920266441
    0x5030a02010923130902040b2407080408100606110604030504290c0d12050c0403020f01050c0105040506160c110405250914030f060c030601020c0a0e 66
    0x40d800200500e07071030f014a212901e03d06151201c07401c1c100d405556801d100070070300741c0d410300c100040704010882824140d00c00c90508001400608111520020a03521885800c6482da201802d512560780441c2d000c44101000f000009201e500038401c1e80002c006586022900502c0d019009240c02d80d441045440761700310784180700010f5003040403242100d165409001d00c45412034072000b1848180030400c140f140340015a564800000b14016000741d01a84685521942d6a1440401c41d541114201c0078644100000e0016242c02d2000d03041c04c1c2c20515203141707000c8003c5001400d69200750b400b115540d11040601075202c0c3c1c1c0b40b440101c10001e0785420f00f41080c45407540b081e01510309084d0382c065681c680100c0c001d94611180c4e4900002d0340c01c14585e204245075002840702d241c9109644071000680c10b01c2c1a90710700070800d04002d040313a8004107496142c000ca480075070352015250605600c0b60160321021902c60302c1c4084001c147d40751100c602803511440100c1c0384140d0419140d480c114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 920268884 1250 920267634 920267653
    0x921020303060f0405070917010632010c020411070c0317071505150a0b0c01060f181e110409050603030a1b0c030605011e06230c0a06090f03090503 65
    0x12843e480c42443d010403200850781d5165140140c410001e190444407200b091460800030f1818150803141c11a681704401001c009024210700b032070700082000700303010a10b10f28010751807503101c0c2c0003035002280014800244505001e141e00e2243e0700c01c8500301d6207160703400400c1091040340003540b083c51040000c07880c40c0000c140c0e114400f0411150b850030403142e540740807500060b044401c9298644000c1c0001c0b800d2925520404000d4000b045110300035070074014085002d0b201c0d02001012507840d205021040c115000c0c90401500202c124280d504502507601c0c180028a401703020034540301e0410003070b51207091584040c01c2d500004c10381030007035000304905c0700c015902500c4145501404860111402c109140041d10410144d0010f44011300b071400214000c0031496442c1d1032500000e0b041c0c0320059440c031050b0342c909424650a208e801c18901004840c0c500c01e0024410703407a503070081c1c803d20503841d034450707007226a82c100c103503240041c1c0903110040681000a6002526007180201003009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 920270134 1250 920268884 920268889
    0x1517060c03012108071e200a170c040606090806061504150c0510050f1b0d1a040603030302220b070f02030c030628050f0a110409092102030306 63
    0x4100c9002c240303952010f00306802c3c84280004d607242c00c3c2d402180700885800740038000740c03041501982035504078005800390f02009900492142142800707842d640e011850000105010a030380d49021a03580200039500c44560b450f48118409000aa118004c440d414011001e00d030140046c001805010705107241000e00c4054016501140c46110705079101584c1580c080301e006051490081582c440e600078a4001c00e1907810003482580780782d04100c0c10740e541d400400c0c103048450405604005003000701d801030b90780d0b07030b00198550801c0304039040c4008681c0c80400c08031600c6900690020781d0204595410314504900902000f041e402c0c2401681d0030300803150b0700c1c0e114001c3c0c014021035400c0b01c800c085450600110079000002810b45d9124980517205a55007440700c1015048041c0043c00401800b0092081500404002c14003400544d500e41c0c420004140c8140584012402804000340b0200d15014020246210304885c240040807107516950107500c5040d01005d54000f132040281c00d8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 920271384 1250 920270134 920270159
    0x142104050604140316030f2a170c03030301081606090609060c170309010516030207050a020607050a200f060301031a19020d0506120d211517060c0301 66
    0xf40c40d820144070503404000c0010745000a054107066448039580000001c1c0546030812000b510301400039451002507452584041c00940c2c40c2514002c01c0307070907051061580c1906603483d81c45031401100d0031a050ba2001a00d140c009074840d020b00c0d4840144074543e2141052810700510b001e080c4004800d0415201070030041786400b0310820400f14002000c1440030f00002520030782840308003940d6034102000e0590103880225180d01c0d81c61710304039056084911178803c9411907500280500200b1055900f04082079000d02da05560358421811442d0114403219010300070b400b000f519007940a20309801703100d80a04519112032080b03c06000400c00702e0341c142440001d6003106101c6810301c0c0d440e0300050131140d0b405111000c15903c0840c0c02d40c80480254485402003004031080c074400d0443d600900d948018000380c0500180c0c0d900d001c0040b82c945c0082c2c0200e44542100040f81c03402c100c1c0110b0354100c04580c0a0b13039541420b980f99102140c07042c0140c0381c001c42e5001d6030074615810629004004c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 920272634 1250 920271384 920271389
    0x20601061b0c0311030d05090d06110c030c0601080c0a0f0501050a030e0601080d1101090f1e1a040209070305010803182d1504030201020c1c142104050604 68
    0x500200c0407699000c8003000e1684a01e10b82c0c800e1414503150b44900700390310704c1c5110381000f82c0680300343c405a0307583c1c0f8000d1094480c1120003e0001c80c885c980c1d80d03030fa0000727041c81d20390b000702d00c800520542c460440e060005d8195801a0f800400f41c9616040e01c1e14a00b0b404000414000c1080503410301880400109003000d403a82130030101d0f40c030780c00d08a0860061004130035a0407640220b5001044041c000310760300702c1800d15130740c9071841c2820f0740c1421400c9819008000b801c00c2042c55448000412090450101c240f590424402e54800d83c0c450308181e041f50310605052406803010402185440300031550405003d00e02000300350304042ca0706a4900c81c0060b2200c2050400007030818a030f0701c8405048111400381800602507408008802220781103451640c803601c03045010301e40443d04201900c085a40583c02440780c0356400d018452007075040c030510785148450b0721090002c80c003004501d07400e034001100189048030052075100ca41c542c56841030034180000b0001002280e45200580b8203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 920273884 1250 920272634 920272637
    0x1b031c05040210030e0c0a06020c0312120601260406020d0c08040b19061802070302011d061906080604110406120f023003040303020c0108190e19050705120a020102060106 75
    0x800010305c104451030440c5003500140e120410302001304145174081035000345901c098085401d1050701445044042c0208200355228003034a400040d202d40c482c0b1462a01c107650003035400c95001a503c01c2d010400c804580941c1e00703940009110314035030841c1c841c03c05524050300d4040902e0501d6038902c4101080038051a03039a2044041e419a044020b03404500104103040603182044100244070001c0e40009500341c0c050b503e0301e0019004410079170142c0c913540740000060031007595440c039011104490340c0f00b4525020b03522000401c0511040103160b01544c0583d0429004c14001000c01082d150141c1007185245645d14404c00000c04044004a401c1d9045840c1c1d201c1610000f075200e680c94000390311a1f9100501c00c400984d0b0600400100240d901032fa083c2c1e000741e000c0100654007104280e07240302e0301a60440340590341103220752108407503040e8001a03034403d100b0b004440b240d00b800c2074010b68854200840410061a0040c40c45203c0f003010005080d09600c81d0700040e489d00c005124450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 920275134 1250 920273884 920273891
    0x1081302060304061116060b0a08010903020d03050c1903020702190b09060f1e030103051002040f060c050a020907260906070c031e110c040905030418021b031c0504021003 75
    0x171100c510206a581642e044c2e003000020040700d0410401400040110070300640c6e04403004035080b641030181500c4586c250700101200088a01c0490082100a0122039a20814000c84c10500300440688184032210b6601507103603074541c010400704002000e0340c8581c41120ba04208020103d01080d1846094212034941d142c1e02c5008030030701c2903c514031498900070000d108014804040c036002e117040e203004008644445030a0750119040348a18041c42c014006a100e08003c0c09100d5400034140d00e104030240c2d01718840c0b03540400d00c40c000598a940c08201610001490b0030f0700c2341e60b041c0f00404001c000034144e06150891940311500542008100600209000181070040c0074100b140103440d41d03000c01200140c00002e1000c001a90280118000e4003140d10892505005d4140b0b5903030020051072410386015960001e121004805080c0d0680030312401000208545000a04000340e102450b40c550071328001d5501440c51030040e0111528000a11015899807600c540c000300c07042c203001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 920276384 1250 920275134 920275151
    0x6090c020c03280f12081e040f2907030b150702010c170301030302060a1b020709020a030f0e0d020c030d050d020706020405120d0e03032d070c030f020108130206030406 74
    0x4026001c80f50b00090b0074521154070140402007100740283d8030003029034a0b0b54254503515021810810452810840e2540384000300e00400c034901015900c0d85e101e00c19015176030300001b401c50811002e0100c1501900125010041000d4060013205d03102442112150a0120b00c84072131540381c042c030f0324003038100301603003820000f040107012040c00700403950b0360f40d2612036a40c0e02d0001d40ea0fa000700d03455903003581401c00380c104500710300c141141000d0031307900900141400c02402500941004e00e400c4200b54075800910400c00443c41210068010000945516551114043c0c5401c1202401d94029404500404540d03944001a10f0b6200001103000d6a03500c01401c0c144040d010755007106600c004803803110b041c5081c0020700c24505a10b1a126142e40e10b00744010076850307014001c0c0e0350b402418a40c0741c0000d8510300c403200d40074200050201506180940d12040074100450304100e826044080e4460f041d0360f00140c0d00d5a2081c4a030b000f80c1d04222150380854002c0c00f0140008040c40c0d22034009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 920277634 1250 920276384 920276443
    0xe010c082d0705010f140705120c0405040608071a0901050706090f08030c03040c090507021009020d0c062102040f03060f0915060e150a06180806070306090c020c03 72
    0x1080190751880800079251030850030024000d011044115030854546124200c900055104041c400d040940b1000d05003c00e04520314208000181044544c0d9000c20011455503a41e225560180c80000e000740011420800c2451950159004020851400348020b00850b070b4410304607100a6403242c0f01043c0c80c0440c3c900b03440544040040182150350200811406044180241d4403803406603460455540d9255030441c02c83d07500380d40100058112030031840c555060360704890130591002d400400000300790349552900300c10640210001862100c1d07070410141016401c8900340c042e1100031450305107400c80624858007640300c018075580d260b0f40d110003104001c0c1c3c0800b80650708502c080c0c1140d0a1080108000d0419024001213004984c001c0361901c0d015444ca032031205000313015500b086003001ca00340e1f00c0310540800800c6a155100300403032240c00c14403101c0c1c0907501d69140400c055080014501c195000d00100c3c03821540080c030800142d0307800180040d0310349498142c1ca140f0104120343c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 920278884 1250 920277634 920277697
    0x302010c15050a0504060b04060f06260f16031806110d060603021b0606060708090607060e030d0b10090e090a2015160b070c020409030e010e010c08 65
    0x201c0120389180100700405101d55421942c8941c0c032624041090752800020842221124001d400d40500b5619003404441c1c0106010340d48000c00188160b004140305a00041c80d040c21903202c40a14a031030300384640c0340324024404844c0c4056003000d000400c80802c1a5001880c1440064070064079400c1d02c4010742246012920024144038092100c142c1360070000e00039600c00c81c540000c90f20b42468554240b4000715955014960060519281c09141d0311509103582041e000d640c0e009800300040000613110b489422000004400515110400307481b110040301d0070851590700800494040b000b507241c0c4502d400003926820780101080f034441118084c0b6001caa90700091250b82c4003031110b032034002041c040a09801701100d0b07492a14980001e00d288034042da50328540705030f159100881c0060154080207503ca000d5240c0340481c0c010036000a0705984019a0a60111301d030140c00c003859590040039540c0c100380a09040044141c0ea5030f448240703108040410910b45070941c2c00700d09211070100c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 920280134 1250 920278884 920278913
    0xc09150d0c0905100f09140415030312060905070e0405040302070824090109080a08040602161a40051203100f050f04051302040e0a050f0f070302010c 66
    0x80042104402821002d09444024000c0b07610411002452601301485030311002c445194961700c09040d140740034806a000425255070701c0d8407540742c420251100403c3c1c3c1d50b010045010742ea4a0005c000d40b00184801c9070307055040b00903102c0c00d0808009900d138020391003504d0311006030f80c0014950f0707890600704d040c000c003500440d03181e005216141c4840f038264003414100100400c0380f0f005c26203032221f0032400c07a82c410f00001e0501d4018001d00c0310043c011300340e10f94414051000540742207281800c0c001404000305d4100c03041040e51800c020313048090207220754854040c03107050100b142003409084e000002d82c0001c98030146540e60074139281c2c003280c0381c04040d254040c045030300c03000080c0000042a0000c460803024100c40c2a00003070341242e08000301d0102c0300003400c0b40703540f03010400600000e07081c014a00b2072403003003000c2a500127880d50f00c42d03030348000480e8014080908130b41c0f8080c1e05210004001880e6640701c0300c041007540a0100320002283d50900703080301c4200039464144541d01100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 920281384 1250 920280134 920280157
    0xb09011206180c0e03190b0709090f061d040b0109020a021203091c0903020108041e0c0920030114060c0f060a150506030906150312030406140f0c0915 66
    0x3140c0380c82c00121504408020070164407840c152894a10616a44110f00d01c1c42980041090420b400480d5102540a400c074105160102d44582c0300c030181c60917500170311440b001850740c9150402c46001082126210003c111040c803500e070810b521861032501060040303500096000841c8100325008111411a80308101600d9469141c1409400d49950303401410f55103610120b10b0382c003945485510408152503050710b80d00400d48980d00c035481e91401d154400d05040c07054030b401c0000f19103000641402804261408909858900c0741c4170050b141c2c1203200c00512005000611070713100016068102c0b400181d0b811600c580c1e02c4900c0074075011490040d103520380144428001c16103c0c940000d41800c481d03854080740303d0780d29402d1152074802260054140e40000000c500c102d000010074011503903004040301c00041d16441c030680d255100359021500700e83e942c6801d03000500c012a00c6940001078012144191405180da01d01603c10801000c1c840c903041503c040244000f0f00540e2500d2490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 920282634 1250 920281384 920281409
    0x1208091612034a0a090b040e0f06070309030e130c0f0e0117040503070209240d0b1b1903060e090c0607170d18020306060406051c050f03030f070f02070b09011206 71
    0x11444254006c0c4000c0100e81d014074140038058044640008801c2150641480201b0503070f038400c10210010411180c4c12401c00c20a4245107545079102c0300441182a070003240000c40c0103401001805107560785c091003050029039110307084540e800ca00e8109002c022950701503025a1a890315500394070074210020351005140b82404100b0750000758107a0302e5003100910510391100d000400c03501401c8018010140b00c0c10300700148242c01c1c031090391210003810032401402c0002c0707145030061030030041d40150002a528481003062005a40e10075801240c810050411600304a012402510511201800c10441d506503011504116402c0341e01e400360b092000c000c507000224141e0f0410542c1030040c0d02c244aa2004034415181c01c1c0320328811030304010075007207040e2004405448030012160007910a40940f80511003200004c0c0025846680380700400c030594500214080d15400300301c4107840855009080034009403d044085526084003400c0088031540d400114401401d05500a609050305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 920283884 1250 920282634 920282639
    0x140112091419050f0303060d060c020a050f0102130b040602071e031e0203010b0f060901030b01030f062705011a070203010e3003041208091612034a0a 66
    0x281c0d500c80d600a1071040050b101384800d034003d016600e00050700d60644c06400840c0040001e00c081e8080320641d00c031801991100866521600d091040b005460b640d282d40004d500901f00307480c1140e540140c007c0354040d504040c24443d00a50741c41c0c0314000c1412042406281003241d59500b40481c00031070380440070311919612000d079031070f030350140030000c0307002b5802c159044d5024907080485500000001d0402401c0c14000001140640340000c456418955603d0421030114464001c101c050010f52190011100c0200141400344120388585540907191000501504e003403a003402411020003000780d502d44c4664000280103001000c400f0010b84204640303120080d150a09130f03041c4400210801d030754028110001c203601d100c215002413008290030514201306014001003604001c070b140c121000c12001d8900000101d04580103602c030310380080ca020081561000310100b0880807080b480c03181c91190b000d800d01c0c09114030b651658820740070707079031240d0900d0800d000400c02000510300d0f4002d55 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 920285134 1250 920283884 920283913
    0x9120901021516030f0b101209060612050d020607020a121e0e04060503030405090f0403031415040c0306150809030c0316021306050109090209030c150307091401120914 74
    0x42000d905200401d040c85200000311700d0900c600340710204007800780d803804540020100c03007454050f0303c1081290f82e01e481c0400441c0790341c03140001034004800c01503082c20351402c002d0314006a8440c1081154001400c0044060b030100d000000d240c2d1081840a0b510a0000c00ba5460803400019440c10071581030440c0e82290302141c150780124040c1c4e000c1000303175252030605407607100e54000e1039044005000070070003502043c4002035005009181c0029111041018500d44410a403006164800408000141781c0313024801c05803425002d0900300600c0c0d18080844090f205040e0901c0d040c4402140050408681801242c503048441005c0c0ca540d8010410381089070300160100340d018406142c00c0b150072040034854682030f2030b0161156848286050541806544500000340d054010181c0207819600c03071400e92200d0600a4500d552603250020008010114503400140d48621b401d480301c0d0310741d8205100f2240130320040408104070716103040018084000c2d680070301d000e01c5850041d0300f181 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 920286384 1250 920285134 920285161
    0xb090d0b1e1509010e13111302161208040f0b130b010f14060c030f160b0a09022d040209060c0708061f0e15030a050d03020c0d0503091209010215 64
    0x10302085403e141d071079894074035402944200b115415500b200701b101010200e204190070078112200209403d03100c2008440c41816030300860000b107004407003030030b140040045082407549980c10707501c0d105209181c0313901c83c803403145c1c40000d001e061341d08450040f50004000000c569001e98102d1030a0580396542c00800740b03607030014441c41d0030107144440000100d01d840e50481c2ca41d950303c40700440c20400d1070b21175002298400c1507a0502800c0355280c40000401600c12540324904455000035204400d00601c4001900e415000215042e0070f4a040c0c01003141100e446018041a680162180c0009002c01c5441c4a28940e00700e9a109000c000188030303800159051003403007010580c925003c013035070341500407140c45d01a01c2e0b901030340e400000310046205100201300303000080460f02c0309001601c40900700b41071074000c0000213800103207000c0d0381501081011280801842c0c007910b507150a0302442d8480303580c1401c412482500066540190f8401c201445c1410305110241e076281c00d01034040c5030007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 920287634 1250 920286384 920286421
    0xd0f140a06050f0a06080c070b04060b0a080a1a0a06051207031211070b07061d010c030b030a081206120318040c08071b17040303090801060b090d0b1e 66
    0x460a000d004603183c104541c3c0304412801c050a0040601c1c10010140c42610303008003801e03d80e007414400c2e84003080d42c4403400c50280c0c0c0158000250601e042050100200060f0007200081e0311031010840001c8025840c010081884110f085481d219204040007500e8158802a407082c418081e2407070329100454000102c92046071200080300380307200140d41200c0345000f011455004420700308052040e070030080508034440c510020f0481c64a01c0200382c002c14815140c2e100d69500c2d02d1421801750503100d41411504c08500a141502c83e642e02c0903001c4c80f50850716252030804101090103130700c13880070001c090408913054989954007001545c0c18442c1c07950540d4825414280e07002d491502559505015801c540c0e5000703440000d4414070756460f070100034204c40852000781054009101c04010b8030240d886695001411460980e11500f584c41a0b048500c140008021410180d80c03100c1607404901d51180d100034070796540c0440f002d000b44800714000f5104040d0410410941044100c4141c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 920288884 1250 920287634 920287651
    0x1110a11070e06090a0902031006261c0507050c09070f031104030b01150c0203120a031a10140903011e0c020609100f090c081c0302030702120d0f14 65
    0x91a42c1ca40070303221002d006588031900704c07044601141d8082620341200c40d50900103011a558000160102012945241c5c002c281c1d0660282e544d890f20059078000f00101248030008000c4d03040f0b41c0100041e01d5541d041c0301c60500c000020345d1420001c0038050b002e0b4a907001010400c1518143c3d901400c804018222000000d18041c400a80c19003000255005d07640c20242c04002c07a070170031400c4103e00643c01540300500c040000c0e580c0046c2e03000c02c1034080d0341080c881042d465880c07109025098603006505400314440b948035080c2c0341d0300c0b02030001c2e4a80109250461485a4140f05047e8034440c4c101c2440e055402e00e2168880c8400004000200003560380040200400c00c1030300702e0302d0f80e4081d20020056002a906c41005c5c00c0190040514619102c0b00042c800702c1c0d0f642c1d00c44103454668444109a04201c00080808510314400840c0d445941825440d500d400300d402500c40c206808100441c5001061840c001c2e00503034000410720391100010030001f41e4002141180c440300312003250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 920290134 1250 920288884 920288893
    0x60c071703040602070b03071b0c140402041d0c221701020a091a040e13050606090103050703030c0c0b07060603051605060d022107081501090602030304110301110a11 73
    0x180032400100300ca00b02c61455000d400c010b802c00519a40941c4090044000c02c800407421030346580b10129000c03100e078403403003272061542e00d80071801c40c140403004020b40c42070784144400c21450103100d8900c2030490440c8644d1070165554180c140490080f80880012080c05641c2144090850b41e8176000303544106107400c001024030b1485030300381c5c460b011402d0005001c8a000b00128a0342d5010342040c6101941090708164540c07a815203512030446104440c101400035030400d000040c0000c0f5008481910181055130564451540e1240f1522005080002150030207051084180380000900348030368590385c0d10682400c0440c090820b600007a03529028410020b1100c610b043c4166046601c080c0c0140c0c20607580713609000c002d41051070240482074150f0b000c401015605c916940c403a2016445000c076504200107548c3c81a00502011410f12000a00510400d900002078030707440750780000c84821241c503080110303015000c00200503100c004d011a0205071160064440251402041c00303ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 920291384 1250 920290134 920290169
    0x7141c0203181b150f09040e101514030a0c030b09010603140a0309060207050d140309040c0504031209050d0b070c0c060f110102090a150507080315010305091b0d02030c060c07 77
    0x20356480c401c071800b00d501c203181040500441e0800c0c0c0c2100200a0300803040d51b0452401c0f61008060303403400042b074989160a014240724080c0b488281c80b04401081c3e00416044900e0f070340d6170240c00355900024102c02000400a54424001d400c12005075a000149002c1003504040c415030300c1044100841c080b071500d440100d00f00f440012298129040105000d212021544603070840034101d000c155610301003002074040a84460107a4051524991380b043c0d0b48502d541410250000d00412100801070390300e808200e0350b035400d00850481b47e042101d010280d1598101a26080800040140124000c40c00022181e40002109a00424544030402e8103207412520908038820344060503484945001c0c18000e03003103491240b4001c1402428214604211511804800d4104481701c21181c224000503c9403940c0c5801000c9c1c00200305001011020703a081001410464010300c02e6001e152259044015542e0400c0840b076513036400740c01ca40c0d42d0340c2c0c072002054440d0040e01400c69070751022f0815 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 920292634 1250 920291384 920291419
    0x2107030305120f040201020c01180b0f072307171c0206061201050609070f1403090c04180317101e030210021f020f0d0e0607141c0203181b 61
    0x3d02e02c01c80d4142c0c00303800c403544500d0041d01d5a00060013102054003001c1e0001c00d5907480f04004202ea0240f4294440e11110700d86003030f10346d055480088061120391003e410300311420000c0c0040584602d20202d200325005c07d40343ca480c0c050804089801d001c011500c00f1080c503000b00c0c00d54000e04081c0c505c016003d0341c0105c07030741c00d841003a1040d2b60095844400a1505031144447c48002c40d51458014100d8041c40c440c2d80c425082687c8503041c0d034100031110f9242e8070340380c4101614102c0000b0404100c0702d658501602088440a00c0460a004080001c1c50f4400c0d4013580806040051502c0e1031040b10904217910540103408100d01503030f0a0f400900c18070f03000003001002c000c4c421260b2203048a2012000d40a9048150035004c410800d0000c03241d50300030350241c2c80c0c1c01c4060f44000c0005144c5401c2c000c01c64004551900d40400080000400101c000320030303101e08200002c4050f07926254400c80e017141103942d40c03034110030780942c1c04141e1104c207030190707090101c1c0401c9504444203050310782c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 920293884 1250 920292634 920292661
    0x1b090f080a0f02060a0207050901060207050102012d0c020309030d08040506090a0f110a12060e010c0306150e0f1c0303140708040b1306021309180308010302210703030512 75
    0x10050b107200c000714000e20061500900a00702c03000184161201e0710703690808138400003001c0e007003080560030001d800d1146581c240b18664900c0c0101d070108420343c500d229800c40d43e002e0348014400b8640c4441d14007801a00800c00c0328070014000e0100d55940101090061a03904160344c125414003c0ca0049044413400003011004182c01100182070000541d0310f0492951805184940001040c14006803c1350811100301d29140100c1020503a03100308075030039003110840c5213040145854800c0a00243d44204109490b030080790928514000a00000451400c3c00700308a9500a911000140400340b90728481d0032200c0c400d407030a020352000c1020403242c4d08001c8a4a03c00500d0800000d00440e0114107003a4201c80003036075481c030f140d8064a80c0e000b603a010318090800d04032602e9041054114507c900364450b10b40b0030340203203480055500182054010300c0081e108440746140040440329440300740308008841402c43d11b019581c2e01d0058056040812001c580010400014115201410303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 920295134 1250 920293884 920293903
    0xe0108070f090507170a06030b01120204140705090d050c0a0b07140c060316170408040807051c12110316020a0512060429130b0c0c0d0e041b090f08 65
    0x440702404411540c00c031410b82d9170000c00403800d40d5111140000403400e00504d590103003e035562003501d0742200d80140001d4400041d08400b80641c0d0000f000003d40e0300205680c0064000c4601c1c00c0700e1807103824614540203986002660040602d1030000d82001c0c40401002860302c10a04441014040d00e080d54aa42c508100b40d80c00c03800400000d00a41c10110406038013003e9030401d0301e039994118016107040ca20469003201c181800090078400e00b0000c10821009200481d0070051500c0400023052000030390000040c50141044c5130300e02810f0140400701d8924150204507a120b003410b031030242c484403c2c42d00990060040807004a5103040601c1c1448074003613614010212a11140d41d00300882024101d003045410582d00b281c007296800ca40e203d03004030742840c85c024003035200f400c03c295030300307005000c50094803800c0005034000c070008030f500c440000385410700d034207081c1ca0480800d010f8082c0120717000c000703098810041030903900100b1070400e4030440065030840e40d403241203040d540c04888 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 920296384 1250 920295134 920295137
    0x10803040b04060e0a120606030b150f04021e070303140a05090a11010311071b080c0a062109050f060a2009120d1d091e0403090e0108070f090507 64
    0x100001c3c4051402052002c00a81c80a408050201c4d946e01040170056180310045580d10703141d010410610052700106900320740680c82005600130480700003070b1140500804140100d8001c1900c45c81c0c119807400c55520003c02400c0203a8034566440d004000b40103181480d0f00f403603e6803000c2448182148622441144500000c1c240240c4540b038156403c0c81c148031450405031684841011004040e001e05400340c03150304407114018404407002d1000406401080d125480015a82d560f43c3d201c5414100329039090801d400c04102200780501501c41c0c840202032a41c0c100080380042100c002212050603030020103032101512804450000d07600449030345074201920480c1f043d80d80d07034640e0040c444054020007a05074000104900c1d030400209103100000301d552032505511f0280b6480412448a80440c0c00d01400d107400722a51035150303010440002c0d46400300e000102054050540c600242c40c1c06105216250b039034014103607449415014030003180740000c20001d40e50805000d500d000e581c40c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 920297634 1250 920296384 920296387
    0xa0b09160e09010605030d030f060b070206041203020c0d200a050a06050d0e0d090e1308040b03090a060e0f160b040506070f17040501030509031903020903100501150206010803040b 79
    0x18800c003512001c4015011a40c80c1d50780c1d00c4001180d540c2006030009200e1a40c030b0115003001111070311000c40341141c1c062143e180c010052000142d5800701150107032382141c58038414052170740c00c08900e4038011044068011f06014140e009200102c0c0b1301c01420304892600c421070000d040300341b000601c481d128042e04544012021b0121500a0303002e0311060031210030000d2030440d00e0102078503148540b46100081440007000b070098410480e0201c1d480042000341c03840110081d82c0d014030510a910400c041a000400072580d0b11b4401d010f11300c1052b401a00602c5407240704202292613100e0107105560b81d10441c0c0ca0107a9009121404104480c8011045410945000c00340485503000c0c2d00300310780c1091002031000000da4a43e12607030440710709196198031241044005021100d014108049590051002c64041c581e01203412551600d00d20b80961a0300812010070300d8142401c07a5034460700e0902d4004114000300003003500411a1700c0d800c44419980c0c68042d03a0300d81c8200d008001407080d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 920298884 1250 920297634 920297639
    0x51002060f0a0e060c07170a0c0b04030e0904051c021209120f030a1d01031b12020d11090f09100b090a090f020c010606081e060f030f0a0b0916 63
    0x9010030120b9000d01502d20120740e10000031000703410981c0459010050550100706901808007003442040c500c4000a2034a14180900700c0240c0842c030b140100501e000c841600040416219040006d690030014040c4034203800c05240254465002a82a100d40f100c0a040c4003d05480065600d19100300100c015207080700e800c0c00d00c42c01f44003119664290b8800da40f0f2050716184200010001e00e01183c0e11500c4007800f41c018104158510486d443c10503040010f2200d290354012040d0700220b4071810030040f0201c0c2e414548000c3d008079401002490314002c40c040d00305aa4000518885000300c8801c0404070565003004900c10f0103940c20244144003080074000f0300b0342180101001d0600504c042c90344e5035201d0030f140c10b0395029241070b44844c0d00880c1d58207440c80300b40950b03409003403142014012490010500207c541005080c110074500c07400104020b42ca9a1014611407140682a11209001084040d075030324503550080ba0070142d1400003d120f0700020070701e080040e0440418010151 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 920300134 1250 920298884 920298901
    0x6030102030705270907080403020c0612070e130c050705060f0103120c110307030f0b10031707060f1112100b0405060903101d120f03270106140a05100206 68
    0x501010110514042c4840c42501a518003503864802e806c603036201641c91402c0d20780242451903100b84980075200500002e0b54028035176400d140c0c00b212529010420040d1800010041503041d40040c04503450003070134096455020000340259030086048801036141c410141c0c00d501000d11000d01038403194000305000b01e00c07800d2000421409000507034142e04404001a06141080d072084403401ea00d20698001c01107561021544500b030032880b1070300f1910b581c40c2d0212190301000888480100014044104407186d80300030550413240d8420041003c08101500b00780d0700c92100010740e08900070000d1081c42c1e07482009401c2d60110003030a401c01e1700d864244562500005c140365070500030040040304503142c0341f0501c1c16400110b1030203503130780000a01c56420000d0401401c0b6111400300415072644410504913600031070b2419242c1694a0009482400b0100400500ac440d500b404e0002036100103002008000000c221407030603055641304100030305a40e2040744a80581c102500080165 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 920301384 1250 920300134 920300167
    0x902090102032b1d0a1407090203102103140d1b02070611030c0c060a18080105091920040f06060c050c0103410403021506030102030705 60
    0x8040c01140e00f814036014202c040a840c22030020b40c3c0c2c1400003050840d03e0319900520011071583d8515420004030030203225111500c4c2c04004d088106a25000703034404070304110340001460304100440d140d0801240991050040c0d10800001620801c21b5000c1c485c0074071003407611150305071a5074100d0f2912050030049034015400440000c0c0d0b85100c01724000900b01040000c49232035901620245085c050007600e0300c0e200b04c89522a40d0310912008205020001c4d40e81c00faa0811140c0a45940880c00c0c21900e485d09500041d54121052400013800c600540106009200510030b03688025210382040d200700440c3c4002521024480b51a04c0350f1013440c0c0a207192412001d4030201d50010072510000a0b5495a400140014455032045040c02024004040504000d01e011300104910b424030040d0036800c421030b01c0f480302c40020030071a50f404456080c50303002d0980400204a00d0b241c10044d4450b840968031078104682d103400250f6a24040c401c591060080e511114200350303000c000074819 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 920302634 1250 920301384 920301397
    0x2032812050705091201150b040503030f0d091b0329160c0c150806060309030403080a05070c1d0a05070504090c260414030301030203100209011b060204090c0206060a0902 75
    0x380f02e4200400101c0307440310b180e8600710081143c0042001c04c0e100340041ca61036080d40c1b240c2e0301414107200602c11590b010048a69000100704015141c01c901350f6138400800a00713000921048501030f410f0310804620740c92400b1039000728410000703045603803000300800707143e44e01e41910520102c0c00520301c00d411031086142c100140c03424065080503070b61002d4034404d0a8200c2101c80707503684165a0385503070214425621040c2a10b20a0941c24802c0c0b0050b03480c001da010040c00c400f0301160350100544260296501181c0250014010b1303a5102d40300004011480c2e080c0f80008608400225000068010280125920350358280751030b180c82c04200040c281141d1140801200c12418a003240d40d01c000c0802000c002000d183d181d050600c2d240c501800340e40004011500140300420140c1c0d40411500c80c003503001c04000d603032a42101c004030340c1d115098100c0c03040c000c001da400d43d0600000358003070416552590410001440c054006076510801102c00d40c0d407140d00c0803010300043d049038024100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 920303884 1250 920302634 920302637
    0x1030504080702040903020c0321040303051c02040e010513020703020705060a020a050105090318030d0c0605060f1206100533040b0a03141e2a0703020328120507 71
    0x200b004642c000303030a8460b40341050700142d0110450305241d1800b40030244041080c00003036400c0b2001d42030904064011342c40007038140f000200d0954918840000300810800d4182d2046503103e4030759400c02c0241c02c0038004c480c0a10364856075a00c4519403482107900498150b0010941d0620300010000d8070707440007406c001140100c00c1b551002072824007420303000c1c4141c3c0340503588940c405844c0003840d442044106c2e1180c1d018250106429800c04054640c2640110010031159105004581d10084440d000c0d074102940310042c20200a020907018001c03400341d55074100f070030364840800c440c0f00407800d150212000741c110b61140740c1401090101300c44064a1510341016030b2100801703216009140d25002007070b15280504901d1280341003141d844480c3c91220028400344500c0034800c0d030001040c540d00c40d94041821036442020b584100004005403429070760340c07603003450000d469410590190441c0d51411000000501c0c0300c818003035611002c1d41d100c000c0c01e4180c0319200041c03c0701034000c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 920305134 1250 920303884 920303887
    0x151109030a02092527060f0e010903120e01091401021506040f0c080906010605031005060a030e1002070507080c030a080703170103030917010501140f01091e0e07020604050307020103050408 83
    0x440f00b18414180496003070313054899030100b04c0750211030007985500700700c0c48071282203010741809100d4000350354038407550b400d25140408088140c01078905c3e0a203034201800c040c0c04003410010080d400b515802c44040300faa10990f0581d554000d0200da04c3e40600b01c58050781003800942481c414518600344e114400601c0810307428164007488048400300f201d02c01c00542081c040110b1030200304040703030041c00903107081461031030a544044600580c5004407031081600050510340c182c42a0802c1c080e210900050320720307801c80d5090001c029031050404a82c540a2088009a51140030802c040083d0002d40905a107802e165a9030800358000b150803000e00840208000d1210207141c0d54502a500c41c0d12007480260900e04920340d1001000780c04881030f810140140b06540e445200c00107a180300342c5648401306210070040c0c4004015401080c2c4070740c0d01d4050011001c014986000407070381c005031540760948030380c242262036003c04c54016096500400c02400194407960015038003900440c14035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 920306384 1250 920305134 920305171
    0x60a0e0a090c051210030512090d0b0a0209011b23120304032606030c120f0609072d1a070b090a0302011104031a060402040b07151109030a0209 63
    0x38040395a505102c800046000c0b41800c041500c0e0402c0c40c1d08241200000c0901038550780e11f182d65050b1402c104e510610010a05400036103c24000e05011940a00041031900d1300c115164001c0d0080703042e03140003076900c41d60703410403c0c0f1861500660b15040742c041000901c031110140100c100034400d02e103030b500c01c115108145007050005503000b240329545102030304049641c01c03800440c00000040140d0b4915007807002c985d4000860f001002e0040e0f400c1c17404141d0700d235142e606000101ca80d01c40180034000c2044888030001c900c4100f074401100d40310340c40808040d030480c41419034110260303d402e001c00c010f00c00c1100f410800c025000c1a11421858524180e807026460841a01d81c0400355100780405000c06070203010306c1509540504c0903a05151640e15565040400d420000c0056580c05d0302280040c2c0340c5404941c043e00f88141c003666120b003a40b400c003d10038050084a08102c1c0f41010030403c103103025007200c3c01544014010040f10840d6000c21a0b482c1c009042c0d000c3d6034030310782d010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 920307634 1250 920306384 920306399
    0x40c021e0a030e040c020d0c020a12230c0907120204030218060f1e0111070b0307020a1101021c0f0c1502040509060f010903030c080c060f0603010c0e060a0e0a 70
    0x411103114009000d050058520701c0c0152103091a1601c4134415400d01c2c0b0140c3c0c1d01c0ba4000740c0d0307000040740d915220129048500100c2d24502541d045603515204c9020807805101d19120076107000785180d034082490000c002a050384413012011403603030044111011030b00052051031079050241d100741d8018642a42c0f50300094045000200301c1d0004e0107081c040194600c0c2c2a007050740162404d494071400c0d09170188015070030a00345c144450500c020000c1e580400d09c010003000d0007403d0720045055503400c0c0b82c03d000e9501c0b0311001045403842c04485008145500c041600207075070b2080212010342501c1c1c40c005480301000280550308000351400900c0c0892200e014540c02d6040d8aa40141e0b0756080506000e428007008010b14080c060068000060780d80c400111412240c2502d40010464101d1801200303d102c1c0d880340c91081d102d034030144003050408161b00c0703020b00d400705c000300000300160409651070423030080d43d1035004206100030305145001c0e00c6001142c102c0204039150842c1c07280d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 920308884 1250 920307634 920307673
    0x10e010c0e030d020a02130f0603050f1f1806020f1201090b030d020c0a12020d080a0504050405010e0712020c0106080316050105010e13110d0f0b072c040c02 69
    0x803640009404001c0412242c10207000030342042c46148040c02c908850354000c513840220ba42040c61101e6030b9244030307107070124166106501866001055440da200c030070703595659840d018000001044811803c200d64a505449507141c100441c1da0800400034007a19070f007000703420106180112100800008a04ad1007590106001e0122000006068000700c4149840d203a00406e140044d5031200c0080251a0760f104240c50444400762102e00b90105e06201040d81d8200d03a840041c00700c06c0118000c1c0c06243c010000d8001e980c1e040d079007001a6a61402c612448c00d000755400e402141c2541c06070810002c2540043c584081100000714246988981082c0345a0040d0103503480c4810716100d4004011082c05043d004003840d1003170030751500f00b4114407009114400d0004040340080d841001d03954559548800c1951380003050b00c0c1d800030f218101100b40d0b0800702c0e08540014010840d40b03210b002d0162004903003020030402e94400b11294010300c00184040c903064002c4d03118961030040c4032100d201 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 920310134 1250 920308884 920308901
    0x1509070215010914011e030c030b150a1d0a0b03030a0801080c030a15020310052e020d0c0209040f050708100b0103200a17070504061b050c0111010e01 66
    0x24028200105194040015103506802c55a502400c02c86200300c0011325420750f074192100080500300903400e41565040c4220941d20052007031000c04400024030908500070340c814110309410304040700a0f0410080042c801c1c1c0a08440b1004080400e4041880303616001d80c0941a040d0024042600000003031440d006101c64074000380034a001130180c80c9051140e207240400903002841080155500d4164101510350b40d440c400e0f5011002450300c00d80350060754018078018007001c400076106880c20042c050358007810300722102c2c030141c03143c00103100040710002c2952075a03a0282450f0f141d4204038141d5000340096030b400402400340d60205600f8441440100b04200041000052803040d030001d0b00c80c0003043d181454a01101419858000c4580b8011803c4151b1003075514100c0740c00a07a900d03803508844180c80b01b000010840c0040d00400204256841030301c69490081440044a2408460810041c01034210454841595002b01d07a288600f56421001080c0103007040541400c5906a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 920311384 1250 920310134 920310137
    0x180b072106150e0901030c0b03040516060507030f0c0b0109020c07030203010c021510080a14100f06050a17030901050c151e0f0f15010201020706020414040506100e0108150907 77
    0x2c012451800c0e0020102051140c080c1c862902962440d1034580e80000ca920521f503580d10000002403c0040500c00c01c2c80016524000b00392107500c6500003042e135040040d00b10003061000b6100f132419401480e02103541a4071000e40d0300c6c9a801c2c032030500040d4100d0141241503101d54180400165021702030740351902c510b603008120b9101c4040620300701400103402d041a040c1071b00e034144503032540418480b0f802c5070400540e40041070ce91403402c4ca084c10f0204110030380351500201700a600d289810280407604102d41406560342c50711440d821100c100520000c441d40100b001d40c110354000d40c00740c41c2ca8042d031800e40da27801e41c00b40308031660b000c0304403104400c2c2a00c4248142082ca01d03035000c5500000080421a02882d00c0d07102c008240c1c501801900c00c210810145948682c400d40498001036070201042d501d03240ea60b034041404507003058005210300d00305030014240d802c010001001084050361001192110140196105107002d000da207100125012854103a03114130420340d0083c22a13 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 920312634 1250 920311384 920311409
    0x503030f0322050a030c0f050a0b04030e0604080715021501140112020a021905030f070c0f050105070b070e06040f0303051b0601050d020f0a091104030501180b072106 73
    0x2040401c01aa8082c039801107042001e544020205500141d1800d102d54076003800c1c0c01c028005d007000381d000651204001e2403807056044040401500c102c0983c00340d40b20791200c21030703201030804101503405140100f88980c0c1c8001403c01190203880e40c80341e00c0454600595010580307441c442c1c0c400c1c1c40c00341c0282d194080700c16490091942e00c11180c115050305503004504202a00c079001303442d140000002e00d20160b214040b01c090240a0046030f000800302d280d2103980e60003504c0e1202060200d40310b40311503e00e86800c0058554014801c0303c0286c1d50200300942250f540c0c4405582c004032542e8403035000001030102285940358003034040040e60280d203a194640e128041c0180f0f10404100e480202d0f500300d00d004000948034110600503255045440c00141600100800c0200b0220b520942880e420030020340c2070594800c004005981c0608004e01c2000300000103840900889940182441c1090340010b40c02d0744100c65560122a000c0c490344c1450320005003031000da0300290440b8111126 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 920313884 1250 920312634 920312641
    0xc060209060a211109040e010608030a020c09150901170111070f1218090f09080a080601090602010c0e011b0b0403020c0a0e06060a0c05160f0905010605120a150503030f03 75
    0x2034420f0a40c494102043e0140700a0031811307880c010a004494409008603168820b10984003000c0d0880400707010100120303034440c44e40c05402550b0b0110004041e000b8414480821040307134100c000e06081c400e005d040e00c0550703483c01c051803101c0c5c1c0395008100c183d0b55035628044407000c80600140007141c01801140500d041c90f051655400701c00d0080030050000380000000120b25100c0e0180c1210012000001c500302046940c6002d0710342d03554000c14405000900005454000031101d00410082e030701c240320b09455007001d90880d607940e4040f0011500410901049610517140b140750301c07050a40f54003002c407140c4c0d03401c010f070403042e28124090303000400342c041c05080105c0400d00070005820102c07400e040c40c0010030303841c0c410100c05e0001c000558800c001840790030403841084072070200e00c0700001566465880e452804c2805240080c034108000001c0c0c80344204156500c801c03a108545c3c0071a1100c41c502c60040c00e03510f4030102104803243c000075160307809101410034455901d005594902c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 920315134 1250 920313884 920313917
    0x21170106050414060711011d130c03180305031b0705010f14060a030305030412180305030306030c04051509040213060e0105040b04111c180305090316080307030c060209060a 76
    0x100f034500b01d901814040c0300d1000800c1c0320500c0c07120307009030038200300c4000400714086245178805c1450550300044044201c5401a0807980021204111f556041013903100003249000300e401c0040001d000990240003203080205505100900c1c0307001c0108443c40c020407684e92134203444450281800d2075590308045001c103000c01314000d500c10021183c04202d607095642c003800501000d0400303024801c05452406e0560700500764000e88000464404a08940d00d242880d070740d0f8002c868080c040d000c3d00354100c0d1141410300a0b1070203803c1ca0403041c0340200908040c400b52850080080e81d020556101c042c096620300d201d200050248421075440703a60500080c40107854040034601e00440c03900b4150342008400e082610080c2c41100300c25504041c2c0e850300900030f0320048101a0303ca8030004545000c06400000401815000b50301b0790326281d20b1840c600650308a00c1c46800156001040b801000a105141512607148684001030810303080801148045d04010a080c0120301c50030320500165 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 920316384 1250 920315134 920315159
    0x315151902060723070c1205011416030b0f090a0603050c060f040b07060b06030a0b040e0c060d09030302041d0403480b070e10080103211701060504 65
    0x50356140000e04490030309000040500c0c0c14100141107181800034498000046601107502803500b0601ca1000d01da02d8030140c140e40d10303842c40115025071900402c140c143c500100a94400e8030174602400900b096040150064080c0c211490b030701c0030140200d5212a660000c6d05400360b4030714100019940d0070351a20b5031030000c49120f080d10521091240303840516800d41150281c03481c114515440340c1107480c0942c003a1800121a5501c07080100420100122560241824075802c45080c805280c00c080295120b43d45220810b8100c0000c2000f00c0c00c0c02e40940008400354864a070040c5080c0d40c81c51803c01602e40800510043c00d2154140014560301c45080b40e45040c0300c0a5a60746206032100441c1b40141102000440b400c0c0d1a0640045d040c03815000d0b0140ca400054078002440e00d070360000d02e00c801c4400c2c1588100040b2025072510b034446c0340c9140c10b8980c80781403e07200e409002401003210f0402007056080003040b542c852031b1010003900b51030080c0750310744690f51518100038600412 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 920317634 1250 920316384 920316427
    0x11010216140d0809030405120f030c280506060609060c0f030927040308040f05190c0b04050102060c03060d0f0809181e072f010c09030314031515 64
    0x30450f520301400b0700c00e503000c02100e0450b0801c407007124080003007409540c1001110244c0803418000070030001c9051402050300d07860329a42d6140d0004d21246400080da550a81c0752000d42294070520018026080c1a40203103c1848000e10440c2403c82400030a49000c3d58405001c20940000c1540403081c1480c00d403580714003110502c0080402d1885005803000903006101508101f50440130030280004112210507498012007560071220050604070415031403000308440241d403402001805081007402d4409403a0168080e044640301c4201d00d00550700b010300b01650101000d07848274001009480c07130b5038004d0720440006440340d10781400c02055020001004500d410400d04010308515070301c01244902810007110401600c80460403654800f5203850608100f00c1d007101d031000c0149000d106203507826150000d002640104000729010300e05880000c0100c0c644441d589103000031000615807008080c5107841174000031200203400b40040521100000c040000d00b0280e601c0050301c1c0c1c00e40c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 920318884 1250 920317634 920317637
    0xb0a05010801030f0b0403030b0925210e0f07061710030c05010f120608151608161b080909100e061c080c0106080709180311010216140d 60
    0x65071454813904000518240e0060a40e215000040c007054043d0b80050030381c280c00b41420040b4504002140303000143c56100c0b040c44085a106d038407295101d00003c0c02841110300000440000b20340c0c21001520000c0c12404550090001c805200d034070401c640d800400090b40d402595070010280b003402044007400d01940d40010101c10320200315040c0c9550300b07d0f4020310340818407034504442110754034401c0500c41901030910200007500f402c0080d01c1034003505003615406450301c0380528051000c825022180c046007149001a4940d000040c40e11141605401c24901491058126042284000c1012076102402040e213020300d0801d1103010b50301c4100b036880420340710304111403001c08840c0104032070310803003109000f15042c5030b10f6940003000d903a21810b80c68651507401c07143c1d40a441140180c010390310a08000041c1d070141401803200004e0614074440010b00c49442c01c480e5000001c205290543d000c020320105001c0080e10900b5850042c1300181a811001019070b00700704102d040c00c2d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 920320134 1250 920318884 920318897
    0x118020406050711061c0218040902030d0e011103030c04090f05071d060909250c080901051323091605030c07050a0519030207051002060423100b0a0501 67
    0x42456000380880f01e0154100070143c903100300000c0002c80c45e2203150410058000c0080c2140845030040d0050308036101d450110030a00c48503c400c2c441103d0034594082c1d455480300140740c1d0002d0040180300d05030401850500204402c44807864510342c0b040e6048203446138005010040d60751359111359001000b04c1442030200e410054401094100441008900c9081900d060451582c4a1741260705101000e040030131186406840c485510000380c45a40c042c0d038900d0142e950701032090411001c51944030041505102000b0011502c903088001412501502c0c03c10120749407410308600d5076150240030800c0f040c0010350b01800050030b0060001c24841c40054980d03091240c2040680c1e6201150701304154940340641403403490a04824000b4145000b02205010300c090441c0f0f04070802d9000e5004c94500359a9041803114a50b94540c0d02001600b01001140001300302c0300c240c83c074204a485603080c1c20f00f410b00b0042d0400e08202c281c034102c55501e0f102200c190504440fa840100703801d09001c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 920321384 1250 920320134 920320139
    0x9050a080c0312131106190e06130801020301141516060902041a0a0b041401030b030a0b013b040b070905030f100b0406061e09090603060507030e010c022508060f01180204 75
    0x118880911440d80300612100301c1c41808c0b6034640c030055422040342c004184942c990746090b101e0007581f00f0700801516058004204c3c00d0790a06003080c84068491b035194600d481c0512400700d4940d10103520485819489003440030250742c4c2c9006c1e45034501da00c055178404114001c42040701014160784440d084003414041002079408803842e1124007131007030034046490a00400024100340442100030141d81803000041801d800380618640c00090300040341081c0380001107400500200d45022600310b07406600020b0008a080c184144c2000303031800c00b02c01058a890009080861055540c9003a42c05250008114001402030007501d01c030696081081c00d0031b0200003880c000d5807000008a07002c0007049528081d109031908002002c072948100041c2da103038900700000d01400d44a10700022b08040c403c401c0e4517810b07c901e465555654000300161220841c1c3c107030100d43c25a2030f1a1150707240b1800000c03015024400284030f40308001880303045605000c04810b030b01c00c252414a07192413042c40103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 920322634 1250 920321384 920321407
    0x50a0f0b010801062607030b15090609040b180108030d06060e0334060504090b03060f0f09030d0f0203010914131e12120f09050a080c0312131106 64
    0x10b56066450f6442d10440d152200c009864250000b558031505451044042085e502e1385035102e860003075400c0341c2e0b48003d010203000000a0b4012a01580d511900030840b00f1030f1807925a1166100707030b40142124281d802c10071990000d45c5400d9000c03150b542c0002401c0c0c03080600921411000d4003c0d420032200058038a00840da80b215450a41020094081003030300704540101c020341503400781184041855500c42600400f2a08184034a1280e64205460382400307140110715244500d41c4e00c140f4284550f141280d1480701c41000d4420a106d0004003c3c08118090301c0c0100c0c0d40459410001507500c3d490040400111003419001c1d2400c1f5541c0804c0c0100683c50750f805038502d54001da80450342008040f1120741020208800030203c00203004510b50140e00b1401e004e17101c860320803042041d0700600c3d080c0b03800d41e0b00200000b081078028184d1080012001805072180c2d0f18031400b10303810284003007011801e00500703946020311802c102c01074200b000120311491404450a845080c10040b50060 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 920323741 1107 920322634 920322647
    0xe071b0807170f180613030c05100309150c021608011d070b090d0507033e0f1c051605030609030a0f1b05060109050a0f0b01 55
    0x4858003014010240c441800c01008402c0c5005540f0042d0707000c0340c04134a0000e074480c0c0306204107581e400c2d5070362002d8041c620400ca0b90b91090b05000400c051100140e10103410581840d098000051342c01211030001c000e902004545451000c0c010303400e0209038070707600c07500085105002440d0b12054002100c9014140e101c0d04009101e9000300303454240f640a01c0443c003d0411144d0304609180300001d2010b0700800503585040d8403641c407840c550340d80c2980b052052240c901428041c00e1032441303101c0e600e031000c00c03404500400c00010070840c8001590852055510520120f01c4a81c880ba000c3e00090b840415542803400034083c0f40742020040c01902d02078410880007030540d01c000411200340d580c02d5205d0543e0344410136001c8460300e4041c4041c070300300d1101088100c0043c004004544c00303403801120201d00d45c504040481d00701c034881c0e030301000400e0418100c24040d0740c101e030 = true := by decide +kernel

theorem cover : BRFrame.Cov 920143884 920323741 := by
  have h0 := BRFrame.cov_init 920143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 920143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 920143884 ≤ n) (h2 : n < 920323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
