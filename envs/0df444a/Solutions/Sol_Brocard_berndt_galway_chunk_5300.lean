-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5300
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:24:53.619836+00:00
-- url     : https://prove2.me/submissions/4c389e1c-21b8-4b22-841c-1e781ee0722a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 953057553 ≤ n < 953237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 953058803 1250 953057553 953057561
    0xc14070303200307020c120c0f0f0a030c0e060616030c0213021b0105060406060203121e071706090112030c0c0e2a131a0c01020424020a0c0605070501060504 69
    0x103800e202e46400814070881c130b501000500c01c200703015140354146c0501d4a81c0a6100c0c480e10041c180110407400891031103607034401030359103801001009003100640301c2c1000141080c2900507030456007080c02c0419480c0c90314005031240360b504009002483c070030b69541140d0141c02c0c1071080780c100d11071984040f5000c1882c0060b1895641c0c09000c1c092320281d9811003400c0d11170181485000e98034101082c007640d0341c084100c4a21560840d402580742d01c3d1200d001422004610b2102c9402c3c04043c21310007619400482d280312607009100030649600d8070010001c031424203100e031141c80381d02e01d01c1050010317008901c07003d542c07400b414003041030700c2e91030b81070000e058011a0140b501c0c20100710010b198190500d0004c0e00075501040030341c18000c00c580b09503a55203c5000b9030882c0b0088541480d10500c540c4101c84003441000000e54949694022000318806115803a00c2c4510600700e001040d0762002841c110307440d0f084500e50400307500d0b018003034440d90310100050715036548a48011076180c5440c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 953060053 1250 953058803 953058851
    0x8070803071d01090b190509100905100801050d0b06030a0b01030c0512160e06150a030203180a0f08032d1e070e06090d020d03030902040b040c14070303 67
    0x4910300e511011000c0500009800b011090500241d000e05110100300441681d180034080f003148142c04424410030303a0079000310b02c2c02c1580900c01c10b40c42030100350700c1a501400c0320030a582d0070300380760301420003550076040c240506500300d03104822543c00310740541003d0707401c42005410344035030130400d88030080b110000f60016a10381698442c10003042c1041010071207601d0781c0902400c0440801b100e2004c0010321845414030f9552614003242d20f940c6d4000a0340c2040d0703145480303030750b5540c1040c1e0085d000c0d41084a05030b00740c80110f0704205514070081004182a5032101b050b03c0c0c258640d5481050310380019110401843d000350b80103054108003010744c60903c126a200541d03078074059071031400701040d01e480c0c030028200300000e00c40d5040c0c01c511608034840040351a952240f000101050001c94004d00107540010141542c03010300d07030550f010302103e5000340d8090000400031000c3c841529040111b140006c1c41e010314901e82d8454940c050100d19101b8074010038500d0425075083e5012000c09 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 953061303 1250 953060053 953060057
    0x50a1d010e07210f030e10030b012303060d0c05030118140c031c03020706060e070f020708340815010603060b030a0e1c0f02010b090c160807080307 65
    0x5181510703041080b03480c0041c0183d0346260018441c9000c0c4a2001000450083c04850041c41103c1014052032010210040203007011842600100005014241a0001c507004c90030108011110b004104041c0086000006d005407860302c0c0e072030902c00003145004058505030b21558020805075028011440704c0c800100c5038403009007150410103c03610b15884000034030741c84080d07a0035460b100802d04020644c09010115204098000140c2c007034850b006005002c50303c0d208010801c2ea1540007010b010f503071155103124501d0b01910050386c1d10071050140d004a0382c0000010707e840d003903441401e01d240405044441003619410407a10b4289030030f4100000b00e8103e4194218905a044803442c0184043e150a02840d89002085400c5c2e200c00390010715406c1d01c45508001c003c004001000500c0c103125441004810440402018001078006400043d403c040340c8000a18140c408540200c0c10010380c03621300a041500d9a0350010b80b060708803612107050049002050041014510840c0e2036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 953062553 1250 953061303 953061311
    0xe010e01020a080604090c0b0d09050304030c080c030609030f0f04080d05040501181503091b0b0a090b120a0c090b0d021201170618010b13020c0115080d03050a1d01 72
    0xc00240c102c04000b81814000da00e81b02c01480480c42030340c0010b00702c0b00c2e00c1c0340c05560341d00c0340801d080203050503c2003c0c3c0940710001c0c0020420010551403000c0303c0310381c01558506100e6404040d2910020390b1180d003150300070b01031404400030080041005042d80d02c2c40324500343d03803942d6060626010505400100d44085010046560800750b40c0010351049505030b04080d0410010010700c03401e4051040400d0368503201c2504010442110030003c00c01c40c4441c1c56517680c0c88044042c6d6510405800001074150000040c0b0401e4480527592151074142c130300f61f050303502d6668507401040e48000380010030140c198002940001032009240b0311000c0c0e5000340e070783c9070003e100c50302005040e4030001880b102e4121190b0201000310350607410240036440b8000300403c0804c80c0340034042042e0380992201e100d94212046801a500034018510118002d10a20101d001a420642d81c28401c007000c9420102c903d1030382600c20f074404d942c0050705000010341070650b03080521086000b864040110b81d51 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 953063803 1250 953062553 953062567
    0x402120c0a17120423012c040f0e0a08092125080604060504020604050a090905010b01111e21092412060a21060e150408090102010e010e0102 62
    0x2486812601285801c519113807500e00300380344d160808240503503644a080030002d00705580c4503d600c41c8448400855071380c25030202e071a21300540c002611900f40f0a6203040e1003288070800c0350091100c2d50a41d03501416410100c4e03200c44030150b03c03402040b036101e1000d00701c40c0101c00c4040069400100180000c0c0070342560002c0c10b220035200100032020000004808100124001440591150b402034020401b40c07510b2000c42c0340d5000e15040183e108440c018082010003150740565407690243c4020301281c40901c005440c048070141c002505504028040604840d42c0c040c0300d07003840407070400c03140c03031500542660299401c0394010307007007580c000100c014031880d01e001104224010300598100402c1034151111171446104201014108280006440703a510012044018050b035040e141900743c0c0b0000100c0074511400d03007107442a24181d92075904c40c00004e040e0b2410203c02d00240300c0d50316071303450b40040764010f02110740c1150740301c8c42c1501c11803d00303002e00100449624005615418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 953065053 1250 953063803 953063849
    0x306071430010501030516270f0e1b0301060309021210020d061508070804140601330801050d0606080a03050705070603090206030f1807061107080604050c0904050709060305030711040c080402120c0a 87
    0xad000e4100240c29210702864503980c5240d0086904481c21401c0005007444a480412000d4001d502c00c25020b001d08807140b5000042340d00103042c1e4500190042107001d4a03420024140103528030040b001070790360000582c1c0503004025658116010b00c05e03001400c14081082d9162082c00d800071004061201c03e0f2121126403403044508120075941098020111450010504081440380314070a040c03180510b014000942e0141c00500b0300320040c3c500e00050ba040c0a0300551140c0d80c116550700c05c10900164542c464450200100c2c1c3c0100305a05e140c80e031418a55180101514001e050010442d80e400e4100d0b040100c0780043c992a2922410305002c1a246424000540c0c0010540e400000c1004000f40b800305451611780c000311000210b07502c81c3c2c00c1c4245440a2600004005881d2807408001d020001002d008000d2084019a06101e0507005200c256040303d0400b201042800000c5030051404000e00c8801c0d00d04c08048580c01024075001443d0030000341d01080c0c04a1160014a030019 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 953066303 1250 953065053 953065079
    0x90f0603170901080f130c0807080723040f0209030d02010902030c0d03120504080c19050105100506030a091e08030a060f050306071430010501030516270f 68
    0x418000c0c0c89909150b03451001030205a8024030340d10742d00c00804002640100880302d000403103500090a641400c1e203519049580da00c140c01982d90520a40900107264603545d00c603007000c840388032400082c400c402030501000e401801076694000c0d40074080c1c0c41941d10104003001480d00075a0001c00c0c040b07086d00505050024510005d406078075054650070110b42c015100780700e00307a40794078006650743d44c6050110702d0380200180d1002d80d00034a011042001400c0812880c8a8001d0b0000c000319110035600718640d040074032401d6001082840021703e000d44603401132031010b01845810224a131250000c080d03202103894100c45e05200407040c13020344002880f07004080d040d01c00104039114246000a60341e042c0090400302081440100c0c1300c00150750707000380e038108842d1250303065410702c1100300d1241e2800c2106010b6892080040002119840b03400f450380680201014000d042c24000012929074007280c05400800c04103110505445003d61111001032104820510b83d250a0410001300c030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 953067553 1250 953066303 953066333
    0x30a05060139060608010c0804050d0e0a060e1302030a090c0e06150a0207080a14010b0114041a070803042102120301050405040219060e0418121404090f0603 69
    0x102c194514405035085510b00d070044240c441a80089030300052424a01428140c5c011503869420505295402c030340010230580034074800c005450403071041101c1110440b06910010b603012010460400049020340062070147d03030081d269000f120f0601402c0003d030b03802aa120400c15540708020410300c90014041400b51000212401090401c038000401000240b40400c003000800103040300142e000300084001803048400b50744148d14107050544e4119901e0355000100c0d400c1a41794602580f02d0342003c08084c4070b041010b801d0604165034802e21400d400300310969200c00300900004030380340b90701540c4564420901402d10038000c40329945001d144100a40655010341c08080d65620b17000d0680341525000c1e0340005041c4c0e1a4000101d8104c68000a8441c1ea05040004100d5981c06110f145415006481c05d100c6500b01040e075521000c000230024120400c405c0000400c0d5120720810f40001d500c14a206082507100c078210000c03541c01801600f5120360361002001044440f0171450303c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 953068803 1250 953067553 953067587
    0xf061410030e0606011419170a0c02150c0c0a06020a09080303013605130c210b150604150e0a0806180f01060806011e08030a03050a02040506030a050601 67
    0xc260b0600c00c503640d9600e006030216040c01000e011a01c8051031400598500780802018a2405052420058008510118403c202100010000b03440c2d01e5240201ea600003699802000c074200c0d81d99110540020241c018009050104220000901c040100d0b2100f903008042c010f9880190030000340000300316074490b0910f500103000410480070049042e003418038100c4001c014400d41402c030300d050080d43c0343c41e152506142405002100c856442e41180390361007004500710035901c0300d082500100c40200c0c0f0781c40c0e540c0c122504400240c8695150b07508050f04040e03a83c00c1040d9040014080e401c10303000302c0303c0344444028101c6c03000c2c0e103d400070340050003c0d1201045d882c24074514a80300c40e8024a260003000c600a110808060b081200b0400d24400d64002c02000d82c580c030722280c039072000f03204420142d0901031588c10500c8422000e00d04070740c0054002c1d0710304400d040040d005004002c181810442d800e00c000030f415260400210321503040a0030000f40d51a1000000d4001c00d00c0700c541c804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 953070053 1250 953068803 953068811
    0x402061608041e060903170d051e0c180f0d0206040e09071a0a08071808030408010e010c1e0c060606030b030d0c022d0406082107020306040b0a0f06141003 68
    0x4130903500164200c0582e0b40098800740c100382050381700000e81c03103a640042c008a00c1e0008101c0d14884221155403c00b004648208560b2a040345c460b03402e00503000030b181440e440da060501140741c1a020501442806043e403480100d02d60005034042e0043c1d401800e900820204000041006003d030602400c0c404021403284582d6401c0c1d17401ca030040e001074000340440c8001013589140a00e24400045524088440005848962254a0381c01c0380c800c6400d42d40c240161010300301c4041c01014841400c0d6074801d0310b003251000d019007003482800c03c00300a1101c5241c070390317010030320f540a6000030300b900d030301d000c20314001c07800c00d00d490030f00c00c08446010000c03001f40c42001a6200034446003a584109290a240c00c10141d100300152009112240d005260520008001c40042010181800c66030b407550840940103841c4887c6100f095802585a0090800100060656080320b0f8101c04d005000152000d0701d032010b04201c030385641080340801e010741011402403405043c081072030b2102d03280c140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 953071303 1250 953070053 953070059
    0x120801060c120804080c010504290c031f0b0d020414060c21042102180108060a020f161b0518011a1903060306140403080f0402061608041e 61
    0xa4503002c45a101d0104025030030001c1000d011140013640c0b54411a40c00070095801c0c0303860078030f4845d200100c0b07500e41d803586000b0140844800403401845014034560281c80d40d6a8081e242c00342801c0c0b11000c2d8048495000e001c510301c0b103040c010f041603804407440143e5403810320042c00c10907d1505c1040e03214003810840c4031110350740071076514002d2103a401c1c921540711099026031803500940c0c0203201740c44c00040300142c40c010b5451703101120a009440303028255400403d2080c2c003803002d00480314650b102c500403400d20704041d401060200324281c00c01c0d0400d0004143d040d00c0304070140007a43d142d04078078807940d200b16159070701000911044078240074000039141280e864090510500074080c0401d00000d03840c498020444991112140440c80e02c4105850050003e01c0e9500059520502d0110103852003081154503600960701038440c0c600390340e2850668540014000c104a800500a01120300c0c403050000742e440002e44644441d603115801d00311840746017020b294052801c004001010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 953072553 1250 953071303 953071313
    0xb0f0a050604060803092103071b120218040c0308040b03090106050108092113170f0304240306030b01120506060d0201170a06030506070305060f010c050c04020c0703050307120801060c 81
    0x6c2d070741144c0c2038034403d20449070100100e400700ea04e104803087c54000010803004015000014604120b00e0108001c02c01c0d490703640e0501030881c0850f009420680311000c01d145011039440c3c481d8801d12407840d2108841e200d617500b580740e41081d44441c0e401c610104c2031204100d001e00481c0041c0070203280000d928584140103681d10b0820562091044106c2a07011030140c01001c1210864802c005601110a9441045041a529950f13941c1118000c2440040c00c4101c0403089400f1950309c3da481c0102d0100d4044615503401c004041d4600f030590b1442d00100103045080a03c0c0200320170300b800e0550f4081030400c18105000203240b6407044000070380c220010703a04060285400f06100d41307140c00d140e40c0c13082072800410980e040030b00b0510030103041090140c0e042e0400d61040303c041d910003002103c8880150742c02100c1c400c2c0144250400411102a802e09071702034506040107104070340000f80d803503d44a0440d4007280d01640c2c0740700242c98006d007040d0090005070060185241144400d05d80c0e4882c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 953073803 1250 953072553 953072557
    0x30105040c050f120111041505030c04060f02030d14070201230f0402060d0e06100504021c0c020106090f05010e0603030c0a0f02061207110d020d09090b06070b0f0a050604060803 78
    0x2180c2c8101603031007030804070740c503145445680e0130580d00c020059442c81c8406810300390401d11504000c170343d04920515100340310300b06407801003241040f294245401c105040c0e4020781110444c40840c4014020b41a80000c10701620469031302d8240c00806909000b02e0090030b5901d20b2400c2014101c0380b08040c00b00c9003000c24441d601040c5ea070ba1413003158a0700d1000500909c5030307414543d4440d09183c8811f40003a13022900f10300684401804c0c3d54810b680d2800d1000341d0003000110506048a9002440c64445581210000300540d01c00052001e849405020884000c0c2101000c000e94810060282141c00062140c114604030021410700383c2202c0901d83c4c5020264008000010036035100c42152208001e0320900c03001c141d10392034580fa009000900b5191b650310315891a20800020b40c20850021601950443d031507950290490300303180210700a00154143c5540101c01044800085140c0f12005401401d12a031440180d0402c1c02c034890942c6d5018140e107100d0352a04000308800880082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 953075053 1250 953073803 953073809
    0x12090f0402070c0308030c03010905070305070c030f18080606130204180b060714030c060f01050f012001051306060801020f04060c1112011d0105010b0a1d060a1d030105040c 76
    0x28050b035540c00a01d482600038995610082081d0000f0080c80b00004d44240507505a03000030200b005155210302c1c00b101560b900740d4901010a201c401b03900040b0707219520707142c182a078601f03188061210500c004022289981d10954060b0004802d100061030060b1320a400c4031041d000550a05040600da403c120040e046d01400d001d0751005c00c010b02e07132241d4050b6940ca0b600108010f0841207480303c0305850380e2048803014090300404000940c07034403441c501d06040c0c44c400344c50f44c4d2813a403082c00190f0300300e507290650004909120034209440c400034019140f14400415801150030000e00e03081b025684160400081d41c0d0040c40035100c08004803003503e003111b8807807600b502c210b20182041141c0d217038460132054101d040d15841d034425140540020140c4108010f00700042c501001d00c0c1422a031082c00340a0b0500d01c100044000789119030383e1654440031414441d025000701c81c0c002001c0e540712489150106d80c04901d1040d8482c440d0030014032001040e802801a1715165444058254240c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 953076303 1250 953075053 953075059
    0x30609030a180515030a0f0603081e0d090c030b070f0f051c051f0909081803030d0c021f0e0c010518030109150c051204020409020127030512090f 64
    0x40b008000040141401040701502010070b081480140c910981d00403144904418200300c00240000c1c51803161004a80d00008124100310034521001a9484414440952581d007404450302004240c413130b900105100d0194610028075500d42307681c145070020050400d11807007040c24200141c04c00c0c600c0152007421f1905a030740704c007458680c0501c160b1070404425541d1800d030070441d0030880403000000c401565024a100c039641e130046041600c0c0100c0c00245070610510406188100540c42d490346c40700d005007036a042030030b11000c10742110003143c4c240c001a407288036280b51381d083c081014003456007071601c1400900251240c0565444004e0b6031141042800104074050b160328202c05624a04001d00030700ca9050342d400d00d81d02d8820b80c190503082c1c051420041ca082203008608a0300104800b20600301303580d94039020000101908007069060040383c01d1203a07511070203020780002640f9840d0115601c0f909508015103841e0450140345411181040064902c0c0d944001c40240000300f2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 953077553 1250 953076303 953076317
    0x70801030611070818031b01050f0d060305151b03130f0201031b020304080c1912060216080c1c0c0b1f0803071202030a051210030210090302030c030609030a 69
    0x82c40020030500c82c9801c0500140c901154005c4600904004038511280840c00c03a141020705800092684195050060201d0401c004447ca00c80c0b46502500070151a500000383c5190359407181401d254040400180c01c080c3c9508003c20004e400344404003480c440d0300341c00d0461600060040c03640c04241d801900b02031450100108681c8650400001c0c082402d11341c0140ca05a46030103540c90b00309000d04005401981c426810a0800082000c11144041d440300b01c20346c41e02c0341c100c006e49482d00040e0b824640070000344a12031a0403200000b07191052410359030300c02c4901d00860030519540014050b0040036000481210761180c010009650402211003075601c4404010415003241c844034000d0442102d800140b036800403001e010803038010402d0141d00310f40d440c0100d0b00c80c0700721076192001c81e07014004c0c5410450420601d5601007041416030902039205c0d00021300454038030f80041c0000d00d0501007070045040138002406100016001400c5074200106000d0f101e00440e48010108045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 953078803 1250 953077553 953077571
    0x60304080304021207140102101112090a050d2a0510020a2c1e09070309150f02040816031e051c05040f0e091f060e100302090108060708010306 63
    0x144e80846140d040d02c450856026554404540051001600001d805030003104401c040050403401200c0c1341c07034604440146403070005070815080c490007401c2524144107070100400010030030003500480c400c0765181d00d00030301c450320200180041e01c0c480c885041000c07004000c0010380005180345220f0344801c1c015894440440d01190281c8005a8602d240080160204503251045d01302c000b1080c0d080e945c4144080740d191220a8146485104582003040724001444862280c0d00c4861114032801101071008140d00603802540c2d035102d4004500395000400b00b02c002c0b81088409000303034800064a40c518550307258065001d81d141d840300e501800083c070326000c000d010f200341d80380110b88540140c1d508481590080280c0c02078042c00c00f074400e417280e000c54084061900c142c030684e2480c00602c500c6100080707480d900c4154401c000c1d616501c41001240090f503502e543c912555013180f401103403500d140108001c854060307214160a81082080c8241c1c240c0c82103125040da41c118001060380c1403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 953080053 1250 953078803 953078809
    0x6070302180406030804050f120712060204030b09010b0f0103110403060f0212182b12020d0207060e011104030c0905070e040f0203060a06110717010609090b040501061406030408030402 81
    0x11121007401d50040c41c21501004003c01e90380a00103030390040e110380143d814041c041c004c1c29003401290040e958008001046a98030201c2d15a008900c2904054180759481d40c07800241c0c1c005440038603036139442d95041d0780c160407c40c8071f0109241007480c0c180410f00078610701c5c02c0c4521580c00090b000301d880d940385204411458045a10034108032020601514050f00902c1c009481000340344841e0140d100468460400100800c4041140380d011044180a4a07419a501e03055040865070554090000b8402040140701030306180c0c0c05068017050805110488500f181c0c0e29000c1801041700501091001c80c00c0326109000f507503411040040c807616240c10980d680768000141a81c05410102100083c0c030035500554060b00c4c060725440c0e4247d80b540c2b015a05a112141b0850701c9610140040201f038900760240541150450b000055042c0c840315580c0a544030840140c0c0c18200010038001041000d110340c00003040c01a05040e500d10807030000a105200180c40075011310004800b09081d55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 953081303 1250 953080053 953080087
    0x10201060b1c0b031c0914011e2015010e0f041506080105010b0c0105100303320301060f0f020a0203100203040813170f010944040f120506070302 64
    0x191004080f20b544040d0b00c40c000c00c8032010174107642e000039a10500060791181c003515801c0070040503103416a0510f2010580c0d01d54070145032071300c000c1014405074890315010039003003001d8070300241001e03101c84021078039828100316041c0c0c0552003009182c010442c0c4004044030154000b0b0f4031041021402c0035008150010705600d0304601080e5282c40000180c012100004003191182e480007802030f035403505400a9030822604c40500030070f50400c50350a40d46a003940300f00c014040780009960340c00000c00071040c15042600102c0209880d401a028290303003146207031003648140d02c01480e0074507140d40402d0302d40c0030b10011041fa054001c0003081c08c0100f0402a510150030484045034505e940303224094840002c3c046494060080030920080e940040c01124441500705402c02a0406600045140200038000d03500e8004808052080c42403690b0301c6810240b10310822582c1c4850604006100c02c0c9040c2e40f10038080c092910b4000c0005a000c504c46601c40c145040050300d035080e01e600074140b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 953082553 1250 953081303 953081321
    0x515090a1a060a23240301090921050d09030e120a0219060507170c0a05070e13021315090e010e060a05010503101806021b0606010201060b1c 62
    0x7010910141c0480103580d03a0465128903412911160741d665100280083d06100c0c1040c2c010b81083e45a407450b290500d00b0b1079104100003100c43c4d010f050a00494140181c00c02c0c0c20074401c040d158541c81c020700900f070411034500c030300007007a00000340346641002c5e01c032307204080d1900304068a8080980c04c2c0f5000340800c0e548440042c044555217200c50a403a51074014400c404c901c260f811510141e11111002c02c150181d902c50f403185450141c0b603444480e440c1000282e5051007203400c0280340074504050011821061242c001071203802d0074441030791098036000384002d034406440002400540c0d21205170160a07800c4c0303c0005100c881c854900d104422554004920172424442030000580f41507003d0315a180c04c0b001604c0203515080c80043c1a15802e00c5103a40c194800d60b80000e4191490340b26440307100401900d030701991060f555a00030f90704070300500b12008603084401c4000020512075143e005001340300801c8080d0610124800354003a68400320410b00070300041c0828110103500041071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 953083803 1250 953082553 953082563
    0x30c06060f0303020c0a08061003020f03070503160305011a062d0406170105101e0201020d09060b0f09070219020a0302091015050405091914010609061b0515090a 71
    0x200e29142d00f000f941c1d0760b4040000300c0c0100c642020000e0640070218042e4090340203074460012541c55a002c01c40194281840c550f850f00852500040d03aaa042048604038600090054503840c51170a020b42141e1511101441e0f10b400721805010f5aa11078080b40c0120304841c2e1090105242104881c0b0490707403408004966200c0002d0100d43c00740c0005c0c10894030708264458001680e01c80042c019034016450710b0344041000e0000d40c24070030300c86a440f000ca041e0940b000604226451100c54144c030181601580c90543d034040c88036407810644240b01e06603606070346044035401c14080c0250342c0e14405200e02000d01c0c084c941c0804650f1740508031002142c0040c00e84149050003148403483c4445449020071210240c80440d0109020b00c05945c01c0b520000c00ca03124503a5200340b500105a440c1140c0c07102565140444040d009682c110903010b0280750362450065424000e01416298105e128441c001c80d47d0940c550003d040001c58082184100301e810300283c4900c8217552403d6001c51300180b0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 953085053 1250 953083803 953083829
    0x40303030e0a200f0f0a0623190e010e090a32060a06020d020a0620180f04020c030702040914341508040813030308010302090a050112030c0606 63
    0x150801c03d80b014074605000c121021440030b5407040402240501444d070458201445207001c10605004090020305103100c800c1c9000d04c00c0c800d090410281c0e0102c41c0042c02040111880c00b42d055100038060203129080c04c02c0d40703c812185000480e64a40106007005440d00c074140850707185800505410b00700960002c1841c6202c0803039000007050821101030307000f039207031aa000420505c00a04400740207507940141046011546580d409441d42501c60142003051302d00b441c050700c2c5880010441d61010341c0a0b800643c1260b020044031701d040c9042a80b0070303030042c403110007020703800700031201800d60464000611403105d103007100d400308000b1090300c0300340200e500c0c074144440c1c0d051a807200680150780c940036455044041c41031000080c040c802200c1c41800300f00c1b00c40c50040c0134890b0403a0041612500b06140e1201c101c001900c29082100020aa00010021424110061a00b180b0961414401503040c403d140c00320750b60001c405805c01c4500d98501060088560010300a0300c25074000c00307 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 953086303 1250 953085053 953085083
    0x6042a06030e1c0c030809120307030c080603030c120918040c06020d03020a090501030504111906031a09040206030c091302031909050c01140d060e16080c040303030e0a 74
    0x16000304041d01408245004060703116801c3c04808038043e0360f040070303500c9551000c12141c508444102d0002c056000300c2c414082159010000b00e4069031003841c1a80e00482e42c070300c0504d0014010304011b4081c500903801405185c142400100e4104d001c5a049400d154030750042c42c0014040c03140810a580c00d10740c0000601040c4040b9406030b80a9030301503001c5070710101e12054110100d01c80c200d003000004202040030700c255842500140e411500403050600b11100b02c40c00a1041614012240c0d20281650810490190580103040c51000005a070804400c4550085020b4100042c0000c2c030074180000020014681d400a80d29800340250040c00d83c0d4100c2d40340c0000a60056a40a6440740f01450040c0d46074198011051000e07030000c090003c40d0090801580c40b1090001d00b9155818107001d000740070110342c4a03c1c0010800c2070b02c039200754140003102608038240b4584c584100583c5500304019940440100d5044036410310380054545000310902d818808280801440c6c02d032918658 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 953087553 1250 953086303 953086307
    0x5240406020a2a0306050601120f150611060c09190602011e05090c0405130b091506011103030c030c1213020901141509010507020d1b140306042a06 65
    0x50350180b0643c035803415500038190420703080d48060000928010740707030703c240005032841c0c02c4035401100c107060864014100c00702e120151141c00440703000f0303aa9200881500d040102402400801441c200310030031030003090f00c154848000504944001200103191078081d241c01c41001c1100e03428151091101d52a1100207000c0c10300043c3e0305480182c4104100100e0059104850088064400508070f110007501880050500108082980c42c1800074110100c0d07542c80789107201e500550b000c0d004101c42d03140c05000d1181c0107800d44c3d04004d4004103851426100004581d0452440d5010580b00d60f19407054504600c03840c00200c04580944080c42110032a01c001c5030741c200d10132618000682e0703c035040c524005111301c11107a44194548982e00c00c011050009088411041c500180307010b0b225000310300313604004402100c41c2604100b44021003001901e0503006040c81c801c2000e54900c00c08e0000380e903460042c0c0081c0c5001702003141881d01c203603580022aa8200851503950030565a4200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 953088803 1250 953087553 953087563
    0xf06100e27010b0c100b0105090907030b1e100804021011071203020129060406140912060f090a030c0b2e06180807030807060b030a081908100524040602 67
    0x40c10205214401d10030380c0b250211b0207903900c0082c042c1c1d1850706140340c800800000c200040d194000f81903a94010344215207a03880fa800080d40d079103d07805800703260310b024000d030522107454a008200d00c010030310005907650300511089200c0da1414201c2ca15000c07080c241001c2e40c982c031400c0c422100e040864200b68064001281e01855080c41030400e80c42c4100d00ca41c0c1019100589600100c03c0105120705130190680c5500c40104000c042e05020b991004100000000c41070006a07a100d441000500740700c0c00308042e03204503200090a0200c2c1195030140c1001040b0800038603d101400c0016010705001900c070000c808490341301402c221030b001c5e84130641c00f628040d10303002070818200314001101200c2030004a503d06401000307035602c0e640324000190050802150450344400000c5036596040004482c0580100b1815654020301c0041b501841d800c14428414498100100103000c001c05820004071502520720003080320042030680d0701c0d000c0307514605810002c04500400c03070560000d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 953090053 1250 953088803 953088817
    0xb090c030610030b0609070f031a03070b0301051003150501080a0905151803040e0c030705040f0b030a1802240903060f0906092803050d140f06100e27010b 68
    0x13240e0026100c0f4414400301500448400e4049a15030b5042400640b2951042c8040e04002d140f40c1c1c100e0880c100006c0c20b0000c01e40c442c2a0098001c0f00520071752824000b0115007140c00d017000c00c0b03483c3d0070230600039850003a4840c0a0600007044001403e8a059410840b20316a0003c01e4900400707407a0441603c1d40f0050701d0454600f0b440d00794404041b500001110107440c102c131010703c030350364400000300a41d0b840141070b030003000003e02c800500902001c00c402c01502000e165151285000c18070702c0215600f400749114280c0040c05d005026868801000e0001845034400c1075242c0342110f0080660f200e03207c0056014490041040209048245610300548513401982d45d643c0301c199140f80d69101c0c081c00003a01c0e848070400c15032245c00e144003040352540700c0d0401c581810302080c0301204071a041c0c441c5624440d130000406c5092107083c140254000303801c4071914044003000348000e002c026070009141c0900340340e24025500345540d110310a0741c03101c444030000f2550b0310795011171a144c00100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 953091303 1250 953090053 953090063
    0x12020909090105071b111219080a180b03150103060513020702130203010806011502101802011202040f17120406050d060510171b03100302010e03060c070b090c03061003 74
    0x22a01da00c80d1045090317a0712071035801c08400491035103503204000590702c44a840303244500c5141e000c0c1542094412409030228040e444650300c0b020707120401b50806040d240340d500003003030300c1c0c005202c0550103505490304a86007041500d012044040164020803030340c3c00096002c0814001c44c0318040d400c1c0c009110f041d109441102850f1800c00c0450140e000c00c0c02050615007040b0014450300704000032001d07205100c1d2044031205110320741030004443d115850038000d210900e00510955821400710850f4517501181180751515182e200107902c0b816020300f900185000540b85c400103001c100d04460121100000c0f0340d601c0e598640a003079917000000c06c05903d4103044000461b031519211400c0d40402035118440b5841c1f45420a00107144014103582c040a5032006034603949a480c40514800c50a103c081d000b000d0441c0000342450300308142152180c2d000c0c0c1d0401201c19085800d807240c4c541d00c01c03214002d0351600322250f400e20413084440c680520a2a04000300d43e0141120038040364050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 953092553 1250 953091303 953091317
    0x121209040f05100315020910090e061909150312080601080f0f06010c0303090f03020c184f0b0a0203090c0105090301060302090103061a1f1202090909010507 69
    0x140c55081aa08115003820f0803043c400000c02c042400455196080f51507444010700e410702e01c1c0f00043e00e0807074420415000540036142881000d003901310082c0c00039421600d501e1401b1220a104088481e5401410340041d00c1c0c62800001c056909205070256074802c4045481040368440141030b410100c4a5900099450700445c2c40c54038444081c9000f4510364661244547d504001918a0b00e0300b850203c0030513640e2020400403580c0c081641524503c26805000f010390b4520410030750000c800300c0c04918080300d0080c4421594000c08001002101422a550811301e01e00d100103481242ca510000d018000c11164415204484803c0340c10342c801c040112403925038000302c40803030104440c003090a40c0001099411507005001800400100a001090711507c96012501c860700c01e90007221040d1700ca82002000c2e00f204020203440d164190348450000070b031801075154103881031220720b091100b007000001200815030101c0314a000090510300850500e001c1060082c8001c4864600040032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 953093803 1250 953092553 953092571
    0x1020a08070c1203020a0905060a020703120302090906130908030907091107052d0a0602030a0c020d080412090e010b0c0c0f060f0c0c04050711060702030306060d0b12120904 76
    0x100c00e07180b02c07140c02c010b210032500410340041e40294040c24240080c0080f80c80c00040903a00d5800600d051102d03940030300401d03451881c250b5520100ca4200e20145070050155103003649030001040c0d40102c0440302d04002407000811072008008c2c03024064043c07031001003040849000014483c0803140303219000c01958003040c464603514060315000500542006031b03070342000e03c40f940b802030304030030f550000180b11009502110b10b0181d02400895416401104210801c00e4610034026010039038000b805080710601c00080903050010802070004000c14184250184506402d5010b00070305581a1403c0d40c4440742c04225801c020001c0000e0300c59103c481c010750400d4000d1141c1410080c103114202401000725070034942040d4041e085911030b21112016580e05c07402054040d14480e100ca0f40120b0310700241a0400c00000c0010301554010801c0c800542c4400c0111507030458000c100140e00d007080310009034072400d41d400460407841880d042115118003000201a40782c000c0380e0420071303421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 953095053 1250 953093803 953093807
    0x203040f0309051f030c090503060910060b0405010905060d02161104051605090f0d0818090c07050d08041e060c0216030206180a230a0b3c03010801020a0807 69
    0x4480003616480c0c007068000e8031165000c0c6c0c210b00340c030240c01e003042102c03030b0788440c0828605082100e650303405900c8a00720004613120340c420705024242082c5901c0c501801c000003e40003454500c28039000b4800050802400f52056054610b15410014040001d501e1800d101c0c0c40b800f00514a40c0c49207142c500490101c034540c55480710f0342c40190301d4080c104401001040864100c68030000d1f000384090041c540041d0b9400028001c034010701015400c22000d04007400341c0003000401e41402c0c14801c02c181d0300030460001d080c110712003440c81c201006580714680048100305032140400391544100c440030800845400c44c030b00310703401a03086030400c5425000d46519542d007444040c5d00305004100044403042420700041070f111001c0c105514050390745640301c000380c4201c00141041441e10511420700d18180220000808030750782050306281030078200c82c18981c0715009800c155a01680010583d00000700300380d14401110f51a10344a41c0d65100a6000c0c2d0303c411aa6000250b038080080c80d224 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 953096303 1250 953095053 953095069
    0x307061109150307020a0501060b040306060f03030203030402190e07080403260f0408091203040306061418091c0c210503010b090a05060c0a05060106080912030411040203040f030905 80
    0x54028100d4000541034040b401d001d50003c1d018004500440c1110804a0803d000d14001000c24100f00390782c45265062410481e407030f503084045058500003080012070f500101382d0340c110340c048528406448000d4a854000d48143c0d000a6030200c0c0c0a041000c071580240f4824801c0340251a021184d03500380c84421651681c040300e9001a4248001045811501e1003d180c0c2c054031881130107180c8025840060b00382a01403040c03000903440010180200455401210700820804041039180e580d0600061065049170055201c4001d0000010f910b41201b00844030914440800100701446404002848240d10040954060400d10401800c143c420441c0c01511710882e902e00f03086908090001450b41e01942c415984031280070000728032036940c04010551658070300c00419800c5458640241013540582c000828400f4000030040004404261400e4018441d03d000f580d80e5920300c0c0c100b98604a40c04502e2700240301004210412482d8084000118000c4d142d40a0503070340c94040250b10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 953097553 1250 953096303 953096317
    0x270901080d091a1c020d18212c280f031a040c05060d0606180501140c1006031a0a020f0405040513050105160e041103060d2303070611 59
    0x524100021520050704e89480c89400c41c000c0005850b10500214041c203890030900a0540703180c01062940c2004914981040020210100c10030103d40b142401343c1440c40d401404601c11000c880301180c030b038800b0196055002c0000b00111031403048144215016003a054490384507805920010411046040b1843c04695101417201400d03220b00300001a61000544100d0355401d100001040350b0741c801000d40a9603211640010b040d901e4070b44014030110910f074000701000000700c0c00307000341c2c0d90002b031120500540c0411941d8502503040b04616020000161001040c0ba100021041000c081107190400b0060b404410803074503601700c00d074100d00c00e544105101a40030403041245003066000039622004501c844400e0942d283c58032403c2d241c044400139598000c0e0001c611081d038001d030b0000c501c0842036400b040690744443c0e00741041c1c0300251089108100041c610b0742040004a0300f400e16900703014903080d1a86071600c180396030b0b170400f201c216066810b01c0b24a19400f81c80c00300b52140c2d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 953098803 1250 953097553 953097599
    0x5011b030f11070206090103090807050a0b100504050601020a12091214241501170403080708100501080426070c050f0904120c1b0f050f060708270901080d09 69
    0x60040451b0040d230061089000c11107100c0c0051004201041c400c2c030890041900801c042c00c880c0c60480304031010494590011441545014103100003a40c2c000381c000c940079405481e401d210800c10406a644650550140c1802881d4071030410800000008a07001c42d02c40130101c4850f1007110325100040103409504410a0b400c2c0c1c000a40000d1481e89001059801030418400140001103140c5075408200d9041c0c001c83d950f1424400c510382c0c0000d04561044194108401c9182007100080c40180064400707481150002c044004010f09114000b00924000398115a500064507124160200390b02c6500d02c51044100d495030a1f003011a07a09224950ac040c01d1744001174001c4c0b043e544481488800c0d070b40c041041c21140c0e1141a001c840ca4007404a035640320f03550601e480d040083e1042c0c01c1508900901003841a500025001c00955640c01b20102d08004100c030328840c00d1080300d9603400745542c8061164000030b041500455200c0d4000c135507642e0007019548814030000c940803441c10200d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 953100053 1250 953098803 953098807
    0x302120619021e123306090312130e0c0a0c080d060e0a09210206040b0c070803180c01020f0601092004090b010f181205011b030f11070206 61
    0xc0307031040750300400f0401c5180c1001e00401c0528035000d00c2c250044083c0c41c04a407541401e00c02203604c283e0410849181600341550082c0c0f0861001e08010411a003081c051200484c8081c80d507a0140444484241002815512032003070004000c0d08601a2041c8101d01d0000d00118500036003010840c1e40582d01d684460310740190503660b0040e284d101291030706510f035070342c0004503200e0b2290f40107601600c540c9901090b9540c0300d09018a814040480e6244a41e40e85071b40035201c1034000c145d5651064000c1c1d444c501d1990346010030406071054400041024600104000b001d2150348086200582e1450403240c0b441200c50042e41e46034940c40320300a150344410010000c02d186030700030010811502001d40c0080c90000300c142c18903000b54000700c08050322400c0a0b0410751b4824150300b02c0c41002d07d000d0b140c14214842c0c8491074040340c0070321491001c0d1030703a404083c04025000345004132814540341d1101407011900900804000701400f0002c2e007460901b40c20490f0900541d0059500285414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 953101303 1250 953100053 953100091
    0x604031b1208092109040b0103200906120702030423030a06020c07050607080d050705030c07030c0609020315060909030c0618070308070b06090a111c0204080f030403021206 76
    0x240b19207030002c0066030148241e059000340c0380c01c000492190300d00003002454455082030100f109462180340c0690404d07241c04200c030503032a2040c120f100b84000b02c4501580c2c410401000c1581381c80313852400144028040c0c144442607600000500440f00c107144000e050400700c03100341914819001c60960f1544c0b00100c803602007a140d41c010301c82c4600d0002207071241c41d914000319450b034015200582d90711a0100300750103266018060103900102da894001c0c91072811980500c2e580c02142005400c00400303040c46410000c0340d9010f8071600d50000e08580f81d90440d19242c1d5079045040f12058000e40151000c24540040001030f140c2c042d0f00980540447c1d80c82154001c0000881890a000d07481520800008204840010000a805419000400d292450510410b450041c0c09140985d14112884200c54190300a850146812940c0403141940010180002e4000c0c0c4d0407440080c00b0700502c0e2408a5400401403080720701c00d403580b81c20141400c0006032a0340007110003000d001d90301d1001c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 953102553 1250 953101303 953101307
    0x30c040209093607080c060307021c050913020304060b010f02030d05040215030903041a0711011d1306050102100507170a0204080106090b12010e07050f0f0904050604031b12 76
    0x10306401d0360707000c4100f6105608040f1041079001c0d040015600d0304030a005001c039540034004c82c0180d100c262039440c59824401d070000d5449900e40d0311038105610107500800000c1c0b14508549480d08000e00640c0d5034141410448020741c419541210f4141c41c040740100c003540903940c00341d8130210a401440c02c0c903c03004441c40240200400407a0722039021078004815484041c00780d40034849401c0110741701c40c100303091451042d00c2c95819030b01489092290100103040c02100581c460001c0ca446031400c3e0f01040c07413a10941601d40340e207501240c0106103031006003083c1d00070f0044400903403c98101e4004c5d00352403030488100b551228001043e0b40003901c448030008403095088540b134403005140c03039603c038481401c58450350005181076458003940041458145d2500300b00101c0400204200e05c0c40140030b0740c0d1400c0030700c5814041c030000708030088542d9982d9491442028068542103a515040c507005031a00381c1241c0490105080d18002c000d0b441120a0016071030342c1c081d5600390381980301002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 953103803 1250 953102553 953102581
    0x615030e101a0d020103060504050907050315010f0b0c1c12140c030402010503060d0b0f10051e19033809030301030308220309030c092009030a0b0114030c04020909 72
    0x61713041c103403640b00024903904c1d14400e4a2040750001d0141280c10304000400d810201059540031503003850b10018090000b46858200495440380e480c40d55850021228a05000250703145a134840402000e9111071038100340d5007a0700040842c820081d010050710342c0e5400c0d003000e89a55800480a200080041d4000e00046800410050110601464650718240514021204c02005803d00c20174480d050107210240303030141c0382c2101d4900c40f03040b4a2506c4100d00e40c0c80307501a489510b01a240480c11245082d0303203030246411680268101001c04100e4000c401050350396204021102002c0c079540781d220080d1801118640051803442e40380d81c40c11a9031000140242880414600c103055424031440c0d000340c0002c0c1b203a26448074107451030500c0c1c0034000f2164005010319040158526401355101c0e00c0540503000354500780e855031b40c80700c0400c0c80c24803d00001030402181e400041a40384030030440700c1e04d048048044610b00e05a80d4244001e81c0242d048050304491a90003040303064001c850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 953105053 1250 953103803 953103829
    0x71208071e0602092e03051f060207050a06030e210f0a0e09060907090303050d090b010803031603020f0301030f170307030f15050f0d060615030e101a 66
    0x1076904407014850a58140030903640341102c40b60390001d0030243d503003410b107404601444103421001c124400301c0c603204000045074a00104040c0d40d00e0010701151810704003220510031801103000c406440d4103010750f0751541da000e900d00c0746047c0320000410b28440d0050600c1c01e070031a8040c002c0301400c061022028410501d5200c03c0070390511100005603001c4001d04201c00082c0d0303c61030081260000e0064601000e0109405000c0c81820001c0d080e41192260b4102d030790500c1c0a03a03489480107694001040340c000018100c03103000c800040c48180c008055030054032180801b4840700d1003c0c50035401c0b8403c1c2c108621150f5024801000421545110042c1b424010703070401e48509103003440141c240e07004940c0c11020a50710700262080c108070384240341e11400001480b0708031a04000000340c40c80d8158605038803e81044013140c00700070443d00060020308002e0b4a00d86803852503000500900182400c0034030b02e01c107440e00740208044900404001040c8410740d100000420020f100b1950f1821b8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 953106303 1250 953105053 953105063
    0x1b06060d1202070306110a03051005060f07020102031902010c02101a01030e010e0a2405090304030f0309080f060a2d020c15010f080606031f0203060d050f1501050307120807 76
    0x30b40d0000110312580500301d4084131b0340e48007070740d03402c810f01300942241d101504903660340009170340034081c81e2548821038403901443c08a9a80f191800e20040340307907100341800c015641340b0100f562101c00307405400c500b0070080c0310703000c1d151600c0b0104d50610440e244800521b000070321038058007a2a5009a1186182601490002c1840d4050f40380c00d40c03900348540012900c003c210b0a0340d01500140074030700405282c050106000c01d090402419681e80114080981f1960355500c11404060289003c04010111002035500ca02411405180c440d030080340c229003240d0601001610a1035494030441940400c001d215409500002c01c40c4000d400050340c0900710311a0b03001c0060301d11882502640200001e41c0e1b101c07002c508003040281000c90152005000360f0010080145002c0c004908021030b0441040040c1c036562400002084582100d42c09441c40c05101040c01034503030080f400c8402440303080c61050141c2d9030b400c145580d4120600c98071402144170204000041e240b00003c1c020603000b1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 953107553 1250 953106303 953106313
    0x70503240d0503190305180703060c09050316030317010648060c0503010e040303050a091a07030501140d03140c01020a05040609050427020109090e031b06060d1202 72
    0x65840500c3c60b8041c001025030038614612418180d9814007030154885604104225040c9104501980e1100140401064103890750b0301240c40a11941e052401080000d044170002003d5101c004403c429030300003a000a980780410900c4c1e80200140300b0304803280c82d40c48084090288801910b05060300302d01c2c1c511550300300301c038000381031494100810a0618034110403091015142100403280c01c90919800d020080c8010410300740c07245015075110390542004540390303689000700d100500074240000c203e003c02d4895408200034241c6050311804464400b001140d0320385407201042c0ca8058101c5501c201d80307a55040c0003d21130400c1561407a800080c6e03904000c90154000e099801c81c8401ca030000703501050802140d40c2c003254450040800781d4040044c1d0180003540010300d002d49910781c00380200d1500c00d40440e442200744400070604140100081500c0b041130545a0340702c0701c08911210403a07460131000f0070001c40c0302c90149100500c454521241d0751303250b4060411281c40d820541c060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 953108803 1250 953107553 953107579
    0x712080306040f330510051608070f060609050a0504170c0a020904050a020a06030b0604090c0c0b0c180307080d081e3d060509060904020408010608010507050324 71
    0x500d080b0184c2d800a4500008200c1c031444584402a0001d60100b441640941a841c055641000444060304140b0510f0300c0100f1607810300660b03a00c28540b004041c010906613042c10b004056100405848501c0000e2103192140700031441030320029200601103900380c0d24030541d040306500003032500010690540e801100700b9000203401c25002c130390945d00d1f90001114002180b07032440081000d0542806d00b00594803081000c00c015010710f000e0361035415079400c450540d41d8020b041c4900c541d80e02100c840c43da440c3c580400241d903049a015100301585d02c0c2112841d40c07402181f08810380f01440000d2613482c10785042107401b55005808030008042c8100804210160b403644075108600c910b54100c42d00c1030a904402d400361000c001580304e0312203081c26501500c2e030510702d2811207507585491600c842c40c59000803603a00c0707500c8501e80c1c0944001400100c0b44010340080003140d842c20020441666000d10a607117030300c0308503a00e004040c96408501403000c512600ba107903080300a0300d4204030030b50b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 953110053 1250 953108803 953108831
    0x1c060504331206140c0313030f050f0c0706020c01030e0a060203041e060903120903080718090f0e060604230a141e010b090a09020f0c07030807050712080306040f 71
    0x74032402c003662101d40310070300b1100c81e1001c8244244c20070440c2d210286107161200c030100203c000c0305c030020108403964280c148414404c4003951118103190f50386950300d50701c0c050324965840c841d10505001d4011103181100641c00b0340308980c03528903494080c103041d1803540cbd200c100941c8000c2084038102c0805241c4070b40f08580d481189050344c8103001c00603000115040150040401068149401c1c0c282003400000030b074082581900710b07030942800d45010100160f21280110700381c020f5461189040705207942000c1c40d4101c41300e0128444160780301c07070303c6000c1800285c2d482030440c140f400307005111282200c0c1c6010700d0968490014600041e4031080c41040e01c04604095032840c45207011151400082180c0030032280c01802402d0356140b805240c135010411a64682c4210291694041022010070050307208842c2210784860035500002e480c4d1a0000c603540003100150f81d00d2140c404081001c1da201240601e00b0754001070000e08595035681040090011401c2001e9110f8803400741c0617a1388 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 953111303 1250 953110053 953110079
    0x204080102040e100b16120c02151b0105090616090e042f0310200307050c070b090607111c0602090f060921121c06050433 54
    0x484600c801c072403070074101000f84c00d00c0401d8100c01d210410800060400e19840c61510000945c0000e00c03481d80c8142c503005a6080850203800f0750040300e403000301400521800004c1002c007946030741e03104004540703203085400c07150103d610165603030020010805c51000c00400d5100c800542c5840000c141e00c2d4051401d0465058078110f40c98528221491641d54107202c0400d0b2070043c01d035500f6600c032402e50001c1e544240f071040c00c0000da6030b1031001182034907000e0000c9810406696450b0354a0034244402891076018203075008403400340000105401c42104101e0740d0b8100024189400c040c0d031900c07407480b00804000140c0d07100c40200c0c4000c505c170a01c038442141700740c040e420040c4c6070310b852024401c5404007481c9083c03140c8410030001d502c55940b50200c88100c900d2174080d000001c100403103149044030100381c0c0c1d11074450208803c1400c7c54a400041c5010031060b40070b0266903650020300080d58200c107070089a8200c041c070340035035141c6982e0f0612826240355228080b06a034407201040d40d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 953112553 1250 953111303 953111309
    0x402060c010608070f1202010c0303051b0f0a02010507022113090e0a050f0c1c08160605010311010c3f0806191d09030d0e060603100c0e1201020408010204 68
    0x90380185504216108071741d14298010445c82942c0d61001d002e0342d00092420303582100080500d980c460101f000069184204915020040032107552546034141440385074000303403180001076080c08006800d940c40818201129100000c840c4030103940341c0540b814540081460001d008003007030000580344228050310912030645000b815810000e400c0c568108202440b000c001c03603001c000200c80e1a01c408181c1c0ea8001c502c0810402400102d00c1c109d90580710342c09004401c4101c1e01c1c41c031414000243d2007981202c0c810702d10240e0300c130110360056406002e2040e01400002c0010042d82c100d402920303035203030080504640c17415903003030107550381241d010354850110020b500c0004002d44e50908040030070080318610350240354070349002940b0341c510b2401024160400c0409000c43c041040030410385041610582090192500c11204540c1d611021142203101e8030540d0916600c1c1c118034841c42080d01860360f0b070030580300c80300c406100d01200c810703014a66543d802c1000040d00b68080c8058405 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 953113803 1250 953112553 953112569
    0x7030212181527060901031a061b15060f040903140c2a2103072f100e100e030d050a0207090e15180105010609060f0c020f01080402060c0106 62
    0x903030f4259414402c3c0900088081d042c0d03044140c8210310607030b8a01c41603841c508024a00803642c005000707060300301059150000c0b40c0101c00440c0d207100356400b04006465805500013212a076900c81060300c240c0c62000e540c0d854000c240101541c4c000e00b030681080c1911030283c1005002002c100f8002d4840341d001c102d004005400002d220f00007200d644039208420585914a014400c0700080000c0c400c1c0000d81e202c401050394141001003031681803050310011500044211500b040d00100b100c0b820102c0c044040d881c1801d4204d030000e920f0011400c00c1001c601d6510728020b241100d06014555510f83c20000078040c00d05400011a6000c0040000ca00c5055590341d80340c4a504074003074a48071503508001c60050400162001112001070a000304584440048070b03203072180c4400400340c54010b1200c141c15400d240c00400c0345500550210121640b5585090594000c40002c59031940f03105802035104a000c16402a03940c42440c0c003c0e0424001810245405500f070740e09804c40303e01da400010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 953115053 1250 953113803 953113807
    0x11281b180c0e06030c03091906060f0b1314031009050a02040e030f0f0901090306020705010501061805090a0e03190c1101090e0f150d0620070302121815 67
    0x1a061030300e0299620340c440358101581c080e050500015054000101280940708010000411009003001002c01e80e404042c42e4800702c01035418100301410090240d404000c8039207000155403031144040301c1000d41030498448441e8204008001142501050345c0d501d031140c03800340d0325502550b01c41e03280f2940c440d0000b8504050f992044c031040e601da01170b2640b01c6e0f41060040d500655031090845001059080440741e0b1006400010385540074250400350101d44007040f44001c001055020314140e070295111841200c0040c0581d1881100318050660007192403404514031900c0e5800c04040302c0b480d1420b42e4107040f00c82640c11211038082c802080040c10807000c4405102064040c00401d40080c03030200b520750300703041c00b5885801024000080720321101c00022915419011080c41e0a20001d00700c0c900030800713042201c05042c0564440c070201d5582020300803000854400c4170b813060b034150007826500e245100824429048030300604c80c0008843ca190301c580c3c0d515203844841e5014040c05503 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 953116303 1250 953115053 953115089
    0x3030f04090e07030f0803070201090c060201090b0a0506100503150d0b0708090105040b0f1009050a022203020a06080a060b0a1e0c0b0114011e02070611281b 69
    0x900360785034480b580e1040e4022450034000309240504038581d0b20b0300819401c1d03807510750000407401480d444070050304c24820903c010424039419088030f040740740144061400ca85886610000700c41d81030380d04c0d562100300302c07000501c607901540146a010300039140c18003030b00c0c109202040b02256000000c486110840c01005000d9420801b81e07900200078000802040ca010790350080c210b01d028000c0c05082403090001a00c000c1089910b00c0540817500c414803084c200740c512503000c1c1d080120402c11008680c1942c6480010700c042030380840303400911303070303148140343c42001c1d240a0006006d03140c1c0c0d9910368070086116095480102813034030603584e9200380c4101c41440c903054581e0030800001044404120303100845c03a9090b529056903500c14200171b00c032116000684440c0822003c0700149040b410079603410715001304100040303074540d403550300e590b1b0103035141d494542c3c4080e03200d00c00001d0858500c060024141803440c9906108600103100030a41c0e40a400380d41d055035100341050504130301c0300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 953117553 1250 953116303 953116319
    0x804050330040e04080903250807170616020a120507060606081003151d01060501020d02030406050a0507062d0f11030a1a10080a050709080a0201110c03030f04 70
    0x4101c8003060540718504042c1040d030b00056042001e800545013050105000c3c0035541c05001d100110f141483d090010b110950b1245051203c041c82490301d035005080c000554400e000d58100014440000600480c0d40d4589001c5da8444401442a04501c21103038902c000500c0002074181c6403406480c1c0d90380301d0003280350a00556465402600c00c001800d000c0c0040101c4480e0f02500b40c03640200c1102091f24200c140782d0060840b002c150313100e05000c06c000c0c640300c2010350041094500a03400d0350703104889110305aa40e84520302c1a80c0000350b0803c12492054411405800710920403080441c0d01e442d14060034140c0401b18098400080c16a002035100c81002d10801c01039010015050051042c100c4810348540002002c1130b5105441d0318051061550b081c0b000000a44020440500e20703251400045c40e6402c100c80c0c1961191409011800260143d4560300031594600d0060144040544c01100c03000d80340d03104883d09205a050f001600c4c0e40c1400a0100b030281d121107251610302d41105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 953118803 1250 953117553 953117623
    0x12030905060115050a0804060f15080c15032404061815060f210504030f0809010902090126010e030c011404120c0c090c050a03140c090d08040503 64
    0x103c09100009400c1060500fa0880281d6004030b5203410b0007051980d0324101940075000c50070307842c0d00781840c000700040040d10b0321507540e0940e07074580100d40400e03200c04d00b842801c400c217098000c2c0c604414800940324500301552076800c031060191301c02080f60392001103030a490182d00880c148003850a910042901c0510650514607500318030100454031700280907058401d4221480c040017407090051050048580e0746d14424000001c0c100309514050a00a18210f40800031000040c00d000200e2101d28050190250564000303004208a0f4070380701da1000d140390510051040d1a50403883d401151307200f1312030f80c80034018800243d41d41e081812055400c4904c02c002d4840d44114603410b10010400070900190482030310f05290f84010000d090000007031103641d110721001401c00342440001d0382d00c0009407103800066101800001551108140340c041c0c00c488200444c10203111000c2a03181c07001401c624a03000b4103001d03140680704c10200e4100002d48120b04486034582080355135203061125 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 953120053 1250 953118803 953118809
    0xf0412020705010f030c0905120c09071706010e010c0b041119030c060503071b20060304110405060d02031603052a040221040609050c06040513020c0109120309050601 73
    0x10150603103904041c0041e113401c0f0800084410503690309030114825003d03140882c090200103007d252542d1180340c2d0aa0391f42864080180500010700108002600880c00f42c503903d0040301a10701103640f96001119090050194141000328484d0124041500110168080c1e0f0203500c9004d0090000802e01101010a18540d40900e850300000c001146c1400c211009403a09441e009641c2d84440a044410110038030015150010b100e14410800800a0401410f805411810a08182520204174040c0000c81c0c0c042d203030010030f01403160540b60560083d68000c0c0e00030304000000c801600460b00c1c0000c035003080e0440c46030380307a42842404420070011310040c00394074030640203901f142d051060010010b1591400345401090041d001021030704100c00011520242500c20f10b080c1c100343c0007070812104c0c182d820b4082d188514170740d410039000300c42c16614042d2030048034408000c070880c02517201c410b051509550301c034520400148040e114001a0f4401e0f50089026106410424180302042e8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 953121303 1250 953120053 953120057
    0xd08070507050318182505090904061e0f14090607021f1e09020f0102011112090109020405090319030c08010303111e0d1202070c05120c03060f0412 65
    0x4001030002038400011519030320344050303134070a2010450340403d0409030b178060010103c0001208100c107035070b120704041103400c6030041c084000c4504003005841c81d100740b69400d074120405600140204240f07420030941d00c0e00d40000507082c8001028500101c80960708841c0c1665290030054180d2150354000641000c1c440740a01041d0810103000b81d9510805c03404007000512521000a6511142c2d208648a424003d204a907602c13001d800380c4010000050220b110f004103031a401c03555441481303006006240035003450326000c0000d405001150b03000342011015900e40301d0100050b12140a15802000d011b0001c58840c8107405005032203180d82840c503410180742c8030510310010390041080d07044903058285a003a0101085810381000958444190507140894102031400000103030040b00c907902c1d940301ca000103a242d008109130f10406e20040d243c28141e590500c42454414641c2d80142401c4003200c04018900e00800c0c00c0603401c8403e8106056075000304024010340c800c0c1311350740c100d0324 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 953122553 1250 953121303 953121307
    0x80105060f03150a1e0c022a012007030309180c0804080906070b01030506010504060801060807032d030503040618150203070c05070305010504050712051221090d080705 74
    0x2c030755036002907a039901d62070580e200890034a1407940e10011024182c2c4c144050124803080303c180c0a03265404c0c2a10041c812920b1000d028a0690540d5016140204c400b4082208140044400200d4100500609040c02c81111005401007049030021481ba0319164030152800300001d4170f000c03c010034680e40e10308100e5000080c59000c4445580700350301c03002d002d4950000d0703404140c007401800c0000704003031f22090020050100c00a265030494204441c240010b40d10b401d022402c2c0c8929109800540d1302c144d100b4000a40140c1c9481c1c0007118000b1400b02c0503c2c0e0030144401400445016008240004140000c1c0003d41c024643c244050800d4034940040f5a9104005044a08850042164003101145c2800e03c80c0d5030b40e4903015041011501c00c55120b00703080e4020401910115170910555138001001d60184003014801ca41100241c211940e0150041c503c9500c1425404824070303da50800b84001602400d46d405540782100030b0407900072210f0080d1600c50068030329400d100d01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 953123803 1250 953122553 953122579
    0x607450503060105011701051c0f140f0109050a17190305041b030f11030c0d29070504030f08130b090f041a0f0d02040e0609010510031a2e08010506 65
    0x210041b46044601c10354044680200c84030001101800040008000703190560f2400180021081d451050360058429034013030310064400142206c1d10810700600ca0b42001100f1000b01e265110301002690100503080d143c0340c50011802c0b6541d03140d0314403d0209550b42d0900051021107001c640864801c03050007030004d030a5480e0240140801071008003889054010000152070500123038082d41405002602030881614040c030440c1d032046441e0300007a140005220030581d044c40880e0103802503440303e03031070641140c441c1401610301000c29580d086040203c2d813080004411104004c000b0340482c0e54481c9003500c00c000c0c1d0032400b901101d10442c1050706540d6281d0360f012508a490741c2c111102e0410003040000304005401c107401c080d502c14508081c402d690721002c51264820131003140204a240d0f42c01d06401100d8030240005004807100c030501042e50146007907a03d400c580301c80200341c0c60051015005014241d10140043c3c187c0301c1d1f21040010000900426402200444806108800e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 953125053 1250 953123803 953123837
    0x1120c060305220609020306011202090f07083909120111160f05101b020a03170405150901150b030108100209060708041202090108060745050306010501 67
    0x1800e0f801400035819011007100410400798003000a456018055803086d40c2c6d6800110400040140280e010341129400039000c3c0007c04a410702c2001d903034403121005e8482d11184030440222801c981d9206c80140a0300b4440015006800141e08070005407070340d04c0b4117180911403520f0040d64504460707810015010910035054095900c41070b060b541d2480c0496245c103052054240c031600c003402c98040d03105090f5149590344c0001e500a90a8074121070210300356841244c0c2c0b007454800c041c00044404001d80e00c50010403a460742c01034040e00c02c0740d9885032448d05032803104805271402440e030b0799908218640040e12906010060410462503811580341882454507042c8101e03807c44a00c1e800945071886640b40d1041d122255004480c864807251a54024502c0080c200c030103a12a902d0803000040c20080014203a20881b26540c6078403800c04070340703200324050300300ca1040a45079070302d1503580f1031448501c51819504003a620411000519000c1130504142c07060f000217040200c9180c8144c3c1c044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 953126303 1250 953125053 953125081
    0x30d0b01020f0c06090a0308040e091204060f0503180d1701090e1f1401060e04270b0705040515030f010e0103021012060504060e04051e0705090c07060501120c060305 73
    0x11050b04d11030307620390b9480700040b003070030345900003c02c0c0d56401308020904150840400d0b1007054030074201c0320116030000e580003450086c2d20401001840160301d14680034440c2d4095908070240c2d40c0702040040700806464285a0100e40c42c0c07002804110f00031881c0101d07403a22a004200402040258100540304a80c5039428969154000c3c0126041030f032176030706160310110044007000400c10040d41c680e28010400c4032002e010503c0b4a040c164002c54140003403d040740e250f82c48031060170544a0b20303071307035043c2c1d0000003480c4006001003400b0009950300d80d0514504000180389441d50341c1c0c82c1110074080725036410b8101464014103a0014001a1102404210310841c21300b0501e8014227070105003000307041030b070b0482a002424070700b00144101e00f13403814030b00a6202d0000e5520101ca80d00e11a11000c40402c00c980305588503a00401c0036050007000346400242a284092034071180b0380f50071040e0b4100382e1140c01c1039162040c4420a00006544481c0980740034a01841182000089d0140743d07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 953127553 1250 953126303 953126323
    0x405010512030a180e01030c180203221b0b04030b15010203090607050f0d091d15040c020c0411072a060305070c1a0108010e280309080f030d0b01020f 66
    0x8404c40c0c1c0a05400b030000380302982d00400510304945c0d003e685038600200c041c1114400c0c40d00010340c44140e4481d0104600036a0300c00c2e00315031426040940c04050030a204a490803041e541071200c00b04984c00c4110402000d400341c125404403981c0c542c5549804481488014002e10025107c200b8581c11607a001c4100c60b07402404550580d03c600c0c0508110f07080110740c44180300148204484160402c2ccc101180310700f1150880c5130f504100d12402c085d44600d020407526500c034600f4020043c8040d01c0e1940c44003030650382a1040710014a0168042021186101c44550300001d000c52103100b00040c1d07940018000d807441d90131600d43c803240c1ca0b280b02c03011494000c003c2415243c1002510b014403400303d80c00010340042d00404c1d07900720f416165501170400c4c01100000d50801194a1541c04006905416460051115140c0f505c19012000801031a55003c030100030214a0005241d9070401c5500302e840c00034405183d071003142070905422103409401d20750540d0040d003d00309484402040c19004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 953128803 1250 953127553 953127557
    0x402120a0b150309101d0d0f030e06090a061503030c0b070e090a0c0f090f1802090a0f0e010504090f02010f0e180f01080a05061303030b0904110405010512030a 70
    0x5594814001480d08049400e021840100c084104194408002410500340b45e51080c100a4002c100090001c8141d91504a14081e84003094680ba024859a180d0b040100946800511190300300c824074107080c02600c0f010107d070b0007400c42005220040c812156000121108620b400c0c1c55558081d2004010b00780c0a42484140c00015102c240910303800000c0c1c001c0203040301440c0c5070075403541c80181201161708001503d49050f0300c1259014144100a80d684024201c49041ca4240c1240e59051540a00300c1416000d1001900540b140d00c95900604042007045180398241114480210016404140b18a04010305140071466081007144550b0702842c01e01101888480150b80804244030165001100e03014080b80041101c1003460080340c1c5030340000d1441e60384003406c940e14064580c014140d60490b0f030200340d40d9081b4680b8a810131f0301c282000f0580d1100391000424102007103a081d500c2c0f1425004038010780c070301445807038007511045503292007240d819262a82d030b134000c401000f41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 953130053 1250 953128803 953128811
    0x70509031005070804060b120c0409020f090103033f0203102c010e0c04060c030e19050306100303050a03020d0902040c260609041e0c230402120a 64
    0x40392001d001c0080c41c001032000500c028100048000c100f650b007240c0c140c0c0d50310b2070414210054503061075000900f881400060136004220301c108002805008022a448240c00d007120303880740c5440100071b000b14041d840c0c0020102c40c400e003554001d01442080640c3d400118042904502d03550581115440007140c0140c0b01d03a1030204009a0500d02d03005080c55035034880499403600c94940545400070f60098559001ea41c0c2ca41d4201e0700e4240035200c2402e821b200344401d221091203101c000450368041c2c60441e004d0384211001c504c050fa182003412600519102c01401103040c1081140e4000f03c8640804520f00d1071614000d0950181e082d00008050300002d0310540c1303126541100040300d400401c100071600c51524040c1020215440c03c042c6a0700d040311081891300e400790a68411480500141690380d15980e82010242100381107046190340015604086411a0388840250aa00d900c0c482002e10502c0422022100c02d010a40300e0382c010019246080c020320004d581020108070041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 953131303 1250 953130053 953130067
    0x60907030807080a0203090306010b041712071e120c02011709100c02010b060f0c070506030c0901080c0c190308011215020304030519170c0412110f041e060f0e0705 72
    0xc0c203510031f60156650500c207000000c10390010b440c004200311507603c48490710540424850540700e04100704401e000f19418014800490980000e05803d6144290302c08440341e0303150f44280c045403086650000081c402040913045503001186800f180000d100d030080107240100d5034a5440041c0c5400414440c3c80b500c1c0b422085000350802d00d890070004080c15162038150941ca46140c20140744042c0520440000044609022003224026a41e1407034403464102110015a44660003a21007011102c0c100f00080300e00c102800340c440c00901600103049444051b0074000c0071882c042e00004184a840249a00018129860040320b05982c4d54056141c3d42d950505440398041c0403003a01d51522011506520180c0c0f00c400d000030b1951203080c3c22459254024400d01c18003e038010a03c0640400024601003035000980d5042508000d160003107550740741c4081805d0701d500480c03d504401010184000f011154000e0002420b027031148841d155191001500d1a6030b4050710110500c82c1c001014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 953132553 1250 953131303 953131307
    0x4110f120f01150e030f0d03020711010801030512070c12060c1d0a05040e0f010507080702060a0c080c1e0d0911030105070207030206070c0905190f0c0f0e0406080a06050702060907030807080a 84
    0x81e10b002c6d00c004141c070002c1d012600302401039880032100711040f8011160710310075580550346450517030360024010f2807048041011845c2035030010105860341071203014005400141061a4128103208982c0400c455441c070001a025a40041b410401d850110381a20095214440000c0407541d0465000c0703006032540790700c00e003403810f100c405440341d50810003008403160704050b001c3e00070358590f821201240c0c0c81012450407103244560a400080e0040045000d0912504c05001800c00982c5003c102c4a00c8c100350a21782c3e07000705c00004400b500d54100e00207001036042d4450304e280c4260700920407898001c000039200d044a0000911454000c50440e0600070784900d9000075008400b020042c4d41419508500580342084a03412402c0c18410301e881715041d540512642038440d80c03101070240103c0d01c8261034407844180ca00750010340d0340000040c8044100702804895001d0754000545042140b0000e007030500080214405a02040c1d0410018100804588186400030380c0315481d14414241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 953133803 1250 953132553 953132563
    0x6030f0501290c01090303020c0607051306030c0e0d030f14070c0509190501030c05090105060c0c06090315040b0708160e01080c2101081606050d0b04110f120f01150e03 74
    0x1103c035600c2d143c0e4400416415900806013400c1c41c0007140e07003c0d034400070204c450307100d681e02c0c20b03d080540d0b040800c14140203400040c0d40c1034050600c1d4140310380002c045500803070903410903070000300000c000c240815002201a1102142100c8551525800ba2a40000740d0081d20910f0b020b6070031080081c400c00744110141d00d10035506001480a565a42054080e880c503501900c3c0c440d21082d0000181e40c6000c204407003201c200c0101800d80ca0421008100a41d00038041d0140c0601508101c8011b0920500c0e1a61099125902c00409801d100c030001380003100050100c06041a03841c9603010840c0c00042011071360f0801d1800002d155151a071000311030140e000324038071984507412101044120f48a030a07050f07441402c00c4486c54581141d036840c0342c40d014480e820204e601040103105002c0d598211010400d400b0340f01140c80924103460001c280d00020392960070100100b80300b8003115544072144c4c1c00c8207000302400208c0d4185440300521900041c4900c0a110500030f9a0005440902c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 953135053 1250 953133803 953133817
    0x10e030a260f030103151b1d0301090602040e06010302090a031e0b040b04141b09090a0c0609080d0f17040c0b0412030e0a0f030b1806010f06030f050129 67
    0x24460302c4210794400c00300203800a00085601c249031103a4205060807502c40c1c4850700000c480b00c039510200141082e106401114400f560100c2c003901d41d81165202405000001032280d440161307603516000d0741c40081c40740070340b1050426004002000c00c5558914081040e08d07008000c01c140e50803545070f2558451016030f40201034010326070420061241c1070380d00070710481c01400c0700c2c07600314000c1c2d141544691004501c880f005080901e604218282400c1c2c02e039011448000700c9419000340c2e25110700c1022180d0216000170f420100c20b00c9032076418040c4544600355810303c0c5640d40d041400150a01c3e241220710402e480701100000e00380892280010b006003c600441076440ea20b880306480c40c4102103006a0104080145a500c0c0307041454092003101c0100c092142c181d42035984074440c040c00036040c5101e0340750000c0c01a2001c00207100041c02002c4517003200d080580b611001134182c030380039480182401e103094010045103241a80380c00001c8600e540c030801d1000c1c0d88035a00d0705405691 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 953136303 1250 953135053 953135123
    0x30f0e15030106031404050303011404091e02030d0c0b0622050702010204090e070b040501080405070312051201080316080901140331030e060a0c05060f0a0605010e030a 74
    0x840c0c440c15020300d000041d8140e030716650301030105c01050041410f10b4041a00c00604070707841000100046110301441c00c0744c440c001040429080801d0710ae03c3c00c0300c01c141144040c0e10710881c8110b41145001c0081c3e42546056050910751031449484d001401d1000500207402800c0c0c0011543c9800c480c560600560400300c1c90400140c02d007840e00900075005401019541c2d40b82c00ca4000740202c0c00130303072801211403500e80d06140600348001150319140c054011252449602000310018030300f40314100c014001d5070360b0262200012040b00c205000180d0259042d40c004110304d044500fa40c0090b10252900402c580f03681e1000706004032402d8540c4c40044d2060440401404174400746004c5110050110165148105208030b00b003002c6003411b40360082c04a28042481246420304a010703014000060410980b94075903921010305001048405103070500100b820070500360614806e070800b60400380b9000103c901c203880441c0c0d030b969281d400505031141540005500c0807240020010480b03041e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 953137553 1250 953136303 953136319
    0xa060b1309120207090603021e010302040506040308030402012c09190e032101121b05060301082b0f08100807170613020901180e0d09030b010b0c0a030f0e 68
    0x14100040200c902c0345584005004001e40002c400c40e0074014507080d25002403c420b0110040c0c0c2601c0100043c416111b41819001e20000402d542d401018000079070250b100c00d9981d151900c00101020801070701551800f541c5900d4070324110003501212615039096640c100d00d074840d504090b40d84404c09101c05105030a06e1740e000300025002c4003504841044048596800040506143c5014024051003649a011941074808180b010100046e1102d00350004500720380c84038045012580242c101100540c0442070b110000004501a20f030701c1c02040b00d025101880001d00105001c2540401004220640c1c000c500601011100344009007400f10845103060354441078920021031021010725640210030015100440c2d80030392118aa50080070070149a00b00500300582c0941c030070f004100c095444103905506c0c3c4080110300d010302e0060b2142c50403949145424803a2030340580020800c24804e105050f100d080004202c3c60b02a8581040100c0b0400302d48102c0c1e440380d1001c000d40d8858a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 953138803 1250 953137553 953137571
    0x2010c080a0903030e18061c1208070e04060305030d020f0904230a02040f0909050c0306150f0f2112130906091e110409140709060c050a060b13 63
    0x4640b9800440b03100e40c03591070b50340042008000400d5010074104104201510000fa11807034202d100c180024107140280c40c0800f241e8a40180544014140c540803c0c0110207000031107070444040c44083c42c0c115400c0c82414107540e5026124018090032480701600814a07400e050001c0041d18a403103c041c0c000c0155402c02805540403882a2505c008680400008500401180d0080f103059450000da282c040f1450050500300604042c0402d440340d018800085a080d501072141c2e80c01540d0f1000c54130200000203041007032400085100034411129010101e4071a02c69210340c080c2405541c040b90340318211040e0541c1020b1f4440c41d0f00524644c001248498030300e0401a001c1074498210302044016140e401c0e50084405a500c407152034502280d84201c4d8484540020303629880d2107044500382507444a00700280e0743e000e112800b184080404002c1c0e61036004180000522083c50f000c000444143c031382d6500ca00d004a00030b0705090310740c42c03140e0071511030621280814004010811140e17034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 953140053 1250 953138803 953138807
    0xf040b03091b0904050c061c020c100c02030a200703050304120507090e0c21101b020a03050409050a0617030a020f0609030f0d06030f080315042702010c080a 69
    0x101c0d82c1e12140c507419201d41862000e0602c00c0d5aa40b0481d0700100402110031900c0800a003500300708070100c41d00103940d00c080307207a40c0d85001810211008400801107600580c0702c500503181c031420388000b154401d0003600b0520b988a0741071120f07600040340608040821589060410201d40c00291244c03100050000340b00710220f07201a0241e0203102559951511156480240c0c3c4981c01d41110a602c1840c10038550724040e10700071300052125400c245120804034845040c44401c500020f051a81c0f40c2c0d58160311051018a01612142c910140640c50340c3d81ea4058410b001e2030007211002d40d954000908052810381c0304a0203820761000e40103500011958150b6130398850140100180628800100116400140b036805405000007450034000203c0903004141c00c440c00380641e0685a00c3c001020035031100c0d81c030102d18012a40d85560349040340d0903109185541160a0140b840c0213240e16581c1c0c50a108020050885400d5040d21056800100c2d90217181100180000324000b4540c0b0b2096 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 953141303 1250 953140053 953140063
    0x40902030304090915060b04060915030b100c020a1e1e080709020405030d090e13020307031722060f081504050907321005040b07031718120f040b0309 66
    0x35103000c2801b000303840344a110254042d6205820100340041c0c0c0c00c0c40b4280900a0700d045010413894002210441180010446240c4150200c04503200100d0202542481c1024001410501c4e0a01d0702c086000114451401d0f030a00c140d100340a020701c4000148060920510700604103030081f103119907129043c820081d440f611a651082c40344200203058180184141000c4442e42c0b0980000c66480d0907680418071030416040340c0c180155074010000441034080743c0783d01040c00070701c83d4440382910b005c111180c00f02300e031030344071061401e40802c07002e0b034002204012548070380307080304072a02c8000c040c001070f4503c101030701d0b402820b010400440050000e16074044400019021076034003006d60212581602e41c1004501882510240c22118101300780c10201002032441c25910705692401b030400150003000c0118001150014410209030092101c180c10283c004d4000d078a5003201c0030413590304e141c01c2515409140000c50072244408005064400424010302d90035541e01d04070803102d0700c40c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 953142553 1250 953141303 953141333
    0x1530070501030c0305060a18020c01020d02030a1d0c040f140a0c0311070b01170a0f0501150e0c180604081f0c0c0803010902031906031208010b03090c0409020303040909 74
    0x103443c0c4809031000354403030b009460107140080c001d00f24490921700d900352800070b00040d07200c80c10703020002010307616400d10080c0418500c1c000016128200240042e080c0c9000c1842a501840510500c0714071440102e02d84281c00b004070350006402c0141464040a44200c2000d01e0320303000e00000b000790603007035500000076030403059400700100007640e4003101041c05021310161807240740b0001405038040390142100c404502e941200c00001c8070342d44811640800c842c2c1142c441e5103c40036264120041c0a09401405005241d0300d990301c0d18583c400014011258030004d01e0800180080d216100c1c00200c41c0501004c00a981800e0f40216007810f00606604600c204c1901d0207015114041c4610400170006910104540c03540e40707040c00000c040d401c00b40c40020340718403040302c1c26441a2140708202c0198813800404600301d602d420043c10b20f46050303205480300a0f00300704200c10303500302240c6003000c02021240002d4038801c600200345140100d41080f074041340382c02e0041e03080c46500c1100c5255 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 953143803 1250 953142553 953142557
    0x10030c06050928170c060307111b06090103020306450112020108100513050403020f06060307050409030509060304051c031a010c1a0f07171530070501 66
    0x40e0034000010b0591003514226000d800c80b81c0700300c00d00c110001201d4004c080c00004003110190b40e450710020b55154000d40d1148003203034100c4450301071408180a0594035600641025106001d22808640300f441181607040c1010341c0000051544d56030384e4232500e01c020384400c901c08818038410b01c1c0844450200640594500010820410803e00d00c0d0340c1810798440308100440e4091990041d1114540500000724420103102e021a0350385030b4116000e81c640c29141c1c04655420036040180c200721060400c0e200b40c1d000041040741c142c600194140490f84d040e2800a80c80741340e401c0845150142050480d0301c000000140003e1100000d164505821516050b040e8410004400e4088440400e0329566280d444440d00c03015600649900140038010242d1003072403006407910300300c600c8003101c0e503450104c403001c240242c0c540c0c0000c401005085a130703484021801c10040909181303103000c09a80c498007103900e01d007805440c00780ba007408860303d2a00d01c16000444000823078440800d4022140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 953145053 1250 953143803 953143819
    0xc0105040b0711011e090c090c03270c0e09030c060a020702011106070c061d01020c010504060b04090c0b0c0a020a0807060807030504081b030415120e1c030510030c060509 75
    0x3c0010b040c400d1256588007615102144660002810050a07a5407002c1d00c2c2c10048901c0020417640758010110742c4034042e1b800017103c0407007050310456040c4000e8254000c0d03408201e4400041d04912605054800e8041d00080c0342c1d4883c074005143d440384e4942c1c40301a00802003800001c0069070081d001c864400d807103401c8007201000041da6688401c88206000810381d1718510046030b8103a1104005840d4060b10b0180c0c11184c2409509903840408100f003169555130410081c49000d1184421300e200488051182805a0311070111446060140d51081000000e0301030b4000070400c42d121f541903016003142c0a29a13110740d5280c4581551283c0300100d40004000303049203100b80320701881282c0c01901c05041c00c4241c4403401500080d1040804117200400001c01c10041c2040d10b4214020076a90307100fa20840c0d03040701c0e070503124017150b0583c4603840f0b2101c1c0110280c10000801e038082d41441c00280c0c0780d841081c06581ca504550018043d1002400040f41803944180200034240c020b4a183c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 953146303 1250 953145053 953145077
    0x20c1306050d0b0105042304030f0e061210080105011211210d03110a0801090c020709051006021212220206040b19020f1e12040e0103170c030f0f0c0105040b07 70
    0x80501c0c1c5200d00a0200b1f032060800050020703001d80c0c0c12a02003001c1e03192003c3c079251044045070050f402080040c400c12600820429401b26440701540a042494000d2080b545840e4022203d0790030041c2c02840314a84110507070031601e07601d4400c2254245d200340031a041d0740c008030154403100100030b00e80029040051038040341405600711900154070366207654440e03182501c3e0000800000d00d04034118003d94800241c2d668071400b80900456800103612103641c070303140010380b8109001c50540714131741e4188500032007107040c07040703095000400d01c000503510f04901c2401c804250300580f000750b000d0000720300480c58801314006400010700c501446a1003d0b42000300b60f0b500c191441512156600c1a4903011809000311704c802615090107084a984440440310040d003500960854920300782080010802c4c458010b0380075000309030724a02036188c080d5840156440703103d400380d130f4602c007030000800c01803d9801404440310440007030001c0200b0b080615124103090010354014001030383c011910 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 953147553 1250 953146303 953146331
    0x706020705210a06090506012c011a040f06050d0522110d020a0305010b150a1407020f1320040602070e07031d06011505030106020c1306050d0b010504 66
    0x580207588000b001e5209600e42400c00000710304044002c00e00500942c402140001c1c00c60144040c1c03940302c0c070050031030396040500da61103041405462910080f80c1ca0030b41411840c41e8802c090640702421840140d0b901c840c0d004202038845c980c41031003000d102840004000307a1240280c5142d26502000f402551154030728807151016040c41241e0700d20040301c9080028061600400d4000030190401c12842c0403500001c7d81120340d68000e03039050351580d01e0050310f0b00e803d9080c1c1e04c6503450380344120f00780707084800c00514040103109001c1d54520700184100030b540d80e0140c2d1080340c100040007000161450002ca40240c254110111940c01002480ea283c090303248003540c1c281c1c0e885070f0003007004034a0100015400d403c0649200145a42c070700c0e601c08100004d000c06100000700b58028101545030000100e000d035000600e850420205100501020f54042147c441c903a2044415945112003080c09200400b1250302c00c030f0b8020400c800b05420082020510b41c100c80d0105d4082160141d01007031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 953148803 1250 953147553 953147563
    0x20f1207030e0a0516060e180402040b060706090203010615020304030627150510060210021605070f1a03041e060e010e0a0c08010e3301060314100807061d0d0303060503070602 77
    0x840d6010b03111182e8200940c00c0c000d2342643c40744c00208046607034006070000c00d0341644407041c20b940329901c2e00920015800d00f401880020203208030b103d41c0c0d48102c81c0c0d00940341c0c040c0c1e00009024945500310344541611810802c1e014065000c920300c0c4c22002ca141c600c1a02804151000f040d9041c80001000c150351014000107c600a801500d4050803940041000b540300c101c020300081c00e4800803001084007040b00c8805800304070102d003409410145100700200114188a6030030344100200800aa61103481c211b80000d003500d0207980075032a15001018203444282480030358a07095000c088240001040d84555018052950105481e050410300303840316401e101da6a5813042c1c945000300103414100e0081c200720300501a0307051060401480b1002020b074060000291240c2d915002c07046e03084281d5400c4811561140003c43c58160a175864601c44e20803042802000c0c404980106680365041111140043c010440e10f26286009030040415020382c07402031003800300100310b04d4000a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 953150053 1250 953148803 953148827
    0x31803020d03020f280912021302070201032a090b030c0f090a0306050f070912150c09080a0b090f07080303150d2013020f1207030e0a051606 62
    0x40640041c80401000741c010390b12414072805540800c02c07030a100e07810b0039074100504002503055041018421907005200344843e400005c1d2041d82000341e1401aa95800341208401c0403003c0503884402900043e00281491842685121360f030140d001c81e150a40c4d580303403031690340c1c0c1c0d10b42c079000700d89401420306180000c0700d83c00c1c1034070070800c18680c40610b0780d000790541020080165101c541c599455400380e40f020755a0b1201d5a000300c090098803500720384c4850107403846120f245000c40e00350f103a010511031402e600c030110a030b6405c41c0c08855446107002802820f52041110f051400615100748201070440d501ca00c0c5005002079001070103001f1a00307004444c0c03404000c5085031240c201926551403510310131980100001013540c002548403128080c10110110807180c120050700500c05088004014014450702c104560044103002c2000c1c2c0e0301004030340c50400d200c0c0c0e030f030180164000d0181c00b50b040d80ea8032440c040d00c4100403001440c0800d00c0302c8042c1622940d5601c103419603102c2e4600b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 953151303 1250 953150053 953150057
    0x17250509010c060b06071a0a1107080d0b1f02030c0f0106150e2403040c0e0601120513080f0a020d0c0b0f04051e010e0105010b030709120303060510050307031803 71
    0xb0703a000100301160003504400d6801003801c0e141180e1550b480d030000d40b05d44101300a0301404070400c0000c4a00307100c0c03c6c1401c010b030f011251904c0c00d19500c034009480f4400903242800d0b910320180c0381354bc031502400c8108004d40c4018030385a00c0b01c1600070390350350070400e007d000c6407256035800d540e80c403c1806404120f548131080301d018038442d08010b031000c0811a0344a0307001180f01107012504822251880d0780e040140188a1b40c80c00c160600d01035481143d009506407010f4502400321990744803000310b40307a05450f14001040d860303c419402d503098400c0805040c0e902c02060411a0303803032880c0100540b18483d000c882500d10f107400243e445013481a00546100314071070000789501e00802501d03074818826001c0e33610a01668800b05120511140208030681d03581c0449503034100248501805403500130351440c103610305031000500c079403c68000c0d072100030310390100c0e4000c0500940251001e00300c011703e10100501c0d030000040541e0400c07584000020305080820b00440c440c0c80f084400d140d015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 953152553 1250 953151303 953151317
    0x40b0307060f051c050708070201090512131a030105011719050601050c0d020f01151a07080706090b06090c030f15030c03160e0705030c04090c1725050901 68
    0xc29010303110500c0c1e0200c0c60381488410444585000450a405080100c00c4c5100060328107015500400b000c100a18142c1960315001808010440024414001e02844280c030307956039407100b0915070001d0603548250044111240036a561091010185046e00c501780d840100958403003d610b04a4001130341c0340f243e5501000c02c13040d100030300d039002540d02c0001070401c10b1a08404200580c03501c07040800020040c0c000f81c5440309100030a00580a58416086070081118141148030381802c01d40340c810641e00b500003450008000000c41901c2e00c280c0c210804200d052600c0c14003900403c42191400c0c403411060001402250307241d42501d0042e80c0012068640741c0d1b46a5681c2440382149880b20b07850701ca052440401070b43c04001104006d1071030042030581c28a40b90f81054411405031046040c85024001c01a0311800c05065500710741c200c0c0c2c40490b0086604800350781c11810a00c080d0780c0c05440c2c20405c5554003104205009a01c1d0106441404941c40c4c0e03800c4580340694500e03a400180301d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 953153803 1250 953152553 953152559
    0x11040e06150c030c0a020f042a090e070207050301180b0624040803071511030c07030314010b0a0e010801141e0d051e060f040b090c03070f0311040b0307 67
    0x41500c1c0d48641d000018a07460044840c8405285400c6003d2a80d40d035030000030a2402c5040c04012100d00c04019030702848a045030200440c0c501040182d040c0d0952008140d17407840700c0c4954101402040d150000f800b8900700030000a446540a0103524040c0d03080640408010081d0143d2030802500703e003444100d034880c0350800448800041c007140300c10304034150080318181e1120041000780401e60065540300014036050b0402607200748074038061445c0190000401c42d064040321341c021845e0303a9281d642c4503e850103a00512204034503000100c1a6800071640e12852002030a0a0030302d500c0d40b181c0c8004010044458000074000c0c842c01d510400380d11400750400101d002100482d0b80e100c04580341c801d0b0003086c0f003034002c032200ba03d15034080c0380e428000001a1404850220240010f01224502038803104059140903000801a07090003002806141c81800400fa84e070074001c09841c0741658945141004104c940026501c20080420161441c9024854450b510001402074440649 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 953155053 1250 953153803 953153809
    0x3060708060d0c03020406080a021e090601051c0c0e091609060e0a091103180d0503040f020319201c0609020312131d0717070c060203010b0307020111040e06 69
    0x21000344112100f00c0c03070b400044010703074440c044e500280c80c008004183c408550300400a0310403c0042e0492050512400580c8039101c200c0d07202e03401a001e080c16559610b48442c10900c2180e5811003000c460301e4030042c010100c0e800312240d1007044040b20b021015854494001c0180041036507120b01081603c10208110b5014075850408150000e094081c007607030700e00c00c3d0300c00c0e0703075101283c05c011400c00002c011241300e1030183d5000000b0968010b00f00c401c0d082c080603019200c0070b8005007841c000d0040400440d60700304001d50400d0340210952210000c0341c5081715041c0140c3c81d2852150721501c1c5121b50500381803a6001113550351000c560075641403611030800900079888141d03054001e88580c54080006c240003413140b0381c00520000156031601c00c82420b00c81c0f240071141803046221041c00001a408080c000300b0354913115282c00d40392540c81d0103481085030a000100014008400050f1185404000e14450b00c81c64000b40100421303207004800320701c1070b80203101810032040d02142c440c0c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 953156303 1250 953155053 953155069
    0x1503030c0a1b03150c0f080108210712020f07050103270305130b04031e0339080405190302011d0312070506040501110429092701050306070806 63
    0x30b0034070000411616140e4039445100440103884241c0c140d194204614840ea201c2c07413001440781c50707140030720403541015112501c03107078150040c0380c450b00440032400d07004242500f15203905900c400c011001140d424006915442071406a010700d0240e07070b5002542c1c0d40a40268100014400d07a00d1002c0000b83c0d0394048c200d9480841a000c020050042d118540102d0300c490020700b8025220f9602c2d0341c40c601d000c09480425039001070a06010240707240000b90818100805010020004c001e000c0c0c01407603040405d0108000c0105919850b1020024018850000c10a403030040d600f500c072100d40c00c108540106014400240021002074510079180ca521154100b0341e2002015920642c0e014106400c0c030350014502030740e20307800c90000c0c0400c020091060002c0d45544402440c149460aa2500c144840003c3d0f81c041508000e0344804004107031390f00300c400031600101907a000e801101c41c507510502c20003040c0c1e1056a6410004129880c0009003140b02c2c000703513036440700070355142d03000e200801c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 953157553 1250 953156303 953156333
    0x30b090f070c1e17071202010204050607061a031e0c030a051203070e0901060f1205040210050c190501060f09020c03031518070203220b16080f07050102031503030c0a 73
    0x4400e05220000003071041d000b0130f81c25510711012a0701c80c041810074984c1405008941405c2da8810441041540c4035842036640507130300700b4000511900609400d01784030a12240d150351600881d94450880310103000c00c6240840068102da002200e0001417583d14140400058880c0d4824100c1c0002805090000c507407202e4a460300c049842c101c5004034501081c284c00080101d204070500903101c680c4515001e00352010a0014085410070ba0049104000c8801c036a000300800080c0f4844029800c001d21409400b804c40e050002c120a41401c078004c01490060f442c00c01d0150383c0029254880c0e00070342c0c0c0c07200d000c400a9445e549400703400000c41c0c0015180980c00442c82044911003188844c1020f03ca402c07241c0245680f45c10f00007811b0340c081e24080708150030700f09000041c40001070b000191180041c0300b02c00048410007a0601720703c07038010398203005415074000424400304003040d009503004100c9900e00d0000100d5103010583c03a03000700c41510b40f459200303074121400b141d60250701001c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 953158803 1250 953157553 953157593
    0xb060d05060d060c350c0a090e0c19021501090f0f0c08010e0105061c3b07061419050d0f2003010b0a0c05070e0106030b090f070c 57
    0xc11030702d582d00c050954400e91915004582c400300725000d41d50700b001d5403054440310811030403030100c0714031042503203144003074101443c400001c01d0b02c042c83c5008001c100301030803429011411902d042802040103510054905c2c4c01c0000c4280704071140d40c00003070004201c20f104409101c0790713828090b1100091044081500786140c9482c44801e010780d80b4800c3d100e00d04e2456440d12031a6040840d00900e43e030040e0711080c000e0358100101c0706484a282c10304c075031f0b01c0b000800114401c40d0b18406003016461802d841301201d10170708012410001d900842c41d00d186801d4066641c8594bc845003a59849070750501f8051401d000c125044000d80610760310007082c411400d0030b90605c500308080d03a040312000da40c400b07902603a90825480240918607580410383e13032211050328540c10802c1c102a50302900d180b001c140030700000d00c003003000001e000c1400981402d41c10601150794800c1d0040103840c142c40e42c00c0c051035509010461a64074515414814042070701c813000f801d8015510140b03031401007800f00e45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 953160053 1250 953158803 953158819
    0xc04060c030e060d0506040501061b14010b15040306050702010501120f1a0a0f050c0a050a26041101110c031f0b030d020601261203040515070917010b060d0506 70
    0x12590343d101c001d88910b41c550400001c10b0302d00759040c082140c01c1070b04400b050100808844072030000c05442c010a0390780c0540c815120f0300c9007045040c003401181c14140d501c100780f102440303481c03000070300500100d80c05820141b00c070f40c81d4100241d089880a00170101181c0c2c0c64900040410b00007046001c2591050542d0035503000c1e02900070088290035103074600090b45429507503110802600642e0703001f1030328a0509160110f80c2c64068590720444100e1010b001d0258440280903401101058101c6502c030b0550a50b80782c540b4082910750003c4c11043d012a0a10711403840504000920440300c03200030300201113000d1720448040e0048180c6825844032034a441940c2010b480078080c0e03c507001082e8005102a50501e01201c08207480316051103c0702804505c80d00c00c442c400078180e420140d00d0017201c1c0e0340c0e03100c1e03003807560400d50121080300d0100b07135450034003500e2a4030911100c1240d4075118002d441031100c005107802e80d10f03401040c40d44084180140c0d8502d61295200a030070a05c0204800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 953161303 1250 953160053 953160077
    0x9030910050c0a0602040515041409060d1e02041a010c0615080a05070f0614040504050411030118020112020406020c041a090a0504030339020c03070e1006080c04060c03 74
    0x14640f51201104442060700810108502e0801c43c960aa082034050f40050a090400305104000980d000a80d40702d0008000170411644035819000522504050000030700c082c56514022001d402e15000c9003da031a005120403811001400c090b083c1505a441c141043d4035519003001070690403840040d540c07004400040c600004111100e41c561068001e40300481c9010803110314000152321400600030344460301405600004200c03426100c0482e00010691103500340b20031049010070202d9010740c6070400c1d80e6000d2404001107050980301340d81c1c441102000700da1100681c02903120750009644901140c070b075645042e41260542e090898241075010386081c0000d0f00700710003038410700e140a660b401480180f50741401120307065a40d0b80380c84003622076903001c80045003100c0b44404c15544007200c1840b42c000c2c424005000f0080b40101242c5c1d14684450301020b240703c040d111000319014211000400034017544102c7e00c0340400441542c240351600000f40d8800203110800c80030801403003420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 953162553 1250 953161303 953161327
    0xf0c03110313081c05040b22140925030902030a06140703050c090a061b06060807090b040905060103081c021b0c0d0503031308091c1203050903091005 66
    0x42c01800400d00401e00c1501d1030001118240344000b240d0b460750f202c0c540d100c5050281c001045504941103890303030a039100703c420080002c034500002e10100c090406500002daa000c1c238400b10131504011a03402d085615801034044d9181c0051400d03810701001d04070300300f1566000e42e0004030420b0020b0260744903000b1035514442141c04080e6446c601070008070a11107040da15108055202180000ba140b422201070300003230515800344100000c0040b0b08060000045100710042c441c0380d0302c540140483e9848103052501c1d00b046000d0011400d28103414070960749081e01800302c1c3c09411201070a0075900b140c0b2520391540c04001c00c44c590007041caa18594404240c4001c000d50898524007010314040c002c0c6060801d903005601d03521071000c80b0b0100021800100850740c01a030b100c80c80c61000704003403501c0500350180c444865031051000c55104d0744c0501c107150700d00d80da80c42040142d41c000c140301d0003501250801c0d01c50203041d51040c822981c0d6400d1958002c588941c0a003001814505480c0301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 953163803 1250 953162553 953162557
    0x1d031f0c0819181208040c06020601060c0b060102030d0e30071101020f06071706010f0906030b0103140901050a1805060c0a0309200a1403120d0605060f0702030c0a03030f0c031103 79
    0x69180000e0307105c81007009200c41e8030311150241c0740303a2001e401c940d490220010301c0135885210244c81d405513003003c20b0546c1c1c000c008603a43c2d81d960142c00e1046003072401c40c1e65140d41d61199205007200d003405050101c15085000701c500e052240c1580d42c1080034070340382c400220030408000c074103500c04c44d6000c0c82001c1c0c04008161162131160341e03154080c4128419a19680000b07045507050010070140d0865085d000110407090700c0c15890001803803003800c401203001e88404213092407050441800e00595140c19008284070385119036091140d03651103000500b6194144201424641208001c21100014600108065507242c6008150601e85d929600105400d201d460301c09941106042040b50508100c940d00a00000c01031b0f4856142420200340c8403401a9000740214078002403040340c502a81e80140d02800300949443d80301c81824000e1410b03540b0624046c0c1c482e116221007842285003c0a080003582c3d0f2590700c00c241211a418187d5066412032002c600f84500501510420601080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 953165053 1250 953163803 953163833
    0x5031b1f0510120b040b0601020709091b1203022a0a09020a120209030a1e0605090a060f0b0a0e0a20121302030307031d031f0c081918 59
    0x100008403810800c085030b0280b60198401c12500e2421003040010801c000d0100d84d00540000f00826281c0e14040100d0404a89401c40e002041c41c059088050020f034040da8030800c412412000959034817000e013140001d011090007401603211806035651003002c440c16041404c50000503401a20312180041c0d144038aa41140081d141e0106200c3d420036800302c0e40840009008104514244040010a071180d44803000a040ea86145152010202c544c1e07200400094110b0010019418403100c10790b101c170115841a100142070035180a001d074030505c42c030002201c005080304207507071502180751244030006000d551043d07602c2c0e00c98123040c00501040c0d403040c0034011100d40e0301d41c9407510324080d6a10190080f0702e03051b441410000181ca0000c04c607440d481c4c15042030140100101c00c03d00b140c2e074401c1d40e942d8160040ca46140340c07869040c1e1a595020080305428410b8504140d001c42d00d042003190340f50303105100c000614000903610360181001b11441c000c2c01e00307025000d86601c211401209 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 953166303 1250 953165053 953165113
    0xc03190201180308090114011401031d01020301091d0625050702030a0507320103020702121209011710051512010e1b1c0b220e0c040905031b 62
    0x403017044540c0400b80f0411a00c400000c100110a5041281082e08004240c44172814155034540300c1e11420354020b40c2c102c01c82e68007002559a5a1207000756005810050078040d52049081e0303e0f41003624000c07070b00910030701c03e201c2c1e00041c00d051400e61850004501e0700c41d4062000070040e0501684092004050706802800200b07030103450585e1588044080781401980c4094056900d8200c0b0b4441b4409204c50200b403901584601450001403480900340d5141c1c80540b15421800e0001d0303955801500a0400c2625010821540200c010f01c1d40141100d0031107005409020620580c54403010540200010305c082c2070510440040c40d0764a01020707000600ba505000d420800c0d602c0d110322070646a0002041100c3c141124030079920361040c03480040404954654090510340c0d1100780e403008880b00c1c1c2c08010f0b2003075108982c842c4000e0000700c5407080c0310701841024100728109400344060a0394004000e624000c81c0460b070030320308004000c06000324059a407080200151045004035103100c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 953167553 1250 953166303 953166317
    0x30f0e0904050717030a050711010306050910080c0103020405012f120c070b070210030f0b130c110106050a0306090507150210050a0b0901050913050d0e01020708030c031902011803 79
    0x400481c034038107803080c0c80c02c0040d54401c000c1028103540c000d060f10341d11527001000080c101070600042c0e020780b4003034200c1a08a68900d0070401e0360340b180e2000710103c509440540e50140c0c1042e0044099204600a05002c180100442204030281020403050803078000c4040c8425004c07409140e0070001000f408019961021030b0041c29003205010101c020107040703140c545001c0d82580480e45170140f03c0c181c0c405040e40e41c2d02d864101145600488a0100d000304400c501013901c1d55032400600360700040100086001c044601500c0e8148140426103038010150748450b8a59600e410151401030300843d41c1c0c0c00b03900000100100001c0d20030b24010604d40250200180e81c2e070b4400c0881c4c0b0001e001c0710495080ca000751000d6200c203d03940b415100203941000036940c4103102145a00c248220060191141c1141510341d00d601c00881c54030f1510036401e4501c26540e95150a0707880c0600510450150810402c074851911a980c03841c40c0c142103800041140e80840c06d84805036840c015041d00805d000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 953168803 1250 953167553 953167559
    0x9012d0f05090a06031101110a0c030c090f1118030102130b040501110601050a12061503031101060911310801020403110409030e120325050c030303040b04030f0e09040507 75
    0x1808109a00c015252801c101a41c17441e140c18807044c05c4a0392180c1844813880552104620a00048000d240c0003003c000105a40340780c06031035910f00e0311400f58803902e4107100c100080f1160003450381c001d490452140c144041d1010350312a24000030441c0c0da06640c01c000d811640c602550307008005001c21311b070302c5488034035100005d081d00c20f9004110180d508002c0040c0425910100e80b42d081e0741c500308104a0510302482c0960013400c00c61401411142d6001d0000704142d80120b0034201d00702c09000a2010301d81d582c80c0482038601040c0003098240052000c40c039044c02d200b04601c10440428560903181c4c0c11441c2d2501d101026400511f180d940024083c000d11515103200801482c00381c1e010004000152030060160004080880c4200e0582e10242d015100c10029540b1042c0740c8941c1413140c3d0181c40f1500581030b4100070890350750149003000d0b902d616011040d64030840d000890a11035540d25603040b00c9107005070b032402041c0400403590b14459200c2c0a10548a00d00c00e170020250341d82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 953170053 1250 953168803 953168809
    0xa03080c0c010224100b030a05060102012301090905011503050303040506011d0601031e1503021c03091e090e010e010b030c01210912082409012d0f05 66
    0x1451550180c150f5000010520150740118030f4082c60340381e59a0f40e0035080d00d54114400341c003074171070b440241200b50100601084c1c811a610690180109030000c12200d001415082d1203032454516402004426000400004065800200c400352048000054207001d01c05030302c01c000c90680080e00d00fa0f00200400c0200242004a24054007034407828049210b40c156069096560003026181010f85540941c042c08220030f1440e540c45000c1002440b00c900b02c503120701c8000045e4403003684140090003664010030924160080002d405030b60b014070300c9040015031064402d80c008600144090340d0000500640c1c18412140301d03440349000401c102060405590a40f41c04d5514144a41c00220196400382e0304070180603d4000000125850010f00c102010f00a00314413401910310004a200320139050b42c00440d4034401e8004404403007442c209103803449002d046d482400b40d00080d0440051100920105090030483c185410f0b102203c0c2d4844d4600c980e10f04158064456a501c90800707020901d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 953171303 1250 953170053 953170063
    0x726010204060921150902031e0d1403010602070312050903100e1b01020615040605090a0203100605030c040603050a090c0b18091e07021c0f09170c0609010903020a03080c 75
    0x20303a044201c0195a050b21061500c000a141800180e40d44500d00003c5440034484201c0070040f0030350072140c9c2004050b01944500e03000300d1200c0011244da450610a0031741d401500e069810715401000c08a0850792240c3d0fa80c2c0415074401c040c49024402c1d000550386c20000c4150842007240301044031060030f0079940c40c0c07800a4411345980030407100c2d90206a42d0014160750b110303061a802034000c10341100810028400b07600b0190f0800c540d84200301002d03210382c004600030590304d9000c0300d2059891004482032701003520800000704082208102c1c43e8841d401c0741c0d40040d15650001089116035845541001141c1c5c081d100603240850f0022003094000290f0b00383c24826940c0e00700c1d61600900032942e42da1a2141002c50b422a0000708481c50320800801007078816100000303008105000001c0c04180000048900050384c8107000304600500c845900c010110310001003a8038404c6c0c80801ca00c641150000f00c2c1045001c0030004056035407031002400550040d10500da07580e03d00f500b40e5040c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 953172553 1250 953171303 953171339
    0xc190e0108010c0f110c04110c0303010311180c0a0f030204052101050a02120f090c060a11061b0a0e041b0c0203010f141303032309071707260102040609 67
    0x200244d40259280204042107074a1b000c1c800b01d80c0000c0d0200c40e400c4004050141305001d80082c4000300003c0204145003184410443e011541c698000d51a0b03055100001e00898404003c00c0d404d0080c1c1c0d0001c2d0040d400021680d40904025003801c1d2903c0115075040c0d00150114000800e051f09000c84500a00c90030342c1024010390f0951910156512200980c80c01902d224804580b040000e001030741c2c14803180410070300040c00300741d452406200c0209248140c00032004607000303840106e0224644151564900e0303220044141c01d0040c1c40343c094450114503440305400684034092502c1d00701903440321070074141654903400c01418460050608507440b0b440c20001061901e003040c42e090809000c070581c0040fa8001c0090010308a00d0704901401070a0151000e0303905001e000219580c030072032103d00c21586482154030050b541c0324801c1c550041c1503406682030700941c1c0244161100300d41c0703180c0a0a4602000c500c200100518070b401c983c441d61140c0000307490b800040c481e00503e44080201 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 953173803 1250 953172553 953172557
    0xa060e010216030e1c030504031104051501080721061a1809280501030605090a0b1303021c020f06010618050f0d060f050108100204080c190e0108010c0f 67
    0x3072440c064071a00c0e00c0c042e0b0040181c280001d0958849081e0b450160691140d20000340202ca400c0b81072030040e005800501003122461050114542241001c0c8581403044451004213000800e8203001543d0302d0030041c0c002810000100c2040500c07070000d415541442091100002e0b10030301e80a140e18ad451746014161a900c40100b120000c800c81c4070308100007a45048030701401341c0d01e0324444007132506408400000102c19100041a00e00c9040e4010350499000c0e140c2448245e603400e51041d215510a90010140d039903801c0420a0602c003080a18000380c40b9004958103400104001c1407003200e1202d503207005a1021040c01c2910000b0312241d8014141801e207084010902c40c10200280c0b0103009040c060030b281c20601c0020741e00c04e07c5a000280d08400108498190341d0802c070060700e4240602407980c420954081e80482052003224101ca4189014000141020307040003c09041c00d2544110701640801c041001640302e02214004c0c03007800c000003043c00c00d20070090b102000b49068401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 953175053 1250 953173803 953173807
    0x6040803070e240c030c0105071814220b030f07030201031404030f050f300106110a060f0207290609150f04271401020a020d03050c1603020a060e0102 66
    0x142c1e040305000b14115000010f8035283d02d4a0303d040390a071450250240b29070ba99030130324007032150550304400c000701c2251041c802424010723200c40c908003602c001120050303088400039400c1c1d0310344100e540d012580400d02d110701207031000090740024901200c1625516058000da0800c03c111340e0141704800180784a2031054500c0d03c1c0a4030301400c207c0d5581000130622034001048212545a00110750744200c1444401804013a03c90741824454102d00191005c42032000c00424403602943c40c29a00a0001004150300c07895035544e0006000c1001c030305c10600d07400748161f10014010250351448100801d08aa020741010b50007000c0388000645828000c0d0006002c1c001408a940c0158405003810354902c58200e0720b1502150080c0f035004a5038030320606030b0102c6c410003540040c1a4107030b14002c154081c9000380502656080b84203030315074003016038041d0380702e0f000081c041e4006c168412120b1000300e0414010030402540c0c2170003180201c0058100e2203207082004001d10a049260351040002c43c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 953176303 1250 953175053 953175079
    0xd0b01090602060f150d03020d09080304050a050f0d08040e07020706031a090601020a080409140606040f030210050705030d0b0310090c0b0d1b0f110615061b06040803070e 75
    0x40d4a9541c0609240792003894040040c80340e1118004034a8050009031006c460000c00d07040003519000c3d440b0729800010501100081c4000000095074142d61000301000500d610740000c008492212925407a0840b04180307409000c0341e02903010300b00038818916001c030949000000242002c6c215000b5000b40740c070f401c80807a2880c4030143d012002241c15108010b81e0784135540182c0c50044868001402d1043c0003030049540c030140d07000011200400311405095440304020010540194000c01c158501c004030104050301d8469000700c2c82246030301380b043c13500401e500c40c00c0c21a4400e40c17030002510b8a90740000e4190904000854181f1580d001c02c00c641c990550302c0300e440582030b03c40c8071004071011950107208620381d44075443c0302c00404401c090548400001600c1016820071060103c0c0311b04003034001d12900440c0f0980709207180310b00321038a0300010b020000b403a001034842040e080d030901c80e0280d4101040021034050b074010111070741c84e460301003401004042120784141c001e82c01e4114071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 953177553 1250 953176303 953176307
    0x3150e0705040314120301122f011403060d06022b0209010e0105070210083c0c0a08060d08070b040606290708030901090c140a0b0307020307060902010e150d0b010906 73
    0xa6410742300304800c058041302c07080c2000d070039030480300044a030a006440c040080072840001e601c0e034054820b0322200f0f0840004900d4182c04c0c0012543d85400c440310108080014520354010890614040300031038403100100101f040b80d156007090b070540c0e20b0b40001d220600b0768000020601c0e4940910704640361440c0b903408150300f0b680d4005140244440f15001c03d800700d03e43d8140f0021980d5004135088030b140d0540444400400c295810703900d2088200108201e2110314089a00300c2050b512603104940740c0c4c009001c080c645184059030080c5c018440c2c3c00001d0313030007074a50340500d000340400304545061400d002803401131031900c880c051400d03070401d118480b05007040c2d40320b441e0843d20319074413a5166144103003d44994680146050030100b030100d000ca8503107104900d9840b00765210450070340c8034ac1081c00300348407e035640e4015034000d200b51000181c01d80c00c061400c1f8810b00d07000600c0682440414881c8a00050500c00d010012500120300041132042070042042464150b002601d80000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 953178803 1250 953177553 953177557
    0x140106020a0f020a0b121e040b1b07060e03090f040e12071b0b0406030b011d06070318180b04020f03070c05070312080601021b0306060103150e070504031412 69
    0x40201601e100600032010b560303d070701c0307041c00401c443c55015590754050003c0b192283c2040307d00005182500790100c0c44000004078107407041e60300c80042145a01c503529400c0e81c005074010f00380e00e500c0c001c01101c2d0015401c0c3c001c0c1c0301c085442400940c2c81e4400c1008101245c10300d0391056001d1803500c1c3c84481e05030000a40d40001c088000b0309150f85a04600385001e0060700c02d1410715801c44400d40000c0c2c3d00c1e01e20f100810440700300f82e030104000c41c020b2004603410a032101c42d5886810007050580700c0d5190030340003000b04a120741408541c10040840d0a14495400c0d40500500013451840014100c070600501010041c1203070110702e04612144907410501001d01702100b00700303003201d140c01085010000c41018640200791200c442c6e0902c100100317402000c4503418014021550f0003890703000e0003660303103071940c1c00140078040c0f507558440118002e01158104034001d1034204d400045040f501c1e14418021078090f42d580f40d8550450402c0c000d00b550441c4007072400c0e809444107035107035484581 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 953180053 1250 953178803 953178823
    0x5030d0c1b080a0e01020c10020c1806030a150f060f06090504090b01060e0a0906080109140105070e01050c010609061404050c0a02250803030a060e1006020a0803100308120a14010602 80
    0xf840700e02421300000403071401c40c010b01c0d034030f400602c952040c41d5650340014441c0101d400c1140c1c00890481170125400c552181075608a803d58000751b0346000180351002c00c1086010030010000d07041e0403d40811050b240613520004001c83c1c040c000380421540304030420090842075409001418446d55152581d10052140c2e400b000750454110340e1030340c3d0301c6143e4030080408990500c041512500c203640203005102046920f0f0525135000710a180044c01280c0c4181e11949454980d0603503c401501c2d40d0b0302c1482c843c0d40319540c50304081000e442c10310070701c40500180d5124040242d0032800f44811150050b0403e450003209219600301c076940064a60700000e000c22042c410200c7c8111540d0165a1036040001c0e00d01021041254003201036008104650003454890282e0300c2d08008541c608825010700001600001d55001c08618114021070f08403103c0c4401e100b2565507911201c150346c0080b460705018542400c14011603503014083c607029603915185445903035241c8040a580c46002c50 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 953181303 1250 953180053 953180057
    0x2040c03090203100c0c050f0304093c150608041502340c063f0207080c0303071106070206061c03110628050c1209030705030d0c1b080a 60
    0x144c1c401a85c42d11030792810f280160f1010440c0d54014624900f25220341003802010340903841c0480c5511040404501b0300090396800c0c40d059050900c00301000b003034003166103003181110740303031204080452030030030303441000701001d42c2c602506082900c1c0c41142e41c1c205404035410940184060441d400f20030100e030240c1c14000303a841c00894500c40e107060b86440a50f00140420b4503035840019025081054a00c842000700004100f80980b025a8800c81d580c1c94411450100c02920901407000654001c0c900c05020300b00690800e0b001c0e00c02540342d0380c0116440740c00103444201c078000c0d44000300511504240503002a2505191a2021691071a0000400b0506081c01d4120f20145130003464030110440300384042d10460302d01202c1d05a412039501038401c0e20745101d1002c04011703407024461240203005809403103141c440b41c0b040e49140710102900001250204120344000950b0400c001e041c403818061001c2452146101f000c1c01c0245254018006902400030726070028218004407400348450b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 953182553 1250 953181303 953181311
    0x70812190f140406080403020d0f120c1b03022a01020c100c0204091101110606030a0f020111010609050f0610211d030c060c070f0b04020612040605010302040c0309020310 75
    0x100850340302020241c10382c0011030000b40421004d40c442c0c1c065109034000d1702103c002d07850014084a22a8030200c03841e0010b0344821160341d1401e0700d600000215041c3e40b40c00c2c94141d003083c0007400d01401001c4100c0150307004c124040c0100740382c5001e84246401b141c2210300781084a40002c0d46652402c00680d100c0c1e5010140c49900602480d41040300c20b401620402140e18145440c1d0a8495842d20b40750116103400c003042d001220000d1014811440500504510305265499130643c000c242e604a051142024280c0c04101091080c10b0003010b6030310f4081060300b0218601c0c00d01e4030700603241e14041c0050030440d422042e000301154141d100790a03005c41c00914510102030040c41e00e8074800030101d40a1031030001d06600000508515030011094403619220103414400c14400d13000300800440c40c0c101c4102c04510010b49250344540050006464641c41d410404122041190100c4419940e8070040c029030401d8490b02a1070071940c18100074802c09500001d070340d1500804030f00f0b001b94031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 953183803 1250 953182553 953182577
    0x1030c0302071e0201030b031614010203070b0f06040b0a231f080612151b0d0504050f070501020606010c0206030c070f0503031b040b0d020a140c07081219 68
    0x400d604840a054219040b16001c60a83d01107541e00c1c407525909070700007810000f0030b05240c43c012800c0d12030a9500c08607401564540300495142d189250341e410306600007801550041904081464071403a120004d000151800300200403c03a003c1c42a0117010b100f00306002e01040c00c40c0d00128081d00400d0000c1103000c0c46070b00c0069001c000440d1307480287c86a28000450080c0c005551a0040408172000c10300f42c90361000740d5917103110754410011000412804240110710044a44841016240480e407070554a2015941a01c00c1500c080302c090740070b15144805a0070502061005e40001d00c06070800e801e01e440000c1c10981486406032180e000080442c4114584600308c07101142d0052400b03191660a0030300946940088403010f81c68081040b1300144408000b086800b0f807100e03900500c1c2016030400c1144000c4d0000d16000c828444101076041e800780b43d030805041150750943c02449400e0411071000d09112410380203940e0072006200012010690450010b1400b040e071a2840072002 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 953185053 1250 953183803 953183807
    0x40f0618061d0a180b1c0209010626040c231003020d1401240507120f0c0c0e15030a1205031f0b19020327060702180a150b030601030c 59
    0x743c0e50707001c030b4119000300b003500002241540040c0b6402e0307811180507011520000c294200f081515070000d502241c0d03140180451805040d0714191840859581d00590814031031003034450301c0a4030155601046954100680c0e203541960040045420444d0410000400081020008a012024103058001c10940e0602003254021451046115842c0d101940c0d20361103000c0c4403440341d000b1585810744d200c210800600900c1100c0c0c0440c1c0c0301c40c001c0702a20702444125040180885210104040d56042078042070300c4020300800307081d081c215041c0d00e0600080b0642700c08204405a40a6000001e0120208400d00b410b65107844040c142a59640c1e500e401030805e010a000a41202c40f02d50f49002c546440744202411410110201c01c20b000100d2001c01d0740c0d24000e0280c41019461410401d8681980a16000425800c003400c070a04110b682e50004904000716989087c606403c0b20401405091038060500c001d1307184940d40c5412410803480c03006511004143d50305058803014801180c038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 953186303 1250 953185053 953185069
    0x2061503160e010f0b0307080621100e06070e03030d09032102040503190209161101020f190c0323070f050307120302030c0a23040f0618061d 62
    0x40315940d241d5481588480424059400030b0146030101d1002410200f5900500803c50740600b40c82d4941d6211507840d8810002500c80d00003004400e03a0744206201c507041d1040000b0b10005098020208024449038029442c1401c01000d110030080b031140b18500584001c411502c10000299000c100300c181428180c603030050702e200409200c40c0c3c07010341106044660b400750040d0b84045003500c12040741584d048010b20782c0c0e544003a600c0080f0030041190a1008004c00c0702c1c851282c10702c514640c60303079124242240c0041e031400c51458400a0381d220303007240320119058801d0079800c109404081d5a10010102c1c03441c3c22440403e04025904a1185400b640c00c0ea50020390006d00700b03040403214501192603402141048403a008010081c8425502900a4034400c255801056080014210b0f040f121a803601c03581003202c0c7c3d850b050180c024003420303000303001400c6000c00b580f101a2400100901e0040c501c4000c0010728110b600511100c4c1e0b00040c0c006800b00101d00768000c10510b040066065 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 953187553 1250 953186303 953186323
    0x80c181e03060c040f08210903010e1b090903040b0304020d0f050d0f0314090d030b04020f030f0702070b090f0423090d0f03140f1003061503120f02061503 68
    0x148280340412054580030f5000348243d8404100031107038155a004251350b629101880e0348160142007030441519a903000151040305401000824880200c4e603c046c02e2200220a82d80f060940d41c0c40c40c40d05003440c4110940241860000314602880c10394042228000a0002403184010001001c14009508029000c00d03800100344d600d10f400c00040502007000b800091000b0a0a004d01030300b07007580414081e03106440880103030244040300c0d0401c034020110015980d5000b503082c007080f410301a020010314030031194007074021140d00340054064900032980c1e02c03c0d0306882041100342d40c00d0b1500360b107000303020034180e4010910400781c603042da070145651440f08180304100030400100c01e40008603503140f0f41b599218040f60880d62481241aa40403080410000c44c0c903078086003040e083c05803031a174031050385130b0a000c0c46500c0b5552042516807080f00c0364803e42c0005814014000d0103441c240412540782006820190042c00c06504d4002c006c11b07040280003071039101c84454a09000304041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 953188803 1250 953187553 953187559
    0x11217030a05040308070216030212010212040f1412070f03050c010507030903031d0604081803070e01080d03020c1e100c0305010f05151801050f040b0a080c181e 71
    0xc0e440e00316103540091504450950008013200007249142d400810024000042c01c0c1e00240d01a056400780494500000000c1a8a40d82082401d11502e070064246000f03500c174580c12540100d050804c100382e034a864156180503008480e81040b0785c48808211079170140e01600b800707100340b035600b41541c2c68058034001c020903508250800c00e400c0e616501021800e8440d80381080441950841c084504682920540051744088003060201d400200908441100140f4852001a0110200f400c1601584c46a07070001d00403c01480824024019031203080c103070340f800b1403c0031184c1da0100d6035240c038204e1780e00b0320742100d100400008030305022205141140400a00102e46d403043d005000340004d00c103030610181442000700f218540600041c5220008402090a01900390591030700408144913481c1801000c1011054148100f00948001c101c48a086070302c0d4001c0000103411408014241304166008100b00801a26001519051910183d44542a000c0040e14030190700701d0180d0201e034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 953190053 1250 953188803 953188807
    0x100c0504230102060109180209012d05060d090c1a030703050906040f031d091906090c0806150715050603010c02010e060a0c03090c1401021923150108010b0a05010512011217 76
    0x1ea4bc01c081c400501c51004003952000e1a41c42d80c00900d04a01c0003802030319402138007000410740c11840f541009402a0080c00d00741200d950f00c848020080102400c1c1a003140c07404000c018510303815208450307102400901525503494290384030011007001443c01010700c2585c09501482d540380d078940310440800546124154100060541c003aa2008001c005d44141003200c046a0444e9600810880303800a888043c41902c80c0001c0000d4011407800312103190341d0911a04000c0b407403e0300c00c010425241403000800703040400906007990a900300b10415a8148041e4404081000450650000c0b40c03980000301302c6d0700d0030b004901400d0f5144c0e0107002d0b4040d030080465001c84120004512032426000c40e60100418140f02c4880003107032802401c0e580e0354084c13042150b00c0392001080100c035004150380b20b2180301000d0b414107003400c7e0400d9209030754803641d2100c030f0304100003100007a0400b402d1107814100c1150240c3e40038401401030f00101400d0350600c4003089040c03401d80241d4810548859 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 953191303 1250 953190053 953190059
    0xb07030f09062403110603060303071205070b0112211107030c051008090c010503190c0801031203060b030c09041b170a0608030702040c02100c050423010206010918020901 75
    0x5403200000c0840c00d0034907022010f03441c03202e0b51401c208807940720524091183c0c400c010481d030b64200402240d0980010408100026040100203880c401e407031725038588031001400d10229a10301600b1280c0045407007510b810208000800f8400c0a0b2040d0190076044075803d401118140d8000444800343d10810304048100036140b11080103446043e281001054030100c01211032500549001d0880d4015100810340355114400440c1c0c44802340a4500e68011074440c0f00040702c0c0041801000911580014800c010354042e1070700e8400c0e02494144500da0a0030303e035030300700d10001e00b6600350300c00300290700000c54907550001f001250500c55240001d00120074050075640380c010307a03002c034500b84e500080d01728460b901c01e103004da038030020055040000039802d00004183c91880704040d0700c40c120103a403440c925402041cae003000351340d134906442c0d13072801c2024001c81e2404100d034100c101c4c000248001c00c1e64001903190444070349000114084035450301d440d549981c40d00000c0e4100c1c81120001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 953192553 1250 953191303 953191313
    0x3050a0b060a05130b010e12060a050a0e0304052407030216121a0a1508011e060e2a03070e030d0206070e0609060d0911090703180b07030f09 62
    0x15214280100e0800005980d04000c200d003550150041c250300a21054605a0f82c00e00c551040d0103008060605040c1d05510740c0000c2c280003105900022160701100400031040f906001c0c4d00e402040c80e1005201820a801c4016240d00440c040c40380541d49180c42c02c440300001c541c440c1202810581d50740e66600c2d090400a441d410390f00f50469140b419040d0000d1400ca040c00180c000a0300401400b00c0c1c65042003000c84009405001c0b1103800d0b448000b000036800840300e0180040119800000d01e9849440c0340c900040b01600365811014540303070040040785c440030705242c0e02c800200205440400c08181e0511b068911140e04000b20801008120303106400002040403020120101c45001e042603c00302d07038a1504551500002d00070010241c024280000523003407072100203000c94180260000c02c0d10846a2041095481c10056424a8220b080008185811402c1442d09002803070809e024003061044023000100394140000c0000c0c070340c512030b6002c4410070940d5181803100c1d028906003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 953193803 1250 953192553 953192563
    0xb0a0b0f1e0c010506120a020a090f0f0c020303060424090506010c0506010801050f01170705090a1e1a1203030f100302120f0106081506040213030506010b070c0609030b04200a0305 79
    0x5c503500590700b07070380701d56803d600002d00c0c031102075170050280400c070b0b0809235110007500c07402c007401c0022901d0380140000c9400502501d2030300e10041c4e0003107882c0d00c0c000e41000709039003c40034001445160700012025409101c0c40a8003900e0342c0c501b01250300e0300c43d0401200e900c0b0385070501801c0b42c00340000104801d40103400c45800351124000880c1241d881e031903503000008026443c9075603a40071800030482400e110c4811a44200151000600ca1400801d201340340d44560b445419041d541c1d1010000c4040f52005003401e8090940d40c0041700c05881c0c1030503a0703d22010300007110140119000512940004003090040c5601400304410f082a00c01c83d01e81e102d481c4402d003c0342e035003440f0380820090000603210140f003c2c0701300110b03540c0c1c4171348007403000a500141003e080803441000102c0441c0003000820b000b010749090b038a1ba5001e05040c4440074a440303401c22004c01804500400c0822178806000b0f4215030409440282002422000c800c45014045041e820201300344000081c4035001c15 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 953195053 1250 953193803 953193811
    0xa170a020d05180d0c0503030d1d031603050d110d090506160e090402240403060c020105070909051015210c0917030f0f0406030b0a0b0f1e0c0105 64
    0x848041000075034081c1c80728001c103c0e0b100480f140c14410030200c0c1c90504c0e0b080c41c07003d004034130016a6945860104e0304580c00030b0201c0c0c100986682c2c51a030710800040e8040c0070401028059402c00703030482c04451402c00c00308000f4081080205410241940d51750000c042c801a0400856489044807100070142c2008041541c0d00d0003601c0004903903c020031150390380041c1d80e1b5034004102d40f0460030041a820080c20503030b001000c0b144400068014900c030318000303580b0704003002c0d03c0740c8c51803070003c06803046c0d4202c40b02164100014800781582103c1070005840800d080841c0030350340c040800ca41c25500c2ea0100e120803030600900c0d10f039250000c01400c00d0214050810704000301ca0251501030340c04086c031890008079550001c00150726020b0b21904c4680400c003c2d130b443c007130b05105980740a030800f03040340d04140c0e000142000515018410b83d110f011050b2440b4000a28040394842c240c05040c02c00c00031100d000031104400712002c8828158800868002616140c20020380c9000f400111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 953196303 1250 953195053 953195057
    0x1c0804170319120b04110a12090203060f01170a120e043b07360504030e090a050f040201050d0204030204020f182e1b051018080405120a170a 62
    0x580030404e45c1424051881c6654121402518040c0c0c114411144a910080d040480740ea41d1404240140c0c0e01340001400307132a6005c1204070319418107804000c5401c0100c42c812865003c1920b100001c0d08180c800c01c140200c60400700f4440b610072021030b0213050f484030280b100f0718088107020b0091038039021000120f03540740351a500380f030a140711050b070300d00b101d016551482e8880140b043d0880b1040103010a108520b07203161150780001c1d0019400d9950588049012032402011001c250400b0300e5941d910001804007484241010f0306003400e0218040d01c081d042082c0040c1011850b101c40d01120001c6030302030170443d41c0b003a11810403091034219122000744d940001400c1c8846107018801036000440c01126840e981407542ea0702029100d400524101f400f03074000d500c112001c60020b5101703c0500807005419140a031a8043e8112030000201400e14564201c1c0400032031390290649081d20340540c0c41010726030310400c5440c90280c210380300408003007010b0150400000720a01400010b4425 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 953197553 1250 953196303 953196311
    0xb18040b070f03140c0a05041809050d080106081b0408070e010503070b040f09150504050a0c020f0d2c120f070f0e0c030402130c09051c080417031912 66
    0x40e038100c0613035070800100c5101c034400c980071401c4a44040c006003240049414800e1610355640b080030500307143e246107050380340e944105100034000140900c0c15482c1c9140303050b1102d50304000001c1c046000262410a1000748100781910803000c0c00f0444014104001c1246c6c10141d48d4854414188803d01a0724040d002c0c807080002d00d020134009603020340710480400c40000303003410780e5200201444010304031300411202000540c0d41b40c1d44559030117180b02c014081102822404060b1904120703825400007a48800c44001c40c1c0c590042400c0030b40501103041d2501301803c8022074007001c40d500107003584542654801e021031600043d42c052401000c00036911226074945080721b1000c8244140314900d6039850004070041c0506c801154464070092200b05840801c02451084507605155000071030302280c41803002c0c1ca0101d407225032000592031403039040b145a40c0d440000740114480d248401b001852103a0000200340b050316515000c154000ca4450349417140148040c0c200710b0880314003460 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 953198803 1250 953197553 953197577
    0xa02031e0f031e0717070c0e060a060e010f120e07030b070516060f0e0d091703030618070c080a0f03050703020712080c040905011203111f0b18040b07 66
    0x8000d0b50f5014a4100c1446000c46094662201e40d90049a0489094140f0708004030740e0311500c4050190680110f000824543c00c0c03070301202c408180079150a10691a0217420080780341d1103107a65008040a180007944901307030340d030250782140c6205030450032981001c600601c1c2900004462044900680749034207070303848507a0251000d204040020b10b8120010b011440400c00e10f80201d03507444061540000c010400312440d508012104d0039034000507611a00801071925074940414843c5058005540f95062640c0000c1141c03041c0c240d1040c03101400700c00141c00501032581d00c4031094100701980c0e41d4840310900104150f408801000110f854540030038a020b1092084d10085079005c0a142c2590040c92400e03281031740014012903042c14200400b18072501d040c050f40d402401c030442406144111403030041e02c42c1d100d50601e1010b6602032200c9007450301c400f01c0207290b400340c40b8000060940044011a007000c1500800ba900c0f0001c4c0c5051108229514200500c0380a007070303440002c0d4041e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 953200053 1250 953198803 953198833
    0x903050604050d3908040b03091e07050105070f170c250b1c060b040807090f0c050d0b0301090b0f04110f061c0b0a030302070602150f010b0702030a02031e 68
    0x1003d0025403050313540300c102c07100903810004c054813055000e01d40250410341da03078081034002d0740300b1141c4030240c0d04040707039203028554003540000c1101861b0001c0c0114909010009056004800029180750a038140031001e01182803821f404603145030700d0f91135940300b804442030764500a81251000142080d04060600030100e00710381c05849608038410310700314a2a2220303826041750820482095a01c990020341958080300030001003401c4400350600710300d88001300c02150613107403030b612690b0b0425184a421700c2e4030804941c1c021400003400940e07814110b0200340101250036000302085116000e2081c0c40e07220a89003807040e0303c92091458954114030a100c0c201141094103900941d0600c10414000d1104071039101d040c1c0fa0350f03000a1842c54200004800c076015500650140c1c00c1300805004040c0d050100020010303040011011904105c0c1021102010502c20300848140c040b40c100115501442a11080c41c1c000741110450250250f031100003046c003000602162092400b09540c0c42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 953201303 1250 953200053 953200097
    0xc19150e25140f0f120703030212090f12071d0420060f0a111905060c090303070b2815080604020d030c031e03050a0507020f1c0903050604050d 63
    0x60704070000918064012024000f0307038840c0c00c0080f50b020f044000407558030340380c6000e0030f07003928404401441298950705001c0e051130081c281070290000104002d94554030b132846401c400ba103050343c03102c0e013945a00030541c1c14040030380c04c412168003113488185800c03d04110640d00441c068000101002d0a20002111000700c40e0b100c91740205c01804440100c04c50000034002103800e506110741041c290030b03031040c01c24440e0381c0d040903240d41d407000700740034044100a440e40c0a42d01c1c1c04d4440c0b078a0715050010f9540d010b01c20f4018000341c40e080018498401c405880080c3d500b000e14120521181054a003000c0c0413110141420104405400581e210001805501450300903241a42180c0d50780c500711000b24000d0f0b000c2d024802d0304507854510355a65070504e1210401603a00080383d0520b102030000380c481c0a030414046501019803d01d404102145591080d00d14038032810f5156003c50003607801000070b6001905034010b590800081c02408a000324082c9121f03901c8940381080300310444112 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 953202553 1250 953201303 953201309
    0xf0605010e030d03020d022b0b03060907120809270c07020a050f15030a0203010620100b120312010806010f0e04030c03031d0c150c19150e25 62
    0xda8003c10b4500c0c81d142c06603004149141000a02528050244902c40d075806181242050300c4926032125180b1140140b00c0c0518040c42140a40200d0500301c0d80250b1319074440c0500460342d140c00798030404212001c0c00b11680d103900a00704c401d80180d4000511340d5610504e000b966112100000194411410340c103c0720707040d60080007800703041d080c0703000c0c08a100030740301155800458600d04c80c101021007a014510810f210040507075290305056004107034250380b18017107440b845400380f442c60311000070640c400703162021440024125031100000c2c084680e80e10070603005000004112505d44450010681a91060740840742140da84010740400c0b21182e1050320051454040401c0003e17110301d8010380498001d01d400705244200942c2a01074640e41c0c001007086503c2404c0f42e154a05010400710280c81302249118105403502c1d080c0c41d142c5410b01018001301441507890f8007005141d08404c01201c4078410f080000581a15000750369055480c0c101013500070000c410f015001c1c030a080142a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 953203803 1250 953202553 953202559
    0x140d1a0f073b04060b0310060206010e1f0e01181104060e0111010204030804090b041d0d031d0102030702010e0f0c0f0d08160302010516030501140f0a180f0605010e 72
    0x1d5807022000e03180c8240e444031107102c40c0b6001d031050081c0c0d0740c0750b0207008007504d02d1000300b65580c1460155040c0c0200c079503000200350340103180100304500051410f982c1c0000c45401903184003180158458080003107810051071141042e002107404400100c506c802c900741c0b8101040007224504008005000e18030800c4001a445048040e0a5105034644081c4400c0ca80015051544a0342c80e494990410b4101e0500340340c3d203e081003260714243c018068601c2c44c898030b0400d9405550103a5440d02d900c2500302d8141911080608505480303966104d0b00307141124004c40d224101954028003a21a920040c003440c03140d61410140c8010118010192040050040811014400910403840c0031081c040d5401c0304140903140e2080c1c0c00e1200c2d5048030380300e98000255490441e0180700c60310140351001041520300790040c41001c1c42c6140801c0744400803515145440764940c0010b50740c0721260130000c0c1000300d042c682c103c10380d82c6801898109403100750a104150b15400110f441228000020368 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 953205053 1250 953203803 953203847
    0x8010908030610020f0715080f0601170c04030b040c0503070501050c0601090f020706021b1e0a0b06030a1209031211060609040501110403150501080102030c0301140d1a0f07 76
    0x5185010f071054242c01056006586807600380582c0603003130590350f600003e1500740d01c5801c1e03071070958881580f0380d0200d5071050f048200c1c24224002050305032160310428003048441d0201c1eaa400504054a00075907020580c826240b5040c51710065030a22403085600170720078178102050960040c41039071054180c003c001d100301c0c0c0c078121002015040001039650740d15401c1095101003809400200b5281110241000f0101d2407200201e14000400f1a0020b1100c140c01c0498000c0f5808070303043e4402d5401050b01c40c2ca589a5030002400c021000c0e81c0100000048031448040c250004041c0c1d046a008110f00740c0c180080101c2039a1844182801040640143e0f001407600d20f0b2007007400c1c2d0043d0040c4000030307101000c4643e44031240c0c06a0410b0b00c5101e1410104450025940240c03401b51968600950460604503d81d031264081070090380401c8100709458103141c0ca4910b502d4007240e400115021020011a404190b0361200342d80d20410701c100f0790002860280030b8100c1210b80712484039016 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 953206303 1250 953205053 953205061
    0x50a051e040303110a05190e01020a060e070f0e0a050919060509070803040902040e15011e0e03070e06010f0f02071226030601020f0a02090601080c090a1e0801090803 73
    0x3401254000744110145076640813008800390801016000c1c4041d00c0e140c0c2d03565034106400f0221000c180003100b00c01c00030600070440c010b907804034411010360b40c0302101190140c031580d03500d0300344550764100c0b560030f004460f80021001c0e00503c91a0148040820421254642d40c04041c1c0b5000860800150405014170340350025145078441540031806000f940c00307043e104c02070142154015840300d840d181c0c0105052040d0448400019003180a59209054145200d400a09105071f84001a00268440030325100100c1c09228150b0000b90012b0607036060030b444640e48598031030240c8426001500d4081945400b0f40a0705804184090540081104518155001101c0c5091000880e002150140240e10002007144c45007207028047e01082d03140c3ca00f0400083c42c00103015901081c5521141695015803200322003c0c0d0881003c0c80c00c91001d44e40c1c00358004003449242400b507002980c00c2da0001d603c465031500c030700b1742c560000c1d8101c541560b2844014280c4a1003240a404024100081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 953207553 1250 953206303 953206351
    0x30f13050109062a1112062e0b0313080a0915030902091602010f1d19080a030c030204030515060a0801060806010b070f020910060329012a0c030204050a05 68
    0x1c48036100301c041c5c140144500d030104041241c0031000750a564000c4041c4540000b024014003110a1070314406464640310107000c4d950700302e0511079406803040000114124000003900005480e81002e221556091060340041070440140b1549030f442c5081d00115054512900903400d406070024103440b0305807207004140c49140e591060325400c0d0341d1b03a1038803110600a580502c80d4407000500c1d034956a02080d21440b41082c560300549042e62004004202c00900d625041d07420119403072800080d031080c0040240c1c0280300e907800c0a00140300d42000c00e40803c0718018100d10030b140c01d5902d80b0006640d01155402d8502c540130b03090b00380e008040107208101e400760140c10f100340992a080441c0015401091040c401602c824a01680b031300c00074800c86805001d0814100c04024004036601c04101c40c3c1041c180c9102016070411004400c038183c0940f00320740c01203002020b2400c0c2e201c4008580352170190b180051008a004504140c006400001c0d070b4840c0c41e1081c0d004068141080d811040c2c0d0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 953208803 1250 953207553 953207627
    0x705100e010f121a030609030a1d2409130e070504090f0209010806151008161707020705120c0306040f140105010605090906040603081605030f1305010906 68
    0x910b030100301e000c288445074203046010304c1000c130340c40c10038034001c032524403081c5802c0000007401b5040300d90042020004041d032115450202c00c1143e521800c0320b002d4240050a260f00e600c14410300990000412126420088000d06420408072825400c100d60308183c4c100361030364806103003640c1c1c00c02c44003001f4600b442e800c1030f00024407492918560001560000b9040c11003038002690315407000d000c106100c146107030003448011040f1800c003418921454014182c060041034515600c1d68403111041c1030340143c011400d092021075072140c03286048030001b56030b400b01c3e1203010310034549001182c1462201080c1e1031030220000d0082c0031190364540b01c0c025156403606044038242c0300408030700315078442881154081c0c14250380312951350944100b00f002451002d0101441145001070030000a01c050f0212a5661015800e030398018000e03040c4203086000c1c0c902c0714490810002000351204840420314425900262a001c41c4540caa50341191420300d004040b9144802001c80100d940320300e842 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 953210053 1250 953208803 953208827
    0xe18070f111e010603170a0815060a3e070e09120901020313030b0103060f020315010f091e031b140105130803180f0105090f060a0309140a050705100e01 67
    0x100104c0c01c0d641c0ca07a542c02001102d00010107401c840801c104000c83c5d8880e1000d0340000e042d0400f13103200c80240c80020124031a050f02d400030b1003080008041e000d010f01c694507800803403003c141032480c0c1e0342c0c2c5444c164803000720500e00e0090154040105440003507051507400f401568005110500c420101c0b01240d40c40003203107605510090221001400c9031064040140d44a04134460395035144d4900641544d061444000039240188200010364400b420308a00c584d009103090f04810040700c1c02941d0344440b40d040303071005840169040814040001c03214084034451580035051140d2410326038684526800740031689845090141d0f415032250000c3c2030f5104001aa11102540c1d91801515544c846a100c009180600400483d149801c00d141040042c2c00e0034158502400c90000601682401c10031500c00c60000c551021840d1081c1c1c000d200040e07000040b082c0d1458143c0d54541e4404a00301c00b00c40e00e1040f404041154246650f15141c0d42c0c3c001c0d00e507aa0080554001034800d010000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 953211303 1250 953210053 953210113
    0x10507110910050a0305010c02011b0f0c1e050604051204050904171902160504020910050c12070b090105060d080a03021b0313050906100e100e18070f11 67
    0x2c0c0c000720f80c40e03650791100c0008510a1000048040d0300480207400d5a005501c40c140142020806002c11358100303413242c00440b0186014100510785241c000c04800c0da1548034483c0100540000381003250004010b4003560084040303603d041c5101c800541c80b84940d00403107800c00d101d540810000b4214003400c0141030807500000c1c0c2480c00405400707800d010701181c6000160320480041d10720700c5541c0d11500c080c01d4192415490314004001040b260390410408500f001400030b03030041ca0701d80c20b11004411182c0300c80d84aa84000c00d04002d00282c0003510b0441c125403a10000c01c500c0c0c03910106249005074050f42c1d07281040d0140340290000e402002d440280322002c04210b04d4042002d20040050b82c071a0211070710500d00780700520a04c000001c00017800323011140100300100390840d03441c205003541102d4103d000515030500729186190b0100480e0445010207541600c01e89910000348906002d5440c1c2e80f0b4405190b90403a01010b0400c0d49480e160001c0345100040b00344d84600c011241c40300c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 953212553 1250 953211303 953211331
    0x10e040f022205040f03080f150d0203030c01020d0b0a080316030c0812010f060f02060c160c1e03022d01030b01021516090e042d060504110306060105071109 69
    0x200740002d096480c11501114a460380c185481c1c101030b000b048242c0c024591100c8410540f40c90031071410701415a45003107201c1c19241c1c01e03c808541d020400c58203004c030300740025900d80211440d00b02c081e1100c0c48a0038810303c481c400104450b000082614000a0200c8034080740c0c0070a902c054903c2c160341201650554030410440d68409070101d400790086c1f00ea010300364091494100010502e02d1002a407404641001050109640300303903090380e062800c01070703415051800a203030018008545600c0190501004400403064441340204030741100d00960724640e4049001c28103900148802c0505041041610f05020855100707901803500c052042c0115500400c21240103c25080111401d146919400240e072040c3c0b94072082c010300030070600c0500c40440c246981c4d90b03154000070304501100505003c6034400400505183c2d4a01503030021010003007403d080c00e0020550a8280c0c00c1c900a20901c2c020a4455200b002140c1c14941c01c070030f0b0041810880000c004402c04082c25000a4600e8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 953213803 1250 953212553 953212609
    0xa0212090604030b1006030b0301090c180608190c090905030304111504030f05070905010f060c08040b04030f0201020124050910080d080f060a0b12310506010e040f02 73
    0x10220710301e801044907417514000c903482d00600605a41c1d00e1400301c0d010340d040040d00c0d40001c403c8a030310000d80f0501110b8200302132008050b040107080f03551145120b88203014a840703413810f41018031001c090142c0078548060762500141c1b41501d0001c2802003986e8401c00004011404580c2c50102d104001405081e07440351003a2442902c1d0000c1c0c0054400d240d00305041410020100030350030041905010070f12140d1f16059400709000c80d10712400c1c0600c03900b00c540c0020040500c0403030b0007034160000c01079200c90b01da003444910740b222a01e003203001d5032904c800b40041c8645640c60701c6058021000424141341041c0a2041c2c024002d80b081c0940050b00d035002c1500c0c0307020311203001114495500c000751482c282c803a000441002600c12405250014414070a40141108484102004c0500c11402d40c50322240701c44e5004003c0016120080701201d210705a00c200c0102c1c0c0c030600e015a0840707106903215800c00c51200c8058400030074510512080d24014109200e0392230484401603504224165 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 953215053 1250 953213803 953213813
    0xb030c0706060e2e0b03010b0d0b041529030c0d0b030604062c0303040221060108030c0d080118051f0b030f0c0a0f0806060c0102071b0503030a021209060403 69
    0x3c0543c0e2401a0842640d00d026001c141d0400310240342d500804000c4050f03180c0001c590540c80b040c01090141c50700016003651040050304038124a00c40904100700c03900b000501c0f0038001501d8010841e41194140c90748244003088902051501ca400d00303035502e15200c08030500c0c141d82c0401070700e1040586450382084181d4003400aa84518094100401c00b0720804070808004080b501b03203419222030224034020400800070035030f5805541a20b244e2280400744001801045400302009124411070f000402c07201c07000300181010903254011600d4660312403400361441d102c01d00075025880c3d403c46034491034605e5a0407480d00400c0d4080302550030302c43e030a00d40b882c03840e403a04110001032f000014031042d480d80c0c07003000d50301480704000c01b4244403100c000140701030003401c004010005941c02003034007039545101b100e903242091030085544120300c1c503029284820100e560654013072402400546420040304998034804258041c0134055440c044004198025143c00381c2c10100c10b20010001507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 953216303 1250 953215053 953215079
    0x122001060f061e0206010603051305060a09020111150a09080418140a050c0d1e0c080402040c05040e04080d0b3c10030b030a1e1103070b030c070606 65
    0x112aa80800d00c41c1d06140c8040c0081e2914103100b1404000380010607206540490b620b410356085280120b1a5140c1c0f868100c0038900994008d880c501800b02441079000e0030380e0085400038400e132900c1070102e401d00c1c400c6403101c910914a100d02d414400019200320200da00c40340140d8800e04005040940342c40c10300113070780c1100d41c110701001d070f80320b806103e202050007c10342d1040640d0b03014411407900500c500018007030303841d070b4000c0d5984034151442c0141c040e40d145006443c44590801030400301d010000c100c0e0700c060364242d02540c50540441c004510800c2140d00b680c00c90380f0b03200a03d0701c2d07035035820301c1e80d038803003904100c0b40e6a036503249001c00d9a844500e2101e61500c17008460300701d81122000420207400503c01c075521048200d1100142d1a2151001a8604241400241601080d0100341801d88207180201000c40b60003a02d81036080103030040705814010355410040c2c0001906059982e810bc0c0900c000f060001c1c000103001c1c48000c4001c040d032034428135020401981c3e405401c180c01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 953217553 1250 953216303 953216309
    0x2030106120807031d01050a05070311060a060e0a020903190303090b040606030615030c060507050c04050117120a0c060908070f030305070f1803020f0607080a050703170412200106 79
    0x4151061542c4611649040364162000301c3c83c03401d1070300001c1c04601c00d88c1411307001d0000100303141081c54040c41c4140b0142811340240e800c240740281034070740100018003038400e2210f420300124000003114420340394070b018003030300500402007071401402e003520042000f1001c241d100e00030500040d000401441c02903100f1200822501d00703510b414025117003204003036000b0404441e41000400c60f040081c40454895040850341c0d0b1901d800c20074203255507280355035003040c149000091034000c150054900d0052800548155003d0700d40c4102540c4113900400c000503200c50b200d031001c01c0007940045212807095616525203117056035080c0075104002400e8010aa44d2420803100a4108036040c029451b20320300640814407000607002c0e65103603400080e0084402446114594595004440195401540c015281c0c0749401d00249558003030b2038102c0000b06c482584e403a5102c68440018000d0707500c05101046a00d2851040302c060b03802005548010701461654084d02c3c400b84078074005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 953218803 1250 953217553 953217563
    0x3030201050402010e0405091203070207050301090f0605011d0a1d0a0c08010e070f150c08070605070314090a120509040213080c01020a0c0b0703090308120a14011406070203010612 79
    0x2082c900350002401c0c411108000500035030400c010800b0200020849490071100d2400326a1281c42e4528200e00e011b1040d0040e94043d0300c0d01c45200d0038081018020012a8803c103000d000c281c4c0c0348d140c0d4544007070b1450455035050380150701042d0408003580261100e12000088603070700030307545000c003468000c01901c1036402680c078400c00d2040d04d0083c020a8903421742d04008111544c641151540a040c3c0c512071584084051054604007510843d4010010b039003000705070351503d456080410091005442642c04203103810401a03019501030240d80c031504898011302103510741030f198001a0045502c400c01000f0b001c114014460b600c0f403026080406001000c081940c0c24104a186408801e080207815544400811000114214030000a0f0b03101083d0b83d6450707180600d410f4070303c0134803500002c04840010607954841c0943d01c051900c1000950000e000075201c2c5640690010800c0c0216000c045003910004420308289009104c0140301a0001561076910418000303180024141140c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 953220053 1250 953218803 953218811
    0x180b06031503010c260915101502061608040303091b0617040803130f061409010b011d210a060c02060703020306030705121c0315061107030215040b0403030201 70
    0x310b410244610a002e4590782082454403408000e9000a103c1c407414002e1030305000030009401140a12a1103600c5030052044007050420302c1288401c1c1d155070150110801d1580d04545035a4400644603000d20a03040f181d0400032201102241c942c1342c01042a01030607103d21003140094900b485c550720314818180700840150904200420340c1c018441c0d0440c0081035101440041800002104d421100d5a0440e0400581d28640401c0d02809000c019101d68948900321803400d468000722481654114000c0295004050056480c1c8940288108440c4001c541d81ea0043c209000210013190802070280003441002c49118500051494111049a00c3d80211280c86804002d1641c0200113420298114a00300380803943d1100c244c441c3ea4401c6030036080a10720b0300400e000c00041c8050290b105900e110304541c010300030b4403200d040394000180e0303881c0009929200c0e000001030303584d646000e444e825165408018000001901010014004000c00140400f12070010001140320360004a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 953221303 1250 953220053 953220091
    0x9062706050901020106060e150a02150c0403020906061903022a010f06060801030803060409060207080a021501060c0506061207180c090e01080a0b0c0c1603260301180b0603 76
    0x84c00d60340c6e035600040031b100300b040d100d4080d0364070300f612010300d1062054484c6d103407014603034102d00d010952240e0300949900765081c401d02020200043c000c1d01e009490b00304d200d071610340030310105104401c0308041001d09040c801c1103851003034006083c001c0c9042c260400c03420488540030700e580800f5484c45d030242e55400b2040001c18490181d88010300042c04e220403690b00d1074444070301610000300313660f105954903503416080020540c191101e540d001141c80d51502c505200196440e00072000c10607499508100000d6028402d0540c088a10740c0103015040f41c1c1c403800c0c00e10024a403405a010100d01a080011070040c0025819085000410303001040300003d01c0405402089190405400511002d005200000002070707848010343d8000d8a04460799208110000300303002c1c2000c01100360060380304142d80401080d01c0352050f207000d0a10004030924201c40c03628100d8100c03010300ea20000a10040041424007206100c92004008011440e020300d180043c046500c00c6400014501c50040c1d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 953222553 1250 953221303 953221307
    0x1b13200c03040e13080a180906081b1203091e0d0339030806010c061a090a0203100626010b0a020f0d05041a0904020c0c1f09062706050901 61
    0x1454000d441c81c561a0110003a58803810864402c01c40401c0902ca01c02c3c140707d0300c2490801e50000140807004080005c561204059510741c1c51030308080f4a98900012072034014606070844802c0e5540000065140c20b01c1042404a02c502c41da20704607040c01c141c3e00f200740c5916115a101800c6e0b110f035807806060203021a4090f4144100041007100ca004c0139010203003c1c0700c00107001c04039901410190101d80c0c0b0b4100407a0b5001e034400340202038500f40706010981c10500803903038080c0401203c2d2800386a540d004247c00700c0c0011112140d413039040300030811103240111a1a07c055040c40702c802000c0f803403072410808140d400e9024000400000609442199051100c800d04c150040050000d0f04a0f45800900b14021030181c446030186400d812034645603424100d5000b910094800c0d92200720181042d51a01201c0030303440d022b00426162400c0c2007161400c100d4030a009600d0f003a5405041c8401201e440303020210301c020f107400080b0500000030150102d90010801550b82070368070340081d400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 953223803 1250 953222553 953222579
    0x10302100206091f09020d0b0106030f050c16170301030309050f03060403020706031e0608010f27030807110f0a03022103010b0a180b0301081b13200c0304 68
    0x380e4800c540120080c02400e150114070b2442d00310f4005860004604da43d00c60300024082c3d08802584901d41a02c94410010244141170480e2501d440070010101c414840301c00b500d00c110340800160300100140d003458000c803010380c0440340c040c0310012030a1443d01e00e41403803a0310030f130000e0f408502501000c02161070308810517041001d0a0b0041d102604013541c1c065540d81d0a809003809154803884a264200fa40d9800e240390400960420b004480d6100c0703180b4028441750303006460040c2800c2c0715507400c58142c0803140760640310302280311039001a80c038221400f040c080c0c480c00421001340754520b03a110040101105403a0101b01415034041d141c54043d1038134600d084555110110034110061300e041c0c01c41504c0c1141d401e0000c285ea40c0710303159004c50b0082d05403110f4142d02000b6000200d40c4210440c05981a035018004941d0584200c03c598070440c0342103400a61f0050b00c280c62204800c5040c0c1250500140080c80c0d5110004603c0b501c001d20f0304540a130484503400403a04000c602042e0311 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 953225053 1250 953223803 953223829
    0xc0311041403010b041b140915190302041203030207020121021206100207051302130f14030102040e0106110a02060d1a0901260c1017150a120503041805010302 70
    0x4040040c0d215120904010300d51180c00300c0c050011410181b00c3c1e1f2507001007113944146c00145403152403a0488004000f907000a4603100c2c0e20703030440100110582c0640300f104c06889001c07e140890300020f0303038120041e50150500300c0c1008800c400c1d07280803069040750564412000342000d40c0b11349074140c181c494610300508581c401c82d03141c0c55024845030081400da00b0303920127480150140c45103810b12000f030b1160b43c0070107a140c1400000005e4080d815030310541500c1201c414420301100100401d03080c1e001d0b40c003800100300502d00c0100126401011a04103404413101507031072050582c0c000aa803a004100091506919078010324420f0505805410400c441110545603e505201e50b12045102ca042a40d103102400c0302c10b01ca07a503600708840c7c0345000005040f00002030300c94000030250f00706416070b48100c01088000c2010303282000fa10a01418014101ca46081e00d029540004038960840560b25404100310100740310b00e50400340120300511400c0450315506d14410301c5601d05ca210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 953226303 1250 953225053 953225059
    0x115361d130c0909061803080601120e0615011e0504141c06021b2521020f0109050d06020c0601060c0b130303110a0305041205040f0302040c0311041403010b 69
    0x1512440003582c1d8040d007906035482860005011030403498030398002c042a440303600c44516000340c00d00030580e2052006100b90b10a130b940a401c1c44444140c00305480703844449130596045000010244420b202201c000c1c41c030705242601003030848494904400e00800d2844000540006040c0016400b40810003d065000d0b01c245500800b003100000741e0045001d801040540c0008620084005001c2c0c1d444121001c181583e043c4d640d00120189030340c0701d201c000c03c040c050030715000441000c0c50f814180104401100c010301d03110703640d08002030390a0101d1468103000400c00701207800c0e214881e4501401d807051074016900e400480d00a031501d00140c0c45a010420740032003580009114115194201d0034480c81e00360352060602e415005006d401038040c103010004079140d00003960640010340038500440041d686072036036a0303040754948158050000350f20a694420401818150300c40389070640341e0700c2c1c0003600f0a40400131130340a6201d540244502c50f0f40814001c124a800c0c0305040e0000303011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 953227553 1250 953226303 953226331
    0x1b02011b0206040f0201030b030607030b1c200301020408010606081504150b070606050405070507030908072601020c0303090d030b031612050c120f060115361d 70
    0x40c00c0095036100b004100600426141d4400421039019810080900d1802400e840c0d41d4507016a00800401103001d03035611407851510800c0d1501400c4039203882540c0c20194400100004000c59a61520783d80101ca406650800c000a02c05c0028441c0c44064000c91352501d1460034400c800d102c1b40c0303103407480700c5204518028581d0021951030360081c0803110b01022080c0c4400c0c0c6410050b000381020351141d80c00604010412039100e42c00030060200ca03100361200c800da00e48812425940305031754010b00d0302c5c2821103171100326140c2211400824a01e00c110001d480e10348800307061800d681003510101500c0c0d001490311011550035014207400704005038020625207683c00340300881708242d48036000038440f0200c080702c1805010b000255000d8805403240e446c2c82e1b941c400e40c581c0c070301c2c456100410f503005007000451b03450b0344203440320526007035592220360444041c000000000c0c1500c0141e489a280b0001c0301c030711303101e80c02000030082002002c0c44070040100c0c1001b414041c802010304101f9400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 953228803 1250 953227553 953227601
    0x1d010905280f020729090c1306081204030210030225020324060a050409081b070e011512020306280902120405010b090c071101050702041b0201 63
    0x28207100550380d80003001d030901c861080855550001d20000d0300303002020b40001414000c0c0003002440110920745440c0301005140340d000c816000c600107172050041d40d0451003500d0007618111401050030660340400080c0103558008080c03a00205804807003851501042c10029850003544c84491210f0700e00b0194a072080c5800301c42414200706010040340c1c0c9034040340710155241007040c55410020a501d603d01c2d18004c20f03540700e00e24070456401c1d1262032540c1d00403456040c0b034050512010350001c0100c1c00d005072884000c0c46d01c441c00a03600c08a11517102c0000d60000c6030300140717008107045681d200840c003000c01c0003449241300340001d02c0b8081c0100107110544d2615801e11f0b800d10000e80f881e07425410b0381c403015a8103e0259200101d514004941d200a020481c9032042c0904d110700020800b00e85d102003400140d0304229040d080e580740902c80c82020481c03a4008900251051500074905901540020100c4510407074071b0480100040c4500c5032590240300b025100400b80e0b00c11900504 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 953230053 1250 953228803 953228821
    0xd0515090601030b010302150418091e170306030c130b010815031c0302192a0b040807150519050106181404151d010b0405060906091206011d010905 65
    0x4e0107120003400b070040149070304042c03284441910007500320130164442d003602c1d05100ca4091300b8881c00030307208041464820f404141c508030288142d66444420715010f01000e0b03483c480c039600000d022540500408450b622103581d00620071609101669000507001040030004107842c00081c201005458035044e03118259500203030041e9042c1c1003105400034a455208120041e02803103800c01a4500c803000540400c50b00401c1914000407103100e8042942c0300d024803400b40c003c0d0f01e1405003c0c200302e00b001c900420310030401003003080d00464000d02c450b14a03080280c201c4004a40400c00e603000109a082e06035418051240100600d01c0c00ca070340c01c400c0c55091000070410307105100b08420103407055402070322150845000003000382c1015260503503d02e410360740040521221604040501c1c00481c2c0c6140f10303030561301501c0000d04801c3c240f8a60b001400883c1d403240c0a1070707030711a06500c5504043c2c0401c00c900340c064480c2e0b80300208102488403603c02c9500701a0003100c4080d0038001044039041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 953231303 1250 953230053 953230073
    0xa0c090515150d0b0a17100212040821130b070809030306040b030c03030d020403140303090709050702100e070536060d0506010806062d060d02090d051509060103 71
    0x5419568581d54883c414400f00204500075000d0740042c4c501e48001041c0f05243d0002214414500541c3c01280b8000c06c00ca040388104100b21404008810104000ca412003010700007074062a68005006600d00c0d109803648002221001c20014122000008003e50204201e030446c640341000c1d0000e0824070700e11034a0b408010025400340780e80714805903c2c2d59081000c4013900d0400b030180c0360364458908000010758070074001601d11104036400c42c140d24000004580c404d02c04440500038443c28645800081c00c4040c00d000110b00c2030b07105000f03440400e4401c0800c9058803000500b2402d140000b44869004450071101c80300e051080080d400e4504441c11980040e9107000c120801c0e0750340c0340060b80210500101410901c10200041080d00001949a0064100716054404030540880f01601160030031010a8074940503484481c450602101814600301c402c4805030800c0c4001000c07035982400700c401515076902c074080c401c0c4051100083d643c0c2110b05000a04101e6040da11009509 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 953232553 1250 953231303 953231329
    0x6030c0903020f0a030b010810060e070c0b18010e1b01050703050d0c021507020307020414010302130e030d020c0a02090a06030f0f0501150909030e300c030a0c090515 73
    0x1a0400c90034110613035252442c1034041c6a002148450360350b15550b200e07644034400c1c2610452603107004030226a489170071130444d1013004603603138002034003495685401d0040405409400c000700010116420381e035083c09400074005020004060280030100c81c8241c3c46400e560b0b05040c4001084000e01280e4000101c0301d0a1040e4440800e44803902d0104034508018064400340030b8110030240316007907a020008000a50003203505104d400c4a04041c124121002e1000a5000030390300b6000a002c4502e810501205564406507030400d00b100744800141d0313001003d01c60240d04074514000c1103107010f0910607003221448004100407800c6540c3c4072200e881000029101001c24842841001003d41080c2c600c403200a04080c03505a0350103070750018141d01c60b4120003088034090a4507017414400784401c2007218a03180c41c070100c5035442e07440c51500a072a140001da0700902d0284006918100603030300c41d0074400d411050f1030360716014a00301100c501510500c0c1a0546142c182c3c07c5a88459000c488 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 953233803 1250 953232553 953232559
    0x3010609021c1a0d030c060f14240306070906031a0d0b1f0b04090f0c050d0c12020c07050316050f100c050703080c1510060c030c05070f0f06030c090302 67
    0x202011055011140f030406100e540d0340034400d98800800c0681c412400c007609131242c07406010300d4a5600317064042d2240782e5040030300324000b08001400300d0302c2c071040e0102106103a0666141c59164002184c10401c0403100308003c20f0840008000642d80362041705205500303401c40c40181412100000d00030100c100d00a00f04e141800c0c00b207001441500448500b0150002c41107284a948240048a42e0407074412100280d19240e200408600d4a00805440b81c01a40d105840e20071451810300081110341d42c103c1c10401c0794075100981c6400c42c4001d000260065000704601031800d81094901309144142c215401c0705c00c001000075403580c1e58801c0015908403101c41c41d18212502c11038404107030102c042c000e803150400010601040a00401c80d01c0f00e003d065520621900c555602d00d411305883ea00e02c0358440c04000c010b410320500c096000e0b103110b450008400c26945d00c895113018050b401c0000d0010120b68100182e460380b00184000704082e040034070081030026805032020648d4400a80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 953235053 1250 953233803 953233811
    0x9460806040b10080613030801080c090f0907030209180106050a0b0d02161a2202060711030f030301061106060904080d0b0a0801111e090a060509131a03010609021c 72
    0x241e03030400f001a0360140440c4001c03107400f8605011030741507110403c80e040c1d0216000400100d0401000704d40b511118101801992194691045c0c200e003100c030052000300d141c001c1980200040e41d6000d040d5016006018088807000381c8495140c1c2111803030781c00a8440d0401030010003400d804541600d00c5c858107000c00684686461081c11101582540c1c020001d4840034448400c0325610720350a03008501e2103240e42d460003a00c0b48140108030411101961081040c0440000544043e92403031011101070241c448020174030480314039503042030300000046180003094001c01d0b282004103035804841140d100c1c106080c0307511803041c0703807260b104149640f54a07184900440d071506030703010b0028903450000b0881059514240e8005404c03880a0a4203e0304403002c05100102d44401c1c0e0340c1c400401841c4101c1c1d00c0c94680280d07140d40c0800707035441d00080c80072008040801c40340728400c1c480c2841e4460b448445031202c101401c48800c0d411208665205000c41c440d15200d440d04903007801000700c0002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 953236303 1250 953235053 953235061
    0x11404120e04140406020d140c1c06030b1e06030a1e0c030c090204091b080c130e1e060117070c02011202040f03021e030a0809460806040b 61
    0x54041d044503c20000c107a40e50b10144010000c16a0060100001c8a03804002601203000c1242015400307440d0520791800130300201c0030951115202980c4948080c2d80090311558a03528a4a007420442d1410309201420002407881191441010362150007103001d4441103407203aa40c2015030351810304625002d4503199070102003009060f6008065a009000889815558540d8030080e6201d805014041414000504501c080b00c0c0706854000300d481d2a1045035039503110f8003812903001034682030082c0803080700000384002d081c100980a80d80c0404002022442d48061410703184000d4100e504100c0c1c101020540000d100d41400d0304030480380360144200f2141c0c00120392810303507100d4400f1030b10310001d4005100406c54421000b1a403003940c1500501901103101480309140d030001c150550400960240018400e03c020b042e80300c001801007008150f5004102c880c5401c0c40341801c03082040d58040751300b80c401c0208480fa07104203061600340103802c02004c00d13207a100c094001040500f44030041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 953237410 1107 953236303 953236309
    0x60a0c020c150d051f090b10051204031b0b0906041403040f050910320402131703071202061006030506060304170d020d0e011404120e 59
    0x2440d00f031040383c20941e000340100801824240400092812091103940802805000603010000e1100e0045050002c20700180596a09100e0140611a0320b8649414043e6000d941490b00c41e2810915580301c0468490200004000041d03040030030500e500300061981c8954000c04006856120258045450b4032860082031881c0701d5890303081c41a410409403150300500c0380290380712515a13a500390210000720142c60415217440c0c024080e0546145011076860702c3c0112021817824120316151540c46541f8403c00040d0011001d540c13041c00070500a40e00600c0c2c014a102c0d0703a552002c00001e4a9081c1100c120011b00302d0000d0200707440b4070030300c5201c0c4104406007441c0d01c0c0d611180c0301c6851550b46001d6000801070b04006ca0031b900d5600380042e0401c400d040001040960054520343d003511040900745001f4200d41c0204804615216112010120b003420074000700c0c9240004 = true := by decide +kernel

theorem cover : BRFrame.Cov 953057553 953237410 := by
  have h0 := BRFrame.cov_init 953057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 953057553 ≤ n) (h2 : n < 953237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
