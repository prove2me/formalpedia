-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2710
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:09.259983+00:00
-- url     : https://prove2.me/submissions/aa69c8ff-1176-408b-979a-63991df5472f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 487230215 ≤ n < 487410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 487231465 1250 487230215 487230221
    0x50603060601020a0c15030b060703180b0c0703140c091009051e040f06060f0f090506010219081810030203160509010f0503060d080c03032430030a09050112 69
    0x500e40c000405c010280c43c00d40c03554020001c0c440700c0d0f000e140d15900814415540d890081640500c6900d0341210302c805034945101c0c80382c8540043c1200542004400c005403030010f4003604030ba80c044e90288054a0800ca541d041507881c1c119142c010205506100403028100100016030341512410071a60340d07203050b981a0303545901048070000280401040226030141e8030303064600d0141d8000329000d80e46440b0078406058960010382403140070710080c0610221805000e0b0011005d200900c40c080b00e00c031003170000c1181c1210052408500154000c0c80c0c4407094445103070600000c040c000585403502024020798800c81d09805129010407021403c14020701c2640e10000d411f03952101c07124001c0c0c005840681c00607101036400400f80511000045004000701050713032441d0095a01c0e407c003038910030720703090307a6104a42520990300340c800000e440c0c8231000b050249942d010070100e40d4410120100700145030351101d202d03020000d20040c50343c0e00140d10302d04454080ea039060034460003040c10811 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 487232715 1250 487231465 487231483
    0x5040c271a010c1401110c0c1c17070f020604090c080901090308010612021b010606080109050c070204020315030609031e04050a0e06060c16050406050409170c010b0a030605060306060102 82
    0x2007882c2c1916100810708448034501c4c2d0144050000994040e2503480380041d81081102c070800747e2141b02a558103041c54002c00301c041035a1411502c0071070407035403058110f80034034403980450303200820500b040c4000540403000b5107401400039540c4946404804010b00041c0304d01c4000f203404000400c0350098140b080c041030641555030000301d41d00300741c4111440a40c503241c2c402d40d15000e0100352407a900010101003010703403c030000034015103840c10207020500140d0003100190718050802030740c2880c140c2221805a412a001641da03550514144102040f28003110780504c900020080849400402040600843d80510f00c0108840c1d020005030321840c010650006111103017089941d284800352504403400409050070054503840c42032070041101c801441c40c1000000c20442401c00c2e11607100646000d41301400400300c2512071290140742915162000040041c034903081602c00c2d40031082901c001802d0400da1503483c00c1440251809071740c0307103200380260400320b40c196000040701c0c2c134 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 487233965 1250 487232715 487232717
    0x1e0904030302090a0f0e010608180303040f141608061b0732060a060603020c03090f041116021c030207090507120905030a0905100e0405040c271a01 65
    0x425a5180d030118041d4100c00d1030703982c125a0902001c12402e248121a074003520005141c038000d0340c500340d4010008000078054020300300990028000004000c0122640641c00c01d01043c40c6011030b02c0d103440c00581c800741031601c41c020f00d2103100200c0e003c4100c0808503481c210032644940c81d16212041640d40c02000d00441d00c0d01040301d240083d4844080b003a0400040b440440300c0c038003441c5c1d120340b181c5002c0c0200503540c00ca2030400c00700154911a1101515051404504103541c441c1c10a0b66031041a2245205265103135881c040d50365681c001d0461140391040c0786841e0a45088075070350080da01d180482c466544030f0700d5841001d55403d00c14510b0340d015030003030200701e2900c0d54a8008120160250041180360404036025041d80e00505003034620035001150795031034003030001f0301c8943c2c0ca400452040118a01005220f03a10040901c2c01c00743c12180010070340c40c1c03444c080b418211990300140c1c030030355241000e8a083c180000b60b001c403840c46905c18800440e031481038540c5400c5043c6518 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 487235215 1250 487233965 487233979
    0x41d0a110c030a2006070816030c120905010f0204080106210209010312140310050414270a1218060318060519290103020c0303010b2508091e 62
    0x180c040380f04c1d0354200030018120091540083c00030760400d041100850b04400800c030100144a4a44a6000405280d0317900c0d203801c00c4010600103005004074104482c1841c49901e804804060201c00e5010340301c1840d8004046643c0c990303030340317500c2d0103083c1c80c3c4550310600313030882c2a4941010003006070407035090b8010120340c2a40c0c2140d5030f00110f00d026a40c00d00c00c01860420013052050071710000e60203008040f616544e002d18040411003510f24041e4000c0104401c035040c4960503030119500c90388510000000190f014203c1031051400e0903035080a45006081350b121210036030050954680400c8003c500c0140c261541004ea05448400d40400b0306e6540408214001c120b060384400d0b00041c022080801c0b8070034844401045c0c81c400d0000404641c84800005080c1e6010603a4103007401c4207003401c1d8101108160107680324001449804400f0400040e4100804503030100034580710045403a5950001481c200108a50060010b25010303e840c1d4941151034000c002031a01c0343c0d9801400e103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 487236465 1250 487235215 487235227
    0x8070b030112050f19021f17060111030d0c08100b0418020f0c0607091a0405040e030403150606080601032a090909150506040608071406041d0a110c03 66
    0x8849a080c4002007a201d9000f00199200034080031700803005008403070812104094203030700402400100f0100c1c0301c115046000c0101215642000c0d40c49601c1a40d8950801d0544d20900140d50304d407100c809083d8140000108010440d00643c030070440514680e031544156612f8507080145c01c2058015140c4181043c00100019103000703201243c18a5038280140c00d24034003000c003070080d401c00300502030180c1100d070400c44010703404a0040000d00c0508000c5010140d100782c1c0605904c5a80152800703240c444001c422110010422034005641c405000d510421402220200800060081c00c0009200303401003101584240519600e40800488044603003140405062035000490320020500041010000f801d28491007400c20440c05010b113849428441e4491b034086440c01040140309510f400002d01c2104400900ca0f015101c510060544180d94500013407400e0280e5400b501d5250100322202607008082410b00b409150924014004c85100840960700780c0a03080c0000181d80c414004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 487237715 1250 487236465 487236479
    0x60b09040b040b151f020f0d090306021308060c0403050c0907210e0d020124121202010209091e070207030b0c07030c050604050307170708090d030e0a08061008070b0301 74
    0xc00303504807404c0700e0700f100c41c0a007200100b081d0089104d48007106a040325015000607406220340039992584401a01098540c2540541810840d001c05880e01c3d50122303500800345a084014805441d4040031521149030442101440781d0190104845a000d25800120581032215105010701d11503261204202c07030207461001051020b005a002068441e02d0fa02243c400030b01c400050003c413039001069004c010010452140200401100da03169168401c1001d00b40d000e40c200078031135011002000c03c8001010803400381c020000390603071104010041c40506100510f03542030140c01d411a8102950b41c0742e5040e078a91b5094880030b0403006084001409400d5000c0c010000c440c403a080610300c00c5003944540c1e2134040c0842e011181e9a200103261030a00c2111454000038207803843d20320b880e0141036650172045000c0e141c0e11500440040103a0703020503004070007060341c0d000007810b01c8894a60b558403407030340d81d0400d9807001002190420041240140410719200740c0790302030043d62841c0d2030003003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 487238965 1250 487237715 487237733
    0x607060b0315010806072d0809010b0d05070b03040302150c0301090e0d0e041d0f0d08060a0f0501032724060e01030b04020a0807060201020a0e041a19080d0804060b09040b04 76
    0x2c25603400303c00010003020011078004010402591f0740d541b086140b0703000d00c0e010308440e1107a80a903c120904151040001c83c0020030304107444242c0d400c10380301d44443c507041e07183c403000c074105104803c00b4000b00048204003602031412121090820f01689956620b12a02d1b514180d034000002009400450341d5424550420105964001032440c02c0d1103800c05007505007618498103003816001a107003525002d90042e407658100004445034000039281541441021001e48201c41c1410340b603944000e483e0502280068200c602100c0b40d109032845803800f00109641e0f0760b103043c81b00360190a11108001244140400e8134254011500305900356200e000c003521009004aa1041c856000855207440a114a00042c0515000036031920002c04000d06600c0c82454001c3c05285050308469004070b070b8018070b5080607001d943c0808208043d21300a86900c22a0300140101d06c20303107005100300360f40a8031191146019039420428242c6480402c41c0030142039502400c41c02042001c00c0125000c19 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 487240215 1250 487238965 487238987
    0x9060b0418110304120306091a041a120a060614060a030e120c0607021005090a0b060609040e0d0f0305220203100612030305010e100302100e0913021008010b0a031a0607060b031501080607 82
    0x640416402f041d0000211740e411242901e940d2608412403290030440760340241170203854000b1171059000700403008074169000b1040440c0800d80c440d01040c4840d01c2c1804940500502c0146581d0356044058102c2d649a00a45680c2c00602c228410814a0348aa100349402002601c0c06069481100d03141c859103054083c0c15917034403900030032540c2040c4d0740e80c3c03107004001c405400140040c10035044000d400c95802c05080b2040c9418001004500060694040840081c0417588040b80500307002003403130301040302c1d66503030024501140402c20070b90138030900800c40d1103540c0c00d00c1030780e88401c5802014035003a20b041e020740d03031700c401e060005207000d80d80211060500d00c2d005111581e1600000c03101613049c0c1e500000402800c110310254244290185503260740740c1021501035240003c580058850714110301c04255690f040078861840505c00c035050f41c04001d007190340b83d0340e140c1000d800801c0425000f40c480d12850300c2240c000c00e451800349048642801c060806a500c0b00c1c0255014103480c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 487241465 1250 487240215 487240241
    0x30906050f130f05010f0e0105040e0c1b070f0603060503060708060d0501020313140d0816030e070b0d151202010819051f09060b0418110304120306091a04 68
    0x6100c1054400e11680c0d002d00140030003207141195502d8603001514004208680350308014400c4641904c590b08001101e040b603100c86040140380d030b210b11550b061070040300c89100201c03402aa480c40c0148000070410195000340d0034107402561b0b00d80041e0b046901d10320401c0d07090380142001507003c43c0124449548048003400d01054052965201422a0310803078505440c03541c4007040c01d06200410004908a04030380c00201040074948101030701c4864020f0201c600e800000001c842d42030b1080c0c0244032003092030300c11141c06645802c0b9901040c6c000580340700031545451014400800111111400c0390313100b1b038502c2c0301b01da059001101c1016006201484200300800c01c60140103843c856284244410200071445120f80d066034004020f181d0710008050b030a0800501004010307208031400c44244c4080d4442416440e9803580242ca030703040c02d001e5602c402000300010b002c090103240f20a100b0a94040046a4444080000f01d69688010000b1580d5050031200f003401c05a02031104449a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 487242715 1250 487241465 487241467
    0x2091909050f01200f1902010b0310050103020315160c0512030c090108010506040810150909080c07150903110102100507090e0f040812040309051518030703030906050f 74
    0x10300e40711107103803030456036500d10a0b0b9501d00f01408407440d108102401d04107040d50b16881c010500b2289072035802a0928818409140f941c172842d0035000b540901c400100241c184e41005001180020042602340700a9000340074040c0300d07016480c1000034040c4035040c0002c41c00c0300102a4001200e000400c400c00f1207040c8524005e9000001501000c0c1d8481c0080004071581c4404036000103224010682c0514054003046c0f10600030b4100202e03501d0b0309401200c00c0010079008603030341c00007850703081d6012300c41043c504644107041c489444000c015800c1003c0403528003564428907850750070040360740f950004000300d07414400a01c481c040c2810f1044d051040320a0605181c04100031907005996070340204950075020455071560032982584017480c4404004c80380b4003512001d5141c450700c0700108131403546500290405004900c0030f00505005032030080302000418060b01c1950202ca004a5012521390302c08106140c0040c40c0d00c2500c1d410fa07507040680d85004420358190700005d40340b1507c80c40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 487243965 1250 487242715 487242731
    0xc03040804150c05122205061e04030b09011b11120a03021e040501110105090a0807150f0f0b041503080a02030912010615080c04051e03010e01060611030403020919 72
    0x403040001701003100421200c83d588001c240d040c0c5d00c0303008000c0c1204001081c09481005240e0706ea8050380c85884a94480c06502902c05404510500c070315000100000f1261090000386c01055014088000081520010483c990742c0140d503552521414000035500c40036250402d4011000604074a502c20b003405410a10380c80304940e504003101075084094103010030308111541e441808100040c00000c002c201e40d00346115200d0312030512140240c202500010102c0c100008030865036a120710394401008503600300280b42c405480702045245e50141804880285454076200d601c80121380c400c98602010703c0d6075107182c695000180a1000e43c00140030700381182c0c032454040c41c0700840c50400020b2031410101e4011680046020b0181002140c40c204000501da000464040c0d81d82101c1031400c070298a400c50b818602d6006520f6095401c00090701d40002e015008541541c4050b2a040381e0f06106607501682da004611019500821140120320700959003c039103448607140900200d00d044c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 487245215 1250 487243965 487243973
    0xa030e0102070b0912070510021602090103080405010e370906120b0108160612091a0402100f050f090f090907080606041a0f030a0b100e0c03040804150c 67
    0xe0489071007076500000f403008110340340c1002c0c410590340344000c03022907081c400952030700e80e07950840d450340c04003041d40004c803648921100680188013581c000c004c07014540c0c580c03412203203d820a100342c0d0700ac103161340b001c0b00c07441c5028a045060401900c52005440704490507621000b90401002c40102e45510f6011402c4203060066501a14000c00d211011a440345400562031034141d003c4202034000c080c081d00b65141c2e1041c00011180c251230108290910751903032030700900700b2a00040c4414500c003441251218400c016506c01d6000701c0d03080c21107401c201c005542408075065080000381b07040050b0f0f100000c42601510744175202030f0900398a040c030300021804142d070a4600401c9a0b209800800c0450b0f41041026400002604c05005401c1c51812100503012070142d8139214500d8041e0980c01920100304c2880010b4000464826505220308010211100307806088480030751040045d030050020301c1281d00032544804202d161038a0a0f07842104014a40f50000402c084848003c0c041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 487246465 1250 487245215 487245217
    0xa0507060f0b1c03080606040f0b0a090806160f0206091908040b0a031401060f0c0b04060e07030309050f0108011d0903160605250903030e0f030a050303011a0f030103080a030e0102 79
    0x520f243c19440362100d00c4505003d8420b1000400181c0f1402080106001400005007603000300d0384041d0400d0f0700c811100c803050720032003071a82010140e0320405041025915081c003c0001c8142c0a440710741190010a9040f6140c0104071a0342070103a210488000070400a80c840c240224010714900e4105038490b0703d50303880340c2d01c0710882e0b4000036151410024544409003a0900504050038240c180710803c00010303000580180024150201450000d8113020494101548000e100d00036034030002c2d128a000343c80788119019403801800d00380ba8500f4207500400c0028160781200d00d841e495464071400040ea036250041120f00d40b80014000514142d2052a040100e184580d002040c645040364103108441940f005001e2003220344025070807480d030484044000d41c0d800d4904100500244004590800c40501a00d6090701c5030050302c405104c804409541030310400540203600c9205494421454040c440846d04011010401080081c1e1000c001b0000394a0609000c282c503000e05000c03e00f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 487247715 1250 487246465 487246489
    0x30213051b030621060609010f03050d0e1c0f0303050c121314070e01240f030f110c0a1202010902130c0314040f060b01020f0a020f0307030203060c0a0f050a0507060f0b 74
    0x1340e4000b1090204916100b29928058034450341e102c0140c600d951100ca94a00703035490340000f4801c02c2030400a29480f80b82d4600c00c4450a605206041d0710309192025510a420308213600007440c0c440030038088941c4100702e0382088295122050591940c100c0d01601100915007101c90356200d01808050078000e000c0c00000b45a400101d07242507140050805105010411a41c0d1042000e0345009000740c1041c101c0c1003003c4107180015481352b420b00d40c080102208640c2c161072000204405151036000901d07011a544180c1010f1174240024030141e00340c8400400080d0b0003140500b401603803046c3c0d50300c20303154408185001301e04a05044c4260251501c16201070b00c0045406c03842100f805118060b1040580003031000303200c05c440e0988915111000e941c0001d2154641c800c52200070790381080a07101560b0000c05480503410040000c448030b6002e001d146021a2041070600811030084083e52001035440d1506450510140c0d42d800c01401c1500584216542d1a000c00b0910307150ba40da9409 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 487248965 1250 487247715 487247779
    0xd060807081006050603010b03060307030c15020c03010903050405060703090f14010806010c03050904020c1c0905010207060e03031c0f06030602040f090e0a030305091203070801030213051b0306 85
    0x900e241c2040070305414060307a0007804203a14208001040306840703800c116030444102d00c81e100c0c2c594403000006418914981e201030402d01c0081c5c8041500d05800f01c1a08210805808540034456010249401c1e12401540a00881d00030b001c100090306100c0b0040004e20312a02d48180032680f00d04240c8821035058200c500322400310655840156004821036400007800d00f80314548020581c2c004105224802d0898003440c1c0101300031011181c208150658181010022625421002802003a980041c459540180f01e0f02d0400510a03021b604048120344010300036500c2c15055583d801c21499444c0110136080d951070701d20700c480c3d88462180344003551044401503661441c1c040c0141020100d40c001c0c4090301d2800a480d00300000c0041c55504042d4181004100395480c4030f4800c3c188074080031a21000a000001c02020b103a1003508541628422103004031482071801c07580c0100c80c0f084030414a24000044d0400c1c9074643c2c8809150300400041c00d6498604143e500343c0700000065842d12 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 487250215 1250 487248965 487248973
    0x1d060115020f19140102030f01030615180b0a0e040510020315130c0e06041d040c0e090703020102010f0509030a0309020604090204060e03010b0f0d1106040e090303060118151101020d0608 82
    0x130003100c1d810900311015140300a44c110304081403100c0c40c2d40410722005080964031500c40384030b1944009000002c00082120384d480c4ca10541e5200081c01258490a1041d0070f4007801098003d84100b002d4003494101c0000d0681c00840c40500c0000d43c4007410b202140c9112044445d0950340300110405c101c1d9052601041025803440d010707141e0f05050703214621604041c0801d1184040c0440c0c015803410050740c070a2820340307075400c2c26070710300b517040c0c120980c180c40100400c10001400211602200d100703900070804007541c4203100c41100d4050790b03c0d500941040114114483c403a400c483d01c02030004240b280307815039400c40c003001c80e4015800314001c81c0308020740c00600e16080c4079030b03021454143c84803821860a40001480b0f52610900100700350220080d1080036104c17071040e42c0181c5205540c2c01e8190420502d150350b03c1c1c20407904a800201403200d4100500c010290020481e80c00300348a000314010f45000b030b1200c10640c03606e400559420310503088203649a01881000f405240090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 487251465 1250 487250215 487250263
    0xd0212090f0c010f0c15020904060602031309021e0904060b0309010c03050c0a080c1b031c1d030a21050708010501110715030207020d150f1d060115020f 67
    0x442c01c0426201503036042c009424008100c0d03d800c4035116000951122500015401742d0020b280213018180030f240d000b51034000081942e50b000002448030300004a0480301d203907a58010303034060380b094030038000400c00c001c0180c141e41c030302c078001800d0303150030003031012540b540c8a18000d40580c2044503c2d6134540c2d181e0381170300041605441181c1c1c0054040350301501c1c1ca4000394000d040e041000d003001d0041d500024100c3e0b20440d000c10600300040440007520359400c44401a41c507181c0d4031381407000d810340c94a140500c4e42c00080300903891000c401c81c05542090600601501c0e5200011943c6440340e42c0341200840615291041500c1001d550b21045074075410301e0700041c6140c0f0305810034030079540030410912170718400c0d100c4122201c04c01c0c40e015030364003418408070740c0b81c00c000c4d03c00a110001c95100d0a581840341d82040c5200400d04d00100035900e42401600c00c1c280c000844461a0380001c0e0040c02070f200700142500c14450107004503071071503001083d0310b0b150042d06034450f03190003c3ea400c0d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 487252715 1250 487251465 487251493
    0x904060609050d08210a020301030308060f0a05061305130905010c0c110d0201050c0a050606040b03010b09010509040602040b03040606150504142206080a0c1505030c0d021209 77
    0x1410003910052070480201c0d0304007000324410100c2010041d0503c132001c01d2a05400120680e203c15215a1302d81c0091a800c00f1401c000c003940080c0400c4011503050780002c7d40c28202440302e600d01450060100980a1038803090180c80c7d84002c00140d41d0204001001c40c0c40d40325412107220110704080c0008581245050090031154854450420031100c6023f1001007240b884200d00d10391806c584000510501c0d100589580c130568a50941c10302070160003005200012486c0340c410740301664140300c100d80c00010076088400d6280b8035a489043c0000500c910700708610b0b800c0d4443d00c80c4e10011300d080c0c0c07150a00e90035038204071b501300d51035900da0005202d1616410300154272401182441400e00e07007407010311120b41d03850140d8603000d10080c407032030603055103070314085030029050310800c00c441074403404011b403248170440b006e0390048404403001406140c002004c5180402315900c60341551508118440980d01c00144a50280c0d0240141c0307c2001d1800c503118000d0314910028800030b1101c80c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 487253965 1250 487252715 487252721
    0x606191a12060301090201140a0207090507080a052d13050a0c0f09021204020609041b020705010212030705192105010504050906090d0e030114040b060a1e09020c1507050904 76
    0x480c2d80aa41410080780c0180d8010441c40c00340c070800c2c4400c1e0781350105400124a0104c02d0f521100c00542003009008600d030300400d14500032110068140420741c0e410200ca4190b01da90b01d41ca07007a03c80c3c0028421205140700700040d4102b0b620b4100c8142030032203a01d880386081c0c0549010790b00c0400b007400030490811151160b40080c00c0640c0150b061144290a000d51100028806030044500003424a0107507036940c4040f202e4203040d030180c0420b0000707001c020f43c0d540741c034000c450142c0701e030f070781c0002c1040580010380340304a03016a915458a0440a405400c00e0000740400f010b10202190015507080c2ca00b07403105030200807003400500740d80341101300400c0e148050302040e001d0700725400b400004040032900c03003d01d074001c0c2040c000d40807046001c6401407250100540d030903015401030104000c482c1d080075000760003c8588000303003503c0f140660800307c2011680381c1015140c0c181045036940c2500070f03110100804068554007400c1101d00074041c0d0701141c00100048001031060010301c0e083c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 487255215 1250 487253965 487253971
    0x2040f080105060d0b220b01090f02161b0b030a0507030612031710050402030108030703020c0a060207031b030b0709061d01090e09070b0c10050f090606191a12 70
    0x4001c1c002c5042c0803000c100301e409481405410031041c14002903c1a100c40542004040c04440d1403070b000c01941003541e0010750030f01a41c1d141e5414184040004003182c0203a4560032240b0029956050040d0354148160b0850084e4002c2440034250004050031480d02440c030481c0c00340000315852608120003030441d40e0035040429100c080141841c0400d50042d500000000f00c0381c03501d511510ad003401c6403040702c011b5000e540d2280c00080045440325011000d000910300c40e80865800000ca0010401203071024018540140d21812041011036031910000114030300710300c1000946500c0e600d6142409800303c900101003a1001c0081200030750100210380307000c00d6403107001e6500d1800c1e07000a11402c19889071103074581003500032840b90394003032003180c3c000d043c9403405558402041c0c0481c1d40300c035400700350094054548000030b100d46440e090850710614222014003156900c0b2070030807130601d00c0040308888541d0216004640c80d070400c40c03480346140e4031030080e0380c4601203080c007861034500003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 487256465 1250 487255215 487255229
    0x6010504030302100e030409090c090c05070f0314090405010e15101b06061203021e03070f060c0e030d210b01080402120a0c030b01050405060a150e150304030302040f 73
    0x8000400102e036000c52100b10122407114042544980d0a00b46495806150030000184d45000a07030000c00c400e58644100f00e6080001c02d1080e0245001d0507140c0f13010b41c0c5805401501190400c1002070320901c4d2102a4013010080e1a052016400125003100d200340c006403180c81c40c40b000d2020b000705442040e1031840040b9251180d8140e1008020710340314121212483d440c0c080040402040300759000540036003407007000c03600040760030300b8002c0d0745001400900740940c40f141d480c218001804021070b10a960002d00403260610f042d036507000100b0100c070042e400c0000151400c90a69802d12055005070038031ba894520341c1d14a41c1e06905054030044498040a1803c0b1041c0c0050b60060420b1b58401e40440352010307071030202c03e500c070709098013010020b18650f180c507008801c0210fa401040c0c140d40c03003946d04106075600c04003807103907401030f602615030441404040420250310800385600c1d10301020702030111084d04404038400303a40066800320003094020030148000c0c094a5002001810a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 487257715 1250 487256465 487256467
    0x32102100b01021c0504170d0801080a0302120a0509100206090d0302030919151113081b0f040603051b24030f180607020a0308060f0109090f14070c0b060105 69
    0x108200203942d404131400030745130000a42d06034140d4240104295030080c4190149510748035400070415403507015520244002c1691003002090300720b00028080348442e415002098003000c005d080c10402d400504010341000b01c1000080b00948800f48640c0c001101034004040d06e04141100c6424041c00c520000101881441040041480010120fa50b410140300000e0301c0040750030079107200c607100c07a04502070509115840c200b50800800a129081140c40740f03105444c1c440e01703119142c12600f1144220042000107844403031a10040741000035400620000365250f036503841d6800e0150101c99003100d540110009403450400c0311040080354004400480600070000c0d10180d00d001c0a0510301c374020301e450024819000125541000c4203220f03040341d115140100d4000d645141c1c1e07070400c5001031042c101042050525800026030300708161540100141000c0506008103400d8418078926525100c0075690400100e1086005507a00c2c1e030351a0700c1004a04168000380340180480b410040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 487258965 1250 487257715 487257731
    0x204090309061b0b010e0c22060f0809030a181e090b040b0102030301090203060d0f0b0601020d09121e1a0a0501060e01080a0f0902100914040603030e1903210210 71
    0x980c0da40c3c07485c1541c1301c075103101d4143c0c2c403015214403050090848280d0040e40800c000c0303008807006010302d02103c8543c0d139100702c0d0b140c0d4548121100b060594101c252640140202032281d80900112808802508040c4070b40d25501d130010003011030709200003d40244162814401c80125018100885500b0b542c00c0c001d42c07840300e0000707540f88414402da03154140d01102040041ea681d4092055941e0400720748107150707400d8100407110b04001e032119805407040c02031280d90f4600610b1144211815000701c02c0202086031500c0340c120605509812640d549a03d41c40c2c00200450b1080c0049003c0d01820401850300700740900403101d06070081e10601c03021603080c46031a0380c8691541e52000d1482c40202d00d40850300081c001622009000075801407640c40f40043d0250301020b8030046400005507600b1400019007484101c85071404003400090068111140e46d00303100903009001580400d174201020303030702d468035000c4880f18010321880d0a0f0454003170b180c0e07942c10880800d0615580008010180d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 487260215 1250 487258965 487258973
    0x30e010522021311181306140d03050c0609060414151b090a09050709050f06091210020d020706050604380411030906090d02120906070204090309061b 66
    0x2201c400020b20514252030030919100d0143c00c01a012808480d4090700c2e040c03d002c0d00d003000314400140c9802990346440080c20401030b80104070450b4546194000100c04000501c03c5003200c01c8415028010100f1444121850400401c4e220f0050302000e0003071403c1c946800ca0b40c2c0103500c250b580c05135000000ca041c0d94403000b0783c03554000610305100084103040c800c444600b4018070324901e80c049840780c0c0018030034645802591084d0955074400e480e807034465040005c50403040c2c1c10240c000c5c40501039a44903080840d1070f0001d015021045450003940030000f5000e0b13a01c054480c0303500319004114141006480e01880c1d40101c000c88044c03086424150511001e1028078600b07140901c43d094003c40c0804103d035008000a80240007401101140c1030001e01550007075414a20b94450b01c2c0018034040300216810310906030705e038003030414203c0d0445600d140e0f130010302245074048001c001541c0140d072244112801f4078883d071261151903203004400f81847e80c604444400d00100160342100107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 487261465 1250 487260215 487260271
    0xa150f060504062a031706041a0613050d08040603110c0a02040b0a051302031b120f04052b08060603130803040503130b04030c060513140d05030a030e0105 68
    0xf455080c13a00e040702c016050180701030030303101c40d0100c0c8a0008081c202c8051541c4a1310062540c0c0c00000415036035281c4109101c100c41d454040400200b504007122000c070301c1c00034001c0c6001016410000780a41d02c40000071040d00707a12404403444c0030001000c1052a805015008003101c0c03031490207040281a06250b5160130400c40002d10455035460b401450f41d65501c1c5541c0a0f01000c0d08040c0f8602d140441c10000758020b6451301c60410380c87e1840c6400c162800210f031003100e032185000c113194a802090040d80e00c000340040710b0302d000b410b82e0f81c1000c00c10b0602d0703e4006103560342461180c0c00c0303864018102c1000544001e000c0c400030000c101170034400c082c014240d20b03440110f1560307030780c0c413410054294018401e002c2c8070580c4107000091711049030400b5100781c0b070041c1b458031019503443c58140c4091181d40c00c00d1f80811042c1c0410012103440c0850010303c0d040c0541048178900c859954039003581d11104800700802d03a22050a82400f10034840e103944408110900c40848170030a1181800c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 487262715 1250 487261465 487261469
    0xd050601053c0d09050c19030305281e0908061f08070f031a01050d0f021c0b0912030f0f10030f080a30020915030a150f060504 56
    0x40358070010b407100400115400705094482812585440b6103211401c0c10240284000036500d0344a14088032145140c80342e4259084440301d020b4094481c55540d0079a240d0708545030b40881d0585440b9080203407141c94001d40c961403040d9980c0b00751031001409500c88035420f030f115641040846503040c41440d600054241d00884044002140344117211040703071600c0b072640c101814078052440000307541c04030380307010100b0340c0e01c11064143e07401424141041200b40c244116a0b100c00302e501941c1c042002104e01403c2c0c140040e152914120443d41048100801a40101c9064244108018062106200c0307a00b054070119011461070400c00e0b5082005070b000340000b4403003000d042c08219480d90030905075005550000c4540c0c200501410070b414960030070450781010400e240c1f601d2038209958040c0741d4903290f00e88010700c911002d00320341c1c0c5c0c000d40010074056000003400e8242c10020704602d02562050320b01500c0403441c000840c403090081c168540c0a084124100380c0240881034002060f101 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 487263965 1250 487262715 487262767
    0x1809090316062a1710120b010609061803061109031b0a0f060203090f0a050a0905010609060813110112061e120201050a0806060d0218030d2109021201050108030d05060105 75
    0x210342d00c402c50000b60304a05c82c1c0c0038816500704104450208a03042c98910f04840c52906c410840a985605c10703a0740d0500400d2a40080e0200382042c400503007164001590102c070001ca06003009116800f0a1a0101c2400045180c1c40e0301000c40c45986446030740e030300c00b0f01000011284c800d890444080c2d92400b802034002d104005210406425807541204e0b0341c02050001c222226460380e601140c00244804c1c082d00300029018480840e850f0302035210310380102140c008081e048070b016202c6a0040c0c0150b0070860420a000c844459180214040c0c040038004107200c8400400141501914100745584032030301254403c810100541c0e000b0054880c81d103001d00300710b10b259640500041b03041c42404c041d54280340c030202c1d0394402c0c41c20811840951610690442d020305c00584d40603280031580da004e145412030b00d0009410003801d1608482003451015140c0e0a04044001c050743c25030341c09810142055001180d610007201d802d02805803c0802820171520b4012401085500302d14030101c200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 487265215 1250 487263965 487264007
    0xc0321200c070b0d0906020a05030403021006030201120c02010f1d0624130e10050f10030804140f0a06031e06120618020316060210021809090316062a 66
    0x841d83c010750410080170754402030455666101c0203024050750420755055006100c4d007100c2c84980c80451050b4415240c058480c04010740c04803012801410025034100c08554030f0b09008221003c6600800c8500018503110280109845040528001c4000c2510a00900c90207942d20804a50700220030007407000e468000041251092807030203060b008401c45054400c8007407004c102800b41d0304c4140603183c10101e5142c075485480c400070302000c544c04054480c4000704001c00c036610038901d40403034007000581804042c210010020b03081d45115030088002c20f03140ca1800c4690a00c2e000d41c0c3da181208943c082006038105500c076480e540c0d0b140d10040c080c540c2c411003240c980c00d0314142c01c4065940202243e03850704003105071040200b10761054001601c105640c841c030604480c02030340c00700001d0425000384907600000b00644031344080c02141d00b5000400c80400d1410b441c17480a1343c03441c02500041741c4c080c60031112901c142c1d130012403d80c15144003860041615417110301c9030401e005030710030a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 487266465 1250 487265215 487265227
    0x303130807020109270c030c0e091b0f04080c060f0d110f07051f0902030606090c04030c060816030204080a0b1807080106090e01060f060c0321200c070b 67
    0x184c0e01452036401c180c40d40e465180c0355509240d407129078040c420942c1070051002080d204410b400741c640650040b0301203003e088140103d401d140001e2981305c4c01c42000723802540b07169510005594408415500001400141031020f07582c200900c4d1200345003510700525001c0c000d40074030303454091040c3c21009681c480886456814451044e541d91401020703165503220300c14500256142e822542e0060b207048890400f60501115104285405070040e01405031075642100700f0002c1b0000030201c01d0100801d0001102090510306204080d001e03640715290f090525070340000719540303604c40c548205801044180201c0c8404102040c096501000700780c0070761525103511800700d81c014a600d0452040ba0300018180d00150001300480706039000412240000200440c241c442d24054000c1e199404001048000c1c40b032244210004d02034904810810003140c281890b0403820b28001000c3c503110029012400403208205454814a140680c60640c00c0800c2a403681e0b01441114404840402d503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 487267715 1250 487266465 487266467
    0x605090c031b04050402031314010501061b06111309180f0803070201110f04030606120c1a0903032802280809040603080406090f0513020a180e061203031308070201 72
    0x10350b009084c000b84155207a25060910011842040302e05542d19040c240780801a150107108440c1a25030b44e40c0c07200d05001e005e240383d43c4a002c1c881012905e45646c2c00c43c0b034210010000150190801c002201443e941c600071800b41034480c2d0541990380304642c101010001281d070b0740000400f42e03111840c961243e80d40f241c2a801081501102039a0210011300000884800c10040c0f050703a2003042c2c1001050748401c1040c3c0c5d000801803009040644410301809410310003200c2c05045488080c241c1c0c50410300c0c0d408607085810420b1800c9007507030b40c8201c015405202650300c41c04508036100816095070302050314000034000d0300e400400451420000c40c14403031450704443c01038502500902c813840e90303407528448d6680580f00310000500c0c1d0000110340000480a03100807101e00501084209410034035070b10085d800f071036510302030140b0b81e03000254440406004030000c000703507100b91540c2d02d020400d00c02580001418008160000c00410454082006488000d1504040c00c00e45812013840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 487268965 1250 487267715 487267717
    0xa1205010b092106070c030e2806020703021c081c0c0f020d080714120f0609090307030503070302092206140303070c2108040b0d0b150a1103160b04060605090c031b 72
    0x8c1e841d04900c0030039000c103410034503c0780000d161520310580c090942e5184803c0b62a022540030003540900b1120b8420000e0007501c02c1403030700f1800b58807120b15080401241038911101c40c103203a040782c1d850301e080201954002942105801c01400a002866900745000b0601c10f0014103640900285116a5442030400016200584039000304403006052240e402d032014403040350f10500ca5240369001948100010056410746540b503194141141c8409a0a402030341000000c1a02b0040e101e84901c0604100a65114414601000060210b08200034034928011640116000783d20420402c00040d02607a6184115070005070302d01804030750b01f0001000702c3c039400d0014120031008140800d198600c4001021440c3c4081c0c01046204180c0040c020403550300c840400c030700c0f0800e102c041d540d030b0b0090015074140b06410b0145c03480d00c22001a1219001c0a000302951004884020041041203a00c40d01d00644000c841380640c82c50b20440504040c40010304031802d000d60b0302d402411482040c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 487270215 1250 487268965 487268987
    0x50d1a0712020703090e0105220b01021006171002090f121005010303080702160b030f190e0c1305040206030103150e0105040b09061f05060a1205010b092106070c03 72
    0x405643e035840c1820001c008001c24003030003c4070803620f40002818945521800c1d800d20b200b080e5020b00248440071710006005d10480a030560148114240c6190304900c10140500341d00074040d03441d0740d5502451444d060100701506c080500c100301030a00743e81c0303c84c00350041140c119101c0000241150f078607403c003641c10300d0b524505401d000001c41056001080188514150341c04c9488001d113084161800429034820091024810800f041c2c800e002800b0039603000c4904200040d4070318a05c0e41c02000ca03011000121030680092110000903e001ea5400800d4071900800b40014189a0005410740c801803100402d4104104c07011106d200d07007600324150052940c0c000b0082464542001800070104480d410554000c0b1000500e000c6002054101581c5c0f0f00c021182d05c450800d03050103c030307503c87d072104014045410248448004c243c005d5034080c0886203451a22560a5824460896184955203007034500241c1103016618002603c0f41c0d200c401841c150000d8112401d0030b440c007421325 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 487271465 1250 487270215 487270247
    0x7051903050d080103031e0c020916080c03040b070c0302030c070f0807050a0f060e010c050303011202010311071205031305030d0c030608190b0612010203071d030c130f140a15050d1a07 81
    0x62b00410070302000b0805940c1e0054a00d0b11107044070390300c00e200144507101c101c0e0002c0c0144210408a19490b20402e51500054801c0c011a464070500f1440e880c5004100d40c0254403202c000c03401400001020b00080008000035141c0f803407441c2c00d002c24030080c0070440c050a001c00c0040200c9401c00c1c0c0c4581c000401d1160040d01740d130382c1c1c3d58688001a00c0350130341000907808a4100380c4000802810301c001c48100c1500400c1030341241003040402c42e565400904030700c030003421520008000c54001e000a004020011100203101d040e07008028040d80c3c00c0d688540301c0e81c2c00c2043d000d200302d0075210030044120341c007055100090380ca0000095030f4020b400c803090100c0d88044104161160000c0e0005040f0340c0c40c503000d0030b002102008050780d50203016030071074000500e856006040d0500e90412440380240600c040b51001e0180d03512450880210b039100d09d820307126132516a80700c80e0240030502a0905440384501c25201e07031181c504801d6070301c2d84620050003050002d01068820380500a42c9140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 487272715 1250 487271465 487271479
    0x91a12090c0f150d1a100e0103050f01120b0a0f06060809060105060c0601140d0f06092307090504060b0409080406030f0b0108070f090533070b061207051903050d080103031e0c02 78
    0x12940040510b0406075031030380400d12b4800423a440105910a4504070303440a090410018440d6403038100c10b150280c00d07145c2d42030300c27110744003000d02d55802104042e2003d03a03a03111491801240007481d11806a1202d80682400c01c10075060342408a0442e0544042282c140389417002400800c080d80c0400d00090040040d409820040001c41d800800710309003c1c00c0801d00c41d41000461042070403010320000e1541e888041c0404c1203000341d400150348103010360800070700d542c03003a804101540c190240455903000c0c00907050110b41e4061190880401d0888010040a0000c0b80042c2480002906410030300000c045112921841031484034040c0c28040c00c1c041549828072000001c1400031910080303200d403001c401c41c0010540d0b4080d1640d10f034111034031070304607142d000604c400029940c084d02854003908002003103a4880200407040c81000c44640d0800714a9410840c1c00d00c0c003080c400000308071a801c010030200b0f61044584071041d005424810202d8041c00042d5001c5540710002034204807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 487273965 1250 487272715 487272739
    0x50a0f0c06021b0a05010c02041e0e060c120117030d060603020d0b0402031605210108100c0c02010801033c120906091a12090c0f150d1a 60
    0x1001000c00311003664007103c009a45a0711004101c40c10540d08035001010081c0803c865071080c4d40780982c01c1d0000d480010004000b400d0307030130f1843c00d26410412032a11200c608414580c00c00100380d1081e0f1102c240f40c100b802180041129060620529003000c5e10030105814610061084500d08600c00c581000300316950720000e00030350401d40e03600ca442071422081d20725a0415000f147e10481d040008000d0045284106071181c1c2c010b80c41034240c00c00c06405c4001d5140c02c000e4424064a2a81d0007000360400e000444425202c0003100401000b805403c1074005036005a04141926480009184440c4203519009a8600b90390800c802058481c03c8408000a14000c0b10300c9140c090301003070403490072001d800c0d607a200c200d00c210340015414641c01c0190f88489008080c035081003841180c64a0b040401d1405c24a0081e10380c5803030b90b0404051001d061a05400d624108030b0187e81450710003801801c000e2890240c001040744c002d88892159403004c1002018050050009001034030b958 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 487275215 1250 487273965 487273973
    0x1b06070206010821091003140f04061a1806061303080408070f0605030406020903150403120b030c01020a02060d0e0312150a180905072402071d0112050a0f 68
    0x91080c494241940540242d00c0d402d0704002e00e110b080e11030030000851821754044207124440040c4081c103001c0560b50201c0000350040760400c60300035160340003002d403281014200001201d2216501d82d1400d186200072822030f450780000c07007a808000c1103011460341d903404082003d078410b0504541c0045400c06001c0100401640900b0540c3c0c41a0110360680b501c2d20000e4042c01964060500481c000b8800100028115001000704420140a488405010006501e100d407130641d01100403810003058020640c600c3c3c424042450030840c01025140c0001e40081e49505041c2d50207802032400040300622207411b900b00c0701e081c2d0646002c50b0351305c28006540e43c24030582920030038074110304411b90006d14548254030a095680044000002e1100c0b1540600242034503039080b105030090309800105c0398003c00c0c920139110844440341e0328004146034024144031064020149200201000c3c1c019204001840c0381502e0180132130302c0380301c545800c101e0300c0c04a0700c2030002c00d0b02400b4a240c0c0104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 487276465 1250 487275215 487275223
    0xc0302071b0302030a0b0405070b0a26060a050d05010e030d0213080708101d0a0606060212120f07050c03132c0a020a03060302060d02030103030e0a03171b060702 71
    0x1107402070a525248a01000205180d10064400603615074021504003000c14070320100250814403500803100250b94450304c20100d078001d130500c0c40c003090200183c09170444000d42c601c200c2280c100a00000303480c1c2100010503202ca14003503d03000b50660400b020030010254000c144001400c001c070b0740c440c1d480b03021036000b95106141e20001c952402d04d0000f02102d0004400c010788800c20003130989a0707040c5d8081c000a00364107021f000d0f0a81802d0404024640900c00c15200e075014290120303000c0d080000180c5040300110f1254070039641041011020752000e00f07160b800002080d9110b01d15141c00070115582d0003804a40072450000241d000724034000e03521070900b2180d0740c40c182e50600103c0e0019070841810703d01160101e000800029200300e00d01c0c0c2c018031210400341800603103691680c0100e0003030b0300185c41e0505080d03130010050041c50740001e080140280c088903606420350640c2d6901507104a42001b03038000d442e021401340c0d41c0358080008034648181c0502220309034078140714009d5036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 487277715 1250 487276465 487276477
    0x4110304020415030b0f070c0b040f030206010b091c0602090a0905060406060c03080402010c1e05060916061209020a09090803072705011b0606060f08160c02091302040c0302 76
    0x30443c6410b0f040c1c14141c024a1100e801c89420446201482d5200701c1030448120008140c8000c0265051007940001c03c0c050169005d1402180d41820440c01c0d4900603207403000603000b1280444c002d01c01d0003c40d070b64039907100f601c106040f40f81c2d142d0012580f50007006800307070a00b540e90020b4541000f1a84006030361140d4410304c030444080c091641c0c3d80d002a034200201b5940500003840540c001400b5502440c0f01c0c99240340710314110240a90841d07604104455034100441316070b004142031000c0030004010038091a0f82040420410510308800a00145180c807001d0407960780320082e90056644000c982c030f00900c0810418010f4170b21514051296038011140074011031100c0c441c0c3c000d941d0703a01800103040a002107070f06d00301a0030807005441c00c0b010641d180819003451380b508400101d56000308002456a40c8a100030021000070141405a0092030410040d47d0720312024029548010f041c01d12580640c0c06041e641c0344e0030040040150804c8000e50450308000f0a9503940346e140d402010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 487278965 1250 487277715 487277719
    0x3030406110c1b0d0c0825030b01061d03060a020d140106081303050d0504030905130b0a090915020a030b0114031311061b071d0f0408090102031c0506010f030203070f0311090411030402 81
    0x2c0f1350340c1f0300d0840041c0f85109003c00751081d0700700300040c0711550107080080c10000818111904039410340340003c3c5030202c1115036801803600030a1041901e5441d0048000340720b06030f22503c88a60426100814600f00100a8052500100109d8044c14042c0d01254100041c3c04c6081c0b14510b42800c000d80300852910400c1d0050010b00540c924041d440d01c101d050080c0001e043c40c402d42e1415680902420310180b05407032040c0e81c1c50706410042d03003504c02071665518544000c25180284d00c00513040c80b401c4c001042c1ca0b03031801c0040080c00311340986071110240d40051a820200300040c0421800c0c028840499400740c20f03030307070110004980028140202c46141d9540d0100b06c00e508013040e10890700b6034800012b60480e4011400007600c5101600c0c04a2062044034141403000410f0004000002c400d04004c03030f6140c040c0714a55a01030000e02e80403200b410103500d03600300050001e02014809420900309075452081160070701b920012502c040c44002c0c03080c0802450446000e10f2035000352000c034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 487280215 1250 487278965 487279003
    0x3030e011e020a020f040209030a060f1d0a081308250b0403020f0d020d0c090207020a051503040204110405040606200d05030f0403050f030903030406110c1b0d0c08 72
    0x1074a6001d00040401d400039030151000e1071030361382800103c240400710140d20a03003e01541c51036890403c10322070064002d078030208940f007404010808980c81507290140c886101c0c4002100d0381000940078245d41d46c085d006666a5403200000480c0070b100e5000402c2034000c11000d00e84808060703041c1c003410700042242c2c0b41542c0e594804150b45108030b1000030340052020500c40110f180000149900038000340880f19a01c1059513190041c0c01d041c0c000a2200764042a4482507080c48480302020b0541541d00b031407880308103040d0307030114000104001e10a545442c4480c2401c580305096400504000d00b05000082d182c0341e010b41910500c001c005013042c11084c588404c1800041c1d20720b2200d80c961a040d1454807074031500e2691090040064050000070401c0100c01e0b00280c0056104001d000050340e02ca00b49440d14000b03440e200c8005020090041c400138a0a51011900c01c07038480035103902c882c0556602000c41e1300c00901240c06803800c0646000002c200f080440c1001d2016a00d070381032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 487281465 1250 487280215 487280237
    0x606030803062d01140d0204120b0603030a08010e0402010309081309050c040509071d0310090209070c080d1e05010305010e190b0a02070809040606031a06040b030f0c040e0103030e01 80
    0x4452614220710b00a1070103e4a15083c400c0795001d00810071420010b0f00042c2e240003017111112040e60300c20b502012240c6801c4e900c400c10300150824498102d04124091031078007500140c000d103928018090440302c11144000b00c2c0031a030003684801f8045a010400503152031000d02c00c0c403100b5005208480c0081d0406000540340c100c40e4040360107407600200b0900b0161581c04013111605218401d0102000c0506c11510895a0810080100003051079001c1600320407803041c404512800340c8400d0901c5010000240050314110030f442180343d11032000100d00300400120201c40f001c3e1540a40a07520b00760000c410f005e0b040d04000c490451300000c0303805880d200b074074074045409910001703032510a0365008500025000d8004119281c000c0800c1e605203080d0b42d0001c5c0840d0300c280d00201c00301e0740d07480e0101d61802c2d40851007020b01c03c00729141810980762420840d12403000a10f4040300f008140b0008900c0c03c00030041d60003608200318080d1484d82c60f031401826142000b0500c9000c9400d00d041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 487282715 1250 487281465 487281499
    0xb03060138070b090703051207060c110a0615051c03020705060711010807110313080607020703020a050603062d01030b090105011704020103230604060602151302030a060603080306 79
    0x508011001c9150303025140070810f0f00c800c2101070020744000064000e01c0400000310310100242071482c3d850540143d91050b0618051048403103048071981840701140c4007000d42c0d0f401080d203180003031700094007088929052100d06100b41a0342c01150f8003904084c0103002c148443c0601a200c40d02c039400701d60103552510304100071405459001024007925098102d4076510824600d50060480c0c01e14900050640542c5410741d0007080411981c03005046080247c2c02c3d0410170f058120503140003a18500d420b54010030aa4061400b0340d1f07008141c00008504a81c94100015152801e01b04807038001d0146031041500b014500c20407140000c0c202241111030380303031526106048501c140c43d0b05e1701d505901002400501e00040040c0d0515940f216040084240003980c2400c20103901c0019140d442c00d0b100300b20458400e41c200c1c00444d80544c114003450716861045035000304d0212103103d4081085d20000f4070708500070f4002045507080c504000204003001c00514000e03201100c01480054031408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 487283965 1250 487282715 487282799
    0x270f0c060314010b1e0a0c110a1a03090a0203120706050a050c09040f1d010c0801170c09191a181b0901050408160305240601050c010b030601 62
    0x30003590500b280c0760041060004e8030000702035512514460680100c0d181c1442a0b07581c100007120008141c103600f075041000f4404a42c14001142207803800d51031806c00d444010480060000320700500800404925008420020903611aa004046075240980090141525001003008031592800c24000c5030405550340035042c80742c5410b80c0843d040410f62410440903118054024000543e200e1180084216150844c5d5070b5001510011400c9900780b40000c0800905a022100c2001c0c00d41c207507002807201150048108404135a0710425460340000e0000308861000100300d01c0d41741c01e10742ca01441940c07101d2408000c0071a400824030307400301c0c2007074882441219050005907000001e60036444c04071000c0c1040441c18540356060039260355055252080e9050324038070f100c24004003041084820400350071b000d03665244034520008202e04000d140c1c440a041d45050001c00302d4521a01c0100b5803251003180e00040c00c5504a594640040f6000103112040c46110300b440c09801f030860030049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 487285215 1250 487283965 487283981
    0x2120a090e0414060106020c0139060519020906040302091008030403060506090108030703211e020318030a0914060705100b1302070c050d140a060e06060901050303030a270f0c0603 79
    0x707190b9030000d0ac544006d030f46070200c1244450b128162061140c4458441481e10700c10400d20610002525050440d0401c964144403406081c2c800c1c0100900c1a254a614003031301e088a03410340d540600e5482d9400e441001e084180c010007568440410000240125a0005c50048000355040081c907600d5002d0310381c6074032951002070003043c03800d5860b8940411411030141800d0307405500103040c0ac041d0249880c401071000141192a0300841806110001c1070400041440d4540003113152400320300740540f014074039201d441d0030304030504914038050302ca40c0100c0340b03410f41c014199481002801d4000005208059010f8007603609010054440c0d61b003442210402900302180300300380340c0f030101003000d0b040040720700302e070320645040c6c00000c804030810070707a5060b900c242e50101d401c10400780610324000303009204074410001c0000401c1103407408011603800c4000c503400454020620f036041002d603916600300f03c081c00301c0700e01d5074001d110b214580fa040052007400e408c01441e41d250411020b03140b420b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 487286465 1250 487285215 487285217
    0xc0c01140307020312090c100801051302071707080708070b1501090b0d020d020c010606210b091815130516380a030608060f0702120a090e0414060106020c01 69
    0x20424145c01410b0024103541c801c1303c00007202c54840b080000300d983c0982c1046c2c43d0012600b0300005110510306400d240890044a4908504018550300ca40f4000040c80381d424800d40c1001403800c0034068401e04854025801005103540c0d5415440d0511030098111001300c2e1942c0c420000f402c1c1507102d100b1200440703800c0c410090510091001c4a0001d5200c409001c49580d801c2140244031842806000000d12154482c1500c070740c4641c920b40101c0c00b25a807803803040d44c545640c480e6195110000c440d0056030301c1d40302041d9248000701c00d5142c645a04840500d00010808100c2c41c00b807000c2d95507201d82c1c070071703000d60b840e50000d1929004844540c5c01000c10390100c4071841720070348400010760f250b1448095200c1d0303031504685810080543c045003000780060340b110014130040008201c0c0d1604003801d007809200d545490040213481742c14080301030324000000124941c20501c0382e003509014001c42603000405040030325081c0311541948085614500680c0c1c000642180003103105030b110401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 487287715 1250 487286465 487286467
    0xe0d241505040e070e0c13060c081c1e05150103050112020111070f0b0d110c0a0b0606090307181404080702210d17010f03150b010c080c0c011403070203 67
    0x50000b084060040303089088180c2c810408005829940740c0346290045c45481085541c803100c604051030306220079080003060000114298000501890844046003103512500d05034000b048110005494200364030740303600c40703800039084d00c030121030388424002d2100d82c0c0c940c3c80c2c04118200540c180c940910524a1000103845030a001d0350003007403104001a60384003540d0b801a00c1c0d00381c00051801c5900320301079401d03021404210203803d130311400d8400051008400d0410102c2e400c0d441d622030071071200500807000b42c80418240c0e02d90b007060b10422a00102030300c00c02d54403451040d038048040f601c3c844019003172100004500442c80074040c0070780d800105031032910000c2e03000e200115840d207082813402c8461940704510140c3c1400000a464000e540c4c001250207900740d003020001040e0090f40003410000c108100040c080d48901d886000015004980c074201840140e8600180310000340101b440007681240940001c200280500d100f62150301c091201520211401d00003210102c0150344 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 487288965 1250 487287715 487287719
    0x312110d0e03120a1701080c0901240c03020304051003090c0e0402010c061109040e03190e010c060e010e011104030c0911030604050603011d01200c070302100e0d2415 73
    0x1000f80c0180a0054582007403030440c4d900d03060a5425820992124900b900700d50480303200c1e80f910faa14103006181e580003210003d02180640e041c3d006840f9194402d01900945c0401010f0007030080c1c90062100034013200d0000030300c0c01c02501030700c00410201e41d0400c800502044500d12031318a0380c0240d4041c0c1d40c103623108600350341d030500804c098024808601740c184001211070352140100944031400c0c8001d181c0383e6145514283c045000c40c2d41350300c02e00c8940074a8820742c6e40e02401c400403031608001e001c16102000d0103840c5c010140070a03111419400c041c050340d120b000f00c2d4000c05c03c4a10a0b4107403e41d05551302e6022049401d40b2200103016030081010030020301e0b00c0d40085801000003400060f41d000410380c2c40d2600c0081c01d0042131079035141d55044041840a05254000001e00991f981c50085034100f0700e5201c0406002c0248100404c000035030500e84219440d05442c3c0c1701801d290f02003540c81c103101052030701c500d4000e007060101100b0b003030880c0b80320b000d4040410210001760b10014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 487290215 1250 487288965 487288993
    0x160f14090705040b0f07060b01030b240f04060519050306030613080c100b0a080c090a0207051f060e130c031101021002030411090105011103070303050c040312110d0e03 74
    0x586007408201080c48080b0340400f29100801c4280b0041100c25a500d00603c0e00307e0030743e03880f8040340e4141858480851a00d0301c9030030316050340500c40d01561104040c0c012044099010b010080444000041004200c1c00c0d0020000c04440703082c0d07049520728544146040b161880101c038103a4043c1c0100e40410031644400003903115262080c081b10741000110707081c07149849400341800d4501c1c0d403104080041810590961406800d8440250141c4913042d008a801d805000e8070070a041e590000d4440b0500c070f0709001e148444402d040d00076680b1180b6116030f2024040c0343c00707000c1e14581c080c0041200c8026010103003801c5540280c01a1000785107881d0203407010203005125040d40110910a201001c551004510861092076010514085001800b1200205070012814080300383c0b8490f100000000540d04150f03818600407400381e880c5000503180340100d030b1008028140303101041001542100e10700680582402c101c40304c000114000702c940045c00310320300d9007541050207080b00700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 487291465 1250 487290215 487290229
    0x3270a2304090201090302090405010f0b0a0308040b180a030305030901050c090f1207090903091403010b1507030219050a0b06010f05070807050106050901030c08010c050a090608041112160f14 84
    0xb4a0050510305112956500410b00f070280c103e504803840e035940d40398411560454414100d1030708007599400702903400c5503140c24240c03282e03002d403041c0c40c400403171642c503503018002208482540142156240d29628500a0710781d401c2503824800c04e50801d80001c038210001402e076003591100900d04481d4a001030188250001d10240d0f02005001e96407010592041500034060341c54403c1e0b40c1c114005241c2201c103182c080c07000901c01d01c41e90600f214003982e0b81e10408001c90160754600000e0380ca42003450241c1c5080d030703624100000c8940803540c03070f000e0241c003049004038540101c50007034150341c9107001104c0d5041180011000305000307211107404a2205c0b0003422881e4860800040c00340d854030006618503e003680221920103003050240080c0700c0070f0007525240d0b00b00d810300310300704240c00c2800f80880d1128064541044080000101880030340b202500c451400540b80c0318001d5120f1041c1030312103c2068020f010360001c4400003034485521603c0408a98082080c4000c25240b141000b5003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 487292715 1250 487291465 487291481
    0x703080c07120e1305071809020a0504210f20090702060720160f09020a050d05060f101e11071721040303090902030f04060203070203270a2304 63
    0x4510407144c2105000303031058502454068456680c0003070010121406e022a80d00490b5066005101341c81007141c0103800d03202074a01d901080e50440440e980901441224006d0140511011039401824421303421109145480d1042c584101c07a014035050000700c0b1029111480103900900004070041d1045005003020108001c0681c00131a400c441c1c1d918200c00d825460a1ba81c0340c0200400402c101d01c42280d0050030814030a40c02d0031100d03403001e0101d0041443d00041c0caa11280000ca46d56903240e0412203411000348080001d21000300000c2c40540038441043d5021868021200c8040c028002d540c50305009200030020ba80c10a040212510002d0b451070415105c0c001e000000200703d00081880d03030081e0b9240a4071503186060003081095540d000c2003902e4070400600000c1b13500608000d030b01c980c000c040541d40c0e4a503100c0491451048070101f001c0c2902c0001c00310040d10015a41c01844507040b900707840301c507890706d00005112b04047c000e10316000d00320121001d5402e1942082d12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 487293965 1250 487292715 487292719
    0x618100312030b1e19080c0d03120c0e040c230717070302060405010f02040b07020d0201050915090a0803090108010311060f1c06060201020a0c03080a0f110703080c07120e 75
    0x50a80340d65804100c1c2c101480407250407030803c5250700891810105081000c4948040400c0c45ea00c0c60640c4040c0c0300e6140780c6801c0d00401f803001036103050502039503688003400000b0900b048000b00140000300048003400354203101e2420140e41840311845800c00340c026403c00c90364280e6410191007600b0159218a500b11070f02e00c0300d50a10a00c90005001608401e4040e03006001c0c0740c1b034145421421505141e0206024510600061211130a840140d40c0000e50580e9410008101c0f0700050b5000d000b0302c404581e0080540740c1e07400b01501507001404250b2000c1d44c00c60455070b101d1056589034007032a85441d000589103001003002c2074440c1005030401c100600418580740c2190045840c0c3c6d807010910104010141e44030350f0f07034008907205100061581d44000c50030f150b800321005013140041d030409401c0101200c0800da90b040c240c0c0c03003890885406041086850b0b0741c10020415070300412015004100480c001880c1c0050b010201c41c40d1070b902441d40c480141507540107447e00c81165491503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 487295215 1250 487293965 487293971
    0xa0614090d14160504110901030213180f0e0a0b040807080702040c0804050d090e01140604150309150b0904061a191e0b2a0105010608061810031203 65
    0x125031100c1d04040b0300a219005011007081d080c0c8101000d00d4503900507030081d4a03000c1d410810441000a5840c626000d29001d81d0314100d455010380c24030081d401c001c030304801c0f07510808148a0306503c0815a00c041c4041400141481241d5035191001014060019082c140024000441803401062480d00c0f400d0000c1c20110940c012a04840c02c100304003001c207010000f44814010100310582c00c0f412203103030070200d090030030032414001207061007142550381006802c1c10880c0d0300d50042c5c4015000365010b45140840265005000e4401418295111209243e1850b0416040d0152407a042c0c00a016141562903a954840041c1982d00390207020300740044200d00140d54003441d001c0042000c1c10381c54411030802c80119075290364000310100100c480401004607403082030698892808a01c000070304103d503480403100f451546082d8103421b51800d800400c4082d000040c507401034406541040c4024076000362030064030000e64403004120000c2c1030400000764504001e00308d4491383d240c08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 487296465 1250 487295215 487295239
    0x210a0c03021c080f15030a020405090703080d0903080c0f040614090d0b100512061303020a080f0a1b0f021509130605030105091507050702030a0b010b0310050a061409 73
    0x41d07580d11a000c440400080c100c00141310040c3e0001d14031a81013070904a00403258909200000e64070424101c009005640307030800030301e90000134411200155040207489a55581485156008007800c420440100707188101040c07840b01080d0540700c0084004806a01e07050a0640540704040c03d29422002008108010200c0703480c1c0c01e0040c3c508600c5101d0003a00d9060018015494200e26000380d4000c44588400300f90740f00d0000b4007079420582e07884048808492909049040c5444d02402524025001804004121b10a00104082c0806503507212140d0b104501e0113403000004070000d001030340480010809450030b50f4089018001c52080d051500e40c6a102041d0054594100001100d0b40c820303081019040a0140780c0e400640000600801030000c41802c0040001502c60f904126020440b0700031928100214020390f9044540b004aa694034a00b640d0281d008840881e805110050001a641003404d10380040c0c3d071032034039442036400100318202030b40e03080180007643c440004084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 487297715 1250 487296465 487296493
    0x140c041e1a130504240e010f0203060604030803060d02061b01050112080301030813081f1a09011208070203070e0105010f17060607061113030c170d0c02031606080702210a0c0302 78
    0x129440704030b040717401249560310040d0541c2103030400b2034001c42c0301c0e004008024041c0d03640f400315401d5039031000b96507482c3d48850713022403400040d5900003500003000188010054540c00c40755007007451413030001d0040340e032189a1526840d10300c20000b86504018001400010000d00c043c100800500c0d090b80f600750340d0768413002c0c90611a820900311018043c4046611019a40a90800008000c920810040d1080003094410605104203003007616030140c0f0900f04051402141c45140c1c0083c2291070711612206070412000d028800c1d03078040f80030301c07082000450060450964a846922003400301e50384100912a031070348a00d0341220425030700c40074107504c00b41c500041c002c50403403074603050a0b41d401d40c5410303035454029801c824411000305403410001c02000070364549805240c42d101004000c14804603242080000b0700031101074201d040860b0b425449411075215880313941c00c41e4108603200da00c61500c0c44c40300e0040204001e0401c071082c0c106010b81803502d03500344688129070303000036601d00d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 487298965 1250 487297715 487297763
    0x90f090106111005060a0e04030c06020c01143405070f0503040504230105040b0d0f061b09050102070308090604030503040f06090e13140c041e1a130504 67
    0x704042200d00c100b600c80400100000ca014000310740c030030007041c281a40042c00740a40c6200b003403030a240003c005405c140c4100e85441d0400c1e803102055440d45500d80109010300320b00305c1d101d0104c01164000800452440540d00a4903055030300d074590612039502032005000200c0d40030024400c04100c1d50000031004204030070240d00a4000c0d64480e03040104103c140d810120315200303418904c010300308031082003001050440f0002c940020700401d0040100d401c1c01c50301c1c0009400e5006c8054010140481c07900450501c1c00741c40115078544140513010381e0164650f004150041e40314032010300009424200070001d04400400c241e0403c0d50b6a500c0303e00d1039105401004038151030700c0c0c040105a800c514244c028202031520303644186451072000e80760924403900074002032074019800c1c42d840300a204892607008080c00c05d102ca09100d00408001609011822610900c0e0a0054060400042144800e0000180791001c5003807404199400b4200c050400d550080b08a10884200100700d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 487300215 1250 487298965 487298969
    0x30417070905090d080a0f0915090204050105040e03040b03090a12020f070501021c0318120e18040b06090408090415031208011406070602130902070b1812090f0901 72
    0x2100404505050451810588002410200d240e5010800102400c2d0b0001810359000f0f0903100006221006a040d44000d00244c0130090a01881c0c50030038440e410145d042040f0f181e00a80781403040fa40e84000340030850b0340e070401890640c1c2050009000d811030890080d80c10400460440c0c40c19903084d140c0c00c0e000041c4020440141e8420341c60051031400502c030003001803000740050f211001168000041c1d00f56004000f1003050340d51440700d041025804406482180c10550003404054450030240410424410852040c404900c2c0480c40c482450403440c42681e00511f82942601c0d010180100e0002c00360080f100f82d84d09018850b92038603184a000f40000c0984216414903156007401400450034960355000c01820340b0043c03006694200031000044000d880041c3e5a84039800c1400c02030040562003c04290440d00014460040350007501030b1501944040c0599115490310041d8800c41c2c0c01403191035000500e00140d600c00040c040c100640340600501e00781c600880000d00e114500f6 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 487301465 1250 487300215 487300259
    0x20a1203021014101202010f0c05030c01050c1b011b20061306050f0f060f012006070906110c091015020d091d0c2508190f200304 57
    0x10010043c60060650b0540e009141d10080030085141c0d03500001c041586a2348580c00307100c00000c070203003008003c000b183d00c0102480c0082155081552007007015500c01d0148200c043c064401d403440048062240d42000a00c1c80b01079000c140c203a40c07003074030010040e441c005802c03a6815600e00100d0b0082c0030444c818800f6a0300340071840140d02d40030007140d002520000b54005494104030060103960209030304030030308a81c180d00900190300100c880094020341c1d41700c20303076006030a1a1140703000030b031a030b020302700326112040c0312038a4803002c48034141e210690408580c4410000440c03400c02c80d80c3c80b0740040503400e9480a0644600c1c8840114031009140001a409489e10381030440e444203210020340502151891000d1070800001110b200162a451021900003180014004c02d080c6908210002802c1025010000d00f0f0002080d00048680050014000c81d002c43e0b4500c50000d01c61b5000040e1100c48420380c2c644121480501500f80448862001300b0000c1074010348440307442c11401907 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 487302715 1250 487301465 487301501
    0x305040303031521140f0717010c1202070f1208040b01051c0201031e0e1e01050621070f0b04080f0a02010f0516080301030818010c020a12030210 64
    0x59458024202c3e24000000741500b00d441600384000503c0580514202d00704000b108035400250400071111414100100c00c507102d9241c164021020110b40e54040790002025005030170700091106090ba0f024003110780005001d19200140e80285074050185940141c2e0450f1071070740d085da251a00300c85030340c0006000c0350a15080004200380500c111340501402e44420b0b14294584007102c8012614140083c14180c96034004100c150081000d400042c40e034082c1400501d002d40141501c810482e80080d0140810307407a54050808140200c0e0b000700d601404040502c0e55034084201503080c00540115103004501e00043c54000092285000d4514a80415911490032452929100a08407178044a0b00140b00450260f80c021f1001d002c09000f40c14480d035a00c403403d0700000f10454002006000c494040004001d0060003400b0707080c04030745400450000c241040065940030341c500c00003075204a2840d01400511314202102240911a0044070101e0780c14401c10703003c2d00c0441c0000f00031210 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 487303965 1250 487302715 487302719
    0x5070818120703020303090d2405011e0312080601020312160e030109020306040f021503040f061d0d0f0e0901090b091308040902030606040816030620071101030b030307030504 77
    0x25008101a810307074034000003005043d00d03580c0030135224020751001c544142d55040d0100140710000d100c650394808582c02800912040e900c100000381001e01a680700d403480070b141d21600c1d6649200440a0b6a04000000d4094100072001c1724104d2006028a04500050055101009484070f409005074001c1c403190105c0c0840030720050090300840c0074541302ea81824a20000f40e103012445581054000105d6070b068489800800c0e001580301c5224061680c0020403c0188503a182c000c10449110356001e0000880c030f6441da14645010120803100c3d80c21850f04009018000c1c00d15a40c1d080304c80c101a0a410040000152101000d80c80015420b071103405a120390b00c0c0ca948840e40c0310601c4074000f6920380098440d41100d0117079028118290f82e002012469669904080e240189400300840703580030707a28038030103584080030301c000ca4405040c070351001394881c560300300f0f254403000000d4507a080a1081d00c0701140c80c0c51001a01d41415626020740a40e620240020110140240c649039070310f43c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 487305215 1250 487303965 487303969
    0x20106361e0618110f0901051603050405130b0915012309041b140c150a0209040b0102060c0d0504060b0619020d05040612021c060807170102090303090d0305070818 72
    0x74401c800041400d81c9061180380803c4d6101c4e0a032000650004013990f2550103007401039480c0c0c4a010007402c164110030a00c10101a881001001070744d030243e0742819000801c100c3c20742514140d0109642c0300203d580000e40c00010381c816403a0403101407404060342c1c0f08e03039201d1400c09242c0d0f01d8038a81c452000520001340342000c1c000c3d07101400d1030382010810941a484010913010381e0b01e4030304410328400500e003403010310700700000e19810b941035412480c141402c90003100294010640580164103154ce00b42040d8008038610b441164100d52181c90300c1441c5294800800c80100101c460a82c0c41c910b00c0382079150700018180032600710148201819081c14040d1800404101910411408000c00d008040c1c1c0140d4401d0a041244400360311aa0302c9020b03462200a003142c141e002a180403400244107000103411812915010303d090802615508414282e100d000740c056050761007000f220315142411050511094042d00d807881c02c00741c55690301e000703d505c0000405811042c002c0914158 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 487306465 1250 487305215 487305239
    0xa060302092a0c1903090806070c050c09070206070c02030102070c120b13030905092505090423010e070504080d030501090b03060906041b09020f0a020106361e06 71
    0xc000080506003040f0700c030700c1e450307550707004101c018100583d000c06500100345c0907501240160080d0b0050710010305c0c04080c02020584a50000d440314402d18400803c18104007484501402c4540e000e03044580c0c9070082510020301000c0d080b609036600300f0590010070306851036000602040801c25100300c0060900580710705000e098a041344001841c03d00000303402c2041c0c0e5080b51420354003403070785035940c001c100d4416040d84103c2d124041c24003400300d90303164130034010038440d82c084808000d902201c45001146244d038698042203401c104005002900e000c540095000040b03151135480c1640307616140b400d04504c0b0031040e012075240e00040c0f102040c14003400e450901c003580140091700e0803808041c8e58031030140c0040d11000e4082204180b03400111000d178050895400c0a655440c1e034084050120f40c040d225180055282100c0400c041000d59801c03554402004002c200804001c00c80b1000c50843c2d0044041c103558420701d0407010050380407050701c45924510001902443c0032404400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 487307715 1250 487306465 487306531
    0xf010512032503170f2401020a1b150810091103060108090c061b0d050c1b030109150c11010b01050706110c07080706020706020a0b0a02030a06030209 66
    0xc0c54100b0b02403103110210030403664150b204000c49a20208020307080a0b2110129221502011000b100820100051200d007907405003000680c2c01d10901c40c000d990a4000f524200d5407070060304440740c101c0100d0710038a01520103110500110441f540c0d10700c61503100b80108004007010460310010403540e441c0d012008001030560000c02d0101003010040612544401032110303050000c81c2e00400e0007108100036061001c100981155030710710005102c0044002120004a1244204410012541c2c81401541c8005004a0040822201c01d88640381d14030511819642c041d0b41c0c4043c0c0b1008500241e280c003480c404520f0780019400c944150060200514016806040e03044c008030b0700c3e02c0e07644801203c0001c0e8100e60000344010900791000c004d40715810340a2101d00c210640400d09130b1001c20074004980e5180c00301da56455541d20241e807210000c0c1009090708050b40001a080241c82d001981e015502c10700c002803440d144d500003022040183c855420741040b242c40390b080f02c0020914902 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 487308965 1250 487307715 487307749
    0xa1d0a0f020405060901110709020f070506060a080d0804050312011814040201080a090809090c0a090806040803010b0903100906020913060b0415050c01090308100e1515040305060f0105 81
    0x442c240c24880421100d1003003100345410000c0400e1000c103003802c14030045001c1c0c040da500070355a61481c400c0b4040d480e00120815140c900804000c5105440d01c040750340100c0d80400050100d03225100300681706000b0003030083d40c15010800411301c00c07841c0015258080d050a182c407000140c107031158001125031243c03190407100f400740c042c0000350b030b0846122644030300c080c10041156822407a11003002d008107446103401200c1001401840040103002d8248142140d4620002643d80d410056807041c0941d0701034001e00d0f04200502c20130380b00d040241000840501150480c0b0b25001c1142c048030520101915030740d07408075202d081c929001d40e51214450b0b0b00071061007821b040402102140c0b10768880c40c40b5115003000c1c90038116000c0c80c2600c0c000c004000c000c000c24000c9041c0600482c9040790503403006112400c001c80c4030028044c95502a004248420780380341261002d10000c1c10a0b28043c21782d408081c0400030015108200091203030f050040b0002055150006001043c801125841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 487310215 1250 487308965 487308967
    0x15240311030f0408090a030807080918011223100c021e0c100c020d0f020102070b2a16030c14220b1c061d2103060a1d0a0f02 55
    0x31203100300ea845001d401075007100c144c0c3d030b980701400001a6901000d0740020428800826075a09010148014180c195019501c42c6030203400f00218060704030b000d000f030b001d8003580090704002141d00c80040454500052800c003424001074aa554505030f400310314007820340d0715115046100d41c1d061101461480d0170008121100e5101420780b81c0b40c0f401045e40e94054254030811100141c2b0465050303c3c080e401805400345070005041c043c00300c0d03080c0c603002da003d84070f040e40002c1c40208440803540e034085c41c03a55020b99103d07101d000c580e821080d0740d01561940324084143c4c0c0c0565883d074507030700194412000701e1401468240c846440c0351107140d0352441070642043c801101480c103c201e600848407807400061201c1a06d0001c2c4032080d446410040520410800740104031040d8031400d1807508014041280001c1c80d00003e6484940700e652400701c001a051003a00483d6000140d03401820007011908016250320780100c400c0e4111124030f451650007802d1103606049403249103540c51201c5825 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 487311465 1250 487310215 487310221
    0x61807050d11090901060f09062d090504051306050f060105071506031b030303050f0910090503190215071d0609040b220605090f04061524031103 64
    0xd011030146103103020540362039a540d854a0008481142e203c6000104038126030f5071181e01c010904040484400d0218130030410100e5440d0041840b45103051054156201c81b003800088004100d040703040d440144203040c14045516a100c1c05800c2c41a90082c3e090486400e00b0f090400649002034052018107840d0810320116991050454940d25044810340c4089282c03c610b080080c04644c1c40505043c3c0241103118200000d405240c003145d010307503400c1c0503545a4429180c8a032205030f0340b00d96194407a40c0c10507030104a68119445003805181070383e042000a000c41c01400c2180701e086401600a6264001c0e8010340c0e500143d006001c601c6c24168031484e4a00e52010b101c81a952640b117150040740d003141654580d0040c10400f0b0025054450103403510034861146e00800c0c6100b0029400c06d000802d0074181000660b124500c0c42d211400c007510ba235100c80c802890035140503040c4800301800400d441c1c9458048080351960403c018140c481c3d11140242200c0c0d5080f08002804010028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 487312715 1250 487311465 487311467
    0x2040b0307030b0a0e090a060f02090d15110408010501060f08040804210f110f060a091401140a050405011e08042a12121803080313020612061807 64
    0x162584101d0905000801c3c504081c00100c1c1402d15034894100328160804100341d03128003007001e01180303104080a00c4a080e10090420a81c0540302c040c5800100f400b9102020982c0c10307000c96150443c900300007c00f08035401d242009948030341c2013100c0d5a03448400401003503034000c090091080c9685003000182c00c0c59a60900c16108510800c075081c11150300440c403a10701400342a8520368003441500d1036178102d24110005040100084d44248505820145942041400c40740354030341c0d40d61254000d5042102c04042071800307041150401c041502d40c0e8101c400f00d24000c04640a82d03442e115192460040010300784500034101481e0369019080d20820f907900325400a8002c2c1c0d01800ca07008400d11040c0b80036082d1b0664100c0c407001c030451200003c071003050003030086805005540040b001e102c80b460035228900c0c00003500c0000a2100c0040000c240540c0245820203c0d8400c030070700c90b640f1500000d159400ca040c2c6420441150b01c2030141c145810038400c1c580c1000d1500d03210f2580b4103100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 487313965 1250 487312715 487312717
    0x6050c12120406020c19060c09080d020703240207140606190b0a020c0306070309140a1110050c1606080f040b0601050f070210090f09110a14090d06021c02040b 70
    0xb0050540360003042255800c0002c1c8280300d807510fa030100c04d000104180c11b00364081d283c03950424000c18000305e404101904080345030f400c00141500140070844c81c665501d481481c0c0507191005450205d4800702880e4003900042840c07074000d0600092910304904010b00344000509101e200d200110714072800e00d0321a10b880700c00c5551030104192240d440c803205a09001810715911703814050b02d000c00004a800d031340b102c031000e8010044c15076401041540d25a40d5820404040c20310780781c0240a46427441d118080c0201580185819030a0035124140c1d1850071100c00081c2c1210a4004130034440b8031380c00140c0a0b8011503018132210603050540300c040c08003002802090401c040080c40380317885030680080301d80c0c0950140000340d8912702481c008002c00c49031300840f0191a50b07080c00203412592402031035000560307550b080c0d01d0041034400c1510311291500d104602400240040e8007a0744e01d44d078400003100e01401c8050f0799070040031403580351822070082003015144140070074805030030070788 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 487315215 1250 487313965 487313971
    0x30207050d08120c030108010e03030903220305030712030b0d120e0105040f080604060506090f071206081c030b01030e06060915130e0c0a050f13020c010606050c1212 73
    0x619103050512807400c100304644540062908403004020503c10360213070700801907040301c0e40e0700020041522084107080c0ca030b120a0310707040c0141c0d00a125601a881604024000c17088280c059000c0044e62a0789960440d00050025950541c0380c103480002d96030140285109440f00310364900400e400da6031000d498405114088040208494079507015034017410031503014107484a40d55041c181e03981040b0340e40b82c00440d0126280d90a06003c1003581c204548643c0c05103000c1c10520748956944001103c09000b07001c100410251108800035800c0c20034401c0d28400e4040a00010307030144450381c090142c80004c03509904151920743c6081c0c0000003c2406600400c088500500a4840c07001070700120040e040707a00e03804140d000242c122162a50302400076240300c281038940b000342a90801500d1601032240d190070075449081d0402c10b11b4140d00b01d40038288000401404d001101d9503160840708145c0242c0d01080e800200546080d80401c410006040d0000f02145070040010031125030b51400307 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 487316465 1250 487315215 487315219
    0x1206120f0d1823030705120604020f01030902092d09010b0907050c030904050901021306020601031b0f0501030207060603120c0b15030304030f140105190509011b11280b070c03020705 80
    0x70300c03090f410030782e001e000c0440140001803c04c04005120642580c681d0410354040b031044c400100303d07101d59400380c019400501d40040c01c0460315560200c0840750303280108503106600d8039000200510172514540c1a004807200b41c00001c02034447c13230500000640140c02003050000601c44148041f4000040300c0c032680058402040a4950004060290168003a2520b420380c0710440481d80c10390000e800c40c1224041d05048480d03ea0004d500f07001ca4403180a0464100c1c006d500a01c40755000b50018940103104d900005502666a10307141c0d030710110441c20000040d002107269080c012080006504a4034894020b55110000c4000a079203104912000345a803400d51480024030420410340c80700d8041400080c065880c0080d000d40710a01c04a0dc2c0d41d12040ca84070101d400c42c803051184041c01ea0013002e0105554010100c1910a04e41d2040e0b02da04c0c0d889803c1c200c1c3e8480340d4441510900301c0c60040c0740c03205980b070f80c0b418240c0d4450003442c1c0d070b00300701403039600c200402c0d4001224400c50f030741 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 487317715 1250 487316465 487316519
    0x819030e060115090305060a0212070906020601140105090a0602071706271006260313031b080708060604061d0a02031503010e0d020f070b1206120f0d18 67
    0x82d000d885418861740003914600408003040040000c50300100030380e400b80307900c1004595030413505880c41d0029005010059200f20010301c09000700144009002e001410154100380c2c2460003d070610049800c41001a000f0a4080060044845110756964a0140600100d00d801c1980342300c81144488100d4041804040700c00300610207101020300614900300500c180d81e12040d100c483c03690b0801c1d10b801c0e40c40b01e40813000c03c4500040243c0d1540c50720380421040c120b1031074990552604ca00c0030061030440a0607000a451542040000000c00904016100030314200b020041140c406a120f6854201c03503500801c02040d003406102c0d4044101c00c80140c030390b11086045841c02c40360303000d066015840e0481c1508003c40c002099840100f03603600b03d4541000650076a47c9502a81c0704204c8407210500601c2e001030041d148243e0b2014028001458068100401c145040000780004880fa08401c009288450703010f49569004a6130b030301c12010007481d0441c000021504004600c8100c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 487318965 1250 487317715 487317749
    0xc0406120f1211030301090915021c0507050c030c060414070b0a050a031506021f0608032505010908030a0c03020306011d041508070f1a070b09190819030e0601 70
    0x702640151202c0f200c48000c9070346a41c0c644125100401c804a820368885204200c41e0514000728001c4607540040c800c220f8044200010222014041c06881d45003403000500050b11803c400700088e10304681c076079000301224141820100d41c000301e907050100e03030ba4004400900c00b401400701101c01c000e029150030b0355a441240000c800605040780c400703429250080f40081c0c06640091301030f0440d025140302e03802d480601425a41114454403d169031074000b406058041807200f241605076030b82091002000d00c3c0b5507601d4a00b100c0b6007074011198500c0c04028002d106500c1d1003106c0d021521030404624604200002800310036082a20103030480746951051442d40751500103000c1107001445514200392600c0905031102101c0c007601c000300a00100001e005c031020b14001d01804103400f9000d2074550603480701000503070000c0c0200d81c24450f01070000c0c0e83d011300d000d1b20710b040c0b4040c0d90746507180c0c1440c0c4040e01d009030300441d10508050512011314410b25000c00c9141c11900d00c6070340780526103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 487320215 1250 487318965 487318967
    0x9150f0a090501091a0604090308060f1f0801060f050c19110907050901020d0320030c120703231e0901060b07050a0b010506040b1218010903020c0406120f12 69
    0x900060041c010f50814003502c00300b00d0b0790745100451400038a6000c50680c0c844042c0400c440300d14101500164001c07000c91007a00b85030b48051200000a4200d143c0c000980c0d240800b00100c1070b0b091800203800c28010002a5402020030304240c40340c2c40c0003881c0800c074075282c2da519014549400888034110844904219524001e1940351802030012821460250350140c815084180c5942c0035002c1c0d0058203800502c0383c49240e0154803d00c400100082c0040c40c2d122854000800c0e41c2c8410702e0400c48100e0801c030b00160741e84202000e84d00410780308660030804144a80b0203603003550f4a1411001d000d041000d1428a40b40c1201035a07100704242d4403100001d000d041c2c1c6a005c10103d0340c0c0040c25600b406804100020b6050084c0080ca2540e40d0b644140714181c03281d441000f00c0c00e07005000b0ba20300b0318442501c42d508185100700800c014043c07800364a0071507090b204102d016074000c1a10b800c25050078040c80000b00407a200340300c075481242d00c1c0c4004450b5034190051001240b091814011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 487321465 1250 487320215 487320221
    0xf0307051b1c060903080a020f030a27050706120506090703110f0a03050108190f060c0905060f070b090f07050405041e08070b0115202104060809150f0a 67
    0x1503090030000d541107141d9081a000402c820641070300000c6d0300d040050100803a03402110701e01d11110b41c259145030365400d4000d00070080709903000c40300d440115000f0250801000c03c0b0000c240a60040c2c500d46261a101074417441101040b200650300f888100800344e660b242020b540441d1034140425105c50f9a1494100ba00c104c81c61400030800201c0d0032400554558080303810394450030300302c03900151100803003440380d00603940041140d00c21022900c0000c3d42900103030007058050504521240c3c6030000901e8680185801141000303001c64208140445032030869000b06060019007000c0350700c0c02e41c981c0c0318000381c0030340c42c000c0740c903007020404010001e0341600381828003c503003138041e80f02c52a21030f08907840481e050b41d001d1300b09000480d01203115800300036584855207402c00d102140307200c0103401620008a900b6180101f00d0316070220304485445110103505040110b1741c550034210064842e48000e0b0000b02c1d1980318409100c03011422518843d08007060760280880d0b42d50700702244000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 487322715 1250 487321465 487321489
    0x18030602030702011d030301030c3f0302010b01081b0a120203070f02070605130e2508060a0608090312190e030315040b100e030a060212090f0307051b 66
    0x2120310000c200555a581035005001c840070b80c0702c40056007003844403020f959000c01e0101401e42581d0810030440030b6410042c0b510952200030746c1c1e81134183c201da620215000c000441210b005000c4450004240d42803107135400710002400c19100b02e0800950707500c4810300007c0340e44400d00c03000a0024440f8041c601c801a1000e0207801590740c0e1528800041c10044802100c0001d072242076030214001d03008000b56100c00d40103001c20210740f442c001e2142900c41010f0024084820310501862902400c2100c144401005407a4070341030307003800030074420b10801030741c080c0040210b0310b402d01542540104c2110411408030304920290348801d4500000340205803019140c40e0314005010b80380d4a80807001d1441161010590500174403e00305200c1550382e184002c650000c1c482d040200b041d40074001c800c1041901030102c13102c030402a40c507103049030b10050300752046604050401018282c10099008841d40d044040d41c200a0745540f10b6545400184440c40a84821520801030381c4640e160140c0e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 487323965 1250 487322715 487322723
    0x61b0903010915050c0f07061a1905120307080d09140610080c0d030e090a0f09050703060617060417120c090306060a060f030f02090301020403151a0a061803 69
    0x500d06480d008000c0d501c08180005031508000005c0e5000038800103951080144113010380c0b90030000da45600051000c000401254401610303140c7c17981e01d42d803860107552215603c060440c3c501700420000c807151841884585913104200f19000982880143c0c1e03006290f00d000451a20464582141075040151140207180300b440c04000000083c048810304071410302064681050301c101c14045080c1300e41102030003084d40030803410100d04200100f540e014003c10380c001642110403c800007a510b840109982c10fa200401c1841401020f125070b00c000d085601c8041c02008110002d070b0789076600148003030600c06007401e02d10056035104048640102c11150078040901d404a100f1603e0f0300b100a410b4000e12440c0001485402c00911020a8516640340e06040f1010318130124042c000040500c85480e800703100303d40003900d090000d000070b180320b9407401403030f0b03043c0e9000701d4111005580042c40000c0c40781d100e1660f0f926414070784800c0c0c0b070300340c54004801840c0d5590400d8141066000170 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 487325215 1250 487323965 487323971
    0xf09040905120a02031201060c0309060818010c0908060906010f03020909010902030604080703020f0c0a090b1207030303050412080c0405040b030a0c0608071209082208030a0c0605010b0309061b090301 88
    0x70b200d0300c1d401720040c512102a100055690790300c0701003c4031580d00c40341008000c02e04580050045a01508140350b2180c4141c42d19015904800c1007542944c0f80000170401180c13a541e414815580709002d0503a0100407030000781220f600d032802c400e11150082c44042d0180480f40081441c0d401c0c01c1d00301c00416500174044440d039041503d401c0910b6444210268010f00a04040100140020444002600000308480442402c0500060007848204100355000c0d084807080e00e000c642c21301c0250010f5000b0389000803a031400e820421811410314140c0c1d03003000984010410400c60480c2560180c031380c165400100d46c0d1040b00407a140800811001c1d200c84422030002400e107034404152807090345166107248075014422046030981d100d840d0300800600d0148946201220724030204000107604041000080346c0e14094241590310020070140045d240403188400c0c8034950084ca40182604c5036011f01d1441d0824260b40c903001c0c080d0400060300c1055503150440030284040c3c44010000600070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 487326465 1250 487325215 487325227
    0x60e06040902032511150726010e0730060308032401030e0604020d03090f030b060a060e0108060d0c081f05060108090d0503091005091605060f0904090512 68
    0xb006102e6403000d810034903203608001368441d0720310485003a6981001c00005010740450000c2414414500400301e070b0400c140c4d00c41c0200700d070080b8500c2c2090b078004d903950b081c002d506080032000c00e020b0040901c0140b10300014203601011815045807507400502c0c0c400540c941300d08440e6000f0f40210303880600005404401e2000c0100b000075112051031007503035200150050100190b0541d206070084130120341126000602500700001c0c081c90551092038100680b43d00d4040c4d400d200009500290340d101e41a03020000c242c1014208c001c080c1c0300c907040c8141111007a5000034403400c03000700f2060080d44d4a18440741000f500c0403500c005881c028040d5640c0e1214072501d4165a42c007191030000450400f404a807042d4040c800d0365008402c01c2000d408090300501040d607041c0d00c0a40310300c03690300c5040e82c5500a25944c1c03203000d001d0311072180505140b04a000e04010111050742216200d07140401030701c03c84000080c200c40080d44107640100d0100e4040c20041d0510b0700b14111035074401000252 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 487327715 1250 487326465 487326481
    0x1060b07032f0c010215060a0302040513021809070e0c03150102010f0c170c040b0304080307020a12030504020f12070918140105040201180501020a0b09011b0816021501060e0604090203 81
    0x242040c0d0300b10a80c2103500a00c40406c80d500c26100070f4981c0703500101090424409807c085e0895a44000c800c4521091440c140d030105149128062031420030354032603002e005980e2420f0000078000d080c00e00055203c0c0c24000e800070718510016241000d600da00c48401d40d1943d00171340010f20001206082080201c012090103010315607400170a2406955840020714040d0800041e142501e5103181114215600d80c0d41d40c4d103080d070010b0b01e981d05520030050200c00013000c801d080c035007100c103507600480d20307003000c0c41440041c0b44440b107000c0c4124640c80c110242c04900003003010443d40350700b5021a00c40015007005407258100c2202508201c440000f20051030815013040e03000714400e90303540094410030441c0f801030722818041d90f80183c1100d050800407407a0710201c40d4100c5081c070000100c02680c1016407a241111500e0a0041a0705200b00400c80700161107541195000340090b03d4410400084010201014003030502406060b079501025901c40b08103840140440c49030455881c144114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 487328965 1250 487327715 487327723
    0xe18010f06110318010309020102031e18060a12050601050405090a050708011a030601080c04091d0f0f07031415090f0706030b100309150222050301060b07032f 70
    0x2901c004100341520300c401002c400400c0b110034201002035039084400e4000110b016010000044e4110b100c02d0000c807194110510303902d107a00030840d041036550320031a03424032800d58005040c240b0848061107d0010203401400b130005217510500d0000340e41c1d0354200143c070b0b03502564001940002c80c042c108007500c03010340e100b64040c000070344903443c0b5603903611789040034030101118912070110140702003841c2c2d500442c4a25007081c03910004509140e16150100b04071207204022150740c844541100400260511203001018501c00180c0b42c081001c2e100155200842d10004100114108030890310750700a0007505513200301c12803400300a081c0000d1140e99224105074040b0203010b0741800180b024085d22a000715403601a010002804124100360000c01c003e420582c1d03a1005140d03c4496514644000d2800e400192020154401c41d1040031041c1504c54002038003e0780b51800038000c8403e01c0060300c181e04e605160003407010115170242070604081740000c0500f041090315000703550f20b0100f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 487330215 1250 487328965 487328969
    0x6050a0e0a1e0e031218070902030702070b310f0e040f05010615080a0504030e0607050a0503160606050a0503070b030408190f031a010509131401060c020306010b0a0503070e18010f 79
    0x8440c2144c46c2c0c841c0d0541d0b582c0c2d5401072a188441d6805602c00b00200c0703402d50060340d0320030b10b14010b840c40950b80b1800051a5031101031403403040b0983c04042c00c44444030b0042d01b150250a0b846010943e0705041840c0380c4ca420034003c0e0106c0800c90b600050400038400f40217440c10364014024000c0a940d410101d11300003a4400c40d4010032481400500e4058552150074440e40d015a038040034641030509100f501c0c2e00102056401d0f0240c400c0c40030204804000030018010002441c144a00f441e08050301103074907513000300f4480d2410400800140d40d0000b112002e4888289842d5035907112880c10074101d106012410388805091042c211400750820414944000f032500c1c02e000300b03d1000700010349a0900075119000c12020300c1120010304102800702902c03011410000b03402c4034140c250b04a0380c0026800040050b65002101003141010301c802030042c1000c51130241800e08040003d0001c4c000140f4250030061020440d040c5a90345418800740000c40f40c3c40880301d945c41c0e410518480c0018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 487331465 1250 487330215 487330237
    0x4050d020f030901030c02030d090b011406040f031e0b010b09090603031306050c0a053a05030402061c0c0c1e03020601170102040b19020106050a0e0a1e0e03 69
    0x1400290411a00100c0c0c0003400c184144007840ca40f045001c010b5004200941c4407001b18402800b0701c0500b1511449000c503518003502c070718140c56150090b2414000720719000c440c080c90702440200814a0305001c042d064035400711080c00500541c091081c2e4405808070041d10b0907000e040006500b11000000749079102094451001d035558610506a40c0d10441c160740000704080c0c5420845a807284000d0141024140181c900070207060b1211841c0a00c8100201003880b08600700c401040041044454400240c40f40c0801041c19503102a14500004001038010200022160310b501c941040c068000d4a00c40d1007000083c0f4141c0703000305100d807040d204403112103c0d408485c00d20114011600d00c003d42c103a009041e01d80c240302c2500341c802c0c030b2105186111740d02407001040420356040900a048004020442c1c00c641000c1d0003400d43d2420381c420740c02220114030074800e1a00c030304443c0c0d81c001c0001e40d000c12008107400c1741014210040501c41c810f2480e1011008012501000600d41c0d1740c14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 487332715 1250 487331465 487331473
    0x14120a0b030a15110423043c0507051602060d02040b070b060301270206040302030607050705010c08130201030c0e03030423090603030a08101206050f0702061018090602120405 77
    0x884c02c1d4060030f4400e40c0a000c0c000250a400e61500e07400716882ea10499001038008160480840310f061020301030f80d4048900c1c400800e454180030a0786031f66000074403c65000920807800c04980c090070304e00c2034401e00c88803144109010815034172104111110152a60001c55031a03548078a918450781001c0c0b0121103240070790004c245240380c1401500030240d080c054070394180441e00c4a40402080c06c11040740c100a0034000000540e4003882620700c20030031502e0705981c903403041c038003c5c0c00c59000f419000140100c2e038092100e44500c001c40011410342c20300b00094142c06207003040c4c40e5161180007503907162000050204000314100b888018904a50744d441842c80314500800c201e20404460b0150968020302c4141c00c0203128001c020b80060b6110001c0700c0701600c0300c07500b600b560120041134030440c2d2075406004403200e40102617035110b6154800f800141c18416040c10052a0030b2082554400076001794010481181d800180b1140d80000308543e503050782044041006030848082d40c0d030b07000e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 487333965 1250 487332715 487332731
    0x20105371e020a05121309020706060503250e0408070510020408120309031e040f09050f0117060c0c070906080c0111060411100c0501020307120c14120a0b030a15 71
    0x40001008120a03a000001c0e1240741a52420a013042d044644034811a206d4214000341030744082c07000380541d03402600c0c00304c0c4603410304091501e0685061a10301c02d0228544040700440300e9840c4100545800d40c544d02d0840e1603e04008010740140d0030050480d0180ca04c1b0703d1009400e0b98018421545810180c4040140900c03c80d0603030300044034019034035041001100c0e1800003071039825400d66401007615040c20f40342c03240d0a0003d00b079604071003070319039032001403140ca501c414039001d0050902200c030601c0c0c0714030000a00c1e00c5845c013402d41442c007100840d03030154100040c0560f1015155446003040210748d109042995909500e00c1d15002c94111180800c1860703021841d00c1c442c0341c010400caa654080d420600200315a040202400c10088208820000300c1c02e0004500450b900d6403030082926614807444100c4441528040134841c0600c841c040300c00b0404159a05661410341450460b524252601c01070b00801c4151941406180706140801142d450001c00c1c2400460302004105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 487335215 1250 487333965 487333967
    0xc0204140f010623040b0a0201140403050405040f020306060901030b271e1003080c011116140d0f270303080a0e01050c39031c09020105371e 62
    0x2504110a02c1000e6130100405d03c420000c0c200107110a803c81c1c8000240c0c0898040210716181090300d04400042d0002010006885c1c2402040c0c0b5810303810904514600b0540005085c902c109104d080c1451b450300c54404440d80d906010803440c0880e80d9101402c0180e10300d4607e555102254801040d41701c55078140244491300309502d1080020720005110b071401d5840f0100703241c00c281b50041440d034030780e03003202c1510024078080c21a140d01201c002111800d14604003000d00d54019805046522a600a03d0f4080d4440b65880b20800303141005400205c04500000401546c2c4c101c04010110150380001010340c805130840c452404036004020f881d2050a203542610300942c3c0c80d00504000707101007040040507800b140300e0706d481450b43c04400c8029403c00040c4903540d4004000c2e0f9040400e540c00c5102101c181041401d9a5440030840d41040d940007034207034080c031803607181300c01480e1642c01e040f13034120030b10203018848400b0b0700c4580001143c0000c02e0748160b00300b114403100f0641d06106141d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 487336465 1250 487335215 487335257
    0x40b0406090e100b0f06030a200a020d0c020913080f03041109010f0e180f01240803071e1e08070c120b0f070c060f0c0201051b0a0c0204140f0106 64
    0x1003140108200541c5c2d41c0f130b0f01004819000035068982c02d950310b070507035047d9105c02e65401000f400754000c40d54440002e40d41c003034141809001701c182030020302910200140d6845071100d91106120402000200042c02c100000d400740484410706064008140320a00501710000b85080804450307a1005031380300e030450407010180344540328405030482e022030103503400f140700b01240c241c28104507a42e920b825400d003425500d80000c40c48144c00c0d4146a06c0848440403405409080708800071880c00c0550365600344828142180795403480b06400705c00d410480465440118440800c8495800c21018200301201d0f60200e0f000300c0708903010600010303c06050070003849810b40c001e0742d2840959698107662500a2000b4001010402c814152000003003651040360f455100307070b910006011550000103401c540c1e0103400640608225030105040d1140d070340860b4038480d45844c0c41d8a070004030384085402b8101d41404000b1440000b0100300301d04154030401812a4030a5452144d0750146030454650 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 487337715 1250 487336465 487336481
    0x904061805101a030c091c020a0b0405010c290109060e010f05090a0e1903051905090d030315050a0e06031005070e0d0213020c0d02010e070e0a0b040b0406090e10 71
    0x2201d03034003030220f51041d01070400345a00c0082044924035188564002800714030050702c07074002c8010342c0328554066080405540002d00440c85006107018180000a4125445042e0086c110085544110003401c0c4102d0803082d41c00d05407101405550f11006004003401050041c840d05039009000001c1e280c0e0039600000442c0c102500000060301c40020600140c00d0164506203284948000e82c1784c07040f0b4003110300100a009039280f50319102c03914003039407100110310304400c01c210b42800800e90a03900c040314102402da050800054001601c0c040070003401031940207561110401000095000c190240c140c4102400c0701030703034180c01d0100e840340101c410950346680052008003441e516414941c0100c0d0310180014605102a101c94403124140d900032051003803075400c0100012810b40d02405802a10100b49020b0501035092103a1482d01c0d80f0000c0c484604079440701205c40391034a460b0702c407a8242d1400380c4103102e1341d600c0e2030b000400360901d8407048000b4841c25501046610040c03045410f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 487338965 1250 487337715 487337729
    0x4020409300f050703081509280504021c0614010303030f0b1518041404060b15030603060a18330204030f020603040201110d08070e0103140615090406180510 69
    0xc00c2c0525614200e0703580341b00070002c540c0c522040c041c410455840c020454458070071112444d001682e404070035080410f058084801d024180024800145c0e01c811b0340c180480c42c120544030882c20603043c10030140c04400424100c00c0b6407000084203040c0d25420074a4841c9514070103000203100e041c14820140b883c10416551000240107494180e5480410705c06251402440031a6841f5003000a140040b8141e40032038001740e43c3c903809a000d09245502522200b884c2c9c41a0741985013003030219488000080c0140021903442000c40c088044c40d001c0d05035129040b1400e00350181e6102c00810703211000c01880840407405141841055030305e8001c440641c2d82c41703100b1140c8903415909000c41c0d60800742040b4180240341c850051469001c00c007030805807902d1b5607900c240d801c0c00c042c003900611071a2101c038105410702c50044103418101445641148054551124448070742c5910800ea015807030440713510500702880000e65800700c10b180d54101d15490800c001689501640154042803071250381 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 487340215 1250 487338965 487338967
    0x3040209010b1e090d050303180f0f030313061b020a0c09064b0e010603020304020d02100915021b1c030c240515030303090c0904020409300f05 63
    0x784410b07503020142c00c104c0806007840b0115021035032207a04680007142d030090400b0241610302800303002002845a21269800905000c628800f031241c0c403072000401240039000038120000800c42d40fa0300c000c08091302501010094441900d000352282d0140c9410f03a20000d0068002c0351741d20f072501c540c00440e10a020900301c52600d0300382c5003204c0e260b8080c4c0629240c1441182c807203090404180c03285000e0700404181d224906107103141140d585d060300140304141c4184100b00060f2140310442c4511501160072a8940340329030421120211035411103028400048194020b0f03d40000700f4142805440301442882a00401805011211364221140c0d4940c501c08040c042400340300c024403124000d0b41f80e200104030a50f0889200b200c2c552051410642c3c0c1d204000c1e4191581102841c1d07000700f10051899401c00c000d10b9983c45160f6030009108445840101c0c00315a80c2c0e500002a05902010040000300541081c8410f00580f00c0343c4041c0c01240b200c1903180d244100c1c101d00c100d09040e120b42e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 487341465 1250 487340215 487340257
    0x10507050706110904230a0c050304060209130e0d0e1c15090f030806100e0a0510020c12010618061a03070302070b010b0a030f02030c071b030b0106020303040209010b 73
    0xc00090060f1203440f8050340010480750f81203403654042c0071a112101d855826154010942d003085100b0010b0121070324034540507020b0880f80d1300c1400c80e0780081c0c04c20710150300c41850300f000418281449254524032480e0a1100c410040045a500c1c0c10b00940e0302c030894480c8100c010f015001a5540c1c40310b4200c1c2d920810388000907419002405038051020300003440c102107030381c1c410200031403c5094010688450402007285000b180e60010040c41e450505010a4000046114000240102031003004440b000c20012032080090312840c0c41c1c0108401815041040064001d280310301800c803050744a07200e0089240c01d0390240f0011501c49500c41248643c810403008402d80010349003204040e003c0042c04042010440c7c6c05000c0c0c9110a411070340c45404030401360450704446a05503006006000704482c41c55520140c40f030b8030b030300081c000f80548440c070340d00044401144c200600303020350140045140360380003026510680c400c0d526244d040c6d8a60380000c03294061010003006626441c421 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 487342715 1250 487341465 487341473
    0xf2301170105090322030c03030201090b01140a0e070c0f0b0603010b030f0307020f0d020316090506042a03020c03030f0109050c042411070b1e0702010804080c0a02041b030b01020105070507 83
    0x5e4040d20000030b200c001c05542c42c0e5540c40b42c0390005500c180c0040c2c2d119a440800d100c0e5400d1703500d005011200d141440c100020002c0750b00e40300984995a150186280000c0350207009080100006a21103c480f550045619200001c4130066a5590003907280801d0b07000705080008141c1c20420784c1c1c500641c00c004095007084241083d111810750008007031b00703100380181c0b81040411803030804809121092414000c1c10002c850740140103910072809e003902442e00541240841c4c80c60134943d4007191380408080c0742600640303d200c0b0741404912002081021556007100c105050b156048001e200c50346660540d00000e000c2e500a241e01030000c0842c00b00c40246015100c501041d0380e007007203c2418000d80078681450703c1907110744440000000c02900d540001000c84544505482040b420702081e81c000038402500140010910800001c0e07194041720204100c00d2041d500400500140416401c4680e00070340c2c20210501003070511036910b11960041c001c984c802c0381c0030355820f0705003101034807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 487343965 1250 487342715 487342747
    0x3050106080411220504060c02060105010c1709060408070311040603080306060a1206080706020c0324040c03060207080a080a09030519030204030203011d100c0509040f23011701050903 81
    0x1294041c210b401d00c804c5076540c01d09001c940912400c0000303010b107850300b02102074801600c0c1801c11500000018080350381c00109140f03030181c001044012407151011001190300c1402d0340c40758003440100f03001446100c000ba424054a104104400450310307064203000030384443c0d000041c0078200a01c0060064203003140230701144c5400e454400500584000007004444940d040315000c0e400400040c044d560301003189427406001600104020704101c1140040340030983c00410045400001180c14040c011030640091a0401800c5558000505e00000749030300110130200825001000100400c802d84102c4100719019141d00f85800d443c016140e80704080d00d0a0082132650030301001c00580c4003445441c002e40d0080b01d0140180d51050780f194601545a01d82d05002424090b40398441588201601d00c0080d06580101d800e100c0452588050854030b400702c014006810400500500307000203540c120b982d091400c2c2c07880304280104509888080329101e0349070b031040040700e22148540c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 487345215 1250 487343965 487343993
    0xc1c050711012c01030c080c0a14040812190315050103020d0207060501080601090b030f070506090d0b0f18010c0912060b0607030815040606020d0804140a05030c0706030501060804 79
    0x11400388030860119030400503c5110704035406821482500c5818a960148a45c83d564501402d0801851400340320200c800d102d5400309200300281141d515404243c0b4005480140030381e1419100582c0e644583c45810750400309004400ba50406c10300507289010f4840c00141c51803401450f1070031420070700150701039840241d08035041a401c00c0701d05d003ca88180300d00b038040d000c10000740225500d060030140a940340c007101da1388240c01588000d810441d0000302ea0080320001c0d602076444050100000d180d0142410001d0412103604040004c01c0d002120b03108e1154810809840d0441c060081c864200c545c82504c42000c5103107010240b0500310754400b0802c42c00d104510201d90140000086882508018001c4011542c50414000d28040105841c264485d06503010401e9a1038600025500c01c201c91201c0f041c0031058000c00c040c4580c04050411a130000720444400810710325000d9a81e0307002d925402241c0c012801c01052710792090083e50f0407124240c0d01e0344180c0e1515161102100426 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 487346465 1250 487345215 487345217
    0xe060306031e10020c010603051519050a0b0402031501083601180302150a14060f0f1009061403091f0e0a0803010816081209031609020c1c05071101 65
    0x1040c40420a450f0320700041c4030603c299070020540914503e840c0f89400202e1840c1507080702d680c000c00c61554030760702c1c084107000c1225001040b540c40307542003840200751030310503660024000800c01c40e403000c1d40b0b294110701d0202a6034900c2c559075000b0480342146a402041030344081c003039114a0082e840d003482480e106040000000d4070310413100c40e100394058009000c6016030800d4021480810310f42141c1940100084403d02089080c9000704207107d200410081c0304103da0780441d04103071210615200340c00005400d112038540740844c06070080360035110303960009170480400407942d00309600f03aa0050003054024441a988107201000c0d441c50601c112686640c0c4045c01e0001c01800c0107014030443c001d440055995040403140e0b41000794194100001c803c1d8101c003080303440700000d110000d4100041e4903d480303600540010382003c485246c003030504c60901e81d0108a0030141e50041a821052000721150010380c844065090058040c1340e00216400b8070560300443c0c0106206000c000c41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 487347715 1250 487346465 487346473
    0xe01021c020705030d02010510122409021011010b03190f08070c0b0d1d060c03090307051b030c0111100f0e0609150601020c0a050f010327030e060306031e 68
    0x3d80c0080707864941c1c07006031100144e4495041c010305001900782d10f005086000d41d10b000480311070300c1e0380c4844545041440ca0b85050200e002c00107424a07806400b4461380146180306044c092803004202c052041001d400f29460300c50b81032401e190008410380c40110510f1140341130301c2d842c2c840c030443b040708150584881074200201c800040914008070080e10440315140e48071b403078a41c924030032103000f000d445036441481150890642d000044040d40000b00b1a000d5689582d81e03801c04d030860140650040407407080c1c080e40c4950344241c10008843d04401e40440342c03001e1082004440344a5034900580594000100030b28004400c0e811018180718000d0020038000600c5e10b0741440c1c08412038543c2030350b8000b1440f0700401c2201800d001d0304100240300070000025428000b0314080f400e403150ba0710038605040750300a41e034041c0c4c003c0589808541039000d040360306502c3c0c03000c0c4020040402c80000701004040d261518048060f00d02900700a802820b50700364001000c1003101c4034807850411441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 487348965 1250 487347715 487347719
    0xe030c06030403140c01050702060a0c1d03100f05060f0a03030f03020702010e0a030b07030e03090f01030911060703090e01050a0b070b1f1508010e010305030a080703020706020d02190e01021c0207 86
    0x30f0711304000d00000724404000a041c1c9008031009041c807001418070280c0504010f4000d58081d80b0005182d200080100425120042040000e00d800110f60995001c582031024207a520a000e078441e07031192809481000c41501c804003080300141e05400002c4c00303d40b02d1050308004904c01ea024003d0244107040484c036980342d0b0b500240c3c03500806c1d031045032079403240410003442541c140240c41244038548000c506040071180080e19036590812410704150f80c030843c2c6c1c0140101039000e100c0c0f009000d4941969140d46040c0202041000e00811b00c1401029000159505101c40d00b00d003200c041c045034a08003034040e510084024000303040c8800c6020030f4041c0c5024000e007a040c0e9030041ca03103405501c100344424200507211400503404500b00040d1080100080b4201008880010b0024980720b81d8564030114141c0c024020400050100362000c503510414100d198000c1c405284070031541c030303041074904100316980f40041030100c1c0160800142c18692102a161710f00c0e980000e401a208483e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 487350215 1250 487348965 487348997
    0x16030b061314090702060610020102040b030718140a030b06030a0507090c020c010305011805090f070612050112020d140a02280803070c2907210e030c06030403 70
    0x2410044072403201c0d0079107030001c20245501880d01d9034000310549804801c0d142143d0041c1d12044014440350044440c1d4400c03070b0450b4400e60403100980400541561207040000009140503a12510130340000b0340404046405851800c0381141c400004003003400c45c50440d40c40440000001d02000e4042c841c403d0031900141c41030000c2d03005040740220000c3c00d9030070701c1c0b0024503104e83c08003001d05051030240144034140d004100c1a255401d00031002c01c09484103407215240500e070110720703141d40c05558004503619078009800501c0c0c41d0111801c1c010303a626130703c0c5681c0f01052004000c1d803240510303244200042c12036691030300741501c01040e00e4910750f007500802c0305203d0107514440a500782700348103c17041c408928941c000d801c2d0b1100a40c18465165103a03800d00a0f94018456150360300600700d00c020410090050260140c1e0304030a45403803441c034000103400c041340e8113200d40411210444034000d109603000843c441d401001418090407140030700082e5030018000303604002900380d07002d54103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 487351465 1250 487350215 487350217
    0x6050402162d020402030907030f0302060603100606051c0e0a11040c0201060b1210050d0302060412030c0207060c1703010f0608071b03031e0609061703040e16030b06 73
    0x1008081c266640ca00700303140741c052044400260180a02200c04a41d030714004610340c003040d1850341c150780050350703a12010b15151402406920040400c19803009010405602044e99800b544059049401d03d5610724401025a41d460196900044c1d05100210703aa490080c1c00140070421a100020003441000609080c103018800036940d40c07520020b14080d0f4103045c4a040f8124442c2d2000f004011305049070346e40940b08000c004090f1814410108602420310388011000700401819103188400b41d2038081d481c1c0300100d84c151801181c0c0405c0303000d010f0080c096107025106980c003400602d400c011041e03d004450500680d06580c05924000c6e01c0700c0c140000318040d1001c0320410900500c0d003a4001c0910400800c40403c2000c01820084014110f40c4600d116591504021804130440d071098080b00c0a560040841941080000a01c0b134945500c04002d40e005089505a5039107030200c0a603482c402e51151703140c00820440000d10300c0744590040c1c464040603150104901031604009902 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 487352715 1250 487351465 487351477
    0x1602010e130e010c020f030403020306190f0c0e0319030f050d060909030201020903060106031415061c0f1103060a21080f09040605120606060a051611030c1e010c0606050402 76
    0x11a03642c4c59030780c09003a4041080748092000c9000a41c505030440d0b000c41c0d1215006011b041001242000c002c00c00d0200307030802840340400610802c816808420024001c0d070b010105c4c01c1c000d001d441a009408040c1607d22072480c0c0d050749130960300c541142d200b00d503160711114510041e1035440001140890503801404041e80c000c1c0d00168881e030281d000c040c100742069010800785460130551000c10341c00600c405d5880381c07409400b035030240380c0d070004030b20b05200c0e03200d030564248900032076050180d41d40c0d4091910500302c0101080541d804013007907d4184029102c242d885040d201080041000840b01481000610a201140340b0f42075500d4254a400115011020322408075080c0c1c12400c19205030700013000d085541d04809080c05440d81e4440300043d005a004000010fa0120400e02640031030b1450f4803010082440c50810f82080c0ca620300b8503280080c46401110b18070321300e074031f083c2c3c4a07000b00120011882800303400e11001582c1c400400c81c01101d0050700e4a000141e183e483d0720141c12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 487353965 1250 487352715 487352741
    0xf080702010f23164e0612020904060c0e060304080403031b080a080411061c1a0307060c1110110705040c090e041e0f050d051602010e13 60
    0x9020405031080c420410024120003000020008035550355521001d217115070704c8610058860010b0103801c2000702100b0060407100d909140c82030821503100f90080741c2e03a1005114040050759111130210016450003940694469030100100c0c02046941e07000c001d00c000701d41451490914428007103a40f94104650645000c60049010000d05070042c0b040101a00d50400c181c2d8502165514002c0e14041c400d0b6980070441c512002a0030801170303407030403984218001c09040d11020074089248144101c0c613012a201c504004000c0c901054401e10203501c80c800601401e08175062090440340d02061203010f4800c565555020707002912015a002103986856030f4107010445600c54151801800d40d000300e00580ca00040e803c5401e0707010313640300203071070b10013903046c2a42d102c07810460b03030030b074240b80c09426007107a028007640411030101ea20f8407a5611820a6600c1d201ca0341900751000c1c001c02100a07103041030000c846e801036120b00300c41000050018424405c01ca8900d021408407010002d00391 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 487355215 1250 487353965 487354001
    0xc03160b04031214131115252102030712092303070b0d0e0d2609421503071a0a02071703041d0402010f080702010f 51
    0x7005150380107803031484a048140302804a0340000c1d64064414000a1128014808414040c8200701703551350b1250070800d00074030542d94510350801c0000e0640c0004400504410101e0b020006903000c025202d4001e90404444010011507451200650408031081400c5020800c28000000e0119580b0543c051031980c0310710f1803604021001040080c9012420814161403151440705c0e500000c07580e01307403090010aa83c0303c40e0b104d050b5001074202289100c0d03041c0912034410042d66405100c880e12000301d0a01f22840040341902d854811806a500002d5030700700441e00c480310411001b09014140340c5940402180b038001c00448420242c810014050104a909100f41e9541c501002440301008030040c2101519005890018440850000c3c0e04c4020102e21072031001d00a105070001072410009501568550080e401d4403039105004c0e1542d02d0442d81c46a21104c1008107886209641c1078648000b0104803180c2030ba03100c00c000703002c4003c41d0348070030040c500014140030780500400c10300d07000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 487356465 1250 487355215 487355221
    0x41d01060e060a05030316030e01261e19020304080f03040615080115030611090303070501200f03070311040f0902030a0f020c0604030e06040905070c02010e1012020c03160b 76
    0x80040e003034940c0300511030391041c400495004100700600307c072282d00d801c8c00c00c4146d20f460010f84016050745400d420b281600d02d40781054001c800001c0d48114200d0b03603035400141000c10b40035240da0060f22201c00c411000d1841d400015030302e50040d6007040c003c0308503a00b065102004107c40e03070700c115001c96450f40c036140b04140039040e0411250190400743c0003030165801c040c520880001c0d56100150003d0307107074107041c1a003803000030444480c4034020301525501c0742c0d2814410301915074255020380412241402001110700c0d002a501c000e0511114203165841d100c07403c4000e008550050300f8840d1080000040c1c8503010341040e0000c094104000d41c0f03034503100401c07900705c07513182c0e5800d45214010003301c40031030808075400f50b01c181e01d400c01e03060000d42c0c400811614061500801074952800c002c1c810f11b282c0200300c03a03440c00d200f40c1e603000d01d0f1102901403180203109062400081041e41c06030722035207542900904848035003e0300316401c203c0038400b1190744054210f030513910003a5110034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 487357715 1250 487356465 487356469
    0xc1b03020f0115061418030a1214090a360c03060e01051c0302190f11030114011a0904060b040303080108060903120603190c090c031a041d01060e06 65
    0x2440180c1d180c03646443d51240d142c24000b50086504084078006090b0002c1c14141451031580a00c1103440003408980000850345072900025085a00b40b40114941c9405440c154543c00c0031107038000405080340980c68540b1009640711040c0803400c406400282c00e4064540410b031306030140c0024401d001040416540304064200c650940141070300b0f010160041c481600c40010103105040c0c140c1c1508003130ba02c9802d00703c0c20312607030700700c0d00d00501030343d0f400c01c8244280030b40c010051a001d4400b64400400b60700c205801c90740c8840d2080b4009400344010080030360407a4484171b07590200380c50245000342c03140000741100d04542021000030760200e824000d1560000c206805001041e000b0842810305000325541c1e4010703610204580941c903070008115031000e1041400604100701070308100760551070326510200c2d4a000c0e420070b283c5040307401c0d806944680114110803000b950000701851201040c0005400c101d420740886642c80941d07250000401d20621005040c886000e9000c0d080802c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 487358965 1250 487357715 487357721
    0x10302121b1c0b1f061e05131e051003090b010306110c251e030b06060702090f06031b01080402101e030f1109060904153303050f0a0c1b03020f01 64
    0x4407008001c15285010036501b0ba24200c0a040c0509003041602e920881001c0251310030f86404c4480c140910100281d45aa6400d48020550f682104c0501c04035030b450300100e048583c0024081d150009100c01000801d5184e07001011225002c4461441c2c40314002c0302d1450a014600243c070b0304020401c08a11310f1607008001c2c07003d81000c3c016040c0c1644245011103004440d4000540300060300404180c0542c1c2c0c20007111003d6502820b92141c40c03808004c1242e20b01d104807034150081c002e0b0f03035041e40d000a1100711034084580503142c0080366103841d024010340c03c446041400c01c0c008a0003980340c0d6a40381c050204408000780e940800c2400c507442c8458281c418441010f0480314050001e200d460b5100001d850810000f0794002403008091010148080e5450340000c0d40030121068880010710324141c0c8184080c01840d001c66081e90101c805c07401c9800c1150b03990500008440403455081d00340d005803598038030a16106000405a25442c802d00075200e2003240541d021119102d000744083c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 487360215 1250 487358965 487358969
    0x215090a0c03031d0a140a05010503090a0b0a0b12072d0513111303020f030304050d03050705010227090a0606050f090a030b040b010302121b1c0b1f 65
    0x240a000301840c150740d0209040c14900004042c420540c140800300b42d44452541c11300840140916080395880c458005501032106680380a07032903000e000308155004004072400362000100401c4039a50783d44034580040c0d8003034078446c4542d81fa020040025520211900307035100d0008003811115150408445050f20724000c0e0040042c6003024041c445003540b0410012107200741e912006e0258505100d000502140c4c0d0151400c01d0041a600b58660a514410f000d6a1099031105407118070407040580d203000314482c280c1c4c070502000608000900c107a029255051180e0000f608040365903090304c0000390003586c0518000003d180d10340440c42c0160801d034210347d10640800009082c0a4014103d12440e0031044002c0c00000d00601c294841150300c800458000039900c00904080c50001540c0d1420710059200301c6540011000c0c82c000880d4110703002e00000030018030200da48007445025018203a000403900d44e6542224081554000e0881c460b40c8140204030040444684821183e001c1d5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 487361465 1250 487360215 487360231
    0xd0c09060f1a030a0519060e071b050616090e04050c0103050c090a0501050f0c0106180c020d090302010c11370b0d0207210c0507060318060b0609060a0215 68
    0x2c1c0c58040280a03403034046a42094101ca030104a99490040c40c43d5003c1c0b00c032254241c3d440c80d0081c00900d030302403584428021101555801c1d005030740c030844403482102030040a46660043c40c049504452100c0380b9014550217400d010007080d6582c03061400000088600b5a01a00210740c98282c3e136070b0503c40d282e48004403402d00c0d030030704206501140b509120b502072181880000641c1d00c02c94952942034800c9104180003d10a99440e65000c1c03215581441e2492006401c1103940d2080354000f188a40d81455586ea4040300c66146400458040b054114250b40f01070070801c03d0b00786a2510494520180d5a0081c0c0c0403602d01c002800d1142c0011980140000c42189081030050f04601c000b00c5041c080100e0001d80c603511a800c00ca520751055400c121300c03ca102c06070312801c07035801412120750780c0c1c0240107940320190395071026015580c0031015002d40141800d0a80300281899000c0c08500c00040d03c518200020704001c10219032000d5255405648051611140345180d505d221740c1c06542 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 487362715 1250 487361465 487361489
    0x20606041d0a02040b041107030201061a0703080712090803130c09060501022a190305100506010903021c050714040e0a0809120109050d08090f0d1d0d0c09060f 70
    0x8061101d075215a10000002e00c51a11010071914a5903030f070300894041c0280303003c5140c1d11011860080d008200700e219100005200d074018004180300c64081e1804180c2580341c1031103c0e5074021040394818403001c10801d40d1691000003402007483c2d000a50b01c10340e00c4114032010740c1c0309402d00c01111802980025007a03030404900b0301050740c1c0400d0440d1125000e002ca00b41490f4459504800040740c1002e00ba04404104080781401040a5005045a000e034064807100c01840800b24141d0f00c040741c10718003003002d240d400c01c01424410062002c0d096159507006120340c0551390f241c01e0002a62064801844405010001d4a8541f0580f03003043c2d0104010400441241d540c00094007030140302c03d10401e03070350802807201c0e002900854051940031090310700120000601800803130059845680030b22036443c00c665000000100b50000d480d0350785415078000a80c02c80c4286100c40008619008280e10740f0250026410500390b002411500c040818124209400044100a103502c50441d0402c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 487363965 1250 487362715 487362761
    0x10203180c220b040e0307120f020d090b030703021201090e0c0406080d03050603070801060e0703050106020c09160203120112060e03030c1c090807050a142b09051002060604 76
    0x1d4100d10007048054400d400b083c1c40856500003002000155424400c0d80400140d810402800b04103030100004161180000032400f00b03400ca0380d40b024801d843c00811046101400b00c407014101540c2e00c205186005444c00c0c0611050103a1280203a0115400300e0300e981000c3c1c01d0680c280804000d8041c15103080200501c0d0051751592464074021503014503560301d0100381d4945082c8842030181c0301c810b0003840781c3c0341d441100c8082c0c090100d900038002840c00d00007044c81c604c0810481c030050001031000420351603158250100c145108800c505510040100254101c00075207094020700c109510020070080380d04000c010340d1502d10b03a03c0c0701a0000c00c10001d624540c5020356000d25061500805c50400e81100c02c0c0040c001e500c400381c4049800f0034503204000c0e0000701038180340c0c410810306141c503052947e07a95403500381e1075540c6440c074906884000b40c41c0012030f820f03035411705501d001150300d07075035034045030382124955240750050300103004202217400c0500501406507a82ca01c0b02c0a100b03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 487365215 1250 487363965 487363999
    0xf0303060402220303080103110d03020337020a0213050c070f061509021315050f07020301091a07020f0c0a0303080601030908030c0702090105041103011214010203180c 74
    0x484010300d064859640894981410900745031046042003140064180c45a141e00f009000010244001c5130b21719401340700904031741000c00f00b07a0025a8103070000c40c01c2958003019541d20402c8030125010591901080c020403e0103a01003084828254000e001742c42c020703006010480da40a49100992820001885240c07078840045071100340d004006540f6496140c90b010b000340403102c2d0200d45020007803c0c0860240c10716801848031100c1c6140c4092a0350f84c4280e00d2040c16106c4410710007145080c005843c02030405c0d8002c004051000700001850145ca65075040d501a0a000c03140e038011000d0304106400d9010002c0814070344d00d600083c03036240e20140c00600710007068000107003000300d4840484c03150b90181d000011a55404440291a07203040003000115803c07160003079108455140000070181071500c52444047c1d503040e142842c2d80c7c00c1000c24080745181200490700d8a407006d03031800b4a964284040c1d030288072101c4118012800c424041071030000b81d50880c510030400740f0782110b810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 487366465 1250 487365215 487365217
    0x120606010c08040e010906052404050f0d02120307031d0306190f060b09011214040813120605060a05120a06111c050108060709120308060f120c030c030f03 68
    0x441000d2030440107918481c60240c00c01e0280b03a10a0603550802400840d8110254100c042560300a40b040750042075061150641a8511030814901010410081c082c0f800e280d542c86040c0c900141802203070b070041d5404103030105d9800c4004500350700003152000801d5441900c03c0b8502e0500100c0d102151403001c0013030745407440034049d240c0020101020300341c1120036070000c44202004010420000b40c1e01c4000c00d103680d01503a990b90001d0b490083d000e03400c80540c0300704040b0705281c0e0080c2400c1da480b03076280241c80d0702190b0460010503034810001041081c00a248007218406c003001708240c1018010300c0450f00554112a2241d07400011500b02480c0014944020a40020011030b06104000c00c000141c4a0001001589081c10b40d02d40240c40380c41d00164100c40501c0201c0e0821341e64000c0c01c0340c10100501580d80c8540382d4400c5100070902c542c1290360040c06c002c2000c10342410100c0080d8034003001c41c0d03100c8080d81042501016902d400d00c00072501c901d069002d000590060a021910303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 487367715 1250 487366465 487366471
    0x4050f040507060c2a030c06022113080303150405070c050a0f02040605100302070506010f080304120623060a140a17120304140610050d020103020318030d0f0b1206 72
    0x100b1100c60321280c1030261540c110910794103240c1700c560516803006240b10340e503c8039000958205041640024282d03100003420306a41082082c0c0204651400d01482c0740799101ca00b2079001010701c0b51020031300e0308080c0010360141180034180c08503110444240007c4d00e5004002d0818050400d0b4103901090000c038004182e141c1c801d001969510040c030001d00108001e81020b0340019141e500c4191140c0c040d802400c00c6070090b4110b980e1681d80e10140241402d10340070310707103843d00b003881308104078140610481e03401407141c0b10105640034000c03212102d04944100f102950040740d4240312840c00e201683d10058406040c101e04141c00c500046624040c651242524195101042d2901814180915585980c0b41c031045c4d5560f0074181804036443c1c040c403c0c142000e00400c80881c003801c80703103110001283c1c1c0161010042d041d85400640082d000140a9000025405042c0c482d40d1000d2000b82110501000c0010b5007444098002e01291580c9a2081c0a01141c82090741000c000160560b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 487368965 1250 487367715 487367717
    0x100c0c03050921030d1409010b0f0d170304121b03080105120a0f42050a02160b070e0a030809040b060d0204080a150504150506030a02130501030204050f04050706 71
    0x40030a001c5038071402c8071a00b07010f1000740000b08514821455680000c16100f91803c0300210549031072100074202c50791600300d240d0290394a4441e01d414201001e500390740d1360040381c040d41103031040d9802141b00d51084034121422141c0010036488203812030102041c2d444800e011001c0d20b034003aa0082d21400060050911550304864240c076203107010411210466403040350740918003024500301c1c100024860200704400d07490301e00c01080011092040064007050700c124000a0700c8040c80034000e0801411074006036400700805140340c406040005030062040d5961800791900030001492071410841e0f42d0703c10361320300d0340400200d41901c0960b40030b0642160002101152030700011418428103901c403101c0c3d400814005080c40d40481e40380b44c4540100000d04803004111105400c81d142183e0081030b0041002e10025070b00390070781c4107642c0100c010741203c4c0c10288507000281e40803001000382603070a8540c0014000c60505010700d41d0000f20b41c0c0403034609130400f81d49080d1551103a002d540 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 487370215 1250 487368965 487368979
    0xc0212031e1606090803090106050603041505060117040b160201020903150a0204030f0c1a0703201207230a0302100b1c05010209150408120702060c0f100c0c030509 72
    0x1006148075484040242ca50000013040b01c2003151801070b00c1078100300c444081651030b2100c00159030038154100c81c0b241e40e22010008003454440016030003410050585410070443d0301c5481500c66441c4905030169000c0d81010080e840c1155641c402d01c0c000000c008210390051000c2c1d20152400990f500c48070060190311000c0340d44011000d00207014a82c400703450000c290700c00e0014400c080070480240e0385034000c0840070141d018840c004601c28440c005000501c00b4614900145050519070210300c0c458059520180305807138100640d4000c3d10040da506c0c410480500c1c000b114003070302e400d4821400c0c0e01400e0060510b86003e9101d5030080302c0d104610307071242c40000040c4e55445015800d225101080800a4210308100d0f0007500009500c40c0180f503910b160304100c80c1200240c404564040d00108088491a42e00407916001240126000031082c80344051001052084103c1d800003140149420200350800c0f4050f200b8056404040c4065445440040f9a00c01c040b60300c030402c281c4402c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 487371465 1250 487370215 487370227
    0x11119050c060f190e0603040602090102120d0b040b03121905071b08190c171005040b090d0f050901030203150406181a0901060c080c060103030c0212031e 68
    0x3190500e4244a0959880840002c80380140f03102400a0b01110a46024a000c00140700d00152003c1c0c1904450701e42c0200280006000038601c1c0c0c004110800040c0705039144442220078809003600510540c0701d0f805e4640d250711560381020b104841e40700784220b0080591541d2609103404a1103880182401000c803c2c42c1500c009006208462009070302c00301035200780f034403c44603003d004c842d80121816405015406621418104201542140c104100d060000d2406848180d403001c80120311006000e954800d9a1060891007058811802030380346003402d141c41400713a402c003240391144900740802031000d820b1050703020058516880c0b080c00c0c0143d0302d8895096141c4001c2c40d080d1507a03403141c00c0007008200686030044035814604512000c1c818502d50134945c901c1e4103021141150090514030041007210f206603031100d03ea502400c2824a0081c020030a5414080b00343c0007600410071302c00410b02103041000e8070000794003600c4040c5043c40c82e000038410861350034000c01c0361a64408982c1c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 487372715 1250 487371465 487371473
    0x302030604151401081b040905012d0506090102010b130e120304030504030204051e0403030608100b060d1505030f150709030b27010e0c19060503010b16151505011119 73
    0x14030402002d641b42c8a0321540c0d110003403400740c10b0134000c1c080e061190400140150260950500781c95880306c40c4600c0c0d5030304004c240261900320050b21411036403103511140c4c06441d41141c1b64480701e070306040859441100c0070558601031b40c0107800034000c1c2c000c00801021940c03050a4a003500d1381241c0104141c2c81707580e00f4400316076017001b456000b1400303003050104064041d4401d80c11620070f4400c0c1e492401c4400c3c100c0b0111031001c48280d80142c0c0402501d0f8280c4840e070b110181c0c44002c410310029160316200070900c2e01c0c0f01d40c241e5449541c040c42901070b012980c800e802d0f0f80b0282c1460301110050440d0b6503a005e100c000b520110080202100107841e019488034220544883d4000801001c42c0c4440000e0795401104c81c400c0c0241c0d481c0c60171320074445a940045081d1465a00e8803403542c3d2070312042081c5540300d1145009002409004107000502d190880a950000e400300492a81000802c3c0c03a0b404446602c040c0c1801201c05800100c41e1021030324142030013881c0510600400e407800c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 487373965 1250 487372715 487372741
    0x31e020904171209031e09012a1b1a033c0a09020916080c250308010501080907081b12010e070314060702100207061b030203060415140108 61
    0x744200d40d4410b080c00c002034010000003411b103000c41c255034825103540000044140788511400180000c0110102861051070201203619079023011001c02880d80c0280ca0301e074900003011070740c0c00c02c1c0c0386405010840500c100510141c2805458105495402d04a80c21700030002e1652a039046501026500c10810154443c1007200300440c00b0005500d251424000c0005c1c070000710100c0c41009800d0114400c5214246014000d81036515800340e142c840040316040c40d080419010010320b58500c10641d61248056140b5503580700f6120607010f541040e00152a441c0d000b0300d1038960f5400342008011030701c000030302c205030031210f081c050500c038040c04046510402d406005030320325070034058a40c103d481300050303441c1120301540d0710540e0301052a8881c0d440e8903040d070f00080180c4c0600707500351400e68260300801002d80708050000c1d1112140001d003668041800340d02e40485c0d404400c01c4098182030003400c245924000c40549103d04020300e00e050564010702c410304008a0700c00244e140d003e104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 487375215 1250 487373965 487373977
    0x20310090c0e041131080a050c09270312070c050c0609010e06031503010b01020607020d120207050607090306112712070b13063612050106031e02090417 67
    0x41c80340000d43c007082d44402c003c01d0800c00001c5c2090340a880015904004142c00800c10342c4003001c1c02c50705030204108289000090030305481ea0142810b031101c0d9000011040041803c008040c54656001481c2e60203001d82c001c00043c240510000741e080000c20110b01e002501703204540090b1944054030048512a040c1d01d15590031900010a21071020b110612070524402c04034000d00018a0f000012611800c06440e0140580d02c42485180d1060085009555402d045400141412030b1070700ca0f01d00d8403070305603824408580c00e10003e0051165074014201b0260765014074901c0c00b40c205014481d040000b6a042d070000310030080841040d5500640d40c10006d2040049414031030300c80c0c54501c1190700503411007070000c24003240000e646024211001d4200399441072201d40051400d807510800c2039512003200382042842e03002c00d242c55001e044446260085000044a9080d842c5c5412603100b185c0711854612003100700b14005075509003001ea8050746c441c00d11000c1d000075442c0543e40f4002c803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 487376465 1250 487375215 487375237
    0x1020303180f1005040606121a04030219061b08010f1e0b0415030509070e01121401060b041a18060c03130b03060f090402030c0d0321020310090c0e0411 67
    0x303041c050204000b078000600036800b5000400946965034040d660441d03074154014082c40080035001e900c04021130001c0d2b8044d00a005a4240354004858007110300d820103011102c150783c078900b41912480b006044400c00342d1506044030194142b40341441c4a0950740710300300340b0041c241c09800031201c081307001000505004445540f1562102c0fa52038a031308250414100103840c000004500000000d83c420440e41c1104d60f00c40641d0816a0f034881519043d01d081c1e0300d4440d2883d47c4140b00c10300b44903420041c0203d40030107441703e08200980411102941c40c089040d1424006460188880d0300325000c071070811250b059840710350310300c41c07403c0d030258055101d440122201e000540350b00c6140110b2046004507991221610034002b000035402051310080d4059100071200c07000c1d400d159204c245814028200350210088008200040b00c1d01e407151114015008410b01c4501c2c40340811240107070001c13003400c0c8919030790714800401040311045518032581d2079000d400e10b6400540101d4021040e5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 487377715 1250 487376465 487376473
    0x803090105131e031206060e012a031209170405030114101202030708010c08010f0e04050d0e0f1c0201020607020609030919090c03060e01080a0201051803121602011d01020303180f 79
    0x1d940c0340a4903c1c1c0e0f90101c92342c0401d0001c4240d1003000b02e07910040c1c03a45036004203140558065601c04903800d00c0d000100c4908665240c2424000c10403403c0e214801c60010043c560b42c1e1070411052600b0f6891000c2000740507506c4005000300741405007582f20035a00785035000c4035008190300020b85801c5441c1d0010300c1e55480d046415440540c490f80c103505950034110903032000755030345000101c031000480b0040d182d5000000a45c50701c0c2e108000d042101e49004104620703100005001407040e13020f2001d1207840600005403041156014002e84d071f0b00240310b0010b0b04ca13900c0c000300115103074854a00528418414070840208200f10082c1d000040c005969081144c9005620081e00500c081d005a4038603c02d5000001103c0400188000120f43d040c1d581c2c4c0d04010755828441e89140703c482c4601e41c18001d45014160403483d030000b420402119902c11036040c0c2c045d00015004680d02c00c070350260801e80800c0002a640c0001c112500410411391034a508030100003d107040c00c960b035135005501e000b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 487378965 1250 487377715 487377719
    0x1e07020418050105040210090b0d0c030e01020408061510020a0f020a0312080703050c0f070303021804050c1902010203130308100510020f010501050607030c03050f0d05040803090105131e031206 85
    0x2c056010511480c400c0d9021300d080b082c00c203800c3c3d5803000c4038400d500440008104c498000582a0441c0031001210f05000c9a41826042c081c0d00760303003054215a409e64018030400c05801c0c418640880c015009503407840113001d4080000f07480301144100508010509450f100071500d0f000000030040d60001701c1c0010f1114841c0b0014442d84080c2c0d485000a0709040119040050500c00c031940587c0c0c4880003807a0003200d9a094000c0e40000c0541e001500c40e01001d421251030700d008480c40f075011480703013582e00d15540c0d82d0050f042c81440d104104683c0b0620801241c0041d1024445115406007014003582d9190070310602c88210780d40102da007160b0380c0c03401c02000640016000c944050240001d1100b81e0b21134041c412079000b15040503001a8144c1c24441c0480d000f00001c00403800000c1c000303842d141c0a02e001909540091710200c41550b40003042204041c402e1003865005051040480ca1280c4180ca80d01e6071245510404c681508141c03800804060088944e41183d842071501417020719 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 487380215 1250 487378965 487378973
    0x61c0c050304020909070e1f0f0902130e0105101d0a0e061201090f020d0c171f02070f02090c09090c0406030c020f151914010306060b1e07020418 64
    0x60001e4030200d000c0c1100e44e0100d00408008a00d010545001d101d400d42941d40b03c001300341104200c11a11041d004110320b0105d448050701c0da0000141900b02d10240e40d6000c0030301602c000c0d070702660002400c50701c3c0320010300040e6034600b40141e10b0556850300d000140503002d0840c000c007080507801030740322640742c40020f0302d02104000700784a21021101d40c240506440c0d5500c1c20390341010001403d41841c00301510041c030b1300c840521041d901a4910150341503d400200c0c01c1d440b4284000541130b884a204090200c04004081c0c0b44491500000e50400840b55501580390a901c41f00a10880400e00024a030b600741c6400e6918058004043c5a02410084c24184440d8807a0160b0030009007000122041c4600010700c9001d2040b1b241c00034105088018000742490b070b0042c0c4266548803820100c42d100100e10701445001c90300106592003a549503241c5001200c05981c0024036401d02882580e0065603151400540070f00c8401c072007596a50341c0c3c4000340080117110003071101051590fa4500502c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 487381465 1250 487380215 487380217
    0xc050315070e04090f080309030c060405070e160f030b1f031a040209060304030e0d020d03080f0f07170907031b0e06010c080315030c040507020102180a0b09061c0c05 73
    0x503110584400704039091950500080d540003c4c0083d00740080c1004210014400c00019603104080c00709aa080203a0040c21a08194056600f40d61950010209100204d40b41540640007a0000d401840d2104800b001030b0502102c41040024980e6400421010341c03104000704081d4480e003070f0700c2c0c50381d074104440103002081c98114000310b84034491401001810540300701ea00001c070050189007150f49070b6030110303024620380d003040d6002a1109030100040e210f010256000301c0c441d40f00c2006902e0a405c100c60034000003801104440100418802c0c6d41ea009220210b81c071f103e40010700c8007580d0b004400e80c5000b802d980014074015000c4981c1c0d08070300d0a4010401a590388001880c00d988580c401154010608000038004e91410004140009502264012000d4010341641c162151100020b0100c032030032104400544d4001402c014059068111111050300c00ca07205080c01c2e0802c503045501f40148206a409280c00143c01050032411815040000c00b41010500c41e04614000003411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 487382715 1250 487381465 487381471
    0xb0a0c05011e0b0402040302220603052b170105060a05041e06180b04260a05030306010216081507050c0a051b0f030a110f0d06060501020f06040b070c0c050315 70
    0x411440c00703e1110482ca4280221800c80c2d4000700a00c928648a00440d4840c07402e071101c00055595607040000020070600c1a083c4400c400b8082c5009804120703000c40d1001e10300c001690400015149540708514001401e905507042910503503241c042d02c6100f6240d030b11440e0825480ca0f8180c02e0811034903d0045020820f0307603050ba640f01c10002c0d44a40070000c0ca0298000d2000509007840240500340040c4500e02e15040c41451660f07202c8020040541451109041a903030313031700008104070040d6010404407010b603500c0e0503000d0703000d4680f02c4000d48a440421340300702d114500c040802c440d503102e0300a4482a201940070f5502c4862a85001d035034075055100c101403044102000103149180240c03000c1c0b4030b001e000c0c3c0500305255156032404d010003011170399030394403004203c0e4101d80740e06d8223181a45507900ca0040014400e0812001900d44016414908403c0c1e0205042000081c0010030340e5410102a060200da130580c40e04d0300b00710701d80081d08000d400d4403a005100044c694031500443c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 487383965 1250 487382715 487382771
    0x30702040617031815030f15011106060607170c06041a0405030d05040507091a030118120f021c03050604060b040807031707050303090a050d030204050a0b0a0c0501 72
    0x410603035507210350030075600d901c030b8648010340050150348a03180346801007030344004004220710180c0c607810300350401da0b070010b940581325012078404028044c940e144010707800700c0003420045042096417030182e540d42c10060069000349000308440d010085904d40c500c00040101030010b4403155101e581e190b07128030449007502c1050350300c01082400310100f100c5500441d00f0901941c0b410698142440140501030000c8440b88a01c40c0d00240300c00051086040b034007620b113008080554400c04050a48044500ca14840701700d02400100080c201040c20440081500f402e0380070801c40d0320140d0402c074469540702280230844540b015800c0e0f1590000d44142ca00701c80412080e40c640401c40494040d0b409055166800451b090012559224480008005516506280a6035540d8150454105640c501d903264040c1c045001000b0381407100358003107809880d08501b09441e100c0080c4207801188240c140036800080d40041c001e100d9019007454036003210003032100a1a030121079813041d5844501c01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 487385215 1250 487383965 487383971
    0x312071506120803040807050c03030316110303060604030f03030b0d03090e071e030209240301060221030112050a02041d07050a0f06080702030d0f060302090a050402010215060d02090903070204 85
    0x11030b66800449015000c5608488258151340d5a075507400342680c400e46050310a4460005000c201344e404200030b5120b5440035541e9103864a040700007800c026107821014940d90000e00c20080c09881310703410340e01180d4214400b00c80c050a2410160000c3c000b001d2110782103145008450113045e003000b140e070f08070717958405c404455560b8440c0448039010017041041c41c560900109040580c4241c01810340d285005108440c800b040f111081100740c95034999030791201b00840100a2160107000b5840c0020290300191606110341c610000340e0b10050040b54001d100c6801e00c881030000c200803448a540c1d0140042144041d0140040501d0202c4d00704075400384102080820542000c02c000011281d0800740064080d08103041aa01c00700010210b400f144424000d801100d042405410114038141500150560840c0140014980024a5841080d0500007400010307640004c4981510f048605002807640319040011100e1458400280d0302c1403d40050000e000c10200c000c00c0114400c032020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 487386465 1250 487385215 487385219
    0x143a0515091b1e1c0e0613081e070b0a06050d030206060f03030c031210090b13090c0b1c0e01060302030d050903030418020a090501030501051e0312071506 68
    0x481c108208484161400e110030a515a42d4440740000e000302003031007070b15880060000070078411a03820008203c21415980007180c03211000e24441c019600404402600d000c0c580b000d12102c80b40030400b07000f8212540002d8046846400c982c1030314010014030052031303580f1810306010010740419106004580d140c003400061614081880ca02440d50640260800d0703600c840402655124404049405000c02c10101200c1c10301400102000c542c68882c00d407850030320034180c11843e081a08800c0342140b81244040d215990712801c050f07400264500414800d429240c03d81c07964000d988100310b05d41c0c000c15900c0d00003010751070103806440030b41c80820082283d0400a0f090390041d00c0060f4043d00b04500346000b01c3e01c220010091000c01408513491715598a00c00b40796006d60512551340300b640810048a01c5038403a00b4000100340910f01448075504040c009402c1803514070b050070348080c04c414080d026032002c1c060340c80981440f8502c5904c41d034190804840007915000c1401440b8504200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 487387715 1250 487386465 487386469
    0xf051b010f1401050f090901110304080712050906040b1309060f06020c0901210317040c0815071b0c05040c020303060901120c061d041d010c143a0515 66
    0x2070904070784c0d009042a003940c410744140f20210300c015210300442e54030351001d0b4010240700b4000b98016446102255600c2c0c486040180480004003005010400104080105070750b481d415a019540401e2002c3d6841c60046041c038882c8007180d11003190079042c001c0c0003a005101503042d0b0129140c0d6000c0d2080600e058007048583e4400340203d00141d000d4a00700c042c00d105240741c80c81d1003482810200c41031400c40742e0b41c1f48140070464044810702c41c130038070910007100b0500c00006800b03c07543e1141c08a0a1544010f0092042c1c0c15080c40c05c89000f8218009000d030082c0107078020403019000b0408801c04d20002500c942c8100c4070346008145501c00010a0018664005107444d08a809440b01c1410718404640e4541c0f801d0b0241c0c00f449094101203c240e031036104890807100c02007449180c0108800e411402d440c1c0054003001480346511129a00f1002c0b0400c0380c9013800b5031103040342c92400740e81a000c02c040501404560340c1003c600c000307884007030941c4024003030540a90648d00c28106041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 487388965 1250 487387715 487387751
    0xb0a0320040203100605130b04080606150a090623030117010506011d0103050c041824030f020f0d0803130201120204210c05030307150c0c120f051b010f 67
    0xf440c442801d82d00070f04105d0203110340007520755402c0b414004016070359510503178000c541260b0040111908100f003400601c4c5171a1501100003480d01480354100070008501a000e4400ba10483d01404010500d00307000e41d811000c40d0038641100c954a0740c5a5071a030384207103110040d1a01622aa42c600310104403650702a08d08130200442c01103084000d04200c0700114003802000d802ca2411030f00600000c203405010043c0c882504446150008080038551002c40d001400394030510f00003039110b4410700c041401a01181100c80e01500c0ba440803013810300200f120361084e8400540401c40103c28000384002c1d1050303402d282d5000b43c1e1200c40e0102a00d800300100d02c150700c01c914180b609030b0310404aa0031410b1a8101141c080c800c1e1001d11a40c0ea03010900310fa010000c110340d01032075031160914200441c486c8800819044c0380500c80040f1555072040c2488082c1205011700c00640da161501601c500d048900d00203242400360860404500143e01808646101c3c203400e80c10304060003695a0600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 487390215 1250 487388965 487388971
    0x3030406060e0f011509030812040213050108072705090607020706080c0d05040501090516180b03071701090c12140f030301120503211906120201120b0a0320040203 72
    0xf1942c8002a46400010700d0111180c0021106002c2600f10000c0854401c0340905406520402940740b1490316204000d002d40005207d042224038010051121070300018444040e9180e0309110800380b06c145a045178601010800e1145103810581088410381c4045080b40c02484181c00300c4803020f032111016a2081d0f0222000761420805002d911850030781c6420540e0824020782c0002550b002a4031003c1c145400e4400300780c8010b0301c9002c10424070511640411510781114810085071b10008002519401144139407114808004200342c4100c43c2980148615030f030110107818400d0f60391103811800401544141c03070800c1c000d503e0b41c0e00340300041441070f08070a40e000610300c1d6a0034202c20700c20b200100030065030030b4801031011042543caa11000c4491817000702c0d820440d4600f9800b0010001e4684131302c2d03083c240c1803050401c035605402c520400c41a90900303203140d0f20140c41208100401d089034486600040c1b081c2d0000034820001c810341586201d0400440c20040c00345c080c001684015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 487391465 1250 487390215 487390231
    0x9030708120a031e0f0c0f030905060403051c050f040b06010516020603101d04020f0102071202010818061510030b0102070e07110a0503120f010b07020d0201091703030406060e 77
    0x810120b41d00502c00d81c88012400c281084044c2030015070f5881c002200c1419544140c45541c03849000c41d4182c2200b04110b100c01a440c040c05109080c0d521603842d1100544001c0900c0b4021914882075070030300c10b42589410920348100120b00c2c103141c40c801c840340306880640b449030601c03010a20651140782104c9a00e00d41c03c04000c00c00126609000c410341c8000c00d008180c7c443d42d5000724240214266403c0c05903941c10585510781803600410403c0141c584013641598000c0008208841600b40c400c000e00390242044c101c155110080f46c5111491280c5503d80b82c06003804200e82445051110104d441d001e86207200390240c502c400313404440e10141040d026034401407040004601d01c5c22110380c0304845241201e046000c0c40c00d150314108403040100d6282d080400c12181c1c890001c1d5195610090692000e0000e5261280f03000c42445801e130040e001d4044800031405590090034510001c101840040044107254024981c8942050300c0443d040780c02d0290000c0d0000c00520118011029 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 487392715 1250 487391465 487391467
    0xc0210080f04021003020904180516150e0f0907170105060f0d050604020706090f0b0a15050d17180306060604030308071d1302040e13081608090d080903070812 70
    0xb4607001c0242c0c01c030031401c100041680802990b99546c44600681c1880418620a00248540b52400508240200142c0c1400510030441088145410b402c2110ba003051400c051040184402c0030031740b03640b01d007250203420100750360038445041d5014a104841c100b1006007124981d803140b0401c00103205e400c8900303241000600c0201000515680310541041c2c00031300c0140b03071920a40c1c4544c103551060109540f40c4885002400c00c1c0401101c45560020300c5020401107400190418448072410380112801410b0340050101042a4450485050041d11519070b84800380041084140c44401055501074001d00700843c401d4102202030354180c0f036050b1240307201592513010468051821010210011441104840c003d440e501c0c0c61990516240d5070140c1d5803400e00800090420014001c0c403060070980e80f06c0000b107400329096400100c007c80000b080c6101d50304040a04d07004a0f010580c0c400116101c28040110500041246513020740c2a6000c43d6030300c8410548590168491402941c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 487393965 1250 487392715 487392721
    0x212070c0801050a290a080d0c0209070206010303090e07051b0105010512010501030c05010503100905040305090f010c020108180c0a09020d0e030a0909150b0309011406220c05040b0a0c0210080f 85
    0xb64030345e162145005402d00800c0d99654410701d01d0809003446100110b04001c82700302c05d504000d000300e5480503d9000403d420351440c3e600500c9107006120341640c240c46c160100304403510883c00c85c1c6900d0481b5012003201c00f84000080e0081c070082c030803184991499442c0e03640c03040042c020f450499401c5510300c0e848525104c015222507100908a49162200c00800b01c1d241255118080c0124020ba45441d00c503618002480041c1484400c82414800c40c00c4103000140e030301200c0705074010007018240c1903451425078624030300f800038503c0941c0804c2800003c1202031860b400742c5000718090005000c142003018405869209000b5440009540b0090600a004a64101014031150f2a0005c0074603a503440c12005c054100707985840a994407078404145400d02e00c00710540204c0c04490181c030a250507a6000c6198008082c2a80c450b030b1a4188140454020001d5900903e020080b950f503800680344010305900c189a400c82c40b4003240c00441020034898a00d85100c2c0a41d19041c11040c1c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 487395215 1250 487393965 487394021
    0x61409040305090d0507050109050409080a0f110a05060901050c041208090613090506040522110307081203040507080c1c150f1a0402120112030212070c0801050a 71
    0x204020015028000c0803c80326619803980c0340c2425445008001170710700d107810100010001100c6034006d510990414524202050ba150100c0b020400c85080201072810f144c401600c08441c001c0050046010340600c070414007001003103a612a501401c007c01250b0744480b0f19084a000d140900500010703400782d2000000c098900404020600034000c5080090a40d1041040400741d080340141540780c10600516040038001c01d500085182481c0c80c460f00082e4441c3c01c12044a00054100c4078a94886007980d20148030b1213024201103815944102d0079090318076019481600c01311224814641c0c0015084008228540110313002069030040c0750320001c1c0c554481964400940e01d180c0c1d69249411812181e22449551b40181c92010805c60705004018041144035003415001f18010400520042c0343c82689506440b17076070b540c6400c00c04040c00c04900d80307580c0108104800c5400200a82488900c03130345142150715070700003408250b132031034440426194443c1140c003203c64071503400d103006 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 487396465 1250 487395215 487395229
    0x8161a10080c10090e0a020c1c0e01090b09011d0604030807150e10050a02091009050103200316140d02030a060602030a0c060e0c0d11090f01080a030e012d020c040614 73
    0x4131b036001025007409180e1074000d04241051108035000d0701c0c4181c0b2418510340084084000000c01d00f01444100d01d85007002000c0d2041011480c10800103145c001e40760076540c01c1c00c102218000d05040d0700c60b03440c0d103000750003507004110030f961284420b450204030b00031030b01800c5036100c028030140819a881d0350b524400740102030842100c1c641c00340052056915060101c1d51a10080c3e61404113003868032001500301c4081d0813240d0384028420030841112440002280d4002d40c41d9840300b0b107050300c60b02d0120f03520394590742102c848c403000040c1c141c002d28164000d11300524045804114143d582d101c01c1c2d030790348180903048000c01c1504282101041319940309815410f003440c10394800302c07100c800103982c1002c01d51080354054042c000007000d904101a03a41e5104210300001c0314154140960aa52040009030040420031112800b03100741e4441c40050300d0030402a80105500850030810a04104188410380010300c1049075503862403070706001c1c40303081f11458001e800400d80c1c05000c1c0910 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 487397715 1250 487396465 487396471
    0x609030915070302102a08060405010f050d02060702010e100806030601061106041b0506040306061a090114130f171005071205130b1f0603060308161a10080c10090e 72
    0x50f002c5614107403841032400500d0760741d00303602547e109005450038030100000c4580c10b803ca03180c000c031036100500c07007502e84100481405404a51040d11188135200485030004440701494006e0107a025022400c0d0304055240c1c000d000c1101035030120782c1c03141c00440baa001916846052a030203580803402041101100d424050700703100a050301c04d0b88450216000d03600c10344c802c4640d40e0b40d130305003001103c3ca0210164924028065018a4003502900090007154850014130301ca8600260054920401000d02401403680400440f0f8072551116090440e80e90b941141805000302605040f07401c8131480340603c01d010588552142c3c68158559000818000f0080d00f68003090002c0310011581c5450802e1040078080c3d59102c0032030490018401c00111540058185400c00f041800004c0710041070350520060070381c0310541c01c103140c10802808100300d000c05114118036410f1003101b100e0030302941c0a541422040368904011102030003024480454542c00003120302da8140031814a241480d50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 487398965 1250 487397715 487397741
    0x10203070f0f0212190b060f0a06050a0e030d09030302060906070518010219060903020d0e03060a0b0d120302090415150f110f060106090e04030806130e060903091507030210 76
    0xd0080da5090340d00d0f141842c0c0b6008a58500c01e803020074070406c00c40108103a0320506c1030710000000460a8041419074915000310307400c0c40b00100d62801c1e180e205005140034114003d003101c514900800d4050703d441214007042d0700501400c80081c82561000030302c140203a14a584040c83c04404103146030002c5481c208150460041c0390076540d122010800070b640550084400203004015850003030300e407601c0b03444c00b102400f8000790f0058040d0740101c0d035a0380c0244402004501b80a8440000e0401c032205c1300000c0070064503220481c03e02d5810b5014004100701610200009400e000000412440300c1c4a40802074444203061207840d071142801c944100ca07182081981c007a0001d150500b80740c104203c0030a154060001008106e5000c407054000309409000340340d8070300349501c004004002c000c0c201806655460408801d0242690003910308640c100243c5826050507070440d501c0390300c910891441980d103440080e0b5401d05142c00c40d411268550018404070303000580b900060710b09440981c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 487400215 1250 487398965 487398979
    0x6060a0c06050c040e0601020622020f0d03021b30030f041e06080915040804050a03050c0a09021c0515040c05070302100e0c0609040f060b18010203070f0f02 69
    0x240c140c0c040d0074040d411410b0b40d075131140d003018488684110000c0c1450304544c031090900401c003d21060b0000c1c402d405c000f50307000b44202400070a8540880c42d510300e402c80000c2c100d04003855404918018044c6450a101111040581c20004803084000329a0307000b03400160980103085202d0554296180c412040d03d0824104c414450f60036081540b000d00d259100e141401008164941058003411031410001110706060100170384d9010204c106c0d240703c00120010409000c2c5600c1660000d0400502001011342c03207291582e12101404045405100c3d010404688a070700c0780281c4a031840304000084041d40700d0641603000e081c028143c0ea044114100b8040c102da280d81c002c0b001042c4582d1a12030f6603401e149402450043d283e450009810300c2c25120f0b5504010200300704840368000c950185c1c0320300006c0700040082c4981a000f070300302c0d8909000000e0a14886001e002c1d102c0c00307800c03024400000342d0010f98882c425040c0080c800c5006200324000548001c140c403221900141c040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 487401465 1250 487400215 487400237
    0x1020d180e01170c0d08040902070c0e07020106050418121821030f140313060b19150f050a03230103200d0203060a0207080705190210021506060a 64
    0x5040d491002c2e0801000e2128142c40d60394400c0042199440f000005d84e58048101c00980310750300180070b40d026a040030f40c0c0014000050210200e108005085c21940c1038226041c503441c064008c3c00a482080d0103a42807443c0442400c221000340a45550403012081603061692000c44d08004140f04040506003490408030b03400222540d0602c03800e0b6007001100c0034900c9410041e081003d030440110800c0300ca480042182c85100301641e41003003000d5940456600b40b4038122020780102030310707187c00c10b20743c642049194000d03000110803900015454640d11a521108890802c00d825160000ca00108544502e00b4469800401c14402c015828034001c8080304400010030000c0c0d00603185040d0b0340317820861500b21250b85602c06103045034118001189035010a40320400100640300c0380750f0105e100018450082c04482e1190b074410251203844209012440300c603a020f46080e40104120360b051504ca900002d0505000d070810f074410900d81c1c2e200010003055911480c046020069081c901d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 487402715 1250 487401465 487401479
    0x6030d03021c05071e09030b06030c030c060c240a061d0f060a03051f06080102040608040f210807030f060608150a090e03030a1109061c09080723060601020d18 70
    0x10840f2280410390f00c0c1746d10b482c86c608021043c0c0c68090310b49403094100760000d60440d03a0010701410036040c01c0e42c43e203445180c16191a41010b469143c01c02007000d042440703200400038215450b205450840040007001c3e101c05051803e129903d0001c4068500300001c00c140d480d0b0040e4060307001e41d008142e816560b480b6a215414140e282c62112b06100c0c00d000d5144000c0110301440010301000c0b8000c5062518100c40100241c0001d48090141d45004a2120510120b403c91a550084a51130400a030280f00070081004004a40090009103480e4400a0b04d00303031406540e049402caa9500e000c2603d5003a04400d03000381d050703002940114000d000042c0d0070310fa0f009248058403a1806940c030780c03400e41001c1d81620220b1110030b0182c0310401c4030285544d00c5c1d40564070305810001e422a500d030030512606d4001c2030203c4001c3c0c2400000310b1307020100844103a1140c130161140e0342c4d80f01510380981704103558900aa84032405070300100a144001881410745c4203a10b5919440131300c803240d4880e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 487403965 1250 487402715 487402757
    0x3060303040504110a031a061804020f0a02030a0f0c0206030a0e0109120c020102060c0c060106120e010614040b03060c0315010e090106080115050309071203020a050105010b0306030d03021c0507 85
    0x843e000ca103210104081c09000c2e00f40c400c03490b400d019000301c1400c2c1c1c06150000b6029210f20303000b09c034a912401000c0304036500e56506881c442c402c008003095032031000000107952038000b0b8503280c001601101200d000da030703ca1000840880c1c0c1c0608000c0c15034a544507000b000d003501d2013040c4d2072590389014420219500301c0048402080e181c803954480c071018000241001001003480b54050740c2001000c0c071030940000c03000d044403d03c1c80c060304c49803141c541c0303c1d000d05001c50188802e503082000215100c4014100c10720703403110844003042111318500605444031800c60f2150300303c2c14240700241c5e120342540100102ca0030140341c1895640c1e40240001d201d800207070040c0f00083c007030704010300400c1204000c4002d4a140d07401c020b0305601d09008800e40d50107003401a450414800031200303040500030010001882ea00000a000710f6849440b02c0c00184c10072210b45110b4880c00208540050037813003225441021001155020a4a403d448001c0e01000e044003080000c0c1e009964004483c680d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 487405215 1250 487403965 487403981
    0x1120501090507090e090c0111030f03090c0f010e01020d0302090a050607081b15070f0924030b1002100b0a1701050a06053003090307031a07030c1403060303040504 72
    0x48030005690800340402809800c4c0c1d500200640303010f1170188000703840b0010304403600210910b00003030820480300759542107000d21001100040f0000c01403001d9000e000c146000200415124442c1c0c00804100440315229804070131809a00010f000e200f10701e10a400415844401034030041002d40e466011030301076840090203503180c00d00401c0c464001440c0710f03070010010a840005003075400720820302c004030030b0010b001002444140f84034000c083d802403aa03d00103103208078048010608640044030013540c00954040000d140070301101480c035104441c1c03641c54207141d000304100f560b490000030062880a09450f0b014001c04000a02c03184048101e00d044c580340f80012170282411280e00054a80981069106e00e890320383e95524000300c0c000062452110200081d0100700b420b200e00d04500c115540c04d038143c052030300c001c414072100401c40030111035103003c042c10b280e450403821021540c6000602c03000813501d418070074180e1261000b0707581101004090300e03c3d041d500d000241c2101c03805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 487406465 1250 487405215 487405229
    0x60e070f0b1314060a03320915280914031201050901030809060a0c140703150606020a080c2409010e0105150d0c0f0905090709020a02070b0901120501 66
    0x19848641840c1401ca0303100520142c0d500c1580c0b807004400084c264040e1203422010960b4a40c0c28208841b155442a8510822260043d5010340b40f035140030b0301124201c428044910403121480c80c28481134004610440814030003a4070040e8109224071a00c1c043c41010381c11948a442a801165403c00c540c040d4031045002950394079888944958074170313416409240b01ea03171078000400c042200d54080380c0c21402d046031700d10f40d01c4885c0201964841c40003040030b00b030008a00e03c481990b403c00110354003500d01401000c9194064200c03450709841c80f502030000103800024a5800080c0030401030035003080d0440a0b0f40302d95508030696110164032121688000f040d1074144401c80380700707104405260180e040240424500752290810840089107002e00400042c0c840030148103031507039480060400014010710983c0d0328840030010340003c1d6445101d42c010700800081c0010035100721440350426070042d00c00145014a031104076040781000c0c07418081d400aa9803010380c524840d16000e440c030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 487407715 1250 487406465 487406467
    0x50a110a050d080f07052506140f01090f1803231204061d06060909030d0509010203090106050109030c032d061d070f0306020a11160306050c090904060e070f0b 70
    0x50010600d407208090722000c280a000c100422042000f100047ca000105102280c0c80c09054540329000300360041c0c81e00c0710704d20440c0074440d100035100c0c0503504072045100b06102c02d012400710401201c81035502e5281d0491f04a0702000028044c003464000019025821070500f100c840046296030700103103202c0305c140505010001088183d20402d01d60907020425080e19400024015940b2000070f8000d51280c4496000902c0200080007121808100c15009100c24100884c3d0313a4041c0d0003c0c4c42d0b8038a154200714010415510951100301101e4104030b0040300d540c40d507103e104406000383e80000004030910404825031005000210001e4070400c0c0010364103401c4180400c02c081c940c280082c958105850801c0151040e5502b2001e480e0001001030ba11880d030401030780c285a090465800c0790088112011001000e07111040c00c40780120414813456840d0560111075204610781e140d40302c00c3d50400708021510542c400001d98501c042203e250a48428031006036135241c0d4011a00000c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 487408965 1250 487407715 487407721
    0x3011103070906020d1106060424030305041805060a03060b010507140610140105040501050f1303080309010e010b06030705030702070b030a0213050d020f091e0c07110f01050a110a050d08 82
    0x1d03040100150004041c6818988502c4041c1095247c68000d8400d0748182d4442d5100000c0704521020821300030154048400719a58074540a880d40c1c216125100c08044461a0014801d415024951003640000c11042c085030030759690200401100401604111003406050000b44055080b040d4818000f4001c00c02403900d50300300c43c3e901c08160803c4402e000044e512520607600202660305590742400c020b5160042908440014051080000c5c441c00000e9400800d01c034205c8000e5003c0d941807030091200c041e03919161820f840b680d010740781d0000010400100c503203200300007031a0081d18034815107201395918088101ca40e001a9448400c84c0ea0008403542c0708004221118000e00b016240050f115002e50000f801c1443c050707000900035050038001448113041e40722250300c10704407001a9080e50910380c0d801d007041d800c1005c048800d180d00f84100b1a161802e18010303005410160340307041c41c0408010084955041898846105218202c40341c80010740a020254005c0380565554810f07203 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 487410071 1106 487408965 487408967
    0x150a12050c040303090603090c030605040203010f0507020615090108060402240a021b03060f04021c0f080a08070c1208070c02030a05010911062703011103070906 71
    0x5180c2401c0050416a03100a032040c1e0303010360740e26940140c480609404555600c030303018000300c98929003000050300343c4d0032140c0e100384040c001242c100c0f1012840e100795401542d400300582c0041040000704040c00d89a005100d0003140d04204e5945090000b60b00eaa101803c040d00442c100c88554a0700c0010800c601e14407800d0f040c03d55507e0380400301c001d440d402d08100c3d031658400b02d00980c02a43ca000070311980902503991043c2403036146c56003048902c100380034201c051400c64102c403101082c0ba0181c80031a0f40e011b0084c03165640c0c40301034014641c01009001005211292a0201c003280d042e00440a0501d814280008640c880407015600030b05001c900030343c10f00c9800864000c202040d0003007142944070742d40c43c10001800d441009400d0180a10041d05c002040740764150420f500070350200d414101800000f10f8440c0020079254980c403c5401c600492113000d0100a09 = true := by decide +kernel

theorem cover : BRFrame.Cov 487230215 487410071 := by
  have h0 := BRFrame.cov_init 487230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 487230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 487230215 ≤ n) (h2 : n < 487410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
