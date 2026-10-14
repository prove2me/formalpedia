-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1334
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:26:06.767683+00:00
-- url     : https://prove2.me/submissions/2f820cdb-10d0-461b-9016-1ca2d45f9b86

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 239748201 ≤ n < 239928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 239749451 1250 239748201 239748221
    0x40507050f22080115090f090b0f0106020c0609011d0120240621010b090717070315091a03030c0703140a0201080f040f0611120c0a0c02011101020f030406 68
    0x1c6140b00550b074205043c01c0364404c42401c0e05200310b030402880b9041c4590460b4144000300c9000240e03241080d00c0d218000d010a03178400c1004980b075001004001e504005100c00c00808031801450070689200190284c240005069428904400c6c03840e0240c0c05103200d241110400120a031410507000710302c58807800160741c80e41c04000040d050101c01c0d01c50561083c860607024148401c000390b00b0048100340c3d214000c40d0b000541d00c6034549007094990440090140c20343d0788640303078103945c8040080520100200304408142c41d01e010249482c22101e041012203c8800b40020740341154a10544581041203c0e02d415100028032001c10200024004080f64001c140c44140e621803c410701c0d48414004d10064000382d0b010011481048030707404066000fa204514251840b052070b46c40e60180c812400e0408103004000c01c0501c000302e48030b240035900c800c44e0b00c02146000f071101409854031907055000f03410005c000d1418070b40381d2825030441c1c07403052902400c1c0d030303d900d0300d85404406490076504d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 239750701 1250 239749451 239749507
    0xc0b0703050418142233200c07030611030105031011180a0503031306020f01020901020d200106180b010e03070b0a09030803240d0507061d060c0d020106061409040507050f 75
    0x140000d03203441144182540650031742850494480032424207c1c0e103810010721400c150140d1007000001940900c1501701f00d0b50100c80450701e0b58540700400d03003070140101c0001c01081c104000c06051202050172038900d1046603007041c034101c1081d004030b080d9a0254000c20b802d48000103013038904100328203844c0c040311465421640c0c6040050062800c3c1d01441c007040380941d101492200101d8002c0d0311404104402400d898100245a522203080d80c0b9540d100300c5000c00300c141d112824010300d0195030244102030825071508013414010a035550304074400d07019454000300d03540481c980305100d450015a040684241c680c1466422040c0c0d200d9403a0b0812800031200c02000c02609060043c8945260000040d020580c9032503019511000084050106880b01040d221900e6030390802411706010524002c109004401c07201a00710b400940101c0d040c001d802c0300e00c0064400070012561684000ea9011405807203411080e5014089c4155031090b500c1d0105500d040032503959501c03018003000003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 239751951 1250 239750701 239750783
    0x16030b130b0f01020d051804022502010e06040e180a080a090e060904080901030c1e120506120a030e03071205060a05240103090c0b07030504181422 65
    0x2500581c5d8419000b140540810420b015141c0c0210b07400301e0001d100700014201610386942984000c074141200c43e004800c55107041d01d05001d55030b1085241c00c03540420781d55039203051b0400642444001d002005c681c4620310028015610744824800074a000340d00c284540d0b20303103100366005003005800340680c400000706000002c0c0c642c0751405486e401607800c05109440c000f075020044003c0d000c40d0340180140501c0000c030b564445048102d83c03002ca6440d5071124000c070000036074602030f5a070280490b031083c2109002c00110364004500294a964141401c912400c6840082800c1c000154044078621202c00001e00a01c00301203031552140c410b040e010020355031440107076a0102c440812510200321654892078003940240d111005082c062030700d8801362947c0d00703410b07200d9038021981180040d0000c82c00b0007840602d42c1202e200e9801623001480742071804820191044c030000d09803660211602c20007811262900b107880201c540000a003462584555000c840340c080d01040c08504001c51 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 239753201 1250 239751951 239751979
    0xb040801050705070b0a15180b010e1e270a1d070303081305010906110a2d0318050d0f12050603030304030309050708070906050a0b03060916030b130b 66
    0x3c0d0080301c8025902945030304c02c0b502c1d500c545600500300701540380b10b04180c0501c0402e0699100040c4102d401d080c040100d000c2402c540014000c0d44042070f4540520340500755031901c21959042c812101ea820b46241c0da030900c02e0040201c88001e088400228440201d050002d049010b8011085202c110001c1c03040c8000c40c1d02c03005a444460b444083d000508070804114001e107189401407816008100215409100d500c59108a89440309503001017040028041c9680f90000345213942d03100348103c01c00d4210a80d04550809800881c07481080541d034030601c92080014141ca0540d00340c0200031120725110091000d003100014451400203d40300013841e41e0b8010f4180034240c4201d0003e0040e500350b4a840e9025005015800c60444d03030750107900004a4000c0b41004240f0050000c00000700d211841c02040c080090b02d01d41008039000710030000c00000d13440b090100342d0440074080843c0b0f80c911104004800410001601e44c3e8407a035803220358016109a070300b0060300d03030008980314010702d850 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 239754451 1250 239753201 239753207
    0x30c25020a1d01090e010207051c0e09010609050906060d05100302040501120c090b060c06070503060a14030606010c0501110f120c0c0a0f021f0c12020619050c090a0b0408010507 78
    0x40d611080003020b40500050000070090381101e119510564001f5092000300d5803001d0801c505100da4201c1c1a0018840000156000b89480340001040d075a1094a505168008007040e5040c0038050040e030b141c4000c0750080d03c2d54012201d00e1000c2030340070480380c10654907280c880026440107910882c140000412015504030f440301510f50701001a4a280d480c108424001d4a14040f00704e612107000d00c0150b660280c14026180b269580360b9034103640c7c0ca4040c081000c0741e4815000300310400184c200514094030000f4126401c102c00f4204451004110700e8600e02611048110042d03100c404920650307000007a4000d03040e1010301c1ca0400101d540c0302c095107609030080c1c0c0c400340c06641c064256800030030381d5100e0400c811030003c1c010306040f101110080c1c849407081100c030000607080c100aa018080b5517843d41e154100c07548054050750820a0740b07a29205220344000d40c0e003a0b643d50226800a03490360446814185c0504081c6440c0c0e9589800741c080d810a1003805501e50a040010300c49600c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 239755701 1250 239754451 239754479
    0x20f0309010e04090209010b0d0e0c0d0212010e0d020106050f03030a0804030c1506030f0b0609040b0604151503060303020f060c0d021c050c1e07020d08030c25020a 72
    0x50540158180a180001151000d0365292915001a51602c111025881c1d684040380680007584030b0035502c0e55080300c0e1404407001420700103019044403094260130b0795a80e2504550701d404655046440c0d00711481c0b1401000180c81d0070300980300340760707400f480643c041d00120201c400456200c1d2910070f012050507108d104508500000908030000600000d0082c0f54052341113005006d00d0311550000c003510300445d81c60350426181c1e006500101020844084600d60b8400c0d01954540c105061071390b1109a180f4004d08203500c1942c4440021280c2800807451000614484003905e0400315400c0010b8000c10240c042a401801482d201143d250000107106004200003562a45404107141200c0000c0d00440c0301c038212503d8503440d80103201040e0061b217001c1e2220481440da101e100b9684007510f107401c803211440717081c024492074000d81e56418803044e1070764011900903078990f19507070411514402d4124250b40202064400d80e07810003660682c603005c0b442130701c051100548612032098812 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 239756951 1250 239755701 239755723
    0x8070308030a090c03060c0c023111121006090e1909170a1205070f05070f11060f0703020d0306050d060f15081005180d0e1f02010b1002 60
    0x1104001080080410760f000c44002da00855104851580f00d645c2c0405462940c404100000d90300707030a410942c45c1c01c5030f141c0082001008100400d90801d500b10700c1001e118110851401d640c2e50552124001c5403007200c103601c0c46800388000c00d00d4252400800c50703410380110f50004030070b00300c04150b84000c00841401011100c1404003900a1280080040c0121070001c80d100d02d040c0c02e000c2203009480006d0460a407140c1c40e2180204080102181114401131903c030401c20360000080109810404840a081d04174407002d040206506040c0240c18506070007c1d040440002c030398402c018580e01604100e84030b582030702c3c0e400e24024400c8044d40d0441c081d06038130280c2d0348000c00020b0706a07484106911002d620100f886000c1110740301c203008140d17000c202150449a504020324825210700d0781c3c8903000a01c2100c8050000f07101c6542e03503070b202e0807c0c001e000310740fa9507002c0d60f0303120038042040040a0030b0f4030f01d00380503243e0001d002e0200000068042d4520f0510300003802e0022034204400c0d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 239758201 1250 239756951 239756963
    0xe1f030f0f0204091e022e030b0307030507030b1909020a06050a090b0a0306080705090411100504080a0305040e090a03210e0304080c01090915180b10020105060109080703 75
    0x1220254072100950440500c089a10036510140380f000075a11408890380c2095001d04c02e41000c2090060090b02404004e102800d04c1c5c640c4a07249002c10999090300f186c0940346400910581e0550211340360001c1c6410181c900d104d0301a0001c10414003c2155210300c0140c00000c00d44c001c88a0741c1416a02001c40003940464000f5060151611440241c0a90745085c032788041c00710b0b40e1703000340c06807a400f2007003401c0041d48603407051108007800c201c4200105016609141d8074503064030342c01648082003e007248641e0000d50403420380c5203e00141c0b0050300d0300100f501e180031228030b00030b040390780310744502e486036190800046d5035000c02161342c80f0002d0b05620303241e440c2072001c0c4919100a0842c1e84541400b43d8500b022050240200050809444213800801c000e542220001d402000682d0180800030b0900500c0c1d07544207140401d540072691580001c641c10130b2400c0e03980c0301511036400170a4000c14103403a01513419505420450040e042a00d440d03080c1a220702d0a540c03a500c20780005040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 239759451 1250 239758201 239758223
    0x309020616300f0c0c0f09140c0a030e0307080d0603060c05070f23030c010f060e090a0803040201030f0f060906090209010518060705030a080a151d060f0a0e1f03 71
    0x6580d00814810580c80700314a8804c00003038040d42d603460720f400650481c0c603110b5814a41840300140074412468010040030700d002c01482d0548176503203075203d5141c26000b01038503144500c2d030b501810400c0d030703500c1984850001d03154200c00311103200400361031000399181400c05650a074241e00079001c880015403c004142000109070f251100421020501085401c13484408841010f00c1403028014880141c80081100d001c01d110380380079264282c000c131034189102c00c2400b09080d400a18501c11a0344011610f07142d41e12400140c0081464800d08028181800e00086200c2c981e54000c8003030f6494113008000c6641c5940d40340d0704034040c1c202ca01d804a00c1c20462614a021070354011140c1b108010040c9292500959500d415900400b03808004150003034140702d00100716005041900c4200c410030b001c9036141c42040040c903003403240300da013014079100042000c0e602c44500d000160785019110851003940e820004442d00011030350380e1104824242c1020341c03d809200010100d0750064500c100d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 239760701 1250 239759451 239759543
    0x60c050d031a220c0201090c090b13090510021911060c0f03090f0a050a060606080f0103080a02120a050a08100b120903090409060903080a0e1209010309020616 70
    0x14103990403d81d4841e21841d201100e5000c00311406400f403122002e600200e0030b88914602941c2d02c158681006c0c6000d0305022100c082e40d1100d525801c40c11410050110340c410b81c0c0c0c10854103000b4070f14504070149000062400e9160945044c1d05400321250341caa84c00c182c0c0b2000460780301c0c0c0c0c06840310b48400030200441001c030508a400303590003001420990365100c000e40140340c42c0c14202d400845854001d40520028410315104010042c07440d400c18003070602d46410501100c3c4414040140300402c00300754079540fa442006003041000000460554a14220001600b42c0e00044616800101070074002400d801040b9001c004903603801850314100061009180d003510001001c884541c442808032070807a903980d00801240c40e01039000054100600e060003000c05100070b24a030080c505007100204c1140303000803a5001c61001c05610f9407100d0b508030048010744640701c2c0c0a58407500100b01c4000c110000d964081d98248101c50400e00c1c0b000c2a44a04131003050001e1f185003170703180504545 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 239761951 1250 239760701 239760709
    0x2d0f070807050f07020f04060905041704080c0103020c0c090703050a0605040b06071e0f0b01170a030206040201030e030d02030906012409260616030c0c020906120a050304060c050d031a 81
    0x8102880101090f41041311440403c04961081e4460a09c0d03036160003d110601030040802e1044651307501c5101e140c0303420918003070350f81c20021440c41d04050780041d04201407038090000149545004240800750b08060100501034402540c154102d10b20b0194000b8113480e29100b030007503024000d00118180f42091f1038000400740340107545040b48480b1080303d40052103601c1440d4469101c0d490031003142d41082c0301c924203017014084d984c3c0941d01030360016000c82d0700003a895a029509180100e200506240322798110300481d441d4108040c00441804801e13140032071081c4c1a90046003d07904040c501150b02c0710310502d500615004100d0948003480700701c0c00103095803141080030b4501c0b2284c0c080700741c08030700e400d60440710103072059012075000403060b41c54015490b155400b45008030841d80300d80c0000e41c1d4004060401d41c440e01e102822402030500500000240540007026a03131169981d03140a4550b11400c0300c00c60b1640203120b0041c0c03209000c1d103d01e0a00c1806103a118126072505801c0c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 239763201 1250 239761951 239761957
    0x90c0312030c0903060a0c02120a1b051c03050105030c030d050403060507090b07031e0503090309010804060e010606020d0806030307030e1c05100f050f07172d0f070807050f 76
    0x602d80e0110b007000300304403548003040400d006441c0f0403000503036040d241200070704001422844c0040c0000c02c204421900b41c1c0300a40f2503424211401d103181d4140d11b8030b407280c54082c00c80c0d104000d10f00c0340d040c241001034060b88101e048403801d80031313243d07014070020426459080c138901d0340b40411001d03c0301f88041111036100503400801410201c02a07520740791100010741128030220009460401c0030280716031042960003803812a03003802821402d1415841da101d016601842d4100403528000400f4400680c110f00240070080c002040501d488280080d11003601c1950400881d042d50081516030400100300d508882d010303a1411610740100040001081020101c03050340c80c403104d041f4020035002d0200746106404c62000194100106007200c05031203000784029031001e069070404c6000d40d000744200c0041c0892440d40c40203960344294804c003141c0002ca6102401c0c4201c94124450040044132070701641c000b101e4005555280c002c100c902c00710485156000803424841221a10b40020103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 239764451 1250 239763201 239763211
    0x9010f1809021c0303150b19030e0c04020d060506030903030403260708042f030c030703050d0c0804030f05010501212105040305013303080702010e0406150215090c031203 75
    0xc0421400d545040b111b01446007074001b540c042e540001c02407005501c1551180b11401c250805009040c08002003a845442902180c0d018035000581d10809600540c4150050b0400414143d124200804080c0e03894008a60440121700c008514003412014400c00801c40002c000032002c9641e108001210400030240c1304440004500c40d0381203208124408414a4100c1000d41060569000082520303007500d40c500355000303812a20040c804100080352403c41e0b0784142c14032500da00d88501d0300d80300b0382c030030b50780b001d03122140f00c08102c0100103040d0000c5040b41c0b40104450b4155420780840f00031210500001070030955694280e48070240c1c1c2d60003486414103d0308040381080c1d502d03141c9500f9104038080141211a11254009183c6080808102c010002c0310380c3d812080d0955803020214441c01102905000800030100c00e203503116001080901019240c40d1901d0f101000007035030700c5960b0713000d000c513a2102c400020080000020340b020346040040080541050050f5416215400546 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 239765701 1250 239764451 239764457
    0x1051b0f070c08031206030c100c061503020d0b010306050a060b18150d050619060f050d0f0c17010503010c09050d06060911030f0a0b0d110a0509010f1809021c03 71
    0xc0002010f5074140007800c580d07140200100c0342460108201401c1102c040c500038803800d20014001071181c4d11056a01401d82d11440014644240d02045005d103403841d0300096002e086c080d203440c208000982000d0403684148001e014a03202c4a08103c19600540100b5030411428000301458081c4610398480d03101b0054410802d49110412003116640301ca400850020785078814040141030a08070030564840060500c2c10203424082d0050501c103421800c42d08008000c0307803410300c10a1580c44203408100c84c2000700100c0004001c0a04110020400701203242e00203800024942418040c447d03074070907070390b03205600703c4d040a040115101b0242019644595955000308003c4030382d200d10006514565000c0d500d900d46042d4244104a0080103043c0240c20502010820749604040c280c80300c0e804600c0d03040301704c07504000c03e481001b2680850350100310f99000250101074000c951040c2d074119041250703907540890080c0151030301c0090082d003000103000360b186240d40c2d54010182c501d12a02e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 239766951 1250 239765701 239765723
    0x9071202100c0213020903070b25030e0301050420040e0616030e06010608090f1b060f0c070f0504060b0403051207080f0706020307030b01020c03060a0c0e040e0a0501051b0f07 77
    0x10f004507900710003160340c0ba00140e030f0000748040949400c1100b5402400e0320403210b0302c0c1012808080501080074441c0c00d07014440080803504050040b5480d104050000d030003000513113010b051407060005c0e040078407403005400c13140c00800c5080c18003904031164140001050b4640b02e0521101c0140d001d0304074282015038521b014100041d046c810f95008000320796981000d410700c5152a030411014049c0f61000d40d00000c0104c1c00307002409455000440200d900c1e5071200c512010300c115038403407540ca03140c2c20b0040c000041000201c03502c801c1c0540d2020b80341044450703104d031080d414a102e54003020788142d1000c880c000b0a00e11600c0140b010920035001c135402c14024000d040080c1d00904021902c0790340210403c9004c81c0d05100e440100802440100021262000400d85807000503000394112600c54210202460007140c1c03007510101c000d0410080404800203a0340c0740c0700344880031106542000042010921840742042800a4411440340b910103d401c40c1440c40c1d11040d02150142194 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 239768201 1250 239766951 239766953
    0x2070b0c010207050a11010f050403350d0e0c0301090803060904020f06040b0d1b0818070f03050a0210030204081c03110424050a020a0f020a1e080609071202100c 71
    0xd1040141c17280c442c09490400554041c000b401c10041c25500713400b00041030000b00007141c6d44050f00000000740316409a0409000b00c07a0282204442520a051400000d2540440d820315071000102c851305000381d81e00b0f00d4580302003509840c8540400b030224001031010a00d5403400e00d86890b0041d100801c0d0a40f04010315011594a4229601908091001056525000100d03000d6a045620004d114400c40361451134050301131100641000e04038160350f6540b01e581e000070008800134201044900240940d2851708030750703c485081081340100089030700c06081c2e6000c0d0003614190341303004c0050120081881317000c01c00c4801a881140405403030300001080007402c08010009010764a00c4032401c2c650441803c927010950101e404104901003001003591503021034800c0d00d00394020b103000130b90303262800002c1c118900358000000b80d80081480c150700800c00961078003200c01c018107840d42d640e2114100c60321941c4174494110314400c5d81c0444001072408503100c08413002d040c00c20252170419 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 239769451 1250 239768201 239768203
    0x61201090312051b070624152006060d0302030706110c0f0c010909022208030304030210060e0105010302030a0e070801060501021603020607060905031c02190e0102070b0c01020705 79
    0x5255001d40100d114440ca080034424039000300c507404084001000742e0f07581c0600f00d1003218411404040c102c0c035550313071080d01d00e410541185d800c1010000741c1c14100d59160b030000700d2852104da88d0f0340041a5110fa1030901084405003c800c060b012001600ca0395980300e00303000075460f0400040b07046000030004100055100d2003200b940601c409280703a10b03645250501d03032403d5024040304000764010036200d0900d030b900144800c282d074540c60b40542c40d501038a1001254106045050507004d10f103c1d0003040e0014000040e5110307e0081e0f08440007100300518000c100d564600601c00740b10606030050203594081d400a541200035500c00003060f0010403100d50a02003140c21008890b515481c6c100180d60b4100900715042c82010440b40460745550b00045c2c040c4642e49008203408d803540c1080b01407003001c0c41500d903105100d4941003008101c0c0d04501d8003d5100540b22030204c8401c11141480e64886d0304102c1ca41d001c1030300284031550411651031603a401881c0c0e02d040f1590200140b00000d44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 239770701 1250 239769451 239769461
    0x303010620010c080417120106030b0418081812032203050a050d1d0109120303020708070b04200603150a12060204090e03190f050d02180306071b0b061201 68
    0x94540d01c4c42c0c030328105440d01401c400110b9500f004080420301c600180042d1124002d81111800d050020b030300b0f091100840c010307207682c01c003810f22110944900414481090b00801c10f10a507050721035a00641c0c00c04014034038030500050800d541c420702801b4048641034180040d2010341a01e0110300644d641d80301032800640081c11512038020203d6000003540201d20000000300305011103001c4042000001e1800c80a449010380820b10a00d40e0014940280d040381c503000d4102c40c100c2d84d510501c2c182078415036000ea90442e08050503210030406601c2c03103040c0a40c4010010002441e640300d031001d90040c1c102c45500c007940828000b80010b224400098602c00040c0b00b9440581c44603e40224a401c0340d05001d22251541c00420041c13000c0c00c00b24441c24019007060910301030180704030404441500445c100100c01c94400100c002520403070403007001c4811012011554541d480240490b8140d40140c0302000c24a407107101c503000256002034507544040c02034080c0124569a0a040b400d60f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 239771951 1250 239770701 239770721
    0x5030601121e0807021c060c030515091902040b19020d080408030a0608010f0f0f050702120a05040e10090e07060e0d0503070209070507031b0b0c0c0a0f0b0601170603030301062001 79
    0x481003010000304015805440044505804c04005d00c0c52f0600580c4107020540803a0792103132190000140d01002c0b0598103080020074464115151a1a0aa01d54196010341005002510b08105442100d417000030400341c2d41c0c8181d030318103d032625160b4a1042c0350700050144405d5039140c0344045041d5100740301c0c281000c0c00560010030b205140900400407900d44207049690b050800c0102715049400140507440c02c4c3d2a000d8a82d55a603014004803050302458000049402d40c840a0020306114030400f030301170366642034040003844202c002c2c0b140d561250340b14a6005c03c506180041403440c000740381d0b41d0b10a01441c103481c601401030780000e20400080f500d01c40821000304041c000d050344018546540303500301c10f1001503126182c03100025000011301140550300000303000882c400c0188490342e071140c2e2014540c12032024a1a000307440c40c4040b1221400140319032040342c40c01c45400ca64500420002d0040d5240da401c141c0c0496441e411750b02014102c0a01744403c0141c0da10034440d4240312 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 239773201 1250 239771951 239771989
    0x10f18050c160c090b0f150334170601140a0e130e0c06030403020a020d020f031c0e0a0b0409200309030913020702012f030a030605030601121e080702 66
    0x19040a010314122007050201c5ea005072a5004541c0e95600d42c40d28069006207000889516544d8410b01b400b1500c4840781d4000a00c0e19903a0001e0004408102074910400917860f014180948203408030001403045a0090009016444040885a20000a041031611403805549c00441600400ca124002e2181a0b003407503030340e00c1d1109405005100c60614228121b030f030b503891820151402035035842c401744080d2180d40c1180c03e0f80110f56038071034a007400d09c0c0050265840c40302d02040903108500f004165601050601041c6000c600e020800d00e8140d4007007016035400e0500b8903c0c520002c004010800700400450b23441000c0c50300300140a1403141110000441c0d80b8080071041c09007802d10803e08103030880c010303c100300041c2c0e0400c925260000329220094608075402d09001030f980c203d20100079580c08001009844240e0640084040d600f0960403201d03140d88c3e030617440191800204018000115404100d844201802a020f0310303036015034021410085903400103200309000c0d258400384 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 239774451 1250 239773201 239773223
    0x102250315060501051e1c020d1a010c0b0408120c1e04032a03020603270c0306010b0d020405061804050a0b130f020d060f030209010f18050c16 63
    0x2040390580ca03000540207014020302c160341c60400081c0190003210f0300305c41008841c161201514902d007040d21011501003041803005204009514000d40c030009052100c0c9042084240c10510542c0c940d50300c03a007041e07542031103001098980040380c4501420466280c40108020b683d2503005051040c0940b241029107590381303080b802803407031000b80b222030b011506400340410400304070b460f100d505034060030502c6001140000001040810a980c2000303501500100c10300410b145011585000c0c041c0448010084090ba003003c1660340b00b907100c16070392503400280180040f20101004d4001c404c2044009802c040e1144c1c006141c5803c46130f5000e0b00301810b550301503d9481c003401020b8100404020802503840d0700d00100340f10084011500034445c0e1110f404241d26503081d41150384202c44031004229298840c56121641e031001d100903441115a000041003141070b00c0541000c4489604410054215521038080602001048800008010720006d0b10b8100c0c42e409943c0294483d10f49030318 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 239775701 1250 239774451 239774453
    0x31a0601020d0809030a0e0f09010303050306031009051221070305190506010903031812140609030c03040e10090207121808060606070f020d030e030105060405090c0f01022503 77
    0x442c100c440c9042204001c43c260a000414101000703d8030015158580b258441d003c1102040c02000308031701260304008008000001d1640c420040c44c0280300c12415503140042d0703840141c05a0300060ba0190003500021407404249060100401d070700343c903c01c0d02d58040e21003c9152550401c0032503544001c01c1d1110100700300c00c050105020300090702d0748410130490600d14002001406213000080602c150408a00380d4421120342040c01000006448110f1011034901400c91320b03916103100000380b28807400b180380b50320b0100643d032203d52000025800c244c9040080317440003402600d41c0201e90980000414100c0040c0002c1158500516601e000302c030101400909042d000300b244144004e810030b06118115000c92640d070000b10482d50380752981c0c01b50a04410f0a1b09002000350302c1082265107408058006d449005141d500320020001035036000240415104111842240d42d00301c1c031045144c602c0c0024452102c160f0620440303a51a580d41c000e14100d01600c20550405d0f080164100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 239776951 1250 239775701 239775703
    0x203040c0f0608090106091802040f06050406031109010e240f0607060b010e151e1b16060c08030601050304030e0909010915090b06011407080f03041401110f0d06031a060102 76
    0x100c02810101800c08c0b480010308402c0c0411442034500900c5191252500805001c6503000325010b09001401000f8166681c603100140748130b04d14013580118840c400005040c61b00050840c8100f442c00b0407034100c4031080c07503880e42900c0b20000240d40f010112640e0616501e800c1c000d00b222a00c621000200900325200140c000c1c0341c034940480c8a6a03280a070301d8080680d50040e9200343c16200030300b00d44240820908a054011403e10000046000700d01004400c030000c0c0040c0c91034401c82440d45001d403240811a0b144032a0b040c050907a103c00c00110303c442d4424401103511500a15281061021070f000068007907000765011000e42e910340c1208008d000304565400d6050203882010800030031aa5035017403181200803c2d007030521481e80a040080075006045400782079000403001c0d80c2d01c0c01140f0202d441e4006440c00d0b50b1907843c26000707c555401c14071450910b204583c40660801845030076200c00ca510070408481000d0300d840000000484000e000904103000024903003c51900c90002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 239778201 1250 239776951 239776961
    0xd0e010603030908010b090114040b03070819030807030501060f110c1305070306120203071a04120302030301140117041e15060e10060f0e060705030c010603120e01050d0203040c0f06080901 83
    0x502c80c181d200010418098030341709e010100d51095a01080d440f500000081c1080240ea210523030070b0180c08910328603260b981d0703610f00e41c8a02c0380c0c440005036210703400101c08071042401548045000c40c4900e006050065107080d14043c10103044480070b071140d40100310360030302d9040c0b10340078a5212420310200da1b405000e00c901400d04480c00458226083c1c0020340e903802c1030b110724007020441450b402c81c2a48200f085030041c244004550f810f4510360f1400035502e6000f4030039180010313402c25181500c0c0d0300c00c059a80c50418070181c03460171511241c456107808801e0403010f4045410001445000441c0d41c40400e08140c4003903000a121840e0000102c4040d40c002d10392501d00480c4242801003982001c1d490b19421020300d08000b602c00c600c0e02103030940c42030210182c1548004030340c0e101c1c0030805410070010707a48501c08181d0220603200c410340750a0303110010b06011400a2028004d089115409154080c1c018040c101030f0640c2c902401c03188041239009600007a030240c0405c100c1c0a000d00034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 239779451 1250 239778201 239778221
    0x20a0c021c081c14040506150a051810080a03020303160507050607050f0d060e190203010f170a0209070c0c0b04050604031e05121b01050c0f0d0e01060303090801 71
    0x26800070350501d41e03034084641c400c101c03c03c69640d0a0301610f214080c80795000b039070f9615540924280600305420040e07034460f402c45040c0100310040742a0b10031800c189141600301c4801074858944102c00c1d880f201070101d03000305090752044240100080d02401000040107040c0650055036681c140080b4a104120910068100380b1208010b00c9000480014566600000919006031241b4115822032680c0c445e406280c006941080000b280c0d109003811070394019041c045048003001c080c9103008040c3d000902c156004000e80701010406854a6040040b491020209035001c0080b9a400606481d10a071102c80000d483d0310358010400a044079034801411005c07602d2801e0924100004041d840b0b103000c0102501d040710510204481180c22014140d6446020358010207910f4000ca1802d4001409108950048008420041206218580c0500c0000c5d4041c3d18004100401d01203a601030748195111507580c00a4002070031081c8119400f641c841c4d51b90007003c6280010050030744404043c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 239780701 1250 239779451 239779489
    0x14030307090e06030a1109090312040c05040e0105151e03060702151806130f0f0809010212090a060e120708030306040b09190b1813031704050c22020a0c02 68
    0x1100204a000c02001250101200ca0351b18079510076045508500410004820109142d02800108642da050ce4800e41c3c03070965042280701c0d241c245003400d036001a42c00c4800f4040000001c1c00900f8a1031480f100300181c010301c10390101c101001710380f07480000c90b5010010b80203040c6002c1d0a1942d02c104942019210b0200c05485c00c3c8030f034103503440d24805089108200d611400c2001041944115203450b20b0b000140c054501441c1c0c10030000b980e001e00c031030034010b00481d003c0b90700ea03003800b0041d00e510340c802030001740b10242040c00c1074400340000881c09921021441c160720105504202702c0c0c010300442c0010707649074200001400140c40c90120301601c5a0f444000300490460140200400100459000304803000d042e000f0403421342145801031811400c4000300080094042e41f0101014400d558809080807007070043c2c200b0398000d035030040c0b503a00074048206540c6080d2a01440a50181c5010054034400310104001c9070f0107621942c1c0407460380d410142c02e520b0100241448908016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 239781951 1250 239780701 239780713
    0xa0f11070507150c06021804060f0b09040b040e030403061b0f02031e0c01020d05040c09050606220e040b0709090b03030f16061811040219030914030307090e0603 71
    0x2545580d100c1075640194061149103c0250841500c035164900c00b00b81c002100315502d070b699007006404030001c0c001d0301c0c0c01a4200b0900003044e080e180d010b4011208d2400311a4242868542048050300c4200c42d82d0758425141d0800e003071103c0050005100941c441c0c600000d0b0072440360501401c1c040c58483e50418016032014034189540c002c4111004c000c40c03410504500c081c174032072001540c00751008034815584003041c080c1c05450070b45e12503402540100f8030b1420b004d658141c4002920382c01c495031508914140004510259541d141440c01c0c8502824880c1c400d845a070f0700031103680d00701d5055031000c410505102c003068000c2c001b0009444441d8052208180c8a00031954030b01c070b4400584001107000030402034003002038000c0c00140394000c02c1400205a8144004200110130300c0545070300380c103402003020500e4036108840100c840c11040d00b0172540c01d604150010b124132041601e200c60042d02841d0036145c01c0c0021849010300c3d07100c205015003400c0074000315020040000b40660301c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 239783201 1250 239781951 239781953
    0x160210020304031713120906110a0302030405010f050f031303120b0306010b0732191502070203010e06090f070e060303040308130f080d0e0105030f01031104140a0f1107 74
    0xc483c100c1042c2c100400c914800d910b0307104a8015a2840741700140660000d190364000c4554840d047c00112481c0f0382e5640c8075480d0200c40c1c1034982c40300b10801800342e48100010055540075413030300000400d06017000c40c01c01c0c01d050800302c1194400c980d03c2d81201c0004a0074420980c0003401d0b4080c200304036008001c050720800200b69108410f01440c00c1080d8085140c000300908002c007185500300e20700390b41c0a80d400392072200f110b0350351640200c280f90003500242e0001c6282114680c80305a00b01342600c1040c0070b9038016500940c000d1405907019500c4403c14940403034200a8503024111420091085c107031a4088d803030800b1140e800066404810701c0034400166030004c1507400b641d402443c1c481e5110000d10b0700d50480320466100303c5402204440019a804002c00c15510002c0310380c03101d02c0210006001140d1a210031902141d0441c0020014000f003142095060301421380903000044a001070b0f070780c000000404030340c8040700980340c682910750b2100900800d080008501c00c030078240003107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 239784451 1250 239783201 239783207
    0x50f090601091a06070c0609150912080f070b061c0503041701140705041e150c06020f160c1a0f07210206040c0501110d2616021002030403 61
    0x10710a20b80015103903c88a404004104404103500f00c0003001c455580d041850080c05161103032081e035005c6001c5401c001510b21b5104215440d50b6011781c0c803602201d0500217010403444080c00192070b00507090114080003240c00c0014045240119034400d0145008010040740007a0f2402c1071440b0703070f4205103840006e02d000090304d0a03031f0541c10400740003c41d07405800e170041070040180314044658500342f044a5800000400c10b48041d00308020090344580001008440f4a00c0703042d4441240311584d0940500c6400042034051090401511300f41a00402e019183c0000506038940c0000028020400c111640707414001e02441d1511010f03200e51520f950300074040c40e03104100b404000140070040110031071110346030382c04d1a1a8040d00f8002000000d68030681120201d90501c0030b2761010500750f0043c00004201003e28000388500c4050100c1140c034010f00100650058201c4610b000041c65070101c040c0c4240503959540716081103103040207140004003880d00c0c0d01188100280808694 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 239785701 1250 239784451 239784463
    0xa03210e0114010b091302180616050c0409020114030406110a02030423060a050d02041d04020906010e060d020c07080607030903080a1103040b04080702190501090806012303030d02040308070204050f09 88
    0x680010010b031030342e400c002d05520701d0541184c02350740500009103019a44d0320444040201c54051012550142e200b603040c001100e04a1202a010907440b180824003001824011548141302d4840400c80300390780701c2d00c14100d412a180440160f00003140c2808010f800c1c0700b20301c0d00340700b101102a038403403c03003c042441c9110f0f40148c00308120b0f000445141041541d012240280303018150b20071104907014140241034016681244030f80442004141c0c6076110301c1d41c3c0300110000425031451302c0e0406520400035403160b0320524481c042c00400088101050002c0c500c100c21948012800b03c18600d00203080f010001c0840015500d03044940782400d148000307076a48142c4c4a214451240c590341000c018501646400951007035a801c800e4640340c5080e2440011139074280c0352040f50075158120151942000d009400b403030b000b0424114807040d9151382a070001e51015040d00d01d000103070046441640c1c045d410540308181c0c00205041182807070b00c00c2d50350001403485802e8081c10540c1019455038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 239786951 1250 239785701 239785729
    0x3060f0c070201021501030506010314010b010906030515090408072904020f0109120c0e0601111b041503030512060607050c0405190f0e0106170a03210e0114010b09 72
    0x8003022400381d0859000700a00303d014524040100d55960352803826075035031002400201d0329640f00080c1c0000b0402d0500801d540500161105c404181c10500210002c0c6002480d01079440300080301c40f449500e400382c1d500d003d01e0152489503542c6c4501e003484081651090358840265011000f000c0e5010000340426401c5981100c00004411030000101d541000e10f42040c6000001611036200b0000705015070070854006143c100520b50342c030001500c0d04d000000400c181030708000c0c00381c000a07040d074000221091000f0000540018295101604480650821000f00e4400284200d0654001000c5a032028089501c2031410f0229603c19460301a60041980180d0702d6102180c4412468036107404206400041008644001060100681103090002c038081d481c200f400720340c020b40c0b2007900b203228641c00001d240c01c640c40e039800c0f5082c0c140000d03910a0700440c400603940c0341d1024094207690140d0300e800400e1151101da00000d41802c10f82c02603000d1a0204424025a02c903850b40420303070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 239788201 1250 239786951 239786971
    0x6010203030610121506020a020310050c07080c070e070f0801080c0609040504060f020d0f060801110708030a060b12090d0e03120a0509030d171b04090e0109060608071403060f 77
    0x10500138141c5405400c2c4c15000580545145e800840e00a07400642885180c4c0218122a8610910811001200c0d026243c5181c0b14804001c0d6902082c1c1050041050400c1082105c0c4c00c10f40e1403900c46160320301640c1d00d50000d49401c40501e100c81d88030803524054000030024003142c004000020300300740b141c01500f0380143d4940c80080c0c02d0281950280c80e0310358004e03905564448014850078000d00d400c4150b00c0c17843c3d103043c1002c5509401449030a01c00700004489902e0030015803140c42c070329003000b444642459200d020100b880c1c01c480c2c02802071000c60041401c02c0b410609065414925480040c6003007028422000c6036a9800082040392154407510301d55a401c460b000840d114810b501e80340c2d4052294400b50070f1320310360010b41e072030151024100419186d2200b5900d41e41e01200700303000c042003410a0109200b00e0056038042d03c07e0704904800000c0d00c3d0010b503101d509865060f130100380c4075001620f0420000081d82c01e0070392000d0046020b42014680740c0910214101c016000e070b250 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 239789451 1250 239788201 239788217
    0x60603041e020306010b0a030c0201050603030304020d020a0305070902070c0603020703080f10030c030503070615121e06140601090503010c02100902033a030615030902061b0606040506010203030610 87
    0x455240e81c00840c66503006801d4030f205686402d022039190380a4108800001d141c0307540a007003a0710603c507250161034000c000e03510f9510740360200001218922010380c1e10040c0d6240000004d002013000300001c1a0081e409601c07000c0b21300f00540650b800354030581c14540108160800643c0c0001507a07032007100c1c0082003005880e0001191200c4030250001003004003035a00c0071080c410000003400c0710750310804003030284003801a508906200544500c40195020b220080d00045003202200c407203045d85110a41c40807544c0d1a220156203421900185c516261018402e142d40e01c4507000001d0702d81900248410840080e00039a545442d12020740c0d00c0b40e50300f100c40c04540d018004002201032818441c01030100301121304106500a2203e80c03444010100f0303102c441c0d07010f400b84030115240803400c4107040c591080c050b406014202c4040382d0092080201d84002c100c03000552400d22800c80c001d119524103501808101c0d8005821036040d54400d00420006039a5500c40b40840703503161400c054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 239790701 1250 239789451 239789483
    0x12030f040609060b04021204120f020304060804150603030c060b0603070c0807020609060c0601060e01020a02180615182e20010203070c11090903030c0906040801060e07090801020306060304 83
    0x4c01e1620b0145a1140c00001e00e05800f9000107045400b03680240885554018411016202e40b009040448051303042031000300400c0340a202455400303070050f080c50002c10052280c2d1402c55080c0e803c101e012602c41c01d2460203124003882000e40040c0144d42080c91420045000b034192845580d00400000300022090110f4413078006403400f81c10301601040e2214154400641c640c0da0034001c0780d00107414422000030542c0700003519035080d0b4000d4188188900550018203010320300a0220340c104402c003401c1c0e001c004882005040c190154060515010785000c00c2120544910f04a22110410b0318901d044c1e83d89200c0c1406142103550403c00d42c04060010065404520300e1414042544040304010401d5005009101814810100e001d80c0608141c10840030f540305030350041d2a80d1041c030026038101038240084c01310840080446003040c1c0e8502c0c000e402d6400c15005500c1041c040e0003400101604090001c02414200c0029400e41c03900c02c0104885000044c4003500c0500f920043c62 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 239791951 1250 239790701 239790713
    0x300a0c080c0301140409080a0908150103170a0e0d080d060f0f0605070c0b0c060411030a030903060507050405030303010f050312071101030b010912050d020d0509030c09070215070206010812030f040609 88
    0x1b4441e8016a1103844200107030029001c4151441010814056400704051514040e000305050382c2d8841290745800424491308402c9800030100e2038240114107041031b602e036599500c1080035501c10090255245280354904d0b0540e042940f040c060714240705000c0c4038001c5051007135005e41d9024980706485001d2410140580305c42640450305030b4500082c0c0b03d221a0000c1110b80c8650700420804890011250070f06542d204c4000d005000203440320b400380006031b4030760810b0ba040382d02880d0007810241c98400090641d4403c0e802208502c400304404c1116043c00d0004502000d12190318604140340d544a4800c01c400808910303040643d903030020510b0340e0058000001038800c410780c0c601a6001071401e035541d01c082040c0d01d000742c032406040c050f0451045088924030040039010340040040001888007462018010310b01354040c0740580b540f444019442c3e14480ca10990042019524100109081c280f0084608400a400f001040821884003136140d8100f40d02c0280060030b07040c0c0741026 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 239793201 1250 239791951 239791961
    0x2030c13020f040f06031125150f02030906060d030512070c060207030302180f0f040f02070813170d0e01200105090703060b06030702060c300a0c080c03011404 70
    0x454002d01c0c045008280d4020041c07940054a40c035413010041e0442c1c00104404038000e0382e0b010650304005205200c4055000c4044110241c40f40d4904800013820400c01000d50742484c041081d03a540c007004011701a2010000140c20a2040e0f0304192048038a40740104a40308480c2414108504040401e428911400e0415800b5821980c11900c0d03030310500d002000380d4840b0510409209020203c0b000c1458a1944c01c1410400103040f042c00c1010781c0244400b8100c00003039600e1240d400d000a90100308000010140c0c03588403a569a105410300030708070803a05410b080c2100a81c4542041382e5a260031007405c15040d5000d00385a01384d65810402a621403800c000e00b02125400d207418011074240008010301038034410641400645502000d00000340012500d0381d006038060004200d00b00406801002c0c14400e6407007141c164910f001c900240d03800301c1500d2140c1d00b5501820080d40480c1031180c88540c0c0607a15000d4942c1c00c059032155844c0c0010b0088004040e04c0c0700409501c2c0d51560300c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 239794451 1250 239793201 239793217
    0xa0c12110a030f0806040522080403150e060903160b04050c0301060314010f0207020306010306150306020304150e0102070c03080a0207090612051c0804112b02031902030c1302 77
    0x8541c040d520614000b8074094899884030085404d03407000c02d4503840c144c0112886004415011004414101028116400115820344607544108404400b2803910058039070030070f0800d40c0109515928280d001c0c5001e100401c80d50b2181c1080c8041402000b24100c0074006a0308480300e06a9601e542c24201c0c1070000e40203216501d9031030301c00004100a42c80071500c2c0c16004400080041c02030700202801a40300e0510300035459007061006000044031a8819060514801450070040e0b440f42ea800e002c9a20a803415600c80c901c104054081041c01d0041c2c00d001c0c000c100080d818515183d40d54440100d0500000b0081d0f600441c80d50005813081107280020442e610090100a590b840c014021121503e800d0703031140035040814407d07060710000d048240b8281e0307480068594443d26142e41c903441e1060740550050360340d40c1d18011021014a07030a0344184000e00d041c040340b006c0c0704152a080ca01c18841c0d00c402200400e040241c1d80124400380482c0003074a15155160000c11001e00070303c62084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 239795701 1250 239794451 239794453
    0x308040f11060a08041103070308041a2a010b060910080a02160c080607050c030406030506010309020a03051509060618040f02090106050415090f030809150a1101060b0a0c1211 77
    0xa803c102640e010070030034000c034050000003844141c050149600c4003c980805080701d07034100810003a400529509038140a500041181003004c8100721644101300025400b0b20304400135030101700c800c8203205a90b1356100803541c05207469804c00101d000700f00101c1180b028801020b00080780342c0e20f2038044680c80c825110034185030780390500d0041d203e0b9699001c1c0005030710031000080c0a440c011402c0350702910301c41000b107090070320b0440101c01510700108440c1c101a101c119640040c0c490301c2003180a1441103003c0e0000034114507090315250b000602ca01a240c0c4101c0070700865450b0000c03182420075000c142400c032540d0394105030a122858080013504140d0320380000500c01c2d80940500140d800c1c40c82100e02880c5c42510458414800303000d501e070f03c0c420052041000410f0000103244481e4080c10b104580a03090030b0710385181e00034501c01c10100d82e0301003811031444028451038000e40b058403441c80c109110141d000b048000402401041e01c0c11412918407040d02800000102180d014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 239796951 1250 239795701 239795707
    0xf1707030c12151103040212100914061302060406180b0304140607090609050d150606030b04060e0f060105070f051f0501050f1020070f0e070c0308040f1106 69
    0x5400c41885005400c2c040c0c400b111060300b8403d45040b41d001d16011440c4000e103440c1903071103c0e001c03c103100c200c9607010500c1e0300c214031140c04401810b000d030600c41070140c0300300d0a0f11103421100740c0c2420002000050000344080c00070005a907401c2c1071f0790917941285030103140e24400303a03010b44c48024550400d281440c0044200010054042a0240401d4540050720050303103171580150703405e811500a0101003084074206115500f4580300d007400d01801621420440e506416120044a100c1e03041040080d031110210386140c20035001d00384c001d040f001440c280b18605800c0d0411061800380400303040090004900c401e00403c840c4d840781803a04141982c0ca019000c0821005205d201d0105040450402000141600e000c03803007000310030030290074000400c102081c00c40d41140c403450410907444131200e15020341541004400040c0c03198000b4094203504000000d105d01e00001c103843c041004c0351815000080d1f01045041e08240d0210445003404468600707400000f6000c03800b25007015000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 239798201 1250 239796951 239796959
    0xb03010e0102030601030b09040f110f0907080403021c1403060105040312020c0a05040e060a0c020f0a0305120a020307050a03020d0902040c05070b0109020a021203060a120803010303020d02070f1707030c 89
    0x10b500960080303800744c0703007001402500d40502c40c18000495000d0180750408150a01103003003c401d5107201200180003580c0c403131803440040c20141058035640000340d141420401007640400c1040d900ca2114800c1c0004100b42120040c01901509a80c441c9208040049102a406003055074051076000340041240c000e90b80c00259501000d01c02580310b102c0641d00000c031030910b0700c1010912041070015018960300c61030b8080c05002e00698050440c401c401c0d2481d6100414000a03900030311a59641380d455103902c003802031802c070217481c0303840140c0b04100348410a5006011140090068180561900007408103a00108141c40021b90840d042c41c0c40c0d0101280d01900030602644500145031031640c0341d000c1c180c200e000b5088580d001d070b4400c0c940d60340c4504072500590383c404001050340c01025110014207c201489c01c0701200c00482c044014000c058050124012450a610051075a1494130810400c01c070110301c02c0c07120030340010056500e003017014441c0070051600800b00821203580e0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 239799451 1250 239798201 239798203
    0x1504030f0b0a0501050105040f0902160b01080f0c04180308090f010f0507022512021c030e03070824040302011404110a0605130b130911090f0303091809010b03010e 72
    0x411161156003d01e00000414107600441c150b60a5400704003441104031309080b903002c000c0d4403001c4a0450300a5008180d40061a28050b4034040c1c068400944245140301940910b807c140d112900d11690809465901c1c425800481403d1070b038142c9400c106070344031301c850a4101900321807072413503035401c0440421018180d5002140a80225400c45482807202014000000640c124a9138500c40603901002260080380d00501044d0006099240708030303c4000252817000c0140c82240860700180c00c890480c034040c40071400800c01640a0001540fa820f08040001100c00c01541981800300214091601c03d50001e040504e281510044900f03150130b2000245640c1001c40340704d0300c51900301243c0c0c07034426410360f468060050581e0f20b2039400c10f2410b00258200022040c442241034600086e03026003405049001030310040f006680da06160b0600100f11017141031603010794420030000507691030701e884100060b01540c402e02c00d252030b040343e82400340c0301d1050400c0d855800c10101d5124214 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 239800701 1250 239799451 239799473
    0x72d0807090501030905070603051005041a04110703020a0314091810060201020c0a081b060a050f0c09180a0b03031b0c0103200a05070f080315120c1504030f 69
    0x40340e2030340341000b035481c0011810360706004401400d58005001c01c100550003500020b8102103007111140065460f034000c00c080f210600015107000244102d02e00807810507114420303c030110407040300c1c60401c964a01940c4c45200580090401100d00401c9410101c1d01d01a281c4071040141400c82c698081d024a11901005840c0c14114180340da400007810b9005108580c6089004c001030031b02e01c2c1290312082c10350b8002e143c404460382d40040000242c1502031000c54840c2e6200200081c60b820840c00c20700b1841030040035002481302c20881d04c40c031030f507803200f03160003c20040d001c3c00d1496881095000c0540541100d0702d803d0721000c50145c00102090118000c9030a0480c11100304d0340c103002c01101582c80884031001154100c10040c0c607000c0c44400100401075031030410f00d1070651309d6990a518a11074500960b0b0344c601c08800d0200180380c000c03c00d1440320b0101c4485002045e010070480e21852003035055881100300c1d0000d5030740842e15a042d10001c54200b038407410294014108410310302 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 239801951 1250 239800701 239800711
    0x6030905010b0a06092d0b03011715040f02031002030a0902040f091718030d0908210f0a120509010b01110f07140609040f1b0903020603072d08 63
    0x150034203941054504103c038240049a41e155160740c1c82d140740500b1242090441c1000e800603e51034501c03800c4101e00c1d405644010500803118681d80d42c9050b55400b09020030801014241d040a03580700f5103813605412864006030070a640e0002d0b411a440003034946000c45a100b0503da002004022543c600d651006040600a80d02805400d802180c0d400440f220302c10300410b01c03c8050402c0010603546030141c011240d00c2078080f1110140440000d2401005281c04000500324034004d12880b5000d1029907030104030040c1b50f5100300c070304000c00d801500079212921540348003c200e0b030340f0a610036040045006540001007280d810b0244101e4081c2c0030b4400000d021480100000020180006e2500c038030b4000c94010b403120a0520114220084e240e004070f0340d01c52001d00c40031105940310f2140d000f5040300d414001070600c15020407850255001c1001c1010300c0002c000410241c0c131030300708407988010586030408102130180c1c450b00211074040b040d046140c207603125040d1402e800c10107142c090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 239803201 1250 239801951 239801953
    0x80d1119023a030e160e0717070906030213050604090906060609080d080a060e0907030c05010507080f07030201110c0d03060b16140c0d05010f05011203020d0e13050106030905 77
    0x885610081102610121282c0c03500c405000322586030452107948004009a110f5058585d001042041024482c280750840c3e808591400240aa1290010071041c40e00007180d2181006252110000c4c0440c10280300702000c2c9600026030040f840100300000010f0030008000d580c59036120159480200b20140084811078900040070401500600c401412146160300410a00200b0401180d404102400c1e00030003d0b1138060115a0005440351644a00c05550007010224030f1070600e4081d0800c41d0f0f0110303051200400205000c6402d10080b07440e41c42c11421a185e9420301e80c5000c030300400740b04030145003808001c200c103a400c900c00f08040e0710714440755809126990b00c3d44c6100250344516402c03424841c1100788003e001444200240ca100c0c40c0c400156403e40d44c03003a0100d900c0f140c6200d0100d400365912520000f100056100d0381d409003100e8075841210200c40e60b00130350359642240250302403005504214001c1d0342d441d0525601c03910001e505000340c2d6500e0030080c0251090401c2140c10b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 239804451 1250 239803201 239803243
    0x806031612120903080d2708030717060d021e03070303020708060a021206040903020a0501020f040608180a1401110406080702060a0e1f0b060a090f0b0304080d111902 73
    0x390b074410800d40c03081c1d0390003142c114541a07503030a100006144900785250001c10019010000b41c0c0084840d000c10781c0540d00c940d81c1c0c1c2c41c0c2241c000300024580c60301070750070032140e60030310840d0b4030f5030004407461650640c0c2031a0a0000888100e807121480004070750305100c2d1000c080109030f0f0204440c021200140201e85950b00c440c04d026013640250981c0c0e103e929070700300c009906072030907800440e09a0b001e4016105011280d45840d400e80e485942042400c040000d0100001c6910806440e0302000b81340c0313401000070066203440d1315a299484081d2032100e5065150035225002c0d03000540d1140740c8540c540e503460303880a0242c42c0e039000300c1d00b10015009501c00182801d001c0e0041c010200b50a2000c0e082404d18908074024180303100c1e001c0d41066681e60120481910703068001e020a201d50348444078203910340110103240030346d90742116061072428400d002c00128403d0540b005207169003c0815032420b007480c0703c9818000c8201c900d90b8403440c450300c90308254000c030713011451181c00800840c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 239805701 1250 239804451 239804483
    0xc030b0f090a03030908090315150f030c0d02120a0c060801060509010f1119050a11151e0702031506010f02070614031003020d08120a05010302010e010806031612 71
    0x551800c0c11603401c4810b82080200900107880f0751701c029070061040310101e081c035000c4004245412442030b03103070341600984814014002d41c8404568000d000407140401c0001c10a40401e80318007004070003078000c0c402003402c6021075807004607030140f24400c03d0890f00480c000d401e000005400511458011880300e00020403242d00c0743c2d04448040e281a110b0119013020f800c0e04440c0c1c40f841000b901c180740607110071403040e81070800701034802a018000501d40c0c9034250a20011030001100d00d60b00c1800d41c1c178528120903000006880f0020601c0042c07808403104101203901c1c40c4035403d0300030b5043c06001c0c4c503d040c240038184030034064802030b038499210703c8080c0d40680c0c0e14206400b5a401080b8100a405840c0c91024010b507480410a000941c0955681d40850b0500e0b03203401c003c684260011802504002180030b51642c00041d141041c4855403541e0006014108500340690400000b40001101a201002604034066191140b88032850b6034a0140041c100d0503002241d1031240400900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 239806951 1250 239805701 239805721
    0x1d0609132304030f120e0d0e030f0d0c0803150402070b0714030601020a110402130e090d08060a030209071e030c0e0604030515040f120302071104060f0b0702060c0a0c030b 75
    0xc2c440c90349501c0301251031003810403c2d03c0000b941345002e601151076070f840a00012042c4a021000c441e20348444404c1070b0740d00101030510b920b80202003503a134000c000740d000709035000c60684400c5802454a03a92a01e0702d0101c1c0b02c83c20501c1000a4001c1d0000841c3d100300445d8482c01131081060f543c8030064003088211000c0d0601c015104c1c240140d000c1003010000c115115600c81c11004010801031410301222004210400981e11415401d8513007810032000b4801031002c0c1d2207652451a199075107280180004401b15020b00010703000712840000500030134040c0249010740c0d84000d440c007010640240d001409040320b550400d0008517900d003c0e03440703424200f00703581c2966400400382403115182550380028401c003d10a6521859482404000c00c00c81c203904004d100e000d54001d40d540b038403810413050659003070000c280224581141080031448488502041e518940d401d665036a549000095050240300e0200d500b5015880700c030410440c0500109045138840d920911042d41c42071580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239808201 1250 239806951 239807021
    0x608061c05031b1501060203030f070201020f1c0f15050a080604020f0919090c0e071b23060109060918050d18090f050402030c0609011d060913 63
    0xc00341d52080c46001481c41c0c01600f00e04680400004440b00ca207048603052000700002c0e400000560000014050301a0703100743c505910000c9400250b1030100815204031580c4a5049401c030201628040820b0407000c54000f5080c09031521004e0205900c80903844d030f01046244540e500c00c80d45080f00042c0c2c4200441c46901c82c80c1c008000307882320442c45081c041c01d1700006116403280481603c5480c00c0b0702c03451003090040740c080c81203003d5081c10100200c41c44107000e050309003841070000020001d010400341c80034403a9480721030101034003401e003c600f488240c1c00101c500c450045500106900c40c04c0d030300c00021600400c0050003141c1c0c0860f2040001040d10314080c1c00b90300426240c221440c020b10155000c1403600d514050305c142e40e50f150354105c4940700d01c121a00e946502c140025481d040008040c0c210301206c40519201c1c417000080c0c0b20009818048011000841c00b1040070b9640c02c0a6076060701014044034019160f0300f0180c0300520800040c42c01c035030707420b082c80c1140300c14007120 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 239809451 1250 239808201 239808203
    0xa0e09010504110706090f080307031506050c1b01020c0a09150504060510030504030e12010b030d051c05090c060a18090b090103030e2809060b03131e0506010608061c 73
    0x2c907628284c02520707020050042020141c803882c100032841130026801d20b006510400b0542e400140400240300c094a140c4482c0d1311241c01c0080c1805000f2000308046081142d100303108801203a1411205c0042c1d04103480300f10762030b0703000c151400002180b17011500311050b0460400d00b81d0b0040742c3c0310800c00c8221012800345940009044a410400500070390041d5003140c028103120b841c08414900240d01c000502e00a4681d030b94449110140d98142004081902000b9050840c14100800c00c50400d1243c3c0709184203800341c80b1000b04036040b006001d4414903c8004d030007107030f80783c0d0941000341c641180003031000546683d03c0c0001803000c11520810001d00d030010503411a0340d285841c00c0340d0074441484038070b41c081d0070380380b851a0307145420000300c05002c0d519111620341c03850b00c0c1120080b5100c0ba844055209010001c10420140c5629041c0310707244d009161641070000300034401301e10080c0d542c00500c140b04000011038040d401c083e099114141c04c448070f83c402c00044001da20030b8950b00748 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 239810701 1250 239809451 239809481
    0x3090309191a0d0b010e01021903050f0408060105091501081303030f0e0c010e03060615130e01060504090c0309150b1206040f0614100302061803030a0e09010504 71
    0x400c8461900e0010340c50507040401e04007030865079444000d05801c0300030054100c1d00b42ca000140c0c0b4129050316025407805900c3c2400c04030543c41a58001070f40310348200f208802c401020003101401c050085054498031000c160b10350351500e03160070207255030b14020b000f000e124400000006241c0030a50b40080d124040694852a10351030707a50240b118590410070450505444554441101c50315200b00001c03004c00d40c005040940381e51001400c40d414101456020342c000390100416a02d501190054080b0050002c2d5a01d03100140d19200d01c407051b4110381c040c001c0e440000984254040f010340240d0312490710411407a14120700c1074084035401d00000340750001d1906001015003495101c1080c0369006000d03030001451488426013004801c4400700c0b8400c496608074814000300f881120440580032081003007504150a1034802e903105403000a07c5440d00040701d803103182c3c44481001e00030201a084945503000a0006815503d903c0902409a410100000f8442c0b44ca0700890011384d80d001c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 239811951 1250 239810701 239810707
    0x3120f0c1306050a09031410050604090b04110312160b0105041a21030d090b0a051003080a0302070204140405060a2c0a08030106121505090c0c0c0307080d0311030903 73
    0x2c40c042c0ca40d60481d00145050000010000021401c505144140107030403070701a050400744201414100d5030701522083c00380b03142003000d1000441d1303984202d8110ba0405200c45410b9040c4000a2800c0150b2624030010700001c071f04018044e83d03e80fa0500b0f100e10030580070b9072a80e2100284011224070801040011288a402c11483c4c03d000c1c5404180f000c00f040a1006844580540c5140d903105000c0307910843d503690300300f4007440b4918004c0e6400c541c00714810300c40c1c0c0c10703c040000c1c04030b0801e0002600e00d00f00096003100c0b80d4020f40c111104c0d02e83c05841400074075804403072180f0350341040740c05980c54050b080008056a5062080d0350110040c81080b2203c02003250040c4500203005135058840d00c034aa886101041035003000c0c600903e034030f550700013074218541c0300a02640e03106204510380c011811001d105035580e2100e450741c4004402c032820384503500702038024a095460380545415000d9041c01041102c0d011400224050f55602c0c24840541d10400d45c80f107500c81100c1a480301d40041c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 239813201 1250 239811951 239811959
    0x60604030f0c2d08030c070e0a0608100507030f0c2106030501060e070216060c02120102130303020309030f1507080c0c030f071401050f0105090702030c03120f0c13 72
    0x400070311800d1030701580207920495110440340d501100c440d00302c801100d008001c1c2124036040480d0200103411154095410003d000c04125510381c41030260303c00200e01600002e101c05c003940d2150006006020840300302d0b0382510300d00001800c1c1500c0030710019003403030085050441c8034003810101c046c1a503216800440c0400c040161882002100209151204800400300d4401d00602e009401c003c0988401400c10080c0603103070034000c0c00c0102c220815181c0c10824bca4000001405280e0181c81b012a0454140300440c024031a41c0181910000380100220501d5400000707001c03224419000c5400400300964101d6644c0c410f03503250303c211640d80c40000c280c2446644281d800100340d451117070606003003050403411608a4091004450008214401400f001c01c58003840307a1400c0b0000c02041c10440301016190005010351405915160f001c00d11003482002200c1441004005890710307544407502600200c1401d948030001250a40c010030b118441e40000c0319034444449c0b12814203d890 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 239814451 1250 239813201 239813213
    0x308270c01080601110601031a0601020a0c09150503030d05180a1e03020102041505030402130b01080a1e06091a0402030105030607030e1e0a150203060d032a141506060403 75
    0xe202c5070400c805d5204e134400c844010443c01d80a07600c98081080054130a80b001c240c5000001d0905046502803e00300300442d5500ca00041039803201c10001c99011004c030200300a001803076010a4042c4800100030404103203642c400c0d800340440342040464503114400b03040d0366070f9040030064a4686224115140e100e400881c007010700d4400d0001509090f82c4150405400806842010204070000b04020851505e1005c500e81d00703803601001c1000c0380981c0300090940340b00030480c411b82ca5443ca10480412100c19110081d4410354405001c107a07140c100150280407041028021501903841840007858180207590681e170b4042e00a000e25038403030000310098004008501e940e80240f1b040c481011030f5080d60200d510300c03207000501e0b403100d581ca40240002411103825803a1441032050061703d54035110340c03240498141c540500c000c4204949e400800c0380b8a074121042e12f0805014030108101d0010030145e688200081c6d8060f94404003c06104805c12103120b80c1c4042c0030030060001400c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 239815701 1250 239814451 239814467
    0x6221a09060310030215070b07080112110111010e0106030213020a020a031206030f140d020c1003020d02161a010608040803160e0910140a0b0a0305090a0501090308270c01 75
    0x70490380352441c0035945d80108207802e54902000401d07000025100061002108190b500009545080040c80d031500407281c0c224001710900502d01c00e0240e01100340d503846000c070301111800001c02000041c2120341640c3c020842844202d01a00d451080f59070340c400c4900c00da480214464000d845044c00c16039044880d85041041d00d40709641c4c0d20008030202e0f40d02100c07207046910a540c49400700c100070f442940b5004145c1450300840d8441314040c0500d4542e2014110011560300740036840d20844006140a0f024a500c040d030342404000e8203e09000c0010340d00c18010801d038200390b4031a600c50504a500b0340c0d0803140540706800400c04a1014030000c50f40c0e42c07104601e46072800c8902420b50015240e550140c8180ba6003241e685018444245100e01c01460600d0465a10600d1482c0c50032000c01b5004480d1460240741e03440340003403000f05041c0100300d01240d0042c0200000c4002d407402403c403210030744030b00c1e000c0f43d0030245099007615000c40c08043c800282c401403204010356401110206 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 239816951 1250 239815701 239815711
    0x1807080f0d0f020a05190314090a0e1009090c051008090607180e040303090b0702010902090415140a05040b01090504050a06090c05060705030301051c0b15030a0206221a090603 77
    0x48a5030140d00040745c400d10080c0b1100d010022800c00c075584600300203000354038510f00021010070030001b070b03201d80e691440c4c001c0465080392011003041e81c2d840c0a5900000e104da00c100380c0302e41020708580420040c4510107098600c1190985208007a52100720f890120072a10220680d10602c0030900c0140503181e04192082640a00b543c80c988400d600380791801c0036142240400e483c6e004510401c61100b4909501095904c0200500c6c0e689800066413800060005401c40c42181072065400403544c01003810481e103500650b0701800d0906060000f00000c980680b0341e1440ca07400804e641265001c1c00c1c0c05280c0000040c920340003503888a40013880480011038403171881c4200000e00707031109800f03014094041c90246403250300d0038040c414900c0054a404410400040069002405c0d0307188117904141d40c2030040c501500d00102092902e002c03004080d40c03020b00416070f402c41e510655000009400a0089402d22542c1d500c4000d0b0f0b00e8240ea500c028240300180801034035400c120020315400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 239818201 1250 239816951 239816953
    0x6040f060615020606030106090218060c0109230106050315040b07110115061704081614011107060b0102120d0b131107231c12051807080f0d0f02 64
    0x6540341c2c62151001d24150600c00960410307020448589000e10400d4000c0184a4040d071400c03c4030001c8480718000104414400c120226089134034440035070004801c16403220040c82e40e442c102c0010190008183c420700400d600b462800700fa10309010640340d400d264004404103840e1190340d25030405500c028071381e40c1040a090303601407c1c02024000c0f041d51090030001d560105040030401484170700c0810740242c00d184c0c62010310000441040440e01030341d000e02020305402d255850b044540b042c801c03403030031040c2d0b013821100c552461010008200441c42031f030b410001c00c0303002ca0040ea11880b48200b807900c1e0708c8013441240c49003501600094004c0c0c0c4010052000100300600507012640d0100103940031a0b07000c40c100702046112000c0d01011070041040d042d5070b00b5440b0140303a542d103003421044040843c428100190600a90051862642e482c0041c0407624190110000161444a00c581c00d032007003460005100c0400708a01c500301080700060910101207201c02c0c0e41c40f1032104090707011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 239819451 1250 239818201 239818211
    0x608060609100809070801060f03032714040e0f0a0b100519060e013002040e0a09030306050118031b03120905030610051c1b031a0a06060206040f06 65
    0x11603458101c407452100b002c0e121400b150074000380c11032815005401c00e0f501c070307031420b6414021400c060703c4040440c1e52601c1d03e640391503c241c0d401e0281040b170346000c1ca65070525100c04249850500e400910400c0146c43c00c11441d252000d605030394082e1000220f40641050400c20085181418140d60199a6103900b040b01c0790340d0004590b204080002c3c0b043d03003500d504028040c084e8400c080020074034091902c1000704046500c0590102d01154144403585000740c11801c800c04560150b500420b02040e00038890f18000100300c02414080c101240007a16103080454151b000f100300d00812107021000024003821030765180c02641045900c0b00b0040c8618500100103040e02c1182d01119805030b4408903081c1c64041498a0040702500d00280c00c05022410302107030b202c058240c482400b001c1c540e9408001e10b070a000d00c0c070490b111074801444091170000b006114440c54103c06501c1540592a407541e9400320281c100c070780500980006800240101d000f080302d107805411054094100011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 239820701 1250 239819451 239819467
    0x24060408030406020a0c1203021e0705090408070c05010503150f0301020909041a0721150f06030c12050405060601120e060a0b0f0111030a031505040501030503070b010f030c06080606 80
    0xc07841e04154010701c016445124038004020b900303c2c10700028000040c2802502803070f80e40182d00d03486000e01440d80340d881c0440f10030040314100142c40052070050002900c904050404051683c0304800603a07075880420000200d6501c2003003220700c02c2c000407540350002410038003080000d18519441130380c190340901c00c1ea80c15688100005006510513494075a07600042e92204040e180000c10310400e105500400d903d850400d20300c42411010320318000510840c4030000c60705500c0d0240c12003d12100100b1000c40d4a6400d0750104030000515201c0d040e69004440000064800c02c40b07006055030002800701d1030550090711008000c1070482804140744418607102c9180c12004c403101c1a04a4841c848c2124900b0811010b4071442020301c2c10401c0300e142141000c3e643d00c104000070301059925410303801c0705210b4400d0351014000040c414811943d403420401d9136900305110560b074084002000041d0444001c0303100c1c1c11283d01101e4540605d181017401e55100500511079030300480c04000c545 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 239821951 1250 239820701 239820703
    0x3020702060903060a0608120319020c2506141608070201140708030a05061c0b072601080d020706080f040809060c07240e3001020702130524060408 65
    0x19201d41000c41000410b1b13880d011545d0b00c1c00e100d4032520414100c00b00180720444068100c41105116032100150703480791809040d072301d40000b50b029a50200401d002a400c0395021240c420200d0341a0b64440c00513072060082d80c400e51240d1281540d6100c441e101c03000005e8285400f808010780141003038840d480c0c411000604c00d5000c1141214440000020803905501a104980d00300a054480b010351341c0300050503028007002503101a00020804000428079032042030096255018074500500741a0007500c142d074600d001707014681c62401402042003030b81c0c1c400100340c0210740b41a9a003220326150316000b140d502c00701600a545902c1c081105a80c10b4170740000410032840e0b02001020154540401c0c2c1c0301c03003e1000c0050450740e4010880400c41c55002d0445445504122524010283d96240180002400400450b15800210b4520307481300350660140c00601d00039154540e80c00c3d0aa0001341c112001101e100ca000c40000c1d2080c90880b2000c01000c05044000c1e00c4e00b8603240c1c54148503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 239823201 1250 239821951 239821963
    0x15010306090302150103020117090f0a0308010e06150703051303080a120f02041503270f050d08370501080c01030b04020901080c03131a01050315010e0703020702060903 74
    0x944040c0e8a400e2510308041c0d0400003000c003d40514482c40455041d603000800c002d0030f8191ba00320b002c0700a004144103003c14010f5420302c04180080341c00040c440e280181580c2e5003441104070300d07402c050001d07400b030800401c440140307180703a07001c80c4c0781c81c2c0c403550b0a8a5941010040001c42a039042011000074408002406680301d1901c1d50b01c3c2800d007070580e40044d00c2901000044040c014803040000304a540065103129034641804500c2d103034129400c94507052021403840741e801400a00409200e01d40d4203000a190107103007920110515000c3c01d0b1840b0000340e507074040744041984086040d82c14004102c01c0350852340341609444c0d9030b0384144820f9503c281c0111040e80c02081d48641c0350360705445401d00e0990240e506500700010340b070010b000100300405080304601c0020028147d51a50003002805a620110803e0141d4059802c1b82d0700c03070000d0042902910400400701d115000150001d412544e040320400c40a9030b80c00d000314040e4101c7c04080b60841c1082c807007107049940501c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 239824451 1250 239823201 239823203
    0x2030303060111120f1911030417010f050a0507110a0308010e090a050607030209010909060509010e0c0409050a0209010f020c090415141311060307052703060406090b060a050a0512150103 82
    0x4607600c8012031a1040c6088003031014500a116447e10b0310300c000030020095030101e80c1112800c04003142e8115070503000d4840c4455500126140c01700b0800c0c20034a50b07024a006400a079070b031046109002c2c880303c0c0e81e82207a070303c0600464030b040010802c004068400561088100703050382c002050a90316245031100c10340301d04010079008240d607003803568003180d95801007544000038050071380303410302140d03040304103000300c14040d41c05000240e001c20912040314011705010404211519000070050002e4000c0c00e009030010740c0bc951040103191000588038a041802445150241c8507540c0d903c42d50503418804903541074950010108050307844460b42e200e41c3c14150081d9519210703280c520b9154128003110b03072041c0000c0c03041c460200d40c0003043c0c509403e01c0780035650483c882480656010b6040c03240885d0706200d214204001c0145641100401c0e5114441d42e0f505601e805041025640c41e0380920b0f40c0000345200304000500d130003648080c0540c0b513001034030402640c201405401d4942604 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 239825701 1250 239824451 239824477
    0x40914010314070f03150204080f07051c080a030c140c062d0711070308030c071709030c0603040807050d020a12020102040b040b0d0605101107120203030306011112 72
    0x10000c0c00b0300b00003000025224140680700403418000034440804284c040035219010700c07080d0380400b10170740d030480d009011254220784121000484403941d07034209000d050b02840d280076014440c0c0c03084840302074441380d020117000d05042940340114001c09180010344100455411583c2c61101c00c100188100314402001d0a138500e040d81c5a06d540130700c1300d284415508090404502d086882ca40035a820204a16082c0c14426440c0b80380c03440c10311540c202801d0110008203000d000b8034004011729201344161798a00c0b0340c541950703240e10940941810b443d01900704070803200b040c1c40c1c650000c5500c24440d288103414003996407034035481c0c00304156030000960300c8200403100f0b10400c1c031210b8082800c544000d600d400d04010b123400e00c50155201d2000e04100101e1142c1c0c50740702c01d4000b10090000035102841c00440c940005142100d0b521000040d0700820300c0c0411351801241d200c04000e40c02500841c80c50715180d00448642c81c0c2400041d6560050504629170750441000038a10551210 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 239826951 1250 239825701 239825741
    0xe060606040512100227060a0207121b06030b03010b01020c09010510030f020c1510030f110102010f0c050301210803270709050601111c1115010b12010602030a1d01050409 75
    0x42540c00e8280d4101c06e0944144403c1c005000d0760760f0700085020070303034070401800c8440000b01d02d8500310210500902d02d1000c21140c001041c001d07807503405500200011402801424000801a07031200c0410801c0e90b000380308040144a00e00b1b00703218940d2204c0e114075000851440c0c0c22420b02c00c03600f1040c884440c5400c50f0621450420030056625040700207501c0c0e0310001ca286035142d03e400c422001d0010000d15081004041a81c001e50080400e112a090140640d0b2400c0344000d0040e4401d00039918001141d1588e0740305031850010420746d07642d003c03078803030b2440d01d8642003a000000c3c1c207045005107024024000b82d06030820710280300103181c40d9201140320708000e0000360500c0500280724076254042920201d01805074040209070340601c1c14501c40f590403080d02c01d03041500b404000d44100c5a1100002404080040188040d02c010100c84030141d0300e40000700c0e200d1040861000000d010242c4d100b40079045100c00d03002c19203050400a2030305031b480c0070500640e100c94681414405949d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 239828201 1250 239826951 239826997
    0x306073504030906050c10050a0905150412050408060c09040e030a080f060409020303030a0b012705090705341707021905151e030103050601090e0606060405121002 72
    0x103c0d86000181015052240c10030070314800f0a9511104100d40f040516141c0c00842e84c085003030740c021880b0700e230810282d9210324003404c0320700042941980c04a40380d9840e00116000a0303c84c200baa0300791215500031300440d03105c010404403141c02c6110388a500c50350f6201d1701c01107030303800300f0040544101c5070701c404202e40741040400d4007006008000c280682d061407031000c0141d030044201c03540705c000303120002002103a207001219a20207089201a010002c0081d40000c1c561086180b02104c800300c1300b103002540d031f15500300d034903006160031140d00780201c103000742e407141418400c0007102106606651984070700740c50300d22814584200c202012000001c82106505280003001148140c2c01c0e11314640c5450400801c007800302c000090035990318003040c0d1019400100340301c8070380e10b406aa403998030703540c41b801d1064031403000381b00e0300b41c100740b500350014100384000c01c1d00c0744500c0300140841d0030300d4034000c180b280f4544c0b0380c403084015001d150094800719003244054400b8003003480c200a07201201c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 239829451 1250 239828201 239828207
    0xe0c0907120506031902061c020a020a21020c09040326150a030804060c080c1005060901060e010f08091905010b0a060201051b070206040305010c0309020a0605030402030607350403 79
    0x703443c1d00d0080d001030001a814007107004440c4036140d41560400e80d140c014a0030783c2a04052480070456080c0001610b420f500e900240e0894000c0c02003c480241c1d1a0032440b11014401c003424540240e003061303200e401540760400620703071710901138200000d00d014022151804010305001000200c290351041c0f1a00e61812404603c1d01c40042d2000302d070752070441d01c52aa090041e8495801001422454041005541801e07504582d421101716021f850703407601c1500c09082c04540a074000d2100c20000200c1c24860b9408016000d810785828003d6140307881d044038080c000400e00710451141c03148034a039040c180100c80919902034000003581c01041d8081010f9100b207030307026104682c1003900b4400f03041c40c002c1c82c8074070381d109181c0016543c02ca184003040c0b0764000d5a00150595203800103c3d08001d4140d009841040d10848607800081c1e1038a40660355800103840207505940058002040507016422105002c1e0300700100c2c41c08004150581d50a00151840c0503042a0940c4180401c141d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 239830701 1250 239829451 239829461
    0x70c14160501210e0a0506040f0327140a0806190e070e0a0f0b06040303110606040212040201110708160815130f020d141509030a120e0c090712 63
    0xc1c0034038240001ca2540c040308203031080303462803c00665580e160fa1040403001040100380041d0f100045d28040c0c9010b0510446400711a08181c000c561400d840700300000d00d01c102c0c8110311404d070f942c140d0018100240741c0d8200c120403002980021040e4000b0a80102c100f00e0184035550a021410b40c0e64080707506802520400380840d10f072a4000f10f8140b020101d124100c0381e121001842c00520b00e01a684650301a10154031250707084280042d010085c0f40d03000c2010500c2c951108101c0b642610b8007420b00080b445a00d4a0400c00120340700400d00561240c3c25803403c00f1402303011188130989078441c107410001022240410104000030401120100f032185000d901c4100e11030132560b2424140e46e10095082940040c100c102d002100700c00c664032042030034040b581000c0070400e10b420a20000b95135644940d01413900103800c3c0f001800f9400700200b180d034485400d46e00c56025407040007104024240c05c0c20a21000e014900f0610710503210b842a01d481030300266103601903007119031404012a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 239831951 1250 239830701 239830709
    0x2809060e01061a0f040906170706140313060f020316230412060f0606030f0e0d0504050418021305160c020a06110c0307090606021509070e070c1416 65
    0x190600b9010403404040c18141c1c1c51081940081c0f03659003074804042e80151085410484040d8940103012400301040c4a860700d031951510201d0303001584800b000c0d00c00c60003122404054074400c000090070660702605011203070b0b00c1381501083c40c8109200e43c005a8100303d441c0c071200c011203000b034480746070300c50140b403200300100c0c0d503040d42c492440d141b4079024461340c0a9501d419072075175104010000035a00c10b480a5008031000c003c2c081d22844c0060140180415802d545030400b02990342c03003200498201840c01031030700c4e0149468944030511003d400c1d40180160800d44c01a00c42000d40c03190220203401016244000a030303403509425580f0390148540040d410000080c1070000141c07141d43d0303844161031060602d852016040440300e45032040d405103854040c0101d0f480011080c00980012050703803030a40a642c40765606a805050764941150149003a6000345010082134400c8032007540c003c25180b5000d0524603003078482d024220b141c1c0a040c0f07034907440303007080e004180300084c0418058 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 239833201 1250 239831951 239831953
    0x9111801080d1110060305060f16080601030e011811090906040305030403050d09051009110609030c090606130b130e07020a02090601110708010f0606050903060c032809060e 76
    0x80e506081a81e9501c04540a4020900c6454160031049000c1001104602c1001003024410242c5a00d403081c0c44d0102502e8510b0284080320104000390300540500c0c121000c41d03034030800c0f580e441c10011001303005420003040d155543e0300c01602c64100d680504201e200c1c000d10300200045864010301007003040003040d8443c5030b0048000d000000b5400011260810782510b802615042494002c0c0c000340030000c8024003a01c80c0742180300c01c072410340e041030000c90b0250100510181607a41070060301d2081d40c020350741c59008248041d0207464030410240e040f1401401c124205080454003402c1a8250b4100001045021038481412007110081c5400391a40715000a16410020030103503036002e02c035400a10a800e0080055170991190100200d048614401c0303500c60342d6940501402004520841d0701524144000402c000340035608480d40300d43d010340205400da43e101402c0071a81c001820312440c02000c03a6541c82c40760309416207050f0001c205080000e624071203181040844100e08540509 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 239834451 1250 239833201 239833249
    0x2031014011415030702100b040b180c0c0102040b0c010e0a0c030204020d0e030f0c0601051c0803130609032c06090409020415080105060114030c03071409040911 71
    0x1225200d00504441d4401c0040d5868100140003400030500804403000a0341e000c010040c0b6260b0004000c0f150400d22841048000c00701800c1c0300c16141c81d560001c7d00b100502841d480120200c6100d60340c8040d81c12040c0e810a96154280c0e4207a0b03000d035109a406000c08202a40c038181c082c402c0c180c0c0000040d000b485014600e40d40c4011124261002a20a41d80800c2c008804461908102c0c40031102609590b0344044031711801c200c580045510038020312603c03001040c1401c0020805010303543c0e04000c1c03610001e0564600b01e0035440248286040410b1480c2c2c10001130036400741860441c483c0c1c5420801c80510105003140740b181c0c1900b0341e003c40b240303c50004191912800c80300c07400c0b41650082a0115940041009040840c002c0c030500340c080b40002403001030641c00f00d8002e42d02640c91108803070506044c10918001640c1c440e880100400100f4005402031890309081c00c2015009400c12007507200260888042c0401695048100c00d400c10142c640380d0402403030b5110354000009 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 239835701 1250 239834451 239834471
    0x1d030306100306061e030b04060e45150408030103060b09072a0c080c04050f040b0a18240b0d0507090902120a03020d120e061f0b0c030403020310 64
    0x800703040000c0407000c882c0d41d40141d0058451091f084041d1500000e0014492169603240311035030810110b40003918200104070381400303080390428004005a0007464442410710001c6040f59140160600c005203100d820504071585581d2440c0500c0f41d40105120b90712985103040c16010781e802202a03c1c070035800d2408020304650040081d04440540600c2c07554285006920408451400701c40601220040d8400044c10680050410091401039605200c1a10b4541040c1c584040a0710020230103880c000006030206001e5010310032210b0301214103c4070b8080354441d4030881941d40f100031f407618115030b50351402940c64041c0700c0703411005440c800750314807803078440ba42c031140280106100540c43c0d119040655807080c040301d02d1503c4c40c8040c1ca030f04e40260310300a941d0704500303444240031030086160000c4801e401d11030100100000f01c040d0a050791441410a6070040002660081c070400800100740305910b200907082282400e03005541e0380e81180100352618500144664041d400c08401c42 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 239836951 1250 239835701 239835707
    0x902040501050a0b0a0c0318030609050d05070206251505250903031206090e150105040b09060f18151504080309060a020f030a0906110a2102011d03030610030606 71
    0x285c0095a1890039010b0000b45103011110b008a40d01055030b00c103c100d10200a01c0180e03406410305920901c111840c030801e0b912705039110300400c40007030350102c0240100d14010784000040000c60344a83c000c548139040588d2044588510b035041c03000515605d50400044140358400940c41040319158160360310366a0314010040b4001e804028200901610a2600d140107a0030180c05015aa00144080565928a03036652820f00c1e20b6480f1f041802000058603013028841d03d581d100b03019006c480706650381c03020b0081080510f0039454020304000500f80211210900c0d140c01070304036010506c02c0051140402c00b81c2d0210b08003410b02d5001c02c1000f0011b1000000c02c4400044065031416118449448240e0400c0c018500c50080e5010000b0525050b0f90f02040704415140350383c40703190103003940030700c51a41c030420309000520001c0114005640c44905000980406040740700100d4140450598045d5440112000400c2640040240b00b024682001405686078040c5410002d40d03140c04801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 239838201 1250 239836951 239836957
    0x5060906090301090f06020a200a0f1a04150e010513060b0a03080a03050a06120507031b050402120f0705070506070507061d0c041a18180a060902040501050a0b 70
    0x26200306800184100540c50a4001c0c05032941c00424107083d50080d0f00340030002e540401c1c00d0341c0018128640100d01c4e009000c40f42c4542c035080000030002c40d2010b58030703403001072210354042c0c500303d0718441a17000b0965205242c80c0b0440c817803680c514140d000c103d0f912059418181d110003207641440200503034016290100503400e5085000070072460504800f28503076442a0f04040c0c020b03d40010145604c9405400a03070003901c2d0503508200c8540e031010203181c3c070340003200b00605a810226080010807503c0405074513000f0300b00481d00303203180c0e590001404c0340e01c0001c2d2102ca0340d18110810807101ea85440d5a64401c0c4581000742c64011030350303940c0751110b1004020609109001c0354010621405501c00c410a10b48611203070000c10b040c000140d82e4030002072446100d01e003000301c0c4c0c00f60024004e0342079540d88000391000030701e607204803600680b1000050503921074088582c00700e130103c0005c01c0380281890040c40005a601d80c1401400700707a1780d050300138a000b440e9200e0200035002c410341c11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 239839451 1250 239838201 239838217
    0x40308030c070606081e070f030f06050a11040807090b060309060109051308120f090706020c09090c060403150b03030406050403030c03090e07210509031e0c060c120a060506 76
    0x140d6610303402440d20030004d0200ea08040c0e914801d1801001c01320003021b80324003034240d03900d00300d40265075140707146400b070f00b2075020051101701e100721040c001800ea50003480d00119600804124000350040b5202150890b43c8203000503804000101b04004d103510a445507544c0540320b66180d0300e0040702c0c0994554040c45000c0003a541e660004100c1500c9150b1a401d81d40c1c003494541c1e80b00307a880c418444401d4242c0c0c1540107840345c400403800e41100001c10b0412100250060800620550f0401c02d8500c0010100304140c010003196000b103941e0301c00100301940c415005400300801d600443d00132600c4004030207009500400080c000e40b81c01c841950126681071a180e442c2d05214502201d0301c000c55400302000840c00401c4c4643d4981042c03d2581d8102486550742e440300d10f140c0385005440c3e05031000686504100a0700a18403d2601d80c44003d07104e840300e81c4d1814420740039013494543c044400c0d4001c5034000c51018006691440c1841d0040752652080c003203241481c1c0005c02520401d64 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 239840701 1250 239839451 239839471
    0xc050303090a05120c0a09020a0807030c020c1203090301060b040e0c040302030604021302130609060f1803020907020a080a030204030c060201140612010902120a05060708040305091e040905010606080c04030803 92
    0x4e5008080008012a82048801401040a803aa00c0c41108041e400551011011821110010780c00910a00c20784016600c203600400c1090540001d100d5280c0e8692405622400201310000f4640c90034040c180050110380001540c443c64190186400c101c080c6c00705000060030001000940d40000c1c1c2241c01a80480d802449060b2940c800c1000380f18607500a18002004400013070140c1d00701c40c080c1c080700c0c1c00317071944c80001c41c283c04101c1e01072031800302000c00e00c40c00710020300c05070404100d81076110003140110307404452591501e400a40020b02101f001070b40019044c000c105002c1d11020040c5050300003409100745514840c0d00164000301020b02a02c2000c495020140382504031400068010b0800c44640f031440c010140c86035601c0707009807441d100d00310101d494284a001000e10030707034041d6540c60070301110508001001d0300c4011010040010304050b200540e94600c11028118440d1000185052a002e006070440c02c0090583c4624641840200042840c1308100c03a400401c01c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 239841951 1250 239840701 239840719
    0xd02031606050c04091b030f02160b07052818081905071809020909060f070804020a1a030a0501090606050a030f140c1e190c020d020306130c050303090a05 68
    0xf0030700035580c011035021103102402c000007400c09108a404605803060981d43c1481100035507510784061340700f50480c0760380f000340451021000ca42e900845a8110f80107103455880d0410180001070b0030443d40d8035981000c03030010030f580b40d0f05070000003264001e50150130000c0400d2414a07440c0d1114841030300496000384805401040281c14407002d806007013003115800e40f88482800d180000d001c0160201d0040385150b000c42c1203004005403442c49240803168402960340d40550440d0110009003049800041400340800c0d4902c07000b03801441c942403041042e4907450103407141401e441c81070b84255141c619207241404420307030050480b1034019141c1404542e1007240c02c0000010b0002d1401000c1d04003480d0280100c0603c07403001403007006491103180c4240300c4210300c0c1c0074044c40b40708900041d0315099042c10383c1103401080505d112074001458900940030304c0e00464104881190034001300301d018621001041004144a80031344001d40085003040701920102c0d400007500e0095901c00c010310 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 239843201 1250 239841951 239841961
    0xd0611131a0702220c03060504050a0605060901050a17130501051e060d032a020a0e060f121908030601180509070c0c12150606030b0a14030309041506020d0203160605 73
    0x280403108a80b4044c44030070030a030210190010700420340c90150b10322490030440800d40c0031000340501e1094802c0140003601e8050707200f0041d1110b50009206800f0b0012440d0a200c80700c0314403416511540740d8070108940c003411450118211807000300451601801e92000325804101005825405075080d0362289a0b002c042c2000d0701e02e10f0f80c07031070316504424031030701c403035266030346981440c0c820902c01d0315106034030782e00e80380c21492109045645c1c03034119014120741031131703450306200003441d900900043d50038910007140d602402d26030a1009131050000002800343c079591121070404520b1140105c004c1e1182007030005021100d02410300c10401c02d600b00c8400500c024071000d24014002002406070304225850403a1740c509819403046600c42ca412000035100b400780c0601d5401c004014840c61500c3e04050524403849000120241c040c0300a0264602c242c403684258009001200c1406d200b051410400074503104020052008542003404001c505118a0050440a40d440000400d00e50382d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 239844451 1250 239843201 239843239
    0x130c0308090d02030f0c01020f06150103050c0c03071101140c101104050306090a03081e0a2406030506040e0a030c060522140f0d0219020d0611131a0702 67
    0x3150296260003004005c400c120f03400198030185007000e1b0203030381040c8107190b9003d8031342d102104c41044410880c492011a58403d034400c2c0d51210703030350640500384202d421500b4170b550400719040303904421248801801c1d60b0031518540040309403e00e024545414403c2d2107440e50282e034241c4041d036898414549441c4614025900a480054101d40842c40c1c00c00000c0d589801c402415400326288a021400c450b035010b4227403c81d018040b1144bc40c5440d1800e00e840280b8944031802580c684108650302500c6001d5004c00c014002e5a6000c0303406e081000401c000c45074000400c0300e040d0f00052a290000b40c000ba09100780d2a080700f0001034640c1c13454001c6100c020010340241c812010b87c021141040390b0444146140d6000c04221040001d48442c00e42c1e4860f030201c1130401691111072023402c801c41c2c4090142c2d609102819003109000345135903220a0b0780c07007680130740c000141c041402845d501240c0f003204010b00311005507030003010141c0800c1d4002d02c14500c019004d00300400c078120003555 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 239845701 1250 239844451 239844469
    0x81b07150c11031203070810060c021002071a04050102331506030403030e0d030c080c07030e06070507060f05270f0d06020307090807030c0b0a09081002030f130c030809 74
    0x30010301544c4514400296003038159204903a402c0100e070101001c03505142c03942c456042605d0390b50702e031011209100e408108507007203120210400c51260010201d04103605480c90030b21898580142600c0d1410100064100303e16000c0203040c0305032409041200c0c4d960700d55200507a80403d006407030141c891189140442d05a4003001e9000b07080002032004040d41540490700c0f20720440d083d600030329810b400460546108e40e00304800243c1081c04240060314150040003194440d050600c5040d030007101048268116400503103c07900050820041c503600220a14041a2285071040c44c00c120041c21104013005004000ba24018040b400c9845403503400c480c0b102c03a0300c0201404803120032071a1103000303580100c4903200002c8800c44001a215030000d0f0700000d0741e610881541c171007401e04801ca00b458206003a850100f02a580e00003070f141c20280201d40d10344855030005031350b901d403c1e1a205507040c409803090f60a1035103002003201248541c41c5d80d00641c1d0740000e901d0303600c014200c00103800382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 239846951 1250 239845701 239845733
    0x121109040b13050c030f06060316050906090306010f0519061b0c0b16060c0309020306040602130f0e04060c0503010524041d0105040c1e18030b04081b07150c 69
    0x500e88418800c07065152000b441c814180681b03500c00e16500d803002d0240602082e03580010b903103400c41580d49802e01510141450150151229013440e8402000074980402a400b5000000c51044180090b00380516040000010040701940d41403501c03a005003035150714030503805061031130500d4004100c0929000c60041c1030000800e074a4004640780076a031840c403450b08403500e514101c05161264042e00941404d0740d0000c014010317a5a0319210640a5401400702610320000c4e0326020071940b102420150180000c9104060986454500001203880f2103840e0028040148010001ca95400c135505100d288116080c005840141501000501958002d404c99040c0c026000944458500c06181200c40480d03007880340c12800074085e1010b50f042011350380c03003181082050170751500845a500c8580350765650282e000c0c0d92a12010000310081e201200c43c1c0d10001101c0c03400c0070280c040a54039201d03080c040c0c4001454032030039244921040d40072000b03119400b140313181445009100b0400c15 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 239848201 1250 239846951 239846989
    0x903010506120a1214041e0501020609100203040816080c010b09130311281505010b1e220503060907060206070e040603020d0309050a21060e010216060c121109040b 72
    0x92034640880c1c0507c0120300010504131b04103201c002801e90700c0010658011403c0c000035141c1a24a0441e00d4065840280706a0300c0074000c01c030403480b4000520019041900072205680c4410381115560b0035a0504c540c8584580f01d0b2005000d00c140c20944002c14066242c1000c04218080039100c42c1440074019103840303090105210340440b40da400c1c1c0d129031604d1203000c20040c039048148100d01103d1081c0625000c100c000c4c070502c81e4508084404d5154190010b0f00c6500300780100c9110b41c000c0380e91480800801c0347d58507080045041c104085070704140b00310043d0400c10704000b0001d50f83e8200030658001c010080f80b403095151110f6000c04040c40c0c01030f241660084c0903080280c0f00d0304a5200c0c8602940700204001450741c0d48100d680507585043c01c2202405666441d00009892000403008655600b00030b6140240404070134004d0703140c030640e030110f80689003020181c10498503a4036100c07024104104d80200c44002d008603180d14500729000030701a00e82030b000c903c003801d208880200c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 239849451 1250 239848201 239848207
    0x30f090f12030901111605040209011202030106260402030c010e0a03080304080a11071a0d02270a080111070f05070e071707050c03030f04020616080903010506120a1214 74
    0x2403150110003006030b000c0a0300c41d220305642c4002c5c02a0340342100d00c2e41403003d12000b030042c401841c0540041c1051641407400140400610f02c04104030b80c82a0720881c049564403480c00f40000940080584071603101c1001c4a451a050700031a40390a62a02c10358100032036201d070403c1540d54184100003640c1c200004a880386010b1604038501ea100400a02c0807070300c60351500b0441000002d8001c280c071040013000400c504d03080050019900704440032401e5035028084007141346080c00d070802c1c406090410013610000c1e070900707115084507681c02c81c581076418601425540700b010802c035107807070f03030f001c8241c12034691a42003503800c000701c035081459500c54207420f0041296100150b101494000c498410705910b90390410380722881191403210703e5410a000117164090720401c0c0c15401800600340c82d16100d2035009040c0029100d120480b10054041080440c6050034883c1c0350344041e0644151003c4a02c62500329920310b60100001d00381c2d001204500841441401e050303510422202e40981c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 239850701 1250 239849451 239849479
    0xf010e03032104050c0307060c0b1e070c170901050708030a02070605040813060206010e010b0a18060513050f031504080d02030106030606111c030903090503030304050601051f02030f090f 82
    0x30058006880c155514030403107514190900d00070401c91f040b10030790341724421803221503a50b01d400d0a800810305d0b9000031312040b4008030100720002d0340c1e10541065403030350324284031071610f90b41c00040b00304a022031503024060f19809980000403210308c50380010010780c0320ba1b1030f000144064402d05200415140c1071100740300070000c1c913401510401030b2034000392041b1901d950003280d80d440c0034841c1c8201118030400410600c501ea400606000703c40d0b1901108040300640500c026500d030360b00c0701d0001840040c4458600e441100d40c800540720442e0102d07207500020001a0303968030411011030b070455500c800b00d0204402e100031202c2419107000190748943c3d4901010b00208680c8c0b00b803c010071034200042d0381d9000c021504848132104a108510032a112000440007080c11040c100c0a000582d407010410359000c202440c4180e2141e0300405640d030400f010700c840321300d050322590790640d0500c0c1103090341794006c01034481c08171a6a04031900c81c030400300029800d40c2500c000c1078200b000000208 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 239851951 1250 239850701 239850757
    0xc0c1908120108031603110c0901080303010609080a110402031f0801093f090810020409060b2805070f031e180308090307030b010b0304030306050f0f010e0303 70
    0x140325038141848901683e41e5220a0713449118007002400207050700c11300712000902410810440c0d61503030341164449078035034020441c1400e0030380110a5980c008001000002c1c2d1115608000c0d015030000390003e102d580e9a0080820802940144500c1e0040000381024948944862900f503807025181902ca80d0390362058000e0a0400302510456054007031007008a00c600e569145d408034601000d51008544250325100644903a544401c01412160000ba0407908001441f490031001e50b0059039140350640300400c94209030f001f400c1c00c1d00e0501681c250810128595102034040030440000d0300b40d001400c071707514400c002c4001d01030040360340300005059005035002000b991240c4810a0004824401e990464194034030794004d0015650034070005150801811b8032000c007808441d0072588a81d5030625580d000d8000200c04c01000c8100414503030306019210043c05d00782e4000c000c80e04a030011414152a07008514107100244081141ea0344080040b0344003c1200003d1000068030101c0b16 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 239853201 1250 239851951 239851957
    0x9200a0905030105070f0509090901020405040e0318010c0203030a0f0915080a05060a0f05040b0d060905150a0203010b030c03061f020d080c0310030b0c0c1603061a01080c0c1908 78
    0xa0183d0300c0c0000044070716000f03c180118820280c7c4a5130b080604403001c2044080008264802e155003d010000329900d0702d004242c1c5401c6868090b540300c00c190219035503103000c101c9405040048050384200507840c04000c54061841500e080075000e2080481601d102000d03500005c00480a408241a8140c1c003c5c1030301e019114913403040c805070719004100407441130680a640e488a9041d8410401445c00b9405202c0002d030145c52182025013a4551408171650140191202d4001c0224142c19900c0142100d60005402c00118119410032203402844d000c0100000c41c3c29400002007a0156074105040d030114200100c90100c0103080c80b802500e81140c1030082000c03c052a000c9003d419041d41a40c0c0f00f0101c0c2c2c04800c0e003491450b20b80d03001f14000079000e103005a0f07041104001300700091060b4810000e4205504140525600d08081200c400c083c510341d000b08551480d109580c2c1c001445504003c00e032401640768924400503030700b05405025401034408292200400b003049490107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 239854451 1250 239853201 239853209
    0x91c0f0609120c02030d030209240901080a05040309031202160303021c0516060b061603050306090a0203040507290d0902040b09010609090225050109020a05030a08030109200a09 78
    0x502c2140140e2201a242030b41c601c00c00a5141d040000040c45c038612aa020b81900c1100405812206020b52003c2134904a1046a0aa03800001481007d156005029180c00400c42d090400241c034041c1c030002c140c482907002c02000066445104031800b4420400c604c5041c00c201410301d00e9580da07140c041c2d0760f0151500b441444444500c01000690b0280341514410402e040350b50040b034003180e4442c03000b01050144a54440c0b003e11031720a08140100c099034495119484066036820130408014469000414103100e8034010402c0000003100818004100d0708090a52180c403455049004d15644080102540e000342c0842d00c0041c3c103059802c000c03030290094808002914482c0144280075109000b0f103800300d0f0300c02c0020800c000e180e070b0040040c0d401c1040c14101e6801d140e0000785162042c503909440b035039101d01c5844291716091076071a000301401c400411000915558070003e5020501c55042807a5a03418084400142c09010101c2c510300750340803a030b45516040003c0c00720307407036805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 239855701 1250 239854451 239854463
    0x80c010501060206130302150702071a04091103010b160533010f1d060415061214130321090b0109200301030f0507080607030906150605091c0f0609 65
    0x1c85d100c401480c6030b150880d9010b038041d1080402d010380c104a5080302070280421803241d10350010394840107080c500d61401210004660b42c41c9030140c2c06055400703c1da5140b902400030401044000e5014007203410707640d2080381445007901c6038100030f42804290348540100360400c4002644114654003007442c0045002119209a41c135071a00c941190118068864070000b183c00301c110345030340c520501d5032160008002041034121a0418084004150b1044001c181c414810b000c1c40b034868000d0405540910b120b80490b440d0650030019260f44240020301400380c42e21000701a00c5a041401701c0f205000881401f805850340b0302228514401d00c501c1c0415880d00704000d04c00b1002e00201c002402081c0203807810f60342561503586651a00c84021185440f6101000421400c18840310380704a113140c03800243e401c070500700704094401c02080d4415138071240009114507504481643c1aaa600b954051202d031014140074039640394110f030180c28034451001e10010031505070000501c15100e00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 239856951 1250 239855701 239855713
    0x4090b21010603021e0306132105190c030e060a091e0302090a0501030201020a030509030307060c02010e01060b0c030a032d0510080c0a051003020f160311280807080c0105010602 78
    0x24201312070341c891780c1c4009505410403804110307400b0000b1241074019010704003c6014005000c42507110012140141c0c0200301e02040c0b091100450b11111080f4140a0034410340001c0c8580d070042c81c0c07640300c910b660302c681c40100345090079038403c06040c13011b007040203c0c9145038080300c1640b88902e00c252108a11a10120001412403d070780d00806040302d5040e001020005190765043d0344980001c02ca061301440705000990200c0c2d07036070065071140b40a98000041c1a4203285500b4290b80940d002f5101d00f400c10031085035101310003c03c54101c03100510300010804280b0881d080c0d80382c0600c00d500845400d0745130860210501e41e1204c1c0c020f40500c1e10f900500d5655240103500c4082d070742a02e640c04a000c4c5003c000c036080c4000300d460b2121a5150042c500352041038101602e0f00401800a072802440d25004105030304039001c0d07450504104010b00002c14100e120040362500907440c0032140d0002c0d1941020007848000b030711000c55100003a103880c0d4400c2c4541900a140034810140188102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 239858201 1250 239856951 239856979
    0x712060e1b04031709040209130b0a0816170a0803040c0e340203130f0911040506030406151a0c06070f0203180f0a03050f1b0604090b2101060302 64
    0x5002c540c112680070701d0003860030359031016003041c9420012610b60032a4003000910140c1d070f2594603104494810709800207a11501c00c0c28414041d0701d580100c1c2140d03000c1f4a000304a20002440d4074200c5030744131107021a1041090026091031a2200000c01e281008801c0c8000c101003500240c007030741c007120040e9106076a035102001c08003010300c82c2e008100c0043c4e20b000e010144101807036800c0500354011249407040442003210588001d6020760090421340318113110b5200c05000348064034052030100c5041c20b0905001458a00c406840182a6592021030518010060001e00020310001ca02c0c800e000019030b8948010303501030541b400542c080c1500050901d40034540030800900140c1c0158100014541004000183e441e107142d4028074004005039103a44035080440070314440c801900541030702d032442c01d01c2c240c410241480415030250300d0840c19182c100584040392040070021400e80c090101286140c1104405c1446580404543c8101c03580d05400c54400c42e4820354028004000d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 239859451 1250 239858201 239858251
    0xd020a1707060f090b120619060207090e01050411101e0309030f031109010507020a05030102040902120106020c0f13020c0708070602070902040b0403230a0b0403080c0a14030712060e 80
    0x82801440307030564043c096110040b046e07036129684294040c14145050459017011510780c0b9042d44440c006920000050001c0c0300103018880254045034028443e5003031580d96410407148028101e401100c6010b0403031002d030f00c680c3d28000c04281c005c1c1410000c0c0403a81008000d001d8a80054022507802c1640c204554801d100710100d0041107002182001f0160b401140d040d4015407090340d10551612002c6111f0b42e0a1004000428850b080142c0d1000d41c1c0076030050498059010f802550048035031542151101e50310580c2c2d4040841f14580c50780c03260312940307009028814601d111489a050040b6940e0800034440080c0c402c0e0350200c442540da42c9001c01700fa4401d03805130640300e940c148801c00c00600d80c0400702070b03282079034040101901c9081846030300c0d03c5803246066aa481000702840b06164001c100d464000c20100c42040c6031408400004c0c00200d02d4684804020b10000b0000b464107100d811501814590a6800d00075107559402c0140c80341019070304034490465207184a101040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 239860701 1250 239859451 239859467
    0x9050f06060703120c1709010218030607050904090c03120f090801020c030910020f0a06050406050105010306120f0302010e0312090c01050c0d08090a02040513151a0d020a1707060f 79
    0x1a040d9181030055468541010141c4098100714040c08000001c0c1c040c0e002c1c1c46c6511612480016000586500c0d00029164001d4a000d01060082c3c00500a02480e142d01804035a05100140c1e80401c0b40c03081c515080b000c0c04816400684411001c01074a01e03c1584403000c2c80001032580e03108201c40b03444402180c00c03440b4203e00a0b41960003001100e00c181400041860074010f81d0040d241000c40c096600c07820651540e00031508150741d101000304000e4184940c5014280078601009040c2c00c00e1055101d040050700050200d12490200c401014802d41059503480e01003001d4944a6562070010650020107840007c154002e80c0c0051040303511607404d03210740b407204000800c040002c1d2241507401c40390141c4941071a024418201e405038a580c040d05014495015074000c1150060030300d00000c0d903402d40007540d501d051000304240c025020003040c52101080708c030310030808040d02c0021183c4899510503c4100c1c1c403181c1c68000040e010a03140100c0d40d06d6111817170502e994020440d1019 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 239861951 1250 239860701 239860703
    0x603010c02071a04150f030e06060607061a060d0f0b030109050d110f06041101170601082805090601080610030c060503072c0a1d060108040f0b0109050f060607 70
    0x10748007000403c001002000e07100b12a51010060350f103010789071011031030488108240200070401610071580c1c5507a16210f01c9000f100040003601d190b040100c000b400b20310400c200030b80090b44030386421581207030240426500040080c000c41d40c95250407003040103040d860f484442d001e032030238200c850981410300a650b2040c1e4028081c107000d0201d4501501c04001c0b03021841d00c00d101d01605220308080410220b4000c83c040c3c0030b400309801c0050001850704201914800b2484030303040034840d1590b001980e02d5000b4030340f50f40b140c0042603080d05015103000c181506d0060b0506203010300c01c5242000c0b45142c14dc03008401903a88641c0c1e6600000101e00a07840000d164003050401041001e00c01d50146030008100c0c50000c509101c00242000c01d498164204444d020740c02030044c1d551315103826000010305801c80400f070704940856080034084002000181030045000000f007c004228a554004540c04000c501d02540c40325500b00003400100c410030350303001b42d2030082016442c1000945800d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 239863201 1250 239861951 239861953
    0xa090207020f0603090a0c031a150108071202070c0f08150f040206090a030813150306120f02041416020601050612070c020303130e09100c08010e04031209050309090603010c02 77
    0x8000c2502c00c1c000d032644002c2408115001d840f130b840b000620140c5941307000b1030242c08003000038400702d11404404c1c40050f02e0854078900341c00f5031081c40c0e6046074002c1d50100b00d90070400000319030350350150068031550380001d0175004503445c0404d0b200075900d84041a0740f030441c11a1002c9030301580a86110800790303040c102d074a01c0c1d8800100149040001400855005001811955a251341e16420354001030a05810b00f0a42442409804068610019030003039a24051140c00d1410142450003145500050030f00303802c02d050b403401d43d1110741012044400d4800720300c10074a031840c0341c0089509084130a40040c00b0302c82c000541440c2a10640c0c00c007a6900c04c0d180544e0b20fa2800a840c84100c00004903014042440454405024a01100c0003844445080902c1d440c1100381a0b0406004510405070300d442c0248100c180c5030300900d5241510940702c0f101d45180c5540c202a82c02c0d1403a0340e1410000c0781420a804100000480501403055068500c0f003060b0300e44a04040c241c9503d50101001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 239864451 1250 239863201 239863219
    0xc010918090204050108010207110906060904090809090c0d1a060301050409050a1b0305060603030f070b0901060b19030f0902090a0207020f060a090e010b12070c0204020c1b0a09020702 81
    0x29401228484540810304034001080e144039400304007501e0090784401c10f0b60358089004018010303190303403811101c0000c40b0180d0107890408000f605e28011540d002c1e00895550039030100b00580d41c02201c010680080a0021502d84241d15190651001d881c60328960f0070181c04c1025008540d026060f0080b000340285d045a091800b0302c4020705001070180c5141c4124070f924000b04070821603100d030000401c218215000c1c1113041047c60454054030300ca0181d40b041000301403140b10b0b1030a542189034418180c1c219511a1156039002d445e6641081c03014240005800950350311051010140d10540c0e2818892541c207084a24101c0346200000303134000c0621400201100c0e44da038028824a480240b601a00c48240d070045070b26a000803481001041c2c0c3c04001703200d0000d2031410a8010f00c3c1e4000c0d4140f0740307001882c21140c1403038090059005c3c800312840b18400c43d80c407501034800688036882280d100760401d03624075405004945000340249044680840c03d01002d00840c1d941580150040c02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 239865701 1250 239864451 239864459
    0x16020f06010609060c1b060e0f1e0f1f02031e09030c01050319060b04030302060c0f07030e0607080c0c0f01170f070302070f150515010804030c02060c0d110d020c0109 73
    0x520810307817503401c60344424020400306802041740204409031210b6510b1500c4d0381c0c001010300a050440c04521440b4425111950344c031180e5001e1141c40c42d003020f5644990050032600410344550b1008880d6642003408003152244a41c00005000100c1c10148c06045402e1307030980e461010311609030140c2d0150404000c0f07050715400380004507001145001c0c840702c031407408080c840c1255904e421403030820b0700c0000c08109040e03040041070b03000000340d800145072165032034000010303208600c0c000b000e0010005402c01c1c00e0b624071040d1480203401014160741c0704040100640c9403410300c520075201e01a0718100c00701c154850a41100084c86c0da44202c0202d13107540d0b95468100000600310010150200301d807200140c1e03101c1425200901c51003032000e08800300000713030301500c00003425086881d01e8000d480034036a07403220a00e50401d40509240807603600307030b0005c00e00300c0c404c242c451600c5205032007400540c03541c81180143d07507070400c000366440c000c45002d041340c0380c031502c1020034002040c405040c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 239866951 1250 239865701 239865707
    0x303090907110a150608032817070224090307081e070f05010f02180405070c06020412020114030705090918010c05030105040e0601030519020103020c010516020f0601060906 76
    0x264000c969414080041002e400502e40b8003000c58804880d91115410702d40000003c60043d18003a004003009142440703401c7c10100601c0e44001e820100000340b0b11281c002042c040c1c0280da1005c09400c203010720078a40420042d5a5940152000c45801d1030650140b840c456141e01071400b4035600342c041d40c5003000540b140b1840b074100c0c5000d58000c1070030062140310014408001c102c11481070f00e5100c940352a50410742e013144d0543c1001c1085d180100f09450384480841411581e920301120005440c1e05d40c600e0480359442d00c00c600400c164400200450240301c00381d0101c540e94403d0f0b0f107600220440081800642c00203456042c00300781c040c0140003552070603008441d4007840700341d000c8807299110800340b402e4501c15040c42006c00c200100510450816000d003e14403148a8014219545550346066032040d50b00c10410b13600c40c1d050b81140442e07100360126408440044000d000500f0070100c88101000c080140b80301602c11503641c1581c812010035041d04860702e544416080348d180c09030907 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 239868201 1250 239866951 239866969
    0x50c09040b041104030303240303051204110a03140c010302070c12080d02030f1005010e0f0103050c0d02040f17060f070c020d0602270d0807080f0c07080109050d0905030309 76
    0x1030742d001d501c4095540b1200e009001610085009a80204220101101801d1100d8000c2d440d08d5500034090401d00210b5044011100d0b01c0c040984880a99921428021300b8036602c031062582c8001070503400024003c4e20300c0b9049150000c1420343d10702c02c5c03441006504911516a0003404040c042200300950a403580b43c06c0090b40c050b94000d45401d0703403404d016040b64421940e00d40b0113900c1c4024401c07242c1c4841d040da07010301020300744124000403042c001000003049100403410913850b900000d20541c81d00d4182c41c400c0700e0b1050b00b991995200c1c6210000b400841c090000070054862401440c0c440c0054114010426641d03000300503284c4040484142c0309403442660000c01c40d186001c002240c52004008203540c00320000d41c9107480044203082c5000f52042203205085450079540801c5007401202d22441d0312104241d6105036040c03a0301124056170301017070a80e000d01400040e001e2419000909002d111f04242c0b80c042d02c628a050701c40d103600d0b0181c180c1561051286142e9402c0001c02c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 239869451 1250 239868201 239868221
    0x1e05040218030a0609110907082404020403080910051e03070e1e0f0604140607051005070203130b0f03071209060c020c010224041e0204092004050c0904 67
    0x104400780c84400881c2c90403500080c21104030b641c81107404203200040d1840100207808580075801d80c01c040c0381c0180b4800c009400b040c130f40d06180d0a20070310381810200300105440c1c01fa20170754071180d0700c0c10507a00c281c00c50b00301c1502801c11305128120b0148250700700c802e070b14034403514480381841d041c142241c0c0c1d030401000b030002d00c1443ca05480c2d885e641c28600890202c07100d104100d014007000140540560300481590094805100902980c51020002c0d5005c2e8400c3d6035070342d03c603406420240d01e004e1541c410070b00441e1803c1c003880700d16a4040014080700010101120b62540d8400040240e0722851101e08224441030000ca4556031162160b01c0c0444e82440010440c10500d807500c000b11400032032400b01580c0050160b0040356014060080140040ca55a0300b0b1132803803058502a449000f030005000070401c007650344204c504d040b01004140c0e0042c0c401c01102c807051504120840c2d100f800003140d2000340100c2c10b01da142900a4a2140300140801ca00307041148082c403010f000d032212 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 239870701 1250 239869451 239869477
    0xb0c0102090405010b0423060306040b03070509040503090a060903020d02010507020402070501111c0203010f1a0705030a095402070b10081c0503040812090c0108011e050402 76
    0xc501c1100355200d0261038041c000e6400e469550324034141d507005005050400001c6842e002d07004c0d00003241d071106c09403a4852410780d00410744402070300c00641040c05a402c01a44402d145003400240903000020b4a1200410345548166603265601500d10070000d11000b58000c1e125114000194401c8004c4c0280f5403020780b016041a030180c2d40d140c2500c48a00c041c01c40c0b040003141540c4001c03a0f18040680300042c80e0030462555040c243c60480030100c078041c60408243c2c0b00f2132210060488000c54440d1500403058070f4480006550003043c0c8803040c840e03801c06a240368443da0328080001414241031004000747c0311308a10000d01180c9401010480102182e1483c000c00305d4410b00e80010028203109540031129450490313507412041280e5004581ca5a2040406001000c1070704441c50220390141099038480d5030b54501001c140c81541c000f1410303285443c0130f0129800340003403018040b0409885100b820303a00c8020129580111199107001e000650328108420308281e40241500200c0d41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 239871951 1250 239870701 239870707
    0x6030c050c030c010506091302030601030609110604090b0907031a0d051c03020d060803040e01121104091407081605040e010905161403010506100806030f1c080609010f0b0c0102 78
    0xa140c07904503040303d11000456516030307040181070702d459035010354050000141c000302015550042580e840c03050000a25082d590302d0306a081c44104501c4401844000702900d41d207980b1006204003410400740c40c203000e44401808251024041d000340c08424115484001d00c10303907034204021402411403420b0300d080c020145025440c0310344c1c240b0507881c45095200540c0e0786c0c6410f0308040407113a10b540320803015001400b0503c0b1400d144a1200e0440354580f5009000d921b5505280c103400090225541e4094984080201045840405d040e403a11032001500c0049a40d011001c2d1510302c844a04c0f800d400d991101481640b5240d40403000c0688a17a0002a00e0300956071028039041500403003035502d0040a1042140804190542100e00c20039402403129040c203038089201c0000c200311032410f0080110000780d194030104444525065004112001c544030309410b41d0780b040300c20302d40d00001030895000401d94203003900d007507040b42e80076001c44000707500e8004044d108c0d030800403003258195020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 239873201 1250 239871951 239871967
    0x40c0504050a060f0b04030c0b180a140f031c1202041a03040212030a05092b03200601030203060406200c07050109060e01080a0507110a0c06200706030c05 68
    0x10710985204210140c000103040781001c8078503034030700072940c000422040200014400500c50007080021541c006540d191103400e00c40305031666040a02d5005c3d08540041000500400900c02e0700c4080c0c0d4050b6a03460100b180ca00a0584800c68061080310070741c00301c00a105094170658a5002100c04168014180381d2900417064403910a1105100104004030500041d468060030100014401200a40c900004d41d180034049004146403d8409d4101078041b020541d0030780d400b543d00c0f441500d041c6449014501d405070140ca0380e000b50506c90075079031424a42c1c1c050000750070380c10707203400a00409942d0f44070380d2a100036000c0405c01601c00c603d0191034000341c0200002400343e4202603000750000340d0629000401302c1149500007400c001850501880c2070f40c2144055400c400b00c41c0b00825140c0c0e4910050303035a410036540011291140c41882c4040c028141c40c00700699075103503101107200801d034444507003180e54200b00c120203400c207500800c83c081c001e03409040402101e0604c142410a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 239874451 1250 239873201 239873209
    0xd051803150708100609151214040b0117060a0b0a0314030a02060a0b0919020c030f21190203060a0f061d090907032006041701050a02070218040c05 65
    0xc014807018408219418420a40e410030003d6510042e98113502c0402c0e46800c4008141300000e100e50841484000000030780584141030b00c1400c0710320514180711103650012880e1110000310303000d0715440d40340d0001165844240c1c5c00c2c0310b030704000400105450b0b1a510f0170b1400410030541ca244c2c2c004102d401c0000002c4480f94680a01c03c80c00000c0c6403182d5685001a09090b401012910300f0391400901c01c100340e480803052030b00201c812038010b2011426075413140080c840c0424613900c520001c114080c0388041c6074010520071641d2000d00504d40c00e50070b850b458400307094a01c808041c8244042007a5100035602555200340000c2030b10a96513610901e032960002c42e50001400200d080492a2024500b0042e058604034140ca00500038904550f00c0364903165203000042000c5940c00e4201c0034400c059010f5a071101000348419580c5950b84101c0d01c40181d1100e11020303d5090200141c0078080600c00da5031644d401518441440b4040400d2407031070354006004071170304040307524080f5050f11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 239875701 1250 239874451 239874463
    0xe0601080303040510050112260c0703021f0c15090204060b12070c05031b07050301020a0c02090a060608040f0204090b09060a060b030103051509120a050901120e0d051803 75
    0xe8003501455590526090403400c0c901203001e6044998103243c01003140b58118503042e80c071b0f6900b268151090740da4800e00e0403040f941840070003032460703808101601c07124000f143d505c040301d00c00c4908649281c10011440c0400e10712050902c080b800c1030710300a01207410004a00410729071050300180342030841d40003408581440e00990044c110104889807540004c2c0d09154001c44075080403940030400350780b050703070320300c11900310303180050f2100c2503290b0304141046820003801c8020025901d68011180c001e00054031204103900c030b50b01d880046144004c45110f00c00568030182d40701d00581d540d41c0c84401d120030b400c1c1c0c41241c1040d503820704170000c180c81d0550340740141c031a1800380c103450410140e044e05071400b5401040110340200010000240002500a6440c000d411480050798480d1000b6041145070b5601c143e02e00f40000b40500810b90200040c05039800c00d817a80928640140720507011500204100c0740c1c0740d40f1040e00f0800302030196002e0310300248443c0517116140c051030003080c180b039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 239876951 1250 239875701 239875709
    0x617160203120f04030801050d020a05130209090f0f0705040f21050d08010806060301180b0402030106210512041503110904061d0a0c0504030b0903070c0324060b0708030a0e0601 78
    0x122202c14130040550054079503004000031640c501c1c4003101da8000626038a25841454410303100c075800c07030710f0042e02c0b42c0513144510340061030040e07240303091820841154805c40c1c441d9031003500280083d80d002d010b00245c406584040070b0580640b42401c280b40e120001c41c009200759280981040000681c0070010340a8424180d91200543d5142a103450316000004e021284213074102844081c02c210041108d02c4043d4102017546240d444c6c0c1d0000ca8014142ca0700200a402e10003000510301120186441c0201d61080044690185036460824101d020700c1c01020542122840d140360024425008490001e100380445072801224500040c00c8840c3d5600c40030791910600800115424164665a802106048244081c50110340010080c0c81240001001c0d1807014021800d11002001640d011590106000c03035076507102c0c106121603c035441141044541281c40d40d01c403030b10b82e138060542100d074500f20b42d0741801342941c3c82e241d864000610b4230607044e43e070310030240041c08200480780c020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 239878201 1250 239876951 239876971
    0x70515090a02190b0f091c0b0f011d070c0302010e1c0801050d0209040f1a0a06030b060a030506071112040303090f0b03190b010e0d120207061716020312 67
    0x1507003644140081c015120400040c0400c4480d020010143d40c20120340c40819661015582d502112001507842c0c1080b9044c0300703d80b000e000d004c2040142c254112809202030701007052090782c2e03550b1000080d08080303e01d540d03500310440100f06d0040c0075640440d045e5100e400040b44202c21141214a80075001c0c1c0d10450000704072969000305a04003520030f000d001d0a40d15000c01c100c003a00400d035800b901a000404081102d0800810712402c00e100c0d814003000006120a20705100041070050291400161400e030795001c04500c0310700e45569a4000c5903404005032070650740340c540a6440c0d0140d07942e000c8550061822002c8242c06060050025511a8032a403840f5403d1000c4c8034117400320b82e00000c071584030400901549140c0c0307982044150404020120b0a842601d004171008688800000d070008410058542040211201900c14140c158211407005a0724602140d46008604840952500c2c0b54045810f01112000c04d000f1072040c2d0045134038005c5400402010304c103080301c0844117 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 239879451 1250 239878201 239878213
    0x50f070b040809010306061403010b0c16030804050907020a1106180303030415051003080d051905100e0912090d030c05070e090c040e03030f0a1107030302031603051b07051509 77
    0x343d5a09441800041c001c90b280907074440c070442020945520041c0640c04030750704045a01180c081c030401c41c800700414940d159840c102c3e5203280c000b1046d0014002c291103503e003140001e80c032074400103890390003030741041c03009140f0384041c014030070958000200d180c100c0c1001a254449502c040006602035489214441d40e0f912552103080120b48000d45400c507034042c40c803020004100147c0590f0541a41e24100107102d4558807000801800044010440303107040004018081e41d4200c01042101c440c7e40c0180c4003591888912603c0b4141200110031400c8c0500035100542090302034202802e2080c02e0030342000c0340b15113550745001603c1d840202040c22440401a41041c180500e0041c028150307024010b0a480c0883c113a2240001840b040e040c50074000020781490782c81e04a258011175514a4130b40d0741c01c09040003000b03507000f142c01414030703031480d02d688144a210b80b1559126070100010f06d2101408002100e509501100e0f0613240c0b031180700c5c0d50b6030700d107098489200d004058010041034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 239880701 1250 239879451 239879467
    0x40819170601020a020901032a030807050706030b010c0602031b07150b09010513050603100614040b09040803060105300403020f0604050304060311480c01050f070b0408 74
    0x220401001d150440d04074180120041c3c4a118215064035840404d60441c06034000311069482d42c074000000c5812042c810001c24802c09500422800d4022010b50303482c282c60712000e40079660100301a0340050790900c101c2020400c01d601850700310401c440840750102200d8030038507081c2c0241209031180c28803c1551040c80001d0301c9100b100c1c1d4000d44000714598585030004d0f00d40031007244452011601cad0720019680d60f40500082000c601c102d0b808102490311040c01031a062a4480b6560280d45481a6200b070783c605050030520550340a59000e1942d60340c2e03401100d99400542c0011020b004200c03c00c28001100340508000b08036441c0312444500d0b007410007d28108a480c000e026a81005041c080418000b00072107058941d981004100f42240140d03400c80343c03060188800817800080c9501001d8107000003007486180d81000040085d2408000c00342e4a114811204580d5500c10401d03868694000c0016000082d99405103504100003034940e120340000c111001c41c1c4030300c00051128 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 239881951 1250 239880701 239880737
    0x15050117060103050d08070e0d080c0d0509060d0e160305010902090f0402031b010918060806010b190305040305040e07020f0609030c1e01111803100b010f08040819 72
    0x2818091036031004040035459926003a88038440c0b04d03190801c100700240043c102074011818551528009005516484802d0034130460907040040c05075458043c41519084092045c01500c4000c00020710141c035007040041100001d081840304410280103022030384c13864807074611b4041c00950103000007040100c203074410000018002481c01c00740e25064401e200240c1c50010b40754544010520441d841c500a2100689250055600c91286050314200b0303546c3c5070845403c080300711010309046039910b03621089202810301070100940c0c102d680a81840c07200600c60b4001c56045402030a083d0302d41500c1e0001e074250080c003201c2e0817025030300219030300071681c004128031640003a2087c040c0d401c101284815940741c040c002d6038000b44440041000001e41c00071b52129481841a074003040c0d0f02c17503030f20145e03c1c0307a24003d802c2c6512030f0007803803030204040e0a2805a022580d0050792030314500304200005840b45280900252000801407007000c5182500e41e5803804e4111051700ca0303c004054046200e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 239883201 1250 239881951 239881979
    0xa1202030105061c0605090309120c030c060a020a080306010909230615090918030c07140a06080c030a0e010e010f11040620101103061008060109140409150501 70
    0x4a8055401981c1303448130003400d4842c0d00c00382039001d18045126100c40440b036181d40515101c0caa0301c604000860780710084c00094a04210720194107881e0803100c8881004000e000c0c0f4113450700542c00240c100c00008401400641e8041c005061a116807a10307214007004039540032400c003289890041d29603215403044d000103640030504813040b82c4490015a080c00090007101d170344078001c28070480030134020101d11100c401c1001141044a4591607030805c003c0c0c0c0c0d5401480f5001840d0205011000142010b0f030000003a036203a501c0d440c1c03050b2140410011203500080421442c0c03983e80ca0744002100c1c085c001c0031225800c5c1d00022401e03009038403003030301203c1c0c2020254000f014100410440180c110440d400c105100003c0300001c650301080da10b042541a0422410051401d0710303000300059400003031401a076054494074400741101c50299010300d419100203001c5841860104417100010001c980f500304080c03c0410440030540e15081980c103164000c1042644810040c80400400386103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 239884451 1250 239883201 239883211
    0x60c04080f06070912240c081b0412110a090b01110c0f090717010b0703030b241e1801030e151311100c050c030d080c07030e0a1202030105 61
    0x2e06014200804080c00040f5a8480d6202c441d250b00b0101042c800c221850007055411201014800c400860801c0e0040200c9000d15001ca40c001c0040340340f2010100007000500b10b0410300700c1ca402c2c201702c9580d03080c0000c54811125240084690041ba4031105a00c000130090401d01094044540d400034002da90110000d110540c0035140824250742d5400403c20141000d5803520134540301c03041304030354508422100034010703102a400001d5050926000306080c6020395800c202445401f41002420b81100b8964500891391400c40b029240402c0010102c05d40006011140c1c4040848041081d82007603000c56512801c0c0240d00d0560f503014018444903403266400707000000c000303181d020b101c5030014001130302450b00c03144031320100308400c080603042030802040c030032881122040013041c020b00c00d4400c071128004d01e030030142c25080000350074040c450f668403000c0c056170b0f50103030085641c0c00055041d0108102c191511001d51542240d4601802c1c0c0488186030905050040c1400c0d9940a44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 239885701 1250 239884451 239884453
    0x9061a010206010b070c0312140a0503070318020f010f020102090a030b0117030c030d0c20010f1104050f04110904050c04060201150f090c0c0203011a180f06061308060c04080f 77
    0x1701000620000b5000c402d5a0f400a0702ea101c0f00e240c024201d07111071084800c0e01e401040002d815100342d8021010710310400c111341e8244500c64000340340e40c8442d080110000e400c11050403403002c1a40c013401c00b100d40c40300a8400181065440782c0002c4014005a2040e600014148010b02418440c00030040c01e10400c800110302c4c00c3c0c4c02c121010b65030300c0350444000201e682d0764420528144222513189030f1500082102c81d02e9400c1081d081d0003001c41d2805030428520b0030b440a02e46220748005e03102201c500401c25400c0003041d00070311001c0d0442701d803138035081c500030011b4070440e554a1040e1405000040422520365061150290866a90075550508130050380800c214900300340351108192000701b4004a4040100101904c82d4000b43c0d80095255007440c2c1da143c03602c0c0e21215420381501d07040700c00c1c0d880c40c4151096014134510075101000409400400108181803100050554180368000d140840b07942c1c08040b8241041030740e130038518280005042000d1300007002880c0042c11090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 239886951 1250 239885701 239885707
    0xe030a0c140918190318060f02160f0603020906070c0e0405240105010f031b0f0e0a0312111e03030a2409110c010905100e15010302090a09061a010206010b 68
    0x1d10703ea507142d10010b680780101c0003028000c8101441400401400c0c1003501c000044d143c1c55001c0908840a01c8070000c0061144c070041c1d40b60030049000c108221406c1d84a042101800d00004401a60040b2007140d0404000c11520b800038540411034002000c0202500760f440c14540340c0182080b000005401c28080b62480e21543c048094402c61304403042420090b903202d002040c15406809150000c40494003100482048a5080510007410807001e541d04101c2ca41c0020410031850041d00002e020184000601100940a80d030251034003140b4034121480f80b2044c00d0411112001c030494a0781c1d0b0707040032084c051102160300910a209111040c58800311501001c040d444003264851507001e1601d172851503c5090603142116042020b0100a000a10290900a6903000c00c3c01d0002142c0c0d03c1d10481401c806004110004d01d08a585030100140c0d195800f0401401c401610900841d582d032458403000911610404081c035403144903041c0002040740000e8180070050b44a001c01c24030030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 239888201 1250 239886951 239886991
    0x16110f010c0b1302211f060605160606080303040302160509040206091012110403020901080613111f0e1f0e0105070f02090c04090b03030f0a0e030a0c1409 68
    0xc02c603070000710802c4034604442640005250711614280607118140541c0c03041140410104500c0429410040803100e082d500444590444a4a21429000903000d100300c80014040080103880640510030104450741c850f084903080d039001303031021405a440303003508825140d18844144001c0100700d8000c10301c0d1410b41c02041d01842011035182c0b1501c000448401c03018081c001d9459051048d880030082d400c19004440c0c0d8551140c00300b40d110310b0070f60340009089180042c0d031a100d40082c7c0c40700c016040307542e981d40819920010019070310005100200841d148a0084585880c169690700280c0b901b280c41400078854844640105a01d448160034040c5030f0004500245400b082c030b05150344d99224140124694200e020096200048000780510018440082c0c025200044800c2100544910815070740380f01e0121000950903050200540c1d035070252001c810524805800c0d107450b401166034004042880350001e902072800e900c015982d038102100480e03031194050034010300d00c00c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 239889451 1250 239888201 239888213
    0x60112020915130606030207050105090a1a041505070804060f050106020601120602040b0c280b06010f021e01020a030c091404020702060c030c072c0411040216110f010c 74
    0x8010b0020b107407562001c02ea07051544a540088401c1015403d0400030b580e1140c80090103075001c07040c150b034950309000109010820120311004015170011500902c074070650201d00210304000c100b076504400151000d038044a01c0e00031a440355401c0c3d9680e460701d18089c0303015021120f001b0b0300c215210740f80000502240c7e40000361281520407401040c0d52050b658541701020b481160003074034030301c0c402003043c0e40da44000149509600c40c08444030040d405221941c01a1525100b402078407405030710002c05e2855014925070200600309105031403940182201124843c0d6003004100040c0e03600007a0f001040e42c0c140710780f4400032080d18041c1002840e007030701000398001c01c01003e4800c1d64005000b80031907881c0002c80310034081420607070303494030303900006182c03074205074032400744215646103008044004004070128100e6003d18004196107664031000806130440c80140e800540c02c108a0b213107080c0b1b0400002849209500c1c4620302c1d030f4010148554540302000e09070510000e070600e0000209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 239890701 1250 239889451 239889469
    0x30c0b070c09021b030f030106030617100203070903020306040b091b0604180204030b070e0306070c0203030331060204170d021509010f02040b0d1409070905100e010e0906011202 78
    0x40a850260f04d80040b00700a015010424102c1c0503113110000f44c80100c08a08000745040302c40765202004038996841c021000041520135101071030b0400c0b803080448981d1a40a141c020120340740c0803003100c0c2c0725808246015810b44007039030b02400e0700040101c50310040003c201803007401102c0c41a170250b0300d00481d0550040d4080c00c00b000c8034001c08084400290b5040c0d400868120001f44e2207800c0000003d80100748144540c0d001e4002c110000c2c14050254074600c0e0381c180d02400a41c5182d80d80812261440d24000f002c0d80c40e4141d5131101411284074811003480799000d440e0045e070b603620f0034211030500ca82107058542aa0020b40200c0302441c0c003c5150640150020203003c100c0d03846400c9503006184130784024046a2003c00c1c0450141041c0c0013500c01c1c80c050110801c0260740c08003019001d243c040b1085281a84400c600b031004030540d8121542055840c1ca005e5100d070b850b80c0e80304003036a80036040015858142c030308201c0ca840081101a0041c51031042e144101d04058000c104d07440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 239891951 1250 239890701 239890709
    0x40509061f0602150a02070515010609080a0c12150e0c131407050a020723040e0109080f0a02010b092a07030203040b0f16030908150603070302010c171201030c0b070c 73
    0x403078813400003150414140c0449424503030250650305003904503001c076900c91600b0b000d01d20000b58107010115940c0d2000494040b0342d0b400c0000ca402c11403a00c4403903a1050440300089902e411141e0308040414164000e813010320007950060b29030b500c0c4034801e2203500034900d140b201c1c602e400c12455100070040044000c0d0030081d1860070726034074801200d050340713483c00c90351181c6003541c0402840000407010303605420308010102c0702440400c1000211901340c40c11400043c182903030420604035a0400000100903a0440780008600e4286100003d80c5110007100e803a034842035080c00000010507419100d480724041d84038158280b19164500a40c2c90085001e0754007940350004405802480075130603a00c1d400b50000701c0c030100b40600d19001b00313172070344a2044805521405601283d680b024281c918400c82020b80280720b0a482d640044900c90028007080c0c1c1e00d10200f0318004460411903000340043c04000c00030807455455440d04040f844110340c801d404805050060344001141030500000f00c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 239893201 1250 239891951 239891983
    0x1b03040b010509040201091a09130b1e1504030809040b01050a05030f060109150c03031107080906180a0b0c06010e040203060420060c0c040e03070c12030e040509061f0602 75
    0x181c2d40c510068035031f50280d030403045003d0044107107542c40710b003050014002407034140c5003000b12a0030b8203040b42c2070303607000030758254401c1181e4809511103440d003000b40012032000303015030726140c000102402c440c5c4c001d03002500c0d2902c00003418401424a4001c2180410080c60602d14021019030002c0c45400090145a0600c24034404902c203680b092440102805071450707051092103c10700040d00c1141c07404d130b08602090a003120480a0f4840e002910003041c0c009103090f180507441c0003008031a0b03005129204901c0d250308418025910354044460181180744001ca5540b507182c2141031070721405130322045142660130200401a10701107542d6803c284d00449030024988410100700c034408008080b15000b060204080542160024000d4010b5109039802c0052443c030b0040c02e40c40e8421244042d0400c08000e108200c540c1d22032400002c0c15000345807160b072006010340001d052703403030645904a060f4405d205200c040d001840017025094003100191000b51714011004c0d48528110a2140807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 239894451 1250 239893201 239893219
    0x601091202040b060a0c0302060609010501052208030c030406110a0314131502030a1701050a17120403200d0209010b1c0501030539040c050c0708061b03040b0105 71
    0x85480755040107100701030040c0b016032150b020b21401400c031441b00c04103900505c2400041042410448a640c1c1a5a0180d49661030400f803440d42072113010b0f48103401d108141a1101c0018002800c0c006041010b02000103980d03240e181c110020000400000018419004403802c8000070f0707000b0640340ca00d00c8a49080701e441c0c0384803a0f851809101e80b40e10508440350711791080f0f140264048000c296441041d00c2e468124108620000b41c0e0103024015290010a109070611801844a8490000304501c10445020407068030100c041c3d07803ca40d0044031441030703159410040c8084c0009811180c1803da0b4150b001e00259000100d0b0428184964000c0040c00149004200c1c0081c2d91415400702c00390051041e940d6a04d8000c2d40c0c0c81c00d00004010400b044c0c2c1080b1380c0d24050b510460301c84810300c00d1140b2100d030342d03404120007002104171400c1488010000c00742c0b442001e20071a0000d200d00c5010b4401071030030b1080c004141c82c22900311203c40340c0400400001824910405066400075a08069 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 239895701 1250 239894451 239894453
    0x60105130b01050706060b0408010e1c18180f06231512040c0302101e0f0509030a061a03010c0215060103090813061b12080712020d05011401050306010912 68
    0xf0b0078880c1e6140504014142003020030310100c284018012a03d0b90700c003c1000c0f03004028226151680d9915a03143e00c8403040803111100d2064140b0344003800c0201e0070783e80c05641d8910800c0c83d56003a030310245055803140d81d0f0800010151103071340000c2c48149120080e003543d01c1c1c2d4011017842d01110491060300303071000340180b800c1c105e800d0300c0301040030800410490420b8246004c0010b19488101d20401c821001201641c1c803980e600e10003582c800c0054007400401a00540b40d1012030402641004400e0050103520f03a010000c00d84031501950300042c400c0a0303200c100c081040452030f0207000341c0c18085a00b070015800a2502e8034281038020700d03a5075440d82c0340120301402d0001e0002d015103601060f0b19124190103030600048403081c2d1100421140800d810b035150700020700c4040e040340c80c5c103514034404a00901d05203a008200d480d0540203c071702280040100d070441119242c01d9039440d401441440300f5106604542c81e07003420800d0030351826500007024400e00e0700803810418500c2d101d8078 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 239896951 1250 239895701 239895707
    0xb0a06091419090207081c020f03010e060102100504060e16050604030b0a06051f0f0801140d1110020c03150103240b030601060e18092505030703081b060105130b01 72
    0x10003030003c1e04415075030380800c0c0c10481d01c0d64000d00d001c64944140c4c10303006948041680308952800c848541554190fa01c2d02c1624103c5030300c0207284a0550142003da100c1c0b01e140d0340728a0b84503511801c400079035038529644481ca4500341808040110b841d05e0414011940c0703c0d000e8504880d40030320020190386d5900d0220014101e5075000d241c0207000306140e2024408031804003034079a8819681d80311103ca00c02000c441f100b5080c8294440c81e00300c035458103400e051698124205034007901000090019240119030208680084000141c01c0b14079694020b01c2d0500c071301100700e40c80000a24113541192100b06240d81442d240340341c80f48000708900d090340080d4204890f8141c0c010103842c000e603035505025004210780b40700740e4895040b40c0803880c0c1d69015580564020340c2d01100812080541044548004102060a66402045440c0011165020081c60000c0c1d0b100d0b1611585540003038400d0000700703000521018844d00148014402a02e0728548015450944100420030702d02020042e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 239898201 1250 239896951 239896999
    0x8150f330a050301081510030f030203071505100803090906010804030212071a070318030f09030b09030a020114090c010509060d1404030906031103060f041407030b0a060914 76
    0x100c55200004915266400d810901550407140d03400142d90750204008801801100200d51600041112000a01c0804c06552005ca01e0511a00441e031038081141c031440742641640980c0d008071902c84080280c1342880b000190000c0401200235410500e41c04000b940e055001024603042004403000241414402c100c00c03001c0c0004403010b69950b10311810b000d035111652070380d003507403641500003c1049903100c0c5c4a14040111284882d8914403055503085400070040a40c403000c102c032041d000302c0440c031400211401034212100a41c2d03103041c1c20b240a07007034800890003400400000010008100e00114840e11021024a05181d54000c80d1001170524000d59072000200c9281140012480507800c58050142d0b000742c43e0020490743e580300c12025540d0401e41c01c00b40030302c10300c0410a030b401d100f000074612240080010802200448030365040d00703070031102c503070000762140004030760343c20500c1012016109a00e804004070742030a05001c800b80c42c6e1701003070b4003442c004120202004000405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 239899451 1250 239898201 239898289
    0xa020304020a0b0c0c090f010e1605090a0602010608010501090506030304031101050f0c010b0108060406140418052d030301060516030c051605041a0d030c0f05030a08150f 75
    0x2200d854040a083c3c4a030b60303078280d0317010034001d0000201045c84812680035540c101c2d00c180207240c8656480050400c8182150110b8400b80081800944203e5070750428603009030080b5400000d19620f003845403801d40e801a40440380c100e02e0700c0113020b00b40e1408011242070b29000080c20401507201c10049506100e406c83c147c04075080031558841d0100306400042e1251400d9079101000c0d2289010001140d010b84140311584803441c0b00b0702c0240c180b41c1c1025406141b14010341c80100680c1d114a401c00c040220000255a03401826000d10144d1220054110a06234005c0d401c0d0340c1400c40c01f0700107115500c0c034621000788421209040601c945203409030164400243c600e10710f6241c03888281c00465010340c0344941e003401401410046030144001242ca40205446c02d9500c42e0345065800b0300e190502562481450704820000c10410001002820442e6840b01e0300d03854840f14404081a40e1001c2038425403031a002921684c0d207000740841181549a010b800700f13062440406000c19840c08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 239900701 1250 239899451 239899469
    0x15100501140a090e0f0f0a050708180a05060903090a0605040b030105010509040b030a05010618020909070f17130210020c0922021203030703141b0307030e0f0f0f0a0b0a020304020a 79
    0x1080001c11440010028051b84264100c103c858403a12500030a45000302d03a0034001070a001d00041c2c0c3d16102205100014100f50240d403d640100d48460381403000c111141460b9034030000740030886041603860380008210b20724040341464203207039030380c1c80611041c03040d00e042040100c2c03841309995490740642a1801e0040c00c4501c05a035038940640602a54458110185c1481c51011a164028004c40c1d8030854018110241542e56440998851980c038014100b0040c007080d011b4613150216440d540510714201c880d1454440c2031042028400e1035145800864000303280c41da559482d0100c03c683c120840c3c102c1c1d42d24080c1c902090300b441d80b00c01c02d07004e0340c05100d40184040301e50740400218000c0310300d80d405001904039018091074001c0260741b14074848002440703400304041180044c6400c42100e2a022413482c6100d00b58038644080080c004900340c0000849a1803001c0030000080886105409402881466262070f48482c2c0000c02891710190004000350031961012035007000b4001303140e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 239901951 1250 239900701 239900729
    0x26180a060606020d050421050102090d030309020a171b060d0c0503041509020901060e1917151303260c04030b0c12040201030e070506030915100501140a09 68
    0x10800c40003030320881c0300c0c1902500980010f0b039121403080f000c80c3c0546054481c0d4128004516035032188114100790203981955003402041419074901014a12480c040d0341d010868a00500411034013410f681d100b072012103a1000107850800002c174106180750b0226060043c03615018011600760b2003241d02c002c40c05460300c203c4840c1d064020010310302450040201d082c0c040000041e038000c68008600181d03000310034100402c5850706c40d90b0510b071917000140040980d000c410400810301da035170303030054410041c0d413010488411030100080040c690181c006107695003442a205204415000000b42c2040038880700c04c0940e070481c11000b024020900045815894640210140c0b9003184c0004c881d244c0c06040071401120611050710ba40c00c20303c03048600790352516030065000340310a004c40569070107486400112070340e903100a1403007040c41c0f8000d0503000007024000405a03200400c0300c451a08444004e08c03490340d001c0a00000001c3c2450250f80e10740c0360480544040c00c41d0f0340310710440c40b050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 239903201 1250 239901951 239901953
    0x71e0f02030607090e01081b1507050a0c14031605120114010e040507080f03090904020d170d0b01180e07110a05010920180711030c07060e0126180a 65
    0x82c144811034603203403032510170750741c840720825125038044441d60031400d0300e00a05001458840030240f510990b42c030799245000200e03941c8d1030510100110650760002c2c0c00f0010020a0180d00a410b10710304124040c0c100343d0381400c01c0d04030030b005a0103418015034400884540341314095005540c1c80000c049009600d607501c8482496010003210220b8590240c2000018440350024a003441240c10f100a10309200342402400340182000b0403d070f901c550421035030f83c00f007202c3e5403511001003103800701703e42d4a8601440107001d4800528000e070403c001650100000703104940c85034142e4400281a400b80e071600c640480d06901c45c400c01201501074081c03050304110341503000902c400c0c496001c403080d421082c080c0004c0f138505d444900390045d80180442c000910405d4074207900c1700362070074100e0380c10580d68034813031540d00013181140751a4000c080a102298101104054800d424030b4404090f071000d20140071518407440158040c54004804035805c400b000389028400c204280c101c60103241d0f0303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 239904451 1250 239903201 239903207
    0xa050c03060d03050913053105152e1403070602030301050f1927020c251a03061509030a080307260f0601030507170a060b03010e04110105071e0f02030607 68
    0xd8110360480000441c42d2314941e92100c000d400340203504400034140044210030800b164002c01040030380d49400f800e0705002130455405a100f80080300201c0a44405c0c01c0c4070a4400c001c180d40c0c10706111b640031041c00c0005950000450741540c500b0343d500030b608684003003c90310400700c0410200001c150060081004041e03600c4490651514039240e5a111400741114130807441050003011072500031801001c036000300901214601d446c0d01e04d007601959911103c86078440c40081071101240700020520205140c89060442413a45030319a0501d8181c0c100000303036480883d42001418010003100181409000344804821508603404950107901c41c14520303440c012044490380002040180410b01a51092150510402d4143c030361018200ca4100b401401c05c000034100d446160b20f403007000c1402042c800255000303201800c040800f5080900d002000e07034a054160504004080c080080441c500000c4a030050f0015010f070f40c004551030400a8a100d01100080d4051151105104501364 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 239905701 1250 239904451 239904481
    0x7030f0302151b070f05070603060906050406060e2e0503091902091311030307030509090a020a0e040f2904200d02090607050109030302030a050c03060d0305091305 72
    0x8800d500b40c604500080001e81e0900100b50f924210040510003030001010185000303042090160040503510741007541c80300e1404c2515000080002d03143d01d4100113407076680c000c60025080c00c840901c425402c0c140f00808115504465622a0080f20761100112003043c003803000800c0c0c008410010b031a4414806041c40c1d009461a114922641c49450340c4070f081500b084c090a0b0303008127100403d40701c0c02d40300c01b03540311807020960341070320411000209030341c080005001151081e200e01d41c07181c2415082002400c0c0c014100c40c2001d00400800c1481030780130410704d078100401c40d80000c032804003001400050500700d015840c03071184003c46610446400114a54229044405000f1908880707030700c40c18055a00b8505249907800e0241140740401c6030040d00d042c8101418107407d004403510740384d0035100e00600613000b00360f00005100b4401e03524041c003940700c4c4ca007000e042e295040c44401700b000da564000000c1d003003180209821000d603070f44a40b550101c80d800030050126041c040380b2480110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 239906951 1250 239905701 239905703
    0x120106080c011e02060606030c0d091208010819060c050405090a1a040b010c060902030c15040e010e0c071502370201090209041b0302060a1d030115030f060b0307030f 73
    0x100a14084a03e40280005211294010b94050500c41d2122010700c1415040036103941d0807a0000d000e814020b05103442603000c0c807805003c0582c082e60b040c0b200503040480681111a035900500c041000d519030b00b82c0002d81451303102900003010607400e00125268080c6070400c0b54048402e030284885c0c811550049904003200d120b01c0c442040c80350040100311103800e10950b0104c0c00145d0b0101c00f01d5800d0744030401041c0060107540701545120000340815401081840c0342c2000800c1c1880b1060a1002c4540540031204400310039040c000700c0f040250040c811700506407221405004980300458041c1c50110520300400d1900394905465032000540155020446840c20308507004c415205000d0030b4034098001e401d9441c00d4a0b65140c1148512940300c002c524144a40310000040c0c84410003011290bc1680e2050800e03000009458580c0f83c064070240d200b0383c1030030720103100c8546264507082229030100d50510132490600d0b080c80544944200b442e810b00540400000b886215182c1da0612 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 239908201 1250 239906951 239906957
    0x19030c02210724141909021302071a01080d09290307051b1203010b0c0703051005150924030a080f040812030103050a020d0302010b0a080f1614040506120106080c01 72
    0x180c20480b9100d0741c0a04d00302c8140240550601c1282c2c000c1603168040c6110b9400603111000f004005041403007680d12a46046500200300a81c00014851001f443e902525201024000001801e54010050802405880580f014032a5442d5084407481400c03202c54211300b04194a9140c060000392590300100b14610318002d5084034940100808149090b940c00350b404203905503400c0000c408075503000380030340090b14481c031070300800070036420496503407071506495011500745480c45940c08080303488642a4061600354081c41800e04541c14091b020f0031001c0c884906400c03800c400070740b13003030241c80000c0d2200c0c1c8000f900c81100e103000e034020002e4a6032141101c2c2c46080846850020344000d11001d85a50065400c505c0140303080c0034403200c013a0081c800802d0300504c4400052035010300354012200e03070f40640c4c520360183c00c0500c0325403a407003511000358800f64a001d90303201488120030304082c812a51640051803e0740c4031619038065400740c5000b040306540350340000e940c41d1074840046000c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 239909451 1250 239908201 239908211
    0xc020f07140607030f17011412191e0b1009050f0c1903060b0d09020109080c180915010e0609060409151d1219030c02210724 55
    0x1070154070451001c201400540780524144480d1400c4031903680e9200c10f4000c010b42c4800300c49850325454003a03406000001c00c80480300f404c400c100100b070a4010700748006a0441401c244221080d91314020070207410064041850074007241003020301200b4100100b02801e41c0d8280038207a201304206000303554445000b00519264850140321682c07044540402400041203810a42600c0c42080d07071a016150502244c042d032103841e01d280a4000941c0d40c0b10042e035a109a20030741d80d2141001000b00a204060038941f041c2a01184800d984050b81c03000c03042104010030703550501001490f22011401c248480156128200704840c0d210540b0001e21400e000c0002c036141d840c091144000c410382c01395a0b10065080441400003410b1607142148410001092056421000703200741030341c150110896950310400d2080031708000101c035040314205440d1445680311aa00000c091444002c42c40c034035622049000038014081c0314881c130003000e5a20341111441641a11703080c4400c0a540c0a80030b0103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 239910701 1250 239909451 239909459
    0x3090c0a0506030109230411011403072705100504230d03080a060306060f091401030b0628060305010806060405040b0a09050c0409080304030801120206030403080601020a060c020f07 80
    0x300300280c0c05040ea11810820040110b00940d62081005464545113000d140d226466441182e0300105c8040d11716812581d8071300015a07000f0215003a41c82150b41d4a41142004c14004186e640c04018656180e08844424140c502031901e900c401000c004000c904000e044110040032070b0050320072800911940506043c407400100b8860340108170103020481a540580c40840c0c50311005400301c81c074140d84d82d030701101080d554020080a811002c1d20080c22600d811541e9007140c40c1040d1011051504c00b00500008001c4000260480005c6841d40c10900c2c480020011007054a82c1c0c41d003c03403503034840000310581c054202a04842d4044151446540d0320313400d106c15a00100d400420481a103030029084610550107040c0071801340d8212103260880d8400b03d000c0b220030400603a0700f120007008110406070700403042da014002903000d1202a03030700d80d80880c4e80ad000240004060003281000104164820040d004e01c03540c002000b803022003418400692504000c06000c9094012058041 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 239911951 1250 239910701 239910709
    0x1c060f0605090703180204021809070503090d08010803040b071b08010b04050117060610051c05010509060d0f02090406020708070614070c030c14150a050618010305030307081009020d0203090c 84
    0x180300440d801d000300c5d601c0c070745540c20000294460540711200401c98010581c0329107800070681d10481c22038442e940c2d203042c51444589820f01c0d09000c0010000c10a0040c400c1c2386000c401e440881d01c0c180300c20383e02d070035241ca40751881d480c2041034603482ca1802200010381d24030540100c09958002c1d030f410840c40c1d80310b182413402c01c1c042040404d2103078800b00c00306140d810400707880c05a02e10146071a030300b4011440540c070b00c80c41c51000c11440c2039889400503c040d2501c003071071580102e4100c410020018141c1e43c0c1c40c0200074000c83c043d10a08071000058140142074044a0b003c942c070001c496179880051600c940140842440654403281c0c0030002400207010319140941140c2544401d06401202c2c0c0d100d8403800103050092034140a4110705807000d24003080094001d054420003c105403600c2c4007444007528803826400c100030840001000400d601004980e0400305a29083c002942d0740442036442ea0403a5025030340d50f510004026840107025406540181c420038191890b0f0551340c4208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 239913201 1250 239911951 239911961
    0x30608100c0813080909150d080705010501080609060c0c03040308070b040303060603151214010c0c050f120409020304030924090f0302010207121a10031b141c060f0605090703 77
    0x1c04025040140401615104442c603a01244030724198441480d0314001c41d002c0100400304275070044020980108011086c0101c5001d000c2030001030030645030402c00076544130b40207007a451a101c000034080b42d8100d0b01f4000c4a01460700700701c0c0560f9034000e0b407070401d007000422241580002d03c0c0001c0885c40324031900646008103007404000002c3c6003002407600d620000203000b12411240011280c0c2132000a005449a6040a44580321601001d0a00605090000380c045416804c504450146006848183c0b8240e8441c5103005071242d9540ca826500815030760080044901820918010141003c1c07034a460084103076686408641d440241191043c010f000090250700000c006001c40d01488410710300c1079000c1c5d400c01c1d2310300c042c1022400034040156031001d9848107520050003880581e200c070300c004400e19242d00007864a4807061103d8005030444280c483d2042a140c420030032882d028985c1095040f01d41040501100a1110b0003404103200d21400740c501900050b020324040d03c14 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 239914451 1250 239913201 239913203
    0x8010e070501020318031e0109030f2109021206100f0b070503041509090207050d0e0105030f060f1201061e05090403320a0f031803051603030608100c0813 68
    0x1035003005d018941001742c110104100d1500342c8200c3c880b0302c5074103070304660f2000340d450070034000030348003001d07050080014840f4040e030010301962408025840c126043d40c0c8611502e04280002c00d0741d45880019045c048901e0b111803103204810a1100303001c0340c42c541d03408440c000e00101103040da40e20307001c170214010414081e001d40c000707010401180c1c020018219800c1c8442c034103080000c0d21061004101d800080c1300340ea941d40882419002c4a4209107040c8113000b09003843c1d130641c54900d040410924008081d940100048950340b40740b40c58000c410824043c00030020300c042a00c4029001d017074402c10a040c104900140c1c3d00113910705006049171300554042c0d407201800c0c0442c141e03050307401c080315498100d4100107103c481036100c0254080c000d210f580d42e80b030300190341c0c62050007020340700145901d0090060440141c3c002907040301c2280c0011810001c1003501f20201c1c102a001002d00d680610100d024140740020100070640c00b4115180050b107400ca055101c1d044840792021140704 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 239915701 1250 239914451 239914453
    0x2130b0306011e033005030603010501050109080303240d0605091204061b0203030f030a020319060b180a0e01060903030f090509070c0c08010c0c05010b1e0909151008010e07050102 79
    0x1000340040307442100406448000100403003420307031782011140c1103000002c07450740c00a41d010050004528080c01703600e005110034600814481e040c52200390316480060106204031605c468100e85500303800361035034600342000340101542049410218054881140d140100c1e001e540c03009120700c0d01c2d00c1c090b01c05aa00c540d882d031030070140d500d6510408041290301130ba40f5100a02c1400c5005032442d0003548a4000108090389a080110746003030841341c0d0600c1260400d05100003400004100c5050344d845211442400480b6030450021a90310384031600544014004500080b940740c0e00151904200c0388070b6074403450031401101c401c490b01302140c0125540011b59001251903240f085211942d4240200c0e41008026074544240e0708483c0710120080101d1243c90307001c0180b00081c0b040b100384d05070988491011200740341c260200114540c4540b0b01c542c0c000070104017164820441090280545144003034107003012019025683e40910510340c0039030070482110359507000440c44c0c3e0111501a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 239916951 1250 239915701 239915759
    0x12030409060b070b010608040c03020d150b0d08031b0403020904050c100207050a15170a1509020c030301030b09070e131119150522060806010525060902130b030601 72
    0x1b10044410540c023900903120f589400380040050b071358105c03000c03454602c0340108000c0420000c5a40d4107a0304051001c034416001c5e505898049102e440880f54000c5c2d41c030040220904201003440f455001705e07080a50005140c0080004002c400607407e019948201d0b00c401c0f50b55042c680490b62502c03a4002c1c50341120450b84100b00b52030207420f524030b5a250b06c0c2025100d2142126642c02c85000c203c542032007950329007822405003400b0311a0700c406001d00c00c03800d51900d942d01140c1a034a203c184001030400e035442000910045003882802c000d0110240a05014188443c1e0000040200039042d0f90141400d80d00604030b191000703526200410002d44403002920307000ba46e011195002a00700709200f010070050024150122000203440c0401e400c40f46014203020004004650040c502414000100700d001c140240c01c1c0307080c4c4040c21a50b0810703020b41c00d05240407406009148002908040458555984403141e03400c4500000d6046d01181c20702d0f0782e2550110070b110506004014008106 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 239918201 1250 239916951 239916959
    0x30114040c03060b010c0f12181a070606080708010c17090a020f012601090c020115090c020a0803010608190515010c1103030403120311090a06050a09030212030409060b070b01 77
    0x143d04201301110301410054040300c16a2030b202c0550b0314152088480c00c01000d100c2107850b0700301098140e0411490082c41850303003000808050300d20781d00f0003e400d031a40400c0302c0d420490030b0380140b409000500281c0c0d5590359100f400314061b11419400c0c002141300d0f080e03083d4403400d841e60b2040c030807000c40f00100030b4a01d81d6000c0c003c4009840001c981041840f01c40d0b40c891019281e122410310748000c1540035907601d00445030381100e40c041c1080007164104070050f400c030414015604145c03003448000190000460005070b25160000c3d40040803100d01100010302103030006401c600c10383c0c880c2903447d01d400d001d201800481e9000c41c2c589214462650045129512a2815a8501388224541911707603400307400007484d54101d5441120000880b4038007003031541d0f0600441402402040c0001d00708082440001c40040040c01500200100814810817203403242c9010300c000c40e00a80056880c8524a08480d1254040d0003900c109508043c1c001503000300d22821aa0030341e800440c078170b046900b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 239919451 1250 239918201 239918213
    0x50415080c18040602090f060a050c0c06040e010302060d0906060e09010c030509120f07053304030906030515090403020102180d020a21051504031707080406050702011e0209030114040c03 82
    0xc00c6c1c003456000f1100101000040d04d414000382107a1400d502c402e03480300a10600356182c0b000714204175018000a000800c0703550860001e080c10350340c0c104e5850342c40d07440c0e2920340401043c10039005041d090030b01e20700169061031001420f0250718104000c5c80782c0340d14031f0780542c107583c003d0310710f0711a5601241e1190094149071020301039100321301800d285420344130340340c65140c41e591107450707444c9941c0a034062180b01d0f4002c50044415641c0240d503400c0c1d2800c0d881c050100d5003280f081c0780626886000150f4481882c1c5604840002c0c000c2401d400c6040604009000707410450050610f200440151112031400c0c0c0150f000741640285820040c5041040702d41d080311111032110011000001e484e0001070052041d201d480c0d401143c0b01026250500303004103540d00014991030b1000d410b0041c80141a031090905601136000140800d00c1c2c0c0755140704a00411103229407074510302c03181c00e41d00c009400340e8004150100e000c80090205c0c11407401401e018240a03100140a65030044c410400914 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 239920701 1250 239919451 239919457
    0x30816090915180f0b190303030b040902180117010b060702060d0b0a0306020d06060f02030324060c0703060501060f050a110102040e0f060907030213061107050415080c18040602 78
    0x40810000035802e56468041407003001014011090039202d9440ca07400455521541c03101410841e60b85501c070703c01c00c20886c1981c205001c050f0405444030310600407034803580c0003402d106501030010780c868004105505410308082c06039086801d081c00030711030805414000d403411284000c200d13500e03245983d030820000d540422402c000707441d120030211903190f99a41010000318060b01e00035949200051984003161450b800000a001503103400203482c07540002546c0e80508010f0300120703006e110b80040c0c03108030261741400c2c1e48400009090820400007240741d0003100e00c50310003803040f662152801d42e00d0031419461000065814404c54003c1da11401030502000c1c2c808000500e0b083d101e03414000a450103c0303203505c20035100018004a820040c0c03006a011001d4074085003040c90408000200080900c40c1c00704012203ca804040c0600c14880d802c02054000c10400080100d46500c0c0461692889020501c2c00b4030100c55201d81849000303008414203180c20940e05541d42e540c1d11000b50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 239921951 1250 239920701 239920721
    0xc01091a070f140609120a0e010305100e0703021c0902060f030709050402030115120902090a020a11030304030903030f0206060102075a050f01030203060d060501120308160909 77
    0x4110692182c000c19000d56400102e01c0c0c0c0340021388a2444c3c414155864401642004466604100b00c10440c0e26031041c0102c0290400b46008074060712001e1120b2441842600000c10a2841c20103100140c0c0c3c1642c010003d403c201c2156107002c1619501d468116001e602d0060340140d01040520640401040210342c400c089051045040d0f03101e06c0414102c0e0801d8014541e00b0740301c0b2050305c1d0540d1b000346103000c006801c24400d00c030f0301302c1c03030750105002840c0078045c2071416801040d08420180a2040303094405012001c030b03a2646090700300104218060f101c140d0120f0401195002034030320100c1c007240f11316010380060141c1c5141010802a036403550407511801ca20008001c00201146502d9100304a0b08956000c0d000c81c422000f581c2e00c1030141c01c0c0b11214031010344100680d0b103890343c0c92045202d090170300507229604e003000319981c40307418080104105e01c1c01002040011178000295503180c0260f44820f1956a03a0400740344c030403041d195000201e00f42d8081040340002640251681c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 239923201 1250 239921951 239921963
    0x1207120b07090f260d02070b0901110a060917070b0f0604181a0c0403050703020d030c1401020711040c08061e040c02100b01030902010507081e0a020a02030c01091a07 73
    0x141d940e07514210800c01e00d401c00c014880f20313802440b2250100142d40414290100c0181a5200b1400390180d6507000030700c1040340001c030100b035500c0c030381c2e0042c40203294480712902640c0709140b0618100c0010441134604461500d80610380a070041100303429106d003160b01c5920301180303807503c506000b84108006c08080d071040d1210ba076040340d031400507400d64045204030501502c0a407804102840810010003c03030880400f4081040840c0300040e502040300d170150b452556000c1141070440c2d46c01d1143c070300601901c002e058030013840c020550003041010701a9200200200490007042f082d0307071038a012100040d040b280803600a02d401e000401e1500725191003c45100c0152020500303403407260204001681000c074108480c0700060140740909802440c0810003a202c540c0042d280d0f001d9404003601d01600442c0c1a00000203030308030104590020a01c86842d84119280203645a00140040b0302a00800340d094040b94040d4521805488611004610b90490120680c0c04c030340042c0015100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 239924451 1250 239923201 239923217
    0x1503071b110604080a1505060109050103110c01020a050a02060a02031003060e0c030f010605010905090f041403091c060b0a0b0406050a05090a080105060315090613080702090705091207120b07 84
    0x142e654100040c001441040d002e800d41d61060300382600c0d015603240704512402c0c10641080707038a0303031b2018175182590000d0070000f86a15880402c0c601e68000c944d80d03070b2a00e40c0300080203c600c0343c2007005840c0d110016804c99445640c0c070075000f02603020a8031032801c080707076a410900010711260070410a4100070f000311258468420000b81c03400c02c9128a1030096591000700b80081e5a0104002c1d0251605556070600d508110110b114400c0b0010406841c42805401840702050180304458807103d006200700d898084c945100e002d4001100c078203e510905c0d040344003085040480030ba800f11942c0703850b903d0910b4548a010303219035000d002c80004115041000030701c0c590740c00c0d0380ea401404620000003664582101414030b844202d4010035494a588010850101d000290040c2c1c00090440100c810380914500b01000e4007401100a50003aa40c004008556070b00c5400341c46119001ca40c510300640701140710944407003290007400c0c42403030300030047d0b80440c00040d6070640085680c500b40e20 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 239925701 1250 239924451 239924483
    0x51b0c0d0222060b03090c010905100309020d14060a05250e0f06040305030a11061312140304140601140f0907050405090a0c02103b120304021503071b 66
    0x41151001c1d084a0304e622404414045c0da01e0080205081d07035074003820081c81040c20900010b070342c80100702c03c4800b0140c07580084011074461041020309568030442c00700d85410001c01013a2984401c0794481ca0b0985403400040c1030089001003004210208000c500800c20b84000459800212030f4000b600100c103034a00040c7c0c2d4490030000c00040d8003c070081e41d00c41c4c5401c80003c140c4087c042c200345003584268244158003d07402080341050f83e0103002c0759142048104141c41185051031504207405001c020081807003800805001e818a0714000d0311000c4ea00c400d08403803c800318410450f004600b07040c0d03c2c41182040c002150300940c0506105081c6691080042d1648204a800c040d015031100891401c442e010042c080000b52198418812000388100c0401000b002001e03103421090f684014448030a00041303101380f800b8254040e11412a403a255821407944191400c07406080c03425000d4501401c0901a20300640d907507521441c1c02030340407804800114100030241c4400291401d804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 239926951 1250 239925701 239925769
    0x30f02010204120609060b01180b0a021504051b01020610031103031b03040609210b15100e0a1509060c05030d06140f030109020609040e031306051b0c0d02 68
    0x140c2e46131003108041600301c85807402d5415038910140042c1485889140c4080400161418409540c02403170020380300e089640c4100d01e8000340e0301c0300440428000091000740400445c04a042d245111018617a40c900e0800481c2e44082c01c550b541c0f000d13510b500050000801c2e600000a02250042c222401c0c044a546c07000072039041c14002c29002c2d440003404100d01070304054504010500d041c0e0791400641c028030409600c0081c0c4000030160841900001d00b1520640504a644d41c00039000602024807103601504220520105510580440da0002120145181c10703642003000c80d60340c0e040440c03500b0003d841600081c0000c5466000601183d020b0400c40c1c498a0020007070380000740d480102400500c10940d1803151182e0199040940c4040561140b104503103110000755400940420040400c07801e5018108010340c03500041c480010304180d100018114a603480780052008000100c6010340d205140600e19400c10521402c82e13004d4a0905031090140b000f2141324120500680191 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 239928057 1106 239926951 239926979
    0xa08071e03112206030506010f0503010e030d09030c2a05011b1b050306130209060a1a030c0d0219110f1b0a030506330607030f02010204 60
    0x5465451450315030b400809aa440c0800003141c17030380381c4070362265000c0c42030301c041d1070001c503001c01c1c185010b20400d45035000f4500203510700386c0400312200290034801d5051b014003c0f0030070a80082145007145460354803065078141d20310880040000c800d01c1c03064105504018094084c090240c030005205440c1e0340c0c000c0e814410810680140012011150304126018014074050101010007640c41035440c900c21034500305143d4440060000905a80c0f1039000020b48614103034150340034081c001c58002a0303218055240c040319400d24020b80e0302419400000d54010441804203e1340724221f40000b042ca000904940c841015046036500400c05045070122b0844c80c00115503a50305404000070740d400b00030f44070285020080c0190702d0b401c182c03041002400049402119668003091940325100080143e8200b0066807802c8400c0c07000fa45004056650130000800e015098005e1 = true := by decide +kernel

theorem cover : BRFrame.Cov 239748201 239928057 := by
  have h0 := BRFrame.cov_init 239748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 239748201 ≤ n) (h2 : n < 239928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
