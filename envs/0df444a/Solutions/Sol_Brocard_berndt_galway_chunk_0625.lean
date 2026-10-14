-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0625
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:47:27.761545+00:00
-- url     : https://prove2.me/submissions/86a41062-d72b-493a-be3b-1b665028b434

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 112230215 ≤ n < 112410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 112231465 1250 112230215 112230233
    0x31003020f03011a0409020301330e0108070521010507020f070b130b13090e0706030506030f06042012010501030b0c130b0f0d090b04030e040c0e04050901110a03060f050a0e04 77
    0x40e840900009181c100c190384140350498035003e01101202b110f0151a03900402c002c1800041c0112041d11035254101007003182c07121044d01400f0300500c1142d0b9292030500c1c0000600e40c40c9004200200712906200354000e4840c43c80401d0761000f0312540e035001882c1d00c0f401c0c044071103040f40e80e100510424103220806040380c0c41400028000300c0b2000c00462115100c1c41542c418600003802804518544103029007a039a008200d1ba1082e042600201070189001c50140d600542c0000d807684142d001d55005804103542070300c0240c003c0100c0c2c074900f402c0003055100e43d042e240160240b102aaa80c008a03099034404c0410690303980c0c11070981040444a890090088034111b140380f01e040a200058240c100e40102009666208085081c0018590400fa84a010400c1601d060084515108014000a5034510580d001d2aa2040080d281080a51001c08450341001c0c010380c0d21202804010080c1401e409018150a4684c07800249840c0014810040f5900720f0700d41c8145664980b610b00c0a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 112232715 1250 112231465 112231481
    0x2030f090105041a071704180e0f0706030e0606090408042102090c090109050603150d02060c06010612050703150b030703061e08011a0d1b0b031003020f03011a04 71
    0x40c0070b000d0002146619074250062424064002d0a540f00d48003070038036404d4200011203211148804010a0081c0480c0b0554200240b0042074007040c01044d041506140501c040362212050042d44008590554144c005901e103d20000c00c4031140d80303410f010880c40302400d6034001d1041d01c007088100300012507819080000312107085003416980b41600414900c04d01240d12921b80e10000840b80301c0782d030300012020090070741a40c045041d4a04a240603000090b0100342a00c9080340d10400c404542e10389044425085181040d61410f503924000980001c0240d005600c4050420000400c024402e2140140c03d0003100d208001c8980b4011183d41150b00107042e007410592075540200f6070310042d45140e06201d0401003d8080e062900030600d08640481424913802e241d8040b50007d03e5858004242c450707a04100080c42c816441014890016400d03440f40c00030500c040100700071180141c64030300882c1d00a03500340d010410308208040c22105070280c00d0078240040e14090505090560042e05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 112233965 1250 112232715 112232717
    0x7200f10031b11190c0b070501060b070311070b070507030b220302160b0309063112090803030417030a0f020c070f0803040305070b03040f210f0504050102030f0901 72
    0x41c01e402200c81c001800504004100081010107100d1448448204401345005000c200445410f01907070b901c11480511510990100d014082031880501400390b01c000003d0040d1001607030f0300c040525001d080004000d20095160180e40300010300700850208803030140d94041301900196040d640d54602c1004003801811030325446850300800a0710810900e10000e000b07400601d03444e41c4250f0000c0b07003041c4a400107a40030109100f442070400d03002820a4012010f51501d0080241c08203032140c504400318045503800c4010017031202444030104401c1c00104480d9500c00c402500d4107103a50362031100383c030700070001c1d000381b65051140e0404001940c1c1142100402049208003000341c4000c2e604094110a601d8005140802001c03041c180f00c4c2009220b00e4020310b0600e440d40c0c582a480d588075110f44041000004002820072400c1700c8101300b031550000351202c000c5a151410524551034004c600c001c41c00d10079001ca03240740120203940c1192030503801149004440d121511207a00076451a034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 112235215 1250 112233965 112233971
    0xe061608160506060a03080f030a2904110306031506030c0604060315050d03050409050615040b03040317090d0c1a16020d031b0305040f1707200f1003 66
    0x4000610031001005040001401e51000c52400d0600c5400c1c8500076006a2180d0542041000010b40e880305959131000ca440b81103072a41c1c0c80e405200e014000c00000c511004020902001214440b0a1204602c08040d501044100e8044214192078402580c070b0582c035901108020024144020359694814409402e07200c0300c66180d4007068041c0c00980051008c00c0e21000d024484410965806000304011a03080e819401d103600c021b001d174410b90195a09541d102c40c0001c409031501c440d444d002c003000032041c55542d95651080560b54005070f03000c500142c02078008800c101884240207008184a002500c0045ca035000285c440086000c0100ca00400402c06000300000750581c55101d0b9035900c0c4256500307030216030700900b03211a15001c0401d152900440d0b41040700480c161001070980f90500084c0c2d81c86604004d43c00c4680040014030080c0390100c0441c8000d00d50010f041003a2240140142200e80e4181e04003c400c0310b00c00181c0c009502d000210310601c0c1920420f21912401d007000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 112236465 1250 112235215 112235257
    0x6040c030e06090a0b0c030130050712030f0c080a0c03030902060408150a050c0412050c030d020304060e04050103080a0c02060408011b080114012115090603020315070e06 75
    0x1d080000450702070f603c903088102d08400748412403651a070300800c0c10040c0391456041c00200f91500c046203540080c2c9144994030155001100c200308603945411401f252030075941c030038030a41071210440c000c40001d01c0048007600890f004030215440f00750b200300a241483c480c050201c86a0624034000d9080645031022a0050780f50b540c0208060640310001e0001c810681000c15400100507200018040c42d100402004c09015030a580030382c1d0300410b08105181c00c0703013810b52420440402559150084038800480d0341d0700080280212426500c55950f0648150200800c42c0c009201c050110b0344100328001c400ba100e0407114000718802405581055142d104890846007000103402c51a100e15441d0418107400240302801040c01041600801d400c54000916400031000a0880300d4420541101c03101001e4100000200034085c455000580d5900e2600207030041c0d1000f48e010b40507100c03e00c22072490302c505c1c140c0f04011903200e0340c3d034a807001c0c410702242e40d10880d0b1030000c6400350092 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 112237715 1250 112236465 112236491
    0xa0207080310030b010611030d05060105070b0709180c08040f0206041206090204050a020306031b0406150e150307082a0408010203060a06030608070b130503060408070309140906040c03 81
    0x70310300480382c00800328821820b41c40e0a4100340c4041e0070003020f1041c00d420800000d403000080300c58603c83c020011403651104401a90940a00100107000105040410a84036803040d00401110350000d201c0c82820803c070412003c546a0010940004100c440018007082c09620644000da201429280c235090741c03603910741c0318100300f22421500692140380d00000c1d441e2038040c00360440400703c0c1c03c51079401c0520000f0342d200840e40110f4a00205121100e5045d621039020030002d041d05801d202440309030620060441d814030341c00c144101e81120070740e4030303c5100d0300689108051585a22900341c44640c154420603501c480d0601d4000d48000074a03c203886a5405031001740010000542c072400d00f40c0401c16583c901c2d4000a042500d401401c02121400260410880c1c184c1e00c440f036590200074403100071024440c0c1000c2d80620558041c4001c2108a40080400078061307a5140207294552410742415043c9800036944260030201003484c85c034050780070100365640d60500107075586004003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 112238965 1250 112237715 112237717
    0xb04061d120706080601080f040f050a020a1e15020304050108220602030411100801060302211018020906030115030f060f0906050a08031204020321030a0b0609010c0206030a020708 79
    0x214040041d000501c2c10050380c0e0700b15201a4002500342000d000d0f61a0089a850b58068010400b404458607039070f8403801c0c040140f2500d0f01194001d000c030002c0c01d0f1107002c031101504d0040340302a048948844001a5015103d8076801d2040c1c86038003862902d86070000444002d00c01805086403040e86c07486082020580c0b1070a0b100e1684a1180980c807460b281c10b111103005070340c6100d43e00940010b80402c40303490340700c00308905680881c100143ca0300b050303040c20900300405050003480d0710b05038020302407110342510203070080703840c1010750159098203500150140d004401d1810340010b403c0c001409500e0005540d840e004460b407030000703070280000400300c0650b01c3c0e952107081c90038401c440c00d01101e030780b501581000c0c2c4820b44041180e02e280c1050190790348903843c0030f200c039604cc9002160440d50706101c0302d4038140c80c29140c0c168032504d400c0038904d140d00c143d40c0402414a480c0404016007021420b40362103010503180d005005040341c0a209140d84001c000c200300c03607400c0014800140e0324030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 112240215 1250 112238965 112238989
    0x60f070f080d060305160605070c0e070c0f0506010302040b060412030f270f05010e0303040902090301060e07050a02100c020607211e0c05030c19030b0607060e010b0a0b04061d 77
    0x500103106d045640940040844502d401000400000b040081c0218142c5402101120068500b055040c3e503001e0b011213251031309441c0280210640c00101c4140140011680d05880c0211820420910440104034940c8580d00c500060a0350306182c2c4004a03000d607420b03418a00407403c1904a5080c102c9541c440c2c00d0100101901020411600703125104042906002400d002c3c03c00e00c0c2c2c1020001b00282c1c0d43e000c2c40c030440d401070343c000400c81c03401c0d01c013900000001c000b00c104658035410000c0d4003070003503040f02144900510460301d03402215002809005000c1a00b50082d005648401100f00c0b001480c114460030203201100f4007000c5115903100d0012f013402c2c0e000f0015445458440503034295a041d100032020050184284403070442c01d282121800d03020b12001030981101424154040c0500b082c403a54480ca000c600b01c002e000761034010505031030001000308501c482101c00c2015a040b02d000740e001c804c0d4140420300860780102583c1283c109582d5101030410201000220920041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 112241465 1250 112240215 112240223
    0x150501080a030e0420090301020d02040b030403080c07021e0d1b030b010e06030d050a090819020418030f0e120706020d0212190f0e041b0e060f070f080d0603 69
    0x110740c2100606070310114440030b01108403414800080000801d6010014a041c04c05410500040003030032a0b4013503040b10303c0c0c0f1002c1c460541d161550351807006040c0d001145c00b40e0100d0100d4002480b40ea04c07800481d90700d40c1c0e00511507407590011502d00d074034115110603200e4006075001c400001040004441c2c00e003110310f08800483d110300794034203c2c1a420040e4041507403180944184141654085060704c86540d0074a043c94480420301400c4950740704a03031200c5464041c61342401081828004000e40550094600b84100c101d440c213640c5103041c0800c0041d0009194001c3c0c01c0c04a88201c4984500801c0107004a03640f0b1403421400d410401694421405a4130540e54400d0058041c440b0b501c4541c0010905400c0400c0909400e0a40e00f6103005c00d0204900f0180000d49140522511416044003420401c66540d01a111440741b540c0c900310760b00800e140447d1a9998076000d0119084011300811142c00d00109581d05e40184003a00001c80b91142c0500074984804000c2c89984010b41c05 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 112242715 1250 112241465 112241473
    0x20405011712040509010b030601090e0106030510080303090607050c12120a06170309010f03061511010501120c05040b0105071209140901120b07030204050d0602070c090203101215050108 82
    0x40129024a4010b00558800c500b02c41440100001ea8524000da4112144042d03255566500c13000101c0d132214030740e0040481300b9150000414120740c554230180c801d42d154903000000726102ca0b10644e0324041200c5c4034030150300071400990584d1242d0003030420b40308114102c410900140032414402d4001412019240380c070001000290040d0380100310090807922104e074078103c601c00c003858491055110081c14800c405c1d80046044d44a903011000811910b00c0f424681c0850b200b000f0300700c0c01009851000c1d0741c28000045080100129400c0d4040e40c050000038820f4036120500018107494008503041c00818840e0034041503020400d80c12081ea1907468100e07040c101241c0082e50204c0d0190180180017810042c084035400384078220000c0d8006811107604e07521000c0c200c001c0d21aa4000542050310500400200321050b0050614144241682c0b8001910f8408000803404221042806131034984002c008184808141c0c03a81c0c280900f4038003c80392107050101e801c3e28400c1e400000c039540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 112243965 1250 112242715 112242749
    0x1902100905032106060d020a05070b01060e0109060e0a0620031606051003030804030305101a0a1101020a0e010c050c1507210f0f05090907080f0901090506040609060902040501 77
    0x2d1030f0611540000c03800d003101c0c01d040011400310f000d90071502d00010b030b0018898420a000350192101c01d540f01310358132010342c0c44d014001d00d9506210005800302d00c58501c00301d402405100c4a501081014260b103146625100089518012035100c000400c10080b0010401420600040440982c1b04003040c0c04c01c250351910808a41c0c004203105111070385100203100007a8448602a08290540f40200700e5071640305800001c00c0456008114404460f0142d000401c001d80160040c0140b503180c0421400500001900740e1264802c009c1c00100c3c4034600b50708a40c000d0340741d11100b41c0108100c0d00072401d04000b0a4800e4140c15411410755008220f260403ca0710b60303210303c1c0030300340310280511400000c88040d09614068420000b405170090903811860f10800aa4540c41c200a0141c00c01c0c4c1030400e400f43c071142c01030701c030324a00d002110001102c0f000e05001303078050a80d016004203120794075a00ea0200505024404940b4103807152494005039841c0d010b0b00d40030b4608a481c40030110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 112245215 1250 112243965 112243987
    0x17040e06010f020105090604020120101b021b190b040308190216050f45070914010e03010f050105030c0103061409060303070b0406140a11190210090503 67
    0x20240ca80c0b0086a06100c10070200c800d0104841c3d410aa0a00305850a412000c000030409103c440c4841c5080c4a511408808488140c00800070106d20780280c0510a000300c030700f2620b171000c0c600c1102c00003520355101c01841c14040c0e0016544400302e40c0030900a40c8811180205030700ca81e10a0790000c60200b0305001c00850250f034003502000758002003194406050348625039041510078103105401c0080f8006103512080341d84600c00e403000e00000302003d01014231110350040c040010b14604000400c10245580400c025405101c50741c4a071040140f034051461803005c1e00c1c0304d15904002c00d01c689941c2c40c0c0c030b0900034030000e24000380740442e40390f0402c410302d807070001070742d0759181011b007032132000c20464410498003245840e041e01d1140300e540d95a000300780fa6204003100140441034040401c030a00c180c03948080c5a641d03085502d0201912600000e10943c1e60040200005000420444015428042950301c00280e0385c01030714101503200204c1800c4800c2c0500c103450780d8200084008890b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 112246465 1250 112245215 112245227
    0x9010c0b06040e0a050d0f110c040c09090906150603024006020a0510021303170405180702010501050910050d020a09110d06050d0b04030f14030103110301050603010c0f0c17040e0601 80
    0x180c47d4a28111155440c448400382c0e41d0b4902c010074030f0045070307170358010820507101c0c0d03d01901400d4a400c051000301d405140c18401044c0c6030b2003a0340c101000c9107000c110079120307001b103031401145140f0380c0304a1400011005030070101007180c241c0c8190000721002030213060602950042581350082d111880003030800d182000500c0d0380c401c141c1441044440f0003400c40140a005032034000128820b00402d2000154440c4030300e0300130381d03070200745442c030440700d104801c400520641c90399000b030040d80d98801c10700428400c281d604001c0202407407801d1010f0305009503034101c020300041c42a0707003503035440302c0030381c100e9000b44860704012100150058000c031450045070300601c415107450040300756075190040441c0d0041c1008003005280b03140c24200a201d86041c8460000c40542e07645d59581d2860000e25000141006600950a100014100e458180b041d014a030041c0d8841c45044a072030002203401c1600342000302c5060310920079680c070041495000e08090400d0400040841c10a00300142078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 112247715 1250 112246465 112246487
    0x10020306100801050a35030702011d0105120c0910050301090606050f190c0614010e0c1801030f0207060f05010e090303010807051302040506030907170309010c0b06040e0a050d 77
    0xb4410818010000d0b92251541402200c407055003c6d401348072400b00390000c0c102200700ca1010613805044440ba000c0020000f8070400e0b00c00d0303e9203018805541411102510390081844c0499401e2010741003c01007591215030141c458441e1078030740003411f40003e9030031244e8094000001d002200500c004400361007031401a114a06005c0c1c1050507054940c060b030b1180da100c01003406070984504400501450001c1201584100300307020320007040d204580c00c02024850741000620460114030346d1090303d0101c619020b2200f0741d80311031401c68001500070f8010401000c107111340c201701802c0410124820a8081d1005240200d855403401500149080c40070704082d046030400c10040003622400201c02c02180c0c5c1c1075942ca48100e224114000c02800b0b02d521045c3c000d0030000c1088140303040801e4803019a00b61b100008004c180d44c4403d01ea50380135402c11280480c803400144c80100c0e080cbc10b195070f400000108007052154828601e0307814001d40b08821240d03a4003400d848421030750413180b4005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 112248965 1250 112247715 112247717
    0x81605040c0c020d062702150a110703080304050606010309121805041d010b18010e06030a060501080303060a14060906090406030c081509190f0203010e12040317072604081002030610 80
    0x2401c6e440300c1c1c00103000c041282c50340700303102a030020309101d15901408400101055032400d583c16140da03401d24000301e91040f07904464034081c24000620541c024421a80d03642e0300304c00d0300e800c030b040e01483c181c03250b42d0070041d240d17100c0c0c50018001846503a98081c10760500d1000c40d0140c04134070090182802d44081d8a044d500c600203420899001b080003018850440350b42d20710310b100944481e000300b03081106200020344035500b8800007081c401c100100442c0582000e0728140c4142d6504c08203018001401c5810590089003000140d4ac4ca1a01001902c4103c0c40180700041003541c0740e6800102c1c540980c001d0996070001195081c01d03179560b1030006d60010410014203483c010004d0344050500104d1002001c48520300d0b110740540d2000d51003000c109030104121009032a42c0041001e60340c0091200300c500040003c08003021a000a090340d4007268400700090802c560544407241ca0890402e090b02c0c0381e201800001001d403c1009035404c1d10001ca40d005a80c2e041080a000c42401d54650100c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 112250215 1250 112248965 112249031
    0x20f030309100b1503060d080d02160b0609100b0912010c030608060106030612080d09050a110a17300304120914100e031608030c0601081605040c0c020d06 68
    0x40b003c44071030005c130b981c084005c41300b020040c006490440840d0040885203081c02d4808503240c40440e5684109100907802005907000e250399901c100b0500780401c0301e403064613000361a02000340525070006401000d100130805452191606065401c48003018490000070f40c44200400418905003c45805001980740078010079040c80300090910300c0f5088010101900082e02e90121851980302e903210650000598040d00840c4c102007500c00c2072003020710701c101500c0c1000100d4114843d51000c00246060281800d60b00040f4910208a040e2600c2080560003241007290050080c1c003d511036441515003903510500701400510801c4242c201c4050001c4514074103840c0c0d41c0b01c114100082c005031901c2600f00c501030020034141032040124180c208914003011a4008011000d40000c1d040e4404942071a030360742214a07500c3c41d4a166000b10391707940172030911003800c040d040a03814010a0034158281c100c1c66000c0703994801002412380350703941d4401c0b103c40070000c61603880392a199804c01d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 112251465 1250 112250215 112250239
    0xc010f0b0a031a04060209120c0909010e060f091c0201020310060509010c1709130504050c0103060302090708090a0b1f0e060f0405060d0b16230301090c020f030309100b 74
    0x28024003030000c052151180442c2c400507041142c5070701195002c407406408e07107100180d00741c559681c445c190707040184289401c1e400504030200c14420071002c07011303141c028100d5440d001400320529401a0850b03045001e48035508220711220102c031459000c444e0300040c2e42c0d1500207000401001d580d00300404010003004808081c0e82c0c030400c40146280c04ca1420b00d090903440303801d01d04510070b845031a50070065513000c030301c2040c58990091b88140d00500030303189003e00c2c40c1d0045040390507600000354405034180102d841e5a1084030f407594401d0341d01d41264005a0540c4401c60007180407150422102c030310300031041c00542030304c584100919060701c4910260034540002061050203100c1c1c940500d0380c80000030150baa440305c2c0344020f1038209840420728213003200007009007402c446100d400b292800002484000234002600e0003c840d04040a086900f850948000307011000d0041046201c0c011940d041e0400030700003140202141d00040902914100251007562581e03a030440c03080710400301d8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 112252715 1250 112251465 112251473
    0x8090a030f030203070e0a12050c04060b03010b0f13090e0d0c0302060106050702190f03020108090604020109090e0114190f180201200d1d0405060f01030203060d05030c010f0b0a03 79
    0x7201c40d400041d04002da1660380e15001114401000c544260b1f1101c03031200b00091000c488005240004e008806170f0700340d01100c00a10041d0b40d07403481010000101040100130304000d207000b40600035440ca4000d450301b8803800c140e4441110607009503014594401c0c1070040c0c1c5204001c80317840e40c215400c0c5070410004985010352a000144184802c2c844009a05021561380c01441030601036015070380340d407194848280c1000c01003140800c90124200ca0302040d009200003401a01c555816914850500d0401d6151400751242c04407110f410b40d281c2c41c1d140c071103001441c0101d10a00050422804420810328a0701c01d8a43d07252203104064a40000780a8001c2030143d132850040e020b007440d00350703e010341039103a8100302d5271603034a1107a0080411a112080d44810350180381d0186112030013103c452102000300300d600650b1302d15403003980c40c0a0407a0550281d0080c1d58841801001000c4e00400c0d034a03580d0459000080107109655a4090745800c0d174007e12803134280000544446007040d0444d59 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 112253965 1250 112252715 112252727
    0x219051c17061005130f06021204030b070f1101020703031e061a0c03040305030d0603060605120d0c110d0f20060301090f06090c03021201080d0e040213050301020c0d08090a03 77
    0x181c80c0110140b031195404640135504880c14108145505200d25603100c901c0c0310707131110358000c0380c0c014003454402c6202d40c9a804c0650301541d0704450200c0450319603c106840d00300e1181c04032010300001d60091a44030780d00b84007404002d4041e44011410401c4d0300ca100a0051400c509a2a27641c03400d901446101d22134030a00101d052040036441e81c074543c8514035461405141c0c4010403600c00040c034562a2001b070740148085920510701844050740b100100444903c01442c8680198400240654030910480c1500281030180e201003841034040e00105e02c4851071503500750740140c5072201e046c0400c01c0300d484403400450b680d100c0200a203003903030004000348010f02c00c0c01f5090341c940902c02c0e12001564042c40c001c02e4074440400c588081ca000180c065004868401750783c00000d000051800310114002c40d0003a01a074840030100c50754000c10002303400c15003000014203008800811103460902c01040106142c60040c000a1960b540080c0f42110040603113049802c0700f100c200009030410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 112255215 1250 112253965 112253971
    0x7080106140f0c03090330030118020a09081b01120504030f051818090d020f03030604020a111b1003020a080c0d0902180901060509040f02100219051c17 67
    0xb030308080d662005020100d1460066180707065060161441a00150328a42603140c2500f0051142025541441c00c101d001030209101d41c11440e5000115202d51080c02e900800201e0f441d03013441100c1686840c98645011710120703044541518044000e0b21647c5c10481503401c3c4803070058180200e18261754000c00000403584003405000003c00c46010615180480e1081450041c00c0c44030620409100c101c01644166074002d0366010b40d0344504002440880c05800401c1c0348001035107035403515414000250301a603210420401e1006140e00364107003e11032020f0740f0100b00c500164005640b410052010500c003240410b062040200303452071500001090340c4911407800c49902c400d05100884003814061030004c1d030040d5101215440010031805c075a001d104442c0082000640b10b02c14481348203025100501501c0d42040c40c079005161104c81d040441030b03580f055401c46400c005103030000c1c00944c2c0045401e5040301c40501811404140402201e49651501385401c449420300023003a98406 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 112256465 1250 112255215 112255237
    0x10e07050a0e0c041e24081803070b0a0204080118150908090d050a060e0a051011120103060b2d0f04020f1b010b0d050618070f0602060708010614 64
    0x5440000c410b5003e890075140107000f150107a90400d2601010b110403264540262803011201c000051140004801403144075206900e602e507040e01d9102514640388503410400150b4842003045400083e41c00340128040d41d1342400c09a2a207060825071829141e00c2c1500c01054070181ea0340d200821041c0b860049a0780c185400054808140d0803c44068842d1203211a0000d01c15814001044000a11183d00070b0107020100603c10b1001c0100380ca03000c0040b80038140f540818180c20400c006035000200300104208050300d0001000010042668268025545240d5038904042103060440900c1c0d84041ca1f00020700070f40d1241c0d84842c100c2143c1c0411302e4010648110b40309910345030f5504580c0c1c1860072909054843c0e80b0702d1054981480c2d03440c400c60243d420300c084500c4070708000d01c00401c0d9981c0b24001d0041d982c0d440404c3e000c0448a11101603c91080940029100c1e80d03007862000603021540c090207141c58102c401130100031042c1d00910400c09821442075403851040b080d2203c036a15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 112257715 1250 112256465 112256489
    0x912030b0f09041a0a0203100b0c030915040303140f0403060f060e0c0d06080105130f0f0206030a0c111f0e070308040905040302100209010806040507260603010e07050a 74
    0x24200100707105140c80c40c04190003003021400e20080c080c03a80c84054841c60a20100d00302541c502041000340e0009030742e0700103030303c48441040c407441c44044080d0111890010032a130802c41e03404001140c005051480b0024550000340600030305500110400420003091601031800200d400d039403416104501c80504000e0744c6100f00401d040094002400070306030a00c5903941401d0005a040680d8481304404051929207080001c8980e03060098134415a510309404152605603100c44901c1c03441d01104a6128140740d0f104c1300160b90b0f41c4050350080346680c1c0001118900a500640340ca0850841a40943e11464001013511854100d44516a820700c002082014072101c020307191004d29080105010b101040214451543d40c0c030070f0307200700d02a07401c03600f2240500020f40c04912842d50380a0005055100041d83d508003500960782121180ca0410240c000440c64224800d42d180d40b01c40b0ba9200883c24030040c0d14090140d0303510300c46500050081280b42c000000c0703902d03040c0c0c40380c9104201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 112258965 1250 112257715 112257731
    0x1051030020c10050601020d090e010302120a05010e030d060e040506070f0207050405250807090b03060f03150406060f0807030b07030e0a03050301050a09020405180406180b090c04091203 82
    0x2407034042d2003042d007406084030501d201040b442070140004454480c0184658011032440e548120404400c90745480682c1155900b180c0a01c82010b01c00c185040b1584622040c0c000091024400c20106040f00405182c59a540b2450386045c1cbd0041d5001d0f85480b00300c10140b2000c914041185504a4500d0520303452909002100340d00741035080d070045030b20a190400300304100c0001803a2010f008146031100851084010f01038501c40000d45030000020390000742444030442c618000c6401040040420f100d28a01d0000603240040e8908044041c0c00d1700c106120400500340550790241c501c00098070304141c100410720356125141d1001400324403203500410a80e6000b5031112501c16180000c0e40c900041d10f041c00341181c0d00a1007194081c0061460008031000b039403081d85d050300c04c01410403050044e04403421074060b2010300143c1d05c0d2581c80400b070751180c0035640d000583d544100c00010451410903511410001d108068074040c0e82081800c00001d601007001940f074030030034103000541d94 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 112260215 1250 112258965 112259057
    0x20303060415080d090509010807061b0204020f0d09061413020603150604060c0b01230909070902130503011b050702010c05150411040b030f03181503010608010510 72
    0xb0502c0e03001411500400524405640e03100002c14155001620880300341e0b40d940880c2c1da9111182e10603c0c0004a90150103150810f40040450ba180c0c00200094200b02d00c0342c110300419800192001d0074540d449802004100f030b40c1c09041c1200c0c0b83c50113030040b80d14050100e14034410340880000c0c45140004002080561040012210301201910a0b9242c0e13487c0c40d806800b40d04150820356a0754014400014404c120503051a104800648000310b030b00e0421007071001d144405800300b0307101d0041c81000310300908584040d1041280c01c09004010343c1c07600080c10300311004d550010307171842d0030302d0005100075070061704803100554207282c0f00c50f480d02c00d03050450400000300308040401d5085c00c180b00078450180481030b11010100c40402c1004203000c100342d5103004881846500380c000b8002d994001149060b4107190140152100708144d03019100211154800d801960100302c00d840140154107128070700c0c01050803030382000582c140b2900c0b5010315015480141410b54007030101b10102c03035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 112261465 1250 112260215 112260251
    0x60708011e030c15020f010504020607170903060901020d060b03101a0708030708010905070e100f020106090906060807050d08040b0f0d0504030c02100201140a0209031e01050709090902010203030604 87
    0x854024040d444440d40b2131214040300700b08000701c800144135000c8031031040d80e81032141c640980d42c01000f05180400d940c3d01c2c07401d500d01c5038900e01c0c60144240541d072405c0c0c4090250758410140c2c44001a6200c0d80c160f020400c42c0c40a1b0410041c0140c140100048005100340020070340f4010300b18141407180b00307088900a1302c80c0c8103001740310f580c012003440855500100b84a06990580105021642d00e191044a40c5c07141c1400306540141540c0421300e2950207100960143c90061001203451134607584420281c0707410040454401c0d42e5440200a28001404240082e21007107032800c12411a0b41c1f142511070055002d40200401d00254000301c1809240803941d1440c85900140b003140317040c1c00e010380b6294003010160302034000d059183d40107500c18881d004078200f0200c0550565140ca440041c025001103910540501c01d03900342d800d81c00b10a550100d03201071b1510010540b07140c01b01009000e03071a60707445212043e00340814680140e801005403540719030240c0d000208102c41724482c083d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 112262715 1250 112261465 112261469
    0x6120a140f070602061b1c05151e040c090f260606031c020a0b091b04150e13051509190305030c030709050604060228020306010b07080d050a050414060708011e 70
    0x5da0b17030581f0502e648140858000503c125003200c0c1c55119200400180b107015009100d00010311a82e0401c40300103032415900c5020041c0301352038050301c016100e520b41c020b2520306070029818400f4401511900f00d0101102c83d5020401401602c03050a0050210341c0d05e4120307018030005100b403880000c501c00d1003000b90200d1680c01400c8000d882c105041d1481c0c37200048c18822142c515200140884c42c1028001c3c12000c1203040440302c221071829400306000100540b2664820240014910108070100a0042031403050f03903107040c03a07040c1042e425280500b00005084420300b0041c00101090300b110a9940c046d17450a0120f44c0c0359648138040301c84540b1070b0031039a407000c400715010998070303400a0783c1d40030407032a5401c000303d803510745040c030082c03030b0b01c140001354585e220701300600c4135940349005011400c0c8100c5031141866526454036055400c201c5500c81c480e50384a08006c1804001e4080403180c010b00da0142c503a03401e103d0030091800005000c0c181c41a186030f2072060541e6102d042c101c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 112263965 1250 112262715 112262737
    0x5120916150e1009230a090f06030803040c080d020f0a0b0a020d06090605040c0908190302031c090308130c051005160609060b06160b06120a140f070602061b 69
    0x6041c00d280c082c00703440711003c1c1c0122aa00362401034001a0462041a109503105d8010a041c070388610701058000034000ca506e6140e019515004004005030b00c84010314003d0348650b10f009505818100320740e150440a82c90201154000c100c450400100401c00768115030704004180215030f540040d04000c1d03c43c05120f0651a854120b000030390070215409401510400c4500f07101810754bc007802c940d001d036103000e982200d80040380c00c00c00c041d85503000004941e02c2401a00d0900c501040409a0603580801e680126525072000034201b40d444498503902000106402400a0301c1d40c07078220300c85400d4010f05000300141c40e2010203482c0503405a80d840444400032a0f6082e0031441c05402820a00000f203070100c1c1450380140c01c0e0715051050364025103a02e207860b9001c0d0aa6211410101c0000d007209030803c00412003406030203000d01ca03031000c40c0d014003602c5000e030340e440350524a80a24040c20710300a41100d4401d111455001c0b58440d001924500380d40904205910129a01c0c414625002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 112265215 1250 112263965 112263979
    0x5091e06070302010e010e16051003060308040f0602010c0305040305070f02030f07180e0c060d0c090f080a050d0e0f150d02031f08010605060d05091002030705120916150e 75
    0xd0402d40d05404c22600c0d20340e00d90080c403020003000c1040740c0c0c0301040c3d070003c0c070a401c0802d010311103410400f10000d4215044c1c60041021a5291104160b03948540c0000c0d18001c101d140610042e074090081c290108140d140801c030741d1900c0c0d100100780e0701400c80c0080401e803c445001d03003507550803c00030f021101c0210981c0c6584c0da99103004000070022204035204030b070811170840c02400c004603d00d1921003002e0441ca00d400c00f42100c0c40018450344003c1800e0100c10603000c107100042e210640c0240c03420310020308285400341481440c1a400c1c0400b98100081407440340386a482d50030320407d0301700e0180c43c2c003030000240078041c2c4c406d400388030f5007910064804010000d25100c1e110751222041019004450041c2d11a02c0550a80d001d50240b1600074008110100058a007a4406503010204006030384400c9040c6d0b0201c403e80e030081d40c061000030341c089001401e5441b0841c4060304408154024016111000d00307001c0e580843d48511003c5110101c482d0582c076005208c2c0904000c001801c034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 112266465 1250 112265215 112265227
    0x20a05030d0f1709060103150f0c0e09100f091d030711010917060612010b03121c020412060207050f242a090f03010f1a1005091e06 58
    0x20502c1c09074840001c0021003210300300c00000c018000d031600401030000907080d00da08549500400324014010051003690382c8041494501151140490b000780c65a0303204078200c800801c00480000107041841300c1e246943c800c0111205442c04602100c82d14900131880d403910241c0c203100c54000c1441c407045400b0006603d01007100f4030071014040c8201340c035010401d9407222600307000e00070301c801d07038035015031014004c98500e213000f1401d403111030200c00010840160784004a8185080030070503013580c0340c2c00700e40c4140713604a02142c0c0780540c0d544541141005c1c9403030040c8400d5034060b10060070710b41d800103100051000501510381c50380c5910003110441d44401c81004e0360307418031624a004c0d548460020405400810a0340203840542c50402d5014403030406916540390302220300c0c1c2d035000c2a00002031079951400c3c01752800440002c1800211814000046400380042a0443d4071958061400307414071500a000e84e88114002e0f43c541c1c0c200c04a10000c00308002100203225442000803070700c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 112267715 1250 112266465 112266467
    0x101209081c0c1e03051015020705040c1112091503010308030a050c07030f0806120f06090705100909020309190506150306011802030c040906081006060f050d0504020a05030d 76
    0x1107404503084103002000032200000341103c641141c41c81d103414003910326110051861003900b20b6504040000940c96280d5550041c0444181e52003240b0720158001841c00c10051619100e008003008040c00c1200c07400e00300d84695500c6503903451030f6091519010440b18015200c0d02c81211072200c0e1581c465a40396103a0800960a0f001141c1c00c8292908140001d9080108001a10340240d45a11620140300c0340d00f001b40e0303800314020030707845c1c129144510350100b5600030003d00c660307030014501500c000d0401e1200d003810800701c0d821460040740380180400c00d043d8086069000c46026950041c0c0781e49405840c0341c241031444440c20090070030740c4003250501c03201050f9240110b10b00740d400ca184410700720a1540f501c0e401d2003811080240740007055205c0450b60000d560040c10b240c803203031409840c3e100c1107040322160b4000740340551203001a514030903680d03c42c070b0001d4141030626003445d8805000040c42446030b00581c21040b80c4680118045440701003224001e4100101a940c6201039410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 112268965 1250 112267715 112267747
    0x1621050d0503160c0b0c1605030301120309050402040605191106011805060a0b03070c0524010317031515070606170c0a08150403021509070e010b030610120908 70
    0x606010041201c0c030360008018050b0313503034080301a807203800907000f59105c0ca503041d259044001b1880b44070402c40b00c51000281c0c28401580a000c0307064941e0108d15003030800410030400364000b50b00951041006014041d0440c5c2a101001c800749000e00e00c020008000b00d500d11110788540e0200d2050302c002040d00411840c4581820b5118441048266104000c02030400c00512401200280c1000460303542d6124024403107066024508a4070030340d40444142041008886c0b8111091203600d0050007002a800f16603440c50030340900060645c01d1414026201059007000340d4403070840852803400300e030110030a5440c050340041c1c0400c41140e80e40c1c1c40ca20303050048000203041c1d0041c020340203924908031151b41c00351040c080040044841e1080554002d21016005030194810003400c00d4030509403900c054820751104000c0c0202e03a10b4a158041014010307000300801941c01d1081007007948030710070500c903040d509182111071101514030001c02841c440c140a4081000040c581e804040d03c06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 112270215 1250 112268965 112268971
    0xc110f030306010305070c11040510080604080a110303150d0204060315060501030e03040602060c13030f0809030c0405090a03081b0a111b0a03060905240601030501081621050d0503 79
    0x1e00e050281e641c0346c12048a454584000042101003019103d9005040a43c45035500030300180e4456120364517244464940342c000c80c2c00f156014000925000915800050074501c5c05d03015000b1070950400519041c001074000b00183e0080e060303041c00c4015541d030b5801101c011900104071480b14400080d450010b800c20340911030200342000d040d13090306000007084800702e5165038090049900e9240000c0a66402003801000c044d0203403002001260784c0c9016044800d109501d555075802102c0181428114400c0589105514160401c10308660100d441c102070b551601d4182d40560303440c1c0d4000c03030941000c0300f40540285c021418031542c1c0d411600040140341c80508547c503145103003034401008003101c0d112541005c210380040001a1281c0c000100da81d00c81c000341c929000488075104c50104501040e04904440300c024020a560184074643c054689100941a4082d030151049050146ca01c1990000001c0111901d080b00503201b0070040b443e403000548400d9603580c00000c0c0550019 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 112271465 1250 112270215 112270217
    0x120f0911030f0d1103090402040b0414030106061416050601080a140f0c10030e01090f0b091c1107170d020706050a09060e01031d0318030610090c110f03030601 70
    0x5541280c10a203000901d082000c1d840318010310001c868064210b500d42d860883d10040c501c004d00c10704d0000e03511400030300060440d00c080f041e191032401c0d183c4040d46803200002030090f490181c01b0300c80d240e070083d101102d038950400321940e030710b020743e29982c02d001588001410740e001c0c0b034001113030300240410600307a01c0340a51000c0d608020007624954441024149020141c1d005144030701c0c2e20b08000200d59000f00c0c0c1c90400203410000c100305182075881085007100c0741106010801d00b001101c80e00c050300b0503040c40042000d00b600808502c90050410b400300188400d449021203c00020402400a042d4a00700c010520528210316039450210741c19090250140c84400310320703684524152801c9242c199a40c0005c03d10f0030b2825544442c5001c005410180c60320b20b281c41d803140403003082000a10304001507a03904000050754098040707450300113200e44c0240c010b0120399140318122105440c022840061001e023459802e85400300c0420b07c4481e02d00806070948050200800907500c0340000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 112272715 1250 112271465 112271483
    0x703090303050a0513030c06110309090601080709090c0507021503060901090b0f030a061b17010b070809091e070c2f03100c030b090c2a0709020d180b0103030f120f09 73
    0x27411010341c4a00039580c17202e42000b180400141d440d885038480039008200327800c20207481c5440b62540070660700d1601c00c210210700c1c00070b544811800c101d055540744080345040c0034190b040c0580010404541032003805446503c940c65014580e0310407009030441c8400808507039000d6013910f818000b501c0200d014413410b0300c400d000400d4160250748200d45503620f0281c0c2c40410782c20203078840f40a8008407020b44006034240070000f2152116103400340681500c3e5401300441030600c001d0051601c00800c20380400210f24011000254441803241083c640742c81c0c6842034019082c89491000303072541c00342c0d5241c8228108180520f03915404104800002d544c28814600d0900c1400914070040c0c800e0140b800c07003040764081c2124014040041c0c0700b925400911050803d41072a40740100d150001e02c0c2d0264006903090b01c6e100b05100700000c40700409025041c0075070070707264441034050510029080c0300340903421544203481041c14010b2081101d108015200040c84c5403001884004030848031002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 112273965 1250 112272715 112272737
    0x60221040213140a0f0902040e06092a04090807060c110105070305070f0c051e100b040603050c1002070e1003021e03030d150302090c1e0703090303050a0513030c06 72
    0x42c590294090ba07440e5a000e00d44039841c0c0c81011801480380000c41000079980713140c0400140d98074020700d030301c2c440d100c1e004202034104032919900302000301c40f42c2d070442104c051501d4150340906490f0003542e20204ca000945240c1828105176034481c600000700f5051424031140c0c4000e03008614690f107a0011402000207a076002d8042d403c640c42a1100804540413620f565005072003008010206032282c400d5503035405044039203c442420303407502d00e5444e070044501c68505000f039100b41540345074200d80900c415032868440c0f07502d5400c045002d5010f1008080e02410540c0200070580042054048210f1940f4010520144070b00c0300703001c124818100504500e845c004e1889650408140003400b640c036081e54101454020202a180080129004000000035030b84196015105000b0616040d5450418954103800032404051a12018905100b4040401c1d0300860003015170f90315007016584c8002c03140d429201401243d03500903015081c44004010454944010301c100d4280b0b40f15a01610 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 112275215 1250 112273965 112273999
    0x1020304141203061509030607021b0f060912030c1c1202280c0506040b0708090d0903030302030601050c0a03210608100903030b130b09060d030206130602210402 71
    0x849528034000072581072000c9032691074179003d403000254920001910780007511020a0512104542043c0560810340b8910240460392214071041c500884842c01c03040b59036000500b560107820f0318107000c2c0c401d954018002c071004008441c05403501404440c450301135018541400551803044c1e40000f10322400482d0106040e00036904032444d07142a1002d440042c19880e03801d80c01400841e420440c1da10010000f0034000c0c4503c50040d0f0044203500f10034584024003511aa07401340500025900185104004c036500c026102c1c1600e074145409030303507500d404004a8890080500894441c0504c1090ba82050b400000d021181c2841444a1040c0044080c021045440c64841c94820b9044203100001c151b01c02c0d4084406640320303040010305c02500c0d00c08190181c400701008481680c1c0c40000d642c1c1440c050b2410f90388550700319844c0d00380317141560b8000e4840b02d02401d60f4004142500409041000c241c0540b00c05021a0020807041080e08100e0343c1c440009481c207901560080041391048 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 112276465 1250 112275215 112275223
    0xd15060e0712090503090a0303030b030708030702060304110a0b0a2106060219020d060905160509060f120c060c03120a060b0a120b0a0902040603150302150a090b0a020102030414 78
    0xd00201e803210305400360301c05444006480e15000c104c425010400600003d40d0314006d4500265000f50750004122100c0300c289880c00c60b181d080710341c2591051180400680d14402140c0d07200c2e078489400003580d618400440ca4034040b5400c160f284500200c0c0340e241c05ca90015501440d01c961084450140b2030421405048503500e018802c0160001c42414109000144002602901c0035020425410030381d2035400481c3c03000d03142124190009228164580d082400e514090401240c1800e11400c103400043c00752404107030700d01d005a50ba1301c40b292841c48140101e038085e04d0082c0181da41c0340c88004640b0384a90020124166091601d00441e1105c903d074481c131000e07298059003031840d26070b00400c141c41d000e81038005041e489403a5001004103480d07542c3c510000380018280903840d503003851409002d40d0b2580c41581448540588104050782c0c8050440252070324188240e0380d1140003420880300b049150700000300c0050b00140f100d040c0340d4154001c0d071103035008025011840310703119907440d11 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 112277715 1250 112276465 112276471
    0x60b0f1e090a03061b0e030709020c0f0a0804080601080309011d01050702100206010503070f0b030a0b03030d061814040215031909050a0b09030a02060115030f051003020111010605180a0603020d15060e 88
    0x103601002041c428407440da2b0080035200310007401c64485036900c010152912000c28004c0307840300c0380070408024103041004180e01514100020b141024212000248944192024288900c49240407500c00364002c40448034101d801920843d1400c00f43c0002030340d600c1e002e103d10703800303445410400a03840c0c203605004d10948054508842c91503c5401e0b41002500c0541d2006515000070000454040054800c0000820031a000b1a2100084014080c100c880c10b00c0000c0d4141c00d804100801650740e4400510402100d4810f1522900c4894445142c20300d25840d41852a14260014060000c0060385840301c501c03901450b02e80d0f580f8441d8041e164010303000d0030400741e840003006209140c0516aa900286018600081e11516141a18080d540150f4511100a50b105414415135a000000340e40d060701c240000d04c88030b1b00d05004100c40003000900e49030070542c01c03804540c601803141c100200031500100b1080d80d00d496810a02504442c0c65045410180340c9000060f40c0d00d6019000c3e84 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 112278965 1250 112277715 112277719
    0x406091b120204020c0f060907030605060405060d030c05031b0114060102030715051308040b0901020c0a120f0f0209040c0905130f030f030f020f0d060b0f1e090a03061b0e 75
    0x14140d0041d0700740406034200c00d480d01854016030300c1b010f40d6000b0400c041445025444000e126182c510b00f05801243c00203043d1501950500e02000115161441c07400e0003540e15241501441030182001f600794091000042d00440b0030765026048038a0542103440b2000e2091527a142d641c9407080166928801c03120014100f4014a00b521854525030744200c0d032001010300300001c50a4540e60301042c0d907100b5003114048075400f054400700d5503410055820034440c16140301c0001703418019200c402c060313030b210300078070340c801080ea810700b04040c4095250704980e010340921810b007001d24013100c0414640c020188440c0c5400002180c000c41c0046c00c40c00d8981120303a0361100d902c0c43d28111005c0d03420710703c0c40091580387c0740c0e1a00c3c0c0351401c1c03004180484200004c9a00e81503481010425540f459111a00d0390205022800503055036400312642c0c02450041ca080050310700036000224003a44402c5944030060340760000500245030010407203420409400d403c96000c058013640d90b140401b03c1d40d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 112280215 1250 112278965 112278989
    0x4060302090612030702030a060212070e012a0219060f0306030809120c0d05010b010e0102031e0703090902040b090a12050c06030903070b01030804030c0605042d0306050406091b 78
    0x2c07028140f03040310200c50440181a80d1802c02c017a008685031070344181c81154900d80c0090355031001d060420100d5000b92041c0f408580b80119440000c001d070f0445180c2d01c403110b003071018074140043c0100191810366409090348414039403400074a4400304c0c01d44500070205920340d406c1036100d13100b441007003b90f9910401b05400d2000100a11040c2c0c0c1618008c000e041c80380c00e0343e084460740c404c103a9a249610038000415910314080c001480203040c1d081c2c1c0b50644d4404c0c404030342400c80c5c0c180e202500c1d01c00707261201d0300c0740c400b400d0868102e060b503072102c180346200003004502d10742241d00801c540c0350250303115484d1710f03541e1441c0020300e03d610001502c1ca8100e403a89610601d040d00003160000200300840342001595221050410000e82c421544048001380810401c0f507491401001403040c2e042090505150440f00f049800181100b0f158100e001c061480040340a01220320107103070400000c100c2450640b0b4990014410058203642d00e010103a503500703007181e58216242c251740300d9a41703030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 112281465 1250 112280215 112280221
    0x3040c06030b0621090c0f1309021909020408010b060a0f2007060306051207030b040b0916080309040b030f07060311040905070804060b010c080715061a0a08060406030209 75
    0x314000c04000d0b62565000c0e400300150fa500464422144d80020313140c2600508500b00004410700d0180b00b1800640211204011405580d0b24103142c540100228000802d211140b4170020302c0124076442450b11f14000010301180380b1441da40a03000380c54010000b00410407100003048064040c00307101400149501050040c624030405107014401d021074900b0007001e0220030304c10304040e010303040900041d64840007004149840c0464220988041340030304160b5045032030314201900000c101404142c42d290102d107030100d04200501d01c03a0385c402503104280da1100c102d151242c0c04180c10f50302c00c03414540405194071380804c0c12825411104000c000303131440c0c180281d0140003030341010346100c041404006128101405010312400c001d039154007103807030145050b00486000081085c10401c250850380001360b600d40403201030b56042044640140d99806240001e03003625040183c00c140c480440e08895010710000e040451110780780d8003065650302040c08100c403010302c800b039800200c02c004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 112282715 1250 112281465 112281467
    0x302060a03020913020d0207060b151621030501260d030f060b0c030a1d030312060303070c060f0201060801150b070c23040c020c030a02130603170c0706020303040c06 73
    0x5101c0b000f406003884000310ba03140815012078118129610010390001076050402140e84500e400b41c050440c0c0c1121000042c0303240320810701070302c1e0458101c2014411003030140002d803094110482940500c28440c12103840000300501403e00c01c00c441a0503410311001c400901050301c200c40c003030390350045c8440c14921030100e0180a0b04121b125000b90350f4880414980541801018401484402540d80745081d800c001c142068000340f00108907502e10a039440c44c0e40200440d5402c1850410b8078200d03407107820000f819880340d804000c010703401403200016940c0e0428007549001078160020498a039903080344500f80da40201000506011040d0140070096020b4040e10350a0f01489800ca502c0341c84008598403421007a514000f1840c90780c2207002649014024000d118101c1d10161207074224070400300c0c0d076481000200a00c01c1d0074810136800720540e06ea104030004e46e0001144a28003034a280008940d620080395031601d17001d0510b0202d4002e0001080b2401341e41d000681c0741515290045c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 112283965 1250 112282715 112282717
    0x4060615031a1c05070b03060a06020a0302060601120e100504021e0a030b130804060306091b05090909011509020304020301050112030206190213061d01021b1504080616080702070302060a0302 84
    0xc3d60440310b2594045840100d2010014040030340551600c060f0b80b81080c80c00c2100d0450654000c404640c881614072001070342c04105160000001c0c249003141481400011b00900785078000140c15100d070704d0f0029006101b42e0041d9004a00035100c804401c45540745039000300740803022481d000180100100000340420b1415a4480883d000c030071403685450f03955100d00c1e4031a600c1400003a4803050b0500141a9174841d41084e110008210000e10550700d00c060035038058011030601c10305004000440e03005003904a41140c10f60010307083c0d071140e20b4542e280300940007558242d0080d0320301000031842a0980c51200002500740e0001c0c0715942d40c8031003217038440030225008210b02d502844043c9000b030042c1c48041c05482561143c002d465070710254044008034800002e411540b24074008070078840000000e294010b0150746070f05200e0003024041e10310b0b200d07035400502688078040422803c0141041030520a0000d0340c0c9101e12903d910b14205d07650232031030001030340c0000108030b410a0540298 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 112285215 1250 112283965 112283989
    0x3030702010e1503070c0c060503070f03020d0609180308130222020903070f05031605011d010e0a030f0c0608070807030209010c021206340c02030709020304060615031a 74
    0x40401800031200343c0d01c0c4141d50815107400c0e0201c3d0b070742c2c2d04c070a0800ca200804100a807440349051825880e144000802000442c0c65001c14180d0000b20302c400306010340c110340b0140400d03000502c40115500100750b074003402200c064000500350300c007095010a0103d4880c1e200d81e001400c00704016080000445140b4409581c0e541c45907080080016a440c18013124009103104807941c4921071400e8203050604000c0764080214801e21801406640e800400c4003042c1e413654204408410007410059914490a10241d03a00a000000020420500c080c00c1403c0510401c0070115096840d502a00c58a5050b14804007052080e0005280e5500c40d60140408000500d801c00c400c001c59004182c3d00d090b60b0039036075442d0300804200603000310081c516034004106004005540060000110b824480003e840300c100079211001d441555420400074000d00240c1e0402c55582c103092414800502042c0302c0d1504111045c11400d00082c024820200c59103201311202c04155902e9040140b00344a0b9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 112286465 1250 112285215 112285219
    0x31a100305180a080301050f09090a0b073c0503090303070309060603060516180308040510050f0c150109020909060d0606090207061401050a060c0311120705210903030702010e 77
    0xb078030031012020703080000056880c01001890390703a504084c2400410700c40000e1040c00b604c0640244002c16500184106010740c014117451010384582404688140040e01801c0c1c541c80300d0030390901c03030400c061003080700042058046140400440c60588580c0411200425581c10510010315441d01a8002d05119442980c0006026485c0d0751507501711001521810303a14920f040c2090400e50700402e01800003211001020000c600d5035691412521450180178080d501c034604030f0601d58040c209458095050f0048203443d000028503096032808040c401020741e1583d180006440e020301d108881702041d01602c12449541c9840901076001d1900c40c08443e820368640b000240441c281c4058440f03180f2441c00030800c4200b2030704026440170180c10092060000d403500b00310040c0c001d00c1c02c0c81c80603070509025018407540ca2010342420f00c0d040f521041e4003c0016500b0400002080c142e0144041c005220f05000b0300c944c20380a10302074030398529055030080001001540c00341451629601c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 112287715 1250 112286465 112286491
    0x30c030406060302090109021e04050307090e240f010918030c03020c10030b0a0f060215150a06030f0e0703031409031603050a29040210110d020d031a100305 69
    0x180c0e5000c2243c1c04007d03031105d03111650108650483c01d13100207a003051402c070389070201c0c1005d04110019840d0202032144800059507402c881a04020900804250741e1480b0b10500450300c1340d036100b148a00080b078039505410305100022a03801c041c0e214003804160021010400c1200d940d41c00c0c0c410320510441a42980b0624154150790b41c5c54602918074118182d0b4041040d0841d403051201608031900714030052000d03503205105281c2d0024248494440e00c804c680142e84406400899001c201018540c0240740e4881c0031400c1c40d05900031014140a1210400640c4000010142c46541d940401030006441d40c00c0c10707100041d00300c0548401c1c1c0c4010305030744103081c912407155586000d560046541e40c200d11440c0080c0000b00300081000030b102c84e851483e11070303444c000032074090004100901c00c00601d004c0501d040e01c46d00144c8107060141d001c23906050200d00d0043e589160603214140003c1c100700d40c10308803100303048801028060141128140d120803013010380c007400c8010188040340c01c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 112288965 1250 112287715 112287719
    0x90102030915062805042003040305030c07050a0f140d02070603020a020102090306150102010501080a0c05100e03010f060503070518010b030c0f0a0e0a0f08030a0e0f0409050601180e03030c03040606 87
    0xc2c1404c3c10614858888080f000c18645402d11055072484c0d000080c4442e05101074440b2001c82030b0071240d00690519009945c2d9031074115501450095282c0074020b031098641520420040501d0700c1b507014001c07001752800d41c0d9080d920560324018202c1c0180144c02c498001c0160341c0c001d8024002281c0ac40c0005801c0c0511240032916152044600317030a0041c1c44245400710356020300c11180500320705406400c3c00e0074030744ca41d03e002000381d02c102c0b4014150440c0c0001458400e00309101d4500d0002c0c0203224061403998150003520050007043e00ca402000300015403440e01154480f01181204100a4640c0c43c042112170940c100a0030351440314420050070b440b503000c2400030710320042c2c42e8607a81891810f000030720550781760b00d8004241c0040403440500180d1400001d1390760014040c5040b94010710020007145040480d90301054210303007004100810010081901816100135580c1c08881e0340d180d18072300d819100d2211000d1025001000441d07910080031006507800307800340d600070590507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 112290215 1250 112288965 112288999
    0x2040c030f0e0604060c0e010f0c0615120b0c031302090604110f030711030301060e040216020402041211030102070b01120c05100806090604060305070522020703031409010203091506 80
    0x81a110612802c0d0300700c20100000c011051103410b0380c1c0442c1d0314007008920812000600008031800e001420b010b007001c958000c10003280c202d4025001c0040c007417403c1b140d803460988a009004182200d401d92480d002506821180c1c055174441c01e103d40e4898134040054080c01052603000e040c05801075214600110305002c40b4009001105000c144c081d40c07460989801014850003149502c000c1c0c20800041100740c0d88100c00d000d50392012a00180d40d07034800c420265044c821020025045800803034002440002d90310460507440c00f40b14655440b210590425080f4420301c60300074042140c010051060382c01c0e02d000e04c0c030f103e4131070401c6060301601c4100148410801c8030314400080c06010030046c0f9800c144080340d400c0f2409603030900001d810b41c2d4a01e51141241d0081a000c0d0007841143c89800001d030280ca150348072151401c5540d04501d050003000f915005140c9210000207102081003014140300f10f83c462000580a00861501da00150f00c50b980050070840d03220404068000c00d007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 112291465 1250 112290215 112290221
    0x17070c02030a0203011a1e01020604140c040507020d020f150c031008010f0213050123090301060902070506010302030c011803020103090f06020310080d090f0e07030e0609060a1a030a02040c030f 85
    0x1107a00c1481501b4154010081104040d00703100c18100b1039603507070207424480c0d8001480070741255201036514058600300700b50070701d46000c604026901070704040902036040c3e0041a150500611542551200f080c1c04c0c0c01c0964400808080c400711180d0741c2d0000700400b415801440e00541c1111080c03210594416100b400d54608500c111442503000910750510308491004134000c20003800c100d01901c11013851003900e01e5000c0248420100c0002d89110303039540a6024001500528400b10348a410718100169070b000c090008030301038401d1150040a647c0100803400c1e01c14411000c05031f00700d04641c011405021040c10403240c8400328000c001c0080e9460014500c02c00b001f94800300107500d4100514030b0b00741b5000100041c01000799041c48503503203c18034541514004241c01403281c0300d0560803801042000a6201507029070010301ca4a4078011550900411034500103000c06207908801d02d551180c90f0007601d070f00d43c2c0035810b00740050034a0b0b000302503014081d04002824a0440400e0003d07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 112292715 1250 112291465 112291481
    0x509090c04050301050601090501050d09020a08070806040519080a030b010c02150913020c030702090919032d09090c03110f040513090c0b0c03041e0303030b0117070c02030a020301 79
    0x2000e180407a05111504003441030681c426024a00071010314641000608a88945400c040c041504c4910380b0080d92500000f0300c00074400b440880c3c40302070f950340d41070752521020340d030807036941c0181a208070f8900c42c0350003511140350f0402e40b80d5181440e42d0400b58000c000d0141024140800088003001594503000c01082c811748403052255511046000c000e01130340014404402075205201d0219900c20000513a00000c0e81035981c83e800d601c580c0085441c0252400d00200803480861a00e010103620295450207415040c047c20841c82c4000305d8505298044040e010009032008070411104401d41c021003c4c003040307030500040d01c100032060181540d00255030064000300000d400c000380c6c1440003448450141210040086200d940e542200c1c1000c01d214420003540c001c5140541202c1c10b000711001000c00b464000940e4201c0c0000c101e03c04110b01c01900402d2500c0d8008200794016548080c030000460642d24150759141402d8500f4501c42c4010380c4c041c4103030850f02c0010f803424425218 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 112293965 1250 112292715 112292731
    0xf061f0314040f030e2209030302091005090102150105010807030c0e0a230604030209070804150203010306060501090b1305040c1103040f09051605040e0406020c0109030e01020d0201020903030f0703050909 90
    0x20115203038107014040c0098170800d14000c100c11444078250040803e00c840c03000080b13030b10104c0c80200c0b07410220040c3c001d40500307503400051840014038103900080284034050080c2c003640c0845070a01c46030144190240b00b42703404108400006400d81d40f1a40c05083c6400240c10304207075205041c3c02240350250f89410107034555448072100350b024540ca4400c0f007400c00045400714600f07421a40032849000001d000785082c400030714040f804200710080707468500c2c030400d602191a507035a0300301030019015500c102e80c0440d030040400328400030f07000c0445015900702d40100300b48034036107818000180b01050f105000c004100c1c182080806060009100a10864000340b07689410803074a130040341da01420340c60400d20842d140c5505c107a00802910102c038030200f110301e9140e58038144800a13103c1c0d0560b020340740d46003801d070504068210130340c7d06070b5107001e83c02c88100325500c034000d03801c0f03100b110798543d4503510900c00d0381000e130035860003041d68910038940b29040a10103c00324820706c0098038522 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 112295215 1250 112293965 112293983
    0x309081603140406020c1504030b0408030103060507050702010c032f01060503010f060602060a020f0403080301060203030708070f090506070203031e07060c0e0d060b0f03030307030b090f061f031404 87
    0x200c00d140d808040c8074002c48001040d286480c1c070b0310308069500c0a101301c046008000d1001e401072240d11060642d0019500507801c6121454185001c015917482404110b81341e62a06010403d50fa1050b005e6403c2c01d54180c41d021082803060718150342e40040980007203100c000300005c500302c0d012503154441d00c1d030311a4800802c800e4241010523003540c03c2641c0440001f0301c0d0035070400100354001a6203800c110800c1c00182c0c0d480a40c60099074034403c0d0380019050120000c000100325a0001c001c4d4420481030f65100b5540e1549041102e0000700e8071100800100c0600d0207006519001000b0541d062004040380d140201007008058105444600e0003140700c008a20706041c0102e501400d19101e0003891b0440740d9130308040004420301110700f0003900e41a0380d907a000140e9101d02d40700d0001d54074010100c035124648240009d0162061001035130040d01102c02190700e81c010750014a0203000000c0c0100840d03c04a8842d45032007810032000030405407a503c00942410f96001186e001c4c2d070040b0a00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 112296465 1250 112295215 112295257
    0x50f0c0103141e090f0336031002090f03100b09090105040b01060f0c0c03061a0303040803040e040305130e040b09030c0a06020a0509090c131505030a0903030908 71
    0x5001c4620a00c04000400c69240410082906004001d0b80e60354103845182c0007902d80290091404000e010120217611000460351030841a02c003143d024460a40d10103958864210b034070700e6540c2c5411038400d0301644506d00142c64048550007425212a0240072080380c420510700080c80c0c429640942c00260f41c2d680410241030902034074403a40107000c0d0b0003c0c0000d00b020b58a40d1008401485580204a20000c0c2011064441c440c42e40c14660030182d20102140c8a0420030003c00080788000401d44c1c083d8106030b85424044182c2d0f08840408001d141007030300e0051083c41081009004408000d8104281869411401d9405000e0520300000e050700c0d29007440c18262070000a401a2542e600910800025810005504c03100b207520100158440c20102da058426010b00c0043d554806c200c0300c20003080c0c00103880588080a203c0302030700181a510604684d000c000301a41d91f000034004c20009038066090740000740128803d280c0000c444074035448640c541e4200b004900307605880880b003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 112297715 1250 112296465 112296467
    0x3130905160206090d0804030c051b040b010f170c0702090103050f12190f12060b091008040506040314070204061206050a0e0304060c05010e060c040f0801022a0a050f0c01 75
    0x81c5004007200303000810380340c2400403003156509040700c0c46108000076070000400f050311450207580c0301a0300004841c010f410001614083d94800300020b40210b2070030901501c1507114039019440d8401c40d413540c1c04400d003d1141c190344400300a10304030400c00204551401030701c0d03140c9160f0003540188040d088652488100340e0034107042221440c8990310a1100c3c0d18005c6058030b00000305c000c0b83c00c0c5030300310b0424200203031140340c40c03144880003071441d022000803c1c210442c0280841c540c102c03030130700040c44400000c1d40c2401d8191030141c166801440090006401004600d0300d6003c1c484403a82001215400581502c956400c856002400746030341204100d01c40c05900d410070150801405801c01c5044825604e00861007603008000c040b16000061000a510201c2d070360707840303600351a21807800f140c5801d5242c1c02071044922402d10203100041c4400184249d80b0301d0040ca80c4460040c1c3c0360080027440a10f04010b80d40103500807017a032070700007540410512406c5115007000e48110b41d20200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 112298965 1250 112297715 112297741
    0x20607090e0a1b08011802040f05010809160f05030c1504150905090408120610020303060114041203081009020a0c0201200618070909150e070b040308070c05010309020a140303130905 80
    0x381500c1b00e180180010b000800c603045007401510400c1ca013001080c0e94100c5000c0c5040d00070500303111404400302010540c070703215619010954000790101c91480388810144a510b91024644544511081c002031201655102d80460410781a19090b0012611100010484c5000b80d4040360b0980000034034100c1003e15880302503000c1400c40c0c03070300700703840d00c06c54082e40760f103c018a05410001d001010740c4280d4600c0e4240e0700502a103c1d88000030b40d400d071902078214034003500d015880c5680391000080170780359402118655900c640e92030820f00c1c0564010344086005c607010b0361100380c800003441112031040241030700c2030039500c40c0c12440f0511280340908091742078001e0541e06041868641c007180401000785070302845140c0c00216091000d010f0750618000e03401a0328080c0f0000b8000051010b84c03000750001c5c5001ea00e10303104003030382c5400640032038103200c00081d001316440d10100941c0243c02c03062540c82c0c1c8081d01790783c5082100300703c082275807038550491001c170355a4400f440104180c0c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 112300215 1250 112298965 112298999
    0x602120f091c12020f03090703021207030f030813050d18050414041b08030c062d0f04080c03041214010b010507111305040305070203010c020607090e0a1b0801 70
    0x1000391262000501c2054034590b4404080003d22078100c04503034a224543c0e044684040844a015440e0b08003805019201c0c2e41d1880140d200b086840740900c80381d00007103420811694040a000d00d240c11315502641e01032801001903d00e00000000400410700502123081030615940c1c82d4440f02e045000c4940c95a02039410940c0202e1904e01b00107090104581143c3e003141d002180c4418170b5105005a00c8028100c0d04408064000030074003810319100011042c3c0610a090b104202c0241064200e071410590810945118503501c0e0100341201a001e0507181c005026040c2e440c6842c5e00c6503015491548642d04c18401a140050001c044c00114900403400030f84440013880100c0344440002e00038050404003505803902d000401985079900a002c01e48250400d50a10440c40c00d410050040d4003d04030a038002d500340100c180880d840411010301ca050742da01d51603107140c01c0581904440400600d01e807501642c44403400401c0c00f011003801074010309680e900046604101c070204c403201c424 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 112301465 1250 112300215 112300231
    0x114070c1208090706030b030c0301110d06090207030801060f0306050301061511010c020319030f0510171f0c030902090103260901050d0b010507061415010c020f0f010203070602120f 80
    0x101e010f0210385240810103208503052072a012a540c1c2c400ca00181c140480d0701541c0e607056190400c0d0500c8542400c0140c00f1903030341404100140365580709c4070700c140c0c071444100a000074041801406064010310441c100c0d980c0c98500000c6054440c4042801c680554001504002c00d00d43d8410842d0b600450054821403014001d010244100c80080d42d603025400919160b030004c0c5081040c0b0034400d602c03440e041c207203500003400b01c0d040c0201004050030840c060141418000b21460210500c00205101070b80d8840590001801e00503580c50001c1120508107010140c98020035400f40e500c6020b4240a1409002c4e82104002e540f80352008440c00c40b18035200c040b5080c0041d01c0079a03002410350303d01881e922400701e40e000704040100c07554818a10000c02162801c800014000c0d40b00e01c115104107004180c0e020911030060054030b001c01d400000a500c20314884c0e040c1c20b40d00b007101c0031800d40d88041c0100c1c1c1c06c00302c0700e6440070140d800486240c480c26018100f0450700d4a0018100340c0c110b984 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 112302715 1250 112301465 112301477
    0xc090301151a3910090311030901090b0f0412110a0e010b03040b04030e130605030c0105071e051504050c150a020a0611130914010501170f06030114070c12 68
    0x980f0650001c0c07140039038116002040d01c50100c81d40300c85030309103a100340e482c5041615045459411103000400014400360300240014641c45502e803000012940d040750142c65042249140c071800755043e500c24401c6460a02044c840041d541940a04855185204010421051002c2014041c504525620115a1300400c0c0b00400c032917943c100c12030350450703009081c04d0720350b0741c40c1d04040d240030036564a51900460009884444c0c00c0030340d44200181c500840070741e81e0400e80d10004581034020080042d00c0e101c0000d1452640701d80302131004014038401c005580c2142010300301c030514a03004031000d9440390090042c0302c00900c1d140c82101503d2502c61909814403484c070320001d54400ca6604000d02d45a0350794400c0f032000300010291451000b01038244221252a481a1806400251686c0d20700c0205000082503540c0100032252000030f001411a41b69907031940c102d000000040e000c260155030340d0549001e4185c58003080b0340705102c1902c0303103c80c0040c1442c1c80844000400f04080c10000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 112303965 1250 112302715 112302727
    0x1002091c030c060b18074806060308031014040203010b0708090f03030c070303120c021507030605090f07020607021b011d0405070e03100905030703080c090301151a 72
    0x904a0040108070f078100e00700244030b041c81004100321100f04419001d10000800c204004254401c0c94403602102490300d20410016001000101003111803000502c28110104040490340140c1e0900500d405648045002a41da8850707180c0c1c0d030f01c01c0c2d441e409007680b1400240700840c2205d81614034001c041c0c03421841d41d8035022031190540500c45005010310310018615402d40c1c6d4004540c0e940303070f000a042d00e50700c2e500e41d0381c1d00c0c1d603c0a1500c800c401090b20b0807510350041c040c6100b120b10381000740d0041c05801040140081140c10014000700915a4418022466851f07852406108a00e410401c0040f410306030f40c082c0c41c2c21401800c01045522502081071060141c1130304482d080c0080c284692031480c039880c180280000f4043e1641c1051602c02000840780d88182400320b40381c070590544101e84103c14258080d540c100303a015086910030440e200c0003d12800300e590740800c0000c0c1860a0054290000e400c0d6100b4500e001e040138a055001c3c00348032603043c031002d0401800b00c42076141007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 112305215 1250 112303965 112303967
    0x20a0914060f1c060b0c0c01030e06010306020f04091a130504022107050904051006050a030506011809050a240204050f0904050a050601030c06120e031e0c1002091c03 73
    0x11062074440c032409900850314003a200b4049001c44803c0c07000e500f043c450103444010509030780c1c01c401c0c0c80c028984141400c50926500a2250000203c1094090b16080e8215280c080c0a540701140003040075008000004a0302c2c0c552007014904120229050f410060100801c00c08208040d900d2144a203428140801039a5a00c000e8000c201c0065040000144d8190741030308019803540a540c01103002400c04c010088041086060041c0c0310000f0881103444074240a008030042c0001040755200380014040d40402c00308103011407066400204542e0030a40d5042c1c284004c07844100c60518403c03441d10010305201412a1075040c034800c0850400740380c6800203440c46040e100040c06082814082814081e05200701504250402c0c100d804659480c41d00c3d8185000e20300c12100003c5400b9800382c810081802440c0f452032f1010001d41c24003c6151001207118545407181020701000c014150303042c0801d011840ca0011038840050320749400c2c80a110f030303000212040311554074559100000103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 112306465 1250 112305215 112305217
    0x236010602030a1d10030914060105010c0b0603120d020703020601090b0d020402071502040803030702120304030e1207050a1401020c0301021615020906030f0a0b0406030506071b15020a091406 84
    0x107040d1450300c0381c2c0c0ca454030044c040c107543c4034500c1c683d0050b4041c0b410340c0400f5050713000303442e005104c2d4003a284080490741c070407501c0348805c2c0510750000360407140c00d0000c1070825408640181d401025034501e8800c60110b5000f991001040340c0390f80350046003070401e068041c400f00c2d0040031400010b001104400000680700080d10400038851640403403c0001c2c003910420b415444d4a1500b41103580c1c40d290b0044695940080310404014403e5800408003214414180ca02032541611452511030740e0380f007049440c511030000036030240305100d000510355035075005101c020002c0407041c501c2c01199000081c240114102c90307070300907801045032076012844207214443c0755401002840f0140c4000d904140a403040044182d4880ca02005200003284107600c414028079000d0001c001400d1400180420b0303c00511000c0c04e56048000000e000c076006450741c0c21505c1324034030403450140d030f0342c1d503a10941001034180d41341d5541d004c20001c040c00d0704000b507080a040303c2450318000c0b020310703000038041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 112307715 1250 112306465 112306477
    0x80f1015110c0a080a020a06021605040f020702130204090605090c0d0e1903081e040b06010e0d0b010906030c1e090c0c12030c03050a2309030403023601060203 70
    0x1003000d081d2054200c91024011459084001003600700c509503120b07032441e0b80714102070060384103c0d1108800152280009081e0a0040c0c648500b030103014035080c2080010300d00b951800312542e0702009842c0050b5250303000145008109940103031902d0510544a0403503010703400c89800b41413071205210700c44401c1420b071220700c0b01c2c110010801406280c400e03414420b054801c401e1403c0740e0450304042541100403288620b642d038a25859401d015030000e60f0b2024103450151881094074046840c03940314002c5e012451401424445201040760350310030300904241e000340106070340d0b080d06004100342d0140013401480c5409a5045c00e0151a0700b19011080c2da1064544040d07a034440401c5040c0100c514540340e80c2c2140340125181201400500900340b40d4070314100207442c040018061241b2441402c441d00d5100d05000340340381042007144000c4202400000151200303000000060351440c8585100e40910015100d1100240200381d82c0010710001d0802444001c80050006540c00815524 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 112308965 1250 112307715 112307717
    0xf09020d12031b020d020607080c0d05060103060f091b0309020102060106030e0c0405010801051801111c09140d0e0607030e0f0d05030c0c011403091f1b080f1015 71
    0x30025101507030507401031843d16a4070680d915000003105803030b9000b04d04004201d034140c0070b031031040c3e0b11403100f11441407003145c03070110f01c10307080c04914a10b640e5544035560010b0706050001d50f05480701070706042c0707000c0d40d8000310a07540c40e100c44441d002101c00144901500608051048050650000c0d483d404140a40c078105551400350b02c0e0f0b1040e0410150f0b2a03054054000c100703d5868528050103002c0448480844c08615911185d4164051003a4095444071418503818580c40c0750640100c0100100c091900760b4030340d490000890150488070861010440007040380e01c040400c054203100911301d07a117200c1d0b2404d004480209030407200b213907001281225000e09000000c800602002200c00d4040c4c114030010840034214000048c0d80012000d00340c0300d031105000c2420480c006817000300c2d45407030a0303003020650042e088203e05881a500071600f43c0814007405582800401c0d60040b014080000c20380c03000c1c81030390a9124105a08031520220204c651410405190980e00030704403c14 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 112310215 1250 112308965 112308983
    0x90b030c0613052202030703020301150c03021b0402040807120b130b0406110c010603033b0d0519030305010f050306070206010311030a050f07090510080a08090402090d060f0f09020d 80
    0x7400041d403918050161144c0340000c5440c0e04001c507000b00250000d00030040e1500b500e0354810201c2c4d000e20550442c10340d05500801c007800f451070f001d01c1005c00e0f00751444c1e002038003803001260380d10051210b10f005d0507500002080e46002420039034044140a0148081000b002d036180b00890b00e004511544190400310100700c1e05d04006090702540703d01c8039414600e51030700602008151348542050840780503a03c0703030710080c601410f0240100910800030860403c0e0300c4030341c0310702c0d007003c4201404143c003c03416036141560402c1c1100c42040d5106048000030b64890060080d03007010b4030003e02401d01640245503034584100042c0d544c1c2c01c10700014001c2c6000303403c4d41400799000c20001c03401c079901c0000c0e80c2303a08000050190b554040342c000c0e08a407600303000c002540108100703030490484003008003d05031515591070301c9009501c00581c458006800300080400d60310b4040e5440b0391184107090000d8011042650602218102801400b0700c81c1003008204c0980d585201c903c9a03507030804185 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 112311465 1250 112310215 112310239
    0x50108090309060f07021c060c1d04050405070b030109060609170a03120204150201050405010f020901090e0601031d0f0d08280b03060705070c050907051b070b04090b030c061305 78
    0x1071454005d42c20700070362009401d61020300e43d61000380c0002000e807003a00103119002e0007040648000400c0040c2d12128000d2183e031519926168102d640c03c540a07009462440e52074a000d80c40e2613000341c011404864441c5020441c16030712048580003889140c20b042200c06d0084420380d240c0d08503d20240402000c45288009000303d6411280100700e1144105120781d4600c0c00a070190504440680301c0e0751030f00c09500c0c45000c441c02100d04004050390740c203012a0070108011340d850750240041b030400d962910501c072902e1000014650140b03080c0000c0c0300404000010030314101c400c0301613108200b003000a10240c28940c2c4007112480d0480c00700300d92001d5080c0c040c1b00041c248040d43c2c0380e0500c03404080c400b20b076402c00020401c25010301e400c0b1610907224418000f1015003583c5840000303200700130600420f8294000d64214540d640103554085654070007011458001d07401c040c1501e5580d0200c2c44061030700304040301043c5420b81c0c21a04040181d9008440e400b2180305080c00b4506815407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 112312715 1250 112311465 112311487
    0x70b01140a170c01021603020a06111f0e0c0103090803070c150f1401090b0303070605041401050408040612050c030411031501091a0f03060a150b121005010809030906 73
    0x4040500401072080d141d0071003480b02076558030b01600580740503000c0c007407020400c601034a007103109132a0090100d00a0920303001e801c640c5183c0304e810040b814040c2c00503100c06071000e4022140c00c240407410104d041d0102000c01402d01d01c09404841c103061801e8407050001b0310800640380e214599050484c00c0c680241415192101c60001c40703941c41c2d16181d9141c03035120300343e4040075448184075401c054507a00d80c410f0300d044800440c0200d6055005000f55000582d0030741025921601c0380721480b01022018041a081d80e106590441d20000c0c013003000d00503242c0c0081e142201310100482801141888d4100c0000c0f40310282c809014504c1c00b00c02140d8688003080804403010140810100540c0d440c61414010069100b0303028200400320042c0c007a82c0350154002a00c00c01c024081c040c42d40341c09040000070a122420f40360301c0100c1120025040d800da1014146280d0704a120b40103500d1722008499055804d81c210034180110700050109001c1e0020a40301c01d07500507108140d450b00d503244 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 112313965 1250 112312715 112312729
    0xf1608060a030807051507020a0b04080304030c050114010e0606070c050d03230403020a05010e130e0c030a030509240301060c03050f0a02010c0305010515160c0306050c041a070b0114 80
    0x39001100004404003080000190070721b4084041c807200d5200d4031a03810403a02d40307003c4000600020640000b05000c10448070086030458030a08140c10001782d5a85d070142981c0300d0aa04007502810308004000803100c03d110356034400402c4032140d00e052299610800d0f201d6840c0121030190200f810700d00101800754112014443d5400855015008900400c113015405400100e0007030700c03841000a920350040c8105080c00d0001095034440521520030b060042c26400800b507410302c28410340c2c0c0c00350749042c4890301501c0d009949060b0741d8242c05050100f2144a400521016050142c0c4580b4605da4101624191106850f021112081a04007220316000d552181e80408200140c3c152070030b03030150b10201844c40540c4052080ba0382c0c81d4201301c005e900417014403400020401003140e504d006030592a540d07038030400d00d9110321600d036116082102c0003103d45c0240c0303460004050010003040c405a03032909600328a10381c074200b115561152102d81c1881110700c12001e12400d11100e5072604 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 112315215 1250 112313965 112313969
    0xa0602030408090607140f28050a02040608070e0c0403081902070f0e0a15050102070510050f0a0302070b010f0501020c100c050a0b010609050102070f1e1a070b0f1608060a 75
    0x501e8140c03074049500b0084580f11344031145014a1087d404541d410900c0803c880300e80e0840249142001c40c00503650000c0d5104441c8d048900b4061081d0b04130041c4e40380e01c1814050100b0368010020700d4148040d210700c40d60007500109041009000420001b40100210b95100040b40e42648408841110507450000c481d001501c947d01d4910000c41c014190852051044116400a12007109213208001480c01c07107028960050304184400d00c0103041c40b00591003990940e1900920385506c1050714003068101140e0140080c0e00002c49406204100d010304e0f01401000d50355610300c500d01b80010f0350303540e00112124000c446494000808500031600c240081340c22000f55000c50300246815034004000340501c6001c80d48018010a56500c00a2000143c07014100c016000754203040c1036031801c415865400681c20482036001c00c0701c0c40e10740c0c25860300e040000501500c030f00040c90a1429840300501c1d02d200107130088100025001e90020580c09038965041051043d2202d8000c80c8580713000d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 112316465 1250 112315215 112315219
    0x10501051612020c09160801051203070b09070512030a020a020f0616050d11010606080a0518030a0e04110702010503041502041502060f0702060c04030b06041d0d030c030e0a060203040809 82
    0x10841c55189980201e401201643c045505c4c20341d076a01c01540b82c02241001002e400002e01d400014040d5080c0a006044005425000c80c5c0c24006035503039550303011034126030350001d0390803203042084182424103059189810703500c0070310300305080810025699a800c15000e4841d003007070032403084a512004110b40450700a00d202c02c1c11042c4904003240d8513100251640001190300b00040c40f6150107126440a5481c640e0faa036250b600c9080e0701030094080070b01201d00034612402602a002e104000805401402e5100d04041b18200340070402150012148044010b4080081200503a0b11008407540681c1c0880103100000703031580e20400074041c540200440a070f5444841d0281070700040d009218007403503000d2449a80d00d2840c1240c40340016203984801060501c420f2001a11201c031071580003001900009800c0902440500c207000489000005900160b4211083c603602d4018480340c900242811303c40c090180313501d0380d0b4950742d240c2e0281c041c030740c08804141000310802c22540c2240c80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 112317715 1250 112316465 112316483
    0x1f0c030605100e0a050402030106200c0904030c0c060f052a100f060f081218060304030504030b090607020706050a0e090103050d11010506061b191104060515030105010516 75
    0x20000241c828240900c042d44034240c2c4007000105d501d0a4000c40341640c11aa9408043d0358008080414481e542d0354030b521980160030308640d0715141d00940c03d00c1a802551042c40714412406c12070400307681358204100700041d001120001c5504041112400c0c602c2090642c00854005620a8220001c807501171040c010220300020b421856004909212081603003001080e1782c2c1c454030171b43e1000d980300d2a00c0030341060100f40844181c0402410700d14041c511110300b450514000508242d104603006c4012646c0424107006001c605500c2c1a4484a60b070010a113a06003860080d6a456080c440c0c0000c0220000341841d40358450b4604180d6604003502c1d45807156104e15025890744013520084d40045e150000140100300140550f900920018040d103191201c000c21407414841890010103540c07281203424001031060f0035100035280c1c0200c2c081d000c610596000c020503280300e40c0c88203100e00c0d4402c4164940000c608205c0e4115042420321954403062140720700780761800402c01030a5200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 112318965 1250 112317715 112317739
    0xb0a12050f090c0108151c0807030f120506090c0d15080d180308070f1106070507150905090a020d0902030d050c0105010603020f0912030d0905150106021f0c030605 72
    0x122140381607008980e800c2c1514899440784004440c0c629049034070010701c401526010315a801c14501c10008541e0240801200f00d010b503c5034130003a0700054048001a0034100c3c075103035407540170604613110403086500748220300707241001642d4140003600855001c040040d41c0035505226a2254101780910b00d450182c0641c1e401e0f102d503c0741054407504020400d40460510810b2440d603510040d280d0140d0281e080c401e003500c69018082000808031001e010100407150360b5504d0002408a46d442000242020750401c030700e40c440c2d075140180107018041001c2d0244890b545101616520002d5208010b0300c900100040501602e20604080d4050103580c178103080f0300303900c0700c000d01c01d600d40600240400d90360380c0d40032022882504207201ca40070b42400180c02e1450900701c600010000141100d080142d99141602154001c0c00100c58651019107000000c50500b4501c0c0e00600d41030019041c0707840140561111001040514a4220740d540152007056002e036004401400c00a0401c8003544 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 112320215 1250 112318965 112318981
    0x705041409070602030a0503010303051c060b07060c02030a1209050c0901060503040b22081e040906030302150606040e04050304270f0b10050f0906070302240405070b0a1205 76
    0x1001640c842500d800b0380080800e140f8000800c0341c080d0031081c3d903828596880c54808550036000300d000c2d20030180f03000f10341020b615039602503030000d401d01a2145988104502c0c3c0380e8112400e4900503000c3d508103100c1403040d80d40040c0d003400090565500420003290f1480d20504048101075612390241e503d00000c203841398001c0280d807195204044284154540c1c1e03028071090704800380400642c0300100c0058000418060180400603100d1184c42c8000081221890213900b282e003150607056a901810401c0c91350403c034080680c0c002c001081540d00781900800d1141c462800b0700928000d80b0300c042001c01004004a900520015134620000300c4d01b030000c403c42d0b9056440082c096424446030000c10300300c2d841000c0304c1c214002d01442c295040381c0c6003522290010360780c850700c0010602c00c510039500e51303000034920306100f540500111001c860460400400c01050317102104101d504010000d900040c1c070780180e0302d041001640318203011008440c5000c850000315001400c0005001c1c07c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 112321465 1250 112320215 112320251
    0x40c03020c190f0f15050a0b03070b030c03040f0201090803030a0504030e0f010804060b06070501061d011e0501030902060c0a0b07020c06070c0b0304060207122a110909070504 77
    0x2200700384256203121104a00303a41c0049812a4090051480c4210340c00004200c20681c4200a104185070811003101c10700b944121101100d600700000e440f06041603c519081c8191005041e80e43d9001d415030400b4004002d15000050000300324608022001003968002c4003c2e0005100c0c8408481d92454400700880c06044141c4048010a0010544400300c0c601641250443d100680d40d41e101941c0b00d031164800b800d101110305800040800280300426800c3c01a480500700ca0b404010f0b101442038201642500145e01042484100d41045100c510707003406100110b44d824031307010070145214000910148a900b00415461040d200ba8800700000d0b40c01240c450b00e5941c080d28800b45c24481840a81d10031b410000b40784140000c000e115034000710020b55000b501502005060980700c0c2c0d20302c03807014a10501d034004030703254500c070030b04d50200803090f2403250341d40c0c45007001d000501e030b07584144d0900840100d5205404120008103610000c1104400405001300b09100920b403506040401d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 112322715 1250 112321465 112321477
    0xe2104030206130e070806031515030706110d05030618060103020f18040c030203060f2205041506050d0f080a1103031e13020d14070f091a0103050103031d0f040c0302 73
    0x1159005130010351464040e241c094401e0b00c4c06405000924090b501148541ba4000d080c80002801648004103649040011401800c003680b9421303150b03a1122107035807500c0c0d485806e26081020030000c210154440034807801c2d6013103040c2100340041d02c8500060700640038400c008400303080c002c0b840c41404800d04128450700d28081d902001103020801003103090b07100c02c550390380d00004c0d038404a0300c1500b4407412144211003400120111500c600b003829094074025075069078454a07801580e100e000051203208000c1004036003500c8084d0081d982d2881d070b0119484060a1950045031035031040d8054080d0795400c1e82c65a040d00c1c0d8a14003a41c4400b003034217000ca42031024108900c00a0380c01041039040c2e890241d001440707822503001940d1141c4c01c01c031504107118001d0140d02c100140486904405101500403c4004600702d20312007111a504981d54429030b04141c03c0c60010400320760003224100314050188082200c0300d4800d40810b400720003100d0141d4000c2e14003e007818140b90316a0182003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 112323965 1250 112322715 112322729
    0x70e030601081603020d11130c08060a050901051507020409030201060e0906010f03060203070507020a0902041a03040b1b0d020301241e050919080105060f100f0c021f08040c090e210403020613 84
    0x41c2c0d9403510810b12330001054040c09400c6849000103000600d00703500080040c49030045011b14060346640490295040800102d0142c0e450380c00c144081c0c12186040341c0e1020013000140038640c94110810380ba4031561001902c0a90300101080607075118508544965801070420420740781e44550f0349009500074410204040c000347d41110103100d841044a0199803c101ca05500d522015200e00c0002903148800c1082c8208000540c1301c8070090010318000e120079201940d00c0301c40b003890f0781d40c03c502c4440240308003d42603030104084000c0c0501c0e0070b00207580f89451502d50400001054104203400c048880681c2c01081c0001d9043c415005103100b040180c5a00c410000400207109284104000140124009400506a49100d44401903403240000c029401e2151100500d07444050402400b4000600480420043c424520a09801440304000401c0f92284e54441c07561182c0307c003502e034095202450b80c0d0424554505d41510090f54005008540e40e4030b102e070382c01c0b030304103954031800c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 112325215 1250 112323965 112323977
    0x908031318021c0b0303040e040b240904030c020a05150910050a020a030507020d080c15060f1c322e23070e030601081603020d11130c 59
    0x5401030580b4000e40d0403a500216003801d0801c0c401c000340002e08603180c01242c05101c1404005480300c454254035000f140607107204015800c14008207510741e105040880d81008181d0400f51007600c8408032181e01c44c2d01442c00361030200ca0f610000308415229800a03174414009018031500440901c0201000d660480b042d00500074882da00b0390307850144460080150700440e20b208040b81c06403005040f89403000700215180c1410b940c4100040d00151807108680e4001030054051401c030a103c1e80e089441111040311581c22000001ca03500020b05110f0501c4030300c100c5001c10061f10344200e0035000840394521900185094441282800c165403004080c03003400340085562000c5038010420310118880035039184130f61415400908201c01088142054080d80d0490980d15000000d00800183c1d5525042101c094201444c1c008103801582d02c0b80c00080641940c1c44a102e481d10490381e040d1500c40c2901070500b0102c104039409003d040d0402d160740c076541d100c0551030b80044400c03c22500d0301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 112326465 1250 112325215 112325249
    0x905010e01151d1609050607060b041d07050d020d060c0c0507090903021005041b060203040501030605042f190504090c1d040b0307030606120c0e04120c0309080313 72
    0x500c580c01c80f07003084000c008190402181c1d0039007021001c110480c20f142460391905903500f010030640c3d8001d500a50720165944501382e01031278240501c2d0341c0d0b2001c1c540c0404403c01158002c5440e103225105e0148503400b80d040c00821903c60460150f40300ea00280c0030407981d801c10314051b1101c0c41c5400211400d0003030b6200031540ca0f51510900c41c00d290035600928034480c0100d01e50b8000d02c00a00241c4140c000c400441a00c480784800c4e4001802450780074540351460000050152025608954030907400c0102501800440e019a4144203010319400f8403030170705060101140e4411020b82d250a401102103c040c0f20350464000e004640d4400000c110400d01b240302114905208514069030b180d0000500e212403419401000d4076440050030b07604420359954618003114955844000c02842e0030300d140081c04860b9900c01d00034031491614031600d20f000d51b0707815010303503102121070107100304640508107040c4140085000303403500d0030481c0d41c0c0741c040180d058620074a078429a260a2054040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 112327715 1250 112326465 112326479
    0x207090f1e061419061b0b09010c08010807050d0204020304060204030c060924020a0b0606040915080c030604080f030a090b040609060f18020103020f0c0105040c030b090c01080a02030a0905010e0115 87
    0x4a40c44404810013090240e040c00021a6441c1c4040031124a040112145501090f5441c1e0780a0007018080000501c16084d41300180c50a14140c1c044002600042e07001c105c84e486041d40d0803141c030b41c11a401030b0f41c1c0d915407030f00100030b000c3c681028040c01c0f801c0c034000c190030307030044d85e80c00c180c542401e0b010580001807801604050360000b80d440050300500407180c00140c1d81c4000b070f40c020400422050425850300c6501040310b81003031030014400d0365020104102d030424040f80400d84020340192080386401d0b2070318401031180d0f0307517081500080000003e003552455403000da00164803c0465605007000d0a248010b0b010107141030314210f113030030030b0b80480b81c0709403007204a00401c480041000401c80d400541c001d4000e03a0f02000600300411100300303140d030284280da02c00c500ca142c00a81250850600e01d84021000b88808025444104840034903a0000109a40003d6400700175070741e540d030000300c1c802921540c00c0041456080c65a0351a859106400c10150414205050004107a036011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 112328965 1250 112327715 112327729
    0x60b030403080a15150c12031d070f170109020312040608060f1f020102040806041212020f04030611070c0e060f0405060907180308041d0f06010207090f1e0614 70
    0x703d0421103441344c6001c00801801600c64070804070282441c0c0c0c20004141c440b01d50750449400200002940c4206102e10b01e80280c00a2940024610040110504107211090922402e024680d800e04a9881c1460a50003d4104006556018080e25696280030180480c03580040c000c450110b00100c00040090a04201c3d0a420080c0280540801178414411080b60808104101d00f1035400304800b02e40f40408015060080e849241c41c0c6100710a02c0500a04a00c002a00c03003168900422552644008400a41d000c0e40d80203040050003d0650314001302d14401e18100925442082100140c41188010002c1c4255000c1d91000c031450640010841192001ca48007540007450901140c4400e1191441d40c0400318214441c001c0103480351a1400ca50f007280c0c1c00b20440881030726400341c1c80103003140025040440c2c0e0483c1c1c8507505040e00081d4072501140070319010550b0360380c2100b41c01845500180150b5003450704616502e8940206040604481d0042510002d948140c80000f420955 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 112330215 1250 112328965 112328981
    0xa0810080f012c0c13060306020c0307051207030e0603070504080f0d1101060e0f09070b1206030c0103050411040c2a02030c060906041a19080a0b0901150e0310060b030403080a 77
    0x81c04130341122604100ea03240782c1c0c40c81141543c0d80c8660100024a00c1d1004240c1c21a101d4011511507002c0d1504a182400500310003040c0303c428082c880000b43c10140306203110070200c843c42c3d03caa07100340c0c0403544da0045600000c00c6108400e42c40542c0e1001090f40b03801c44c0340e00d641c0c8801480d519040c15082c0d0b40c00748250310b400525600003076013142c100c601c2c90340c100c0b90780b0040e20407060799038851241c15085178000c2c960301c54030300080c00101d1500308103148203070343c082c02d040c019881c045d20795808440100300d03524001c0d921504010307015031080405000d100302001c155029040c403010400390014051038224040d204120140e299464244152254114000c00b100d14103410401000c00c4c032200e61001c0d10200900b40031a404005024844201413079007030f80d540b900340c903000d03209505031109000342c5801400008014405051403160851001c80309040290300c180d05d400209240c07031f5201e810340d6002807419901240185000009602a80c042d985012582d04d541c41018200c132804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 112331465 1250 112330215 112330301
    0xc0312080a1b0e0f1005030f01050306040f0303020a020a060507050408061e0105010c0303090807111009080309010f26010614030106090302120a0f08031012080a0810080f01 76
    0x164010400a407041418103d1040d003d4000c814250140c1302198599501c3e06041d00420b10100070020109100401e5500600b021002071006080c29201c00400e10700041003d410507400080c1d030803406008000326003040307501c03e404029900d04108000e0540d04140075035001da0090101141a080f031098040d4544007119140105991074440151110a0604c1d03045041c1502c64641001282500307000c1c00c6d181d07010310101041c480c08001009030680390782130301000b84071f1046d0b41444a00800801e8071410705080c00c2154420140c8503082d2801c8007440848409003050b100800402480140c03200d04903021070300d910140710841c070300110070b85c042400f5a00006034180010805898005154514440c041c810307101000d050740c842c503050005412040d58220000401c0c450003035000c0c072291004041c0c000c0d1340401c520700c5075615041846484a071f00c0812451101050451704007808000091a400084031360b1901044d5215002e001c03001c01c1c2d9914860960000d4011880169011003003c1e05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 112332715 1250 112331465 112331501
    0x1020d030e0c0904050a1406040201030c030c02060c180406080d0e010f0f0815030a0f0507050a0b04030f0501060b030a0b01180b12070e1c021302130306090501090c0312080a 76
    0x2c0704042c0103041c0740090043e981c40c401c021100021400040802c2c5002ca20071014080b40d140500002d01a1074a00040c01c04052418003869560f5502285c6281c1151001c0701c4140d81d40b40d02c00d051000150980780c403680c880c2c5000340002d0221400105000d480d080c980303592038501c0850006444c07140c0381041d0304012600049040d2140c41c400c0c91003590000446c8a440b08051040300484c5c0352a21564040f130313000c6169085141402000c0140c0d400602003241e803070a825041003c0340c482070195200c0100080032602101d02001803c3d041200074110609100e5140d18022100c440a4800c0d5952140443d00510b84500d146149000441c2565100110b13240b034003000c07007225248072030002c11010800072801d141600070350301e084011001b440300580c001566070b4079004202d05a910710444992007481040320700c00c8481c0d18502c00e07080304d4001c10001501a403a0500ba40034089102c40201086003203e0007008120b00c140101e41c0410740c1d0740d25519a0b41d00e08220000722aa4004242e111082c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 112333965 1250 112332715 112332733
    0x9030f0503060a170303040b150d0809030102070614010e0c04060e09060a0b030a0e060108030301081504030210060b03180c1c0305040503070801020903100902090105150c120901020d030e 82
    0x101500007180c11890180ca100c0b00b003079507180780c0805485842541800c0740c00010074030007404811010300350011405510301856001c2200081c460b24841c8a001b09200001302d08a44143c0e402c0d03040da1401034000340d060201a031a210718a503100d009004503072030590300701e000c1200241e04070240d5050351021b4a4040581c40d6000c200000e003d00200320030b50003c0741402c045101ca00d0100a10300584a81c040800c140320040546401c2040507080800594010720042010300e900040d44a150301c13103c1e42c100a6078840d0b040803402e010360000300c50315050501c172000902c1c0d0b8841009512a21081200240c01c40458801075111020503180310f500c0a501d110b46005581b4400b03460f12078034804e05106160a075035501290074212542d01c000c0103650f0200c2c00c0c011a08060001040300c9400010400002c00280d000031020306060045600038003803040039401d001c2040c41116168002081242d028100032141d0b2030342c503803000502c1380c010300806580380340c040e020b03002d149002c603850b07409804000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 112335215 1250 112333965 112333967
    0x11010b030c15090a060e011b050a08030702150411040513020a090b0402070519030314010b0a03020d020912060702070b0c0c0d03020a0209010806060f010f0806330301051309030f 78
    0x742c0d2804040090380c0041001d584070380e450200e103038024081a1100080c40d41c40c0800501403103180e01500145400292000340001c10101c0e84801d06940b2014031a103030340318408200d240c01105005000202448801e0206201620085200710902110180030541e1001e0394000e00914041c0001d400c02840b813402d0002c0c2d4200d400034002000007500060600c940d640300c0b94900600c4041e00c1480e401d1128080c0281503041c0101c840c0d9403059108009254502806062103100710300086082650200b001b0910400513011030f1030b040070003401c0c100e000d5580440c00340c40c0c110a42c0c401000d4400c014000a510494030706645100742c45001070103022000c601800421848483c1c120114041d041001c00103135100320b0524041e0440308010861032800310248460a6810540d4505102c880b880030311000e5030068032254068400d03556420300c039103000c0c1c0001c000407076807c003842520124030500d240c00e22120041d6040f240121034621b270720062040d1b510111043c20002800254820f50300402403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 112336465 1250 112335215 112335229
    0x303060d0602090a060c12050a050307081308030421030b03070311040b12030a020705030a080301030f030e13020d1104031e1406010303050901080f090616020f070609050111010b030c 80
    0x5000e0071001d45015421000507002c05a1600610081b0301c0d850a028103120141030703407001c51074083c204103140c1280428043c040d070100421400c1040300440020f990007035140d440c550300d030b58410f05043d180c0c00d052900c1d00c0700f41d074840400301e94541042007481c07800d0b1007400b0301021080054013810700f20342542c40f0f248129880c010619080340c0c40d8010400325882d0307010441840103100000c0d43d207801c0030920090400e001540818030076808001ea520104460b442102c0c11030f9800300c100046014240b9041e1038101c820070426611101c402ca1185400f81690010f210300c200708401000a0010096042201e001c2c602000e444501405508e080c0b14004a0f06118114044c580300c000341c0d00c2e40390f00585416000d81045000800204550501d0b5800c59103540d00883c03004925545d900d04024440d5881c3c00060002e106a80941d040520840c020b104040a00f40c19400b50342c500c64903860f006d48082d41c58400d260000b00190103d003444130042c42040000780d001009030004c25081c0c8204520 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 112337715 1250 112336465 112336489
    0x50f042a03020c100b130f090b04060b0f0316030605060118060201060f0e0411150f0d050115080702030f030601090b03090606090901020a0203070807030c0c0f0302040c11030306 78
    0x14201203080d602540110800042890314255a00969140c8020004604114001910602c007504000484910f0742d82e900020b200004802000200641200888000740c46040300140a03404044184000e000103a04001e98100094901c0f0a0091740d52050681d038140450090140e00d00f6a4420700006045800c540e4000105141090314001d00c4000c403050a10a50700910160703564090805c803503201200c240c001002c0f2410b009003546010349603500c65008888800c5d11608848030110048103165007a1a61000030024450303c0b2291188101d005040a00444144400040010048074812a1864420172050307000d107003880039a041004458101803da01d0600410003030202d0550b401c04c01861160125000030001d03070a00310b0a000d0300034000303040c1040c40d0740104003040100c1d400208590080e54006119517031541141021a800051840b006241080d45200019440e02c42060030003a03078000c680c10841d1414030042522902c4441d0003650b11a0021b00c001010f92a2203a101a8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 112338965 1250 112337715 112337741
    0x910060c0b0a0b03030408010614040b180910060e010305010b0306070507030305070909090303050709050105091e040f020a0903110901140603060109090f020a0e0901080c09090313030807020118050f04 88
    0x90400303c0140040d0a50304590024400ca03950381200300103001c41d8500d42032450f00185c1d410881c10340c4500c089a11300c90b45141c41d9403000000000714201c81c40c100603c0d900308880000030005103880f03100b540341e00c860030b2006a403290300700040540580780c0030075224011661510b45c0351500c500383da820f4000e844010401010311100b40e030b00049903881d6008400f05203100b581c0029962801a8010b000e02d035a03904240c3c1040424003000910352030f8080074260520784001e030812146540781c00900a42020b044da511482c1c004910400610381001c60f81d800c0c1c074424419018038050300c0f000d0288a000034858140c00220f4203500318140e00b080402940c00c444189441400701c3d4440b5070110680d012a03864000e0640d00082c0c504042c1d40c07050701c0070f8038103104072030002c91949040d042641c0c40300704802552144500768003140118034100116060a503103408042c05655490504403007a4000c008240d01080000b089525807280c0038514006840d801001d281e4007200d803105002c000c00f44070036031070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 112340215 1250 112338965 112338971
    0x10e0d0305070605040c05100c050d03020c030d1107050607030902060304031101090204240605030405031b031306020601031703060901060e030a140d111203040303020a0c021309020910060c0b0a 85
    0x4103d450040038420350140b209544094500401d00510800341c08003041009615000400099004121000e03410024503016031110510015203040d4401c01c00300000a5203008203210f00c0d00d107244c1c0a0410280550305580a640c0c84810a03000d580c104a4029070208040000500180c041c8055025003004e00c0300008880c581c95010600301c039249509800d40d4030318485501e00c114400d015403c0541300c0c0c5d142140c11814250756650341d0340550182c00c0c0d8009007012800c02110410401e0b5034400454018181c442541e80314080e441e140280030503512340b00034402c01440e519508080340d0041d240035002c2249a80780040445818540841c19030740360046203242804908552595115217070b0341d20150010905400300a8841101c8a80b408503e03007090600e02240300030481600d5009816040160b030b5802d001d40d088445070301d207540c000d510070840d42e42c0c030281e0813059001082462084c0c81000b0603813a184590903c004061240e030f4001030321102031600068030030540f40c0c2c00100c00b00000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 112341465 1250 112340215 112340227
    0xd0f0905041505030d02010b061b0a120f0e0a0605030604150b0a0201020301230108010b220920040f05040207060e0703210e0a1e1a090f0609010e0d0305 67
    0x2002d5841c1032498094544400d4428071407480e09121418013940e1500081158102c4103010070010b01800c100561010100601c1014031602400031010903070780328400c480035801d01c4401810b00c1540e0740703217040010f8045018003824103114504500340c030010384a46042d5030b01d0104000140c402d0400304001074a0518000031800d140d41c0c09003c03d549141c00250b120341c10455010a44401304040302290346242c5072111459800012190550b0184a495a55412009040d140240101d40c103121118a802000203030b01c49079603ca0000d100c0c5419103a4450618820032a040340039034001c45004a80c015400c110b18070b0a03030b004100d00d40c0b050b0301c04100440c1c0c4115050904009910070f0750074a00603803460740c1c0f202e6001010f503403444890400c2d954240308071000c90820051400780020013044207001065043c840c0c507903c001030803d0040c0101e540742000c99240690001d56005010b0f0100c00b503841c243d4941001921140032045c0d5035030028248100c03c0040f011041001901407220404c46 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 112342715 1250 112341465 112341469
    0x1060212040b090102100f1e0213060c0f0503130311090f0711070f120327050103020307020c0915100e030c0609060c01020f1b0a0b0c030604060807080601090b010906020d0f0905 78
    0x100c1da4225a8400e000a41c1e034543c8d00321248050683c11070048507441003121310380d05403000c4580d20039605c05140c101c0d204019807408140c10000601c0191661101250426484551041d00000d8074840c0c00d041c1050400d1a00b0700c5110b81060394072001c01c407110170000303003158801c42d034013140c0c1c80c0c41c401111500d541d02e42a50702174008581040301c0b001d101da401881455001500058200c0f40c002c2c0500c0900420b403604c2d034801030355000d1a4105500040490340e024420015100703201002041441c2c3c41c24011505014100e118a41c1406901140c5111003414000d0782c0021003d07402034040d007005040c580400002d9445912480c0d030180040c040451109000d20180c024259803014899407a03610140c588040144075048415030790103641c000000a14621540380c00c211000d10240e200e07285c000c00034020b441c441e08022414400c8007000601c406d000030307070203049480707489040180031581c400445600185009040242cac3c03000c000c002826201e40440780050712941741c4a1076258403680 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 112343965 1250 112342715 112342721
    0x3032715041506080a03050702100e030f0a020f0301060806060d0602070b09060603010b0a031a040c09020f090405010501080403050304152c010b0301180212070b1201030b01060212040b09010210 85
    0x303420b403582201a145000d00c001e039031003040d0103051003100501e00003240355030007071403442400d41c000e011722611040d00c05400d008a12107030110a001b01690340e0200d0710000c544d6124408042644511100b0106250504040c8a94000d4903402700241882e0381d5048240000000d8880c0200c41c00c0368200a520080303044018424007c41030000544107070705014040500327441d025461288142a55101000016401203d03851800c0c071a508850035030795581015905950a58400c1d804035000007000c2c0d0212001d013006100301c0c0401c56040081c0e0342c840e40110b904880c1203900130007060041001c107010a14514803c0c060035010f15001c20f020a42c8901c0c01101509501903d81024140e0307070b5541a050f082c040d5194240c0150000c00030381580d1291040010b10341603000c1d0141008440a903501d40f41440000003500d18008816521205000c42a801400134031041d00c010300b04100206a01e0300c04542c0c80b0342c01c20101c0060b800c0031700303100041c007003030f4002d50803141503208210314418040e440d40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 112345215 1250 112343965 112343971
    0x1120b0603030919060801080d0e04090516080a150903050304031202070c0308040305011d0706030f0e030414030601240806040b090129070c060c0f06020f04060f0203032715 76
    0x74a800b0310605c2d20078040c09045040c3c11091854102d41100e01501d507000c0c0c7c00d0303034156504882c0410406c4241c00c1403400c10b600c00040403103950800310f000c6083d000006000d200184500c0c5002030641606d0b840001715481d00b0740050004104001280c04039115040402c821044403800500c2d0001958482c401245240e004540780840401c1c1001841000c0c8181144041c103030742c810702550020b480d0035482d8130088c000c80d8203043c1e54429902400e41c09034040082c0c0d03002c0f0720440740e44648440c40c078a030011110740c0c058402d2040700000b0071010b807070811351010303051040e0602c040000302d01025150000c0040c032503608260340f215500c280d0398940c040c443c020144c8947c0d0030f00480c210060540301d094100800d0714142010000c40d80026840c081c0c00c0f00f11542490003045800e0540390080921a003060042d2400b40049000032540d07070b482000340121000d545506516003c0b03003100b49d031203001c2113680011400c0d18034011224071181182c000c46042400098900d10310081d0880c0d00c9142c425 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 112346465 1250 112345215 112345249
    0x1121e05070e0601020c090103080a030e010203010f030501060522050a181a070e0d0b0a020c060106110c0904031707052101050411090a0312020102090a0b0310090501120b06030309 79
    0x100350400c42100d0b9600c605400c40000c0c4083c025005030100407031800c841c18400105042e50009a00e01c000f846540032480403036481c0002e55480d603440400d070a09500c01d000035505546026800151032510212030300f011107140c94400c5489a00c00960801800d00411511015854008141d002c5c10070300c1d4607080f0319100e01c2034145582030b441071103980000020946410b0011543e050318181d070b58444c0c120400ea610261032856079946452500c0a409590100c1e011131003044000f1400700e4000321015888006403040301c14041e078240030007100240544014000c514800200c8001c80600200d266122000e41481c6240c90004011540303a8242c800345006244103542c0107100618003405140700c807401d95482c070360504205070001703240b07040c1500c002019181403441c00c5083e24003e405803031201100a2031212001c0d580e0420303140c03940c03046614543c8581c4614002c1880c001c01c0c400c5a058601d00616141170010a0f134814082c900e01401c0c01e5410311043c010045a9955052000401140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 112347715 1250 112346465 112346473
    0x10090302010f0e060105010e0603041406040302030a080901060f1e0b03180c04061a0304050c0a0303050a03140106021b041d03040f080a02010f140706060603061703070203030301121e05 81
    0x20001414080300c40d00100f00315103820110042186070f91010340500f24010446030990780792542c0c50400581d105200c42d81c1c84900483c8104014580c0100151000d070046031984560382e910145000d0032a00039010b800079010144c501400140b00c41101c03242556043d074030b001e0b06161140c4d04000d07503801c12500c9224000102c4800c5240c01c030140213000080c501614203001c035604052600507084c00c00007010000ba140480050103000c0200a802420180a0320740c5a41c1910380c01e000b1f0440c0d10000f81c2c0f801003030900030355046030f0005030b050604948a613400341c0f03040003640d488a41d140e5044941c5690143d1107014600240d03808001c1e400b04400343c070b0001d5030368502c0c18414408250070303a400b00e40190400d111400150745c01c019480340152451801c0146c007580500720ba4804d0040c005c2c060001e0b0b180c044040b403695050707801042528481c3e0b0680312000008158240e407480784141c0290550000e00040180503070aa4603c0c507154401c00d406840013409042c08048458900400e076501d85c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 112348965 1250 112347715 112347731
    0x50f0d0501141315050d0c09090b06040c0c1203380103050702120405060d0204120609030207080d05070b13050a0308060906041a0f030c1309110901060207090c021009030201 76
    0x3d841c000c01d042c414900141401000280c601c9290f100c000761040740d0051181d40e018500b00000031032540e014004041c402c0010510604140309004012a103450140b4649008804401d000f403400710b0050f50b014151003030b60b4403280000c402410401d5540740034840c88011407200c00380325003500d20084041907041186410300b039000409490001c0e141c00d0070354108040c40390054043c1001c80f0140e60080d41d410f075817029803101020091140d40d000c28030465110400c0d0702004181d40210100f14003030760851b8492a2030b80c0b805901c40700344182103030104e0820072690700001c10140800da400316010048600d46031103510350a040440e060400c40000340400b007001010300d4484c1010380c10030b00c01d0b1000c000100f41d142e183c10000310700301d20980c86110340c400010801da504010500d085503024241e0b10f2391480c20300b05500a848814411501000340c080700101358104041401e040302c05a9005115052074420654003c0001c900250114000d11a0385007600209000e031a81d4244290300001d8001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 112350215 1250 112348965 112348969
    0x9040f14160b0726042102060307031e0204081f1404080a021209060f09040b0a150201050105030102030708040314090a03121803020a1a040e09062e0303050f0d050114 73
    0x2118030401c900c0456a6080c0d50700c180807640e0541c5c0940303608641c0c443e1201c002c040c4d030103400e8440c0e03000203501000c000304006030160b05401041c1e80c48585000225420b4000148000341d01a500540b03500c2d87c018040540c08504200c0c030788104c05410880012641305003042c280c0010000c9a058542c1c8400183d04e011080c1e040040b1307183e00c06d842c4049803c00b4141d000042c42c42c03241c64181d2009101c082031895259681c0c1d800148100401842d40c4102952003041c02e08500d034030100700f8099460b001c000a003c1c00c041c0201c0c0d1080308150740381917060f81c90356800e0307841181c211340141e400903050151041e1610342030110f90265010b43d0304c0c50900b40d9468030040c000328101201c01b0541030b55840401c01030310348a0624090360101e09014404120200300c10009010710341c0210103052541e002c7c0181c9031404980180540540075003640703902c0f064005141000c0015008001e001450441040030038400c10103003240000c141c05007807030051140010341c282c41c406c0c1c200c000c90101d400c130030003054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 112351465 1250 112350215 112350233
    0x13020c0714031504080304140c0405151002060105090f0721140117060408090f13151212080a0905030c070602160e130302030405060d05011409040f14160b07 69
    0x20503281d0b0f52100c030030700d400d6590355081d0101a0000700485542c1d101480d4842c001d0020440c007110203401008076107000c200e0b1003e00200740b0751090092105c82c4800058071703c0410560306903003014100704085c0e00c0d141080e401d100340c001d007444e08005120307690009201c00305912860b410900e2801003921040078860010780041039000070015505641d02d50614080403490383d0f48250000005611b421340e05021804174802c8405103540701107911252810618264041003c12031102038a052140d210030080d18000b4100101070407800140c21000a003502c50101c840d484000d40c240896041e0072640e604d0301c0d5802c882030503050358012002c10300c001e42e41044900a04086101441d80951410104002c55040038089403241e0030030b9006082414000c204840040c1070191565a841080074641c800030714007030058440c02c04815401c03070f1103441c04070f080030301440d003003151080b00101940d90503500004505003680305016850280440d4000c0d40348201c018103103c0c0040e59034403420f1400c0680 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 112352715 1250 112351465 112351483
    0x7030306031217040201030c0e0d0c08010501050a1a0c01061a0a0320070f140f0721080406030b0a05090702030c0c030d170c0f030726010506030613020c071403 70
    0x2001050640b50200c42d10f082c643c41c0d0040c1d0282000120402d000004942c000c0000030398a03040b0003e8248c000c01c0155560420040320314100081043d66242c4003000707540041031289066400da01e28400200300d07115802007003154510030001950954035510415009600000400684404100a03c46a415001c0c10601180003136a05584448540c1040018080e800d400b820b40da00400c000f00c100000d000c80302e11f180c07000c00304071414852008040d5598480d2030080c11015000c103500440310703000d4400340c0940c0707a0303010761000d042a00f4010110010700501184c9a0b20200c9542d000400780ca5a4444a0140c0c000da8003465403058080850351505034200f2a56000e43c0c048940e058000b540210361511020f040e01d5440704948a0701303034051040c0240226004580000001e0088154001c9100e03540d412442500304040040c0030042256078200341b0034140c01c00c000b000003440074505883ca050a1118000005090a403885549490000c1c0c5400100c400404240d81c0740944c50b0411010304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 112353965 1250 112352715 112352717
    0x905070305060a12060609020c071d0108100b0301021605010b041a0d0f05030d0f060e2d100807030605010e0112150f0b0907080f0c0903030f0901090506070303060312 73
    0x40c28001c1c0030860f4903030103120b00c2d40441c1031040704808100300781d0840b10041001440039510740040d0400d058036003a9900c290b580071000450300c2592001c480d45d03001d04903180000a411140400000e14000e440e82480795503140d5400c010096000c00d61f04250b5403a07501a03000010503595030410302007141c8424000040a00d03030f06406410a59405481c110075551101c1407c0c5422150f1070b00a2940c0141681020410b0410b1001e044901b0140c1c000e00032102200541c501c02e44034806800f0700300d424800c8121118020700b40401014070300ba051643c01030f00c00b190640020380e0703802c151814040140c02c01c840070380c0c07a94010800e2003e1040d0b000d0140c2080110f084006041c0ea46040c14103e020310200e807101d45500410000c40c0c060350016460704000fa1501c1518901040014840310085448000050030000814005000b01003540c0e000380e0050011441c04406001c0c0c1c0441c0d805c103005e06810400c101401040c6521100c02601c00184070b914085009400c0d86003d6106c07004050b0214 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 112355215 1250 112353965 112353971
    0x30f06150a091502190809041e140a0c02060601140405060a0509030d0504240e04140a05090313030807080f0a11071410050309010603050102041502010f0b010f0f090504110409050703 80
    0x54500041c04032159001d500c40802a601e5007c03001080240a80d1030051822101780300b0000c642d441e050b080710314000c664061012880d50340d040104102d139910106080181e2090000232550350180d131803281400e8401c280982800d03038400c006480390740260301c958006603004c82c44140d03074101009940581c070050b060090415040c51f203101c02d42c040000c0075414401168080a0806000c0d88442c02c0030000030b0f00a0024840c464210030340d8110031b842d0b200c0c075903140000040840c00007009465007032031400b09030200ca6246031205250381e0044c02044d100c10384200100d0003070300700030001400c8a030070750f0b01d0700c1c0410020011600e080101a50205148140c2c08041103220707520051495115015410002d44903124241503600401007904010900d610024020912030803540302d800c1d003191254001d1150b1040c40903114203885001ca43c69012800901854000c0c0d405041110101c061070310300407980e5039843c8006825500c0110040701008000501400700d5461030103850350144540c1070038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 112356465 1250 112355215 112355233
    0x1407080d240f05060406140d0209041a0f01090302150c011503050c0307080a1106070f050d02010b0a050303040e0106140c0106030c1d0f0109020f13030b0a05130503030f06150a091502 80
    0x1400b04c0e101180f000203648800500c01d0048d52141c3c1c140e40c1c607407030040c100b044118800d02c010f000e540400e00480c2c1c85110015910b0081e58420050030b4143c4e46c0c041e080340700341c3d21001c2c400c005d181c024030001240d954070b644a9940d058458104007004500850040480d60651800d06007424002d81100c1aaa004007812a0200300c103582c43c0e52504030296903c6036107080c942084c00c2900540d80004102c0e0140c6101c055a00754150040c03482500d0842e08941d020b551542010742d41c0c803840c82403181d490b14410040201c6070003461225402c2c10000840741c5040c070a80540340c00c48800760002c480d140904502440070521813850a440505224140500e90070802101120a00e0500c2809400f913000a1125110300c445000e81e680c0c200d842c00589061516071400c2001303110b045490010b04e03450440020580043e49440a100c260414055451500d41c2103046a0f911402000e15030048c5141c808411f002c40d12200030440c0540030b0381d03481c15040c20015000307460b001c032a5402045600c00046 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 112357715 1250 112356465 112356467
    0xc030f070b0a0b01110a170403020301020c0606010e03010b150703031e020309060709032307150e1504030b0a0905011b0201020703030605040b0a0b0304170c0f010c1407080d240f05060406 82
    0x100301d411f900114001000649a460120144a0754000030b416500104e03810f51401d500241b058010130b026201c0903d600d0f0740100b81402c0780c80d100340c0140e00040328145d4140ca06150f40091040d50701a2601040041e00d10043d4980c520841046580140d40001005260300c42402016084090340c0f515009091858a4162500350060b404080c3c240c0c0c010b40c482e00014013001100c004000300d0f0a03481954180820182440300c0c1c11509038003405600700c44044040c150000c0b501500d510088411003911345403004001044001000c582079981c81c118006404091101210300d034015500159440b0050300e001019508540d0159000390705001c101032280d0b45a191000507a1500088a81c1343c0e40d4500340944103000341f40d1681d0310350000046442c43c1c84408100d1104001740b0320000e000800d04c41e101251030749201d0086103030040b4103005c0c1800246840c80100140b01111101140c01c2607951036900b0548620180030300d441c00103c4080101c9030070700801000404048891030700741460118 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 112358965 1250 112357715 112357723
    0x506011701050f0d050f1506190611010f0f0605130501060f0c050106090606020319090b1b1c050d0c0206150418050a0303021305060304020f060c030f070b0a0b0111 72
    0xd42d0303110300c1c031284021074152544402d01e4200c54200040350001580c418416896022a0526960342007804000640c20708100d075402c80c1e45c024002240c00d105143c0390f002c944042c0c002440d00d146540302c05812800081f58015040d14018005000401d01c3c0361408112402d01540d007181101c504000041112542154103811a4080f901f0700142508041ca0f103a030040459801000803d458040046510759000020f0300310f80b440412405451001d061065404010f540704800a459042000c408070306084503e40c202100c0700706c00c84407044001691460b17603034a0032400b94001400400c0c1080d0303070243e40c0100210510140050f02da5414441c120420755800b02c0e01e198000c41e00c48510a01c1d0403002d407140c1c4100c50304141038844540341440c008002c0e40c0300600225002110000103c0ca81c44d20808890080e54005d0468505c0d030ba5041c14490f041d0095424a00c2901007400411001d401e01c1d0012300200744501c200c403980b8507100040b18100d45405000904110484610701203c102c005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 112360215 1250 112358965 112358969
    0x6090a1506030b012307050c0303030417070218070c03090506090901090b2106040204050f0c09011d060a020708191e022407020907020606030a0602030a0207020a0305060a0506011701 80
    0xb01d404100d001c2c43d4001601d2030034811591a420f031303d0740d0b480e08801150740006010700c2480741e0251662031580204143c0c0d00d00042d5401b41103243d1900e1040101c8944400a0000501c06091040301e10707040030a81301200e504445041c00710346100121410164000f001070040c00301203440c10b041c01020004503009a00501440c901c8c65913461004050b036440d207004004280d5290b0b84030502280d990420380c0c6500041e901240118108000301d9504840644080c0c41000101e012500b413416590044a40e12110f281c040d450200c40202c624003602c13880010032040c0d110f60014150030340b410109a1070906081e1601c1480040c44e0000c400103a912520413241c0400b07242034042e440700074000603041c4500b0250b03907109001e135849058000c018010203052583c0c000c03034042da0399580d1900281c1c7c541030112501079041c0c00c00c1d00020300003076080c0c2c042c1da0040300e01400181050020b601240132642d194100740d82c5079014404008a20318180034817540014281780924441c100449841c00c1c5007018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 112361465 1250 112360215 112360217
    0x90409020a0e100f1d130f03050d060b0f030406090f1b030209010e010807150210051e0f04050607120603120503010e07020f15040201171602070501020111190203070b01030b06090a1506 81
    0x21401144240540b10800c1b4003841d004210b44e03100008615018005610181d040300746581803880005240a100e02034400c240c0703806818600d544d4481e0b60706030080410a100321400304c0c40d001603c0210b503000c16180320310b81444000540ca141507004004203010140d0100d1048064a4014086000b001c240c0c00300b00e5180c0c0009039000c00210314160704106441c0940d000e03441c40e250400041740c00641c80a1020940d4040254141d180c00c10644c4003c002110040e00350790022000c158240e2140e03030400340b880c5441900143c041d40301e5071030b003510404203c186d00000e5000b00040c000d000006000070f401c11518001009001d9056000caa100c5004d074400302c4814507070b1800a41964042c81c0400c0c4a10700f03940c1044414507001d4040414040c032000b40070018400e14602140d15401481007c1a844020301418207029445520702850343c00045d10b5170840c0410300c6140b0020f2490340e100e5010b580714940100f0245006014082100b00080900c12118288030403420140c0c40d81078500291a12 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 112362715 1250 112361465 112361519
    0x1050a0e060a1502010603150207110108100f080109230c010804061b02010608010b0103151202180405060901050f0609070e010306081212010e011a090409020a0e100f 73
    0x5100002030120b541688640c2c4140c0c288048200b506506501100640e413007100208a03500240000c10128090301030020403041c4d00b82000d030441d40c051620305601c06042c62144004a480f04250306030481c0507885510702b40e4503003100c40c04111011820002854000302010140140e180408c0d075503a080202c4070703060095103400b1a003440807030b401038000c0a0185110b034a01c0910500700034000d10142c880c1e11400c0d464104800790a41c030900452038030307210700790031207029031b0901030b400703841400c0924102d0b806044c0d00c0611078192840e81d001c0c2d200c0e07402741028180503d01340c44841c0c00d50380001d0659414845200802c40950740300c2800c6c6070010802c2c91301c8020001c107500180c004210a400c00c180b58400c285402c500118150700030825290181d05800c031507684d5403c840038565080c0504000740100b440d07850030004400002c1d003502c00700100003180c0c801c0d158000c117a1082442d00003246004050040114902c68641c001d0018041403c000141c01e00d4001c1c0020a402c5440c11848500301c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 112363965 1250 112362715 112362721
    0x3020a0b0a0c110f21150c18030c03060f180a020d08130506030c1b0c0a0510140d0501030b160f0e0d060e01020408160e06061b120405031501050a0e 65
    0x142d00104c00d00040c0064001c05519150b400d40d180303000070040c0030107018881c408240d03086542020a550080085000341ca0810031030607810000c401e4100101d54052040d040074208550b4204000d500604000803c50300a041c042c0c1d403121404c07981140901c06030310100000300143c444507414940180c228003403075100c001007810755807034114540c811580711a02000b40310758451458014840b2880701c200d1082402c3d903861425882c3c280c038800c03065010b1807681003001182440e000d070600302880303442c1180000a005060002507007082101c40901692080103001b000840164160409500c4c68546001030000c80014909000303d0380034410845469120443c80d00c1e1030428000f29070b40850107110807404481000d00030b4000b4494005130381b140a0311914407551002c440020f0302c0c2c44400301c0500b5a984024080a5807201e44442c103286c08407040c0c0c43e14442c0030300900c415884c4148049a40d10316140405103801e900341603d2110b00c803d4801048903656980c0164100c0d00780f0080600139039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 112365215 1250 112363965 112363969
    0x3070909060509010e0c120702011e06030203060c28020a0b0f13021e090a05100f1a0906040302060c070317120a050a0207051903081e1503010f0603080403020a0b0a0c11 74
    0x201507c000c44150349070000c18030000039019042030035103031b14002440500002210b081ca09a42c0f180c0320183d00340d000000400d83d140300c000300130300308009a40c51070410b0011a42c40740f407154404450460040e00302c51000000c01650740b80389500082c00c3e04982805d400c1c00b0f83c4241000ca0340c024000e201c2c3e5652005501c80c81200110280e500e43c000342a492140f070f02d0b0000401600c1c0c21141440103555110010544030003101650040c1c8030b5088103050300c0c400c41200b00203264014805103a10140c24000000182c0e10080201500c0c181080030b0000c640c03451400da409025212005070159030103105800ca202054140a50300000360000418141c4420394150000e11a00002034941e024100080d07042a0b01e80c04c100383c1c401d1095403011415074a401c6a920802c1e8405ca06140c01300c0f03142c000c502c0707485840c1445000380710018000142d1281d041208000c603200742d8003c0307074242d40200e41001540f8007050300d440241950704400d4500845240014203040104200031310900d9903000c1c01c4429 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 112366465 1250 112365215 112365217
    0x507090627050d080705010b12060a0902030a0b01030303090318060215130f140709051012020102070801060f08120405030a080304080403050d05040819030f050915040b03070909060509010e0c 84
    0x4007000703007224501030f680d4240000160301144041c1d50560030b1160f12152800c00d20038130381ca03010510014108940f1a5032079503000c0c0810500031b0303074184290002000400c0c0d150b41d8040c000c41c401e072030028003a01e080c94042d18214010b59985800340020b502000181d80118070318195654070441c45107a40c0d40c00030103e2030006002e030043c0c1710b4030a450b070450821803a510031005110a50048406803503036489010107442c41155a21b0945510040400c0314102605100b4403d520500555800c1c985801c0c0503400c55540ba032050840c3d1003e42010882188144540d60140340392001c0c242c038003070500004c070f95103801910f00207242c00c000000003010301400a054801a40d80081502d03409031150a00402540041c0070f0358009020b01d62407014015814108003007003a42c55101d40c0050015100281c0d040c0c2c00100b040d9801c14541c000303040c2001072510007803002e02542205107489040040c0024a4006280c100312401c0c0c0c81d10b00c0621043d42c400416504507100c03032410301070503a07500005501e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 112367715 1250 112366465 112366469
    0x1e020a1a1309020a09080105010501120e01020c062703090303030403080c0c01021303060b041a0618060409140705030906060d0f06020706061802040501120b30010507090627 76
    0x1056106a40401c042c602e0381c0040840b902c1550b01e0f4060180c49800107802c031391080c811140400c800105001a40c0070541000b2202c0000b030000505203100c0075040e40c240725080b259440740004a2020080b0381d0800102c150410f84100001d5003001100804a503076480b024201505110907500040c80541c016400c5404003a03402c1c0096454031805601d40e05403840501044890a080602004160500d4450211540028220341c15041c5403041484030380d070b01803100311040320f09000b10111252500030042c00240300604000403900160040980d5441d0003400c4101040801c00900490034000202e56400c41d00c1215030300800d0203140380401300c4881e415002400b9070300100b074400034440598441d404840880d4040c500d18a07406071070f08100d02c0745004050103c0d0710003628841841242d804022210800317481c40301d1022401d115052385c64210040080c040f80c03034400351001c2c090280a2150421628144042c00c0d504000000d00308001d0041e43c410b403500201000c1c00c84a4020201d580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 112368965 1250 112367715 112367737
    0x30c06040303030f1116060b190308030402030f0f0601061d040615030506040605010f0c110418061a011b020d14160e010b04030b0c1c091e020a1a 64
    0x503950769a8680a8040e00744d00491003841e030310b400c1441c0c1c2401c000d1012100519507403074200a88544550716000103041ca03440e115040b074240d41b006201a420500c03100080c601031908140c40c1d250910405181c000100c80001d003942050300c41608075000090003505544850038003103506040c0d480c0000307038a40010084e903802424001d000400340340d01c072421b02140c4074507582805980c1d01c4100f440240c034924407500d40001c000070408901c1521501407018454071910804410300640000101543d200000c560f43c00001f0445060030480148124207045407005410031034003d200c80041d0075070303c03450220100c10310f01d140744000315034030210442d010551190310100d039800e07109411070352024183c00c1c0014110f04400003285074810f08008034102c42c612100745140074215560303241c08000292495031050014090701600c4841080c80c00b9460b0124000050f0050a07418101c820071081008440b11440d071220140150f241e01410b041955821404d20b500b0a004034982c007141c0c030409128403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 112370215 1250 112368965 112368967
    0x201180b0411030706050307050901090305120a0f090b120406231008031206060f0408070311130905060c0307180e040c0605041514040b0a18080d0c11030c06 69
    0x180811000994840c0a18080c0854485461051040c0750784c80e20207008039030115209100040c0002c1c0304ea002040c202e40189030040b6625070721382c0e50b2071034600c0e451080c24080e10042161141640c1c81824079585100b1481d040c6c02042c0341c54a02c914500c2030030116020003442c04005003d02c1b8054021300d15485004c842c4003200312440b070f0008c0e100603060700c250000c810350f42130000340c60000006817940e01408140440c502c0d11501c0c2082060f501c99601e01040e035006000020340008203000c0c910046010b0325042d21892010b008104654060400b07042c0d650b0314200d0303014042400014801e0703111404400d419600e0b240c0c40b20a40c0c0e04601c50305400e1301603071342900100b156484502c486002c0c2c1d21441804098a071594000c4d078060049001e00410902c401101c4502284900606102081d00c5017106180985494400449a00c80600c84000c02d202d20b4091001a0308016400020a0490040d03e0101a1000010203460010101919100080303468002c540c3d0103010000307417820020515 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 112371465 1250 112370215 112370261
    0x5070c0209100303030647031005010905010906080a090816060b03010b0301020c0a030e0103060b0f03060a0506031902180a15081003020907030905010b090106020a0516030317070201 80
    0x82071200940800c1300007078103190300050701140e180100c1440c07401281c805e03003da09070742149429404100c8010fa050000b104000c600040c040e030004d5020380940710301034504a04081c00545450419807155040103400030b0200039540d4004c0066810211031040400c1003581c03414034807039500902c0442415011003112240c1000f0007503009550014064000b8442019100201802c074000c4280e205810b40140f001540001d106803e801007030441418005585070f1201c429a0190300030b20001c0c1c8c8421000000c0c803080d0324000e48010010001190b9440c1b4500d0400c0040701c050b110b05644445207034000c504403200451442081f148207030042c2c074460001d691b0b204c18440b414841401d16010030550008160724600e44000e40042d650041c01900b8113440c2d00104400500d0240d909917840d55840e110200300395030f100c1405000f040b07164004c00b224015420100d060020b10300300b003942181091001c200194000841005000910b40c45001c02d80c0c0302103003a80580200c031a04682c0400180c60 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 112372715 1250 112371465 112371481
    0x1020406030b0a090603050d050d0f1b02060901090804050402090607120f090e0411060703030f05010b030105190806060d02060409020412120813020f040e0f011b0c0309030605070c0209 81
    0x88458008001c80b0b92035543c0e82c2d00c49112046039800d000103041904049022400e980c0110010038110316001c5000031001016640d0800300c1c1c0c5060341c04107510a513400c09508071036040007441d410411a60081100b01501d83e00e1b91054403551141501450700850f646040d560f801044c0c81e101900850b42603100425000001c00000c500d0000501007080b01c900414102d01002007503201e1548626001c44034170f0000708010242c0c100c0f09089040644803103a01d41100c03d6402030394000c0011011181c1c69504000400400890502d2900700c180c2907102c0400c00c8040c0001c400d90001011b55012418400c2400410003521458000840003400080c00040c2c62802854110f6194061800e4012a0401c0601241c0911007510540065a22840d009026284c28088122240f80040c8006a92010b292005040c020550a1a4026590f8088110610003070740d6500a40320003520b421108017150755005070421602c0c1c00042d00a5581c2c41c0014903190290b848040c1442e001042000245001d4038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 112373965 1250 112372715 112372721
    0x70e030105090c0301110a05031b0d2901020f19050a330603020906090919140607020a05030406050c12030a09110f2211070515070c08070b06120102040603 68
    0x10a01942c601480d240c0c5003800c200c2540e201c071401c0e98a051843e00c1d118040c0c160180c1d10100211410f6040020241c05c03100c0b8818450b552180509600c88030078040040001d2133a1008107905540120074100a15080450b4036141074542c040481110449420705514000224200070b140104026611603a80352840001c0525480e4140702c0288041c58440c03181a00d007213210094000582402280d180e24001c40c805034441009400c51b0b00b000c44000a0306581070b040d09054070070004004c100c0045040602082c3d03840b0941c0d00040034020459950b090782c034401c80c40344904000e03020640883d07881040c04101c2c0342c01103106443d81c03281032a16500c4000d103c0e4000864044800380c0d020059030400310340802514000400e4410f1408111b9902e180055007400400c003c190345251380402d0500e120040c00300c05024400030b200c1901c5010140b480724501614502c00c1c044100041400180150101e500c141da00490751032444c3c44103030100d0700041c40b650400f038203540081004070300664594 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 112375215 1250 112373965 112373983
    0xa020601080f0d0807030903140f130e0c1e0409050411031e100f0b03060708011d040b07030e010e06040318060801121103030409050c0307091401090509070e03010509 73
    0x40a40b491090b488521958403428034089501080d62035000588460095101145080c02403c2c00c0c0c000c840c1e01902140c5907070242c2008840020045145800c03440c00104080280039004102c5815044c0002840250700864800031050080e02c94220012205201510700800440d00284001d0915140507040c5082e11044140031b031090019501c2040c1c01d45003042c0780b06200d2806440b68000c0203a824002d00111448000e01c1c0b522149510155101000b01c01c0c85201542d03a80040ca5040501c0341044440d01c03884241080c14050501020643d01104580c100000b410001051001c0810321409086148015003540c0514401c1200341078000703441e0b00140306501840d004940d06c813841500e44800a00580303007100e01c0038800b14000340c4005074054074110b0040440b1b040582c0c0d510084180e80381228000800400401030140c9150000d4007034020302101e11030458241c0703060000030040d888074070a0900c0307941c0e9400440c01c0d442c020b80d145914080080c0c024006031400d0300385195179003010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 112376465 1250 112375215 112375229
    0x90b070503120703090308070e120f01020306030708060708072105040f0b060a03030c17120709050a090b06090411090607080702100806090a02030901020f0c0a0309050402040f030204090f080a020601 87
    0x70b0004040d80d2080c4034007482c1030f030305845280160701c1e0301c441211500705122420b81c2040100c000d05010010401901c1c2410b00c00d0700000d40d50703103000000e0504025181d48181c2060340481e0522191580100030164070001600d001a05440c01010404000c40410310101400345080e05000a1040e0300c81d000e6255401100c01d0140e907200c480601c049200707948000381c000780c10054001c0000300000d405440310174030420b8035414610705400003402c0420a9414001046001004020f075082641c42000140b407007402c104003440038680842c40b1361050340d29070b40c81160b03071b0188000702060314015107489100c040d1000b900c131088da141c0f50380c040d88124001ea00c00c6089041c550946481211010302ca03190280c40d10304907031580d00307000000e9000500500659502441804141070703090000d002c10181210040c420050541805000b0601a4004900450041200b48903981d140c0a107002100e034152000181ca41c56420008000501c00c030004010950028114030300755800031b8103038103035000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 112377715 1250 112376465 112376497
    0x3040b03010308070b09060112060908090a0609090e1f0b03120d02070b0109110a0804050a02030604030804060e0c2202090a030609030207080f0a0209250216060e030a12090b070503 79
    0xe120b11b080c2e0f0388000f4401d910001656214100024095803c442503143c45685880d06000e0f015000a00706845500301000040d88158104040c0d001c03806810056104132001c1d100003a40c1c03000c08544840740000c2201c03010b45a440c0d486440c0c504000d044401c43c641405030742c41d40e1115500c0b4001c0e40c4004010f941101d035a40c004a502d85003445140d4a1010b0010114500800315000355042c900041c000c5e40c1902801d424580503880500c0322500c59882a40d40d5801880c0a00d02001103605594941e2030640c040141c80d11180c545280e20071400e2034011000001032000b90071030b00079104d40300880d50000c02600d800410402c058000111040c401d809036002c0325180d180403a40d03443c0d60010480182c1c000d0920790701508040c210b4a4000480403030102c10b03202200d14640c622924040442c006903c0071488820a80903100f414003d020f803454000828088800026507a40141ca030145c0754100060a500741180269884c100500002d0011629201c1a0030314544030340202800184d4030314 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 112378965 1250 112377715 112377721
    0x240501030510031e0c0b0310150e0103050a0b031006060201050c070803060910120f0308060105040509010b0c1c0f02010f020c030d0507030e160810020310090b0303040b03010308070b 80
    0x3000780201445001c000c881c0600c95442c0d91108030002c1d5001000c0720a01ea41c0d205203c0214000c5a9040d000d4101c80080039071300d04280380e40c603000305000e612114423034900813200090603920405000c40c5a0091030089155210644500300401c0750300c59240c0d051181c250031040c405459040003048620340e8000300100da880000d51003942c8503009000780200010800291145030240b42c130754000f5414000078140030303118140800850480350050301d1182100600c103040540c802085513208000f0700e04181031910346000b041c12800306014a0089a078045410140244101300522802c0054428100101c602c1c0601070041084041860019401d003e01107106070700b107000b03d8009000c40c10080d0b1030201c82138003500c000c0c00050306040404d40c480740540311041e01001a14184035244400c204c82c60320b02003040e8503010300341d603454201c01d00500c2004101110000318008603a082e0101198002e0000300090561040d6001500aa0320110010041c400950090000700d407240d2540c0784261 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 112380215 1250 112378965 112378967
    0x106090c0c0b070f0903030c1e0605090c04061203050d090209011d0106020703020d02011101140a0f06120302071a0f071101030c02010603020f15071e200f060a0c06240501 75
    0x1c0d48844c40c40407070711500081000a03c140140da8010340503040904128441007a000440d0007803a1060b249607803588184450100148001c130b40140c0100d4040000b685401000d900201e400300c405810b002c40800c000d501803881d034001d6841035600509031041d540c1c55501c8003400b0352500101d601030340c5201c2d00224410f800040e010342500d8000b031900d49444201e90044400e0b0280043d801c42a549031418007071521010391080f40a4102ca400203d00024085030b500104d81d415404007200301c0000c01d08202003500030428109403003940e002c1c03d4000903405074018440c85080d4101e83c101c2400500032050090311a032600c000442680c2c00d100c05094030408070309942e43e03400040c0d80031060000070000c0c2c1c5400c074082d500031950f820713000781000da00e519032324003e410074100340744030860b0300282504001750110800d1000c0b01241c40301224004200200d0724241000007064060600042e83d180c1b03d60088400302c158035070213441400400000c1e600710070070003581c5c41810081403c01e2008038040d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 112381465 1250 112380215 112380227
    0x30a0503070f1d040c210b031213032d0303061409070801062106080c03010501060c050709020702010c0501051e090a0506220c080a1110051801020106090c0c0b07 71
    0xf038a005015400005034002c1004020b19809a40906000c26003040c00341d082c0c500c84400403140d0300c00c00006691510081030608294800c2c11009034450100180782c01c2c80d00c00c80780c40c2c00340ea070068031803901c82c449141b074148010700309035090b5200070300403030b0708001c256240d0460001c0c0c40000c000c0301c40c95050b0009100c0580c0b020f54041000c20b030b200005002c089e00c0f50b180e04d06510000da441703400d60785100c10700b9011511a80c004540075007224060b800b550409000f032a0042c030192601c03c145038900e0f01e030740d030307c4003886d000c0c0480550b000140d03541960700ca40c40790000300360400c0080040e42819440511150004240300c000d140b030040025010a001160914543e600100644100d6070b4005d00d00c18040780c0740140c1c02025040ca22901e000c5299540d902001d403030140004c140e8103421703080022601d0a00c59045204403d04404040700560040549460010484800140c0b0142100507400342140340c02444559150826640320942d10031030329034845000700b8440440707864110048800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 112382715 1250 112381465 112381487
    0x1211031603061407021b0a0b070f060b060705031b15010e100503030c0a06090206071b06030614060a030906062301080f0601091206061e0302030f0a0308010b0702060c030a0503070f 79
    0x240e004401b021024014070b190450710100000c080e206110340700c031021402604800b0007546c26242c290500e40c2013103c81c1c818540400c2040384c129017011801d542c0c4981d80e10803134115100018000243c501104030030402001100318490520040c0d42e145d0540380c1e005101110940302c40c0c803001000040324107020040f5441041b113100a41005c94540c0c40300030142103220001c076000700301003040c103000c9200305008030802007107182c1c42d8644502e0010000e060720310f81d40211a50340d504000035001a41d82808580c0b10001c50304000c03900d800103080c00303001000c0560056a44078038841c808201e00c1414885d141c81e640090b2202841c0303850714400e00040500031628940070032a1100b00f07011815092004003545803184d4004141c2c581c68429604614100340c3ca00204000605001e20442c9000c0c404410305442c9a80100b0744d14000e62001800b0705010302c240e044003440054902c0c2503403190001c98102000c2e01044954408041d03034010048d500c11034101000a044018004529108503601c00d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 112383965 1250 112382715 112382717
    0x13090606030b031618020c03120c071b05010819180501050a140c160807290109020c070e070c0803010b07020a080a0807150219020607020f03131211031603061407 71
    0x40f0070102848985c00a50008550f0300c6548002d00002804004008000d03100ba120218103948503440e07072600030003c0000380050a440c030b180c80000c0c00f00b41d9100b00303c1b80c0e10050007a156a461452100705a00903e10203809580c40480c045400c0140320b4150011401400c21b00c6041040016201c050320504606135441c02207014100f14401082c0100c1001c801110301842d8150729041d000d581c1c001150403110050400d10511a1001d0701c0c92021240d11401003082d641e056181c08d004940550302d030201d600032043d0341c03003181c0b0103d200b80b841505a482442d03804030506a880d44c64a050100581200b80120f200d09e003040c4d0080390030350004c6940c0756041e5100038031a0801010390750310000d807454020b08000300755003071040100c159120f10030300f0401030340d640140400d030400c00c42c000e0801a440300079204e10740c02000a5051070583d1814070003103401d40d10308044450360b41c4c40d294100b65041d401256052080c400e11661010014600908480c81030030200545480240140440c00084940b80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 112385215 1250 112383965 112383989
    0x30e030c1c03090f0306090204110a0c061d0307031205010b09090a050402060909151216031124030106110d0e040203040c030b070e01020610050603060613090606030b0316 75
    0x454840c1e02200d0380c1c00607119042003801103840d07080001d50440981d0055070010384580081041d4209445a10f0103101c07413641e03192811900310000340c403032030078448000e1002d950352845400704290203160190071f481000c141c0307030740355040d0400500600074010862000c5284c140002100101c02040f1800420041d280910944d1541e40b480d005001c014803c0e82c00610420120072159107403104988259085050390001d03c01e0103040c004159442d0100141d42c1c2d11040407040500c0d503d08000d0101c036408845004004810400300d142070144a14015230111155200d0602d40744840c05036059803190380c0c8040c004030b00d9071880ea94031b90400808801107944004006064100740d0001c59205000f00e50390030f0075036500d0340e07000f00244048a650000030304000c000d900a40c0d05000e80354000010054603841036003007100281c544c0c40003600641c0304035000215000580e4012900000410f160b81c0e04119190384c0305ca018002e082d0510240e4401d001e1041c4000840203c110050103403140041e0350 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 112386465 1250 112385215 112385239
    0x603140403080c1c060308030108060f040b15010e0303040306060303110706080a0216021807030b060705030a0804051e0604060608060906180304030f0c080609071d060414070c030e030c 81
    0x140c403c6921009400b41c10399102404010128410700031304c401180300341816035596140c039401508286010301200702c0c803540c010070310020034003440d00c458003d0300000354607080002d90001030391201a032105903601404040740000900040b680450304681c021380300c0340401f8010540302500d811040c0502804140c408001c544405503170781c040c0040030745103442c0008014031600001c440d4005107400a000340c0307501041110542e030500802c22003400513103c0c1400d0040039035031b05481e4000c9005070030410804500013070902408100300e11118000c42c1070021990380c41d9910702c2c0c0300d400032242914624104840081d640d035000602d548511280400344c101d03500d5040725041020b03c0c07114030400c548070612022000c15140d4060f0312400d840340c0d0b090704a4910703105800e801c10700c00409150700764010700b03001c005200644078103034407040980200340300550307400300001c0080c04000d8086002e81030034800c0015541d0008a909880b13802a03d5002e445401c1004040c4c0d141806198103401442100c1c04c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 112387715 1250 112386465 112386481
    0x180902150a05040306050424150501020a0203060f101805060118080604020d02150d27050a030e0a091a030106080708120c070b28080c0403020907030e06070306060314040308 76
    0x701a4100703105095192000c0308c00444074071107400c01c00c40d807400d880ea50801d04960000030b0246000800081c000781c4403640080d00001d440e05c0d00103100d4101182801c00049041d207c00c52843c0207013000703c00c485000c030070400b840c0000745402c4131460b000c2a000420300030012845206a02212607410003009590303183d0382800410103030300b04202d07000000e041749160a12003807400390052400c2c0800c002a0300c0207001d20905203e00058004012012000c80c0401044000c00c0d03136200e080d01800d003d45240c0064020070307640e5119900141c0528a4078900d0200490305460b0041d0301d03142140240a060740780c01c48141c4801c42c6100d0044240c0c86964051848003910303000d420314444001c02d60304102d58501d00803030560b0100c813104c41901081c403200744079003d42d03000d210300c0034201d0b180000e07892810380482c1c0c00d54801d41c0800381c4500f404400182d900c40c800e40089001c00600d0065442c50708121201502801c01402041d02181c14030a002c890800c496101c548500d415a450603d143c6031056 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 112388965 1250 112387715 112387721
    0x50a030809010e06031e0606031e0c04050d080d050901111b010605041104050108070e031b04330909020d0308040201180f06090605070c0618180902150a05040306 71
    0x1d00203051000030a041c554998440016620035005c410b5052903e03000042c040142002c01882c0911842062060013032010301e0043c44138030803004014031079580d02d0320804010580500e071300c00359001011900c60710130480c0c01c4019101c0701e421604180247d80310300c1c4885081c0d50f07104189502d00c5009100440d00400306005d288440b00c45076000003003032512100458251501d10f03144d06000c4800040801c895680510401d90041e00c0d854840c400704c4215001941310303681241e0034100000c00c80c0305194655a1940083c0081c902c004403118100616078400c0900c04546040100c80600304800040e04042d9000d10b21281d075000b484509001d01607036007074800d03040c09002030781040143d131070000c2001c502094a0010701040c181d1000741c1d91034080014030580326604014100300c424401200005d280b001448140c41c2242444140707100507000f01000312203d584039002d00180303076665505000c1298404600c0030f00948510f00740000c0d04580588a1060304040ca0006804001c20008190154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 112390215 1250 112388965 112388977
    0x1150510270503060103050102030402030c03030301080705010c03170906010f05040b010206060405040c081203060a05010e060d090602191106090a031b060b09070807020f1606050f0903010c020708010b0604050a0308 94
    0x89080540c030b4842c004280381007002d030821582d0707039800010300c42549810000401c1151044000b90f02d5981401d600030780b100c0161241d07a0502c104010b100d000c1501440e0b2200f074200d03c400383c40c8400e181c1222108c0c0c0c0e4041c01e22607000c1e8550b40290110f081e0070517004a424848040e0001c041c1510740d2401c0c4001050020400d80c0c02400d01e07800400d00b80d2080c0084110100304c0303104a500c07420041c04100403500e481c3e03c8941804a10020f481c01512a00c050710010b00c00e80000280b03699403410440064484e030f240001d907165a161401171890342094400754a89042d004075020341d0760b80b4084a5503031b020000c0103000306002d0a001c84402400700f01c04160076114410105008540001181e0010700942d0b01001041010007002000c0d58100300660480c10302c1402080d8280d1055050071500780180500400c001c400541e051402803880d007168001107010b402002140c601d1640203440d400c00d405120102e5080405404080c980002030b0f070140c990040c030003590703140b40d03640d00b4210758485 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 112391465 1250 112390215 112390277
    0xb0a08091e0a0308060402070c05060706091403040303030509010c02031c060e0c070b060307150f021e1609062402160e010602010c050c0a0b100305030301060201150510 74
    0x942240310161a0490072140c807401c6a1008020260751450081d120180013042d040c025403050000d0700102c1e13942040d02c0c0c00c40c0c400340e41c895641c5180d8140300c000740a01000150a04880450b0124071072030000061084a000b903074100410b455450403503090300c0d11800c501d0010782c030501c02881d8001c0d03041d031340ca10f84004210000425654590303d040d081402201e403840d103504041414814000020b000c5584031000720044c006083c00c0110a4000000304c0394040e0401004454005040d8020003511554491440500300c500502c144e900d60340d685169032814010068130400a41d00d00c4a0141400b035400320b13542c410401590385c0701c101d10040606000400c40c400c0d0307410284602c3c01c10380101e02a0034a016004000d6040400180c02c3d541072006860800104004030072241402050340241117506c0041129a915005204003000c10190405850345c00000000103099805501020070605c0940d0035840c040d81d5441082804415903207000301246280240b5128161105036150b080000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 112392715 1250 112391465 112391473
    0x912030106211104180e120325090603230a0e1f0527070b0304080d090f020405100f0b07031e18050a03050607080c0f0d060f0b03010b16030c020d060b0f0102070b0a0809 74
    0x8050074944152201c0c800c900403c04907101884483d174980137080c14400b00c003113120b40301c1c1b4580e0002000b04070001c0107a0340056030341c0490b505c107000c2031040600659804c0f007075650f1030028010500c004c100680c3d621705410400d2400300d15444404486040c0b2041d080090901a443d0045031034040d823005100b09e4808008100301a0303022200d03c12001d0080c002c1c0c0480721182e04601c140400c40e0006040c14500c4d8040500400000f603407040c5a0055a60030101e0035104c170703003c2c0350a44412003c030710400e02e04081201400001c07a485400c02c9088120312101c0761043e45c4c0e42080c016240514000503085400440c005000503000c1d407040e40c0c110110642d49ca180422590a00c1d0f1681c000342c4012a8036901c0f02c00c108142500c0c1520390000e0310800b201e10b032465140401c6d00340c151140c00216100a208401c0040074113004500c0d64040c1500038103034110700542c074540301004280209000d8460140a03942103079651000800303d042d15a00000d2030325240300c1803819240c41c00000d2112049201e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 112393965 1250 112392715 112392751
    0xc040303050d061221080108031e040b030c030a0c080106050f07030207081f0e01020301151b0602040b0a080702150106140405030d0201140912030106211104180e1203 73
    0x1100700c10009008900400e221303801c0c170000341c0701104484444810400b1002c018021a1804412910702403440460903d034042d0310030390740b9610700440c0d02083c850000402006140354001009620032280510108442c2d103440d40c054600520a020344400502c0a0101c841c1005c0c154004204942c0a401141c0380d0655905005107408220f84003011300055108481c1d43d04401070142c2084051808000c6d402c641c1000d044150b00c8120012010800003d130b1442104200030364000704099030002c4007507541d6500d81d01c41120700c0d48040c0022001943d0900001c0c46184081200011290718413103440c4664680401112006191448040c01c20001c020000e00c95408103d00c0100541c282c00101c1c00c060301d5580c44100900046c155140c6800000030318501c508032000710b0f41920200c1c00c0c0441c003000c42031440b00e101405582c0c11102070b46400e1509952803402d40281c000c50780b58041c0d41500381a9029081c05813034004080c05001e5000303401140e035154060020399131107510003400d140040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 112395215 1250 112393965 112393979
    0xc0302040f0f06140112140604091e0804031e031d062101030b01060f050a0f03020d150302130b090604090302010e06040311060f090c2202072301050c040303050d06 72
    0x502258000d90301c150404c2d0100255580000300303000d92a00000c01004400300004041e41c0d0204000c1c00f903881603a41d44440300810040c1a01c0c4074040c85010b16850042d10300780740c080c1583d803203400282c5800100501441c00c0c3d59000c25070b81182d0358569100d01c41c074500101868581c0994035a000e40c01241441920101205244d92240d10030981001000a5240d030400020201040c0c011100300100c903c040c60f40c03190080c0464440070300c18a000702130f6680c0f0210450003805410010302c00c1e142403500341d02c01c01100c0b0b5440b0040d00d00032a0040d0140d40150703a81400c40302c000350034507045169500000d51501c1c26500c82c01640e806070001054080000c60111b081880854003140410300e03009100034807140420000351b102c03189082d422103904046601e170340c0d41d1403a61042d80c45269004180500105070803044085d0343c070031603000e5480e00658a402d4000c50017600900000d080c005007031041074101400380c58042c1801001a601d800d045840460b101d52000ca0360611440d101c0800040038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 112396465 1250 112395215 112395221
    0xe030409020d05060f030102040812030405070527060a0609060c0602220303080a090f1b05090703142202010c060213030b01060305060d12121506020102070203190c0302040f0f 77
    0x1450b034440005240c070f0980108055499aa00d206000b684180b0062080380720001d5030ba212408a031343c40b617480e42c0e95443d0080c5001c5464101e0794000084e8880642003092843c1c51415500c000029003509070749030802d0002c03000e0345201c2e000c0040c0a8081c104600c902401002c40000d02400000d45050040c00164000d00c12541100340070005040b010024503500c410300640044080106000410050302c881c0107890110300080e18101c074141a03601401500f01102000b4840640444103c3c1340c16103002d4000c04d801030b9801043c242000016072a00c0349150040007401450030b02c0f008683c865001144c039061203007822110582e013040554682980482144000d600ca0724070f00601d5030400400400f580d201600650250452107440b00c0000d1140340209908040761904c850000301c02c0010310094110104804891500303070701c020500c1a41074009150b918001d8040340c08034000e1000c0a125440310071005001d10030300c95002e00041c5465045070300003000110010840f0802d8040740411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 112397715 1250 112396465 112396477
    0x3020f03011e0801020a1e0c12081e0112121101060902030106090e040b070503070509041415060c030307030c200a020f04020c030d0207081306050705100506130e03040902 75
    0x25a2692800d202c0c200c2040000290107003198000940c200201d100b4081c2140c1c0d000005664454090000d03011890702c204100003419420880d0603101c03a40500d400b428205091f20401c0c5811340d0358511010b42074003103500904035421107020380402112038840c580800244200c0c1810000400306a44400a013401010060200c2510040c0c0c0da5241210150407a06203500c240c0da605c10041c10000070035140d0308015440030300d606007940c0e40d680710714003141c2c2071042c0c840031540645003a0440c0011041d201c1880e12950001119903a00409081004441d00030303076140103034aa00070400548160b1090304180c010b221241018a000c001c104100c4031680035026820301f056205158080a611f05000c2a04d90031078284c1e0118608a4100c00e05a142e100340c00425104a070001100800c0201001c02c440000541c0e00641c407145450701c100030507a90260105948034460001c460340d41d0203181c494180100300050560150040d0111054007820042101050b9408188800500c6440d24002002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 112398965 1250 112397715 112397729
    0xa08030a15090e100c0c0f1104060f0503060702030c07090c050d050109050910150b03040c030605010605070303050618012d080c0a08070e070c0f02060f03041e020105040b070303020f0301 82
    0x103c0b612884040c0f0704e41114010010146400c19221210f040d401400d0340c8402c54020100402d1004181486c002e200d0340b030500da171340103450070030006090020500141d060710011420345605403160402241d9a000c0e2140401e4a0b0300081d004120034180c80c0c0c08949104c046051090030444010000011039100346d105904c015151000c10211500c00d00000b516069070481c208032004100c500343c84c082043c0d0040f940d851038000040f0f000e2150801c080b40c02140d22403400c2c003c40d0b8550500a2407074000c60022030109080c00c0c081035548c030b0001c03a500c0c0c050781100c44c8007489a29240d03c100c180001d405220b00c040240c1084004103042511100d0007030280c5c03800a0000c04480c406100d864620b6a0000c0c810350441074042c0400d040c03090140c1e41001443c640185650114240b0010000d80710900030b40c401c1000609969028032040034510590044070b03034105085400d8400c00380c2d05982180207000450800090080c0149900500440c80c0070303190050820f01401c1c500c00c495802078100c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 112400215 1250 112398965 112398971
    0x90204181a0f01090f06030516050306070302030103020306150f0a03050d0f030608060f0702160f0614030402090406020a11060c0309070812090f01030e0d0806040501050307080a08030a1509 83
    0x841482146481c1420596020600364118904030728202c2c0484410b000b0750071200c0d103d034000c03542d0818542100c009141c01a00350f50340300002d03e216003c0080e03144900740c028040e80c80040d5009001c0c0c0709032412650083c0203443d00b07a4403c51342031002c1e8003840b41160f2203020403804802c00d0300c40c000035a01852042c0c004024410b804507024111000c40d4542c0000c00d4148102031000d56000b01d8010b4102c2606001e1684944030000e080e0300304507081200e0341200e6101c4c0d1000955604e01c080709412100d8079111240c0d4038202d05500100cd101c04c03200030750014842e10100f070015480798010400483d440c40d045076100c203201900390034900c00f61180844280044107020100c0307000d10207600185a080d0042c1440720049003201000d014101d401c41c401c000e404400e2015134020381100b050300312458151410241c074154040c3c9110025112903000d18941130005c100e030f060001e08501038928490091110501540e40c41134241c0c0700078550401552264070012140300c0c444c1101024008820000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 112401465 1250 112400215 112400261
    0xc010605091302031902030a0f0b06040f0204061706011817060f0103260f0a030e0d0503100b031e012d05100302180a0b040306050a1419090204 63
    0x10321000c0103040d0b00034002c4400590401a90001503908102078508039154032180e007400001e04180500c80050000002205110104604400454030071017048808020821b44a00f9490490081e03000b40c10208070b061240910b5030300c7c5140440d501410514004107001d0394440c44504410243c1e0016444812800c6680011141404280d6020711070000d0300b0001d40c91510740d04181d501140e00d02111b141407804101e008000041210408284030442c50380c0d4240c0c2c2e1000400600c20007044024602a68101d0260306110380c0880e0300403188030925111070f40c01c103580c903801030340090002400400240c1c501d5000180401019009196010304640340e0083c004130003c0e22035a82d80c450030300c03281c1811309000c8c3ea41d6002c860b0310300320b0040c0b5006884400509540c3d0035914102801944072003500e2000a030301c41d60070006c0080c1c81c404c40b001d105a0b00c030620200c0031b69481c58801a10044607100080c07103558220b001c1e400a1000c1000440c8413552900441d04440c07084044d09030181e050114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 112402715 1250 112401465 112401469
    0xc0f0c0f0d1101180c180905010c0807180b091002010e1606110a03021203090f0a1203150f0302010e0a03120801091a01082a03010b0711010f1d010309080c010605 71
    0x4d10007218810308482d84c0881c10750ba655055510707240c000c0c0148001c1c2403100d0368040586600002d0b0040d070120081103020f803101d801034041c5000329503000028151500949808089c12545000c55440c18910b90400f9400c40070001000452030f85241190341ea111403070305007c3e0400c211448541111211428241840c10042407050b40340d04550b1191300c001d01c083c0020707a0004003502226485100580c032a101c00780c8060400c400410407132140d1180041c81030500200f98032101da08015900c04200401c801841481040c11500c81d080c200d4244000400155016040c2c050461600078070204501d84c907613650003009034540c814440003902e444010f20006906100390030300d00909113002c028081026000070100312004000e04c0805061303c100389542d4890519081103071810140c100d80307a6855a4440840ba000940150f4050301101c90b99001540504211030900e504d42c1e550710003a00080340c0c01c14260744040c1d402030403d503807103019802041580010303109410401d00086102803070201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 112403965 1250 112402715 112402721
    0x80a1a09040c210305030408090d021f02060709030302060f07051207020d0f05041809050f0d0201140105010305090709020c070b04090b01030630051c050a020706080c0f0c0f0d1101 79
    0x112161880460f000780d010a030030130240c1fa800382e801420141d0700e0260001050300003504010083d000221101040d009114030398008090100036800c40e4025076038102c0481c0c00380720754403000e40541c11450101c1d00c040e10400e011940001d0300e090a518041d040c0c0d80341a40860100c1d100c80060300842003031701810780d100700e21400d0506280340c41d078103103414800f6010240381506402031b4400d6564003640100036061160307440c49200001036800300c6108a5019020b44000c06c10000d40591090000c1000d40c02889000c1c040c4c02040010000b01c5d060080c9030b400cd50015901d40f94074801c520780043c03901c2802d40200042e010201001c60200a008000b40035521160000d80c00040e9000c24421086d0700c50003150000c40b4161400c200081e124104a030030700d449034103900d55080316884007444c0550031100414160365581d00712004560b840e04111500708003902d5200040c40e003002441c3e400d0b003087d005400400035407815100c5000c9074038001850321000c0e07100c41b00420303000000d034100f1240030300c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 112405215 1250 112403965 112403999
    0x302280908160605030a0b03120309030403060b0a0e0105010c0303150314061501020d050d061211030601080111090904030315080f070503010905030a0c0302030409060b0d0507020d080a1a09040c 85
    0x40441620b6030b04041e00a002c50000078001c00b070707040d507950401c07000c0e540401846078610390141603103590342480c100640e101e42c00740c00140c40c1035041480f0000d0f18103040c0103500c101c0e4502200302d10300d642440c2c0111546c12411105070708064640c1c200152240264210740300030b41c030440c00d100c060f442d1000c00314104003006212208c14501ca100c40b900598001c03540406090551074150b540e41c590031840d0b001801c80d83c10081c1d8400d850200c01007005406504c01814030300c1201154210ba030707180b2489080e0303a004000700703c046c2d405110401e11800c0041c3c0160b0401d20070304021400240e4001d1210040000b03a0010590764031842082464580510207a03001d030a00354001d0100c602c080d1a19a82c1348200d164020801c1070020b00744c3d00b414800c0c0705a80c083c0000c0320003800701039034031007110501d90400c041c0340e9003061400e800700c0e0304030703000083c24140c2e0495516400102d54500c3d000c90020101c021418001103211003c0268655541c84914400c40c89020711020f40c50900e803102c2d440c5038002d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 112406465 1250 112405215 112405243
    0x18070807080a0902031e0f070e011d1603111b0c0a140105160c0503030c100b01030903080610021c020303041e03080117241501090f03030302280908 65
    0xf650400c0540c0b0089095822045194076807440c1b41840c5201510785508010749071034900400310003049812604031014121750184204001e5181d00010b102d804100036921028004103400c05c00c0b04060081d04010b9030030742d5040000d802c2c01100c00d14800d480100c0a40003120750011400c4840030b02d003024419002d0140300a00d80102c00b0342c000042d050b40304079010b1404101d498003804003001081d0703441d200070b05030140c250b945a50711411a07941e142d821203901070079181800c00d4080e10f54481c0c403403965002d80517582c40f00700d5250582400b0f00810401110310841c020b03020000c903144401d1141e0403401101da4001d669900c0c05045c00200c14010030751400c00034801c0c80036440820341c00000c07503055400394007000301305500a10345145451b0156102400c402c9503101d94003001940021041d100d101040a10400f0500900045031240618010710030742e010991000c0c004a403081e805803035404042485d4440000b0110500d011002c181604100000c1082000b403041d042c00b4032910b086000c0f9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 112407715 1250 112406465 112406471
    0x60f0a1d0c130c020c130f090c17010b0f010f020f0303010f0305100911013207030e01080c0a0e01051e0a0f02060c071202160806010f051203071118070807080a 70
    0x118000203480d0051760020911920100d502240002c140303a0203051003181010341044080c500e840c2c1080580700038860038a62000340e0103201c1409a060150780e0120034001d00e0b842d4110900c40040d141c0115913070b946411441140e00392512070404000071400f0703240724401900842e2951030140e1a050b0048450004507007000c0c011800500c84004a401514090903c0012000407114000701056550b24012001080c0f1a1110454000c03d001f000d601d4042c1da80d40588098400064a22190941e0a00040e0382c0812141942511801c620020140c052514514115190b8806040d41e2040220300c0035400d0001240c1a502e5007140f200c55000340c15001070007031450b051010300d20301e000350310b0302511401c441c00f2407601d001e109119266001c60b50f04007216449494414191f510203003401490100c02031450080780c1c5180104000d1a06041c40004604e042d83d2541c2d05086840045003080d00441101d50b4000c001c41610441131094001e43d448000d035140902c0004c010b0440944031b20b01c1c00e49 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 112408965 1250 112407715 112407731
    0x40503070303051c051608010e130821010f0e0f010e040209060a03050604050709180c170c1201090204060e06061e0c0d08040c0501030e060f0a1d0c13 66
    0x802091120407a0b405052464460400548401c1c14a0084031601a05803814042004510008000202014a0f580d40b901c05a03210542c500725010241c403805c044200b940c1c0c5000c00245444003c01c0030410700071201c410100300818098cc0b60000ba00b14001101c42880300b445171581d20301085511252814018420354544449040303481d00143c40a8000d0031002c00003121515525000801960320004660f1240b5040c01d107036803114218040d9911160401c4403807221160a005c0c0ea02860b41c000002c195118500300b040c03c200c040000d6801d682e80505a4080076954940381c0d085500b074100400460106018070410007211804e0b041480164401000d01c1100e0b1203450995141100800030a6000f02c4c00d544075880c0c42c05088034210b0103118041e82c95510542c0a04014012440358441c0c40c18540c0380d200650694500b1122010325501c01400500c0c4002c1446038581c0281d120a000510051640351615032070030b00200c078000701d50041061030b9090134503001c00e699504030110704104580f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 112410071 1106 112408965 112408969
    0x21804020f030f190501060e07020d03050105010810120317100612091a130204020403060c02060601090e0c07030e0405010909050607050406020717031b0618030405 72
    0x411000310701e00303040c0003038001988141c08000d4406040340c00c030060040e024101c005e0340c0564940100180c69560a080f680c002e410035409440e4009003080c0c0a029180103902142c100b084603020412440b4819043c081640d40b09400071101c440b05013800c07144510360a00d5102c905400304148031090700c0c1880c04204580e400e0b1501c25014420f44120004c840d91240301810300f0f101c04004281d4079009200141d4040d441101d0036148c0700554002c10700301d1b0801d41003120706980d951001e4416680400409a0005091a0a1040741e091005c8034614400103041d070b45031118007184040c100740c0a650395000b40840604100429a5114040001740811140c01d641500500e40882c9805124501300c6050790141d400038400c1d1480d0060700180b420071055024a03600044c004000b1a2000349045c824802440380284020b0500845845100d0b1881c28400c110750b04c00c000800c100e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 112230215 112410071 := by
  have h0 := BRFrame.cov_init 112230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 112230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 112230215 ≤ n) (h2 : n < 112410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
