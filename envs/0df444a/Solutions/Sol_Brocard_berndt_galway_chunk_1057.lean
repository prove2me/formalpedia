-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:02:46.168658+00:00
-- url     : https://prove2.me/submissions/3acd1d58-bb0b-4219-a616-ceee5a88371a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 189928057 ≤ n < 190107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 189929307 1250 189928057 189928061
    0x5271602031c15090203040b0f0405010b0a03060b0109060503090c0402070c0b030c0d05012403021c1107030311040605040611070801060b0903010b0301050c0f0c16090608060f060d0809030c04 84
    0x4902c51440c0045001c03481011000241c8043c1d600c440c404500c1802440000b628030800d858220030305100c045940c1c0c84500300365004280c0b810380198001e01e1180000100034540c1c014002c40712003601c40d000f400c5e5071004182e03514441102c11514a8106101602d1a0710b050b41c007418095000d031480c2941540c450318503108950085c0c4504600c25030104640040c81c565004041c007400c1c0840f2076010303841801a0264000300803031646014550040341904610010700f141c904424641c150501c14241c3c862950440c43e8801c44054000909041e850a040390b002ca04807002c860702561560302c1e103440e102007110f13043d120304450032a602840000290086d02400742e0382c083e0203801000c641c0c2d008014101400c5030f240c0f813401c078007a1b4100002c11a80040100542d0325002c1001c50a41d641e80b00240c2850801d425002080042405102c0218110149502410555100340112034280e1908403d0001c1c1000403100e060340300904103542e400241060014103014800035044813040140d840024003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 189930557 1250 189929307 189929347
    0x2208090a03211d010503070309051606120b030c0d02060409020c010203010609090903140d060504050f0a05060306011401030f0b041a0f0d0206030c090d0503030a060527160203 77
    0x240d40269032802c401900d07030b50003072003101003410309000500c490704140d080c9041c01c040007124140840400098100b40c0280c10480d40c0643c40400d84a500d1284591900d07007003110b001e07103000034a042008007210f0034184104031003148000d00402281e481e400070032003582c00590013242c100e4420f200008140010740042c20200c0c0c14030001589a60400b000104a00c07016400064818284201d000100350084041d0455030501e000155561003007981c1030015100e20340c411608140390a04215001c0c010b100b40d1401543e00410500090b240c120405035528000c3c01181000301c0e00a20104e40f543c0290700a10036203d0141e80400d0240c0c80c60006400c46800340350400280d030903601c0d00c0d01d1920b841ca80321301e000c05c021510f021655800c0c1d000700e802c600000b009640b06000005402800d682d981820018066018040301da0b00c4c600b00396840d004c0c0c40203104240c020446038124800c05405510b941c550781c1c8c0074031644080790f41d4844460036181b6070b80a034407017503010800c4400003331910381c0030150b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 189931807 1250 189930557 189930563
    0x4030b0604230a09050d031103150301061a03010302040f020703050a050c240403020f0105091e0a0501090c09060f030b0a0203060406050a1e0f060f050711041d0c03062208090a03 78
    0x249441d05081c05402c2c40780c1b2000060426151002002c841c2d58241c0c00c0d03982200c180c50a807200c85a5620100340101010341090700d582c002c4a020f000c00c0c841c440c1c000c0d410baa2007581c0c2030151501c4480c009040e030160840080115a003030106640d03e40c4914013070640301052004407843d03403a0007044150b01c41080310074600c088128004000038190108080100d113141d00008106519003c41c0007900d81000c0303150b580c841e80c1d810a04541041e410481d041c1200d8105000300300b21240d915104030040510720070070042604011001840075035003a401d00c222501f22080040c0c603078806241200a40c07000b41041c2d48169079210101d610380300e0309004c1026101d200d01c50343c003003070050070314800a5103c2d60000d403d03240c41c11801d0003440d6100c6002c29401405050040d1070381c40e18a00b91006480800d40781c0d0b081850b200180900350030030781c0c00c4d4008041d00d0f416241c20980d0b4205050726258211070509180120810f100851030b4035403182d201070f0f40584003003420645000002000d402881d4402e13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 189933057 1250 189931807 189931811
    0x90a090302010e0f12090301480e010804051005240d08090603090f100f0b101d0310050412030510030c060e04020d0f05090c0604030b0604230a 63
    0x42099024810b611094420000419040c4c05403d9059500c02e05034003001305181d0042141905501e09400c00100d6081108001001290000d85030070108181518410000050340d4030444449480c3d0004400b2012135580104c550000001502d54000c080c0046456211356104400384036540c0c881c190280010701d0081c591040c2e0030360065149108100800e1061f1005038040c00098940030490340e40c840142c9030241c80c0d680f5140d900703040c10020750491040e03000e1500c14803107000a41e40402d00c040150242000040d04000a202a140c40400030138085100402e01c3c0440c00d00c288141400c2d49002000c0351182114280481c00b500c0c000d681c101d03040c032800031400f80450382500889501043c40004a00040d00d15140c00161001ca4031805007845100d40a250380c43c1c407103404079288c0743c24580c410311182c1e115403800b03c0104011254450180100d901c1c0305820315003c01140c0c04c4070340240e2824119242c034401c1200030180e10312840004c2964400102150400751241c6104881c01400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 189934307 1250 189933057 189933071
    0x70c0803131e030201051021020d0c0e0405060103050d051c09050c0406123305040203011503051510050d06020c01021308030705010c02010c0801060e240912010213061d090a 76
    0x950b01f031041c110b4114240030345042145c1a09201800c42505040f50104c1c0c01c05075141032420018001c0b21207411000f02002c000d02080280080010400d040300e00ca10300311181d41100200c02c41d640d0140d51a40c608450f225100009520829008802400d000b00e0030783c0d109507100d8000504a44c83e82c4d110040b43c2ca01c0e62015424005401d40750701110340100e54100000e03030040740358010040f41860b0320752400d9580b0041003e5403001d40c010814824603154010300641c032810702c0350f50394042c44000c51541144500207550b1000d68001541150005066004010703081d541c4c940203904680d040f040c080d0740c00e1004001d400001d241750f10040c0f20721406160307a1041e40c1441400d4490b91180c100a580c100aa0f0400075a0b200c0b43e040d04680c0549004003a40f12560001086015803180d951031000e007004043c3e5184949400414001808450241d003155400803030500b82e000f18992001d681f400e569081040764020a114a4800d021040559801d04103000190460300d0a4800f46210350340c0e0b0b44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 189935557 1250 189934307 189934321
    0x11b150c031505060c0604030c0f0b070509090702011424040603031e05040e01030209191b0e0f060a030b01020f030703020c040f140103020127030b0906070c0803131e03020105 77
    0x501c920243c00c0a4030f00b6031400199050380c550390800900f004041140c49002241480a4910401c004c40c1d40080e90300c0d03403401c24060040083e04400107a0340304080442c08103001c540144649018407184800e50307282c95a8002d42480d4035180c880349c120200c00c0d4003080504642c4c55128a0003d0341c403940303030305a070988649920080d88085134600703024000204018044c0100201d115411031394102e65402a5031350311048510b000b600e1038400d44903e41848c40032809000742e24285040112565121b0340100010f40410184003030031745080350000700401c1070300e074050b1081d04145607844040c0101e85100b21404030b22450366100c181c06900580103400c000c400c0c0e2810b801101d518440c910420300290f641000c1c1840410b206100c0207050003030707008140700d145940009034181d44443c0e00ca480d00040c2c0c1c90400d11003000e011940c0740f095028680001d158103000701c850b11601608004401c1c196070f60800394000c0344000c3c0405861001c400c500244840c40c1420300314542a12a82c000304160038504 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 189936807 1250 189935557 189935591
    0x3070605010f080a0204110d0c0908060703330816080105070807020d210f33030b040314040320031b0904080702042d020306011b150c03 60
    0x80c001c001400d801c2d1004101c071040005114101a0301200c0024616182ca00300360172920650403414030b16428104d55612003600506054103c45490003901c0d003036a2080821400c03248201002d03d8100c000460300e17118904070b41d02402a45585100c080c4d419501c51403407500c1d00b40d0500a00320041d07244d5a0034880d00c40c0a00810340c100030942490841c50600c0706d000703901d61200324240010010302d8044948041300780300c0c101c14088501081040215060606040036200101e504881c460f003c203558440c0541899065400c4d500780715901070050b041d940c9194019001801c00c1e03040080c4519031010303400414009000a51080301c2c3c41d01e40c0842141840011750030032000c1442504100c41d00780d19800e96904903540d48030200d0342d04186507220b19102c42503029501002c1c0d046403600b80c0380080d01300070b00f102c0503488a004032208a000902c026000c240d2204881c3c0788d000459445010912045140b00070401c1485001d00e401355000d1203d842003101c1e04040344100080e1906079a00382e210707c05c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189938057 1250 189936807 189936809
    0x1805031c18140d1a1e0112080403080a1101020d050103140c060a030f020c0304120b010e090a03030e1509010506180408030c0a090e0c040f1715060406090e0307060501 73
    0x1001284103410315202e03a00007a074102c00c0100b401044400d100c10204021800c0c042060400340d401e43c1181e003000052060103682000072036804020440000c28420841c800b9901080c0d482a0345500c0d241c210b5030384440783d402c00702119081c40251035882010b102d003030000d040f046241c502c0c0020030358510f00b000207035500391082110440e0080c5001c03032481c0e180d51080b600400389905002c102d540051080780c0084c4100c40d01c4c81110300010a01240c5407854000d00d150080c010180551176980354840404900c605958080031a48442c01038030009000343c0100c0b1000c150315060301e41904554241e0301603c40b04443c0700c002079540d142008035038580003083e40c403510020200840a481c103603803a0441d41c032002c0c049603c0f601003c128a003a8610502d070039400351540328001062030500e68000c0e44160441d01840004401d18400410401c49400c4081385491040000b03f9441d0000c00030054009800b030300319034105840d140d0106400d881802000d902c42d0021b0000c40e82c81ca41400e0680482e401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 189939307 1250 189938057 189938087
    0xf060605041a040b030c03030408010507020f03130e0c0403061b02010507050f1602220507030515030309040b150a1709010504021e010302040f0902030618010b07031805031c 76
    0x240141084a6001e0541c0c10301400600f0b840006601e40c55600280c1742c05901100c49505200009011403100010740007217003d420180c0841d60070032001c04000c3e03201e0040003040400c004c80c0c14410840141040300c010341000d001c0700100c0c6420b803240c680c801951401d9503184c10b01d1803030b22001c030101a824411290302915900d8214205140302080010340c1c403c60300d0b50359204218040160075541c807103401d0742c0010682c002100031484041d80306000703000211000e030701282ca0070000421004500c8142510620024050342c905501c000800009100301425680c20000b981240c4502c00c40b8503000349443c8803aa2915070342d81c012281244130701c80d401055111244d0405041c04010b8031a900c560200f000c0354400c0014521003100120001e0080303501140728002b8031240040d580c240766001318000c0340c081d542c2198105142c88100120a001e1040d2441341c1d508010040200b84541c5640c42c1c003031033780001100041d944a0000349000400a18040d00305228000c10901c81c0e08a1035646201c10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 189940557 1250 189939307 189939311
    0xb06040203011d0a06120507030b060604050a030321150503060c160308070e031005010e06010c03090b0c12030109051e01051302030421020c040c0504081c120203040f06060504 77
    0x3041c0074001c04803106807040e4050700d1034060042404c8400c03507005040a0440ba00300381461400307500b0702036940c80c2140f0040c1d9612036040c01090a9003001c0b401c95082c0c1d035019200030401480c65608480e21b03480c0710710b40411504907070340c0c0d2440c110181c05500080500c01440042d8142014100b600344000a40306408440c81001800504101101009041600342c01d20020707680e80c00a040e1401c5000c1e1560a515010307640f051800300b080ba0b48150b059034010001c944507070350f48400659840309907180180106107802410407070461200010005243c0321400c0d14850303503122040c0c0d40311750000c0e00410003940d150010484651100c01d14103013504070315050180c0039450701d4042103c000c404808a091607400000007014030103032840c021b00444c0c246c02c0c004100c401042c03009440e407040070340f0103204030309081020400d28031410655040e80c402102a1141c010003018a003440500b900720103060045902c04404414203a1014501c03803800754411801e500034503c0d180080364a00d07000b4510440c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 189941807 1250 189940557 189940559
    0x5060a050925050105090604030b01150f020d171003080706020c01050601020304210807020d0609060b0303040503060609090a0506070c030201060f0315051009020c030d0b03012703050909070c0b0604020301 90
    0x7100103002d000b101c1081c2881941c90030190080342135403080340c0016200052113400051940103141c000700809a580d66042046c0d0f0580004030b03142c120001a1200090a10800c04881201041d0f07003604480a810000c10b0580d4030740d034003041c0c0e8003d900103581580e80490607401480d028015558000310905c0030b5890142010584050f420240003118041d031105408007080080c04000c484ac80750700280100071071009441c10344e020741000300040ba1201d04002a888150500001303880c10740d50014060700c044d0780c942d42800b44058004041e0b0b92184140c20300c1c2750219400344603030742c050402c0d0f543d08010701a40781000380c01d41d1400d40c0300c40d10b18250040c04002080360803030b140040d103403907682c0441c1917200c0c410400e900e0501e54000d44c0e2103500c0051510903991000000705505110060103100c0f0302d80040805080714a100c1712810380c450034001c108407640340d07a12065400c9109007000c0b404c4c00e202401041800310200c0d10007010600007410041030115220702141d21044c100c80c298555 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 189943057 1250 189941807 189941863
    0xf0102010605030d0302090a0f180b0301290112020f0a1b02060703020a0c0e100b0c0c09090318040506010503040b040804030c14040f0b0a09020c030c0604060b0a08150c0a0c05060a0509 81
    0x154485003d07110342b007960745400051903030b82074102071045000c2c001c0c0807004854012120b1607214030207911034041029102c002c080030060340283c070b0340805018003030350801013250310030303945900081c220703165080400031400010b0b9a14006880d6040c0254000c1a0713101b001c1c50034052214a54207c020020302460400c0203459801c80840c0c151a001b00115071a44100d19641385404402c8071002e9000410104001911400001608220940079600c81c01c0307084880a010071140107941305d6001400800016001c10064921107800901c645e0398140b405690b03840d55980d405098100d11200100560301a6040c64140292081c1d900da0090420142640000051120720f4600c920305e40c194011905c0007000e1410710544031304600390b00581c3e00c14503140c9040c00042610100c2c5902c9980440000b0403450400110240c0400c401701d40202240c4800000304025041241d601007040407404084000507020f115a41c0918510b20021615080c8480c141d810070000168000308502020055100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 189944307 1250 189943057 189943079
    0x1203050603030409180b01060f1202120417070b090a1a24060f04080a020a08030f0a1218110f010e01020601090e0106080613020102010c0e0d020f0102010605030d0302090a0f 76
    0x112080e03281c00042c41a0350415000032400741e51800b9000101b0072000150903900f0488102024409a48880c1d0b80840c0f5014030003240114045906141d02d070f03c000400041e035015121050300d8a203103003641450b0702a9074105070003004407400c0e68250400d0b4207050411206080b02d4202c42441c108171440303403400e040b00214030f40380180d4420f10009906024007040d29003404a03090300b600c00000e256115181d403071407603980703020300380880c000e201c0d40780c0002c2c4000c0c020040d100750102c82e9030803901c3c115031004112a4480517400b03860043ea03070f0b5076100395a84000c1101c055441d101d04081d03c40440200c080240c1c905880344494144100406c020516070b82c007080d07d505541c0c86000014030340400035645401001650002031301c074030651081c8a03001c000d00c507083c50001d00c01d80c0240b001c1d00700b02c0001c445030301a00c01e07900d4000c80d03d01d0500c001860400180811250103100010381c003a41d0b98002032401c0408008140800d0303000641c46258180420000090303c00440e030f40003864500328640c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 189945557 1250 189944307 189944309
    0x30209060108060f0a1706010611060a09031209030f080a0501060905060705010902030a0506040c0603060506090f0f04020a050d0f050603060c1e0301171501060f0518040e0303010312030506030304 86
    0x1c10069004000ba505903200b0303800c44403045015108924a68840000c4221007a411280e40742c1e80c400e0b140005502c80c820141c2103030b8520b0580141101d03031100c4007100c02919258508031300744442c81715494076040716071240344941400fa594036030500081d21000f9000f418040d080c880d0701801c001c018400f841d00048444120b038425030b15940d842000d802c00328014280d464000b075043c020f4180e00f00074484002640c40c0564000c125072040a90b40b110181c0461306c0c0ca02c207141c0c21900c14003a01100785060708030003201c8000680020982c484000002d4120781c02001510086100880d05450040d050321801d2600e1085200c02c0105052400019540c0c1d040100801400c40b0006050061000c15401c41c8102c1f04800f280749840356150711804281c40c01c2e500070b55519200d04031044c9100b150030b075144d034121b0700d0315210300036150156031049505a000b564526864503c1c20075a4607903440354130449040030780b000055600c03035065241290070200320040c25010181440c05001e00b41c1d40100842c0c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 189946807 1250 189945557 189945559
    0x2090f0102010b1005310e090a0201020a080d14100810020f180a12050c01081609050405071b060f0506010212030a0b1c050c01180f17030408030c031201050103050103020906 76
    0x1916138080110b000404000e1b82d010807000d0340102840422031000c00d04200c00d0710345144507901241d0300e11440541d111005800a0f0050384000403103008030f00c0c002d0083c690000368900c0400d100320303007181c1505030740c0050b12941d407045a01da40c10000e0740401d0002c0352000c40e180d402546040000038051840723020300e061880c80c18541d1803a001c40d654516907894000e01401c0301c05501c07440135080054459074030701c610b1804a181040041c01ba040074030f00c2c10f600340c0c003d40c450b81d005d00c2c10030b018071000303103401018a07042c00030f01c40c00d102101c40c0d440400440d40c2c0c03083c2c030045240358940440034262032010b060359040d54020313030030380801042141c1504e5100c0f200102c0064542058000034008007a1000001140e41ca400301792002d0160204140e1980c1000780c8803240034405c5905040359203a40c81c85695119080e030b002c148403100c2c2e6445002201da01540840e81000e840c0c15800b0306540c002d208102c0d460780001581107112484042290042c64242800c01956246d600841c0c480c0300010034103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 189948057 1250 189946807 189946817
    0x7020a1a06120a0c09060f0b071401020c01060e040c0f0602062a0a030203040c0b0f0d0f09080c0a06050606030714090a03080c0c01030515010c0222020d02090f0102010b10 75
    0x40d940b5152400c1100700700804400301d6002c00c8481c1000c070071604c543c0c00381d520100d04001c0b010407124000d01060080f680140c2c2120300d0b0412540303d0003004c00c1d5030b18448446540812804c40142c00c24083c10000e000084e2020269080a15150a0482c0c440d401402e1003203480c2401c010035a004110203904c02400790b94540c48240346111081c1d0f010090b19605121700c40813448003005681940990b1146224030161001603864000034030160191040d00e2080c90410070091844000b00d400c010494012100049813503041952045241d420180341c0d01820761041500341c092000074016190018010740300345186081404008008130074920081d2440c4000081c1c140f041e480d10358020b0001d64121412a880c1d40751414032a80b204541020180002c2c20031001c0340185810f010040c070100e205171a1880050f1865090146101d10700350a180c05030b01c00303807a414610005000600c612207001c0401a902c00d0340d00c2c100803802d125404154110380c5040c200b8805500c13954107581e4103150b14104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 189949307 1250 189948057 189948061
    0x1180302070302011b152c03220815191506031113060e0102010e0c0603060919050c0d060e07170a0f02040e0901110f0a0f03090204140105010807020a1a 67
    0x401c0254400c0b00c04020018101d010007071810f440c25900c100744280342e01580c403076043c421f020380c450f002410340000c548a42040161000302061140d5200c0001401e203228540035039110885414410043c8481c4241950b2208110100000541d01e1849040340c0320100880a00001d40d03001c4c1a40601481c81072582d505103810501e07403001c042e11206140481c1045055844400003814000000c00300c502560a00044004a00001c00c005800d130101070a12411a5140c0d4204210307084050326410754120700010794485040e842c002c2d240b03d0a03645503042e41e5010a03401142c100c17500c0d0340c420071890001c8018071886a81c004000c003007504080f04c981c032580d00e400040100410013041d00e11050b40c4002070020344444401d500f588900040d60080128001d07001440d0414403030804402c40112040040c0708000707000301c91001c80501b541c9070024008015a02107402c0300d428481071a04480c1d5035004100940e840402035500c03246c248054041810240c2e9a10f0958078101580341101d500c01d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 189950557 1250 189949307 189949337
    0x30403050f0c010c0c03020601170c130b0d0602032d1918060608060c1e0703120f090606320f0d080c190b01030b0604060906060e01020118030207030201 67
    0x68886003400d01d0001c000060700290040d1031031880b904101d025005850000440105202b00306001b40102c80c080d00c02c28820004015240c90108003103070007665100c02003600c070340319081c94551aa10405e001a80ca003032000380020b801c03940706041020145121030001890000030344c1550029200307100c0d1011100e1099010380602078416410750140585406035092242e150000401c44003a0780036503240c1d07100c0d000c01074403d10605188201c64441c0b13640d5000b042107424002e102e024003900e04142510300c0c0204500c207640c00e170400300c0a404e40320034990051281512031710001b0020b00041c120802d0309aa040d1050000b5400042d001c2030458060300403c0d11031242c45203802c42c00a00202524100385404c01c40354000c612100c1031807081d8080781c1c03089401c055000c100c640d000540001c242e0306e9960703625100d00c4018030564029840300d00004004000740101c3c4060303c01c40d02d9140410300d06a000a003194115001c600c030b2201000c4d0744001180d0046a098150b81e02031a240008481d094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 189951807 1250 189950557 189950587
    0x10f032a0902070f02040e100b090106210b03030304060207061404020a0b070203030c010c0203031f0302090a050703090203010c0806040c0507020a031101111c0801090e060f06010c0f0b0103170f03040305 89
    0x16002a400509248860b0700c0b109010032361889007001c041041000200813403e01026120034064000862000b554039000c1c4031009588002c04658a00089040107407480401d040d5002540c0840e00d043c0c002c03441004000aa0090100c103c9005075020f001e481c0c943c00007160541a40702c0d1400311400001d0f81002c1d52024000c451840742028000e21400e840e2030b038000c0d602e03441264000442103034003c2094801051070a0941100d4000701240c4150301c0381c04a43c00140790142004050540e41c00c42c440050700c00b8082d0044901194a80072540c0c03034a03605000556036003001c980c2c2004010010040141d607100d42c080e05036034000c80c04808038901400161a2503c0007041d6408900c101c1c4807228045001040b20308000086507155100742e40c0c5c5c5d0120005444a40c01559060381000000514004482c8059a0b001c070051403c0c0d03c4002158881035074100d1350340c800340d81c40e03d181c03401031040c082c40d101e030305011182d80c000d01e03403415004010310313102800701600c002d0801500046041c410b20140c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 189953057 1250 189951807 189951833
    0xc0c0103270c050f0d0528120309030801080a0201140f0f030a05060a0603020a020a0f02031009080405031209150a0e1008070201051528080303010f032a090207 70
    0x46600050041c581406a080c98451040383d00c1226141d2865a8600304411443d051662000c0102a501040e402010750041e0403003843d0002e1500d1000c95000c10b0781114600181005a00e001603041c0581c1001420f000050300840d905030b1102c1100c3c0c0044c1d0344140945540f00d910034080f911041003950310f006501c170f40e0416501440c0080140130751303243e00c1c0d800720380119411a070348440265160380c150240e008080c102000741c1c00018140000c940b42d0841185900d00c0242078802a441084200080721142001603072045d0300494140800c0c01c0802c0304012800c1d2151800d81088641e800203031881940c041107030180d00700418003003d428001e100e02441c2d00c0740240401d0203550781c0a4018100082202c0c05d000640c02c140200d103400410400000f100c40340034007504a1003803070f020b82c810400e8000c031030101c2038611701c100011a5801407015501900b00c4545d08502c1c94070394100b420340c0010590b60044402d0341400d04500d442050403500c42103030303520740005d070b242c1e40b442c14101c40c0383c050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 189954307 1250 189953057 189953111
    0x30302030a0b09070908060a11120601020c190342060504060e150a0e010b090619020a17040b091203090307030501020a030f110304140f07081e01020c0c0103 69
    0x20f580c042c80900c1d600055a04140c9140300200d4003166140c0c81c0717080a84030341d03441c01c1e01c00140800661078101040e4401950156041c0105c0d0520360001000c40c03407a8900d50503a801d041d0700e1280030300c1000021400510304040800c2c5910304500c2c00180b40c4014030480302d50444112103501012a0541c0f60381004000b88001071080204a580e054030f980d01403021204802008041c2c9402d10284c5031402d1170506855210903000c4003607080c8003944515a11031601c0036400301d4144203d910306c0c4001c070b454010b0014a0345c080c295002e90707403521006d010009101003c90768418007060104501510581d5149842118400307000d40d008000603040d44100c0c03002d140c05004461000c000c1c00015002000440d03050340e03041018900c0703c080f4074100d070b0541c0209030341d0344000c00c085004129203074000383c8014004000d03698251800801d6a00c0d1415a9000407040e42181100110501c508608002650010002949001e01407801140c40322241c1c00a541810341c1c51461103034208482c42c051420f000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 189955557 1250 189954307 189954319
    0x2103090b030c0304031b0507050108092a03070b03130b28050f010b1606020d0e030a110d09060c24110903070906030f0f060b100f020106170a030302030a0b 68
    0x40c40c0700304450b16841124241d01062880054114469090f00c1e44039001d50800d0140001504200c0111036410000d030440b0840e114040140c1c140003080800c45c10403060f0980d032100800d00c4a020b06003007040952100b943c0034404e10400000d0391030b100503a04455400309841d5116070350749402413120140301c6512900203818015440b14034129501c460b0140400c2c1030340c44020381e6169084419403040b44409090409141c00180018a054003e4080284080f80100ea00d045045000e851a04140406000200401c1c03010349071002c14801c00404141c2440c045091300d0408401500c11080301d00f009200d5404421010b900d6101c0219502e48a031100d0002c1c84018a840303410302e4070741c2007000f001d0f00c2402401307000079811a0320f1081030200d07940100725601c0180075855500429424a0060f58003030f858803005c40e00e42e47d03035540e0066525219141e9481c140034041c0000d0841d0219003040301a12001e5028140d08540022044e5603d42e0515000d41c0d00d80d01d019514000d85040e04a10383c11032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 189956807 1250 189955557 189955561
    0x306020f04090e15090c061e040518011503060b03010510021e0a020f0a03031e0903020301050f011d0105011b050102040905070207150f05030402010c020f1011010c0305012103090b03 80
    0xf0304041800e43e110140d001c0542d140c1d80310074460729110802e06d500320b503010343c1c04c000c0d9500c0c20b036012440c0e80500410b010214200b590311804160751100c1c1c400d05505a081a00c014040014105150b4603503130483c3c9010002a800d040300c1074068031040c000c1078400c0c1e12095840b044507108000001d06900b06141b16414402e0044015071b8403903024070124072a100d140006c1c1000e0a00f4680d2600301d941565039076240c207040010074414000510b400001f0000c0368080800940c500b40111405503219180d0024550301d04245a00d80c000d501041c2400d0403400c0004005981c0d000115400d68081c0444101d010390391490494028800d0381c1c00b0091181c141000c01006a401060b040c0444000c40c00d004020192904d003200c80c205002c0300350020030010b0000c070340554803075584c598005201402c2c400040301c0100000f180078002411042c009002c00c4418207000000303004607030744d1072080d0400748400d5040c90141c078480b040c4c1c0c00c44141100800160103051521454040300180740c0e440c0019035034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 189958057 1250 189956807 189956831
    0xe0901020720100201021903090206072001031a01090b0a05040806040c08150412050918091605010e01020c09040206071205091c020d02090c0c100204090f020f03010306020f0409 78
    0x120b91820340940700d90340c40000000c40600600071160286e4252107042580c200046080e0000d041d188801d0fa00f00c0000e029140004803114450900c2c00d0b1003890003401c030f454003c0010282c41d00c2d402c440c1d10308050a03002e140241d0308805000c05865183ca221515603030052800c036400c0c01150f01100039803040c2c1041c44140050840da22094841038011340d0f00f0702d218440312204030842036400802a510780003001584c0b600c1100075000009005240d034074445405041e205500c5001da03009081e981100d00c14011a91000c81c0c50b800511003800c001400045800010f501c445c180d5100074040d00035080080c0c210354a013001c65000980c030020640c03031640884002022600400c0086015094003025548060fa0f00c5c2e00c26030368164024140d002102841d400d200d40068050204005a40240110b2040c2d10050118100d003201140d40144c1f036504c3c08503054152405400110221407040000d800751411761002c50303064940200340540e132000101c0d10099507200f50780c0030b01c1d44903140c1142c1c5501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 189959307 1250 189958057 189958103
    0x80f060420031501050403020a120f0c0816081c0305090f1f2003161205010b0703031103010803040510171003060b1002100902120a060203070206070c0c0e09010207 72
    0xf94070a501014054106000150703014480c0e40800781d403204012004102c00043d141070100715620501c410440c95402d0b03a10b400b000000c5400c940e1458000700003054213500d0a003d84801000c040c00246424a4400d090034501c421042c0b6000030075441d840000c607084401c0107402e5064122808591102c44481801d1100301c10f54090701d100d06060002c984202c103c480010050390014803403a9245880300c1621810840c0301d442d0902c184544003480c9034050b94544241d500030140301c0d800c1d41d40c0d00100d140050445099881c55100214240010300005100206960640e0006e403a60001400780a034245e4249e204c06844040300794140d01000861000d40000c2800c51344180340034032940c410807040011a00c018074401005034003c1a0b1814010001e8000346aa280050021a07003548107414141c00c205c910744055502e60340001c14031071016410894240d0040305883c0c0350500303401d581ea980171012440d11503140c8d507400280200d0b8002078298126000070364000c0c10318400600b0b500400c02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 189960557 1250 189959307 189959311
    0x3180f050c130e030f09010c0203070806160c0c1a121302130e0a1e0507150e0a0605070b0a0f0c0201150f180203090a021201050f0c070201080f06042003 67
    0x300400c0340c4408007000282901680243c02c090402540c205018041100e0185d04004180303410000f0401010340561401e0107171001420410028003101e103401d1411030303030641c0083d5440c010000501c100c0004030390303e00c03005c1d0281c0b18650003102e42a0910300c181165070282406d2900d4800c1d08405020b54030307140c191480300321842910030013290090f680b54401203c545418020709074000580a0300002c0300c03020001001023085484000003c020349505240c18071942060041c824100240c4005075004003254403810700884d1400c10240c244070b0020181d01a003d0000c040b001c1e403801150446d0125040301101104c811820442c09020640003800307040c10b21030306c140b030821001c40800c1807400d41005200380e46180443e01d0000840415540c000c0d403001b8020085802004402401a540c0c0d5150700c4001060741e00100b4582001540c036200f00758060314103104190100020340050760400c004c1580040d100004104555510000c10701030b04900740ca40074090f09880b000c200d0300349010041c41c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 189961807 1250 189960557 189960559
    0x1020a02120c0a05010503160804170703030209090c0408073015060905150d020409080a080103120c030e091810150b04050a050607030c17030a05060906090703180f050c 74
    0x1082c013a41c400c01550544070503600a02520100135210301000d000e07594094001d032240741009290703140c4c051100100e8101540c1180065000940c07000b41c0c0c5004011075404c40f220749000d41c44c00303182000d89960f400e110300c10101a450407200c25035181c091000d0904842e9040085081000501d18041040441d80c0c04e40d0401035251000101e174981072482401c2c0b09131010400603c50030104d40402180f4444443c8c12a0701c25160340403c40001e01060213840512069155100e2550640c6410440d44c40a000308030300b040b41000c108004680d001c0c407500c00c684402d464502c90f0351940c1059a5011000520346000c81c030441e0b5008011071a82cdd4800114a850180f03502d000c542c03504d2161b80303944254401c60f5400a110441803016140c110300a00300d4030710908010301c3c00320aaa640c03299a0034291417000e0300c04404010000307603110707501910307602000c120703810140c0d4074000c400120007030320280c401d00c01c150b070358018003201075440b0120b842c5094116051003602649413400580c1c0d202251111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 189963057 1250 189961807 189961819
    0x30203090d0206011a160c0909030f020c09040f080d0c0509040608060108031e16080406260a050c0403060203100302010f050406140a031d010509060106110c040b01020a02120c 77
    0x101e80c1452011403103d043e110241c601d80e180b00b40442c03031403080d50440c000e03928614541d5100540002c0d90543d0040042007000400700d451080381c14050300e051940250030082d0341017001d440e009940c98858250b841644031001e582410b5007828048a58001c502c0718242c19460413001404a41c0c0100c050000805c04440901c001a107a681c200e031900300070f214450265100388140141076070380102c80c10300030035039480702c41c1062149981174080c49080740c1d06540717440000405120040d8480201103c0b5910541c0112001d4540c1e42183d0340120002d2041c0c000999074408642020182e030111002140c01040654480c00d018000084610b420b1000f24003081c10380c0f00c89894503000e1000d40b411038100345c94030b03840045000103c2500e6070210200d0030405a60740302c815489031501c000380d038460781c0660001496160004d0300c0c07460200182c20000038011000d00070300c841240080c020000020a90300456210503402c0142d2800153380f1009602c80880d2a940d40360b4040060307810608002120f03c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 189964307 1250 189963057 189963073
    0x12030f05010f0f09020307020c030a0c060f080c070215130914100501051b070b1b07080c031b0301060e04050a031e0e0103050415020406020709050c04081c09050a0603020309 76
    0x440d800403080c0f00d850541d680c0d80c2c03010008028542c0c080d5602400354019030305144001c50001e81001c181d460200d820f400360782d90a00425134802c03031640120301c980c10880060b05029189002ca80102500207229841442400014800140a0340d8120707405000c108429525000180090701d00c4113100d040d80781c0c2c0000058850010300a0705005c4a8060b168980380c0351400d40900d81c003081201d0310222502c078248000030a9011013004140a400f91000d61600302d1650203c941020480d80c802040d44d80711802c14201613401140b07110300181151408641e2010800c042030161a0302c0d84044034800d5840100800d2050202e03c0360709581c071a41d42c10b40301e00f282d01808103032101850341070b07000252001900302165002e54401d030341190051701884001420f05a840301079a1150308440b0041c3c0003414104401e40e1140903083d048580c8005a600b02410701c1030690350707a0045100c00324a50104410f1041c803a01980304d000c081d00c00a82981100c94880b04003030043d520a0724055024402c4c580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 189965557 1250 189964307 189964319
    0x10c0c030f1b06050703020f070e010302010c0804030b0a090303050a140a0c0e03010501030c030b07050f1e1207030606030b1210020a0c06060906060e0111120f0f0c0114071e051612030f0501 83
    0x22202c058407102c0c0180e0018be42140c004445003003d409040790628010840071010a00c00101a44664280480818508030f00d140050982c0c074007609440c1070742d08010100140700d1200c40d04603841042201c00152000c549001141d044910302100ca40551038800048240310401c103400301500e0141d01c8040c03035500c6080d0304803202c3c458881659044075041c4800c130f00201c41e40d40f860b54001902070482c2d0a00300c0d22814185c41503000e40e001004a56035100410280e07406014240041c0401ca800402c051103904a098640c0458200c818000d5400212500b40c10301545c2240740d800d40006040140584884500004103458021403020802c4810605c00b43e44c4907420084182d0440c1e0f029000b045591482c2c02030302e070000590b4403101a42030040802422036100a8000c1a14500000c2451a800380300100304010240c044810048082c410090b0f038144030905a883c00310030b107091699105403901400340034080c2c4c003005010803040c6400c50302c21945600498000c00b40c408040100b0b90b6a02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 189966807 1250 189965557 189965563
    0xf030703060510050907081902070201090b030a05180703050316140d03020a031406010c02090c0d11030615190807050403060204030b060a0b044a15010c0c030f1b06050703020f 77
    0x4441c0c1100004004c0c2301c808085180c0c0180001c0c61040c10300c0076400d5200d081c40120382e0400c072004c0909070307510020031503c1d5191801c05c91344030980c10044d00030302e8203646030542c42e84901d0b020711000b4186221360200304452000b01d856010300703100913200210182c5100074003941c002c0e010080001e0800c44010817550301c001046004034030585600e400c203030a5030709121833010000c2440711021030511544030b01c85454081c251044080351007081d0b03285010343c100a900d150030200e903400000180000303e8083c0c800c200744051400c05003004961551209003c651911598000a154038004034000040144000e995400786000b2900d44448548400003603281d4080e5200340c05c04568500b00d107003034000c005845e0010098420198400c01052101d089001c606034103c00b54902818104005601600881c840b004802c03d1814541002d2507171a41c0104070014080a00b0b503503c006c110104124449081e024106882e107990000e550740c5100240c00c0b6000340e502a0054041d50440101a41d004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 189968057 1250 189966807 189966811
    0x10b0907080103060914010204080a0b091504230a030807110f03030a0e070302030a0b0910060b0a0e06130e0907060309150506060d020408031312030e0f03070306051005090708 77
    0x36a24041c0036032030360b1100c20203031403425003d584400015805442140082c0020070207442c0030f000804000e032140c13a00f50030410004103000400c2d0480c2444c0c140c0d200b200480250040c0e0000000d0403110380021b0502c2c2d0800c108003042c540d91144403003010405804c800140d1080ea45902d42c410b42550250340140c0352490f180502c8a140c0042001501100c866401607070ba0f00c0f00a01110306c99070300c1e980420b20700b0f105050180c403401030460402122400400004118501b1a2000d00600d07241c1030b40512a03004401e17a8000344040014080d2803500c3d160142c644881070054800c07002590380c00c119008110556021041340103070035000c91003134040e001f00194207500a01c3d2030684482140c00d2001443c014000c640c1c0172808001621100c00c950001e44003130840c6502841d80c4100030115804c001d05681e2010340741c50030031b05008011036000002410200800e40f40b012a05501a00180c01d044198000038911490070003441040074200000100307807542520081243d40b03d1700004d803041750003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 189969307 1250 189968057 189968071
    0x151a0f06090f1e03030c0709240302090a020f03040f03030b03010e0303060d050703051f0605010f05070b0c04050d03080f06010203120115090e0a0207020406060e01050a05030c040b120405010b09 85
    0xe82e1003142c19003084405191140c89404032548092040f900003130865010942d094216440b01c0e000b400048064850034401d07804403041c00c80f01d6500c00c241400d940986100292080a444c000503100ca04950111481c4c00c0c1454215a520700c0e09140902c0d0b060b207003110560000780f609002503801d041c1441100e01c2040c0e0b0b10300441c11555000204084c10300e000c00102e40078029844d000001407030801c0002070505003001401c05c100d5101d41d561080318010b5002034100413000391000c0f0308176080400c803544650042030003480d9603107801401a4030700c00c0c0c0d8030072600307c0c041c0a0b440c803e0540c02242d050290300d00c400309640e5516224012645d90140703054a091030340601e03004000d00c0820501d14001080c540c00c144000c26503070107441c00e00703c0c400c4400c010761927000244041145443d208202c068100f50828544d1400380c600007e0541c0150b40d034143c180701d000804504000400d105803801481c403403071100c0d51240f881081c1c5210903001d1300c007204c0725070904004003014902040c42e1842590 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 189970557 1250 189969307 189969319
    0x1207080a022a1e060c030301031101140a230f040513020c0c0603151c02030c030106061b020f1002011508010209010e04022503050c0709021213151a0f0609 68
    0x41c4680c10001e041600400fa201e5603900c01545144503110300d406072004518030009152a50b145080000d02c80d021801107a040040c4002400c000c04800015201c410003e4a45440141c81d0754612480180540050103100c600c08030300803024002010040c0b069910030390b0030340000301c2c90705c400100307a009000180c101604941d02610311814503402655010142070700380d4011405550200d041802c0c160004038031058000030200c25400c04115078500d110054000700402032400c2c0006046420150034400382c3c18030f1400f03410955480c0c0c8080a80081d00a0200c0781c0b40401c0c3c000030b402008101e84c6680300f01e1180c00c0c0061000418400d4581031003060312402a2400d416042000039440742404041260429010f2041e00c0c0d007a10592640c18820307140c0e25510020120420720300403196111400c1c4900401c15000004144142a9005005804d10480d40d0b850381c0342590006008520303940980d032500300b0640c00441440c1c1c40030310030041500c46030450f8900405000c01e922400c0500740d0824 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 189971807 1250 189970557 189970633
    0x30b060309030f070305120406061d0f070807140d0f110403030f14040305160306180c0302062d0a120501031a09011509020702040b120604141207080a02 67
    0x100d8400081c080c13a8400e2414501e01600c01c24044841030080d242603c040d55500e00038403065a080400d00044158000c5403001071070201d0415801801c02482241000144008910b030755019654050400d1204200c41e0380f14100003202000400403240e003c01e8103400c007800c1e11010f001400c115419071303405070340701401501c000c2d409a84001122020504004007000700002040d4103000001e510402d0003060340d2601d203035051410590b2852a880b0100402c1980440c0000e203075103181d04116039041d61450b0302c0781d110a0244a2144101c0719800c1c5914000742e815601c82007450090031140032507100c0c1e086000702c500e00042216800d00005100c2c4e00c141c113980300485130800d41a076000e41e61000110b108070410105a00c041140e0f40031a25980d00801e007003003107103014081c2d0300c009101610815046da54805180b50b0728103024001802070031a40e45281c401800c10700900c2407205282c028156282c3d03444c68100c2c00b030390011008000500a010f07120307a03210034916aa481c2043d0702d8110b41024 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 189973057 1250 189971807 189971827
    0x10e060d050705090a0e04030305070503090307020d0614100602191a0417130f08010207080304020607030507021915031b032a0306030213090206030c16020d0c06030b06030903 77
    0x80402402c01400c0c00014000c0c201e45a44100703001000d0111420071070980c1c1001e14018080d144047c02d604207000043c0100010711400005445059404441c1c3c0d05550040b030820701c00409180191404c0008680308100c84000452518030460300282d00702d405448012480e1540c03151500d00041002100d02c0d06825075006a01c8800d812502030300740d804100e014610180001d60004042c480303004030000702084040e0003440c550009000b1003000307529240d4155101c0b100c0341b0000300001e104400204209050511030015180740c0750307001d4050700802c60641411910040b10384240000540b400340c2820440c1e20a004414400300b000030042e01215411005401400150207400070b0411040130300316819502200c6401e20907120b03240029902d00310b006015480c00301180c10000c0341c3c2082500c10050315050b0849901804001d9043d840b00107004c07200541704000e4a000c0d5100c7d40e03601c03510091080d4010080d08079055034608002c80d58211091100b68041100c0b880b2039600280801094 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 189974307 1250 189973057 189973061
    0xf08030903060a1d070621090f030f0507050111070210110c091305011410080307120e0a030b07022803050904110c060112020f0604050f1e2d010e060d 66
    0x490b59040780007004094281c00348074a071125070b1b400740d40050103500c2007103540251012464110b62042c1d10030b20540c5150303240c1d55900e1810040050406c040c00c83c00c11903c8d4402c806a418060b030040003408820f9020940507802e03088103105074491424000070854641c05210f82d00b207400c1d00c40c40070300003c5540d0f40030400c00701802454250341091100604c000201c080c070424076081503d04c4e000d400ea04000384200a2021203800000700c03684100900004074220341c00c03140c10707034880c0e01d0009083d40c00880860034140b0705900050a010b85402440318050700414030041c00340c10305000060440d210284128280c1e8150401740c0410010010390a05050075040010b4042c948081c0c0c2d85001d081ca03141c0c5141c10b1003603002d0740030501c12154007021403070b201c001c03c00c1c494402c039541401d003030425002540da40d81e148455440b030ba048103590000300c290000c0c8245102070084c0328800c0360911410b450700039103c03640d6000c40704110b140b086c0c40d590b0042026115000005d0300003400c0407d0f214081c80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 189975557 1250 189974307 189974321
    0x9020c0a0201110f03070f0b01050904030212030912040608070314060d112106010f0902120601050a030f060b04090615051b070e040c080c03010506010f03020904061805010f08030903060a 82
    0x3190141600200e20414108010806c10303114007880b031050b00b2103090880901300103070066441031940c41c05200100b82d0001e440840300c040f0740c4074565a0344840d050186400780e40940b52800c440e010500080d603540000c6a54810340e080d86082c40300c101441890700c052a01116415406101d2404010100341620303401461033b6400340089255104004420444a0607480c0d03080b40c59001c0d00040c0103881280035000021b120155055040c2100072519044103440200800d0400001188640c0d08511a4002c802441542602086203075154a40005c440d480350081c100d455003009800914810390301012070841180b5590310f4207003000344e030b020403400c03c8861340a0046c1c403417060b000c03809140a200d2203000b01d20604038580e1051915040b50b007400a0310901c1031113a4500000c114250b42c020484c01820b03c41850f0050707480041c48001001403072540c2114160b60001001e041ca905459031007141a9080a20110115070380e9505451340d0303201d0000b069402d42c00c00d0001c15a800c051380c01441c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 189976807 1250 189975557 189975587
    0x5070f020402040b0a11190b0903210109060509010803040506090d080412060e0f0a0605090102040b0304060617031e070f021003090c05060a0203181216050a09020c0a0201 75
    0x468100200e800141c1603800c40d8100200c041d9000a00c4158036420035101c18110740e404016042e50765508101060b02625402c01400d1100d10a0000340c0300308090040b110720b40305228520030302000000501200750400d01906200501d0140082000d00c1c0031030589040710181d1008514090902d02030106a80100c243c1680142c41c050b01c000c00240e009000d080540443c0d18102400035140c24840140c450468001078641c101003202c0b48056404903450090b103030480300c01320709130715410140d03070091195034040c5063300404803d00080001c0d68000c7c0c0200c0d02a0440094001454100a0344a2142415000560060046030942041100003400c0321034000c2e900b0080019840c1c0120f01142404d24401703002030f644101f400c04101d40380350044040c00b41500c00c14104034a248010703580b0311034136001c215030541d01c108040e40f42e0f64903240c0d000208440c400f0740d10a156032400d0041d00d034802d07008030b601c140d42100000c07500a03a14402da810b1045a4402482c078000142c00545200fa9034511803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 189978057 1250 189976807 189976823
    0x31b1a09030304050a09050f0c040503060f07021e03030603070e06221803052713020c01110f0a08130309030b070e04051314010209010503160c05070e090123070507 72
    0x2503070356526400381e0006c1212000206452a001c1290801d80c1e00c000c050102a960900041c4119100043d580b40c0c40840c08040085540300c011003130740342140564100c102d5801100140c500b21401101a5000702016012074400981b580b030341044101d0708440060b0400100d8a0000a403010002039130082c0c4c0c950b2100140071700621400a07100d043c0c0320f4081e03003c1100041c1e80310070b240d0840c0f240e0900740c4014401c0501c9094140c0007504600041008404940d0040742c50b000c2e42600b9409030343c1e0400d011141c140e07a400f82e154280825001b5101400101c4c10000c001080c0082d8151480980c5a06a49140040b0706640e1090110a8050645010003242005188198450f44550b900408012022814541031850f10401003440c010403019140d005000392040c90740c100003500e4014030110990140910300c0c0d041129040e114000151613885603a1000403c11314800f07400e40541d420200910200d104610190090448a1401078040e0000c800040d07406104601400d9643d21403080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 189979307 1250 189978057 189978059
    0x509040f032706020c1503010519090603060c080106030e0d0f03020c0d18050a0e040602030402061c200a090603020c120d060504140c0f03070c020d03020106031b1a09030304 76
    0x1481c200b503444900300320502018000288003c640400c800e4074180c1c8121580c0201d003158048034a0103020601c070f800d015040b000d400d1800e210b01e105080c00a04042c540810a041e030300d09068026100040700c01000c21042e40c0041003082c801d02454031000c08040c000d000700c01003003104680713402128104600b00744e824860399014007014442741c0c0f80044150380f030b4a0480c02a800b40100122650700c0241300310a400400c10642c0e1102d0500381d80603420040060b12603941d800420302d02c0c400c000c120005551003c04208040049901c80441d81d40340d403141120350034480340718104601c01c111100020a42400040188601c00d40042c0b403118a19802d5409020742c04c1110001a044080c0c05a051502d6120920907803c3c188142241c14803000012119400d00d04000241403041031045007400c00c0000024a805028a504001280d4085c00e004ca05441a080c003c1c0201801e02080358030f40c0e05034014001d038250442070348043d0f8000320b030f058074400d9821590b29403661090301426054001804 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 189980557 1250 189979307 189979337
    0x121606020d1a0109091a10030b030601030305070b06010c1a06510f070501060e160801050102030a020309010c020a0302030f07081002161e150f0b0402040509040f03 72
    0xb0414005011003081429400050001d00405202d80020f4a0039191007110011000c46084510700301c103041d50411114291000c046020700400e50f92290180710300070001003010b41c045c0092400c00c1c001c1d81a6405070b12503070011104c4214441c4064500342c21001d07240e0b1440c008a03130494000c41c00074048400340c0541d100801d02c501305031480c00700c1400341c081000c0d80c420506003408074900842c4100300295240f0b983c0740c440d9014440d0340c419845008150700c8104a000d6200b203024240409040300a881d0103010024045100740c140c900081400000058035400003050303c0c01c559254001c0c5040204580044500026000307050740c1c00300d08a0300000150b2028051422825400c0300174003c414144620a86845418880000141c0c810003680c01c00c1100300c120020303445c0c0d12000250b46084c0c001d0740760200021046001d0309080840100c0e0529208a41c0503640e0b041c0841014404541d101007003104070b010758852a60042c18041c00580003e07c09c14040000e54440d0815000b04a0000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 189981807 1250 189980557 189980561
    0x30105042406020a0201170f01060c060605060313110114040b0c01020417071d09031206061b061f05030a02043305120a051c0c050609061503121606020d 67
    0x140c04140075821a0039104c0c00c0d564408607014818250300c0f00c40205051003110250311007014410700c3c041223056080c0074200035242c0c02040041c84000c09164482c1001d583d00078050507441c6040f10080305c09501c000d82e035401000d45051740080810f13403500346131034419035403211350001c2d03902107855508003c003052010003900c3e42c610702c41d01400108a218104000000082c00680111822440785030410001c0e4030000100d0301c9038040c131039142189880d403001242d06401807006031180c203404010080c2c00302400150280c0b00f43c004821030f21080c0285c0c40403a41c0d01a0318020185c064000140392009800c0075080f6130000c01105100c04806074007410b50391082900815034082019900303104012030b01c0c1500301494041c040c0c01c080c05c0380c10740d19038a881d602c25104507160125142012081280d6000d01410030702c141c0c006007500d01510b0400402511007404850090181003080d07015445410005a00101d41604101c12407802c3c110b04000d42c6421811582110015000c02210102446034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 189983057 1250 189981807 189981809
    0x30d060306060503010c0206091c2a0302010f02070f0f0201140d02030702060a180201030b03121201090513120c020d060207030503040614150108040501110f030901200301050424 78
    0x81078001030741c5003802c08040c25201a076004a04540c0544c041c001c0c1200d0225107880040d5040c1d03000340081c40a007000380c0320942680080461100c6201a2004580500d01040302c02e503c0b95000300407440c3d41241032030490242c004040c10382501c3c0004000090304000b01000814014182124482403a5030f611a00382d101c6441c01d40015008000d000071160108503040d08142024418001c4021800b100082d050580002a04064403001151955141800b41400844070920050381e188401090909045e000b0302c600a042880c00d400100350749051528500303016802800400c1c081440002100d089001200a991007000c1340c082d880056020f1004160039803080d01c071191a4642410038a04031030f1720700180c1442d89410300410501c0c00004840c100d5095007403c042070140c8540c14402e00400d000d11940300a0311000448054040c01a00518803504015000b1b10032400e400400c003082c0f003c3e02d500524289030a00040c0540d14054001c1b9085660103601e13038030032000c24240445410f8207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 189984307 1250 189983057 189983063
    0x809010f1e0501050411071b0b0d0b181e0c190f20030a0c11030a06090c1a040b28080a2306010c080c0d0917010b0904060c02030d0603 59
    0x2034040d00120101c0c03602030705004003002c8400300544a0041703009a680c6c45802c00045c10180580001040400d04112010180c90309507940340c0c03074400c0a200b10000700864401d0700d11403030000c043e104507c110b402c1414400c0f440c4080445030644440700340085410050192000110144402e91805102c002c00201d14201c2c3e6889010600008001809400f41c0c0c0c6a80e4200b0011541007000e4034030000100c60170610a80f40002080310f0b141020030500540b0046c41d82d05004040390300c2c0c00d0104540090a545005125101074507644040122a4890080d0380c0b103039980c82403204011544c640005090354413000c00d1003000d202201c00c0c0301511b680c443d04898021a101c841844a442c00310300c64035020302c480400e000300b644400101001080d50050407941004491141d0a0401000c1400d0b034603100c1d070744400c5034940c0003d030102414001160240c03000342200141103003030b00b41050090f0050a1005440c10540c5e40312500c1d80d8000d4000c5451807415480100440b11626000d803207040300940c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 189985557 1250 189984307 189984341
    0x3030518030d05040b010611280f1a1e01050f0d210e010e0f1302190305040201080f04020907080703021323040b03030f0904090206070605061008070c030809010f 71
    0x203898900848002c03030607000074041000c088d1144420000025410700300c1604403500c203d4803820b00c1c0d2001d15817501d0080c001c10b01c81000d107804042001c0701d124036004895091010000ea0348440c140b48150315080c00c481784205941004000500300941800b040043c0035100d01002d01d01c41e29203950440030320a4002a9800882d05040c20130351004107002000024a84051000f040c00d0001d10240340000c40a84280b481c0e1200b82450b030081c2e8104c49804501801c5081c0802034118060004c01c8111810790101d181c0c9030006081009158560303100b694005c0801016446040089849410040902d400c1c55400c1000c0c0c003000100450150040055010b8a00c2e1041142040030b0a42e02d58140280194107116070b14070345640c0031040c3c90300304404c0f443c1c580d183d0190b00006005090607000c041e410503000100102803180c903401541c45080140c407060510000001c048500f42002c6078140001000783c600000000d01c111a10341d0007a80d0900081041c5140c107691800311080e44106000b084 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 189986807 1250 189985557 189985561
    0x909070c02030606010221030603030c0a05030d050f10091a1c113a08040303030506120a0507090b0102010f110a020615011b080c010603150b061603030518030d05 71
    0xb190030412581d00c00c10030301c05090b00900440c400b004c40c0c0c41070781c03000701002c1d03000c000039030f40d5101082900c500c00c1c921030403114940203500f1b04688a500071003929410307509001c00110012006180385c1d0003544200180c0f20742c40e103004140001446e116070401c44244800c42883d26035a144032034100c032004a1640c080028006160698010290300003040c001e0090101d02d5010046154200703d8911144081c405868901d0a600803d6a14000003c060401c04035010060540c10340c8220710031001650310411801003803540d6036880004541c006c00507440f200060203401c9903078101100d42074042c00081134651580b0080020740352212104001000e010880c08000e5604201580e04441455500101d481c60300000800e002d40b0220005d81140d410041e10080000083c1203454142c813081c000c118107a2039192170541d0301c40302c01c2c00c498500d0034051101400d00c0d04404945600000400c0401240080c1c2d8080e40648002000c446010804501c4802c81c01024001440c985545038400a224 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 189988057 1250 189986807 189986809
    0xe180103060b011b020306060f0310020403150c020c03070510030603020402040e0618010608060616060212040606060e09060f06040f030506040c060c0206030a0e03040b0d021c0915110909070c02 85
    0x304444441c1007149146944d000405a280440c001d6000141076411002c4c0f010800c02182c0703004000682010442e1000030000140209114404000c90004409010259401d04204d98845074881c0e4107901da0031070142003100d0f140501d00c0e40d20f01c03015800e020902542d66000a030898203d40d100001c0c24084a003004079900e000c0b400800c48503c0343d149820b0719414103038014840341d0f006005034010000010314280450306008940e10240e40a8803d640e10031040c6000311704610156811503180c2c0c20940080390b518010300f045018080060110142a81c40c94108440404102d14240e0031440811010039889549425200503600a000904a908142c500710b00c494415030700c004c0070000c0030340450340181c0d1110201c03900149200800b08406281410003401d5100e558401c030798010001806002c00d060302d03001f030004603200c0801840140b00c1e51030710714103642e80544024040020342c99840f40c0c071281c030351000b001038103501e50083c01d00c280000402c5406070700f52014004180d40c007405600f1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 189989307 1250 189988057 189988067
    0x72a030e030705090f040b04020112020d1d031c0203130b040c030b090102040b07020105090301060e160201050a0605060906220906030209090726010b090c041d0c0a0e180103060b01 79
    0x181400d1310181c030b00b454060094a042000980700801e18101031000c10256071042040204100440b84110368820f00340f01d0120040c50740c0b06036180c495181074140ca552880c04020349502110049141110070030055441c80294001080e56205038060a001404107070300200c0d262045208000c2169098154280380340808002080c845942c1e0040200388a61031fa01400d4034052a4282011612590b440b00001c0c05000c8541044403460042c10410020070482030301c0d84140b0349150003c03c074545807504070b9400e4402c0da0080641286d41004461003d0502000400c0300c0054800070507078512143c8504200d07008154040e00b2241d8580c8410301c194a0304100d100d402146200040c0302181c41d21a2140009070401d00070758060384080112040c4803000c2d0890000c5000080500e103251a08118008440d0414050340b1042509410344000081c0324410460041603005242800d29010010031110060f004a4080d0030100800001c3e0b802c030111006603018501c00d8502044241d603007400140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 189990557 1250 189989307 189989309
    0x607020d1d0604090903030b10120f02190503100f0807061119080c031303052803020304050904080c0613020102010f180206030402030c1008100f0608072a030e0307 72
    0x20700c5000252607030711969184215801c4034610180442c100c040e50505400030280d08007030301e8005140c0507400030b0792607025060b0341000409080400004018034a85d404030b0081c01c2000d24840195800754441c640070f10f024541c0042801c2051142d142c48800f10710200310786a100b03e00c59030000c00140402c6803c42c10602c00d040b120b030001c0800003402603501203c0c050106c0042c025081c0000d0040709000c0500c00c44201601182c881070225070740b884d210b0b545111620941031911244600c410300da6020300300c1c00d1032085e0554019402c2604140401c100f000740544121001141044003a0304100705000591043e220500e011010360a10b000180c00e4509100940815034a082c130701100015211000818458044e600d10b0348a6684e8400300c1d113082d0025940c07650140c0b0780e0902d020261342c40040103216858000c1c424404980d08c040400360700c60715025840101d8404400621440d00c920b001341c00c2c3c804a01c03441150010600d181c1c0d01c585000050960009916080000303039801c1c1009a04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 189991807 1250 189990557 189990587
    0x70306050f0124030e01020c07060509150406050711030a02040c0f02010606141c06030b010e09070801110d020d0603121205010806040f0311030706050109050105040506090f0a110c0607020d 83
    0x2e0440c400b0781e140541d00030f41c5078030000181031361034004410454095058504458000044411f161344441001e003054100b065000c0c030910f03400000700e8041c048141550211620307503d8050030407074660749425035400d405586ca03405100d104410000340e5141d0240c085000e01b02e0f00c600c540418000380003401d460058000300144041045420506145501100d5209490017010101050100b03010406014154009403809015400100c0e076603d04080c0b1364000c0700c20804403a0325030790301c10301c19090340d43c00c1c00f8003946c002c01800704160144242c0c004001614000342c00007249922960350311065048440701030700040c0c018501c220740300410310505014010040007061076152a80d1548800c03070071500300a04005a1100d204107a00c0704209841086a0244052240350b840340d8406005200034030502c0e00c07660800c00440c50909007070010364085c290760049103025aa4640f0a10b010f04030f03480d100c0a4100040200135545082400304e43c0c0186c6c074950140c0f1000500c01c0004146403100d070602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 189993057 1250 189991807 189991829
    0x30609070c0519030201020c0f0304061205040f03050903030d0e010e010e2107151b12230603031b010506030c0a080a030f030e030c072603040302060f0c070306050f01 73
    0x4040441d0002030010103002081c400000769180a1130308038061f00501180c80c40340c0c03113004030500c4100390201c0540155401c03036a0b604e4402c002031401d80c00f40c0300c041d2070103000304036002d01740408640b1950040100b400b014044a103004902c4620381c0c1199101b00500388265540c281194000718280900182c01c11408020081484142c9107008000490907204d80043e100103008010080d80d0189100f11079070381041048581d011040500280c1c80e04115040059a4142d00300b03803260300ca104003418119000c841040006404041840504d40608200d615110900c21503445207140341c04004040f00d010008596400c3c110241450305c141840b080d481108141824094102c2c0054550101c60700751602c120301413240c1000307800410403440c00342c445010009022940d044001151800c9a03521039030f81240281d2204414030307810f0108840d4900b030304200010000344ca0007201400421701403400031071030b201c0d000180754500450350b841156060303211001c02081c6103802d07842d513004090348484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 189994307 1250 189993057 189993077
    0x510060b0a080a0b1f02030409060603020a050d0902061c0b09060103060815060a1205030c060a0606050406030b04020f030906040c06140403031b0606140406080714010f0e0a06030203060907 83
    0x4042c08034000140034014503541c03510b01c0720581d5201c072030545040080780303140301d44905500c0001b510380e88a400349499041c03c001c3d000411038400c1c0700701d5969045d00d544141c1000029000f03100a03007034481003aa4420014828070461282e145c580c1e0107076810300c00000a800d100300c0d0500001800081001d414149032070010401c0e5000450f021a8042004004600c141c1c1c1d4640060111891074100ea01345009134100d08040260000050040005450031200260307a40200b1100380d03840c030b01840c00020403d00c0104003060290f04803502442004001500340350101c46070694a4104031808542a0b200c4418002841600f0040c480504540c0ca48646040842440d10000d0b00c211f1000400304000e21300700c0d54051002c0c030344411006501103c14400c01d5551020309507181c00340507415100c0c6140420015598400041c420101c0302020241d5400005e40c90054072064018029007050044c9141c0c00038003607507450316650180030b081e04c005880c0e0030002c060050408004003154180102416 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 189995557 1250 189994307 189994327
    0x20a15140c011508061501081009050408030a0b0a14040e07090207050309090703020a1707031d0102030718230d050106090203071d09010e130206070506010e09070608060d17070510060b 81
    0x1b80780c007600c1000e081004841d00e8981091000060540c001c2c03107410710380003d0108000340180110700504c1c240c0c0c0c0a00c144620344040012001032449035200d50103203006c0901860034a030708907201d0003001c0c13420740d80001c2c2d40305801405d9a00414007200d6070381001880ca546840c21917286500860703a8a402c504000b40c4003000781c07070400b00070315200b08280b03903200181040e0301c80d420011030291209680c0c07074180b1103034510034040d410a60744480404d41100072003000a088250b02421a030291f1403a40700c08a00030503101c20100c4210000c0e40054408000201040003400381000901c04030600590300e207800c01004154109610980c204640305204c000e4260b034035000140e043d030f20b00310b00e01e107402e44400050900d8002c512400a400c54008510503083c8080820800d040b611300311603200d025542c044841c0e4032442c1a01420000ca0144008500d5509000302003c2d80c1b5446041001d50406613942d03d607005401400c822600780d401445114142c910b18094031009182d44101c150501c3c480070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 189996807 1250 189995557 189995581
    0x1061d010e0f2202060c160306180201080412020c0901080604110904030507030e0a050a090204050f120d1107030606230301020c12180d030c03020f0307020a15140c01150806 76
    0x60b458101010f0141014002d40d680c00d404c0b1020721a4502c104eaa0341081c0e0321041050007480d100950f88180780c04032110360030b2111410039910700e605946004640d0740355601c0348840610740850302d046100303241d0070030160b464035034180d4041d102c40ca0040245280c2450400703e0b80c40300001c45400f034615001404006034004003603070311280d0b2500300f00101d841d481d40414000304c1268049a440b80c0d090800041700541da500510035140140c0c2c01c42ea20740380007824054099403203842055154080b60701205c0079072041c40d000184028140940d01030aa0b81d0700c03040242d9405400c1403040c1e104100400800201d1904a004003000c00e6001354141107510082c02c2c0c880d8003036140e6086145000074156507401ca80c00d40c2c0c10300080020810501e046807420f005004045605040707025100b586003100d45407800005071781d0600d50041402d4883e604008244100851f003400840601011682040c502d20750b40018113041510704000050303080c843c00002d2440c5000350f11044882d00182d05000000b5180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 189998057 1250 189996807 189996841
    0x30216210b04060b040204090f0506310204081002030906060109050603070e0301020919060807050405060702060d020c010504050c0f0109080601210503030115090816030b070201061d010e0f 83
    0x104401c00038a50716402c001e4040c0010310000b81d40300f840064007040c009001d62041c41c10403007903242008643d0f580401d10210348050091070384030b00501d0184407000e03205a0342031101011a00c4016080680c2e0760201440c10b540c905160fa100d40e00401001070416003048131603888502480d08500c502d14107004a41c041c031000e440901042940004040603440940441e0520500500030071806a408000404060744900440c0000f45002001c00c964a10540c140c80503030b2802841e90340391030070507400c01c5030719448504100407840e000d0003c440030741d0f828800c0340c2c82180500c4c040c1819907409020800f110030348651450520151a90902c10f1640000340c440c19203809080c03400515000f03001c091041516030700300410f603120020000c0f4005c486015055520071040d00e48041041c3c07101c1a10b911120ba10040041c0304041c458108003203805a800260011064000007130306a440306c0c0000b801e00f2641c01d4406040c02d00304010802c54000c1c40d040ca5104144034241d5500e07090403a1050896689 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 189999307 1250 189998057 189998063
    0x10e040e0a1b0609050111070e04030e061201180213030f03091e150e060a08190614130501060206011406040b0c0c03010b04152105070303021621 64
    0x6100008950031008000e5405007541100301d005000800122400c104009070240c100042d000c054006140c2d4081d90989040703403049005008080d09121603030b400d120300208140e08010108600510584880307000b0a40d00005001501e89503041400c917003100c20340b8445800810307104225684110565220304016030358408410304200d0801d05040703032076845940101495803030128511100302e040d071500c0c80031540030001140d40d0300115002a51030804000c0c0054010340108216802c852140c0100e690041e07414680780c4c1145005202c0008403a150341102c0788030300340607c1561903480e200b2070414131840d00420900456052490080d01d0b11010320990b040181d440900d5101075440d0426900a419404015500c0d41c41c003400d15540c030001d030b5101c540217501e0011100101e003881d00940b1902d114503595102c543e80341400c9200141e5280a4210b041042c01d00c907400042da052009a004500950061481210b141c02400440546504c19544c41d141203000541684025040c0505d00350 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 190000557 1250 189999307 189999311
    0x3090d080601021209220203100305060702030307051801090b0a05040305010b12072102040c03090b090703111005070c060206011a120403030c021e030408010c020303010b2506020d050f070e010e04 86
    0x12006d0b44a06110a107120314400160004c8208041005d10201d800c007246d0080703040b2070568541a038182c3c0c403444250f641c400024410446032141d100310a296510507041803401c48042555100c205010350450a0b500c00003070070014040040c002e00340038059400e40f088901d4261880f040ca50280e0322003103407251001c00c0101d0006039001803200303145042c0352074024100380600c00184e0b00c002c0c000c040d812822141c9403013450200c2c183d4400000e0485c2521390006a0b4a41084d10904101c042004c8804c0e031820031900308807100c0000c100c20810310081072150024043c0c1c4d414424006601e8410480e100700f000014040303085c41c3d002c0c1c21040c0b500190141000525100407040032802c104102c40c20103c048151042e1000e10b2100100510403100408000c1020340c202c01300c00c0b80c4910003840381a090080901845922422a900c810308203410421030444488007941c4800980e00000f2032407644543d51010002e0711048010f80c281c0c456103502c1c0490790304159000203852004030030580c0f07018603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 190001807 1250 190000557 190000579
    0x4050a0614070b0903191b0212030405130209010905030d020304030f0609050f07081605031c031e0203070e0103090203100e0f03071407090b0603040b150603090d080601021209 77
    0x101c00d1400321a0380c1a0404060651494920031043d543c2c0d00c40e42c89540002d400f03840d00c145040c0724108001007079206080d80640803455400300081501e113100345003e140000c0000140c69520035030000145215000e025803034121980001d031200170745078041c1b03000741c1101c1b940800659000c002c40e01a40d130f1207907e4202c10402410030800030510302c5c000130300034031a910448014060026990301140e010320b003285c0404c0303404000151400740c00e02c00c0c0e9030994041e0b100090001d10201c48080000c003103150001d2071a1414010000b621081442d013080b041d030002c2030001c080d6001c0980150b0b03d10030f080a100d40185940130075a03a00b0f00c0b8240d01c81003992003041c602007200034424851000712080441b40c40c2c000d1810414960030905161021a109114002a180c00103000d03030b20041c1e01c004c000300d05540da1601c032100000b00042c0394182144403544401140c2d41c501e005107003e844210300901e0901c000c3c5d4405019100007402031410b552013001d2042c49818890201e40070b984083d01d10800b04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 190003057 1250 190001807 190001837
    0x60405011103010f091e0f0218040b0d02090a180c0810140703050403020c0406140406150219050102120103290c16030c020901030311060106030603151a0909160b04050a06 75
    0x700e100406c0d41081c01c1c3c1003160030100880c50b500644107201e0f9641c0201d210150b01800c10003142c0403100070175080386508802d41c02501e03002c01c0095018040c0b20020441082c603842c1d40c2144620410300300c030440150b0380180440340c020019032040954141082041d001c00c5501842c1214005041004260302c800005040520074445840d120f00e01074010300682c2e03220588a4040ca02941c1c86500841c0b6050001800a040b84000c01c00383d00b02c2e030054051f041700006905007640b25208141d58075902081084030307981846908034000c1d40548019006c80800a6101240e0300e4841d54010400141000b0b02c0b007042e000c4812123050000a00c044081d030700440c034066800b4a2405406580a030072140000f00380358000d0b0926582c00c1080050320510b80c0c88240541c102ca4043c04007901521103100052099200c13a40550b00802844881006900c405400104486000c0b41c421030a038000094031039042c0c24290a500140661300e41e034a08160800000c90125040c500c14a0200b1101401541c25 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 190004307 1250 190003057 190003091
    0xc061e22020904050f19020f0105090126012112120e011503030f02060f06091302030109030c05160e0c030a1b03090308070c031205060109080f060405011103010f09 72
    0x38040d07028049441615160908986503458107070303c03031483e000d5800552403415107a0072910f240d9900410b82007002e501400119000d0b0840595141880712100c11621007503040809880c0400c0c00c860007610540c1400c406650680c00255600320424040c00030600192042034204039903a201c1ca4081040c0c2d000c40e83c1000031303082020010b0174551a00c89412a18020390741c8030360039240203464071000001640022a0f036840c00f111804030000b01c08000c24000d04e840d106a54014401034001c50800c905900042c1c00c60398516411000300f480070a0400400005010722120803070f020b06250702c41446d120031698001c0c0024021b010410700040044d0080000b035204200c90669030101d01c102403800c100c050010b201458041c0c0100f062000040c00300780c4075000000c9110b42c5980c468000103203030800d50b0082e100103000b0364140b040104011510100c100410400300f80707500e0042110b810701e401c2440c216640381820694203c0304000510292407040c142804584800000051002d101404165 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 190005557 1250 190004307 190004371
    0x60c030209040c0c02032b03090f0c060518040506030309010c15090f0b0901051302060706061a130f080606100e03031201180b030d0c0c0b07080c061e 66
    0x1501c5450040c8115590764010b503928404c610035400c07501014461103178501801c044c002d4261960102080c2801c41c68465000f8003400c41c41180000d21540d407030342d200300400506400c00c03030001d800840d81454035202c44400c13200900064038104203a09111010036280d00c01c140c3d00a041c009084d036210300b0891031140400b170401220000304000e00c010300e0203070702d40d0b003070114142c4510f079164000c01d000000610440303005004000402008820b0b80d8280103480d00f0000c026a0303020398901c8001404450500c802c0c0d068000031910035a20300c01100c0a0311064940c1e008940034000044c8240081500018143e0300140200c420740c08000c100b800481300040c4160209825020200b6038042100c44c400c801816140500000e8602d4280d0703078181d80841d0b50858506070700d544400d9031a03c909010300c012041c1c15006040c000c2055841e5030441e845544480e004582070800000d2081d03412009104407908544441c880321030555a40c481c03c8030070040035080910008400c003900c0208040000007030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 190006807 1250 190005557 190005559
    0x4603081501090503070605041d010806070e0315070e0406270209060c01020c150a090203060402210a080903061608010302040506040b0306091c050903070e13050a050a0501140103020d060c030209 85
    0x30388165207412009007690049e00c516554450840c0c8e0303150198501d0750040317042c1e0b042100280141e42e00d00c0811140c55021603240e640500410000c427000c00f6421007460310542203a101c84460309441803d210840c0c50369800b60407800d12511516003602100903a4144011200c40050f0b20344a824001030610712403490f51554035031000404480d0340c9004903801e203800281840400440d501d170480700082d06c42c1d070320000350700d5001600020b0051030305100f1b2000c110044c2c0800f000502080e15840e2900740a000152070380880850041003e280030001f1030382c001014041030001c11521000601203000c103000007840385441d00d00050460311958801121184c00404680d06400e11540f802d8071081d0100d089179015002e4001110901c0c0107104841c15414080d00800c2c6003480d111702000355400184c620302d04d00f50201c94001c0402c80c100716507a45140921701a10018040e441c0c9036003103981c401c0401806822070f80040000d81d07224210a074100b43c01c4240400c0d11083c252085000380f048000032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 190008057 1250 190006807 190006813
    0x180703050a02010806310b1c170903060c070201020a0209010e04060b0108011214010e031c0b1906030207021503010b09041a0619024603081501090503 66
    0x1040c0200054000d0340e950003130300c3d080d0668991005200740c01c1243c040206020100e283c007003040c09101055403440c81d1220800051058820000070040403880c030107030b50300c46080107020051004440030482d0220a81e00d126240070b842c040801d45640009041070851980460741c2001d43e4000d0007041ca889900402007131081d80c50792841884078009680c152106840e1901070401c55008003545c1d0b040c0d40a11018800fa664250b80382c00c116840d8182800c001d541301c01b06d41015110820182540480034511001504e51710000c640480307070f40007a4140306100d03003e088644400c040c520035003602c900340341c00359840d2814000301d0700d8001148110131500d00c0000001400024a40c0a0a1900400c83e400e1020300981c1258540580c0c10070109075218030100207115098018004811190200f40107850401103000e0b04020544130700c04000001c500402802050040400c20441d02420a45000303105101680c0b001406507800501408191700450000310181c3c0c0610950070060200900f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 190009307 1250 190008057 190008059
    0x9090109020a06180e0a1a0904050316060e030304060b011101140a020a0219081e07020f09070c080c010b0108070c030804120201110c01020a0206061509010f031d0615011103121807 79
    0x700c4007c0c10300781344400382c0c039030350011601191408800c01400341e40c11500840c1400c91071034515918014820007101c20540e0782e5aa203c0c241000c0c000b40d44641d026080c00038501c0e0000d0000342c4074018021041e66076074174048001ea0301010721001c61360410410140140c072130340005c10691070040343c502c00156480744e0010b100c041101d404010402400c0300c000c1c400c80d0030b1a2410b003520300d00400800a40c0080c1645400303007242007588010754004102e103010f01c0841d045484411490340000c0104581c0d9454a00f0280a03580082200341c2002c0c051521489408890f20001c00d510340c0079100a1403903589000500703106100350410603401000a90599550200c40c14442c002c1d4020706d150710150140e100040d1092401000c04814001d84400807487c1030400001103036a4896000c0401c245942c4002d000340800402a4090309080c10f0b0004101600f005040040419a2912443d040181d003440046803140080140c0d0b03448843c4c6080ad420989414443d42c101030706400d0624a54818910 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 190010557 1250 190009307 190009321
    0xc03020415030201031d030906070218040b01030209070509090f15100816020703050706050a02150906100915090e10051e01060509060a1b020a0803040509090109020a06180e 76
    0x74032070741228401d0b2410040c901a403030300c00300c003403180021100003900240441e0749581003101c0140312507031008080070300307d40c01861102114002914151001760148006000b14200100102c2e0060010b0030450304010854000030039106001700303181118420741011410101c0221000b800c600f4004141117030070100300c0c20003005003004880310301e04c056440c4601809240045032090680350030074050141d81d4241241611154800380d010f20852140f0218800c90b040380f90b0290f401420102c000c6c146e00d0030884d0000f904940580c000e040303e20303e458004422460000e820b0021601d10b0807010400f81c4a02001c2c40c03d182008080850003802d2004012076032240e207a00f110446480180380c420703030740c80c0c0208a81a02602e006e45802c140c04201040c402e40c003610b10515110940402c1c110341042941c04110941c1803a031124216a101260510181c0b600100c4154042d000000030006112a41c0018104029510680051005413078001c40e000c403804030b003800900200c42a81503c2d0030800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 190011807 1250 190010557 190010591
    0x6020309010f061a040302100e0405130302010c0807051603020109050f0d02060c0304121b1a070e04021804051b07110a060815011d0a09020301060305010e0c0a0503040c030204 77
    0x910300400c52443e204001c100d00100103807031910052808442d5040600f160300740a4200c81e031035880e00510a4069180ca4140d54034010380e4801c1e546a45200b14032445850082d0a561740e150400060003e14005c0010199114098454401c010a01500e201d001401c05a00411503140f000e0a24062809401c0d50030400240440004041d60300720b41c0305680d5004041040e00042c0c400403c01c14039142c40d8940b0340e00c12100301c50300081215118000c01c415540325030381a0b14482107600c071042c554041004454010108061a1005440c1989081805015010f00310f440e80141da100c0c2d561813002c280f5150712160704280300510701c00040d41e04c032480c9c10110580780c04117015503c0f40143d81c4010417010b101c0d50300a40108441e40300302000030b04000065540e0314007104000c600001c0c14403a103c5550f100c2948100810490100681e4cc5d414210011705480c2c050300050051100f14090000720007182c4102c454158003403500c640c0b41c2c1c85a1034091800911a80040e51160824140c403070358100c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 190013057 1250 190011807 190011821
    0x12110d02030610020d170403030e0604051c090302181b04090b0406090c0e0907020c06120109110c0a030e010504030812061002010608070512030d0e06151c0f0606030602030901 77
    0x1168070f0b5a6080b041c010480e52218840d2200d0000b139582d144582d1529820b103201900107100741008540c0d1740c0d40204140c50140f003202d0541e0684d0204404c00c6180c40382440440141d52240b500820031800c42d00818030181c0b4005403910500c0e000030020300507491800c48540641e034088481c55503180d80701899006400040903d500c40c0c1e1501000040221592082032a401c0c07860f1113020f42c00c418001000220200100140d096005403841e182c00c90361250b00030b000041162070018440d506004d900c00440b004000003002da10400c2100c54010000012800d880325458901000041032230300040b030f8a40250781c8010401040814400642c1c085103044c94032684058030710018070800788004900342d88aa1060584980004205100381d00b40b02d03103000510720ba845c044914048440c44001d084900f04011081e40f0740004040c441d405140c01b90300443e5100c200c0343ca44103640c0180ca601c040260184e40200340c07a0408000000f000219000f80303008642014003151a890300300c1c0903d0182c450 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 190014307 1250 190013057 190013059
    0x80c0c040c11070e04020109030813150c03030e0a030507080c07050406030c090b0f24070b0f10120309050616060501060206061314070804080c0a0317071d0112110d020306 75
    0x1003610104c0c45001c0d81d10b00500c1150160b50700e1aa49145031501c201d01d0b0b104081c040c0c081045401c01080c2c08076080000b51010b401651400c56054581c00d0081c112111030001038401e0300017803136031801b02e9401400d450281d0703013020700c1d5a92086085002441c000d900d511054019003014400020300650f0003840c411108019018000c6462400401c00018014400380b03503c00c0102800b10005e01d229107440414640c0c0703101072403a005081d101e040301064100c0b5000003040b60007040224215060110b10010010125513507100811030340c0141444416004660151502103520b0391070030424030b1608082c0d50010b100b0003031035071500d40083d1101d0045448a0064000d4101d50340c40f100f4602c40c52078015004002e5003900d84504c94111a042400390058070310750300501815400e83e009101100c007261081c1ca03040b03a618002c8400a00850004025030244101d0307000001ea00b100000c1c2941001e0700034079001e200d0700da0324002c2d03c00502004540305460500400c1c0ca0030f104516a00035401950 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 190015557 1250 190014307 190014313
    0x180a18050117010c02070e0a090605090d170c04270207120206010510020304030b040c05060a09090c05160f060608190c0905040807110a09050403030c111603080c0c040c11 75
    0x50140c4443d091390070310702e24000143e00880c410002c4540342d5400c1034202d842d41d00081904c0d10251200e40079204240c80341c1d403541d0801c00300255070036002a40da0040741d901c80e0500005140207180b490540c09988a03c0b4160040081201007110340c19410a80200f10310701c00315110101410031800c0d1b80b901410240140c40b81100226a500d030480c0e01a100400b180e0041d80f030b00307081d59548a903102001c1c1c400c441950318110046199030fa400301034058400d80d65500b45c00146000707500003d03212680d450f80140082002101030303400c01291f4143c075a0390000e03120b2031800300928003c8020f140945c0001c00c20302034000044807026440310081c64081c01001d0134005142c0350302c4814229035082e40c00420303159040160310700054986103240e19000c0d004180001d80c40c0d4903264441aa1000c680480000350344507800680e1a82148129030031800c804003c019075001c4a135200b00c6000e05003c05000e540002c0f5400101c903004100c400d405c40409072007030104025030b40010b826a200e407650300480340 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 190016807 1250 190015557 190015589
    0x21c020706050f0603031e070206041e060804080a1b060c170603070e0f041e03030204180510050418020a260d0804080c01020d060f0906120206180a180501 68
    0xc0c2e10076041d8050680203003c0e5247c910441e2481c42528242c4080aa100005011503405a91241e003e070004290100d000340c186820404595040038213078105100b803100e07110134000460b00e840280c80c6940f21501303040c0307090340768030704039200c602203101c40100b480d030602c0340098405074420507207015104400c000b192583c44060405d610b030201401a141c0c00d1503a400000c5203a402181e0958119000700c03800c20213600031a10316000000c02020917800b190b0001000c2150b8000c01c00042c1c0a14000c00e01000785080c0700c410a18240c4c103d10401e845641c5441060802482104100c0511640200290805a40d80c4080c106403907135036505c0d030107124000000101994000c41d0803043c150f22940c0c0c12009942d6a9122202ca400065410005660a0101120311a11440f481c4064505807201561541c6400011001d60304030b17401200407039042424003801030f254030041d150700d21110390300444400820000b144940c803c1e584140c142104222245448116990040b070588101001280c080 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 190018057 1250 190016807 190016821
    0x30509041a1c050a02010305060d0b041a010815400201030506101b1505070905030d02070506030f0c0708040909050d03060b12180313240801090c03021c02070605 71
    0x2d22822030042e200e0782100c0140f40066109074072071039200200600881500c980c2d5103c00ca40807608660403240d01c6003041801c505c100d050301c0500d0040c002000244800b0b140c0401c000c0d0030440c00740800c509121414060085209480800b00710a2114885104a031034a20601c8810300b1103003c0580c00b1a00d018041201400c1a4131198401d040302d80b0b401c550544e1400c1c4100c01c000003080207a030b0344d07510411601d04c148100e00829004420a0b0385620300710781440304160805681e4131408041d540107041c10807854031007200b56a440b8003a030818030280e0b501d94100e4059445a0000240105400240403074100c02035409801041d001d542124410195803100341c00710303050740c0200c0480300c20a201c0f50f010921021455540b10845449118a0152503500c1500d15000807107607002400740d40c002440b1203c1d204038180198907508021001c4400000300141a00506004040303000c0d486030300c088900c502175011a680c41068018844001c2e0803008000029004010201c0d122030a00c2c001c2604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 190019307 1250 190018057 190018099
    0x60f0c030e0a140a080307020a03180807120c0308130e0105030a0c14040e0706171005010f0507080903030703030b1e030316050f160612020c0c0d030509041a 69
    0x4800c01d00c4001c280c0282c003501c44490700c010601c101c25280c451003051400003074a43c030145d03008007081d80081068013407929001c1d02d54143ca408564600305540010411210009046012903804c512184841c4419040c0705003a4a03a40d00064183c0000080c0d00140081c10340f01c95080341c0b403c8501d030a00c1d0b40ca620415440c7d607241440541200c20030f071070501c04649078000000b035400c00100000b030056011101da9040c103040341d000304003142c1c201180343d80001c2d9103030480354001032442c02c2c868900e04250028100c40313103641264082200124020007080115001c031940c0500c020200d90b110506890001c003d0000c054540d40101c001001d0740c1d011183c420b03003204e8040f50040181d8100a036a0820000d940d200480a0340d561040860741c45540d407081c070202034052040c0134490b01c01800c051028240349d1442d207910642510402039000214004103001c0245c0c081100c00300c1804041d81800c6445014464201c0d50251401c8180508036021030001d091080040d2485050b440848100e260 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 190020557 1250 190019307 190019321
    0x90509090109150513020909010209040c1106010e0c0714010f0c0f02070308030604110711040c09030503030a09080d1e0c020304030b06090a020f070803040c0f08032a0307060f0c03 79
    0x401c0c0411214200901011500b1084c3c0c0120088100b4491790f850f60005000303160b0581e4440101c0c0d40c001a00042ea04041c010750018121604081c0141c0001c041429035503d8144142182c60031020086203980014104451072960085082c1c1180c0c80040d00c014002c0c02e8074003804072500e01c0d100c44014680e0044c3c001c0e030355024081c0c0250581c0f03403844d16002501c1d4002411035520075907034410760b00c11582e05c1014001041c0a150710194503a0010240b00854030399092682c00c1c084584400c10000d0b4000045950040c0c0040b004079000003146803030722007409a4000f4002e41400c00741060700002c041c0481c9450407114282c2805060313a0f40b01d090f86c8030f1060b404050245d0b0602c20010741141008172030550032242d100310052411149000c0301c84c0d0340d0013000f021030320f1132000020f00c03083c00010400c00000d8405038035044603e0385001d454a0741c2e40704030610b134079404100000c807800c4003031210400031414402200b071369604e100e41d01d4030000800141c000a40c0e07481c907050a03080b04520902c00c00c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 190021807 1250 190020557 190020563
    0x3090909011e1413050316020f040e1b030a02100e04150e09060a020306010906050c03090312040e0132120610090e010204031a0c130f08010b011d10021507090509090109 74
    0x50302d000740007490644004a441c0007641c005000c40348000140d11203114801803514850060200400b02031601c041d1162330403120351082d40700b41251130243c0d44400705e0890504050410180140c003240104c1c001c0c11050321015224034039044005040c4205402240c4550307402800d544503581d0700c0c1041000c80c042501d00d1741c001130302810140000b602860084c0100705441048905255a060000b46025544d40380c003507a544000c1400c20210490b02c400502401c480d41120b40b9400c54201c2440d012510b14a80d0312000d07815407482c1c03540d61a040409003c1401d03100c03d80c1c0c45442d1000812203050550710407503482500d04a0900321788801031003a941680c1d07020380c0441003107100910014180300b014000224541080024403400031804203800c000307004184910000a01e007040d0b00303003150200c03d48103041c440c03c40c0c40d50340e556810b24031000445100701c800c0741e4102c0c0000c42c104d250440c220003031145e0240c200b09118000f40c00c080c940c0d00b140c02c100d400f100c0507651030704000e00340c0341622001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 190023057 1250 190021807 190021813
    0x2010224060609061c240303021b04091719140d050414010219030b1903060e07050d05030903010c050f0d020307030e1b010207090b0303090909011e141305 68
    0x4903007546410070080c24640c2e4000c001d80d08100c040300100c038200c0491500c0f100740c81c2c0c0d0f89040c075a00d01c82980d040820ba4550780701c404801851510081c0d1180500190b161740c09400a4940b0900c0d615544640c003105d4020040078540d05010100700491b501250b180e0701c100034126100c0d201d89114009002094101d580705605050340c2e02001d01c0500300c01b03441142c40b522260012042c00400748040c1c00e607241c1a078000a116005031a02800303d49049050074002e0800c00d881d0030030b21038a01d428000303c0b50703c085c0008002d404400e6641c1458042d420903640807602807072031018803000002605090104900804c0350f5010200155a20f11a05099000341402400904003090013540a564800280d00b004030b50f107500040c2203420510880204860b121039a2103401035943e04010440181c102440204080500940000d56a000d1240318500c50b6418400081c9800001c0d00903000c04030700c40048000e081031141c4240050201070504540245400c8000b6148010110894400365041405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 190024307 1250 190023057 190023061
    0x20412140a140304230d0212070f06110c040203010e071d100809121e0d06120b090c06090906091003021003060807090c1e030f051302010224 62
    0xa030412400c20214040d5540225001c101c045119005050301c1c420400010f1030783e55041c80b500c61400309907007a60780740d8181c000010f008180c079851106c1e807071740c0e0b0100d4054004280c41c804142c13400300950000006d9180840c00068503542100c000042180300d4030917210107100b414140801c81c04244255540c0c240140081003c0328042e03500f52440e10f2404a52000d6942d0440c04260445400c4041800003000c20b0700b0000ca040e8240003960042d1415500c0a00d05004002c80040c1c04681e8544810f01000004082d030482103281c4c009070003010f40703150f080e009055a00700100c4103582110201c1250040072810100340c9404000c80c1c40850008140c2c40b0203848040601c00181402008207002e81c1c00a403003c070240e601e05d070b91103907080031030340e00490340070b00744003070141003130090b500c1070110ba424134440d10449500080340710620a88180c5260010031030707a4040340680814520910320394035050502071801202410445924004e0b0201c9020b0070b0181d594004032070600c0c81000c43c065000c80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 190025557 1250 190024307 190024313
    0x608010c08190605090f0415060311011202120103030c0203060f060a030b0a1d0d0311040b0a08101203090501030c0c0506010501030e03070212010b0319121206170c0109050301020412 80
    0x10251000d441c0c541d2000507080c2c0c03120302117649600700313070303030240b4621040c104200c10041c0128540481410502d414018a0310b55961a0300940c1100703c1181400280056243e243d040e541c1075403102c043d401400d501d1540c1d01d007409040c0707813036426080c0e009004004c002448050a000c186000748406415015901c2c0303541c454039048000903050800b1241c0b9811040d01950340c42003940000381400000d00080e06001070064121400000f010b807940005001c10810259410151401c1c0070250410f21003d42c0d40816444201070a604454031140e006104c035000c2c141d01031801c40545030280c80c01c2090844030322083e603289a5406000f415940101e0051002e94440d8100c81c1da6462910200c0f42810101d40c001461000b00c0318860000ea0f43d20604112a032404100280b1403080c04921080101515103501c0c034110a08650b01043c022000e115082021985c0e000c84001c0c42c9800450316500305400102c1e485501c40c1c8101070002d469000d001c00c80340350610072103003242d0201102d0700d8944400c0da = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 190026807 1250 190025557 190025581
    0x80f070605070c15080a061208031602120705060a060515090d060f0e030309070902120f0c090904080a08150a05040b120105041a0709450903030608010c08 68
    0x2c50803220b40e0032084000401510301401443d04045940f260000d81c50705141c05422220207501414021400703161480c00718003000e04503900700300b0f8102044180c1d1013001d4240d00c0c2420015043c800b1000000312031040c0070020840c0b901480c0a003205010302a51007042240c40017070040102c800850401a404041ca4148100b52002d44a200046000c040d840c0c2c10000700c035031039900b105071b0b50400010000d60080a001c030718040c1c80903650460400ca1002d006820b0140001c01c103500428150000c185440c0c00b16080d2861850000c00d507801d41e03d05803510701802d40220070a02c002c40c40d0b201c00714441c0c90b0610306114100c00040d21403043e85190900300006043d0b00740c655a00310352400d454003032000d000c2c01010b00c030703a00903007000100c41441c5108001c0004010001d80411080803070030301420522071400c18034111141c0e00d8038000305488051036101030702e800402c81c0e000803c0c40070103030f030400981000802d030740a5101008995541d20001c0c1c26035a0907481140052406400240056140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 190028057 1250 190026807 190026817
    0x160303050901031a1e040f021219020706150e060306010e1612090503130902030f0c03090f060f0105010f0503040503190219080711100804060b0d020307140406080f070605 75
    0x10b0510011005070036000ca00e40842189a006818a468000e030201e401c0c18001c146a030350705100d0031851305d90319000020f2400c0010344ad42180300088082c0d0015040d00b40c0684203541d8201100301300071170303240c240544041e5880c0704580449005c040000d03020310b404201c5a04a400440c07002c0001e5952200a021140410640b0001c0c0f10450341c01064403040c0e40308070000076209a00440ea5581d225103066034613036440d400b01c09118010810050032440800140390400340b84c988aa45903211199282d040c440c50700500b064910440c41004402480d040019040303e0342030325418800c03020407604960358402104d01801c41d51042152060618042c070001d448a0354910617207966015007140d03003140480580e01555030000110303040c0c00344100d030261088a00401c481c2655003060b05080981465401000038120f01e035100301da20b60503220f260055a181e5401001d54603826251013112a480007046d0700c0700e00076440c00c40d0100f4040000507818400108070780c003c2000500c1d0800840e941c1d400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 190029307 1250 190028057 190028081
    0xd080f090111040807031703071b02011202070f06060501020111040314120c010c030c0903051005060f1206240916050d0e03211501050702061e0c16030305090103 71
    0x1a40703482c000d4000c40d48018101401c2c450700584141851070900d40113541035240e400245481c1081401800b9821008030300f503402d1308002d0220001c42c40d00059170300c03100030100000540d00025485007044512901641241d200360b90800041c0d0300c9200481c2224591010440384050402007480860382e10541f084004180c0c50450b00c080756a640640165040001c060030603a44507003540c00c2e91502340c0a02a40c2d1141441c10000c0b0341d195171281c130380c0c0f8014032021142050355180841c0140d12250601001c07010702801c00d6094001b03a1200c160782d01c2c01100c0414050740c1e0050074a8245e5500c920395150032400800c05c041640350045a1110408003450880c203000041044030542c16250185080e4580c048000d0740c0c0b640418aa410030b14030100112000c00500d45081000d0702d81d8510744501141c1080c03800036142c88003440411420700c914001a010800c03070b1200b10700304030003240050a001030240250b0302c0028841d00ca00b000c01419000c000d0100b4010304c541402c0e9442603020b60802c1351 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 190030557 1250 190029307 190029311
    0x4060e010f03021e09060f0f210f24030706050403110405040503120c0702270f04151508150123090601110a0209180120040302010c03090810140106020d080f0901 71
    0x88171f10051003807070384070000199800202248240f06010303494140e072442e03030442c4842c2202e441c04410825490000800481c08001200c2411215405c00100303401c01e04c1000c2d003280d081c0783d15090054220340140c40b0031074100701642c030f003000c19007094015a405590b01100541c24640b20940c50040701000074040310755000e0920508015030b80d000d501c0020440d4580000d94901c070801100c450760070006000101c0001c0001c103000002d0111106481c0400b00e50000080b1080c1e200100d25000780f199000150920540c400020b520f0320b0716010341c0c1207a00c1c00da48807007114109480404801c00703d42d526580106040c1c00288c442d409100000001c11881e415035a10205948c00665041c00035210b040750702940c40481020300b40240310b40304100100001d6000480c0001619050a2240e804001e0400a43d05510410540190702c91809803040200b595180000d000f60f01000340410041c45d614504060300003e10240003088079410700100d5503840d02c140d5103641c141070414001410510b490740d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 190031807 1250 190030557 190030567
    0x30b070210060f0303080c0a021e0c130b031c020c04020a030e0f0708060a060317070f0c29040305030702040b030c0a031103010c020d08010e09070b04060e010f03021e0906 75
    0x5518421000509118988a8071860450131700401e08240100110020746081150a104603000a03454500c007490349002d03054401c0b048407480c01d1601c90103803c0d030080d01403082c07040c110480360402e10610303000340c04540104003104200d80c14600c4811410b40540c2281c03c0307240c41030500740c0050080e2242401c0c08500c0203224951f4514013901462420215000748400744640303001408850f401c059115006c1c0401ea045803a05003441c0000d4054149049e00014000200030203c2020038110f6001201c212496941d107400040001503500c8030307504030650041003c0c10288410603141a2038008000310704010301340d400e202c0188216170b00c4950500c201d2224544542c0c8546444000e14450b601080d000d016060a05094640048920096401c010703200c00d00690322100890459001e0740742c0c003445444802c4014241080c68100310002040001d011680c0c607041070a58920070020b985011014070b10302c0f004c904034042c00302801e00e880ca2500780090102c243c00040e264003a00105040d10340b03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 190033057 1250 190031807 190031833
    0xc03062404020f040801090606060e0a060507060b060403140f0a0b0f1003021005091306050d03050a03020d0908070201020f0d140a030b0303030f04020a080106031533140102030f04030b0702 83
    0xb40d003056200305c2c0169103464490b02045164000c500080869003050440c9802c01000150901080e00a810130044c000c6260402d100480e000307a100174002500c2d0965803522401e1a02d485c050b4070590307010b6031003041340d00544420001070404615410a5a0315001d440c0c2c0c01054285140242c000000f1400b0083c010001d43d88106000c131400f81c19850b043c1d078400c0704030b0a0210070110f20001b00c1100d480c0c440100840d44400c058a450340b42e02d80b4081d0f0380c403404580244d0080c090f1444220700302e4601101d040030403500000420413071307000360212103004041d030006660340d82d102d88006000a01140b40c0807026032510018020f890000c0c140462182c1c00b10021038510b0b00110f604903c200701f100248415401c04203862009020f000e030007480110b0a5403241c54030b10351218800d2190b550360707110035018803050700300d80103030591040080090b0901000300c4050890441c014046100302a800348100d0703600000880b081d4100c42c0746080d00b03161540d1501000c00c2c1004007100706501920f540103000c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 190034307 1250 190033057 190033087
    0x20f010c02030d0605012303071e020109021203071101080a23010603060b07030e01050d0207021e0f030a021c1a07030c0806180f040203010e0d09080c0306240402 71
    0x282081d50080d9129841e078a06101528040d611490501c42c18101043c00d078000c0c0c841055014920145180c1c0d6511040c1041350885001d01004c6202c0e14550a405419070b41900f0020085008a642120707001940d603026460b842155401090a44000408441035000700941c075840101e05200045281014071088000700d4200e00106500096000600843c1d4051007510082c21130078480c170f4108040d0341d9002d08034106120303019040c406d012480c402202102c1e0100c0d40d1641e8081c05001c80c281c200401c40300c4090011000318410740d110b410103500740c100081c080c0d0401350010154070004548485032400c0049403c2c090311940f1060800b4a01000300c04d1b480c0e13004580d5541d0014120502100040c2800300c06044a442421821000364100c0d5148031000c1d0850992ba4800101743c0740c9100003401400000c40350380e000d004070a02c440004d030b004041c00742150036090603190080880410151501c0c0200d8203a40302405e8070072042c4583c2c103aa8160f0b1808403001c0d00052510710640700c0d0b940 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 190035557 1250 190034307 190034321
    0x516080105010f080111040b070222020304210c02060903031e070b0106051c0e16170c03150c0a021504061a0111030406110c0a0305031b030304110d03020f01 69
    0x42a912070004000c050105009076000340070040c000c0001d1a08040e40d100107100b41c3c400d01202d081d0200b498025552a5440e1403180841d41c404410321a9403484d03c0030294008480546da054020101e43c0a403400d0301e840d800300700b0896911103130420340c16030800c1080e801c00062a070300f510080c00170080001c03645c20200d4001d44124180f5803211101e25010303000d004141c01071000c020b0281701c40c0c0f117950b1111010b49242d0102200200b0190440d031048ca1800840d40030384406d1500101d40010203010181041c5045240001600e00811800c020300d03680b80c500d414400350780071840e00051031403818100507181c40c090520581da0002d010a503106001c0c8001d817410b98210382c1c1c540101e101c10701942c1d0b0f18000e001d020b0800803051031450b55403644902641c8101c0050080710780440c11460424042074909000c01440705840d2522400c1c216681c0e000060a8003903200600020501800c0000c141c9100d5036100e405010111080428024400c1d04410300710300303501c2207145407a5200700c207002e004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 190036807 1250 190035557 190035569
    0xd1b08090d1e09050312072009071101090b01060e030706020f060f060a0f06080a0501090e0a020105030a020d0203010b0705010506031603060b04020f18011b02240702060708030103050705090f040209040516 90
    0x242d07d510b81c80c10800340f8000d4030f030b03907496464801c000e050590b5100e80e501c80c1c1d400145818507220012105074013901400340800001c00046c601c2e0300105660303401089440d10300d007050b02180c1d00c20307403904010390340d0311604c1d8044105a4090360008442c1c0034000d00041d8001005421a4240c607507480905160102c00d40219011450f088200308030805207104460040089680c2408201c01d04209603495030303a080c1d006410024008001528607060381c0458002400381d240843d920345e900c1c52407400c0364001e248115004e500b01008240c1070720700012000582e0b42410081c143c480d00e140c0e1038000426581e02c0721600160284404042c0b05480742c050072858030011030140302c0310200c00c0014201c01004c2654141540f56200c0c220142c0c48080542801c01c0d1a08804100c503103480343c00c0030040c001c900c0025400f0034002100410444c180006c3e60407a4460b1007265031b420f454004020603050101d078684500360701d000c00500586803400e84560001d0060042d581d600c80800004032074016207030400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 190038057 1250 190036807 190036843
    0x1507080406031401050603041b081f050c0a05041203090f0e06040b0a14010305091c020f0714010e010302070c031401020a091203050406140d1b08090d1e090503 70
    0x100300c1c15406004a5101c6511100c40750807660420000400500000e4000b4002d03600c0b0340b849c8620340300c2109920340585001c800f122070501e04400c0505014140c03103102c1501508010100700425402c00039030309107000a485440c2072505110000c000300e03101d18019004c1001ba2800040c10071800f000740c00140c9503040041a2a1030b1100500c800da0302580c1c0514010f0803001ca042281c84d00724400c202c03200388246808a019101c030b0301304034900314210b00302010341340320901149020358000420000d01c0551206540c5c1c03071a42c80c0b015400c075041c400101c1d4007084001040188562081c1c0c02806520720450002403a1034490b103d0402a034040d0141003c280c0d40001d50b0026641c0120300d0034000c0404c0f060b00340c40350041d6600200700c0e025610070402401040c0c004001e910420106541003031800002c108840b8028828440c80d046004120310702152105d4045006c440b03004c28039950040d6940c0303070410311a1194a910100d40c1c2034880807003c0014441010556a03030600500e0301503244603041e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 190039307 1250 190038057 190038059
    0x50319020f0a0314010501201014060306090a03020c090408190908011103060a0504020f04180507110c151303050106080a030801050d1e020f060c0106150c1e0215070804 74
    0x20240850f141300211081502c2e610b40104480da9011010314800340b941018555890800e008151503d42c848105440f00c90411000e0b481e5843c0d07014001c0e225031320480449a041e01c1e1304c180c054442d80c0d80900500143c110702c130b410700e141c10170044050301b03d03200e0121a0314200356222252a021030580041380020250301c403c000807a030900400710800a4403582c5842c0d402c0450008401e0461441074034041d40e00030506a501c4012001a00d00074281201642184141c1d121058010501203c141000c05e001000100b240203001800a07440c207006000881480b41c10702c0c070000c00d41c002c33442e13840030360320b80040210004100780604401814900c0042c154185d80e480c02605141058000c3c601030719041c522500415500d0011200b54001003480850345511170010a04a1402090b01a00140c0000790701603c624150700040450700d04001603640c0e415040303c00c035403040101e040a42449440446403c3e101c40d441e0b2802c00c141c1c8024030120403440c91b03040d00c4801d50800c10050f50b2135000410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 190040557 1250 190039307 190039327
    0x5130527090d0203030402042315030709050f061e060c01090b06010305100e0903090a030f0302060603010e0a020f0f0907180f0b0703030c0306090501090b1e03060403050319020f 78
    0x5200d682040d0200041e1070502e6100400035568000100041e00c110303142c0c0c0e0716010b40c00400a4902d081f042c0f1403885101e030300c0c0040341c0310510040500414028801c103880045c0740f242d544101402200d052450300c0f20780c1c031745008004001c001701d8441c11003d030904c1e041d00708a1303980c0c0c8010a898050540003099a01c21400e02000011004000a040c50f040c04100400d51f1180040c034000c1d01e0480044402545640781c4040c51070240c0c1d0300b580c1c1c002e136111501009000b15410315a030024171a41c00c84189591b90810701d802c0e183c25001840c41d83c2d102c49100310051908200d101c0c0058805040702d2219029180050000d4805403500d6000c144500e402440004680200401521030340488860b02071802d690941d5a00c1000f0000d001c0569070084910f60910075000314008148010040c0405d503141c65504000342038039002184900142c0213080f281d0b010103000c0040500005003d8a03442d61a601c003a10580c0c401000c0c2c00140e100020044001c000030700c054840745c000c0c2030000b038a65080d20 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 190041807 1250 190040557 190040629
    0x10204081b040b09060d110307090209101d1c020405040602030601140903030720040603050d020d08091009050a050d02060f0601020f0d03020d06121b0f0b0a051305 72
    0x20307040760255003005442e04003500e44000c030310b400c03500a40c0c1d9000700300c089042621403c18121040c9034175024000001035004140d401030030b4008000c0303941c040b4481c402c04042e41c4640b420070300400c020410501d45001e40c9441c0c0d18001079010b48018803281c1228a50028007205d004075001c0f15203d03404018031842d96880801c0e070101680051030302d8036115102d40063360364000e41c07400411521040d080c22a50080c081e4040e507908501070310600c011034403031400d0398459480440303075001440b5520903040c680e40300e20343e00c0c2d00684003c40076210224001180350040c2c00d0400d01a692481076461040c0015002c0091009444482d800b4000c6400c0c41401c1d054107034806040d40d411903000030140404d0220100f04e05407005442c0c1030044e91440780d035170447d0103048075911480241328090b19180600c4604d2401160500304421100c520a0b15011000804d031014091107100030303024030055000d01c0c02400144041e204408007080c8081d5258001100b610090b03030440c001e07014046e000040107900d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 190043057 1250 190041807 190041853
    0x160f140121050402010309151a060901120b0406030f110f060705100c02250812161b0504060303030e060604020a140913051006020d0906080711070801020408 69
    0xd2916518504060011504400c426207014044035034a4000c501168003a0b030000165aa0089040d1000c003214070a50005000b00003204400101241d901d00711454503508580003a01c051f100d500050041c0c155110007400c8181c1000d0f0000d568050210204640218001034188180c0b01d014032010450180201c290f07450003151301641080c00b0b018001000071a11040e00700d038070100041c03901e0390500103e1503c110552152990140d0110074131072007078200c1ca94015200480c0494484d200c2c00c075104112030bc10030304580803940340030301c1c0da00014110300e40c40c1c400c081c29607003960031080d03e17240054100d850960040b80460b6540c0c0110a81034410301000b6404401100c00b18144540000090640d02020b034522440100c0000d4000c941d5030b41c007403a4141c0e1804610704002c1c0d45441d4624030040b000501440000d80320350b04030320341594450040541520300310390302e40200707468024003039030740140d944000407040c010b030000443c1c8441c00f4800340000f8036001e001040586d0709441c4a1240c0400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 190044307 1250 190043057 190043059
    0x1808180103060e01030f1109310f1203091a0402040f0501050907030903030f0203040f031404080706030c0203270a08060c0301060c0f0b0708100e0603070b0903160f14 73
    0x1400010401103d1040405044a070002c04091040303a8500d0015140440c441809170701c03100b100103000c102d040302d0300341414101040c801c20150510904188086011809000389180211780d81030000078801c0f20140c2e812103003400d012402139401e9850b030111341150310012045802d07100c204001c1d4a03080c021060103104101007041a5410040030400f0312100078032202c14191191201c1003014420340c000038103080d07034030030454480c01c02d407070101080c0002140c143c0000d20700440841a00c1c0c1c2e200112001ca461550043c00b04900d02a81074000d04030080d110820f40c001402046031018030036401e9542d288030884941800c81c842c00c1044503d08564002c0d450a0b803200041000000712101142e056a003617007844110700301149002703808610b200318004c10889601701840700307003600501c0c82c0e030080aaa41c2415502511003030034542c13032039046800650590010f0301c100000550301c0c0041c440d006000c1d0036075101c410038070250218241e02d0790000e00c03103903049202003122071851aa84042c0243c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 190045557 1250 190044307 190044311
    0x12020114071b0605151509180c041a0705010504030e010306060903112407060209090a020322080f0c070f0501110d0324060e0405070e21011808180103 66
    0x94000100900e402034048020302e001d84d240c0114419000e801c491400c18080100282000c00b00039030f07202c2094014441080c05000d00c207000c40d041c103044d00b0709144504e071010003903800d05140c0241242e10041000080032000420414400450000e00490b40311314041d46420740c11200520004013110025800039040101120341480010013002d01215404811201e4240c0c442c1079540c1460b41c0b4010841c1b81581c1400014a80b0070031149030058000941e0494041d1016a1581c1c4070314183d03c011204042ea849400d8000312480301882840038416006001940c00c0184000902c50140c1c04990011001d500050040001104120211000e40000c3c039010220852001d82160b42e03003062802c04080c140c44482d581200055100741c40381107000c1907801c01c6103d503250700181c80150401c00203800342e4244000916810b000c2c500540301100301400d05001c4014001c00c807011025890801c1696540b40d6030208101f01c01c0c0ba0f202e0801600840c6000d6030b4404249c100c144080f00518828103240c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 190046807 1250 190045557 190045577
    0x6090606161103163b0103030c11060a0e2d10020102090406090929060103020702060d0504030203040e07170a0b060904060f0801060504020903031909031202011407 72
    0xc03900c25180d00c1d415404040512100c000724002400c09140d0400d9101d031003000c240002e02c4000c06902e0800c0b4484003140c186400101001038104d400300030f00303070ba0700c883e070803000400000e4810404100b0507802400c18145406048000411a44c4006260f00000b00d00396007405181c0f40401c8080b6110720f8030f000403401d02003072142800e11711850f2107115208000c4074260002c0c81d03000390125040c50000034030030000140c0381e140307400040c041c1d00c000390703205c0e2104410b106801b030400b19201425450307024044403a80da40700044002e944100c0003240c001d181480441c50301401030161f2406240b00e0380240d49c6440c10140d400752100c0000302400d04100700700d8044901402740d07120307003074001e50302c0400840c841c0301d0316000c6600f600c03803410350a030050b1601c0300000784002c448080320180e644c0e21000340060340e5604208170aa000f00401e40c0c1d85a0001c0128003401f084420036a40f003981d290400381941540ea48a07400b1112004107510050b0751298080c0b9100b01d42220f120b030b403107015030401d030101c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 190048057 1250 190046807 190046827
    0x50601090606020102091021050a1d0a020f1c020a0b03012c01140a0810050108010606050405031902030111030702010b01021c0804030c17040303020f0d1403130f080d020306090606 79
    0x1080080e07000350123210351181c54288000303008600610245202d00f040c000d9040c060250b100030201d001c0e036210034000c2c26881018075603004c01c006924503001400d401d502101c02042010001c2d80d0b03240d00c2d1a40c59405201c20040c1c0f26419400e00416503a01102d4a03589841e001800300342e00303d21411f07414511402c42110091200c1350803415651109a0824690000f40c0810709000c450f400a445074410f011541c03c486030545c1100341a02d01e1030000b03100440d5600c2050707030360340694040c441c1d041e000a44040d400c02001460b901c201030008002250040c0f484140140580c82598a0341c0140d440344080350080d6010032801e07000e002c001300341c000700c034030301140c01400c070350018000404101800e14280140495000ca00c00b002c041064109d541f00d540345400b9544101036425803040703000364000c0c103c41d14003518030030b030111603000790b8580b540d9120030307003c2c081c098150022201e8020940582012809150142100b9241e201300181d413420035008122100d60010070082c8180c10812070a000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 190049307 1250 190048057 190048069
    0x2070e100e15030102070c03050a0c0603060602030d051302060f040e0f04030503010b0a020705091608010902190f120507050306030114070e060901090302060d021308060103030e100309020d05060109060602010209 93
    0x846a08100c1842c03020b4039600000b8060301c60b500014010f09205800402404000300b006a4501d02c54401803a03015500c2c803055003075407000d1081c5809070704248940401d6810f1134104541c441c032050502e210394046640011403580140c04100da0a010100e0140b14000490710842e070820000e034208419403401d0350f002042c80c4814041d4403181100803400c0b0581078000c024080c054a00181b14044618140b040c100417080384010110009281c94000984000070b4800c0302c03021508641c104449400c00301d003e8444241b090041d80c1001618500c18104044074803800d4014403c0b175a0b1244d0700d0074102c0c2050f00351500540207100c40d031400800e000100350032414000c2c850f00140c0340c0c25140c444141c01a10782c0407141d40013a401a000290245500c80e0b81da00401986844010f2103065035194140c0079929030007404000c02007003500d00094603501e0302444940305c8403c68540440c21a00c0c507804150702c40100c95044403950310600051000c40a1030042c00003800b8644021420100d4103c00150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 190050557 1250 190049307 190049311
    0x6020a080301060c0f05060103030f0e1c08070c08030d09330b210d03050f0106080c07080c1c020606010309080d110c0604030503040302010b0d0305031f1502070e100e 73
    0x2090100d010305013010401564940c000e01d54004059814560b940d06001d0002a201c8008000264a55855981c5440c0c600d01c42d1134003041103541d94620004035600e1203141d0780040e205644001c1c0c1d41c840011820420001400121142c0101003100c03071392071400c181140c2c4102d54070410082030342076032284909000307407080c81001005e00c00b00c1c03503800b507101117101200c11600149401d07400202d00d240829000075003036091040307581d0800540e030b5440c00c030102030242800307107030b001038a03500100769501d003410f02402d50580100300700751400300c070350303841d50310b0501c02030460324810b41820a21400303550107215407a4041d4003803c0c00d0081030810b54403030816108080b149800655121004940e890100c41600d030201d0864048a5150600c1d00f8081c0541d0800c68044006600f81000f40e143c0c0d042c407008942880d90b03d5107c06003141ca55005421606500303c000380c940f508065400a408000c0c1c100d07102801c1591340142041c0740c10041600907460307004184815502a0040421500d02e107282c02903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 190051807 1250 190050557 190050569
    0x305030a1a0604030503120f1e07030605120c2b080c010615080103050606060f09010f0309080a0c030e06030105030309060309010b0d0c14030114011703070f061506020a080301 77
    0x1e52a0400c90030194494180d40805400000203d0302208000d000401000c8000c1000c1407203411b0ba8425040e050709010450b180740954854659405007030b00d204800c25003001482c10040358481c1c80c1c001061194020341d5074200e5560081a5050050801d1203031300702d14000542ca03001c60400b40840c42c90040b080154004c0c100300d00040c0c074001c050340a620000140c031448001c6541d200144800802c8090280020f45445c0150310218580c4d18009084502c15546020503d040140c15801580c0b1801a01e41810900d0386500715a40010200c0004000349460340d1580c1c0f045110314140144104410100c036405440e0410042c00340d0307a000401c3ea601602d048840c280c0d07980e81c007440e060261010320b100f26000110390500c1000c001458080c40c050301d0900c201001030a4085d1700f054242c0c1e460b1004440700341e501d0b0005100b03040c0c4400c0004541000c0c4400c481c5890141ea03036240071075041d201c085c0c1e01c0c281d86001031080c09000c00211401044144002c6c1760240260715070030840e10043c4504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 190053057 1250 190051807 190051811
    0x106021b03010906050a06050a080c010c0303020f07120201020c10090f12050c060705040306050a05131214030c0c0d02060103081206010c060c020a11040905030d3603021204030305030a 81
    0x90a990700b500320b11040c5600c0a428840340c10704100144c09000a03028040c843c48a16001241c03844002422180c807250503598800740c40382070780b400c0c1c0080d88907108407200c6820130043c000220340034008407032410140c0e900040e41d407030400010320b00b4032801c0c841d4108442e0400c1c141c0340118249031200013140742c12128040f4020301c020700c1034406110307048030703580140103c0341040400c9420401400c200c0f402a40244010f6442d20a00c06c100c1b40c081740d085c000640c94242d0600854518440b20f01d51000c1410210b0303150806c4040280c05800c100d41e50f41e002c4000180c102104242031003424107000c890f000405155046640399403541c00798151390943c1031040f00014010768840c1410001658201504000c4448503c1d0000c0d2513403010003040d00c0b80300301c0500c5e14043d828035216880101790048080d600b08501c10300c200c5c0281c002c1020422014440910b0500300b108544100d070003c01e60101040020394180c600a801c0411a900050000f0800c2c4020004250840100c9510545000340 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 190054307 1250 190053057 190053103
    0x926040f1503020405120c03060c16060b040609090c08011503020d150605061909050130020d2c01140402091807080c031e030f03100306090807060b010305010602 71
    0x30031002130145130b10184d40511039019003040004081420240c2d20381c15819100281d864021381405886400b80e40f005400c6900c01d0a00070409a900803c0a40300060011440c1503403a5015010351b995204107a4078103050310400c0250039000d01c40d03006400c441040751807841785990002070b8824054180507054030307014a260325880c0c03440d501001c0a000c0c001e02c3c3e2916a108540c070803200464022803440803030041e603c040341940c0201e18000c80200030039424115400c624500c118500718500140200035024070500c000e611090088018443c451502a1040903090b400603410180c10308600035580d140081d1400c1102000902c80d5005170150350841d01030f158000540d00c0003540441d4055503000300d09010a82c008042002e04c08905c0c124121407441003c403c1c2c03038440d01035031500c01030150f104110703141070224000c000d15800803a10071401902039580d103410b8162040c0c0c2e03104950610f00001c0d520704008032846121303241d14003843c040015606064004c0d58540d0120347c82c0001c8003003500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 190055557 1250 190054307 190054349
    0xb1e090c07021e01030b01080609130507120809011205061302030c0c0105090d200a1103030d06061e0e090411030f15041a1b0f04090926040f 62
    0xc1110728040d8090110201c1c60000c50580d4038900b40300940900090902410b00c42ca5840313145a03e0080d1070050003001e6036100c038480c40141403400c010031141c50141780400101c030a065190710204c2c0c0c1c01030003100c0d0b8a69214000402015074000501d800529090901104d601c0e651801d0611070016200185e4035280c0e80c441900c64050505080219803c000c10082008804a02211000c000d62601103d5508074021941106101203c030a81e03036105140d14000320380d551442d460b01900240c2520700e0003100c103241d0416109981c05c400041800c2c1003801ca25180c07003001316000c180c0c0e07525000201c200706d9000a002440060030242440a0140d0a681160343c140300252280407902c2c12070380c1c490310700780f0360100e024002c44054030301c0b800000200b40d20540340349896102d031303030350040581c5140d0000f002c1100f550017074a039880c04070340180300120f200417841c0b04410103e4003e41c42401e0800da92000c0c482c10682e00104500c0011050004000b51110488103006a03070300c0301d40700c0003c0c4688030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 190056807 1250 190055557 190055581
    0x14030316020721080c1b09130f0f0204060b0c0102040e010501031a0f03030f130315090c1e0e011d01050a05010c080d0b03060f09011a0d1203060906180b1e09 69
    0x4034030082c2030301603c007403200d001b85460035503402c1c17172819650102e081c0c1c1c07a80a1200301c11400342d801340002d00d512a00a0005000e042c011a200344010400199a41c4810803000302ea04112680c6c201c60798009014800a41d04940403130041c5000d20b000d03c07020303840c0022403400c5059210388070700945074945401c1c041c0d44c0c2807003507407901e220b04154162210869050000d800203284800c2d42c1c50035148842072001d0712a4043c00400e41d4116a00480c03444c604810800034310342c041c42ca903000c11900f0601203212090440b0f40e1f0b00074501000300c1440d125103061025007080041e4465882141c00030740400c841c0e60800844003c9a4100762400e0b01d911188260802031b08600340c50681c035005030b104204010401c110424000c02462008010b203209201c1c3c1030440449418519600030311a50500c3c0010726141b50100741401d003403401281e800e64818070002510420741042d0307106040d64045410b001440c1c800d0b02c086140480301500900c2409450349400c1c60084021405a90284002403030320442c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 190058057 1250 190056807 190056817
    0x70309050907030c170c120a0e1f0b12060109020c03041a07120305010f090b06130306061d0412050309150103050304050112090c0e0a091403031602072108 68
    0x580607800500d85031000500908080030713100d0105041d0000d8802d6a85020549881401340d140703054940041c80c5680c00b0140c0e0003c2c680203225407a00e40300c801c01c90046c03201c02c2d00c91440b1940756603a040181909000d444691845a005842c80440b04090b0300300000e805045032003136000166a030f03140000b040d08501c0341c0d03040398500c9068070581c074407003411001c000c00449000740510082e912013060110182c1c1c07420311980404000b0792105001d01c041c0c0380d0102004450043c412407130103060010f001c5140409900079200280e4829040102c0244804032448100351940f1800d481d203090fa4484461480664101c010081e02000003122503400304840b000d001b1407510102c2d100d40c0e40b0303e455a502e42c0140110380c005070b52164020b40c180301501401129139400b8591810003410001001d4540138000c0494540342c0d01c40528030003003010001e200e101e070b1031b210000c0c507502d10344024620741540701c84808104560040304104011458444201e000c01c3d821241d441c00036625040c030100398040d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 190059307 1250 190058057 190058059
    0x170309100806040603080f0304030810030f060b01032301080106080a1a0403110f07140103020403030815060d0f05040b070c030c0807051c020d020c030d0207060e180f040309080105060d020607030905 87
    0x1000900e910307d02d0a480281d407045101c1da81e44400741e40c8100c01c40c40b034011ba501c07009107036040300058000001c01b16000890009418540041e06004480b15207940c41000f4070380071490350b0460012301900000b03008940180c560403009003030288555580600d01d000803e14174004060f80d2010500301446689980014031310740381100c140c24030990130720f03031600c00380c0c49055443c0ca4540540c810650190081d134045a03055241c03800385548001c0c8015901140e010b11076030200c4200220000c2c00e0140c45042d18001c0d20740000115441d240c90b01120780314010341410180084d074110400020b501030b4006650703507440982e4035161180b5103040c0c1c4c580b6140141440480f030900c3c09603482da139030025981d45000ca182d801c80d24080f602105060710341015048100050700080000d0104901940c006481c0e100040e092070407104280c408a000d5010a50310100b085003944144414980c1c009920000761030300b54002c00440c00d2500024803041a101c0d40240100700c042042c000380b5000306017230b10080030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 190060557 1250 190059307 190059323
    0x609020d02101701050307182d0b090c0301080d0507320606041b0e060c010203010303081e010b04030f080c0717070f0b030c071401020a09170309100806040603 70
    0x24800002d0f1044442030b00c1d150b09105048000112481d000841c9400c41d407029141101c101240324001000d045185140e0402c840c0c041220024005442c000d00011102c14000082001e90748040280001c005414044003080901c010f0040703079000308200650200c2400d18954400c0c551030018650b4009084a000007241d020741c420b034580f1a050241010120942642c82a545610030003007183d03001d1441e08000c804158161400a0050110310824480145801e051115080d092030984c1d0007600200c0c00a040d860910003050410705103803081041c00201400a9070400f401c2810038092407001a0080c07400c4c0c010342003408501800c407000340fa0030105984106444290702118502980440d1441e48107000d130004207a85007251041c00d80714500b0015240d038031a20314200d665000948140d41c0144802c0391011055824801800000c60a451f088601d6240a07500301d4103a6000c03c3d11900303500100f046c22801d94502c50300303814a12150070701d009070342c5a28010800821f155000100384030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 190061807 1250 190060557 190060579
    0x70501020d0c17060108060d0f08180a0e040b06150309010b010e0d051f020c16051e060d0905030904060e060a14030607230403110112180609020d02 65
    0x54190010034415030600414000c1e10111807080700d0001102c056200303180746560114100f50310804c5020b82000000700b5010140b045030300c808a1041d484c407802c0700c3d60301e40020b2045480c0c10641859458090413100f14882c14585482d800380060010001000640300c0f600050075507a61840405ca400c610b0781d40c0719103e10382000301900800c0c2949003280441c00c0e03485940c984e80350a08003030f941c0c03030340c482c010f071400012030b001140505c1ea00041001d1115020f1041a621710700800c03100c0100c03a90610b03c0f0050714940b90500150310003544615162441c22148040543c4910081300c3e860280010700240070101800c100e0f0840c040c640f00503034032908003200050248a100314080c0128011a4400209603a0701c07600241c000e02079130307459050b4001000281040d8003c041c811015559804e29000706c13490042e04000d642d0003a0400c407054030003641e410209507401050200e00303080715041044010040401010904140200182032a49504403d011074a540c1112480103a015200300d4060b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 190063057 1250 190061807 190061813
    0xc1b03020609100501050a0e060d210e0d0c0e040f021005040512030a020717030904060b03010e090705090c0a020f03030406050412020102160206070f15050703140105061b100207 78
    0x1140c0c00d8030150342e144110840202000002c1c0716a41c12540300070102c258061a1400d1020104001414190700006807800c100229200003903010f8141c2c1481060740d0034024444000e80b12031071154107c0d001310740141da01c10008980c07449a000361900741c0448001035940b423401680b124500c0c440250040001c02e200227019070032602410980c0d0003118580c1c0d09111788103070650750380900124100107030321981041000190b601c119004258080d01a640f4000c441c90205003a1403140c3e000c0a0100000030040044441001c540b03904039440101920741140380030b002994100001c0c00e0740407610000140d109005000300509010101d2100a5948910f0f050610400902d01260305a4501c00c000032212622881842110464007242010341c1a131401a000e101881e040524220f070051198505003001c20300a20b0501c441200d01d1101080c249810000201640c640313034842d41c58000d58000511480e6030718800d0b50b010342c04900580c2520100c12070714610304141c2e169134443d1311388009141024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 190064307 1250 190063057 190063063
    0x30c042409090c0b030402011404180e030c0a030806121006061112070303200304050d030c020a0804090c020102130906150e09060d150213080c01050702030706030c1b0302 75
    0x500349440301100358560340340010300c190382c000d5000421880e81600c061150101d00806541c00c2401031400d80c0e907642196280d0707806507125810a04107078200e4460000d944c0c05a01540d0301810715940507608100340300611654230840b188004040c400c18100041a44d259003102e0109901da100495102c801e86014440040c4058000c1c0350000f2010106840896000074242e0b60140c50402e00d5484c1031003036201180104465a202110301e00100f0f01e04200e60f00c035001550003140a134015005078000d1b040e000d422950611103080941d0820185440811a2001910304070f4000f0400455841440d000803030091103001c40a50403000c109202041800b0f0592040b070544518030200a503036202c20805589150010904a40c00056500042c6160401101c81d0383e04a12640404100d488884100000c0c3d81104c1d200c900b5090383c800040149400802880c83e210300c080c201207251404540200b0b03164800ca00a0a0505450380c00d004910b41c414100c000d05141c0d00130140594420615000b0340b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 190065557 1250 190064307 190064351
    0xd0c080d1404050c010c08040e060a03020409030e0f030105090c01030905010b030a0305070c0b19230a030f051317030907050a0b070516050604350c010801081507030902030c04 77
    0x141c02d100b40032003044c40d0350003000100402c9400c4100c040c10146440346441003024020306094100c40807000001c0180c4540c050642a540b1a0b141d5407600d40000c01400f0844c0b450408040c843d078142804c1c00510b50000c25407802c01d01080c81d01248540701418800d01500d8681021605031203202c01c05014076500402500c1e41a20a102400c0d4959135800c403090f540c01191060440070349a510981c0c11640030341e610029500c9012000785d481504640000800e40041c610743c800f0a48400d440311308584544503d940c04100e0040b0714020b00e0031500d913820009403450054900101c000003003240c400c000c01c00c00c0001e1500400250b906a02e0740400c401d2030304041c00072a024407a40c41048189104032815200362080505424241403515089020125902d8004d403103803005003074050007040e86030710f01c1b14120103290018070080c04900001805d05a05a1040d02c0039002070303400ca42c605800302805504007180e85004a9401c017140000390409249100c560761007071801544410761946004002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 190066807 1250 190065557 190065563
    0xb07020a03080c071a0405030c0d03170a0606020106060201060b0f0309071a0a0306172a0a03050a02010f050f03161413080609030f071b080a0f0618050d0c080d1404 72
    0x2841c0304000d03940705c4002d80140c0c01aaa419000354000204d1820b0044900001701e010386804110510051045048044c0903548a51401e45610f410310455409001d40e600920603880204003103854000f40329102d0080d0a2100a0184008040750200d4010085040540342c02e08c5d050202418048050b062035103c0c00d6420042424502e00007252003d040c0b4001c103407020f0074043c184c00306180030a0403c1c8036120f9190191842e038100281d000d500d6000561020314425030040100307201c1c0b4000900ba8005130031540c001c0010801004000081440130f0b280c01040340700d10441c8540d050b0720107461990902049840c218001f056044401620044140480e103082054882a4035519806616841801464811807000f004004001402440b810b4a0841e040486045942e15604001d0404940030815503202014a039004140100340c2f0072401050600c02c0d17804480d001c1c6503582d94940030420104410310001030350180078014406d044030321055480034100028078500558070441e8030187c50503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 190068057 1250 190066807 190066829
    0x4061704081b01020d05060d051005060103021603020a05100b060d090501110d1a0a060e120f0706020601060e0303130504050a0603020909030a081b0306100909110306010f030c090b07020a03080c07 86
    0x45282410a64523001c1d0480e0070001820300d00101d1241d020180c503018000904240c0d0800180c1007118030114221303d9503100c5e0303018201c1c450982c28214600a0b140f065407240c5c1d841c00126454654a40b4102c980148100601056125450400700d006003c12400d25550b00e400040324a0b40c036041b41d10480c034180e4086030b10080000b00d8000c1c0608228a4051030b404148101003000302882c0000041612400c480201d401008003c100385003003030002e80c88600940e11031801403003055002070311240c01c1c0381c0540007107041072081100108145411f1060a00642d5110082052040160400b0002e960044c0c441303034450030f01c11541070342e03540a000400300103039001c0c0102d4000f0f207030840c04800d05154000300909544034901008013500ca41075008040c0440044002041d002e14007a0324100c0350040c007a07a85a241407400075200c0080c8420400425141800110302e05070400d032240300f030303406884845440b640340303202290160000381c0001c2c2407550301003955528828005110340070342d1005444 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 190069307 1250 190068057 190068061
    0x813060f03090b06040f0204030c12030207140a03020d030e1018330c0506090c09091504080a0903051015060804050a1101050d140f0c04061704081b01020d05 69
    0x308808407007100d0001030100b034850700402c450745041d170010301c1c4c010310b540401890981d40b992600da85030090351166060010903441842810703018480000148440c82e0781c0994500c8940024001c0025800000d2150011b070029030180b42c41681d44110403400901161100340b41500301a140000002484162103800507021031100000c2da4101c211151101c8003010b8248045142c010f0140503820712410010820a494089513003004a240150f0500b8003401001c44a00f090180134038006107000103d41c800c0c20001913113800da200859106400090254441c9003459048440d07004591002d0450f02c900c100c1192000c94607800410607466003659948050760b6600185d408210464001e4816001401d03094040707040030a00b4141c20300145081c40ca000e2190311030400300c95003a100d000342c40c0c000b4010400c1d400050340495801c9002a0f1074181058075101d4014043e24031009002400010000883d04100f0300200740c0f0703452081050215102040410581c1c000e4028100c4510000d041c540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 190070557 1250 190069307 190069337
    0x70516081b06030406020a02150406061d010308091011031c050109110a180b070501020901081503100b0a030b04050d021b0f040510050915040b060901080610020a081306 74
    0x210104072000090881415992039442d000000d4101016400542c0144601d0340e60550b400e1190a01c00d6101b000001034107410044c03c034018403841e10b105090f40e50711200501c04205103000b5030b404c24008175110b03880c40b0001072003210390203241d0200112900c400310b100c4480312203040070f001c2240b0050f0b0080100e681e81e24078000c1540d0110b81c04061010301042200c0c0c0e000e00c614540c054052440356407021440d81c44c50340810b194046c402c1903030140d5002c0307094482586c3c0f14071140d4002a00c10714611506001100081c1c80d5205200100c0c22907940303484d59100c1e0b45030900c4090003123800c00d00d06259440c15090a0b611003031710901c01d0006010310365070415280c60003e640c0310341f20781c0581070004a10640062000606015003410840c40c5049800220b030365a621403d80b151481e010540c85c805069402c2c0310a80e844040724903c079040500000d80240d80c04610943d1000c411654442c0015812000760b0070140e1000015214120004410103051524105201290340310b40d203400111990f50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 190071807 1250 190070557 190070593
    0xe0105010b070308100e0a0c030507080103020a0510020c030f060603121204030e01120905010606031d0a08070305070b15090601050c0714040b04020408010b09060618011407051608 79
    0x100a01a0707808050010b44080707840707600c8080c3d0151400080700340107625429000320b4024225440030305161070310344e404600d5a040c02a1504180c031030404041a5045600041c4214a01c0c00350034054403160010f401e2162080208050386032016040e00d0800d02d403406001c0e03c8541c1121044d010b0312520304e568118103000340c02c9079421480700e882005940c43d00d44d0101c500f0405544e0359030400442d003100100b10810b0780300d1152618480c3d07000003881d0b490300300c002d0152000c0b100100c20301000a0301201d840003005c5218141d0707940c446400e594991241c034003942c0502030504050601c0c0301e00d000b042515803d903503e20f2043c41d0101c0d101c600c0c0780d480500460701c901c00e181080380d5940021400b00844008003c842201c0f440040011031148400b40200e4101d80007680700e14140c0e9100c5000072070500341a1350395038115805440300ca2500d8030101c10781c0034003804201c246040041707500300d8002e254200d074207494001e544003060351003001c4018042100035100340580700d0280628008014059104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 190073057 1250 190071807 190071809
    0x70b13270516022a06120103030806010507030504050d06021b010204031a040503070b070e03010c120c030b100e0a09060801090b07050310030f08070b012301020d0e0402090a05220e010501 82
    0x20f40c0208048051200008451200300e10a60035500c4415440b0a01d65140005000540e0b0b00d00c0c0070022561460500070b1940f01d01408840c141720080140720040390b40034040b902610020b41d082c0340d11440a290100c0280b07c0c0c50403107410700000b00e0b4040010101074005004590145e496504040398100300449864400c1e64010020740c41000100c0001d6550300d04c403580100703241040c481d00c0d00c3c0303540032a09581d50141d6980000c2c00300b03592051102e581e4850064401914981003090002035804070307254403244036020046c001c498406c01d5035a9659001000505070300042400401d42e50340f0302d140a0176403210200c5884202c900000c0d1442e216200b45ca1144969a10503803d50f0301d5512780c44c0c0d800f502501c0540300c405007040000081000075821900a0810001c800714006450010351040358180d07540b54119017200d99150900c99001c3c1c2101c091910448005942e120403100007440420300c2c0d030120f5040000c0c400c80a6040508082070b8403401d070f8800e001c0c4524842c1c020018202d840c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 190074307 1250 190073057 190073101
    0xc0f0f040f150e040b01091503020406020f120427060b030604050f1b0c0a1b051c1205092d0f030604080d15120b190c02070b132705 58
    0x10b80c8000540f01d00e440c3d007000140715018107006081648507201000848442d94024000c82d400040801550b5810801e0740000045a00a0507011508800c003404a115078410013040c0603041d4a00556040c1207100c004100706070581c1000700035035462800c003446d0070071030f2218490b80ca0400014a00428a60707614483c4071000d100d150240305404001007103400040103404c0301d00c942c8031807400080404954880c07419411940c1c624031458803080000b183c8800c1340720b07401c0419600418002801c0031841c1200003140b82401034a4011032008075003080110340740c0d103004c0d44050b40c80c0005148030b405814403280e03080d00c3c1211105110810700d9501c1400780d5006048000c104030360000d540f0940d03c011003048007092662802c0c0c1d60b0340f2035805d0314002104141c131944001014007022400078000254100300c151801e1100d44c0c1d01c1900a500e9418500c611400711100041c5503507641590080000940a03591412800b07041c9440500d0043c4031500060a40c05e18100114070100a900340d05803070458 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 190075557 1250 190074307 190074317
    0xb031e0c16080307030b30030c07050d1a0703050601020606010c0b0c07060207120e040f0c0c0b061201020d1a01030203041e050a0204050403050c0c0f0303040e0c0f0f040f15 76
    0x1600c0e560b2040c0c60350005110340100b540e071318109040c0f65241212407420607260407140c04040280322a020803171502185226940c0d10801c84001506804150b020031108100c404100042c11400c202c41e060015007411100b040003c02002200e0341c04bd4441c9000b908281d003112010303a58080152078041030382c2c00c090b10003034030040000d454486010003040c0c1644035482c0582001ca65940c0ea10185456440341c40c0860304070140b088083c140b130b20444001d110400011311004c040720502601e54000d8200141c0400f20781400a01241c41c1e07104480d030b00b03051742c400840d40d4103031240d0540014144040c00380c2d070441080829854962180c020b5234010f40d003210400b840d101c1e80070880b158580c0c620404507854081c1c010154090390721480f981c0e1160f402a1215507a811121000500300083c0d418075038461030350f024110715291000003c0e0740544498501000080d1a50804104680101a15503803810030004047c0e1818140a000e80304440c00406c81900030b54507040160700d002c2e80a03240400040c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 190076807 1250 190075557 190075597
    0x8030f0f030a09080412051006030b060405040f150b13050f0c0a0306031b09051305030415050c0d021e060114040c051c1a0303030108030f130b031e0c 66
    0x9219030065800c4295600c0015042c1856a40c0041c01d410580c442400c0c2804141d040342409010b201c03050540c00c8406040068074110340d50860440f001402407401140e0382e10008040254482d040000b40307400200440c4401700c248407450107041c8001e15140504026a00d210760003035923004d514007441600000103407550319202503840039040190810209070f1690000008a500142c6020303020300b240c90402006401c02c02e5a1043d41d10161101c49140c0b6810590008908080103540564100780e00340441070415030310482c1d4600450040314017034002c0300c2d4440351440d00010000307016504460ac03460843c4906031440d4075008244640c604040c80161104050320301540a040c21001500300079041050030000c4d0151302218500241b9803a60b240080010f802410070311411800f412002540356604041c0d440703860f40518500c1e50b54141c004240300100c40d821041e10b01c09032007030004440e140d280c43d400d4584140000704000d841000860046101400078404903460851900d00e000070031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 190078057 1250 190076807 190076827
    0x1171902010e060f040305061012020102120f040801060b0405010f020a11060304080d1e0609021309051305030d0c0801060c03081311030706030b09070203040e040b0402010e060a080a0608030f 84
    0x107100107203400c50f4081c004201c01001c900d0440b014101940c000c0004100a00c0d0510011840b6002c0d5000b60700742c21010250400145c1e4000784014000605030400e9403150507076103114180740a1504040070390b50800d440424210b400d500603008071130090f0384041651450345020307601c0744d4100c1001b0740603964842a101250500c138004680080c800c0010342d01d03203050745612204450340420502c11124194504822140d42c80c001c406c050700821f0003c45c80c2c424020b204a04400302d91240e94850384d100c000040401c8481c20031924150b4000040d80d50b5001c61170707002001007180004941c01300380e103900042809446650840941d50341071f12010001d450311042c03000d08881c0c1507011901103000c4800484030340c40a12901d002054151000710f284601081003016001c070003031031401154810710080000f0800040804d03080381e040309000381c00b0b8903a070004844107a0701031612600000c000458514496005521030304c181d0780100100100c985510029071a072103090f1500380f03600404e100e00190 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 190079307 1250 190078057 190078067
    0x30c0a060c0302162009041202060a0218010c0602130f030312020906090405100510110105090c0d02120a0f0b0604050a09021e190312110f0a03030c170a02030117190201 74
    0x10b08a46840c48228034050400006c00d885c0b02194201c44404004403030f2051140c0411103d900104510025800d00001c41018002c580b007405079036041000e549070074400e114250303041301d00b140840b003d203000098071440e1142e85401e039480101c000900c0b8101d503401c0e02d5250710a4070016400108114a014924810080070b0036016044607000410f00600213003664030a90315021032030b86500c5061904040840660031108001c0101041d81c110001c0d0008960b034180301940300f540d046a0082960088601c0549000684580180b04048282e01c0f60140314105182e42d00c150000c40701440a60b03540c80d507010035142461070007500019101c88000e10580b12a294030760b2000085c0807244400304000b590050404a0350042d20802c107021b0340382c680fa56101000c480c204445c903004000403064800b10a5035002c100f1005810141d80340f40c030404042c07282c90405a11001d2111314105810a100240001e600a101d030b45d9818101003070004680b078000c2503003101e03c170303100f074404408410f280c0056074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 190080557 1250 190079307 190079333
    0x60e09131407061d040506030d0f1e08190903020c061608030c03040b090607090603020f19020d1119020d0206041505070605070c151508030c0a060c030216 68
    0x1580107000c9000c0e08000000c2245500030040caa48038103070104000c411800140040d403507240104d08000403c551a200002d40e42046280b52404000c455484101104e1026010400c0c0c88403100c055205100743d68050b40190103494420f81d61840c08480e082010202e0b1150200200940c004a58402141ca03201010340f0201d9035228441b03440f02e0066444c0f140c1607000f154100e0b18003001000b80014000e00f104010b40c450703c8080100a1400c1c12b0a024103e81141d200e000101900007600c0e50807251501c065a02c0d440242040507480c078904a8003940310068551418005a82c10511030a00400003d00041051101a081070154140d4081c01104141980144d80014003000005484804600c590101d604d107655110307110220f925010054503006048901000905106c0e030001c035107140c1c00040050340142000440c0740701081c20007460b01c2180e002c0c40702404042001000c80d400451000c030058820001004880c0142d0f10070b030102c1c05104220104000204801130029048000c202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 190081807 1250 190080557 190080563
    0x50f07061404210c0807030b181501180209180702010c052d040b0307170709030b0609100503030301092a0c0b0903130306021c0504050c100c0506010e0907060e0913 72
    0x42c071095201c0844a140c803078540d008584425260b0704000d02d199400701c01903009105a0041c21082c04403030480c5810704018050195204420063340031340c070b09030307904542590001a081c502148221900d00001c100d04640840c055400c1602c08011548240221175400000c64100901c848440310000000c01440041500b0741008000111340e00ba61380000e5442071f003071036885002e80140c61405504a1a000d8000c03c203003c4150400c0c4000780b45221015440340d0181c5925a0310ba54251900d041c2c40d40ca544050b805000020000c00c440c0013030307003255940c000e6480c010030b01c0c030314400c100710600780300b0150883c009880c03010a00009103001305a960403070b00c10000c903400c0c5a0480c0c6a00c800203410b0340126025540091201200c8503580104003003921034500c00c01040c0742c9500c600b83c40f1281c00100c81d2181c00308409080d6414040c038007520b401c0d030b0881e04507105980c680310901d000040550740e1030060b10a003040080c0c2148211441e804454010302066059207803280100d80e00c1044400403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 190083057 1250 190081807 190081823
    0x81009090b190623062205131808030604090f140f0a0506040602031f09021c0921110105090601030c0806100b0f0c1f0b060f07080313050f0706140421 66
    0x2000c0300021620110002ca40306c0c3c0301e0000140c6c03400082002c60718083c942551203509100c0c046842ca9030f0b10411180b40354000c002190341360340300000a0300602810380300030881b5440c8076004041c00450045401142001d03c00c4a2405a00c120311564070041340344020010362118000400282164001e03642184003214113050045680340c1140c1500290703008403801a41c04140f242845042c07210f01803120b000f94408001c000025140c4080304407004448d0740c80d480000d102070011503c164008020185020001c210761b042010005031122028072059898060940020480d6000441c1036401803650340407481099213020709180c450380101c19454150882408544e042a505019410020308030160000c01c0f10310101c104800c40d080700e51428082c0c0340c1800203059000006085861117a0040901912582c40130500c0c040000380c0100200903001e100745540a400d070010300070040d01c04070b032910b00303210340241c0006045004a1148e000c10308410000745040e03000e10001d01140c54066202 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 190084307 1250 190083057 190083067
    0xa030b010806060108011a07120e030a0b0a060807080d1d0d0b04150c0f031113080714010212041e0e0702070f051002030406081009090b19062306 64
    0x40250058099000c0e103407a401c40e004221056038401c00c19070252000c0d010340a100001011100f6040c003404400812282da00c0210044450041521440d0b1394002000c8440c00740345850030b200e035404240c0b0322400803801c0c0300c0b000c60300030000300e100019907a103480241842c020000c1e04881c0b4a01c124500340c580c82d4000c03030701c00213a11080140c0e0300107401400310700d1407805d1902e8940b1414248000c400411850640c4c500025a070058a01c00388060926001c1000742c0060781d1030700c00303210350380002c42005407441c000240d8401c00f280403022201480c505201d00a40c038001a40c8450300107800038000001000140703c4035410382070120300103890442c088040340c0c60f140e01501c064000d40f40b080160f0b1000c00c2c02c01c81e0440e041c0c24040503000c02c0d2030300c1184018420019549000303d0180c8400d00c110900000d4400e40b1080381c0600500c99402c0a10051000c0e04104103c0f4809071344925100306003000c00e44812900d405150116481d64003011110310203422111003030031300460400d6200031f00f000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 190085557 1250 190084307 190084313
    0xd0b070819110909090604030f030c020c090a091205031909050a170414180103110d06020a090608060f09040308091504050c0a060809120a0e12060105010305090705030a020f0a03 78
    0x206910500e1040c2c000a0f64409804040003d1680c00800c2c00d41785500490410000a038400d508140d00c8001c0d0901140740c1c0310100040c0c1c20039012045094004491800300320501245070401c401c3e0502600344844240e00010049070a440226241740f80c0854004444802d02d4050703201040080c00f500c180d400311141980d54003458039960301c60b02c40500c00424144100d404080c61802000e4007156082c07010303e01d0185883c2000c50511000d0a10304001e241c0c401c030340d1036031101c80510503441801156035600451001d03000384020f016820019070020b00040c0c50342481380c405103001d00028101022552541d40c2250b41d480014070385801030080a00e5184840650000d0a01070b5106001400418607150300f40b1a491040d42e018101300840a0284071034440080340003002e106559010030345d00d0700300c40c100351741003100741181640200360a0a0071401c0300c40450103506840c400d0317030203200c642c840104881d50b0b503103240074495140c0c0040c400380300146071001c80304c19607200c051b02e810350403a0740c6c0e1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 190086807 1250 190085557 190085561
    0x304020d150f0b0307060203071a040c0308040f030c09050702031602030705270a020f040303030b0315010603020306030618030904050a14010b1e0406080114030f100e010b0d0b070819 80
    0x70904030442d07215180c560300c130300d000e0090304042d0440d840214109480c07515258980b041541c01e80345001c021201103401e0100008828000d1508032020b2a50703079941d6008802e42200d103100c20b86062590141c0070961000c135011341c0f170040c802a0b00450401024400c3c805c0840400003080344e01d8031900c0c0000480d070b10f800300139481510840160541d07005071410351003d046001494180300d18410003a4025050031041a00c0581390107290000d004484007022914102d007110030301e9000a400000010140c1c0c1c103030019881008190255442620381190ba810740380b198803c40d0419030024080303040c00c2e00701035202d1382d40042d07891408540030540c401560f250301020380240d00629000181400e03503035400c901c800300f8500845081d0b1324040c0381c050014020031040c09203108030305920207000e5a81c7c1e0200000741041c06a031060310445150304500100a24101c5003080d059400c0c6074500c000d41c40e2840e0303520b02d02d0360010001505075070b03400f10854404000528040c4071607880181c400c07000c40f481c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 190088057 1250 190086807 190086821
    0x3010507020708011503020a0b0c0708100b030f07030c150509190f0e040203060c0705010b0301150501021006080d050c0a0b0f060a05060a0c0210090306110d060b0408030304020d15 79
    0x1d40152102608004003542914000207a0042d44403605000308016141d070301540c0d00300c3d03500e40380461b01d4280d804210350921f205c070b51041d0710600c10030f003802102c507030b0a40c0f100171110b604030112810800f200e400c0f06d45840323040c0300192400c80306e200c040007403c40c203e502d441d0b006103514010349030160b00b500044070100c03041000d900b9040c0000c5e0034443c0600764040030300503184040100c2803504e425030001c0c2d035905c0003c000c4484c1a001250300c100f0404250400c40780140000d000b4440803068108810307010741c40d881581e00511440c07540f0001c030a054031889051b140c000d80500b1b032501440b0001c9da42640915825885032003621203050201d920240003a0041c1c9064180103418104407041145030716941d00402e100b600704111403100281c204500b9070005a054410180400c085141564042b20035400074041c40d060042c0c0d01254401d040040a030240c1c0303400704001480d02e80354149201d000c5c50180d50a641d1080010a002d45040c14000303c080d841101d1114080321444440b005807865 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 190089307 1250 190088057 190088071
    0x303030c070c051e060f040302060d090507050105070506010510050702030a0501060e0604020405030607031a0a1404050c2d1308010504020a0509071d03071214010606090f180b030105 80
    0x71079000308100040e08900e00030300080319180c8402544180050300801d2101c85030788510380002d0003a1084118a007990025500180856110782c0482c1451010b400d2000041b00d050142e004081103a602407030030343c0c4c680c0d030308403004000d20b80c202000e01c075031514410510030905c00c1c140400c0c00140e0b810440c1c07085051050b0b0010a03403600d08440c4080034800501006d209900500c41031200b0f480001d00313107a001c40b40b442d0109071071001081001d084030f12541240e41041c0741280124404040401421840300159804c00040d650001084900e00411030034100072402c0e814410701c0b807003d843e030700c1c2101c05150b0b130240c4c6842d488040c00b440c0d03036055a0041d14241d456108000c00e6140103400300008000a0310f00001e0351414010090400555800c2d04481c101d16562001c090f49041200002403c90301c680c024980505003020f02c5807651908041c80f0560030b09001082041c800d840f000112282e41107010305c0340d400c1060340c1c065100c5960100005580d81c841201140d13409004080c02168 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 190090557 1250 190089307 190089331
    0x903120a09030b060a030b0a1802061603140403020f011239020d080115090e0403080105090a0209010801060804030c02150a031d0726070b0316020c0d060f0902030303 73
    0x102e1441c0c0b150b8400401080f2500c24000c031007007000412002e1141039407045c060390000440d81d84196207002c641404c1100a0341001d400300d40489031994400302019011300946480402c00340501e00b41c0d036a403245000c002d410001c030002e4801c465000343d884e0080420001c1011074800c01c040c4002e04403004040700790030310016041001c0501d0159481c5243c3da002030784080c2c1a01c007240312001e41144c13018421145900c0c0384555440301c0c10710a401d8000a032074854014103150800e030030014420303203081c02424803410324140403808442480c402c0340e011f08010307104d800e400d81c42d2201c2511203003001032041e824081c075513440d500107a60ba00c010001c2213110b030160940b41c042c0ca5a00400310f4007050b2228034500640242d101484400083d113000f1180300c101d5866403d8000912407019a0003148239003050b1048200119041c40184040d5128804212903a900380240b020704996411710041e503a138112068a80060118801d074201c80010301610307001052015541d400300745107500848480c00c1909e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 190091807 1250 190090557 190090559
    0x902030901050f0c180108060a0807030507150c030c030c03031103280b0109031b08031801020d050702060d09170f030a0b010305091f0b040608030d050a0203070c080903120a09 77
    0xd401c43c1482030b00f00c00101140c50038000d0300c1042100c9070803840b441c9810303c100c07803001a4643ea40c500189000d000c400c015a80c02540d80d14010b40d44000c40d014543c05001d42c449a045407600c10940b0b02da001d9007507074406260b014261810307030f00031880314820340070181c0366180c004541041c3c000450041010040c030700064280c415112403040e2142540101d45418851400e06582e4000d2651042c1d030b0300241141d000b074410307140004c410b010035405034400b4040401c65031220784d045910030720000c02c203800740c4000540104e0101d03403078403414a0007035028405002410f49582c0a600a030040d61189080c68500d048034031140e55281c22981003410640700000400c560b00815005445410600782002d011a051984009441d0101c0164041d86070245050b080c4141c0020b0708180c0c9030000140c010804e094a400d10356450380e102000240e006400c181c0803440c050111b01c00c407480364200360340304400d034001641c406c00701d0b601c100c00c0140e044c843c13440014480c0125400034140e41140b0f17140c0504503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 190093057 1250 190091807 190091821
    0x11030d0b13180501110315011b050d0f1e0909020a1107180b03010608120708040e15041d030f0c010b090112021002010606140904140103030918050405070e060604090203090105 77
    0x2494180fa81d1305001c80003030003407000d072848050034240c0c5102c1c04d0070050200c601d00030392142702d0549080040e0080c414246a0303000300d84c01c02a0060502080d9490752540510542403060b0088080031343c200154022004204028882d400707032021410358070341104d00500700c0f05243c0c60a4415000542110405482c1107c10100d601c2108688a4140d0090002500c1d04041ca5101c3c00b0b11802d01031a034800145030400c0028200883e4060302c0324600000d0142010348040904180907160a40198a0b010100041051040e180417500350802c0003113207081e8a0001e090840d070004507165801d07640303a200405d11170b920b100c200744c060240d1605c840000c01a0303004000a1b0440c2c41605400e6900d44002030103a640e000d44003040009101461a641d400d009001c9070040c170800400848851a9200120405501020785400c075520416000502103020f88601d0450320103550007440c030b5001c0c100070001500c00b50810396204100400e03450400b9a91b1414406a0b4011030702c900302c6035910380c00c101103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 190094307 1250 190093057 190093061
    0x90204180b06040303050a0909050901050109180b0105011803051e12070f02090606041809020405070e0310050702010e0709230c07020d050709020703030203061011030d0b13180501 79
    0x2140d80044051218030508008a0820700c2940000340400c1800104501c0791806445c504c2c00420190720100024580003064038000c2000780106401d29013080602c0d1001800d815450907295080010742010340d02e0b00c07005450142d1028400c8030b044c0d5040c00c0010200c3d10034090f002c14014504010441128190030140c1003a06620700c030703441500c044c88490045442c840104480d554140e65422654855400064641c0203d40c00750002c030b00c20100103c03100041c1d4100c030000308d20a9405103d40d86030914180c50b008020706139a0b805910580380348060070b0f40313600003d820135058000010519a80d480144c140034041d000124650344500c1d01c048428040841038280c40c012003818451400c00068914080c0701d8000040e110340103000c230310020300000744903900080844250843d6036080034034014020390011904648100702c618a0000642d0140c100f40003006003070740244d80390501c520341034001821104c1d405a007004c403050030504458a03510945500440507070410b203400d103080c540107007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 190095557 1250 190094307 190094339
    0x11130e07030f140a0510090804051005130509090a0206030415050f01080d050a0c080721200102040501140d09051f0c0309020a05010f0302130b0909150619020a020a090204 75
    0x20681c2c0c007880707004c0081000030501d950460281200854510040d08050702c15010301d80195a200032018000c038091500319000b420054000000300316005d65171410440c0340c00040703030f460800d500702001c1c0c4401498400011544903100741c040d80782c888244a0302d101140d400715821300034888044018801d44400300301c5201d405200307161440c0340c44d4441c54028a03450784064014000308000c181001004904034604440403801d4060380c00d07404213400c0007402c0394040d0303002c0c0c40c03036818444800000403030600844041d11810b850390b1012418158440210b0b42c000100c003074500c1c4e92080410002401404a1000d40d00b4030071885c0c80600440c0240c01c115445403000c00181454405440300603221000103508543c0242840022040c201e04194042d100300045440700c20101c55020860300c0b6040082d01c01d11100b9500e04103150f460000140681281110840d40440140310040038102807100644c030521083c41901d0320807100303a01042c1c0301400d58208415035600400c0510060841d4400e84e8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 190096807 1250 190095557 190095593
    0x4290a03091407080c0907030e10061a030f070c0212060106031406040504020108060103050901020d110d1b05030105101e08220f15180302060106030506010c11130e07030f 75
    0x201c85107000c280c20785e9504803000320350103002803d0001c0c8916000e5440b003032002016209441590300301d0621640101141d0092610441d8a0180c8104400090061301d1050440c41140c0a41e500d8504095446080300c2d1f030100e0b444815803030b032000d0040003804068000e180d20345011031801c4818804c00d907018002081d4a000f24030706420080580c1e0722456442c0c00c11760a080000307068584500e03184c0688a00420000c0c100d081901c52400c10f4070724001080010f07101002005603a940311080c4100d040c4d9498008005103050006005920705200521101115402c08141b40c1404108040b81e00d91554050780c045007105080041c0c4031004402401d501110a140050240059503040800114a06d01600c448082c00d50701c20244007550240384090008100140701e8032442c40d00940e02c200074081c0400181c20200496001e5004010715000f00e98400c138800c0c3d28205060611003c0c0c1d1441c80440407154030354a800d042d200007808030740d0286014400c1d5444242c16414000e50554500b800b00d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 190098057 1250 190096807 190096813
    0x4180e031c06050603071d0f030f03070c06081611160e0f090309060a1220071101030204051305060a030c0b0c1509190807020901091b0c0804290a030914 67
    0x201554005481714444c10892129031f6201d080c83c0100306598000445660140300325003c1a600d808004041d000080c400c201d0884440e803200c1044602c120251919034403601010f00c20038401d8054144000030005480442e400001c01d45100c3c890b40025511210380c40d00301c44140622070130304518669100c0da10100651509000002103003c51050780201410040f400c1000c0c80001490341002c0940040798684180d9400e40100398003050340301120450b612642c600c8500183c0d4000d00036542260002000d0021214000e00c40e040030340002005990f04c00350440d408000551041085c201a05007404441d03110707400c02102c84d280480705603051660005907000c000726500005403e1a6140900e02d003c0103d0340c292030049020f008004000358804c120303800110305441d0540c0410f6075280c04114844028180c1c1e00b0660300c0301e100280240100804120600c0039010f00c2d42100d240384690182241c2030302d040e6002e0001500321a41c8a40080e8480500c0d00500072800d00f9820070758111009 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 190099307 1250 190098057 190098061
    0x711010b090c2808070215041725030905040f05060a0b0a05040902070b060a0b090109060f020a02150901080c030c071205070203010203040309171204180e031c06050603 74
    0x2024070300010041c0112403000a03242e80e8031100381c04000c4000e5821020345a504000e2040581002000c0701d91900510a0904020590814043e46130207190080c4100c8401607030304d5030300d18495000c40c218001003a0064034006c41c1d4003000600b1021980a1f1b9940428582020304100c2540c0500c0703401198a03090900b071090540e1260005d10482e080b850301c1603a94070b02c054003035540340100e0340320242a501c0420f10806000e400108607201d118100e640303095030380e1600c013030681078015607113000c0c0040d00c603030028071940b809007803420384801c078034011a110b03246254002075010f2800c0c0c243c04078607000070a01c040d00703503008190a070b04106d034196018110701e81aa0303e075038580110380010f0541c1c1203080715a20068001ea04403840030350090025982c0b45014240507182800502c6a444642c441c0612050103000215248524040d0340d0401e5182520f0010310790149050920750300103a40e91442200016030b400c200401042980484030702c0e0048a2800306000ca90044c5d02c114080e41080007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 190100557 1250 190099307 190099309
    0xc0a0f0c12090302042f0702040605030d09090b0103050103050a06090507050d0c030c0501050c12071104020301080a0b0a0c050901140405040e0601140103150501051b100e010b030a0b22080d02030711010b 89
    0x128070280c030101b0b6245036250000c42c00040c0290000341e01c210b815004610400e43d8640d80100144262200036005028403030684004604071582444050115001280c0c0c0c0b40003e0710f40d0f00603007a480d02075002c8600003511000000c13250184488100c92000c40440100100003005544a00400090070302c1e60a000c000f07545030341c441c02025801410004001085070420000c0c10600c012980003820440d00e075038641c20860303541c0c0ea088001f51404412400001c010b40340074068220030300e02c180d480754206141a001500c01080101c9201807051091002040315100d5100e203d0240e00d0200050095500d4211100342c4042d08000c21030415040852840040880200d0b602c00c40b04286041503640e08400090030f141c541c1750745ca0f4032660242c00601160346030203412410701106180020820180ea110400d42d0750031050340d0003040d51104d500022800c0e02341520070444031a000e10019070705146561200b030107501c45800c1c07140181d8003005000515900c028034402c14076891307000700002e0030060 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 190101807 1250 190100557 190100621
    0xe060106050a0909110405030c032d010603020d060b120327030f0f1609020306090105042307020a0b06010503190f09020910030611030c0a0f0c1209030204 68
    0x102450060010008072041080e21a000d40380040a025104000c0540d08030f811840c554410301c20540309114a9512208a150200c0d00c0500541369528100c03043d200462f143e280724059000b07115241d581c9103000000b580701c4501d00007500e0b00c52280000c4200e460700400c031206003100d00b0f50403103520501140c00c2d240703100c07000400075041140c03c640b424105400040d1410010345c1c800c1c0e040303010b03a0789001100030700003c0d42051400e126110828481d119840c82d0300301d001c00ca8020ba4440310120040202e81003035841403500c696a500d0240401c40d2840b00141e000c0000d44542c801a031103074002e00184205107802c150482d409181a5196051181501000811050940c248a6901c00d841c54158100750b002e4861113601804451551401d040c465561606600c42600d03198100031840003803030315880843e40320b14003603035025007000002c200031160034004419681c24810801d5580c00444c40c48109110802c071941d031503407155400c500c1031009842ca00704032208203003040c010101103582c0c54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 190103057 1250 190101807 190101809
    0x30c0303020306150703120e0c0f040f110403050c0a1203170c091504140604150e01050403020d0503030910020c0a02010c1505070206040c0806150f040f0608030d0608010e0601 77
    0x1500c0d0168907030316002c1c005002c500038842e1251030068001a840109034010801c8450034a080c0d01c00c001c640c2c4400790703058031004080821644110b1680e0380c50701d2403406600004640310314000001e07007440c02d8546120507610540041e00c1d50f5118032101da5903880e05c0301800700940100d008410024030665800703020104000305503020010b590000883c04090316054403c030000041c07000c070740c001c1c040d0780d0301d00d803a070140c080c080241911004820345802c0401c111803c032030304100340d84451072254900b1240d41c2107082805041000821000000d6500c4010740080e090240010f0f56480c00c00c2c0d00761074600740600a40c2c00003d401886212200c000215102d90380c242c080c281902441e0035407070203c0d2502ca10190103070307540e8904004d0003141e60340018924030aa01c100006030040351a4113085656800480c0c51078003000804c06a2003050a03d41c480e40107000d0082e0004c58104581c00541081e6601a041151554030110705c0082c00380c0325005280040441c14001c00c80b046062846944440301 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 190104307 1250 190103057 190103063
    0xf0609011e0902041407030603020108010e0c120910060b0c0105150307060e0310020316140c100b01031b0f0e0f090406241202102c130f0f0513030c 65
    0x30b07400005056480b00e0300b048454000d50b4680310441d20704803138098000c0106020903400a0106030004c40d041c2740005001e805901c0c460f00f46420a006e0b81c40e042c040a1004040b00c2584c002c1200c207000c1d07488a130156101800340303141d41d1500c48104c0090142101c0006041500031094003189014548001c80c50009a428901d85001009072a002003858200340080d01d40300e281c4004100a07080305648001a605005c517074504480c620115000e8105004400102c20150000d40c110855030304079a11140b0709440c18180850700c603c0c2d050a440000c3c403c0c4528101288003120790300b2856074130012041109a0860307000d0ba900c0c1007140414110341c00100010421a42c41440403000100c411000841300c05851408000c5501c0380307014941000d864030300320301920270034003003a8a4500615000c3c0281c3c011030b149082031440c14001000d814080d51486400c000c54166200204095020304564102d44a001052100c1541e480100310b0b0001010b000161601d500040e0004c0d80c811170824003203030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 190105557 1250 190104307 190104311
    0x15040207150b0a0e0c0307020706050708030f041112060601080c04060c08070f0203030706020702040c0512040210030219091703090604171c021f060f0b030a14090f0609011e 76
    0x410202081c0c804015400c0244e81510714010010300130381e850015882408140c0c2a1500030b66110801d80d0b080c024080000c08a07081400060111842105040e40c458095100c0302e1240329040c000c02e0302502c03120391002e06504581c04010300ca58100310b950340c1004019000318645840c0c06801071490380000402441c002c4002207107010710813885150403d590b00202565554245841c0a4000f5480a182280141d05005060110038010015140307010500a03010703d1a40e0fa0b603082144901e0034507c1002855402e21401060001515072100c0170102c503141e50000500701a4001141c0005d81c42444150b8420880300d00d140d290041580c00b100d00001c8450010211006c0d01818013469240c00800c2480c3d000300b00c260507500140030804211140790903103410702044990416282980641406000341400410114404000640c0d001c0f00c8050005415601090100d003070700c01c00c1d60085510340c03054400c1540c01c103041c85003a40004844008008443e5003a0b50b04000303a08040c0c45009181d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 190106807 1250 190105557 190105571
    0x102c03040605070b13140706080c04050a03110315010906050f040608070e07020304031e1505040206030c13080f1c030506010903030c02061e03090f0604021c17030f1504020715 77
    0x400c541701c03410000358000c652060201174582082ea44145501c92103000440900115141c2840c003002c0750182c8202400b8800c4c401d00b1526000d03141840c3c2c10341a41c00d8030651480302c07102c1d0001010903010301005c46012071140c6c64681000710170b0043c6042c4500c00c4d80b50001c00c004003040051030034204d40120a0121883d600c0c240241e0841c012640050402240340c0b16002c0c1864110014103031803840360401d02ca810001144400444e682140d00030340004040021489c10407510016007440c06080c901110b01c181c945821340d0411402031900481c1c0e82c4200301c40c981d415418201d00c035a007419031404010b20314100f4002404200644406024045d000c3c50340e0041d500c0784000c89081d02c1842c0603010050b1800700b84520564000c0350380c0145401000710340c813203d00010904034021500100180c030020b1201c8412245009030142c2161001d210403650000c404088026510540c910761089501d440d22040e0152440141e04070a0311491040048500280e14903035500346207100208006401c0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 190107913 1106 190106807 190106821
    0xf14010c0b150d14060c030403020c060721090306180302070311040618020304020a0501080f0f040510020d020705190305040e0702102c03040605070b 66
    0x412800403800855110824160008035142e01c031054a060000090301c2c40400d40821200c188071044d40c80d40e000018001c060f44110b0402a00349185401d0782c00030f40301c82c00303400a14402c080100d0040184040590b803041e00507030a054480c0e0680d81054040d010741c04501c81101e480c2d060402554600f00c04819190160380e050f0000c03c01103040d5941d56100b00744504203e50019a100c2c000148151030b01491441c503915444010b80d281854018000c80344410303005241408801005c1c04010b100c079412050748000031803c59407403030303c6500d4440c3c28800d100c4001000f450000c12014109640e950041410500c110f003280d184942c403500c0002044d0b2480d0014001c90424001001514040d4036010380c0680c503481640c1c0c4220a2410781f03003c0b103c21244007a07015642002c1c841080c3c85008604803030143e400000d505040c5040801400c1d8031800000515501168020070b0503 = true := by decide +kernel

theorem cover : BRFrame.Cov 189928057 190107913 := by
  have h0 := BRFrame.cov_init 189928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 189928057 ≤ n) (h2 : n < 190107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
