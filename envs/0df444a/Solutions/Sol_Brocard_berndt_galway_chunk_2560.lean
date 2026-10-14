-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2560
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:22.308982+00:00
-- url     : https://prove2.me/submissions/566f1274-d3d7-41e9-a845-e8ecaa21b956

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 460251798 ≤ n < 460431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 460253048 1250 460251798 460251811
    0x140d050a06031406070f0c03090e04050706110a021323090102030103200603060f03160305010e0c030d170c1905030610230304050109080a02030a03060503150a23 71
    0x185079046192285421140d41d0381074030b699000e8410041c480b40c2085c00a104141c02d81001c50540c0c44901d012130741541b0341d400505000c507a02081c0805c1080008151040e5101515515025680c803240180d40e404940c101039400303031844003880110b20881d070060451140060304c07410080300d01100e00c0215441550070300c0303d9a40c0000100103000b000a5400740c40006185079a010486800014000e4003024010522034119645000c0c803d41e401c100e11910000c0034040c5206540d43d9041443c02070141e590b004503c3e00600c0741c48011440c01280146d40c203000740c0c80ba40101444c080281200b41c000400c130814030301c005c000005c1d6403040c0e04845480c0608640e1855564a4040c060100c01c2705c1000c80001401600c00804640c41d074940d25401d810310346084980d440744d0741c80c1403050250404140180100e200012000720165000c002449407071407030f0310184160743d0f442013811340ea6201000d881004450040c080745c80c40c01d10381c0080072901c222404122504880c0808281001e1058545 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 460254298 1250 460253048 460253051
    0xa0e0307080c010b040204060c0209060a0503010f021206090402010206161812060b0a0b0301090e120a0306080d050301080c06280905040f0b0d0803060109031e02090c031303140d050a 80
    0x740b04000c0d02401400e02c0d0b0907068a042d403e142c900140074103040c400483c004c0c4141e0380300c4001407603512000c42da1401018002e000384040d4254101f440c00a50000005450358406500001d40d0360402603a554000ca80c103900402640d0ba5120200c0d10341c0ca1806901010400c2500840c80d030302c000790340d00c10301070000f00c1c55081c10240750340381450854400c0d18005000d178000040420001003914107031380c111006008040380c04c0d500206928181401440c8210190501044015619601da44030718240c44c051700c1200c500303201404042d18503000034030489280754442503030b092250030400e0203005080c1d81c10001c00c20414452260407400c1c01040c03098000180603010400061401c1d005540300000382040803c1200e40e504041146d2641c14400a06260800404a03925901c6150404020340e0000195000303044140d01c405a0b4054200090340b0a01d00180803c0791420001d089902504400c50341100f021125681510025200301c4000d05c070b49402d001c0700341800e440e402140d1080031100c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 460255548 1250 460254298 460254307
    0x4080102030a06080f0c01050903030f040806101d04110607080706140a090827130203090d030506010c032106080604060e070609030602032502011a01260a0e030708 72
    0x1850780403a80700d540000041d6000d1040e00c00b102c01c0106040c1046e0100b0b01c8c200b42d0b100c45000106c0d155202c0d6007030003e0706160000b030000d40c0740008079070280140140c2c41e0011020b952202d40700b0000c04000b85071029114098082000070304a88100402803038090100e600f021100e0300e40c10041d412640e01501d22030b407140e54058098100794200c0b540501d404404000c00002600e808031a030080283d000000404041802d2600d03c0c00726000f905607000a000700c0c50071620707114400194000f980c90303003224400c00c1c00070300c10a07000340107040c40340c0e5040c0c1d00d41516912540782110b00c4400f114915030842c1c440c0300604100301a5006183c0a0701040c001031a0904051522804542050030700c504960001841845256409030400048a4102501503142e4507046920346008140503c0080201546518040203503010b411251a60705050700280150111600644840b03507c150049542594800880b0316284908521500f1140100b40000c40300c05407448580f17160701940e41600c0610b070224 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 460256798 1250 460255548 460255561
    0x18040609140c090f0705040308090301061a04033003090204151401090f0e07080403030b03010c080103150507051611120a050d020118060c02030705011406040c05030609040f050a080408010203 84
    0x2e44e0460940a410451840e0900c4010b05600807400028962200050212050759003500064040d154040301841040701422091340164407604c403c60700400c801407a59280301c0b4160f84000d01d980040030600000070120402c030014007001d02c04030b0740b00365100c44070b0f02d000b0f2100200341c0103030240b880c1000d403411200c1c00142440c46181e00002084012541c01e104512150780801e400c08198140391050f5121482c0079070252503800001c9801d90728041c4040c2006a01c80c14540c100d030300510b48408290b201000070015074104452030004140f04111410081003504070040307009004004074010080c54034001001c29011084114813a0300840d40d10b01440380c05e2107004d501f0f510381d00007048022001c20460030560810718016120030b548500b01800c090007481103c020340da102e4002c20100340e00e40d0380c009d024201528880d000c0c520302841d0748000c90141003100e0042000400c035102c95a6555a00281007200d01e42c12580e6000340d8150718000350182c4098009801007a002607202d15024 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 460258048 1250 460256798 460256809
    0x506190219030e0f060c09040c030902010e060904200a08090307030f140d0f0507021b01270b1b0c040605100c2f090a050618040609140c 60
    0x14044048114030401c4441001514085100c1120300350742400b0841c00180c2d404103040185010f00d0444c503020f454108840c01c1e400768010504504211810420342e91000c400b00c007260039000d0024042100301d00d214111349000c1011b030076110b40003800403c0900b4554000403040c2d08000c0e51864940010501d000c090b90040724065010092100841c00c0900c0d0751030041c81e6800c8a08040180b182c101400c0c241d14600c5011150800c40003542441724008980c10140200802c654a40c0140580350b0540044041d20b81070380700c1400305a4851400c814040c0101080c2d00140c41100401c08100340e000130011040405414140e09600c07101c4040c825890b14241008100b50f0f01760b07c0390307140030810710142e070b43c01149907299441c918103036150245070f1816001c4007441903e103a501149109016030081c0099041d8948071605840c00c0c41d16480f002502e000f41c69042d2200c541c014000605041d543d240341d010182e0060049102141a40d450385038400d09100b001d111071020341040510b143c403800c06 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 460259298 1250 460258048 460258081
    0x441060402040f0504080a030203060607020603070c0b01051203040608180f1b0405190c030b030105090709110a020703021302040506040303090806090714060a02070b030108030c0d0810052b0506 85
    0x2412041c13001d4a03041c0d64044040c0f0601108500b03040e4044041030304c503100c00c0140e41d5015409060300e5607a042000b4050082810b05408075440700b032500010403107052000004e90080b00460065040034107014090f00c400350001d0500d07a031003a070f600c00c2c052941c0040006610340b0400d50081e0064650068450b400e03800b441480700d01640c00d19090010703280080c00028003c0c41e413180c0015114010800c00c80140162100c901d50540c05c1000380285e800010403000120307544000e041014920304040012a0b01640c1e10210168020407020009800c110304207800409028000601c0d186d1250001001500706800c1503000540c101014031042904002080d00305c102d40e002406200d15101c3c0b250802c00802a0300b074041c400c08124452158020040000030b400790310400b94036980c4445280340d41f41c114510241441c41a0480c03541801e000f500868002e540d03d044600c040e030304107014030480b00c103118204848644410003c1d00b034503003a020301c5240a441007014015a0070189aa4030442d0340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 460260548 1250 460259298 460259321
    0xc03130e1006021009020103090218070e031903080612010501140f030f0c040f020913020903070e040b01030210050f0a030b040f060f18020c0d090e0f044106040204 72
    0x118a0710500c032894000420542180b607414001c92929101e200480c050308084900940194204941104101c86000b200344101070030307960708401109207801c042e601e124014401041c100500c850001282c41001402da201101900008050311030781c003000d007103903000d90126000040ca811140312510700a54070710300450b800c078004c0058135240003400341c076800c07554030882c441d5030386500400884949805840c10070b04c00070a02445005020180d00181d40a00030480c4240105c0d8004691050030429070740c040c0c0c0e081008000301d6801e541c20700034040a514040000d22509119100e06070010030014032100391260780100340c10301c0d880240401c1d1010b60301c1c810302c1c107801c00c0014800441d840c4503240461b0000c5c62020556600f54212000074842c514503044a0302036900c50140c5281c0006051040710320840c6031031843c1c0d4550309044036849090341c000344282c0303081c0c1402e00101141c0c56182c000d041100001c810010340b60701c0040754000034036031200080d04654100802d52510b803083e1440004d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 460261798 1250 460260548 460260571
    0xf0302030712090606080706031d030c0618010f050114210d03020708040302030304030803010f12021c1109011502431208030f0702010905210c03130e 66
    0x74410009020304480c4412407100c1d650b03d807003c1c4280181c4d0340104004102107410741d4401c9480b480001c0c0a02196084940403400080352074083e0040042160640ca41b003001030f0200d030315010109075036484101111141592581d2041c01c0490b060701c14680280b040300024826a001c42082c89498200001c030403500030020003015003407810100b000d40990000340342c010307034a000ca407030409054000c1d074002035050b1001080110030400c5c0e40d002141070b11040d411200d50540d607100d0301061400c041c1c10007500010b400700b612014818010b2803200d503a00c90548890800240004140300c080241d100058400c0583d0010071966014817810a1a414408081645010006070609070b000c0d201d00788408550b403030303010505d5000031400c14405401c121940c0e2101103034a05120b8420f41040e00d48034211000740e070214110310b0052060302c079207661010260100001b4812009000c03181495450394010041002010025051004001c1c4101034a25000407d06000481a00344401087c803074800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 460263048 1250 460261798 460261801
    0x20d0b0a0303021b01090e0c03041b060512062e0e04090804030b091e01090c05030d0e0f010c080c0709230103060209010e0d0507090f09170d090507080c010f030203 72
    0x2e07400315000c00509007a10059000c1c4240c04c00403180680c41d03601402081c8940c1c024405407442c3c200085000e08d00640480500c6048040344009a800511400c00820340c204a000340350606420804d034840e400802200546480b4058865144987d07007004d08205038a140d507600c101c0c0c00070307043c2101c40000c1d00c0c1048129441c2e5200c01c40341c883d83c00060042d490300b0300000c2c11401c1c10805c41c1d20072500c80d8642c0603626072540c1810702900322003d080315a44201440820346040c0001c2c00e07a8821040d40e9000b0700301580d00c060040e06d03001080154100080c0c90100804a02418001d043d61100c841c004c01d20b00e0320301000d0350100c1c1c011079440b81120045421171880d009003141490705594001a0044e0745059400c01655038035090480240c014100012030414450081105d1044030328400703007800030551031a41c04041b40c0c103844009115100940422100592a80140280315020b16001038440126140c80f0b2428415500401450f4401d92500c0395652744850f041042188500b400e5041d07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 460264298 1250 460263048 460263053
    0x905100e0a08070602070c1e0513020f031f080d1701050402070302062413090b01050102030306030d082a190824010216060201020a03060f0501051606060315020d0b0a03 74
    0x143c07090150140c0025000701ea080c06204008002d24000c24040c1d42c3d407900c18610750070503580640c880c0300c0c2c0ca12910001da04000c812000c0c0c001c84409441d107800d0301d441c40d81c48030b0001c211520912020606903203108004a841d0108004002d6124031036120008003268060304601c0955058000d107010300d005004040000ccd0300010a43c2d0400764041110000c0448647c0f541d000e40380329084a0741c0100e82d814183c01c0c10309a0340c0700d140400d00881c1c200d21181e88513001660360b8407080d00c00a4240d8060145540d440b40f1449896800c80c1d04040340c0c1000401032000240c100040b071030783e001480c00000303505000003090304401a5480c1d090030300c80041e2911058078442c51310004e0244d4a0f400c2184900c0301907a00c20722041e071070040400034408020381c940390000d000350000842180801c1c50300402096004035510541c08940d0160b40c1c041c5080f4107203a55945150403540111901030f211840400061b60034140aa84a001c10a0060301d0b000b490b2001010b803401c1c541814043c12151038140003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 460265548 1250 460264298 460264313
    0x909020108040b0411030a08090f010e030327090a02090130020c19080a14030f04060216080f0a0f03021806160b0901050403020c061213030e040905100e0a 68
    0x20b020760088902c2e00260354a0a02c0305080c1150100741d40c0c0350058029980030441c101c00170b441b500000760f58012100e5042001913440f1f540380a4050751660061041c1c1841d43c00d10f400c1d0310340b40b5902c111f00e9201740140c0001301c2c80d01c1800340c800840c042e801281d84595541d014448012146030301c040081211210f00c0001c0d1001300308d408401c0041c0d00010014110b4404001001c2194260050080344080c0c0e403c0081d80e1b50419004e40b000907004102c0e0039401c40142054030300604907003111460640f9280d617003030020f502481003401034003440c200c180d000c500e10001610100c418031801c1c2c5c0d501c141d031602c0201210b41d1005190203240c070501014102d0003d490207441d40e00303801d0710304c1d82d0f0352111803a08581e03082003c40d0041910941604100c03000310304bd0007180c0200d00c00d400325488440002c1c10800f2501401020070410380d00c4000085220400c90003c0321030f140a424a8450205004085001d070350b40000c0c280e4080d44140c0c1d10005407403a5104145006420070060001d003849641c03500c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 460266798 1250 460265548 460265551
    0xd0e06010f050f040b0310050103170f0f03061f032a0c0312060504020408030d0b0303310b0c010b09070908100504140d02071d071707111006050a0909020108 69
    0xa010b0f99080d00c10144540300c1d9800074888500003401c031180b000da81c02d07050019000034003044601d601c1c2e501c03010004285200c1500c0154001104450918243c0360b06229940c20090240b9030042d081e4001e9064005c403c01c0c9a204c1c00c07055507003c43e8001441c6c1070b201c002440c090a035018041e02c81d400c010b685a029491800541c1c1c1443d00c045200e0002d54458042e0a907900a02e501c43d1000400280d2010300100901056038607400600480100404054490151050343c2c0200030820811081449280c01d4112051950301a2040003a441e000400700d950400da403c1c40e50f6a40d150034017030080c42c000c0202ca900204501c1c0a12040d0300f071000680c0c40e10842d00a480d0502e40f500f0100c2c00700102030519070392035403084040b1003550301c0c1c4045c000e503101c042d480f5541c3c41c0b0030042203141c2048000000144102500d03100c0c0601200300310b0036880c0c03188000341030004001104038a209041c0d02806081c0e01001d00b404007242590030b02e001c020f200c071160740c003000f101890a250200183d800401c0075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 460268048 1250 460266798 460266809
    0x302090a0905010b0919050114060403120c0503130303030b240a050408031815090906010503070309050706180501021b01111e0a0b0f041a1e0108030d0e06010f 70
    0x803440052910b0218050181124a2513000e0800790402070720818008079951b03044803092042c040e59076130755080104c1030301030384c4040d4001004000600100b002540402c10200091070541444002031302c88034107507002240b50140720003280c0010070a140d413501690b50156402c070782e22003004400001003421504030200c032480680000c034140341003a004500356801008458147c0e07a80f81c4130024000791741408581d042d03200e10949940b4100114500c0c0590b0082d51002d802500300340c54600040d601034100400d0303030003050b40300c5503c200020400e111140c0109810340700c0404031140c6110040e01082160007883c110751162003114009005514590315100d002c2c00d000c804d1a811002c542e0500e11021020411900d040841d54480140010b500c3e0000d8020114900e0356100c0000400e030300001543d010303104080382c070700e0450884800a4081c0d04481c1e403044018081c1441c02501200c00700981c421903198001062040b502c207494000d10f0104d183d0103001e00003a40c104442c01c071141116001c0d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 460269298 1250 460268048 460268051
    0x17040306060b1c1a030618060f01140d17071202010f090302031e070506010303050a031b02150a060504110d0b01030207121107030b010806070f050f0f0d0912080906100302090a 77
    0x50080c0340c00030b9034800310400107030580e000ba16004407c0440d64034040724102c030a104081c00140c0c443e4885a195040c0c1d02070800500c03900b1003101c00c201d40300300040340681d2202e909010f8000200c502c08010649039210700c800f04901100e00344042e0031614801010740c4941e04000c00800000da0200c12180b0400380e250b27094008580c081300c2e00e8000e00807508024524417940b00080103042d00100641103551069405116840d000d80c03110384094a02003044004d64080c9100150f031072214038000d83d01c0815130100154403982c4000150170f07641c0c44403184a8076000050740041090460051000011080c01d0035450007000baa030701150108000c074a90100000e100074410b200070140000c000071030f04201d82120a507103c03444c40340c444101303466841c0400c3c2c0c581407c1007128020401ea4130801c0c503d80c0f00900382540c12204000962000003a540083c1c1d035a14404001002c000050a400d101d942c0e5000451900010051a1000141a002150a1030381c0308000507a12030380031270f6201149000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 460270548 1250 460269298 460269311
    0xa06151413140708150d210c0204061202011202040b0304120c05010f140a1418121819050303040312050705011419181b0317040306060b1c 61
    0x9800402072400c01c0382c40600a0301c1405191a40719200c40e0090024100f01c220241040041180819940400400c01180b10a1500d03000c0c0f68201510031100083c02d240f40110303540c2e40040c0456980e5000144482040d00307003a0150b50b0322249155242030030701030440c5424202035282d1628013000b40002c0c2800301a4860700b50141c8614081c4441a5104000703000c1140380d42c040e0006822284104a100d01d0100f001401151880c02400c0488000d410040d03900d850f10b11012140c01c803000ca00030207501c06c442a03d06401034101c0240414107003c8007021845402004100e11050480c207410382407140030034103004599020046401326644010904541005000d0a0700e0038051003001411552030f01e00c0184801035103200c80ca06c01c207000c800683d6280010a0301e84101d4641c4959544480803610007400020f100c0d20b50300e00c1d091462149000e00380e649545550054004c4601c0a10840c40420100308014103070254401810b2942092800c0080185d9a811501c41d94810440740780e89456 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 460271798 1250 460270548 460270579
    0x501050609150f04090204060806180403110c030a05010606020c03031206090402041407090501020f150c03060d0803010f050a090e1915020d050414070807091505040c020a061514 78
    0x4643c5003404035040d0300c2c0c0b100c0d6079044210003034103c0c0c8113050219050100180c05864000f107042041000c1400a40140e03c0e035031421500d02c503031103117060078610800d409020b85560401c892211203100e00000b1580c1410040c0c001c2c1401151114207000e40e0050001811214141e0f800c5907209001350341c0c001c015680d130700009024150340d089141300391075003100780000b550f8004200030540d042a000c44280010007034015036107103140f0800807000080c0c01d01040c60080b014009640155004198507400c41d0700d5201e010042e402a48a04401d88041c40c003000b00d400d00030148030051004050400402d40079038a0b01e5110401c1e51924641605a0364079481040202d1918074034400d260760b01191142d6840010000500c421358040d141d0384240041040c20500001d00324042d6403003403014002c400d2501c0c40b21805005001c4261807211801e080106203525207208007860b48850303900402d0418141d080500c02c44408002050300c1804400b403c0c89500c1486100301c1001d1025504d8449650084 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 460273048 1250 460271798 460271839
    0x8030c0a0302210901060b0910121b020d02060903030709051201110c010c09050a06020304120609051912021b060708160308061f080a18021f120501050609 68
    0x3d80420030400100c205201d0000e10072034440e481580c0324802044a640caa0352102c18a0042100c1c040c1d000342100d24820b052445001c0a0703200103110040859000e01800e0802c01c1e00c0121550500168800030a0100907030781000182d80000403a0013551460400e444014130715075443c082c09000741d01e40c203c211558035095003c01c80005075007141d5510b40d448242c11a0182290366541e500103032510b0408181490500c201000322440d0360001d515003460000d6504008440003c140d8031107540d045001d01007403050040040302403048030001e036010910314000c03c890494406410031076010b014410381d0b2010300c0440400b00380381180c00980340d2466190026091140c0300b441814140724112032020107812450281c09104100d66840183c0701850010585d84465108900040c0e40240801d04000c059071003800100e26100c0124080e1089401051480f075640104075403015062200c0d804581d40301c4411120860107281c288031755450840001c1c81030007200401449154100010503400500c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 460274298 1250 460273048 460273057
    0x30903020103110904090b0615121512060f01050117070c0b06121207030e010516021e0d03120c0f120e250306051b03040b07090b0d060f0503060408030c0a0302 70
    0x3c05c18802501c1c5483d0070105414150f03000c9000b2844100002c00c144121425510160b0040040c03031003950301c003400c2122076820561040d80061030222a44940c100510419111b0321040d40544c1c1c00c1d51401000400d030507178070603154850400e00c0040c031100e50390029203c200150000d400c2c009948403440021540c03000c440840a03148603220480a802801e134000c0d1100c18002c1d19982c0d2109800401035a0710b208640103c40191581c4507200c00614008007038030140765880d2480c800100c4540c1c0420034ad0900310b001030f008103600d20659100060307503008402c02c01000d494030030282c1400b00b501502100c2100701616800d40c668111219404c41003000c1040b1031038114a031803030450000c10300c4180c1911b0740400d50380c0905050000e03140d03218840d607107181040f88802c203510f5580c80ea15032139591600a4a50b50820521030000a400b64800003d0000310794011400900c10340360044400340c0b40b019601090294001d42c040101054116040c2c1b5880460000d900e5602d941505e4110002d104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 460275548 1250 460274298 460274317
    0xc050906030a2d210503095a07080a060b13090f03170c0a0c020a181401080c2b120815042c01020904060b0c150403090302010311 57
    0x105000c04406103e0404a001300074141c075040b003c41d480d840b082c00c590070b01c0b080301c07415100d82c0b00c404c200343c0340750342414502040d100f9202c1c02480800071032958100b9a0342900c1ca08a00003148102038004401c0e130b040c0f0350215075020b0041c4200382c540321a00761600b101100c050314656441d1920003064444070216003004c1c03030295080100b0f160915000c0d44502c1c624030203800082c1c03458076030948034072540b003814081c01c06000190705040080303004582012482d04200c0c2c200d00c0904000550406061120000c40078001e000321342c0003800c8010100d9644142e006010f994002403441015850340c0e2142038910449898507104010302c80c45c07000c0d40300e1585500808100c08100742039030041d84030200c0c3d0b000301c00595510b07480f1115101000169200441240c21190280b40110350304480841c04240156621002505101c0403400080403a4203e500c080c2c40c804c0001603017259031405206e590344540c0000c9a0207003505003610005c00146190200a042c103544007500710141d0b60450039a00c00b2103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 460276798 1250 460275548 460275623
    0xd0c170c0f0c1518010507020606090c12190c030213210c060206060a06030b0108070809010f0f090209060a0b0702060304060b030a050703061a03030d111e04030c050906030a 76
    0x86a00c183c400640300100c4039040c0315880b00f01d040d540100c06001e15405000c455000341104e86510741042005030010b44101250403041058400001e02c00074400c1c4100307075200c44224410300080030b6400b40e400f03444004040510400c40420300764070030154039080d00c00d03007641c0c0f80d0400c450401c56044101014805007403a0803001000403180c1e40064140c0c42148140c440e0480c40b0303030f1001c0c00c0d400c1d00c60320301074180415034040009030300c40c1c0f240d40410b41c080103007800401ca22002441460031030b4942d005c00310b43d09880f00c24060950508007881e54112078149d0f00c070344210785001710b0080507005103c0024400e08000010900b8488180c200c0510341c1001400d440000501d80307895545c5104520044407140d090010105000c441c0a1103084884005005136142200103584100103160200712041d403c80c0520400c02051034020a00c846c1080d07908245944605608000102c041290300892150170701c402004401d0318082185440c29a2041c840001c0601d050303005c90142e0180b0149240c0b04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 460278048 1250 460276798 460276813
    0xc01140d020a0345030e0d0519110907020613060b030a17030f090718021303080a050d0e06040f060c020c091e0604090f170f0307050d0c170c0f0c 64
    0x9075440d014004c4d03010004c0d50a54540c6041095032080d000200f040a0045070f4942a00c2010b414007400841e0007600c2982612000c2e0700314990301c010581182c20564401484a50700462820004a003d82115207400104214500320380703203c40714070805c0d40c014500303903c031800403800d92020407082c00300940c0a07841c205001c0c3c0d0414005050303002260b009a40340c8245000c0741d050303800850080b0686001c6041c030004c0c0304500b00c82c02c02940c04420f03031604200e00804000301090010001d04001c10b25a60b8681d6a081d2000d03000302034521005183d05542c00500500c40003444407001010004c1d4003800c0840d44184000303040e070402c1120228283c0200e040410400b1180142d11010b4541d603040161000070f444540500044aa1442004025240c0c100c00034021400b00e83c80d640c4084c25076540249003068800301041e203600306541c1c4c000881d00209440354007030b0050040186142032894800f42c26285900e20100700c1700043c09005182d0000548424030402020494002060720301c115400d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 460279298 1250 460278048 460278101
    0x615080402010215010501050a05070206040306020c011401170a200a180c020304030206181507110f03060f1603090206040b1e0c060c031806100302030c01140d020a03 73
    0x898208580480c0140035881d4075842071410418144d05031003040c0c1d0b9103802c00d02c041d0402c0c4c5a940c0321800c180d9101c0800e100000000306103000804580c0c041c3c60006c03a0fa07505100000c440c1d04010380054098021303440c03801e0340d400d170001004400075811500d8804411203000a1040c03c2445010303407074200c0841d00f004601b12407a03408004204142c26002c014020b0070050481c0c032070003035002c0294460010050312240100e42076811003a03a034001c007006599440c1ca4403c3c0020790021000726244084469a40c06900c1d0007007012800f10f00645c003403d2285070142c1c2d50000c02c0c10050605e0522031800f02c0c559105442503103c7c00c40c10341c0c080c00c080c1d42c8a4981c00700f016160045c6010b20b8440d0170555151044405800c11703140c071500311000404680d200c4c110349071204c2e04010031460004444a401d81c0c2100c80030413110380540e03045206030024a0440c01410304040f401d01009050101103c04100c0a017007050448003c46510f80d4010f8a90108100450260410001c189000f907241e03886100d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 460280548 1250 460279298 460279307
    0x110d1e0f0b0702010b0a260703210905010e010f020708120c25060e15040312080a150e18030403031d0a0b030c0a0e0a080a03020c0414190615 62
    0x206005450854850359048000c038269100e040ea4290000c6c1c280700c0c104005440c0c000003005410684040c4124404858101840d1184641c0700343d9074a5680c00400016808100f64805401c45900d0400409401c10002030403001d444c0302003074100f2590008403030761244280b005801501100c01510040b005400840e80d0540000c05000414000c507410f054007a04c143c103100d80903607e1708108007222031401800b99440b88980b401ca541061503091300700140208080107202440c030503c0d80004084482500070a0b4100c024450440a81307064030030381c041c100b48a03102080301d54a9001010540e641684961a01c142c04450740b003134840030030044101504200700e210388c0203083d11400010640c41e000c02c03415250b80e1103500305058082000c100038a01c004c00070191011103041c02c0308405603000c01b1070032158040d48a240960480800c10b0109a4140020410381804480c184416912881e611001b00c0c00681402c440d017800e0a42e420404006070030120003002c8403444114074003c0740002a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 460281798 1250 460280548 460280573
    0x3060a0e150a0e040314030414010c050d0c021605060d0e06070806030d051306050c0a120809191101030207050f0f060115020d0905040213031b0918110d1e 68
    0x510501e00b04101168000c07030100036510840d0543d48920f21000c500c0741040d10360b030010b0015200d107040341b0031b0354460b45001d01400c1c40f021000c6c1c0c1c1c2c442d030342d0043e064404229078106a0500c11034005051000d1082c400709007540540710110b800664440c00d207a07100e401001e8464400301d56020740020005400d030082c520500ca4075068064854a05440008a5032407241030084450f80c85402000e001c014400c1002e031801c805450211101005151100f2610f410300b182500300043ca18402c102008006001e04424045030a4205200e140c49a40359140300385801c500b241095408140e40d002d002c020014005694a0380007640c2110100c4683d081e1504d0342406200c0e00c841c41150104600c91000500c07243c0003186545246100b410401008041d501210078440f001040303c6000c00800c90041004114441d4003a07092079a61801121000f40d4013042c011307102550720b10081401040c44110400d401940444001c0070914071460180d12805003a41030002c0400700c82c41e800e0030003001e41da004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 460283048 1250 460281798 460281841
    0x31f090f1b050108160c0309031a0103060f1808030c16050c100503090d140408071d01050a061d0a1d072a02010806120d0c0606061403070503060a0e 65
    0x4419140d01c0b20019503030410141c500c1c0f01c070300201e00c0c1092004c5104e04030081c4030030f20a10b4941c0c0c1041d545d8580d0b0382d81c01012201d10307c140b5030280041003003115030710584400c0300c5281414001007901110191890f40030380360181100d030001000400c811003540464030145a904a04003030214142011039070b03034103a80e08517406020702d00c8001880e41c4c05002528801c2c0d0707031007004048041e01c4800442c1d0b0001c0c450f1450f0300264080c4808900540140f00c804043c0200703801c0d161009070640d010012002060f4002070007420b00b11805d004040d03200c0034800d0b80c40501c40c12070704c24014040c08102041182e81c40f002a081002000711a001d61501c00ca5004102aa40d0044020310031208460310240c104140b010409004c0070040c01540204003441c2d000000401400c00c03914040d14103410100308210b50000211081c8641d0204050b52284001070242c62500c107242c4030f8a50640d1805100c0a02014180a00800007604a0340d030743c003401c405000480c481d9001401c180c085104a01b511250301c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 460284298 1250 460283048 460283093
    0x3050712020105010b04030f1a0915160903080f0d0f0e0d17061002010f06060e0a060c0b01180b03070305070906120c03030f021005280506031f090f 65
    0x300d001403050203858180ca4515414518203442e40da00d240c0c000c0095142150891100302c00001c0b0782c0c0320344400a12500c80300014040005402003e4001070b80d009019510305694000060600782d8416170304402daa40c0849050b031350b088141d510401034003c80b41207079801801c01000100e80161a04105e6250200804880008000c1d4206403021240e084030803152050600000312185000003007000c42c45550300000a138220174454403000d0700c081d50805800304100322000748850038800d1540300280000e1410a250389a240d41e1803032080018410280c043c03006a1700300e040c0b2803c590088841d0200201140c010943d6441c1c01516100d076072144002140ca088400903c01c0181158008030941c00880f0064103421030350261500b40b10030305a203003184a0446c0140b103007802c0b440703124001d5554071920440d030020300300c120103116080108010030074180414041140c03400102101010a207140c08104000344900190003880b000d50041e140b103c140340c0d0700050149075000c0c0095594072a00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 460285548 1250 460284298 460284323
    0x409020a080f070c030f180906050901080a0f110609030a0b060913030507080a2604061b0804121e0503010f0b040b0307080415020712020105060a29090d030507 70
    0x101d00e26000b030219402d0010524810550700080d10940c460010700e00541054503442118040c41d20b0801140c1e000249003655841c414015441d002c000b141c018500c3d1001041034406a590301c2c0800c0307800c1c3c80003d1041c000d44842c02032540e00c09042d54100100602100c0040354142008900c0301c1e803e40350140031741422404501c01800f400b048030325154040e103030680b0389010b82da1010440d600c0900d0030001c00030341c1100c3c4001004030030540101c600c8a04104030f40c500b094100003003107455070703000d601c22080d0450413040802c0e013200405a0090700111505003625a1000a840401d44c0641503411611010803038104550080040c43c1680c403a02c2043c90700300c6c0c0300c42c1c80d42ea0b18130683c00740500500c82840050441d9101d801040d40c003074858084000146800d02100041e45c00c88dc0040703c4000f8803281403440369909105543d8024011200e001401b0303d880315070340070000f403080110080512210f00130015070fa080201c030300d10b60019262070b858250a0800802c02e070400803040302d15000120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 460286798 1250 460285548 460285561
    0x5010f3302100b150f1303050706020604150912051b031306021e0c1e0603010e0a200904090c031a070815010206070f020a050a03050903010b030609100902010c080409020a08 76
    0x80c0c45246458001c1c142e24030b0904603000c0303800705d9080000010144400084080001102405840010309003500149030a08242c039001d2051204010000e44181c1f9102070100401c4400c654042d104005c2e090941d03070784540d50003103110380000000801d580c0c400040c0740003404c0300c50f2900d501240c8050b800d80ba40c0301420b41d14140e0048080a69040c80e03880320240c02c8040c681000c02c0d03031540803413031100700d8000380d024080741554000741c0c000d80702c1e118a007040081040d900d0040200d080d2000b42c0000f080090101c071001c1ca4011408414029a80e5850505c100b1584840000c065030700030183e02203140611150710000001110011f0029210350007240d4039803540402c40d60f551b68142c02410071584c1d101c000700c404060180b00d040452040b1240080410003d104d1110114002e46d610303903841040130141400d41e8a51283c490084d449201000041617011030080c42c125046140070901c48441e0004940922102402810301c1d0f0b800600080d928407540d0040400302959190500c80340e6841 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 460288048 1250 460286798 460286809
    0xf0506011d0f0402040506120105240609010804060b15040b09010e01050406021f021c06051c020d06090503040302090a021c0501030809040c030222170105010f3302100b 74
    0x181d80360b00c10784014201190051a103a0000e41d40524054021140c200309524003900355641510004001c031031000d221010032244040c0110415815203400e403030109068002003101071f00070006401c040c1c0d6054a903801c2d5550012030f0b00151313010703044a07440e551a603801c8643c0da4003120f101c0d404550b0b040e5007020194050001d440446c0c8140e0007400d1302c00d10070f0b40708140e01c60301b207800d005019900f00122405805245075000080e5a1444009203241c10201444022420010002c801c0490681201e00580d01c25522801084d44044042410b14140c44c160f865401190002940080124200640c806665000d085a81503c850140c01410b0f0008000d007120401c2c0005080302c0320821007141c180c1490782010301c501c2e05034a401403911011401d601002c2c2c0c2844a8182100d0805100300812149046280060b0710100d001b04420b502d0010701030f4510543d031045001c5004588541d8003007001c8049008010354220303180740612105450700a40f240100c40c002c050851030b0001b10b61650400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 460289298 1250 460288048 460288051
    0x606080603060109020306060d020307020f0c03011e1a03030406020a170304020d1e061104030b1f060f0516110405072118050d050c060115050702100c0f0506011d 71
    0x40c0c0501856420071140c013010794401450560407100c1049103a44400051000318402c2940750301805160314034503005420544440c001c18800da040c892074200340c3ca414004c0800c284c141c0680003c2280b0fa03119259400161018248c3e8140804240042d00ca030300400e03087c255a214092020051042c0c28140110340019a0301a411030005084031001038102595a000b07402803815104c05c48601e80d50b80c0d02503440c411820440880082410420008050074203500800c060195030f20f11650010803403098800f500c155020441d0904512156074081c50841d174086541c0075559800c000b82c1d040c03519003910302c5c50380180514a08000205980c0c81080301c1d28560000c04611402011070a00c0c14000e082c1115448200e4080719800c40001203080201d0b0b10300300d425072510303511248101c0c041402e01405900900031601c11044d407008a550041c110342c0f0240c0d0494941c3d581203903100c03044840400501000740320510b0401c01c50240900011014121905109070900c1d0143d102d8151100160 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 460290548 1250 460289298 460289311
    0xb071107140d0201030e010509031e041a0307050d02030c0403020109081506130b0306090c01020105010f08060609071209050c0f060a050304060f0222090506060a080f0901020919050301060608 84
    0x10340305a000340c41c2c5812000308103401458003181c0b0300d8039411200e007100d6060710004802d500001c1c10041e859481d060620310f050702c0180c000c0c1024a49812401810f80c815405514000000f001595503400349041c0c0e0f03400c6006c0031085459140640d01c140f007035405800309a0100700e0039040018402c2002030700020012a6a400f1295600c1304024007144100c04d90710452001d44800b500711964400f001501d00c07403800ca40040c40d070004100d00183c216031040c1c22541c0001e0141c10b0900c0b00c0390000948980121042d6071058565654035421500b0a0540301401e100600300720088007403140004440b0030404045980c0d415500900c1c04001680c416500c104004c03070402d00028001c15001c0d40302400411410101619200000000c4646902d107103200242550500c441032060183d18402c2c1c40d0300c480165011407a0562070360029045801c002d120610101002000604040c0290142e4502103000360004441d15221a9035009101c41030240d140a0b43c6014000a00a407040300441c1c014135 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 460291798 1250 460290548 460290569
    0x70908120f16080c16030204061e1208041502030c0d05090d060b030703020a120b010807050906090604060b030c120f100314160b19110715020f0105040b071107 70
    0x451400c080c0c070300648400410f56810b00c05003d1007140000c00e010750011050030300e104c180d003181035104005c01c907642c6400c05c46003c42641c1035482950002c01540c41603401042c4404c444148070b1909222911482d0081d801807034400c05d4100b90581c001002c4d20705000c014044c1d6400301021401100c3d640a40009903901a10440d444030200360a9800403460032406002c1e6601d941d01c0341c02141c0030030100d42c001489030586c50169010311080c084220701400500c00503100d01450300c000940100400f502a900c515950004130300581e807140c1c8194000c117207441d182500ca1408404d00d000542110881017011500800041e890001c101141880342050b85007414426095850f464442001050f03d86000e128441c8616203250f41c008409000b000a0309040c3d40e41d60008030740402c54180090400c003446209400303080c0311030012802800365081003a80060031802c9030401c0f490082da00b89441003035480d05003480180021001001e110310440d0300d441d4412201e000a40755034040c0c42c0304019280 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 460293048 1250 460291798 460291807
    0xe150d03020d18080105090a0c12080a0e0d0f11031506060403030323010801090312020901080109050702010b090c09013b120f010504110a03020919020c0303070908120f 74
    0xc0e0b003d104003040c0e02581d0301680c0603007078540150901315141620b014000d9403145010004010070007000350068241c00301c1c901c0517844203a84107540c900821000105000200200400d55211182c09800341e91b00500c1200021146003041d1074178809100c4568041d010310781e100203000c6041d4058600803800501024503141c51a2400c50042c42e046802035681350f03102a034400540c01c0740c1c0811303029210a03c000074620501307140151200c16043c800c145100c0c0180211798180e0b070480c02160448a4041c0085080c0d44e40e00400c82c0100140900d00d540a511a0184400941200050901e0700000c0c0c840d4240c3d010040a4608054005034090407010814040c0007000ea00d001902600000040d00350b001c08415204000d081c50424004c803503841c0e41d50400c010034408500702001c000c4009032410107001c2c1c29a00450380910b4010010100e00302640c00d82d820550482d41158001601c0d013055a0300c1e8108180010500e00041c483e050f03c0f4811640c1c481c40f071442e440c0484135590705038035650717240 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 460294298 1250 460293048 460293073
    0x52202090a0f020403140601050102011a1c020f1314010b1e072303130e0105031e0307230f0316020d021201150f0909080307270e150d0302 61
    0x20780080c0490b6440c0c55001e010000010b243c070f11468102c012014098403040d8100800282150b0ba65042c42400b140411071255032501c07030b0600001c50408510080190b40e4082c0041a9124420002c558006042002424664107035a00060043e4002403400f8520b9a031a02568150f0041501d079008100c516a0700040ca0740c0c90303400030703c034181c810101d0340c0075408114002070090103007141b8182240c00000f48003403000503084000c0041d0001c2c42801c0340e613505140101360348050305000b40401c0782d90810341030b038003030420000d4170b4200d540083d410000c0c80700c8002d4100803280900580a8030f00c81e0500380c0d0b44401c0040140d880c2001010814962800540c003081210012440c0c184c0e04800080c94000c0c0300d5a003801100c00840c180c203914501d072071a01c14021030b0603501c7d5003d000080c2c0340a050b4400901b001d0111b030340000551803c012200b50a25a0015402d4005404152402c03600b000144034a9040107442c4a014100b0b48412000c00d1300060100000c805080200142c0182084058 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 460295548 1250 460294298 460294301
    0x7060e1c0203074113050c090d060f0f02043f081204030905010e0111060408030c0f04140a091802060c120d090b130506070507030c0b040303052202090a 67
    0x1c400d02c0d080c800b84448000c00b85810b9120242150316180c41318201007024281400807600d0000c41c40e00c001048985004407060026015140b000b41c030070100c400e0500140701c02d5070817413a1150301716442040018034007010100254403506c2803e00516010100182403d10740c800c148107a5040582120b4281c0e40a21941007840746200c212840c0b40180207424070212100c1c009442203110b0303100d07a80002e00b018009042c01aa0700780c1d003810403400032403007070550b000425001c3c0c005070310010300c40e00c946548400b007405004010f100890b41c0000b082c002410b41e1410340142c454a0f0940300c180c0b030a901c0d0865001600c0b051400783c0da1044c56009400d00504080c001809291030030741c1600e00c540f41004803500e2a030300c841c80054216031902c02807030a000c204500307035400c40364004628003008140c2d81c40f51703107907500104900c040c000f003c541d21003410300403186a00907503440514185c40340341034a4040c0082105a8040145140030320040c0290420402c1c01c80d646074004002e12419036600c0c19020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 460296798 1250 460295548 460295579
    0x1090e090a02190b0d150f03030c0f0c1706153309131a010305070c120c02060c0d0815010207141207240203090a03030807030e07060e1c020307 63
    0x40d01958000000140404194045c2403803c82105d40422000c48401c2c4030b0842c1002d070b1b0001c00107180501400c00001e5041282208480da120481c04842189820803003d0489a648910202d58010801030000c4001040c0e883c42000386d00e2a4000280030074040c4a00a00404981e61b16641b1805286070103e40b101030003200c910b400c0b020a482c22405202040482841640d460003880e200c02814a04440c000882c0e010b40400f803800b00180c1c0b6000c0d10051901c5100305026006513641c20114000c203106031650f1400d01c0e0040c2105503503182e0940800d41c1c40d048800708a000030440d8002c10008035a07060003810403c4164002c003c581e0800050100c1c0707c52444405520003c0c90708210754160301403107082c00a20100501107541c0c03003503104403107481c580101d01c0c10464104005102242da07a40580b002540d03014a0485142c1d80c5400c0d058000305074040451070b03203108410300051480d81c400d10408140005031f58480c5111040f41480d4086058010025415003000c4414401d0740b051a0035034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 460298048 1250 460296798 460296829
    0xc0d1805041a060c010b04060b030403170703180308091c08160e040903020c03060a0b091b1201030b010f06050f040b1c0504030806011e0c080c0c031b01090e090a02 72
    0x31501c42c800b20020325283d124240c06940d070b0b5128140041207181c01e105100081c0703041c04120740f452a19035402495501007401c545a480c0361503010403103080c1701e1340c4000d41c90b082c10610460030070300c4c0d070401400b030040844d00340c210f911501900400c007440a400010100340c280e00d035504039841310349a00443c21652005181086040c01c60200180c4d580e00841040d18026000b07084100c028200741403c0c030100606050b080380c10150f101485441e20462507510103014590030070102c0501d044201036207c3d141d038919080b100302002000b8403042c00840c504030b45c451303001c00c91403070340e940c01c1640e140c05411884448944203000c00c204500c801d034000c03c8022505450071b00080904d00801c0121a4140c40640006080408100003035030800c942c030418148a0181c10500c484090b00240001e00c031172030051000202040c5800348003030800100342c0d4a100182a1100404400342500003524100c24a50025140e1600002d5191807411418010111400900780c580660b40a0100d01130403240b86 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 460299298 1250 460298048 460298081
    0x1030b030d080a0e06010f060801051c03080a021c05010503071a0306100c020a0303030e010506120d1815030906050a0204230d06020a020319050406050706150b0307050c0d180504 78
    0x31113400401d0114601800c0540009401c4a040990080a092050b0000340c0183c0e0188841002c49140c00810b840059051070200e050381c1d5200900406070240080d40e00392030114109000c02520f07180c00c1181a14001d0b0101d0391050342e01c0507109884442c40c0b81c00d8419040030404030b1141d0500b03800d03550f1440e015003080690b100040c1c0c042200200b2170740c015000259180340078480d914003802010307001203040303c48041c0d00c928800700340e440f80f440120082c18844084050140400711101c0c14000b0000503150200005031450080c000d0306815400b181c00500d01400200c88019a20a98095500e505000308400c0ca451402284070710450300300d01d5214448000c000001a0070b8002049040140d0f4007541c0c031070350440480544002c205000c81c06001c01800140311050f803040a581c0c1b9140c004c0d0010031617940c0e46e0408501c4441540010030203080c00020040a06c1e0090000c2403c060035a048841c403682902044552a001c0c0e11751000748404072808124618041e00000303641000ba01e903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 460300548 1250 460299298 460299311
    0xc100f23060307080a21050403021f030902120f010b090408031308190e0906040509100b0d140d1409090a1a0306091c03020f0405040c050712050706060501030b030d080a 74
    0xb800d281c145000700c200c8658010480d41e0702e00e011074241b0148a514039003050b03800c0c0380c11a400960350702c01205551022600e01c003217195015101c0c0e00b19910480d00a031901d690440b25003480ca49a1200221507480d660034034400341c48500700b82000c1481650480100c50079511621105038000c1240c20b01a00d40303800502140c0c440041401070750400c42440c0d10b6400d2000c00c61001c1c410b441000816840c40360b46805c0800c4189030001c5120512034001c81000581500c1d2000002c1420002c0440135182801c0403d10620380c80002810790140300e2941ca640d040500d2003000407a00344158440c1c0c64100885402281f00e290381500400c01240031540350941c2070014401081c0340c9282180d5445403035004030045a040020040780c032031012283c0c0350a500d0b210383e0440d450028400c92180380e010715515022035111620400075100010b81c050039040e48004860070050040c1c20060055503810f1070900001180c0d80a407140c4800c554001e800f510841d00b080c0340a0380c0700d07000180710603912600d908 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 460301798 1250 460300548 460300559
    0x519020408060103021f020a060e03071403030901051006020a080a030207020607060506100e090c090d0804080a030e0a21021309050f0d0201052e0b0c100f23060307 72
    0x1600c0034216050040805600d1401000050019110011102001400081a01c46d808a080c01000b50480c00105449620501451840c8681000609419040ea185802e98040070000314025403050000344101c0c1c40380342000c01200d02d24032074000980c1c0181c140b103000404603404ed0440c0d072114180107040681d076401141065008001c2100c81580e180704000340d5181c040b0240c074582103545050b03518046008081618054058950103a01d6404190f0260541d1100d000c1c2c0c007890351003809151034039582c01d0003035619901d0200c12000324090860810880c01c100406074116507405003d4a202c100788105a1407004040704180d030004000100606c150100780070b000d04c900d10507402082c100902d4203056041615040c202d0045904100c09e014807181400c00c5607540506c91440b1100c24800d20302c00018812413a4065908103201080e150000030380441c10400c4914a640c050284100c01c040250032200f4803900d00e4002c443c080814804100070301251070b8403000107001c55540701d8441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 460303048 1250 460301798 460301801
    0x43209120d0203041506080304050d050f010617060108030336071202040b0603070f11010209030706110f0607050409090f1b17010b030a060f0902100504090c0507080d0519 75
    0x1a841d524007580c00009010030000c10298840c2414800303a03040010318240f00391161a440340380310b030f1880744a92400c01c40501005205402420242d0340007000040d6541c0c05800342090a00e6900019014900001034039000110442e4400c0b8054000f510058a4081040c0517140142c58082e0308020401c0400c003a00804119810240a060200d0015054284104000e40328030209960141100f0b01c00c0c0060140c000c190200321103024100440a0018002490f00901640c0d40c401d83c50701c82c035000040c035950408881e040d032039642c0701030381c0350303200811442c41d5660f5046d540d000c005030081108120600b6a5404172081611640e07400426501c07d0711480b071030317031107440c0e1600c40c08408080411001c24180220510003003454000d011b52414180000d8840224036405002e5a4890700c80444944059000599a81d4028514403040c4c10704803000700260010f0290080d40c0389480005c1480034010ba05072a01c0c1d644c4504401e1500c85076500302800f40070041c120181040006000e1400c22016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 460304298 1250 460303048 460303057
    0x150b0c160605070b0a0c1209031e02120304110d050102030a0902270c0d02070b09010606090e0412030b220510060c0816050330010608011206050403020c060a0206010504320912 77
    0x3039980051a28078215503284180310b12b400d5400303540c00107038402c40c00c211460689900030380103040a1001100c0c2004225090284100181700f940700008004d400300407644901d10160007600c07144000803414070342882c20003803032580070000c000090020700c40c08003400050004001c946005030810005585400b4481c105480850303441c0d46514050018a07400404074005000006010031142443c1e16209a80110103003d5803c040d2990040980c980790441000c0c82000001d0485042c00c03500107c0700c00929065605c043c01d00305545001942a2183d8113249074180c000301d03414640f14410100d4601480c4001d021205400203000d00110070600100980940324624860491254080c46041203040141c0102007032244850041c010213403104c84103040d250380408001555140e40c10181c0c588404108640d6211000244400401d54045007080c101c0d0020755090140c1d911456401c00031304a400400d800f40c05210007401c620a1480c95156000351040050b101e5440c0303c4a4a24841c0d4030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 460305548 1250 460304298 460304303
    0x20f21070513060315020f0f12150a051507020a0f060513090c050a0302090111010f0209030106090b0913030e030d0f0809010c12150b0c160605070b0a0c1209 69
    0x510810090070070312500800d1180c0b10708100406821a99642c0303900c01c0e40032404004c50750200d020403800d480c1c0d5085903620200352404030b444000d200700c119501201211800b03420000010030a00a0400e51590341c01e65800400c07086003000c2151100c00c10303030070001c001d91b44010780003400a405140d01c40290054032069403102c1c0c5c0c031418080e021109980300c0e40414581454000740040e10350340001528881c00d810310300503030358101c408012035044c40c2440320081e4030351802c6100c0b4462100ea40c006e00c0b01d400103a00900841c0e9803451000101c0f00d400ca9903940002c0f0110010f2404185c10090740400c034400d0508400700e024200c0403e00c1e000c0105021000319041c607041c10b90064202846a0348085102c0c0284481081500005c1c103004103030004044294440f40c44c0c48203500c0094590015084200c61b849d207907929602416525008403107413410407000c041022034000d104070304803401e00d81c0103070700380302284c0f280440c0c1c0006101c044c400204202180ca100e0031825254060100c1590 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 460306798 1250 460305548 460305553
    0x908130806130302070b0a0201021c0c12090c0306020903070f0605070303181a0712020304060c030b03060f010e1801020a030c0e01050408060c092809050708060607020f21 75
    0x50034450094507203400507000780d001403100c2d29008000303a40028500f0640b007410006075101c1c007480c4002d0f40640200320883c9190503030003070009940e00c05039009540041ea00d585103c4c10900249011044900c015400f43c0202d0701800c003440450f4254004009080b0051f040301d5800340e45441d00095001c040e08454009040024804107055050098440700c11400c4015048041d480d9545801d03005020500402242c1510005100c1c034080c0810503001d2040c101c0943d56807915142034002800041000306c04280340c030855032494200058218403580210991000590030110b14500000e0000d0035a41118060201c08035041000e0018021540207030700c010641e008007400203016018070884090400c03038140001c105401000514980203100d0040f011360396040320020410b160020a901d0700c0901403408840303654024140b006084400c0b0b54010030040e21480c0d4205c40000c0107440303071039000405001c240054a81200302c14605900180a94421304078442c421000c2820329000d0360954 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 460308048 1250 460306798 460306837
    0x120601050f091905100f0605070506100b03040f020409060f150918030513050907020616020604020d0b270d08060405040206190507020d12021e1f0908 66
    0x90030540400d0718242400c80301522940380100020034140080381c4100101a2900e0101d900c00443e15000c0010b0701254945254044d115003016090358816002140d181c45484002901a489001e1200c1a00c00c0d844559181d0f1320f95490b07120400744480d01c02c0c1d074003950354841180000d00354412002c1d04500d00d41c01044c60f9244c0c01101000020030b511000d01e660030a89012610924203400c41c5070319625040c510784848500c580741c6000071261f00403d40081c042c0080c047c5e00c0d41c001483e1031085804c0706141041003c11041242c0710001644d0003500b00c046c2c80e01f903030000703000341000e0b552090301100702c14000c600c2ca035441c1041490544030054a40c20001359030003100c2e8400030351980450142d60502c800d08056011588510512840042899102d480801c007284648102c4602540051a0342e140c00e055041c00442c007064031140901520a10307a44a08400882c24070941071380b51100605960a02004844040c03100b034503506420594681c9900d0000394003401601c0c0d40701c0342c0e00c0382400c034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 460309298 1250 460308048 460308059
    0x909101401090b0301050405120c0c060705010b030714090a020a17070905010e01080f01050f0d05060403030609060e1e0c09031203060102070f08030324100e030601050402040303050904051302120601 87
    0x319404015424043d90505c0204408101c00027048568520740f82d001955541c502000c803414440c6000381c060b401540011850b00b03004054101013030718481181038821103035a4a00d90904010007031081b6800400d45070000b03800c0315495011303000b0480f460811880b5144031044840b44404101c81803004200000420700c000d50f0322040407500c002082c2042c0117941400500241c0c0000b051080d28400c507103002c020801070b03c42210711001142c2c0a022030b41c250410f40340c0500680001d0044c9240c0d285840d40000d500582c1c5141c45000729010000d0060200c10203000c0b02603e00300400d03403410311208105114498604010000540000c14411626800d02200090801400f94095803000410500500020f407011003101d4001245080990b40c4d4440391a42a5050031180403c0390b2084041007031524294003e0b0035001007030411015034580740e80300c1e41008201e00403400080c0005005001e00c0300317613040650116800032000040c20300400700560000385046054080000c2540014004000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 460310548 1250 460309298 460309301
    0xb030a1401150503060a0b0301140f0114060a050a0305070306080a060e1524031005040b0a0b0603070f080c12011e120807150b0301020d0b01181202090910140109 71
    0xc4034400550342e801840c040000740e90f440060f01c2c004460b692a001c01140b030f80c0950040009106030341c0d2094a0b03203171401014000c54030034461012a801301b6920340002c1e1901600326142d1135943e48805041c80d41040048001b0075000703003200103041d55184040303070044042040603200d91140c44045148201031070054104001d58004010389204072062107540400e21a0178007100b41e04020b01c0e400c010040380000d10300000000e56960140c940018081031051144649120300a8502c4c1030082943c02d5081c00340c244800c40300d030000228800060b2040c248621503898015050641a0f410494800d2500107108000c5e8403032031400000400600e43c00706001800c070003c140c0008808400121911200d42c1d074400c1440052007019410010403c1e480c0b141c6c80030f912954090021901e5a0103a004070000b8016198142c0c040303034101c4584882d034400900c8940503140b80000420042580d80d003440080c0801400b41002401041c03072000114005105064408080c540300c8104c0c0e5241203545070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 460311798 1250 460310548 460310561
    0xc070203011b0203070b070e220b030a081606060b130501080c030402090f181005070905040504050309040903050706050901090311030721020a1718060414060d0b030a1401 75
    0x10b4288a8081c594101a004800d0301c0050740c00010f03035807643d03a542d4070440320b00000d030b1141584440000940c0020216040307038240355a100950400c41040c01c07204059441ca8a80d100502c4410b04010034000c0003410781032900c03a02d00c20318010440f1a00c500600c600c64110b40240310f031710841c00c4000c01c0190703400070314541c00143c02c0344007a00e9400c254000c114240c00040c04501c24624850101d408001e00e05803c1c0c0941007a0720548044000c10100b038005048103648000014200450108180c0781610500e8040c541c08001545402c0301041400068509010103900340a41800b150020960500599211ba02c1d00f4000050302d4401d4900030701891040aa1031205903c03d106450008411030013042420002e50300c0d00e00c00c40c2c0040012860310030406401000c103510010b40184010741c2030080c1107180c0000000180d000c4000044c003106001d01d1082c0c1e00e00f21900700c000d09240c144074004001801155401103201004c62002c20700d04032a400c0c0c01c5461100b42021041c2c502e80030311512 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 460313048 1250 460311798 460311821
    0x60533030c130b1531080d02010617010218130902090c0705010c1106070809030f040e0f06010309020604140f150910081b090604030605090303071107230d020303030c07020301 77
    0x281c02c003480301040218038641d22080c60110038180d190705006400c180c6041703000740081c0342141e41111103100001d0190210307110b04464001c07038801604501c1818025a010202c500c50010204d500002c00c22281003141401d68000b00d82c3c0340b40100c05612008810751055450100c0d942e03640d002032030a1421182d00700d405c0800c02031090300010541601148131600030a60f0f1406000035203c544be610308504c030302031303072140030702800200040c0c41c4172400c4071517118080e210010031080e503402c0c0c0107405491254030000d511400402c010322102c95615801020001e000d00014000e280f03800100e0032101010700c16001800001c984140349161042242035500501e00c8c1c001e1490811611249602d40d004c041c04050682c0411038076096198070341a94015a0042000e01050a10343e116980f40d0b80180d80b484005000102800c183c140006942c004541ea1a03800400c0c0081d0000080048038140341c00e554010b05525488002d81c3d400c01c080c600a070f068200113540c42590340304260171900d400d200c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 460314298 1250 460313048 460313089
    0x605030411040c0207050909010926030c1303081c18150c0302070c151e021203060f0d030305060f120a08071e0b0103060533030c130b 59
    0x4200005040c116065001d40040c2e4000c908046840d2050b030415607a9080203402181070010400c880805420811440b40a0413507000c2003140307200103002a00e100002071204040c00c00220349000f20490092514000d441031804480d034030780d55550704990011800c10354000001d241ca44030580c1320f01c03d002d058000040101c1c00b0310f5180c0d40307040502c05400020424680e60b9500075259038001d4040720002c96019111843c015141c0c00c03041012402c46460b50000340e10004d25070000c03081c1446803c0503010036002054160714181c54028250b1004242d1500442001640d03103036a107500ca4060415442600c0205003031074441e0600c480324152079074082c0f05411146808003c1ca0012450a628980003c00c4d155500c1c80d505144e00d00a0706c0b1401002d8060000755050300b40400781c1261410380e44a00000e002644945081c0100d80f4891692001749441010700f40c031249803a0389403410100c4014007503c000300c0690b800a00c001d0a21110f52200c40d0700c1c0c02c580c3c465071400040071041020717554072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 460315548 1250 460314298 460314301
    0x70603050a180323070f03080105061809180d092c0a151502070303020d0c0b06010c0c0801060801060302120319110c040c030903030b090112061d030a090f060503 71
    0x1540440b02c1d07030804003800348041c42d080503480d80111415605440500084140d884003e032916041901000c201600000d50070400400c082c0341c101c0440d00e980112601d01e00702904280b082258080c405482103d5418001e102c408580c05c2c14049400804000c0d1a034194076443d00340c0420903500c1000c845842c9520100e0244008402029015000402031030001900650007503c11348004445d0410b5016030700c540303a080c03d15a800592001a24030036826a5012155004150741c80060550005d107000c3c8960001986544a00d205208440c002c1c0307000e024040e540c16559003143c203d604000b0160351195028400d6003040000110300c0840711008501d003040da0790140580302c1070801c010b420032000741001e2910b070030104660341090340d005004002e80c00c0c2035440030b07004050145040740840c0c20403203038504514115000c14100c4e00c11801c16201020140e56100040441c0030101b00340004200d00390781b0b450002c001030828a0415180d80d4280c6040c00340d80e4007400031a03800441008020030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 460316798 1250 460315548 460315571
    0xa02070b0c09010f051804060f030516030b0402011b021207081608120c0c0915010e03010c12020d0f05010609050915010e0f040e0105250504030b0f091e070603050a 72
    0x2180305a01c1c180740041d159240d0001041001b02250603056005091040c082407603203400c0a00c00440c1d100c0c0c01203d00c00b011004440403451514480030781903040b520009005035006814a091220640030484284500c0713900259090303c2c0e0184140065010300800d1204200404c142c244d94040741c0310401c0d610f4580b0303a030155503214150850002d2000072035002c0510a041040d170101d105c005010107030600c2c080d00e620b4400301c8076514250004913a603425140905040c0708198400940d50b5418004940070680c2601a62046400008066950782c145900e030540740b00c0d0501820302583e955040c146000108000000c000d4241c1c05899280f0014203a1603070080f5000c0c40c00102541c0b0700181d05542e40001e401001c1d43d010011495003080200540002e5614285a07501554031083d840030400d280704855a001f603003c0208695030b40008a0564083c040700c060748250900d080f24032180d102c10391091180140c142000b02e6522460b03040c0117490301070040e164801900801040780d10480d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 460318048 1250 460316798 460316807
    0xc0201140f070c0f06050c180d0f111201090507060807080106021504020a08030a0906030606020f0606150c0a060207020108070807050d050c13030807050613020a03080904140a02070b0c0901 83
    0x41c0408050001981084041103444444c11641542004041142d0b1610903010f8a5942c86106400e04581501e00185030919204180c50b0401d078001d050780c44000090b6440b980c28004510301c1542c050080c41d04080b503007109001c0c10003414420405810018548240a090b644000d0326010501403240018850182c0c0003402e002404002c60121499455a00215140d4003c5800c411218080020303c5460550000071144c120b0328943c1e000c01042e40c1e1401d080380c588107000f1280c105a082500400c0e1103207000c2d18002e40c2105841c0205150800045140303141510780001103031010307000f1684900790742c2c002030342c294080043d0400080c5440e0840b0010403521841420f41111599080400c0441e142d9509407041c1d000948641034080e41c4070305140d589a082000200c850740b080c080020248011600683e0314264060062003245007150340d403002c1768110140b0143c00945d01d42d040740001102030a8070340141c80e84240141c3d9009503040c10ba509410040c201f000784582000310050690740b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 460319298 1250 460318048 460318051
    0x10b120c070615060e09010e09030a0825081023060331050f030405010203250f11130c0503060f0f0306010306050708010f08070b071a09010c0201140f 66
    0x44140c6540c4440078900032005141c1c080207807001041c08000801c1054015500240d5284201c030074070156a6292802a5404000c488039113943d0010321040c2c443e8ad006440c40f1f030300b002c49044940c50812804c40c100000860702043d0b900002c50750400d0003441d014007401e82000c0c0c07469511014205a01c1880d43c06204ca1410140b4041c1a00000145d6a84540f8007512017100005a500e086443c0c014041100800320040c140c3c0c2e10f005211140554507000402c5030110f235410307005542841560603044032002d45a0600c3c0f04e820480c0320b400c000040c02458080415886504140002490b0009004520003c11001403040b46010001a9801d1300003007603951041040701c1c0080410210310103d0b1021001d862266003621805001108202054111318407407000750741c0da1080c40c1c2c0d071f595402d0b13042c402900c1286280d80100c0d80a11203100b2400c0107200b81401150214030341c0e034103156440342c000f00407541c42441d40d40d03904c50307002aa0350a00640c503180040c000c8113411801c1c540202441c4400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 460320548 1250 460319298 460319311
    0x403030207060c0f0f050f0f0a0c05010e06040f06021c0c03080103020405060616060c2604080d02041206060503070501030c0801050f030a050a06020a09050d0b0417091c0209010b12 79
    0x11004400c020041c404420840d210342c1700c02d02040207100ca203401a56000e041c444102d00d8000e0244607189030f1000101d0402d03142e0000000b0740003a161400641d01072811095160b0424020040800d422880700c03100e2000303002c4c42d80280701c00040d03000040116074800100e02c082042e0305001201081e8030a42d00e5066076011100041d880d101c440000c2c181d44a03850483c04040302d03281044090100d140e0003e070001e8166150100103d00010645c400301c60009207a02c040000640460041a1207001601c103014144e440140f4040e00c9a00101c9c0415109504540c0c040d03d4000602c01030070f0500c03600004000a00741407041001c2c06c070011b0030b03408050191ba409400d070101003e02c1e0795020070801c900140c100c5c09464510541d810824041e5109050050110703410b000c0026043c201040e0301402550080c10305600d68a0344e035516001840540d00c04001c1c2c45050100044558403898080f450340c1d071200c03200c540c016582c03040c0b094401e0140d010040c400710a101179034080d10032109680d400032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 460321798 1250 460320548 460320557
    0x1f06032903030408070e0f0108030f0d0f02042d06031a19030c03030519080618060f030313030b0105191811030a0608011b0207230907020601060f0203040303020706 72
    0x46440012902e540100e600000031441002d000103009400c40284074052140700245600503078a40c204640d4a00c0340d0032400600030f80400a80056a170681d01503030606038a000b0251400e9960303c050306550380050354080c1a4462450301e400c0d40610250064020b00f000e00f0284a50034074010303140054014414114004c0410140704c04214003101041005941d02000701009540c0f242001082600540706203198003410b4103400e5949400342c001c061040000030515280c0e060781d04082c0220400180c641500203080303003c404038542d001e0001d00300e043d11b40015840007030f01d5800e00b0520000706a0100303000384c1c0da202999031203c4444041d403041c0e8104100d05d00b158079040500384000c2c103001000403442172000c0240214103400b900540c04403543c8100a021070081028400d1030103010043d80005a0f101c82020405c0c100a101000c041031000c80010502c52024404a450007504807040c000680181006100c132641000401500540c14402542440c0c2544c0d0040e540386a140950310071310 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 460323048 1250 460321798 460321871
    0x8060d0203120c0601051c05070315021e0d060608090309060c0709050103061a040507080f060409021309060c0809060a050c0d0216050706030209030c0d03020c06031f0603 75
    0x1900d0400c6240b00808a5078661551244482442900d403c428000c491040c00c01d10500d00c1e41d6008402100c6c50550004040d20301c01e8a959201c280300310a0340701c40b025280d000d1062400031100c2040c40014000c00d4011190790750318910782c0f401102d44680188040c404c4c003a0501001c0400003085d01d01c110001d9400580e1501800100b500c3c261039a80202440c40c189000841003062540242d14401300c001c003029429502d4030104420345d20704680b060001003400300090200d10745c00e9052504000007610004ea04d00103031300070542c0030070b9407a110708000b5211840e40d401c00500344038030002e02c4258a00f50105081c04080251509400303480703021040c0c0c564010901c084040030803100c030504026402c650f40c21071340c0d80350a0b40c1707080d00c1c034141c3c0c0c1030003070b11400114079001c0d00031125003403030050143c610034501e001005565031030794009408501c82c410004100b5102c82d001180503055a2200014200d4140001810000c450300036800305420540e4015000c1500b044030041040070a8502004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 460324298 1250 460323048 460323053
    0xc0b07110f01020f0f0a03090e160e040b040c09031106030621011b020d032a080903070b1e130b010e150a26010b0303090108071814030d0f08060d 64
    0xc0032100c90002800d409504408180500005032041020341f0a4036034000041c0d80d0b404041c3c03111001c41e55042005c907140384241000c2c1c482c0b940b00000b900c00800001e05016514045000c4800030328403c00410032100040c001d00a1400058078071b00400c0340c503a499031600710302091200d05100c0c0c980d00000040c1040d081a01829003004040c40c06501007030b4a0754011181c025aa00040000240031a02e0501c5600201080b4100da04644201c05005080922020030403140d0780001403040350240800e2120b20006072601041e54011000034965900c41c3d003280c40c00c40c81c08503001d40610095102c2d0810140029a20707800700d030458404e1590341c01a80e0b2510603008583d1031400e00e26500003580d0501040403c0070f41c0b4410300c0908450b03040010280391200c89400c07074410740802a17141d8028040307020719611481c5030642c0081140791034900c02800800500036054950046000807440071a42103003400e04000e1942c0e80d0000b4034104044800c94040a882c054010303044034010b00161002109 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 460325548 1250 460324298 460324303
    0x91503050c100e12191a100e1602010209040f060303390807020301050c0d060e0c220b0d090b280203061210060611060403050d09030e06070b040c0b07110f0102 70
    0x103d0607024030301500c0120081c0351580100c00c0b46d80d04580b0b406c045038045886038060400716405d58060304070b079041c1e586031106031443e0440c00d45c000300d00710b42d000c10107403003039803614001c140c0d88806400000c00c21a055103005041d152040c85041c155040c4020940310214110607800241d0510442d19a011010f80c1408030991050800181d019801d00c4180b0422804003402400d41d5406408100401a00d0740c0910700d92400503215014441d03030500c0101c00401825183c00c1422400380c0c0003c0701146d503216185200d0704060001c0d124280c3d901d010324248690450015401111104580042c0000420000d0348a617140107130a4103c0d030102c0042d800b526040c6241d0303100c0302420104c1700da0050b0b50724a440549041d008082c000b0b119000010307a18030000508902556164076154200290403110f40020322428400b0b404003c10710a80540c03640702c8070014003002d8055845901c1c289000d040000e00b1003101c0d8060040f4040411424020864600d000d10069004540e080103a49913140100c0c0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 460326798 1250 460325548 460325563
    0x1060b0a0c020f040e161806180b0d30030b061b03090d081e0a08040327032a0807030605061f081914130309091503050c100e12 56
    0x174600ca03c0107524511b0601c90b0001d81103c084180381c5040f21103013183c030300645104e44640369200910040501003107580d90044040c0010250260824190603211141c212408407442c072042084801d507121043c51243c0d64019960403400d042c4007030656000030401d640f10340c035030240800c1c0d84c0e110a440340040a00490700420801000e00e03404514509003000e00785c0c0141102c606411450300d0780e00d58661b641042d541113004a4490b06210f64840d03c05031085c41c1e901105a03914021580301c42c1709080e6625154000e50301030b490b8484494410141c614410b8040070040d000003560340010801450000769140a403070f480709000ca041d442e640301040c6041000d4004007046480884140e0200d50300000b010f10805980c481c90b020b040e02001034030100e81d00040d44012280010f40085c01c40705043d25a491010721902e0304180040e61544454111560394031440b0481600c0103081040c00380801110040103c202c40d00c06d090b51412102901000903c80c4440c090303880d2842032120040e060180c036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 460328048 1250 460326798 460326821
    0x90b090601200105010f0806091204180b091005040e070f06030e0c030a030e0a0e01030206030408160c03110310051909030207090608012a0e120106031b0801060b0a0c020f04 76
    0x4d104a503100c0301c2480d15207400340640c880e188500300026140000000f04070244440410301d407072921703007000803148040c002c845c2159400f680b84d13040d83c641307078403420b2407070348510001c0c60084a42400e01c4100419100d408110700040d42c0403120030301c00040c1c00c404000460301c96090007d071102c0c4000c513250400c200e0603140d550502a800002e818035810181c0ca05040504440c00034400e921001076105407003080c040030b5040b950a000003000240aa00145148641d40341d59070025403440c0c0c0c0b84501d115003034008032080c608005071210181810810306803480117180082c812481c101d900d40b44500e411440c65134205480c3c001c180140f42c000d20000000d0481d080041c00034544854415029110b1440c441080c00280e030b11000c0c004820404850342d03000300e6510560303904011820440001040109800555661013000001403005e91030116082c40c11441800b04501e000c40e1a421200b25520502803200300f0042503480990014502032069812641d11303041400d29000700e0003e00781e5842300e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 460329298 1250 460328048 460328051
    0x503070311190306050105070302030d0216060e01090201080a0e0a020d02060c061609170606011206150c060c050c071e0e0a0e07051f08041406070810090b0906012001 73
    0x410b0812800600000c0310b01d0141d02e040c816542e07180300444261050580180058105200d4440c031038185800410b0407052a4200404020507034484404031910000c00640580d5650030103404c43d42c01820b074940c450390703400042110182d009022a180c0b409000c00901c9005030080d06021940c0b6241590201c24001080340c00c0351070460010080706028003034000101d003403508001102c5031034118508040f50303038001030710311070b00d40f4401507903007582d00e440da40c0c80c1903122040801c402058003000e2884d40301039a203900c54103031141440700442e0012140302c01002800c01603502c110034000b844c1011207521403a03003288042009000341c00015150805a8042c00b07a40a0140d41c030303082c1e003000c0940c51070001070b101d0071a40d075000c01400740c1031525046c5400c50007900300704840d03005d40c03912a1300074001c0a000c2e1100e80080851400c00030202ca00b00040f0390302a00303029500e030301c504420025250701481044410300310800034200c407000800c8181000001501002d4038403101d01d00080a40d0355100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 460330548 1250 460329298 460329307
    0x907093b0f15032a0a031b030309050901080307080a050c010203010609030218070e0f180406020307080f04080304020d0f0b0c0d0e01060e010302040b0d0f0b0a0c031b0503070311 78
    0x40303244210000341c0b142c0100100741c90a40041e8500481d03042d020407a000c0e00c2203101014500903c100000044031640c3c4111004070001c00300d40c100840c002d144010305c44894003107040d072a014008035620b4200601410740e580040c400d25800000f281c20641e0040810780e205c01840e0000c4440d4803890200005650010000040c1d079a003180d1894241c901c01c8410b403c0341004043c00c90044001200c09100180002071048054280380c007900d204144040c040b02c1c0d0900c0c8010480628190a9034101c42e050380c00000c200350709510081a0360021201c0d030520a1504154480402c1c6000c041d0011b44600c0306034840c1801c200800710402c00155200c00c80317240c1881d200d414040c0d01d400807410303c1320b19428a2503d401141d410321070481950007052003c02540d086409100080200300c1c00541c201c6190306080d40860210000e081c44140f00b140207aa031807820048202c29031310016404010305040c514880c0c0c1d40041405c9607204801d040c50840e071281d03102501180504410940006c03103640c00203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 460331798 1250 460330548 460330561
    0x3060504050a1b060e10020607110f1b040b030703032715030e010b0a03050604120c0b090a060b0a0b1e04120501020306030d0c0f080c0c0901080a020907093b 69
    0x1c07204007118096155498007000c00705c02d10010000740e004070300042c3c20070400101c10701d000d60040703022140303034404840d1412451140d0900c1e16903c00200600400c0140f032030445071a050003019040103003640509441131841d03401800504402141d110204a0a00980750354040031030000001c00e80f0305424898042c3c803d0b00034000340b500140e140560350911804001c0c03800c00c179600e8821070340c1c494001d051568958031550400341d1111314913401c100c0d00c01c60001c0402c140580b20740c050700d80c02d800b5020900092030010b04807024400100e02408507420100008403158096991408516032010341c41c981c002c20140c41803245401a500709110f008000c01480750541c080c51003620290b040b9030311321040481c199081411a2001801108207051034000142c404000d0140015280300325151014020002100c101090308100a039500811800302907151460070070303401c8240e90030041442c034144015004000306161341c3e03000c01c8400314215480350000b0f54a03c400100c026840c3c080a0030101e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 460333048 1250 460331798 460331843
    0x61d060a0203151e030727020c010e070f0e09060f060108040f08041d180c01050a05040503070b0327190c0918020909010501050637021e010e0703060504050a 69
    0x80005d0181c07041e44030100e419480d80140c410190203a0400903440307444007010f84040d40c002c225030486035484180c0e80d04003650410140001d840c010341180c0c0724600309540c00040d09030040c45d602041c0e211005000c581e05018049580000003880c1050080e0744034144080360b008405001003908a00180015045e8280190b000720444070411502c000d03210b00b0044100005903010500f001c0c0c202c40c01c0b040c0b2a41c06031000304169074084c10b0840c1800e503030b040000d0a1407082c3c1d0044135480342c00410801012200100f03150010a0035040001c29041898059602c110300f07a05514101c501c540c0040c14008000300d20300c01401d0207841449200c01c008140031040b0f08189041b0301654020010880b051410b0203010f0580f000500050b007003a5050b40c1041d40c9480c1e42e0206548010420210b555802160080c0410b51080b0340091100b401e0350710003503940e0402801c1da90ba180c4d140c1900400c0e441c0000c1120821240c11400200311a155800c16500304642c0c0300c0002d0150761018101c1d107015070701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 460334298 1250 460333048 460333099
    0xc020a0f030f020d1d040506150703021e1915060308030924070206040602091507111314010905280e06010f030f140106050301090609061d060a020315 66
    0x6a030b09403034800d0b0f08030b0744c151402c0091030401040904c8110710400242400d501c00c5030300c40300040010b82c03051080d968205055110803c01d80c01a08000c402c850000c85507a90b0190230282c200080c0081e405486a0120401c800d8070f006084001c0203403007035807900703894010401460304001145d90303038148501031076583d62001460150300b1158640c18119810756410707540c85228240c000d40810350343d680e240002540096203c550000c0d450141d5003030180060007038040c2500c1000ca0400d1001c1e841d0401c804248900ca23007070f0605042c04010364584400b03900c41411070f01100d50102c0c8540303e0742d00c0882801c20552a414130350309440b410070459980d50300501c1c102e840d0881511352598072603043c1480a8901d000c0a40401c0d82041c4130000601d903034070541d0700110b403c07000003040ea4482c40084d0a4540351007056803280d85070344114041c81803d102d540c0c10142100d00c1a4054495410a103071140001410049030f9a4040300140700721029403060104c2180007031440c02d003055000c0848912500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 460335548 1250 460334298 460334327
    0x81f06020c0a0b040f06050c0102120708040c050613060302070501090203011503420b041505090606030708040b0405150106172802090105071e0308090109030e01030c020a0f03 77
    0x2e08000005200440310121404c0c1c5400c4007500c802c40741031a00954a690001c400d2074410b66017000401c007100f08500609000c0e555a0750340080341d08081c244940c03002640d40085124540810002e00098180100b02013201c100341009038490b003203030510318014000c45070069015420700c41e5100300002000a16019a8030401d8615036007803900c504803a1100303100401c1d01c51000058040d164282240d401d00e600006860008190740115101040c00d132581c409417181c940f10000c900380041e240400ca090392140c0251825821803130003040052501c0c00292002c0e00f60400080450107011050083d12078090101e0300242480d65240402802c550544100001d03041c5007001041400c2c2219004080c1c030200b0184003e900b0300d080c0d031014006d5204510641c18444200410400500e030701070502c42418080102c0189403586040103022044000c0c42d144a5903d0070310060002038000e482c282c030a41003807030f00050744100e4403401c0c0e14041d0748030009040851040e00800c10581d0041943d4035801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 460336798 1250 460335548 460335559
    0x10b090111010203102d0f050102120f030a020708071703160f020c1e030712120c080d11040504150807210b0c1606060e06060f0a081f06020c 62
    0x8041210242c00c0340025a4125204842e040041203090280d000c96124005003080e05004504040b82c03202c980701030b0390301240d04185024810001ca68061040012100000000303915100d504c58440b890342c03000030b010740c80103a400f007001c2c014000513405a50f2000e9014401e042d0f401c01201660345a604102c0790320028040941040d01180d1003140f41884a00642c1c0050400b10307101000c0000360055400600144241c1c5218a056980c080000350018114640c09001c1214241030081c124250107284809005007059110700040788001210454035043c01c0c00a00000101c4407040703a40f18641c803095102c3d0520b54111a0f0105034820300c411146003104584c81503a0350341c03c40d41005602c80c0d1000c1c0411001c03048501042c0f50300841580810032000d0705140c07550b020001040c0c1c015030403042e542280d941c41c05000c48072070090b8840d008002251018100700b03070100486440c1c4128664881001004004603050310307681c141c00102c41c640a8081c0c66040d0b210303603000f9075401e4006035140c440c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 460338048 1250 460336798 460336817
    0x71a13120305090f0a08190201020f1b0312030622020403060c1701290c0106120503191b0204090302070315090b0f0c07030f020304050301060b0c010e070803190e030303010b0901 78
    0x180340404d0303805c0c01c440401c80500489076198001a0283c0c0403100300f82e05500490a0b1550505010f0100070001c1c446000042d0941105406041c680035045271400642541003050240550340d90aa4043c6a4030424420381002c940100c030340e01070700a0707500041c0140c0c200000c0201058001600c00002c5402496106050fa0382d072481c10850000405084988590407541c0c0f440c3c08038241c01842c11035443c030000300e1442e5a40840e000c0401241c0301c1542d2a82000c1810302c5500d0b0030300030011020360a4600000350300355091071031204034030314035000b845150364141120415000f8080720005540001c0d030251140c03034044070000500740700d800032214094941d000401d1207444001783c500030011a80300a050044070380d01039500039046880041544824000014551303024028000030f41501608546c40b00000c070009400c1d902100f0354001d00f03810a40301408021000002d40301100c43c1003a030500b040c000140e0946007140420319854041c0400000441c01442d681c00502d20ba441c00e9030ac500f01d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 460339298 1250 460338048 460338079
    0x702100c0c05010e030c03030d2307201507020c010f0302070c05101e03090c141e121e0c01051204060c050c01151403071a1312030509 59
    0x200c00080e0001804081d1150080c4140d5101d86115420503001134211031440f0205000245182c12100c10000c0040d00c03a000700400c000c0b000340106142d44040d824400318142413002602240118070075014004000c0d400bc0650751040041e20740301040c01014603c1c604050038000d4603211040b075040d005c12030408910745014400d200701c410440e006140d28410b41d00b03001c10818500c12021010381088103050400d151080a0001c08a080415441c009007038540e41c40c10281313910707907980701c2a2004071003015480c003611a0030321418030041c040c0403d0b90960301d0800185c0c1c1440c00b50201103080c421504a0b40c0000f1800342001201c2e038111003200c2c482c65184004550301e2059000145c0b447d009500410006055900140121611802c0083c105141c22100908582e6081c500c3c80103030b01100070800c404c4080120100c2c1da594160081d2140900b0a05c03276540140285a000416060000300d440c0b59002c000500000380925580e0000303124400e040081c11074020010440c4280110840a041c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 460340548 1250 460339298 460339307
    0x1c031205100501021c03060503030d023610090f091e110f0f040509160f0e0f09150a180f0207020d060c030f0c031406040608070e070221070210 63
    0x40ba0300590003001110400c1d21301407010300600c4881401e05444400c045000c0d9001d0000d480e001c02845030042e2210320f40c000002c2c543c210209240c00b500c070100e520440c480010800401c1440302502c12101080385258115a540180c0c0d02c0b00180c80c0e54400045100d01440e00304880d10300342e4941349694000860032110403030351180c6444200b5001001003440007000751010741360720494010041d0800e81d40740046265900102c4103506410201030404c141d0715081145003440000382c3c80c104e4041608a004120042c0502d000c4a11903100c100000e0301204800b509a00e40240c040e0140040301c0c0e49483c0c102c40c203003520901c02400d03801c1151010600c0164801e031642250002c012219100454440b0780007400c00a2079801051744038020410030b0304480c0142c8091401581c1c0000f089442100020110380c0042c122910850400030200802c8100140c00e1040e141195091180d0340c451030740a9161040000540d0085036004034001300c80078401c0050189103000740d0310401650700c603c10484 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 460341798 1250 460340548 460340581
    0x220c03061509060c0516060c020306090604030905040b130f0605010807050c0d110a12050309100e0a11061303050a1505040b070f02070801110409060b0a14091c031205 73
    0x1000250b50480801c0840d10960100101502035070540e08507580c8007a400e0100d01c2c1c260441000f0030b180089003000c5090070454030350300040400c040d100505107035400400424041c41403d11582d21038890041c15a100100700303a0098080030300304640b0403800c491a010344954407510740030078241d40008124078022401c8070400c00c1540060a6002d0141c1c006403620250240c41002900c118460302d0002081040c10303114181541d160303103881c6d140011400340b41c40c0203440c44071283d6041038881422b205000801c0e1000650143c107042801c1071071b4011030214060a040c10580b50003041000040c0301020076129001d03400b030f000c0c0044040100580f101a40d00964000301900c109100142d00350788129076000b074101440c070543d40c210340d82d16105825900740d103235008000c034000101008410001d00c90f0380003d00741030501e142400500f0401404031040c0360a00404c90800003400152030b6240c0308070741043e14214040b44480e036040d06000b040c0c036405103090a8141e10300030100e80d81a07032048002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 460343048 1250 460341798 460341839
    0x31905130b130f14010510060203040b07200d140d050c1b15070c2301080103030507081e0a14031b090402040f060807020c01081501050702220c0306 65
    0xc42d1900c40385060041603095095400c0c450305004400040c0707519008031a44d04203007002040c3e9090184030916445100e0f442030082d0341c4204010441100c0c400d094804c0190002848840150b015100e801d100c0d01c1c4070b50081c4e115802c41c2c13170142009845030394a0114007020b000c503140c00300324a400b40c50610846480280c150f0000304403030740c008404191448025030103005d18200e1010f0206181c1c4039005175008891100c010034040c00005140c03048240c148041c1d10307080305100550000a0311f40c020600002e810058000f840100344002ca10840b800280d440310628a030038000c2c0c03200b0846070000492100000c8a00302c0505964403a85c2c103a81c0110404070300200c01009242d03003088540e0040300895002038080c480002c40ca0b5a03c40c43c003000b00929194603940d441e140100a0030304107402079007410f00000b5418016a481c0e0220080aa20000c0c2011030ba03460440c00042c4008000e951003546645d20602066644841600231090301c01e66903d0601c5103681724055014440170900302c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 460344298 1250 460343048 460343063
    0x3150f0b090f04150509150c0405060403230312070e0901030c0b090f1c0309090606080708070e040603030f091a070b1e0405061008011b030209010306080303190513 72
    0x41129104408802c9410a02c00e852410010313007000880c1043e02d00c01c8603801915007003403541044110402c107485901030f4002c035072140780c113050030006481e038080c5003c0a02402404a0740c15108440b10114203651206002100d85441d4148003e00380f0b4101203581400182080000c020142006940f050580b5840005803001905022400401d0780006160741d9110051800341c541780c1d00d6000b8805841c48030305940a403160030314103010700b818205501c5800a0b500c0c00c0c00c00c0002c079a0100007a500001c05241110454a41e850708880038441c0403250765100789461400010550801400c3c0360112281d101d81c91000c4d84c569600140c9564202a41d40310202080084001140e80602c968070038007202d400e944081c4142e1201c4074801c81120115065801041402401c4500304c40c500010034051000f03100f1801c040c80341d498500d0201c841407041c0350300070a2400c9a0b038007030740050f40034160201c00c407600da29000400748030042850f0700c0c1907803552034907000c100d0428190914240701e40d0032888 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 460345548 1250 460344298 460344301
    0x40c0504050702101103060405060330070203010c1e02071d040c030b010b0309061005100c02150a05280f1b0605010e161d0607080904050103150f0b09 66
    0x1804058a0700070102000c50190104050b0414458829001d201400300b0301d5035160703e040c0d0184011100701a1090b80f19501034500b1800002030030001c00c400818030400100d10544603070700888540200b810003035041d4204085240341c00c4c0c3c80700d00b14104c800c6c000c1920780105981c0600741d07240c101c240105c4100d080e1240340c074024145400445908188505007401800390349845001a500c001e030080886468004180001c020b000c000301e9400070b501326158000e0500d0300001840508070034814030700344411000e0203020342da10100400c29500ca0081155603072045400010141c0e40320803003a003032540c08100c2c18189442054500d140ca011140c4034070400c0100e02e1026036008030903546680c0715a61291030007002500c180956030003405860081d00707403402c110b0310300005682c0140c8240200318000048003c40140360403640c00303580054a1a59480e05582440940c0b40b1802c10b1142c0c0050400b0000070411003220002d0a80704960074041284070401d0710204140d0340000e0700c2c25449007a050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 460346798 1250 460345548 460345559
    0x50a050711030304090e06010f05090105100806210c031905030a081b0432091504180c06020706050a050417150c0306030c0109120602090a0f0f03060e06040c 69
    0x20814503001100070100c3c1e080c1940d40030400155268002070070300340d420030001042140038401c0d48070040c0c1012a40078800b58102404142c81051445130070082016500110346d0710f032034031480390555180714414104a4860405c00c0b41d030f00d800b03000b8464040d01c101c03800519170030b66020f007102c1003645c0140514941030f1300b504c0031942d907c00a000d03644208a80f080c02480c16130f8010003000200408050f0800f4400112400c1d941c1c001d0866000407108403170303c82600380e0b64480c00c00b40d41c85442480720381c100c0c1d103031400420000c04040034004c020810600075041440143c80d500f00c1250941e43c00c03911802d8607607030200c2e800c0c000c003800c00e4003185007408140b2800c000303900d075031107442060710440e0350030780c01e07162419915001610305540c00d81000041c010306080501519040c1c100c02e0130004445803911051410001410402078000c82d0701203a0540c4595585c64410000c007040800e156180e0b4480380b610540c4000c0d0b200c1210101c3ca42410035200d010003044143c480c03034105c0c00141b030451600 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 460348048 1250 460346798 460346813
    0xc011205040f0b071e1806030b0901030303050c070501020309030405030105090a0b270105130201030c1b1e170307021b10080a0f020f070b070801051f2102030a0c050a0507 75
    0x5000b08085c0040c0c04440c074254812624444009003039030b503034030440710a2000e110305402c07000d4220038205401c05020940d01c2c0c461b2510036045940c10300c0d0008903940e80d6034191500d0b01668070018000e500000c14800c80c1540040500290b42c0101c008000c1a2512062b807651448001c0c4001d00d5220f00746c0010b0001503980c0d0b80c1e01d0348044020000308092800350740c0c40e42101c8084690017030003035285241070103650f454442c4040812150503e034000610b0301d0036191507404811001040011185114499445d43e03059001c0d5003940b04c540e0115892450350350120540084406400501c1075800c2c811a44100448401d201d10002c0d0500c102c001c5001e40446034044001e003140380f03142d180e00ae8840c804c10284010002d1a8a422046440d04028136200e02c1601c8081c0090302000114401032116030385081d6038000042490000c2c4000d602c88260545941480a420301d5a00c100007840c1c01c800c600b0358000718071403400c401c400c108243e82400255001e0140031103400c0040d000303009040004091 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 460349298 1250 460348048 460348051
    0x90a0b090112050723040f140312030c0a03050604060f03080c0c0a060e01030609201c1a030d14030c16021504060210110a030b041401080c011205040f0b 67
    0x1803408014000302c03004458241c035410b0780d0707000c001211403002a0b552a58100e40c0d007408140d1101403881c0c2460080d080c0c6446405014802500c44d002041c0c1c002030750100591600c0913a07102040c0c1d128a08004942e0790742e04240107038030100c0d007024001921440c091140b03006032000b40c04101e241504680300d29002d908410b070015050300c41c0d10104903082d503c4030441c00040c420380d940c100046e904540010160344656120044050802400e00340f100201c500c00035060010403481c2c1d440e80c150840c40d60580950004034083e05181201601641c101031021b80d00c901020b40c04c45a12159980f0100e601c40c07007890300c1c40c0ca212414004181d45840350320092110440c4005400000310751070700000d0781c00031034403c2001d10480014003000b902d0703010700414144180904040003511103100100308140300c0c80035140c00301582d134080074035140d07620b90080e58000c921000c001c0082d07840307000380741e070724451504070760701044002e0b41d04410250b041c001c141c0300b80e9102000550f031450035980d20401040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 460350548 1250 460349298 460349317
    0x307080a050c01050921092107320916180512030307020d08010b03040b04210903050606270403030912090501091406071b050a090e0c06090a0b 63
    0x90400c4a04201d0809000b44d90103107944001a00080c0c0b649490a110240d41140042c5d041c1d10070b0040701c0b43d50ba1442c2e0303540e038200fa5003c2c4590703942000c00400d50400455401440300410000080503140d0f00550500244c24130711010340611400080410054801c200e6903440f40703108500400325114840c2c002da082c00c0b110803818040301078a400003d012880a0140700101e5400802003000c1c841d410032201d01200b0f202d0908001550402e540510517105c0100040d090001d1940483d01b00404004071000540075040380e60350903c100320004110305003500c015503403440b0300004500c0c6882c2130000d000b5500d12203e210026181e041d80b50103a41880208140c0505686c0c030750036404285500f90b04440600030382e49200805041c41c001424a00d21904840064401c22100c840207443d0b66080f602c407160080c01ea4081c80f0300e21101103c2c0c00750250462600580d500800003020300d00c1e500080b158000c6c040a5821041644c0c1c1406503030b006043d60302e87e01c002c04170410098505008002d049142 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 460351798 1250 460350548 460350557
    0x60302072012030403030203070b0f04080d0e0a020d081207092702040b0318010e070317073806040e0316060209040504080903010b040c0e15040e090705120a050307080a 74
    0x1d0b02c001116080d50480e510980146e000000c201042000c5400b18030b1f8002e4140208410030705050f181ca071042d0040c504440a482c2d034030f60030300440e0901000b0391505c03d9402007568005000380d10740401c0c0c03500106e407001030190f0701c2008207010f5401401c0c808261038407500e0351038080c8680074450480f0502c206164200d0f903030802010a031090440011031250b110081c026030105140c0140e42d013100c000c00100001908070305030500003d200480c21484008a05901549611880c181400c1001140c0040e000c4980c40340e0840340c00101150003142074910104100c890b9a0ba00820300083e9550141c04a200f90020000c06400d001c012490524481c090440103040c804510081802c40c1c10658003600c0c6403001240b08000351a090003012062041610f0900c101c0b800500003415a81c2c1299845101d0040740740074680b1140c41c0001e0b100241741201295290b42070244280e03458900038020381c1d00903450300590484500c00017800400c44c5a002e0011403500801c0e44503000c4c0c03034000059607400c10 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 460353048 1250 460351798 460351819
    0x130504170a050f13080f0601050303070204020f1b011b0e100302071407031b1e0e0c0f120103050706050403031706010c0f050c01080a06031728020c0a0603020720 71
    0x7100c81d80252031340c8109400c003c540113003841105403411054403045c8802e03a0101c00103205584010040e10000c603419580903850f4014410049664040d0813103400b500c29606080c1510072405402518000c00706003c0c00c07203c1d05000c0c004440c40807210a4058000e00c108840c043e00724400e600501d0403d000301c0b048403003405071000c11400d0418550059589850711003100c9103214500704100003c1c08003122038003001d840c003000721036440d001e4411644204001000641d09283c0f0302e00321400c0b0b1856030002665098804d5840070380c481d00380000c0c0d6043c40b1380e090104085010300200d405a0750143c0f2054004d9440500000049400626180c10030107400009000102043d4018032503074132074009040004442c0e000107141240007403500c1da0b40e60a0601c1000030039041c0386884001d00000c40850350b50b1106020f032020161000d400078084881d42020014016408140d0380303041c0e40c0803241142800d46d80c000072416401280409094040c0b009060768255024124100403460040c0400804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 460354298 1250 460353048 460353067
    0x102070b030c04030506180105010e0702420a060503190620280513121a0903070507061404090b01020a02030d030c031b21090b040c05130504170a05 65
    0x2028020b03a40006180f04001f0380d190080d07800e0161307a0240a814203c2c90b03140c5013400d0003d54490403500b0400384c2c4584040030744000d07030000c4901d4040295101e0a032030401c004101c2c000d02d440080b02c1071282d0b20b182817008034003844c0102d00701c40005044070b00c080300032000752551001000c4040c251a072403440d20344615040c409480180c02003103099444481924000c1c030001c030340035004d14a42d0041240400035401c1c114400101c86042d50b00c88134503041c0da031000b40b802c2c4068040c554811009c609480041001c0703000d0010003009080d1003101640c1c841e0713540d4001510082c602e40f42410304003000780004e0059980990004510740c20500c120340e1078000580100e0300b40010754000d580000c0c0c40319032042c4444c0d01401a503400014900e804030240c130b0302c2d01e0000c20080f0000206d080c0f44040300b4003508075001a0b0003011007103030000c0d9a242d003401c2c20f280140810f8502e1181c00d00441e4a40400d4030b00d010b2600c00c3c00e00c170710341100300216606a43c80b100042e41c0d002e00b032210300340b01041c0300b90f00c1d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 460355548 1250 460354298 460354303
    0x11040810151a190f081509010b0a021509010e0721080c0c3c101b060c030605041404050a0b1e01120506241306030602070f02011d0102070b030c040305 66
    0x748503140d04d42620394188510010120a001000480302c0b034070b003d15054031901c5d9801120f0440d5400541d8a483e10400e013000c03401c064a0350125415224403000740016030f801035210181034440d1100700c60000e07035a030b610a00c1c1000350200e2400b65040118a00000c24000c00003010010500d03c140c07010001d029001039002045580d071160122854180a06500400e480a0078201709a220042c10b5003000c40000e2030903008018101e04000c03103080c08158240d00300507541c00b002e07400b51052114008a4070b0060003844540320b0580304505200c6415484082c000310203002d642c001c000b60005103400d440d482c0d140078001e8072508607002c5003e03115600c180c0c103129190180035441c0c1510510131150400f940f070200040c1000c47d1000d41070010380200c507181180d20011030f01c10366a8805550000f51104002c2c505540041c15080c00080c0c85002c01416003105401c643c401d803030f181d0440d000f90498200c0c12240c403c2d0300d030260b801050180103021500007d1680304850f190641d1405440ba07443d01d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 460356798 1250 460355548 460355587
    0xb0a110a060902100309080904090f080f030a0f09030c1103031308010506040e0309090112080d0f020a11070506090105090604030c0303020d0e041401030b06031011040810151a 77
    0x2203005036158014011461318804041c4600551700e01070098410940303a03901c1c00d03c584911f0750b20880d03861406c07104000072051841b1019400c0b000c45503d40801c85102c081b0b0364000c0381d040c100689891705500f990035861203441c808981581c2c501400c80300c1a07403600b005c001a5000203a1622041c84058084400c1c01841e40103004410000300316824841c0130300c4103503a8074944066103a0010300c1a0000d40d00d80c07803052411102d110b1143c1d4040e00704c40c140180c0c180f02d0100d05d11810390a0640300300c0703c1d0b9540d40051509840c0380d0b551409440c9a81f18054a811781400380a0b40300b00700704a11f40c2c40351704c164040c2c0750401004112610301a0f80c0d6541d420003901562080b00540c00c945004400c458020b0080d400c0001d082d01c0c103004441103550042080d0700140801040f000702c800c04580507482c200a0414441405e0004003c8a0207d41080c85503030024402d2002c1c3c2d10452a50350f090341c03c9805140c00221850000081a50500d02002d09180705516014043d5038107000c20346c0c2c0d6035041c0e1280c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 460358048 1250 460356798 460356803
    0x120207060e0d050d060b040e13030905210d0e06032806030c050126060409030e03100e120c060f06060d02030c2703060c030915040c061106010f0b0a110a 67
    0x1039580f44000c1d5113000940d102540824413542d010300003040078290514080b0303130110901201035004201494155a011601d4005541009072215982a140808020294161601c0c6c003258a418020b80c0c080351907a80c0b0307003c1a508007505001140014500000c1000c5079401c150041c1194441f60188070100c0f42c196209541c40101e028003000031307580007101d00000c440c19107101d65068a00c010721800d01c09000d00202d02a079540e02540091502c5038200081e4003800800351401d810056032903101030b18407202003411602424a9001d841215a03003112064081c04004d8441a0358541c00107040031802803031960022403c1100b000d1421082c4000d52046c003201e501c00c2d03100c04000903451a10f45094103102468001c41301150700365500050407642c000c241c1c03900643d45e5982e035902c40d03082440d82c03122003c814104500344800c002040d40c0c01015600f9659481e8910f0100d58405541c4603409c2c86038103001c100040d01031150840d8140108000750311414032000401d0146c41d454034285042c3d105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 460359298 1250 460358048 460358057
    0x1109150316090510080a02150906030f100510270308030a060e0a0903020309090a020405130203090c0901050d1502040f15020d020c0a06080406061a0a09060f120207060e0d 75
    0x34402c0340d08502c61260040d034041c010341c402c1030a152041d07965000e0000041c0c820800c0a5449513000d280104a0f22400d2016205a4803410103003c042c00440095558100c3d6600c545404a26401e214280b0800c009480d0740f881004046003200c903220589420048042401000005c03001c01c2c00d0400843c00340d403034503c2c0014602d1800c40702100d02c80c0044c3c0000310b014207040344800440e034000282e8101a80c1107600c00ea25441d1444020000d20079139001c4c64220b0302001c0200c1c1200c14035400f65105240d0300090718a0844100100300040c04240215a4024442d5500d40f021501d0994040700504280a0052a103a04c80845660011141d441034071000c14801c045059245d0600400c14142075500042c80c1d9003107000000b80103284180103203420455006e00080c1840b1464102c5c0008250501d00c11686da505000c07803100c1a4402c0d00482c0c0402c503044000500d55100d00c0800d040381a0701c0d609e804c0000c24968081c00690f000c83c605803490303600d44105403008001400102c82a2840d40c0b103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 460360548 1250 460359298 460359343
    0xf030d05210705220302030f07030c171507030225020f0d111207050a0902041d01060e040207050a120207061115072003070f0204110711091503 63
    0x807100c040c480c112014052000400c24001c1090300300e41641c83d510f10b0f4844240040c690034441000038956540069030512030300c1c001001c080030100d624001e881c092030028011540b2584000b20040600605030340d5540075201c49a440703248070803c0d541054151034090710340b008540030029801204001160600140320104d01185000460501c40d0380d020f07103101500c140c3c070f03444403100d9458802049026110b010300180318590148020380c003600d4028610000c40362600f002400a410900031586090410450100c035441c002d807105048031103550340c10160300030780c00921000e5040f2400490b818402d12403200c5c001502c0001c452074200d4680e006221076480d1400081011030412061490b80c2c03c013040d5002c1c000c000848150b40100d140c101074001c140142c100701c2041c00810410f1441e030001141d0340d403c0005c8081150300c3c45000700c4051000b01c02000c02e140d440e01c10008020b200b00300040030712507c0d041451005a110b401600c40d003c46581c034401182c10b0518070500304448100c01031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 460361798 1250 460360548 460360567
    0xd0506040501090e0709051902040e0610050c1f060305010c020d0807030e0c0f031f0207020f01360506040902130e0408030a09060f02070302240618060f030d05 70
    0x1249a0040502c030703000b409241002e1801580710b80c894000c07514401e0b120000142d981012003501042c0c0c0c5008c10085507100da0f40c850010440c8001ea55030303442035080c006070290302e920803020340d0380d00341c520741c003a01e400407650000842c40100e50190701c50341c039102c442c0040452001e11400e410858250044c001001d820b01c4d004001c00f43c0180328605041c9080c081c041c551400140301c0403070440035580c0740c80280b580c0001a141c24140c10310042e110320304006c04140542c0b540c014001c09442078480d000303410382000041d0382507881d6107280d036040004c0700307041c41440007c07403207081c046c01d00f80082c80348080e181c40101d2802d42c0240c000200b0180c0005886260089107a0080018512803c6e00c416a0500e59204001880042c0014002c56122010401408a150f01c081051109180b04555801451801a4036001c3e0200f180c103100764443c2c0d00741d00300c00c05910140c2c8524402044410212955008040b0084014000d50341003140c140422440b52801c00c542d040061403620b0f850b0f103662441 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 460363048 1250 460361798 460361801
    0xa0f0608060d24140c070602071a070c05060c030c1225030b1906051207030f1401150906080601030c020f01050f04050d0f0e01050901030b2e02060105030307030f090b0d050604 77
    0x1c150310340c01e00480308103d170700301c0300c84269903142da0301c5000503982d20000e0401e98071100200090b840038555032024002d030f190300002d81041c460304c40c13820b507102540e500021070b005000840e960041c019003040a000e45600d0621015407050b8034100b51000000901d200e03282d80040440801c02103556000e208404e8540301c00c1c0403006443c04a07811008a0070400000c0c16400780d02140300b0f00c1a520408258814041d420015150070325810401041140c8460114100000c5c4200e04d81c2002180b02e03d03000520600b110b10607601982c413401d0310340d04c880004400030f06921040b0400c41c0208403040480c0c0100f0701929000b400f0403030450303001d41080c0c00d044e030811924941e1482882414078a142409030810041d0318000340c2400c20540310b13001200180c01501000007080e038000500c5041c01c191201104200a40d1030b60100072980d11200c026080e65200028003d0583c554001e110920001340300708444841b03074007145040804e0079944d03285d409058100e1604582c1c456113a0701040200d042c113 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 460364298 1250 460363048 460363061
    0xf0b01090b04081213090e0a060b030c0904080d091e050f060708040209040f02060a11070501020a0812070e10020307060522020d26070507050a0f0608060d24 69
    0x303500c0c00502d803a141403407480d0b40b600031190104101001144120b80403060361074407001000700c0700b010f100a59020b0780c001d8660100010456007103103001d40b0151a8200014401c4282c00090b00c4a806903c0b141c5030140583c008403503c1c0103182d115600b820000785e08401010003010180740b003448021241c68034a0400400a040b510b960707115a017003046142c2e210543c02d400a4066a02181a80b40c600344140301c24218035010750803800000d072008817554488114100e48503101c0548101540354401240c0740d00030641d010b844001c0c184009148500010760850b045034407800c0031843d8246030404950712001e00070303061000d41c00101d203010601070309000c0c05610501c150311880700011400300d00d0081c09120400070340a440c800070440c041040c1000c0090800781980d0f0080c044580e150400e020b58ad100c090204c0d414020031f20001241d003482001d0500307440c0c80d4142200041d0800344101c0b40034100801d075a44c00440040d4140c042150024100002d8403402140c88800c41704c4118103068490 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 460365548 1250 460364298 460364309
    0x14010f0e0f28060803091e01020c0405100f06051b0303010f090e0c03071202040605040c0503060d0501060b1c0b090603030a03090201090308030a020403050f010b06090108060111010f0b0109 83
    0x61a1007000841d903006001298020756188510304a1048050440351074041c19614041c214a8440041101d2a001000e0000400101c90640001590402c0d0308000028070403c10b02680c407034004a0914542500300c031780d1145c40300e894a91404e80d01c0050118100791070b80b242004ca2030000760391389044020038408065890754001036245503d0300344243c4412989129104510399181020700804106101400e00090002c044800131a02c0f860003406107805014120f102d2413030000001100e050a026407603050002e520b60500316640c0b41b00744035103402840c104403240d559892022880d81c00b030801520140444d010040f03801c04c10289542c044503196034801d0300c0780c036088040207011b5030000100c540c1d03411145008204501d003880183c401e003129030801002071002104018803911103501402c11240203000f2a140601500b40c668200e400c0c402c2d1040d00140100800030440d402241d1050304500c042c90b16205184407200b00c00d00316200740004001d65511203c507044c40d51703401205500680f2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 460366798 1250 460365548 460365569
    0x31809021b010219050309160b04090b090112020f060c010e0c12010b0918030f0c160b0a0801031e05100507110d05042303030c010203011a0711010c021314010f 70
    0x4000400801501c181c00b4071000810070000002204820280715448c3d4a0f04140034141006844150b00155604140900d242080c9802000b9200b454401807540c12500d2842e030307191403048a5000d22038101411056107800100030050603040b040248500ca2703081c4400c0c4060600034002c0030400040510980c2019480d80c103003055022281d60702601542c1080d1030009440020f600d4104650443c007a10300b000c025440d0101d4040c4c0c00d4500850040d98810902200d1400b5a8490a068031640254400c03000068815401807000484c07103058001442500c0b985044508510740c2c1e014606041d00700440d0100751220280040e950704410440e411561030005040506444400108a07020358031424441d900070302d8980194100e143c4036110f902c0b401805907652010b4400c0564007039130003031258210001510b541c2c034403690011001c0c6e514255005820b5481e00408500444030303d1903d1006a9011007c40407080744c1c84814031542c0d0180c803059040302d840e50301d070070a2084169a503500018a10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 460368048 1250 460366798 460366807
    0x120f071b240b1011060906010b04060c0606050a0b19050a020a03030504140a120e0613051201110414030111070507060804150606200706021009031809021b0102 70
    0x40c100c00504120501040760850045550480c1c40c0302402150041d140c001010320309010340b280e03010681c01c0b2401028421a0001e80340c00396040e039562024450305003642400d10040c00030b18498a05200740078010000072402517155000203803e0026a40841040d031800103491307035800e004d070300180f461110f50304101d8100307100c00402a4481c0d2000c43c0041c10160b540f00018100842080f03c0d240c070150b0b07601101c1307445445141a421000b4982c40b81004284c0d143d0303209080b0b190400880e2030b41c0700c901c600000c081d031a040620904c0c0c030400322400c14039500c5117500096200d151001d0002000b0340404a6407a00d90141414215024000407900c0e0b60420411440840d0340010340304116036207460900c07034680d100d0403c180803206512441d4081350400400041c0310707a101400754042d44080c403d00d1034040700b0f00040da54030142032041c00c0160300515803600c00d542107070340004007030b9020b814283c1d43c004400510007030b00030543d0044003900e98040380c502100d071600d01c000d40583e40444007c6290 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 460369298 1250 460368048 460368053
    0xe06031c021209190b090108090105060303070807260a0e2d0a0909030e120a050601090c030905010221010b0315090a0b030a060615140409090503120f071b 68
    0x141d401d864070b0340180c06070005045581d0b032500086070001d401e02c070901088560302c0c1c10001e80315074807071000140042c0340c000225031024010304c18640540c5c00103001f1071601010365a5820140c003c5076060f10014006c12080681051b00c940300100c00c0c0c100f5030b0701607542d064158064030501c0c1c0d0058560284025011803400d442502e20b1800c1020300392504804803a100400065001c03601e80c025071152420401744004064110640083c902c000301c0d0203215010703004c5002c564440c082d2002030010b40c0954010003070340082d6030204c0c0d07625045240114000c105521200e099a01c1086214840c2000d42103917070301320300e440040c80c0c05000e1502000d403660070186101004111144030003407081d141d49011411140c00d540c40300500c0000038082e5405221a070070000c0040100d44200765603030000b6000c1c4079580e03200d20040c846408500c3c0c0300310b04060420981800400804070115000c0c1720030081c0480c044524490140704240f00c6000a00074038040900400010b07110b82c54503000d95211590500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 460370548 1250 460369298 460369303
    0x516060516060216020a09051b030c1602151b0106080a0507060503060d021e2422050603041209120b04150617030408190302250b040e06031c02 63
    0xc410b90050800350300c801c2d03601d80d46804c400a02000030b5000305801c2c00080c014038690007141c4031f1041d001140c43c000c90950019030081c4801c03074020300e130001d04000d000f6a41c0042070000c130004e0f002420341126000501c03002c074142c0e80044500b092800c035044034804404000d024005c003a208035005001480319507a0741507035aa041e409003a050040c08000202c141d200e422174015180d40003084002070b10b00051132000e03502e40001c003c501a1202885806140b0303040c181d030642c0c035884180540c1c80c00c00c4164048081c0080078000b9010345a1035640015146c0c0e48401550160740200400080d05501c468058840d0f034031613104200c0300266042c1040070551032502035a0054000340d0000910051011040c003c8c4000d42004480d29051191000707804800406401540e0b40d05046404440d6190040040091075150050050f440000101c40b03240984001500e108100004441c5007070f1180d08010203034100750890702d00d40038104c080212a00c2d04008403002d00800c03242040401500da40000e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 460371798 1250 460370548 460370587
    0x601081f111b01020c070f06030c0207140d03030209060a091511030301090c0203070c091e1401090e030f040e04030f17071b0204050a060515030c040501080604020405040905160605 79
    0x303941180c0703240c940405070020340407541c03144208004d94020a03201c900500300c01f00140210b40020b49405145180c5e01d0001400c1b00a6800407094640780600d200c0401c002405008811810540c0a0040c0071641d2119409442d004000d5202c0da1a5a410000d100b06a00e04d0600a07000304540391409118154010007141c2c1562034100d00450720410100099141d4072641d42c0041000c030504500140000055001c1d1104c40320440441c039100d035410b1030b900c081c1c0e2000078030074402280c98801009007960075030158485081c010300741e9041403101a0003091642003079100c6040305042404000070554080d05002d4160307182c0c1040e400c4080640c90400900c0d600074102000c2c04215410004007800007400400e03250760007042401546481e0034040701410385c078442e85014440240c2880c40b6901c40409880c410b2031685003140c02d141c542001103039243c1c0060030f05900941c2c02c00c00402d60361200e02580b62054014001405114000c0032009040070859010b50304116047c09580301314000c180304071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 460373048 1250 460371798 460371817
    0x5150f09070c0b10030f0c09060b041a09030c0909010b09220b062214070201200a030b0a0e1510020706080414151f06050a030213080601081f11 63
    0x92816654003112018800b03185e8202400e201c49104d403141c01c010080c003890041d5a407186013400419642c0244107118044da0144d006031a048072020103590701d0705809082d21000042c11210700114502c0800c0d00c0d80f00a892141d81d594440801101c1400d00941c49901701911803100c204203401c0a91420815024000c002c1400e10f148010a40b665901008280c0d500455040c4480000100300e41400404450202680c280941e600044101c1d00620036440e000440d9008600c0d000740c540c5041d600740c1e001100c1c034801d166a6000c001140d840311600030b130203800c081420f203865092600e09450b051115010551060003418a011070243c0e02044100407640541010f102a45a41c5400710820f01920701407041c2d4410a00407035400c0e0203020802e40110b42491042040210b6484502458511402100e020440400107050801e20a50047c0391040c10015000581303a12200391034201482a845003080358030512003425480d0065000200c0c600c2d40768401c00000c500b0221107813187c06440c07540d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 460374298 1250 460373048 460373063
    0x51b0d080903100e070303021207020a0b0f160c03060b0a15030f0e0d030506090708010608060603040212010c2a020310150909080307090801291305150f09070c 70
    0x808190349041140c80c0300c101d054482808001103840010341c5c0c03108240302c150010b10515000e00d0303070503820a040380ca0341074018001c05e0310785040074400305456000c0102e44041c5081000030308058100c0c450341440c200c0c4554009081940344d810150140c80c480030015200b00d0300080100705024420741038a2400e482820081034460749410040c0080071000140c030300c6070044000c0c02c29110740c150700140c812030003100ca6480c00c0e21021400c8580350400d000c2c05010640d4070380410311601d00340c80035640c0244010204606220701c0f951042c20b43d0352014501020079580d400c28401d486030b8905801c0b1501a08084041e1918681c0010382d0320802c01d400c8541d104c0e59003070b0606580348010707102c2c0090f014000b01400100c050385800a5107500c22200e036400070f00e5282c004120018180107000c501004c4c008804484981c0c00421000c49400e141c005900603682a40c0c4002000c030740c0910b61041d1018130143e501c184400f014416812020043d4503c2002031008100a071030304007544000040d00001e9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 460375548 1250 460374298 460374307
    0xa0c0e010e06130e04021008070207051c210f05070804120c0302030f030405030c04060e070e040f0e0109060e150403110102090a0305100c08100e09190c03051b0d08 72
    0x100300248a0071283c001c214450110200703408250b0348031180114402c1d5000d80406052a0040303d40d400300382d518a005801601c420400c074505802d55a01100280707050a5000e08550b81f8203118000b0ba90340c02c244000031907620542590003000c07041c0000d5046c1003462501c0b200d90380c1ea16140c800e500886406a00d101458024890581c6c04007000e55401b40840f6501d024001c1c40d40d64035041442040d01c03d00c00e074005490682444d01402c3d00b20303442c1c1c581520003500c445806a40803084003e1030b0360400c1e60ba152104080781039000300d9134007d01c038000025140e14242480300580341c0e12100403003541d0140d401440096080310040d5030054140c80d0003039010000c6a0725034007900c12400c0c5140d00c0710032107202006000000c10350002c5400ca002c0304114861500000340d400304012120203041d00c001410400090300350f0402290f0115400c130030780d160324142d450380640074104e048080d62079980c0e0740da083c820018200140e01c2100c819020308040344001c10009068503200584c001e080c07000114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 460376798 1250 460375548 460375577
    0xb011808071e0b0c280b01030b0a0b0303040f0302090c0f0a050a050906040f0501030f090b060118050d0f050d090e0a09140a200619052104080d050a0c0e01 68
    0x35500c0020340300c2400207139950003895005555526181907400041110800c0c0071514419084003510065480030407803595038a035444503140d0000c0209004411a00d07160036010741d84c0d0520062001d0300d8a4400421035904600502c4183c64000f080c1c91041c0030701b0400c0449001440081e14081080352078030a07501c4050341412241400344900f49504881d01080126041034003010f99026030b1020707a8208505050300000800359118a9070140c040a80c03c804900194443e10302030081ca100190300094050b036806c0406d100c88250394058500c2020310203808104181800100d620300c4241c680f000141c0c0c1080000c0c01c5015002d02074121180d036405481c000c0110005803020007500d0f000554a1506690500c142c560752001d1030400741d041c940340c035000c440ca0300b00151440c1e89a000042e03c29415030380d1041d81d090303100c110090119404103020409540d108030300300e0f01c0b8a00c92500541c803442540c455605443e030240c44288084d04015845000036400740150803600c1c824a0154100c05202 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 460378048 1250 460376798 460376849
    0xf0604051009080c0d09050f041b0320160512120f07031b0206040c0b072f0a0306020d151401080705041e05090a0c080f060604090c02010b01180807 65
    0x9213000a0140036081c201c20740c1941000382c0e50121541504c0480c03261003445c0c200003c5461030748004041c07403035042500031a10300c03a910000c003060100311501c0f030080801001607060342060380d0f01710f000f00e000180c10082040510040103490564020b59007000224a844c040f440c40080c21444040140000154400c1c03003500040c407012a04841c224290300445030094813042704481c1520040f01d20342000030308107203503403c44000320703002880a0030080c1030031a150345074040203211110401000c2d041d10b0260382c89071100001107100d00401a522002100047c0030750b540004119000c0710315807810400d0301c0c83ca54039403c2100003441c8c4100a03940da84c0040d1224007031a00907840444081120075500c01c203803440781e17040e00c030211081d0741c140d0365003800c90080e180602d84031400501e070400480d09060940686039042140100024103150311143c1000451711801c00840040c2e45405042d225540c0101da1250358003007646074155810300749445030f60355400b140b08612107501c5c4500509401e1148 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 460379298 1250 460378048 460378057
    0xc05070b04120f09080c09130506011d0a06120609050a292511030c030706060e09010902060a0f030b0306160f02060106090b0c0c1305090f060405100908 67
    0x841003820312070405040064a0030206409640440c0396411040e03021400341001c00116007a80340240080544a1b0500c0701c0c1c0d08018012070071900d8440520000181d051007864080c241c0245040f0f08032030740c07140c1000c40000140a2640940c5000c0301030010707001e5420503041c5590403500101d00c5500a1a007070b89092074182010700214582900c504903004540150100c0720a17260424010761640351407240780d030101c03003403c01c00e41c6810701c0c61007800b501130030a001c1130b10711007802c0d00d00b8001c520301100c4c103543c0500c5044503595580e060074441c0805002105402190601c000c100703030312160f804182c0310f110303490307901e0203104c0041014000d8074480d41148140350000b90503101c0501f040c2528000240001200e000825070345140c48801501c00035004e4101c070b0469031201d01c064540408012180e00c82d0759000581c1c02030300c510403210340b610b03a075102d9180080303031000900e4601000c0302e80c182503041800801701e801581c1400085400001d100d101c6500c4402e0000b8010307102d14080603580b04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 460380548 1250 460379298 460379303
    0x100e0c0d02180406061517070e0102030c030d06031202010b03060615160f020301051b0405150909070906081302061213120c0501150303020a06110906120415050105130c0507 76
    0x360002c000800c01150490001c07100d40060300c8003806c00c13216055a85440c0d0079001c80442513044001200944115020150000c060040d0f902c0c0000030001c160841c2e0020746c5400201b51605401c10030042290202c2c406001148001c01c001d00124000a45400b000350183d8130844d440d048443d03032001044100c0e940c24003007114071100691a807901000e010038000c4140d01c20751038040026030110662007100c10b0a4681310a60707207020309000400900e501054a6580608000c2c8860303007140c6c54030681c1e00c0c09003000d0b0b1503007c0580c3c9452001002c81400a00d20010344801c0c8000e000143c540d1015035141031341d825151440d903611000da480d155450b4050283c000b6925100481d80c1c142c201c00c5103126140201d000380b1049054490700469000c1a2000400580c05500c4070710110702907500000c00e99000180311458440350500142440c1c00c00c5288010700b000110501c020407002c11071054820211410074000b0f0761400d00012170800003030040d90400703034031170b000308038020702c508100d815840c2d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 460381798 1250 460380548 460380589
    0xe16030b03010b12060a051b070311010917130b0a0c02040905010b0307290a1d0d050607030e1501210c03020a0f090f09150c0e13020c100e0c0d02 64
    0x1106000b06585ea6400c0d0340f11400589480089074816034607140b0307212a1700d041d9038518074040040d030741120b14003100e01032030a80c1c0d5650b20700c000c00a4061440b121440994180260321030400d82d001010300d4000360f003e03500b40c00342004940007450300700f8100c0d96081c0e01114009090342ca542001d81c050440001c409905000d004000709414500d290660328010142c01100f40413544a11801b059100d6002600c0101d10352108282d154160700440d03084c0e0b01809000e04940880969403989404010b40e0b4140210392260480c5440d04020440c081165083e0094040554036020a802006844201000c81d0086e04c84954003404090600341c0e0040d50701030b01c0040107641c4c80a20122591460140e070f0300c07080c1030031042c40e81c04005001c1c00c5502c50f04285140c1991078241c501400800c1c200d2042414021000103024048c0c8c0d5140c02640b030015418070142c1e4075038645080368200040d018080340500d103400120b840d41c1a0006490304001015120040000101e00004411801101a03000b080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 460383048 1250 460381798 460381819
    0x302031b18010618060327111503180715080403090b0d020d110315040e070e090616180e06210a2f04091a100f0e16030b03010b 56
    0x50341c2c00b400c0040b03000641104c12081c291980000c8041d0b6540c150890b50041500c100c400d424000e00e9040034415110381040580a049100400c429903586207030110303110070200030488448000e4000c0443c0000c810302900c1850704001c0711010703102e10602d0440c01c000130200010304040c000d800c20b101501c8600c991544410003504600c000c1c5d0322441404011500b0900f00d100042c1c50b48080e41d01944868420803125000704040c0720080425500b9030f88244250b00d030000f86d06108a92507401601000090a21460980412500c00b00302d00b6500040042c4403440e140c048a00c06828401d44041d50305a5800340c032044000f40099007a0201114030f181030040c2000b0f0410000740c550700403407107104a03034501d980042800d54169110164592040e031748001c2e03000c140c0b0b8143d000c1c001c032038404c2c1001d41d40c0c20010202c03011406001c980d1004200500d100c144880e000142258004044a0000010b1781c904903507040d40e1411a98610400d2503160031070500b180e0303400e400c0018407802c0034040c1d803c803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 460384298 1250 460383048 460383059
    0x4030203120702010f0f050d0e1f0f06060c02090403030c0212030109140718030303051909051b0f06090d0302100f14010b09090105010f03060e011d100302031b1801 72
    0x4942c45480200d000c19036800c907441d803090041c180d5880c11074070340d15514100f080d0100f9070000341000d1803107058a809848078010000c0251130084099503c640f0b80010280b0250300202c0480c0c80d150024800c1c01082c900ca0001aa64034030340b031341e0080d450319010840e07030064141a844d1940c2c0b401c00e4999280084004104040b469000c0711100c8803160600401c0e4540340c3c001e0301c0f602c0c111942800000118001803006c640280c001e03541001004c0500102c1e0680b406035034040b188a440c04079074680203007a100c1000580b00644846411040322803661203802040021a2446408622400742919502c00700c1418000d10441c10b94080d0366006210740503030a5099401000c05a2180003140c01050000c10741491020030f0704e041580107003208441e030b424800159000030010703840c0c00405443c0e680110310104a40595030003800301d00315800071042c0486441c4100e00004101402c0b03101d00010070000b50b0b5001940303044e080d4503210f90284100383c08002c120721482280b0342d520051307206c1000081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 460385548 1250 460384298 460384333
    0xe030406170604110d111612080f07081305030d11091509031002030c040f030602070308181e0f06010e0612060f0106050306040209130f0510030c0b030402030304030203 74
    0x1444524110065850b5452004000495040203000001160306105200c0c007062a039010404030300410120a06100d0000302440580d0058003040300c90405101c80c25040e41d422800e1035070840c1c00c1809141d5240350851004183d046d000348240c0c2034410900c90f5100780035051003203c848040b0300d04140a07070300000224404a50041510600542e16600e22034048040203064500240000300500700303000e0b141740d401000c0d420150003d203040c1001c000000721454001080c400451040c80c0140c1c847c0f15504028149020041c5841e40d04140980b044111200c00300d00a02d010404140140d003060744034407028030380321601e40e240c6210300c40c41d0000b003035400700040b41d91321401046504403001d081001c01356448940546840b40c450740c02c0b900610016001e5806503030700000280c001401c00341c4a4000030310900c3e199460a204c16178a0a0902d180c2e039450003240c2c1d2000746113805130115031450781c503040181058172840481c140c011001c00c04568081c0304440c029038006044500311103851500c401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 460386798 1250 460385548 460385567
    0x61d070e01350c0a0203090607031403091f0c170c0f1b0c04090201020307031d0402120a050106020304052206030507060207150e0f131d010c03061a07150e030406 71
    0x10030b002c16080051040d0000c90100d0749550f41d5980518188121401488407a4220b0701c011003d0002d0713200840d00c2d4844000c095132203480058020210114107a402d00100c3c20104501c040d051700303000022502e907401c000b04004141100d16098901e907141002c49141c0c0c0a9010640320308200000d42000304400900d0592100031b11406a40f145d039800130810044030030301c481c001d0260b0003d1115402181c050907000001e4a07411002d03000783e04181300010220b901250341007201c040c4c2e141c144401034800f0310515024000b5400214075103400d003c0080d06d40090707018a800754100c1c95803036500103c5560090401907501c07804980328680c54000103500d58126005e01e10384800c54041e00d01420303106040041c280000a4440d903600258401071082d01c04e03c03407040790955a1103405004440b440000b071680e220303940341d000040d0095812002070645400d94007001602c3c0c206405000714080820444601a60205241400048069004002c0c00210710200380a00011400240c401c0c1c201e42c450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 460388048 1250 460386798 460386887
    0xc06060923010503150103080c0c03010504080315030d211b020c132306010c141b12122101030302010603061103040b04032f0c04061d070e01 62
    0x30744076a2103c0a05a6a07001804241e412007101070040000c2100c040040c10710469103c151900d5000080c042801d5a00c00d0f6011282c00000008000a4000841c60389a5080c400c80c09001c852480c0c05006111150300b04c2001600007510b4010b501111856204551000c001d080c02000a1039100b006511800000c45d2280140381014007001e0704000c0e031280007203c1607064900c003943c01c91081c45c0d026143c00180610b051200201c5d0742008181460100000100c82100030101c1484040d00712244070300c03010446004484613880200031004c00f00750721803a1007000a040d51142c0643c0701b0011044501d017a5160070400401c0040700741035064100c501980d00900e0140124141c1c888000e42500c411200070b84a800408c01060000b03120340b00c44040d26442d45200d812000410120b1000c102203000468400c1d4000700140341541000d00480d00182074408810351400840424074024180050050040000c0f803118004581e00444602c0e5866080c440407909a0558160204510f146040341 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 460389298 1250 460388048 460388111
    0x20c0d0c06021501031e0204061e090f0c05030f0403020a08030115090b0f0306040f02040506120f0901200d2003100b0301060210050a090515040b010503070e070c060609 74
    0x820103400c503c1642c0b241282d9012003806040f040f4000c0e040c5d100510030401300c6e841a00c894001902d040340345154101080000c3c0c03101c0000340762054090480b0754004241050506140004840d682c104083d0b80d80100250044d00c07555403540f401300d04010b00c0c0c020081c0110300c00710011800b50382030100020a42d2194175400d8640f40c0351110074a19001c1c1c142c0440a00700c0800c0000d020342803d800160356580c40d802c0c05824280c07202c0020f582508a1740c01140703440d440c42d00b040343c1a0700c04000765400005079802000a81c0110401d0b0743d82180c094018441c1910000d800d4100d107005902074016800340b9001c0f4081c4081c0c070041c400c4940e10540c1c20b20340496443c5004038010034600200c9040f070300a40c00400903107107561f1f038040c05080010850400c00380e0320000c2402107201031000c0507039951215150314252130a4074284200a80682140e80a0f0380103180034001c03800d48544243c1c1140740790604101000c1180344c502e000d00080d03040741c0011428203c00780e10b005c030125042511786651400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 460390548 1250 460389298 460389313
    0x6070812010b0403170d0605060406030f18020f0919050403091d090601060c0305090d030c140c13050a0b031605010909150b0a090803120f07020607120c020c0d0c0602 73
    0x30503440b580101d0001624015004405000844141c00105090003030b046000c54090b546c4d038001440c0d034210381c0c0920042900c0301c2e410440b44907181303e000d41001d005505020703036035000d80100361824120344600c1d018112050210700c0c548000c0e4940959071003041400d100600d440d24005003041140d03c1035100011041460b4030042c0c010521140c402d01f5070304c1c000c16150780380c61422218001003041c107400340041040100c4060700d550540300c0700c45000e038035800004800c03885c020a090200d09200d000300d0308820a8a455039480303004081c2104203080d40402d0949440480c07000400e400c50341140d151081d0f2030000b400c050403400c0042102c5007600e5010100340c1c1e64010070161442008000c0c42c04105507414040345410387c0261001800030714004801d1502e41004910703542c0440541654881680e0030800c17030107020350a10b0341c001014809428642032a9401030806080c0600c1c6a0520343c132508600301c2c80c0e200b044045d481c0003004103080f0000000d824201e440905500a04005018898 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 460391798 1250 460390548 460390559
    0x10b09090307151d030c0d08010626071101090c03110f0913060212010b0310060e0918010e030d020c10061d04030302161401050a0c05090607050106050607081201 71
    0x3034902c6a0780050704031448210801e0701000030980b0500300e500c0401c189249559410040001c0e1107007030203000003011200e0841388050403280c4142d2001082010500040010003814104459080c800203041c1a43d80c595110a40d40140294200d00c0d2039807070421210107202c2c14814140403039001d4102c4550080d262000d01c4003000468000d142c000300d42001058a0720a0701651411081c0608001030504540c0c1c464a401c59000382d21031410a100403003880585010201c5950060999003002a079030115000444c6200900820034440400e100b440703081e41303013801e40202000000394403d903641d810340c4000c908004c0d04074509000071440b0302e07d84015099500e22a04042e5103c038040b0a405100c806102d0344000c0d030052085080580901640c107610a00e230000341442c2c0d12450103c11b68440442510342101c900911464801e410300e00400b00040d000422100d175607209a03080303036840040d8180365000d0702090b8080b50304000000380010074400c02c080909455810303008410142e980c2d07403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 460393048 1250 460391798 460391803
    0x30b04060f12050a0b090f100615030c021c050d061d0f10080714011d0108130501091707120207241106010e100605031003060902061b010b0909 63
    0x2400340000c0d14824103414002c1c95456a10345095511a104607035801010f50380d070104400c070943e88582d941d4001c81c03001612800611501540d00c644980030400c40e45400075592201513164407030000c0c180d840d018950703014802d110ba14000c0503c4202c0b01c1900c12002401095913208508500500b0320302040400c8501c410103180c034910342143d10034105500d560220a5404401407c1c0c0d0b4210300720700c0c1c00001c503070a090007080010100e1040ca0108280301c040090082d52110482110500d540c0a1203540b0303a8002c0300c02504070502e08444401501c036860928010300070888090131714091100d00104050300603004000c450b05c51240700821041840d4180d0f61a180340c000d2074401c0000c3e80543c400d00d03d00c104250510007851502d003104064a4078014280318080c0c00900307031811141f0411916800010450004042c83d280451640c03030120140c0148818501008040984032500c0b40195aa80c1c4180d403040c90300b0700710312800303505401d0303000b8024100c00907514021fa94650004080f41d102 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 460394298 1250 460393048 460393061
    0x17010b0103150b210406020409140603070b0d0617030304020411040f09090c05060a1107120b0f0901020f0a0c020102010b040209090a0903021e070f080a170a141603030b04 75
    0x18010400645030070000e0803400f6401c41c00340071059140b4004075000d040d000c01c0c62140079500580005075207508000c0c0080940741054542484c800c0050240916a100015088112803200786182d49403101715600d0f0018054561040305003004003521400fa07044088015030149100715001c002e20844400c900a550003284680090b400d40444204086101e581160307201c180305d543c01c010401e4403940010541c1d041421480000f0b1981c5030000b41d00c000030401034028150f081200e44010f981e566035080b4401c4010710320700c0199582000309441e20801d405035800040c20264440d11000d0300a4002c0101500031000d030b00560821510701008d04051084507a0301c00040e00b044110b03910819510094412494110300b1441520005c982a04003095204130350100c550107001004c0c90054581c00440f241e0b007007452a0740102800800155204920840c0f00c100202510748031100c0c070b50140c51590310b070075070180c20040010301095014200b582c44145284a62800c00a000d03a9005200484c0d15 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 460395548 1250 460394298 460394321
    0xc1611120f07120b160c0807050607090806010b07080c03130303020303040c0b04230f094002090a0b0901090c020105070309030f18120b010e090c030a02040b1917010b0103 75
    0x800780007161181d804005c65800700700c0242010403024a0b01d0b504c408255100360403e442d0340d0048028002c650790300c040000c0c01000283c000f000154181515590141304007000282926800298050324010500550f240e101e503c04005100c00d0341c904000c1d4880c2d00403242142c1d510f095031408038181030541c041c1d60039941e6500152480000c411441415094140101070f40112018002c0307200e9528010568402c032800000d054110203009050341c661070400007401d041d0355045043c4d100806049200c0c0320700c903404944808841e201c804030710780100b00341c411040c2c00c40b142d03000214501c0610740000c043c0c0409036000700032984d82c6032011000c40328810380040000301c007000c5141003d440b900e2080302e00c0005e401c0d0f103600c40740c0d110341880064130766131012075881540c20010020808603042655210103080b01500d030101e403041c0001e03110f4055200c000d207c1c82c4d58280070340c8291124044824a64010038405080b20384880d4a41603401914140d013015608010305011154441c1c0960241c459 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 460396798 1250 460395548 460395563
    0x110d020604030507080c121e03040209152e2705060a02120c07030203060c0f03010902070c120b04050c010e0a0306050603030f0a08010305060a050c1611120f0712 71
    0x468542d022a0b080c1e0048105480c1e0601c00c0c0321380321010406002c003c600b00010b06080360f403240707410041519210000c00503512900180208030158070358103115980003186040e0311020600c1900010151001500b544000506051804c403200e0407007003642d85c407030303145032241618450030701442c000410080c003050781c800002c5181002141000c0c0f028295000483c01914440d214000400301c9640200910f241e1550241c5002c00540c00c051260782d4125080e940854a4005101101c032071902c03041c4212403120354005450401d128440c0b405401038035803412560610000d5003000d2404000a5900390b403140918564024150b002d00c000104051003d011203921070301e551141c4e001000001e00254040c0001c115109603003410382d00030508010540c80328506541141086482c202c001408580640e103000700303104003041c0240030307558840b03a10a2604e845002502e00b82501840c11400d46402443c15044614003620200700d10400c00c1e504e2084132020340c0c3c0c03517101c00c0300d0180c044030203440c0c0c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 460398048 1250 460396798 460396801
    0x91e060c0b090106270f060e073e070603021806031b030f07140403080412020d06020d06060e09061c030c02060f0d0b0f1e0f06030f0106110d0206 64
    0x1d50400e16141c0c00007500d070001a210382d0710b2098a100d90b41c1842e41054907100d0032560003480c00103210300006500e29940400c05942007516240da0098040c02a4090010010189020111001034000a01800f50400c2c010010103441c1e1030b4000910283d20845005031000880d00307902c240300f9941003426481e0792041814864041c08000c0c1d101502d0191000514100103c0310b110f403030015802424ac11004010914110800420000170803003d401e044a003000200081107002c41900e041d01c6604508480c0c0211501c00149042402c0740000e00203800800d28043c100807503400304046410503210b060b0203100724020000c0fa480200c41180d8410002540c2c04c007220190301c0707071a90051003030600040007100358000640c2900020f60070420703030000050b2200680c00310f00520301c3e20901694103242400012000801701086101c40020b81c1a03442d802041c903654031070082403030890140c8a580e4074203183c0c1034860041c1d424041d10f0003050076080c0c107a55000d40004d20340c1c4894041c0e0f016140300d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 460399298 1250 460398048 460398053
    0x604060507061503050a0203150610050c01020d0609060f080a080f0306060409020f040501030b010c030c080a0207030213050f1312120f1802010e12060a020c010e070303091e060c 78
    0x319003103114152481e640d0381c1c040d0600162440e4868001d07501440c014901404ca40c0304141c5010402e00392040f40311a41400d01c4916125800f40c1900004039080160700e1341003410255009014034000740c10520b0070014001100400b540c03040090743c03c0790302800812074607017075041d40d03c68040384003c12074403040108680400403140a19002a030041240e403400355901c0c200800e03a0840030710700b40e0340ba40004003007289607054816802d040d1030a00700009402c00a44003c0c12049038041c0c085c11240303001668402003403003404a84080d540c0106070300168507201c0603140091030b0495941d0144401c15020808003014030640034045584900c0640200703181c00b0044030702808450708411040e0710350208005110303603406101218014010465281da4443c00010800d06e190107140340903140c00c02c000c516403a400300c0c140d81e100003049400340e619407449080314014002c2403a462881d028041c804420540d02440290442d075000c0e5007072100e0494080d1a01c2198060300c56080884c05100310a1300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 460400548 1250 460399298 460399307
    0x8191107210f0224030609010e0c0304110103061e030507064d01050405010b150912120f1801031b0c11030303091005180c0909010207171902060402060406 68
    0x102c4510152510800c400f10380190400f40c9101141051800b10100c00c200c0036003003600c6a54018807a05140b01450b081140896440d40301c0034102510840400e440c251300380c1d0182d0070100090100b402408060031440c041160043c00c02c0c04112107900440b000094414480c400c1d61801200f006142c94004080030045114044101c00e0908101c80490200780140001507a03900103442a200208007441c091504c21300311001c6c0c01940307205c0c800c0c980c0078484c55500c580c1654400e040c01e84401d01004007049402c0d1822080003a1041c0d0707036a00086038441040c03e0340252280d1010202d03908050f50081006609558410b20800e403003185210070311461501c0303201e0203118140100311107215040c603c00442e0940e88104c03010345907540000d03500c04262502d803183c0e42c0e11414840b003039940c2040c5801400d45845e0030805e07040c0b28907030020210303260310029812200015032201d10520704c0f00e07945491100326042900780c0402c024450100b00040c0f40042941d5100319401007507a0f140509281c001d89 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 460401798 1250 460400548 460400573
    0x1020c12010608010c091404050403080a110d02030c12070c0206070b060d02100201060f06050403050d0e010219110108010605030f24030a0602031f0305190819110721 73
    0x501507482e03080004100900f8450021400c002c2e56901100034102505803950722110450300f406549003004000110707a00c12941c81c0c1103101c0c0700d00030409580c90425140360b800b80e08a0420740b1403000081c8240c003100e013001000302c0c46821982c048640d440c0c903c00e45400005003800ba4200c1f20400c100e50008020703240c0c035a80420002c01c0e800d00e594094000c9403840380c0b030030b2030b07480540c0d580c0e401808070050b1400020003c00840c9002880c2c10304543e0342c6500c65042e20b0000f03080c090741e0b0810800503802480421000c5080d07002003400913082d410403100d10a140b000780c0c3d0101e141c040000ca00c0c1445102240c0c8102c5070845103040544507580355190911402000c100c3d60583e10380030408a65007031052480702c0d0b0042c04056101d00b480102d110900c005040c46010b030b000b10000400018801085010758034005007000c0380012020b05010300944940d400404140036140f02100200790418130020f02005c500003118680c40d290b0201e06074015400c0001040010314454220009131180400e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 460403048 1250 460401798 460401829
    0x6030a12080601210903030b120c04020a032003060a060f0c110f03031206030705040c090b0a050904060305100b0103051014031608030c010b03031801030f090b07210b01020c 76
    0x211001d60800304401820b44c0d404850030b1070252070f030201d0400d1507494001d140035500101d800641442c0712100a5640d00309004e1400d0080d174010440c4000340c0d0082c0c0c0105070303401141d02d5500c2100b80404100c1c03510b62040721458491482d0f0700c800f2401a10942c050b08a49149480e40c1d100510f407a04c0b0761502d010f10a9200358044c1030010f500c180d40d00c05101405104005d11003201c0e0358100701c0201400d10016820075801503103001084200a41c1c010300350700495182000f400c1d540c10742e8034411a8244540c036000d94026003070000000c2000000640d03400c240726085030800100000000442c19243c06a44449811021300b0040c04000102c2d504424050740c01811640c801060486e4111150031300d0b4032021490708041084020000300b07004000008000310099441c02400c029824101e4030600901410190b440d100d20b81000717503d600075404681c00410440461501e03900083c00004c4003140c1520460301603203c0c680e0021079001343c02c03030795505030050300303502e8520401d11002c1203400000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 460404298 1250 460403048 460403057
    0xd0f0c020609091b0c0309030111071703070509030712030e0a0f1a0d060f0e07030509030d09080c100f0b03030c060103061e090f030f020d0c06020d06050307140906030a12080601 78
    0x2030710004c02030800a1000c0320300c140185407030b00030a60416085541c85184070306001010080c0c2d01c0002c16208180c0b188500d01c81d1103d84940318074500700d507240503c4078425014400c090002c0344419003103420012051090340e0356a4241005001d00c0120021344c4110f45002010803400e01c2225086c6c5400c0c944120350131081c0d82041d0101110300d096800c1380e4443c216003514002c043c01852411010181c0c044090300301802242460080643d591289801480c2155035800c50401048040790407541c10140a60072103003072400d43d451020082548002c240d01407440d0001c1d141d55814044280c070803240c4903030003505080e81381d078441c60086c100c1c504042140101040200000041ca88100764809001c1c1c0101c0807407060a1038003800008800183e08103640c02500d0f511b4000b907110a04000c500d17482040981c882500004d8100a040c16070412035060041d01c80103e01c602e0748502541c011502142e00088a032140e105054540521240242a880700d40b00414001801381442a8022406141 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 460405548 1250 460404298 460404331
    0x2010e0906030312011401080903130312090b12011403010b010c0609080c0615040c08060d140304090c050903010f02130b090a0506030108060a050601030b062b06080d0f0c02060909 79
    0x41c1500400406d8209084180070180f42114550707011507040d9200c03541c05c00451400020040300301602c0590f200092414020340c6070380046034419115200100365110859890794080b03076000b28809000d0090700c1110381c13030b43d0704100e0034641406404810401a140e01280ba00a500ca18003c1e2407402011b41b140071040241d4076040108001543c401c1610641120b0000d0380201044280c031203c0701110100042c01e814405142d0307616000500490b40032440035246054841d01d80d045020f90741c012103405103048040c0c92015007000080c952010114000c0000e0881203100348128051202c00704107094428409112542408000307080b84140206000c114558840028002c5c0d8400d0700020b40ca900300e2000c0c00b1180d2503d0141641014090905000c465160310200702d9900a0141144e88088014a201320108002c1c80034001c1c145a0031081c040207868401c078035580c82140e000b10b40020440d41880d075189210f000c00f0642d1700d86c02400c0030714241e619820042640070182200c40380c8a034040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 460406798 1250 460405548 460405567
    0x5031f06020708010623100c05010204060c0b0606030103050c121c03060e090a0210030207080d0504030c05070b0406050304020d0302031c0506040606020102160b071707021507030902010e09060303 86
    0x266450042510368020503140d4180005942035583c40c0e80300400024040141c3d0b60b001d034020f2200701540701c064413180b1211800600864409454440c05001c0c0d5200083c00b0a0b560f50094a010105008002c103031000e071144000d001301c1e44400d04c00540759030460503001519140412002d12015810740c02c440b081101c95002684045c0c10307140b100c000ca90380301020000302d50301d0b540d0355601841d07401c068804e00c034803500820300003642d40c0c06810405a00041040401403500185d800840059404010034a42441e0242c4590206202581d01d8440d01d8000504400040100d9044d11001d030390380da05644555080c081c041d0794000c402c40c1580800d0060346402000d4080c000c00c3c2411008022815003050428081140c071141c011408690040044640f0102c12400880e001503010759156115660301d80111032052140f0030520241d02144188012168001004802c0540344134070948191111241a0701f00c0c1c51804c2c0083c085585072158840d1840c1a07100c499010341d02400f5a0310705503809 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 460408048 1250 460406798 460406851
    0x7080a0209010e130605070206161e1b060e0d200d1202040305010f0605011101020a0e1201150801020703030b0913020103050c0c0f011a060301030218072c09090705010f0503 76
    0x710f4107d00107174052020840885030901211080d107946003804901c8880d0b081180300c07000d0060001d0018042407240391152024549900c04d0030701c3d0054004c00102c0c215803545612001d80c041c0340e0f00004c1c05202d4008000480406040c0200701a10042880ca03040035000c0e14002c2d44840925901b59003840000041070742800740010117407020b54005216800c01e0000f402c0c1e20703491710481845d80c0c414440d4260650b040031110504843c00c8401e8400706108100642c0585a07003104100035641880d4001401c41054014118151081d1030a0012990b003c040c48000c2c5000c070f171116490f111610b18100554025403100e41c1142c03008a08625040e0040d4a07685040b00c040b075203440301c0c0c4d5544030102c0d4058194042610340f203000c0702d00d0740ca154991340006103040042000780c090150003402142c2410b00604511000001203500e0700d1159400c4000c40710442c030801c0380b541c040c0e00b210700040e1141078007081c52400d890050312103074802503800c4800c5a41f500010042c011024143d07842842d5100740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 460409298 1250 460408048 460408051
    0x50f04090923060613050907090905100204060906110a0308010311120706090618050105041a04090903120b10052203020603010e101505040b1c0e0102030907080a0209010e130605 78
    0x107000a0000e428451300303000850440294841c00340385080700303112011070081484412641d4421010420000508025042a02a0040900c142d200103000180700e500206444129029512050000c2c5c4080d0100d68689807603190040000d0303e01c400510020700c50500840964001500050700d645030a1401460402c172500004041211407030104001c550081c4a41c298000101482928500d0500081d00314002d50007060035007580e0100ca01101040c80d0103840c0108a1240c052007011918200900903401c0d41c41c050b01c20300d040000b82000d0703090a401002c20b1480c5940c40300d00d480c40c0c40643c040b174002c1c520f0b0784841c41a030300c11000000d030b65203002450182107007200d0441c45040050360168074070100d520400d0510b441e861860341c0306800c03009880440e0441c02509507141e0003072100b100003d50190103010228034102d02d41c0030022055000e1486500f903441103501071a01c55031419a6480104e20081d03019144800500217030b64038900241d0001c11080b00c0103050700302641c4000a0b90070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 460410548 1250 460409298 460409363
    0x181a0d0609140304092f161b03021806090f0a0908070b0a061e050402030c090607030c0204111309020901020a050d0c020307141807140a020307050c01050f040909 71
    0x800709040c4624007035031180711281301001100801c1d106d00c010300c5407541d00b100300c80b101e0302400c0415038035041000150001c0c1440c0e8007551401140c00400b10360000c2d400103000c2a80242949071520307003024080c8124600a09000780f81428540d55113040c120584401881e21026a4a030507800b0300144400c000380841c10f201c2c80e650240c40c60403500c0d8400b2280542e10402103049488240040240008014400d4a02c1a01c015a81e0b5882e81c00141c828070528514a8100e240054041c05243e0712070300340e4002500c211000e105102050003542011700075119034140742110401c04003e0b011803a401400800c0c0b041c0180c40c04040c03a030322040e090410311012003010031002142102140340c18010200900700da18401e004c00e1000c4400309120301070400c0794944103202c000100300018080c00c0c8040707441206180a5588042c0040c0c02134507500903540485603449442c0c0f500c0d4443d07025005507020090580d00480c280351801000da40030700f40d0900141c66610b4030040c06941c0c03440b808080000c006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 460411798 1250 460410548 460410553
    0xd03110f011409061b0d090f050f0f0714010c0f0503071505090d05030a0c0c05120406090801050108030a0f120f0501150804020102101512050601181a0d060914 70
    0x41400103a4500e4004001c5401c0740c01038010803402d03106800300c0403560038100d00650345071b1850f0106c2c44010800f030880a00488201100501082000905200603000000c103443c0c04007003190714240c1c1c504d02070060560100341e1114284003540f05860810703a0741e001760301c14801000d1070b450b00c904560090303a0540d0214022024801c5441c1a8020700303800921000060071981c030301323050003001400042c00307020000791a0076418401602c1440d80344403040e0000309a40c03001d02c03240d0195915a1051040304041810f400c40010f81c6003040c810f0341c0c101c50030480510b150242220080b110b100d12075000c0d200344048401d0840695203075100d104030300320160340d0006103941003030b100c00d006254a030142402c11540c1010000142d0740416040380521071400045000c1030703e42507154610356990002000f4580040c2c410301406400202c1c0390403100c88081400e405030700790221806581401a06401c409030691b041007440c06e103044c2c1a8815809080000781091283e541c03a00348000080060625030b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 460413048 1250 460411798 460411811
    0x11b080f0d0c09060915051c0f02031504050103050304270912110a0c050405060a0305010207230d020312070e030102070b04050705180a0506041b03050f0f150d03110f01 74
    0x160403182c580f0241001c1d0802040c110700d00707090300d400a01c075114080e0401801186410840e900d0089020a0050b0010180040c0344607417500740094008461300000c1c102e03030504015250825101d46416650040049c1d0320b0503041000c00e00a1600c11165141441154074954404840d00c0c89116402840303151344054851110f0b20040001c8000c804428841c0c004080741000036204600c540b08564003980d01040e40e0780c0710000a02d01c2c81140d0b1000d009540000342810400034030f003c000c00344890181001004900c040a155a44c0078614414405a44204888640d8480c00c21050342e1100032031620f41c000107142c401003404c1e60440041100e0f456807030410302007040424041400a02002c1e1071030560307005c01440398264000d001e000405119901c4000c9030194440e90000f0b60100003541100150340500780009008060889042d01545150b001203482200e03041d007000d014205401d166190302644004220304922883c0c3c3c11003d0148612001e80f807803d05000b00b860340b8204400000d020f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 460414298 1250 460413048 460413071
    0x29090c0112050f07030c2304091d0a1401060b0d0510090515040f11031305010b0d020d02010f181401020c182413020a02100506011b080f0d 61
    0x20a1a01c0d07521800c904100411901d110a030a0f520342c03041c9645030105c1c1040e0308010984a211541208001d00f0100110302511045072000800c00c40d480100d041100e80d40d0081c40c003031041007020700d9a07199001800310300c01044d004041c0e05448481d4600010324181e40d4003942010781c1c041c01c0348889a035120000c02150f442d20340744801c001e01860030244498600304a0301252100680d5001d8482c9603641e60110728030100ba84004a4091200083c640e242420720100c041e03021500c100b218a5800c02d5003551450609094031804564003404a100161980d40195030300c40014070110b0412000c140046144140c20724030b40e0017082c401d01010103100b00000020300f070045c5820b02500541006950b13200c0120841001648503003584c522100c003000441e1641030b04088104603d40c4030b40c0a407443c01c0408105d50041400d8010f079021507070138108490259054039005ca50311404512585052800604404050880c503441500050316000d180c86106055030040c0d0f428151059850381e940c0314 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 460415548 1250 460414298 460414307
    0x120206090c010509120f0a060212091f020d02070210050c011d030d0e07082a0f030c120111040806010303091d011202040209060a1701051203040329090c01 68
    0x821040d03000140039025900381c0060414410300b140c050081080c0001d07200245418014012840046020345204804904002010350480f0b10b5256444d00700384e0224002d01e0001800060300703041d0011000d0090004501200290020401201d00359020001c890041e40c900801852901c05a2100d50300c403a41d0030700071421240c00302c42c1c106600600040b41e4422800000980d01d4240848a000c2000c42c8198941400c001f8617500038807507845410300c00d01d840d182e40c40226880340c0c2c000800c071040008036000c005402c0801041c0c0c5070540c1008103804600d061010b1100d4050b484a40080750640c54090b0200703241c0d10652049180780c002c0c1c0d0051081590140e49500107242102a11404c0ca20071420030200e210184180042d9040c0c5940350402c5440c0c07501a0752400c0c1000303240c261110011000603025003006c00c2135038107a07400032001148524025050115804016004500342410340d50707060741c0c54445080c0d0300d100c1d9a1484c07141c0340484445008902ca950703598041c01806403400e00150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 460416798 1250 460415548 460415551
    0xa0b01050906270307140d020a0f060c0b0c19300b030d050c030a0815090a0203090c01090f1404060905070f12050106080601050a110628050105060715020d09120206 72
    0x24401d411004003005803007000740390605040b401300c940071220700d003620001c0ca43c4401c0345c1c45140e6481d441c0ae000641c180c1c0251040750003038002d45440a5940d0380119043d09441840900b941c012480050701400c648211101c0710400040d80d25043d5a0310004500b41402401c0d440c101140b68a80d02846102d003000c0c050300344100754a0800d581070851100c00c2c02c0e02c1c0c3c012031030b440081203c088002000381c601c1082c5000b14030380c05040d01801c0d081c124900c4000e907004a40520651140c0e030240c03600c035445500c0e407504544400c0f6400e1640b604015070000c080324440121a8480c0c0c032540e021031240034510406002d03030b10f50b442d05280d401c546500504044d4041202081891034680104455600190403a900110901e0020756507048540107139181c1c0c0c6800700c248905d1007030b0410482c008030010001940d2950280444c101c1121881a800c00da0b03070309025064200105000150000f2120102e02030352003049040541004085440181100c2400606494000e014460814043d4040c00b199 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 460418048 1250 460416798 460416877
    0x601150e09010302010c12020102090d030c021002070b18031c0e01090603020f040e0a0207052505040509070909030504080a0c0f0503030901090b0f04080a080327060a0b01050906 78
    0x1d1900d9851a000a8007150592001401c3c00c01d0100c04000c5041c400e6048408105c001410107410303042600b40101140c2d1160b50882c085e07400c006501c000140005030010440d25400369592a10740b0840051003801c0d413501c0c200e40c2506c1100740c00030014490406030180055a40d4511040c0c494503030004140d03030002d500840030b2510421000321401c14030b2084806641c144440c003125500c440c0001c00091080c804094401e00035911010b0401120015607128502450000c6080a8451003040221001510980b0640e403159000f0000100c07990402c03d0910300038140702c2d040135030746c0d5081da09001c0d2a55086400c0c08003940c0c140505840101d00303001a01c0706600541c20040704400207461001035000e604144400071511009804880c0121009080d4860560380c03001651b1030140180c2d0025034030806030b9100200342c90000101c4980c0400300140c18030042000f40c8681182400030007810600c6070400104200c900790649424005150005101c2403507602d0280f4034400d4620801e050022 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 460419298 1250 460418048 460418059
    0x4090f08071a070f03020a140c10050106030b03071e050a08032805070b0a0b040e06060f01030e120c1c081b0f09040203060301020403060501031a0907060c0615080601150e 75
    0x51040d0b4981c848038690803484c1034140140c3d1522081c406880040c005002c144294200041a495100000c81c404043d520003d00c14813039070762203000a40959822003011509a4400301e020405020a00f580050101c2100d0303126080c01d807610040b6451052a8020315210340c0009000840a0500c08250202d080ba0300441d49800c861410020300358440c560016141e22040008506580c0f0343c3d502071342c45244024800c0001c0745507940c41689815080320024442c1c0392004d4242c0087d4064007594002502010280c041004641e4144049030041d0318260b4562051000300085405008080c940155464807910f03442d103400c4402503130401c0d0000c0c214842c007209005c03186080001c88240c1d42c02e0181200d02503101d40e51400420f00a004691020740044d00b45000007040c03100c0032035400c19100504c2881e8901d0350352050059501c1d0303c90302ca40300000300d07030000d20004038050b0740c0309461120300e038100d036400a69500b80c600e10700b0750203030070508010003804021a07080c1c3d04040c3d0b505d003d82040d5407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 460420548 1250 460419298 460419301
    0x3030402130f0b0406060f2604140f0a0c05090709030803070518090a140a02030403090e060315010303020c0120030306010e151611030c090601030b04090f08071a 71
    0x20541011400803820300c8140c0350750180020400030b07088001e0741c00c0013400401c0313026a074200c000d080c8841040300101180030b5a07104600c508440310000e8107425040f10b41121600c0701e9445800c01103e1442e480c84a021b152109900c0c100140107001c109400307003c9a17010681054208070707070400040d000c202445454001000059002000c0d242d01c0200ca05000307440300d885a500090b80030b4607540e4164040c9030310080040f111800c0e401250029144007078100349985a1085900700e10041d1000380c046013034030101708401388a54006582c00a400b8050300c0d400ca19040c050303170715140d00381c20890140c0c0200303018011039680308884c440101d00740540040d240520041040c0c6a11016020714100001c10164160b1500d41e02e84c0d0b43c10000c00d2107a12542c0c0c0107140c000e000e1212002504031340d41c0042c0d0007513041c0c0c1c1c0340004080440490080c090321064440c940150700400c44500440e810a0315400d107032002c01c0c910603642814034091103d080e51107400e464210084040e442c2e106071124003260 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 460421798 1250 460420548 460420553
    0x102071a030103200f270f070e060c100b0103060e04030c050c010207050a0302060c12040807050406050f03060f28150504090302030706050915150a08060c1614030c0604050d02030304 80
    0x82c3c844131403031003500d4422091040e00c040c00421152581c2e2040c6d2080d2003c20700010b050301d00f020b01d200d1500b950b543d4a0141d9401e0801106206880c0403045030340c050403002c600100140e0051214100504002800079601e10818407600c0045400f58081003a44650f44288030090007a030311805002d10141907058240000500700541602008c0e00541c00861200d1030580e0400c030b11484a0040d420241c1c580d40d59608581c0e8650303041c0039036401103007081000101410140081500313014010050b003502c1d51075440d100041a0018400019480c0084e40d084540c0003269610031002d10b0084c01080c0c80b0b00b51003005503410b0117944124000d5140c20148000301c1c1c1d021080d41c18240d400100800c1e030b0b0b15071010261a02141c2c082411075500354200b0300c21902f00e0100031854400003505e61151080c6d4178100651114411926041e03001c2080182c0c680f018580514140c8040c8140e03070400103254601c0742c4914540068800e002d01c0e034496000d2000f4444108180015000117100440c0b030340c507042d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 460423048 1250 460421798 460421809
    0x10e03030703080c090a0f1e0b0a050304020102070302090a0f0509070305030316020109170c150705090f0a03060c032703170a0917190815010e0102071a03010320 71
    0x4807406001c1100e50030116034113810b01411241c40d064000c5c00008a43d890324500c0308201c07800e100300300d5500c09010810141c03c40d00800380040351400d080b000c1c2421b03080c0700255207503400140200d045019118012005036075000b040e501801c03058800007000700081e000142100d101810943c0503074408403080001074800421031394014480032018181c01e006500c26409028151401400711044c501a1884008010050f017000c0080c08101c4107a000c26000101802409488070b0000500030005103042c0c1c10030348051050140080d0901a441d5602d44888086803440c1c0c840c88000b079140e0a4100e0349101d45504054085401920702c1904201d41d0b4002d09040303c0d90f00110700040d040000541c0790f15250780540300490308880c04807400400704088510319031024038801403501244480d20305843c46844224410041c071401205e0141c039000c01912455030b560245c41c114890b0040200e0141100c4642425202100c2e141c00c1e02c070b5046280c0701f658a903081862001c400440d01047c103031917640 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 460424298 1250 460423048 460423057
    0x40e0106140402070213050934050909030d05150a21060f0204080f01090209090f06010b0721030207060b10050304240e0606210304090e07180c0e010e0303 68
    0x31a801640c0711002c4c40801c0b0510140070f01c04006c54586800c1042c8800c000c14201401c00750340d00410002d610941c19a80d203995a02c28041c50002491000e01050078902c0400350802e00c2c0104403802d18100c42c14680c01e5820482c1c0091000c0c40b045c000001606103003000c00003400079465511004100580c491b602000c00007005441252500249200300e549981140c0103484410b0035640c0d050361403031441e03010b820300400881c01003d000c000a11160800b05061100d11328120140c10305910b0103000301e016410000d0291381d4980f000c000d032040d20890030303600c0c4c0c2c038008203803400768941c02103060010884504154550240848507001040b056101080b00e41c01948500e131000c80c10100003205080d1000c800c440c0d681c01d850b01000c450184400524035114180845000c055000d000c00e1440c09010f000d42c0102c1144d2052100740007a0030103801c14401209060100c0302d04e00c1e6103000310300300c03000c40c1e00031114101e6507490584501c550100c0b4002c2c2100080c01c06040206045011954034800c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 460425548 1250 460424298 460424339
    0x901060c0b13080706050103050604030e030102090a0506071506080f0105070e0a0303111002030a06030506100b07081b0a03050423011d0102010b060c070602060114030a0b180706050405040e0106 85
    0x100782d98001d080010010944201c3e5400c44030170066982c4034902140e4544050b01c054001c03da010203000010f01d814000c5442542c8058880540c00d49000c0a0007520340040c02e0072075840351040c0c652500103482d4801c0300010500c0000900480c1c88101909084400183c800c0040186900345110b09031580401c0d103080320341c10715094101c49480386080d820484008168002c0a0000041c0555981e032070300440705980c024010340c0c0030303a1240c4940564a044a118600f4144c0041c05140701249040000c0c10601c00c080603901d6114680310011410001820710840200b032000c10240107421606100009894075103520301d1114415000180c03903000d00200c0c1d030840e42024650136610341d100b90000315001070050310075512503a0030030390103850b0745440c0244001481010000905141a81c039054078200014001c0d01210b91641c40380e80d031f0820700800e0003201c41018213040b184807108001110080000317542c2c1e291100e003018100400e4400140c0c03070110a070305102e814402998000103c24013680c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 460426798 1250 460425548 460425571
    0x12040b101a220b0a0e01080412180801020a020102070c090c0e0909070e0405100c0f080408070201110d0c0302011b0203040902031b0412050d170f070311070c050901060c0b 75
    0x4942c9042c80910724000111440188030080e000a2214100c1010b0304403200385407905100c0b649060300440c1d0490302260082d02025840d203050306420302410480301810007941c1c1458190b600c444540f407d980c080207246c0010303980000d013801441941c0c21050040c0800301003e10071042040002400000b4070313080701d485030003000046070084a081041c6001080a100580a1803400782000d9895180c00d030aa00b503c10308040000e80d440e440354401c1c0049841035101c0c020030fa119500c0300c40207a00514022418400c026010b00072664041107403000900c8140d9030280304258506d4000c1c00d684c1464061581d0b003088207079280707600f6000f00580f020b0b074102450040e200c1d40d800005c0400d0f4190f108854003107400015010402c4444c085907211000c1c020001c984580d6003a0301c040f2404481403d41d60155802403000c2126000484240c50b04041d552a004c00c11024440205050707030f101d800308680c019040103040203079044ca0000b80b0b004040c80c2c14030b0304000300b072610b4034002c940303004012420a1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 460428048 1250 460426798 460426807
    0xc100b0310060b1b120d021e0f0304050c09060312070f081303050c030303010506070f0f060f0207060e010e070519080a0305030a180507050607060f0212040b101a 71
    0x25141000440e00380e1501d4042030041a9452080310800d500c43d5138005030034501348050041408002441d0003440a40696181c606203140c500c0c0d20013500590030080400a01100d80340e0040c14038009804030000c01306960745d0301d0500780340c694500070800e06094062501b031005c0114954010900b0070004110102060783c034207040c9480c20707000c5102e0000034039140000c200920101d288056541c00e59114000312800003200500701a43d90000341f07c1c3c1c507441a410011840040c0b00302d401404694230410070310703615915555540e410b40748031007003504805a010405c42c0502c846c1e030048444204101d0020803504010340e603959180c07070003405000c2c0103112180010900038640001d4070003c00d890410340e003000c0c0c03480c9030080159109131080c85102e81001c82550b41c99440c141c80d50382244c0c1c008010b1980520300418070405030414001030708c3d0a941c80c90415812600c03400204103285040013516118034043c0343c08120410040d0070888452002d034028803000d44880421114103e00781a51603c0d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 460429298 1250 460428048 460428071
    0x303020c1905030a03110708010501030b0403111504120306120c381b0f0d0f020304240201180f080f0705011a090117070b0a020a0503040e0106030b04020c10 69
    0x1250700c00d81c012601482032a00d454185a4094034040241c480307841a50b501e05d54503200d850a84034280400f40c5001402da0100b40000d00030200c04006c03181c94015107164030140d1054242c5540d044400341d076403042d042c5200c0e050a42c14403c0c41d0151409007020044042182c81e80d6600300301c68000d9001c598620925920300e40c1ca402d04208202e45510101c034041c103100c1062240a40008000341e0302d008070700c4030088a07010003181803412904d50728001c004082d0312010454090380207140c03000c1035000420010615202c200454020001d20204000901502031802821100021802c00300c1004c014802c41c009602480346419260300201c450703407923185405403510130b4824000014841d6203040001240114018404103c00004031400351143c1ea80d0314100c072540c900b00380a134070340d034000c40414001d02030198050282c0c1ca59070b06c103d03800c9115640d681855503000b9000298900001c60041180039030600450803200000d65007581003107142e45420390b803180304c400e50308906a00e80034000031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 460430548 1250 460429298 460429339
    0x12030112060b0a230103020414100306081912020c01021002030916031b17032a010603050303011a1e03060d061b020610050a03080f070602030c03150306010303020c 72
    0xb4a80104002451a40c03014104070b500f01c0d20304070280320002c411460740207601030b1081d18212402941118250b80703602d4108140b03141c00c00544001c2c10b43e01e120100da80503003001000510403440f4030000c0f0310001d9040002080e0083e5007564210f42c40300e010f11240ba6400f00e540c00d04a180020003503225210180007605103220740d108440200300b00c040000c00d0040e00c9002c160700707480703400c40310404903150184800550b002d180d1101c0c6641c401c10000b00c245a107154000010301e0414040000340b13101100403825110258002d480d1386d400880180003a04511031074211400c0b03070009481c64074240f440c4600020602d9094400030600c00b10000c0c025850381c40500860580c8014104211402d408000d42481454000b680051046800048075145902011800d4803001000544240e2843d59010a69405021900641a428081ca0380010303500e001030340c0105050035280742c5a00e8000d524090001083c0e901911943c481001000403071780202e0b48068040c0261905549841000d01d0345c003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 460431654 1106 460430548 460430561
    0xa021204061a040b0f2101020f093d02030c0708032703060c0304081308060117060f06010807180e062e080709240807021203011206 58
    0x80341031520354030b0b90b6060042c043d0800c4e40d4420500381c007802e80c1c025000321275a0031030201d40d044840c50403900d0107072211280d1221928400441c10740550f8440e0041140002034070000c00d40781c01910074000c4a0541c000442110511541c485000b80d0b82d80c049504c0401c96030622076100c7c030950b000c134071403c40064010018030f40c0e40c407502e1003080d6982c40500200c1d0710810400c201c40c514200030380e80d00b00414446c0c0180809601d00b0341d004000d071518121070100754002c04200401c0607a1b00a010b070304160300f840c05440b6991881001d907124500e00900403140010340700009280705030755541764030440064912041114080e0012090042c03004480082505031102c4aa00e6074030a0060340d034048500e1411100e00f136501d00b42c007601840549002d401c81c04828032140141c0ea088907010f07420104d03600c01010010001e2070824050300043c0151102100b40c10400c50500c4803d81100 = true := by decide +kernel

theorem cover : BRFrame.Cov 460251798 460431654 := by
  have h0 := BRFrame.cov_init 460251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 460251798 ≤ n) (h2 : n < 460431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
